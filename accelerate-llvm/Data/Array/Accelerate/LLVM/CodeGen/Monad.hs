{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Monad
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--


module Data.Array.Accelerate.LLVM.CodeGen.Monad (

  CodeGen,
  runLLVM,

  -- declarations
  freshName, declare, intrinsic,

  -- basic blocks
  Block,
  newBlock, setBlock, createBlocks, createBlocks', beginGroup, terminate,

  -- instructions
  instr, do_, return_, returnV, phi, phi', br, cbr,

  -- metadata
  addMetadata, trace,

  -- llvm-general-quote
  (.=.),
  B.CodeGenMonad(..)

) where

-- standard library
import Control.Applicative
import Control.Monad.State.Strict
import Data.Maybe
import Data.Map                                                 ( Map )
import Data.Sequence                                            ( Seq )
import Data.HashMap.Strict                                      ( HashMap )
import Data.String
import Data.Word
import Text.Printf
import System.IO.Unsafe
import qualified Data.Foldable                                  as Seq
import qualified Data.HashMap.Strict                            as HashMap
import qualified Data.Map                                       as Map
import qualified Data.Sequence                                  as Seq

-- llvm-general
import LLVM.General.AST                                         hiding ( Module )
import qualified LLVM.General.AST.Constant                      as C
import qualified LLVM.General.AST                               as AST
import qualified LLVM.General.AST.Global                        as AST
import qualified LLVM.General.Quote.Base                        as B

-- accelerate
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.Target
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Intrinsic
import Data.Array.Accelerate.LLVM.CodeGen.Type
import qualified Data.Array.Accelerate.LLVM.Debug               as Debug

-- Names
-- =====

instance IsString Name where
  fromString = Name . fromString

-- | Generate a fresh (un)name.
--
freshName :: CodeGen Name
freshName = state $ \s@CodeGenState{..} -> ( UnName next, s { next = next + 1 } )


-- Code generation operations
-- ==========================

-- | The code generation state for scalar functions and expressions.
--
-- We use two records: one to hold all the code generation state as it walks the
-- AST, and one for each of the basic blocks that are generated during the walk.
--
data CodeGenState = CodeGenState
  { blockChain          :: Seq Block                            -- blocks for this function
  , symbolTable         :: Map Name AST.Global                  -- global (external) function declarations
  , metadataTable       :: HashMap String (Seq [Maybe Operand]) -- module metadata to be collected
  , intrinsicTable      :: HashMap String Name                  -- standard math intrinsic functions
  , next                :: {-# UNPACK #-} !Word                 -- a name supply
  }
  deriving Show

data Block = Block
  { blockLabel          :: Name                         -- block label
  , instructions        :: Seq (Named Instruction)      -- stack of instructions
  , terminator          :: Maybe (Named Terminator)     -- block terminator
  }
  deriving Show

newtype CodeGen a = CodeGen { runCodeGen :: State CodeGenState a }
  deriving (Functor, Applicative, Monad, MonadState CodeGenState)

instance B.CodeGenMonad CodeGen where
  newVariable = freshName
  exec f = do
    f
    let n = newBlock' (Name "nextblock")
    _ <- br n
    createBlocks

assign :: [Name] -> CodeGen [Operand] -> CodeGen [BasicBlock]
xs `assign` f = do
  xs' <- f
  zipWithM_ mkSelect xs xs'
  let n = newBlock' (Name "nextblock")
  _ <- br n
  createBlocks
 where
  mkSelect :: Name -> Operand -> CodeGen Operand
  mkSelect n x = do
    let t = typeOfOperand x
        true = ConstantOperand $ C.Int 1 1
    instr' t n $ Select true x x []

class Assignable a b where
  (.=.) :: a -> CodeGen b -> CodeGen [BasicBlock]
instance Assignable Name Operand where
  n .=. x = x >>= \x' -> assign [n] (return [x'])
instance Assignable [Name] [Operand] where
  (.=.) = assign
instance Assignable [Operand] [Operand] where
  ns .=. xs =
    let nameFromOperand (LocalReference _ n) = n
        nameFromOperand op = error $ "can't assign to non-reference Operand" ++ show op

        ns' = map nameFromOperand ns
    in ns' .=. xs

runLLVM
    :: forall t aenv a. (Target t, Intrinsic t)
    => CodeGen [Kernel t aenv a]
    -> Module t aenv a
runLLVM ll =
  let
      (r, st)   = runState (runCodeGen ll) $ CodeGenState
                    { blockChain        = initBlockChain
                    , symbolTable       = Map.empty
                    , metadataTable     = HashMap.empty
                    , intrinsicTable    = intrinsicForTarget (undefined::t)
                    , next              = 0
                    }

      kernels   = map unKernel r
      defs      = map GlobalDefinition (kernels ++ Map.elems (symbolTable st))
               ++ createMetadata (metadataTable st)

      name | x:_          <- kernels
           , f@Function{} <- x
           , Name s <- AST.name f = s
           | otherwise            = "<undefined>"
  in
  Module $ AST.Module
    { moduleName         = name
    , moduleDataLayout   = targetDataLayout (undefined::t)
    , moduleTargetTriple = targetTriple (undefined::t)
    , moduleDefinitions  = defs
    }


-- | An initial block chain
--
initBlockChain :: Seq Block
initBlockChain =
  initBlockChain' $ Block "entry" Seq.empty Nothing

initBlockChain' :: Block -> Seq Block
initBlockChain' l = Seq.singleton l

-- | Extract the block state and construct the basic blocks to form a function
-- body. This also clears the block stream, ready for a new function to be
-- generated.
--
createBlocks :: CodeGen [BasicBlock]
createBlocks = freshName >>= \n -> createBlocks' False $ Block n Seq.empty Nothing

createBlocks' :: Bool -> Block -> CodeGen [BasicBlock]
createBlocks' reset l
  = state
  $ \s -> let s'     = s { blockChain = initBlockChain' l, next = if reset then 0 else (next s) }
              blocks = makeBlock `fmap` blockChain s
              m      = Seq.length (blockChain s)
              n      = Seq.foldl' (\i b -> i + Seq.length (instructions b)) 0 (blockChain s)
          in
          trace (printf "generated %d instructions in %d blocks" (n+m) m) ( Seq.toList blocks , s' )
  where
    makeBlock Block{..} =
      let err   = $internalError "createBlocks" $ "Block has no terminator (" ++ show blockLabel ++ ")"
          term  = fromMaybe err terminator
          ins   = Seq.toList instructions
      in
      BasicBlock blockLabel ins term


-- Instructions
-- ------------

-- | Add an instruction to the state of the currently active block so that it is
-- computed, and return the operand (LocalReference) that can be used to later
-- refer to it.
--
instr :: Type -> Instruction -> CodeGen Operand
instr t op = do
  name  <- freshName
  instr' t name op

instr' :: Type -> Name -> Instruction -> CodeGen Operand
instr' t name op = do
  state $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> $internalError "instr" "empty block chain"
      bs Seq.:> b -> ( LocalReference t name
                     , s { blockChain = bs Seq.|> b { instructions = instructions b Seq.|> name := op } } )

-- | Execute an unnamed instruction
--
do_ :: Instruction -> CodeGen ()
do_ op = do
  modify $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> $internalError "do_" "empty block chain"
      bs Seq.:> b -> s { blockChain = bs Seq.|> b { instructions = instructions b Seq.|> Do op } }


-- | Return void from a basic block
--
return_ :: CodeGen ()
return_ = void $ terminate (Do (Ret Nothing []))


-- | Add a phi node to the top of the specified block
--
phi :: Block                    -- ^ the basic block to modify
    -> Name                     -- ^ the name of the critical variable (to assign the result of the phi instruction)
    -> Type                     -- ^ type of the critical variable
    -> [(Operand, Block)]       -- ^ list of incoming operands and the precursor basic block they come from
    -> CodeGen Operand
phi target crit t incoming =
  let op          = Phi t [ (o,blockLabel) | (o,Block{..}) <- incoming ] []
      search this = blockLabel this == blockLabel target
  in
  state $ \s ->
    case Seq.findIndexR search (blockChain s) of
      Nothing -> $internalError "phi" "unknown basic block"
      Just i  -> ( LocalReference t crit
                 , s { blockChain = Seq.adjust (\b -> b { instructions = crit := op Seq.<| instructions b }) i (blockChain s) } )

phi' :: Type -> [(Operand,Block)] -> CodeGen Operand
phi' t incoming = do
  crit  <- freshName
  block <- state $ \s -> case Seq.viewr (blockChain s) of
                           Seq.EmptyR -> $internalError "phi'" "empty block chain"
                           _ Seq.:> b -> ( b, s )
  phi block crit t incoming


returnV :: Operand -> CodeGen ()
returnV op = void $ terminate (Do (Ret (Just op) []))

-- | Unconditional branch. Return the name of the block that was branched from.
--
br :: Block -> CodeGen Block
br target = terminate $ Do (Br (blockLabel target) [])

-- | Conditional branch. Return the name of the block that was branched from.
--
cbr :: Operand -> Block -> Block -> CodeGen Block
cbr cond t f = terminate $ Do (CondBr cond (blockLabel t) (blockLabel f) [])

-- | Add a termination condition to the current instruction stream. Return the
-- name of the block chain that was just terminated.
--
terminate :: Named Terminator -> CodeGen Block
terminate target =
  state $ \s ->
    case Seq.viewr (blockChain s) of
      Seq.EmptyR  -> $internalError "terminate" "empty block chain"
      bs Seq.:> b -> ( b, s { blockChain = bs Seq.|> b { terminator = Just target } } )


-- | Add a global declaration to the symbol table
--
declare :: Global -> CodeGen ()
declare g =
  let unique (Just q) | g /= q    = $internalError "global" "duplicate symbol"
                      | otherwise = Just g
      unique _                    = Just g
  in
  modify (\s -> s { symbolTable = Map.alter unique (AST.name g) (symbolTable s) })


-- | Get name of the corresponding intrinsic function implementing a given C
-- function. If there is no mapping, the C function name is used.
--
intrinsic :: String -> CodeGen Name
intrinsic key =
  state $ \s ->
    let name = HashMap.lookupDefault (Name key) key (intrinsicTable s)
    in  (name, s)


-- Block chain
-- ===========

-- | Create a new basic block, but don't yet add it to the block chain. You need
-- to call 'setBlock' to append it to the chain, so that subsequent instructions
-- are added to this block.
--
-- Note: [Basic blocks]
--
-- The names of basic blocks are generated based on the base name provided to
-- the 'newBlock' function, as well as the current state (length) of the block
-- stream. By not immediately adding new blocks to the stream, we have the
-- advantage that:
--
--   1. Instructions are generated "in order", and are always appended to the
--      stream. There is no need to search the stream for a block of the right
--      name.
--
--   2. Blocks are named in groups, which helps readability. For example, the
--      blocks for the then and else branches of a conditional, created at the
--      same time, will be named similarly: 'if4.then' and 'if4.else', etc.
--
-- However, this leads to a slight awkwardness when walking the AST. Since a new
-- naming group scheme is only applied *after* a call to 'setBlock',
-- encountering (say) nested conditionals in the walk will generate logically
-- distinct blocks that happen to have the same name. This means that
-- instructions might be added to the wrong blocks, or the first set of blocks
-- will be emitted empty and/or without a terminator.
--
newBlock :: String -> CodeGen Block
newBlock nm =
  state $ \s ->
    let idx     = next s
        label   = Name $ let (h,t) = break (== '.') nm in (h ++ shows idx t)
        nextB   = newBlock' label
    in
    ( nextB, s{ next = idx+1 } )

newBlock' :: Name -> Block
newBlock' label = Block label Seq.empty Nothing

-- | Add this block to the block stream. Any instructions pushed onto the stream
-- by 'instr' and friends will now apply to this block.
--
setBlock :: Block -> CodeGen ()
setBlock next =
  modify $ \s -> s { blockChain = blockChain s Seq.|> next }

-- | Generate a new block and branch unconditionally to it. This is used to
-- ensure a block group is initialised before recursively walking the AST. See
-- note: [Basic blocks].
--
beginGroup :: String -> CodeGen ()
beginGroup nm = do
  next <- newBlock (nm ++ ".entry")
  _    <- br next
  setBlock next


-- Metadata
-- ========

-- | Insert a metadata key/value pair into the current module.
--
addMetadata :: String -> [Maybe Operand] -> CodeGen ()
addMetadata key val =
  modify $ \s ->
    s { metadataTable = HashMap.insertWith (flip (Seq.><)) key (Seq.singleton val) (metadataTable s) }


-- | Generate the metadata definitions for the file. Every key in the map
-- represents a named metadata definition. The values associated with that key
-- represent the metadata node definitions that will be attached to that
-- definition.
--
createMetadata :: HashMap String (Seq [Maybe Operand]) -> [Definition]
createMetadata md = build (HashMap.toList md) (Seq.empty, Seq.empty)
  where
    build :: [(String, Seq [Maybe Operand])]
          -> (Seq Definition, Seq Definition)   -- accumulator of (names, metadata)
          -> [Definition]
    build []     (k,d) = Seq.toList (k Seq.>< d)
    build (x:xs) (k,d) =
      let (k',d') = meta (Seq.length d) x
      in  build xs (k Seq.|> k', d Seq.>< d')

    meta :: Int                                 -- number of metadata node definitions so far
         -> (String, Seq [Maybe Operand])       -- current assoc of the metadata map
         -> (Definition, Seq Definition)
    meta n (key, vals)
      = let node i      = MetadataNodeID (fromIntegral (i+n))
            nodes       = Seq.mapWithIndex (\i x -> MetadataNodeDefinition (node i) (Seq.toList x)) vals
            name        = NamedMetadataDefinition key [ node i | i <- [0 .. Seq.length vals - 1] ]
        in
        (name, nodes)


-- Debug
-- =====

{-# INLINE trace #-}
trace :: String -> a -> a
trace msg next = unsafePerformIO $ do
  Debug.message Debug.dump_llvm ("llvm: " ++ msg)
  return next

