{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Type
-- Copyright   : [2014] Trevor L. McDonell, Sean Lee, Vinod Grover, NVIDIA Corporation
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Type
  where

-- accelerate
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.Util

-- llvm-general
import LLVM.General.AST
import LLVM.General.AST.Float
import LLVM.General.AST.AddrSpace
import LLVM.General.AST.Type
import qualified LLVM.General.AST.Constant as C

-- standard library
import Foreign.C.Types
import Data.List


-- Generate the LLVM type for atomic types
--
class TypeOf a where
  typeOf :: a -> Type

instance TypeOf (ScalarType a) where
  typeOf = llvmOfScalarType

instance TypeOf (NumType a) where
  typeOf = llvmOfNumType

instance TypeOf (IntegralType a) where
  typeOf = llvmOfIntegralType

instance TypeOf (FloatingType a) where
  typeOf = llvmOfFloatingType

instance TypeOf (NonNumType a) where
  typeOf = llvmOfNonNumType


-- In order to use operations from Arithemetic.hs when defining skeletons, we
-- often need integer types
--
class IntType c where
  int   :: c Int
  int32 :: c Int32

instance IntType ScalarType where
  int   = scalarType
  int32 = scalarType

instance IntType NumType where
  int   = numType
  int32 = numType

instance IntType IntegralType where
  int   = integralType
  int32 = integralType


llvmOfTupleType :: TupleType a -> [Type]
llvmOfTupleType UnitTuple         = []
llvmOfTupleType (SingleTuple t)   = [llvmOfScalarType t]
llvmOfTupleType (PairTuple t1 t2) = llvmOfTupleType t1 ++ llvmOfTupleType t2

llvmOfScalarType :: ScalarType a -> Type
llvmOfScalarType (NumScalarType t)    = llvmOfNumType t
llvmOfScalarType (NonNumScalarType t) = llvmOfNonNumType t


llvmOfNumType :: NumType a -> Type
llvmOfNumType (IntegralNumType i) = llvmOfIntegralType i
llvmOfNumType (FloatingNumType f) = llvmOfFloatingType f

llvmOfIntegralType :: forall a. IntegralType a -> Type
llvmOfIntegralType i | IntegralDict <- integralDict i = IntegerType (bitSize (undefined::a))

llvmOfFloatingType :: FloatingType a -> Type
llvmOfFloatingType f =
  case f of
    TypeFloat  _  -> FloatingPointType 32 IEEE
    TypeCFloat _  -> FloatingPointType 32 IEEE
    TypeDouble _  -> FloatingPointType 64 IEEE
    TypeCDouble _ -> FloatingPointType 64 IEEE


llvmOfNonNumType :: NonNumType t -> Type
llvmOfNonNumType t =
  case t of
    TypeBool _ -> IntegerType 1         -- data layout ensures 8-bits are actually used
    TypeChar _ -> IntegerType 32        -- Haskell char
    _          -> IntegerType 8         -- signed and unsigned C characters


signedIntegralNum :: IntegralType a -> Bool
signedIntegralNum t =
  case t of
    TypeInt _    -> True
    TypeInt8 _   -> True
    TypeInt16 _  -> True
    TypeInt32 _  -> True
    TypeInt64 _  -> True
    TypeCShort _ -> True
    TypeCInt _   -> True
    TypeCLong _  -> True
    TypeCLLong _ -> True
    _            -> False

unsignedIntegralNum :: IntegralType a -> Bool
unsignedIntegralNum = not . signedIntegralNum

someFloat :: FloatingType a -> a -> SomeFloat
someFloat t f =
  case t of
    TypeFloat  _                    -> Single f
    TypeDouble _                    -> Double f
    TypeCFloat _  | CFloat f'  <- f -> Single f'
    TypeCDouble _ | CDouble f' <- f -> Double f'



-- | The size of an LLVM type representation. Note that this does not currently
-- handle with all types, such as function types or named type synonyms.
--
bitSizeOfType :: Type -> Word32
bitSizeOfType t =
  case t of
    VoidType            -> 0
    IntegerType{}       -> typeBits t                   -- Bool returns 1, but 8-bits are actually used as per data layout
    FloatingPointType{} -> typeBits t
    PointerType{}       -> bitSize (undefined::Int)     -- Native word size
    VectorType{..}      -> nVectorElements * bitSizeOfType elementType
    ArrayType{..}       -> nArrayElements' * bitSizeOfType elementType where nArrayElements' = fromIntegral nArrayElements
    StructureType{..}
      | isPacked        -> sum [ bitSizeOfType f | f <- elementTypes ]
      | otherwise       -> error "bitSizeOf StructureType (with alignment)"
    FunctionType{}      -> error "bitSizeOf FunctionType"
    NamedTypeReference{}-> error "bitSizeOf NamedTypeReference"
    MetadataType        -> error "bitSizeOf MetadataType"

typeOfConstant :: C.Constant -> Type
typeOfConstant C.Int{..} = IntegerType integerBits
typeOfConstant C.Float{..} = case floatValue of
  Half{}      -> half
  Single{}    -> float
  Double{}    -> double
  Quadruple{} -> fp128
  X86_FP80{}  -> x86_fp80
  PPC_FP128{} -> ppc_fp128
typeOfConstant C.Null{..} = constantType
typeOfConstant C.Struct{..} =
  StructureType isPacked (map typeOfConstant memberValues)
typeOfConstant C.Array{..} = ArrayType (genericLength memberValues) memberType
typeOfConstant C.Vector{..} = case memberValues of
  (x:_) -> VectorType (genericLength memberValues) (typeOfConstant x)
  [] -> error "typeOfConstant: empty Vector"
typeOfConstant C.Undef{..} = constantType
typeOfConstant C.BlockAddress{} = PointerType (IntegerType 8) (AddrSpace 0)
typeOfConstant (C.GlobalReference t _) = t
typeOfConstant C.Add{..} = typeOfConstant operand0
typeOfConstant C.FAdd{..} = typeOfConstant operand0
typeOfConstant C.Sub{..} = typeOfConstant operand0
typeOfConstant C.FSub{..} = typeOfConstant operand0
typeOfConstant C.Mul{..} = typeOfConstant operand0
typeOfConstant C.FMul{..} = typeOfConstant operand0
typeOfConstant C.UDiv{..} = typeOfConstant operand0
typeOfConstant C.SDiv{..} = typeOfConstant operand0
typeOfConstant C.FDiv{..} = typeOfConstant operand0
typeOfConstant C.URem{..} = typeOfConstant operand0
typeOfConstant C.SRem{..} = typeOfConstant operand0
typeOfConstant C.FRem{..} = typeOfConstant operand0
typeOfConstant C.Shl{..} = typeOfConstant operand0
typeOfConstant C.LShr{..} = typeOfConstant operand0
typeOfConstant C.AShr{..} = typeOfConstant operand0
typeOfConstant C.And{..} = typeOfConstant operand0
typeOfConstant C.Or{..} = typeOfConstant operand0
typeOfConstant C.Xor{..} = typeOfConstant operand0
typeOfConstant C.GetElementPtr{..} = typeOfConstant address
typeOfConstant C.Trunc{..} = type'
typeOfConstant C.ZExt{..} = type'
typeOfConstant C.SExt{..} = type'
typeOfConstant C.FPToUI{..} = type'
typeOfConstant C.FPToSI{..} = type'
typeOfConstant C.UIToFP{..} = type'
typeOfConstant C.SIToFP{..} = type'
typeOfConstant C.FPTrunc{..} = type'
typeOfConstant C.FPExt{..} = type'
typeOfConstant C.PtrToInt{..} = type'
typeOfConstant C.IntToPtr{..} = type'
typeOfConstant C.BitCast{..} = type'
typeOfConstant C.ICmp{..} = case typeOfConstant operand0 of
  VectorType{..} -> VectorType nVectorElements (IntegerType 1)
  _              -> IntegerType 1
typeOfConstant C.FCmp{..} = case typeOfConstant operand0 of
  VectorType{..} -> VectorType nVectorElements (IntegerType 1)
  _              -> IntegerType 1
typeOfConstant C.Select{..} = typeOfConstant trueValue
typeOfConstant C.ExtractElement{..} = case C.memberValues vector of
  (x:_) -> typeOfConstant x
  [] -> error "typeOfConstant: empty Vector"
typeOfConstant C.InsertElement{..} = typeOfConstant vector
typeOfConstant C.ShuffleVector{..} =
  case (typeOfConstant operand0, typeOfConstant mask) of
    (VectorType _ t, VectorType n _) -> VectorType n t
    _ -> error "typeOfConstant: expected vector arguments to ShuffleVector"
typeOfConstant C.ExtractValue{..} =
  extractTypes indices' (typeOfConstant aggregate)
 where
  extractTypes []     t = t
  extractTypes (n:ns) t = case t of
    StructureType{..} -> extractTypes ns (elementTypes !! fromIntegral n)
    ArrayType{..}     -> extractTypes ns elementType
    _                 -> error "typeOfConstant: expected aggregate value in ExtractValue"
typeOfConstant C.InsertValue{..} = typeOfConstant aggregate

typeOfOperand :: Operand -> Type
typeOfOperand (LocalReference t _) = t
typeOfOperand (ConstantOperand c) = typeOfConstant c
typeOfOperand MetadataStringOperand{} = MetadataType
typeOfOperand MetadataNodeOperand{} = MetadataType
