An LLVM backend for the Accelerate Array Language
=================================================

This package compiles Accelerate code to LLVM IR, and executes that code on
multicore CPUs as well as NVIDIA GPUs. For details on Accelerate, refer to the
[main repository][GitHub]. Please also file bug reports and feature requests
with the [issue tracker][Issues] of the main repository.

  [GitHub]:  https://github.com/AccelerateHS/accelerate
  [Issues]:  https://github.com/AccelerateHS/accelerate/issues


TODOs
-----

These are some TODOs and notes that pop into my head from time to time...

**Code generation**

  * Implement a wrapper over llvm-general-pure so that (at least) Operands are
    typed. Thus, implement a completely typed compilation and execution
    pipeline. Moreover, LLVM IR is typed, but we only get type errors at
    Accelerate compilation time, which corresponds to Haskell runtime ):

    * Would that be the first completely typed DSL?

    * The llvm-tf package may provide useful inspiration.

    * Still unclear how to implement tuples...


**Native backend**

  * Complete coverage of skeleton operations

**NVPTX backend**

  * Complete coverage of skeleton operations

  * Rename NVVM -> NVPTX?

**Thread safety**

  * There is a bunch of behind-the-scenes state going on. This is all wrapped in
    MVars, but I'm still not certain if it is all correct. There is a line in
    the MVar documentation that says 'modifyMVar' is "only atomic if there are
    no other producers for this MVar", which is a little worrying...

  * IORef might be a (faster?) lighter-weight alternative to using MVar.

