| Compile haskell source files |      |                                                              |
| ---------------------------- | ---- | ------------------------------------------------------------ |
|                              |      |                                                              |
|                              |      | You need to compile the haskell source file with the free-compiler and put the result into the `../Output` folder. |
|                              |      | The source file is `FastAndLooseReasoning.hs`                |
|                              |      | If you are in the root directory of the free-compiler you can run the following command for the compilation process. |
|                              |      |                                                              |
|                              |      | ```                                                          |
|                              |      | cabal new-run freec -- --transform-pattern-matching -o example/CaseStudyMorallyCorrect/Output example/CaseStudyMorallyCorrect/FastAndLooseReasoning.hs |
|                              |      | ```                                                          |
|                              |      |                                                              |
| **Compile Coq files**        |      |                                                              |
|                              |      |                                                              |
|                              |      | To run the proof file `Proof.v` you need to compile the dependencies first. |
|                              |      | Make sure that your `_CoqProject` is locted in `CaseStudyMorallyCorrect` and not in one of its subdirectories.  Add the following lines into the `_CoqProject`<br /> `-R .\Output Generated` <br/>`-R .\ProofInfrastructure Proofs` |
|                              |      | The easiest way to do so is to create a `Makefile` from the `_CoqProject` in this directory and run it. |
|                              |      | ```                                                          |
|                              |      | coq_makefile -f _CoqProject -o Makefile                      |
|                              |      | make                                                         |
|                              |      | ```                                                          |
|                              |      | The easiest way to do so is to create a `Makefile` from the `_CoqProject` in this directory and run it. |
|                              |      | The `Proof.v` file can now be executed.                      |