# Compile haskell source files

You need to compile the haskell source files with the free-compiler and put the result into the `../generated` folder.
The source files include `Razor.hs` from this directory and additionally `../Proofs/AppendAssocs.hs`, as we make use of a lemma which is proven in the corresponding proof file.
If you are in the root directory of the free-compiler you can run the following command for the compilation process.

```
cabal new-run freec -- --transform-pattern-matching -o example/generated example/Proofs/AppendAssoc.hs example/CaseStudyHuttonsRazor/Razor.hs
```

# Compile coq files

To run the proof files you need to compile their dependencies first.
The easiest way to do so is to create a `Makefile` from the `_CoqProject` in this directory and run it.

```
coq_makefile -f _CoqProject -o Makefile
make
```

The `*Proofs.v` files can now be opened from this directory or from the parent directory.
