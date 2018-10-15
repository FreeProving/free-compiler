# LaTeX-Template using KCSS-Style

The template is based on the KCSS-Style.
You only need to modify the `thesis.tex` and `thesis.bib` files.
Only after consultation with your advisor you can also alter the `ifiseries.sty` (if necessary).

For code highlighting we recommend using the `minted` package.

# Building the PDF

You can use the following commands for the initial build.

```bash
pdflatex -shell-escape thesis.tex
% compile the references
bibtex thesis
pdflatex -shell-escape thesis.tex
% in order to get all references right, a second compilation is necessary
pdflatex -shell-escape thesis.tex
```
The flat `-shell-escape` is only necessary if you use the `minted` package.
When you recompile you only need to recompile the references if you modified the associated file `thesis.bib`.
Thus, in most cases it is enough to use `pdflatex` only once.


[minted package](https://github.com/gpoore/minted)  
[KCSS-Style](https://git.informatik.uni-kiel.de/kcss/kcss-style)  
