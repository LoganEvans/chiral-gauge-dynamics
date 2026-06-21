# Litlib LaTeX Artifacts

This directory contains automatically generated files to seamlessly integrate your formal Lean 4 verification into your LaTeX paper.

## 1. Setup

If you generated this inside your `paper/` directory, the files are already in place! 

In your LaTeX preamble, include the `litlib` package:
```latex
\usepackage{litlib}
```
*(Note: `litlib.sty` automatically loads `minted`, `hyperref`, and `xcolor`.)*

## 2. Bibliography

You do **not** need to manually copy and paste the generated citations into your hand-crafted `.bib` file! LaTeX perfectly supports multiple bibliography sources.

**If using BibLaTeX:**
```latex
\addbibresource{my-references.bib}
\addbibresource{litlib-references.bib}
```

**If using traditional BibTeX:**
```latex
\bibliography{my-references,litlib-references}
```

**Smart Deduplication:** 
`litlib4` automatically scans your target directory for any existing `.bib` files (e.g. your manual bibliography database). If it finds that you have already defined a specific BibTeX key manually, it will gracefully suppress that key from `litlib-references.bib` so that BibLaTeX/BibTeX will never complain about duplicate definitions!

## 3. The Code Summary Appendix

To embed the fully formatted and automatically hyperlinked Lean code summary into your paper, simply input the `.tex` file under a section or appendix heading:
```latex
\section{Formal Code Summary}
\label{sec:code_summary}
\input{litlib-code-summary.tex}
```

**Speeding up LaTeX compilation:**
Because `minted` shells out to Pygments to format the syntax highlighting, compiling the full code summary can significantly slow down your build times while drafting. To do a fast build, simply comment out the `\input` line:
```latex
% \input{litlib-code-summary.tex}
```
The `\leanref` citations in your main text will still work and print the appropriate `[L?]` markers, but the code block itself will be omitted until you are ready for a final build.

## 4. Inline Citations

Inside your text, you can cite any formally verified equation or theorem by passing its exact Lean 4 declaration name to the `\leanref` macro:
```latex
We define the Spacetime Point \leanref{Litlib.Y2024.Author.SpacetimePoint} as...
```
This will automatically generate a clickable `[L?]` annotation in the PDF that links directly to the code summary, and logs it in the Formal Verification Index.
