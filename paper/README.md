# Manuscript and supplement

[`main.pdf`](main.pdf) is the reading copy of the paper; [`supplement.pdf`](supplement.pdf) contains
the complete proofs. `main.tex` and `supplement.tex` are their sources. They share `macros.tex`
and `refs.bib`. In the printed text, numbers with the prefix S refer to the supplement and numbers
with the prefix M to the main text; in the sources, cross-document labels carry the prefixes `S-`
and `M-`.

From the repository root,

```sh
bash scripts/check_paper.sh
```

compiles both documents (twice each, to resolve their mutual references) into `paper/build/`
and fails on a LaTeX error, an undefined reference or citation, or an overfull box. A
source-only checkout needs no previously generated auxiliary files. The figures are TikZ
drawings in the TeX sources.

The statements of both documents carry source tags `\lean{...}` naming the Lean declarations
that formalise them; `scripts/paper_tags.mjs` collects them into `../verification/PAPER-INDEX.md`
and `../verification/Audit/PaperTags.lean`. The correspondence with the Lean development is
described in the section "Formal verification" of the paper and in `../verification/README.md`.

For the shortest assessment of the claims and verification boundary, read
[`REVIEW.md`](../REVIEW.md). After rebuilding, copy the two PDFs from `paper/build/`
to `paper/` when updating the reading copies. Generated auxiliary files stay in the
ignored build directory.
