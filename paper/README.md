# Papers

| Directory | Paper | Files |
|---|---|---|
| `p1/` | I. *Explicit Hamiltonian full packings of the four-ball by equal balls* | `main.pdf`, `supplement.pdf` |
| `p2/` | II. *Explicit Hamiltonian ball packings: general capacities, higher dimensions and the Siegel–Yao criterion* | `main.pdf`, `supplement.pdf` |
| `p3/` | III. *Elementary packings of the four-ball and their limits* | `main.pdf` |

Each directory holds the TeX sources (`main.tex`, `supplement.tex`, `main/`, `supp/`, `macros.tex`,
`refs.bib`). In Papers I and II, numbers with the prefix S refer to the supplement and M to the main
text. Paper II restates the results it uses from Paper I (`p2/p1refs.tex`, `p2/supp/quoted.tex`).

```sh
bash scripts/check_paper.sh     # from the repository root
```

compiles all three into each directory's `build/` and fails on a LaTeX error, an undefined or
duplicate reference, or an overfull box. Copy the PDFs from `build/` to update the reading copies.

Statements in Papers I and II carry source tags `\lean{…}` naming the Lean declarations that
formalise them; `scripts/paper_tags.mjs` collects them into `../verification/PAPER-INDEX.md`.
