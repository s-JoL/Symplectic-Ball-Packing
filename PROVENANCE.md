# Publication and provenance

Liang Song, *Explicit Hamiltonian ball packings in every dimension*, version **1.0.1**,
29 October 2026. The archive includes the manuscript, supplement and Lean development.

- Version DOI: [10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498).
- All-version DOI: [10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575).
- Deposited files: [Zenodo record](https://zenodo.org/records/23763498).
- Fixed GitHub release: [v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/releases/tag/v1.0.1).
- Fixed source tree: [v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/v1.0.1).
- Fixed reviewer guide: [guide at v1.0.1](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.1/REVIEW.md).
- Citation metadata: [CITATION.cff](CITATION.cff). Mathematical and formal scope: [REVIEW.md](REVIEW.md).

Use the version DOI when citing this version. The all-version DOI resolves to the latest
published version. A later change to `main` does not alter the fixed release or DOI files.

## Changes from 1.0.0

1. The six-dimensional relative Moser paragraph now uses the compact support bound
   `‖X‖² ≤ 6`: the correction has `|X₀|² ≤ 2` and `‖X′‖² ≤ 4`. The Lean support bound was already 6.
2. Rational auxiliary capacities are obtained by density in a nonempty real open set,
   after a sufficiently small positive increase in each coordinate.
3. The formalisation appendix records the existing compact swept support set and its
   containment in the explicit support ball.
4. The verification guide states that default CI does not request fresh kernel replay;
   the manual `full-build` and `kernel-replay` workflows do.
5. The scalar comparator's opening comment identifies the fixed mollifier construction,
   separately from the general polyhedral log-sum-exp construction.

No Lean definition, theorem statement or proof changed. The optional project cache and
verification receipts are regenerated for the new raw source digest; the old receipt is
not reused as evidence for this version. Release packaging runs the source checks,
Lean build, axiom/explicitness/independence audits, regression tests, both paper builds,
and a fresh kernel replay bound to the current proof sources and compiled objects.
Default CI remains a separate check and does not itself imply fresh kernel replay.

## Checking this release

The matching GitHub and Zenodo downloads contain `main.pdf`, `supplement.pdf`,
`symplectic-ball-packing-1.0.1.zip`, `verification.json`, `PUBLICATION-PROVENANCE.json`,
and `SHA256SUMS`. The ZIP contains the history-free public sources and PDFs,
`RELEASE-VERIFICATION.json`, `KERNEL-REPLAY.json` and `MANIFEST.sha256`.
It excludes Git history and optional binary proof caches.

After downloading the six deposited files into one directory, run:

```sh
shasum -a 256 -c SHA256SUMS
```

Inside the extracted ZIP, run the same command with `MANIFEST.sha256`.
The external `PUBLICATION-PROVENANCE.json` binds the release commit and Git tree to the
file hashes and proof-verification receipt. Keeping it outside the Git tree and ZIP
avoids a self-referential commit or archive hash. GitHub and Zenodo must serve the same
bytes as the checksum manifest.

A source-cache hit alone does not re-check a proof. The archived kernel-replay receipt
records a separate replay of the imported declaration closure into a fresh Lean kernel.
The receipt identifies the exact source and compiled-object digests and pinned toolchain;
it is not evidence that a later working tree was checked.

## Original 1.0.0 archive and compatibility links

The original [version DOI](https://doi.org/10.5281/zenodo.23756576) and its seven files
remain unchanged. Its former GitHub release page and tag were removed after a Git
committer-identity correction. The corrected publication commit
[`baf33f27ba2d4eae32dcae795d5c9a79a39ad368`](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/baf33f27ba2d4eae32dcae795d5c9a79a39ad368)
has the same original file tree, `7d20dc4221190aecf89b3dff49e674db750f8f9c`.
The compatibility **branch** `v1.0.0` preserves previously shared
[source-file links](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.0/REVIEW.md);
it is not a release tag. For the corrected manuscript use 1.0.1 instead.

The original archive's provenance file identifies its original commit, and its
OpenTimestamps proof applies only to that original provenance file. A calendar
acknowledgment is pending evidence until anchored in Bitcoin; a Git commit date alone
is not an independent timestamp. No new OpenTimestamps claim is made for 1.0.1.
Zenodo creation/publication times and GitHub release times are service records.
Any Software Heritage archive is a separate historical record; a save request does
not confirm a completed archive visit.

These records identify deposited content and document its existence by a particular
time. They do not independently establish authorship, mathematical correctness or
novelty. Lean verification and human review of the paper-to-formal-statement
correspondence have the separate roles described in the reviewer guide.
