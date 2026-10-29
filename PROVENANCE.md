# Final publication and provenance

Liang Song, *Explicit Hamiltonian ball packings in every dimension*, version **1.0.0**,
29 October 2026. The archive includes the manuscript, supplement and Lean development.

- Version DOI: [10.5281/zenodo.23756576](https://doi.org/10.5281/zenodo.23756576).
- Deposited files and repository metadata: [Zenodo record](https://zenodo.org/records/23756576).
- Fixed source tree: [identity-corrected publication commit](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/baf33f27ba2d4eae32dcae795d5c9a79a39ad368).
- Fixed reviewer guide: [guide at the publication commit](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/baf33f27ba2d4eae32dcae795d5c9a79a39ad368/REVIEW.md).
- Citation metadata: [CITATION.cff](CITATION.cff). Mathematical and formal scope: [REVIEW.md](REVIEW.md).

Use the version DOI when citing this final version. The current `main` branch is a
convenient reading copy; the files deposited on Zenodo identify the fixed publication.
Git committer metadata was corrected on 29 October 2026, and the former GitHub release
and tag were removed. The correction to the publication commit preserved its file tree.
The archived provenance record identifies the original publication commit, rather than
the current `main` commit. Zenodo's creation/publication timestamps are service records.
A Git commit date alone is not an independent timestamp.

The compatibility branch `v1.0.0` preserves previously shared source-file links, including
the [reviewer guide](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.0/REVIEW.md).
It points to the identity-corrected publication commit
[`baf33f27ba2d4eae32dcae795d5c9a79a39ad368`](https://github.com/s-JoL/Symplectic-Ball-Packing/commit/baf33f27ba2d4eae32dcae795d5c9a79a39ad368),
whose tree is identical to the original publication tree. This branch is not a release tag.
The former GitHub release page is unavailable; use the version DOI above for the archived
publication files. The paper and formalisation have not changed.

Both the original publication commit and the identity-corrected commit have Git tree
`7d20dc4221190aecf89b3dff49e674db750f8f9c`. Later changes on `main` update access and
metadata documentation; the fixed commit above is the source reference for the DOI archive.
The archived README and provenance guide retain historical GitHub release links. Those
links have been superseded by the DOI and fixed-commit links on this page and in the
Zenodo record's access update; the archived files and their hashes have been preserved.

The Zenodo record contains the two PDFs, the verified source-and-PDF archive,
`verification.json`, `PUBLICATION-PROVENANCE.json`, `SHA256SUMS`, and an OpenTimestamps
proof `PUBLICATION-PROVENANCE.json.ots`. The provenance record binds the Git commit and
tree to the exact file digests and the proof-verification receipt. After downloading all
deposited files into one directory, check:

```sh
shasum -a 256 -c SHA256SUMS
```

The original Git identifiers are recorded in `PUBLICATION-PROVENANCE.json`. The archive also contains
`MANIFEST.sha256` for its own contents. The publication's external provenance files avoid
putting a self-referential commit hash inside the Git tree they identify.

For the independent timestamp, install the official
[OpenTimestamps client](https://github.com/opentimestamps/opentimestamps-client), then run:

```sh
ots upgrade PUBLICATION-PROVENANCE.json.ots
ots verify PUBLICATION-PROVENANCE.json.ots
```

A calendar acknowledgment is pending evidence until it has been anchored in Bitcoin.
Upgrading adds the later confirmation to a local copy of the proof; it does not change the
timestamped file. Full independent verification with this client requires a Bitcoin Core
node. The OpenTimestamps website also offers a verifier.

Any Software Heritage archive is a separate historical record. A save request is not
itself confirmation of a completed archive visit. Once archived, the Git commit determines
the revision identifier `swh:1:rev:<commit>`.

These records identify which content was publicly deposited and give evidence of its
existence by a particular time. They do not independently establish authorship,
mathematical correctness or novelty. Lean verification and the paper-to-formal-statement
review have the separate roles described in the reviewer guide.
