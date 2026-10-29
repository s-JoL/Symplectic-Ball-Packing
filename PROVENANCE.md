# Final publication and provenance

Liang Song, *Explicit Hamiltonian ball packings in every dimension*, version **1.0.0**,
29 October 2026. The archive includes the manuscript, supplement and Lean development.

- Version DOI: [10.5281/zenodo.23756576](https://doi.org/10.5281/zenodo.23756576).
- Deposited files and repository metadata: [Zenodo record](https://zenodo.org/records/23756576).
- Citation metadata: [CITATION.cff](CITATION.cff). Mathematical and formal scope: [REVIEW.md](REVIEW.md).

Use the version DOI when citing this final version. The current `main` branch is a
convenient reading copy; the files deposited on Zenodo identify the fixed publication.
Git committer metadata was corrected on 29 October 2026, and the former GitHub release
and tag were removed. The correction to the publication commit preserved its file tree.
The archived provenance record identifies the original publication commit, rather than
the current `main` commit. Zenodo's creation/publication timestamps are service records.
A Git commit date alone is not an independent timestamp.

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
