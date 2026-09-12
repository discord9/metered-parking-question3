# Third-party notices and license status

## Original project material

No general reuse license has yet been selected for this repository's original mathematical manuscript, Lean proof, verification scripts or explanatory text. Public visibility is not itself a broad reuse-license grant. No author identity, copyright assignment or blanket open-source license is inferred from publication.

The original material was developed with AI assistance. The repository maintainer does not present internal AI reviews as mathematical authority or as outside human peer review.

## Build dependencies

The Lean file imports mathlib and is checked with the toolchain and dependency revisions recorded in `lean-toolchain`, `lake-manifest.json` and `VERSIONS.json`. Dependency source, compiled caches, executables and license files are **not vendored** in this repository. They are obtained from the public upstream repositories during setup and retain their respective licenses and notices.

- Lean: https://github.com/leanprover/lean4 — Apache License 2.0; see its upstream `LICENSE` and notices.
- mathlib: https://github.com/leanprover-community/mathlib4 — Apache License 2.0; see its upstream `LICENSE` and source notices.
- Transitive dependency URLs and exact commits are preserved in `lake-manifest.json`. Consult each upstream revision for its license.

The proof invokes existing public library declarations; it does not redistribute the library sources. The independent verification scripts use Python's standard library only.

## Source question and literature

The original question is attributed to Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, _Metered Parking Functions_, **Integers 25** (2025), A73, Question 3, p. 32. The original article is linked, not redistributed:

https://math.colgate.edu/~integers/z73/z73.pdf

Other cited works remain the property of their respective authors. The literature audit records a bounded search and unresolved access limitations; it does not establish priority or the absence of earlier answers.

## Typesetting

The included PDF was generated from the supplied TeX source using Tectonic 0.15.0 and standard TeX packages. Neither Tectonic nor its package/font cache is distributed here. Tectonic and the individual TeX resources retain their upstream licenses; the PDF metadata identifies the actual producer.
