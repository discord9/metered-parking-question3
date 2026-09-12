# Metered Parking Question 3

**A uniform affirmative proof, with a Lean formalization, of the lucky-count polynomiality question in _Metered Parking Functions_.**

给定任意 `t ≥ 1`、`m ≥ 2`、`1 ≤ k ≤ m−1`，成功且恰有 `k` 辆 lucky 的有序偏好串计数，对**所有 `n ≥ m−1`**等于一个**次数恰为 `k`**的有理多项式。计时规则不变：**车辆 `j` 停妥之后，车辆 `j−t` 才离开**。

This repository contains a self-contained manuscript with two ordinary proofs, the complete primary proof formalized in Lean, and reproducible finite checks. It is a public research repository, **not a claim of journal acceptance, external human peer review, or a first solution**.

## Statement

There are `m` labelled cars arriving in order and `n` ordered parking spaces. A preference list is an ordered element of `[n]^m`. Each car parks at the first free space at or to the right of its preference, or fails if none exists. After car `j` successfully parks, car `j−t`, if present, leaves. A car is **lucky** when it parks at its preference. Spaces may be reused after departure.

For fixed `t ≥ 1`, `m ≥ 2`, and `1 ≤ k ≤ m−1`, let `a(t,m,k,n)` count successful preference lists with exactly `k` lucky cars. The result is

\[
\exists Q_{t,m,k}\in\mathbb Q[X],\qquad
\deg Q_{t,m,k}=k,\qquad
Q_{t,m,k}(n)=a(t,m,k,n)\quad\text{for every }n\ge m-1.
\]

There is no upper bound on `t`. The case `n=m−1`, including `m=2,n=1`, is included. The count is of **preference lists**, not distinct outcomes or history pairs. No recurrence, template bijection, embedding formula, or degree bound is assumed by the final theorem.

## Read the proofs

- [Paper PDF](paper/main.pdf), [Markdown](paper/main.md), [TeX source](paper/main.tex): the primary rank-template/gap proof, plus a complete independent collision inclusion–exclusion proof in Appendix A.
- [Lean source](AiMathLab.lean): theorem **`MeteredParking.question3`**. The root module retains the name `AiMathLab` for source continuity but contains only this problem; its only import is `Mathlib`.
- [Formalization and verification record](verification/LEAN.md): statement correspondence, trust assumptions, exact reproduction commands and observed results.
- [Finite verification](verification/README.md): independent definition enumeration, template generation, both inverse checks and targeted mutations.
- [Bounded literature audit](literature/question3_literature_audit_2026-09-12.md): checked sources and unresolved access/search limits.

The Lean proof follows the primary template route. It proves the dimension bound by a direct finite-set cover instead of introducing graph components. The independent inclusion–exclusion appendix is an ordinary proof; it is **not separately formalized** here.

## Reproduce the Lean check

Install [elan](https://github.com/leanprover/elan), then run from a clone of this repository:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true AiMathLab.lean
LEAN_NUM_THREADS=1 lake env leanchecker -v AiMathLab
```

`lean-toolchain` pins Lean **4.31.0**. `lake-manifest.json` pins mathlib to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` and records all transitive dependencies. The first command downloads public dependency caches and requires internet access. Once the pinned dependencies are present, checking the proof needs no solver service, private repository, or local path override. Do not run `lake update` to reproduce the checked snapshot.

The final declaration is:

```lean
MeteredParking.question3 (t m k : ℕ)
    (ht : 1 ≤ t) (hm : 2 ≤ m) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
  ∃ Q : Polynomial ℚ, Q.natDegree = k ∧
    ∀ n : ℕ, m - 1 ≤ n →
      Q.eval (n : ℚ) =
        (MeteredParking.countSuccessfulPreferences t m k n : ℚ)
```

Its axiom dependencies are the standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom, `sorry`, or `native_decide` is used. `leanchecker` replays declarations with the **same Lean kernel**, not a second independently implemented checker.

## Run the finite checks

Python 3.10 or later, standard library only:

```sh
python3 verification/run_checks.py
```

The runner works without Lean, Git or internet access. It creates `verification/generated/`, compares results byte-for-byte with `verification/expected/`, and requires the two intended mutation failures. It covers 1,139,145 definition-level inputs and 4,173 template-check inputs. These checks detect mistakes in the stated finite ranges; **they are not the all-parameter proof**.

## Build the manuscript

A ready-to-read PDF is included. With Tectonic installed:

```sh
cd paper
tectonic --untrusted --keep-logs --keep-intermediates --reruns 2 main.tex
```

The manuscript uses standard article/AMS packages, without shell escape or external figures. The checked typesetter is Tectonic 0.15.0; its first run may need to download TeX resources. No TeX installation is required to run the finite or Lean checks.

## Integrity, scope and disclosure

```sh
sha256sum -c SHA256SUMS
```

[VERSIONS.json](VERSIONS.json) identifies the toolchain, dependencies and source hashes. This repository starts with a new topic-only Git history. Internal review transcripts, research task IDs, unrelated conjectures, private Git history, credentials, local path overrides and dependency caches are excluded.

The proofs, formalization and manuscript were developed with AI assistance. Internal AI review is not offered as mathematical authority; the ordinary arguments and Lean terms are available for inspection. No external human peer-review verdict is claimed. The bounded literature audit does not prove the absence of unpublished, unindexed or inaccessible prior results, and formal verification does not establish novelty.

### Source question

Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, _Metered Parking Functions_, **Integers 25** (2025), A73, Question 3, p. 32.

[Journal PDF](https://math.colgate.edu/~integers/z73/z73.pdf) · [arXiv:2406.12941](https://arxiv.org/abs/2406.12941) · [DOI](https://doi.org/10.5281/zenodo.16881806)

### License status

No general reuse license has yet been selected for this project's original manuscript, proof code or explanatory material. Public visibility alone is not a broad reuse-license grant. Dependencies retain their respective licenses; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). No original-paper PDF or dependency source is redistributed here.
