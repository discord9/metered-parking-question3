# Lean formalization and observed verification

The complete primary theorem is formalized as **`MeteredParking.question3`** in [`../AiMathLab.lean`](../AiMathLab.lean). It proves the original statement without hypotheses supplying a recurrence, template equivalence, embedding formula or degree bound.

```lean
∀ (t m k : ℕ), 1 ≤ t → 2 ≤ m → 1 ≤ k → k ≤ m - 1 →
  ∃ Q : Polynomial ℚ, Q.natDegree = k ∧
    ∀ n : ℕ, m - 1 ≤ n →
      Q.eval (n : ℚ) =
        (MeteredParking.countSuccessfulPreferences t m k n : ℚ)
```

The type is explicitly checked at the end of the source. The final polynomial has a positive coefficient at degree `k`; since `k≥1`, `natDegree=k` expresses the usual exact degree rather than the zero polynomial convention.

## Definition correspondence

Cars and spaces use zero-based `Fin` labels, corresponding to external labels `val + 1`. `Active` includes temporal distance exactly `t`: the expiring car is present until **after** the arriving car parks. `IsParking` directly requires preference ≤ destination, a free destination, and an active earlier occupant at **every skipped physical integer spot**. It permits later reuse of a space.

Outcomes are proved unique for each preference list. The count filters the finite type `Fin m → Fin n`, so it counts ordered preference lists, not outcomes or preference/history pairs. `luckyCount` counts the original car indices.

## Proof outline and boundaries

1. Canonically rank all distinct outcomes. Prove preferences have ranks, retain repeated outcomes, and derive unit spacing only on edges actually traversed by a car.
2. Inflate legal rank data into the original physical first-free process, covering every skipped integer, and prove the preference/template-embedding equivalence.
3. Extract both endpoint gaps and all internal gaps, prove both inverse identities, and count free gap vectors through mathlib's symmetric-power/weak-composition equivalence.
4. Prove the dimension `c=r−|E|` is at most `k` by a finite cover of the ranks, and construct an actual dimension-`k` template for every allowed `t,m,k`.
5. Sum rationally shifted descending Pochhammer polynomials, divided by factorials. At the only undersized case `n=r−1`, use the rational root `c−1`, **not** a truncated natural `n−r+c`. An actual top-dimensional template makes coefficient `k` positive; lower coefficients are not assumed nonnegative.

The manuscript's primary proof uses the equivalent least-car-in-each-component argument for the dimension bound. The formal proof avoids a separate graph representation. Appendix A's independent inclusion–exclusion proof has not been separately formalized. Its integer-coefficient corollary in A.4 is likewise an ordinary result, not a separate Lean theorem: `MeteredParking.question3` continues to quantify over `Polynomial ℚ`. The manuscript additions do not change the Lean source or the pinned configuration checked below.

## Pinned reproduction

From the repository root, after installing elan:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true AiMathLab.lean
LEAN_NUM_THREADS=1 lake env leanchecker -v AiMathLab
```

The toolchain is Lean **4.31.0** and Lake **5.0.0**. The checked dependency lock pins mathlib to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` and fixes its transitive dependencies. No private repository, custom package path override, external solver, generated source file or network service is needed to check the proof once these public dependencies are present. Initial dependency/cache downloads require internet access. Do not update the lock for reproduction.

## Actual standalone validation

The public source was checked in a Linux sandbox containing only this standalone project, standard system runtime and the pinned Lean toolchain. The private research repository was **not mounted**, the network was disabled, and no local package override was used. Public upstream dependency sources and caches were prepopulated at exactly the locked revisions; the project had **no preexisting project olean**, and compiled its own source. This verifies independence from the private project but is not a claim that fresh dependency downloads were performed in that offline run.

All these commands actually exited zero:

| Command | Raw observed output |
|---|---|
| `lake build` | [`observed/lean-build.txt`](observed/lean-build.txt) |
| `lake env lean -DwarningAsError=true AiMathLab.lean` | [`observed/lean-strict.txt`](observed/lean-strict.txt) |
| `LEAN_NUM_THREADS=1 lake env leanchecker -v AiMathLab` | [`observed/lean-replay.txt`](observed/lean-replay.txt) |
| `python3 verification/run_checks.py` | [`observed/finite-checks.txt`](observed/finite-checks.txt) |

The standalone project build and strict check emitted no warnings. The Python run was separately isolated without Lean, Git, the private repository or network access; it matched both reference JSON files byte-for-byte and passed both exact mutation checks. The shipped expected files were unchanged.

[`observed/results.json`](observed/results.json) records the execution statuses, source and olean hashes, and isolation limitations. The compiled olean hash did not change during replay. A matching local olean hash is not required for verification on a different platform or build path; rerunning the checked commands is the substantive test.

## Trust and review limits

The final theorem's printed dependencies are:

```text
[propext, Classical.choice, Quot.sound]
```

All **76** printed `MeteredParking` dependency lists were inspected and are standard-only or empty. There is no custom axiom, `sorry`, `admit`, `native_decide`, unsafe/IO implementation, or executable elaborator/macro in the proof source. The closed `by decide` arithmetic proof is ordinary kernel-checked decision.

`leanchecker` replays this module's declarations with the **same Lean kernel**. Its success is an additional artifact/replay check, not independent-kernel certification. Internal AI source reviews checked statement correspondence and proof structure, but are not supplied as mathematical authority or as external human peer review. The ordinary arguments and Lean source must be judged directly.

The all-parameter theorem is not inferred from finite computation. Formal verification does not establish mathematical novelty or publication priority. See the manuscript and bounded literature report for those separate limitations.

## Source continuity

The accepted topic-specific Lean declarations, proof terms, comments and inspection commands were preserved byte-for-byte when preparing this repository. Only the old unrelated import/diagnostic prefix was replaced with `import Mathlib`. The public source is 1,547 lines and contains only `MeteredParking` material. The standalone build, strict check and replay above apply to this extracted source, not merely to its earlier research version.

No private Git history, other conjectures, dependency caches or internal review transcripts are included. The root module retains its original `AiMathLab` name to avoid unnecessary source churn; it imports only public mathlib.
