# One-meter parking: complete formalization and observed verification

The separate [`Main.lean`](../../Main.lean) module proves the all-car-count one-meter result for the **original successful ordered-preference count**. The existing Question 3 module [`AiMathLab.lean`](../../AiMathLab.lean), its manuscript and the dependency pins are unchanged.

## Count and statement correspondence

The public count is defined directly, not recursively:

```lean
MeteredParking.OneMeter.Successful m n :=
  {a : Fin m → Fin n // ∃ p : Fin m → Fin n, MeteredParking.IsParking 1 a p}

MeteredParking.OneMeter.totalCount m n :=
  Fintype.card (MeteredParking.OneMeter.Successful m n)
```

Here `m` is the number of arriving cars and `n` the number of spaces. Zero-based `Fin` labels correspond to external labels `val+1`. The previous car remains during the new search and departs **after** the new car parks. The original predicate checks every skipped physical spot and permits reuse after departure. No lucky-count restriction, global outcome injectivity or relation between `m` and `n` is imposed on the count.

`generatingSeries n : PowerSeries ℤ` has coefficient `m` equal to `(totalCount m n : ℤ)`. The one polynomial denominator is

```lean
(1 - Polynomial.C (n : ℤ) * Polynomial.X + Polynomial.X ^ 2) *
  (1 + Polynomial.X) ^ n - Polynomial.X ^ (n + 2)
```

Theorems `generatingSeries_mul_denominator` and `generatingSeries_eq_quotient` prove, for every natural `n`,

\[
D_nG_n=(1+X)^n,\qquad
G_n=(1+X)^n\operatorname{invOfUnit}(D_n,1).
\]

`denominator_constantCoeff` proves the inverse's required constant coefficient is one. This is a genuine quotient in integer formal series, not field division or an analytic-convergence statement.

The explicit coefficient definition is

```lean
recurrenceCoeff (n j : ℕ) : ℤ :=
  (n : ℤ) * (Nat.choose n (j - 1) : ℤ) -
    (Nat.choose n j : ℤ) - (Nat.choose n (j - 2) : ℤ)
```

Its denominator interpretation is used only for `2≤j≤n`. The complete scalar theorem has exactly these hypotheses and conclusion:

```lean
MeteredParking.OneMeter.totalCount_recurrence :
  ∀ n m : ℕ, 1 ≤ n → n + 1 ≤ m →
    (MeteredParking.OneMeter.totalCount m n : ℤ) =
      Finset.sum ((Finset.range (n + 1)).filter (fun j => 2 ≤ j))
        (fun j => MeteredParking.OneMeter.recurrenceCoeff n j *
          (MeteredParking.OneMeter.totalCount (m - j) n : ℤ))
```

The filtered range is precisely `{2,...,n}`. The homogeneous recurrence starts at `m=n+1`, not `m=n`, where the numerator still has coefficient one. The other public endpoints establish:

| Theorem in `MeteredParking.OneMeter` | Conclusion |
|---|---|
| `totalCount_zero` | `F₀(n)=1` |
| `totalCount_one` | `F₁(n)=n` |
| `totalCount_lucas` | `F_m=nF_(m−1)−F_(m−2)` for `n≥1, 2≤m≤n+1` |
| `totalCount_firstCorrection` | `F_(n+2)=nF_(n+1)−F_n+1` for `n≥1` |
| `totalCount_capacity_one` | `F_m(1)=0` for `m≥2` |
| `totalCount_capacity_two` | `F_m(2)=2F_(m−2)(2)` for `m≥3` |
| `totalCount_two_two` | `F₂(2)=3` |

These are actual natural counts, with integer casts where subtraction is required. The base counts and bounded Lucas relation provide sufficient initial values. The ten full types are checked in the source and again by the [import-level consumer](consumer-check.txt). **No final theorem assumes a GF identity, transition recurrence, counting decomposition or equivalence supplied by the caller.** The Question 3 theorem's capacity threshold is not used to replace an arbitrary-length argument.

## Proof route

1. Define one auxiliary type of successful preference/outcome histories. Forgetting outcomes is a proved equivalence with successful preferences, using the original uniqueness theorem.
2. Prove exact nonempty-prefix extension semantics for timer one. A destination following the occupied spot can arise from two distinct appended preferences; the tagged extension equivalence preserves both.
3. Partition histories by their last outcome. Prove singleton one-car fibers, predecessor endpoints and the additive natural-cardinality balance. Establish the complement bound before cancelling truncated subtraction.
4. Construct the actual-count series and one bounded state-series function. Its virtual zero is the zero series, not a fabricated last outcome for an empty history. Coefficientwise equations come from the proved cardinalities.
5. Sum finite state equations and induct over bounded state indices to eliminate the final state without intermediate inverses. Obtain the exact polynomial denominator identity and its constant-one unit-inverse solution.
6. Expand that denominator as a finite monomial sum, checking degrees zero, one, `n+1`, `n+2` and the tail. Extract coefficients by guarded monomial shifts for the scalar recurrence.
7. A local inverse of `(1+X)^n` produces a residual with constant coefficient one. Its coefficients give the Lucas range and exact first correction. Capacity-one/two results are small specializations.

The [ordinary note](../../one-meter/main.md) uses a weighted geometric-sum presentation. Lean proves the same conclusions by division-free finite-state elimination; it is not a line-by-line formalization of that presentation. No minimal-order, coefficient-positivity or larger-meter result is claimed.

## Reproduce

From the repository root, after installing elan:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true --stdin < verification/one-meter/consumer-check.txt
LEAN_NUM_THREADS=1 lake env leanchecker -v Main
python3 verification/one-meter/check_counts.py
```

Lean is pinned to **4.31.0**, Lake is **5.0.0**, and mathlib is pinned to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, with every transitive revision in `lake-manifest.json`. Cache setup requires internet access; after the pinned dependencies are present, proof checks need no solver service, private repository or local path override. **Do not run `lake update`** to reproduce this snapshot.

`lake build` checks both libraries. To repeat the preserved Question 3 checks as well:

```sh
lake env lean -DwarningAsError=true AiMathLab.lean
lake env lean -DwarningAsError=true --stdin < verification/consumer-check.txt
LEAN_NUM_THREADS=1 lake env leanchecker -v AiMathLab
python3 verification/run_checks.py
```

## Actual standalone execution

The release was checked in a network-disabled Linux sandbox containing the standalone project, pinned Lean and public upstream dependencies/caches at the locked revisions. The private research repository was **not mounted**. There were **no preexisting project oleans**: the release freshly compiled both project modules. This does not claim that dependency downloads were performed in that offline run.

All ordinary check commands below exited zero:

| Check | Raw observed output |
|---|---|
| Default build of both libraries | [lean-build.txt](observed/lean-build.txt) |
| Strict Main check | [lean-one-meter-strict.txt](observed/lean-one-meter-strict.txt) |
| Main consumer import, ten full types | [lean-one-meter-consumer.txt](observed/lean-one-meter-consumer.txt) |
| Single-thread Main replay | [lean-one-meter-replay.txt](observed/lean-one-meter-replay.txt) |
| Strict Question 3 check | [lean-question3-strict.txt](observed/lean-question3-strict.txt) |
| Question 3 consumer import | [lean-question3-consumer.txt](observed/lean-question3-consumer.txt) |
| Single-thread Question 3 replay | [lean-question3-replay.txt](observed/lean-question3-replay.txt) |
| One-meter finite check | [finite-one-meter.txt](observed/finite-one-meter.txt) |
| One-meter check from another working directory | [finite-other-cwd.txt](observed/finite-other-cwd.txt) |
| Preserved Question 3 finite checks and mutations | [finite-question3.txt](observed/finite-question3.txt) |
| New note typesetting | [paper-typeset.txt](observed/paper-typeset.txt) |

The Main strict and consumer runs each emitted **32** name-matched axiom reports: **30** standard-only and **2** empty. The fresh combined build emitted **167**: **163** standard-only and **4** empty. All ten consumer theorem types matched. Lean runs emitted no warnings/errors or `sorryAx`, and their stderr streams were empty. Both project source and olean hashes remained unchanged during consumer checks and replay. [results.json](observed/results.json) records statuses, hashes and isolation boundaries. Olean byte identity across different machines is not required; reproducing the checks is the substantive test.

The separate four-page PDF was regenerated with Tectonic 0.15.0 in untrusted, network-disabled mode using cached public resources, with no warnings or stderr. All four rendered pages were inspected for missing content, clipped formulas and overlap. The original Question 3 paper was not rebuilt or changed.

## Finite checks and failure detection

The standard-library-only checker imports the existing two definition simulators. It enumerates **586,023** ordered inputs for `n=1..5,m=0..8,t=1` and obtains **45** count rows. A separate state/scalar comparison covers `n=1..20,m=0..40`, including the bounded Lucas range and first correction. The entire generated JSON must match [expected.json](expected.json) byte-for-byte.

Output is written under `verification/generated/one-meter/`; the shipped expected file is never overwritten. Script-relative paths also work when invoked by absolute path from another working directory. A deliberately altered expected-file copy was separately mounted for a failure-path test: the checker returned **exit 1** and the exact [mismatch message](observed/finite-expected-mismatch.txt), while the shipped reference remained unchanged. This expected failure is not a failed proof check.

The retained JSON's historical `scope` label describes its origin as a feasibility diagnostic. Its finite bounds and mathematical data are unchanged. These finite computations are **not the all-parameter proof, a premise of the Lean proof, or evidence of novelty**.

## Trust, disclosure and continuity

All new final theorems depend only on the standard foundations:

```text
[propext, Classical.choice, Quot.sound]
```

There are no custom axioms, placeholders, `native_decide`, unsafe/IO implementations or executable elaborators/macros in the project proof source. `leanchecker` replays declarations using the **same pinned Lean kernel**, not an independently implemented kernel. Internal AI mathematical/source/deletion review is not external human peer review; readers should inspect the ordinary arguments and checked terms directly.

`Main.lean` is a theorem library, not an executable. Its sole import is the unchanged `AiMathLab` module. Adding it to the default library targets is the only build-configuration change; the old Question 3 proof, manuscript and dependency pins are preserved. No private Git history, internal review transcripts, unrelated conjectures or dependency caches are included. See the [bounded literature audit](../../literature/one-meter_literature_audit_2026-09-13.md) for the separate limits on attribution and priority.
