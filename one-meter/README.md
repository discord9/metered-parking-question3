# One-meter parking at every car length

This release contains the ordinary note and its companion Lean formalization:
[paper (PDF)](main.pdf), [paper (Markdown)](main.md), [paper (TeX)](main.tex),
[root `Main.lean`](../Main.lean),
[Lean acceptance record](../verification/one-meter/LEAN.md), and
[literature audit](../literature/one-meter_literature_audit_2026-09-13.md).

## Scope and status

For every $n\geq1$ and any arrival count $m$, cars have meter duration $t=1$;
the previous car departs after the new car parks, so parking spaces can be
reused.  It counts all successful ordered preference lists, not a fixed lucky-count
stratum or a set of distinct outcome sequences.  It gives the generating function, explicit scalar recurrence, first
correction, and the $n=1,2$ boundary cases.

The root `Main.lean` formalization is complete. A fresh standalone build,
strict checking, consumer import, and single-thread same-Lean-kernel replay
all passed; the linked verification record contains the observed output. The
ordinary note uses its $q$/geometric-sum proof, while Lean proves the same
claims by division-free finite-state elimination. This is not a claim of
novelty, independent-kernel certification, or external human peer review.

## Reproduction and finite checks

From the repository root, run:

```sh
python3 verification/one-meter/check_counts.py
lake build
lake env lean -DwarningAsError=true Main.lean
lake env lean -DwarningAsError=true --stdin < verification/one-meter/consumer-check.txt
LEAN_NUM_THREADS=1 lake env leanchecker -v Main
```

The finite Python check covers the intended semantics for 586023 inputs and
45 count rows, plus state/scalar values for $n=1,\ldots,20$ and
$m=0,\ldots,40$; finite checks are not a proof.  Read cache and pin guidance
in the root README; do not run `lake update`.

To rebuild the paper, run the following from the repository root:

```sh
cd one-meter
tectonic --untrusted --keep-logs --keep-intermediates --reruns 2 main.tex
```

Tectonic may download public TeX resources on its first run. No TeX installation
is needed for the Lean or finite checks.
