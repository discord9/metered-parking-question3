# Portable finite verification

Requires Python3.10 or later with its standard library only. No original repository, Git, Lean, internet access or external Python package is required.

From the repository root:

```bash
python3 verification/run_checks.py
```

The runner locates files relative to itself, so invocation from another current directory also works. Generated results, mutation logs and bytecode go under `verification/generated/`; the shipped `expected/` files are not overwritten. A custom `--output-dir` resolving to `expected/` or a directory beneath it, including through a symlink, is rejected before any output is written.

## Contents

- `definition_check.py`: the reviewed two-simulator exhaustive definition check, with unchanged mathematical logic and finite window.
- `template_check.py`: the reviewed independent-template/embedding and two-way correspondence check. Only the import location is adapted to its sibling definition checker; no original-workspace lookup remains.
- `run_checks.py`: runs both checkers, compares normal outputs byte for byte to the shipped reference JSON, checks substantive totals and records the two expected mutation failures.
- `expected/definition_result.json`: raw82 rows,40 finite-difference arrays and fixtures from the original observed run;1,139,145 preference comparisons.
- `expected/template_result.json`: all1,737 pairs,367 template records and1,101 embedding count comparisons from the original observed run;4,173 direct input lists.

## What is checked

The definition check enumerates every ordered preference list for m=2,...,5, t=1,...,m, n=m−1,...,2m. One simulator reconstructs active occupancy from the latest t recorded outcomes; the other maintains mutable occupancy and removes the old car after the arriving car parks. Whole outcomes and lucky counts must agree. The program records finite differences, not a numerical interpolation proposed as proof.

The template check uses m=2,...,4, t=1,...,m, n=m−1,m,m+1, k=1,...,m−1. One side enumerates actual successful preferences; the other generates T1 templates directly, followed by increasing embeddings. It checks both full-history round trips, multiplicity-one counters and per-template binomial counts. The ranking helper assumes its supplied history has already successfully replayed; all exercised callers meet this condition.

The small traversal-edge helper is shared by template-side routines, so it is not claimed as two independent edge classifiers. The literal `113 -> 123` case and the normalizer-only mutation separately distinguish forced traversal edges from unforced physical unit gaps.

## Mutation checks

1. Wrongly move departure to before parking. The expected first mismatch is t=1,m=2,n=1,preferences11: actual process fails, erroneous replay parks both at1.
2. Wrongly force all physically unit gaps. The expected mismatch is t=1,m=3,n=3,preferences113: true forced edges[1], erroneous edges[1,2].

The runner requires these exact failures; an unrelated exception or a mutation that passes is an error.

## Limits

These finite runs support the stated algorithms and examples, not the theorem for every parameter. The complete ordinary arguments are in `../paper/`; the primary all-parameter theorem is also formalized as `MeteredParking.question3` in `../AiMathLab.lean`. See `LEAN.md` for the pinned environment, commands and verification record. Collision inclusion–exclusion and optional leading-coefficient compatibility are not separately executed or formalized here.
