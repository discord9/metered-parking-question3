"""Bounded candidate finite verification, not an all-length proof or novelty audit."""
import itertools
import json
import sys
from math import comb
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE_DIR))

from definition_check import reference_simulator, replay_simulator


EXPECTED_PATH = Path(__file__).resolve().parent / "expected.json"
OUTPUT_PATH = BASE_DIR / "generated" / "one-meter" / "one-meter-scalar-results.json"


def choose(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def scalar_counts(n, bound):
    # [x^m] D_n G_n = [x^m] (1+x)^n, including the numerator boundary.
    c = {j: n * choose(n, j - 1) - choose(n, j) - choose(n, j - 2)
         for j in range(2, n + 1)}
    counts = []
    for m in range(bound + 1):
        counts.append(choose(n, m) + sum(c[j] * counts[m - j]
                                       for j in c if j <= m))
    return counts


records = []
total_inputs = 0
for n in range(1, 6):
    expected = scalar_counts(n, 8)
    for m in range(9):
        actual = 0
        for alpha in itertools.product(range(1, n + 1), repeat=m):
            a = reference_simulator(alpha, 1, n)
            b = replay_simulator(alpha, 1, n)
            assert a == b, (n, m, alpha, a, b)
            actual += a[0] is not None
            total_inputs += 1
        assert actual == expected[m], (n, m, actual, expected[m])
        records.append({"n": n, "m": m, "count": actual,
                        "input_lists": n ** m})

state_checks = []
for n in range(1, 21):
    scalar = scalar_counts(n, 40)
    z = [1] * n
    counts = [1, n]
    for m in range(2, 41):
        previous = sum(z)
        z = [previous - z[j] + (z[j - 1] if j else 0) for j in range(n)]
        counts.append(sum(z))
    assert counts == scalar, (n, counts, scalar)
    assert all(counts[m] == n * counts[m - 1] - counts[m - 2]
               for m in range(2, n + 2)), n
    assert counts[n + 2] == n * counts[n + 1] - counts[n] + 1, n
    state_checks.append({"n": n, "counts_m0_to40": counts})

result = {"finite_only": True,
          "scope": "candidate feasibility diagnostic; not proof or novelty",
          "definition_bounds": {"n": [1, 5], "m": [0, 8], "t": 1},
          "total_preference_inputs": total_inputs,
          "definition_rows": records, "state_vs_scalar_rows": state_checks}
output = json.dumps(result, indent=2) + "\n"
OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
OUTPUT_PATH.write_text(output, encoding="utf-8")
if output.encode("utf-8") != EXPECTED_PATH.read_bytes():
    print("FAIL: finite verification result differs from expected.json.",
          file=sys.stderr)
    sys.exit(1)
print(f"PASS: {total_inputs} ordered inputs, {len(records)} definition rows; "
      f"state/scalar checks n=1..20,m=0..40. Finite verification only.")
