"""Bounded definition-level checker for metered parking; not a proof or formula."""

import itertools
import json
import sys


# This switch exists only so the archived mutation command can check departure
# timing.  The normal checker always uses False.
EARLY_DEPARTURE = False


def reference_simulator(alpha, t, n):
    """Reconstruct active cars directly from the saved ordered outcomes."""
    outcomes = []
    lucky = 0
    for preference in alpha:
        occupied = set(outcomes[-t:])
        place = preference
        while place in occupied:
            place += 1
        if place > n:
            return None, lucky
        outcomes.append(place)
        if place == preference:
            lucky += 1
    return tuple(outcomes), lucky


def replay_simulator(alpha, t, n):
    """Independent mutable-occupancy replay of the arrival/departure timeline."""
    occupancy = set()
    outcomes = []
    lucky = 0
    for j, preference in enumerate(alpha):
        if EARLY_DEPARTURE and j >= t:
            occupancy.remove(outcomes[j - t])

        place = preference
        while place in occupancy:
            place += 1
        if place > n:
            return None, lucky
        occupancy.add(place)
        outcomes.append(place)
        if place == preference:
            lucky += 1

        if not EARLY_DEPARTURE and j >= t:
            # The departing car was still occupied while this car searched, so
            # its place cannot be this newly parked car's place.
            occupancy.remove(outcomes[j - t])
    return tuple(outcomes), lucky


def result(ok, name=None, params=None, expected=None, actual=None,
           counts=None, fixtures=None, total_preference_checks=0,
           finite_differences=None):
    return {
        "ok": ok,
        "name": name,
        "params": params,
        "expected": expected,
        "actual": actual,
        "rawcounts": counts if counts is not None else [],
        "fixtures": fixtures if fixtures is not None else [],
        "total_preference_checks": total_preference_checks,
        "finite_differences": (
            finite_differences if finite_differences is not None else []
        ),
        "bounds": {"m": [2, 5], "t": "1..m inclusive",
                   "n": "m-1..2*m inclusive",
                   "difference_k": "1..m-1 inclusive"},
        "finite_only": True,
        "scope": "bounded finite definition check only; not a polynomial proof",
    }


def as_json_value(outcomes):
    return None if outcomes is None else list(outcomes)


def forward_differences(values, order):
    current = list(values)
    for _ in range(order):
        current = [right - left for left, right in zip(current, current[1:])]
    return current


def run_fixtures():
    records = []
    literal = (
        (1, 3, 2, (1, 1, 1), (1, 2, 1), 2),
        (1, 3, 2, (1, 1, 2), None, 1),
        (1, 2, 1, (1, 1), None, 1),
    )
    for t, m, n, alpha, expected_outcomes, expected_lucky in literal:
        actual_outcomes, actual_lucky = reference_simulator(alpha, t, n)
        record = {
            "t": t,
            "m": m,
            "n": n,
            "alpha": list(alpha),
            "expected_outcomes": as_json_value(expected_outcomes),
            "actual_outcomes": as_json_value(actual_outcomes),
            "expected_lucky": expected_lucky,
            "actual_lucky": actual_lucky,
        }
        records.append(record)
        if (actual_outcomes, actual_lucky) != (expected_outcomes, expected_lucky):
            return records, result(
                False, "Literal fixture", {"t": t, "m": m, "n": n,
                                             "alpha": list(alpha)},
                {"outcomes": as_json_value(expected_outcomes),
                 "lucky": expected_lucky},
                {"outcomes": as_json_value(actual_outcomes),
                 "lucky": actual_lucky}, fixtures=records)

    t, m, n = 2, 3, 2
    outcomes = []
    for alpha in itertools.product(range(1, n + 1), repeat=m):
        actual_outcomes, actual_lucky = reference_simulator(alpha, t, n)
        outcomes.append({"alpha": list(alpha),
                         "outcomes": as_json_value(actual_outcomes),
                         "lucky": actual_lucky})
        if actual_outcomes is not None:
            records.append({"t": t, "m": m, "n": n,
                            "all_fail_outcomes": outcomes})
            return records, result(
                False, "Literal fixture", {"t": t, "m": m, "n": n},
                "all preference lists fail", outcomes, fixtures=records)
    records.append({"t": t, "m": m, "n": n,
                    "all_fail_outcomes": outcomes})
    return records, None


def main():
    counts = []
    total_preference_checks = 0
    rows_by_tm = {}

    # This order deliberately starts with (m, t, n) = (2, 1, 1).
    for m in range(2, 6):
        for t in range(1, m + 1):
            rows = []
            rows_by_tm[(t, m)] = rows
            for n in range(m - 1, 2 * m + 1):
                successes = [0] * (m + 1)
                failed = 0
                fullinputs = 0
                for alpha in itertools.product(range(1, n + 1), repeat=m):
                    fullinputs += 1
                    total_preference_checks += 1
                    reference_outcomes, reference_lucky = reference_simulator(
                        alpha, t, n)
                    replay_outcomes, replay_lucky = replay_simulator(alpha, t, n)
                    if reference_outcomes != replay_outcomes:
                        return result(
                            False, "Departure timing replay",
                            {"t": t, "m": m, "n": n, "alpha": list(alpha)},
                            as_json_value(reference_outcomes),
                            as_json_value(replay_outcomes), counts,
                            total_preference_checks=total_preference_checks)
                    if reference_lucky != replay_lucky:
                        return result(
                            False, "Lucky-number replay",
                            {"t": t, "m": m, "n": n, "alpha": list(alpha)},
                            reference_lucky, replay_lucky, counts,
                            total_preference_checks=total_preference_checks)
                    if (reference_outcomes is None) != (replay_outcomes is None):
                        return result(
                            False, "Success replay",
                            {"t": t, "m": m, "n": n, "alpha": list(alpha)},
                            reference_outcomes is not None,
                            replay_outcomes is not None, counts,
                            total_preference_checks=total_preference_checks)
                    if reference_outcomes is None:
                        failed += 1
                    else:
                        successes[reference_lucky] += 1
                row = {"t": t, "m": m, "n": n, "successes": successes,
                       "failed": failed, "fullinputs": fullinputs}
                rows.append(row)
                counts.append(row)

    fixtures, fixture_failure = run_fixtures()
    if fixture_failure is not None:
        fixture_failure["rawcounts"] = counts
        fixture_failure["total_preference_checks"] = total_preference_checks
        return fixture_failure

    finite_differences = []
    for (t, m), rows in rows_by_tm.items():
        start_n = rows[0]["n"]
        for k in range(1, m):
            values = [row["successes"][k] for row in rows]
            differences = [forward_differences(values, order)
                           for order in range(k + 2)]
            audit = {"t": t, "m": m, "k": k, "startn": start_n,
                     "values": values, "differences": differences}
            finite_differences.append(audit)
            for index, value in enumerate(differences[k + 1]):
                if value != 0:
                    return result(
                        False, "Question3 finite difference",
                        {"t": t, "m": m, "k": k,
                         "startn": start_n + index, "order": k + 1},
                        0, value, counts, fixtures, total_preference_checks,
                        finite_differences)
            kth = differences[k]
            if not all(value > 0 for value in kth):
                return result(
                    False, "Question3 finite difference",
                    {"t": t, "m": m, "k": k, "startn": start_n,
                     "order": k}, "positive", kth, counts, fixtures,
                    total_preference_checks, finite_differences)
            if any(value != kth[0] for value in kth[1:]):
                return result(
                    False, "Question3 finite difference",
                    {"t": t, "m": m, "k": k, "startn": start_n,
                     "order": k}, kth[0], kth, counts, fixtures,
                    total_preference_checks, finite_differences)

    return result(True, counts=counts, fixtures=fixtures,
                  total_preference_checks=total_preference_checks,
                  finite_differences=finite_differences)


if __name__ == "__main__":
    output = main()
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if output["ok"] else 1)
