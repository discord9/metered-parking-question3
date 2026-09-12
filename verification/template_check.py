"""Bounded rank-template normalization/inflation check; not a proof."""

from collections import Counter
from itertools import combinations, product
import importlib.util
import json
import math
from pathlib import Path
import sys


FORCE_PHYSICAL_COMPONENTS = False
BOUNDS = {
    "m": [2, 4],
    "t": "1..m inclusive",
    "n": "m-1..m+1 inclusive",
    "k": "1..m-1 inclusive",
}
METADATA = {"finite_only": True, "not_all_n": True,
            "uses_literature": False, "uses_lean": False}


def load_reference_simulator():
    path = Path(__file__).resolve().with_name("definition_check.py")
    spec = importlib.util.spec_from_file_location("definition_checker", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.reference_simulator


REFERENCE_SIMULATOR = load_reference_simulator()


def edges(u, v):
    return tuple(sorted({q for left, right in zip(u, v)
                         for q in range(left, right)}))


def normalize(alpha, parked):
    """Rank an already-successful actual replay; callers establish that premise."""
    x = tuple(sorted(set(parked)))
    rank = {spot: index + 1 for index, spot in enumerate(x)}
    u = tuple(rank[preference] for preference in alpha)
    v = tuple(rank[spot] for spot in parked)
    forced = set(edges(u, v))
    if FORCE_PHYSICAL_COMPONENTS:
        forced.update(q for q in range(1, len(x)) if x[q] == x[q - 1] + 1)
    forced = tuple(sorted(forced))
    return (len(x), u, v), x, forced, len(x) - len(forced)


def admissible(t, m, k, template):
    r, u, v = template
    if not (1 <= r <= m and len(u) == m and len(v) == m):
        return False
    if set(v) != set(range(1, r + 1)):
        return False
    if sum(left == right for left, right in zip(u, v)) != k:
        return False
    for j, (left, right) in enumerate(zip(u, v)):
        active = set(v[max(0, j - t):j])
        if not (1 <= left <= right <= r and right not in active):
            return False
        if not set(range(left, right)).issubset(active):
            return False
    return True


def independent_templates(t, m, k):
    """Enumerate T1 locally, rather than normalizing preference lists."""
    templates = []
    for r in range(1, m + 1):
        for v in product(range(1, r + 1), repeat=m):
            if set(v) != set(range(1, r + 1)):
                continue
            choices = []
            for j, right in enumerate(v):
                active = set(v[max(0, j - t):j])
                if right in active:
                    break
                choices.append([left for left in range(1, right + 1)
                                if set(range(left, right)).issubset(active)])
            else:
                for u in product(*choices):
                    template = (r, tuple(u), tuple(v))
                    if sum(left == right for left, right in zip(u, v)) == k:
                        templates.append(template)
    return tuple(templates)


def embeddings(template, n):
    r, u, v = template
    forced = edges(u, v)
    return tuple(x for x in combinations(range(1, n + 1), r)
                 if all(x[q] == x[q - 1] + 1 for q in forced))


def embedding_formula(template, n):
    r, u, v = template
    c = r - len(edges(u, v))
    return math.comb(n - r + c, c)


def inflate(template, x, t, m, k, n):
    r, u, v = template
    if not admissible(t, m, k, template):
        raise AssertionError("inflate received an inadmissible template")
    if len(x) != r or tuple(sorted(x)) != tuple(x) or len(set(x)) != r:
        raise AssertionError("inflate received non-increasing ranks")
    if not x or x[0] < 1 or x[-1] > n:
        raise AssertionError("inflate received ranks outside [n]")
    if any(x[q] != x[q - 1] + 1 for q in edges(u, v)):
        raise AssertionError("inflate received an unforced traversal gap")
    alpha = tuple(x[left - 1] for left in u)
    expected_parked = tuple(x[right - 1] for right in v)
    parked, lucky = REFERENCE_SIMULATOR(alpha, t, n)
    if parked != expected_parked or lucky != k:
        raise AssertionError("inflated template did not replay its parking history")
    recovered, recovered_x, recovered_edges, recovered_c = normalize(alpha, parked)
    if (recovered != template or recovered_x != x or
            recovered_edges != edges(u, v) or recovered_c != r - len(edges(u, v))):
        raise AssertionError("inflation did not normalize back to its template")
    return alpha, parked


def json_template(template):
    r, u, v = template
    forced = edges(u, v)
    return {"r": r, "u": list(u), "v": list(v), "E": list(forced),
            "c": r - len(forced)}


def failure(name, params, expected, actual, **extra):
    output = {
        "ok": False,
        "name": name,
        "params": params,
        "expected": expected,
        "actual": actual,
        "bounds": BOUNDS,
        **METADATA,
        "scope": "bounded template normalization/inflation check only; not a proof",
    }
    output.update(extra)
    return output


def fixtures():
    cases = (
        (1, 3, 2, (1, 1, 1), (1, 2, 1), (2, (1, 1, 1), (1, 2, 1)), (1,), 1),
        (1, 3, 3, (1, 1, 3), (1, 2, 3), (3, (1, 1, 3), (1, 2, 3)), (1,), 2),
    )
    records = []
    for t, m, n, alpha, expected_parked, expected_t, expected_edges, expected_c in cases:
        parked, lucky = REFERENCE_SIMULATOR(alpha, t, n)
        template, x, actual_edges, actual_c = normalize(alpha, parked)
        record = {"t": t, "m": m, "n": n, "alpha": list(alpha),
                  "parked": None if parked is None else list(parked),
                  "template": json_template(template), "x": list(x),
                  "lucky": lucky}
        records.append(record)
        if parked != expected_parked or template != expected_t:
            return records, failure("template fixture", {"t": t, "m": m,
                "n": n, "alpha": list(alpha)},
                {"parked": list(expected_parked), "template": json_template(expected_t)},
                {"parked": None if parked is None else list(parked),
                 "template": json_template(template)})
        if actual_edges != expected_edges:
            return records, failure("template forced edges", {"t": t, "m": m,
                "n": n, "alpha": list(alpha)}, list(expected_edges),
                list(actual_edges))
        if actual_c != expected_c:
            return records, failure("template fixture", {"t": t, "m": m,
                "n": n, "alpha": list(alpha)}, expected_c, actual_c)

    t, m, k, n = 1, 3, 1, 2
    t7 = (m, (1, 1, 2), (1, 2, 3))
    enumerated = embeddings(t7, n)
    formula = embedding_formula(t7, n)
    records.append({"t": t, "m": m, "k": k, "n": n,
                    "template": json_template(t7),
                    "embeddingcount": {"enumerated": len(enumerated),
                                       "formula": formula}})
    if enumerated or formula != 0:
        return records, failure("T7 threshold fixture", {"t": t, "m": m,
            "k": k, "n": n}, 0,
            {"enumerated": len(enumerated), "formula": formula})
    return records, None


def main():
    fixture_records, fixture_failure = fixtures()
    if fixture_failure is not None:
        return fixture_failure

    rawcounts = []
    template_records = []
    forward_pairs = []
    counter_rows = []
    template_cache = {}
    total_preferences = 0

    for m in range(2, 5):
        for t in range(1, m + 1):
            for k in range(1, m):
                templates = independent_templates(t, m, k)
                template_cache[t, m, k] = templates
                for template in templates:
                    r, u, v = template
                    if not admissible(t, m, k, template):
                        return failure("independent template", {"t": t, "m": m,
                            "k": k}, True, False)
                    forced = edges(u, v)
                    c = r - len(forced)
                    for j in range(m):
                        active = v[max(0, j - t):j]
                        if len(active) != len(set(active)):
                            return failure("active outcomes unique", {"t": t,
                                "m": m, "k": k, "template": json_template(template),
                                "j": j + 1}, "unique", list(active))
                    if c > k:
                        return failure("component lucky bound", {"t": t, "m": m,
                            "k": k, "template": json_template(template)}, "c <= k", c)
                    template_records.append({"t": t, "m": m, "k": k,
                        "template": json_template(template), "embeddingcounts": [
                            {"n": n, "enumerated": len(embeddings(template, n)),
                             "formula": embedding_formula(template, n)}
                            for n in range(m - 1, m + 2)]})
                t7 = (m, tuple(j if j <= k else j - 1 for j in range(1, m + 1)),
                      tuple(range(1, m + 1)))
                if t7 not in templates or len(edges(t7[1], t7[2])) != m - k:
                    return failure("T7 template", {"t": t, "m": m, "k": k},
                                   "present with c=k", json_template(t7))
                if embeddings(t7, m - 1):
                    return failure("T7 threshold embedding", {"t": t, "m": m,
                        "k": k, "n": m - 1}, [], [list(x) for x in embeddings(t7, m - 1)])

            for n in range(m - 1, m + 2):
                direct_sources = {}
                forward = Counter()
                reverse = Counter()
                actual_counts = {k: 0 for k in range(1, m)}
                for alpha in product(range(1, n + 1), repeat=m):
                    total_preferences += 1
                    parked, lucky = REFERENCE_SIMULATOR(alpha, t, n)
                    if parked is None or not (1 <= lucky < m):
                        continue
                    actual_counts[lucky] += 1
                    for j in range(m):
                        active = parked[max(0, j - t):j]
                        if len(active) != len(set(active)):
                            return failure("active outcomes unique", {"t": t,
                                "m": m, "n": n, "alpha": list(alpha),
                                "j": j + 1}, "unique", list(active))
                    template, x, actual_edges, c = normalize(alpha, parked)
                    expected_edges = edges(template[1], template[2])
                    if actual_edges != expected_edges:
                        return failure("template forced edges", {"t": t, "m": m,
                            "n": n, "alpha": list(alpha)}, list(expected_edges),
                            list(actual_edges))
                    if c != template[0] - len(expected_edges):
                        return failure("template component count", {"t": t, "m": m,
                            "n": n, "alpha": list(alpha)}, template[0] - len(expected_edges), c)
                    if template not in template_cache[t, m, lucky]:
                        return failure("direct template membership", {"t": t, "m": m,
                            "n": n, "alpha": list(alpha)}, True, False)
                    available = embeddings(template, n)
                    if x not in available:
                        return failure("direct embedding", {"t": t, "m": m,
                            "n": n, "alpha": list(alpha)}, [list(x)],
                            [list(item) for item in available])
                    try:
                        inflated_alpha, inflated_parked = inflate(
                            template, x, t, m, lucky, n)
                    except AssertionError as error:
                        return failure("inflate direct", {"t": t, "m": m, "n": n,
                            "alpha": list(alpha)}, "round trip", str(error))
                    if inflated_alpha != alpha or inflated_parked != parked:
                        return failure("inflate direct", {"t": t, "m": m, "n": n,
                            "alpha": list(alpha)}, {"alpha": list(alpha), "parked": list(parked)},
                            {"alpha": list(inflated_alpha), "parked": list(inflated_parked)})
                    pair = (template, x)
                    forward[pair] += 1
                    direct_sources[pair] = alpha
                    forward_pairs.append({"t": t, "m": m, "n": n, "k": lucky,
                        "alpha": list(alpha), "p": list(parked), "r": template[0],
                        "u": list(template[1]), "v": list(template[2]),
                        "E": list(expected_edges), "c": c, "x": list(x)})

                for k in range(1, m):
                    for template in template_cache[t, m, k]:
                        for x in embeddings(template, n):
                            try:
                                alpha, parked = inflate(template, x, t, m, k, n)
                            except AssertionError as error:
                                return failure("inflate reverse", {"t": t, "m": m,
                                    "n": n, "k": k, "template": json_template(template),
                                    "x": list(x)}, "valid replay", str(error))
                            pair = (template, x)
                            reverse[pair] += 1
                            if pair not in direct_sources:
                                return failure("reverse direct source", {"t": t, "m": m,
                                    "n": n, "k": k, "template": json_template(template),
                                    "x": list(x)}, "direct source", None)
                            recovered, recovered_x, recovered_edges, recovered_c = normalize(alpha, parked)
                            if (recovered != template or recovered_x != x or
                                    recovered_edges != edges(template[1], template[2]) or
                                    recovered_c != template[0] - len(edges(template[1], template[2]))):
                                return failure("reverse normalization", {"t": t, "m": m,
                                    "n": n, "k": k, "template": json_template(template),
                                    "x": list(x)}, json_template(template), json_template(recovered))
                if forward != reverse or any(value != 1 for value in forward.values()):
                    return failure("template pair counters", {"t": t, "m": m, "n": n},
                        "equal unique counters", {"forward": sum(forward.values()),
                        "reverse": sum(reverse.values())})
                for k in range(1, m):
                    template_count = sum(len(embeddings(template, n))
                                         for template in template_cache[t, m, k])
                    rawcounts.append({"t": t, "m": m, "n": n, "k": k,
                        "actual": actual_counts[k], "templates": template_count})
                    if actual_counts[k] != template_count:
                        return failure("template aggregate count", {"t": t, "m": m,
                            "n": n, "k": k}, actual_counts[k], template_count)
                counter_rows.append({"t": t, "m": m, "n": n,
                    "forward": sum(forward.values()), "reverse": sum(reverse.values()),
                    "unique": all(value == 1 for value in forward.values())})

    for record in template_records:
        for count in record["embeddingcounts"]:
            if count["enumerated"] != count["formula"]:
                return failure("binomial embedding formula", {"t": record["t"],
                    "m": record["m"], "k": record["k"], "n": count["n"],
                    "template": record["template"]}, count["formula"], count["enumerated"])
    return {"ok": True, "name": None, "params": None, "expected": None,
            "actual": None, "bounds": BOUNDS, **METADATA,
            "scope": "bounded template normalization/inflation check only; not a proof",
            "fixtures": fixture_records, "rawcounts": rawcounts,
            "templates": template_records, "forward_pairs": forward_pairs,
            "counter_rows": counter_rows, "total_preferences": total_preferences}


if __name__ == "__main__":
    output = main()
    print(json.dumps(output, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if output["ok"] else 1)
