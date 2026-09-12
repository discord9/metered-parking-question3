"""Run the portable finite verification checks for the referee package."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import py_compile
import subprocess
import sys


BASE = Path(__file__).resolve().parent
EXPECTED = BASE / "expected"


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n",
                    encoding="utf-8")


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_cli(script, destination, generated):
    environment = os.environ.copy()
    environment["PYTHONPYCACHEPREFIX"] = str(generated / "pycache")
    completed = subprocess.run(
        [sys.executable, str(script)],
        cwd=BASE,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    destination.write_bytes(completed.stdout)
    return completed.stdout


def require_equal(actual, expected, label):
    if actual != expected:
        raise AssertionError("%s differs from its expected JSON bytes" % label)


def check_definition(output):
    bounds = {
        "m": [2, 5],
        "t": "1..m inclusive",
        "n": "m-1..2*m inclusive",
        "difference_k": "1..m-1 inclusive",
    }
    assert output["ok"] is True
    assert output["name"] is None
    assert output["bounds"] == bounds
    rows = output["rawcounts"]
    assert len(rows) == 82
    assert output["total_preference_checks"] == 1139145
    assert sum(row["fullinputs"] for row in rows) == 1139145
    for row in rows:
        assert len(row["successes"]) == row["m"] + 1
        assert sum(row["successes"]) + row["failed"] == row["fullinputs"]
        assert row["fullinputs"] == row["n"] ** row["m"]
    fixtures = output["fixtures"]
    assert len(fixtures) == 4
    assert all({"t", "m", "n"} <= set(record) for record in fixtures)
    audits = output["finite_differences"]
    assert len(audits) == 40
    by_parameters = {(row["t"], row["m"], row["n"]): row for row in rows}
    for audit in audits:
        t, m, k = audit["t"], audit["m"], audit["k"]
        assert audit["startn"] == m - 1
        assert audit["values"] == [
            by_parameters[t, m, n]["successes"][k]
            for n in range(m - 1, 2 * m + 1)
        ]
        differences = audit["differences"]
        assert len(differences) == k + 2
        assert len(differences[k]) >= 3
        assert len(differences[k + 1]) >= 2
        assert all(value > 0 for value in differences[k])
        assert all(value == 0 for value in differences[k + 1])


def check_template(output):
    bounds = {
        "m": [2, 4],
        "t": "1..m inclusive",
        "n": "m-1..m+1 inclusive",
        "k": "1..m-1 inclusive",
    }
    assert output["ok"] is True
    assert output["name"] is None
    assert output["finite_only"] is True
    assert output["not_all_n"] is True
    assert output["uses_literature"] is False
    assert output["uses_lean"] is False
    assert output["bounds"] == bounds
    fixtures = output["fixtures"]
    assert len(fixtures) == 3
    assert fixtures[2] == {
        "t": 1,
        "m": 3,
        "k": 1,
        "n": 2,
        "template": {"r": 3, "u": [1, 1, 2], "v": [1, 2, 3],
                     "E": [1, 2], "c": 1},
        "embeddingcount": {"enumerated": 0, "formula": 0},
    }
    assert output["total_preferences"] == 4173
    rawcounts = output["rawcounts"]
    assert len(rawcounts) == 60
    raw_keys = set()
    for row in rawcounts:
        key = (row["t"], row["m"], row["n"], row["k"])
        assert key not in raw_keys
        raw_keys.add(key)
        assert row["actual"] == row["templates"]
    counter_rows = output["counter_rows"]
    assert len(counter_rows) == 27
    assert all(row["forward"] == row["reverse"] and row["unique"]
               for row in counter_rows)
    pairs = output["forward_pairs"]
    assert len(pairs) == 1737
    assert sum(row["forward"] for row in counter_rows) == len(pairs)
    pair_keys = set()
    for pair in pairs:
        key = (pair["t"], pair["m"], pair["n"], pair["r"], tuple(pair["u"]),
               tuple(pair["v"]), tuple(pair["x"]))
        assert key not in pair_keys
        pair_keys.add(key)
        assert pair["E"] == sorted({q for u, v in zip(pair["u"], pair["v"])
                                     for q in range(u, v)})
        assert pair["c"] == pair["r"] - len(pair["E"])
    templates = output["templates"]
    assert len(templates) == 367
    embedding_counts = 0
    for record in templates:
        for count in record["embeddingcounts"]:
            embedding_counts += 1
            assert count["enumerated"] == count["formula"]
    assert embedding_counts == 1101


def mutation_checks(generated):
    definition = load_module("portable_definition_check", BASE / "definition_check.py")
    definition.EARLY_DEPARTURE = True
    observed = definition.main()
    expected = {
        "ok": False,
        "name": "Departure timing replay",
        "params": {"t": 1, "m": 2, "n": 1, "alpha": [1, 1]},
        "expected": None,
        "actual": [1, 1],
    }
    actual = {key: observed[key] for key in expected}
    if actual != expected:
        raise AssertionError(json.dumps({"expected": expected, "actual": actual},
                                        sort_keys=True, separators=(",", ":")))
    write_json(generated / "definition_mutation_result.json",
               {"expected": expected, "observed": observed})

    template = load_module("portable_template_check", BASE / "template_check.py")
    template.FORCE_PHYSICAL_COMPONENTS = True
    observed = template.main()
    expected = {
        "ok": False,
        "name": "template forced edges",
        "params": {"t": 1, "m": 3, "n": 3, "alpha": [1, 1, 3]},
        "expected": [1],
        "actual": [1, 2],
    }
    actual = {key: observed[key] for key in expected}
    if actual != expected:
        raise AssertionError(json.dumps({"expected": expected, "actual": actual},
                                        sort_keys=True, separators=(",", ":")))
    write_json(generated / "template_mutation_result.json",
               {"expected": expected, "observed": observed})


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Run portable finite metered-parking verification checks."
    )
    parser.add_argument("--output-dir", default="generated",
                        help="directory for generated outputs (default: generated)")
    args = parser.parse_args(argv)
    generated = Path(args.output_dir)
    if not generated.is_absolute():
        generated = BASE / generated
    generated = generated.resolve()
    if generated.is_relative_to(EXPECTED.resolve()):
        parser.error("--output-dir must not be inside the expected directory")
    generated.mkdir(parents=True, exist_ok=True)
    sys.pycache_prefix = str(generated / "pycache")

    definition_script = BASE / "definition_check.py"
    template_script = BASE / "template_check.py"
    py_compile.compile(str(definition_script),
                       cfile=str(generated / "definition_check.pyc"), doraise=True)
    py_compile.compile(str(template_script),
                       cfile=str(generated / "template_check.pyc"), doraise=True)

    definition_bytes = run_cli(definition_script,
                               generated / "definition_result.json", generated)
    template_bytes = run_cli(template_script,
                             generated / "template_result.json", generated)
    require_equal(definition_bytes,
                  (EXPECTED / "definition_result.json").read_bytes(),
                  "definition check")
    require_equal(template_bytes,
                  (EXPECTED / "template_result.json").read_bytes(),
                  "template check")
    check_definition(json.loads(definition_bytes))
    check_template(json.loads(template_bytes))
    mutation_checks(generated)
    print("Portable finite verification passed: definition 82 rows / 1139145 inputs / "
          "40 audits; template 60 raw rows / 27 counters / 1737 pairs / "
          "367 templates / 1101 embedding counts. This is finite verification, not Lean.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as error:
        print("portable verification failed: %s" % error, file=sys.stderr)
        sys.exit(1)
