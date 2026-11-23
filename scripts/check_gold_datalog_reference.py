#!/usr/bin/env python3
"""Run the ordinary Datalog acceptance programs against pinned Souffle 2.5.

These are native reference observations. They do not certify the module reader,
lowering or emitted execution, and PathStep is a program relation rather than an
enumerator of all unfolded derivations.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "metta/gslt/module/gold/SouffleDatalog/examples"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_relation(path):
    rows = [tuple(line.split("\t")) for line in path.read_text().splitlines()]
    if len(rows) != len(set(rows)):
        raise AssertionError(f"duplicate output rows in {path.name}")
    return set(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--souffle", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path,
                        help="new directory for retained inputs, outputs and results")
    args = parser.parse_args()
    binary = args.souffle.resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    before = {str(p.relative_to(ROOT)): digest(p)
              for p in sorted(EXAMPLES.rglob("*")) if p.is_file()}
    before[str(Path(__file__).resolve().relative_to(ROOT))] = digest(Path(__file__).resolve())
    before["native-binary"] = digest(binary)
    record = {"passed": False, "compiler_correspondence_qualified": False,
              "binary_sha256": before["native-binary"], "source_sha256": before,
              "cases": [], "checks": [], "invocation": ["souffle", "-j", "1"]}

    def check(name, condition):
        record["checks"].append({"name": name, "passed": bool(condition)})
        if not condition:
            raise AssertionError(name)

    def run(name, program, empty_inputs=()):
        folder = output / name
        folder.mkdir()
        inputs = folder / "input"
        inputs.mkdir()
        results = folder / "output"
        results.mkdir()
        source = EXAMPLES / (program + ".dl")
        shutil.copyfile(source, folder / source.name)
        for fact in sorted((EXAMPLES / program).glob("*.facts")):
            if fact.stem in empty_inputs:
                (inputs / fact.name).write_text("")
            else:
                shutil.copyfile(fact, inputs / fact.name)
        started = time.monotonic()
        result = subprocess.run(
            [str(binary), "-j", "1", "-F", "input", "-D", "output", source.name],
            cwd=folder, capture_output=True, text=True, timeout=60)
        elapsed = time.monotonic() - started
        (folder / "stdout.txt").write_text(result.stdout)
        (folder / "stderr.txt").write_text(result.stderr)
        record["cases"].append({"name": name, "exit": result.returncode,
                                "elapsed_seconds": elapsed,
                                "empty_inputs": list(empty_inputs),
                                "retained_sha256": {str(p.relative_to(folder)): digest(p)
                                                    for p in sorted(folder.rglob("*")) if p.is_file()}})
        check(name + ": exit and diagnostics", result.returncode == 0 and not result.stderr)
        return {p.stem: read_relation(p) for p in sorted(results.glob("*.csv"))}

    try:
        version = subprocess.run([str(binary), "--version"], capture_output=True,
                                 text=True, timeout=20)
        (output / "version.txt").write_text(version.stdout)
        record["version"] = version.stdout
        check("pinned Souffle 2.5", version.returncode == 0 and not version.stderr
              and "Version: 2.5 (2.5)" in version.stdout)

        graph = run("cyclic-graph", "cyclic_graph")
        nodes = ("a", "b", "c", "d")
        edges = (("a", "b"), ("a", "c"), ("b", "d"), ("c", "d"), ("d", "a"))
        expected_graph = {
            "Reach": {(x, y) for x in nodes for y in nodes} | {("u", "v")},
            "PathStep": {(x, y, z) for x in nodes for y, z in edges if x != z},
            "Eligible": {("rank", "7"), ("loop", "3"), ("other", "2")}}
        check("cyclic graph: exact relations", graph == expected_graph)
        check("two distinct final joins for one conclusion",
              {("a", "b", "d"), ("a", "c", "d")} <= graph["PathStep"])
        check("failed comparison, missing premise and wrong conclusion excluded",
              all(name not in {r[0] for r in graph["Eligible"]}
                  for name in ("low", "missing", "wrong")))
        empty_graph = run("graph-without-edges", "cyclic_graph", ("Edge",))
        check("no edges: all outputs empty",
              empty_graph == {name: set() for name in expected_graph})

        points = run("points-to", "points_to")
        initial = {("p", "cell"), ("alias", "cell"), ("x", "red"),
                   ("y", "blue"), ("q", "other"), ("z", "red")}
        loaded = {(variable, value) for variable in ("out", "cycle1", "cycle2", "viaAlias")
                  for value in ("red", "blue")} | {("otherOut", "red")}
        expected_points = {"PointsTo": initial | loaded,
                           "Heap": {("cell", "red"), ("cell", "blue"), ("other", "red")}}
        check("points-to: exact relations", points == expected_points)
        check("unknown pointer and wrong heap target excluded",
              not any(v == "missing" for v, _ in points["PointsTo"])
              and ("otherOut", "blue") not in points["PointsTo"])
        no_stores = run("points-without-stores", "points_to", ("Store",))
        check("loads require heap stores", no_stores == {"PointsTo": initial, "Heap": set()})
        no_seeds = run("points-without-addresses", "points_to", ("Address",))
        check("cycles do not invent address facts",
              no_seeds == {"PointsTo": set(), "Heap": set()})
        check("binary and authored sources unchanged",
              all(digest(binary if name == "native-binary" else ROOT / name) == value
                  for name, value in before.items()))
        record["passed"] = True
    except Exception as error:
        record["error"] = str(error)
        raise
    finally:
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"passed": True, "cases": len(record["cases"]),
                      "checks": len(record["checks"]),
                      "record_sha256": digest(output / "result.json")}))


if __name__ == "__main__":
    main()
