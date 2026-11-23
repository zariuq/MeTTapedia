#!/usr/bin/env python3
"""Exercise authored-module compilation and optional ordinary Datalog programs."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from packed_source_reader import retained_reader_arguments
from source_io import source_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--datalog", action="store_true")
    parser.add_argument("--souffle", type=Path, help="independent Souffle executable")
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--parser-host", type=Path, help="CeTTa source checkout supplying the shared native parser")
    args = parser.parse_args()
    tools = Path(__file__).resolve().parent
    repo = tools.parents[2]
    lean = repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise SystemExit("output directory must be empty")
    cetta = (args.cetta or Path(os.environ.get("CETTA_BIN",
        repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta"))).resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    environment = dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1")
    records, timings = [], []

    def run(label, command, cwd=lean, expected_failure=None):
        started = time.monotonic()
        with (output / f"{label}.out").open("w") as stdout, (output / f"{label}.err").open("w") as stderr:
            result = subprocess.run([str(x) for x in command], cwd=cwd, env=environment,
                                    stdout=stdout, stderr=stderr)
        timings.append({"step": label, "seconds": time.monotonic() - started, "exit_code": result.returncode})
        (output / "timings.json").write_text(json.dumps(timings, indent=2) + "\n")
        text = (output / f"{label}.out").read_text()
        if expected_failure is not None:
            errors = text + (output / f"{label}.err").read_text()
            if result.returncode == 0 or expected_failure not in errors:
                raise SystemExit(f"{label}: expected the declared diagnostic")
            records.append({"control": label, "diagnostic": expected_failure})
        elif result.returncode:
            raise SystemExit(f"{label} failed; inspect its retained logs")
        return text

    def both(label, program):
        first = run(label + "-cetta", [cetta, "--lang", "petta", "--quiet", program])
        second = run(label + "-petta", ["bash", petta, "--silent", program])
        if first != second or not first.endswith("true\n"):
            raise SystemExit(f"{label}: incomplete or differing native outputs")
        return first

    def sequence(items):
        sequence = "LNil"
        for child in reversed(items):
            sequence = f"(LCons {child} {sequence})"
        return sequence

    def app(name, *children):
        return f'(PApp "{name}" {sequence(children)})'

    zero = app("Zero")
    one, two = app("Succ", zero), app("Succ", app("Succ", zero))
    bag = '(PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons ' + app("A") + " (LCons " + app("B") + " LNil)) RNone)"
    cases = [
        ("arithmetic", tools.parent / "tests/module/RecursiveArithmetic.module", "Nat",
         [app("Add", one, one), app("Succ", app("Add", zero, one)), two]),
        ("petri", tools.parent / "module/CollectionPetri.module", "Marking", [bag,
         '(PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons ' + app("C") + " (LCons " + app("D") + " LNil)) RNone)",
         '(PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons ' + app("A") + " (LCons " + app("D") + " LNil)) RNone)"])]
    for name, source, sort, states in cases:
        compiled = output / f"{name}.metta"
        run(name + "-compile", [sys.executable, tools / "compile_gslt.py", source, compiled, "--sort", sort, "--name", name])
        workload = output / f"{name}-run.metta"
        workload.write_text(compiled.read_text() + '\n!(let* (($source (quote ' + states[0] + ')) ($run (' + name + ':run $source 6 300)) ($nodes (' + name + ':explore $source 500))) (println! (ModuleResult $run $nodes)))\n')
        text = both(name, workload)
        expected = f"(ModuleResult (RunTrace ClassDone {sequence(states)}) {sequence(states)})\ntrue\n"
        if text != expected:
            raise SystemExit(f"{name}: completed reduction or explored states differ from the specification")
        records.append({"control": name, "completed_run": True, "native_outputs_identical": True})

    run("wrong-sort", [sys.executable, tools / "compile_gslt.py", cases[0][1], output / "wrong-sort.metta", "--sort", "Missing"], expected_failure="selected state sort is not declared")
    run("preserve-output", [sys.executable, tools / "compile_gslt.py", cases[0][1], output / "arithmetic.metta", "--sort", "Nat"], expected_failure="already exists")
    for name, other in (("CycleA", "CycleB"), ("CycleB", "CycleA")):
        (output / f"{name}.module").write_text(f'import "{other}.module" as other\nModule {name} {{ Theory Empty() {{ Types {{ A; }} }} theory Empty() }}\n')
    run("import-cycle", [sys.executable, tools / "compile_gslt.py", output / "CycleA.module", output / "cycle.metta", "--sort", "A"], expected_failure="cyclic module import")

    if args.datalog:
        examples = tools.parent / "module/gold/SouffleDatalog/examples"
        datalog_cases = [("cyclic_graph", examples / "cyclic_graph.dl", examples / "cyclic_graph", ("Reach", "PathStep", "Eligible")),
                         ("points_to", examples / "points_to.dl", examples / "points_to", ("PointsTo", "Heap")),
                         ("basic", tools.parent / "tests/datalog/basic.dl", output, ("Same", "Low")),
                         ("nonlinear_closure", tools.parent / "tests/datalog/nonlinear_closure.dl", output, ("Linear", "Nonlinear")),
                         ("same_generation", tools.parent / "tests/datalog/same_generation.dl", output, ("SameGeneration",)),
                         ("boundaries", tools.parent / "tests/datalog/boundaries.dl", output, ("Seed", "Empty", "Copy"))]
        for name, source, facts, relations in datalog_cases:
            compiled = output / f"{name}.metta"
            compile_command = [sys.executable, tools / "compile_datalog.py", source, compiled, "--facts", facts, "--name", name]
            if args.parser_host:
                compile_command += ["--parser-host", args.parser_host.resolve()]
            run(name + "-compile", compile_command)
            reader = compiled.with_suffix(compiled.suffix + ".build")
            canonical = Path(str(compiled) + ".source.dl")
            parsed = run(name + "-roundtrip-parse", retained_reader_arguments(reader,
                canonical, output / f"{name}-roundtrip.cnf")).splitlines()
            parse_status = json.loads(parsed[0])
            if parse_status["outcome"] != 0 or not parse_status["accepted"] or parse_status["semanticResults"] != 1:
                raise SystemExit(f"{name}: canonical source did not produce one completed parser result")
            packet = output / f"{name}-roundtrip-selected.metta"
            packet.write_text("\n".join(parsed[1:]) + "\n")
            source_prefix = source_command(tools.parent / "module/gold/SouffleDatalog/Syntax.module")
            rounds = 32 * (parse_status["inputScalars"] + 1) + 256
            run(name + "-roundtrip-coverage", [*source_prefix,
                "coverage", canonical, output / f"{name}-roundtrip.cnf", output / f"{name}-roundtrip.cnf.pni", rounds])
            run(name + "-roundtrip-catalogue", [*source_prefix,
                "catalogue", canonical, output / f"{name}-roundtrip.cnf", output / f"{name}-roundtrip.cnf.pni", packet, rounds])
            canonical_compiled = output / f"{name}-roundtrip.metta"
            run(name + "-roundtrip-emit", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "emit_datalog.lean",
                canonical, packet, facts, canonical_compiled, name])
            if Path(str(compiled) + ".program.metta").read_bytes() != Path(str(canonical_compiled) + ".program.metta").read_bytes():
                raise SystemExit(f"{name}: source round trip changed the independent program payload")
            if canonical.read_bytes() != Path(str(canonical_compiled) + ".source.dl").read_bytes():
                raise SystemExit(f"{name}: canonical source printing is not stable")
            if compiled.read_bytes() != canonical_compiled.read_bytes():
                raise SystemExit(f"{name}: source round trip changed the emitted runtime program")
            workload = output / f"{name}-run.metta"
            workload.write_text(compiled.read_text() + '\n!(let* (($machine (' + name + ':run 100 10000)) ($result (gslt:snapshot:result $machine))) (println! (OrdinaryDatalog $result)))\n')
            both(name, workload)
            decoded = output / f"{name}-facts"
            run(name + "-decode", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "check_datalog_output.lean", str(compiled) + ".dictionary.metta", output / f"{name}-cetta.out", decoded])
            record = {"control": name, "ordinary_source": True, "completed_run": True, "native_outputs_identical": True,
                      "canonical_source_roundtrip": True, "program_payload_equal": True,
                      "canonical_printing_stable": True, "emitted_runtime_equal": True,
                      "complete_roundtrip_forest": True, "complete_roundtrip_catalogue": True}
            if args.souffle:
                reference = output / f"{name}-souffle"
                reference.mkdir()
                run(name + "-souffle", [args.souffle.resolve(), "-F", facts, "-D", reference, source])
                counts = {}
                for relation in relations:
                    actual = set((decoded / f"{relation}.csv").read_text().splitlines())
                    expected = set((reference / f"{relation}.csv").read_text().splitlines())
                    if actual != expected:
                        raise SystemExit(f"{name}: {relation} differs from Souffle")
                    counts[relation] = len(actual)
                record["souffle_fact_counts"] = counts
            if name == "nonlinear_closure":
                if set((decoded / "Linear.csv").read_text().splitlines()) != set((decoded / "Nonlinear.csv").read_text().splitlines()):
                    raise SystemExit("nonlinear_closure: the two recursive formulations differ")
            records.append(record)

        reader = output / "basic.metta.build"
        protected = output / "protected-source.metta"
        protected_source = Path(str(protected) + ".source.dl")
        protected_source.write_text("preserve this source artifact\n")
        run("preserve-canonical-source", [sys.executable, tools / "compile_datalog.py",
            tools.parent / "tests/datalog/basic.dl", protected, "--facts", output], expected_failure="already exists")
        if protected_source.read_text() != "preserve this source artifact\n":
            raise SystemExit("existing canonical source was overwritten")
        negatives = [
            ("unbound-head", '.decl P(x:symbol)\n.decl Q(x:symbol)\nP(X) :- Q(Y).\n', "typed positive core"),
            ("wrong-arity", '.decl P(x:symbol)\nP("a","b").\n', "typed positive core"),
            ("overflow", '.decl P(x:number)\nP(9223372036854775808).\n', "literal is outside the symbol/integer/unsigned profile"),
            ("floating", '.decl P(x:float)\nP(1.5).\n', "literal is outside the symbol/integer/unsigned profile"),
            ("negation", '.decl P(x:symbol)\n.decl Q(x:symbol)\nP(X) :- !Q(X).\n', None),
            ("missing-period", '.decl P(x:symbol)\nP("a")\n', None)]
        for name, source, diagnostic in negatives:
            label = "source-" + name
            path = output / f"{label}.dl"
            path.write_text(source)
            text = run(label + "-parse", retained_reader_arguments(reader, path, output / f"{label}.cnf"))
            lines = text.splitlines()
            status = json.loads(lines[0])
            if status["outcome"] != 0:
                raise SystemExit(f"{label}: parser budget did not settle")
            if diagnostic is None:
                if status["accepted"]:
                    raise SystemExit(f"{label}: unsupported syntax was accepted")
                records.append({"control": label, "diagnostic": "grammar refusal"})
            else:
                if not status["accepted"] or status["semanticResults"] != 1:
                    raise SystemExit(f"{label}: expected a parsed program with an admission diagnostic")
                packet = output / f"{label}-selected.metta"
                packet.write_text("\n".join(lines[1:]) + "\n")
                run(label + "-admit", ["lake", "env", "lean", "-DwarningAsError=true", "--run", tools / "emit_datalog.lean", path, packet, output, output / f"{label}.metta", "rejected"], expected_failure=diagnostic)

        generated = [sys.executable, tools / "test_datalog_source_printer.py", output / "generated-source-printer",
                     "--reader", reader]
        if args.souffle:
            generated += ["--souffle", args.souffle.resolve()]
        run("generated-source-printer", generated)
        printer_checks = json.loads((output / "generated-source-printer/qualification.json").read_text())
        records.append({"control": "generated-source-printer", "independent_ir_programs": len(printer_checks["controls"]),
                        "canonical_source_roundtrip": True})

    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    summary = {"controls": records, "cetta_sha256": digest(cetta),
               "petta_sources_sha256": {str(p.relative_to(petta.parent)): digest(p) for p in sorted((petta.parent / "src").glob("*.pl"))},
               "scope": "Operational CLI checks; universal source-to-native correspondence is a separate proof obligation."}
    (output / "qualification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
