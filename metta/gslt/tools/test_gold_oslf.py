#!/usr/bin/env python3
"""Cross-check operational Gold IRs through OSLF and shared MeTTa execution."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check_product_graphs(product, manifest):
    """Check closure, rootedness, outcomes and the complete list of local obligations."""
    graphs = json.loads((product / "graphs.json").read_text())
    expected = []
    if len(graphs) != manifest["mailboxPrograms"] + manifest["ocamlPrograms"]:
        raise RuntimeError("the product graph inventory differs from the fixture inventory")
    for graph in graphs:
        nodes = {node["state"]: node["successors"] for node in graph["nodes"]}
        if len(nodes) != len(graph["nodes"]) or graph["source"] not in nodes:
            raise RuntimeError("duplicate graph nodes or missing root")
        if graph["target"] not in nodes or graph["wrong"] in nodes:
            raise RuntimeError("graph disagrees with the independent result fixture")
        if any(target not in nodes for successors in nodes.values() for target in successors):
            raise RuntimeError("graph has an unclosed frontier")
        reached, pending = set(), [graph["source"]]
        while pending:
            node = pending.pop()
            if node not in reached:
                reached.add(node)
                pending.extend(nodes[node])
        if reached != set(nodes):
            raise RuntimeError("graph contains an unreachable component")
        if [node for node, successors in nodes.items() if not successors] != [graph["target"]]:
            raise RuntimeError("graph has an unexpected terminal outcome")

        def row(formula, state, answer):
            return f'{graph["file"]} | {formula} | {state} | 1 | {answer} | fuel=2 hints=0'

        for state, successors in nodes.items():
            allowed = "bot"
            for target in reversed(successors):
                allowed = f"(or (is {target}) {allowed})"
            expected += [row(f"(box {allowed})", state, "established"),
                         row(f'(dia (is {graph["wrong"]}))', state, "refuted")]
            expected += [row(f"(dia (is {target}))", state, "established") for target in successors]
            if not successors:
                expected.append(row("(dia top)", state, "refuted"))
    actual = [line.strip() for line in (product / "matrix.txt").read_text().splitlines()
              if line.strip() and not line.lstrip().startswith("#")]
    first = graphs[0]
    expected.append(f'{first["file"]} | (mu X0 (or (is {first["target"]}) (dia X0))) | '
                    f'{first["source"]} | 0 | suspended | fuel=2 hints=0')
    if actual != expected or len(actual) != manifest["rows"]:
        raise RuntimeError("the matrix omits or changes a graph obligation")
    return {"graphs": len(graphs), "nodes": sum(len(graph["nodes"]) for graph in graphs),
            "closed_and_rooted": True, "all_local_obligations_present": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cetta", type=Path)
    parser.add_argument("--petta-runner", type=Path)
    parser.add_argument("--oslf", type=Path, help="Compiled OSLF executable for the file-based comparison")
    parser.add_argument("--erlang-bin", type=Path, help="Also run the receive controls on native Erlang")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    gslt, lean = repo / "metta/gslt", repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    targets = ["Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLFControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldOSLFCollectionControls",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeOSLFControls",
               "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission",
               "Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlExecutionData",
               "Mettapedia.OSLF.NativeTypes.Product.Main",
               "Mettapedia.OSLF.NativeTypes.Product.Export"]
    with (output / "build.log").open("w") as log:
        subprocess.run(["lake", "--wfail", "build", *targets, "oslf"], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    cetta = (args.cetta or repo.parent / "hyperon/cetta-prime-2.0-draft-20260910/cetta").resolve()
    petta = (args.petta_runner or repo.parent / "hyperon/PeTTa/run.sh").resolve()
    generator = gslt / "tools/generate_gold_oslf_controls.lean"
    ocaml_generator = gslt / "tools/generate_ocaml_kernel_controls.lean"
    product_generator = gslt / "tools/generate_gold_oslf_product.lean"
    oslf = (args.oslf or lean / ".lake/build/bin/oslf").resolve()
    common = gslt / "tools/test_gslt_complete.sh"
    match = re.search(r"^libraries=\((.*?)^\)", common.read_text(), re.S | re.M)
    if match is None:
        raise RuntimeError("the shared runtime library list is missing")
    libraries = [gslt / "lib" / (name + ".metta") for name in match[1].split()]
    inputs = {Path(__file__).resolve(), generator, ocaml_generator, product_generator, oslf,
              common, *libraries, cetta, petta,
              lean / "lean-toolchain", lean / "lakefile.lean", lean / "lake-manifest.json"}
    inputs.update((petta.parent / "src").rglob("*.pl"))
    inputs.update(gslt / "module" / (name + ".module") for name in
                  ["Radix16", "OCamlIR", "OCamlMachine", "ErlangData", "ErlangMailbox"])
    erlang_source = gslt / "module/gold/Erlang/examples/mailbox_operations.erl"
    if args.erlang_bin:
        erlang_bin = args.erlang_bin.resolve()
        inputs.update([erlang_source, erlang_bin / "erl", erlang_bin / "erlc"])
        inputs.update(erlang_bin.parent.glob("erts-*/bin/beam.smp"))
        inputs.update(erlang_bin.parent.glob("lib/erlang/erts-*/bin/beam.smp"))
    for target in targets:
        relative = Path(*target.split("."))
        setup = lean / ".lake/build/ir" / relative.with_suffix(".setup.json")
        inputs.update([setup, lean / relative.with_suffix(".lean"),
                       lean / ".lake/build/lib/lean" / relative.with_suffix(".olean")])
        for dependency, groups in json.loads(setup.read_text())["importArts"].items():
            if dependency.startswith("Mettapedia."):
                inputs.add(lean / Path(*dependency.split(".")).with_suffix(".lean"))
            inputs.update(Path(path) for group in groups for path in group)
    pins = {str(path): sha(path) for path in inputs}
    def save_pins():
        (output / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    save_pins()
    with (output / "generation.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", generator, output],
                       cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
    manifest = json.loads((output / "oslf.json").read_text())
    questions = manifest["ocamlPreparedStructural"] + manifest["erlangMailbox"]
    if not questions or not all(row["expectedReachable"] is True and row["wrongReachable"] is False
                                for row in questions):
        raise RuntimeError("OSLF did not decide the expected positive and separating negative questions")
    conditional = manifest["snapshotAndWaiting"]
    if not conditional or not all(row["answer"] is row["expected"] for row in conditional):
        raise RuntimeError("OSLF did not decide the snapshot, waiting and collection-kernel questions")
    collections = manifest["collectionQuestions"]
    deferred = [row for row in collections if row["answer"] is None]
    collection_answers = [row for row in collections if row["answer"] is not None]
    if not all(row["answer"] is row["intended"] for row in collection_answers):
        raise RuntimeError("a collection certificate contradicts the kernel's intended behavior")
    maude_answers = [row for row in manifest["maudeQuestions"] if row["answer"] is not None]
    maude_deferred = [row for row in manifest["maudeQuestions"] if row["answer"] is None]
    if len(maude_answers) != 2 or not all(row["answer"] is row["expected"] for row in maude_answers):
        raise RuntimeError("the Maude IR direct rule questions did not agree")
    if manifest["exhaustedMailboxQuestion"] is not None:
        raise RuntimeError("an exhausted mailbox query produced a verdict")
    product = output / "product"
    with (output / "product-generation.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                        product_generator, product, gslt / "module"], cwd=lean, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    product_manifest = json.loads((product / "manifest.json").read_text())
    graph_checks = check_product_graphs(product, product_manifest)
    if (product_manifest["mailboxPrograms"] != len(manifest["erlangMailbox"]) or
            product_manifest["ocamlPrograms"] != len(manifest["ocamlPreparedStructural"])):
        raise RuntimeError("file-based and emitted fixture inventories differ")
    for path in [product / "matrix.txt", product / "global-matrix.txt", product / "graphs.json",
                 product / "manifest.json", *product.glob("*.module")]:
        pins[str(path)] = sha(path)
    save_pins()
    started = time.monotonic()
    with (product / "stdout.txt").open("w") as out, (product / "stderr.txt").open("w") as err:
        result = subprocess.run(["lake", "env", str(oslf), "--matrix", str(product / "matrix.txt")],
                                cwd=lean, stdout=out, stderr=err)
    product_output = (product / "stdout.txt").read_text()
    rows = product_manifest["rows"]
    summaries = re.findall(r"^(\d+) of (\d+) rows as expected,", product_output, re.M)
    product_passed = (result.returncode == 0 and not (product / "stderr.txt").read_bytes()
                      and "FAIL " not in product_output and "error:" not in product_output
                      and summaries == [(str(rows), str(rows))]
                      and len(re.findall(r"^ok   ", product_output, re.M)) == rows)
    product_result = {"passed": product_passed, "rows": rows, "exit_code": result.returncode,
                      "seconds": time.monotonic() - started, "manifest": product_manifest,
                      "graph_checks": graph_checks,
                      "reading_policy": "Product.readingOf", "universal_core_adequacy": False}
    (product / "qualification.json").write_text(json.dumps(product_result, indent=2) + "\n")
    print(json.dumps({"executable_oslf": product_result}), flush=True)
    if not product_passed:
        raise RuntimeError("executable OSLF disagreed on the operational IR files")
    workload = output / "workload.metta"
    workload.write_text("\n".join(path.read_text()
        for path in [*libraries, output / "machine.metta", output / "controls.metta"]))
    for path in [workload, output / "machine.metta", output / "controls.metta", output / "oslf.json"]:
        pins[str(path)] = sha(path)
    save_pins()
    results = []
    expected_names = [row["name"] for row in manifest["erlangMailbox"]]
    for name, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(workload)]),
                          ("petta", ["bash", str(petta), "--silent", str(workload)])]:
        started = time.monotonic()
        with (output / (name + ".out")).open("w") as out, (output / (name + ".err")).open("w") as err:
            result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                    stdout=out, stderr=err)
        rows = [line for line in (output / (name + ".out")).read_text().splitlines()
                if line.startswith("(GoldOSLFNativeControl ")]
        parsed = [re.fullmatch(r'\(GoldOSLFNativeControl "([^"]+)"' + r" (true|false)" * 6 + r"\)", row)
                  for row in rows]
        passed = (result.returncode == 0 and not (output / (name + ".err")).read_bytes()
                  and len(parsed) == len(expected_names) and all(parsed)
                  and [match.group(1) for match in parsed] == expected_names
                  and all(match.groups()[1:] == ("true",) * 6 for match in parsed))
        results.append({"engine": name, "passed": passed, "exit_code": result.returncode,
                        "controls": rows, "stdout_sha256": sha(output / (name + ".out")),
                        "seconds": time.monotonic() - started})
        (output / "mailbox-results.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results[-1]), flush=True)
    identical = results[0]["controls"] == results[1]["controls"]
    ocaml_results = []
    for question in manifest["ocamlPreparedStructural"]:
        label = question["name"]
        directory = output / "ocaml" / label
        with (output / ("generate-ocaml-" + label + ".log")).open("w") as log:
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", ocaml_generator,
                            directory, label], cwd=lean, stdout=log, stderr=subprocess.STDOUT, check=True)
        ocaml_workload = directory / "workload.metta"
        ocaml_workload.write_text("\n".join(path.read_text() for path in
            [*libraries, directory / "machine.metta", directory / "controls.metta"]))
        for path in [ocaml_workload, directory / "machine.metta", directory / "controls.metta",
                     directory / "preparation.json"]:
            pins[str(path)] = sha(path)
        save_pins()
        engines = []
        for name, command in [("cetta", [str(cetta), "--lang", "petta", "--quiet", str(ocaml_workload)]),
                              ("petta", ["bash", str(petta), "--silent", str(ocaml_workload)])]:
            started = time.monotonic()
            with (directory / (name + ".out")).open("w") as out, (directory / (name + ".err")).open("w") as err:
                result = subprocess.run(command, cwd=lean, env=dict(os.environ, CETTA_PETTA_SEARCH_MACHINE="1"),
                                        stdout=out, stderr=err)
            rows = [line for line in (directory / (name + ".out")).read_text().splitlines()
                    if line.startswith("(OCamlKernelControl ")]
            parsed = [re.fullmatch(r'\(OCamlKernelControl "([^"]+)"' + r" (true|false)" * 6
                                  + r" ([0-9]+) ([0-9]+)\)", row) for row in rows]
            passed = (result.returncode == 0 and not (directory / (name + ".err")).read_bytes()
                      and len(parsed) == 1 and parsed[0] is not None
                      and parsed[0].group(1) == label and parsed[0].groups()[1:7] == ("true",) * 6)
            engines.append({"engine": name, "passed": passed, "exit_code": result.returncode,
                            "controls": rows, "stdout_sha256": sha(directory / (name + ".out")),
                            "seconds": time.monotonic() - started})
            (directory / "engine-results.json").write_text(json.dumps(engines, indent=2) + "\n")
        same = engines[0]["controls"] == engines[1]["controls"]
        ocaml_results.append({"program": label, "oslf": question, "engines": engines,
                              "outputs_identical": same,
                              "passed": same and all(engine["passed"] for engine in engines)})
        (output / "ocaml-results.json").write_text(json.dumps(ocaml_results, indent=2) + "\n")
        print(json.dumps(ocaml_results[-1]), flush=True)
        if not ocaml_results[-1]["passed"]:
            raise RuntimeError(label + ": OSLF/native structural comparison failed")
    erlang_reference = None
    if args.erlang_bin:
        erlang_output = output / "erlang"
        erlang_output.mkdir()
        for options in [[], ["+to_core"]]:
            with (erlang_output / ("compile-core.log" if options else "compile-beam.log")).open("w") as log:
                subprocess.run([str(erlang_bin / "erlc"), "-Werror", *options, "-o", str(erlang_output),
                                str(erlang_source)], stdout=log, stderr=subprocess.STDOUT, check=True)
        command = [str(erlang_bin / "erl"), "-noshell", "-pa", str(erlang_output), "-eval",
                   'io:format("~w~n", [mailbox_operations:run()]), halt().']
        native = subprocess.run(command, capture_output=True, text=True)
        (erlang_output / "reference.out").write_text(native.stdout)
        (erlang_output / "reference.err").write_text(native.stderr)
        expected = "{{a,b},{b,[a,c]},{a,a},{2,[{n,0},noise]},{a,b}}\n"
        erlang_reference = {"passed": native.returncode == 0 and native.stdout == expected and not native.stderr,
                            "expected": expected, "actual": native.stdout, "exit_code": native.returncode,
                            "controls": 5, "erl_flags": os.environ.get("ERL_FLAGS", "")}
        print(json.dumps({"erlang_reference": erlang_reference}), flush=True)
    changed = [path for path, expected in pins.items() if sha(path) != expected]
    record = {"engines": results, "input_pins": pins, "changed_inputs": changed,
              "ocaml_programs": ocaml_results,
              "executable_oslf": product_result,
              "oslf_decided_checks": 2 * len(questions) + len(conditional) + len(collection_answers) + len(maude_answers),
              "oslf_deferred_questions": deferred,
              "maude_deferred_questions": maude_deferred,
              "exhausted_mailbox_question": manifest["exhaustedMailboxQuestion"],
              "native_checks_per_engine": 6 * (len(expected_names) + len(ocaml_results)),
              "outputs_identical": identical and all(row["outputs_identical"] for row in ocaml_results),
              "erlang_reference": erlang_reference,
              "all_passed": product_passed and identical and not changed and all(row["passed"] for row in results)
                            and all(row["passed"] for row in ocaml_results)
                            and (erlang_reference is None or erlang_reference["passed"]),
              "scope": "O0 structural IR, M0 rule questions and E0 mailbox operations; no complete source-language adequacy",
              "full_erlang_core_qualified": False, "full_maude_core_qualified": False,
              "full_ocaml_core_qualified": False}
    (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    if not record["all_passed"]:
        raise RuntimeError("OSLF/native qualification failed or its inputs changed")


if __name__ == "__main__":
    main()
