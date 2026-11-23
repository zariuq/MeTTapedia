#!/usr/bin/env python3
"""Read both candidate surfaces through the shared packed parser and expansion.

The gate checks complete forests and selected catalogues, replays every chosen
packet against the actual source, and compares expanded programs and ordered
answer atoms. Executable
agreement does not establish whole-family operational adequacy or C refinement.
"""

import argparse
import hashlib
import json
from pathlib import Path

from packed_source_reader import Commands, LEAN, REPO, TOOLS, build_native_reader, parse_direct_source


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta-source", type=Path, required=True)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--reader", type=Path)
    parser.add_argument("--swi-root", type=Path)
    parser.add_argument("--transform-library", type=Path)
    parser.add_argument("--expected-stderr", type=Path)
    parser.add_argument("--collect-failures", action="store_true")
    args = parser.parse_args()
    work = args.work.resolve()
    require(not work.exists(), "use a new evidence directory")
    work.mkdir(parents=True)
    commands = Commands(work)
    driver = TOOLS / "derived_transform_source.lean"
    authored = REPO / "metta/gslt/module/derived-transform"
    examples = authored / "examples"
    cases = json.loads((examples / "cases.json").read_text())["cases"]
    owner = LEAN / "Mettapedia/Languages/MeTTa/Experimental/DerivedTransformForms"
    inputs = [Path(__file__), TOOLS / "packed_source_reader.py", driver,
              *authored.glob("*.module"), *examples.iterdir(),
              *(owner / name for name in ("Presentations.lean", "Code.lean", "Lowering.lean"))]
    if args.swi_root:
        require(args.transform_library is not None, "SWI execution requires the complete authored transform library")
        inputs += [args.swi_root / "run.sh", args.transform_library]
    else:
        inputs.append(args.cetta.resolve())
    if args.expected_stderr:
        inputs.append(args.expected_stderr)
    pins = {path: sha(path) for path in inputs}
    if args.reader:
        reader = args.reader.resolve()
        native_inputs = [reader]
    else:
        reader, native_inputs = build_native_reader(args.cetta_source, work / "native", commands, selections=True)
    inputs += native_inputs
    pins.update({path: sha(path) for path in native_inputs})
    (work / "inputs.before.json").write_text(json.dumps(
        {str(path): pin for path, pin in pins.items()}, indent=2) + "\n")
    reader_pin = sha(reader)

    def lean(label, *arguments):
        return commands.run(label, ["lake", "env", "lean", "-DwarningAsError=true", "--run", driver, *arguments])

    controls = []

    def rejected(label, *arguments, message, output=None):
        try:
            lean(label, *arguments)
        except RuntimeError:
            require(commands.rows[-1]["label"] == label and commands.rows[-1]["exit_code"] != 0,
                    label + ": command did not reach a terminal refusal")
            diagnostic = (work / (label + ".out")).read_text() + (work / (label + ".err")).read_text()
            require(message in diagnostic, label + ": wrong refusal reason")
            require(output is None or not output.exists(), label + ": refused input produced an output")
            controls.append({"name": label, "passed": True})
        else:
            raise RuntimeError(label + ": invalid input was accepted")

    def packets(label, row):
        records = (work / (label + ".out")).read_text().splitlines()[1:]
        require(len(records) == row["semanticResults"], label + ": retained result count differs")
        return records

    # Two genuine authored productions for one spelling must survive selection.
    ambiguous_grammar = work / "ambiguity-grammar"
    lean("export-ambiguity", "ambiguity", "export", ambiguous_grammar)
    ambiguous_source = work / "ambiguity.source"
    ambiguous_source.write_text("(value x)")
    ambiguous_forest = work / "ambiguity.forest"
    ambiguous = parse_direct_source(reader, ambiguous_grammar, ambiguous_source, ambiguous_forest,
                                    commands, "parse-ambiguity", selected=True, result_limit=64)
    require(ambiguous["accepted"] and ambiguous["semanticResults"] == 2,
            "ambiguity: the two authored derivations were not retained")
    records = packets("parse-ambiguity", ambiguous)
    catalogue = work / "ambiguity.packets"
    catalogue.write_text("\n".join(records) + "\n")
    identity = str(ambiguous_forest) + ".pni"
    lean("ambiguity-coverage", "ambiguity", "coverage", ambiguous_source, ambiguous_forest, identity, "1024")
    lean("ambiguity-catalogue", "ambiguity", "catalogue", ambiguous_source, ambiguous_forest,
         identity, catalogue, "1024")
    for name, changed in (("missing", records[:1]), ("duplicated", [records[0], records[0]])):
        mutation = work / ("ambiguity-" + name + ".packets")
        mutation.write_text("\n".join(changed) + "\n")
        rejected("ambiguity-" + name, "ambiguity", "catalogue", ambiguous_source, ambiguous_forest,
                 identity, mutation, "1024", message="differ from the complete selected catalogue")
    rejected("ambiguity-pending", "ambiguity", "catalogue", ambiguous_source, ambiguous_forest,
             identity, catalogue, "0", message="selected catalogue construction remains pending")
    for index, record in enumerate(records):
        retained = work / (f"ambiguity-{index}.packet")
        retained.write_text(record + "\n")
        core = work / (f"ambiguity-{index}.core")
        lean(f"ambiguity-read-{index}", "ambiguity", "read", ambiguous_source, retained, core)
        if "DValueAlternative" in record:
            output = work / "foreign-packet.expanded.metta"
            rejected("foreign-packet", "lower", "expression", ambiguous_source, retained, output,
                     message="source packet does not reproduce this complete input", output=output)
    require(any(control["name"] == "foreign-packet" for control in controls),
            "ambiguity: foreign grammar control was not exercised")

    results = []
    failures = []
    expanded = {}
    expected_atoms = {}
    for style, suffix in (("expression", "expr"), ("interaction", "rules")):
        grammar = work / (style + "-grammar")
        lean("export-" + style, "export", style, grammar)
        for case in cases:
            name = case["name"]
            label = style + "-" + name
            source = examples / (name + "." + suffix)
            forest = work / (label + ".forest")
            row = parse_direct_source(reader, grammar, source, forest, commands, "parse-" + label,
                                      selected=True, result_limit=64)
            require(row["accepted"] and row["semanticResults"] == 1,
                    label + ": expected one complete retained parse, without a first-parse fallback")
            packet = work / (label + ".packet")
            packet.write_text("\n".join(packets("parse-" + label, row)) + "\n")
            lean("forest-" + label, "forest", style, source, forest, str(forest) + ".pni")
            rounds = str(32 * (row["inputScalars"] + 1) + 256)
            lean("coverage-" + label, "coverage", style, source, forest, str(forest) + ".pni", rounds)
            lean("catalogue-" + label, "catalogue", style, source, forest, str(forest) + ".pni", packet, rounds)
            output = work / (label + ".expanded.metta")
            lean("lower-" + label, "lower", style, source, packet, output)
            require(not (work / ("lower-" + label + ".err")).read_bytes(), label + ": lowering diagnostic")
            program = output.read_text()
            if name in expanded:
                require(program == expanded[name], name + ": surfaces expanded to different source programs")
            else:
                expanded[name] = program
            setup = examples / (name + ".setup.metta")
            probes = examples / (name + ".probes.metta")
            complete = work / (label + ".metta")
            complete.write_text((setup.read_text() if setup.exists() else "") + program +
                                (probes.read_text() if probes.exists() else ""))
            if args.swi_root:
                reference = work / (label + ".reference.metta")
                reference.write_text(args.transform_library.read_text() + "\n" + complete.read_text())
                runtime = ["bash", args.swi_root / "run.sh", reference, "--silent"]
            else:
                runtime = [args.cetta, "--lang", "petta", "--profile", "extended", complete]
            observed = commands.run("execute-" + label, runtime)
            expected = examples / (name + ".expected")
            if name not in expected_atoms:
                expected_atoms[name] = work / (name + ".expected-atoms")
                lean("normalize-expected-" + name, "normalize", expected, expected_atoms[name])
            observed_atoms = work / (label + ".observed-atoms")
            lean("normalize-observed-" + label, "normalize", observed, observed_atoms)
            diagnostics = work / ("execute-" + label + ".err")
            stderr = args.expected_stderr.read_bytes() if args.expected_stderr else b""
            passed = (observed_atoms.read_bytes() == expected_atoms[name].read_bytes()
                      and diagnostics.read_bytes() == stderr)
            if not passed:
                failures.append(label)
                require(args.collect_failures, label + ": runtime observation or diagnostic differs")
            results.append({"name": name, "surface": style, "parser": row,
                            "source_sha256": sha(source), "forest_sha256": sha(forest),
                            "identity_sha256": sha(str(forest) + ".pni"), "packet_sha256": sha(packet),
                            "expanded_sha256": sha(output), "program_sha256": sha(complete),
                            "expected_sha256": sha(examples / (name + ".expected")),
                            "observed_sha256": sha(observed), "stderr_sha256": sha(diagnostics),
                            "expected_atoms_sha256": sha(expected_atoms[name]),
                            "observed_atoms_sha256": sha(observed_atoms),
                            "complete_forest": True, "complete_selected_catalogue": True,
                            "runtime_passed": passed})
            (work / "results.json").write_text(json.dumps(results, indent=2) + "\n")

        for name, spelling in (("trailing", "(value x) trailing" if style == "expression" else "emit x trailing"),
                               ("malformed", "(once" if style == "expression" else "first {")):
            source = work / (style + "-" + name + ".source")
            source.write_text(spelling)
            forest = work / (style + "-" + name + ".forest")
            row = parse_direct_source(reader, grammar, source, forest, commands, "parse-" + style + "-" + name,
                                      selected=True, result_limit=64)
            require(not row["accepted"] and row["semanticResults"] == 0, style + ": invalid source accepted")
            lean(style + "-" + name + "-coverage", "coverage", style, source, forest,
                 str(forest) + ".pni", "1024")
            controls.append({"name": style + "-" + name, "passed": True})
        source = work / (style + "-nonvariable-chain.source")
        source.write_text("(chain (value a) a (value b))" if style == "expression" else "chain a <- { emit a } ; { emit b }")
        forest = work / (style + "-nonvariable-chain.forest")
        label = style + "-nonvariable-chain"
        row = parse_direct_source(reader, grammar, source, forest, commands, "parse-" + label,
                                  selected=True, result_limit=64)
        require(row["accepted"] and row["semanticResults"] == 1, label + ": expected parsed invalid binder")
        packet = work / (label + ".packet")
        packet.write_text("\n".join(packets("parse-" + label, row)) + "\n")
        output = work / (label + ".expanded.metta")
        rejected(label, "lower", style, source, packet, output,
                 message="chain binder must be a variable", output=output)
        wrong_source = work / (style + "-wrong-input.source")
        wrong_source.write_text("(value y)" if style == "expression" else "emit y")
        held_packet = work / (style + "-held-code.packet")
        wrong_output = work / (style + "-wrong-input.expanded.metta")
        rejected(style + "-wrong-input", "lower", style, wrong_source, held_packet, wrong_output,
                 message="source packet does not reproduce this complete input", output=wrong_output)

    changed = [str(path) for path, pin in pins.items() if sha(path) != pin]
    (work / "inputs.after.json").write_text(json.dumps(
        {"pins": {str(path): sha(path) for path in pins}, "changed": changed}, indent=2) + "\n")
    require(not changed, "an input changed during qualification: " + ", ".join(changed))
    require(sha(reader) == reader_pin, "reader binary changed during qualification")
    record = {"passed": not failures, "paired_programs": len(cases), "executions": len(results),
              "runtime": "authored SWI-PeTTa" if args.swi_root else "CeTTa", "failed": failures,
              "controls": controls,
              "cetta_sha256": sha(args.cetta) if not args.swi_root else None,
              "reader_sha256": reader_pin,
              "input_pins": {str(path.relative_to(REPO)) if path.is_relative_to(REPO) else path.name: sha(path)
                             for path in inputs},
              "scope": "authored syntax, complete retained parser results, checked packet replay, source expansion and calibration observations",
              "whole_family_operational_adequacy": False, "c_correspondence": False}
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{len(cases)} paired programs; {len(results) - len(failures)}/{len(results)} runtime observations passed")
    require(not failures, "runtime discrepancies remain: " + ", ".join(failures))


if __name__ == "__main__":
    main()
