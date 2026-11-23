#!/usr/bin/env python3
"""Qualify the shared module-driven direct parser, replay and source printer."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import struct

from packed_source_reader import Commands, LEAN, REPO, TOOLS, build_native_reader, parse_direct_source
from source_io import SOURCE_BINARY, read_source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    commands = Commands(work / "commands")
    target = "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand"
    qualification = "Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxQualification"
    commands.run("proof-build", ["lake", "--wfail", "build", "sourceSyntax", qualification])
    binary, native_sources = build_native_reader(args.host, work / "native", commands, selections=True)
    files = {SOURCE_BINARY, LEAN / "Mettapedia/GSLT/LanguageDef/ModuleFormat/SourceSyntaxMain.lean", Path(__file__).resolve(), TOOLS / "source_io.py", TOOLS / "packed_source_reader.py",
             TOOLS / "source_family_selection.h", TOOLS / "source_plan_identity.h", binary, *native_sources}
    setup = LEAN / ".lake/build/ir" / Path(*target.split(".")).with_suffix(".setup.json")
    files.add(setup)
    modules = {target}
    for name, groups in json.loads(setup.read_text())["importArts"].items():
        if name.startswith("Mettapedia."):
            modules.add(name)
            files.update(Path(path) for group in groups for path in group)
    for name in modules:
        relative = Path(*name.split("."))
        files.update((LEAN / relative.with_suffix(".lean"), LEAN / ".lake/build/lib/lean" / relative.with_suffix(".olean")))
    files.update((REPO / "metta/gslt/module/gold").rglob("*.module"))
    files.update((REPO / "metta/gslt/tests/source_io").glob("*.module"))
    digest = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    pins = {str(path): digest(path) for path in files}
    (work / "input-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    prefix = ["lake", "env", str(SOURCE_BINARY)]
    results = []
    families = [
        ("datalog", REPO / "metta/gslt/module/gold/SouffleDatalog/Syntax.module",
         [REPO / "metta/gslt/tests/datalog/basic.dl"]),
        ("ocaml", REPO / "metta/gslt/module/gold/OCaml/Syntax.module",
         [REPO / "metta/gslt/module/gold/OCaml/examples/core_closures.ml"]),
        ("maude", REPO / "metta/gslt/module/gold/Maude/Syntax.module",
         [REPO / "metta/gslt/module/gold/Maude/examples/core_peano.maude"]),
        ("erlang", REPO / "metta/gslt/module/gold/Erlang/Syntax.module",
         [REPO / "metta/gslt/module/gold/Erlang/examples/core_multiple_values.core"]),
        ("composed", REPO / "metta/gslt/tests/source_io/SourceIO.module", []),
    ]
    for label, module, sources in families:
        directory = work / label
        directory.mkdir()
        driver = module.resolve()
        grammar = directory / "grammar"
        commands.run(label + "-export", [*prefix, driver, "export", grammar])
        if label == "composed":
            for name, text in (("ambiguous", "x"), ("ordered", "(x,y)"), ("duplicates", "(x,x)"),
                               ("unicode", "λ🙂"), ("empty", "")):
                source = directory / (name + ".source")
                source.write_text(text)
                sources.append(source)
        for source in sources:
            tag = label + "-" + source.stem
            forest = directory / (source.stem + ".cnf")
            status = parse_direct_source(binary, grammar, source, forest, commands, tag + "-parse",
                                         selected=True, result_limit=256)
            lines = (commands.work / (tag + "-parse.out")).read_text().splitlines()[1:]
            packets = [line for line in lines if line.startswith("(result ")]
            if status["outcome"] != 0 or not status["accepted"] or len(packets) != status["semanticResults"] or not packets:
                raise RuntimeError(tag + ": parsing/replay did not complete")
            if label == "composed" and len(packets) != {"ambiguous": 2, "ordered": 2, "duplicates": 4,
                                                         "unicode": 1, "empty": 1}[source.stem]:
                raise RuntimeError(tag + ": wrong number of retained alternatives")
            commands.run(tag + "-coverage", [*prefix, driver, "coverage", source, forest, str(forest) + ".pni",
                32 * (status["inputScalars"] + 1) + 256])
            catalogue = directory / (source.stem + ".packets")
            catalogue.write_text("\n".join(packets) + "\n")
            commands.run(tag + "-catalogue", [*prefix, driver, "catalogue", source, forest, str(forest) + ".pni",
                catalogue, 32 * (status["inputScalars"] + 1) + 256])
            cores = []
            for ordinal, packet in enumerate(packets):
                stem = source.stem + "-" + str(ordinal)
                packet_path = directory / (stem + ".packet")
                packet_path.write_text(packet + "\n")
                core = directory / (stem + ".core")
                printed = directory / (stem + ".printed")
                commands.run(tag + f"-{ordinal}-read", [*prefix, driver, "read", source, packet_path, core])
                commands.run(tag + f"-{ordinal}-print", [*prefix, driver, "print", core, printed])
                if printed.read_bytes() != source.read_bytes():
                    raise RuntimeError(tag + ": source text changed")
                replay_status = parse_direct_source(binary, grammar, printed, directory / (stem + "-again.cnf"),
                    commands, tag + f"-{ordinal}-parse-again", selected=True, result_limit=256)
                repeated = (commands.work / (tag + f"-{ordinal}-parse-again.out")).read_text().splitlines()[1:]
                if replay_status["outcome"] != 0 or repeated != packets:
                    raise RuntimeError(tag + ": reparsing changed retained alternatives")
                cores.append(core.read_bytes())
            if len(set(cores)) != len(cores):
                raise RuntimeError(tag + ": distinct constructor alternatives collapsed")
            results.append(dict(case=tag, alternatives=len(packets), bytes=source.stat().st_size,
                                exact_source_roundtrip=True, alternatives_retained=True,
                                authored_forest_representation=True, complete_whole_input_forest=True,
                                complete_selected_catalogue=True))
        # Missing constructor must fail at checked replay, not at import or compilation.
        if label == "composed":
            original = (directory / "duplicates.packets").read_text().splitlines()
            for mutation, changed in (("missing-result", original[:-1]),
                                      ("duplicate-result", original[:-1] + [original[0]])):
                catalogue = directory / (mutation + ".packets")
                catalogue.write_text("\n".join(changed) + "\n")
                rejected = subprocess.run([*prefix, str(driver), "catalogue", str(directory / "duplicates.source"),
                    str(directory / "duplicates.cnf"), str(directory / "duplicates.cnf.pni"), str(catalogue), "64"],
                    cwd=LEAN, capture_output=True, text=True)
                (directory / (mutation + ".log")).write_text(rejected.stdout + rejected.stderr)
                if rejected.returncode == 0 or "differ from the complete selected catalogue" not in rejected.stdout + rejected.stderr:
                    raise RuntimeError(mutation + ": native catalogue corruption was not rejected")
            malformed_packets = directory / "unknown-result.packets"
            malformed_packets.write_text("(result (node Missing nil) nil)\n")
            for diagnostic, catalogue, rounds, message in (
                ("pending-catalogue", directory / "duplicates.packets", "0", "selected catalogue construction remains pending"),
                ("invalid-catalogue", malformed_packets, "64", "invalid native forest or result catalogue")):
                rejected = subprocess.run([*prefix, str(driver), "catalogue", str(directory / "duplicates.source"),
                    str(directory / "duplicates.cnf"), str(directory / "duplicates.cnf.pni"), str(catalogue), rounds],
                    cwd=LEAN, capture_output=True, text=True)
                (directory / (diagnostic + ".log")).write_text(rejected.stdout + rejected.stderr)
                if rejected.returncode == 0 or message not in rejected.stdout + rejected.stderr:
                    raise RuntimeError(diagnostic + ": catalogue status was conflated")
            packet = directory / "bad.packet"
            packet.write_text('(result (node Missing nil) nil)\n')
            bad = subprocess.run([*prefix, str(driver), "read", str(sources[0]), str(packet), str(directory / "bad.core")],
                                 cwd=LEAN, capture_output=True, text=True)
            (directory / "bad.log").write_text(bad.stdout + bad.stderr)
            if bad.returncode == 0 or "selected source packet failed independent certificate replay" not in bad.stdout + bad.stderr:
                raise RuntimeError("missing constructor did not receive the intended rejection")
            trailing = directory / "trailing.source"
            trailing.write_text("xz")
            trailing_status = parse_direct_source(binary, grammar, trailing, directory / "trailing.cnf",
                commands, "trailing-input", selected=True, result_limit=256)
            if trailing_status["outcome"] != 0 or trailing_status["accepted"] or trailing_status["semanticResults"]:
                raise RuntimeError("whole-input recognition accepted a valid prefix with trailing input")
            empty_result = read_source(module, trailing, directory / "checked-empty", args.host,
                Commands(directory / "checked-empty-commands"))
            if empty_result["alternatives"] or not empty_result["selected_catalogue_checked"]:
                raise RuntimeError("empty result did not receive complete catalogue checking")
            results.append(dict(case="checked-empty-source", alternatives=0,
                                complete_whole_input_forest=True, complete_selected_catalogue=True))
            limited = parse_direct_source(binary, grammar, directory / "duplicates.source", directory / "limited.cnf",
                commands, "limited-results", selected=True, result_limit=1)
            if limited["outcome"] != 4:
                raise RuntimeError("limited alternatives did not remain an explicit pending result")
            identity = directory / "ambiguous.cnf.pni"
            for mutation, payload in (("truncated", identity.read_bytes()[:-1]),
                                      ("wrong-label", identity.read_bytes().replace(b"First", b"Wrong"))):
                corrupted = directory / (mutation + ".pni")
                corrupted.write_bytes(payload)
                rejected = subprocess.run([*prefix, str(driver), "forest", str(sources[0]),
                    str(directory / "ambiguous.cnf"), str(corrupted)], cwd=LEAN, capture_output=True, text=True)
                (directory / (mutation + ".log")).write_text(rejected.stdout + rejected.stderr)
                if rejected.returncode == 0 or "native forest failed authored-plan representation validation" not in rejected.stdout + rejected.stderr:
                    raise RuntimeError(mutation + ": identity corruption was not rejected")
            # Remove a valid alternative while preserving the physical forest's
            # structure. Representation alone must accept it; completeness must fail.
            raw = (directory / "ambiguous.cnf").read_bytes()
            header = list(struct.unpack_from("<14I", raw, 4))
            node_count, choice_count = header[1], header[2]
            nodes = [list(struct.unpack_from("<14I", raw, 60 + 56 * i)) for i in range(node_count)]
            choices = [list(struct.unpack_from("<6I", raw, 60 + 56 * node_count + 24 * i)) for i in range(choice_count)]
            rows = (grammar / "direct-productions.terms").read_text().splitlines()
            positions = [i for i, row in enumerate(rows) if '(pp-label (pp-def "Term") "Second")' in row]
            if len(positions) != 1:
                raise RuntimeError("omission fixture lost its unique production")
            retained = []
            for node in nodes:
                kept = [row for row in choices[node[12]:node[12] + node[13]] if row[3] != positions[0]]
                node[12], node[13] = len(retained), len(kept)
                retained.extend(kept)
            if len(retained) >= choice_count:
                raise RuntimeError("omission fixture removed no alternative")
            header[2] = len(retained)
            omitted = directory / "omitted-alternative.cnf"
            omitted.write_bytes(b"CNF1" + struct.pack("<14I", *header) +
                b"".join(struct.pack("<14I", *row) for row in nodes) +
                b"".join(struct.pack("<6I", *row) for row in retained) +
                raw[60 + 56 * node_count + 24 * choice_count:])
            commands.run("omission-representation", [*prefix, driver, "forest", sources[0], omitted, identity])
            rejected = subprocess.run([*prefix, str(driver), "coverage", str(sources[0]), str(omitted),
                str(identity), "64"], cwd=LEAN, capture_output=True, text=True)
            (directory / "omission-coverage.log").write_text(rejected.stdout + rejected.stderr)
            if rejected.returncode == 0 or "failed independent whole-input coverage" not in rejected.stdout + rejected.stderr:
                raise RuntimeError("a structurally valid omitted alternative passed completeness")
            (directory / "SourceIOBase.module").write_bytes((module.parent / "SourceIOBase.module").read_bytes())
            malformed = directory / "BadSelection.module"
            text = module.read_text().replace("Module SourceIO {", "Module BadSelection {", 1)
            text = text.replace("  theory Grammar(base.Grammar())", "  Theory SourceSelection() { Types { Selection; } }\n  theory Grammar(base.Grammar())")
            malformed.write_text(text)
            bad_driver = malformed.resolve()
            rejected = subprocess.run([*prefix, str(bad_driver), "export", str(directory / "bad-selection-grammar")],
                                      cwd=LEAN, capture_output=True, text=True)
            (directory / "bad-selection.log").write_text(rejected.stdout + rejected.stderr)
            if rejected.returncode == 0 or "declared SourceSelection port is malformed" not in rejected.stdout + rejected.stderr:
                raise RuntimeError("malformed declared selection silently defaulted or failed at the wrong boundary")
    # A valid grammar tree must still satisfy its module's declared policy.
    policy_module = REPO / "metta/gslt/tests/source_io/SourceIOPolicy.module"
    policy_directory = work / "policy"
    policy_directory.mkdir()
    policy_driver = policy_module.resolve()
    policy_grammar = policy_directory / "grammar"
    commands.run("policy-export", [*prefix, policy_driver, "export", policy_grammar])
    for word, constructor, accepted in (("x", "First", False), ("y", "Other", True)):
        source = policy_directory / (word + ".source")
        source.write_text(word)
        packet = policy_directory / (word + ".packet")
        packet.write_text(f"(result (node {constructor} nil) nil)\n")
        checked = subprocess.run([*prefix, str(policy_driver), "read", str(source), str(packet),
            str(policy_directory / (word + ".core"))], cwd=LEAN, capture_output=True, text=True)
        (policy_directory / (word + ".log")).write_text(checked.stdout + checked.stderr)
        if accepted:
            if checked.returncode != 0:
                raise RuntimeError("declared policy refused its positive packet")
        elif checked.returncode == 0 or "violates the declared selection policy" not in checked.stdout + checked.stderr:
            raise RuntimeError("a grammatical packet bypassed the declared policy")
        status = parse_direct_source(binary, policy_grammar, source, policy_directory / (word + ".cnf"),
            commands, "native-policy-" + word, selected=True, result_limit=16)
        if status["outcome"] != 0 or (status["semanticResults"] > 0) != accepted:
            raise RuntimeError("native and independent source policy disagree")
    changed = [path for path, before in pins.items() if digest(path) != before]
    if changed:
        raise RuntimeError("qualification inputs changed")
    record = dict(controls=results, missing_constructor_refused=True, trailing_input_refused=True,
        corrupted_identity_refused=True, malformed_selection_refused=True, limited_results_pending=True,
        grammatical_policy_bypass_refused=True, native_selection_matches_replay=True,
        missing_native_result_refused=True, duplicated_native_result_refused=True,
        invalid_and_pending_catalogues_distinguished=True,
        well_formed_omission_rejected_by_coverage=True, inputs_stable=True,
        foreign_grammar_compiler_used=False,
        scope="Shared imported-module direct ParserPack, independent whole-input forest completeness, complete selected certificate multiset, checked packet replay, declared-policy validation and exact source printing. Universal native C implementation verification and language binding/runtime correspondence remain separate obligations.")
    (work / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
