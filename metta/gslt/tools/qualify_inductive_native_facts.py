#!/usr/bin/env python3
"""Replay the available M1 native fact routes on one CeTTa executable.

Run in the project's Lean environment, after building the statement emitters'
dependencies. The configuration names existing proof producers and a retained
HOL Light source closure; this driver neither proves facts nor admits axioms.
Native acceptance, exact source statements and authored-carrier correspondence
are separate obligations. Passing these component gates does not complete M1.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time


CONFIG_KEYS = {"mm0_compiler", "mm0_reference", "megalodon", "hol_source",
               "hol_closure_helper", "hol_adapter", "hol_stream_tools", "hol_source_tools"}
HOL_ROOTS = ["num_RECURSION", "num_INDUCTION", "NOT_SUC", "SUC_INJ", "NAT_CARRIER_INFINITY"]
MM0_ROOTS = ["naturalClosureZero", "naturalClosureSuccessor", "naturalClosureElimination",
             "naturalClosureInduction", "infiniteSuccessorT", "infiniteSuccessorInjective",
             "infiniteSuccessorNotOnto", "infiniteZeroT", "infiniteZeroNoPreimage",
             "infiniteZeroNotSuccessor", "holZeroT", "holSuccessorT", "holZeroNotSuccessor",
             "holSuccessorInjective", "holNaturalInduction", "holNaturalInfinity",
             "holRecursionGraphElimination", "holRecursionGraphZero", "holRecursionGraphSuccessor",
             "holRecursionGraphExists", "holRecursionGraphZeroUnique", "holRecursionGraphSuccessorInverse",
             "holRecursionGraphFunctional", "holRecursorT", "holRecursorGraph", "holRecursorZero",
             "holRecursorSuccessor", "holNaturalRecursion"]
MM0_PROFILE = "HOL natural subtype: primitive recursion from a total functional graph"
MM0_CONTROLS = 74
MM0_MEANING = {
    "authored_meaning": "IndexedInductiveNaturalMM0.all_models",
    "authored_graph_meaning": "IndexedInductiveNaturalMM0.source_graph_iff",
    "authored_selector_meaning": "IndexedInductiveNaturalMM0.source_selector_agrees",
    "meaning_scope": "standard authored natural interpretation; explicit selection law",
}
MEGALODON_PROFILE_MEANING = {
    "profile": "optional classical natural theory",
    "axioms": ["niChoiceOption", "niClassicalOption", "niInfinityOption"],
    "parameter": "niChoose",
    "roots": ["niSelectedZeroNotSuccessor", "niSelectedSuccessorInjective",
              "niSelectedSuccessorNotOnto", "niSelectedInfinity",
              "niSelectedNaturalZero", "niSelectedNaturalSuccessor",
              "niSelectedNaturalInduction", "niSelectedRecursion"],
    "carrier_meaning": "IndexedInductiveNaturalMegalodonProfile.sourceOptions",
    "successor_meaning": "IndexedInductiveNaturalMegalodonProfile.selected_successor_eq",
    "zero_meaning": "IndexedInductiveNaturalMegalodonProfile.selected_zero_eq",
    "recursion_meaning": "IndexedInductiveNaturalMegalodonProfile.source_recursor_agrees",
    "meaning_scope": "authored natural carrier; explicit optional theory assumptions",
}
MM0_REFERENCE_CASES = [
    ("published", True), ("typed", True), ("changed-definition", False),
    ("changed-conclusion", False), ("reverted-type-definition", False),
    ("changed-strengthening", False), ("changed-injection", False), ("changed-zero", False),
    ("lost-no-confusion", False), ("wrong-zero-type", False), ("changed-natural-predicate", False),
    ("wrong-natural-equality", False), ("missing-natural-step", False), ("changed-pullback", False),
    ("changed-graph-output", False), ("reversed-graph-method", False),
    ("changed-recursive-selection", False), ("missing-second-graph", False),
    ("reversed-recursion-method", False)]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def project_source_pins(roots, lean):
    """Fingerprint the project import closure of the Lean source producers.

    Reuse the subject-boundary audit's comment-aware import inventory.
    It does not establish that compiled artifacts were built from these sources.
    """
    scanner_path = lean / "scripts/check_two_sort_boundaries.py"
    spec = importlib.util.spec_from_file_location("m1_import_inventory", scanner_path)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    pins = {str(scanner_path): digest(scanner_path)}

    def visit(path):
        path = Path(path).absolute()
        if str(path) in pins:
            return
        pins[str(path)] = digest(path)
        for module in scanner.imports(scanner.mask_lean(path.read_text())[1]):
            if module.startswith("Mettapedia."):
                visit(lean.joinpath(*module.split(".")).with_suffix(".lean"))

    for root in roots:
        visit(root)
    return pins


def validate_hol_record(hol, binary, binary_hash, expected):
    """Intake identity for the maintained HOL gate, not another proof checker."""
    require(hol.get("qualified") is True and hol.get("selected_fact_interface_qualified") is True and
            hol.get("m1_qualified") is False, "HOL component scope or qualification differs")
    require(hol.get("binary_sha256") == binary_hash and
            hol["input_pins"].get(str(binary)) == binary_hash, "HOL used a different binary")
    require(expected.get("profile") == "standard" and
            expected.get("authored_meaning") == "IndexedInductiveNaturalHOL.NativeFacts.all_models",
            "HOL policy or authored interpretation differs")
    require([row["name"] for row in expected["facts"]] == HOL_ROOTS and
            hol.get("roots") == expected["facts"], "HOL typed statements or root inventory differ")
    require(hol.get("meaning") == expected["authored_meaning"], "HOL authored meaning differs")
    require(type(hol.get("source_axioms_added")) is int and hol["source_axioms_added"] == 0 and
            len(hol["source_axiom_nodes"]) == 3 and len(set(hol["source_axiom_nodes"])) == 3,
            "HOL source assumption inventory differs")
    require(hol.get("native_refusals") == 3 and hol.get("packet_refusals") == 3,
            "HOL refusal coverage differs")
    require(hol.get("full_source_definition_history_refinement") is False,
            "HOL full definition-history refinement is not established")


def validate_native_records(mm0, meg, binary, binary_hash, mm0_expected, meg_expected):
    """Check route identity and finite coverage without granting broader authority."""
    require(all(mm0_expected.get(key) == value for key, value in MM0_MEANING.items()),
            "MM0 authored interpretation or its scope differs")
    require(mm0.get("qualified") is True and mm0.get("source_axioms_added") == 0,
            "MM0 route did not qualify without new source axioms")
    require(mm0["input_sha256"].get(str(binary)) == binary_hash and
            meg["inputs"].get(str(binary)) == binary_hash, "native routes used a different binary")
    require(mm0.get("profile") == MM0_PROFILE, "MM0 selected recursion profile differs")
    require([(row["dialect"], row["controls"]) for row in mm0["native"]] ==
            [("he", MM0_CONTROLS), ("petta", MM0_CONTROLS), ("prime", MM0_CONTROLS)], "incomplete MM0 dialect/control coverage")
    for row in mm0["native"]:
        require([item["label"] for item in row["results"]] ==
                [f'{row["dialect"]}-{index:02}' for index in range(MM0_CONTROLS)],
                "missing or repeated MM0 result packets")
        require([item["value"] for item in row["results"]][2:2 + len(MM0_ROOTS)] ==
                [mm0_expected[name] for name in MM0_ROOTS], "MM0 statements differ from fresh Lean output")
        require(row["results"][2 + len(MM0_ROOTS)]["value"] == mm0_expected["type_definition_axiom"],
                "MM0 type-definition declaration differs from fresh Lean output")
    require([(row["case"], row["returncode"] == 0) for row in mm0["reference_checks"]] ==
            MM0_REFERENCE_CASES, "incomplete MM0 independent-reference coverage")
    require(set(mm0["upstream_proof_dependencies"]) == set(MM0_ROOTS) and
            all(mm0["upstream_proof_dependencies"].values()), "missing MM0 assumption inventory")
    require({"inf", "ax_sel", "abs_rep", "rep_abs"} <=
            set(mm0["upstream_proof_dependencies"]["holNaturalRecursion"]),
            "MM0 recursion assumption scope differs from the checked source")
    require(meg.get("profile") == "recursion" and meg.get("selected_observations_equal") is True,
            "Megalodon conditional-recursion route did not qualify")
    require([(row["dialect"], row["controls"], row["exact_statements"], row["imported_axioms"],
              row["proved_theorems"], row["definitions"]) for row in meg["runs"]] ==
            [("he", 23, 4, 0, 24, 7), ("petta", 23, 4, 0, 24, 7)],
            "incomplete Megalodon dialect/statement/assumption coverage")
    require(meg["roots"]["nrRecursion"] == meg_expected["recursion_name"],
            "Megalodon recursion identity differs from fresh Lean output")


def validate_megalodon_profile(build, carrier, profile, binary, binary_hash, expected):
    """Keep source export, native replay and selected theory meaning distinct."""
    require(expected == MEGALODON_PROFILE_MEANING,
            "Megalodon selected profile or authored interpretation differs")
    require(build.get("built") is True and build.get("status") == "passed" and
            build.get("semantic_qualification") is False,
            "Megalodon source compiler build scope differs")
    require(carrier.get("qualified") is True and carrier.get("m1_qualified") is False and
            carrier.get("theorem_count") == 32 and carrier.get("definition_count") == 14 and
            carrier.get("imported_axioms") == 0 and
            carrier.get("native_controls_per_dialect") == 18 and
            carrier.get("previous_stream_unchanged") is True,
            "Megalodon axiom-free carrier qualification differs")
    require(profile.get("qualified") is True and profile.get("m1_qualified") is False and
            profile.get("profile") == expected["profile"] and
            profile.get("selected_axioms") == expected["axioms"] and
            list(profile.get("parameter_hashes", {})) == [expected["parameter"]] and
            profile.get("native_controls_per_dialect") == 18 and
            profile.get("refusal_controls") == 4 and
            profile.get("declaration_counts") ==
              {"THM": 40, "DEF": 16, "AXIOM": 3, "PARAM": 1},
            "Megalodon optional theory qualification differs")
    require(all(name in profile["roots"] for name in expected["roots"]),
            "Megalodon selected root inventory differs")
    require(carrier["inputs"].get(str(binary)) == binary_hash and
            profile["inputs"].get(str(binary)) == binary_hash,
            "Megalodon carrier/profile used a different native binary")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--config", type=Path, required=True,
                        help="JSON paths for the existing MM0, Megalodon and HOL source producers")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    lean = repo / "lean/mettapedia"
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    binary = args.cetta.resolve()
    report = dict(qualified=False, m1_qualified=False, status="running", stages=[],
                  scope="Available native facts on a single executable; distinct statements and assumptions per route",
                  remaining=["Remaining selected DTT profile and annotated-preservation comparisons"],
                  non_claims=["No proof of linked native C or producer correctness",
                              "No identification of ordinary closure elimination with closure-premised induction",
                              "No unconditional Peano recursion from a conditional theorem",
                              "No Megalodon Prime-mode qualification",
                              "HOL law-signature interpretation is not full source definition-history refinement"])
    pins = {}

    def save():
        (output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")

    def pin(path):
        path = Path(path).absolute()
        value = digest(path)
        require(str(path) not in pins or pins[str(path)] == value, "input changed between stages")
        pins[str(path)] = value

    def merge_pins(values):
        for path, value in values.items():
            pin(path)
            require(pins[str(Path(path).absolute())] == value, "gate input differs from retained input")

    def run(label, command, code=0, diagnostic=None):
        start = time.monotonic()
        result = subprocess.run(list(map(str, command)), cwd=lean, capture_output=True,
                                text=True, timeout=300, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        (output / (label + ".stdout")).write_text(result.stdout)
        (output / (label + ".stderr")).write_text(result.stderr)
        passed = result.returncode == code and (diagnostic is None or diagnostic in result.stderr)
        report["stages"].append(dict(name=label, passed=passed, returncode=result.returncode,
                                     seconds=round(time.monotonic() - start, 6)))
        save()
        require(passed, label + " failed; see captured diagnostics")
        return result

    save()
    try:
        config = json.loads(args.config.read_text())
        require(set(config) == CONFIG_KEYS, "native fact configuration has missing or unknown keys")
        config = {key: Path(value).resolve() for key, value in config.items()}
        for path in (Path(__file__), binary, args.config.resolve(), lean / "lean-toolchain",
                     lean / "lake-manifest.json"):
            pin(path)

        emitters = {"mm0": lean / "scripts/emit_mm0_natural_recursion.lean",
                    "megalodon": lean / "scripts/emit_megalodon_natural_closure.lean",
                    "megalodon_profile": lean / "scripts/emit_megalodon_natural_profile.lean",
                    "hol_light": lean / "scripts/emit_hol_natural_facts.lean"}
        gates = {"mm0": repo / "metta/mm0/hol/check_natural_closure.py",
                 "megalodon": repo / "megalodon/tools/check_natural_closure.py",
                 "hol_light": repo / "MettaKernel/Curriculum/HOL/check_natural_facts.py"}
        merge_pins(project_source_pins(emitters.values(), lean))
        for name in gates:
            pin(gates[name])
        expected = {}
        for name, emitter in emitters.items():
            result = run(name + "-typed-statements", ["lean", "--run", emitter] +
                         (["recursion"] if name == "megalodon" else []))
            require(not result.stderr.strip(), "statement emitter produced diagnostics")
            expected[name] = json.loads(result.stdout)
            path = output / (name + "-expected.json")
            path.write_text(json.dumps(expected[name], indent=2) + "\n")
            pin(path)
        run("mm0-native", [sys.executable, gates["mm0"], "--cetta", binary,
            "--compiler", config["mm0_compiler"], "--reference", config["mm0_reference"],
            "--module", "NaturalRecursion",
            "--expected", output / "mm0-expected.json", "--output", output / "mm0"])
        run("megalodon-native", [sys.executable, gates["megalodon"], "--cetta", binary,
            "--megalodon", config["megalodon"], "--profile", "recursion",
            "--expected", output / "megalodon-expected.json", "--output", output / "megalodon"])
        mm0 = json.loads((output / "mm0/qualification.json").read_text())
        meg = json.loads((output / "megalodon/qualification.json").read_text())
        validate_native_records(mm0, meg, binary, pins[str(binary)], expected["mm0"], expected["megalodon"])
        merge_pins(mm0["input_sha256"])
        merge_pins(meg["inputs"])
        checked_artifacts = {
            output / "mm0/natural-closure.mmb": mm0["artifact_sha256"],
            output / "mm0/typed-reference.mm0": mm0["typed_reference_sha256"],
            output / "megalodon/proofs.sexpr": meg["proof_sha256"],
        }
        for path, value in checked_artifacts.items():
            pin(path)
            require(pins[str(path)] == value, "native gate artifact changed before intake")

        compiler_builder = repo / "megalodon/tools/build_source_candidate.py"
        carrier_gate = repo / "megalodon/tools/test_source_export.py"
        profile_gate = repo / "megalodon/tools/test_natural_profile.py"
        for path in (compiler_builder, carrier_gate, profile_gate,
                     repo / "megalodon/tools/mathdata-export.patch"):
            pin(path)
        compiler_dir = output / "megalodon-source-compiler"
        run("megalodon-source-compiler", [sys.executable, compiler_builder,
            "--output", compiler_dir])
        compiler_build = json.loads((compiler_dir / "build.json").read_text())
        compiler = compiler_dir / "megalodon"
        pin(compiler_dir / "build.json")
        pin(compiler)
        run("megalodon-carrier", [sys.executable, carrier_gate,
            "--compiler", compiler, "--baseline", config["megalodon"],
            "--cetta", binary, "--output", output / "megalodon-carrier"])
        run("megalodon-profile", [sys.executable, profile_gate,
            "--compiler", compiler, "--cetta", binary,
            "--output", output / "megalodon-profile"])
        carrier = json.loads((output / "megalodon-carrier/qualification.json").read_text())
        profile = json.loads((output / "megalodon-profile/qualification.json").read_text())
        validate_megalodon_profile(compiler_build, carrier, profile, binary,
                                   pins[str(binary)], expected["megalodon_profile"])
        merge_pins(compiler_build["inputs"])
        merge_pins(carrier["inputs"])
        merge_pins(profile["inputs"])
        carrier_proofs = output / "megalodon-carrier/proofs.sexpr"
        profile_proofs = output / "megalodon-profile/proofs.sexpr"
        pin(carrier_proofs)
        pin(profile_proofs)
        require(pins[str(carrier_proofs)] == carrier["proof_sha256"] and
                pins[str(profile_proofs)] == profile["proof_sha256"],
                "Megalodon carrier/profile proof stream changed before intake")

        run("hol-native-facts", [sys.executable, gates["hol_light"], "--cetta", binary,
            "--source", config["hol_source"], "--closure-helper", config["hol_closure_helper"],
            "--source-tools", config["hol_source_tools"], "--stream-tools", config["hol_stream_tools"],
            "--adapter", config["hol_adapter"], "--expected", output / "hol_light-expected.json",
            "--output", output / "hol-light"])
        hol = json.loads((output / "hol-light/qualification.json").read_text())
        validate_hol_record(hol, binary, pins[str(binary)], expected["hol_light"])
        merge_pins(hol["input_pins"])
        wire = output / "hol-light/natural-facts.holr"
        require(pins.get(str(wire)) == hol["artifact_sha256"],
                "HOL artifact differs from accepted native input")
        assumptions = []
        nodes = output / "hol-light/source/closure.nodes.jsonl"
        require(str(nodes) in pins, "HOL source assumption records are not pinned")
        with nodes.open() as handle:
            for line in handle:
                node = json.loads(line)
                if node["rule"] == "AXIOM":
                    assumptions.append(dict(source_id=node["id"], theorem=node["theorem"]))
        require([row["source_id"] for row in assumptions] == hol["source_axiom_nodes"],
                "HOL assumption statements differ from the accepted source inventory")

        # Revalidate source identity at the join; native artifact acceptance alone is insufficient.
        for path, value in pins.items():
            require(digest(Path(path)) == value, "input changed during native qualification")
        artifacts = [wire, output / "mm0/natural-closure.mmb", output / "mm0/typed-reference.mm0",
                     output / "megalodon/proofs.sexpr", carrier_proofs, profile_proofs]
        report.update(qualified=True, status="passed", binary=str(binary), binary_sha256=pins[str(binary)], input_pins=pins,
            artifacts={str(path): digest(path) for path in artifacts},
            mm0=dict(statement_kind="natural subtype, constructor laws, induction, infinity and primitive recursion; standard authored interpretation",
                     meaning={key: expected["mm0"][key] for key in MM0_MEANING},
                     full_source_definition_history_refinement=False,
                     evidence=mm0, statements=expected["mm0"]),
            megalodon=dict(statement_kind="closure-premised induction and conditional unique recursion",
                           evidence=meg, statements=expected["megalodon"]),
            megalodon_profile=dict(statement_kind=
                "authored natural laws under explicit selection, classical and infinity options",
                compiler=compiler_build, carrier=carrier, evidence=profile,
                statements=expected["megalodon_profile"],
                default_kernel_axioms_added=0, full_source_definition_history_refinement=False),
            hol_light=dict(statement_kind="typed natural-law signature with authored-carrier interpretation",
                           evidence=hol, statements=expected["hol_light"], profile="standard",
                           source_axioms=assumptions,
                           reference_only=False, full_source_definition_history_refinement=False),
            trust="Native checkers/toolchain are qualified implementations, not proved linked C; producers are untrusted")
        save()
        print(json.dumps(dict(qualified=True, m1_qualified=False, native_routes=3,
                             stages=len(report["stages"]))))
        return 0
    except (OSError, subprocess.SubprocessError, ValueError, KeyError, TypeError, RuntimeError) as error:
        report.update(status="failed", error=str(error), input_pins=pins)
        save()
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
