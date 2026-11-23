#!/usr/bin/env python3
"""Qualify the explicitly selected classical natural theory profile.

The source names one polymorphic selector, its law, classical reasoning and
Dedekind infinity. Native import receives exactly those three axiom names.
The result is a checked optional theory node, not a default of the Egal kernel.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


AXIOMS = ["niChoiceOption", "niClassicalOption", "niInfinityOption"]
SELECTED = ["niSelectedZeroNotSuccessor", "niSelectedSuccessorInjective",
            "niSelectedSuccessorNotOnto", "niSelectedInfinity",
            "niSelectedNaturalZero", "niSelectedNaturalSuccessor",
            "niSelectedNaturalInduction", "niSelectedRecursion"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    compiler, cetta = args.compiler.resolve(), args.cetta.resolve()
    sources = [root / "theory/logic" / name for name in
               ("NaturalClosure.mg", "NaturalRecursion.mg", "NaturalCarrier.mg",
                "NaturalTheoryProfile.mg")]
    inputs = sources + [compiler, cetta, cetta.parent / "lib/megalodon.metta",
                        Path(__file__).resolve(), root / "tools/checked-proof-stream.patch",
                        root / "tools/mathdata-export.patch"]
    pins = {str(path): digest(path) for path in inputs}
    record = dict(qualified=False, m1_qualified=False, status="running", cases=[], inputs=pins,
                  profile="optional classical natural theory",
                  selected_axioms=AXIOMS,
                  non_claims=["Not an Egal kernel default", "No HOTG assumptions",
                              "No choice law inferred from a function type",
                              "No equality with a separately authored natural carrier"])

    def save():
        (output / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command, expected=0):
        result = subprocess.run(list(map(str, command)), cwd=root, text=True,
                                capture_output=True, timeout=180)
        (output / (label + ".stdout")).write_text(result.stdout)
        (output / (label + ".stderr")).write_text(result.stderr)
        passed = result.returncode == expected if expected is not None else result.returncode != 0
        record["cases"].append(dict(case=label, passed=passed, returncode=result.returncode))
        save()
        if not passed:
            raise RuntimeError(f"{label}: unexpected return code")
        return result

    save()
    try:
        source = output / "source.mg"
        source.write_text("\n".join(path.read_text() for path in sources))
        result = run("source", [compiler, "-sexprinfo", source])
        if result.stderr or re.search(r"^\((PRIM|ADMITTED|QEDWITHADMITS)\b", result.stdout, re.M):
            raise RuntimeError("profile proof stream has diagnostics or hidden assumptions")
        counts = {tag: sum(line.startswith("(" + tag + " ") for line in result.stdout.splitlines())
                  for tag in ("THM", "DEF", "AXIOM", "PARAM")}
        if counts != {"THM": 40, "DEF": 16, "AXIOM": 3, "PARAM": 1}:
            raise RuntimeError(f"profile declaration inventory differs: {counts}")
        axioms = dict(re.findall(r'^\(AXIOM "([^"]+)" "([0-9a-f]{64})"', result.stdout, re.M))
        parameters = dict(re.findall(r'^\(PARAM "([^"]+)" "([0-9a-f]{64})"', result.stdout, re.M))
        roots = dict(re.findall(r'^\(THM "([^"]+)" "([0-9a-f]{64})"', result.stdout, re.M))
        if list(axioms) != AXIOMS or parameters != {
                "niChoose": "416ea32884c01532bc760e9c24df68a0d213108d4ceb03f323fa882259356389"} or \
                any(name not in roots for name in SELECTED):
            raise RuntimeError("profile assumption or selected-root identity differs")
        proofs = output / "proofs.sexpr"
        proofs.write_text(result.stdout)

        def program(policy):
            policy_atom = "(axioms" + "".join(" " + json.dumps(name) for name in policy) + ")"
            lines = ["!(import! &self megalodon)",
                     "!(let $state (mg:new-theory-state egal) (bind! &profile $state))",
                     "(= (T) (mg:use (get-state &profile)))",
                     "(= (AUTH) (mg:authority (get-state &profile)))",
                     f"!(mg:import (AUTH) {json.dumps(str(proofs))} {policy_atom})"]
            for name in SELECTED:
                identity = json.dumps(roots[name])
                lines += [f"!(ProfileControl {name} (mg:is-theorem (mg:known (T) {identity})))",
                          f"!(ProfileControl portable_{name} (mg:is-theorem "
                          f"(mg:check-evidence (T) (mg:evidence (mg:known (T) {identity})))))",
                          f"!(mg:dependencies (T) {identity})"]
            identity = json.dumps(roots["niSelectedRecursion"])
            lines += [f'!(case (mg:try-prove (T) "profile_forgery" (Tm.all (Tp.prop) (Tm.db 0)) '
                      f'(Pf.known {identity})) '
                      '(((Error $call $why) (ProfileControl changed_claim true)) '
                      '($other (ProfileControl changed_claim false))))',
                      '!(case (mg:try-known (T) "profile_forgery") '
                      '(((Error $call $why) (ProfileControl failed_publication true)) '
                      '($other (ProfileControl failed_publication false))))']
            return "\n".join(lines) + "\n"

        observations = []
        for dialect in ("he", "petta"):
            script = output / ("replay-" + dialect + ".metta")
            script.write_text(program(AXIOMS))
            native = run("native-" + dialect,
                         [cetta, "--lang", dialect, "--profile", "extended", script])
            if native.stderr:
                raise RuntimeError("native profile replay emitted diagnostics")
            packets = []
            for line in native.stdout.splitlines():
                if line.startswith("[(") and line.endswith("]"):
                    line = line[1:-1]
                if line.startswith("(ProfileControl "):
                    packets.append(line.replace(" True)", " true)").replace(" False)", " false)"))
            controls = SELECTED + ["portable_" + name for name in SELECTED] + \
                ["changed_claim", "failed_publication"]
            if len(packets) != len(controls) or any(
                    packets.count(f"(ProfileControl {name} true)") != 1 for name in controls):
                raise RuntimeError("native profile controls are incomplete")
            imports = [line for line in native.stdout.splitlines() if "(Megalodon.imported " in line]
            if len(imports) != 1:
                raise RuntimeError("native profile import result is missing or repeated")
            imported = dict(re.findall(r"\(([a-z-]+) ([0-9]+)\)", imports[0]))
            expected = dict(primitives="0", parameters="1", definitions="16", axioms="3",
                            theorems="40", unproved="0",
                            **{"depends-on-unproved": "0", "unsupported": "0"})
            if any(imported.get(key) != value for key, value in expected.items()):
                raise RuntimeError(f"native profile inventory differs: {imported}")
            observations.append(packets)
        if observations[0] != observations[1]:
            raise RuntimeError("native dialect observations differ")

        refusal_count = 0
        for omitted in AXIOMS:
            script = output / ("missing-" + omitted + ".metta")
            script.write_text(program([name for name in AXIOMS if name != omitted]))
            refused = run("missing-" + omitted,
                          [cetta, "--lang", "he", "--profile", "extended", script])
            if omitted not in refused.stdout + refused.stderr or \
                    "MegalodonRefused" not in refused.stdout + refused.stderr:
                raise RuntimeError(f"missing {omitted} failed for an unrelated reason")
            refusal_count += 1
        script = output / "empty-policy.metta"
        script.write_text(program([]))
        refused = run("empty-policy", [cetta, "--lang", "he", "--profile", "extended", script])
        if AXIOMS[0] not in refused.stdout + refused.stderr or \
                "MegalodonRefused" not in refused.stdout + refused.stderr:
            raise RuntimeError("empty policy failed for an unrelated reason")
        refusal_count += 1
        if any(digest(Path(path)) != value for path, value in pins.items()):
            raise RuntimeError("profile inputs changed during qualification")
        record.update(qualified=True, status="passed", declaration_counts=counts,
                      axiom_hashes=axioms, parameter_hashes=parameters, roots=roots,
                      native_controls_per_dialect=18, refusal_controls=refusal_count,
                      proof_sha256=digest(proofs),
                      remaining=["Typed semantic comparison with the selected source carrier",
                                 "Profile inclusion and checking-policy comparison"])
        print(json.dumps({key: record[key] for key in
                          ("qualified", "m1_qualified", "native_controls_per_dialect",
                           "refusal_controls")}))
        return 0
    except (OSError, subprocess.SubprocessError, RuntimeError, KeyError, ValueError) as error:
        record.update(status="failed", error=str(error))
        print(str(error))
        return 1
    finally:
        save()


if __name__ == "__main__":
    raise SystemExit(main())
