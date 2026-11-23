#!/usr/bin/env python3
"""Qualify Mathdata source export and native replay independently of Proofgold.

The carrier's classical, infinity and selection interfaces remain hypotheses.
These checks establish finite proof replay and producer regression coverage;
they do not discharge those interfaces in a selected logical theory.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--baseline", required=True, type=Path)
    parser.add_argument("--cetta", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    compiler, baseline, cetta = (path.resolve() for path in (args.compiler, args.baseline, args.cetta))
    sources = [root / "theory/logic" / name for name in
               ("NaturalClosure.mg", "NaturalRecursion.mg", "NaturalCarrier.mg")]
    inputs = sources + [compiler, baseline, cetta, cetta.parent / "lib/megalodon.metta",
                        Path(__file__).resolve(), root / "tools/checked-proof-stream.patch",
                        root / "tools/mathdata-export.patch"]
    pins = {str(path): digest(path) for path in inputs}
    record = dict(qualified=False, m1_qualified=False, inputs=pins, cases=[],
                  scope="Explicit-interface carrier construction; source export and finite native replay")

    def save():
        (out / "qualification.json").write_text(json.dumps(record, indent=2) + "\n")

    def run(label, command, expected=0):
        result = subprocess.run(list(map(str, command)), cwd=root,
                                capture_output=True, text=True, timeout=120)
        (out / (label + ".stdout")).write_text(result.stdout)
        (out / (label + ".stderr")).write_text(result.stderr)
        passed = result.returncode == expected if expected is not None else result.returncode != 0
        record["cases"].append(dict(case=label, passed=passed, returncode=result.returncode))
        save()
        if not passed:
            raise RuntimeError(f"{label}: unexpected return code")
        return result

    save()
    try:
        previous = out / "previous.mg"
        previous.write_text("\n".join(path.read_text() for path in sources[:2]))
        old = run("baseline-previous", [baseline, "-sexprinfo", previous])
        new = run("candidate-previous", [compiler, "-sexprinfo", previous])
        if old.stderr or new.stderr or old.stdout != new.stdout:
            raise RuntimeError("earlier natural proof streams differ")
        source = out / "carrier.mg"
        source.write_text(previous.read_text() + "\n" + sources[2].read_text())
        failure = run("baseline-carrier-refusal", [baseline, "-sexprinfo", source], None)
        if "no polymorphism allowed in pfg:" not in failure.stdout + failure.stderr:
            raise RuntimeError("baseline failed for an unrelated reason")
        result = run("candidate-carrier", [compiler, "-sexprinfo", source])
        if result.stderr or re.search(r"^\((AXIOM|PARAM|PRIM|ADMITTED|QEDWITHADMITS)\b", result.stdout, re.M):
            raise RuntimeError("carrier stream has diagnostics or unrequested assumptions")
        if sum(line.startswith("(THM ") for line in result.stdout.splitlines()) != 32 or \
                sum(line.startswith("(DEF ") for line in result.stdout.splitlines()) != 14:
            raise RuntimeError("unexpected carrier theorem/definition inventory")
        for flag in ("-pfg", "-pfgsummary"):
            rejected = run("requested-" + flag[1:], [compiler, "-sexprinfo", flag, source], None)
            if "no polymorphism allowed in pfg:" not in rejected.stdout + rejected.stderr:
                raise RuntimeError("requested Proofgold export failed for an unrelated reason")
        malformed = out / "malformed.mg"
        malformed.write_text(source.read_text() + "\nTheorem niForgery : nrFalse.\n"
                             "exact nrEqRefl set (niZero (fun P:set->prop => "
                             "(fun x:set => x)) (fun P:(set->set)->prop => (fun x:set => x))).\nQed.\n")
        run("malformed-proof", [compiler, "-sexprinfo", malformed], None)
        proofs = out / "proofs.sexpr"
        proofs.write_text(result.stdout)
        roots = dict(re.findall(r'^\(THM "([^"]+)" "([0-9a-f]{64})"', result.stdout, re.M))
        selected = ["niNotAll", "niNotOntoHasOmitted", "niSuccessorInjective", "niSuccessorNotOnto",
                    "niZeroNotSuccessor", "niNaturalZero", "niNaturalSuccessor", "niRecursion"]
        lines = ["!(import! &self megalodon)",
                 "!(let $state (mg:new-theory-state egal) (bind! &carrier $state))",
                 "(= (T) (mg:use (get-state &carrier)))",
                 "(= (AUTH) (mg:authority (get-state &carrier)))",
                 f"!(mg:import (AUTH) {json.dumps(str(proofs))} (axioms))"]
        for name in selected:
            identity = json.dumps(roots[name])
            lines += [f"!(CarrierControl {name} (mg:is-theorem (mg:known (T) {identity})))",
                      f"!(CarrierControl portable_{name} (mg:is-theorem "
                      f"(mg:check-evidence (T) (mg:evidence (mg:known (T) {identity})))))",
                      f"!(mg:dependencies (T) {identity})"]
        lines += [f'!(case (mg:try-prove (T) "carrier_forgery" (Tm.all (Tp.prop) (Tm.db 0)) '
                  f'(Pf.known {json.dumps(roots["niRecursion"])})) '
                  '(((Error $call $why) (CarrierControl changed_claim true)) '
                  '($other (CarrierControl changed_claim false))))',
                  '!(case (mg:try-known (T) "carrier_forgery") '
                  '(((Error $call $why) (CarrierControl failed_publication true)) '
                  '($other (CarrierControl failed_publication false))))']
        program = out / "replay.metta"
        program.write_text("\n".join(lines) + "\n")
        observations = []
        for dialect in ("he", "petta"):
            native = run("native-" + dialect, [cetta, "--lang", dialect, "--profile", "extended", program])
            if native.stderr:
                raise RuntimeError("native replay emitted diagnostics")
            packets = []
            for line in native.stdout.splitlines():
                if line.startswith("[(") and line.endswith("]"):
                    line = line[1:-1]
                if line.startswith("(CarrierControl "):
                    packets.append(line.replace(" True)", " true)").replace(" False)", " false)"))
            controls = selected + ["portable_" + name for name in selected] + ["changed_claim", "failed_publication"]
            if len(packets) != len(controls) or any(packets.count(f"(CarrierControl {name} true)") != 1 for name in controls):
                raise RuntimeError("native replay has missing, repeated or failed controls")
            imports = [line for line in native.stdout.splitlines() if "(Megalodon.imported " in line]
            if len(imports) != 1:
                raise RuntimeError("native replay has no unique import result")
            counts = dict(re.findall(r"\(([a-z-]+) ([0-9]+)\)", imports[0]))
            expected = dict(primitives="0", parameters="0", definitions="14", axioms="0", theorems="32",
                            unproved="0", **{"depends-on-unproved": "0", "unsupported": "0"})
            if any(counts.get(key) != value for key, value in expected.items()):
                raise RuntimeError("native proof/assumption inventory differs")
            observations.append(packets)
        if observations[0] != observations[1] or any(digest(Path(path)) != value for path, value in pins.items()):
            raise RuntimeError("native observations differ or input changed")
        record.update(qualified=True, status="passed", theorem_count=32, definition_count=14,
                      native_controls_per_dialect=18, imported_axioms=0, roots=roots,
                      previous_stream_unchanged=True, proof_sha256=digest(proofs),
                      remaining=["Independent typed statement/model comparison",
                                 "Selected-theory evidence for classical, infinity and selection interfaces"])
        print(json.dumps({key: record[key] for key in
                          ("qualified", "m1_qualified", "theorem_count", "native_controls_per_dialect")}))
    finally:
        save()


if __name__ == "__main__":
    main()
