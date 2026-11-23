#!/usr/bin/env python3
"""Replay axiom-free natural proofs and compare their Mathdata statements.

The upstream checker produces the proof objects. CeTTa's existing native
Megalodon checker checks them with an empty axiom allowlist. Lean supplies the
independently typed statement syntax. This driver is not a proof checker.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path, required=True)
    parser.add_argument("--megalodon", type=Path, required=True)
    parser.add_argument("--expected", type=Path, required=True,
                        help="JSON from emit_megalodon_natural_closure.lean")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profile", choices=["closure", "recursion"], default="closure")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = root / "theory/logic/NaturalClosure.mg"
    sources = [source]
    if args.profile == "recursion":
        sources.append(root / "theory/logic/NaturalRecursion.mg")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cetta, meg = args.cetta.resolve(), args.megalodon.resolve()
    library = cetta.parent / "lib/megalodon.metta"
    expected = json.loads(args.expected.read_text())
    inputs = sources + [cetta, library, meg, args.expected.resolve(), Path(__file__).resolve()]
    before = {str(path): sha256(path) for path in inputs}

    started = time.monotonic()
    combined = output / "source.mg"
    combined.write_text("\n".join(path.read_text() for path in sources))
    upstream = subprocess.run([str(meg), "-sexprinfo", str(combined)], cwd=root,
                              capture_output=True, text=True, timeout=120)
    (output / "upstream.stderr").write_text(upstream.stderr)
    upstream.check_returncode()
    sexpr = output / "proofs.sexpr"
    sexpr.write_text(upstream.stdout)
    if upstream.stderr.strip() or re.search(r"^\((AX|PARAM|PRIM)\b", upstream.stdout, re.M):
        raise RuntimeError("source proof closure has diagnostics or unrequested assumptions")
    roots = dict(re.findall(r'^\(THM "([^"]+)" "([0-9a-f]{64})"', upstream.stdout, re.M))
    selected = ["naturalClosureZero", "naturalClosureSuccessor", "naturalClosureInduction"]
    total_theorems, total_definitions = 6, 2
    if args.profile == "recursion":
        selected += ["nrGraphFunctional", "nrRecursorZero", "nrRecursorSuccessor",
                     "nrRecursorUnique", "nrRecursorChoiceIndependent", "nrRecursion"]
        total_theorems, total_definitions = 24, 7
    if len(roots) != total_theorems or any(name not in roots for name in selected):
        raise RuntimeError("missing or repeated source theorem identities")
    if not re.search(r'^\(DEF "naturalClosure" "' + re.escape(expected["definition_name"]) + r'"',
                     upstream.stdout, re.M):
        raise RuntimeError("definition identity differs from the typed reference")

    lines = [
        '!(import! &self megalodon)',
        '!(let $state (mg:new-theory-state egal) (bind! &natural $state))',
        '(= (T) (mg:use (get-state &natural)))',
        '(= (AUTH) (mg:authority (get-state &natural)))',
        f'!(mg:import (AUTH) {json.dumps(str(sexpr))} (axioms))',
        f'!(NativeNaturalDefinition (mg:declaration (T) {json.dumps(expected["definition_name"])}))',
    ]
    for name in selected:
        identity = json.dumps(roots[name])
        lines += [
            f'!(NativeNaturalControl {name} (mg:is-theorem (mg:known (T) {identity})))',
            f'!(mg:dependencies (T) {identity})',
        ]
        if name in expected:
            lines.append(f'!(NativeNaturalStatement {name} (mg:proposition (mg:known (T) {identity})))')
        if args.profile == "recursion":
            lines.append(f'!(NativeNaturalControl portable_{name} '
                         f'(mg:is-theorem (mg:check-evidence (T) (mg:evidence (mg:known (T) {identity})))))')
    if args.profile == "recursion":
        if roots["nrRecursion"] != expected["recursion_name"]:
            raise RuntimeError("recursion theorem identity differs")
        lines += [
            f'!(NativeNaturalControl independent_recursion_statement '
            f'(mg:is-theorem (mg:prove (T) "natural_recursion_reading" '
            f'{expected["recursion_reading"]} (Pf.known {json.dumps(roots["nrRecursion"])}))))',
            '!(NativeNaturalStatement recursion_reading '
            '(mg:proposition (mg:known (T) "natural_recursion_reading")))',
        ]
    identity = json.dumps(roots["nrRecursion" if args.profile == "recursion" else "naturalClosureInduction"])
    falsehood = '(Tm.all (Tp.prop) (Tm.db 0))'
    lines += [
        f'!(NativeNaturalControl portable (mg:is-theorem (mg:check-evidence (T) (mg:evidence (mg:known (T) {identity})))))',
        f'!(case (mg:try-prove (T) "forged_natural" {falsehood} (Pf.known {identity})) '
        '(((Error $call $why) (NativeNaturalControl altered_conclusion true)) '
        '($unexpected (NativeNaturalControl altered_conclusion false))))',
        '!(case (mg:try-known (T) "forged_natural") '
        '(((Error $call $why) (NativeNaturalControl failed_publication true)) '
        '($unexpected (NativeNaturalControl failed_publication false))))',
        f'!(case (mg:try-prove (T) "forged_hypothesis" {falsehood} (Pf.hyp 0)) '
        '(((Error $call $why) (NativeNaturalControl unbound_hypothesis true)) '
        '($unexpected (NativeNaturalControl unbound_hypothesis false))))',
    ]
    program = output / "replay.metta"
    program.write_text("\n".join(lines) + "\n")
    controls = selected + ["portable", "altered_conclusion", "failed_publication", "unbound_hypothesis"]
    if args.profile == "recursion":
        controls += [f"portable_{name}" for name in selected] + ["independent_recursion_statement"]
    runs, observations = [], []
    for dialect in ["he", "petta"]:
        start = time.monotonic()
        run = subprocess.run([str(cetta), "--lang", dialect, "--profile", "extended", str(program)],
                             cwd=cetta.parent, capture_output=True, text=True, timeout=120)
        (output / f"{dialect}.stdout").write_text(run.stdout)
        (output / f"{dialect}.stderr").write_text(run.stderr)
        run.check_returncode()
        if run.stderr.strip():
            raise RuntimeError(f"{dialect}: unexpected diagnostics")
        results = []
        for line in run.stdout.splitlines():
            if line.startswith("[(") and line.endswith("]"):
                line = line[1:-1]
            if line.startswith("(NativeNaturalControl "):
                line = line.replace(" True)", " true)").replace(" False)", " false)")
            results.append(line)
        for name in controls:
            if results.count(f"(NativeNaturalControl {name} true)") != 1:
                raise RuntimeError(f"{dialect}: missing, duplicated or false control {name}")
        imports = [line for line in results if line.startswith("(Megalodon.imported ")]
        if len(imports) != 1:
            raise RuntimeError(f"{dialect}: missing or repeated import report")
        counts = dict(re.findall(r"\(([a-z-]+) ([0-9]+)\)", imports[0]))
        desired = {"primitives": 0, "parameters": 0, "definitions": total_definitions, "axioms": 0,
                   "theorems": total_theorems, "unproved": 0, "depends-on-unproved": 0, "unsupported": 0}
        if any(counts.get(key) != str(value) for key, value in desired.items()):
            raise RuntimeError(f"{dialect}: unexpected proof closure {counts}")
        definition_prefix = (f'(NativeNaturalDefinition (Megalodon.definition '
                             f'{json.dumps(expected["definition_name"])} '
                             f'{expected["definition_type"]} {expected["definition_body"]}')
        definitions = [line for line in results if line.startswith("(NativeNaturalDefinition ")]
        if len(definitions) != 1 or not definitions[0].startswith(definition_prefix + " (source "):
            raise RuntimeError(f"{dialect}: definition body or type differs")
        for name in ["naturalClosureZero", "naturalClosureSuccessor", "naturalClosureInduction"]:
            if results.count(f'(NativeNaturalStatement {name} {expected[name]})') != 1:
                raise RuntimeError(f"{dialect}: theorem statement differs: {name}")
        if args.profile == "recursion":
            if results.count(f'(NativeNaturalStatement recursion_reading {expected["recursion_reading"]})') != 1:
                raise RuntimeError(f"{dialect}: independently typed recursion statement differs")
        observations.append([line for line in results if line.startswith("(NativeNatural")])
        runs.append(dict(dialect=dialect, seconds=round(time.monotonic() - start, 6),
                         controls=len(controls), exact_statements=3 + (args.profile == "recursion"),
                         definitions=total_definitions,
                         proved_theorems=total_theorems, imported_axioms=0))
    if observations[0] != observations[1]:
        raise RuntimeError("dialects disagree on the selected observations")
    after = {str(path): sha256(path) for path in inputs}
    if before != after:
        raise RuntimeError("qualification inputs changed during replay")
    report = dict(inputs=after, proof_sha256=sha256(sexpr), roots=roots, runs=runs,
                  selected_observations_equal=True, seconds=round(time.monotonic() - started, 6),
                  profile=args.profile, scope=(
                      "axiom-free closure and conditional unique recursion; successor and choice interfaces remain explicit"
                      if args.profile == "recursion" else
                      "axiom-free natural-predicate closure and induction; not full Peano recursion or infinity"))
    (output / "qualification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
