#!/usr/bin/env python3
"""Compare the closed Lean call-guard judgment with selected SWI-PeTTa."""

from __future__ import annotations

import argparse
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


SELECTED_COMMIT = "91c27146b129f4d54776362ddb58898568f4665f"
CASE = re.compile(r"^\(([a-z0-9-]+) ([0-9]+)\)$")
REFERENCE_ONLY = {
    "revision-before-add": 1,
    "revision-after-add": 0,
    "revision-number-after-add": 1,
    "revision-after-remove": 1,
}

LEAN_PROBE = r'''
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

namespace CallGuardReferenceProbe

open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection

private def queryBit (query : Query) : Nat :=
  if queryDecision query = true then 1 else 0

private def primitiveAnnotation : TypeAnnotation :=
  ⟨15, .number "3", groundedMetaType⟩
private def primitiveSnapshot : Snapshot :=
  ⟨1, [], [primitiveAnnotation], []⟩
private def primitiveNumberQuery : Query :=
  ⟨primitiveSnapshot, .getType, .number "3", numberType⟩
private def primitiveAnnotationQuery : Query :=
  ⟨primitiveSnapshot, .getType, .number "3", groundedMetaType⟩
private def primitiveUndefinedQuery : Query :=
  ⟨primitiveSnapshot, .getType, .number "3", undefinedType⟩
private def unknownFallbackQuery : Query :=
  ⟨primitiveSnapshot, .getType, .atom "cg_ref_unknown_symbol",
    undefinedType⟩

private def plusExpr : Term :=
  .list [.atom "+", .number "2", .number "3"]

private def count (snapshot : Snapshot) (call : Call) : Nat :=
  (successfulDeclarations ⟨snapshot, call⟩).length

private def exactDecl : ArrowDeclaration :=
  ⟨1, "cg_ref_exact", [numberType], numberType⟩
private def exactSnapshot : Snapshot :=
  ⟨1, [exactDecl], [], ["cg_ref_exact"]⟩
private def exactCall : Call :=
  ⟨"cg_ref_exact", [.number "3"], [.number "3"], .number "3"⟩
private def wrongInputCall : Call :=
  ⟨"cg_ref_exact", [.string "bad"], [.string "bad"], .string "bad"⟩
private def wrongResultCall : Call :=
  ⟨"cg_ref_exact", [.number "3"], [.number "3"], .string "bad"⟩

private def metaDecl : ArrowDeclaration :=
  ⟨2, "cg_ref_meta", [groundedMetaType], numberType⟩
private def metaSnapshot : Snapshot :=
  ⟨1, [metaDecl], [], ["cg_ref_meta"]⟩
private def metaCall : Call :=
  ⟨"cg_ref_meta", [.number "3"], [.number "3"], .number "3"⟩

private def rawDecl : ArrowDeclaration :=
  ⟨3, "cg_ref_raw", [atomType], expressionMetaType⟩
private def rawSnapshot : Snapshot :=
  ⟨1, [rawDecl], [], ["cg_ref_raw"]⟩
private def rawCall : Call :=
  ⟨"cg_ref_raw", [plusExpr], [plusExpr], plusExpr⟩

private def uncheckedDecl : ArrowDeclaration :=
  ⟨4, "cg_ref_unchecked", [undefinedType], numberType⟩
private def uncheckedSnapshot : Snapshot :=
  ⟨1, [uncheckedDecl], [], ["cg_ref_unchecked"]⟩
private def uncheckedCall : Call :=
  ⟨"cg_ref_unchecked", [plusExpr], [.number "5"], .number "5"⟩

private def holeDecl : ArrowDeclaration :=
  ⟨12, "cg_ref_hole", [holeType], numberType⟩
private def holeSnapshot : Snapshot :=
  ⟨1, [holeDecl], [], ["cg_ref_hole"]⟩
private def holeCall : Call :=
  ⟨"cg_ref_hole", [plusExpr], [.number "5"], .number "5"⟩

private def softcutDecl : ArrowDeclaration :=
  ⟨13, "cg_ref_softcut", [groundedMetaType], numberType⟩
private def dualAnnotation : TypeAnnotation :=
  ⟨14, .atom "cg_ref_dual_atom", groundedMetaType⟩
private def softcutSnapshot : Snapshot :=
  ⟨1, [softcutDecl], [dualAnnotation],
    ["cg_ref_softcut", "cg_ref_dual_atom"]⟩
private def softcutCall : Call :=
  ⟨"cg_ref_softcut", [.atom "cg_ref_dual_atom"],
    [.atom "cg_ref_dual_atom"], .number "3"⟩

private def numberOverload : ArrowDeclaration :=
  ⟨5, "cg_ref_two", [numberType], numberType⟩
private def metaOverload : ArrowDeclaration :=
  ⟨6, "cg_ref_two", [groundedMetaType], numberType⟩
private def overloadSnapshot : Snapshot :=
  ⟨1, [numberOverload, metaOverload], [], ["cg_ref_two"]⟩
private def overloadCall : Call :=
  ⟨"cg_ref_two", [.number "3"], [.number "3"], .number "3"⟩

private def duplicateSource : SourceSnapshot :=
  ⟨⟨1⟩, 1, [exactDecl, { exactDecl with occurrence := 7 }], [],
    ["cg_ref_exact"]⟩

private def atomOut : ArrowDeclaration :=
  ⟨8, "cg_ref_outputs", [], atomType⟩
private def undefinedOut : ArrowDeclaration :=
  ⟨9, "cg_ref_outputs", [], undefinedType⟩
private def holeOut : ArrowDeclaration :=
  ⟨10, "cg_ref_outputs", [], holeType⟩
private def outputsSnapshot : Snapshot :=
  ⟨1, [atomOut, undefinedOut, holeOut], [], ["cg_ref_outputs"]⟩
private def outputsCall : Call :=
  ⟨"cg_ref_outputs", [], [], .string "bad"⟩

private def ownedDecl : ArrowDeclaration :=
  ⟨11, "cg_ref_owned", [numberType], numberType⟩
private def ownedSnapshot : Snapshot :=
  ⟨1, [ownedDecl], [], ["cg_ref_owned"]⟩
private def ownedNumberCall : Call :=
  ⟨"cg_ref_owned", [.number "3"], [.number "3"], .number "3"⟩
private def ownedWrongCall : Call :=
  ⟨"cg_ref_owned", [.string "bad"], [.string "bad"], .string "bad"⟩

#eval IO.println s!"(primitive-number-type {queryBit primitiveNumberQuery})"
#eval IO.println s!"(primitive-annotation-cut {queryBit primitiveAnnotationQuery})"
#eval IO.println s!"(primitive-no-undefined {queryBit primitiveUndefinedQuery})"
#eval IO.println s!"(unknown-type-fallback {queryBit unknownFallbackQuery})"
#eval IO.println s!"(exact-number {count exactSnapshot exactCall})"
#eval IO.println s!"(wrong-input {count exactSnapshot wrongInputCall})"
#eval IO.println s!"(wrong-result {count exactSnapshot wrongResultCall})"
#eval IO.println s!"(metatype-fallback {count metaSnapshot metaCall})"
#eval IO.println s!"(raw-atom {count rawSnapshot rawCall})"
#eval IO.println s!"(unchecked-input {count uncheckedSnapshot uncheckedCall})"
#eval IO.println s!"(hole-input {count holeSnapshot holeCall})"
#eval IO.println s!"(exact-softcut-single {count softcutSnapshot softcutCall})"
#eval IO.println s!"(two-overloads {count overloadSnapshot overloadCall})"
#eval IO.println ("(duplicate-chain " ++
  toString (count duplicateSource.resolve.snapshot exactCall) ++ ")")
#eval IO.println s!"(unchecked-outputs {count outputsSnapshot outputsCall})"
#eval IO.println s!"(owned-number {count ownedSnapshot ownedNumberCall})"
#eval IO.println s!"(owned-wrong {count ownedSnapshot ownedWrongCall})"

end CallGuardReferenceProbe
'''


def run(
    command: list[str],
    *,
    cwd: Path,
    input_text: str | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=cwd,
        input=input_text,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )


def cases(stdout: str) -> dict[str, int]:
    parsed: dict[str, int] = {}
    for line in stdout.splitlines():
        match = CASE.fullmatch(line.strip())
        if match:
            name, count = match.groups()
            if name in parsed:
                raise ValueError(f"duplicate result for {name}")
            parsed[name] = int(count)
    return parsed


def python_library_environment() -> dict[str, str]:
    env = os.environ.copy()
    interpreter = shutil.which("python3.12")
    if interpreter is None:
        return env
    result = run(
        [interpreter, "-c", "import sysconfig; print(sysconfig.get_config_var('LIBDIR') or '')"],
        cwd=Path.cwd(),
    )
    library = result.stdout.strip()
    if library:
        prior = env.get("LD_LIBRARY_PATH")
        env["LD_LIBRARY_PATH"] = library if not prior else f"{library}:{prior}"
    return env


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--petta-root",
        type=Path,
        default=os.environ.get("PETTA_ROOT"),
        help="selected PeTTa checkout (or set PETTA_ROOT)",
    )
    args = parser.parse_args()
    if args.petta_root is None:
        parser.error("--petta-root or PETTA_ROOT is required")

    project_root = Path(__file__).resolve().parents[2]
    petta_root = args.petta_root.resolve()
    fixture = Path(__file__).with_name("petta_mainline_call_guard_reference.metta")
    if not (petta_root / "run.sh").is_file():
        raise FileNotFoundError(f"not a PeTTa checkout: {petta_root}")

    head = run(["git", "rev-parse", "HEAD"], cwd=petta_root)
    if head.returncode != 0:
        sys.stderr.write(head.stderr)
        return head.returncode
    if head.stdout.strip() != SELECTED_COMMIT:
        sys.stderr.write(
            "PeTTa reference mismatch: expected "
            f"{SELECTED_COMMIT}, found {head.stdout.strip()}\n"
        )
        return 2

    lean = run(
        ["lake", "env", "lean", "/dev/stdin"],
        cwd=project_root,
        input_text=LEAN_PROBE,
    )
    if lean.returncode != 0:
        sys.stderr.write(lean.stdout)
        sys.stderr.write(lean.stderr)
        return lean.returncode

    petta = run(
        ["bash", "./run.sh", str(fixture), "--silent"],
        cwd=petta_root,
        env=python_library_environment(),
    )
    if petta.returncode != 0:
        sys.stderr.write(petta.stdout)
        sys.stderr.write(petta.stderr)
        return petta.returncode

    lean_cases = cases(lean.stdout)
    petta_cases = cases(petta.stdout)
    reference_only = {
        name: petta_cases.pop(name, None) for name in REFERENCE_ONLY
    }
    if reference_only != REFERENCE_ONLY:
        sys.stderr.write(f"PeTTa revision cases: {reference_only}\n")
        sys.stderr.write(f"Expected revision cases: {REFERENCE_ONLY}\n")
        return 1
    if lean_cases != petta_cases:
        sys.stderr.write(f"Lean cases: {lean_cases}\n")
        sys.stderr.write(f"PeTTa cases: {petta_cases}\n")
        return 1

    for name, count in lean_cases.items():
        print(f"{name}: {count}")
    for name, count in reference_only.items():
        print(f"{name}: {count} (selected-reference qualification)")
    print(
        f"matched {len(lean_cases)} closed call-guard cases and qualified "
        f"{len(reference_only)} revision cases at {SELECTED_COMMIT}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
