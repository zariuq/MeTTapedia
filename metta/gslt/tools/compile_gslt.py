#!/usr/bin/env python3
"""Compile an authored .module and its imports into runnable shared-runtime MeTTa."""

import argparse
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--sort", required=True, help="declared state sort")
    parser.add_argument("--name", default="compiled")
    parser.add_argument("--mode", choices=("standard", "canonical"), default="canonical")
    parser.add_argument("--root-only", action="store_true")
    parser.add_argument("--free", action="append", default=[], metavar="NAME:SORT")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9:-]*", args.name):
        raise SystemExit("entry name must be an ordinary MeTTa function prefix")
    repo = Path(__file__).resolve().parents[3]
    lean = repo / "lean/mettapedia"
    source, output = args.source.resolve(), args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    driver = output.with_suffix(output.suffix + ".lean")
    if output.exists() or driver.exists():
        raise SystemExit("output or compiler driver already exists")
    free = []
    for item in args.free:
        name, separator, sort = item.rpartition(":")
        if not separator or not name or not sort:
            raise SystemExit("free bindings use NAME:SORT")
        free.append(f"({json.dumps(name)}, .base {json.dumps(sort)})")
    quote = lambda value: json.dumps(str(value), ensure_ascii=False)
    driver.write_text(f'''import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
#module_tree {quote(source)} as Input

def main : IO Unit := do
  let .ok authored := Input.language
    | throw (IO.userError "module elaboration refused; inspect the retained compiler driver")
  let .ok core := authored.toCore
    | throw (IO.userError "authored algebra or binding requires an additional certified core lowering")
  let language := core.language
  unless language.typeNames.contains {quote(args.sort)} do
    throw (IO.userError "the selected state sort is not declared")
  let snapshot : GeneralExecutionAdmission.Snapshot :=
    ⟨language,[{','.join(free)}],{{signatures := [],rows := []}}⟩
  let permissions : GeneralExecutionAdmission.Permissions :=
    {{sites := .{'rootOnly' if args.root_only else 'all'}, includeDerivedEquations := false}}
  let plan := GeneralExecutionAdmission.compile snapshot permissions
  let spec : CompleteEmission.Spec := ⟨plan,[],.base {quote(args.sort)},.{args.mode}⟩
  match CompleteEmission.emitText? spec {quote(args.name)} with
  | .error (.obligations pending) => throw (IO.userError s!"admission refused: {{reprStr pending}}")
  | .error .unbalancedEquations => throw (IO.userError "equations require a supported certified orientation")
  | .error .dynamicProvider => throw (IO.userError "a finite declared provider is required")
  | .error (CompleteEmission.Refusal.nameCollision collision) => throw (IO.userError s!"entry name collision: {{collision}}")
  | .error .unrenderable => throw (IO.userError "module has an unrenderable data payload")
  | .ok text =>
    let sources := RuleExecutionProgram.scopedSource :: CollectionOccurrenceSearchExecution.SelectedNativeSource.sources
    IO.FS.writeFile {quote(output)} (String.intercalate "\\n" (sources.map (·.text)) ++ "\\n" ++ text)
    IO.println s!"compiled {{language.name}}: {{language.rewrites.length}} rules, {{language.equations.length}} equations"
''')
    subprocess.run(["lake", "--wfail", "build",
                    "Mettapedia.GSLT.LanguageDef.ModuleSource.Loader",
                    "Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission"], cwd=lean, check=True)
    subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", "--run", str(driver)], cwd=lean, check=True)


if __name__ == "__main__":
    main()
