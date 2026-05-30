#!/usr/bin/env bash
set -euo pipefail

src=${1:-cml/metta_m1.cml}
dst=${2:-cml/metta_m1_runner.cml}

awk '
  /^fun call name args =/ { exit }
  { print }
' "$src" > "$dst"

cat >> "$dst" <<'CML'

fun run_file fname =
  let
    val ins = TextIO.openIn fname;
    val text = TextIO.inputAll ins;
    val _ = TextIO.closeIn ins
  in
    case run_program_text 80 text of
      ProgramOutput out => TextIO.print out
    | ProgramRunError msg =>
        (TextIO.output TextIO.stdErr ("ParseError: " ^ msg ^ "\n");
         Runtime.exit 1)
  end handle TextIO.BadFileName =>
    (TextIO.output TextIO.stdErr ("Cannot open file: " ^ fname ^ "\n");
     Runtime.exit 1);

val _ =
  case CommandLine.arguments () of
    [fname] => run_file fname
  | _ =>
      (TextIO.output TextIO.stdErr "usage: metta_m1_runner FILE\n";
       Runtime.exit 1);
CML
