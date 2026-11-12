#!/usr/bin/env bash
# Generate the Egal reading of a carried Lean development.
#
#   generate-target.sh TARGET           writes generated/TARGET/{Families,Functions,Computations,Theorems}.mg,
#                                       generated/TARGET/{Evidence,Qualification}.tsv, generated/TARGET/Skipped.txt
#                                       and controls/TARGET/reject_*.mg
#   generate-target.sh TARGET --check   regenerates them beside the committed ones and compares
#
# Inputs, for TARGET (for example functional-correspondence):
#   artifacts/lean-declarations/TARGET/families.metta   (scripts/ExportLeanDeclarations.lean)
#   artifacts/lean-declarations/TARGET/terms.metta      (scripts/ExportLeanTerms.lean, LEAN_TERMS_TARGET=TARGET)
#   artifacts/lean-code-equations/TARGET/tests.tsv      the tests with CeTTa's recorded answers
#   targets/TARGET.families                             the families in document order: a family, a
#                                                       nested block (bk F), or the main member of a
#                                                       block (view F), one per line
#
#   CETTA   the CeTTa binary (default: cetta on PATH)
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project=$(cd "$here/../../../.." && pwd)
cetta=${CETTA:-cetta}
target=${1:?usage: generate-target.sh TARGET [--check]}
decls=$project/artifacts/lean-declarations/$target
tests_tsv=$project/artifacts/lean-code-equations/$target/tests.tsv
work=$(mktemp -d "${TMPDIR:-/tmp}/lean-egal-target.XXXXXX")
cleanup() {
    rm -f -- "$work"/*.metta "$work"/*.mg "$work"/*.txt "$work"/*.tsv "$work"/execution.json
  rmdir -- "$work"
}
trap cleanup EXIT

# The target's family declarations, with the families it borrows from another
# export (targets/TARGET.borrow: lines "SOURCE FAMILY..."), such as Nat for the
# indices of a block exported on its own.  A borrowed family brings the names
# of its constructors, not another family of the source whose name begins
# with its own (List does not bring List.Perm).
python3 - "$decls/families.metta" "$here/targets/$target.borrow" "$project/artifacts/lean-declarations" \
    "$work/families-in.metta" <<'EOF'
import os, re, sys
own, borrow, root, out = sys.argv[1:5]
text = open(own).read()
if os.path.exists(borrow):
    for line in open(borrow):
        parts = line.split("#")[0].split()
        if not parts:
            continue
        source, names = parts[0], set(parts[1:])
        facts = open(os.path.join(root, source, "families.metta")).readlines()
        families = {m.group(1) for m in (re.match(r"\((?:LeanFamily \(Family|LeanAdmitted) (\S+)", fact) for fact in facts) if m}
        for fact in facts:
            m = re.match(r"\((?:LeanFamily \(Family|LeanAdmitted|EgalName) (\S+)", fact)
            if m and (m.group(1) in names or
                      (m.group(1) not in families and m.group(1).rsplit(".", 1)[0] in names)):
                text += fact
open(out, "w").write(text)
EOF

# The functions' definitions are opaque in the computations, which use the
# proved equations only; checking needs no unfolding of large definitions.
# A function that computes a type (it has a theorem NAME_type_In) stays
# transparent: a value is typed at what the definition says.
opaque_names() {
  sed -n 's/^Definition \([A-Za-z0-9_]*\) .*/\1/p' "$1" |
    grep -vxF -f <(sed -n 's/^Theorem \([A-Za-z0-9_]*\)_type_In .*/\1/p' "$1") | tr '\n' ' ' | sed 's/ $//' || true
}
opaque_open() {
  local names; names=$(opaque_names "$1")
  [[ -n $names ]] && printf '%s\nOpaque %s.\n\n' "(** The runs use each function's proved equations, not its definition. **)" "$names"
  return 0
}
opaque_close() {
  local names; names=$(opaque_names "$1")
  [[ -n $names ]] && printf '\nTransparent %s.\n' "$names"
  return 0
}

run_metta() {
  "$cetta" --lang petta "$1" | python3 -c '
import sys, json
skipped = open(sys.argv[1], "a")
buffer = None
for line in sys.stdin:
    line = line.rstrip("\n")
    if buffer is None:
        if not line.startswith("\""):
            continue
        buffer = line
    else:
        buffer = buffer + "\n" + line
    try:
        text = json.loads(buffer, strict=False)
        buffer = None
    except json.JSONDecodeError:
        continue
    if text.startswith("SKIP "):
        skipped.write(text[5:] + "\n")
    else:
        print(text)
' "$work/Skipped.txt"
}
: > "$work/Skipped.txt"

# Families, blocks and the main members of blocks, in document order.
{ cat "$work/families-in.metta" "$here/generate.metta"
  grep -v '^\s*\(#\|$\)' "$here/targets/$target.families" | while read -r entry; do
    case "$entry" in
      "(mutual "*) name=${entry#(mutual }; name=${name%)}
                 echo "!(println! (mutual-view-section $name))" ;;
      "(view "*) name=${entry#(view }; name=${name%)}
                 echo "!(println! (view-section $name))"
                 echo "!(println! (view-cases $name))" ;;
      *) echo "!(let \$ls (egal-section $entry) (map-atom \$ls \$l (println! \$l)))" ;;
    esac
  done
} > "$work/families.metta"
{ echo "(** Generated by generate-target.sh from the Lean declarations of $target.  Do not edit. **)"
  echo
  run_metta "$work/families.metta"
} > "$work/Families.mg"

# Observe this build executing the exported program; expected values are
# comparison inputs, not substitute observations.
if [[ -e "$tests_tsv" ]]; then
  if ! python3 "$project/scripts/lean_code_equations_diff.py" --cetta "$cetta" \
      --slice "$target" --report "$work/execution.json" > "$work/execution.txt"; then
    cat "$work/execution.txt"; exit 1
  fi
  "$cetta" --lang petta --quiet "$here/answers.metta" "$work/execution.json" \
    "$work/answers.metta" "$work/binary.txt" without-source "$tests_tsv" > /dev/null
else
  : > "$work/answers.metta"
fi
# The expected tests: every row of tests.tsv, answered by CeTTa or not.
ids=$(sed -n 's/^(LeanTest \([0-9]*\))$/\1/p' "$work/answers.metta")
tests=$(wc -w <<< "$ids")

# The typing lemmas proved in Egal by hand (proofs/functions/).
"$cetta" --lang petta "$here/splice.metta" facts "$here/proofs/functions" "$work/typing.metta" > /dev/null

reader() {
  cat "$work/families-in.metta" "$decls/terms.metta" "$work/answers.metta" "$work/typing.metta" \
      "$here/support.metta" "$here/generate.metta" "$here/interpret.metta"
  printf '(EgalProofLibraryRoot "%s")\n' "$here"
}

{ reader
  echo '!(let $ls (functions-section) (map-atom $ls $l (println! $l)))'
  echo '!(let $fs (all-functions) (let $ls (refusal-lines $fs) (map-atom $ls $l (println! (format-args "SKIP function {}" ($l))))))'
} > "$work/functions.metta"
{ echo "(** Generated by generate-target.sh: the functions of $target, read from their"
  echo "    equation theorems through their families' recursors, with Lean's equation"
  echo "    theorems proved from them.  Do not edit. **)"
  echo
  run_metta "$work/functions.metta"
} > "$work/Functions.mg"

{ reader
  [[ $tests == 0 ]] || echo '!(prepare-readability)'
  for i in $ids; do
    echo "!(case (computation-section $i) (((computation \$n \$t) (println! \$t)) ((stuck \$w) (println! (format-args \"SKIP test {}: {}\" ($i \$w))))))"
  done
} > "$work/computations.metta"
{ echo "(** Generated by generate-target.sh: computations of $target's tests, each the"
  echo "    reading of the Lean term equal to the reading of CeTTa's recorded answer,"
  echo "    replayed by Lean's equation theorems.  Do not edit. **)"
  echo
  opaque_open "$work/Functions.mg"
  run_metta "$work/computations.metta"
  opaque_close "$work/Functions.mg"
} > "$work/Computations.mg"
# Exactly one outcome per expected test; a defect stops the generation.
"$cetta" --lang petta "$here/accounted.metta" "$work/Outcomes.tsv" "$work/answers.metta" \
  "$work/Computations.mg" "$work/Skipped.txt" > /dev/null

# The control: the first joined test with its answer replaced by a wrong one.
first=$(grep -o '^Theorem Lean_test_[0-9]* :' "$work/Computations.mg" | head -1 | grep -o '[0-9][0-9]*' || true)
{ reader
  if [[ -n "$first" ]]; then
    echo "!(case (computation $((10#$first)) (wrong-answer $((10#$first))) Lean_test_wrong_answer) (((computation \$n \$t) (println! \$t)) ((stuck \$w) (println! (format-args \"SKIP control: {}\" (\$w))))))"
  fi
} > "$work/control.metta"
{ echo "(** Generated by generate-target.sh: a joined test of $target with CeTTa's answer"
  echo "    replaced by a wrong one.  Both checkers must refuse it. **)"
  run_metta "$work/control.metta"
} > "$work/reject_wrong_answer.mg"
# Theorems: each statement read from Lean, in Egal's own logic, with its proof
# from proofs/TARGET/NAME.mgproof (a proof written in Egal of the read statement).
{ reader
  echo '!(let $ls (theorem-statements) (map-atom $ls $l (case $l (((stmt-line $t $s) (println! (format-args "{}\t{}\t{}" ((egal $t) (nm $t) $s))))))))'
} > "$work/theorems.metta"
"$cetta" --lang petta "$work/theorems.metta" | python3 -c '
import sys, json
for line in sys.stdin:
    line = line.rstrip("\n")
    if line.startswith("\""):
        print(json.loads(line, strict=False))
' | LC_ALL=C sort > "$work/statements.txt"
python3 - "$work/statements.txt" "$here/proofs/$target" "$work/Theorems.mg" "$work/Skipped.txt" <<'PYEOF'
import os, sys
statements, proofs, out, skipped = sys.argv[1:5]
with open(out, "w") as f, open(skipped, "a") as s:
    f.write("(** Generated by generate-target.sh: the theorems of the development, each statement read\n"
            "    from Lean's, with the proof written in Egal for it (proofs/).  Do not edit. **)\n\n")
    for line in open(statements):
        egal, lean, stmt = line.rstrip("\n").split("\t", 2)
        path = os.path.join(proofs, egal + ".mgproof")
        if stmt.startswith("REFUSED "):
            s.write(f"theorem {lean}: {stmt[8:]}\n")
        elif os.path.exists(path):
            f.write(f"(** {lean}: its statement read from Lean; proved in Egal. **)\n")
            f.write(f"Theorem {egal} : {stmt}.\n{open(path).read().rstrip()}\nQed.\n\n")
        else:
            s.write(f"theorem {lean}: statement read, not proved here yet\n")
PYEOF

# A control with a wrong statement: CEK.eval_to_machine with its run of the
# machine (the reflexive-transitive closure of the step relation) replaced by
# a single step, which is false for an application; its proof must be refused.
python3 - "$work/Theorems.mg" "$work/reject_wrong_statement.mg" <<'PYEOF'
import re, sys
src, out = sys.argv[1:3]
text = open(src).read()
m = re.search(r"^Theorem (Lean_CEK_eval_to_machine) : (.*?)\.\n(.*?)^Qed\.$", text, re.S | re.M)
with open(out, "w") as f:
    f.write("(** Generated by generate-target.sh: CEK.eval_to_machine with the machine's run replaced by\n"
            "    one step.  Both checkers must refuse it. **)\n")
    if m:
        stmt, proof = m.group(2), m.group(3)
        head = "(Lean_Relation_ReflTransGen_Prop Lean_CEK_St "
        i = stmt.index(head)
        def arg(j):
            while stmt[j] == " ": j += 1
            if stmt[j] != "(":
                k = j
                while stmt[k] not in " )": k += 1
                return stmt[j:k], k
            depth, k = 0, j
            while True:
                if stmt[k] == "(": depth += 1
                elif stmt[k] == ")":
                    depth -= 1
                    if depth == 0: return stmt[j:k + 1], k + 1
                k += 1
        r, j = arg(i + len(head))
        a, j = arg(j)
        b, j = arg(j)
        assert stmt[j] == ")"
        wrong = stmt[:i] + f"({r} {a} {b})" + stmt[j + 1:]
        f.write(f"Theorem Lean_CEK_eval_to_machine_one_step : {wrong}.\n{proof}Qed.\n")
PYEOF

# The hand-written proofs of typing lemmas, in place of their markers.
"$cetta" --lang petta "$here/splice.metta" splice "$here/proofs/functions" "$work/Functions.mg" > /dev/null

# No line of generated text is longer than 200 characters.
"$cetta" --lang petta "$here/wrap.metta" "$work"/*.mg > /dev/null
sort -u -o "$work/Skipped.txt" "$work/Skipped.txt"

# The evidence of every manifest constant, and which tests it qualifies.
"$cetta" --lang petta "$decls/terms.metta" "$work/families-in.metta" "$here/evidence.metta" \
  "$work/Evidence.tsv" "$work/Qualification.tsv" "$work/evidence.txt" "$decls" "$work" > /dev/null

outputs=("generated/$target/Families.mg" "generated/$target/Functions.mg" "generated/$target/Computations.mg"
         "generated/$target/Theorems.mg" "generated/$target/Evidence.tsv" "generated/$target/Qualification.tsv"
         "generated/$target/Skipped.txt" "generated/$target/Outcomes.tsv" "controls/$target/reject_wrong_answer.mg"
         "controls/$target/reject_wrong_statement.mg")
if [[ "${2:-}" == "--check" ]]; then
  status=0
  for out in "${outputs[@]}"; do
    if [[ "$out" == controls/* ]] && ! grep -q '^Theorem' "$work/$(basename "$out")"; then
      [[ -e "$here/$out" ]] && { echo "check: $out should not exist"; status=1; }; continue
    fi
    cmp -s "$work/$(basename "$out")" "$here/$out" || { echo "check: $out differs"; status=1; }
  done
  [[ $status == 0 ]] && echo "check: the generated files equal a fresh generation"
  exit $status
fi
mkdir -p "$here/generated/$target" "$here/controls/$target"
for out in "${outputs[@]}"; do
  # A generated control with no claim (no test, no statement to alter) is not written.
  if [[ "$out" == controls/* ]] && ! grep -q '^Theorem' "$work/$(basename "$out")"; then
    rm -f -- "$here/$out"; continue
  fi
  cp "$work/$(basename "$out")" "$here/$out"
done
echo "generated $(grep -c '^End .*_Section\.$' "$here/generated/$target/Families.mg") family sections," \
     "$(grep '^Definition' "$here/generated/$target/Functions.mg" | grep -vc '_method[0-9]*_[0-9]* ') functions," \
     "$(grep -c '^Theorem Lean_test_[0-9]* :' "$here/generated/$target/Computations.mg") of $tests computations"
echo "not read:"; sed 's/^/  /' "$here/generated/$target/Skipped.txt"
cat "$work/evidence.txt"
