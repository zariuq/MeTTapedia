#!/usr/bin/env bash
# Lean's proofs followed into the Megalodon kernel of CeTTa.
#
#   kernel/follow.sh [ROOT ...]     (default: the roots of artifacts/lean-declarations/transport/lemma-roots.txt)
#
# The transport target's document (assembled as check-target.sh assembles it) is opened as a live
# kernel theory (session.metta), and each root theorem of the transport export is followed from
# Lean's own proof term (transport.metta).  A root is followed when the kernel's theorem states
# what the root's claim states: (FOLLOW-DONE C NAME), with the theorem published as NAME;
# otherwise (FOLLOW-LEFT C WHY).
#
# The roots listed in ../targets/transport.followed must be followed.  Then the controls: each
# followed root is followed again by a proof of another statement (trivial, a proof of True),
# which must be refused: (CONTROL-OK C).
#
#   CETTA   the CeTTa binary                 (default: cetta on PATH)
#   WORK    a directory to keep the work in  (default: a temporary one, removed afterwards)
#   SAVE    a path: the theory, with the followed theorems, saved there as a Megalodon library
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
project=$(cd "$here/../../../.." && pwd)
root=$(cd "$here/../../../../../.." && pwd)
cetta=${CETTA:-cetta}
data=$project/artifacts/lean-declarations/transport
preamble=$root/megalodon/examples/egal/PfgEAug2022Preamble.mgs
if [ -n "${WORK:-}" ]; then
  work=$WORK; mkdir -p "$work"
else
  work=$(mktemp -d "${TMPDIR:-/tmp}/lean-egal-follow.XXXXXX")
  trap 'rm -rf -- "$work"' EXIT
fi
fail() { echo "FAIL $*"; exit 1; }
listed() { [ -e "$here/targets/transport.$1" ] && grep -v -E '^[[:space:]]*(#|$)' "$here/targets/transport.$1" || true; }

if [ $# -gt 0 ]; then roots=("$@"); else mapfile -t roots < <(grep -v -E '^[[:space:]]*(#|$)' "$data/lemma-roots.txt"); fi

# The reader's inputs, as generate-target.sh prepares them.
CETTA=$cetta "$here/generate-target.sh" transport --inputs "$work/inputs" > "$work/inputs.log" 2>&1 \
  || { tail -5 "$work/inputs.log"; fail "the transport target's inputs"; }

# The document's files, in check-target.sh's order up to the functions.
mapfile -t prelude < <(listed prelude)
mapfile -t library < <(listed library)
if [ -e "$here/targets/transport.core" ]; then mapfile -t core < <(listed core)
else core=(Library/EqFacts.mg Numerals.mg Decidable.mg Library/NumeralDecisions.mg); fi
parts=(Library/Conversion.mg LeanInEgal.mg Library/Typing.mg Library/Digits.mg "${prelude[@]}"
       generated/transport/Families.mg "${core[@]}" "${library[@]}" generated/transport/Functions.mg)
quoted=$(printf '"%s" ' "${parts[@]}")

{ echo '!(import! &self megalodon)'
  echo '!(import! &self (library megalodon_equations))'
  cat "$work/inputs/families-in.metta" "$data/terms.metta" "$data/proofs.metta" "$work/inputs/answers.metta" \
      "$work/inputs/typing.metta" "$here/support.metta" "$here/generate.metta" "$here/interpret.metta"
  printf '(EgalProofLibraryRoot "%s")\n' "$here"
  cat "$here/kernel/session.metta" "$here/kernel/terms.metta"
  printf '!(case (egal:open-parts "%s" "%s" "%s" (%s)) (((LeanSession $verdict $summary) (println! (session $verdict))) ($other (println! (session $other)))))\n' \
    "$preamble" "$here" "$work" "$quoted"
  sed '/^!/,$d' "$here/kernel/check-statements.metta"
  cat "$here/kernel/typing.metta" "$here/kernel/invert.metta" "$here/kernel/rules.metta" \
      "$here/kernel/numerals.metta" "$here/kernel/compute.metta" "$here/kernel/transport.metta"
  echo '!(let $ok (eq:init (egal:equality)) (println! (equality-laws $ok)))'
  echo '!(let $loaded (rules:open (egal:equality)) (println! (rules $loaded)))'
  # Without transport mode the prover holds the hand proofs of the very theorems followed.
  echo '!(case (tr:enter) (((TrMode (hands $h) (companions $k)) (println! (transport-mode $h $k))) ($bad (println! (transport-mode-failed $bad)))))'
  cat <<'EOF'
(= (follow:root $c)
   (case (tr:prove (egal:equality) $c)
     (((Unfollowed $why $at) (println! (FOLLOW-LEFT $c $why)))
      ($thm
        (let* (($same (mg:try-convertible (egal:theory) (mg:empty-context) (mg:proposition $thm) (tr:claim $c)))
               ($name (format-args "followed_{}" ((egal $c)))))
          (if (== $same True)
              (let $published (mg:try-publish (egal:theory) $thm $name) (println! (FOLLOW-DONE $c $name)))
              (println! (FOLLOW-LEFT $c another-statement))))))))
(= (follow:save $path)
   (case (mg:save-library (egal:theory) $path)
     (((Error $call $why) (println! (save-failed $why)))
      ($saved (println! (saved $saved))))))
(= (follow:control $c)
   (case (tr:prove-with (egal:equality) $c (pcite trivial ()))
     (((Unfollowed $why $at) (println! (CONTROL-OK $c)))
      ($thm (println! (CONTROL-FOLLOWED $c))))))
EOF
  for r in "${roots[@]}"; do echo "!(follow:root $r)"; done
  [ -n "${SAVE:-}" ] && printf '!(follow:save "%s")\n' "$SAVE"
} > "$work/follow.metta"

"$cetta" --lang petta "$work/follow.metta" "$work" > "$work/follow.out" 2> "$work/follow.err" \
  || { tail -5 "$work/follow.err"; fail "the follower's run"; }
grep -q '^(session verified)' "$work/follow.out" || { grep '^(session' "$work/follow.out" | head -2; fail "the transport document is not verified"; }
grep -q '^(transport-mode [1-9]' "$work/follow.out" || grep -q '^(transport-mode [0-9]* [1-9]' "$work/follow.out" \
  || fail "transport mode set nothing aside: $(grep '^(transport-mode' "$work/follow.out")"
grep -E '^\(FOLLOW-(DONE|LEFT) ' "$work/follow.out" | sed 's/^/  /'

done_roots=$(sed -n 's/^(FOLLOW-DONE \([^ ]*\) .*/\1/p' "$work/follow.out")
for c in $(listed followed); do
  grep -qx -- "$c" <<< "$done_roots" || fail "$c is no longer followed"
done
echo "  followed $(wc -w <<< "$done_roots") of ${#roots[@]} roots from Lean's proof terms"
if [ -n "${SAVE:-}" ]; then
  grep -q '^(saved ' "$work/follow.out" || fail "the theory was not saved: $(grep '^(save-failed' "$work/follow.out")"
  echo "  saved $SAVE: $(grep -c '^(Megalodon.theorem .*(tree ' "$SAVE") theorems as proof trees, $(grep -c '^(Megalodon.theorem .*(dag ' "$SAVE") as rows"
fi

# The controls: each followed root by a proof of True.
{ sed -e '/^!(follow:root /d' -e '/^!(follow:save /d' "$work/follow.metta"
  for c in $done_roots; do echo "!(follow:control $c)"; done
} > "$work/controls.metta"
"$cetta" --lang petta "$work/controls.metta" "$work" > "$work/controls.out" 2> "$work/controls.err" \
  || { tail -5 "$work/controls.err"; fail "the controls' run"; }
if grep -q '^(CONTROL-FOLLOWED ' "$work/controls.out"; then fail "$(grep '^(CONTROL-FOLLOWED ' "$work/controls.out")"; fi
[ "$(grep -c '^(CONTROL-OK ' "$work/controls.out" || true)" = "$(wc -w <<< "$done_roots")" ] || fail "a control did not run"
echo "  controls: no followed root follows from a proof of another statement"
echo "PASS"
