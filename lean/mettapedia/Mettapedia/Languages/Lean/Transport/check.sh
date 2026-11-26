#!/usr/bin/env bash
# Lean's proofs as MeTTa data, and back.
#
#   Transport/check.sh [controls|readback|subsumption|library|invariance|grammar|all]    (default: all)
#
# readback        The transport closure (artifacts/lean-declarations/transport/proofs.metta, from
#                 scripts/ExportLeanTransport.lean) written back as Lean by MeTTa (readback.metta)
#                 and judged by Lean's kernel (Readback.lean): every theorem rebuilt, proving its
#                 original statement, and closed (resting on no original theorem and no axiom
#                 beyond Lean's three); each corrupted twin refused and each untouched twin
#                 accepted; the compiled module replayed by leanchecker and audited again from
#                 the module alone.
# subsumption     The theorems whose statements are instances of earlier ones (subsumption.metta),
#                 each proved by citing the earlier one, judged the same way.
# library         The lemmas worth having under the posterior of a Bayesian grammar of the proofs
#                 (grammar.metta; the stored posterior grammar-library.metta beside proofs.metta):
#                 each proof fragment's expected uses over the theorems, times the nodes a citation
#                 saves, less the lemma's own size, must be positive.  Every proof is rewritten to
#                 cite them by an exact dynamic program (library.metta), and judged the same way.  A
#                 lemma Lean refuses is left out and the proofs are rewritten again, for at most
#                 three rounds.
# invariance      The library stage is a function of the corpus and the posterior: the proofs' atoms
#                 loaded in reverse order give the same lemmas and the same rewritten proofs.
# grammar         The stored posterior made again: the grammar's chain run from its seed on the
#                 training theorems (one in six, chosen by a hash of the name; or, when the target
#                 has a held-out.txt, every theorem it does not name), its samples averaged, the
#                 held-out theorems parsed and their reuse set against the reuse predicted; the
#                 candidates must equal the stored ones (WRITE=1 stores them instead).  Not in all:
#                 it is a long run.
# controls        The MeTTa controls (controls/): the matcher; the grammar's moves against the exact
#                 posterior of a corpus small enough to enumerate; the library's matching, lemmas
#                 and rewriting.
#
#   CETTA   the CeTTa binary                 (default: cetta on PATH)
#   DATA    the target: its proofs.metta and modules.txt, as scripts/ExportLeanTransport.lean
#           writes them          (default: artifacts/lean-declarations/transport)
#   WORK    a directory to keep the work in  (default: a temporary one, removed afterwards)
#   WRITE   1: grammar stores the posterior it makes
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project=$(cd "$here/../../../.." && pwd)
cetta=${CETTA:-cetta}
data=${DATA:-$project/artifacts/lean-declarations/transport}
# the grammar's chain: seed, rounds before sampling, rounds sampled, type moves a round
seed=3 burn=70 samples=10 typemoves=400
if [ -n "${WORK:-}" ]; then
  work=$WORK; mkdir -p "$work"
else
  work=$(mktemp -d "${TMPDIR:-/tmp}/lean-transport.XXXXXX")
  trap 'rm -rf -- "$work"' EXIT
fi
fail() { echo "FAIL $*"; exit 1; }
seconds() { local s=$SECONDS; "$@"; echo "  [$(( SECONDS - s ))s]"; }

order=$(grep '^(TransportOrder ' "$data/proofs.metta" | sed 's/^(TransportOrder //; s/)$//')
[ -n "$order" ] || fail "no (TransportOrder ..) in $data/proofs.metta"
# the training and held-out theorems: the ones $data/held-out.txt names are held out and the rest
# train; without it, one in six by a hash of the name trains and another one in six is held out
if [ -f "$data/held-out.txt" ]; then
  train="($(for c in $order; do grep -qxF -- "$c" "$data/held-out.txt" || printf '%s ' "$c"; done))"
  held="($(for c in $order; do grep -qxF -- "$c" "$data/held-out.txt" && printf '%s ' "$c"; done))"
else
  train="(tsg:part ($order) 6 1)" held="(tsg:part ($order) 6 0)"
fi
# the export's scope: the whole closure, or the source modules' theorems with the rest cited as Lean's
scope=$(sed -n 's/^(TransportScope \([a-z]*\))$/\1/p' "$data/proofs.metta"); scope=${scope:-closure}
lean_path() { (cd "$project" && lake env printenv LEAN_PATH); }

controls() {
  local lib
  for lib in subsumption grammar library; do
    case $lib in
      subsumption) cat "$here/terms.metta" "$here/subsumption.metta" ;;
      grammar) cat "$here/terms.metta" "$here/grammar.metta" ;;
      library) cat "$here/terms.metta" "$here/grammar.metta" "$here/library.metta" ;;
    esac > "$work/controls-$lib.metta"
    cat "$here/controls/$lib.metta" >> "$work/controls-$lib.metta"
    "$cetta" --lang petta "$work/controls-$lib.metta" > "$work/controls-$lib.out" 2>&1 || true
    local ok failed
    ok=$(grep -c '^(control [^ ]* ok)' "$work/controls-$lib.out" || true)
    failed=$(grep -c '^(control ' "$work/controls-$lib.out" || true)
    failed=$(( failed - ok ))
    [ "$ok" -gt 0 ] && [ "$failed" = 0 ] || { grep '^(control ' "$work/controls-$lib.out" | grep -v ' ok)$' | head -5 || true; fail "$lib controls: $ok passed, $failed failed"; }
    echo "  $lib controls: $ok passed"
  done
}

# write NAME LIBRARY COMMANDS: the MeTTa run that transforms the data (LIBRARY, COMMANDS) and
# writes every theorem and the controls back as Lean, $work/NAME.lean
write() {
  local name=$1 library=$2 commands=$3
  { cat "$data/proofs.metta" "$here/terms.metta"
    [ -n "$library" ] && cat "$here/$library"
    [ -f "$work/$name.refused" ] && cat "$work/$name.refused"
    cat "$here/readback.metta"
    echo "(TransportOrderList ($order))"
    printf '%s\n' "$commands"
    echo '!(back:all (term:order))'
    echo '!(back:controls (term:order))'
  } > "$work/$name.metta"
  "$cetta" --lang petta "$work/$name.metta" > "$work/$name.metta.out" 2> "$work/$name.metta.err" \
    || { tail -5 "$work/$name.metta.err" || true; fail "$name: the MeTTa run"; }
  { echo 'import Lean'
    grep -v -E '^(#|$)' "$data/modules.txt" | awk '{print "import " $2}'
    echo 'import Mettapedia.Languages.Lean.Transport.Readback'
    echo
    echo 'open Mettapedia.Languages.Lean.Transport.Readback'
    echo 'set_option autoImplicit false'
    echo 'set_option maxRecDepth 100000'
    echo 'set_option maxHeartbeats 400000'
    echo 'set_option linter.all false'
    echo
    grep -E '^"?back_(theorem|missing|lemma|accept|refuse) ' "$work/$name.metta.out" | sed -e 's/^"//; s/"$//' -e 's/\\"/"/g'
    echo 'back_kernel_control'
    echo 'back_audit'
  } > "$work/$name.lean"
}

# judge NAME: Lean's kernel on $work/NAME.lean; its verdicts in $work/NAME.out
judge() {
  local name=$1
  (cd "$project" && lake env lean -R "$work" -o "$work/$name.olean" "$work/$name.lean") > "$work/$name.out" 2>&1 \
    || { grep -E 'error' -A3 "$work/$name.out" | head -12 || true; fail "$name: Lean refused the file"; }
}

# verdict NAME: every theorem rebuilt and closed, every lemma closed, the controls as they must be;
# then leanchecker on the module and the audit from the module alone
verdict() {
  local name=$1 out=$work/$1.out
  local written rebuilt borrowed closed leaves rests lemmas refused twins controls
  written=$(grep -c -E '^back_(theorem|missing) ' "$work/$name.lean" || true)
  rebuilt=$(grep -c 'REBUILT ' "$out" || true)
  borrowed=$(grep -c 'BORROWED ' "$out" || true)
  closed=$(grep -c 'CLOSED ' "$out" || true)
  leaves=$(grep -c 'LEAVES ' "$out" || true)
  rests=$(grep -c 'RESTS ' "$out" || true)
  lemmas=$(grep -c -E '(^|: )LEMMA ' "$out" || true)
  refused=$(grep -c 'LEMMA-REFUSED ' "$out" || true)
  twins=$(grep -c 'TWIN-OK ' "$out" || true)
  controls=$(grep -c 'CONTROL-OK ' "$out" || true)
  echo "  $name: $written theorems: rebuilt $rebuilt, borrowed $borrowed; lemmas $lemmas (refused $refused); closed $closed, citing Lean's own $leaves, resting $rests; twins $twins, corruptions refused $controls"
  # complete accounting: every theorem of the order is written, so a partial run cannot pass
  [ "$written" = "$(wc -w <<< "$order")" ] || fail "$name: $written theorems written of the order's $(wc -w <<< "$order")"
  [ "$borrowed" = 0 ] && [ "$rebuilt" = "$written" ] || { grep -o 'BORROWED .*' "$out" | head -5 || true; fail "$name: a theorem was not rebuilt"; }
  [ "$rests" = 0 ] && [ "$(( closed + leaves ))" = $(( rebuilt + lemmas )) ] || { grep -o 'RESTS .*' "$out" | head -5 || true; fail "$name: a rebuilt name rests on an original"; }
  [ "$scope" = sources ] || [ "$leaves" = 0 ] || { grep -o 'LEAVES .*' "$out" | head -5 || true; fail "$name: a rebuilt name rests on an original the closure lacks"; }
  [ "$twins" -ge 3 ] && [ "$controls" -ge 4 ] || fail "$name: the controls did not run"
  local path prefix
  prefix=$(cd "$project" && lake env lean --print-prefix)
  path="$work:$(lean_path)"
  LEAN_PATH=$path "$prefix/bin/leanchecker" "$name" > "$work/$name.checker" 2>&1 || { tail -5 "$work/$name.checker"; fail "$name: leanchecker"; }
  printf 'import %s\nimport Mettapedia.Languages.Lean.Transport.Readback\nback_independent_audit\n' "$name" > "$work/$name-audit.lean"
  LEAN_PATH=$path "$prefix/bin/lean" "$work/$name-audit.lean" > "$work/$name-audit.out" 2>&1 || { tail -5 "$work/$name-audit.out"; fail "$name: the independent audit"; }
  local audit
  audit=$(grep -o 'INDEPENDENT.*' "$work/$name-audit.out")
  [[ $audit == *"theorems=$(( rebuilt + lemmas )) originals-cited=0 "* ]] || fail "$name: independent audit: $audit"
  [ "$scope" = sources ] || [[ $audit == *" leaves=0 "* ]] || fail "$name: independent audit: $audit"
  [[ $audit =~ axioms=\[((propext|Classical.choice|Quot.sound)(, )?)*\]$ ]] || fail "$name: an axiom beyond Lean's three: $audit"
  echo "  $name: leanchecker replayed the module; $audit"
}

readback() {
  write readback "" ""
  judge readback
  verdict readback
}

subsumption() {
  write subsumption subsumption.metta $'!(subsume:index-all (term:order) 0)\n!(subsume:run (term:order))'
  local found
  found=$(grep -c '^(InstanceOf ' "$work/subsumption.metta.out" || true)
  [ "$found" -gt 0 ] || fail "subsumption: no theorem is an instance of an earlier one"
  echo "  subsumption: $found theorems are instances of earlier ones"
  judge subsumption
  verdict subsumption
  grep '^(InstanceOf .*(already-one-citation false))' "$work/subsumption.metta.out" \
    | sed -E 's/^\(InstanceOf ([^ ]+) ([^ ]+) \(old-size ([0-9]+)\) \(new-size ([0-9]+)\).*/    \1 is an instance of \2 (proof \3 -> \4 nodes)/'
}

invariance() {
  local variant art=$data/grammar-library.metta dump
  [ -s "$art" ] || fail "invariance: no stored posterior in $art"
  dump='!(let $ls (sort-atom (collapse (match &self (LibLemma $n $t) ($n $t)))) (println! (lemmas $ls)))'
  dump="$dump"$'\n''!(let $rs (sort-atom (collapse (match &self (RewrittenProof $c $q) ($c $q)))) (println! (rewritten $rs)))'
  for variant in forward reversed; do
    { if [ $variant = forward ]; then cat "$data/proofs.metta"; else tac "$data/proofs.metta"; fi
      cat "$here/terms.metta" "$here/grammar.metta" "$here/library.metta" "$art"
      echo "!(lib:choose $(wc -w <<< "$order"))"; echo "!(lib:rewrite-all ($order))"; printf '%s\n' "$dump"
    } > "$work/order-$variant.metta"
    "$cetta" --lang petta "$work/order-$variant.metta" > "$work/order-$variant.out" 2> "$work/order-$variant.err" \
      || { tail -3 "$work/order-$variant.err" || true; fail "invariance: the $variant run"; }
  done
  local k a b
  for k in lemmas rewritten; do
    grep -q "^($k " "$work/order-forward.out" || fail "invariance: no $k"
    a=$(grep "^($k " "$work/order-forward.out" | md5sum | cut -c1-12)
    b=$(grep "^($k " "$work/order-reversed.out" | md5sum | cut -c1-12)
    [ "$a" = "$b" ] || fail "invariance: the $k depend on the order of the atoms"
  done
  echo "  invariance: the same lemmas and the same rewritten proofs from the atoms in either order"
}

# judge_lemmas NAME COMMANDS: the chosen lemmas, after COMMANDS (and the refusals so far), judged by
# Lean after the theorems rebuilt as read and before any proof cites them; the ones it refuses in
# $work/NAME.refused
judge_lemmas() {
  local name=$1 commands=$2
  { cat "$data/proofs.metta" "$here/terms.metta" "$here/grammar.metta" "$here/library.metta" "$here/readback.metta" "$art"
    [ -f "$work/library.refused" ] && cat "$work/library.refused"
    echo "(TransportOrderList ($order))"
    echo "!(lib:choose $horizon)"
    [ -n "$commands" ] && printf '%s\n' "$commands"
    echo '!(lib:emit-all)'; echo '!(back:all (term:order))'; echo '!(back:lemmas (lib:lemma-names))'
  } > "$work/$name.metta"
  "$cetta" --lang petta "$work/$name.metta" > "$work/$name.metta.out" 2> "$work/$name.metta.err" \
    || { tail -5 "$work/$name.metta.err" || true; fail "library: the lemmas' MeTTa run ($name)"; }
  { echo 'import Lean'
    grep -v -E '^(#|$)' "$data/modules.txt" | awk '{print "import " $2}'
    echo 'import Mettapedia.Languages.Lean.Transport.Readback'
    echo
    echo 'open Mettapedia.Languages.Lean.Transport.Readback'
    echo 'set_option autoImplicit false'
    echo 'set_option maxRecDepth 100000'
    echo 'set_option maxHeartbeats 400000'
    echo 'set_option linter.all false'
    echo
    grep -E '^"?back_(theorem|missing|lemma) ' "$work/$name.metta.out" | sed -e 's/^"//; s/"$//' -e 's/\\"/"/g'
  } > "$work/$name.lean"
  judge "$name"
  grep -o 'LEMMA-REFUSED [^ ]*' "$work/$name.out" | awk '{print "(MinedRefused " $2 ")"}' | sort -u > "$work/$name.refused" || true
}

# library: the lemmas the grammar's posterior makes worth having (grammar.metta, library.metta,
# the stored posterior artifacts/lean-declarations/transport/grammar-library.metta), every proof
# rewritten exactly to cite them, judged by Lean.  The chosen lemmas are judged first; each one Lean
# refuses is stated again from its occurrences in the training theorems and judged again; what is
# still refused is left out.  A lemma refused while the proofs cite it is left out and the proofs
# are rewritten again, for at most three rounds.
library() {
  local round new art=$data/grammar-library.metta horizon refine
  [ -s "$art" ] || fail "library: no stored posterior in $art (check.sh grammar makes it)"
  horizon=$(wc -w <<< "$order")
  refine="!(lib:refine-refused $train)"
  rm -f "$work/library.refused"
  judge_lemmas lemmas ""
  cp "$work/lemmas.refused" "$work/library.refused"
  judge_lemmas lemmas2 "$refine"
  cat "$work/lemmas2.refused" >> "$work/library.refused"
  echo "  library: $(grep -c -E '^"?back_lemma ' "$work/lemmas.metta.out" || true) lemmas chosen; Lean refused $(grep -c . "$work/lemmas.refused" || true) of them alone"
  echo "  library: $(grep -o '(lib-refined .*' "$work/lemmas2.metta.out" | head -1); Lean refused $(grep -c -E 'r$|r\)$' "$work/lemmas2.refused" || true) of those"
  for round in 1 2 3; do
    write library "" "$(cat "$here/grammar.metta" "$here/library.metta" "$art")"$'\n'"!(lib:choose $horizon)"$'\n'"$refine"$'\n'"!(lib:rewrite-all ($order))"$'\n'"!(lib:sizes-by-split $train $held)"
    judge library
    new=$(grep -o 'LEMMA-REFUSED [^ ]*' "$work/library.out" | awk '{print "(MinedRefused " $2 ")"}' | sort -u || true)
    [ -z "$new" ] && break
    echo "  round $round: Lean refused $(echo "$new" | wc -l) lemmas; rewriting without them"
    printf '%s\n' "$new" >> "$work/library.refused"
  done
  [ -z "$new" ] || fail "library: Lean still refuses lemmas after three rounds"
  grep -E '^\((lib-chosen|MinedSizes|MinedSizesByClass)' "$work/library.metta.out" | sed 's/^/  /'
  verdict library
  [ "$(grep -c -E '(^|: )LEMMA ' "$work/library.out" || true)" -gt 0 ] || fail "library: no lemma was cited"
  grep -o -E '(^|: )LEMMA .*' "$work/library.out" | sed 's/^: //' | cut -c1-160 | sed 's/^/    /' || true
}

# grammar: the chain on the training theorems from its seed; the held-out theorems parsed with it;
# the candidates it hands the library, against the stored ones
grammar() {
  local art=$data/grammar-library.metta
  { cat "$data/proofs.metta" "$here/terms.metta" "$here/grammar.metta"
    echo "!(let \$tr $train (let \$r (tsg:run \$tr $seed $burn $samples $typemoves) (println! (training (term:length \$tr)))))"
    echo '!(tsg:recount)'
    echo "!(let \$tr $train (tsg:print-library 1.0 (term:length \$tr)))"
    echo "!(tsg:extend $held)"
    echo '!(tsg:held-sweeps 4)'
    echo '!(tsg:held-report)'
    echo '!(tsg:recount)'
  } > "$work/grammar.metta"
  "$cetta" --lang petta "$work/grammar.metta" > "$work/grammar.out" 2> "$work/grammar.err" \
    || { tail -5 "$work/grammar.err" || true; fail "grammar: the MeTTa run"; }
  grep -E '^\((tsg-recount|training|library-candidates|held-out-proof-fragments|band) ' "$work/grammar.out" | sed 's/^/  /'
  grep -q '^(tsg-recount ' "$work/grammar.out" || fail "grammar: the state was not recounted"
  if grep -E '^\(tsg-recount ' "$work/grammar.out" | grep -q -E 'mismatched [1-9]'; then fail "grammar: the sampler's state disagrees with its derivation"; fi
  grep -E '^\((LibPosterior|LibCandidate) ' "$work/grammar.out" > "$work/grammar-library.metta"
  [ -s "$work/grammar-library.metta" ] || fail "grammar: no candidates"
  if [ "${WRITE:-0}" = 1 ]; then
    cp "$work/grammar-library.metta" "$art"; echo "  grammar: stored $(grep -c '^(LibCandidate ' "$art") candidates"
  else
    cmp -s "$work/grammar-library.metta" "$art" || fail "grammar: the candidates differ from the stored ones (WRITE=1 stores them)"
    echo "  grammar: the stored posterior made again, $(grep -c '^(LibCandidate ' "$art") candidates"
  fi
}

case "${1:-all}" in
  controls) seconds controls ;;
  readback) seconds readback ;;
  subsumption) seconds subsumption ;;
  library) seconds library ;;
  invariance) seconds invariance ;;
  grammar) seconds grammar ;;
  all) seconds controls; seconds readback; seconds subsumption; seconds library; seconds invariance ;;
  *) sed -n '2,31p' "$0"; exit 2 ;;
esac
echo "PASS"
