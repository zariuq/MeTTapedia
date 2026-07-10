import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength
import MettaHyperonFull.Operational.Semantics

/-!
# Verified MeTTa, entry 04 -- match/query over LeaTTa

This entry verifies the core MeTTa query operation directly against LeaTTa's
`Space.transform` semantics: a one-fact atomspace queried with a variable pattern
returns exactly the matched payload.
-/

namespace Mettapedia.Languages.MeTTa.LeaTTa.Corpus.MatchQuery

open Metta
open Mettapedia.Languages.MeTTa.LeaTTa.Corpus.ListAppendLength

def node (n : Nat) : Metta.Atom :=
  mE "N" [peano n]

def answerFact (n : Nat) : Metta.Atom :=
  mE "verified-answer" [node n]

def answerSpace (n : Nat) : Metta.Space :=
  ⟨[answerFact n]⟩

def answerPattern : Metta.Atom :=
  mE "verified-answer" [mVar "answer"]

def answerTemplate : Metta.Atom :=
  mVar "answer"

def matchQuery : Metta.Atom :=
  mE "match" [mSym "&self", answerPattern, answerTemplate]

private theorem node_not_var (n : Nat) (v : String) :
    node n ≠ Metta.Atom.var v := by
  simp [node, mE]

private theorem match_var_nonvar_atom (v : String) (target : Metta.Atom)
    (h : ∀ w, target ≠ Metta.Atom.var w) :
    Metta.matchAtomsWith none (Metta.Atom.var v) target =
      [[Metta.BindingRel.val v target]] := by
  cases target with
  | var w => exact (h w rfl).elim
  | sym _ => simp [Metta.matchAtomsWith]
  | gnd _ => simp [Metta.matchAtomsWith]
  | expr _ => simp [Metta.matchAtomsWith]

private theorem answer_match_eq (n : Nat) :
    Metta.matchAtoms answerPattern (answerFact n) =
      [[Metta.BindingRel.val "answer" (node n)]] := by
  simp only [answerPattern, answerFact, node, mE, mVar, Metta.matchAtoms,
    Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith, Metta.Bindings.merge]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "answer" (Metta.Atom.expr [Metta.Atom.sym "N", peano n])
    (by intro w h; cases h)]
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal, Metta.Bindings.lookupVal]
  unfold Metta.matchAll
  rfl

/-- Querying the one-fact MeTTa space returns exactly the payload matched by `$answer`. -/
theorem matchQueryComputesAnswer (n : Nat) :
    Metta.Space.transform (answerSpace n) answerPattern answerTemplate = [node n] := by
  unfold Metta.Space.transform Metta.Space.query
  simp [answerSpace, answer_match_eq, answerTemplate, Metta.instantiate,
    Metta.bindingsToSubst, Metta.Subst.apply, Metta.Subst.lookup, mVar]

/-- LeaTTa's operational `match` rule computes the same exact answer on the runnable surface. -/
theorem matchQueryReduceAtomComputesAnswer (cfg : Metta.RuntimeConfig) (n : Nat) :
    Metta.reduceAtom cfg (answerSpace n) matchQuery = some [node n] := by
  simp [Metta.reduceAtom, matchQuery, matchQueryComputesAnswer, mE, mSym]

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.MatchQuery
