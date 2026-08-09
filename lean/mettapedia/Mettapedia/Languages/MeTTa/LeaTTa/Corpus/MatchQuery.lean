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
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
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

private theorem peano_vars_nil (n : Nat) : (peano n).vars = [] := by
  induction n with
  | zero => simp [peano, mSym, Metta.Atom.vars]
  | succ n ih => simp [peano, mE, Metta.Atom.vars, ih]

private theorem node_vars_nil (n : Nat) : (node n).vars = [] := by
  simp [node, mE, Metta.Atom.vars, peano_vars_nil]

private theorem match_var_nonvar_atom (v : String) (target : Metta.Atom)
    (hvars : target.vars = []) :
    Metta.matchAtomsWith none (Metta.Atom.var v) target =
      [[Metta.BindingRel.val v target]] := by
  cases target with
  | var w => simp [Metta.Atom.vars] at hvars
  | sym _ => simp [Metta.matchAtomsWith, Metta.Subst.occurs]
  | gnd _ => simp [Metta.matchAtomsWith, Metta.Subst.occurs]
  | expr ys =>
      have hoccurs : Metta.Subst.occurs v (Metta.Atom.expr ys) = false :=
        occurs_eq_false_of_not_mem_vars v (Metta.Atom.expr ys) (by rw [hvars]; simp)
      simp [Metta.matchAtomsWith, hoccurs]

private theorem answer_match_eq (n : Nat) :
    Metta.matchAtoms answerPattern (answerFact n) =
      [[Metta.BindingRel.val "answer" (node n)]] := by
  simp only [answerPattern, answerFact, mE, mVar, Metta.matchAtoms,
    Metta.matchAtomsWith]
  unfold Metta.matchAll
  simp [Metta.matchAtomsWith, Metta.Bindings.merge]
  unfold Metta.matchAll
  rw [match_var_nonvar_atom "answer" (node n) (node_vars_nil n)]
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

/-- LeaTTa's operational `match` rule computes the same exact answer on the runnable interface. -/
theorem matchQueryReduceAtomComputesAnswer (cfg : Metta.RuntimeConfig) (n : Nat) :
    Metta.reduceAtom cfg (answerSpace n) matchQuery = some [node n] := by
  simp [Metta.reduceAtom, matchQuery, matchQueryComputesAnswer, mE, mSym]

end Mettapedia.Languages.MeTTa.LeaTTa.Corpus.MatchQuery
