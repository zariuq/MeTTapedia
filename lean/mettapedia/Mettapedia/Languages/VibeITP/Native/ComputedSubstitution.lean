import Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
import Mettapedia.Languages.VibeITP.Presentation.CompleteSubstitution
import Mettapedia.Languages.VibeITP.Native.TermShapeCheck

/-!
# Direct shifting and substitution in Vibe certificates

Queries supply inputs; the evaluator computes their outputs. The resulting
operational judgments are qualified against the independent kernel and the
existing presented rules. Both finite replay and direct computation therefore
authorize the same results on structurally admitted inputs. This module does
not assert that a MeTTa or C implementation has already been generated.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ComputedSubstitution

open Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.Languages.VibeITP.Spec
open Mettapedia.Languages.VibeITP.Presentation

inductive Query where
  | shift (amount cutoff : Nat) (source : Term)
  | subst (arguments : List Term) (offset : Nat) (source : Term)
  | top (arguments : List Term) (source : Term)

def Domain (sig : Sig) : Query → Prop
  | .shift _ _ source => TermShape sig source
  | .subst arguments _ source => TermShapeList sig arguments ∧ TermShape sig source
  | .top arguments source => TermShapeList sig arguments ∧ TermShape sig source

def guard (sig : Sig) : Query → Bool
  | .shift _ _ source => TermShapeCheck.check sig source
  | .subst arguments _ source =>
      TermShapeCheck.checkList sig arguments && TermShapeCheck.check sig source
  | .top arguments source =>
      TermShapeCheck.checkList sig arguments && TermShapeCheck.check sig source

theorem guard_iff (sig : Sig) (query : Query) : guard sig query = true ↔ Domain sig query := by
  cases query <;> simp [guard, Domain, TermShapeCheck.check_iff, TermShapeCheck.checkList_iff]

def operation (sig : Sig) : Query → Option Term
  | .shift amount cutoff source => Spec.shift sig amount cutoff source
  | .subst arguments offset source => substGo sig arguments.length arguments offset source
  | .top arguments source => substBVars sig arguments.length arguments source 0

def run (sig : Sig) (query : Query) : Option Term :=
  if guard sig query then operation sig query else none

def judgment (sig : Sig) : Query → Term → Pattern
  | .shift amount cutoff source, result =>
      jShift (encNat amount) (encNat cutoff) (encTerm sig source) (encTerm sig result)
  | .subst arguments offset source, result =>
      jSubst (encNat arguments.length) (encTermList sig arguments) (encNat offset)
        (encTerm sig source) (encTerm sig result)
  | .top arguments source, result =>
      jSubstTop (encNat arguments.length) (encTermList sig arguments)
        (encTerm sig source) (encTerm sig result)

def evaluate (sig : Sig) (query : Query) : Option Pattern :=
  (run sig query).map (judgment sig query)

theorem run_eq_some_iff (sig : Sig) (query : Query) (result : Term) :
    run sig query = some result ↔ Domain sig query ∧ operation sig query = some result := by
  simp only [run]
  split
  next accepted => simp [(guard_iff sig query).mp accepted]
  next refused => simp [show ¬ Domain sig query from fun h => refused ((guard_iff sig query).mpr h)]

theorem run_of_domain (sig : Sig) (query : Query) (domain : Domain sig query) :
    run sig query = operation sig query := by
  simp [run, (guard_iff sig query).mpr domain]

theorem operation_iff_derivable {T : Theory} {allocation : Nat} (hosted : Hosted T allocation)
    (query : Query) (result : Term) (domain : Domain T.sig query) :
    operation T.sig query = some result ↔
      FODerivable (kernelRules ++ theoryRules T allocation) (judgment T.sig query result) := by
  cases query with
  | shift amount cutoff source =>
      exact shift_shape_iff_foDerivable hosted amount cutoff source result domain
  | subst arguments offset source =>
      exact substGo_shape_iff_foDerivable hosted arguments.length arguments offset source result
        rfl domain.1 domain.2
  | top arguments source =>
      exact substTop_shape_iff_foDerivable hosted arguments.length arguments source result
        rfl domain.1 domain.2

theorem run_iff_replay {T : Theory} {allocation : Nat} (hosted : Hosted T allocation)
    (query : Query) (result : Term) (domain : Domain T.sig query) :
    run T.sig query = some result ↔
      ∃ raw, checkRaw (kernelValidated T allocation) (judgment T.sig query result) raw = true := by
  rw [run_of_domain _ _ domain]
  exact (operation_iff_derivable hosted query result domain).trans
    (checkRaw_exists_iff_foDerivable (kernelValidated_presents T allocation) _).symm

def computation {T : Theory} {allocation : Nat} (hosted : Hosted T allocation) :
    QualifiedComputation (kernelValidated T allocation) Query where
  evaluate := evaluate T.sig
  sound := by
    intro query goal returned
    unfold evaluate at returned
    cases computed : run T.sig query with
    | none => simp [computed] at returned
    | some result =>
        have goalEq : judgment T.sig query result = goal := by simpa [computed] using returned
        rw [← goalEq]
        have domain := ((run_eq_some_iff T.sig query result).mp computed).1
        obtain ⟨raw, checked⟩ := (run_iff_replay hosted query result domain).mp computed
        exact checkRaw_soundness checked

theorem compact_iff_replay {T : Theory} {allocation : Nat} (hosted : Hosted T allocation)
    (goal : Pattern) :
    (∃ proof, check (kernelValidated T allocation) (evaluate T.sig) goal proof = true) ↔
      ∃ raw, checkRaw (kernelValidated T allocation) goal raw = true :=
  accepted_iff_replay (computation hosted) goal

/-- An operational refusal excludes all replay results for that same query.
The structural-domain premise is necessary: malformed inputs are refused by
the boundary guard, not used to make a claim about unrelated rule instances. -/
theorem refusal_rejects_every_result {T : Theory} {allocation : Nat}
    (hosted : Hosted T allocation) (query : Query) (domain : Domain T.sig query)
    (refused : run T.sig query = none) (result : Term) (raw : RawProof) :
    checkRaw (kernelValidated T allocation) (judgment T.sig query result) raw = false := by
  cases checked : checkRaw (kernelValidated T allocation) (judgment T.sig query result) raw with
  | false => rfl
  | true =>
      have impossible := (run_iff_replay hosted query result domain).mpr ⟨raw, checked⟩
      simp [refused] at impossible

end Mettapedia.Languages.VibeITP.Native.ComputedSubstitution
