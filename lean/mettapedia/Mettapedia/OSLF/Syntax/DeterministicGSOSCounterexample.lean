import Mettapedia.OSLF.Syntax.DeterministicGSOSFiniteActions

/-!
# An infinite-action natural law without any finite-premise presentation

The probe returns a stopped process exactly when every input action is
disabled. This is a genuine natural law for the countably infinite action
carrier. No collection of finite-premise rules presents it: any rule
firing on the all-disabled input misses some action, which can be enabled
without changing its premises.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.AllDisabled

open CategoryTheory Mettapedia.TypeTheory

inductive Operator where
  | stopped
  | probe
  deriving DecidableEq

/-- A nullary stop and a unary probe, with infinitely many available labels. -/
abbrev signature : Signature.{0} where
  Srt := Unit
  Operator := fun _ => Operator
  Position := fun operator => match operator with
    | .stopped => Empty
    | .probe => Unit
  argument := fun _ _ => ()
  finite operator := by cases operator <;> infer_instance

abbrev actions : signature.Srt → Type := fun _ => Nat

noncomputable def stopped (X : signature.Families) : signature.Term X () :=
  IndexedPolynomial.Free.node signature.polynomial Operator.stopped (fun position => nomatch position)

/-- This rule observes the entire availability pattern, rather than a finite subset. -/
noncomputable def rules : GuardedSchemas actions := by
  classical
  exact fun _ operator guard action => match operator with
    | .stopped => none
    | .probe => if action = 0 ∧ ∀ address, guard address = false then some (stopped _) else none

/-- The probe really is an actual natural transformation. -/
noncomputable def law : Law signature actions := toLaw actions rules

abbrev disabled : Guard actions (sort := ()) Operator.probe := fun _ => false

theorem disabled_returns :
    universalReadout actions rules (sort := ()) Operator.probe disabled 0 =
      some (stopped (universalVariables actions (sort := ()) Operator.probe)) := by
  simp [universalReadout, rules, disabled, stopped, Signature.rename, signature, IndexedPolynomial.Free.map_node]
  congr 1
  funext position
  exact position.elim

/-- No finite cylinder determines the successful all-disabled result. -/
theorem not_finitely_observed : ¬ FiniteSuccessfulObservation actions rules := by
  classical
  intro observed
  obtain ⟨tested, determines⟩ := observed () Operator.probe 0 disabled _ disabled_returns
  let fresh := tested.sup (fun address => address.2) + 1
  have missed : (⟨(), fresh⟩ : Address actions (sort := ()) Operator.probe) ∉ tested := by
    intro member
    have bounded : fresh ≤ tested.sup (fun address => address.2) := Finset.le_sup (f := fun address : Address actions (sort := ()) Operator.probe => address.2) member
    exact (Nat.not_succ_le_self _ ) bounded
  let enabled : Guard actions (sort := ()) Operator.probe := fun address => if address.2 = fresh then true else false
  have agrees : ∀ address ∈ tested, enabled address = disabled address := by
    intro address member
    have different : address.2 ≠ fresh := by
      intro equal
      have same : address = ⟨(), fresh⟩ := by
        exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq equal)
      exact missed (same ▸ member)
    simp [enabled, disabled, different]
  have notDisabled : ¬ ∀ address, enabled address = false := by
    intro every
    have impossible := every ⟨(), fresh⟩
    simp [enabled] at impossible
  have empty : universalReadout actions rules (sort := ()) Operator.probe enabled 0 = none := by
    simp [universalReadout, rules, notDisabled]
  have contradiction := determines enabled agrees
  rw [empty] at contradiction
  cases contradiction

/-- Even an infinite set of finite-premise rules cannot present this natural law. -/
theorem no_finitePremise_presentation :
    ¬ ∃ presentation : FinitePresentation actions, Denotes actions presentation rules := by
  rw [finitePremise_iff_finiteSuccessfulObservation]
  exact not_finitely_observed

/-- Extraction from the independently constructed law retains the counterexample. -/
theorem law_has_no_finitePremise_presentation :
    ¬ ∃ presentation : FinitePresentation actions,
      Denotes actions presentation (fromLaw actions law) := by
  rw [show fromLaw actions law = rules from fromLaw_toLaw actions rules]
  exact no_finitePremise_presentation

end Mettapedia.OSLF.DeterministicGSOS.AllDisabled
