import Mettapedia.Coalgebra.CoherentPrefixTower
import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Stream finality through guarded finite approximations

The final behavior of a stream coalgebra can be characterized without
identifying temporal guarding with logical necessity.  Agreement at depth
`n` is a finite observation.  The head and tail equations turn agreement at
all strictly earlier depths into agreement at depth `n`; Löb induction then
gives agreement at every depth, and the coherent observation tower yields
stream equality.

This is a second proof route to uniqueness of the final morphism.  Its
negative controls show that `Later P n` does not imply `P n` by itself and
that agreement at all earlier prefix depths need not include the current
depth.  Guardedness supplies an induction discipline, not an ambient
reflexive necessity modality or an evaluation strategy.
-/

set_option autoImplicit false

namespace Mettapedia.Coalgebra.GuardedFinality

open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Coalgebra.CoherentPrefixTower
open Mettapedia.TypeTheory.GuardedTimeModeTheory

universe uLabel uState

/-! ## Guarded prefix agreement -/

/-- A proposed final morphism agrees with canonical unfolding through one
finite observation depth. -/
def PrefixAgreement {Label : Type uLabel}
    {coalgebra : Coalgebra.{uLabel, uState} Label}
    (morphism : Hom coalgebra (streamCoalgebra Label))
    (depth : Nat) : Prop :=
  ∀ state,
    finiteView depth (morphism.toFun state) =
      finiteView depth (unfold coalgebra state)

/-- The coalgebra-morphism head and tail equations advance finite agreement
by one guarded stage. -/
theorem prefixAgreement_step {Label : Type uLabel}
    {coalgebra : Coalgebra.{uLabel, uState} Label}
    (morphism : Hom coalgebra (streamCoalgebra Label))
    (depth : Nat)
    (earlier : Later (PrefixAgreement morphism) depth) :
    PrefixAgreement morphism depth := by
  intro state
  cases depth with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ depth =>
      funext index
      refine Fin.cases ?_ (fun priorIndex => ?_) index
      · exact morphism.observe_preserved state
      · have nextEquality :=
          congrFun (morphism.next_preserved state) priorIndex.val
        have priorAgreement :=
          earlier depth (Nat.lt_succ_self depth) (coalgebra.next state)
        have priorPoint := congrFun priorAgreement priorIndex
        exact nextEquality.trans priorPoint

/-- Löb induction supplies agreement at every finite observation depth. -/
theorem all_prefixes_agree {Label : Type uLabel}
    {coalgebra : Coalgebra.{uLabel, uState} Label}
    (morphism : Hom coalgebra (streamCoalgebra Label)) :
    ∀ depth, PrefixAgreement morphism depth :=
  lob (PrefixAgreement morphism) (prefixAgreement_step morphism)

/-- The complete coherent finite-view tower turns guarded agreement at every
depth into equality with canonical unfolding. -/
theorem hom_to_stream_eq_unfold_guarded {Label : Type uLabel}
    (coalgebra : Coalgebra.{uLabel, uState} Label)
    (morphism : Hom coalgebra (streamCoalgebra Label)) :
    morphism.toFun = unfold coalgebra := by
  funext state
  apply Tower.ofStream_injective
  apply Tower.ext
  funext depth
  exact all_prefixes_agree morphism depth state

/-- The guarded proof and the direct finality proof establish the same
semantic uniqueness statement. -/
theorem guarded_and_direct_finality_agree {Label : Type uLabel}
    (coalgebra : Coalgebra.{uLabel, uState} Label)
    (morphism : Hom coalgebra (streamCoalgebra Label)) :
    hom_to_stream_eq_unfold_guarded coalgebra morphism =
      hom_to_stream_eq_unfold coalgebra morphism := by
  apply Subsingleton.elim

/-! ## What guarding does not imply -/

/-- A predicate false exactly at revision zero. -/
def nonzeroRevision (revision : Nat) : Prop := revision ≠ 0

theorem later_nonzeroRevision_zero : Later nonzeroRevision 0 := by
  intro past earlier
  exact (Nat.not_lt_zero past earlier).elim

theorem not_nonzeroRevision_zero : ¬ nonzeroRevision 0 := by
  intro different
  exact different rfl

/-- `Later` is not reflexive necessity: without a supplied Löb step it does
not entail truth at the current revision. -/
theorem later_does_not_imply_now :
    ¬ ∀ (predicate : Nat → Prop) (revision : Nat),
      Later predicate revision → predicate revision := by
  intro reflexiveLater
  exact not_nonzeroRevision_zero
    (reflexiveLater nonzeroRevision 0 later_nonzeroRevision_zero)

/-- Equality of two streams through the selected prefix depth. -/
def PrefixEqual {Label : Type uLabel}
    (left right : Stream Label) (depth : Nat) : Prop :=
  finiteView depth left = finiteView depth right

/-- Agreement at every strictly earlier depth need not include the current
depth.  The guarded step premise in `prefixAgreement_step` is therefore
load-bearing. -/
theorem earlier_prefixes_need_not_include_current :
    Later
        (PrefixEqual (constant false) (changedAt 0 false true)) 1 ∧
      ¬ PrefixEqual (constant false) (changedAt 0 false true) 1 := by
  constructor
  · intro past earlier
    have pastZero : past = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ earlier)
    subst past
    funext index
    exact Fin.elim0 index
  · intro equalPrefix
    have atZero := congrFun equalPrefix ⟨0, by decide⟩
    simp [finiteView, constant, changedAt] at atZero

/-! ## Axiom audit -/

#print axioms prefixAgreement_step
#print axioms all_prefixes_agree
#print axioms hom_to_stream_eq_unfold_guarded
#print axioms guarded_and_direct_finality_agree
#print axioms later_does_not_imply_now
#print axioms earlier_prefixes_need_not_include_current

end Mettapedia.Coalgebra.GuardedFinality
