import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelSeparation

/-!
# Channel separation by any structural observation

The existing separation head counts an output on the zero side of a channel
partition and an input on its nonzero side. This generalization permits any
natural-valued channel observation invariant under structural congruence,
including closed reflective names. A zero count proves quiescence even when
structural congruence can rearrange the process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

def separationBy (feature : Pattern → Nat) : Pattern → Nat
  | .apply label arguments =>
      separationHead label (arguments.map (separationBy feature)) (arguments.map feature)
  | .collection _ elements _ => (elements.map (separationBy feature)).sum
  | _ => 0

theorem separationBy_SC (feature : Pattern → Nat)
    (invariant : ∀ {first second}, StructuralCongruence first second → feature first = feature second)
    {left right : Pattern} (related : StructuralCongruence left right) :
    separationBy feature left = separationBy feature right := by
  induction related with
  | alpha _ _ same => subst same; rfl
  | refl _ => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second
  | par_singleton pattern => simp [separationBy]
  | par_nil_left pattern => simp [separationBy, separationHead]
  | par_nil_right pattern => simp [separationBy, separationHead]
  | par_comm first second => simp [separationBy]; omega
  | par_assoc first second third => simp [separationBy]; omega
  | par_cong first second sameLength _ recurse =>
      simp only [separationBy, map_eq_of_get (separationBy feature) sameLength recurse]
  | par_flatten outer inner => simp [separationBy]
  | par_perm _ _ permutation =>
      simp only [separationBy]
      exact (permutation.map _).sum_eq
  | set_perm _ _ permutation =>
      simp only [separationBy]
      exact (permutation.map _).sum_eq
  | set_cong first second sameLength _ recurse =>
      simp only [separationBy, map_eq_of_get (separationBy feature) sameLength recurse]
  | lambda_cong _ _ _ _ _ => simp [separationBy]
  | apply_cong constructor first second sameLength pointwise recurse =>
      simp only [separationBy, map_eq_of_get (separationBy feature) sameLength recurse,
        map_eq_of_get feature sameLength
          (fun index firstBound secondBound => invariant (pointwise index firstBound secondBound))]
  | collection_general_cong _ first second _ sameLength _ recurse =>
      simp only [separationBy, map_eq_of_get (separationBy feature) sameLength recurse]
  | multiLambda_cong _ _ _ _ _ _ => simp [separationBy]
  | subst_cong _ _ _ _ _ _ _ _ => simp [separationBy]
  | quote_drop pattern => simp [separationBy, separationHead]
  | par_empty => simp [separationBy, separationHead]

theorem separationBy_pos_of_reduces (feature : Pattern → Nat)
    (invariant : ∀ {first second}, StructuralCongruence first second → feature first = feature second)
    {source target : Pattern} (step : Reduces source target) :
    0 < separationBy feature source := by
  induction step with
  | @comm channel payload body rest =>
      simp only [separationBy, separationHead, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      by_cases side : feature channel = 0 <;> simp [side]
  | equiv sourceRelated _ _ recurse =>
      rw [separationBy_SC feature invariant sourceRelated]
      exact recurse
  | par _ recurse =>
      simp only [separationBy, List.map_cons, List.sum_cons]
      omega
  | par_any _ recurse =>
      simp only [separationBy, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega

theorem normalForm_of_separationBy_zero (feature : Pattern → Nat)
    (invariant : ∀ {first second}, StructuralCongruence first second → feature first = feature second)
    {source : Pattern} (separated : separationBy feature source = 0) : NormalForm source := by
  rintro ⟨target, ⟨step⟩⟩
  have positive := separationBy_pos_of_reduces feature invariant step
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
