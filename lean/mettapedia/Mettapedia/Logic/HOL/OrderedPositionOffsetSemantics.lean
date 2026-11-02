import Mettapedia.Logic.HOL.OrderedPositionOffsets

/-!
# Exact natural-number meaning of retained segment offsets

At a valid segment ordinal, the absolute slot is the sum of all preceding
counts plus the retained local position. An invalid ordinal has no witness.
The model contract keeps full domains and the zero/successor representation
explicit; no executable decoder is inferred from the semantic equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionPrograms
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Δ : Ctx Base} {number index : Ty Base}
    (zero : ClosedTerm Const number) (successor : ClosedTerm Const (number ⇒ number))
    (model : HenkinModel.{u,v,w} Base Const) (numbers : Nat ≃ Ty.denote model.Carrier number)
    (full : model.FullDomains) (arithmeticValues : model.Valuation [])
    (zeroPreserved : model.denote zero arithmeticValues = numbers 0)
    (successorPreserved : ∀ n, model.denote successor arithmeticValues (numbers n) = numbers (n + 1))

include full zeroPreserved successorPreserved
theorem selectedOffsetAt_denote (ordinal : Nat) (plan : Plan Const Γ number index)
    (environment : model.Valuation Γ) (images : Subst Const Γ Δ)
    (localPos slot : Term Const Δ number) (values : model.Valuation Δ)
    (represented : ∀ {type} (entry : Var Γ type), model.denote (images entry) values = environment entry) :
    (model.denote (selectedOffsetAt zero successor ordinal plan images localPos slot) values).down ↔
      ordinal < plan.length ∧ numbers.symm (model.denote slot values) =
        (((evaluate model numbers environment plan).take ordinal).map Prod.fst).sum +
          numbers.symm (model.denote localPos values) := by
  have closedDenote {type : Ty Base} (term : ClosedTerm Const type) (context : Ctx Base)
      (later : model.Valuation context) :
      model.denote (weakenCtx context term) later = model.denote term arithmeticValues := by
    rw [model.denote_weakenCtx]
    apply congrArg (model.denote term)
    funext type entry
    exact nomatch entry
  induction plan generalizing ordinal Δ with
  | nil => simp [selectedOffsetAt, HenkinModel.denote, PreModel.denote]
  | cons segment rest previous =>
      rcases segment with ⟨count, childIndex⟩
      cases ordinal with
      | zero =>
          simp only [selectedOffsetAt, HenkinModel.denote, PreModel.denote,
            model.eqv_iff_eq_of_fullDomains full, List.length_cons, Nat.zero_lt_succ,
            List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, true_and]
          exact numbers.symm.injective.eq_iff.symm
      | succ ordinal =>
          have translated : model.denote (subst images count) values = model.denote count environment := by
            rw [Soundness.denote_subst]
            apply congrArg (model.denote count)
            funext type entry
            exact represented entry
          have recursive (offset : Ty.denote model.Carrier number) :=
            previous ordinal (fun entry => weaken (images entry)) (weaken localPos) (.var .vz)
              (model.extend values offset) (fun entry =>
                (Soundness.denote_weaken model (images entry) values offset).trans (represented entry))
          change (∃ offset, model.adm number offset ∧
            (model.denote (weakenCtx _ (SuccessorOrder.sum zero successor)) (model.extend values offset)
              (model.denote (weaken (subst images count)) (model.extend values offset)) offset
              (model.denote (weaken slot) (model.extend values offset))).down ∧
            (model.denote (selectedOffsetAt zero successor ordinal rest (fun entry => weaken (images entry))
              (weaken localPos) (.var .vz)) (model.extend values offset)).down) ↔ _
          simp only [closedDenote, Soundness.denote_weaken, translated,
            SuccessorOrder.sum_iff model full successor arithmeticValues zero numbers zeroPreserved successorPreserved,
            recursive, evaluate, List.map_cons, List.take_succ_cons, List.sum_cons, List.length_cons,
            Nat.add_lt_add_iff_right, HenkinModel.denote, PreModel.denote, PreModel.extend]
          constructor
          · rintro ⟨offset, _, same, valid, tail⟩
            exact ⟨valid, by omega⟩
          · rintro ⟨valid, same⟩
            refine ⟨numbers ((((evaluate model numbers environment rest).take ordinal).map Prod.fst).sum +
              numbers.symm (model.denote localPos values)), full _ _, ?_, valid, ?_⟩
            · simpa only [Equiv.symm_apply_apply, Nat.add_assoc, evaluate] using same
            · exact Equiv.symm_apply_apply _ _

#print axioms selectedOffsetAt_denote
end Mettapedia.Logic.HOL.OrderedPositionPrograms
