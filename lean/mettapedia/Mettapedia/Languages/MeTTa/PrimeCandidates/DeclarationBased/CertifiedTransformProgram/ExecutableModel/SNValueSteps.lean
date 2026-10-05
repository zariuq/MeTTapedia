import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueModel
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyIterJ

/-!
# Computations and numbers of the transport value model

The value side of the model of every extension of the transport value model (`TExtension.model`)
computes the executable package's equations other than identity elimination: every root step of
the package whose left side is no spine of identity elimination is a step of the model's
reduction (`TExtension.step_of_rules`). So addition, the recursor and the iterator compute on
the value side at their constructor forms, and reduce their scrutinees.

A number of the value side is related to the numbers with its shape, and is realized by the
realizers of its shape: the Kripke candidates of the realizer side's numerals of that shape
(`TExtension.numIndPack_real`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape)
open CertifiedTransforms (shared sharedBody)
open SetProfile (zeroNative sucNative)
open Package (numRecName iterName jName numT numRecApp iterApp iterPartial)

namespace CodeModel

namespace TExtension

variable (X : TExtension) (v : Nat → Nat)

/-! ## Root steps of the package -/

/-- **A root step of the package whose left side is no spine of identity
elimination is a step of the model's reduction**: the computations of the
package other than identity elimination are computations of the transport
value model. -/
theorem step_of_rules {n : Nat} {l r : Tower.Tm n} (step : rules.computation.step l r)
    (notJ : ∀ args, l ≠ appSpine (.const jName) args) :
    (X.model v).rules.computation.step l r := by
  change (RootComputation.unionAll (computations.filter
    fun entry => (fun _ => true) entry.1)).step l r at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  have listedIn : entry ∈ computations := (List.mem_filter.mp mem).1
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X.step v (tmodelListedAt X.roles v 0 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 1 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 2 (by decide)) h
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, -⟩ := h
    exact absurd rfl (notJ _)
  · exact X.step v (tmodelListedAt X.roles v 4 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 5 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 6 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 7 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 8 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 9 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 10 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 11 (by decide)) h

/-- A spine of a constant other than identity elimination is no spine of
identity elimination. -/
theorem ne_jSpine {c : DeclName} (ne : c ≠ jName) {n : Nat} (args : List (Tower.Tm n)) :
    ∀ args', appSpine (.const c) args ≠ appSpine (.const jName) args' :=
  fun _ e => ne (appSpine_const_injective e).1

/-- A computation of the package other than identity elimination computes on the
value side. -/
theorem rule {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ computations)
    (ne : entry.1 ≠ jName) {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    WhRed (X.model v).rules (X.model v).roles l r := by
  obtain ⟨args, rfl⟩ := computations_headed entry mem h
  exact .single (.root (X.step_of_rules v (rules_step mem h) (ne_jSpine ne args)))

/-! ## Addition -/

/-- Reducing the second argument of an addition. -/
theorem add_scrutinee {n : Nat} (x : Tower.Tm n) {y y' : Tower.Tm n}
    (red : WhRed (X.model v).rules (X.model v).roles y y') :
    WhRed (X.model v).rules (X.model v).roles (.app (.app (.const addN) x) y)
      (.app (.app (.const addN) x) y') :=
  WhRed.scrutinee (before := [x]) (after := []) X.extends_.add rfl red

/-- `add x zero = x` on the value side. -/
theorem add_zero_step {n : Nat} (x : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (.app (.app (.const addN) x) (.const zeroN)) x := by
  have rule : equations.family
      (.app (.app (.const addN) (.var 0)) (.const zeroN) : Tower.Tm 1) (.var 0) :=
    equation_listed 0 (by decide) rfl
  exact .root (X.step_of_rules v (equation_sound rule fun _ => x)
    (ne_jSpine (c := addN) (by decide) [_, _]))

/-- `add x (suc a) = suc (add x a)` on the value side. -/
theorem add_suc_step {n : Nat} (x a : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (.app (.app (.const addN) x) (.app (.const sucN) a))
      (.app (.const sucN) (.app (.app (.const addN) x) a)) := by
  have rule : equations.family
      (.app (.app (.const addN) (.var 1)) (.app (.const sucN) (.var 0)) : Tower.Tm 2)
      (.app (.const sucN) (.app (.app (.const addN) (.var 1)) (.var 0))) :=
    equation_listed 1 (by decide) rfl
  exact .root (X.step_of_rules v (equation_sound rule (consSub a fun _ => x))
    (ne_jSpine (c := addN) (by decide) [_, _]))

/-! ## The recursor -/

/-- Reducing the number of an application of the recursor. -/
theorem numRec_scrutinee {n : Nat} (P z s : Tower.Tm n) {t t' : Tower.Tm n}
    (red : WhRed (X.model v).rules (X.model v).roles t t') :
    WhRed (X.model v).rules (X.model v).roles (numRecApp P z s t) (numRecApp P z s t') :=
  WhRed.scrutinee (before := [P, z, s]) (after := []) X.extends_.numRec rfl red

/-- The recursor at zero returns its value at zero. -/
theorem numRec_zero_step {n : Nat} (P z s : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (numRecApp P z s zeroNative) z := by
  have rule : equations.family
      (numRecApp (.var 2) (.var 1) (.var 0) zeroNative : Tower.Tm 3) (.var 1) :=
    equation_listed 5 (by decide) rfl
  exact .root (X.step_of_rules v
    (equation_sound rule (consSub s (consSub z fun _ => P)))
    (ne_jSpine (c := numRecName) (by decide) [_, _, _, _]))

/-- The recursor at a successor applies the step to the recursive call. -/
theorem numRec_suc_step {n : Nat} (P z s a : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (numRecApp P z s (sucNative a))
      (.app (.app s a) (numRecApp P z s a)) := by
  have rule : equations.family
      (numRecApp (.var 3) (.var 2) (.var 1) (sucNative (.var 0)) : Tower.Tm 4)
      (.app (.app (.var 1) (.var 0)) (numRecApp (.var 3) (.var 2) (.var 1) (.var 0))) :=
    equation_listed 6 (by decide) rfl
  exact .root (X.step_of_rules v
    (equation_sound rule (consSub a (consSub s (consSub z fun _ => P))))
    (ne_jSpine (c := numRecName) (by decide) [_, _, _, _]))

/-! ## The iterator -/

/-- Reducing the count of an application of the iterator. -/
theorem iter_scrutinee {n : Nat} (A P s x e : Tower.Tm n) {c c' : Tower.Tm n}
    (red : WhRed (X.model v).rules (X.model v).roles c c') :
    WhRed (X.model v).rules (X.model v).roles (iterApp c A P s x e) (iterApp c' A P s x e) := by
  induction red with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail (WhStep.scrutinee_single (c := iterName) (arity := 6) (before := [])
        (after := [A, P, s, x, e]) X.extends_.iter rfl step)

/-- The iterator at zero returns its value and evidence. -/
theorem iter_zero_step {n : Nat} (A P s x e : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (iterApp (.const zeroN) A P s x e) (.pair x e) := by
  have rule : equations.family
      (iterApp SetProfile.zeroNative (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) : Tower.Tm 5)
      (.pair (.var 1) (.var 0)) :=
    equation_listed 12 (by decide) rfl
  exact .root (X.step_of_rules v
    (equation_sound rule (consSub e (consSub x (consSub s (consSub P (consSub A Fin.elim0))))))
    (ne_jSpine (c := iterName) (by decide) [_, _, _, _, _, _]))

/-- The iterator at a successor uses the step once and continues. -/
theorem iter_suc_step {n : Nat} (a A P s x e : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (iterApp (.app (.const sucN) a) A P s x e)
      (shared s (iterPartial a A P s) x e) := by
  have rule : equations.family
      (iterApp (SetProfile.sucNative (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) :
        Tower.Tm 6)
      (shared (.var 2) (iterPartial (.var 5) (.var 4) (.var 3) (.var 2)) (.var 1) (.var 0)) :=
    equation_listed 13 (by decide) rfl
  exact .root (X.step_of_rules v (equation_sound rule
    (consSub e (consSub x (consSub s (consSub P (consSub A (consSub a Fin.elim0)))))))
    (ne_jSpine (c := iterName) (by decide) [_, _, _, _, _, _]))

/-- One shared use of a step reads both projections of the computed pair. -/
theorem shared_beta_step {n : Nat} (k s x e : Tower.Tm n) :
    WhStep (X.model v).rules (X.model v).roles (shared s k x e)
      (.app (.app k (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e))) := by
  have step := WhStep.beta (R := (X.model v).rules) (roles := (X.model v).roles) (sharedBody k)
    (.app (.app s x) e)
  have body : Presentation.inst0 (.app (.app s x) e) (sharedBody k) =
      .app (.app k (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e)) := by
    show Tm.app (Tm.app (Presentation.inst0 (.app (.app s x) e) (Presentation.rename wk k))
      (.fst (.app (.app s x) e))) (.snd (.app (.app s x) e)) = _
    rw [inst0_rename_wk]
  rw [body] at step
  exact step

/-! ## The numbers -/

/-- A term of the numbers of the value side with a shape. -/
abbrev VShape {n : Nat} (t : Tower.Tm n) (s : NumShape) : Prop :=
  HasShape (X.model v).value.toSetting (X.model v).value.star t s

/-- The realizers of the numerals of a shape on the realizer side. -/
abbrev VNumReal (s : NumShape) : X.realizers.Cand :=
  NumReal X.realReflects X.realNumerals s

/-- The numbers denote their inductive pack. -/
theorem num_inv {m : Nat} {ξ : World (X.model v).reading m} {PA : ValueSide.Pack (X.model v).value m}
    (den : ValueSide.DenS (X.model v).value ξ numT PA) :
    PA = ValueSide.numIndPack (X.model v).value m :=
  ValueSide.DenS.num_inv (X.valueLaws v) den

/-- **The realizers of a number of a shape are the realizer side's numerals of
that shape.** -/
theorem numIndPack_real {m : Nat} {a : Tower.Tm m} {s : NumShape} (shape : X.VShape v a s) :
    (ValueSide.numIndPack (X.model v).value m).real a = X.VNumReal s := by
  rw [ValueSide.numIndPack_real_of_shape (X.valueLaws v) shape]
  exact ModelSN.kcand_ctorReal_num X.realizers X.realRoles_num s

/-- A number with a shape is a valid value of the numbers. -/
theorem num_val {m : Nat} {ξ : World (X.model v).reading m} {a : Tower.Tm m} {sh : NumShape}
    (shape : X.VShape v a sh) {PA : ValueSide.Pack (X.model v).value m}
    (den : ValueSide.DenS (X.model v).value ξ numT PA) : PA.Val a := by
  rw [X.num_inv v den]
  exact ValueSide.numIndPack_rel.mpr ⟨sh, shape, shape⟩

/-- Numbers with a common shape are related. -/
theorem num_rel {m : Nat} {ξ : World (X.model v).reading m} {a b : Tower.Tm m} {sh : NumShape}
    (left : X.VShape v a sh) (right : X.VShape v b sh) {PA : ValueSide.Pack (X.model v).value m}
    (den : ValueSide.DenS (X.model v).value ξ numT PA) : PA.rel a b := by
  rw [X.num_inv v den]
  exact ValueSide.numIndPack_rel.mpr ⟨sh, left, right⟩

/-- Related numbers have a common shape. -/
theorem num_shape {m : Nat} {ξ : World (X.model v).reading m} {a b : Tower.Tm m}
    {PA : ValueSide.Pack (X.model v).value m} (den : ValueSide.DenS (X.model v).value ξ numT PA)
    (related : PA.rel a b) : ∃ sh, X.VShape v a sh ∧ X.VShape v b sh := by
  rw [X.num_inv v den] at related
  exact ValueSide.numIndPack_rel.mp related

/-- A number with a shape is realized by the realizers of the shape. -/
theorem num_real {m r : Nat} {ξ : World (X.model v).reading m} {a : Tower.Tm m} {sh : NumShape}
    (shape : X.VShape v a sh) {PA : ValueSide.Pack (X.model v).value m}
    (den : ValueSide.DenS (X.model v).value ξ numT PA) :
    ∀ {u : Tower.Tm r}, (PA.real a).mem u ↔ (X.VNumReal sh).mem u := by
  intro u
  rw [X.num_inv v den, X.numIndPack_real v shape]

/-- A term of a shape keeps its shape along a renaming. -/
theorem shape_rename {n m : Nat} {a : Tower.Tm n} {s : NumShape} (ρ : Ren n m)
    (shape : X.VShape v a s) : X.VShape v (Presentation.rename ρ a) s := by
  have renamed := shape.subst (renSub ρ)
  rwa [subst_renSub] at renamed

end TExtension

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
