import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionReadout
import Mettapedia.TypeTheory.ContextualSumReadout

/-!
# Interpreting the authored dependent-pair context map

The raw generic pair evaluates to the pairing of the model's two genuine
component variables. Its authored packing substitution therefore evaluates
to the independently constructed sum-comprehension comparison. Opening both
component binders retains the supplied dependent second section.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums ContextualSumComprehension.normalize
  TypeOver.extensionSubstitution

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_genericPair (model : ModelData S C) (stable : StrictPiSubstitution model.products)
    {n : Nat} (Γ : Scope C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (domainEvaluated : model.evaluateType Γ domain = some A)
    (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B) :
    model.evaluateTerm ((Γ.snoc A).snoc B) (genericPair domain body) =
      some ⟨_, (NativeModel C).toCwf.tmSub ((NativeModel C).toCwf.vz (model.sums.operations.sigma A B))
        (pack model.sums A B)⟩ := by
  let double := (ModelRenaming.weaken Γ A).compose (ModelRenaming.weaken (Γ.snoc A) B)
  have domainRead := model.evaluateType_rename stable domain ((Γ.snoc A).snoc B) Γ
    (Fin.succ ∘ Fin.succ) double A domainEvaluated
  have bodyRead := model.evaluateType_rename stable body
    (((Γ.snoc A).snoc B).snoc ((NativeModel C).toCwf.tySub A double.arrow)) (Γ.snoc A)
    (liftRenaming (Fin.succ ∘ Fin.succ)) (double.lift A) B bodyEvaluated
  have firstRead : model.evaluateTerm ((Γ.snoc A).snoc B) (.var 1) =
      some ⟨(NativeModel C).toCwf.tySub A double.arrow, genericFirst A B⟩ := by
    apply congrArg some
    apply Sigma.ext
    · exact ((NativeModel C).toCwf.tySub_comp A ((NativeModel C).toCwf.wk A) ((NativeModel C).toCwf.wk B)).symm
    · exact (genericFirst_heq A B).symm
  have secondRead : model.evaluateTerm ((Γ.snoc A).snoc B) (.var 0) =
      some ⟨_, genericSecond A B⟩ := by
    apply congrArg some
    exact Sigma.ext (genericSecond_type A B) (genericSecond_heq A B).symm
  have pairRead := model.evaluate_pair ((Γ.snoc A).snoc B)
    (domain.rename (Fin.succ ∘ Fin.succ)) (body.rename (liftRenaming (Fin.succ ∘ Fin.succ)))
    ((NativeModel C).toCwf.tySub A double.arrow)
    ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) double.arrow A))
    domainRead bodyRead (.var 1) (.var 0) (genericFirst A B) (genericSecond A B)
    firstRead secondRead
  rw [genericPair, pairRead]
  apply congrArg some
  apply Sigma.ext
  · change model.sums.operations.sigma ((NativeModel C).toCwf.tySub A double.arrow)
        ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) double.arrow A)) =
      (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub (model.sums.operations.sigma A B)
        ((NativeModel C).toCwf.wk (model.sums.operations.sigma A B))) (pack model.sums A B)
    rw [← (NativeModel C).toCwf.tySub_comp, pack_over, model.sums.substitution.1]
    rfl
  · exact (pack_variable model.sums A B).symm

end ModelData

namespace ModelSubstitution

set_option backward.isDefEq.respectTransparency false in
noncomputable def packPair {model : ModelData S C} (stable : StrictPiSubstitution model.products)
    {n : Nat} (Γ : Scope C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (domainEvaluated : model.evaluateType Γ domain = some A)
    (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B) :
    ModelSubstitution model ((Γ.snoc A).snoc B) (Γ.snoc (model.sums.operations.sigma A B))
      (packSubstitution domain body) where
  arrow := pack model.sums A B
  readout index := by
    cases index using Fin.cases with
    | zero => exact model.evaluate_genericPair stable Γ domain body A B domainEvaluated bodyEvaluated
    | succ index =>
        simp only [packSubstitution_succ, ModelData.evaluateTerm, ScopeData.lookup_succ,
          ← Value.substitute_composition]
        rw [pack_over]

def openComponents {model : ModelData S C} {n : Nat} (Γ : Scope C n)
    (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (first second : TermExpr S n) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (b : (NativeModel C).toCwf.Tm Γ.1 ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a)))
    (firstEvaluated : model.evaluateTerm Γ first = some ⟨A, a⟩)
    (secondEvaluated : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    ModelSubstitution model Γ ((Γ.snoc A).snoc B) (instantiateComponents first second) :=
  (openBinder Γ A first a firstEvaluated).extend B second b secondEvaluated

end ModelSubstitution

namespace ModelData

theorem evaluateType_pack (model : ModelData S C) (stable : StrictPiSubstitution model.products)
    {n : Nat} (Γ : Scope C n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (A : (NativeModel C).toCwf.Ty Γ.1)
    (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (M : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 (model.sums.operations.sigma A B)))
    (domainEvaluated : model.evaluateType Γ domain = some A)
    (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B)
    (motiveEvaluated : model.evaluateType (Γ.snoc (model.sums.operations.sigma A B)) motive = some M) :
    model.evaluateType ((Γ.snoc A).snoc B) (motive.substitute (packSubstitution domain body)) =
      some ((NativeModel C).toCwf.tySub M (pack model.sums A B)) :=
  model.evaluateType_substitute stable motive ((Γ.snoc A).snoc B)
    (Γ.snoc (model.sums.operations.sigma A B)) (packSubstitution domain body)
    (ModelSubstitution.packPair stable Γ domain body A B domainEvaluated bodyEvaluated) M motiveEvaluated

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
