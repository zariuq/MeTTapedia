import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonPrograms
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedEquivalence
import Mathlib.CategoryTheory.Types.Basic

/-!
# Type-valued classification and ordinary Set semantics

The generalized binding clone at the one-point stage is transported to the
actual selected program carriers. Its events are the endpoint fibers of the
model's event objects. The comparison identifies classifying values with
ordered valuations and classifying arrows with valuation transport.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}

theorem equivalenceSquare {A B C A' B' C' : Type u}
    (e : A ≃ B) (e' : A' ≃ B') (d : B ≃ C) (d' : B' ≃ C')
    (f : A → A') (g : B → B') (h : C → C')
    (first : ∀ x, e' (f x) = g (e x)) (second : ∀ y, d' (g y) = h (d y)) (x : A) :
    (e'.trans d') (f x) = h ((e.trans d) x) :=
  (congrArg d' (first x)).trans (second (e x))

/-- Pointwise equivalences commuting with arrows give a Type-valued
natural isomorphism. -/
def equivalencesNatIso {C : Type*} [Category C] (F G : C ⥤ Type u)
    (e : ∀ a, F.obj a ≃ G.obj a)
    (commutes : ∀ {a b} (f : a ⟶ b) (x : F.obj a), e b (F.map f x) = G.map f (e a x)) : F ≅ G :=
  NatIso.ofComponents (fun a => (e a).toIso) (fun {a b} f => by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x
    exact commutes f x)

/-- Maps from the one-point stage are actual values. -/
def pointEquiv (X : Type u) : (PUnit.{u + 1} ⟶ X) ≃ X where
  toFun f := f PUnit.unit
  invFun x := TypeCat.ofHom (fun _ => x)
  left_inv f := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext x
    cases x
    rfl
  right_inv _ := rfl

namespace TypeModel

variable (M : CategoricalModel R equations (D := Type u))

/-- Generalized natural families are equivalent to the selected small
function-object carriers. -/
def carrierEquiv (Γ : Ctx S) (s : S.Srt) :
    (M.programModel.stage PUnit).substitution.Carrier Γ s ≃ M.programModel.power Γ s :=
  M.programModel.elemEquiv.trans (pointEquiv _)

/-- The ordinary small binding clone on the represented carriers. -/
def algebra : BindingCloneAlgebra.Algebra.{u} S :=
  CarrierTransport.algebra (M.programModel.stage PUnit) (carrierEquiv M)

/-- The original generalized-element clone maps to represented values. -/
def toRepresented : FreeBindingClone.Hom (M.programModel.stage PUnit) (algebra M) :=
  CarrierTransport.forward (M.programModel.stage PUnit) (carrierEquiv M)

/-- Represented values determine their natural generalized families. -/
def fromRepresented : FreeBindingClone.Hom (algebra M) (M.programModel.stage PUnit) :=
  CarrierTransport.inverse (M.programModel.stage PUnit) (carrierEquiv M)

theorem carrierEquiv_variable {Γ : Ctx S} {s : S.Srt} (v : Var Γ s) :
    carrierEquiv M Γ s ((M.programModel.stage PUnit).substitution.injectVar v) =
      (algebra M).substitution.injectVar v :=
  (toRepresented M).raw.map_variable v

theorem carrierEquiv_substitute {Γ Δ : Ctx S} {s : S.Srt}
    (env : BindingSubstitutionAlgebra.Environment S
      (M.programModel.stage PUnit).substitution.Carrier Γ Δ)
    (x : (M.programModel.stage PUnit).substitution.Carrier Γ s) :
    carrierEquiv M Δ s ((M.programModel.stage PUnit).substitution.substitute env x) =
      (algebra M).substitution.substitute (fun t v => carrierEquiv M Δ t (env t v))
        (carrierEquiv M Γ s x) :=
  (toRepresented M).map_substitute env x

theorem carrierEquiv_operation {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FreeBindingTerms.FamilyArgs S
      (M.programModel.stage PUnit).substitution.Carrier (S.arity o) Γ) :
    carrierEquiv M Γ s ((M.programModel.stage PUnit).operation o args) =
      (algebra M).operation o
        (FreeBindingTerms.FamilyArgs.map (fun {Γ s} x => carrierEquiv M Γ s x) args) :=
  (toRepresented M).raw.map_operation o args

/-- The ordinary model corresponding to a Type-valued categorical model.
Evidence is the actual endpoint fiber read through the carrier equivalence. -/
def operational : OperationalModel R equations where
  base :=
    { algebra := (algebra M)
      satisfies := CarrierTransport.satisfies _ _
        (ProgramPoints.stageSatisfies M.programModel M.program.satisfies PUnit) }
  model := (M.stageModel PUnit).pullback (fromRepresented M)

/-- The ordinary endpoint fiber consists of actual events with their two
represented program values. -/
def EventFiber (j : Judgment (algebra M)) : Type u :=
  {e : M.objects.event j.1 j.2.1 //
    M.objects.source j.1 j.2.1 e = j.2.2.1 ∧ M.objects.target j.1 j.2.1 e = j.2.2.2}

theorem elemEquiv_fromRepresented {Γ : Ctx S} {s : S.Srt}
    (x : (algebra M).substitution.Carrier Γ s) :
    M.programModel.elemEquiv ((fromRepresented M).raw.map x) =
      (pointEquiv (M.programModel.power Γ s)).symm x :=
  M.programModel.elemEquiv.apply_symm_apply _

/-- The generalized-event presentation and the actual endpoint fiber are
equivalent, preserving the event's identity. -/
def eventEquiv (j : Judgment (algebra M)) : (operational M).model.carrier j ≃ EventFiber M j where
  toFun e :=
    ⟨e.1 PUnit.unit,
      (congrArg (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit) e.2.1).trans
        (congrArg (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit)
          (elemEquiv_fromRepresented M j.2.2.1)),
      (congrArg (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit) e.2.2).trans
        (congrArg (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit)
          (elemEquiv_fromRepresented M j.2.2.2))⟩
  invFun e :=
    ⟨(pointEquiv _).symm e.1,
      by
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext u
        cases u
        exact e.2.1.trans (congrArg
          (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit)
          (elemEquiv_fromRepresented M j.2.2.1)).symm,
      by
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        funext u
        cases u
        exact e.2.2.trans (congrArg
          (fun f : PUnit ⟶ M.programModel.power j.1 j.2.1 => f PUnit.unit)
          (elemEquiv_fromRepresented M j.2.2.2)).symm⟩
  left_inv e := Subtype.ext ((pointEquiv _).left_inv e.1)
  right_inv e := Subtype.ext rfl

theorem pullback_represented :
    (operational M).model.pullback (toRepresented M) = M.stageModel PUnit := by
  change ((M.stageModel PUnit).pullback (fromRepresented M)).pullback (toRepresented M) = _
  rw [← SubstitutionModel.pullback_comp]
  have same : FreeBindingClone.Hom.comp (toRepresented M) (fromRepresented M) =
      FreeBindingClone.Hom.id _ := CarrierTransport.forward_inverse _ _
  rw [same]
  rfl

private def modelHomOfEq {A : BindingCloneAlgebra.Algebra.{u + 1} S}
    {X Y : SubstitutionModel.{u + 1, u} R A} (same : X = Y) :
    SubstitutionModel.Hom R A X Y where
  evidence := {
    toFun := fun _ j e => cast
      (congrArg (fun model : SubstitutionModel.{u + 1, u} R A => model.carrier j) same) e
    commutes := by
      cases same
      intros
      rfl }
  preserves := by
    cases same
    intros
    rfl

private theorem modelHomOfEq_heq {A : BindingCloneAlgebra.Algebra.{u + 1} S}
    {X Y : SubstitutionModel.{u + 1, u} R A} (same : X = Y) (j : Judgment A) (e : X.carrier j) :
    HEq ((modelHomOfEq same).evidence.toFun () j e) e :=
  cast_heq _ _

/-- The stage target maps to the ordinary target by representing programs;
the event witnesses are retained. -/
def representedTargetHom : (M.stageTarget PUnit).Hom (operational M).toTarget where
  base := (toRepresented M)
  evidence := modelHomOfEq (pullback_represented M).symm
  point x := FreeBindingClone.Hom.comp ((M.stageTarget PUnit).program x) (toRepresented M)
  point_move f x := by
    rw [(M.stageTarget PUnit).program_move]
    rfl
  program_point _ := rfl

theorem representedTargetHom_event {a : Classifier R equations}
    (value : M.StageValuation PUnit a) (i : Fin (events R equations a).listed.length) :
    HEq ((value.map (representedTargetHom M)).event i) (value.event i) :=
  (ClassifierTarget.Valuation.map_event _ value i).trans
    (modelHomOfEq_heq (pullback_represented M).symm _ _)

/-- An ordinary contextual interpretation determines its actual program point. -/
def recoveredTargetHom : (operational M).toTarget.Hom (M.stageTarget PUnit) where
  base := (fromRepresented M)
  evidence := SubstitutionModel.Hom.id R _ (operational M).model
  point h := (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies _ PUnit).symm
    (FreeBindingClone.Hom.comp h (fromRepresented M))
  point_move {X Y} f h := by
    apply (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies _ PUnit).injective
    have atY := Equiv.apply_symm_apply
      (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies Y PUnit)
      (FreeBindingClone.Hom.comp (FreeBindingClone.Hom.comp (modelMap equations f) h)
        (fromRepresented M))
    have atX := Equiv.apply_symm_apply
      (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit)
      (FreeBindingClone.Hom.comp h (fromRepresented M))
    have moved := (M.stageTarget PUnit).program_move f
      ((ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit).symm
        (FreeBindingClone.Hom.comp h (fromRepresented M)))
    exact atY.trans ((congrArg (FreeBindingClone.Hom.comp (modelMap equations f)) atX).symm.trans
      moved.symm)
  program_point h := Equiv.apply_symm_apply
    (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies _ PUnit) _

theorem recoveredTargetHom_event {a : Classifier R equations}
    (value : (operational M).toTarget.Valuation a) (i : Fin (events R equations a).listed.length) :
    HEq ((value.map (recoveredTargetHom M)).event i) (value.event i) :=
  ClassifierTarget.Valuation.map_event _ value i

theorem recover_represent_point {X : Base equations} (x : (M.stageTarget PUnit).Point X) :
    (recoveredTargetHom M).point ((representedTargetHom M).point x) = x := by
  apply (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit).injective
  change (ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit)
    ((ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit).symm _) = _
  rw [Equiv.apply_symm_apply]
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s t
  exact Equiv.symm_apply_apply _ _

theorem represent_recover_point {X : Base equations} (h : (operational M).toTarget.Point X) :
    (representedTargetHom M).point ((recoveredTargetHom M).point h) = h := by
  change FreeBindingClone.Hom.comp
    ((ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit)
      ((ProgramPoints.interpretationEquiv M.programModel M.program.satisfies X PUnit).symm _))
    (toRepresented M) = h
  rw [Equiv.apply_symm_apply]
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s t
  exact Equiv.apply_symm_apply _ _

/-- The equivalence identifies each ordered event witness with its original
fiber value, even when two witnesses have the same endpoints. -/
def valuationEquiv (a : Classifier R equations) :
    M.StageValuation PUnit a ≃ (operational M).toTarget.Valuation a where
  toFun value := value.map (representedTargetHom M)
  invFun value := value.map (recoveredTargetHom M)
  left_inv value := by
    apply ClassifierTarget.Valuation.ext' (recover_represent_point M value.point)
    intro i
    exact (recoveredTargetHom_event M _ i).trans (representedTargetHom_event M value i)
  right_inv value := by
    apply ClassifierTarget.Valuation.ext' (represent_recover_point M value.point)
    intro i
    exact (representedTargetHom_event M _ i).trans (recoveredTargetHom_event M value i)

/-- Actual values are generalized valuations at the one-point stage. -/
def stageValueEquiv (a : Classifier R equations) :
    M.classifyingObject a ≃ M.StageValuation PUnit a :=
  (pointEquiv _).symm.trans ((M.valuationsRepresentableBy a).homEquiv)

/-- The arrow equation identifies categorical interpretation with the
independently defined valuation transport in Set semantics. -/
theorem stageValueEquiv_map {a b : Classifier R equations} (f : a ⟶ b)
    (x : M.classifyingObject a) :
    stageValueEquiv M b (M.classifyingFunctor.map f x) = (stageValueEquiv M a x).transport f := by
  have point : (pointEquiv (M.classifyingObject b)).symm (M.classifyingFunctor.map f x) =
      (pointEquiv (M.classifyingObject a)).symm x ≫ M.classifyingFunctor.map f := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    rfl
  change (M.valuationsRepresentableBy b).homEquiv
    ((pointEquiv _).symm (M.classifyingFunctor.map f x)) = _
  have acted := M.classifyingFunctor_homEquiv f ((pointEquiv (M.classifyingObject a)).symm x)
  exact (congrArg ((M.valuationsRepresentableBy b).homEquiv) point).trans acted

theorem valuationEquiv_transport {a b : Classifier R equations} (f : a ⟶ b)
    (value : M.StageValuation PUnit a) :
    valuationEquiv M b (value.transport f) = (valuationEquiv M a value).transport f :=
  ClassifierTarget.Valuation.transport_map (representedTargetHom M) value f

/-- Actual classifying values are ordered program-and-event valuations in
the corresponding ordinary model. -/
def valueEquiv (a : Classifier R equations) :
    M.classifyingObject a ≃ (operational M).toTarget.Valuation a :=
  (stageValueEquiv M a).trans (valuationEquiv M a)

/-- The categorical interpretation is the ordinary valuation transport. -/
theorem valueEquiv_map {a b : Classifier R equations} (f : a ⟶ b)
    (x : M.classifyingObject a) :
    valueEquiv M b (M.classifyingFunctor.map f x) = (valueEquiv M a x).transport f :=
  equivalenceSquare (stageValueEquiv M a) (stageValueEquiv M b)
    (valuationEquiv M a) (valuationEquiv M b) (M.classifyingFunctor.map f)
    (fun value => value.transport f) (fun value => value.transport f)
    (stageValueEquiv_map M f) (valuationEquiv_transport M f) x

/-- Type-valued categorical classification agrees naturally with the
ordinary Set semantics of the corresponding represented model. -/
def classificationSetIso : M.classifyingFunctor ≅ combinedSetSemantics (operational M) :=
  equivalencesNatIso M.classifyingFunctor (combinedSetSemantics (operational M))
    (valueEquiv M) (valueEquiv_map M)

end TypeModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTypeComparison

end
