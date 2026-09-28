import Mettapedia.OSLF.Syntax.CartesianModelFinitePresentations
import Mathlib.CategoryTheory.Presentable.StrongGenerator

/-!
# Finite generation of cartesian models by authored contexts

The reflected covariant representables form a small strong generator of the
category of cartesian models. Since the generators are finitely presentable,
every finitely presentable model lies in their finite-colimit closure. This
identifies the objects of the relative finite-limit construction by actual
authored context presentations rather than by an unrelated smallness test.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits Opposite
open Mettapedia.OSLF.FormalFiniteLimits (CovariantPresheaf)

variable (C : Type) [SmallCategory C]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The small family of ambient context representations. -/
private def ambientContexts : ObjectProperty (CovariantPresheaf C) :=
  ObjectProperty.ofObj (coyoneda (C := C)).obj

theorem ambientContexts_strongGenerator :
    (ambientContexts C).IsStrongGenerator := by
  have h : (coyoneda (C := C)).IsDense := coyoneda_dense C
  exact Functor.isStrongGenerator_of_isDense (coyoneda (C := C))

variable [HasFiniteProducts C]

/-- The same context generators after imposing the authored product laws. -/
def reflectedContexts : ObjectProperty (Models C) :=
  (ambientContexts C).strictMap (cartesianReflection C)

/-- The context representations already used by the authored-language embedding. -/
def authoredContexts : ObjectProperty (Models C) :=
  ObjectProperty.ofObj (representedContext C).obj

/-- Reflection of an ambient context representation agrees with its existing
cartesian model representation through the adjunction counit. -/
noncomputable def reflectedContextIso (X : Cᵒᵖ) :
    (cartesianReflection C).obj (coyoneda.obj X) ≅
      (representedContext C).obj X := by
  have hcounit : IsIso ((cartesianReflectionAdjunction C).counit.app
      ((representedContext C).obj X)) := by
    change IsIso ((reflectorAdjunction (ProductModel C).ι).counit.app
      ((representedContext C).obj X))
    infer_instance
  let f : (cartesianReflection C).obj (coyoneda.obj X) ⟶
      (representedContext C).obj X :=
    (cartesianReflectionAdjunction C).counit.app
      ((representedContext C).obj X)
  haveI : IsIso f := hcounit
  exact asIso f

/-- A reflective image of a strong generator remains a strong generator here:
maps out of reflected contexts are maps out of the original contexts into the
fully faithful right adjoint. -/
theorem reflectedContexts_strongGenerator :
    (reflectedContexts C).IsStrongGenerator := by
  let P := ambientContexts C
  let L := cartesianReflection C
  let R := (ProductModel C).ι
  let adj := cartesianReflectionAdjunction C
  have hP : P.IsStrongGenerator := ambientContexts_strongGenerator C
  rw [ObjectProperty.isStrongGenerator_iff]
  constructor
  · intro X Y f g h
    apply R.map_injective
    apply hP.isSeparating
    intro G hG k
    have hk := h (L.obj G) (show reflectedContexts C (L.obj G) from
      ⟨G, hG⟩) ((adj.homEquiv G X).symm k)
    have htrans := congrArg (adj.homEquiv G Y) hk
    simpa only [adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply] using htrans
  · intro X Y i mi hi
    have hpres : PreservesLimits R := adj.rightAdjoint_preservesLimits
    have hpresmono : R.PreservesMonomorphisms := inferInstance
    have hmono : Mono (R.map i) := inferInstance
    have hRi : IsIso (R.map i) := by
      apply hP.isIso_of_mono
      intro G hG k
      obtain ⟨a, ha⟩ := hi (L.obj G)
        (show reflectedContexts C (L.obj G) from ⟨G, hG⟩)
        ((adj.homEquiv G Y).symm k)
      refine ⟨(adj.homEquiv G X) a, ?_⟩
      have htrans := congrArg (adj.homEquiv G Y) ha
      simpa only [adj.homEquiv_naturality_right,
        Equiv.apply_symm_apply] using htrans
    exact isIso_of_fully_faithful R i

/-- Every finitely presentable cartesian model is assembled from finitely
many reflected authored-context representations using finite colimits. -/
theorem finiteModels_eq_reflectedContexts_closure :
    isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0} =
      (reflectedContexts C).colimitsCardinalClosure Cardinal.aleph0.{0} := by
  have hsmall : ObjectProperty.Small.{0} (reflectedContexts C) := by
    unfold reflectedContexts ambientContexts
    infer_instance
  have hpresentable : reflectedContexts C ≤
      isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0} := by
    intro M hM
    change (ambientContexts C).strictMap (cartesianReflection C) M at hM
    cases hM with
    | mk F hF =>
      change ObjectProperty.ofObj (coyoneda (C := C)).obj F at hF
      cases hF with
      | mk X =>
        have hamb : IsCardinalPresentable
            (coyoneda.obj X : CovariantPresheaf C) Cardinal.aleph0 :=
          represented_presentable C Cardinal.aleph0 X.unop
        have hinc : ((ProductModel C).ι).IsCardinalAccessible Cardinal.aleph0 :=
          model_inclusion_finitary C
        exact (cartesianReflectionAdjunction C).isCardinalPresentable_leftAdjoint_obj
          Cardinal.aleph0 (coyoneda.obj X)
  exact IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable
    (reflectedContexts_strongGenerator C) hpresentable

/-- Finite presentations are generated, under finite colimits, by the actual
authored-context embedding. The comparison uses the reflection counit, not a
definitional identification between the two model presentations. -/
theorem finiteModels_eq_authoredContexts_closure :
    isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0} =
      (authoredContexts C).colimitsCardinalClosure Cardinal.aleph0.{0} := by
  let P := reflectedContexts C
  let Q := authoredContexts C
  have hPQ : P ≤ Q.colimitsCardinalClosure Cardinal.aleph0 := by
    intro M hM
    change (ambientContexts C).strictMap (cartesianReflection C) M at hM
    cases hM with
    | mk F hF =>
      change ObjectProperty.ofObj (coyoneda (C := C)).obj F at hF
      cases hF with
      | mk X =>
        have hQ : Q ((representedContext C).obj X) := ⟨X⟩
        exact (Q.colimitsCardinalClosure Cardinal.aleph0).prop_of_iso
          (reflectedContextIso C X).symm
          (Q.le_colimitsCardinalClosure Cardinal.aleph0 _ hQ)
  have hQP : Q ≤ P.colimitsCardinalClosure Cardinal.aleph0 := by
    intro M hM
    change ObjectProperty.ofObj (representedContext C).obj M at hM
    cases hM with
    | mk X =>
      have hP : P ((cartesianReflection C).obj (coyoneda.obj X)) :=
        ⟨coyoneda.obj X, ⟨X⟩⟩
      exact (P.colimitsCardinalClosure Cardinal.aleph0).prop_of_iso
        (reflectedContextIso C X)
        (P.le_colimitsCardinalClosure Cardinal.aleph0 _ hP)
  have hPQclosure : P.colimitsCardinalClosure Cardinal.aleph0 ≤
      Q.colimitsCardinalClosure Cardinal.aleph0 :=
    P.colimitsCardinalClosure_le Cardinal.aleph0
      (fun J _ hJ => Q.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        Cardinal.aleph0 J hJ) hPQ
  have hQPclosure : Q.colimitsCardinalClosure Cardinal.aleph0 ≤
      P.colimitsCardinalClosure Cardinal.aleph0 :=
    Q.colimitsCardinalClosure_le Cardinal.aleph0
      (fun J _ hJ => P.isClosedUnderColimitsOfShape_colimitsCardinalClosure
        Cardinal.aleph0 J hJ) hQP
  rw [finiteModels_eq_reflectedContexts_closure C]
  exact le_antisymm hPQclosure hQPclosure

/-- Finite presentations are dense in all cartesian models: every model is
the canonical colimit of its finite presentations. This is the density side
of the eventual classifying equivalence, not yet its essential surjectivity. -/
theorem finitePresentationInclusion_dense :
    ((isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0}).ι).IsDense := by
  let P := reflectedContexts C
  have hsmall : ObjectProperty.Small.{0} P := by
    unfold P reflectedContexts ambientContexts
    infer_instance
  have hpresentable : P ≤
      isCardinalPresentable.{0} (Models C) Cardinal.aleph0.{0} := by
    rw [finiteModels_eq_reflectedContexts_closure C]
    exact P.le_colimitsCardinalClosure Cardinal.aleph0
  have hdense : (P.colimitsCardinalClosure Cardinal.aleph0.{0}).ι.IsDense :=
    ObjectProperty.IsStrongGenerator.isDense_colimitsCardinalClosure_ι
      (reflectedContexts_strongGenerator C) hpresentable
  rw [finiteModels_eq_reflectedContexts_closure C]
  exact hdense

end Mettapedia.OSLF.CartesianContextModels
