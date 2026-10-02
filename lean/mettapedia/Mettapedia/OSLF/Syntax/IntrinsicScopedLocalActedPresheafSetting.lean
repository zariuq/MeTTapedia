import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericEvent
import Mettapedia.OSLF.Syntax.CategoricalBindingPreservation
import Mettapedia.GSLT.Topos.PresheafPredicateProjection
import Mettapedia.GSLT.Topos.ConstructivePresheafFunctions
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Subfunctor.Subobject
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Presheaves and predicates on the authored operational classifier

The presheaf base is the rule-local, substitution-closed classifier. Its
event-free objects represent programs in every context and sort. Predicate
objects use the existing subfunctor projection, including its cartesian lifts,
and correspond to actual subobjects of these standard presheaves.

Finite limits and internal function objects belong to the entire presheaf
category. Identifying a particular representable with a binder function object
requires a further comparison of the authored term and assignment arrows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres

universe w

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-- The standard presheaf category on the authored operational classifier. -/
abbrev Presheaf := (Classifier R equations)ᵒᵖ ⥤ Type w

/-- The embedding at the declared presheaf universe. -/
abbrev embedding : Classifier R equations ⥤ Presheaf.{w} R equations :=
  uliftYoneda.{w} (C := Classifier R equations)

/-- At the small universe the lifted embedding agrees naturally with Yoneda. -/
def embeddingZeroIso : embedding.{0} R equations ≅ yoneda :=
  uliftYonedaIsoYoneda

/-- The actual program restriction of the lifted Yoneda carrier. -/
abbrev programRestriction : Object S ⥤ Presheaf.{w} R equations :=
  (authoredEquationPresentation S equations).quotientFunctor ⋙
    programSection R equations ⋙ embedding.{w} R equations

/-- Generic programs are the restriction's image of the actual scoped term
object, retaining their full context and result sort. -/
abbrev program (Γ : Ctx S) (s : S.Srt) : Presheaf.{w} R equations :=
  (programRestriction R equations).obj (CategoricalBindingModel.oneObj Γ s)

/-- The generic carrier retains each individual event. -/
abbrev event (Γ : Ctx S) (s : S.Srt) : Presheaf.{w} R equations :=
  (embedding R equations).obj (eventObject R equations Γ s)

/-- Finite limits are computed in the standard functor category. -/
theorem hasFiniteLimits : HasFiniteLimits (Presheaf.{w} R equations) :=
  inferInstance

/-- The presheaf products are the actual cartesian monoidal products. -/
abbrev cartesianStructure : CartesianMonoidalCategory (Presheaf.{w} R equations) :=
  inferInstance

/-- Internal function objects satisfy the monoidal closed universal property. -/
abbrev closedStructure : MonoidalClosed (Presheaf.{w} R equations) :=
  inferInstance

/-- Presheaf predicates correspond to subobjects, not merely subsets of one
stage's carrier. -/
def predicateSubobjectEquiv (P : Presheaf.{w} R equations) :
    Subfunctor P ≃o Subobject P :=
  Subfunctor.orderIsoSubobject P

/-- The existing predicate total category instantiated on this classifier. -/
abbrev PredicateTotal :=
  Mettapedia.GSLT.Topos.PresheafPredicateTotal (Classifier R equations)

/-- The actual predicate projection onto classifier presheaves. -/
abbrev predicateProjection :=
  Mettapedia.GSLT.Topos.presheafPredicateProjection (Classifier R equations)

/-- Every predicate has the required cartesian reindexing lifts. -/
theorem predicateProjection_fibered : IsFibered (predicateProjection R equations) :=
  Mettapedia.GSLT.Topos.presheafPredicateProjection_fibered (Classifier R equations)

/-- Predicate reindexing is a strongly cartesian lift over every base arrow. -/
theorem predicateLift_stronglyCartesian
    {P Q : Presheaf.{0} R equations} (φ : Subfunctor Q) (f : P ⟶ Q) :
    IsStronglyCartesian (predicateProjection R equations) f
      (Mettapedia.GSLT.Topos.predicateLift φ f) :=
  Mettapedia.GSLT.Topos.predicateLift_stronglyCartesian φ f

/-- Every predicate map over a composite factors uniquely through the
classifier's concrete predicate pullback. -/
theorem predicateLift_factorization
    {P Q : Presheaf.{0} R equations} (φ : Subfunctor Q) (f : P ⟶ Q)
    (a : PredicateTotal R equations) (g : a.base ⟶ P)
    (h : a ⟶ (⟨Q, φ⟩ : PredicateTotal R equations))
    [IsHomLift (predicateProjection R equations) (g ≫ f) h] :
    ∃! k : a ⟶ Mettapedia.GSLT.Topos.predicateLiftDomain φ f,
      IsHomLift (predicateProjection R equations) g k ∧
        k ≫ Mettapedia.GSLT.Topos.predicateLift φ f = h :=
  Mettapedia.GSLT.Topos.predicateLift_factorization φ f a g h

/-- A map to an event-free classifier object is exactly its program
assignment. Events in the source do not add hidden program coordinates. -/
def programHomEquiv (a : Classifier R equations) (X : Base equations) :
    (a ⟶ (programSection R equations).obj X) ≃ (a.base ⟶ X) where
  toFun f := f.base
  invFun f := arrow R equations f (toEmpty R _ _ rfl)
  left_inv f := by
    apply _root_.CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext
    case hfg₁ => rfl
    case hfg₂ => exact hom_ext_empty R rfl _ _
  right_inv _ := rfl

/-- The assignment comparison respects precomposition of classifier arrows. -/
theorem programHomEquiv_precompose {a b : Classifier R equations}
    (f : a ⟶ b) (X : Base equations)
    (g : b ⟶ (programSection R equations).obj X) :
    programHomEquiv R equations a X (f ≫ g) =
      f.base ≫ programHomEquiv R equations b X g := rfl

/-- The assignment comparison respects maps of equation contexts. -/
theorem programHomEquiv_postcompose (a : Classifier R equations)
    {X Y : Base equations} (f : X ⟶ Y)
    (g : a ⟶ (programSection R equations).obj X) :
    programHomEquiv R equations a Y (g ≫ (programSection R equations).map f) =
      programHomEquiv R equations a X g ≫ f := rfl

/-- Forgetting event variables is left adjoint to the program section.
Consequently the section preserves the existing program-context limits. -/
def programSectionAdjunction :
    _root_.CategoryTheory.Pseudofunctor.CoGrothendieck.forget (fibres R equations) ⊣
      programSection R equations :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun a X => (programHomEquiv R equations a X).symm
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := by
        intro a X Y f g
        apply _root_.CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext
        case hfg₁ => rfl
        case hfg₂ => exact hom_ext_empty R rfl _ _ }

/-- Products and terminal objects of equation contexts remain their limits
when viewed as event-free classifier objects. -/
theorem programSection_preservesLimits :
    PreservesLimitsOfSize.{0, 0} (programSection R equations) :=
  (programSectionAdjunction R equations).rightAdjoint_preservesLimits

/-- The composite program embedding preserves the actual program-context
limits through both the section and lifted Yoneda. -/
theorem programEmbedding_preservesLimits :
    PreservesLimitsOfSize.{0, 0}
      (programSection R equations ⋙ embedding.{w} R equations) := by
  let := programSection_preservesLimits R equations
  infer_instance

/-- Yoneda preserves the pullback square that reindexes an event variable.
This is the required operational pullback, without any preservation premise. -/
theorem embedding_eventPullback {a b : Classifier R equations} (f : b ⟶ a)
    (j : AuthoredPositionedRulePolynomial.Judgment (modelAt equations a.base)) :
    IsPullback
      ((embedding.{w} R equations).map (reindex R equations f j))
      ((embedding.{w} R equations).map
        (projection R equations b
          (AuthoredPositionedRulePolynomial.mapJudgment (modelMap equations f.base) j)))
      ((embedding.{w} R equations).map (projection R equations a j))
      ((embedding.{w} R equations).map f) :=
  (embedding.{w} R equations).map_isPullback (isPullback_reindex R equations f j)

/-- An event-free representable is the program representable reindexed along
the actual forgetful functor. This comparison is natural at all classifier
stages, including stages carrying event variables. -/
def programRepresentableIso (X : Base equations) :
    (embedding.{w} R equations).obj ((programSection R equations).obj X) ≅
      (_root_.CategoryTheory.Pseudofunctor.CoGrothendieck.forget
        (fibres R equations)).op ⋙ (uliftYoneda.{w} (C := Base equations)).obj X :=
  NatIso.ofComponents
    (fun a => (Equiv.ulift.trans
      ((programHomEquiv R equations a.unop X).trans Equiv.ulift.symm)).toIso)
    (by
      intro a b f
      ext x
      rfl)

/-- In particular, the generic program carrier is represented by the actual
equation-class term object, with its context and sort unchanged. -/
def programEquationContextIso (Γ : Ctx S) (s : S.Srt) :
    program.{w} R equations Γ s ≅
      (_root_.CategoryTheory.Pseudofunctor.CoGrothendieck.forget
        (fibres R equations)).op ⋙
          (uliftYoneda.{w} (C := Base equations)).obj ⟨single S Γ s⟩ :=
  programRepresentableIso R equations ⟨single S Γ s⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
