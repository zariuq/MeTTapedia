import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentCwfMorphism
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentNormalization
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.BoundaryJudgments

/-!
# The permissive tower does not reflect simple-type inhabitation

The sealed tower's raw typing relation does not require domain formation in
lambda introduction or target formation in conversion. An untyped recursive
type can therefore be used as a lambda domain. With
`D = lambda x. Pi (x x) ground` and `A = D D`, ordinary beta conversion gives
`A = Pi A ground`. The self-applicative term `delta = lambda x. x x` then has
both types, so `delta delta` inhabits the closed ground type.

The empty context and the final ground type are well formed. Thus merely
packaging endpoint formation into the existing syntactic contextual category
does not exclude this derivation: formation would need to be enforced inside
the typing rules. No existing rule or semantic interface is changed here.

This refutes inhabitation reflection from the current raw tower to the
intrinsic simple fragment. It does not contradict conversion reflection
between two already translated simple terms. The Pure regular-typing theorem
rejects the self-applicative computational skeleton; it is a different typing
relation, not a normalization theorem for all raw tower judgments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentInhabitationBoundary

open Presentation
open FourFaceBetaExperiment
open FourFaceBetaExperiment.IntrinsicSTT

/-- An untyped type-level function used only to expose the missing formation
premise. It is not asserted to be a formed tower type. -/
def typeDelta {n : Nat} : Tower.Tm n :=
  .lam (.pi (.app (.var 0) (.var 0)) (.head .legacyGround))

def recursiveDomain {n : Nat} : Tower.Tm n := .app typeDelta typeDelta

def delta {n : Nat} : Tower.Tm n := .lam (.app (.var 0) (.var 0))

def omega {n : Nat} : Tower.Tm n := .app delta delta

/-- The recursive-domain equation is one ordinary beta step, not an added
axiom, universe equation, or declaration-specific root computation. -/
theorem recursiveDomain_unfold (n : Nat) :
    Conv Tower.HeadEq (recursiveDomain : Tower.Tm n)
      (.pi recursiveDomain (.head .legacyGround)) :=
  .rel _ _ (.betaPi _ _)

/-- Raw lambda introduction does not request formation of the recursive domain. -/
theorem delta_typed {n : Nat} (Γ : Tower.Ctx n) :
    Tower.HasType Γ delta (.pi recursiveDomain (.head .legacyGround)) := by
  apply HasType.lamIntro
  have typedVariable : Tower.HasType (.snoc Γ recursiveDomain) (.var 0) recursiveDomain :=
    HasType.var 0
  have function := HasType.conv typedVariable (recursiveDomain_unfold (n + 1))
  exact HasType.appElim function typedVariable

/-- A closed inhabitant of the opaque ground type in the permissive tower. -/
theorem omega_typed_ground :
    Tower.HasType .nil (omega : Tower.Tm 0) (.head .legacyGround) := by
  have function := delta_typed (.nil : Tower.Ctx 0)
  have argument : Tower.HasType .nil delta recursiveDomain :=
    HasType.conv function (.symm _ _ (recursiveDomain_unfold 0))
  exact HasType.appElim function argument

/-- The existing tower checking meaning adds endpoint formation, but that
condition also holds here. This is a semantic claim, not acceptance by a
particular executable checker. -/
theorem omega_tower_check_meaning :
    BoundaryJudgments.TowerMeaning .check BoundaryJudgments.emptyTowerContext
      omega (.head .legacyGround) :=
  ⟨omega_typed_ground, ⟨Tower.zero, .headType .legacyGround⟩⟩

theorem omega_tower_synthesis_meaning :
    BoundaryJudgments.TowerMeaning .synthesize BoundaryJudgments.emptyTowerContext
      omega (.head .legacyGround) :=
  omega_tower_check_meaning

/-- Its computation genuinely loops by beta reduction. -/
theorem omega_self_step : Step Tower.HeadEq (omega : Tower.Tm 0) omega :=
  .betaPi _ _

/-- The loop remains a genuine reduction after erasing tower heads. Thus the
failure is not caused by reflexive head-equation steps. -/
theorem omega_skeleton_not_accessible :
    ¬ Pure.Intrinsic.PresentationBoundary.ReductionAccessible
      (TowerConversionSkeleton.erase (omega : Tower.Tm 0)) :=
  Pure.Intrinsic.PresentationBoundary.omega_not_in_normalizing_candidate

/-- The existing regular Pure kernel rejects the computational skeleton at
every result type. It cannot supply normalization for this tower derivation. -/
theorem omega_skeleton_has_no_regular_judgment :
    ¬ ∃ typeCode, Pure.Intrinsic.PresentationBoundary.RegularJudgment
      .nil (TowerConversionSkeleton.erase (omega : Tower.Tm 0)) typeCode :=
  Pure.Intrinsic.PresentationBoundary.regular_omega_has_no_judgment

/-- The raw tower reduction relation is likewise not strongly normalizing on
this genuinely beta-looping, closed, ground-typed term. -/
theorem omega_not_step_accessible :
    ¬ Acc (fun reduct source : Tower.Tm 0 => Step Tower.HeadEq source reduct) omega := by
  intro accessible
  have noSelf : ∀ (term : Tower.Tm 0),
      Acc (fun reduct source : Tower.Tm 0 => Step Tower.HeadEq source reduct) term →
      ¬ Step Tower.HeadEq term term := by
    intro term accessibility
    induction accessibility with
    | intro term _ ih =>
        intro selfStep
        exact ih term selfStep selfStep
  exact noSelf _ accessible omega_self_step

/-- There is no intrinsic simple term at the empty-context ground type. -/
theorem no_simple_ground : ¬ Nonempty (Term [] .atom) := by
  rintro ⟨term⟩
  have impossible : Empty := term.denote (Ground := Empty) ⟨fun v => nomatch v⟩
  exact impossible.elim

/-- Quotienting intrinsic terms by beta conversion cannot create an inhabitant
of an empty term fibre. -/
theorem no_simple_ground_class : ¬ Nonempty (BetaClass [] .atom) := by
  rintro ⟨termClass⟩
  induction termClass using Quotient.inductionOn with
  | _ term => exact no_simple_ground ⟨term⟩

/-- The counterexample has a formed ambient context and a formed result type
in the actual contextual target of the simple-fragment translation. -/
def contextualGroundInhabitant :
    SyntacticContextual.Term (SimpleFragmentCwfMorphism.mapContext [])
      (SimpleFragmentCwfMorphism.simpleType
        (SimpleFragmentCwfMorphism.mapContext []) .atom) where
  code := omega
  typed := omega_typed_ground

/-- Endpoint formation alone does not make the contextual term map full. -/
theorem no_contextual_ground_retraction :
    ¬ Nonempty
      (SyntacticContextual.Term (SimpleFragmentCwfMorphism.mapContext [])
          (SimpleFragmentCwfMorphism.simpleType
            (SimpleFragmentCwfMorphism.mapContext []) .atom) → Term [] .atom) := by
  rintro ⟨retract⟩
  exact no_simple_ground ⟨retract contextualGroundInhabitant⟩

/-- Unlike the raw annotation-erasure collision, the inhabitation mismatch
survives passage to intrinsic beta classes. -/
theorem no_contextual_ground_class_retraction :
    ¬ Nonempty
      (SyntacticContextual.Term (SimpleFragmentCwfMorphism.mapContext [])
          (SimpleFragmentCwfMorphism.simpleType
            (SimpleFragmentCwfMorphism.mapContext []) .atom) → BetaClass [] .atom) := by
  rintro ⟨retract⟩
  exact no_simple_ground_class ⟨retract contextualGroundInhabitant⟩

/-- The unrestricted inhabitation-reflection statement is false for the
current sealed raw tower, already at a closed simple ground type. -/
theorem no_inhabitation_reflection :
    ¬ (∀ (Γ : List Ty) (A : Ty) (term : Tower.Tm Γ.length),
      Tower.HasType (TowerDTT.eraseContext Γ) term (TowerDTT.eraseTypeAt Γ.length A) →
        Nonempty (Term Γ A)) := by
  intro reflects
  exact no_simple_ground (reflects [] .atom omega omega_typed_ground)

#print axioms recursiveDomain_unfold
#print axioms omega_typed_ground
#print axioms omega_tower_check_meaning
#print axioms omega_tower_synthesis_meaning
#print axioms omega_self_step
#print axioms omega_skeleton_not_accessible
#print axioms omega_skeleton_has_no_regular_judgment
#print axioms omega_not_step_accessible
#print axioms no_simple_ground
#print axioms no_simple_ground_class
#print axioms contextualGroundInhabitant
#print axioms no_contextual_ground_retraction
#print axioms no_contextual_ground_class_retraction
#print axioms no_inhabitation_reflection

end SimpleFragmentInhabitationBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
