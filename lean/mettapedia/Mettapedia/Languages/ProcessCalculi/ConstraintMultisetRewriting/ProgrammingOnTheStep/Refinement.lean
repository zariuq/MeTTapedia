import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# What a firing learns does not type what it makes

On the dependent full step (`Interface.DependentFull.step`), a made row must be typed in the raw
frame the firing extends to (`DependentFull.Make.WellTyped`), before any solution is chosen, and the
step settles along the identity. Knowledge refines the types of rows only at solutions
(`DependentFull.Controls.refined_made_type`); the frame itself never absorbs it.

**The obstruction** (`coerce_refused`, `coerce_typed_at_solutions`). Over `X : U0`, the firing
`coerceFiring` makes the helpers `x : X` and `g : Ground`, tells `(x : X) ≐ (g : Ground)`, and makes
the row `x` at the type `Ground`. At every solution of its own information that row is typed at
`Ground`, so a solution-level reading of typing would admit it. The step refuses it: in the frame,
`x` has the variable type `X`, and `X` is not `Ground` (`x_not_ground`). The firing that makes the
same row at its frame type `X` (`DependentFull.Controls.refinedFiring`) is admitted, with the same
information.

So a dependent program on the step can only make rows at the types its own telescope gives them;
a type learned by matching or telling is used by later matches (heterogeneously, through
solvability), never by typing. The solution `toGround` types the row (`coerce_typed_at_toGround`):
a step that settled along such a solution would admit it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.Refinement

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls

/-- **The firing**: make the helpers `x : X` and `g : Ground`, tell `(x : X) ≐ (g : Ground)`, and make
the row `8 : x : Ground`. -/
def coerceFiring : Firing setting.levels baseState where
  helpers := .cons xType (.cons (groundType _) (.nil _))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(8, ⟨groundType _, (.var 1 : Tower.Tm 3)⟩)]
  tells := [(xRow, gRow)]
  guards := []
  queries := []

/-- Its information is that of `refinedFiring`: the one told equation. -/
theorem coerceFiring_information : coerceFiring.information = refinedFiring.information := rfl

/-- That information is the one told equation `(x : X) ≐ (g : Ground)`. -/
theorem coerceFiring_information_eq : coerceFiring.information = [(xRow, gRow)] := rfl

/-- `x` has the type `X` in the frame `X : U0, x : X, g : Ground`. -/
theorem lookup_x : Ctx.lookup triple.raw 1 = (.var 2 : Tower.Tm 3) := rfl

/-- **`x` is not of type `Ground` in the frame**: its type is the variable `X`, a neutral type, and a
neutral type equals no head. -/
theorem x_not_ground : ¬ Typed Tower.rules triple.raw (.var 1) ground := by
  intro typed
  have le : TypeLe Tower.rules triple.raw (.var 2) ground := by
    have generation := Typed.generation typed
    rw [GenerationAt, lookup_x] at generation
    exact generation
  have formed : CtxFormed Tower.rules triple.raw := triple.formed
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 2 : Tower.Tm 3) := .var 2
  have equal : TypeEq Tower.rules triple.raw (.var 2) ground :=
    TypeLe.rigid (S := setting) le ⟨.sort Tower.zero, .sort _, ground_typed _⟩ formed
      (fun u _ e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inl ⟨u, rfl⟩)).not_former.1 u rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inl ⟨A, B, rfl⟩))).not_former.2.1 A B rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inr (.inl ⟨A, B, rfl⟩)))).not_former.2.2.1 A B rfl)
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) equal formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

/-- **The step refuses the firing**: its made row is not typed in its frame. -/
theorem coerce_refused : ¬ (step setting.levels Nat).Admits coerceFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  exact x_not_ground (typed _ (List.mem_singleton_self _))

/-- **At every solution of its own information, the made row is typed at `Ground`**: the solution makes
`X` equal to `Ground`, and `x` keeps its type `X` along it. -/
theorem coerce_typed_at_solutions {Θ : Context Tower.rules} (τ : Θ ⟶ triple)
    (solved : (frames setting.levels).Models τ coerceFiring.information) :
    Typed Tower.rules Θ.raw (subst τ.substitution (.var 1)) ground := by
  obtain ⟨⟨u, hu, e⟩, -⟩ := tell_heterogeneous setting.levels coerceFiring solved (List.mem_singleton_self _)
  exact Typed.subsume (xRow.reindex τ).2.typed (TypeLe.of_equal e hu)

/-- The solution `X ↦ Ground, x ↦ p, g ↦ p` into the frame `p : Ground`. -/
theorem toGround_solves : (frames setting.levels).Models toGround coerceFiring.information := by
  intro e member
  rw [coerceFiring_information, refinedFiring_information] at member
  obtain rfl := List.mem_singleton.mp member
  show (frames setting.levels).E (xRow.reindex toGround) (gRow.reindex toGround)
  rw [toGround_identifies]
  exact ((frames setting.levels).equivalence _).refl _

/-- **The information is solvable**: the firing is refused for typing alone. -/
theorem coerce_solvable : (frames setting.levels).Solvable coerceFiring.information :=
  ⟨point, toGround, toGround_solves⟩

/-- **At the solution `X ↦ Ground, x ↦ p, g ↦ p` the row is typed**: a step that settled along that
solution would admit the firing. -/
theorem coerce_typed_at_toGround :
    Typed Tower.rules point.raw (subst toGround.substitution (.var 1)) ground :=
  coerce_typed_at_solutions toGround toGround_solves

end ProgrammingOnTheStep.Refinement

#print axioms ProgrammingOnTheStep.Refinement.x_not_ground
#print axioms ProgrammingOnTheStep.Refinement.coerce_refused
#print axioms ProgrammingOnTheStep.Refinement.coerce_typed_at_solutions
#print axioms ProgrammingOnTheStep.Refinement.coerce_solvable
#print axioms ProgrammingOnTheStep.Refinement.coerce_typed_at_toGround

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
