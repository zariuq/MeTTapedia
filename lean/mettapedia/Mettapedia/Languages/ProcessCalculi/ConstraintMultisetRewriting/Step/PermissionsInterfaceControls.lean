import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PermissionsInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullIndependenceControls

/-!
# Read polarity of permissions at dependent frames: controls

Every occurrence is at space `2`. At `triple` with no rows, the firing `makeGround` makes the row
`Ground` (occurrence `1`).

* **Shared: one make spoils the absence** (`shared_absence_spoiled`): with `send` at space `2` the
  make is admitted and permitted, and the absence of `Ground` at space `2` is no longer entailed.
* **Owned: the make is refused** (`owned_make_refused`): without `send` at space `2`.
* **Owned: the absence survives every permitted firing** (`owned_absence_survives`), by
  `dependent_absence_preserved`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PermissionsInterface.DependentControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull
open Interface.DependentFull.Controls
open Interface.DependentFull.IndependenceControls
open MeTTaCalculus.InteractionTypes (Facet Rights FormedUnder)

abbrev X := ContextualDependentEta.frames setting.levels
abbrev P := (step setting.levels Nat).toStep

/-- Every occurrence is at space `2`. -/
def space : Nat → Nat := fun _ => 2

/-- Every right everywhere. -/
def shared : Rights Nat := fun _ _ => true

/-- No `send` at space `2`. -/
def owned : Rights Nat
  | 2, .send => false
  | _, _ => true

def start : State Tower.rules Nat := stateAt [] ∅

/-- The make firing, at the start. -/
abbrev make : Firing setting.levels start := Plain.toFiring (s := start) makeGround

theorem make_admitted : P.Admits make := by
  refine (Plain.admits_toFiring (s := start) makeGround).mpr
    ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
      (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun o _ present => absurd present (Finset.notMem_empty o)⟩,
      ⟨triple, 𝟙 triple, fun e member => absurd member List.not_mem_nil⟩,
      fun _ _ _ => ⟨Frames.models_nil _, fun _ member => absurd member List.not_mem_nil⟩⟩
  obtain rfl := List.mem_singleton.mp member
  exact Make.ofRow_wellTyped _

/-- The absence of `Ground` at space `2`, at a solution. -/
abbrev AbsentGround {s : State Tower.rules Nat} (p : TotalTerm s.frame) {b : Context Tower.rules}
    (σ : b ⟶ s.frame) : Prop :=
  AbsentAt P space (dependentLabels Nat) 2 p σ

/-- **Owned: the make is refused** without `send` at space `2`. -/
theorem owned_make_refused : ¬ (Permissions.permitted P space owned).Admits make :=
  Permissions.refused_without_send P space owned (o := 1) (List.mem_singleton_self 1) rfl

/-- **Shared: one make spoils the absence.** -/
theorem shared_absence_spoiled :
    Permissions.Permitted P space shared make ∧
      (X).Entails start.knowledge (fun _ σ => AbsentGround (s := start) groundUniverse σ) ∧
      ¬ (X).Entails (P.result make make_admitted).knowledge
        (fun _ τ => AbsentGround (s := P.result make make_admitted)
          ((X).act (P.along make make_admitted) groundUniverse) τ) := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, ?_⟩
  · intro _ _ _ o present
    exact absurd present (Finset.notMem_empty o)
  · intro entailed
    have spoiled := entailed triple (𝟙 triple) (fun e member => absurd member List.not_mem_nil) 1
      ((makeGround.mem_fire_iff start.toLocal 1).mpr (.inr (List.mem_singleton_self 1))) rfl
    apply spoiled
    have moved : X.act (𝟙 triple) (X.act (P.along make make_admitted) groundUniverse) = groundUniverse :=
      (X.act_id _).trans ((X.act_comp _ _ _).trans ((X.act_id _).trans (X.act_id _)))
    have labelled : X.act (𝟙 triple) (dependentLabels Nat (P.result make make_admitted) 1) = groundUniverse :=
      X.act_id _
    exact (congrArg₂ X.E moved labelled).mpr ((X.equivalence triple).refl _)

/-- **Owned: the absence survives every permitted firing.** -/
theorem owned_absence_survives {f : Firing setting.levels start} (admitted : P.Admits f)
    (formed : Permissions.Permitted P space owned f) :
    (X).Entails (P.result f admitted).knowledge
      (fun _ τ => AbsentGround (s := P.result f admitted) ((X).act (P.along f admitted) groundUniverse) τ) :=
  dependent_absence_preserved space owned admitted formed (h := 2) rfl
    fun _ _ _ o present => absurd present (Finset.notMem_empty o)

#print axioms make_admitted
#print axioms owned_make_refused
#print axioms shared_absence_spoiled
#print axioms owned_absence_survives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PermissionsInterface.DependentControls
