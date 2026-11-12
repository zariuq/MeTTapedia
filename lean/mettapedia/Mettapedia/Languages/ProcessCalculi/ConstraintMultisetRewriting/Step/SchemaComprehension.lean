import Mettapedia.TypeTheory.ContextualSchemaTelescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ContextualCwf
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUniverseFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta

/-!
# Schema comprehension with the frame's actual equality

Context comprehension does not choose the equality used by a solver.
A substitution-stable equivalence on judged CwF terms supplies that equality.
The constructions below retain the real raw-conversion and typed-beta-eta
frame instances. The strict semantic model remains a separate instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace SchemaComprehension

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u v w w'

/-- The equality of a typed language, independently of context comprehension. -/
structure Equality (C : Cwf.{u, v, w, w'}) where
  relates : {Γ : C.Ctx} → NativeUniverse.Judged C Γ → NativeUniverse.Judged C Γ → Prop
  equivalence : ∀ Γ : C.Ctx, Equivalence (@relates Γ)
  substitute : ∀ {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {first second : NativeUniverse.Judged C Γ}, relates first second →
      relates ((NativeUniverse.cwfFrames C).act σ first)
        ((NativeUniverse.cwfFrames C).act σ second)

def Equality.frames {C : Cwf.{u, v, w, w'}} (equality : Equality C) :
    Frames (NativeUniverse.Judged C) (fun Γ Δ : C.Ctx => C.Sub Δ Γ) :=
  { NativeUniverse.cwfFrames C with
    E := equality.relates
    equivalence := equality.equivalence
    preserves := equality.substitute }

def strictEquality (C : Cwf.{u, v, w, w'}) : Equality C where
  relates := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  substitute := @fun _ _ σ _ _ same => congrArg ((NativeUniverse.cwfFrames C).act σ) same

theorem strict_frames (C : Cwf.{u, v, w, w'}) :
    (strictEquality C).frames = NativeUniverse.cwfFrames C := rfl

section FormationSensitive

variable {Head : Type} {rules : Rules Head}

def formationEntry {Γ : FormationSensitiveContextual.Context rules}
    (value : NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ) :
    Dependent.Entry Γ := ⟨value.1, value.2⟩

def formationValue {Γ : FormationSensitiveContextual.Context rules}
    (entry : Dependent.Entry Γ) :
    NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ := ⟨entry.type, entry.term⟩

def formationEntryEquiv (Γ : FormationSensitiveContextual.Context rules) :
    NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ ≃ Dependent.Entry Γ where
  toFun := formationEntry
  invFun := formationValue
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

def formationEquality (rules : Rules Head) : Equality (FormationSensitiveContextual.cwf rules) where
  relates first second := Dependent.Entry.Convertible (formationEntry first) (formationEntry second)
  equivalence _ :=
    ⟨fun _ => Dependent.Entry.Convertible.refl _, Dependent.Entry.Convertible.symm,
      Dependent.Entry.Convertible.trans⟩
  substitute := @fun _ _ σ _ _ same => (Dependent.frames rules).preserves σ same

def formationStore {Γ : FormationSensitiveContextual.Context rules}
    (store : EquationStore (NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ)) :
    EquationStore (Dependent.Entry Γ) :=
  store.map fun equation => (formationEntry equation.1, formationEntry equation.2)

theorem formation_models_iff {Γ Δ : FormationSensitiveContextual.Context rules}
    (σ : Δ ⟶ Γ)
    (store : EquationStore (NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ)) :
    (formationEquality rules).frames.Models σ store ↔
      (Dependent.frames rules).Models σ (formationStore store) := by
  constructor
  · intro solved equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact solved original present
  · intro solved equation member
    exact solved (formationEntry equation.1, formationEntry equation.2)
      (List.mem_map.mpr ⟨equation, member, rfl⟩)

theorem formation_solvable_iff {Γ : FormationSensitiveContextual.Context rules}
    (store : EquationStore (NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ)) :
    (formationEquality rules).frames.Solvable store ↔
      (Dependent.frames rules).Solvable (formationStore store) := by
  constructor
  · rintro ⟨Δ, σ, solved⟩
    exact ⟨Δ, σ, (formation_models_iff σ store).mp solved⟩
  · rintro ⟨Δ, σ, solved⟩
    exact ⟨Δ, σ, (formation_models_iff σ store).mpr solved⟩

theorem formation_entails_iff {Γ : FormationSensitiveContextual.Context rules}
    (store : EquationStore (NativeUniverse.Judged (FormationSensitiveContextual.cwf rules) Γ))
    (observation : (Δ : FormationSensitiveContextual.Context rules) → (Δ ⟶ Γ) → Prop) :
    (formationEquality rules).frames.Entails store observation ↔
      (Dependent.frames rules).Entails (formationStore store) observation := by
  constructor
  · intro holds Δ σ solved
    exact holds Δ σ ((formation_models_iff σ store).mpr solved)
  · intro holds Δ σ solved
    exact holds Δ σ ((formation_models_iff σ store).mp solved)

end FormationSensitive

section TypedEquality

open TypedEquality TypedEquality.Normalization

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- Typed beta/eta equality from the actual unifier frame, on exactly its typed terms. -/
def typedEquality : Equality (TypedContextual.cwf rules) where
  relates := (ContextualDependentEta.frames levels).E
  equivalence := (ContextualDependentEta.frames levels).equivalence
  substitute := (ContextualDependentEta.frames levels).preserves

/-- The schema adapter recovers the existing typed frame, including its equality. -/
theorem typed_frames : (typedEquality levels).frames = ContextualDependentEta.frames levels := rfl

end TypedEquality

end SchemaComprehension
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
