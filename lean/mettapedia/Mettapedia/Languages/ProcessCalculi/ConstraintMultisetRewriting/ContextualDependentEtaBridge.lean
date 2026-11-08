import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity

/-!
# From raw-conversion solutions to typed beta-eta solutions

The comparison preserves each telescope, term and substitution code. Its
certificates are reconstructed using the existing conservativity theorem.
That theorem requires constructor-form facts, root and head preservation,
and Church--Rosser for raw conversion. These are meaningful qualifications
of an admitted computation package, not assumptions that the desired map
already preserves equality.

Every raw-conversion solution of a qualified package becomes a typed
beta-eta solution. The same statement is not asserted for arbitrary root
rewriting. Nor does this forward map imply reflection of eta equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta.BetaBridge

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (church : ConversionCoherence.ChurchRosser S.R)

def context (Γ : FormationSensitiveContextual.Context S.R) : TypedContextual.Context S.R :=
  ⟨Γ.arity, Γ.raw,
    FormationSensitive.ContextFormation.toTyped (S := S) facts roots heads church Γ.formed⟩

def hom {Γ Δ : FormationSensitiveContextual.Context S.R} (σ : Δ ⟶ Γ) :
    context facts roots heads church Δ ⟶ context facts roots heads church Γ where
  substitution := σ.substitution
  typed index := FormationSensitive.Typing.toTyped (S := S) facts roots heads church
    (σ.typed index) (context facts roots heads church Δ).formed

def type {Γ : FormationSensitiveContextual.Context S.R} (A : FormationSensitiveContextual.TypeOver Γ) :
    TypedContextual.TypeOver (context facts roots heads church Γ) :=
  ⟨A.code, A.level, A.universeWitness,
    FormationSensitive.Typing.toTyped (S := S) facts roots heads church A.formed
      (context facts roots heads church Γ).formed⟩

def entry {Γ : FormationSensitiveContextual.Context S.R} (value : Interface.Dependent.Entry Γ) :
    TypedContextual.TotalTerm (context facts roots heads church Γ) :=
  ⟨type facts roots heads church value.type,
    ⟨value.term.code,
      FormationSensitive.Typing.toTyped (S := S) facts roots heads church value.term.typed
        (context facts roots heads church Γ).formed⟩⟩

theorem hom_id (Γ : FormationSensitiveContextual.Context S.R) :
    hom facts roots heads church (𝟙 Γ) = 𝟙 (context facts roots heads church Γ) :=
  TypedContextual.Hom.ext rfl

theorem hom_comp {Γ Δ Θ : FormationSensitiveContextual.Context S.R} (σ : Θ ⟶ Δ) (τ : Δ ⟶ Γ) :
    hom facts roots heads church (σ ≫ τ) =
      hom facts roots heads church σ ≫ hom facts roots heads church τ :=
  TypedContextual.Hom.ext rfl

theorem entry_reindex {Γ Δ : FormationSensitiveContextual.Context S.R}
    (value : Interface.Dependent.Entry Γ) (σ : Δ ⟶ Γ) :
    entry facts roots heads church (value.reindex σ) =
      (entry facts roots heads church value).reindex (hom facts roots heads church σ) := rfl

/-- Both annotation conversion and value conversion are promoted through
the qualified preservation/confluence theorem. -/
theorem preserves {Γ : FormationSensitiveContextual.Context S.R}
    {first second : Interface.Dependent.Entry Γ}
    (same : (Interface.Dependent.frames S.R).E first second) :
    (frames S.levels).E (entry facts roots heads church first) (entry facts roots heads church second) := by
  let left := entry facts roots heads church first
  let right := entry facts roots heads church second
  have annotations := Conv.toTypeEq (S := S) facts roots heads church
    (context facts roots heads church Γ).formed same.1
    left.1.formed left.1.universeWitness right.1.formed right.1.universeWitness
  refine ⟨annotations, ?_⟩
  exact Conv.toEqual (S := S) facts roots heads church
    (context facts roots heads church Γ).formed same.2 left.2.typed
    (Typed.convType right.2.typed annotations.symm)

def problem {Γ : FormationSensitiveContextual.Context S.R}
    (source : EquationStore (Interface.Dependent.Entry Γ)) :
    EquationStore (TypedContextual.TotalTerm (context facts roots heads church Γ)) :=
  source.map fun equation =>
    (entry facts roots heads church equation.1, entry facts roots heads church equation.2)

theorem models {Γ Δ : FormationSensitiveContextual.Context S.R} (σ : Δ ⟶ Γ)
    (source : EquationStore (Interface.Dependent.Entry Γ))
    (solved : (Interface.Dependent.frames S.R).Models σ source) :
    (frames S.levels).Models (hom facts roots heads church σ) (problem facts roots heads church source) := by
  intro equation member
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  have converted := preserves facts roots heads church (solved original selected)
  exact converted

/-- Every future raw-conversion witness is transported, not just a selected
closed witness or an endomorphic solution. -/
theorem solvable {Γ : FormationSensitiveContextual.Context S.R}
    (source : EquationStore (Interface.Dependent.Entry Γ))
    (solved : (Interface.Dependent.frames S.R).Solvable source) :
    (frames S.levels).Solvable (problem facts roots heads church source) := by
  obtain ⟨Δ, σ, models⟩ := solved
  exact ⟨context facts roots heads church Δ, hom facts roots heads church σ,
    BetaBridge.models facts roots heads church σ source models⟩

end ContextualDependentEta.BetaBridge
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
