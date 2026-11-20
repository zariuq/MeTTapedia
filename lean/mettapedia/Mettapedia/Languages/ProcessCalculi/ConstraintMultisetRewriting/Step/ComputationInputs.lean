import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Preservation

/-!
# Starting computation from an independently derived source typing

The type annotation is formed by the existing presupposition theorem. Only
that proof metadata uses choice of a universe; the stored term and displayed
type are the given source syntax. This supplies ordinary initial states for
checked compiler outputs as well as directly declared package functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem source_type_formed (Γ : Context S.R) {term type : Tm Head Γ.arity}
    (typing : Typed S.R Γ.raw term type) : IsType S.R Γ.raw type :=
  TypedEquality.Normalization.Derivable.presupposed S.levels typing Γ.formed

def inferredType (Γ : Context S.R) {term type : Tm Head Γ.arity}
    (typing : Typed S.R Γ.raw term type) : TypeOver Γ where
  code := type
  level := Classical.choose (source_type_formed Γ typing)
  universeWitness := (Classical.choose_spec (source_type_formed Γ typing)).1
  formed := (Classical.choose_spec (source_type_formed Γ typing)).2

def Configuration.ofTyped (Γ : Context S.R) {term type : Tm Head Γ.arity}
    (typing : Typed S.R Γ.raw term type) : Configuration (S := S) where
  state := ⟨Γ, [], {0}, fun _ => ⟨inferredType Γ typing, ⟨term, typing⟩⟩⟩
  active := 0
  present := Finset.mem_singleton_self _
  consistent := ⟨Γ, 𝟙 _, Frames.models_nil _⟩

theorem Configuration.ofTyped_code (Γ : Context S.R) {term type : Tm Head Γ.arity}
    (typing : Typed S.R Γ.raw term type) : (Configuration.ofTyped Γ typing).code = term := rfl

theorem Configuration.ofTyped_type (Γ : Context S.R) {term type : Tm Head Γ.arity}
    (typing : Typed S.R Γ.raw term type) :
    ((Configuration.ofTyped Γ typing).state.label 0).1.code = type := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Configuration.ofTyped
