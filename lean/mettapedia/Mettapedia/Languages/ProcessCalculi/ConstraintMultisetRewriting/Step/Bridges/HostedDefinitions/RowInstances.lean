import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RowCompiler

/-!
# Schema substitution and the generated native-source templates

The left-side compiler commutes with actual native simultaneous substitution.
Only unmentioned slots receive fixed padding; right-side coverage makes that
padding irrelevant beneath every native binder and type former.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
namespace RowInstances

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open RuleBuilder

/-- The continuation is outside the native term's substitution slots. -/
def bindingValues {slots ambient : Nat} (substitution : Sub Tower.Head slots ambient) (continuation : MClosed) :
    Fin (slots + 1) → MClosed := Fin.lastCases continuation (fun index => encodeTm (substitution index))

def padded {slots ambient : Nat} (left : Tower.Tm slots) (substitution : Sub Tower.Head slots ambient) :
    Sub Tower.Head slots ambient := fun index =>
  if 0 < AlgebraicSchema.variableMultiplicity index left then substitution index else .const .anonymous

theorem padded_right {slots ambient : Nat} (left right : Tower.Tm slots)
    (substitution : Sub Tower.Head slots ambient)
    (covered : NativeTypesOnTheStep.Computing.DeclarationCheck.coveredB left right = true) :
    subst (padded left substitution) right = subst substitution right := by
  apply ConstructorSystem.subst_congr_occurring right
  intro index occurs
  have inLeft := NativeTypesOnTheStep.Computing.DeclarationCheck.coveredB_sound covered index occurs
  simp [padded, inLeft]

theorem materialize_pattern {slots ambient holes : Nat} (term : Tower.Tm slots)
    (substitution : Sub Tower.Head slots ambient) (images : Fin slots → Template holes)
    (environment : Fin holes → MClosed)
    (agrees : ∀ index, materialize environment (images index) = encodeTm (substitution index))
    {result : Template holes} (compiled : RowCompiler.pattern images term = some result) :
    materialize environment result = encodeTm (subst substitution term) := by
  induction term generalizing ambient holes with
  | var index =>
      cases compiled
      exact agrees index
  | const name => cases compiled; simp [subst]
  | head level => cases compiled; simp [subst]
  | app function argument ihf iha =>
      obtain ⟨f, first, rest⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨a, second, last⟩ := Option.bind_eq_some_iff.mp rest
      cases last
      simp only [materialize_node, List.map_cons, List.map_nil, subst, encodeTm_app]
      rw [ihf substitution images environment agrees first, iha substitution images environment agrees second]
  | refl term ih =>
      obtain ⟨value, first, last⟩ := Option.bind_eq_some_iff.mp compiled
      cases last
      simp only [materialize_node, List.map_cons, List.map_nil, subst, encodeTm_refl]
      rw [ih substitution images environment agrees first]
  | _ => cases compiled

theorem literal_pattern {slots ambient : Nat} (term : Tower.Tm slots)
    (substitution : Sub Tower.Head slots ambient) (continuation : MClosed)
    {result : Template (slots + 1)}
    (compiled : RowCompiler.pattern (fun index => slot index.castSucc) term = some result) :
    materialize (bindingValues substitution continuation) result = encodeTm (subst substitution term) :=
  materialize_pattern term substitution _ _ (fun index => by simp [bindingValues]) compiled

theorem materialize_list {holes : Nat} (environment : Fin holes → MClosed) (terms : List (Template holes)) :
    materialize environment (RowCompiler.listTemplate terms) = listC (terms.map (materialize environment)) := by
  induction terms with
  | nil => simp [RowCompiler.listTemplate, listC]
  | cons first rest ih => simp [RowCompiler.listTemplate, listC, ih]

theorem materialize_environment {slots ambient : Nat} (left : Tower.Tm slots)
    (substitution : Sub Tower.Head slots ambient) (continuation : MClosed) :
    materialize (bindingValues substitution continuation) (RowCompiler.listTemplate (RowCompiler.environment left)) =
      environmentC (DataEmbedding.rawEnvironment (padded left substitution)) := by
  rw [materialize_list]
  unfold environmentC
  apply congrArg listC
  apply List.ext_getElem
  · simp [RowCompiler.environment, DataEmbedding.rawEnvironment]
  · intro index smallLeft smallRight
    have bound : index < slots := by simpa [DataEmbedding.rawEnvironment] using smallRight
    simp [RowCompiler.environment, DataEmbedding.rawEnvironment, padded]
    split <;> simp_all [bindingValues]
    change Fin.lastCases continuation (fun index => encodeTm (substitution index))
      (Fin.castSucc (⟨index, bound⟩ : Fin slots)) = encodeTm (substitution ⟨index, bound⟩)
    exact Fin.lastCases_castSucc _

/-- An actual instance of an authored row enters the real environment helper
with its complete body. This theorem has no desired reduction as a premise. -/
theorem compiled_row_instance (entry : Σ slots : Nat, Tower.Tm slots × Tower.Tm slots)
    {rule : ProgramBinders.Equation MSig [] ()} (compiled : RowCompiler.row entry = some rule)
    {ambient : Nat} (substitution : Sub Tower.Head entry.1 ambient) (continuation : MClosed) :
    ProgramBinders.Answers rule
      (rootC (encodeTm (subst substitution entry.2.1)) continuation)
      (substituteEnvironmentC (environmentC (DataEmbedding.rawEnvironment (padded entry.2.1 substitution)))
        (encodeTm entry.2.2) continuation) := by
  unfold RowCompiler.row at compiled
  split at compiled
  · cases found : RowCompiler.pattern (fun index => slot index.castSucc) entry.2.1 with
    | none => rw [found] at compiled; cases compiled
    | some lhs =>
      rw [found] at compiled
      cases compiled
      have answered := RuleBuilder.instantiated_answer
        (RowCompiler.active "hd-root" [lhs, slot (Fin.last entry.1)])
        (RowCompiler.active "hd-subst-env" [RowCompiler.listTemplate (RowCompiler.environment entry.2.1),
          literal (encodeTm entry.2.2), slot (Fin.last entry.1)])
        (bindingValues substitution continuation)
      simpa [RowCompiler.active, activeC, rootC, substituteEnvironmentC, bindingValues,
        literal_pattern entry.2.1 substitution continuation found,
        materialize_environment entry.2.1 substitution continuation] using answered
  · cases compiled

end RowInstances
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
