import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceObservation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Well-scoped proof contexts have canonical physical seed boards

Position i is stored at occurrence identity i even when several positions
carry equal judgments. The equation store starts empty. These are concrete
finite occurrence stores used by the execution category, not proof vectors
standing in for runtime state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (judgment action)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location)
open InferenceJudgmentBoards
open _root_.CategoryTheory

structure PersistentContext (definition : ValidatedCalculusLanguageDef) where
  judgments : List Pattern
  supported : ∀ pattern ∈ judgments, pattern.isWellScoped = true

namespace PersistentContext

variable {definition : ValidatedCalculusLanguageDef} (context : PersistentContext definition)

def row (position : Fin context.judgments.length) : Occurrence :=
  (position.val, (.judgments, judgment (context.judgments.get position)))

theorem row_injective : Function.Injective context.row := by
  intro first second same
  exact Fin.ext (congrArg Prod.fst same)

noncomputable def state : Configuration Value Occurrence := by
  classical
  exact ⟨[], (List.ofFn context.row).toFinset⟩

noncomputable def board : Board context.state := by
  classical
  refine
    { entries := List.ofFn fun index => (context.row index, context.judgments.get index)
      distinct := ?_
      occupied := ?_
      readback := ?_
      supported := ?_ }
  · rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr context.row_injective
  · intro occurrence
    simp only [List.map_ofFn, Function.comp_def, state, List.mem_toFinset]
    constructor
    · intro member
      refine ⟨member, ?_⟩
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      rfl
    · exact And.left
  · intro entry member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    rfl
  · intro entry member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact context.supported _ (List.get_mem _ _)

theorem board_judgments : context.board.judgments = context.judgments := by
  change (List.ofFn fun index => (context.row index, context.judgments.get index)).map Prod.snd = _
  rw [List.map_ofFn]
  exact List.ofFn_get context.judgments

theorem consistent : locatedAction.Consistent context.state.equations :=
  ⟨action.identity, locatedAction.models_nil _⟩

theorem occurrence_positions_are_distinct (first second : Fin context.judgments.length)
    (different : first ≠ second) : context.row first ≠ context.row second :=
  fun same => different (context.row_injective same)

end PersistentContext

def wellScopedContexts (definition : ValidatedCalculusLanguageDef) :
    ObjectProperty (ClassifyingContext definition) :=
  fun context => ∀ pattern ∈ context.judgments, pattern.isWellScoped = true

abbrev ScopedProofContexts (definition : ValidatedCalculusLanguageDef) :=
  (wellScopedContexts definition).FullSubcategory

noncomputable def PersistentContext.proofContext {definition : ValidatedCalculusLanguageDef}
    (context : PersistentContext definition) : ScopedProofContexts definition :=
  ⟨context.board.context definition, by
    change ∀ pattern ∈ context.board.judgments, pattern.isWellScoped = true
    rw [context.board_judgments]
    exact context.supported⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
