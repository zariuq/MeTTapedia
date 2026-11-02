import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceExtensionReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceClassifying
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadOnlyContextNaturality

/-!
# Whole selected traces are conjugate under physical board reindexing

Changing the initial enumeration of one protected physical store changes
only premise addresses. The terminal reindexing is the actual identity of
physical occurrences in the two projected final boards, not an arbitrary
comparison arrow supplied as an assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturality

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value)
open InferenceRequestExecution (Occurrence)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open InferenceTraceClassifying
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

theorem kernel_terminal_reindexing
    {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (first second : Board before) :
    ((origin.board first).reorder (origin.board second)).interpret definition =
      eqToHom (origin.board_context first) ≫
        ReadOnlyContextExtension.carry ((first.reorder second).interpret definition)
          ⟨[origin.conclusion]⟩ ≫ eqToHom (origin.board_context second).symm := by
  have same := congrArg
    (fun mapping : ContextMap (origin.board first).judgments (origin.board second).judgments =>
      mapping.interpret definition) (origin.extendedMap_is_reorder first second)
  have carried : (origin.extendedMap first second).interpret definition =
      eqToHom (origin.board_context first) ≫
        ReadOnlyContextExtension.carry ((first.reorder second).interpret definition)
          ⟨[origin.conclusion]⟩ ≫ eqToHom (origin.board_context second).symm := by
    unfold InferenceSelectedFirings.SelectedFiring.KernelOrigin.extendedMap
    rw [ContextMap.interpret_transport, ContextMap.interpret_extend]
    rfl
  exact same.symm.trans carried

theorem kernel_conjugacy {before after : Configuration Value Occurrence}
    {firing : SelectedFiring definition true before after} (origin : firing.KernelOrigin)
    (first second : Board before) :
    (first.reorder second).interpret definition ≫ origin.arrow second =
      origin.arrow first ≫ ((origin.board first).reorder (origin.board second)).interpret definition := by
  have untransported := ReadOnlyContextExtension.readStep_naturality
    ((first.reorder second).interpret definition) (origin.picked first) (origin.picked second)
    origin.generator (origin.picked_reorder first second)
  have transported := ReadOnlyContextExtension.transported_square
    (origin.board_context first) (origin.board_context second)
    ((first.reorder second).interpret definition)
    (ReadOnlyContextExtension.readStep (origin.picked first) origin.generator)
    (ReadOnlyContextExtension.readStep (origin.picked second) origin.generator)
    (ReadOnlyContextExtension.carry ((first.reorder second).interpret definition)
      ⟨[origin.conclusion]⟩) untransported
  exact transported.trans (congrArg (fun terminal => origin.arrow first ≫ terminal)
    (kernel_terminal_reindexing origin first second).symm)

theorem firing_conjugacy {before after : Configuration Value Occurrence} {actor : Bool}
    (firing : SelectedFiring definition actor before after) (first second : Board before) :
    (first.reorder second).interpret definition ≫ (projectFiring firing second).2 =
      (projectFiring firing first).2 ≫
        ((projectFiring firing first).1.reorder (projectFiring firing second).1).interpret definition := by
  cases actor with
  | true =>
      exact kernel_conjugacy (Classical.choice firing.kernel_origin) first second
  | false =>
      let origin := Classical.choice firing.client_origin
      have same : (origin.board first).reorder (origin.board second) = first.reorder second := by
        apply ContextMap.ext
        funext index
        rfl
      change (first.reorder second).interpret definition ≫ 𝟙 _ =
        𝟙 _ ≫ ((origin.board first).reorder (origin.board second)).interpret definition
      rw [Category.comp_id, Category.id_comp]
      exact congrArg (fun mapping => mapping.interpret definition) same.symm

/-- Initial and terminal board permutations form a commuting square for
the whole actual selected run, with every source proof node retained. -/
theorem trace_conjugacy {before after : Configuration Value Occurrence} {actors : List Bool}
    (trace : SelectedRun definition before actors after) (first second : Board before) :
    (first.reorder second).interpret definition ≫ (trace.project second).2 =
      (trace.project first).2 ≫ ((trace.project first).1.reorder (trace.project second).1).interpret definition := by
  induction trace with
  | nil =>
      change (first.reorder second).interpret definition ≫ 𝟙 _ =
        𝟙 _ ≫ (first.reorder second).interpret definition
      rw [Category.comp_id, Category.id_comp]
  | cons firing rest earlier =>
      let headFirst := projectFiring firing first
      let headSecond := projectFiring firing second
      let tailFirst := rest.project headFirst.1
      let tailSecond := rest.project headSecond.1
      have head := firing_conjugacy firing first second
      have tail := earlier headFirst.1 headSecond.1
      change (first.reorder second).interpret definition ≫ (headSecond.2 ≫ tailSecond.2) =
        (headFirst.2 ≫ tailFirst.2) ≫ (tailFirst.1.reorder tailSecond.1).interpret definition
      exact ReadOnlyContextExtension.paste_squares
        ((first.reorder second).interpret definition)
        ((headFirst.1.reorder headSecond.1).interpret definition)
        ((tailFirst.1.reorder tailSecond.1).interpret definition)
        headFirst.2 headSecond.2 tailFirst.2 tailSecond.2 head tail

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceTraceNaturality
