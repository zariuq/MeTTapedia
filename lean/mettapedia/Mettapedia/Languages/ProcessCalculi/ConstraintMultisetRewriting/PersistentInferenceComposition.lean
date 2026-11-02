import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceApplication

/-!
# Physical inference execution composes through persistent premise positions

The second execution is an actual trace starting in the first one's physical
endpoint. Earlier outputs are selected through the computed structural
retraction; no rule replay or copying of theorem identities is required.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence payload system)
open InferenceSelectedFirings InferenceJudgmentBoards InferenceTraceClassifying
open InferencePathFunctor
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

noncomputable def Execution.arrow {before : Configuration Value Occurrence} {prior : Board before}
    {goals : List Pattern} (execution : Execution (definition := definition) before prior goals) :
    prior.context definition ⟶ execution.board.context definition :=
  toBoard execution.trace prior execution.board

noncomputable def Execution.initialPositions {before : Configuration Value Occurrence} {prior : Board before}
    {goals : List Pattern} (execution : Execution (definition := definition) before prior goals) :
    ContextMap execution.board.judgments prior.judgments :=
  (execution.board.reorder (execution.trace.project prior).1).comp
    (retraction execution.trace prior)

private theorem paste_retractions {C : Type*} [Category* C] {a b c : C}
    (first : a ⟶ b) (second : b ⟶ c) (backFirst : b ⟶ a) (backSecond : c ⟶ b)
    (left : first ≫ backFirst = 𝟙 a) (right : second ≫ backSecond = 𝟙 b) :
    (first ≫ second) ≫ (backSecond ≫ backFirst) = 𝟙 a := by
  rw [Category.assoc, ← Category.assoc second, right, Category.id_comp, left]

theorem Execution.preserves_initial {before : Configuration Value Occurrence} {prior : Board before}
    {goals : List Pattern} (execution : Execution (definition := definition) before prior goals) :
    execution.arrow ≫ execution.initialPositions.interpret definition = 𝟙 (prior.context definition) := by
  rw [Execution.initialPositions, ContextMap.interpret_comp]
  exact paste_retractions (execution.trace.project prior).2
    (changeBoard (execution.trace.project prior).1 execution.board)
    ((retraction execution.trace prior).interpret definition)
    (changeBoard execution.board (execution.trace.project prior).1)
    (trace_keeps_positions execution.trace prior)
    ((changeBoard_comp _ _ _).trans (changeBoard_self _))

def Execution.follow {before : Configuration Value Occurrence} {prior : Board before}
    {firstGoals secondGoals : List Pattern}
    (first : Execution (definition := definition) before prior firstGoals)
    (second : Execution (definition := definition) first.after first.board secondGoals) :
    Execution (definition := definition) before prior secondGoals :=
  ⟨second.after, first.actors ++ second.actors, first.trace.append second.trace,
    second.board, second.outputs⟩

theorem Execution.follow_arrow {before : Configuration Value Occurrence} {prior : Board before}
    {firstGoals secondGoals : List Pattern}
    (first : Execution (definition := definition) before prior firstGoals)
    (second : Execution (definition := definition) first.after first.board secondGoals) :
    (first.follow second).arrow = first.arrow ≫ second.arrow :=
  toBoard_append first.trace second.trace prior first.board second.board

theorem Execution.follow_observe {before : Configuration Value Occurrence} {prior : Board before}
    {firstGoals secondGoals : List Pattern}
    (first : Execution (definition := definition) before prior firstGoals)
    (second : Execution (definition := definition) first.after first.board secondGoals) :
    (first.follow second).observe = first.arrow ≫ second.observe := by
  change (first.follow second).arrow ≫ second.outputs.interpret definition = _
  rw [Execution.follow_arrow]
  exact Category.assoc _ _ _

noncomputable def Execution.join {before : Configuration Value Occurrence} {prior : Board before}
    {firstGoals secondGoals : List Pattern}
    (first : Execution (definition := definition) before prior firstGoals)
    (second : Execution (definition := definition) first.after first.board secondGoals) :
    Execution (definition := definition) before prior (firstGoals ++ secondGoals) :=
  ⟨second.after, first.actors ++ second.actors, first.trace.append second.trace,
    second.board, ContextMap.pair (second.initialPositions.comp first.outputs) second.outputs⟩

private theorem paste_outputs {a b c x y : ClassifyingContext definition}
    (first : a ⟶ b) (second : b ⟶ c) (back : c ⟶ b) (left : b ⟶ x) (right : c ⟶ y)
    (kept : second ≫ back = 𝟙 b) :
    (first ≫ second) ≫ ClassifyingContext.pair (back ≫ left) right =
      ClassifyingContext.pair (first ≫ left) (first ≫ (second ≫ right)) := by
  rw [ClassifyingContext.comp_pair]
  congr 1
  · rw [Category.assoc, ← Category.assoc second, kept, Category.id_comp]
  · exact Category.assoc _ _ _

theorem Execution.join_observe {before : Configuration Value Occurrence} {prior : Board before}
    {firstGoals secondGoals : List Pattern}
    (first : Execution (definition := definition) before prior firstGoals)
    (second : Execution (definition := definition) first.after first.board secondGoals) :
    (first.join second).observe = first.observe.append (first.arrow ≫ second.observe) := by
  change toBoard (first.trace.append second.trace) prior second.board ≫
    (ContextMap.pair (second.initialPositions.comp first.outputs) second.outputs).interpret definition = _
  rw [toBoard_append first.trace second.trace prior first.board second.board,
    ContextMap.interpret_pair, ContextMap.interpret_comp]
  exact paste_outputs first.arrow second.arrow (second.initialPositions.interpret definition)
    (first.outputs.interpret definition) (second.outputs.interpret definition) second.preserves_initial

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
