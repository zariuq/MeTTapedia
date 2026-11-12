import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLParallelAgreement

/-!
# Exact-definition mutations, aliases and empty valid occurrence fibres

A well-typed definition that drops the right store is rejected by readback.
Equation-list duplicates remain distinguishable as lists even though the
HOL membership observation erases them. Reusing an occurrence identity
aliases one cell. The inhabited raw carrier contributes no valid occurrence
when the represented occurrence type is empty.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLBodySyntax HOLModelsBody HOLParallelBodies

def droppedRightSyntax : HOLBodySyntax.Syntax :=
  lambdas [("left", storeType), ("right", storeType), ("x", termType), ("y", termType)]
    (apps (varTerm "left") [varTerm "x", varTerm "y"])

theorem dropped_right_is_well_typed : (checkClosed Store.operationType droppedRightSyntax).isSome = true := by
  decide +kernel

def droppedRightBody : HOL.ClosedTerm Symbol Store.operationType :=
  (checkClosed Store.operationType droppedRightSyntax).get dropped_right_is_well_typed

theorem dropped_right_definition_refused :
    ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 19
      (.eq (.const Store.symbol) droppedRightBody) = none := by decide +kernel

theorem wrong_definition_entry_refused :
    ExactFormulaReadback.read? HOLParallelDefinitions.received.received.registered 20 Store.definition = none := by
  decide +kernel

universe w uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem duplicate_equations_same_membership {a : Obj} (equation : Tm a × Tm a) :
    HOLFrameEncoding.store [equation, equation] = HOLFrameEncoding.store [equation] := by
  funext x y
  apply propext
  simp [HOLFrameEncoding.store]

theorem duplicate_equations_different_lists {a : Obj} (equation : Tm a × Tm a) :
    [equation, equation] ≠ [equation] := by
  intro same
  have lengths := congrArg List.length same
  cases lengths

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLParallelDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem one_shared_occurrence {O : Type uOcc} [DecidableEq O]
    (code : HOLOccurrenceCoding.Coding model O) (occurrence : O) :
    model.constDen Present.symbol (HOLOccurrenceCoding.finiteValue model code {occurrence})
      (HOLOccurrenceCoding.finiteValue model code {occurrence}) =
        HOLOccurrenceCoding.finiteValue model code {occurrence} := by
  funext raw
  rw [present_meaning model full equations]
  apply ULift.ext
  apply propext
  exact ⟨fun either => either.elim id id, Or.inl⟩

include full equations in
theorem empty_occurrence_profile (code : HOLOccurrenceCoding.Coding model PEmpty)
    (left right : Finset PEmpty) (raw : HOL.Ty.denote.{0,w+1} model.Carrier HOLOccurrenceCoding.occurrenceType) :
    ¬(model.constDen Present.symbol (HOLOccurrenceCoding.finiteValue model code left)
      (HOLOccurrenceCoding.finiteValue model code right) raw).down := by
  rw [present_meaning model full equations]
  change ¬(HOLOccurrenceCoding.finitePredicate left (code raw) ∨
    HOLOccurrenceCoding.finitePredicate right (code raw))
  cases found : code raw with
  | none => simp [HOLOccurrenceCoding.finitePredicate]
  | some impossible => exact nomatch impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelControls
