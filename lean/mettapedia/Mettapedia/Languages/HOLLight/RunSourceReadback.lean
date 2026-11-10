import Mettapedia.Languages.HOLLight.RunModelCorrespondence

/-!
# Exact source roots for finite-run interpretation

Seven received facts connect the loaded list, path and pullback declarations
to finite labelled runs. Both the datatype and operation equations are checked
against the actual theorem cache, then interpreted in its constructed model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RunSourceReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution SourceProfileModels TypeFamilySemantics ReferenceBooleanSemantics ModelInterpretation

universe w

structure Operations where
  lists : ListSourceReadback.Operations
  state : Ty
  value : Ty
  path : Const
  pullback : Const

def Operations.signature (operations : Operations) : RunModelCorrespondence.Signature where
  lists := operations.lists.signature
  state := operations.state.toHOL
  value := operations.value.toHOL
  path := .const (.constant operations.path
    (.function (.function operations.state (.function operations.lists.element
        (.function operations.state Ty.bool)))
      (.function operations.lists.sequence (.function operations.state (.function operations.state Ty.bool))))
    (by simp only [Ty.toHOL_function, Ty.toHOL_bool, ListSourceReadback.Operations.signature]))
  pullback := .const (.constant operations.pullback
    (.function (.function operations.lists.element (.function operations.value operations.value))
      (.function operations.lists.sequence (.function operations.value operations.value)))
    (by simp only [Ty.toHOL_function, ListSourceReadback.Operations.signature]))

def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  return ⟨← ListSourceReadback.operations? symbols (.var (Name.global "E")),
    .var (Name.global "S"), .var (Name.global "V"),
    ← List.lookup "tc_path" symbols.constants, ← List.lookup "tc_pullback" symbols.constants⟩

structure CacheIndices where
  lists : ListSourceReadback.CacheIndices
  pathNil : Nat
  pathCons : Nat
  pullbackNil : Nat
  pullbackCons : Nat

structure Readings (operations : Operations) (state : Registered.State) where
  lists : ListSourceReadback.Readings operations.lists state
  pathNil : ExactFormulaReadback.ReadFact state operations.signature.pathNil
  pathCons : ExactFormulaReadback.ReadFact state operations.signature.pathCons
  pullbackNil : ExactFormulaReadback.ReadFact state operations.signature.pullbackNil
  pullbackCons : ExactFormulaReadback.ReadFact state operations.signature.pullbackCons

def read? (operations : Operations) (state : Registered.State) (indices : CacheIndices) :
    Option (Readings operations state) := do
  return ⟨← ListSourceReadback.read? operations.lists state indices.lists,
    ← ExactFormulaReadback.read? state indices.pathNil operations.signature.pathNil,
    ← ExactFormulaReadback.read? state indices.pathCons operations.signature.pathCons,
    ← ExactFormulaReadback.read? state indices.pullbackNil operations.signature.pullbackNil,
    ← ExactFormulaReadback.read? state indices.pullbackCons operations.signature.pullbackCons⟩

structure Correspondence (signature : RunModelCorrespondence.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  lists : ListSourceReadback.Correspondence signature.lists model
  path : ∀ step events source target,
    (signature.pathValue model step (lists.equivalence events) source target).down ↔
      RunModelCorrespondence.WordRun (fun s e t => (step s e t).down) events source target
  pullback : ∀ back events value,
    signature.backValue model back (lists.equivalence events) value = events.foldr back value

noncomputable def correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy
      (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (readings : Readings operations after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Correspondence operations.signature
      ((sourceReplayFrame commands after accepted).frame.model other assignment) := by
  let frame := (sourceReplayFrame commands after accepted).frame
  have valid {formula : HOL.ClosedFormula Symbol}
      (reading : ExactFormulaReadback.ReadFact after formula) :
      (frame.model other assignment).models formula := by
    apply frame.cached_models_of_translation other assignment reading.known reading.translated
    intro hypothesis member
    simp [reading.closed, translatedHypotheses] at member
  let full := frame.model_fullDomains other assignment
  let meanings := replay_meanings commands after accepted other assignment
  let lists := ListSourceReadback.correspondence operations.lists commands after accepted readings.lists
    other assignment
  exact ⟨lists,
    operations.signature.path_iff _ full meanings (valid readings.pathNil) (valid readings.pathCons) lists,
    operations.signature.pullback_eq_foldr _ full meanings
      (valid readings.pullbackNil) (valid readings.pullbackCons) lists⟩

theorem checked_correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy
      (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (indices : CacheIndices) (read : (read? operations after indices).isSome = true)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    Nonempty (Correspondence operations.signature
      ((sourceReplayFrame commands after accepted).frame.model other assignment)) :=
  ⟨correspondence operations commands after accepted ((read? operations after indices).get read)
    other assignment⟩

/-- The correspondence covers every source list value, not only a chosen set
of externally encoded words. -/
theorem path_decoded (signature : RunModelCorrespondence.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (agreement : Correspondence signature model) (step events source target) :
    (signature.pathValue model step events source target).down ↔
      RunModelCorrespondence.WordRun (fun s e t => (step s e t).down)
        (agreement.lists.equivalence.symm events) source target := by
  simpa only [Equiv.apply_symm_apply] using
    agreement.path step (agreement.lists.equivalence.symm events) source target

theorem pullback_decoded (signature : RunModelCorrespondence.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (agreement : Correspondence signature model) (back events value) :
    signature.backValue model back events value =
      (agreement.lists.equivalence.symm events).foldr back value := by
  simpa only [Equiv.apply_symm_apply] using
    agreement.pullback back (agreement.lists.equivalence.symm events) value

end Mettapedia.Languages.HOLLight.RunSourceReadback
