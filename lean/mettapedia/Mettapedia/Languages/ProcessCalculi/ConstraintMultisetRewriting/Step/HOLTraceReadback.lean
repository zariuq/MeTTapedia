import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTraceSemantics

/-!
# Exact source readback for the generated trace operation

The operation carries its registered constant identity. The complete source
meaning formula is checked against an accepted theorem-cache entry. Its
interpretation is derived in that accepted history's constructed model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution SourceProfileModels TypeFamilySemantics ModelInterpretation

universe w

structure Operations where
  trace : Const

def runType : Ty := .var (Name.global "R")

def Operations.signatureAt (operations : Operations) (run : Ty) : HOLTraceSemantics.Signature :=
  { run := run.toHOL
    trace := .const (.constant operations.trace
      (Ty.fromHOL ((run.toHOL.arr (run.toHOL.arr .prop)).arr
        (run.toHOL.arr (run.toHOL.arr .prop)))) (Ty.toHOL_fromHOL _)) }

def Operations.signature (operations : Operations) : HOLTraceSemantics.Signature :=
  operations.signatureAt runType

def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  return ⟨← List.lookup "tc_generated_trace" symbols.constants⟩

abbrev Reading (operations : Operations) (state : Registered.State) :=
  ExactFormulaReadback.ReadFact state operations.signature.meaningFormula

def read? (operations : Operations) (state : Registered.State) (index : Nat) : Option (Reading operations state) :=
  ExactFormulaReadback.read? state index operations.signature.meaningFormula

theorem meaning (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy
      (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (reading : Reading operations after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ((sourceReplayFrame commands after accepted).frame.model other assignment).models
      operations.signature.meaningFormula := by
  apply (sourceReplayFrame commands after accepted).frame.cached_models_of_translation
    other assignment reading.known reading.translated
  intro hypothesis member
  simp [reading.closed, translatedHypotheses] at member

theorem correspondence (operations : Operations)
    (commands : List Registered.Command) (after : Registered.State)
    (accepted : Registered.replayFrom policy
      (Registered.empty SourceProfile.primitiveContext) commands = some after)
    (reading : Reading operations after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (generators left right) :
    (operations.signature.traceValue
      ((sourceReplayFrame commands after accepted).frame.model other assignment) generators left right).down ↔
      Relation.EqvGen (fun one two => (generators one two).down) left right :=
  operations.signature.trace_iff_eqvGen _
    ((sourceReplayFrame commands after accepted).frame.model_fullDomains other assignment)
    (ReferenceBooleanSemantics.replay_meanings commands after accepted other assignment)
    (meaning operations commands after accepted reading other assignment) generators left right

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceReadback
