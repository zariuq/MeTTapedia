import Mettapedia.Languages.HOLLight.ListModelCategoricity
import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.ExportCodec

/-!
# Received list laws and their model correspondence

The reader checks the exact source formulas and declaration identities. Its
evidence is used in the model constructed from the accepted source history;
constructor laws are not supplied as assumptions about an arbitrary carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ListSourceReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution SourceProfileModels TypeFamilySemantics ReferenceBooleanSemantics ModelInterpretation

universe w

structure Operations where
  element : Ty
  sequence : Ty
  nil : Const
  cons : Const

def Operations.signature (operations : Operations) : ListModelCategoricity.Signature where
  element := operations.element.toHOL
  sequence := operations.sequence.toHOL
  nil := .const (.constant operations.nil operations.sequence rfl)
  cons := .const (.constant operations.cons
    (.function operations.element (.function operations.sequence operations.sequence))
    (by simp only [Ty.toHOL_function]))

def operations? (symbols : ExportCodec.Symbols) (element : Ty) : Option Operations := do
  let operator ← List.lookup "list" symbols.operators
  return ⟨element, .op operator [element],
    ← List.lookup "NIL" symbols.constants, ← List.lookup "CONS" symbols.constants⟩

structure CacheIndices where
  separation : Nat
  injectivity : Nat
  induction : Nat

structure Readings (operations : Operations) (state : Registered.State) where
  separation : ExactFormulaReadback.ReadFact state operations.signature.separation
  injectivity : ExactFormulaReadback.ReadFact state operations.signature.injectivity
  induction : ExactFormulaReadback.ReadFact state operations.signature.induction

def read? (operations : Operations) (state : Registered.State) (indices : CacheIndices) :
    Option (Readings operations state) := do
  return ⟨← ExactFormulaReadback.read? state indices.separation operations.signature.separation,
    ← ExactFormulaReadback.read? state indices.injectivity operations.signature.injectivity,
    ← ExactFormulaReadback.read? state indices.induction operations.signature.induction⟩

structure Correspondence (signature : ListModelCategoricity.Signature)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) where
  equivalence : List (signature.Element model) ≃ signature.Carrier model
  nil : equivalence [] = signature.empty model
  cons : ∀ head tail, equivalence (head :: tail) = signature.prepend model head (equivalence tail)

/-- The full list carrier is obtained from actual checked formulas, including
the induction law which rules out additional non-finite elements. -/
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
  exact ⟨operations.signature.listEquivalence _ full meanings
      (valid readings.separation) (valid readings.injectivity) (valid readings.induction),
    operations.signature.listEquivalence_nil _ full meanings
      (valid readings.separation) (valid readings.injectivity) (valid readings.induction),
    operations.signature.listEquivalence_cons _ full meanings
      (valid readings.separation) (valid readings.injectivity) (valid readings.induction)⟩

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

end Mettapedia.Languages.HOLLight.ListSourceReadback
