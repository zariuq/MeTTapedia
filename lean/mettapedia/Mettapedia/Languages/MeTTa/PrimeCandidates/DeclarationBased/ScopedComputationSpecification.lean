import Mettapedia.TypeTheory.DesignStudy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ScopedComputationQualification

/-!
# Shared implementation requirements for scoped computations

An implementation contains only an operation handler and independently
authored primitive world lists, at the same native term scope. Realization
and native result preservation are separate semantic requirements on that
data. Their conjunction qualifies every independently admitted source
computation, including under refined substitution into the target scope.

The native state/reflexivity example inhabits this specification. A changed
handler realizes its changed world semantics but violates the declared
dependent result family. Thus realization alone does not qualify admission.

This is a shared admission/execution study for the existing finite scoped
sequencing fragment. It neither selects a language nor connects the separate
native J, mathematical-host, or demand-machine rule packages by implication.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation
namespace ImplementationStudy

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.DesignStudy

universe uState uIntent

/-- Raw implementations share operation names, native terms and world state.
No formation, realization or preservation proof is stored in this data. -/
structure Implementation (Head Operation : Type) (State : Type uState)
    (Intent : Type uIntent) (n : Nat) where
  handler : Operation → Tm Head n → Program State (Tm Head n) Intent
  primitive : Operation → Tm Head n → State → BranchTrace →
    List (WorldResult State (Tm Head n) Intent)

variable {Head Operation : Type} {State : Type uState} {Intent : Type uIntent}
  {n m : Nat}

/-- Primitive execution preserves all ordered world information, not only
answer support. The right side is supplied independently of the handler. -/
def Realizes (implementation : Implementation Head Operation State Intent m) : Prop :=
  ∀ operation argument state branch,
    runWorldsAt (implementation.handler operation argument) state branch =
      implementation.primitive operation argument state branch

/-- Each primitive respects the separately authored dependent signature in
every target context, whenever that operation and its argument are admitted. -/
def Preserves (rules : Rules Head) (signature : OperationSignature Head Operation)
    (implementation : Implementation Head Operation State Intent m) : Prop :=
  ∀ context, PrimitivePreserves rules signature context implementation.primitive

inductive Requirement where
  | exactWorlds
  | nativeResults
  deriving DecidableEq, Repr

/-- Both requirements concern exactly the implementation at this index. -/
def specification (rules : Rules Head) (signature : OperationSignature Head Operation) :
    Specification (Implementation Head Operation State Intent m) Requirement where
  holds
    | .exactWorlds => Realizes
    | .nativeResults => Preserves rules signature
  required := [.exactWorlds, .nativeResults]

theorem satisfies_iff (rules : Rules Head) (signature : OperationSignature Head Operation)
    (implementation : Implementation Head Operation State Intent m) :
    (specification rules signature).Satisfies implementation ↔
      Realizes implementation ∧ Preserves rules signature implementation := by
  constructor
  · intro qualified
    exact ⟨qualified .exactWorlds (by simp [specification]),
      qualified .nativeResults (by simp [specification])⟩
  · rintro ⟨realizes, preserves⟩ requirement _
    cases requirement with
    | exactWorlds => exact realizes
    | nativeResults => exact preserves

/-- The two requirements establish native admission for every source program
and every refined environment into the implementation's target scope. -/
theorem qualified_interpretation
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : Implementation Head Operation State Intent m)
    (qualified : (specification rules signature).Satisfies implementation)
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {code : Code Head Operation n} {resultType : Tm Head n}
    (judgment : Judgment rules signature sourceContext code resultType)
    {environment : Sub Head n m}
    (target : FormationSensitive.ContextFormation rules targetContext)
    (typed : FormationSensitive.CtxMor rules sourceContext targetContext environment)
    {state : State} {branch : BranchTrace}
    {output : WorldResult State (Tm Head m) Intent}
    (returned : output ∈
      runWorldsAt (Code.interpret implementation.handler environment code) state branch) :
    FormationSensitive.Judgment rules targetContext output.answer
      (subst environment resultType) := by
  obtain ⟨realizes, preserves⟩ := (satisfies_iff rules signature implementation).mp qualified
  exact judgment.interpret_preserve implementation.handler implementation.primitive
    realizes target typed (preserves targetContext) returned

/-- Exact realization propagates through every source constructor. This
retains branch identities, multiplicity, state and intent order. -/
theorem qualified_worlds
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : Implementation Head Operation State Intent m)
    (qualified : (specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (Code.interpret implementation.handler environment code) state branch =
      Code.worlds implementation.primitive environment code state branch :=
  Code.interpret_worlds implementation.handler implementation.primitive
    ((satisfies_iff rules signature implementation).mp qualified).1
    environment code state branch

/-- Here realization also supplies nonempty source worlds, because the
finite handler language has no abort constructor. This is not a theorem
about termination of native payload normalization or unrestricted search. -/
theorem qualified_worlds_nonempty
    {rules : Rules Head} {signature : OperationSignature Head Operation}
    (implementation : Implementation Head Operation State Intent m)
    (qualified : (specification rules signature).Satisfies implementation)
    (environment : Sub Head n m) (code : Code Head Operation n)
    (state : State) (branch : BranchTrace) :
    Code.worlds implementation.primitive environment code state branch ≠ [] :=
  Code.worlds_ne_nil_of_realization implementation.handler implementation.primitive
    ((satisfies_iff rules signature implementation).mp qualified).1
    environment code state branch

namespace Native

open NativeExamples

/-- The two independently authored native components, at any term scope. -/
def implementation (n : Nat) : Implementation Tower.Head NativeExamples.Operation Bool Nat n where
  handler := NativeExamples.handler
  primitive := NativeExamples.primitiveWorlds

def evidence (n : Nat) :
    (specification Tower.rules signature).Evidence (implementation n) where
  supported := [.exactWorlds, .nativeResults]
  verifies := by
    intro requirement _
    cases requirement with
    | exactWorlds => exact handler_realizes
    | nativeResults => intro context; exact primitive_preserves

theorem qualified (n : Nat) :
    (specification Tower.rules signature).Satisfies (implementation n) :=
  (evidence n).complete (by simp [Specification.Evidence.remaining, evidence, specification])

/-- There is an actual inhabitant at every target scope, not just a
conditional compatibility theorem over an uninhabited candidate class. -/
theorem inhabited (n : Nat) :
    ∃ candidate : Implementation Tower.Head NativeExamples.Operation Bool Nat n,
      (specification Tower.rules signature).Satisfies candidate :=
  ⟨implementation n, qualified n⟩

/-- Alter both execution components together; neither is defined from the
other. Their agreement still cannot validate the dependent declaration. -/
def misindexed : Implementation Tower.Head NativeExamples.Operation Bool Nat 2 where
  handler := misindexedHandler
  primitive := misindexedWorlds

theorem misindexed_realizes : Realizes misindexed :=
  misindexedHandler_realizes

theorem misindexed_not_preserves : ¬ Preserves Tower.rules signature misindexed := by
  intro preserves
  exact misindexedWorlds_not_qualified (preserves context)

theorem misindexed_not_qualified :
    ¬ (specification Tower.rules signature).Satisfies misindexed := by
  intro qualified
  exact misindexed_not_preserves ((satisfies_iff _ _ _).mp qualified).2

/-- Realization and logical admission are demonstrably independent checks
even when the implementation components share every data carrier. -/
theorem realization_does_not_imply_admission :
    ¬ ∀ candidate : Implementation Tower.Head NativeExamples.Operation Bool Nat 2,
      Realizes candidate → Preserves Tower.rules signature candidate := by
  intro implication
  exact misindexed_not_preserves (implication misindexed misindexed_realizes)

/-- A sound declared world semantics cannot certify a different handler. -/
def unrealized : Implementation Tower.Head NativeExamples.Operation Bool Nat 2 where
  handler := misindexedHandler
  primitive := primitiveWorlds

theorem unrealized_preserves : Preserves Tower.rules signature unrealized := by
  intro targetContext
  exact primitive_preserves

theorem unrealized_not_realizes : ¬ Realizes unrealized := by
  intro realizes
  have sameAnswers := congrArg
    (fun worlds : List (WorldResult Bool (Tower.Tm 2) Nat) => worlds.map WorldResult.answer)
    (realizes .reflexivity newer false [])
  have wrong : ([.refl older] : List (Tower.Tm 2)) ≠ [.refl newer] := by decide
  exact wrong sameAnswers

theorem admission_does_not_imply_realization :
    ¬ ∀ candidate : Implementation Tower.Head NativeExamples.Operation Bool Nat 2,
      Preserves Tower.rules signature candidate → Realizes candidate := by
  intro implication
  exact unrealized_not_realizes (implication unrealized unrealized_preserves)

/-- Partial evidence retains the unsupported obligation as data. It cannot
supply a qualification proof for the altered native implementation. -/
def misindexedEvidence :
    (specification Tower.rules signature).Evidence misindexed where
  supported := [.exactWorlds]
  verifies := by
    intro requirement member
    have same : requirement = .exactWorlds := by simpa using member
    subst requirement
    exact misindexed_realizes

theorem misindexed_remaining : misindexedEvidence.remaining = [.nativeResults] := by
  simp [Specification.Evidence.remaining, specification, misindexedEvidence]

end Native

#print axioms qualified_interpretation
#print axioms qualified_worlds
#print axioms qualified_worlds_nonempty
#print axioms Native.qualified
#print axioms Native.inhabited
#print axioms Native.misindexed_not_qualified
#print axioms Native.realization_does_not_imply_admission
#print axioms Native.admission_does_not_imply_realization
#print axioms Native.misindexed_remaining

end ImplementationStudy
end ScopedComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
