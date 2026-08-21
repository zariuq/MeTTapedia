import Mettapedia.GSLT.Core.LooseRelationEquipment

/-!
# Judgment-indexed proof-relevant computation

A computation in a dependent theory should retain the judgment fibre in
which it runs.  Starting instead from an untyped endpoint relation forgets
the typing invariant and makes preservation an attempted reconstruction of
discarded information.

`JudgmentalComputation` is the informative object:

* `Index` identifies a judgment fibre, such as a context and result type;
* `State index` contains the terms or configurations in that fibre;
* `Step source target` is proof-relevant execution evidence inside one fibre.

Sequential composition retains its intermediate state and both witnesses.
Forgetting states to raw syntax produces an existential evidence family, and
Boolean/propositional reachability is a further quotient.  The final section
connects an ordinary extrinsic typing judgment and a raw step relation to this
form: a preservation lift is precisely the missing datum needed to turn a raw
step from a typed source into a judgment-indexed step.
-/

namespace Mettapedia.TypeTheory

universe uIndex uState uStep uRaw uTerm uType uTyping uReduction

/-- A proof-relevant transition system fibred over judgment indices.  A step
cannot change its index because source and target inhabit the same fibre. -/
structure JudgmentalComputation (Index : Type uIndex) where
  State : Index → Type uState
  Step : {index : Index} → State index → State index → Type uStep

namespace JudgmentalComputation

variable {Index : Type uIndex}
variable (computation : JudgmentalComputation.{uIndex, uState, uStep} Index)

/-- Identity computation evidence. -/
inductive Identity {index : Index} :
    computation.State index → computation.State index → Type uState where
  | refl (state : computation.State index) : Identity state state

/-- Sequential composition retains the intermediate state and both step
witnesses.  It is horizontal composition in each judgment fibre. -/
def Chain {index : Index} (source target : computation.State index) :
    Type (max uState uStep) :=
  Σ middle : computation.State index,
    computation.Step source middle × computation.Step middle target

/-- The judgment-indexed chain is exactly proof-relevant loose-relation
composition in its fibre. -/
def chainEquipmentEquiv
    (sameUniverse : JudgmentalComputation.{uIndex, uState, uState} Index)
    {index : Index} (source target : sameUniverse.State index) :
    Chain sameUniverse source target ≃
      Mettapedia.GSLT.LooseRelationEquipment.comp
        sameUniverse.Step sameUniverse.Step source target :=
  Equiv.refl _

/-- Reassociation preserves both intermediate states and all three pieces of
evidence. -/
def chainAssoc {index : Index}
    (source target : computation.State index) :
    (Σ lastMiddle,
      Chain computation source lastMiddle ×
        computation.Step lastMiddle target) ≃
      (Σ firstMiddle,
        computation.Step source firstMiddle ×
          Chain computation firstMiddle target) where
  toFun
    | ⟨lastMiddle, ⟨firstMiddle, first, second⟩, third⟩ =>
        ⟨firstMiddle, first, lastMiddle, second, third⟩
  invFun
    | ⟨firstMiddle, first, lastMiddle, second, third⟩ =>
        ⟨lastMiddle, ⟨firstMiddle, first, second⟩, third⟩
  left_inv := by
    intro evidence
    obtain ⟨_, ⟨_, _, _⟩, _⟩ := evidence
    rfl
  right_inv := by
    intro evidence
    obtain ⟨_, _, _, _, _⟩ := evidence
    rfl

/-- Propositional support is a quotient of step evidence. -/
abbrev Support {index : Index} (source target : computation.State index) :
    Prop :=
  Nonempty (computation.Step source target)

/-- A chain witness always yields a supported two-step path. -/
theorem chain_support {index : Index}
    {source target : computation.State index} :
    Nonempty (Chain computation source target) ↔
      ∃ middle, Support computation source middle ∧
        Support computation middle target := by
  constructor
  · rintro ⟨middle, first, second⟩
    exact ⟨middle, ⟨first⟩, ⟨second⟩⟩
  · rintro ⟨middle, ⟨first⟩, ⟨second⟩⟩
    exact ⟨⟨middle, first, second⟩⟩

/-! ## Erasing to raw endpoints -/

/-- A realization forgets each indexed state to a raw runtime or syntactic
endpoint.  It does not claim that this forgetting is injective. -/
structure Erasure (Raw : Type uRaw) where
  erase : ∀ index, computation.State index → Raw

namespace Erasure

variable {computation}
variable (erasure : Erasure computation Raw)

/-- Full evidence that two raw endpoints arise from one judgment-indexed
step.  The index, both typed states, both endpoint equations, and the exact
step witness survive. -/
def Evidence (source target : Raw) :
    Type (max uIndex uState uStep) :=
  Σ index, Σ typedSource : computation.State index,
    Σ typedTarget : computation.State index,
      PLift (erasure.erase index typedSource = source) ×
      PLift (erasure.erase index typedTarget = target) ×
      computation.Step typedSource typedTarget

/-- The raw relation is the support quotient of erasure evidence. -/
abbrev Relation (source target : Raw) : Prop :=
  Nonempty (Evidence (computation := computation) erasure source target)

/-- Every erased transition receipt exposes the common judgment index. -/
def Evidence.index {source target : Raw}
    (evidence : Evidence (computation := computation) erasure source target) :
    Index :=
  evidence.1

/-- An erased transition still proves that its two typed representatives lie
in one fibre.  Preservation is retained in the receipt, not rediscovered from
the raw endpoints. -/
def Evidence.typedEndpoints {source target : Raw}
    (evidence : Evidence (computation := computation) erasure source target) :
    Σ index, computation.State index × computation.State index :=
  ⟨evidence.1, evidence.2.1, evidence.2.2.1⟩

end Erasure

/-! ## A strict information-loss control -/

namespace ErasureCanary

inductive CanaryIndex where
  | first
  | second
deriving DecidableEq, Repr

def canaryComputation : JudgmentalComputation CanaryIndex where
  State := fun _ => Unit
  Step := fun {index} _ _ =>
    match index with
    | .first => Unit
    | .second => Unit

def erasure : Erasure canaryComputation Unit where
  erase := fun _ _ => ()

def firstEvidence :
    Erasure.Evidence (computation := canaryComputation) erasure () () :=
  ⟨.first, (), (), ⟨rfl⟩, ⟨rfl⟩, ()⟩

def secondEvidence :
    Erasure.Evidence (computation := canaryComputation) erasure () () :=
  ⟨.second, (), (), ⟨rfl⟩, ⟨rfl⟩, ()⟩

/-- Distinct judgment fibres can have identical raw endpoints. -/
theorem firstEvidence_ne_secondEvidence :
    firstEvidence ≠ secondEvidence := by
  intro equality
  have indexEquality := congrArg
    (Erasure.Evidence.index (computation := canaryComputation) erasure)
    equality
  cases indexEquality

/-- The erased endpoint relation is inhabited while its evidence is not a
subsingleton.  Raw truth therefore cannot recover the judgment receipt. -/
theorem relation_does_not_retain_receipt :
    Erasure.Relation (computation := canaryComputation) erasure () () ∧
      ¬ Subsingleton
        (Erasure.Evidence (computation := canaryComputation) erasure () ()) := by
  refine ⟨⟨firstEvidence⟩, ?_⟩
  intro subsingleton
  exact firstEvidence_ne_secondEvidence
    (subsingleton.allEq firstEvidence secondEvidence)

/-- No endpoint-only readout can recover both judgment indices represented by
the same raw transition. -/
theorem no_endpoint_readout_recovers_both :
    ¬ ∃ readIndex : Unit → Unit → CanaryIndex,
      readIndex () () = .first ∧ readIndex () () = .second := by
  rintro ⟨readIndex, first, second⟩
  rw [first] at second
  cases second

end ErasureCanary

/-! ## Lifting extrinsic typing and raw computation -/

/-- The fibre of terms carrying evidence for one extrinsic type.  The typing
evidence is data, so different derivations need not be collapsed. -/
abbrev TypedState (Term : Type uTerm) (Ty : Type uType)
    (HasType : Term → Ty → Type uTyping) (type : Ty) :
    Type (max uTerm uTyping) :=
  Σ term, HasType term type

/-- Restrict a raw proof-relevant reduction to endpoints already carrying
typing evidence at one common type. -/
def ofExtrinsic (Term : Type uTerm) (Ty : Type uType)
    (HasType : Term → Ty → Type uTyping)
    (RawStep : Term → Term → Type uReduction) :
    JudgmentalComputation Ty where
  State := TypedState Term Ty HasType
  Step := fun source target => RawStep source.1 target.1

/-- A preservation lift is the exact extra datum needed to refine raw
computation from a typed source into judgment-indexed computation. -/
abbrev PreservationLift (Term : Type uTerm) (Ty : Type uType)
    (HasType : Term → Ty → Type uTyping)
    (RawStep : Term → Term → Type uReduction) :
    Type (max uTerm uType uTyping uReduction) :=
  ∀ {type source target},
    RawStep source target → HasType source type → HasType target type

/-- A preservation lift constructs the target state and a step in the same
judgment fibre. -/
def liftRawStep {Term : Type uTerm} {Ty : Type uType}
    {HasType : Term → Ty → Type uTyping}
    {RawStep : Term → Term → Type uReduction}
    (preserves : PreservationLift Term Ty HasType RawStep)
    {type : Ty} {source target : Term}
    (step : RawStep source target)
    (sourceTyping : HasType source type) :
    Σ targetState : (ofExtrinsic Term Ty HasType RawStep).State type,
      (ofExtrinsic Term Ty HasType RawStep).Step
        ⟨source, sourceTyping⟩ targetState :=
  ⟨⟨target, preserves step sourceTyping⟩, step⟩

/-- A target-state lift says that the raw target can be reconstructed in the
same typing fibre.  The endpoint equation prevents a degenerate choice of an
unrelated well-typed state. -/
abbrev TargetStateLift (Term : Type uTerm) (Ty : Type uType)
    (HasType : Term → Ty → Type uTyping)
    (RawStep : Term → Term → Type uReduction) :
    Type (max uTerm uType uTyping uReduction) :=
  ∀ {type source target},
    RawStep source target → HasType source type →
      Σ targetState : (ofExtrinsic Term Ty HasType RawStep).State type,
        PLift (targetState.1 = target)

/-- Preservation gives the target-state section lost by erasing the judgment
index. -/
def PreservationLift.toTargetStateLift
    {Term : Type uTerm} {Ty : Type uType}
    {HasType : Term → Ty → Type uTyping}
    {RawStep : Term → Term → Type uReduction}
    (preserves : PreservationLift Term Ty HasType RawStep) :
    TargetStateLift Term Ty HasType RawStep := by
  intro type source target step sourceTyping
  exact ⟨⟨target, preserves step sourceTyping⟩, ⟨rfl⟩⟩

/-- A target-state section recovers ordinary preservation. -/
def TargetStateLift.toPreservationLift
    {Term : Type uTerm} {Ty : Type uType}
    {HasType : Term → Ty → Type uTyping}
    {RawStep : Term → Term → Type uReduction}
    (lifting : TargetStateLift Term Ty HasType RawStep) :
    PreservationLift Term Ty HasType RawStep := by
  intro type source target step sourceTyping
  rcases lifting step sourceTyping with ⟨⟨actualTarget, targetTyping⟩, same⟩
  cases same.down
  exact targetTyping

@[simp] theorem PreservationLift.targetState_roundtrip
    {Term : Type uTerm} {Ty : Type uType}
    {HasType : Term → Ty → Type uTyping}
    {RawStep : Term → Term → Type uReduction}
    (preserves : PreservationLift Term Ty HasType RawStep)
    {type : Ty} {source target : Term} (step : RawStep source target)
    (sourceTyping : HasType source type) :
    TargetStateLift.toPreservationLift
        (Term := Term) (Ty := Ty) (HasType := HasType) (RawStep := RawStep)
        (PreservationLift.toTargetStateLift
          (Term := Term) (Ty := Ty) (HasType := HasType)
          (RawStep := RawStep) preserves)
        (type := type) (source := source) (target := target)
        step sourceTyping =
      preserves step sourceTyping :=
  rfl

/-! ## Preservation failure control -/

namespace PreservationCanary

def HasType : Bool → Unit → Type
  | false, () => Unit
  | true, () => Empty

inductive RawStep : Bool → Bool → Type where
  | corrupt : RawStep false true

/-- A raw relation may leave the typing fibre, in which case no
judgment-indexed lift exists. -/
theorem no_preservation_lift :
    PreservationLift Bool Unit HasType RawStep → False := by
  intro preserves
  exact (preserves (type := ()) RawStep.corrupt ()).elim

/-- The source is well typed and the raw step exists, so failure above is not
vacuous. -/
theorem corrupt_source_and_step_inhabited :
    Nonempty (HasType false ()) ∧ Nonempty (RawStep false true) :=
  ⟨⟨()⟩, ⟨RawStep.corrupt⟩⟩

end PreservationCanary

/-! ## Axiom audit -/

#print axioms chainAssoc
#print axioms ErasureCanary.relation_does_not_retain_receipt
#print axioms PreservationLift.targetState_roundtrip
#print axioms PreservationCanary.no_preservation_lift

end JudgmentalComputation
end Mettapedia.TypeTheory
