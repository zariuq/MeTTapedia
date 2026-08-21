import Mettapedia.TypeTheory.JudgmentalEquality
import Mettapedia.Languages.MeTTa.PureKernel.Universe.DeclarationSignature
import Mettapedia.Languages.MeTTa.PureKernel.Universe.TypingGeneration

/-!
# Typed computation receipts for declaration-aware presentations

`RootComputation` is the raw operational readout of a declaration signature.
This module connects it to the reusable judgment-indexed computation theory.
The informative carrier retains the telescope, displayed type, source and
target typing derivations, and exact root-step witness.

The distinction exposed here is important:

* a well-formed declaration supplies canonical typing for delta unfolding;
* `Signature.WellFormed.declaredPreserves` supplies a uniform lift for the
  explicitly declared computation family;
* preservation of inherited computation under the larger signature and delta
  preservation at every displayed type are separate premises needed for the
  full combined root relation.

Thus a raw signature is never promoted to computational authority merely
because its equations are stable under renaming and substitution.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
namespace Declaration

universe uEvidence

/-! ## Proof-relevant root evidence and its logical support -/

/-- Declaration computation before support erasure.  Rule identity and all
authored arguments remain data; renaming and substitution act on that data
under binders. -/
structure ProofRelevantRootComputation (Head : Type) where
  Evidence : {n : Nat} → Tm Head n → Tm Head n → Type uEvidence
  rename : ∀ {n m : Nat} (rho : Ren n m) {left right : Tm Head n},
    Evidence left right →
      Evidence (Presentation.rename rho left) (Presentation.rename rho right)
  substitute : ∀ {n m : Nat} (sigma : Sub Head n m)
      {left right : Tm Head n},
    Evidence left right →
      Evidence (subst sigma left) (subst sigma right)

/-- Definitional conversion consumes only inhabitation of root evidence.
The full receipt remains available to the authority and execution layers. -/
def ProofRelevantRootComputation.support
    (computation : ProofRelevantRootComputation.{uEvidence} Head) :
    RootComputation Head where
  step := fun left right => Nonempty (computation.Evidence left right)
  rename := by
    rintro n m rho left right ⟨evidence⟩
    exact ⟨computation.rename rho evidence⟩
  substitute := by
    rintro n m sigma left right ⟨evidence⟩
    exact ⟨computation.substitute sigma evidence⟩

/-- Support is exactly the propositional quotient of retained evidence. -/
theorem ProofRelevantRootComputation.support_iff
    (computation : ProofRelevantRootComputation.{uEvidence} Head)
    {left right : Tm Head n} :
    computation.support.step left right ↔
      Nonempty (computation.Evidence left right) :=
  Iff.rfl

namespace ComputationAuthority

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.JudgmentalComputation
open Mettapedia.TypeTheory.JudgmentalEquality

/-! ## The declared computation family as data -/

abbrev DataHasType (base : Rules Head) (signature : Signature Head)
    (context : Ctx Head n) (term type : Tm Head n) : Type :=
  PLift (HasType (extendRules base signature) context term type)

abbrev DataDeclaredStep (signature : Signature Head)
    (left right : Tm Head n) : Type :=
  PLift (signature.computation.step left right)

/-- A type-valued preservation section for every telescope. -/
abbrev DeclaredPreservationFamily (base : Rules Head)
    (signature : Signature Head) : Type :=
  ∀ (n : Nat) (context : Ctx Head n),
    PreservationLift (Tm Head n) (Tm Head n)
      (DataHasType base signature context)
      (DataDeclaredStep signature)

/-- The existing proposition-valued field has an exact proof-relevant data
readout.  No type index or source derivation is discarded. -/
def Signature.WellFormed.declaredPreservationFamily
    {base : Rules Head} {signature : Signature Head}
    (wellFormed : signature.WellFormed base) :
    DeclaredPreservationFamily base signature := by
  intro n context type source target step sourceTyping
  exact ⟨wellFormed.declaredPreserves step.down sourceTyping.down⟩

/-- Conversely, the type-valued family is sufficient to discharge the
proposition-valued preservation field. -/
def declaredPreservesOfFamily {base : Rules Head}
    {signature : Signature Head}
    (family : DeclaredPreservationFamily base signature) :
    ∀ {n : Nat} {context : Ctx Head n} {left right type : Tm Head n},
      signature.computation.step left right →
      HasType (extendRules base signature) context left type →
        HasType (extendRules base signature) context right type := by
  intro n context left right type step sourceTyping
  exact (family n context ⟨step⟩ ⟨sourceTyping⟩).down

theorem declaredPreserves_iff_family_inhabited
    (base : Rules Head) (signature : Signature Head) :
    (∀ {n : Nat} {context : Ctx Head n}
        {left right type : Tm Head n},
      signature.computation.step left right →
      HasType (extendRules base signature) context left type →
        HasType (extendRules base signature) context right type) ↔
      Nonempty (DeclaredPreservationFamily base signature) := by
  constructor
  · intro preserves
    exact ⟨by
      intro n context type source target step sourceTyping
      exact ⟨preserves step.down sourceTyping.down⟩⟩
  · rintro ⟨family⟩
    exact declaredPreservesOfFamily family

/-! ## One computation fibred over complete typing judgments -/

/-- A complete typing index retains arity, telescope, and displayed type. -/
structure TypingIndex (Head : Type) where
  arity : Nat
  context : Ctx Head arity
  type : Tm Head arity

/-- Terms with their exact typing derivations form the states; declared root
steps form proof-relevant loose arrows inside each typing fibre. -/
def indexedDeclaredComputation (base : Rules Head)
    (signature : Signature Head) :
    JudgmentalComputation (TypingIndex Head) where
  State := fun index =>
    Σ term : Tm Head index.arity,
      DataHasType base signature index.context term index.type
  Step := fun source target =>
    DataDeclaredStep signature source.1 target.1

/-- A canonical typed receipt for one declaration equation.  Unlike an
endpoint-only reduction fact, it records the exact telescope and displayed
type together with both endpoint typings. -/
structure DeclaredStepReceipt (base : Rules Head)
    (signature : Signature Head) (context : Ctx Head n)
    (left right type : Tm Head n) : Type where
  sourceTyping : HasType (extendRules base signature) context left type
  targetTyping : HasType (extendRules base signature) context right type
  reduction : signature.computation.step left right

/-- The informative form of a typed declaration step.  In addition to both
endpoint typings it retains the exact evidence inhabitant whose support is
consumed by conversion. -/
structure ProofRelevantStepReceipt (base : Rules Head)
    (signature : Signature Head)
    (computation : ProofRelevantRootComputation Head)
    (context : Ctx Head n) (left right type : Tm Head n) : Type where
  sourceTyping : HasType (extendRules base signature) context left type
  targetTyping : HasType (extendRules base signature) context right type
  evidence : computation.Evidence left right

/-- Support erasure is explicit: the retained rule witness is forgotten only
when a consumer asks for the proposition-valued declaration step. -/
def ProofRelevantStepReceipt.toDeclaredReceipt
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (receipt : ProofRelevantStepReceipt base signature computation context
      left right type)
    (supportEquation : signature.computation = computation.support) :
    DeclaredStepReceipt base signature context left right type where
  sourceTyping := receipt.sourceTyping
  targetTyping := receipt.targetTyping
  reduction := by
    rw [supportEquation]
    exact ⟨receipt.evidence⟩

/-- Typed substitution acts on the full receipt, including the retained rule
witness. -/
def ProofRelevantStepReceipt.substitute
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {left right type : Tm Head n} (substitution : Sub Head n m)
    (receipt : ProofRelevantStepReceipt base signature computation
      sourceContext left right type)
    (typed : CtxMor (extendRules base signature) sourceContext targetContext
      substitution) :
    ProofRelevantStepReceipt base signature computation targetContext
      (subst substitution left) (subst substitution right)
      (subst substitution type) where
  sourceTyping := receipt.sourceTyping.substitute typed
  targetTyping := receipt.targetTyping.substitute typed
  evidence := computation.substitute substitution receipt.evidence

/-- The exact typed-substitution image of one proof-relevant schema. -/
structure ProofRelevantStepReceipt.InstanceAt
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {sourceContext : Ctx Head n}
    {sourceLeft sourceRight sourceType : Tm Head n}
    (schema : ProofRelevantStepReceipt base signature computation
      sourceContext sourceLeft sourceRight sourceType)
    (targetContext : Ctx Head m) (left right type : Tm Head m) : Type where
  substitution : Sub Head n m
  typed : CtxMor (extendRules base signature) sourceContext targetContext
    substitution
  sourceEquation : subst substitution sourceLeft = left
  targetEquation : subst substitution sourceRight = right
  typeEquation : subst substitution sourceType = type

/-- Reconstruct the complete typed receipt at a recognized substitution
instance. -/
def ProofRelevantStepReceipt.InstanceAt.toReceipt
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {sourceContext : Ctx Head n}
    {sourceLeft sourceRight sourceType : Tm Head n}
    {schema : ProofRelevantStepReceipt base signature computation
      sourceContext sourceLeft sourceRight sourceType}
    {targetContext : Ctx Head m} {left right type : Tm Head m}
    (occurrence : schema.InstanceAt targetContext left right type) :
    ProofRelevantStepReceipt base signature computation targetContext
      left right type := by
  have transported :=
    schema.substitute occurrence.substitution occurrence.typed
  rw [occurrence.sourceEquation, occurrence.targetEquation,
    occurrence.typeEquation] at transported
  exact transported

/-- Every canonical schema belongs to its own exact substitution image. -/
def ProofRelevantStepReceipt.identityInstance
    {base : Rules Head} {signature : Signature Head}
    {computation : ProofRelevantRootComputation Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (schema : ProofRelevantStepReceipt base signature computation context
      left right type) :
    schema.InstanceAt context left right type where
  substitution := ids
  typed := CtxMor.identity _ _
  sourceEquation := subst_ids _
  targetEquation := subst_ids _
  typeEquation := subst_ids _

/-- The complete judgment index retained by a canonical receipt. -/
def DeclaredStepReceipt.index
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (_receipt : DeclaredStepReceipt base signature context left right type) :
    TypingIndex Head :=
  ⟨n, context, type⟩

def DeclaredStepReceipt.sourceState
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (receipt : DeclaredStepReceipt base signature context left right type) :
    (indexedDeclaredComputation base signature).State receipt.index :=
  ⟨left, ⟨receipt.sourceTyping⟩⟩

def DeclaredStepReceipt.targetState
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (receipt : DeclaredStepReceipt base signature context left right type) :
    (indexedDeclaredComputation base signature).State receipt.index :=
  ⟨right, ⟨receipt.targetTyping⟩⟩

/-- A canonical receipt is literally a step between two states of the same
judgment-indexed computation fibre. -/
def DeclaredStepReceipt.toIndexedStep
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (receipt : DeclaredStepReceipt base signature context left right type) :
    (indexedDeclaredComputation base signature).Step
      receipt.sourceState receipt.targetState :=
  ⟨receipt.reduction⟩

/-- One typed declaration receipt is a generator of judgment-indexed
conversion.  Its source and target share the complete typing index by
construction; no separate subject-reduction reconstruction is needed at this
layer. -/
def DeclaredStepReceipt.toConversionEvidence
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (receipt : DeclaredStepReceipt base signature context left right type) :
    ConversionEvidence (indexedDeclaredComputation base signature)
      receipt.sourceState receipt.targetState :=
  .step receipt.toIndexedStep

/-- Typed substitution transports the entire receipt.  In particular, it
does not merely substitute the raw endpoints and then ask preservation to
reconstruct the target typing. -/
def DeclaredStepReceipt.substitute
    {base : Rules Head} {signature : Signature Head}
    {sourceContext : Ctx Head n} {targetContext : Ctx Head m}
    {left right type : Tm Head n} (substitution : Sub Head n m)
    (receipt :
      DeclaredStepReceipt base signature sourceContext left right type)
    (typed : CtxMor (extendRules base signature) sourceContext targetContext
      substitution) :
    DeclaredStepReceipt base signature targetContext
      (subst substitution left) (subst substitution right)
      (subst substitution type) where
  sourceTyping := receipt.sourceTyping.substitute typed
  targetTyping := receipt.targetTyping.substitute typed
  reduction := signature.computation.substitute substitution receipt.reduction

/-- Membership in the exact typed-substitution image of one canonical rule
schema.  Endpoint and type equations are retained because different schema
instances can erase to the same raw syntax. -/
structure DeclaredStepReceipt.InstanceAt
    {base : Rules Head} {signature : Signature Head}
    {sourceContext : Ctx Head n} {sourceLeft sourceRight sourceType : Tm Head n}
    (schema : DeclaredStepReceipt base signature sourceContext
      sourceLeft sourceRight sourceType)
    (targetContext : Ctx Head m) (left right type : Tm Head m) : Type where
  substitution : Sub Head n m
  typed : CtxMor (extendRules base signature) sourceContext targetContext
    substitution
  sourceEquation : subst substitution sourceLeft = left
  targetEquation : subst substitution sourceRight = right
  typeEquation : subst substitution sourceType = type

/-- Exact-image membership reconstructs the complete typed receipt at the
displayed target judgment. -/
def DeclaredStepReceipt.InstanceAt.toReceipt
    {base : Rules Head} {signature : Signature Head}
    {sourceContext : Ctx Head n} {sourceLeft sourceRight sourceType : Tm Head n}
    {schema : DeclaredStepReceipt base signature sourceContext
      sourceLeft sourceRight sourceType}
    {targetContext : Ctx Head m} {left right type : Tm Head m}
    (occurrence : schema.InstanceAt targetContext left right type) :
    DeclaredStepReceipt base signature targetContext left right type := by
  have transported :=
    schema.substitute occurrence.substitution occurrence.typed
  rw [occurrence.sourceEquation, occurrence.targetEquation,
    occurrence.typeEquation] at transported
  exact transported

/-- Every canonical schema belongs to its own exact image by identity
substitution. -/
def DeclaredStepReceipt.identityInstance
    {base : Rules Head} {signature : Signature Head}
    {context : Ctx Head n} {left right type : Tm Head n}
    (schema : DeclaredStepReceipt base signature context left right type) :
    schema.InstanceAt context left right type where
  substitution := ids
  typed := CtxMor.identity _ _
  sourceEquation := subst_ids _
  targetEquation := subst_ids _
  typeEquation := subst_ids _

/-- A well-formed signature lifts a declared raw step from a typed source to
an indexed target state while retaining the identical step receipt. -/
def Signature.WellFormed.liftDeclaredStep
    {base : Rules Head} {signature : Signature Head}
    (wellFormed : signature.WellFormed base)
    {index : TypingIndex Head}
    {source target : Tm Head index.arity}
    (step : signature.computation.step source target)
    (sourceTyping :
      HasType (extendRules base signature) index.context source index.type) :
    Σ targetState :
        (indexedDeclaredComputation base signature).State index,
      (indexedDeclaredComputation base signature).Step
        ⟨source, ⟨sourceTyping⟩⟩ targetState :=
  ⟨⟨target, ⟨wellFormed.declaredPreserves step sourceTyping⟩⟩, ⟨step⟩⟩

/-! ## Canonical delta receipts versus full root preservation -/

/-- Canonical delta unfolding retains both endpoint typings at the declared
type.  It makes no stronger type-uniqueness claim. -/
structure CanonicalDeltaReceipt (base : Rules Head)
    (signature : Signature Head) (context : Ctx Head n)
    (name : DeclName) (type value : Tm Head 0) : Type where
  sourceTyping :
    HasType (extendRules base signature) context
      (Tm.const (n := n) name) (liftClosed (n := n) type)
  targetTyping :
    HasType (extendRules base signature) context
      (liftClosed (n := n) value) (liftClosed (n := n) type)
  reduction :
    (extendRules base signature).computation.step
      (Tm.const (n := n) name) (liftClosed (n := n) value)

/-- Signature well-formedness constructs the complete canonical delta
receipt in every ambient telescope. -/
def Signature.WellFormed.canonicalDeltaReceipt
    {base : Rules Head} {signature : Signature Head}
    (wellFormed : signature.WellFormed base)
    {name : DeclName} {type value : Tm Head 0}
    (typeLookup : signature.typeOf? name = some type)
    (valueLookup : signature.valueOf? name = some value)
    (context : Ctx Head n) :
    CanonicalDeltaReceipt base signature context name type value := by
  have fresh : base.constantType name = none := by
    unfold Signature.typeOf? at typeLookup
    cases entryLookup : signature.entries name with
    | none => simp [entryLookup] at typeLookup
    | some entry => exact wellFormed.fresh entryLookup
  have sourceTyping :
      HasType (extendRules base signature) context (.const name)
        (liftClosed type) := by
    apply HasType.const
    exact combinedType_of_signature base signature fresh typeLookup
  have targetAtEmpty :
      HasType (extendRules base signature) (.nil : Ctx Head 0) value type :=
    wellFormed.values typeLookup valueLookup
  have emptyRenaming :
      CtxRen (.nil : Ctx Head 0) context (Fin.elim0 : Ren 0 n) := by
    intro index
    exact Fin.elim0 index
  have targetTyping := targetAtEmpty.renameTyping emptyRenaming
  refine
    { sourceTyping := sourceTyping
      targetTyping := by
        simpa only [liftClosed] using targetTyping
      reduction := RootStep.delta valueLookup }

/-- The two remaining premises for preservation of the complete combined root
relation.  The declared branch is already supplied by
`Signature.WellFormed`; these premises cannot be inferred from formation
alone. -/
structure RemainingRootPreservation (base : Rules Head)
    (signature : Signature Head) : Type where
  inherited : ∀ {n : Nat} {context : Ctx Head n}
      {left right type : Tm Head n},
    base.computation.step left right →
    HasType (extendRules base signature) context left type →
      HasType (extendRules base signature) context right type
  delta : ∀ {n : Nat} {context : Ctx Head n}
      {name : DeclName} {value : Tm Head 0} {type : Tm Head n},
    signature.valueOf? name = some value →
    HasType (extendRules base signature) context (.const name) type →
      HasType (extendRules base signature) context (liftClosed value) type

/-- Once the inherited and arbitrary-displayed-type delta premises are
provided, well-formedness lifts every branch of the combined raw root
relation. -/
def Signature.WellFormed.combinedRootPreserves
    {base : Rules Head} {signature : Signature Head}
    (wellFormed : signature.WellFormed base)
    (remaining : RemainingRootPreservation base signature) :
    ∀ {n : Nat} {context : Ctx Head n}
        {left right type : Tm Head n},
      (extendRules base signature).computation.step left right →
      HasType (extendRules base signature) context left type →
        HasType (extendRules base signature) context right type := by
  intro n context left right type step sourceTyping
  change RootStep base signature n left right at step
  cases step with
  | inherited inherited => exact remaining.inherited inherited sourceTyping
  | delta unfolding => exact remaining.delta unfolding sourceTyping
  | declared declared =>
      exact wellFormed.declaredPreserves declared sourceTyping

/-! ## Axiom audit -/

#print axioms ProofRelevantRootComputation.support_iff
#print axioms declaredPreserves_iff_family_inhabited
#print axioms DeclaredStepReceipt.toIndexedStep
#print axioms DeclaredStepReceipt.toConversionEvidence
#print axioms DeclaredStepReceipt.substitute
#print axioms DeclaredStepReceipt.InstanceAt.toReceipt
#print axioms DeclaredStepReceipt.identityInstance
#print axioms Signature.WellFormed.liftDeclaredStep
#print axioms Signature.WellFormed.canonicalDeltaReceipt
#print axioms Signature.WellFormed.combinedRootPreserves

end ComputationAuthority
end Declaration
end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
