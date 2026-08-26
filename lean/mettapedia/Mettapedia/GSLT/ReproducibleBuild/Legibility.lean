import Mathlib.Tactic
import Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
import Mettapedia.GSLT.HierarchicalComplexity
import Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling
import Mettapedia.GSLT.ReproducibleBuild.HattaProfile

/-!
# Observer-indexed verification legibility

Verification legibility is not an intrinsic scalar attached to a program or a
transformation.  It is relative to a verification question, a presentation of
the evidence, and the methods admitted by an auditor.  The informative object
is the ordered family of sufficient audit views.  Hierarchical-complexity rank
is retained separately as a readout of an actual verification plan.

The information order reuses the executable `OpenEndedContext.Refines`
relation.  `coarse <= fine` means that the fine view can be forgotten to the
coarse view.  Consequently the family of sufficient views is upward closed,
and a weakest sufficient view is a genuine least element when it is attained.

The Model of Hierarchical Complexity is used only to classify concrete audit
plans by permutation invariance.  No claim of human readability or independent
attestability follows merely from being a chain.

References:

- M. Hatta, *Reproducibility Is the New Copyleft: Defining AGI-Oriented
  Reproducible Builds* (2026), especially R4 and R7.
- M. L. Commons and A. Pekker, *Presenting the Formal Theory of Hierarchical
  Complexity* (2008), for the chain/coordination criterion.
- D. A. Wheeler, *Fully Countering Trusting Trust through Diverse
  Double-Compiling* (2009), for the independent DDC premises.
- D. E. Knuth, *Literate Programming* (1984), as historical motivation for
  treating audit presentation as a first-class object.

The audit-view order, capability-indexed formulation, strict separation
witnesses, and their GSLT applications are new.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.Legibility

open Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext
open Mettapedia.Cybernetics.HierarchicalComplexity
open Mettapedia.Cybernetics.HierarchicalComplexity.Composition

universe uState uAnswer uView uOutcome uOccurrence uEvidence

/-! ## Audit questions and the information preorder -/

/-- The judgment an auditor is asked to recover for each proof-relevant case.
`State` may itself be a sigma type retaining source, result, and execution
witnesses; no functional-build assumption is made here. -/
structure AuditQuestion (State : Type uState) (Answer : Type uAnswer) where
  answer : State -> Answer

/-- One presented observation of an audit case.  Different views may expose
different types and different amounts of information. -/
structure AuditView (State : Type uState) where
  View : Type uView
  observe : State -> View

namespace AuditView

variable {State : Type uState}

/-- Information order: `coarse <= fine` when the fine view contains an
executable projection to the coarse view. -/
def InformationLe (coarse fine : AuditView State) : Prop :=
  Refines fine.observe coarse.observe

instance : LE (AuditView State) :=
  ⟨InformationLe⟩

instance : Preorder (AuditView State) where
  le := InformationLe
  le_refl view := Refines.refl view.observe
  le_trans left middle right leftMiddle middleRight :=
    Refines.trans middleRight leftMiddle

/-- Mutual executable refinement is the extensional equivalence induced by
the information preorder. -/
def Equivalent (left right : AuditView State) : Prop :=
  left <= right /\ right <= left

theorem equivalent_refl (view : AuditView State) : Equivalent view view :=
  ⟨le_rfl, le_rfl⟩

theorem equivalent_symm {left right : AuditView State}
    (equivalent : Equivalent left right) : Equivalent right left :=
  ⟨equivalent.2, equivalent.1⟩

theorem equivalent_trans {left middle right : AuditView State}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right :=
  ⟨le_trans leftMiddle.1 middleRight.1,
    le_trans middleRight.2 leftMiddle.2⟩

/-- The mutual-refinement quotient relation. -/
def equivalenceSetoid : Setoid (AuditView State) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Product observations retain both component views. -/
def product (left right : AuditView State) : AuditView State where
  View := left.View × right.View
  observe state := (left.observe state, right.observe state)

end AuditView

namespace AuditQuestion

/-- Audit two questions at once. -/
def product {State : Type uState} {LeftAnswer RightAnswer : Type uAnswer}
    (left : AuditQuestion State LeftAnswer)
    (right : AuditQuestion State RightAnswer) :
    AuditQuestion State (LeftAnswer × RightAnswer) where
  answer state := (left.answer state, right.answer state)

end AuditQuestion

/-! ## Sufficient views and actual verification methods -/

/-- A view is sufficient when an executable decoder recovers the declared
audit answer on every represented case. -/
def Sufficient {State : Type uState} {Answer : Type uAnswer}
    (question : AuditQuestion State Answer) (view : AuditView State) : Prop :=
  exists decode : view.View -> Answer,
    forall state, decode (view.observe state) = question.answer state

/-- Sufficient views are upward closed in the information order. -/
theorem sufficient_of_le
    {State : Type uState} {Answer : Type uAnswer}
    {question : AuditQuestion State Answer}
    {coarse fine : AuditView State}
    (sufficient : Sufficient question coarse) (refines : coarse <= fine) :
    Sufficient question fine := by
  obtain ⟨decode, verifies⟩ := sufficient
  obtain ⟨forget, commutes⟩ := refines
  refine ⟨decode ∘ forget, ?_⟩
  intro state
  simp only [Function.comp_apply, commutes, verifies]

/-- A verification method is a sufficient view together with the concrete
MHC action used to perform the audit.  Sufficiency and plan rank remain
separate fields. -/
structure AuditMethod
    {State : Type uState} {Answer : Type uAnswer}
    (question : AuditQuestion State Answer) (view : AuditView State)
    (Outcome : Type uOutcome) where
  decode : view.View -> Answer
  verifies : forall state, decode (view.observe state) = question.answer state
  plan : Action.{uOccurrence, uOutcome} Outcome

namespace AuditMethod

variable {State : Type uState} {Answer : Type uAnswer}
  {question : AuditQuestion State Answer}

theorem sufficient {view : AuditView State} {Outcome : Type uOutcome}
    (method : AuditMethod question view Outcome) :
    Sufficient question view :=
  ⟨method.decode, method.verifies⟩

/-- Combine two decoders while supplying the actual composite audit plan.
The caller must classify that plan separately as a chain or coordination. -/
def productWithPlan
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (plan : Action.{0, uOutcome} Outcome) :
    AuditMethod (AuditQuestion.product leftQuestion rightQuestion)
      (AuditView.product leftView rightView) Outcome where
  decode visible := (left.decode visible.1, right.decode visible.2)
  verifies state := by
    simp only [AuditView.product, AuditQuestion.product]
    exact congrArg₂ Prod.mk (left.verifies state) (right.verifies state)
  plan := plan

/-- The two component audit plans indexed by `Fin 2`. -/
def binaryChildren
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome) :
    Fin 2 -> Action.{0, uOutcome} Outcome :=
  fun index => if index = 0 then left.plan else right.plan

/-- Permutation-invariant composition yields a chain audit method. -/
def chainProduct
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (process : BinaryProcess Outcome)
    (invariant : IsChain process.scheduleSemantics) :
    AuditMethod (AuditQuestion.product leftQuestion rightQuestion)
      (AuditView.product leftView rightView) Outcome :=
  productWithPlan left right
    (BinaryProcess.chainAction process invariant (binaryChildren left right))

/-- Order-sensitive composition yields a coordination audit method. -/
def coordinationProduct
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics) :
    AuditMethod (AuditQuestion.product leftQuestion rightQuestion)
      (AuditView.product leftView rightView) Outcome :=
  productWithPlan left right
    (BinaryProcess.coordinationAction process sensitive
      (binaryChildren left right))

theorem binaryChildren_equalRank
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (equalRank : Action.rank left.plan = Action.rank right.plan) :
    forall index,
      Action.rank (binaryChildren left right index) =
        Action.rank (binaryChildren left right 0) := by
  intro index
  fin_cases index <;> simp [binaryChildren, equalRank]

/-- A homogeneous chain preserves the component verification rank. -/
theorem rank_chainProduct
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (process : BinaryProcess Outcome)
    (invariant : IsChain process.scheduleSemantics)
    (equalRank : Action.rank left.plan = Action.rank right.plan) :
    Action.rank (chainProduct left right process invariant).plan =
      Action.rank left.plan := by
  exact BinaryProcess.rank_chainAction_of_equalRank process invariant
    (binaryChildren left right)
    (binaryChildren_equalRank left right equalRank)

/-- A homogeneous coordination raises the component verification rank by one. -/
theorem rank_coordinationProduct
    {LeftAnswer RightAnswer : Type uAnswer}
    {leftQuestion : AuditQuestion State LeftAnswer}
    {rightQuestion : AuditQuestion State RightAnswer}
    {leftView rightView : AuditView State}
    {Outcome : Type uOutcome}
    (left : AuditMethod leftQuestion leftView Outcome)
    (right : AuditMethod rightQuestion rightView Outcome)
    (process : BinaryProcess Outcome)
    (sensitive : IsCoordination process.scheduleSemantics)
    (equalRank : Action.rank left.plan = Action.rank right.plan) :
    Action.rank (coordinationProduct left right process sensitive).plan =
      Order.succ (Action.rank left.plan) := by
  exact BinaryProcess.rank_coordinationAction_of_equalRank process sensitive
    (binaryChildren left right)
    (binaryChildren_equalRank left right equalRank)

end AuditMethod

/-! ## Auditor capability and attained minima -/

/-- An auditor capability identifies the methods actually available to that
auditor.  Closure under executable refinement says that a finer view may be
forgotten to an already permitted one without changing the audit plan. -/
structure AuditorCapability
    {State : Type uState} {Answer : Type uAnswer}
    (question : AuditQuestion State Answer) (Outcome : Type uOutcome) where
  Permits : {view : AuditView.{uState, uView} State} ->
    AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question view Outcome -> Prop
  refinementClosed :
    forall {coarse fine : AuditView.{uState, uView} State}
      (method : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
        question coarse Outcome),
      Permits method -> coarse <= fine ->
        exists lifted :
          AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
            question fine Outcome,
          Permits lifted /\ lifted.plan = method.plan

/-- One capability-permitted audit method, retaining its heterogeneous view. -/
structure PermittedMethod
    {State : Type uState} {Answer : Type uAnswer}
    {question : AuditQuestion State Answer} {Outcome : Type uOutcome}
    (capability :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome) where
  view : AuditView.{uState, uView} State
  method : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
    question view Outcome
  permitted : capability.Permits method

/-- A weakest permitted method is attained and its view is below every other
permitted view.  No global choice of minima is assumed. -/
structure WeakestPermittedMethod
    {State : Type uState} {Answer : Type uAnswer}
    {question : AuditQuestion State Answer} {Outcome : Type uOutcome}
    (capability :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome) where
  selected : PermittedMethod capability
  weakest : forall (other : PermittedMethod capability),
    selected.view <= other.view

/-- Minimum plan rank is a separate attained readout.  It need not be carried
by the weakest-information method in an arbitrary capability. -/
structure AttainedMinimumRank
    {State : Type uState} {Answer : Type uAnswer}
    {question : AuditQuestion State Answer} {Outcome : Type uOutcome}
    (capability :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome) where
  selected : PermittedMethod capability
  minimum : forall (other : PermittedMethod capability),
    Action.rank selected.method.plan <= Action.rank other.method.plan

namespace AuditorCapability

variable {State : Type uState} {Answer : Type uAnswer}
  {question : AuditQuestion State Answer} {Outcome : Type uOutcome}
  {baseView : AuditView.{uState, uView} State}

/-- Capability extension adds permitted methods without withdrawing existing
ones. -/
def Extends
    (larger smaller :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome) : Prop :=
  forall {view : AuditView.{uState, uView} State}
    (method : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question view Outcome),
    smaller.Permits method -> larger.Permits method

/-- A capability has an actually permitted method at or below a declared MHC
rank.  This is an attained property, not an infimum assertion. -/
def HasMethodAtMostRank
    (capability :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome)
    (bound : Ordinal.{uOccurrence}) : Prop :=
  exists selected : PermittedMethod capability,
    Action.rank selected.method.plan <= bound

/-- Adding methods cannot make a realization less legible by erasing a
previously available lower-rank audit.  A newly supplied inconvenient
certificate therefore cannot establish opacity. -/
theorem hasMethodAtMostRank_mono
    {larger smaller :
      AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
        question Outcome}
    (hExtends : Extends larger smaller) {bound : Ordinal.{uOccurrence}}
    (available : HasMethodAtMostRank smaller bound) :
    HasMethodAtMostRank larger bound := by
  obtain ⟨selected, bounded⟩ := available
  refine ⟨{
    view := selected.view
    method := selected.method
    permitted := hExtends selected.method selected.permitted }, bounded⟩

/-- Generate the smallest refinement-closed capability containing one base
method.  A permitted method must refine the base view and use the same actual
verification plan. -/
def generated
    (base : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question baseView Outcome) :
    AuditorCapability.{uState, uAnswer, uView, uOutcome, uOccurrence}
      question Outcome where
  Permits := fun {view} method =>
    baseView <= view /\ method.plan = base.plan
  refinementClosed := by
    intro coarse fine method permitted coarseFine
    have baseFine : baseView <= fine := le_trans permitted.1 coarseFine
    obtain ⟨forget, commutes⟩ := coarseFine
    let lifted : AuditMethod question fine Outcome :=
      { decode := method.decode ∘ forget
        verifies := by
          intro state
          simp only [Function.comp_apply, commutes]
          exact method.verifies state
        plan := method.plan }
    refine ⟨lifted, ?_, rfl⟩
    exact ⟨baseFine, permitted.2⟩

/-- The generator is permitted by its generated capability. -/
theorem generated_permits_base
    (base : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question baseView Outcome) :
    (generated base).Permits base :=
  ⟨le_rfl, rfl⟩

/-- The generating method attains the weakest permitted view. -/
def generatedWeakest
    (base : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question baseView Outcome) :
    WeakestPermittedMethod (generated base) where
  selected :=
    { view := baseView
      method := base
      permitted := generated_permits_base base }
  weakest other := other.permitted.1

/-- The generating method also attains the minimum rank because refinement
closure preserves its plan rather than inventing another one. -/
def generatedMinimumRank
    (base : AuditMethod.{uState, uAnswer, uOutcome, uOccurrence, uView}
      question baseView Outcome) :
    AttainedMinimumRank (generated base) where
  selected :=
    { view := baseView
      method := base
      permitted := generated_permits_base base }
  minimum other := by
    rw [other.permitted.2]

end AuditorCapability

/-! ## GSLT observer relativity -/

namespace GSLTObserverRelativity

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.GSLT
open Mettapedia.GSLT.IndexedOperational

universe uTerm uIndex vIndex

/-- The same GSLT-IL naturality square is a chain when the auditor asks only
for its endpoint and a coordination when the auditor retains its authored
proof route.  Legibility classification is therefore observation-indexed. -/
theorem naturality_audit_classification_is_observer_relative
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram.{uTerm, uIndex, vIndex} Index)
    {source target : Index} (route : source ⟶ target)
    {left right : SemanticTerm (diagram.obj source).theory}
    (step : SemanticStep (diagram.obj source).theory left right) :
    IsChain
        (Mettapedia.GSLT.HierarchicalComplexity.DiamondObservation.endpointSemantics
          (Command.naturalityDiamond diagram route step)) /\
      IsCoordination
        (Mettapedia.GSLT.HierarchicalComplexity.DiamondObservation.routeSemantics
          (Command.naturalityDiamond diagram route step)) :=
  Mettapedia.GSLT.HierarchicalComplexity.IndexedNaturality.naturality_classification_is_observer_relative
    diagram route step

end GSLTObserverRelativity

/-! ## Presented realizations -/

/-- A behavior together with the evidence presentation exposed to an auditor.
`Case` may be a proof-relevant execution episode. -/
structure PresentedRealization
    (Case : Type uState) (Result : Type uAnswer) where
  Evidence : Type uEvidence
  behavior : Case -> Result
  evidence : Case -> Evidence

namespace PresentedRealization

/-- The evidence supplied by a presentation as an audit view. -/
def evidenceView {Case : Type uState} {Result : Type uAnswer}
    (presentation : PresentedRealization Case Result) : AuditView Case where
  View := presentation.Evidence
  observe := presentation.evidence

/-- The extensional behavior question, distinct from its evidence
presentation. -/
def behaviorQuestion {Case : Type uState} {Result : Type uAnswer}
    (presentation : PresentedRealization Case Result) : AuditQuestion Case Result where
  answer := presentation.behavior

/-- Presentation equivalence forgets evidence but retains all extensional
behavior. -/
def ExtensionallyEquivalent
    {Case : Type uState} {Result : Type uAnswer}
    (left : PresentedRealization Case Result)
    (right : PresentedRealization Case Result) : Prop :=
  forall input, left.behavior input = right.behavior input

end PresentedRealization

/-! ## Strict, observer-indexed separation witnesses -/

namespace Canary

open Mettapedia.Cybernetics.HierarchicalComplexity.Composition.InteractionCanary

def clearPresentation : PresentedRealization Bool Bool where
  Evidence := Bool
  behavior := id
  evidence := id

structure FullTrace where
  first : Bool
  second : Bool
deriving DecidableEq

def opaquePresentation : PresentedRealization Bool Bool where
  Evidence := FullTrace
  behavior := id
  evidence input := ⟨!input, input⟩

theorem presentations_extensionally_equivalent :
    PresentedRealization.ExtensionallyEquivalent
      clearPresentation opaquePresentation :=
  fun _ => rfl

def clearMethod :
    AuditMethod (clearPresentation.behaviorQuestion)
      clearPresentation.evidenceView (Nat × Nat) where
  decode := id
  verifies := fun _ => rfl
  plan := separatedAction

def opaqueMethod :
    AuditMethod (opaquePresentation.behaviorQuestion)
      opaquePresentation.evidenceView Nat where
  decode trace := trace.second
  verifies := fun _ => rfl
  plan := interactingAction

def clearCapability := AuditorCapability.generated clearMethod

def opaqueCapability := AuditorCapability.generated opaqueMethod

def clearWeakest : WeakestPermittedMethod clearCapability :=
  AuditorCapability.generatedWeakest clearMethod

def opaqueWeakest : WeakestPermittedMethod opaqueCapability :=
  AuditorCapability.generatedWeakest opaqueMethod

def clearMinimumRank : AttainedMinimumRank clearCapability :=
  AuditorCapability.generatedMinimumRank clearMethod

def opaqueMinimumRank : AttainedMinimumRank opaqueCapability :=
  AuditorCapability.generatedMinimumRank opaqueMethod

theorem clear_attained_rank_zero :
    Action.rank clearMinimumRank.selected.method.plan = 0 :=
  rank_separatedAction

theorem opaque_attained_rank_one :
    Action.rank opaqueMinimumRank.selected.method.plan = 1 :=
  rank_interactingAction

/-- Extensionally identical behavior can have different attained verification
rank under explicitly different evidence presentations and auditor
capabilities. -/
theorem same_behavior_different_attained_rank :
    PresentedRealization.ExtensionallyEquivalent
        clearPresentation opaquePresentation /\
      Action.rank clearMinimumRank.selected.method.plan = 0 /\
      Action.rank opaqueMinimumRank.selected.method.plan = 1 :=
  ⟨presentations_extensionally_equivalent,
    clear_attained_rank_zero, opaque_attained_rank_one⟩

def constantView : AuditView Bool where
  View := Unit
  observe := fun _ => ()

/-- A constant view cannot answer the nonconstant behavior question. -/
theorem constant_not_sufficient_for_behavior :
    Not (Sufficient opaquePresentation.behaviorQuestion constantView) := by
  rintro ⟨decode, verifies⟩
  have atFalse := verifies false
  have atTrue := verifies true
  simp [constantView, PresentedRealization.behaviorQuestion,
    opaquePresentation] at atFalse atTrue
  exact Bool.false_ne_true (atFalse.symm.trans atTrue)

/-- The opaque capability admits only views from which its complete presented
trace can be recovered.  In particular it rejects the constant view. -/
theorem opaque_capability_rejects_constant_view :
    Not (exists method :
      AuditMethod opaquePresentation.behaviorQuestion constantView Nat,
      opaqueCapability.Permits method) := by
  rintro ⟨method, permitted⟩
  obtain ⟨forget, commutes⟩ := permitted.1
  have equal : opaquePresentation.evidenceView.observe false =
      opaquePresentation.evidenceView.observe true := by
    rw [<- commutes false, <- commutes true]
    rfl
  have firstEqual := congrArg FullTrace.first equal
  simp [PresentedRealization.evidenceView, opaquePresentation] at firstEqual

/-- Every method admitted by the opaque capability has a view that refines the
complete two-event evidence presentation. -/
theorem opaque_permitted_view_recovers_full_trace
    {view : AuditView Bool}
    (method : AuditMethod opaquePresentation.behaviorQuestion view Nat)
    (permitted : opaqueCapability.Permits method) :
    opaquePresentation.evidenceView <= view :=
  permitted.1

/-- Rank-zero verification does not manufacture third-party attestation.  The
clear behavior is realized by the existing exact identity build, while the
rejecting attestation discipline has no evidence inhabitant. -/
theorem rank_zero_does_not_imply_attestation :
    Action.rank clearMinimumRank.selected.method.plan = 0 /\
      (forall input,
        Nonempty
          (Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.identityBuild
            input (clearPresentation.behavior input))) /\
      Not (Nonempty
        (Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Attestation
          Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.rejectingAttestation)) := by
  refine ⟨clear_attained_rank_zero, ?_,
    Mettapedia.GSLT.ReproducibleBuild.HattaProfile.Canary.no_rejectingAttestation⟩
  intro input
  exact ⟨⟨rfl⟩⟩

/-- Even exact byte equality plus a low-rank audit presentation does not
supply Wheeler's semantic DDC premises. -/
theorem rank_zero_and_matching_bytes_do_not_supply_ddc_premises :
    Action.rank clearMinimumRank.selected.method.plan = 0 /\
      Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Matches
        Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.benignExperiment /\
      Not (Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.ProofOnePremises
        Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.rejectingCorrespondenceModel
        Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.benignExperiment) :=
  ⟨clear_attained_rank_zero,
    Mettapedia.GSLT.ReproducibleBuild.DiverseDoubleCompiling.Canary.matching_bytes_do_not_supply_proofOnePremises⟩

end Canary

end Mettapedia.GSLT.ReproducibleBuild.Legibility

#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.sufficient_of_le
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.AuditMethod.rank_chainProduct
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.AuditMethod.rank_coordinationProduct
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.AuditorCapability.hasMethodAtMostRank_mono
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.GSLTObserverRelativity.naturality_audit_classification_is_observer_relative
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.Canary.same_behavior_different_attained_rank
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.Canary.opaque_capability_rejects_constant_view
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.Canary.rank_zero_does_not_imply_attestation
#print axioms Mettapedia.GSLT.ReproducibleBuild.Legibility.Canary.rank_zero_and_matching_bytes_do_not_supply_ddc_premises
