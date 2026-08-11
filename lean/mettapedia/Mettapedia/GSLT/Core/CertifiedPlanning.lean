import Mettapedia.GSLT.Core.Composition
import Mathlib.Data.Finset.Basic

/-!
# Observation cells and finitely supported realization plans

`Realization` certifies one lowering against one named observation.  This
module adds the structure needed when several certified lowerings coexist.

* `ObservationRefinement` records an explicit loss of observable information.
* `ObservationCell` compares two lowering routes without identifying their
  artifacts or execution traces.
* `PartialRealization.withFallback` turns a conditionally admitted backend and
  a total reference backend into one total certified realization.
* `FinitelySupportedPlan` identifies the finite declaration cone on which a
  compiled choice depends.  Revisions outside that cone leave the choice
  unchanged.
* `PlannedRealization` packages request-indexed supported plans whose generated
  artifacts remain adequate at every implementation environment.

These definitions do not choose a universal abstract machine.  They specify
the certificate boundary shared by heterogeneous machines: optimize and
select freely, preserve the declared observation, and invalidate a plan only
when its finite support changes.

Finite support is a deliberately useful planning class, not a completeness or
necessity theorem about every possible compiler.  A realization with genuinely
infinite or dynamically discovered dependencies would require a broader
dependency contract; nothing here rules one out or identifies this interface
with a final architecture.
-/

namespace Mettapedia.GSLT

universe uBase uSource uPrefix uArtifactLeft uArtifactMiddle uArtifactRight
  uObservation uObservationMiddle uObservationCoarse uDeclaration uValue
  uOutput uState

/-! ## Observation refinement -/

/-- A typed projection from a finer observation to a coarser one.  The map is
retained as data because different quotients may forget different evidence
even when their source and target types coincide. -/
structure ObservationRefinement {Base : Type uBase}
    (Fine : Base → Type uObservation)
    (Coarse : Base → Type uObservationCoarse) where
  forget : ∀ base, Fine base → Coarse base

namespace ObservationRefinement

/-- Observing at the same precision changes nothing. -/
def identity {Base : Type uBase} {Observation : Base → Type uObservation} :
    ObservationRefinement Observation Observation where
  forget := fun _ observation => observation

/-- Successive losses of information compose in their declared order. -/
def trans {Base : Type uBase}
    {Fine : Base → Type uObservation}
    {Middle : Base → Type uObservationMiddle}
    {Coarse : Base → Type uObservationCoarse}
    (first : ObservationRefinement Fine Middle)
    (second : ObservationRefinement Middle Coarse) :
    ObservationRefinement Fine Coarse where
  forget := fun base observation => second.forget base (first.forget base observation)

/-- A certified realization remains certified after an explicitly named
observation quotient. -/
def mapRealization {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifactLeft}
    {Fine : Base → Type uObservation}
    {Coarse : Base → Type uObservationCoarse}
    (refinement : ObservationRefinement Fine Coarse)
    (realization : Realization Source Artifact Fine) :
    Realization Source Artifact Coarse :=
  realization.mapObservation refinement.forget

@[simp] theorem identity_forget {Base : Type uBase}
    {Observation : Base → Type uObservation}
    (base : Base) (observation : Observation base) :
    (identity : ObservationRefinement Observation Observation).forget
        base observation = observation :=
  rfl

@[simp] theorem trans_forget {Base : Type uBase}
    {Fine : Base → Type uObservation}
    {Middle : Base → Type uObservationMiddle}
    {Coarse : Base → Type uObservationCoarse}
    (first : ObservationRefinement Fine Middle)
    (second : ObservationRefinement Middle Coarse)
    (base : Base) (observation : Fine base) :
    (first.trans second).forget base observation =
      second.forget base (first.forget base observation) :=
  rfl

theorem trans_assoc {Base : Type uBase}
    {First : Base → Type uObservation}
    {Second : Base → Type uObservationMiddle}
    {Third : Base → Type uObservationCoarse}
    {Fourth : Base → Type uOutput}
    (first : ObservationRefinement First Second)
    (second : ObservationRefinement Second Third)
    (third : ObservationRefinement Third Fourth) :
    (first.trans second).trans third = first.trans (second.trans third) :=
  rfl

end ObservationRefinement

/-! ## Proof-relevant agreement between realization routes -/

/-- A semantic 2-cell between two certified realization routes.  Artifacts
may have unrelated types and traces; the cell compares exactly the observation
named by the two routes. -/
structure ObservationCell {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation) : Prop where
  compiled : ∀ base source,
    left.observeArtifact base (left.compile base source) =
      right.observeArtifact base (right.compile base source)

namespace ObservationCell

/-- Agreement of compiled observations is equivalent to agreement of the
source observations named by adequate realizations. -/
theorem sourceAgreement {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    {left : Realization Source LeftArtifact Observation}
    {right : Realization Source RightArtifact Observation}
    (cell : ObservationCell left right) (base : Base) (source : Source base) :
    left.observeSource base source = right.observeSource base source := by
  rw [← left.adequate base source, ← right.adequate base source]
  exact cell.compiled base source

/-- Two adequate realizations with the same source observation admit a
canonical semantic comparison. -/
def ofSourceAgreement {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation)
    (agreement : ∀ base source,
      left.observeSource base source = right.observeSource base source) :
    ObservationCell left right where
  compiled := by
    intro base source
    rw [left.adequate, right.adequate]
    exact agreement base source

/-- Identity 2-cell. -/
def refl {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifactLeft}
    {Observation : Base → Type uObservation}
    (realization : Realization Source Artifact Observation) :
    ObservationCell realization realization where
  compiled := by intros; rfl

/-- Reverse a semantic comparison. -/
def symm {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    {left : Realization Source LeftArtifact Observation}
    {right : Realization Source RightArtifact Observation}
    (cell : ObservationCell left right) : ObservationCell right left where
  compiled := fun base source => (cell.compiled base source).symm

/-- Vertical composition of semantic comparisons. -/
def trans {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {MiddleArtifact : Base → Type uArtifactMiddle}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    {left : Realization Source LeftArtifact Observation}
    {middle : Realization Source MiddleArtifact Observation}
    {right : Realization Source RightArtifact Observation}
    (first : ObservationCell left middle)
    (second : ObservationCell middle right) : ObservationCell left right where
  compiled := fun base source =>
    (first.compiled base source).trans (second.compiled base source)

/-- Precomposition by the same certified stage preserves a 2-cell. -/
def precompose {Base : Type uBase}
    {PrefixSource : Base → Type uPrefix}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (earlier : Realization PrefixSource Source Observation)
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation)
    (leftAgreement : ∀ base source,
      left.observeSource base source = earlier.observeArtifact base source)
    (rightAgreement : ∀ base source,
      right.observeSource base source = earlier.observeArtifact base source)
    (cell : ObservationCell left right) :
    ObservationCell (earlier.trans left leftAgreement)
      (earlier.trans right rightAgreement) where
  compiled := fun base source => cell.compiled base (earlier.compile base source)

/-- Postcomposition by separately certified lowering stages preserves a
2-cell when each shared boundary names the same observation. -/
def postcompose {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftFinal : Base → Type uPrefix}
    {RightFinal : Base → Type uArtifactMiddle}
    {Observation : Base → Type uObservation}
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation)
    (leftLower : Realization LeftArtifact LeftFinal Observation)
    (rightLower : Realization RightArtifact RightFinal Observation)
    (leftAgreement : ∀ base artifact,
      leftLower.observeSource base artifact =
        left.observeArtifact base artifact)
    (rightAgreement : ∀ base artifact,
      rightLower.observeSource base artifact =
        right.observeArtifact base artifact)
    (cell : ObservationCell left right) :
    ObservationCell (left.trans leftLower leftAgreement)
      (right.trans rightLower rightAgreement) where
  compiled := by
    intro base source
    change leftLower.observeArtifact base
          (leftLower.compile base (left.compile base source)) =
        rightLower.observeArtifact base
          (rightLower.compile base (right.compile base source))
    rw [leftLower.adequate, rightLower.adequate,
      leftAgreement, rightAgreement]
    exact cell.compiled base source

/-- Whiskering by an observation quotient preserves route agreement while
making the information loss explicit. -/
def mapObservation {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Fine : Base → Type uObservation}
    {Coarse : Base → Type uObservationCoarse}
    (left : Realization Source LeftArtifact Fine)
    (right : Realization Source RightArtifact Fine)
    (cell : ObservationCell left right)
    (refinement : ObservationRefinement Fine Coarse) :
    ObservationCell (refinement.mapRealization left)
      (refinement.mapRealization right) where
  compiled := by
    intro base source
    exact congrArg (refinement.forget base) (cell.compiled base source)

/-- A hybrid backend selected from two adequate realizations remains joined to
the left route by a semantic 2-cell. -/
def selectToLeft {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation)
    (agreement : ∀ base source,
      right.observeSource base source = left.observeSource base source)
    (choose : ∀ base, Source base → Bool) :
    ObservationCell (left.select right agreement choose) left :=
  ofSourceAgreement _ _ (by intros; rfl)

/-- The same hybrid selection remains joined to the right route.  Thus
backend choice is a two-dimensional comparison, not a new semantic root. -/
def selectToRight {Base : Type uBase}
    {Source : Base → Type uSource}
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source LeftArtifact Observation)
    (right : Realization Source RightArtifact Observation)
    (agreement : ∀ base source,
      right.observeSource base source = left.observeSource base source)
    (choose : ∀ base, Source base → Bool) :
    ObservationCell (left.select right agreement choose) right :=
  ofSourceAgreement _ _ (by
    intro base source
    exact (agreement base source).symm)

end ObservationCell

/-! ## Proof-producing compilation traces

A compiler trace is a path through one language-visible state carrier.  Source
documents, admitted declarations, plans, and serialized artifacts should be
constructors of that carrier rather than private phases known only to the
compiler.  The certificate producer is untrusted: only the independent
checker and its soundness theorem authorize a transition.

This interface deliberately does not prescribe a wire format or a fixed list
of stages.  A concrete V1 pipeline may use four stages; later compilers may
refine or replace them without changing the trace theorem. -/

/-- An independent checker for one compiler-state transition.  Evidence is
ordinary untrusted data.  Acceptance proves preservation of the explicitly
named observation; rejection proves only that this evidence did not establish
the transition. -/
structure CompilationTraceChecker (State : Type uState)
    (Observation : Type uObservation) where
  Evidence : State → State → Type uState
  check : ∀ source target, Evidence source target → Bool
  observe : State → Observation
  sound : ∀ {source target} (evidence : Evidence source target),
    check source target evidence = true →
      observe target = observe source

namespace CompilationTraceChecker

variable {State : Type uState} {Observation : Type uObservation}
    (checker : CompilationTraceChecker State Observation)

/-- A linked, finite trace.  Its endpoints are indexed so a producer cannot
silently omit the connection between adjacent stages.  Individual evidence
items remain untrusted until `check` accepts them. -/
inductive Trace : State → State → Type uState where
  | refl (state : State) : Trace state state
  | step {source middle target : State}
      (evidence : checker.Evidence source middle)
      (tail : Trace middle target) : Trace source target

namespace Trace

/-- Replay every local certificate in order. -/
def check : {source target : State} → checker.Trace source target → Bool
  | _, _, .refl _ => true
  | _, _, .step evidence tail =>
      checker.check _ _ evidence && tail.check

@[simp] theorem check_refl (state : State) :
    (Trace.refl state : checker.Trace state state).check = true :=
  rfl

@[simp] theorem check_step {source middle target : State}
    (evidence : checker.Evidence source middle)
    (tail : checker.Trace middle target) :
    (Trace.step evidence tail).check =
      (checker.check source middle evidence && tail.check) :=
  rfl

/-- An accepted trace preserves the named observation from its first state to
its last state. -/
theorem observation_preserved {source target : State}
    (trace : checker.Trace source target) (accepted : trace.check = true) :
    checker.observe target = checker.observe source := by
  induction trace with
  | refl state => rfl
  | @step source middle target evidence tail inductionHypothesis =>
      simp only [check, Bool.and_eq_true] at accepted
      exact (inductionHypothesis accepted.2).trans
        (checker.sound evidence accepted.1)

end Trace

/-- The GSLT induced by independently accepted compiler transitions.  This is
the trace theory itself, not yet a claim that a particular native compiler
implements an authored language semantics. -/
def toGSLT : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    ∃ evidence : checker.Evidence source target,
      checker.check source target evidence = true
  rewrites_resp_left := by
    intro source source' target equal step
    cases equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    cases equal
    exact step

namespace Trace

/-- Successful replay supplies exactly a path in the checker-induced trace
theory. -/
theorem toMultiStep {source target : State}
    (trace : checker.Trace source target) (accepted : trace.check = true) :
    checker.toGSLT.MultiStep source target := by
  induction trace with
  | refl state =>
      exact @GSLT.MultiStep.refl checker.toGSLT state
  | @step source middle target evidence tail inductionHypothesis =>
      simp only [check, Bool.and_eq_true] at accepted
      exact @GSLT.MultiStep.step checker.toGSLT source middle target
        ⟨evidence, accepted.1⟩ (inductionHypothesis accepted.2)

end Trace

/-- A trace together with successful independent replay. -/
structure AcceptedTrace (checker : CompilationTraceChecker State Observation)
    (source target : State) where
  trace : Trace checker source target
  accepted : trace.check = true

namespace AcceptedTrace

/-- Every accepted trace is a path in the checker-induced GSLT. -/
theorem toMultiStep {source target : State}
    (trace : AcceptedTrace checker source target) :
    checker.toGSLT.MultiStep source target :=
  Trace.toMultiStep checker trace.trace trace.accepted

/-- Accepted trace endpoints preserve the checker's named observation. -/
theorem observation_preserved {source target : State}
    (trace : AcceptedTrace checker source target) :
    checker.observe target = checker.observe source :=
  Trace.observation_preserved checker trace.trace trace.accepted

end AcceptedTrace

/-- A proof-producing compiler emits an accepted trace from each input to the
artifact it selects.  The checker remains absent from the ordinary compile
function. -/
structure ProofProducingCompilation
    (checker : CompilationTraceChecker State Observation) where
  compile : State → State
  certificate : ∀ source, Trace checker source (compile source)
  accepted : ∀ source, (certificate source).check = true

namespace ProofProducingCompilation

/-- Forget certificate production and obtain the ordinary certified
realization. -/
def toRealization (compiler : ProofProducingCompilation checker) :
    SimpleRealization State State Observation where
  compile := fun _ source => compiler.compile source
  observeSource := fun _ source => checker.observe source
  observeArtifact := fun _ artifact => checker.observe artifact
  adequate := by
    intro _ source
    exact Trace.observation_preserved checker (compiler.certificate source)
      (compiler.accepted source)

/-- Certification erasure leaves the compiler itself definitionally
unchanged.  Normal execution need not invoke the checker or retain evidence. -/
@[simp] theorem toRealization_compile
    (compiler : ProofProducingCompilation checker) (source : State) :
    compiler.toRealization.compile () source = compiler.compile source :=
  rfl

end ProofProducingCompilation

end CompilationTraceChecker

/-! ### Positive and negative trace canaries -/

namespace CompilationTraceCanary

open CompilationTraceChecker

/-- One carrier containing all stages of a small four-pass compiler. -/
inductive State where
  | authored (payload : Nat)
  | selected (payload : Nat)
  | admitted (payload : Nat)
  | planned (payload : Nat)
  | serialized (payload : Nat)
deriving DecidableEq, Repr

inductive Stage where
  | sourceSelection
  | sourceAdmission
  | planCompilation
  | artifactSerialization
deriving DecidableEq, Repr

/-- Raw evidence may lie about either the stage or the payload. -/
structure Evidence where
  stage : Stage
  claimedPayload : Nat
deriving DecidableEq, Repr

def observe : State → Nat
  | .authored payload
  | .selected payload
  | .admitted payload
  | .planned payload
  | .serialized payload => payload

def checkEvidence (source target : State) (evidence : Evidence) : Bool :=
  match source, target, evidence.stage with
  | .authored sourcePayload, .selected targetPayload,
      .sourceSelection =>
        decide (sourcePayload = targetPayload ∧
          evidence.claimedPayload = sourcePayload)
  | .selected sourcePayload, .admitted targetPayload,
      .sourceAdmission =>
        decide (sourcePayload = targetPayload ∧
          evidence.claimedPayload = sourcePayload)
  | .admitted sourcePayload, .planned targetPayload,
      .planCompilation =>
        decide (sourcePayload = targetPayload ∧
          evidence.claimedPayload = sourcePayload)
  | .planned sourcePayload, .serialized targetPayload,
      .artifactSerialization =>
        decide (sourcePayload = targetPayload ∧
          evidence.claimedPayload = sourcePayload)
  | _, _, _ => false

def checker : CompilationTraceChecker State Nat where
  Evidence := fun _ _ => Evidence
  check := checkEvidence
  observe := observe
  sound := by
    intro source target evidence accepted
    rcases evidence with ⟨stage, claimedPayload⟩
    cases source <;> cases target <;> cases stage <;>
      simp_all [checkEvidence, observe]

def goodTrace : checker.Trace (.authored 7) (.serialized 7) :=
  Trace.step (checker := checker) (source := State.authored 7)
    (middle := State.selected 7)
    ({ stage := .sourceSelection, claimedPayload := 7 } : Evidence)
    (Trace.step (checker := checker) (source := State.selected 7)
      (middle := State.admitted 7)
      ({ stage := .sourceAdmission, claimedPayload := 7 } : Evidence)
      (Trace.step (checker := checker) (source := State.admitted 7)
        (middle := State.planned 7)
        ({ stage := .planCompilation, claimedPayload := 7 } : Evidence)
        (Trace.step (checker := checker) (source := State.planned 7)
          (middle := State.serialized 7)
          ({ stage := .artifactSerialization, claimedPayload := 7 } : Evidence)
          (.refl _))))

/-- Positive: all four linked stages replay successfully. -/
theorem goodTrace_accepted : goodTrace.check = true := by
  decide

/-- Positive: the accepted trace is a four-step path in its induced GSLT. -/
theorem goodTrace_reachable :
    checker.toGSLT.MultiStep (.authored 7) (.serialized 7) :=
  (⟨goodTrace, goodTrace_accepted⟩ :
    AcceptedTrace checker (.authored 7) (.serialized 7)).toMultiStep

def payloadTamperTrace : checker.Trace (.authored 7) (.serialized 8) :=
  Trace.step (checker := checker) (source := State.authored 7)
    (middle := State.selected 8)
    ({ stage := .sourceSelection, claimedPayload := 7 } : Evidence)
    (Trace.step (checker := checker) (source := State.selected 8)
      (middle := State.admitted 8)
      ({ stage := .sourceAdmission, claimedPayload := 8 } : Evidence)
      (Trace.step (checker := checker) (source := State.admitted 8)
        (middle := State.planned 8)
        ({ stage := .planCompilation, claimedPayload := 8 } : Evidence)
        (Trace.step (checker := checker) (source := State.planned 8)
          (middle := State.serialized 8)
          ({ stage := .artifactSerialization, claimedPayload := 8 } : Evidence)
          (.refl _))))

/-- Negative: changing the selected payload rejects at the first pass. -/
theorem payloadTamperTrace_rejected : payloadTamperTrace.check = false := by
  decide

/-- Negative: no alternative accepted evidence can launder a changed final
observation through this checker. -/
theorem noAcceptedPayloadTamper :
    ¬ Nonempty (AcceptedTrace checker (.authored 7) (.serialized 8)) := by
  rintro ⟨trace⟩
  have preserved := trace.observation_preserved
  simp [checker, observe] at preserved

end CompilationTraceCanary

/-! ## Conditionally admitted realizations with certified fallback -/

/-- A backend whose compiler is available only when its explicit admission
test succeeds.  The proof passed to `compile` prevents rejected requests from
entering the backend accidentally. -/
structure PartialRealization {Base : Type uBase}
    (Source : Base → Type uSource)
    (Artifact : Base → Type uArtifactLeft)
    (Observation : Base → Type uObservation) where
  accepts : ∀ base, Source base → Bool
  compile : ∀ base source, accepts base source = true → Artifact base
  observeSource : ∀ base, Source base → Observation base
  observeArtifact : ∀ base, Artifact base → Observation base
  adequate : ∀ base source accepted,
    observeArtifact base (compile base source accepted) =
      observeSource base source

namespace PartialRealization

/-- Restrict a total certified backend by an explicit admission predicate. -/
def ofRealization {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifactLeft}
    {Observation : Base → Type uObservation}
    (realization : Realization Source Artifact Observation)
    (accepts : ∀ base, Source base → Bool) :
    PartialRealization Source Artifact Observation where
  accepts := accepts
  compile := fun base source _ => realization.compile base source
  observeSource := realization.observeSource
  observeArtifact := realization.observeArtifact
  adequate := fun base source _ => realization.adequate base source

/-- A partial backend plus a total reference backend gives a total certified
realization.  Rejection is a typed branch to the fallback, not an error or an
unchecked retry. -/
def withFallback {Base : Type uBase}
    {Source : Base → Type uSource}
    {FastArtifact : Base → Type uArtifactLeft}
    {FallbackArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (fast : PartialRealization Source FastArtifact Observation)
    (fallback : Realization Source FallbackArtifact Observation)
    (agreement : ∀ base source,
      fallback.observeSource base source = fast.observeSource base source) :
    Realization Source (fun base => FastArtifact base ⊕ FallbackArtifact base)
      Observation where
  compile := fun base source =>
    if accepted : fast.accepts base source = true then
      .inl (fast.compile base source accepted)
    else
      .inr (fallback.compile base source)
  observeSource := fast.observeSource
  observeArtifact := fun base => Sum.elim
    (fast.observeArtifact base) (fallback.observeArtifact base)
  adequate := by
    intro base source
    split
    next accepted =>
      exact fast.adequate base source accepted
    next _ =>
      change fallback.observeArtifact base (fallback.compile base source) =
        fast.observeSource base source
      rw [fallback.adequate, agreement]

theorem withFallback_compile_fast {Base : Type uBase}
    {Source : Base → Type uSource}
    {FastArtifact : Base → Type uArtifactLeft}
    {FallbackArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (fast : PartialRealization Source FastArtifact Observation)
    (fallback : Realization Source FallbackArtifact Observation)
    (agreement : ∀ base source,
      fallback.observeSource base source = fast.observeSource base source)
    (base : Base) (source : Source base)
    (accepted : fast.accepts base source = true) :
    (fast.withFallback fallback agreement).compile base source =
      .inl (fast.compile base source accepted) := by
  simp only [withFallback, dif_pos accepted]

theorem withFallback_compile_fallback {Base : Type uBase}
    {Source : Base → Type uSource}
    {FastArtifact : Base → Type uArtifactLeft}
    {FallbackArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (fast : PartialRealization Source FastArtifact Observation)
    (fallback : Realization Source FallbackArtifact Observation)
    (agreement : ∀ base source,
      fallback.observeSource base source = fast.observeSource base source)
    (base : Base) (source : Source base)
    (rejected : fast.accepts base source ≠ true) :
    (fast.withFallback fallback agreement).compile base source =
      .inr (fallback.compile base source) := by
  simp only [withFallback, dif_neg rejected]

/-- The total fallback assembly is semantically joined to its reference
backend for every request, including requests admitted by the fast path. -/
def withFallbackToReferenceCell {Base : Type uBase}
    {Source : Base → Type uSource}
    {FastArtifact : Base → Type uArtifactLeft}
    {FallbackArtifact : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (fast : PartialRealization Source FastArtifact Observation)
    (fallback : Realization Source FallbackArtifact Observation)
    (agreement : ∀ base source,
      fallback.observeSource base source = fast.observeSource base source) :
    ObservationCell (fast.withFallback fallback agreement) fallback :=
  ObservationCell.ofSourceAgreement _ _ (by
    intro base source
    exact (agreement base source).symm)

end PartialRealization

/-! ## Finite authority cones for generated plans -/

/-- Two implementation environments agree on a plan's declared dependency
cone. -/
def AgreesOn {Declaration : Type uDeclaration} {Value : Type uValue}
    (support : Finset Declaration)
    (first second : Declaration → Value) : Prop :=
  ∀ declaration ∈ support, first declaration = second declaration

/-- A revision changes no declaration outside the named finite set. -/
def ChangesOnlyAt {Declaration : Type uDeclaration} {Value : Type uValue}
    (changed : Finset Declaration)
    (first second : Declaration → Value) : Prop :=
  ∀ declaration, declaration ∉ changed →
    first declaration = second declaration

/-- An executable plan together with the finite declaration cone sufficient
to determine it.  `stable` is the cache-validity certificate implementations
must produce; it is not inferred from a global revision number. -/
structure FinitelySupportedPlan (Declaration : Type uDeclaration)
    [DecidableEq Declaration] (Value : Type uValue) (Output : Type uOutput) where
  support : Finset Declaration
  run : (Declaration → Value) → Output
  stable : ∀ {first second}, AgreesOn support first second →
    run first = run second

namespace FinitelySupportedPlan

variable {Declaration : Type uDeclaration} [DecidableEq Declaration]
  {Value : Type uValue} {Output : Type uOutput}

/-- A constant plan depends on no declarations. -/
def constant (output : Output) :
    FinitelySupportedPlan Declaration Value Output where
  support := ∅
  run := fun _ => output
  stable := by intros; rfl

/-- Reading one declaration records exactly that singleton dependency. -/
def read (declaration : Declaration) :
    FinitelySupportedPlan Declaration Value Value where
  support := {declaration}
  run := fun environment => environment declaration
  stable := by
    intro first second agreement
    exact agreement declaration (by simp)

/-- Pure result transformation does not enlarge a plan's authority cone. -/
def map {Mapped : Type uObservationMiddle}
    (plan : FinitelySupportedPlan Declaration Value Output)
    (transform : Output → Mapped) :
    FinitelySupportedPlan Declaration Value Mapped where
  support := plan.support
  run := fun environment => transform (plan.run environment)
  stable := by
    intro first second agreement
    exact congrArg transform (plan.stable agreement)

/-- Combining independently planned results depends on the union of their
finite cones. -/
def combine {Right : Type uArtifactRight} {Combined : Type uObservationMiddle}
    (left : FinitelySupportedPlan Declaration Value Output)
    (right : FinitelySupportedPlan Declaration Value Right)
    (merge : Output → Right → Combined) :
    FinitelySupportedPlan Declaration Value Combined where
  support := left.support ∪ right.support
  run := fun environment => merge (left.run environment) (right.run environment)
  stable := by
    intro first second agreement
    have leftAgreement : AgreesOn left.support first second := by
      intro declaration member
      exact agreement declaration (Finset.mem_union_left _ member)
    have rightAgreement : AgreesOn right.support first second := by
      intro declaration member
      exact agreement declaration (Finset.mem_union_right _ member)
    rw [left.stable leftAgreement, right.stable rightAgreement]

/-- A revision disjoint from the authority cone leaves the plan result
unchanged. -/
theorem stable_of_changesOnlyAt
    (plan : FinitelySupportedPlan Declaration Value Output)
    {changed : Finset Declaration} {first second : Declaration → Value}
    (changes : ChangesOnlyAt changed first second)
    (disjoint : Disjoint plan.support changed) :
    plan.run first = plan.run second := by
  apply plan.stable
  intro declaration supported
  apply changes declaration
  intro changedMember
  exact Finset.disjoint_left.mp disjoint supported changedMember

@[simp] theorem constant_run (output : Output)
    (environment : Declaration → Value) :
    (constant (Declaration := Declaration) (Value := Value) output).run
        environment = output :=
  rfl

@[simp] theorem read_run (declaration : Declaration)
    (environment : Declaration → Value) :
    (read (Value := Value) declaration).run environment =
      environment declaration :=
  rfl

end FinitelySupportedPlan

/-! ## Request-indexed planned realizations -/

/-- A realization generated from a request-indexed finite-support plan.  Every
implementation environment may alter the artifact, but the declared semantic
observation is invariant. -/
structure PlannedRealization {Declaration : Type uDeclaration}
    [DecidableEq Declaration] (Value : Type uValue)
    {Base : Type uBase}
    (Source : Base → Type uSource)
    (Artifact : Base → Type uArtifactLeft)
    (Observation : Base → Type uObservation) where
  plan : ∀ base, Source base →
    FinitelySupportedPlan Declaration Value (Artifact base)
  observeSource : ∀ base, Source base → Observation base
  observeArtifact : ∀ base, Artifact base → Observation base
  adequate : ∀ base source environment,
    observeArtifact base ((plan base source).run environment) =
      observeSource base source

namespace PlannedRealization

variable {Declaration : Type uDeclaration} [DecidableEq Declaration]
  {Value : Type uValue} {Base : Type uBase}
  {Source : Base → Type uSource}
  {Artifact : Base → Type uArtifactLeft}
  {Observation : Base → Type uObservation}

/-- Freeze one implementation environment to obtain an ordinary certified
realization. -/
def freeze (planned : PlannedRealization (Declaration := Declaration)
      Value Source Artifact Observation)
    (environment : Declaration → Value) :
    Realization Source Artifact Observation where
  compile := fun base source => (planned.plan base source).run environment
  observeSource := planned.observeSource
  observeArtifact := planned.observeArtifact
  adequate := fun base source => planned.adequate base source environment

/-- Changing only declarations outside a request's support preserves its
compiled artifact exactly, so cached artifacts remain reusable. -/
theorem compile_stable_of_changesOnlyAt
    (planned : PlannedRealization (Declaration := Declaration)
      Value Source Artifact Observation)
    (base : Base) (source : Source base)
    {changed : Finset Declaration}
    {first second : Declaration → Value}
    (changes : ChangesOnlyAt changed first second)
    (disjoint : Disjoint (planned.plan base source).support changed) :
    (planned.freeze first).compile base source =
      (planned.freeze second).compile base source :=
  (planned.plan base source).stable_of_changesOnlyAt changes disjoint

end PlannedRealization

/-! ## Canaries for finite support -/

namespace CertifiedPlanningCanary

/-- A real one-declaration dependency. -/
def readTrue : FinitelySupportedPlan Bool Bool Bool :=
  FinitelySupportedPlan.read true

/-- Positive: changing only the unrelated declaration leaves the plan result
unchanged. -/
theorem readTrue_stable_under_false_change :
    readTrue.run (fun value => value) =
      readTrue.run (fun _ => true) := by
  apply readTrue.stable_of_changesOnlyAt (changed := {false})
  · intro declaration notChanged
    cases declaration <;> simp_all
  · decide

/-- Negative: the plan that reads `true` cannot honestly claim empty support.
The counterexample changes the read declaration while agreeing everywhere in
the alleged empty cone. -/
theorem readTrue_has_no_empty_support_certificate :
    ¬ ∃ plan : FinitelySupportedPlan Bool Bool Bool,
      plan.support = ∅ ∧
        ∀ environment, plan.run environment = environment true := by
  rintro ⟨plan, emptySupport, computes⟩
  let allFalse : Bool → Bool := fun _ => false
  let identity : Bool → Bool := fun value => value
  have agreement : AgreesOn plan.support allFalse identity := by
    intro declaration member
    rw [emptySupport] at member
    simp at member
  have stable := plan.stable agreement
  rw [computes allFalse, computes identity] at stable
  change false = true at stable
  exact Bool.noConfusion stable

end CertifiedPlanningCanary

end Mettapedia.GSLT
