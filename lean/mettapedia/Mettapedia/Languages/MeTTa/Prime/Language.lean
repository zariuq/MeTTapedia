import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.Prime.UniversalName
import Mettapedia.Languages.MeTTa.PrimeNeedWorlds
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedProfile
import Mettapedia.GSLT.LanguageDef.CalculusExtension

/-!
# The Prime language nucleus

Prime is a lazy reflective MeTTa language, not a proof calculus and not a
particular abstract machine.  This module isolates a modular semantic nucleus:

* a selected occurrence source faithfully hosted by an operational base;
* an independently selected revision-keyed call-by-need layer; and
* structural quotation and drop.

Today's query-first implementation additionally supplies finite causal
receipts.  That source-specific evidence layer is kept separate from the
generic Prime assembly.

The three components form one GSLT by composition inside `(T,E,R)`.  Unlike a
mere coproduct, the composite contains explicit crossings: an occurrence
request may enter the Need component, a Need answer may return to the selected
base observation, and evaluation of quoted syntax enters that same Need route.
Both the direct semantic step and the lazy route remain visible.  The selected
base nevertheless embeds faithfully because no crossing invents a new rewrite
with two base endpoints.

Need reduction is not a second evaluator: its steps are exactly the selected
occurrence steps decorated with a stable revision key.  At the current
query-first point, every such step additionally admits a finite causal
explanation.  `kernelElaboration` assigns every base, Need, and reflection
state its complete occurrence-bag meaning and proves that all internal and
cross rewrites preserve it.  Quotation exposes semantic syntax, never host
continuations or heap addresses.

Certificate-GSLT authoring is composed separately at the end of the module.  This is
intentional: a Prime point can host many proof calculi, while the selected
base and lazy reflective layer remain explicit parameters.  Runtime scheduling
and compilation likewise belong to certified realizations rather than to the
language nucleus.
-/

namespace Mettapedia.Languages.MeTTa.Prime.Language

open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.Dynamics.OperationalRegion
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.Prime.UniversalName
open Mettapedia.Languages.MeTTa.PrimeNeedWorlds
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## A modular Prime assembly -/

/-- Revision identity is an independently selected layer over a host's space.
Two extensionally equal spaces may still belong to different theory revisions
and must not share cached Need cells. -/
structure RevisionAuthority (Space : Type) where
  Revision : Type
  revisionDecidableEq : DecidableEq Revision
  revision : Space → Revision

attribute [instance] RevisionAuthority.revisionDecidableEq

/-- A Prime assembly selects an operational base point, its total bag
observation, and a revision authority.  It does not inherit from, or require,
the current query-first Zero implementation. -/
structure Model where
  base : OccurrencePoint Pattern Pattern
  observation : OccurrencePoint.BagObservation base
  revisionAuthority : RevisionAuthority base.Space

abbrev Model.Space (model : Model) := model.base.Space
abbrev Model.Revision (model : Model) := model.revisionAuthority.Revision
abbrev Model.revision (model : Model) : model.Space → model.Revision :=
  model.revisionAuthority.revision

instance (model : Model) : DecidableEq model.Revision :=
  model.revisionAuthority.revisionDecidableEq

/-- The current query-first implementation data.  It is kept separate from
the Prime assembly so source-specific causal receipts do not constrain the
admissible operational region. -/
structure QueryFirstModel where
  zero : MeTTaZero.Model
  revisionAuthority : RevisionAuthority zero.Space

abbrev QueryFirstModel.Space (model : QueryFirstModel) := model.zero.Space
abbrev QueryFirstModel.Revision (model : QueryFirstModel) :=
  model.revisionAuthority.Revision
abbrev QueryFirstModel.revision (model : QueryFirstModel) :
    model.Space → model.Revision := model.revisionAuthority.revision

instance (model : QueryFirstModel) : DecidableEq model.Revision :=
  model.revisionAuthority.revisionDecidableEq

/-- Select today's query-first Zero point and its bag observation as one Prime
base assembly. -/
def QueryFirstModel.toPrimeModel (model : QueryFirstModel) : Model where
  base := MeTTaZero.currentOperationalPoint model.zero
  observation := MeTTaZero.currentBagObservation model.zero
  revisionAuthority := model.revisionAuthority

/-- A Need cell is identified by the exact theory revision and demanded
subject.  Allocation lineage and generation are supplied by a realization of
the reference Need machine; this key is the stable language-level origin. -/
abbrev NeedKey (model : Model) := model.Revision × Pattern

def needKey (model : Model) (space : model.Space) (subject : Pattern) :
    NeedKey model :=
  (model.revision space, subject)

/-- The current revision policy as an independent keying component. -/
def needRevisionKeying (model : Model) :
    RevisionKeying model.Space Pattern where
  Key := NeedKey model
  key := needKey model

@[simp] theorem needKey_fst (model : Model) (space : model.Space)
    (subject : Pattern) :
    (needKey model space subject).1 = model.revision space :=
  rfl

@[simp] theorem needKey_snd (model : Model) (space : model.Space)
    (subject : Pattern) :
    (needKey model space subject).2 = subject :=
  rfl

/-- Revision changes invalidate Need identity even when the demanded syntax is
unchanged. -/
theorem needKey_ne_of_revision_ne (model : Model)
    {first second : model.Space} (subject : Pattern)
    (different : model.revision first ≠ model.revision second) :
    needKey model first subject ≠ needKey model second subject := by
  intro equal
  exact different (congrArg Prod.fst equal)

/-! ## Current query-first causal answer receipts -/

/-- Language-level dependencies recorded by a Prime answer.  A returned value
depends on its requested Need key and on exactly one immediate cause: a stored
space atom, a grounded capability result, or the open-world inert default. -/
inductive Dependency (model : QueryFirstModel) where
  | request (key : NeedKey model.toPrimeModel)
  | spaceAtom (key : NeedKey model.toPrimeModel) (atom : Pattern)
  | capability (key : NeedKey model.toPrimeModel) (result : Pattern)
  | inert (key : NeedKey model.toPrimeModel)
deriving DecidableEq

/-- The causal support of an immediate answer cause includes the request that
made it relevant.  Closing a receipt therefore restores demand provenance
without storing the request redundantly in every root set. -/
def dependencyBasis (model : QueryFirstModel) :
    PrimeNeedWorlds.FiniteCausalBasis (Dependency model) where
  support
    | .request key => {.request key}
    | .spaceAtom key atom => {.request key, .spaceAtom key atom}
    | .capability key result => {.request key, .capability key result}
    | .inert key => {.request key, .inert key}
  self_mem := by
    intro event
    cases event <;> simp
  hereditary := by
    intro event predecessor predecessorMember
    cases event <;> simp at predecessorMember ⊢
    all_goals rcases predecessorMember with rfl | rfl <;> simp

/-- A proof-relevant immediate cause for one Zero evaluation result. -/
inductive Cause (model : QueryFirstModel) (space : model.Space)
    (subject result : Pattern) :
    Type where
  | equation
      (candidate left right : Pattern) (bindings : Bindings)
      (candidateMember : candidate ∈ queryAll model.zero space)
      (equationView : viewEquation? candidate = some (left, right))
      (matching : bindings ∈ model.zero.matchAtoms left subject)
      (instantiates : applyBindings bindings right = result) :
      Cause model space subject result
  | capability
      (member : result ∈ model.zero.groundApply subject) :
      Cause model space subject result
  | inert
      (unknown : interpretedResults model.zero space subject = 0)
      (unchanged : result = subject) :
      Cause model space subject result

/-- Every authored immediate cause is sound for the exact occurrence bag. -/
theorem cause_mem_evaluateOne (model : QueryFirstModel) (space : model.Space)
    (subject result : Pattern) (cause : Cause model space subject result) :
    result ∈ evaluateOne model.zero space subject := by
  cases cause with
  | equation candidate left right bindings candidateMember equationView
      matching instantiates =>
      have equationMember :
          result ∈ equationResults model.zero space subject :=
        (mem_equationResults_iff model.zero space subject result).2
          ⟨candidate, candidateMember, left, right, equationView,
            bindings, matching, instantiates⟩
      have interpreted :
          result ∈ interpretedResults model.zero space subject :=
        Multiset.mem_add.mpr (Or.inl equationMember)
      have nonempty :
          interpretedResults model.zero space subject ≠ 0 := by
        intro empty
        rw [empty] at interpreted
        exact (Multiset.notMem_zero result) interpreted
      rw [evaluateOne_of_interpreted model.zero space subject nonempty]
      exact interpreted
  | capability member =>
      have interpreted :
          result ∈ interpretedResults model.zero space subject :=
        Multiset.mem_add.mpr (Or.inr member)
      have nonempty :
          interpretedResults model.zero space subject ≠ 0 := by
        intro empty
        rw [empty] at interpreted
        exact (Multiset.notMem_zero result) interpreted
      rw [evaluateOne_of_interpreted model.zero space subject nonempty]
      exact interpreted
  | inert unknown unchanged =>
      simp [evaluateOne, unknown, unchanged]

/-- Every result returned by query-derived Zero evaluation has a finite Prime
cause.  This is the semantic bridge from evaluation to receipts. -/
theorem exists_cause_of_mem_evaluateOne (model : QueryFirstModel)
    (space : model.Space) (subject result : Pattern)
    (member : result ∈ evaluateOne model.zero space subject) :
    Nonempty (Cause model space subject result) := by
  by_cases unknown : interpretedResults model.zero space subject = 0
  · have unchanged : result = subject := by
      simpa [evaluateOne, unknown] using member
    exact ⟨.inert unknown unchanged⟩
  · have interpreted :
        result ∈ interpretedResults model.zero space subject := by
      simpa [evaluateOne, unknown] using member
    rcases Multiset.mem_add.mp interpreted with equationMember | capabilityMember
    · rw [mem_equationResults_iff] at equationMember
      rcases equationMember with
        ⟨candidate, candidateMember, left, right, equationView,
          bindings, matching, instantiates⟩
      exact ⟨.equation candidate left right bindings candidateMember
        equationView matching instantiates⟩
    · exact ⟨.capability capabilityMember⟩

/-- Today's query-derived Zero evaluator supplies one causal layer over the
generic occurrence point. Future evaluators may supply a different evidence
family without changing revision decoration. -/
def evaluationCausalOccurrenceSource (model : QueryFirstModel) :
    CausalOccurrenceSource
      (MeTTaZero.evaluationOccurrenceSource model.zero) where
  Cause := Cause model
  sound := cause_mem_evaluateOne model _ _ _
  complete := exists_cause_of_mem_evaluateOne model

namespace Cause

/-- The single direct dependency recorded for a cause.  Transitive demand
support is recovered through `dependencyBasis.close`. -/
def dependency {model : QueryFirstModel} {space : model.Space}
    {subject result : Pattern} :
    Cause model space subject result → Dependency model
  | .equation candidate _ _ _ _ _ _ _ =>
      .spaceAtom (needKey model.toPrimeModel space subject) candidate
  | .capability _ =>
      .capability (needKey model.toPrimeModel space subject) result
  | .inert _ _ => .inert (needKey model.toPrimeModel space subject)

def receipt {model : QueryFirstModel} {space : model.Space}
    {subject result : Pattern}
    (cause : Cause model space subject result) :
    PrimeNeedWorlds.DependencyReceipt (Dependency model) :=
  { roots := {cause.dependency} }

/-- Publishing a one-cause receipt always includes its originating request. -/
theorem request_mem_closed_receipt
    {model : QueryFirstModel} {space : model.Space} {subject result : Pattern}
    (cause : Cause model space subject result) :
    Dependency.request (needKey model.toPrimeModel space subject) ∈
      (dependencyBasis model).close cause.receipt.roots := by
  apply (dependencyBasis model).mem_close_iff.mpr
  refine ⟨cause.dependency, by simp [receipt], ?_⟩
  cases cause <;> simp [dependency, dependencyBasis]

end Cause

/-! ## Revision-keyed call-by-need as a GSLT -/

/-- Current Need terms are generic revision-decorated occurrence terms at the
selected evaluation source and revision policy. -/
abbrev NeedTerm (model : Model) :=
  RevisionedOccurrenceTerm
    model.base.source
    (needRevisionKeying model)

/-- Current Need steps are generated by the generic revision decoration. -/
abbrev NeedStep (model : Model) :=
  RevisionedOccurrenceStep
    model.base.source
    (needRevisionKeying model)

/-- The current Need GSLT is an instance of the generic revision-decorated
occurrence construction, rather than a second evaluator definition. -/
def needGSLT (model : Model) : GSLT :=
  revisionedOccurrenceGSLT
    model.base.source
    (needRevisionKeying model)

@[simp] theorem needGSLT_step_iff (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat) :
    (needGSLT model).Step (.request space subject)
        (.answer space subject (needKey model space subject) occurrence result) ↔
      occurrence < Multiset.count result
        (model.base.source.occurrences space subject) :=
  revisionedOccurrenceGSLT_step_iff
    model.base.source
    (needRevisionKeying model)
    space subject result occurrence

/-- At the current query-first point, each lazy answer step has a finite causal
receipt.  The generic revision layer itself does not prescribe a cause
vocabulary. -/
theorem needStep_has_finite_cause (model : QueryFirstModel)
    {source target : NeedTerm model.toPrimeModel}
    (step : (needGSLT model.toPrimeModel).Step source target) :
    ∃ (space : model.Space) (subject result : Pattern) (occurrence : Nat)
        (cause : Cause model space subject result),
      source = .request space subject ∧
      target = .answer space subject (needKey model.toPrimeModel space subject)
        occurrence result ∧
      Dependency.request (needKey model.toPrimeModel space subject) ∈
        (dependencyBasis model).close cause.receipt.roots := by
  cases step with
  | @found space subject occurrence result copy =>
      have member : result ∈ evaluateOne model.zero space subject :=
        Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)
      let cause := ((evaluationCausalOccurrenceSource model).complete
        space subject result member).some
      exact ⟨space, subject, result, occurrence, cause, rfl, rfl,
        cause.request_mem_closed_receipt⟩

/-! ### Need decorates the selected occurrence source -/

def evaluationToNeed (model : Model) :
    OccurrenceTerm model.base.source → NeedTerm model :=
  decorateRevision model.base.source
    (needRevisionKeying model)

/-- The selected occurrence theory embeds faithfully into revision-keyed Need.
The extra key records cache authority but neither adds nor removes a step. -/
def evaluationNeedEmbedding (model : Model) :
    GSLT.Embedding (occurrenceGSLT model.base.source) (needGSLT model) :=
  revisionDecorationEmbedding
    model.base.source
    (needRevisionKeying model)

def needObservation (model : Model) :
    NeedTerm model → OccurrenceTerm model.base.source :=
  forgetRevision model.base.source
    (needRevisionKeying model)

/-- Forgetting the cache key recovers the exact occurrence observation. -/
def evaluationNeedObserved (model : Model) :
    GSLT.Embedding.Observed (occurrenceGSLT model.base.source) (needGSLT model)
      (OccurrenceTerm model.base.source) :=
  revisionDecorationObserved
    model.base.source
    (needRevisionKeying model)

/-- Revision-keyed laziness is a certified realization of occurrence-selection
terms.  Its artifact retains the cache-authority key while its named
observation forgets exactly that implementation-facing decoration. -/
def evaluationNeedRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (OccurrenceTerm model.base.source) (NeedTerm model)
      (OccurrenceTerm model.base.source) :=
  (evaluationNeedObserved model).toRealization

@[simp] theorem evaluationNeedRealization_compile (model : Model)
    (term : OccurrenceTerm model.base.source) :
    (evaluationNeedRealization model).compile () term =
      evaluationToNeed model term :=
  rfl

/-! ## Structural quotation and drop -/

inductive ReflectionTerm (model : Model) where
  | quoted (name : Name Pattern)
  | drop (name : Name Pattern)
  | value (term : Pattern)
  | evaluate (space : model.Space) (name : Name Pattern)

inductive ReflectionStep (model : Model) :
    ReflectionTerm model → ReflectionTerm model → Prop where
  | dropQuote (term : Pattern) :
      ReflectionStep model (ReflectionTerm.drop (Name.quote term))
        (ReflectionTerm.value term)

def reflectionGSLT (model : Model) : GSLT where
  Term := ReflectionTerm model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ReflectionStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem reflection_drop_quote (model : Model) (term : Pattern) :
    (reflectionGSLT model).Step (.drop (Name.quote term)) (.value term) :=
  ReflectionStep.dropQuote term

/-! ## Interacting lazy reflection -/

/-- Evaluating a structural name releases its payload into the same
revision-keyed Need mechanism used by ordinary evaluation. -/
inductive ReflectionToNeed (model : Model) :
    ReflectionTerm model → NeedTerm model → Prop where
  | evaluateQuote (space : model.Space) (term : Pattern) :
      ReflectionToNeed model (.evaluate space (Name.quote term))
        (.request space term)

/-- Reflection and Need are composed by one authored direction of
interaction.  There is deliberately no reverse crossing: a cached answer is
not silently reified as source syntax. -/
def reflectionNeedInteraction (model : Model) :
    GSLT.Interaction (reflectionGSLT model) (needGSLT model) where
  leftToRight := ReflectionToNeed model
  rightToLeft := fun _ _ => False
  leftToRight_resp_left := by
    intro source source' target equivalent crossing
    cases equivalent
    exact ⟨target, crossing, rfl⟩
  leftToRight_resp_right := by
    intro source target target' crossing equivalent
    cases equivalent
    exact crossing
  rightToLeft_resp_left := by
    intro source source' target equivalent crossing
    exact crossing.elim
  rightToLeft_resp_right := by
    intro source target target' crossing equivalent
    exact crossing.elim

/-- The lazy reflective component is an interacting sum, not two independent
services. -/
def runtimeGSLT (model : Model) : GSLT :=
  GSLT.interactingSum (reflectionGSLT model) (needGSLT model)
    (reflectionNeedInteraction model)

/-! ### Shared meaning of reflection and Need

Structural quote/drop states denote the syntax they carry.  An explicit
reflective-evaluation state and every Need state denote the complete
query-derived evaluation bag.  The authored crossing from reflection to Need
therefore preserves meaning rather than merely connecting two term carriers. -/

def reflectionMeaning (model : Model) :
    ReflectionTerm model → Multiset Pattern
  | .quoted name => {Name.unquote name}
  | .drop name => {Name.unquote name}
  | .value term => {term}
  | .evaluate space name =>
      model.base.source.occurrences space (Name.unquote name)

def needMeaning (model : Model) : NeedTerm model → Multiset Pattern :=
  revisionedOccurrenceMeaning
    model.base.source
    (needRevisionKeying model)

def reflectionElaboration (model : Model) :
    GSLT.Elaboration (reflectionGSLT model) (Multiset Pattern) where
  elaborate := fun term => some (reflectionMeaning model term)
  equation := by
    intro source target equivalent
    cases equivalent
    rfl
  rewrite := by
    intro source target step
    cases step
    rfl

def needElaboration (model : Model) :
    GSLT.Elaboration (needGSLT model) (Multiset Pattern) :=
  revisionedOccurrenceElaboration
    model.base.source
    (needRevisionKeying model)

/-- The reflection-to-Need interaction is semantically compositional: its
crossing preserves the complete evaluation bag. -/
def reflectionNeedElaboration (model : Model) :
    GSLT.InteractionElaboration (reflectionNeedInteraction model)
      (Multiset Pattern) where
  left := reflectionElaboration model
  right := needElaboration model
  leftToRight := by
    intro source target crossing
    cases crossing
    rfl
  rightToLeft := by
    intro source target impossible
    exact impossible.elim

/-- One interpretation of the complete lazy reflective runtime, induced from
the component interpretations and their authored crossing law. -/
def runtimeElaboration (model : Model) :
    GSLT.Elaboration (runtimeGSLT model) (Multiset Pattern) :=
  (reflectionNeedElaboration model).toElaboration

def runtimeMeaning (model : Model) :
    (runtimeGSLT model).Term → Multiset Pattern :=
  Sum.elim (reflectionMeaning model) (needMeaning model)

@[simp] theorem runtimeElaboration_elaborate (model : Model)
    (term : (runtimeGSLT model).Term) :
    (runtimeElaboration model).elaborate term =
      some (runtimeMeaning model term) := by
  cases term <;> rfl

def reflectionRuntimeEmbedding (model : Model) :
    GSLT.Embedding (reflectionGSLT model) (runtimeGSLT model) :=
  GSLT.interactingSumLeft _ _ _

def needRuntimeEmbedding (model : Model) :
    GSLT.Embedding (needGSLT model) (runtimeGSLT model) :=
  GSLT.interactingSumRight _ _ _

@[simp] theorem reflection_evaluation_enters_need (model : Model)
    (space : model.Space) (term : Pattern) :
    (runtimeGSLT model).Step
      ((reflectionRuntimeEmbedding model).toFun
        (.evaluate space (Name.quote term)))
      ((needRuntimeEmbedding model).toFun (.request space term)) :=
  GSLT.InteractingStep.leftToRight
    (ReflectionToNeed.evaluateQuote space term)

private theorem runtime_equiv_eq (model : Model)
    {source target : (runtimeGSLT model).Term}
    (equivalent : (runtimeGSLT model).Equiv source target) : source = target := by
  cases equivalent with
  | left equivalent => cases equivalent; rfl
  | right equivalent => cases equivalent; rfl

/-- The base-to-runtime demand relation is the generic hosted-revision seam
instantiated at the selected occurrence embedding. -/
abbrev BaseToRuntime (model : Model) :=
  HostedRevisionDemand
    model.base.source
    (needRevisionKeying model)
    model.base.occurrenceEmbedding
    (needRuntimeEmbedding model)

/-- The runtime-to-base return relation is the other direction of the same
generic hosted-revision seam. -/
abbrev RuntimeToBase (model : Model) :=
  HostedRevisionReturn
    model.base.source
    (needRevisionKeying model)
    model.base.occurrenceEmbedding
    (needRuntimeEmbedding model)

/-- The crossings between the selected occurrence host and Prime's lazy
runtime are assembled by the generic revision interaction. Today's query-first
Zero kernel is one host instance, not part of the construction's definition. -/
def baseRuntimeInteraction (model : Model) :
    GSLT.Interaction model.base.host (runtimeGSLT model) :=
  hostedRevisionInteraction
    model.base.source
    (needRevisionKeying model)
    model.base.occurrenceEmbedding
    (needRuntimeEmbedding model)

/-- The selected base and Prime's lazy reflective runtime share one answer-bag
interpretation, and both directions of their authored interaction preserve it. -/
def baseRuntimeElaboration (model : Model) :
    GSLT.InteractionElaboration (baseRuntimeInteraction model)
      (Multiset Pattern) where
  left := model.observation.elaboration
  right := runtimeElaboration model
  leftToRight := by
    rintro source target
      ⟨space, subject, sourceEquivalent, targetEquivalent⟩
    cases runtime_equiv_eq model targetEquivalent
    calc
      model.observation.elaboration.elaborate source =
          model.observation.elaboration.elaborate
            (model.base.occurrenceEmbedding.toFun
              (.request space subject)) :=
        model.observation.elaboration.equation sourceEquivalent
      _ = some (model.base.source.occurrences space subject) := by
        rw [model.observation.elaborates,
          model.observation.occurrenceMeaning]
        rfl
      _ = (runtimeElaboration model).elaborate
          ((needRuntimeEmbedding model).toFun (.request space subject)) := by
        rfl
  rightToLeft := by
    rintro source target
      ⟨space, subject, occurrence, result, sourceEquivalent,
        targetEquivalent⟩
    cases runtime_equiv_eq model sourceEquivalent
    calc
      (runtimeElaboration model).elaborate
          ((needRuntimeEmbedding model).toFun
            (.answer space subject (needKey model space subject)
              occurrence result)) =
          some (model.base.source.occurrences space subject) := by
        rfl
      _ = model.observation.elaboration.elaborate
          (model.base.occurrenceEmbedding.toFun
            (.answer space subject occurrence result)) := by
        rw [model.observation.elaborates,
          model.observation.occurrenceMeaning]
        rfl
      _ = model.observation.elaboration.elaborate target :=
        model.observation.elaboration.equation
          (model.base.host.equations.iseqv.symm targetEquivalent)

/-! ## The composed Prime semantic GSLT -/

/-- Prime's semantic nucleus is assembled inside `(T,E,R)` with explicit
cross-rewrites between the selected base, lazy demand, and
structural reflection. -/
def kernelGSLT (model : Model) : GSLT :=
  GSLT.interactingSum model.base.host (runtimeGSLT model)
    (baseRuntimeInteraction model)

/-- Prime's whole semantic nucleus has the occurrence-bag interpretation
induced by its selected base, Need, and reflection together with the two
explicit crossing laws. -/
def kernelElaboration (model : Model) :
    GSLT.Elaboration (kernelGSLT model) (Multiset Pattern) :=
  (baseRuntimeElaboration model).toElaboration

def kernelMeaning (model : Model) :
    (kernelGSLT model).Term → Multiset Pattern :=
  Sum.elim model.observation.meaning (runtimeMeaning model)

@[simp] theorem kernelElaboration_elaborate (model : Model)
    (term : (kernelGSLT model).Term) :
    (kernelElaboration model).elaborate term =
      some (kernelMeaning model term) := by
  cases term with
  | inl term => exact model.observation.elaborates term
  | inr term => cases term <;> rfl

def baseEmbedding (model : Model) :
    GSLT.Embedding model.base.host (kernelGSLT model) :=
  GSLT.interactingSumLeft _ _ _

/-- The selected base enters the Prime assembly by a typed forward
operational arrow.  This preserves equations and steps; exact local coverage
is deliberately a stronger claim and is refuted in `EvaluationCoherence`. -/
def baseOperationalArrow (model : Model) :
    OperationalTranslation model.base.host (kernelGSLT model) where
  mapTerm := (baseEmbedding model).toFun
  mapEquiv := fun equivalent =>
    ((baseEmbedding model).equiv_iff _ _).2 equivalent
  mapStep := fun step =>
    ((baseEmbedding model).step_iff _ _).2 step

def runtimeEmbedding (model : Model) :
    GSLT.Embedding (runtimeGSLT model) (kernelGSLT model) :=
  GSLT.interactingSumRight _ _ _

def needEmbedding (model : Model) :
    GSLT.Embedding (needGSLT model) (kernelGSLT model) :=
  GSLT.Embedding.comp (runtimeEmbedding model) (needRuntimeEmbedding model)

def reflectionEmbedding (model : Model) :
    GSLT.Embedding (reflectionGSLT model) (kernelGSLT model) :=
  GSLT.Embedding.comp (runtimeEmbedding model)
    (reflectionRuntimeEmbedding model)

/-- The selected occurrence component embedded all the way into Prime. -/
def evaluationKernelEmbedding (model : Model) :
    GSLT.Embedding (occurrenceGSLT model.base.source) (kernelGSLT model) :=
  GSLT.Embedding.comp (baseEmbedding model)
    model.base.occurrenceEmbedding

/-- A selected occurrence request enters the revision-keyed Need component. -/
theorem evaluation_enters_need (model : Model) (space : model.Space)
    (subject : Pattern) :
    (kernelGSLT model).Step
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((needEmbedding model).toFun (.request space subject)) :=
  GSLT.InteractingStep.leftToRight
    (hostedRevisionInteraction_demand
      model.base.source
      (needRevisionKeying model)
      model.base.occurrenceEmbedding
      (needRuntimeEmbedding model) space subject)

/-- Returning from Need restores the exact extensional evaluation answer,
including its occurrence identity. -/
theorem need_returns_evaluation (model : Model) (space : model.Space)
    (subject : Pattern) (occurrence : Nat) (result : Pattern) :
    (kernelGSLT model).Step
      ((needEmbedding model).toFun
        (.answer space subject (needKey model space subject) occurrence result))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  GSLT.InteractingStep.rightToLeft
    (hostedRevisionInteraction_return
      model.base.source
      (needRevisionKeying model)
      model.base.occurrenceEmbedding
      (needRuntimeEmbedding model) space subject occurrence result)

/-- Negative witness for the generic hosting seam: a base term outside every
embedded request-equivalence class cannot demand a revisioned evaluation. -/
theorem base_term_without_request_does_not_demand (model : Model)
    (baseTerm : model.base.host.Term) (space : model.Space)
    (subject : Pattern)
    (notRequest : ∀ demandSpace demandSubject,
      ¬ model.base.host.Equiv baseTerm
        (model.base.occurrenceEmbedding.toFun
          (.request demandSpace demandSubject))) :
    ¬ (kernelGSLT model).Step
      ((baseEmbedding model).toFun baseTerm)
      ((needEmbedding model).toFun (.request space subject)) := by
  intro step
  cases step with
  | leftToRight crossing =>
      rcases crossing with
        ⟨demandSpace, demandSubject, sourceEquivalent, targetEquivalent⟩
      exact notRequest demandSpace demandSubject sourceEquivalent

/-- **Every Prime kernel step preserves the shared occurrence-bag
interpretation.**  This includes direct base steps, Need steps, quote/drop,
and every explicit crossing between the components. -/
theorem kernel_step_preserves_meaning (model : Model)
    {source target : (kernelGSLT model).Term}
    (step : (kernelGSLT model).Step source target) :
    (kernelElaboration model).elaborate source =
      (kernelElaboration model).elaborate target :=
  (kernelElaboration model).rewrite step

/-- In particular, entering the lazy Need route does not change the complete
answer bag denoted by an extensional evaluation request. -/
theorem evaluation_need_preserves_meaning (model : Model)
    (space : model.Space) (subject : Pattern) :
    (kernelElaboration model).elaborate
        ((evaluationKernelEmbedding model).toFun (.request space subject)) =
      (kernelElaboration model).elaborate
        ((needEmbedding model).toFun (.request space subject)) :=
  kernel_step_preserves_meaning model
    (evaluation_enters_need model space subject)

/-- Evaluating a quoted term enters the same Need component as an ordinary
evaluation request.  Reflection therefore affects the reachable behavior of
the composed language rather than merely adding disconnected terms. -/
theorem reflected_evaluation_enters_need (model : Model)
    (space : model.Space) (term : Pattern) :
    (kernelGSLT model).Step
      ((reflectionEmbedding model).toFun
        (.evaluate space (Name.quote term)))
      ((needEmbedding model).toFun (.request space term)) := by
  apply ((runtimeEmbedding model).step_iff _ _).2
  exact reflection_evaluation_enters_need model space term

/-- Merely quoting syntax is inert.  Only the explicit reflective-evaluation
form crosses into Need. -/
theorem quoted_name_does_not_demand (model : Model) (space : model.Space)
    (term : Pattern) :
    ¬ (kernelGSLT model).Step
      ((reflectionEmbedding model).toFun (.quoted (Name.quote term)))
      ((needEmbedding model).toFun (.request space term)) := by
  intro step
  have runtimeStep := ((runtimeEmbedding model).step_iff _ _).1 step
  cases runtimeStep with
  | leftToRight crossing => cases crossing

/-! ### Direct and lazy routes share one semantic endpoint -/

/-- The direct reference-semantics route for one evaluation occurrence. -/
def directEvaluationPath (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (kernelGSLT model).RewritePath
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons (((evaluationKernelEmbedding model).step_iff _ _).2
    (OccurrenceStep.found copy)) (.nil _)

/-- The corresponding Prime route passes through a revision-keyed Need cell
and returns to the same extensional answer. -/
def lazyEvaluationPath (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (kernelGSLT model).RewritePath
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons (evaluation_enters_need model space subject)
    (.cons (((needEmbedding model).step_iff _ _).2
      (RevisionedOccurrenceStep.found copy))
      (.cons (need_returns_evaluation model space subject occurrence result)
        (.nil _)))

/-- Quoted evaluation and ordinary evaluation share the same lazy engine:
after the reflective crossing, the very same occurrence proof drives Need. -/
def reflectedEvaluationPath (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (kernelGSLT model).RewritePath
      ((reflectionEmbedding model).toFun
        (.evaluate space (Name.quote subject)))
      ((needEmbedding model).toFun
        (.answer space subject (needKey model space subject) occurrence result)) :=
  .cons (reflected_evaluation_enters_need model space subject)
    (.cons (((needEmbedding model).step_iff _ _).2
      (RevisionedOccurrenceStep.found copy))
      (.nil _))

@[simp] theorem directEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (directEvaluationPath model space subject result occurrence copy).length = 1 :=
  rfl

@[simp] theorem lazyEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (lazyEvaluationPath model space subject result occurrence copy).length = 3 :=
  rfl

@[simp] theorem reflectedEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    (reflectedEvaluationPath model space subject result occurrence copy).length = 2 :=
  rfl

/-- Proof-relevant comparison data for direct interpretation and lazy
realization.  The common source and target are enforced by the path indices;
the unequal lengths ensure the two routes are not being identified by
definitional equality. -/
structure EvaluationRouteComparison (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat) where
  direct : (kernelGSLT model).RewritePath
    ((evaluationKernelEmbedding model).toFun (.request space subject))
    ((evaluationKernelEmbedding model).toFun
      (.answer space subject occurrence result))
  lazy : (kernelGSLT model).RewritePath
    ((evaluationKernelEmbedding model).toFun (.request space subject))
    ((evaluationKernelEmbedding model).toFun
      (.answer space subject occurrence result))
  direct_length : direct.length = 1
  lazy_length : lazy.length = 3

/-- Every admitted occurrence carries the direct/lazy route comparison. -/
def evaluationRouteComparison (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    EvaluationRouteComparison model space subject result occurrence where
  direct := directEvaluationPath model space subject result occurrence copy
  lazy := lazyEvaluationPath model space subject result occurrence copy
  direct_length := directEvaluationPath_length model space subject result
    occurrence copy
  lazy_length := lazyEvaluationPath_length model space subject result
    occurrence copy

/-- Base observations are preserved explicitly; the embedding does not merely
assert a generic notion of faithfulness. -/
def baseObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed model.base.host
      (kernelGSLT model) (Option model.base.host.Term) where
  toEmbedding := baseEmbedding model
  observeSource := some
  observeTarget
    | .inl term => some term
    | .inr _ => none
  preserves := fun _ => rfl

/-- The base inclusion into Prime preserves the exact occurrence-bag meaning,
not merely the identity of the embedded term. -/
def baseMeaningObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed model.base.host
      (kernelGSLT model) (Multiset Pattern) where
  toEmbedding := baseEmbedding model
  observeSource := model.observation.meaning
  observeTarget := kernelMeaning model
  preserves := fun _ => rfl

/-- Smallest cross-layer law: attaching Need and reflection does not change
the selected base meaning on embedded terms.  This is preservation, not an
identification of the base with the assembled Prime theory. -/
@[simp] theorem baseEmbedding_preserves_meaning (model : Model)
    (term : model.base.host.Term) :
    kernelMeaning model ((baseEmbedding model).toFun term) =
      model.observation.meaning term :=
  (baseMeaningObservedEmbedding model).preserves term

/-- The selected occurrence component embeds into its base while preserving
the complete answer-bag observation. -/
def occurrenceBaseMeaningObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (occurrenceGSLT model.base.source)
      model.base.host (Multiset Pattern) where
  toEmbedding := model.base.occurrenceEmbedding
  observeSource := occurrenceMeaning model.base.source
  observeTarget := model.observation.meaning
  preserves := model.observation.occurrenceMeaning

/-- The occurrence-to-Prime inclusion inherits its observation law by
composition through the selected base. -/
def evaluationMeaningObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (occurrenceGSLT model.base.source)
      (kernelGSLT model) (Multiset Pattern) :=
  (baseMeaningObservedEmbedding model).comp
    (occurrenceBaseMeaningObservedEmbedding model) rfl

/-- Prime is a certified realization of the selected base at exact
occurrence-bag observation. -/
def baseMeaningRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      model.base.host.Term (kernelGSLT model).Term
      (Multiset Pattern) :=
  (baseMeaningObservedEmbedding model).toRealization

/-- The composed evaluation inclusion is likewise a certified realization. -/
def evaluationMeaningRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (occurrenceGSLT model.base.source).Term (kernelGSLT model).Term
      (Multiset Pattern) :=
  (evaluationMeaningObservedEmbedding model).toRealization

/-- Prime itself is a certified realization of every selected base term at the
explicit optional-base observation.  New Prime-only terms remain outside that
observation rather than being confused with selected-base behavior. -/
def baseKernelRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      model.base.host.Term (kernelGSLT model).Term
      (Option model.base.host.Term) :=
  (baseObservedEmbedding model).toRealization

@[simp] theorem baseKernelRealization_compile (model : Model)
    (term : model.base.host.Term) :
    (baseKernelRealization model).compile () term =
      (baseEmbedding model).toFun term :=
  rfl

/-- Reflection genuinely adds behavior: its drop step is not the image of any
selected base step. -/
theorem reflection_step_not_from_base (model : Model) (term : Pattern) :
    (kernelGSLT model).Step
        ((reflectionEmbedding model).toFun (.drop (Name.quote term)))
        ((reflectionEmbedding model).toFun (.value term)) ∧
      ∀ source,
        (baseEmbedding model).toFun source ≠
          (reflectionEmbedding model).toFun (.drop (Name.quote term)) := by
  constructor
  · exact ((reflectionEmbedding model).step_iff _ _).2
      (reflection_drop_quote model term)
  · intro source equal
    cases equal

/-! ### The Prime operational specification region -/

/-- Admissible Prime operational points host a selected occurrence base and
its revision decoration in one total theory. -/
abbrev OperationalRegion := RevisionedPoint Pattern Pattern

/-- Every modular Prime assembly determines one point of that region. -/
def operationalPoint (model : Model) : OperationalRegion where
  base := model.base
  revision :=
    { keying := needRevisionKeying model
      keyDecidableEq := inferInstanceAs (DecidableEq (NeedKey model)) }
  total := kernelGSLT model
  baseEmbedding := baseEmbedding model
  revisionEmbedding := needEmbedding model

@[simp] theorem operationalPoint_base (model : Model) :
    (operationalPoint model).base = model.base :=
  rfl

/-- Positive arrow witness: every Prime-region point has its typed identity
arrow, retaining the base, revision, and total hosting squares. -/
def operationalPointIdentity (model : Model) :
    RevisionedPoint.Hom (operationalPoint model) (operationalPoint model) :=
  RevisionedPoint.Hom.id (operationalPoint model)

/-! ## Certificate-GSLT authoring as a hosted service -/

/-- Runtime terms and proof-calculus documents may coexist in one authored
GSLT document.  The proof-calculus summand retains its own equations and
rewrites; it is not a field of Prime's evaluator. -/
def proofHostingGSLT (model : Model) : GSLT :=
  (GSLT.compositeDocuments (kernelGSLT model)
    canonicalCalculusAuthoringGSLT.authoring.theory).theory

def runtimeHostingEmbedding (model : Model) :
    GSLT.Embedding (kernelGSLT model) (proofHostingGSLT model) :=
  GSLT.compositeDocumentsLeft _ _

def calculusHostingEmbedding (model : Model) :
    GSLT.Embedding canonicalCalculusAuthoringGSLT.authoring.theory
      (proofHostingGSLT model) :=
  GSLT.compositeDocumentsRight _ _

/-! ## Concrete revision discriminator -/

abbrev VersionedSpace := Nat × Multiset Pattern

def structuralModel
    (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    QueryFirstModel where
  zero :=
    { Space := VersionedSpace
      contents := Prod.snd
      matchAtoms := fun pattern atom =>
        (matchPattern pattern atom : List Bindings)
      groundApply := groundApply }
  revisionAuthority :=
    { Revision := Nat
      revisionDecidableEq := inferInstance
      revision := Prod.fst }

theorem structuralModel_lawful (groundApply : Pattern → Multiset Pattern) :
    MeTTaZero.Lawful (structuralModel groundApply).zero := by
  constructor
  intro name atom
  simp [structuralModel, matchPattern]

/-- Equal contents at distinct revisions have equal Zero observations but
different Prime Need identities. -/
theorem revision_changes_authority_not_zero_answer
    (contents : Multiset Pattern) (subject : Pattern) :
    evaluateOne (structuralModel (fun _ => 0)).zero (0, contents) subject =
        evaluateOne (structuralModel (fun _ => 0)).zero (1, contents) subject ∧
      needKey (structuralModel (fun _ => 0)).toPrimeModel
          (0, contents) subject ≠
        needKey (structuralModel (fun _ => 0)).toPrimeModel
          (1, contents) subject := by
  constructor
  · rfl
  · intro equal
    have impossible := congrArg Prod.fst equal
    change (0 : Nat) = 1 at impossible
    exact Nat.zero_ne_one impossible

/-- The branded current query-first implementation is merely the point
obtained by selecting its generic Prime assembly. -/
def currentOperationalPoint (model : QueryFirstModel) : OperationalRegion :=
  operationalPoint model.toPrimeModel

/-- Today's Zero host enters today's Prime point through the generic selected
base arrow; neither endpoint is built into the definition of `Model`. -/
def currentZeroToPrimeOperationalArrow (model : QueryFirstModel) :
    OperationalTranslation
      (MeTTaZero.currentOperationalPoint model.zero).host
      (currentOperationalPoint model).total :=
  baseOperationalArrow model.toPrimeModel

/-- Current-query negative witness: a public query request is outside every
embedded evaluation-request class and therefore cannot cross into Need. -/
theorem query_request_does_not_demand (model : QueryFirstModel)
    (space : model.Space) (pattern template subject : Pattern) :
    ¬ (kernelGSLT model.toPrimeModel).Step
      ((baseEmbedding model.toPrimeModel).toFun
        (.inl (.request space pattern template)))
      ((needEmbedding model.toPrimeModel).toFun (.request space subject)) := by
  apply base_term_without_request_does_not_demand model.toPrimeModel
  intro demandSpace demandSubject equivalent
  cases equivalent

end Mettapedia.Languages.MeTTa.Prime.Language
