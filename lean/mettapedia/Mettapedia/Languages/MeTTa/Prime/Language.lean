import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.Prime.UniversalName
import Mettapedia.Languages.MeTTa.PrimeNeedWorlds
import Mettapedia.GSLT.LanguageDef.CalculusExtension

/-!
# The Prime language nucleus

Prime is a lazy reflective MeTTa language, not a proof calculus and not a
particular abstract machine.  This module isolates the smallest currently
justified semantic nucleus:

* the public query and query-derived evaluation of MeTTa Zero;
* revision-keyed call-by-need identity;
* finite causal receipts for every returned occurrence; and
* structural quotation and drop.

The three components form one GSLT by composition inside `(T,E,R)`.  Unlike a
mere coproduct, the composite contains explicit crossings: an evaluation
request may enter the Need component, a Need answer may return to the
extensional evaluator, and evaluation of quoted syntax enters that same Need
route.  Both the direct semantic step and the lazy route remain visible.  The
Zero component nevertheless embeds faithfully because no crossing invents a
new rewrite with two Zero endpoints.

Need reduction is not a second evaluator: its steps are exactly Zero
evaluation steps decorated with a stable revision key, and every such step
admits a finite causal explanation.  `kernelElaboration` assigns every Zero,
Need, and reflection state its complete occurrence-bag meaning and proves that
all internal and cross rewrites preserve it.  Quotation exposes semantic
syntax, never host continuations or heap addresses.

Proof-GSLT authoring is composed separately at the end of the module.  This is
intentional: Prime can host many proof calculi, while its lazy reflective
evaluation remains fixed.  Runtime scheduling and compilation likewise belong
to certified realizations rather than to the language nucleus.
-/

namespace Mettapedia.Languages.MeTTa.Prime.Language

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CalculusExtension
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.Prime.UniversalName
open Mettapedia.Languages.MeTTa.PrimeNeedWorlds
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## A revisioned Zero model -/

/-- Prime adds revision identity to a lawful query-first Zero model.  The
revision is semantic cache authority: two extensionally equal spaces may still
belong to different theory revisions and must not share cached Need cells. -/
structure Model extends MeTTaZero.Model where
  Revision : Type
  revisionDecidableEq : DecidableEq Revision
  revision : Space → Revision

attribute [instance] Model.revisionDecidableEq

/-- A Need cell is identified by the exact theory revision and demanded
subject.  Allocation lineage and generation are supplied by a realization of
the reference Need machine; this key is the stable language-level origin. -/
abbrev NeedKey (model : Model) := model.Revision × Pattern

def needKey (model : Model) (space : model.Space) (subject : Pattern) :
    NeedKey model :=
  (model.revision space, subject)

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

/-! ## Finite causal answer receipts -/

/-- Language-level dependencies recorded by a Prime answer.  A returned value
depends on its requested Need key and on exactly one immediate cause: a stored
space atom, a grounded capability result, or the open-world inert default. -/
inductive Dependency (model : Model) where
  | request (key : NeedKey model)
  | spaceAtom (key : NeedKey model) (atom : Pattern)
  | capability (key : NeedKey model) (result : Pattern)
  | inert (key : NeedKey model)
deriving DecidableEq

/-- The causal support of an immediate answer cause includes the request that
made it relevant.  Closing a receipt therefore restores demand provenance
without storing the request redundantly in every root set. -/
def dependencyBasis (model : Model) :
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
inductive Cause (model : Model) (space : model.Space) (subject result : Pattern) :
    Type where
  | equation
      (candidate left right : Pattern) (bindings : Bindings)
      (candidateMember : candidate ∈ queryAll model.toModel space)
      (equationView : viewEquation? candidate = some (left, right))
      (matching : bindings ∈ model.matchAtoms left subject)
      (instantiates : applyBindings bindings right = result) :
      Cause model space subject result
  | capability
      (member : result ∈ model.groundApply subject) :
      Cause model space subject result
  | inert
      (unknown : interpretedResults model.toModel space subject = 0)
      (unchanged : result = subject) :
      Cause model space subject result

/-- Every result returned by query-derived Zero evaluation has a finite Prime
cause.  This is the semantic bridge from evaluation to receipts. -/
theorem exists_cause_of_mem_evaluateOne (model : Model)
    (space : model.Space) (subject result : Pattern)
    (member : result ∈ evaluateOne model.toModel space subject) :
    Nonempty (Cause model space subject result) := by
  by_cases unknown : interpretedResults model.toModel space subject = 0
  · have unchanged : result = subject := by
      simpa [evaluateOne, unknown] using member
    exact ⟨.inert unknown unchanged⟩
  · have interpreted :
        result ∈ interpretedResults model.toModel space subject := by
      simpa [evaluateOne, unknown] using member
    rcases Multiset.mem_add.mp interpreted with equationMember | capabilityMember
    · rw [mem_equationResults_iff] at equationMember
      rcases equationMember with
        ⟨candidate, candidateMember, left, right, equationView,
          bindings, matching, instantiates⟩
      exact ⟨.equation candidate left right bindings candidateMember
        equationView matching instantiates⟩
    · exact ⟨.capability capabilityMember⟩

namespace Cause

/-- The single direct dependency recorded for a cause.  Transitive demand
support is recovered through `dependencyBasis.close`. -/
def dependency {model : Model} {space : model.Space} {subject result : Pattern} :
    Cause model space subject result → Dependency model
  | .equation candidate _ _ _ _ _ _ _ =>
      .spaceAtom (needKey model space subject) candidate
  | .capability _ => .capability (needKey model space subject) result
  | .inert _ _ => .inert (needKey model space subject)

def receipt {model : Model} {space : model.Space} {subject result : Pattern}
    (cause : Cause model space subject result) :
    PrimeNeedWorlds.DependencyReceipt (Dependency model) :=
  { roots := {cause.dependency} }

/-- Publishing a one-cause receipt always includes its originating request. -/
theorem request_mem_closed_receipt
    {model : Model} {space : model.Space} {subject result : Pattern}
    (cause : Cause model space subject result) :
    Dependency.request (needKey model space subject) ∈
      (dependencyBasis model).close cause.receipt.roots := by
  apply (dependencyBasis model).mem_close_iff.mpr
  refine ⟨cause.dependency, by simp [receipt], ?_⟩
  cases cause <;> simp [dependency, dependencyBasis]

end Cause

/-! ## Revision-keyed call-by-need as a GSLT -/

inductive NeedTerm (model : Model) where
  | request (space : model.Space) (subject : Pattern)
  | answer (space : model.Space) (subject : Pattern)
      (key : NeedKey model) (occurrence : Nat) (result : Pattern)

inductive NeedStep (model : Model) : NeedTerm model → NeedTerm model → Prop where
  | found {space subject occurrence result}
      (copy : occurrence < Multiset.count result
        (evaluateOne model.toModel space subject)) :
      NeedStep model (.request space subject)
        (.answer space subject (needKey model space subject) occurrence result)

def needGSLT (model : Model) : GSLT where
  Term := NeedTerm model
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := NeedStep model
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

@[simp] theorem needGSLT_step_iff (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat) :
    (needGSLT model).Step (.request space subject)
        (.answer space subject (needKey model space subject) occurrence result) ↔
      occurrence < Multiset.count result
        (evaluateOne model.toModel space subject) := by
  constructor
  · intro step
    cases step
    assumption
  · exact NeedStep.found

/-- Each lazy answer step has a finite causal receipt; laziness does not erase
why the answer exists. -/
theorem needStep_has_finite_cause (model : Model) {source target : NeedTerm model}
    (step : (needGSLT model).Step source target) :
    ∃ (space : model.Space) (subject result : Pattern)
        (occurrence : Nat) (cause : Cause model space subject result),
      source = .request space subject ∧
      target = .answer space subject (needKey model space subject)
        occurrence result ∧
      Dependency.request (needKey model space subject) ∈
        (dependencyBasis model).close cause.receipt.roots := by
  cases step with
  | @found space subject occurrence result copy =>
      have member : result ∈ evaluateOne model.toModel space subject :=
        Multiset.count_pos.mp (Nat.zero_lt_of_lt copy)
      let cause := (exists_cause_of_mem_evaluateOne model space subject result member).some
      exact ⟨space, subject, result, occurrence, cause, rfl, rfl,
        cause.request_mem_closed_receipt⟩

/-! ### Need is a decoration of Zero evaluation, not a rival semantics -/

def evaluationToNeed (model : Model) :
    EvaluationTerm model.toModel → NeedTerm model
  | .request space subject => .request space subject
  | .answer space subject occurrence result =>
      .answer space subject (needKey model space subject) occurrence result

private theorem evaluationToNeed_injective (model : Model) :
    Function.Injective (evaluationToNeed model) := by
  intro source target equal
  cases source <;> cases target <;> cases equal <;> rfl

/-- Zero evaluation embeds faithfully into revision-keyed Need evaluation.
The extra key records cache authority but neither adds nor removes a step. -/
def evaluationNeedEmbedding (model : Model) :
    GSLT.Embedding (evaluationGSLT model.toModel) (needGSLT model) where
  toFun := evaluationToNeed model
  injective := evaluationToNeed_injective model
  equiv_iff := by
    intro source target
    change evaluationToNeed model source = evaluationToNeed model target ↔
      source = target
    exact ⟨fun equal => evaluationToNeed_injective model equal, congrArg _⟩
  step_iff := by
    intro source target
    cases source with
    | request sourceSpace sourceSubject =>
        cases target with
        | request targetSpace targetSubject =>
            constructor <;> intro step <;> cases step
        | answer targetSpace targetSubject occurrence result =>
            constructor
            · intro step
              cases step with
              | found copy => exact EvaluationStep.found copy
            · intro step
              cases step with
              | found copy => exact NeedStep.found copy
    | answer sourceSpace sourceSubject sourceOccurrence sourceResult =>
        cases target with
        | request targetSpace targetSubject =>
            constructor <;> intro step <;> cases step
        | answer targetSpace targetSubject targetOccurrence targetResult =>
            constructor <;> intro step <;> cases step

def needObservation (model : Model) :
    NeedTerm model → EvaluationTerm model.toModel
  | .request space subject => .request space subject
  | .answer space subject _ occurrence result =>
      .answer space subject occurrence result

/-- Forgetting the cache key recovers the exact Zero evaluation observation. -/
def evaluationNeedObserved (model : Model) :
    GSLT.Embedding.Observed (evaluationGSLT model.toModel) (needGSLT model)
      (EvaluationTerm model.toModel) where
  toEmbedding := evaluationNeedEmbedding model
  observeSource := id
  observeTarget := needObservation model
  preserves := by
    intro term
    cases term <;> rfl

/-- Revision-keyed laziness is a certified realization of Zero evaluation
terms.  Its artifact retains the cache-authority key while its named
observation forgets exactly that implementation-facing decoration. -/
def evaluationNeedRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (EvaluationTerm model.toModel) (NeedTerm model)
      (EvaluationTerm model.toModel) :=
  (evaluationNeedObserved model).toRealization

@[simp] theorem evaluationNeedRealization_compile (model : Model)
    (term : EvaluationTerm model.toModel) :
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
      evaluateOne model.toModel space (Name.unquote name)

def needMeaning (model : Model) : NeedTerm model → Multiset Pattern
  | .request space subject => evaluateOne model.toModel space subject
  | .answer space subject _ _ _ => evaluateOne model.toModel space subject

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
    GSLT.Elaboration (needGSLT model) (Multiset Pattern) where
  elaborate := fun term => some (needMeaning model term)
  equation := by
    intro source target equivalent
    cases equivalent
    rfl
  rewrite := by
    intro source target step
    cases step
    rfl

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

private theorem zeroKernel_equiv_eq (model : Model)
    {source target : (MeTTaZero.kernelGSLT model.toModel).Term}
    (equivalent : (MeTTaZero.kernelGSLT model.toModel).Equiv source target) :
    source = target := by
  cases equivalent with
  | left equivalent => cases equivalent; rfl
  | right equivalent => cases equivalent; rfl

private theorem runtime_equiv_eq (model : Model)
    {source target : (runtimeGSLT model).Term}
    (equivalent : (runtimeGSLT model).Equiv source target) : source = target := by
  cases equivalent with
  | left equivalent => cases equivalent; rfl
  | right equivalent => cases equivalent; rfl

/-- An extensional Zero evaluation request may enter Prime's Need mechanism. -/
inductive ZeroToRuntime (model : Model) :
    (MeTTaZero.kernelGSLT model.toModel).Term →
      (runtimeGSLT model).Term → Prop where
  | demand (space : model.Space) (subject : Pattern) :
      ZeroToRuntime model (.inr (.request space subject))
        ((needRuntimeEmbedding model).toFun (.request space subject))

/-- A Need answer returns to the corresponding extensional Zero observation. -/
inductive RuntimeToZero (model : Model) :
    (runtimeGSLT model).Term →
      (MeTTaZero.kernelGSLT model.toModel).Term → Prop where
  | answer (space : model.Space) (subject : Pattern) (occurrence : Nat)
      (result : Pattern) :
      RuntimeToZero model
        ((needRuntimeEmbedding model).toFun
          (.answer space subject (needKey model space subject) occurrence result))
        (.inr (.answer space subject occurrence result))

/-- The crossings between the extensional Zero specification and Prime's lazy
runtime.  Their equation laws are inherited from the equality-based component
presentations. -/
def zeroRuntimeInteraction (model : Model) :
    GSLT.Interaction (MeTTaZero.kernelGSLT model.toModel) (runtimeGSLT model) where
  leftToRight := ZeroToRuntime model
  rightToLeft := RuntimeToZero model
  leftToRight_resp_left := by
    intro source source' target equivalent crossing
    have equal := zeroKernel_equiv_eq model equivalent
    subst source'
    exact ⟨target, crossing, (runtimeGSLT model).equations.refl target⟩
  leftToRight_resp_right := by
    intro source target target' crossing equivalent
    have equal := runtime_equiv_eq model equivalent
    subst target'
    exact crossing
  rightToLeft_resp_left := by
    intro source source' target equivalent crossing
    have equal := runtime_equiv_eq model equivalent
    subst source'
    exact ⟨target, crossing,
      (MeTTaZero.kernelGSLT model.toModel).equations.refl target⟩
  rightToLeft_resp_right := by
    intro source target target' crossing equivalent
    have equal := zeroKernel_equiv_eq model equivalent
    subst target'
    exact crossing

/-- The extensional Zero kernel and Prime's lazy reflective runtime share one
occurrence-bag interpretation, and both directions of their authored
interaction preserve it. -/
def zeroRuntimeElaboration (model : Model) :
    GSLT.InteractionElaboration (zeroRuntimeInteraction model)
      (Multiset Pattern) where
  left := MeTTaZero.kernelElaboration model.toModel
  right := runtimeElaboration model
  leftToRight := by
    intro source target crossing
    cases crossing
    rfl
  rightToLeft := by
    intro source target crossing
    cases crossing
    rfl

/-! ## The composed Prime semantic GSLT -/

/-- Prime's semantic nucleus is assembled inside `(T,E,R)` with explicit
cross-rewrites between the extensional specification, lazy demand, and
structural reflection. -/
def kernelGSLT (model : Model) : GSLT :=
  GSLT.interactingSum (MeTTaZero.kernelGSLT model.toModel) (runtimeGSLT model)
    (zeroRuntimeInteraction model)

/-- Prime's whole semantic nucleus has the occurrence-bag interpretation
induced by Zero, Need, and reflection together with the two explicit crossing
laws. -/
def kernelElaboration (model : Model) :
    GSLT.Elaboration (kernelGSLT model) (Multiset Pattern) :=
  (zeroRuntimeElaboration model).toElaboration

def kernelMeaning (model : Model) :
    (kernelGSLT model).Term → Multiset Pattern :=
  Sum.elim (MeTTaZero.kernelMeaning model.toModel) (runtimeMeaning model)

@[simp] theorem kernelElaboration_elaborate (model : Model)
    (term : (kernelGSLT model).Term) :
    (kernelElaboration model).elaborate term =
      some (kernelMeaning model term) := by
  cases term with
  | inl term => rfl
  | inr term => cases term <;> rfl

def zeroEmbedding (model : Model) :
    GSLT.Embedding (MeTTaZero.kernelGSLT model.toModel) (kernelGSLT model) :=
  GSLT.interactingSumLeft _ _ _

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

/-- The extensional evaluation component embedded all the way into Prime. -/
def evaluationKernelEmbedding (model : Model) :
    GSLT.Embedding (evaluationGSLT model.toModel) (kernelGSLT model) :=
  GSLT.Embedding.comp (zeroEmbedding model)
    (MeTTaZero.evaluationEmbedding model.toModel)

/-- A Zero evaluation request enters the revision-keyed Need component. -/
theorem evaluation_enters_need (model : Model) (space : model.Space)
    (subject : Pattern) :
    (kernelGSLT model).Step
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((needEmbedding model).toFun (.request space subject)) :=
  GSLT.InteractingStep.leftToRight (ZeroToRuntime.demand space subject)

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
    (RuntimeToZero.answer space subject occurrence result)

/-- **Every Prime kernel step preserves the shared occurrence-bag
interpretation.**  This includes direct Zero steps, Need steps, quote/drop,
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
      (evaluateOne model.toModel space subject)) :
    (kernelGSLT model).RewritePath
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons (((evaluationKernelEmbedding model).step_iff _ _).2
    (EvaluationStep.found copy)) (.nil _)

/-- The corresponding Prime route passes through a revision-keyed Need cell
and returns to the same extensional answer. -/
def lazyEvaluationPath (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (evaluateOne model.toModel space subject)) :
    (kernelGSLT model).RewritePath
      ((evaluationKernelEmbedding model).toFun (.request space subject))
      ((evaluationKernelEmbedding model).toFun
        (.answer space subject occurrence result)) :=
  .cons (evaluation_enters_need model space subject)
    (.cons (((needEmbedding model).step_iff _ _).2 (NeedStep.found copy))
      (.cons (need_returns_evaluation model space subject occurrence result)
        (.nil _)))

/-- Quoted evaluation and ordinary evaluation share the same lazy engine:
after the reflective crossing, the very same occurrence proof drives Need. -/
def reflectedEvaluationPath (model : Model) (space : model.Space)
    (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (evaluateOne model.toModel space subject)) :
    (kernelGSLT model).RewritePath
      ((reflectionEmbedding model).toFun
        (.evaluate space (Name.quote subject)))
      ((needEmbedding model).toFun
        (.answer space subject (needKey model space subject) occurrence result)) :=
  .cons (reflected_evaluation_enters_need model space subject)
    (.cons (((needEmbedding model).step_iff _ _).2 (NeedStep.found copy))
      (.nil _))

@[simp] theorem directEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (evaluateOne model.toModel space subject)) :
    (directEvaluationPath model space subject result occurrence copy).length = 1 :=
  rfl

@[simp] theorem lazyEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (evaluateOne model.toModel space subject)) :
    (lazyEvaluationPath model space subject result occurrence copy).length = 3 :=
  rfl

@[simp] theorem reflectedEvaluationPath_length (model : Model)
    (space : model.Space) (subject result : Pattern) (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (evaluateOne model.toModel space subject)) :
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
      (evaluateOne model.toModel space subject)) :
    EvaluationRouteComparison model space subject result occurrence where
  direct := directEvaluationPath model space subject result occurrence copy
  lazy := lazyEvaluationPath model space subject result occurrence copy
  direct_length := directEvaluationPath_length model space subject result
    occurrence copy
  lazy_length := lazyEvaluationPath_length model space subject result
    occurrence copy

/-- Zero observations are preserved explicitly; the embedding does not merely
assert a generic notion of faithfulness. -/
def zeroObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (MeTTaZero.kernelGSLT model.toModel)
      (kernelGSLT model) (Option (MeTTaZero.kernelGSLT model.toModel).Term) where
  toEmbedding := zeroEmbedding model
  observeSource := some
  observeTarget
    | .inl term => some term
    | .inr _ => none
  preserves := fun _ => rfl

/-- The Zero inclusion into Prime preserves the exact occurrence-bag meaning,
not merely the identity of the embedded term. -/
def zeroMeaningObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (MeTTaZero.kernelGSLT model.toModel)
      (kernelGSLT model) (Multiset Pattern) where
  toEmbedding := zeroEmbedding model
  observeSource := MeTTaZero.kernelMeaning model.toModel
  observeTarget := kernelMeaning model
  preserves := fun _ => rfl

/-- The direct evaluation-to-Prime inclusion inherits its observation law by
composition through Zero. -/
def evaluationMeaningObservedEmbedding (model : Model) :
    GSLT.Embedding.Observed (MeTTaZero.evaluationGSLT model.toModel)
      (kernelGSLT model) (Multiset Pattern) :=
  (zeroMeaningObservedEmbedding model).comp
    (MeTTaZero.evaluationObservedEmbedding model.toModel) rfl

/-- Prime is a certified realization of the Zero semantic kernel at exact
occurrence-bag observation. -/
def zeroMeaningRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (MeTTaZero.kernelGSLT model.toModel).Term (kernelGSLT model).Term
      (Multiset Pattern) :=
  (zeroMeaningObservedEmbedding model).toRealization

/-- The composed evaluation inclusion is likewise a certified realization. -/
def evaluationMeaningRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (MeTTaZero.evaluationGSLT model.toModel).Term (kernelGSLT model).Term
      (Multiset Pattern) :=
  (evaluationMeaningObservedEmbedding model).toRealization

/-- Prime itself is a certified realization of every Zero kernel term at the
explicit optional-Zero observation.  New Prime-only terms remain outside that
observation rather than being confused with Zero behavior. -/
def zeroKernelRealization (model : Model) :
    Mettapedia.GSLT.SimpleRealization
      (MeTTaZero.kernelGSLT model.toModel).Term (kernelGSLT model).Term
      (Option (MeTTaZero.kernelGSLT model.toModel).Term) :=
  (zeroObservedEmbedding model).toRealization

@[simp] theorem zeroKernelRealization_compile (model : Model)
    (term : (MeTTaZero.kernelGSLT model.toModel).Term) :
    (zeroKernelRealization model).compile () term =
      (zeroEmbedding model).toFun term :=
  rfl

/-- Reflection genuinely adds behavior: its drop step is not the image of any
Zero step. -/
theorem reflection_step_not_from_zero (model : Model) (term : Pattern) :
    (kernelGSLT model).Step
        ((reflectionEmbedding model).toFun (.drop (Name.quote term)))
        ((reflectionEmbedding model).toFun (.value term)) ∧
      ∀ source,
        (zeroEmbedding model).toFun source ≠
          (reflectionEmbedding model).toFun (.drop (Name.quote term)) := by
  constructor
  · exact ((reflectionEmbedding model).step_iff _ _).2
      (reflection_drop_quote model term)
  · intro source equal
    cases equal

/-! ## Proof-GSLT authoring as a hosted service -/

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
    (groundApply : Pattern → Multiset Pattern := fun _ => 0) : Model where
  Space := VersionedSpace
  contents := Prod.snd
  matchAtoms := fun pattern atom =>
    (matchPattern pattern atom : List Bindings)
  groundApply := groundApply
  Revision := Nat
  revisionDecidableEq := inferInstance
  revision := Prod.fst

theorem structuralModel_lawful (groundApply : Pattern → Multiset Pattern) :
    MeTTaZero.Lawful (structuralModel groundApply).toModel := by
  constructor
  intro name atom
  simp [structuralModel, matchPattern]

/-- Equal contents at distinct revisions have equal Zero observations but
different Prime Need identities. -/
theorem revision_changes_authority_not_zero_answer
    (contents : Multiset Pattern) (subject : Pattern) :
    evaluateOne (structuralModel (fun _ => 0)).toModel (0, contents) subject =
        evaluateOne (structuralModel (fun _ => 0)).toModel (1, contents) subject ∧
      needKey (structuralModel (fun _ => 0)) (0, contents) subject ≠
        needKey (structuralModel (fun _ => 0)) (1, contents) subject := by
  constructor
  · rfl
  · intro equal
    have impossible := congrArg Prod.fst equal
    simp [needKey, structuralModel] at impossible

end Mettapedia.Languages.MeTTa.Prime.Language
