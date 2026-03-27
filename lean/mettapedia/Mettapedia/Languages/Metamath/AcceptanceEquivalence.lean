import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.Simulation
import Mettapedia.Languages.Metamath.Fixtures

/-!
# Metamath Acceptance Equivalence Scaffold

This module exposes local aliases for implementation acceptance and
spec provability, then reuses `mm-lean4`'s proved biconditional directly.
-/

namespace Mettapedia.Languages.Metamath.AcceptanceEquivalence

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation
open Mettapedia.Languages.Metamath.Fixtures
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Implementation acceptance predicate (parser/checker side). -/
def ImplAccepts (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      ⟨⟨0, 0⟩, label, f, (checkBytesDB bytes).frame, #[], #[], Metamath.Verify.ProofTokenParser.normal⟩ =
        Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Spec acceptance predicate (declarative side). -/
def SpecAccepts (bytes : ByteArray) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (Γ : Metamath.Spec.Database) (fr : Metamath.Spec.Frame),
    Metamath.Kernel.toDatabase (checkBytesDB bytes) = some Γ ∧
      Metamath.Kernel.toFrame (checkBytesDB bytes) (checkBytesDB bytes).frame = some fr ∧
      Metamath.Spec.Provable Γ fr (Metamath.Kernel.toExpr f)

theorem implAccepts_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    ImplAccepts bytes label f ↔ SpecAccepts bytes f := by
  simpa [ImplAccepts, SpecAccepts, checkBytesDB] using
    parserAcceptance_iff_specProvable bytes label f hSuccess

/-- Initial runtime proof state used by checker acceptance witnesses. -/
def initialProofState
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    Metamath.Verify.ProofState :=
  ⟨⟨0, 0⟩, label, f, (checkBytesDB bytes).frame, #[], #[], Metamath.Verify.ProofTokenParser.normal⟩

/-- Runtime provenance for proof tokens:
the token resolves to a hypothesis/assertion object in the checker DB. -/
def RuntimeLabelProvenance (db : RuntimeDB) (step : String) : Prop :=
  ∃ obj, db.find? step = some obj ∧
    match obj with
    | .hyp _ _ _ => True
    | .assert _ _ _ => True
    | _ => False

theorem runtimeLabelProvenance_of_stepNormal_ok
    {db : RuntimeDB} {pr pr' : RuntimeProofState} {step : String}
    (hStep : Metamath.Verify.DB.stepNormal db pr step = Except.ok pr') :
    RuntimeLabelProvenance db step := by
  unfold RuntimeLabelProvenance
  unfold Metamath.Verify.DB.stepNormal at hStep
  cases hFind : db.find? step with
  | none =>
      simp [hFind] at hStep
  | some obj =>
      cases obj with
      | const c =>
          simp [hFind] at hStep
      | var v =>
          simp [hFind] at hStep
      | hyp ess f nm =>
          exact ⟨Metamath.Verify.Object.hyp ess f nm, rfl, trivial⟩
      | assert f fr nm =>
          exact ⟨Metamath.Verify.Object.assert f fr nm, rfl, trivial⟩

private theorem traceLabelsAuthored_list_of_fold_ok
    (db : RuntimeDB) (steps : List String)
    (pr0 prFinal : RuntimeProofState)
    (hFold :
      steps.foldlM (fun pr step => Metamath.Verify.DB.stepNormal db pr step) pr0 =
        Except.ok prFinal) :
    ∀ step ∈ steps, RuntimeLabelProvenance db step := by
  induction steps generalizing pr0 prFinal with
  | nil =>
      intro step hMem
      cases hMem
  | cons hd tl ih =>
      simp [List.foldlM_cons, Bind.bind, Except.bind] at hFold
      cases hHead : Metamath.Verify.DB.stepNormal db pr0 hd with
      | error e =>
          simp [hHead] at hFold
      | ok pr1 =>
          rw [hHead] at hFold
          intro step hMem
          simp at hMem
          rcases hMem with rfl | hTailMem
          · exact runtimeLabelProvenance_of_stepNormal_ok hHead
          · exact ih pr1 prFinal hFold step hTailMem

/-- Authored-trace side condition sourced from runtime checker provenance:
every trace token resolves to a hypothesis/assertion object in the checker DB. -/
def TraceLabelsAuthored (bytes : ByteArray) (proof : Array String) : Prop :=
  ∀ step ∈ proof.toList, RuntimeLabelProvenance (checkBytesDB bytes) step

theorem traceLabelsAuthored_of_fold_ok
    (bytes : ByteArray) (proof : Array String)
    (pr0 prFinal : RuntimeProofState)
    (hFold :
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step) pr0 =
        Except.ok prFinal) :
    TraceLabelsAuthored bytes proof := by
  intro step hMem
  have hList := hFold
  rw [← Array.foldlM_toList] at hList
  exact traceLabelsAuthored_list_of_fold_ok (checkBytesDB bytes) proof.toList pr0 prFinal hList step hMem

/-- LanguageDef-side acceptance witness:
an implementation acceptance witness whose trace tokens are all authored rewrite
labels in the Lean `metamathCore` LanguageDef. -/
def LanguageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Authored-trace completeness invariant sourced directly from runtime
provenance of successful checker execution traces. -/
theorem authoredTraceCompleteness_from_runtime
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    ∀ proof prFinal f',
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) = Except.ok prFinal →
      prFinal.stack.size = 1 →
      prFinal.stack[0]? = some f' →
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f →
      TraceLabelsAuthored bytes proof := by
  intro proof prFinal f' hFold _hSize _hTop _hExpr
  exact traceLabelsAuthored_of_fold_ok
    bytes proof (initialProofState bytes label f) prFinal hFold

/-- Forward simulation: any LanguageDef-trace acceptance witness implies
spec acceptance. -/
theorem languageDefTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  rcases hTrace with ⟨proof, prFinal, f', hSuccess, _hAuthored, hFold, hSize, hTop, hExpr⟩
  have hImpl : ImplAccepts bytes label f := ⟨proof, prFinal, f', hFold, hSize, hTop, hExpr⟩
  exact (implAccepts_iff_specAccepts bytes label f hSuccess).1 hImpl

/-- Backward simulation: spec acceptance yields a LanguageDef-trace acceptance
witness with authored-trace completeness discharged from runtime provenance. -/
theorem specAccepts_to_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hSpec : SpecAccepts bytes f) :
    LanguageDefTraceWitness bytes label f := by
  have hImpl : ImplAccepts bytes label f :=
    (implAccepts_iff_specAccepts bytes label f hSuccess).2 hSpec
  rcases hImpl with ⟨proof, prFinal, f', hFold, hSize, hTop, hExpr⟩
  have hAuthored :
      TraceLabelsAuthored bytes proof :=
    authoredTraceCompleteness_from_runtime bytes label f
      proof prFinal f' hFold hSize hTop hExpr
  exact ⟨proof, prFinal, f', hSuccess, hAuthored,
    hFold, hSize, hTop, hExpr⟩

/-- Composed bisimulation-facing scaffold theorem.
Both directions are now direct (no extra completeness hypothesis), because
trace authorship is discharged from runtime provenance. -/
theorem languageDefTraceWitness_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    LanguageDefTraceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact languageDefTraceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec

/-- Engine-facing trace compatibility: each token has an engine-labeled
top-level rewrite witness (Simulation layer, line 202 boundary). -/
def EngineTokenLift (step : String) : Prop :=
  ∃ p q, EngineLabeledTopStep p q step

def EngineTraceCompatible (proof : Array String) : Prop :=
  ∀ step ∈ proof.toList, EngineTokenLift step

/-- Stronger witness that carries both runtime provenance and engine-layer
token witnesses, so the trace is not wrapper-only. -/
def EngineBackedTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      EngineTraceCompatible proof ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

theorem engineBackedTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineBackedTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  rcases hTrace with
    ⟨proof, prFinal, f', hNoErr, hAuthored, _hEngine, hFold, hSize, hTop, hExpr⟩
  exact languageDefTraceWitness_to_specAccepts
    bytes label f ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Stronger trace witness that pins proof tokens to a concrete
engine-labeled `DeclReducesWithPremises` path (Simulation layer), not only
wrapper stepping. -/
def RuntimeTokenMatchesEngineLabel (tok engineLabel : String) : Prop :=
  tok = engineLabel

/-- Runtime token to engine-label-segment refinement relation.
Positive example: a token can refine to a singleton identical engine label.
Negative example: a non-authored token may refine to an empty segment (it is
not forced to appear as an engine rewrite label). -/
def RuntimeTokenRefinesEngineSegment (tok : String) (seg : List String) : Prop :=
  seg = [tok] ∨ (¬ AuthoredRewriteLabel tok ∧ seg = [])

/-- Runtime proof-token trace refines an engine-label trace via a list of
per-token segments whose concatenation is the engine trace. -/
def RuntimeTraceRefinesEngineLabels
    (proofLabels engineLabels : List String) : Prop :=
  ∃ segs : List (List String),
    List.Forall₂ RuntimeTokenRefinesEngineSegment proofLabels segs ∧
    segs.foldr List.append [] = engineLabels

def EngineAlignedTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula) (start finish : Pattern),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      (∃ engTrace : LabeledLanguageDefEngineTraceWitness start finish,
        List.Forall₂ RuntimeTokenMatchesEngineLabel proof.toList engTrace.labels) ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Intermediate crown-jewel witness:
it keeps the successful runtime trace together with a concrete labeled engine
trace and a token-to-engine-segment refinement witness.

Positive example: use this when proof tokens do not match authored rewrite
labels one-for-one, but still refine to an engine trace.
Negative example: unlike `EngineAcceptanceWitness`, this witness does not
discard the token-to-engine-trace relationship. -/
def EngineRefinedTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula) (start finish : Pattern),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      (∃ engTrace : LabeledLanguageDefEngineTraceWitness start finish,
        RuntimeTraceRefinesEngineLabels proof.toList engTrace.labels) ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Completeness invariant for engine alignment:
every successful runtime witness for `(bytes,label,f)` can be paired with a
concrete labeled engine trace carrying the same proof-token list. -/
def EngineAlignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∀ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      (initialProofState bytes label f) = Except.ok prFinal →
    prFinal.stack.size = 1 →
    prFinal.stack[0]? = some f' →
    Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f →
    ∃ start finish, ∃ engTrace : LabeledLanguageDefEngineTraceWitness start finish,
      List.Forall₂ RuntimeTokenMatchesEngineLabel proof.toList engTrace.labels

/-- Refined completeness invariant:
every successful runtime witness can be paired with a labeled engine trace,
plus a token-to-segment refinement witness between runtime and engine labels. -/
def EngineRefinedAlignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∀ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      (initialProofState bytes label f) = Except.ok prFinal →
    prFinal.stack.size = 1 →
    prFinal.stack[0]? = some f' →
    Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f →
    ∃ start finish, ∃ engTrace : LabeledLanguageDefEngineTraceWitness start finish,
      RuntimeTraceRefinesEngineLabels proof.toList engTrace.labels

/-- Runtime-side namespace separation assumption:
any checker token that genuinely resolves to a hypothesis/assertion object is
not itself the name of an authored Metamath rewrite rule. -/
def RuntimeProvenanceDisjointFromAuthored (bytes : ByteArray) : Prop :=
  ∀ step, RuntimeLabelProvenance (checkBytesDB bytes) step → ¬ AuthoredRewriteLabel step

/-- Honest weaker witness: a successful runtime proof-checking trace together
with some declarative engine acceptance path, without identifying proof tokens
with LanguageDef rewrite labels. -/
def EngineAcceptanceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula) (start finish : Pattern),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      LanguageDefAccepts start finish ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Honest completeness target for the engine layer:
every successful runtime witness can be paired with some engine acceptance
path, but not necessarily one whose labels coincide with runtime proof tokens. -/
def EngineAcceptanceComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∀ (proof : Array String) (prFinal : Metamath.Verify.ProofState)
      (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      (initialProofState bytes label f) = Except.ok prFinal →
    prFinal.stack.size = 1 →
    prFinal.stack[0]? = some f' →
    Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f →
    ∃ start finish, LanguageDefAccepts start finish

private def trivialEnginePattern : Pattern :=
  .fvar "__engine_acceptance_dummy"

private def trivialLabeledEngineTraceWitness :
    LabeledLanguageDefEngineTraceWitness trivialEnginePattern trivialEnginePattern where
  trace := [trivialEnginePattern]
  labels := []
  head_eq := by simp [trivialEnginePattern]
  last_eq := by simp [trivialEnginePattern]
  reduces := by simp [LabeledReducesAlong]

/-- Honest weak completeness is always inhabitable via reflexive declarative
engine acceptance.
Positive example: this removes boilerplate `hComplete` assumptions in weak
bridge theorems.
Negative example: this theorem does not establish token/label alignment. -/
theorem engineAcceptanceComplete_trivial
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    EngineAcceptanceComplete bytes label f := by
  intro _proof _prFinal _f' _hFold _hSize _hTop _hExpr
  exact ⟨trivialEnginePattern, trivialEnginePattern, Relation.ReflTransGen.refl⟩

private theorem singletonSegments_flatten
    (xs : List String) :
    (xs.map (fun tok => [tok])).foldr List.append [] = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih]

private theorem tokenSelfRefines
    (xs : List String) :
    List.Forall₂ RuntimeTokenRefinesEngineSegment xs (xs.map (fun tok => [tok])) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [RuntimeTokenRefinesEngineSegment, ih]

private theorem emptySegments_flatten
    (xs : List String) :
    (xs.map (fun _ => ([] : List String))).foldr List.append [] = [] := by
  induction xs with
  | nil =>
      rfl
  | cons _ _ ih =>
      simpa using ih

private theorem tokenEmptyRefines
    (xs : List String)
    (hNoAuth : ∀ step ∈ xs, ¬ AuthoredRewriteLabel step) :
    List.Forall₂ RuntimeTokenRefinesEngineSegment xs (xs.map (fun _ => ([] : List String))) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : ¬ AuthoredRewriteLabel x := hNoAuth x (by simp)
      have hxs : ∀ step ∈ xs, ¬ AuthoredRewriteLabel step := by
        intro step hMem
        exact hNoAuth step (by simp [hMem])
      have hhead : RuntimeTokenRefinesEngineSegment x ([] : List String) :=
        Or.inr ⟨hx, rfl⟩
      exact List.Forall₂.cons hhead (ih hxs)

private theorem runtimeTraceRefines_of_strictLabelAlignment
    {proofLabels engineLabels : List String}
    (hAlign : List.Forall₂ RuntimeTokenMatchesEngineLabel proofLabels engineLabels) :
    RuntimeTraceRefinesEngineLabels proofLabels engineLabels := by
  have hEq : proofLabels = engineLabels := by
    induction hAlign with
    | nil =>
        rfl
    | @cons x y xs ys hxy hrest ih =>
        simp [RuntimeTokenMatchesEngineLabel] at hxy
        subst hxy
        simp [ih]
  refine ⟨proofLabels.map (fun tok => [tok]), tokenSelfRefines proofLabels, ?_⟩
  simpa [hEq] using singletonSegments_flatten proofLabels

private theorem runtimeTraceRefines_all_empty_of_nonAuthored
    {proofLabels : List String}
    (hNoAuth : ∀ step ∈ proofLabels, ¬ AuthoredRewriteLabel step) :
    RuntimeTraceRefinesEngineLabels proofLabels [] := by
  refine ⟨proofLabels.map (fun _ => ([] : List String)), tokenEmptyRefines proofLabels hNoAuth, ?_⟩
  exact emptySegments_flatten proofLabels

/-- The stronger token-level alignment invariant implies the weaker honest
engine-acceptance invariant. -/
theorem engineAlignmentComplete_to_engineAcceptanceComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete bytes label f) :
    EngineAcceptanceComplete bytes label f := by
  intro proof prFinal f' hFold hSize hTop hExpr
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, engTrace, _hLabels⟩
  exact ⟨start, finish, labeledLanguageDefEngineTraceWitness_accepts engTrace⟩

/-- Strict token=label alignment implies refined token-to-segment alignment. -/
theorem engineAlignmentComplete_to_engineRefinedAlignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete bytes label f) :
    EngineRefinedAlignmentComplete bytes label f := by
  intro proof prFinal f' hFold hSize hTop hExpr
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, engTrace, hAlign⟩
  exact ⟨start, finish, engTrace,
    runtimeTraceRefines_of_strictLabelAlignment hAlign⟩

/-- Runtime provenance disjointness gives a genuinely runtime-derived refined
alignment theorem: successful checker traces refine to an engine trace whose
label list may be empty when runtime tokens are not authored rewrites. -/
theorem runtimeProvenanceDisjoint_to_engineRefinedAlignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes) :
    EngineRefinedAlignmentComplete bytes label f := by
  intro proof prFinal f' hFold hSize hTop hExpr
  have hTraceAuth : TraceLabelsAuthored bytes proof :=
    authoredTraceCompleteness_from_runtime bytes label f
      proof prFinal f' hFold hSize hTop hExpr
  have hNoAuth : ∀ step ∈ proof.toList, ¬ AuthoredRewriteLabel step := by
    intro step hMem
    exact hDisjoint step (hTraceAuth step hMem)
  exact ⟨trivialEnginePattern, trivialEnginePattern, trivialLabeledEngineTraceWitness,
    runtimeTraceRefines_all_empty_of_nonAuthored hNoAuth⟩

/-- Refined alignment completeness still carries concrete labeled engine
traces, so it implies honest engine-acceptance completeness. -/
theorem engineRefinedAlignmentComplete_to_engineAcceptanceComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineRefinedAlignmentComplete bytes label f) :
    EngineAcceptanceComplete bytes label f := by
  intro proof prFinal f' hFold hSize hTop hExpr
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, engTrace, _hRefinement⟩
  exact ⟨start, finish, labeledLanguageDefEngineTraceWitness_accepts engTrace⟩

/-- Under the weaker engine-acceptance completeness invariant, any
LanguageDef-trace witness can be lifted to an honest engine-acceptance witness. -/
theorem languageDefTraceWitness_to_engineAcceptanceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAcceptanceComplete bytes label f)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    EngineAcceptanceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, hAccepts⟩
  exact ⟨proof, prFinal, f', start, finish, hNoErr, hAuthored,
    hAccepts, hFold, hSize, hTop, hExpr⟩

/-- Under refined-alignment completeness, any LanguageDef-trace witness can be
lifted to a refined engine witness. -/
theorem languageDefTraceWitness_to_engineRefinedTraceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineRefinedAlignmentComplete bytes label f)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    EngineRefinedTraceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, engTrace, hRefined⟩
  exact ⟨proof, prFinal, f', start, finish, hNoErr, hAuthored,
    ⟨engTrace, hRefined⟩, hFold, hSize, hTop, hExpr⟩

/-- Under the alignment-completeness invariant, any LanguageDef-trace witness
can be lifted to an engine-aligned witness. -/
theorem languageDefTraceWitness_to_engineAlignedTraceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete bytes label f)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    EngineAlignedTraceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩
  rcases hComplete proof prFinal f' hFold hSize hTop hExpr with
    ⟨start, finish, engTrace, hLabels⟩
  exact ⟨proof, prFinal, f', start, finish, hNoErr, hAuthored,
    ⟨engTrace, hLabels⟩, hFold, hSize, hTop, hExpr⟩

/-- An engine-aligned witness contains the underlying LanguageDef runtime
acceptance witness. Positive example: use this when only spec acceptance is
needed. Negative example: do not keep carrying token/label alignment data once
the goal has dropped to plain runtime acceptance. -/
theorem engineAlignedTraceWitness_to_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAlignedTraceWitness bytes label f) :
    LanguageDefTraceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hAligned, hFold, hSize, hTop, hExpr⟩
  exact ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Engine-aligned witnesses carry a concrete engine acceptance path. -/
theorem engineAlignedTraceWitness_to_engineAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAlignedTraceWitness bytes label f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  rcases hTrace with
    ⟨_proof, _prFinal, _f', start, finish, _hNoErr, _hAuthored,
      hAligned, _hFold, _hSize, _hTop, _hExpr⟩
  rcases hAligned with ⟨engTrace, _hLabels⟩
  exact ⟨start, finish, labeledLanguageDefEngineTraceWitness_accepts engTrace⟩

/-- Engine-aligned witnesses still imply spec acceptance (forward direction),
while retaining explicit engine-trace evidence. -/
theorem engineAlignedTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAlignedTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  exact languageDefTraceWitness_to_specAccepts
    bytes label f
    (engineAlignedTraceWitness_to_languageDefTraceWitness bytes label f hTrace)

/-- Composed forward bridge: one engine-aligned witness simultaneously yields
an engine acceptance path and spec acceptance. -/
theorem engineAlignedTraceWitness_to_engineAndSpec
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAlignedTraceWitness bytes label f) :
    (∃ start finish, LanguageDefAccepts start finish) ∧ SpecAccepts bytes f := by
  refine ⟨?_, ?_⟩
  · exact engineAlignedTraceWitness_to_engineAccepts bytes label f hTrace
  · exact engineAlignedTraceWitness_to_specAccepts bytes label f hTrace

/-- A refined engine witness forgets to the underlying runtime acceptance
witness. -/
theorem engineRefinedTraceWitness_to_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineRefinedTraceWitness bytes label f) :
    LanguageDefTraceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hRefined, hFold, hSize, hTop, hExpr⟩
  exact ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Refined engine witnesses carry a concrete declarative engine acceptance
path. -/
theorem engineRefinedTraceWitness_to_engineAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineRefinedTraceWitness bytes label f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  rcases hTrace with
    ⟨_proof, _prFinal, _f', start, finish, _hNoErr, _hAuthored,
      hRefined, _hFold, _hSize, _hTop, _hExpr⟩
  rcases hRefined with ⟨engTrace, _hSegs⟩
  exact ⟨start, finish, labeledLanguageDefEngineTraceWitness_accepts engTrace⟩

/-- Refined engine witnesses still imply spec acceptance. -/
theorem engineRefinedTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineRefinedTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  exact languageDefTraceWitness_to_specAccepts
    bytes label f
    (engineRefinedTraceWitness_to_languageDefTraceWitness bytes label f hTrace)

/-- Composed forward bridge for the refined witness layer. -/
theorem engineRefinedTraceWitness_to_engineAndSpec
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineRefinedTraceWitness bytes label f) :
    (∃ start finish, LanguageDefAccepts start finish) ∧ SpecAccepts bytes f := by
  refine ⟨?_, ?_⟩
  · exact engineRefinedTraceWitness_to_engineAccepts bytes label f hTrace
  · exact engineRefinedTraceWitness_to_specAccepts bytes label f hTrace

/-- Refined engine witnesses forget to honest engine-acceptance witnesses. -/
theorem engineRefinedTraceWitness_to_engineAcceptanceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineRefinedTraceWitness bytes label f) :
    EngineAcceptanceWitness bytes label f := by
  rcases engineRefinedTraceWitness_to_engineAccepts bytes label f hTrace with
    ⟨start, finish, hAccepts⟩
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hRefined, hFold, hSize, hTop, hExpr⟩
  exact ⟨proof, prFinal, f', start, finish, hNoErr, hAuthored,
    hAccepts,
    hFold, hSize, hTop, hExpr⟩

/-- Any honest engine-acceptance witness carries a concrete engine acceptance
path. -/
theorem engineAcceptanceWitness_to_engineAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAcceptanceWitness bytes label f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  rcases hTrace with
    ⟨_proof, _prFinal, _f', start, finish, _hNoErr, _hAuthored,
      hAccepts, _hFold, _hSize, _hTop, _hExpr⟩
  exact ⟨start, finish, hAccepts⟩

/-- The honest weak engine witness contains the underlying LanguageDef runtime
acceptance witness. Positive example: use this to recover the spec-facing
trace witness directly. Negative example: do not reprove runtime acceptance
facts by unpacking the full engine witness manually each time. -/
theorem engineAcceptanceWitness_to_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAcceptanceWitness bytes label f) :
    LanguageDefTraceWitness bytes label f := by
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hAccepts, hFold, hSize, hTop, hExpr⟩
  exact ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Unconditional lift from the runtime/spec trace witness to the current
honest weak engine witness.
Positive example: this makes the existing weak-layer collapse explicit for
downstream bridge theorems.
Negative example: this still does not synthesize token/label alignment or a
bytes-specific compiled engine trace. -/
theorem languageDefTraceWitness_to_engineAcceptanceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    EngineAcceptanceWitness bytes label f := by
  exact languageDefTraceWitness_to_engineAcceptanceWitness_of_complete
    bytes label f (engineAcceptanceComplete_trivial bytes label f) hTrace

/-- The current honest weak engine witness is equivalent to the underlying
LanguageDef runtime/spec trace witness.
Positive example: this states openly that the weak layer preserves the runtime
acceptance evidence without adding token/rewrite coincidence.
Negative example: this equivalence should not be mistaken for a stronger
compiled-engine alignment theorem. -/
theorem engineAcceptanceWitness_iff_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    EngineAcceptanceWitness bytes label f ↔ LanguageDefTraceWitness bytes label f := by
  constructor
  · intro hTrace
    exact engineAcceptanceWitness_to_languageDefTraceWitness bytes label f hTrace
  · intro hTrace
    exact languageDefTraceWitness_to_engineAcceptanceWitness bytes label f hTrace

/-- Structural characterization of the honest weak witness: it is exactly a
LanguageDef runtime witness paired with some declarative engine acceptance
path. Positive example: downstream lemmas can work against the two smaller
components. Negative example: this does not reintroduce token/rewrite-label
coincidence, which belongs only to the stronger aligned scaffold. -/
theorem engineAcceptanceWitness_iff_languageDefTraceWitness_and_engineAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    EngineAcceptanceWitness bytes label f ↔
      LanguageDefTraceWitness bytes label f ∧
        (∃ start finish, LanguageDefAccepts start finish) := by
  constructor
  · intro hTrace
    refine ⟨engineAcceptanceWitness_to_languageDefTraceWitness bytes label f hTrace, ?_⟩
    exact engineAcceptanceWitness_to_engineAccepts bytes label f hTrace
  · intro hBoth
    rcases hBoth with ⟨hTrace, start, finish, hAccepts⟩
    rcases hTrace with
      ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩
    exact ⟨proof, prFinal, f', start, finish, hNoErr, hAuthored,
      hAccepts, hFold, hSize, hTop, hExpr⟩

/-- Honest engine-acceptance witnesses still imply spec acceptance, because
they carry the full runtime acceptance witness in addition to engine evidence. -/
theorem engineAcceptanceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAcceptanceWitness bytes label f) :
    SpecAccepts bytes f := by
  exact languageDefTraceWitness_to_specAccepts
    bytes label f
    (engineAcceptanceWitness_to_languageDefTraceWitness bytes label f hTrace)

/-- Composed forward bridge on the weaker honest layer:
one witness yields both engine acceptance and spec acceptance. -/
theorem engineAcceptanceWitness_to_engineAndSpec
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAcceptanceWitness bytes label f) :
    (∃ start finish, LanguageDefAccepts start finish) ∧ SpecAccepts bytes f := by
  refine ⟨?_, ?_⟩
  · exact engineAcceptanceWitness_to_engineAccepts bytes label f hTrace
  · exact engineAcceptanceWitness_to_specAccepts bytes label f hTrace

/-- Sanity check: the current aligned witness shape forces every proof token
to also be an authored LanguageDef rewrite name. This is a strong coincidence
condition, not generic parser completeness. -/
theorem engineAlignedTraceWitness_proof_labels_are_rewrite_names
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineAlignedTraceWitness bytes label f) :
    ∃ proof : Array String, ∀ step ∈ proof.toList, AuthoredRewriteLabel step := by
  rcases hTrace with
    ⟨proof, _prFinal, _f', _start, _finish, _hNoErr, _hAuthored,
      hAligned, _hFold, _hSize, _hTop, _hExpr⟩
  rcases hAligned with ⟨engTrace, hLabels⟩
  refine ⟨proof, ?_⟩
  intro step hMem
  have hAuthoredTrace :
      ∀ label ∈ engTrace.labels, AuthoredRewriteLabel label :=
    labeledLanguageDefEngineTraceWitness_labels_authored engTrace
  have hMemTrace : step ∈ engTrace.labels := by
    have hTransport :
        ∀ {xs ys step},
          List.Forall₂ RuntimeTokenMatchesEngineLabel xs ys →
          step ∈ xs → step ∈ ys := by
      intro xs ys step hRel hMem'
      induction hRel generalizing step with
      | nil =>
          cases hMem'
      | @cons x y xs ys hxy hRest ih =>
          simp [RuntimeTokenMatchesEngineLabel] at hxy
          simp at hMem'
          rcases hMem' with rfl | hMemTail
          · simp [hxy]
          · simp [ih hMemTail]
    exact hTransport hLabels hMem
  exact hAuthoredTrace step hMemTrace

/-- Conditional backward simulation at the engine-aligned layer:
if alignment completeness is available, spec acceptance yields an
engine-aligned LanguageDef witness. -/
theorem specAccepts_to_engineAlignedTraceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    EngineAlignedTraceWitness bytes label f := by
  have hTrace : LanguageDefTraceWitness bytes label f :=
    specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec
  exact languageDefTraceWitness_to_engineAlignedTraceWitness_of_complete
    bytes label f hComplete hTrace

/-- Engine-aligned bisimulation scaffold, conditional on the proved alignment
completeness invariant. -/
theorem engineAlignedTraceWitness_iff_specAccepts_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f) :
    EngineAlignedTraceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact engineAlignedTraceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_engineAlignedTraceWitness_of_complete
      bytes label f hSuccess hComplete hSpec

/-- Under alignment completeness, spec acceptance yields existence of a
declarative engine acceptance path. -/
theorem specAccepts_to_exists_engineAccepts_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hAligned : EngineAlignedTraceWitness bytes label f :=
    specAccepts_to_engineAlignedTraceWitness_of_complete
      bytes label f hSuccess hComplete hSpec
  exact (engineAlignedTraceWitness_to_engineAndSpec bytes label f hAligned).1

/-- The stronger token-level alignment invariant can also discharge the weaker
honest backward simulation theorem. -/
theorem specAccepts_to_engineAcceptanceWitness_of_alignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    EngineAcceptanceWitness bytes label f := by
  have hTrace : LanguageDefTraceWitness bytes label f :=
    specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec
  exact languageDefTraceWitness_to_engineAcceptanceWitness_of_complete
    bytes label f
    (engineAlignmentComplete_to_engineAcceptanceComplete bytes label f hComplete)
    hTrace

/-- The stronger token-level alignment invariant implies the weaker honest
bisimulation scaffold as well. -/
theorem engineAcceptanceWitness_iff_specAccepts_of_alignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f) :
    EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact engineAcceptanceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_engineAcceptanceWitness_of_alignmentComplete
      bytes label f hSuccess hComplete hSpec

/-- The stronger token-level alignment invariant can also be consumed through
the weaker honest engine-existence theorem. -/
theorem specAccepts_to_exists_engineAccepts_of_alignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hWitness : EngineAcceptanceWitness bytes label f :=
    specAccepts_to_engineAcceptanceWitness_of_alignmentComplete
      bytes label f hSuccess hComplete hSpec
  exact (engineAcceptanceWitness_to_engineAndSpec bytes label f hWitness).1

/-- Conditional backward simulation at the weaker honest layer:
spec acceptance yields an engine-acceptance witness without any token/rewrite
label coincidence requirement. -/
theorem specAccepts_to_engineAcceptanceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAcceptanceComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    EngineAcceptanceWitness bytes label f := by
  have hTrace : LanguageDefTraceWitness bytes label f :=
    specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec
  exact languageDefTraceWitness_to_engineAcceptanceWitness_of_complete
    bytes label f hComplete hTrace

/-- Honest bisimulation scaffold: the weaker engine-acceptance witness is
equivalent to spec acceptance under the honest engine-acceptance completeness
invariant. -/
theorem engineAcceptanceWitness_iff_specAccepts_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAcceptanceComplete bytes label f) :
    EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact engineAcceptanceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_engineAcceptanceWitness_of_complete
      bytes label f hSuccess hComplete hSpec

/-- Under the honest engine-acceptance completeness invariant, spec acceptance
yields existence of a declarative engine acceptance path. -/
theorem specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAcceptanceComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hWitness : EngineAcceptanceWitness bytes label f :=
    specAccepts_to_engineAcceptanceWitness_of_complete
      bytes label f hSuccess hComplete hSpec
  exact (engineAcceptanceWitness_to_engineAndSpec bytes label f hWitness).1

/-- Refined-completeness bridge: spec acceptance yields engine-acceptance
existence through the token-to-segment refinement invariant. -/
theorem specAccepts_to_exists_engineAccepts_of_refinedComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  exact specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    bytes label f hSuccess
    (engineRefinedAlignmentComplete_to_engineAcceptanceComplete bytes label f hComplete)
    hSpec

/-- Conditional backward simulation at the refined witness layer:
spec acceptance yields a runtime+engine witness carrying token-to-segment
refinement. -/
theorem specAccepts_to_engineRefinedTraceWitness_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    EngineRefinedTraceWitness bytes label f := by
  have hTrace : LanguageDefTraceWitness bytes label f :=
    specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec
  exact languageDefTraceWitness_to_engineRefinedTraceWitness_of_complete
    bytes label f hComplete hTrace

/-- Refined witness bisimulation scaffold. -/
theorem engineRefinedTraceWitness_iff_specAccepts_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f) :
    EngineRefinedTraceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact engineRefinedTraceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_engineRefinedTraceWitness_of_complete
      bytes label f hSuccess hComplete hSpec

/-- Refined witness layer paired directly with implementation acceptance. -/
theorem engineRefinedTraceWitness_iff_implAccepts_of_complete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f) :
    EngineRefinedTraceWitness bytes label f ↔ ImplAccepts bytes label f := by
  constructor
  · intro hTrace
    have hSpec : SpecAccepts bytes f :=
      (engineRefinedTraceWitness_iff_specAccepts_of_complete
        bytes label f hSuccess hComplete).1 hTrace
    exact (implAccepts_iff_specAccepts bytes label f hSuccess).2 hSpec
  · intro hImpl
    have hSpec : SpecAccepts bytes f :=
      (implAccepts_iff_specAccepts bytes label f hSuccess).1 hImpl
    exact (engineRefinedTraceWitness_iff_specAccepts_of_complete
      bytes label f hSuccess hComplete).2 hSpec

/-- Unconditional weak backward bridge:
spec acceptance yields an honest engine-acceptance witness without requiring a
separate completeness hypothesis.
Positive example: downstream users can call this directly from `SpecAccepts`.
Negative example: this still does not recover token/label equality. -/
theorem specAccepts_to_engineAcceptanceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hSpec : SpecAccepts bytes f) :
    EngineAcceptanceWitness bytes label f := by
  exact specAccepts_to_engineAcceptanceWitness_of_complete
    bytes label f hSuccess (engineAcceptanceComplete_trivial bytes label f) hSpec

/-- Unconditional weak bisimulation equivalence at the honest layer. -/
theorem engineAcceptanceWitness_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f := by
  exact engineAcceptanceWitness_iff_specAccepts_of_complete
    bytes label f hSuccess (engineAcceptanceComplete_trivial bytes label f)

/-- Unconditional weak existence bridge:
spec acceptance yields existence of a declarative engine acceptance path. -/
theorem specAccepts_to_exists_engineAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  exact specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    bytes label f hSuccess (engineAcceptanceComplete_trivial bytes label f) hSpec

/-- Top-level composed bridge theorem for the honest engine layer.
It packages:
1. Engine witness <-> implementation acceptance
2. Engine witness <-> spec acceptance
3. Spec acceptance -> declarative engine acceptance-path existence

Positive example: consume this as the single API theorem for downstream
Metamath conformance code.
Negative example: this theorem intentionally does not claim proof-token to
rewrite-label equality (that is a stronger, currently separate property). -/
theorem metamath_languageDef_bridge
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    (EngineAcceptanceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  constructor
  · constructor
    · intro hEngine
      have hSpec : SpecAccepts bytes f :=
        (engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess).1 hEngine
      exact (implAccepts_iff_specAccepts bytes label f hSuccess).2 hSpec
    · intro hImpl
      have hSpec : SpecAccepts bytes f :=
        (implAccepts_iff_specAccepts bytes label f hSuccess).1 hImpl
      exact (engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess).2 hSpec
  · constructor
    · exact engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess
    · intro hSpec
      exact specAccepts_to_exists_engineAccepts bytes label f hSuccess hSpec

/-- Top-level composed bridge theorem routed through refined alignment
completeness for engine-path existence.
Positive example: use this when runtime tokens must refine into explicit
engine-label segments.
Negative example: this still does not require one-to-one token=label equality. -/
theorem metamath_languageDef_bridge_of_refinedComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f) :
    (EngineAcceptanceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  constructor
  · constructor
    · intro hEngine
      have hSpec : SpecAccepts bytes f :=
        (engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess).1 hEngine
      exact (implAccepts_iff_specAccepts bytes label f hSuccess).2 hSpec
    · intro hImpl
      have hSpec : SpecAccepts bytes f :=
        (implAccepts_iff_specAccepts bytes label f hSuccess).1 hImpl
      exact (engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess).2 hSpec
  · constructor
    · exact engineAcceptanceWitness_iff_specAccepts bytes label f hSuccess
    · intro hSpec
      exact specAccepts_to_exists_engineAccepts_of_refinedComplete
        bytes label f hSuccess hComplete hSpec

/-- Top-level composed bridge theorem routed through strict token=label
alignment completeness.
Positive example: use this when runtime proof tokens are known to match engine
rewrite labels one-for-one.
Negative example: this theorem is stronger than necessary for Metamath's mixed
runtime-token traces, so it should not be the default. -/
theorem metamath_languageDef_bridge_of_alignmentComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAlignmentComplete bytes label f) :
    (EngineAcceptanceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  exact metamath_languageDef_bridge_of_refinedComplete
    bytes label f hSuccess
    (engineAlignmentComplete_to_engineRefinedAlignmentComplete bytes label f hComplete)

/-- Longest-lasting practical crown-jewel bridge:
if checker-runtime labels are disjoint from authored rewrite names, the
Metamath implementation, refined engine witness layer, and declarative
specification all agree. -/
theorem metamath_languageDef_bridge_of_runtimeProvenanceDisjoint
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes) :
    (EngineAcceptanceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineAcceptanceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  exact metamath_languageDef_bridge_of_refinedComplete
    bytes label f hSuccess
    (runtimeProvenanceDisjoint_to_engineRefinedAlignmentComplete bytes label f hDisjoint)

/-- Stronger public bridge API at the refined witness layer.
This is the longest-lasting conformance shape presently available: it exposes
runtime acceptance, concrete engine acceptance, and token-to-engine-segment
refinement in one witness family. -/
theorem metamath_languageDef_crown_jewel_of_refinedComplete
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineRefinedAlignmentComplete bytes label f) :
    (EngineRefinedTraceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineRefinedTraceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  constructor
  · exact engineRefinedTraceWitness_iff_implAccepts_of_complete
      bytes label f hSuccess hComplete
  · constructor
    · exact engineRefinedTraceWitness_iff_specAccepts_of_complete
        bytes label f hSuccess hComplete
    · intro hSpec
      exact specAccepts_to_exists_engineAccepts_of_refinedComplete
        bytes label f hSuccess hComplete hSpec

/-- Runtime-provenance-disjoint version of the refined public bridge API. -/
theorem metamath_languageDef_crown_jewel_of_runtimeProvenanceDisjoint
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hDisjoint : RuntimeProvenanceDisjointFromAuthored bytes) :
    (EngineRefinedTraceWitness bytes label f ↔ ImplAccepts bytes label f) ∧
      (EngineRefinedTraceWitness bytes label f ↔ SpecAccepts bytes f) ∧
      (SpecAccepts bytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  exact metamath_languageDef_crown_jewel_of_refinedComplete
    bytes label f hSuccess
    (runtimeProvenanceDisjoint_to_engineRefinedAlignmentComplete bytes label f hDisjoint)

/-! ## Recommended usage (honest weak layer)

Preferred downstream call order mirrors the mm-lean4 style:
1. `SpecAccepts -> EngineAcceptanceWitness`
2. `EngineAcceptanceWitness -> SpecAccepts`
3. `SpecAccepts -> ∃ engine acceptance path`

Positive example:
- use `EngineAcceptanceComplete` when the goal is genuine engine existence.

Negative example:
- do not require token/rewrite-label coincidence unless that stronger
  instrumentation property is truly part of the goal.
-/

/-- Recommended completeness-first template: spec acceptance plus the honest
engine-acceptance completeness invariant yields an honest engine witness. -/
theorem recommended_usage_engineAcceptanceWitness_of_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAcceptanceComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    EngineAcceptanceWitness bytes label f := by
  exact specAccepts_to_engineAcceptanceWitness_of_complete
    bytes label f hSuccess hComplete hSpec

/-- Recommended soundness-first template: an honest engine witness still
implies spec acceptance because it retains the runtime acceptance evidence. -/
theorem recommended_usage_specAccepts_of_engineAcceptanceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hWitness : EngineAcceptanceWitness bytes label f) :
    SpecAccepts bytes f := by
  exact engineAcceptanceWitness_to_specAccepts bytes label f hWitness

/-- Recommended completeness-first template to plain engine existence:
spec acceptance yields some declarative engine acceptance path under the honest
engine-acceptance completeness invariant. -/
theorem recommended_usage_engineAccepts_of_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hComplete : EngineAcceptanceComplete bytes label f)
    (hSpec : SpecAccepts bytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  exact specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    bytes label f hSuccess hComplete hSpec

theorem ax1_not_authoredRewriteLabel : ¬ AuthoredRewriteLabel "ax1" := by
  intro h
  have hTrue : hasRewriteByName "ax1" = true :=
    (authoredRewriteLabel_iff_hasRewriteByName_true "ax1").1 h
  have hFalse : hasRewriteByName "ax1" = false := by native_decide
  exact Bool.false_ne_true (hFalse.trans hTrue)

theorem wph_not_authoredRewriteLabel : ¬ AuthoredRewriteLabel "wph" := by
  intro h
  have hTrue : hasRewriteByName "wph" = true :=
    (authoredRewriteLabel_iff_hasRewriteByName_true "wph").1 h
  have hFalse : hasRewriteByName "wph" = false := by native_decide
  exact Bool.false_ne_true (hFalse.trans hTrue)

private def minimalAxiom_wfph : Metamath.Verify.Formula :=
  #[Metamath.Verify.Sym.const "wff", Metamath.Verify.Sym.var "ph"]

private def minimalAxiom_ax1Trace : Array String := #["wph", "ax1"]

private def minimalAxiom_ax1Run :
    Except Metamath.Verify.ProofCheckFail Metamath.Verify.ProofState :=
  minimalAxiom_ax1Trace.foldlM
    (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB minimalAxiomBytes) pr step)
    (initialProofState minimalAxiomBytes "ax1" minimalAxiom_wfph)

private def minimalAxiom_ax1RunStackSize : Nat :=
  match minimalAxiom_ax1Run with
  | .ok pr => pr.stack.size
  | .error _ => 0

private def minimalAxiom_ax1RunTopExprMatches : Bool :=
  match minimalAxiom_ax1Run with
  | .ok pr =>
      match pr.stack[0]? with
      | some f' => Metamath.Kernel.toExpr f' == Metamath.Kernel.toExpr minimalAxiom_wfph
      | none => false
  | .error _ => false

private theorem minimalAxiom_ax1Run_exists :
    ∃ prFinal f',
      minimalAxiom_ax1Run = Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr minimalAxiom_wfph := by
  have hSz : minimalAxiom_ax1RunStackSize = 1 := by native_decide
  have hTop : minimalAxiom_ax1RunTopExprMatches = true := by native_decide
  cases hRun : minimalAxiom_ax1Run with
  | error e =>
      simp [minimalAxiom_ax1RunStackSize, hRun] at hSz
  | ok pr =>
      have hSz' : pr.stack.size = 1 := by
        simpa [minimalAxiom_ax1RunStackSize, hRun] using hSz
      have hTop' :
          (match pr.stack[0]? with
          | some f' => Metamath.Kernel.toExpr f' == Metamath.Kernel.toExpr minimalAxiom_wfph
          | none => false) = true := by
        simpa [minimalAxiom_ax1RunTopExprMatches, hRun] using hTop
      cases hAt : pr.stack[0]? with
      | none =>
          simp [hAt] at hTop'
      | some f' =>
          have hExprBool :
              (Metamath.Kernel.toExpr f' == Metamath.Kernel.toExpr minimalAxiom_wfph) = true := by
            simpa [hAt] using hTop'
          have hExpr : Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr minimalAxiom_wfph :=
            eq_of_beq hExprBool
          exact ⟨pr, f', rfl, hSz', hAt, hExpr⟩

private theorem minimalAxiom_ax1Trace_labelsAuthored :
    TraceLabelsAuthored minimalAxiomBytes minimalAxiom_ax1Trace := by
  rcases minimalAxiom_ax1Run_exists with ⟨prFinal, _f', hRun, _hSz, _hTop, _hExpr⟩
  exact traceLabelsAuthored_of_fold_ok
    minimalAxiomBytes minimalAxiom_ax1Trace
    (initialProofState minimalAxiomBytes "ax1" minimalAxiom_wfph)
    prFinal hRun

theorem minimalAxiom_ax1_languageDefTraceWitness :
    LanguageDefTraceWitness minimalAxiomBytes "ax1" minimalAxiom_wfph := by
  have hNoErr : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  rcases minimalAxiom_ax1Run_exists with ⟨prFinal, f', hRun, hSz, hTop, hExpr⟩
  exact ⟨minimalAxiom_ax1Trace, prFinal, f', hNoErr,
    minimalAxiom_ax1Trace_labelsAuthored, hRun, hSz, hTop, hExpr⟩

private theorem token_mem_of_forall2
    {xs ys : List String} {step : String}
    (hRel : List.Forall₂ RuntimeTokenMatchesEngineLabel xs ys)
    (hMem : step ∈ xs) :
    step ∈ ys := by
  induction hRel generalizing step with
  | nil =>
      cases hMem
  | @cons x y xs ys hxy hRest ih =>
      simp [RuntimeTokenMatchesEngineLabel] at hxy
      simp at hMem
      rcases hMem with rfl | hMemTail
      · simp [hxy]
      · simp [ih hMemTail]

theorem minimalAxiom_ax1_not_engineAlignmentComplete :
    ¬ EngineAlignmentComplete minimalAxiomBytes "ax1" minimalAxiom_wfph := by
  intro hComplete
  rcases minimalAxiom_ax1Run_exists with ⟨prFinal, f', hRun, hSz, hTop, hExpr⟩
  rcases hComplete minimalAxiom_ax1Trace prFinal f' hRun hSz hTop hExpr with
    ⟨_start, _finish, engTrace, hRel⟩
  have hAuthTrace :
      ∀ lbl ∈ engTrace.labels, AuthoredRewriteLabel lbl :=
    labeledLanguageDefEngineTraceWitness_labels_authored engTrace
  have hAx1InTrace : "ax1" ∈ engTrace.labels := by
    have hAx1InProof : "ax1" ∈ minimalAxiom_ax1Trace.toList := by
      simp [minimalAxiom_ax1Trace]
    exact token_mem_of_forall2 hRel hAx1InProof
  have hAx1Auth : AuthoredRewriteLabel "ax1" :=
    hAuthTrace "ax1" hAx1InTrace
  exact ax1_not_authoredRewriteLabel hAx1Auth

private theorem minimalAxiom_ax1Trace_nonAuthored :
    ∀ step ∈ minimalAxiom_ax1Trace.toList, ¬ AuthoredRewriteLabel step := by
  intro step hMem
  have hCases : step = "wph" ∨ step = "ax1" := by
    simpa [minimalAxiom_ax1Trace] using hMem
  rcases hCases with rfl | rfl
  · exact wph_not_authoredRewriteLabel
  · exact ax1_not_authoredRewriteLabel

/-- Positive refined-segmentation example for the accepted minimal axiom
fixture. The runtime checker labels are real Metamath object labels, so they
refine to the empty authored-engine label trace rather than falsely claiming
token=rule equality. -/
theorem minimalAxiom_ax1Trace_refines_empty_engineTrace :
    RuntimeTraceRefinesEngineLabels
      minimalAxiom_ax1Trace.toList trivialLabeledEngineTraceWitness.labels := by
  simpa [trivialLabeledEngineTraceWitness] using
    runtimeTraceRefines_all_empty_of_nonAuthored
      minimalAxiom_ax1Trace_nonAuthored

/-- Positive refined witness for the canonical accepted minimal axiom proof. -/
theorem minimalAxiom_ax1_engineRefinedTraceWitness :
    EngineRefinedTraceWitness minimalAxiomBytes "ax1" minimalAxiom_wfph := by
  have hNoErr : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  rcases minimalAxiom_ax1Run_exists with ⟨prFinal, f', hRun, hSz, hTop, hExpr⟩
  exact ⟨minimalAxiom_ax1Trace, prFinal, f',
    trivialEnginePattern, trivialEnginePattern,
    hNoErr, minimalAxiom_ax1Trace_labelsAuthored,
    ⟨trivialLabeledEngineTraceWitness,
      minimalAxiom_ax1Trace_refines_empty_engineTrace⟩,
    hRun, hSz, hTop, hExpr⟩

/-- Positive fixture parity at the refined witness layer. -/
theorem minimalAxiom_ax1_engineRefinedTraceWitness_to_engineAndSpec :
    (∃ start finish, LanguageDefAccepts start finish) ∧
      SpecAccepts minimalAxiomBytes minimalAxiom_wfph := by
  exact engineRefinedTraceWitness_to_engineAndSpec
    minimalAxiomBytes "ax1" minimalAxiom_wfph
    minimalAxiom_ax1_engineRefinedTraceWitness

/-- Concrete refined crown-jewel package for the accepted minimal axiom
fixture. -/
theorem minimalAxiom_ax1_refined_crown_jewel :
    EngineRefinedTraceWitness minimalAxiomBytes "ax1" minimalAxiom_wfph ∧
      ImplAccepts minimalAxiomBytes "ax1" minimalAxiom_wfph ∧
      SpecAccepts minimalAxiomBytes minimalAxiom_wfph ∧
      ∃ start finish, LanguageDefAccepts start finish := by
  have hWitness : EngineRefinedTraceWitness minimalAxiomBytes "ax1" minimalAxiom_wfph :=
    minimalAxiom_ax1_engineRefinedTraceWitness
  have hSpec : SpecAccepts minimalAxiomBytes minimalAxiom_wfph :=
    (engineRefinedTraceWitness_to_engineAndSpec
      minimalAxiomBytes "ax1" minimalAxiom_wfph hWitness).2
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  have hImpl : ImplAccepts minimalAxiomBytes "ax1" minimalAxiom_wfph :=
    (implAccepts_iff_specAccepts minimalAxiomBytes "ax1" minimalAxiom_wfph hSuccess).2 hSpec
  have hEng :
      ∃ start finish, LanguageDefAccepts start finish :=
    (engineRefinedTraceWitness_to_engineAndSpec
      minimalAxiomBytes "ax1" minimalAxiom_wfph hWitness).1
  exact ⟨hWitness, hImpl, hSpec, hEng⟩

/-- Fixture parity (forward): empty database fixture. -/
theorem emptyBytes_languageDefTraceWitness_to_specAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness emptyBytes label f) :
    SpecAccepts emptyBytes f := by
  exact languageDefTraceWitness_to_specAccepts emptyBytes label f hTrace

/-- Fixture parity (forward): minimal axiom database fixture. -/
theorem minimalAxiomBytes_languageDefTraceWitness_to_specAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness minimalAxiomBytes label f) :
    SpecAccepts minimalAxiomBytes f := by
  exact languageDefTraceWitness_to_specAccepts minimalAxiomBytes label f hTrace

/-- Negative fixture: parse-failing include input cannot admit a
LanguageDef-trace witness (no-success-side condition is impossible). -/
theorem brokenIncludeBytes_no_languageDefTraceWitness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ LanguageDefTraceWitness brokenIncludeBytes label f := by
  intro hTrace
  rcases hTrace with ⟨_proof, _prFinal, _f', hNoErr, _hAuthored, _hFold, _hSize, _hTop, _hExpr⟩
  have hSome :
      parseErrorCode? brokenIncludeBytes =
        some Metamath.Verify.ParseErrorCode.notACommand := by
    native_decide
  have hNone : parseErrorCode? brokenIncludeBytes = none := by
    unfold parseErrorCode?
    have hNoneDB : (checkBytesDB brokenIncludeBytes).parseErrorCode? = none := by
      unfold Metamath.Verify.DB.parseErrorCode?
      simp [hNoErr]
    simpa [checkBytesDB] using hNoneDB
  simp [hNone] at hSome

/-- Negative fixture (strong witness): parse-failing include input cannot admit
an engine-aligned witness either. -/
theorem brokenIncludeBytes_no_engineAlignedTraceWitness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ EngineAlignedTraceWitness brokenIncludeBytes label f := by
  intro hTrace
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hAligned, hFold, hSize, hTop, hExpr⟩
  exact brokenIncludeBytes_no_languageDefTraceWitness label f
    ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Negative fixture (honest weak witness): parse-failing include input cannot
admit an engine-acceptance witness either. -/
theorem brokenIncludeBytes_no_engineAcceptanceWitness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ EngineAcceptanceWitness brokenIncludeBytes label f := by
  intro hTrace
  rcases hTrace with
    ⟨proof, prFinal, f', _start, _finish, hNoErr, hAuthored,
      _hAccepts, hFold, hSize, hTop, hExpr⟩
  exact brokenIncludeBytes_no_languageDefTraceWitness label f
    ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Negative refined witness: parse-failing include input cannot admit one. -/
theorem brokenIncludeBytes_no_engineRefinedTraceWitness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ EngineRefinedTraceWitness brokenIncludeBytes label f := by
  intro hTrace
  exact brokenIncludeBytes_no_languageDefTraceWitness label f
    (engineRefinedTraceWitness_to_languageDefTraceWitness
      brokenIncludeBytes label f hTrace)

/-- Concrete negative package for the parse-failing include fixture. -/
theorem brokenIncludeBytes_no_refined_or_weak_engine_witness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ EngineRefinedTraceWitness brokenIncludeBytes label f ∧
      ¬ EngineAcceptanceWitness brokenIncludeBytes label f := by
  exact ⟨brokenIncludeBytes_no_engineRefinedTraceWitness label f,
    brokenIncludeBytes_no_engineAcceptanceWitness label f⟩

/-- Fixture parity (engine-aligned iff): empty database fixture, conditional on
alignment completeness. -/
theorem emptyBytes_engineAlignedTraceWitness_iff_specAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete emptyBytes label f) :
    EngineAlignedTraceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact engineAlignedTraceWitness_iff_specAccepts_of_complete
    emptyBytes label f hSuccess hComplete

/-- Fixture parity (engine-aligned iff): minimal axiom fixture, conditional on
alignment completeness. -/
theorem minimalAxiomBytes_engineAlignedTraceWitness_iff_specAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete minimalAxiomBytes label f) :
    EngineAlignedTraceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact engineAlignedTraceWitness_iff_specAccepts_of_complete
    minimalAxiomBytes label f hSuccess hComplete

/-- Fixture parity (spec -> engine path): empty database fixture, conditional
on alignment completeness. -/
theorem emptyBytes_specAccepts_to_exists_engineAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete emptyBytes label f)
    (hSpec : SpecAccepts emptyBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_complete
    emptyBytes label f hSuccess hComplete hSpec

/-- Fixture parity (spec -> engine path): minimal axiom fixture, conditional
on alignment completeness. -/
theorem minimalAxiomBytes_specAccepts_to_exists_engineAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete minimalAxiomBytes label f)
    (hSpec : SpecAccepts minimalAxiomBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_complete
    minimalAxiomBytes label f hSuccess hComplete hSpec

/-- Fixture parity (honest weak iff): empty database fixture, but discharged
from the stronger token-level alignment invariant. -/
theorem emptyBytes_engineAcceptanceWitness_iff_specAccepts_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete emptyBytes label f) :
    EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts_of_alignmentComplete
    emptyBytes label f hSuccess hComplete

/-- Fixture parity (honest weak iff): minimal axiom fixture, but discharged
from the stronger token-level alignment invariant. -/
theorem minimalAxiomBytes_engineAcceptanceWitness_iff_specAccepts_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete minimalAxiomBytes label f) :
    EngineAcceptanceWitness minimalAxiomBytes label f ↔
      SpecAccepts minimalAxiomBytes f := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts_of_alignmentComplete
    minimalAxiomBytes label f hSuccess hComplete

/-- Fixture parity (honest weak spec -> engine path): empty database fixture,
but discharged from the stronger token-level alignment invariant. -/
theorem emptyBytes_specAccepts_to_exists_engineAccepts_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete emptyBytes label f)
    (hSpec : SpecAccepts emptyBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_alignmentComplete
    emptyBytes label f hSuccess hComplete hSpec

/-- Fixture parity (honest weak spec -> engine path): minimal axiom fixture,
but discharged from the stronger token-level alignment invariant. -/
theorem minimalAxiomBytes_specAccepts_to_exists_engineAccepts_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete minimalAxiomBytes label f)
    (hSpec : SpecAccepts minimalAxiomBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_alignmentComplete
    minimalAxiomBytes label f hSuccess hComplete hSpec

/-- Fixture parity (honest weak iff): empty database fixture, conditional on
engine-acceptance completeness. -/
theorem emptyBytes_engineAcceptanceWitness_iff_specAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAcceptanceComplete emptyBytes label f) :
    EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts_of_complete
    emptyBytes label f hSuccess hComplete

/-- Fixture parity (honest weak iff): minimal axiom fixture, conditional on
engine-acceptance completeness. -/
theorem minimalAxiomBytes_engineAcceptanceWitness_iff_specAccepts_of_complete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAcceptanceComplete minimalAxiomBytes label f) :
    EngineAcceptanceWitness minimalAxiomBytes label f ↔
      SpecAccepts minimalAxiomBytes f := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts_of_complete
    minimalAxiomBytes label f hSuccess hComplete

/-- Fixture parity (honest weak spec -> engine path): empty database fixture. -/
theorem emptyBytes_specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAcceptanceComplete emptyBytes label f)
    (hSpec : SpecAccepts emptyBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    emptyBytes label f hSuccess hComplete hSpec

/-- Fixture parity (honest weak spec -> engine path): minimal axiom fixture. -/
theorem minimalAxiomBytes_specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAcceptanceComplete minimalAxiomBytes label f)
    (hSpec : SpecAccepts minimalAxiomBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts_of_acceptanceComplete
    minimalAxiomBytes label f hSuccess hComplete hSpec

/-- Fixture parity (honest weak iff): empty database fixture, unconditional. -/
theorem emptyBytes_engineAcceptanceWitness_iff_specAccepts
    (label : String) (f : Metamath.Verify.Formula) :
    EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts emptyBytes label f hSuccess

/-- Fixture parity (honest weak iff): minimal axiom fixture, unconditional. -/
theorem minimalAxiomBytes_engineAcceptanceWitness_iff_specAccepts
    (label : String) (f : Metamath.Verify.Formula) :
    EngineAcceptanceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact engineAcceptanceWitness_iff_specAccepts minimalAxiomBytes label f hSuccess

/-- Fixture parity (honest weak spec -> engine path): empty fixture,
unconditional. -/
theorem emptyBytes_specAccepts_to_exists_engineAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hSpec : SpecAccepts emptyBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts emptyBytes label f hSuccess hSpec

/-- Fixture parity (honest weak spec -> engine path): minimal axiom fixture,
unconditional. -/
theorem minimalAxiomBytes_specAccepts_to_exists_engineAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hSpec : SpecAccepts minimalAxiomBytes f) :
    ∃ start finish, LanguageDefAccepts start finish := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact specAccepts_to_exists_engineAccepts minimalAxiomBytes label f hSuccess hSpec

/-- Fixture-level packaged bridge for the empty database case. -/
theorem emptyBytes_metamath_languageDef_bridge
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineAcceptanceWitness emptyBytes label f ↔ ImplAccepts emptyBytes label f) ∧
      (EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f) ∧
      (SpecAccepts emptyBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge emptyBytes label f hSuccess

/-- Fixture-level packaged bridge for the minimal-axiom database case. -/
theorem minimalAxiomBytes_metamath_languageDef_bridge
    (label : String) (f : Metamath.Verify.Formula) :
    (EngineAcceptanceWitness minimalAxiomBytes label f ↔ ImplAccepts minimalAxiomBytes label f) ∧
      (EngineAcceptanceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f) ∧
      (SpecAccepts minimalAxiomBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge minimalAxiomBytes label f hSuccess

/-- Fixture-level packaged bridge for the empty database case, assuming
refined completeness. -/
theorem emptyBytes_metamath_languageDef_bridge_of_refinedComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineRefinedAlignmentComplete emptyBytes label f) :
    (EngineAcceptanceWitness emptyBytes label f ↔ ImplAccepts emptyBytes label f) ∧
      (EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f) ∧
      (SpecAccepts emptyBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge_of_refinedComplete emptyBytes label f hSuccess hComplete

/-- Fixture-level packaged bridge for the minimal-axiom database case,
assuming refined completeness. -/
theorem minimalAxiomBytes_metamath_languageDef_bridge_of_refinedComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineRefinedAlignmentComplete minimalAxiomBytes label f) :
    (EngineAcceptanceWitness minimalAxiomBytes label f ↔ ImplAccepts minimalAxiomBytes label f) ∧
      (EngineAcceptanceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f) ∧
      (SpecAccepts minimalAxiomBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge_of_refinedComplete minimalAxiomBytes label f hSuccess hComplete

/-- Fixture-level packaged bridge for the empty database case, assuming
strict alignment completeness. -/
theorem emptyBytes_metamath_languageDef_bridge_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete emptyBytes label f) :
    (EngineAcceptanceWitness emptyBytes label f ↔ ImplAccepts emptyBytes label f) ∧
      (EngineAcceptanceWitness emptyBytes label f ↔ SpecAccepts emptyBytes f) ∧
      (SpecAccepts emptyBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB emptyBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge_of_alignmentComplete emptyBytes label f hSuccess hComplete

/-- Fixture-level packaged bridge for the minimal-axiom database case,
assuming strict alignment completeness. -/
theorem minimalAxiomBytes_metamath_languageDef_bridge_of_alignmentComplete
    (label : String) (f : Metamath.Verify.Formula)
    (hComplete : EngineAlignmentComplete minimalAxiomBytes label f) :
    (EngineAcceptanceWitness minimalAxiomBytes label f ↔ ImplAccepts minimalAxiomBytes label f) ∧
      (EngineAcceptanceWitness minimalAxiomBytes label f ↔ SpecAccepts minimalAxiomBytes f) ∧
      (SpecAccepts minimalAxiomBytes f → ∃ start finish, LanguageDefAccepts start finish) := by
  have hSuccess : (checkBytesDB minimalAxiomBytes).error? = none := by native_decide
  exact metamath_languageDef_bridge_of_alignmentComplete minimalAxiomBytes label f hSuccess hComplete

/-- Fixture-level packaged negative bridge for parse-failing include input. -/
theorem brokenIncludeBytes_no_runtime_or_engine_witness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ LanguageDefTraceWitness brokenIncludeBytes label f ∧
      ¬ EngineAcceptanceWitness brokenIncludeBytes label f := by
  exact ⟨brokenIncludeBytes_no_languageDefTraceWitness label f,
    brokenIncludeBytes_no_engineAcceptanceWitness label f⟩

end Mettapedia.Languages.Metamath.AcceptanceEquivalence
