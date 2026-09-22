import Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-!
# WM calculus: denotational readings and subject reduction

A `WMReading` interprets the sorted WM-calculus terms (`WMTerm`: `Revise`,
`Extract`, `Combine`, `EvidenceZero`, named atoms) by world-model operations,
an evidence algebra, and atom valuations.  `denote` is the fold of a reading
over a term.  `Agree` compares values sort by sort: states agree when every
extraction agrees; queries and evidence agree when equal.

Under `CoreLaws` (extraction sends revision to combination; combination is
commutative, associative, with right unit `EvidenceZero`) every root `WMStep`
preserves the denotation up to `Agree`.  Through `wmStepStar_complete` this
covers every `wmCoreLanguageDef` reduct of an encoded term, and the minimal
six-axis vertex has the same one-step relation as the core.

The denotation is compositional: `DenotationsAgree` is a `WMTermCongruence`
as soon as `Revise` respects state agreement in each argument
(`ReviseRespectsAgree`).  The other four argument positions are congruences by
the definition of `Agree` alone, and `CoreLaws.extract_revise` implies
`ReviseRespectsAgree`, so `CoreLaws` needs no additional law.  Consequently
every step of the contextual presentation
`wmExtVertexLanguageDefWithCong wmExtVertexMinimal`, at any depth, preserves
the denotation of an encoded term.

Root subject reduction alone already preserves every observation the calculus
names (`namedQueryAgree_of_contextStep_of_root`): extraction at query atoms,
and evidence.  `ReviseRespectsAgree` is what extends state agreement to
queries of the carrier that no atom names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusContextEncoding

/-! ## Readings of the WM calculus -/

/-- Values of the three WM-calculus sorts. -/
abbrev SortValue (State Query V : Type) : WMSort → Type
  | .state => State
  | .query => Query
  | .evidence => V

/-- A reading of the WM-calculus signature: `Revise` and `Extract` by
world-model operations, `Combine` and `EvidenceZero` by an evidence algebra,
state and query atoms by valuations. -/
structure WMReading (State Query V : Type) where
  revise : State → State → State
  extract : State → Query → V
  combine : V → V → V
  zero : V
  world : String → State
  query : String → Query

namespace WMReading

variable {State Query V : Type} (R : WMReading State Query V)

/-- Denotation of a sorted WM-calculus term. -/
def denote : {s : WMSort} → WMTerm s → SortValue State Query V s
  | _, .state name => R.world name
  | _, .query name => R.query name
  | _, .revise first second => R.revise (denote first) (denote second)
  | _, .extract world query => R.extract (denote world) (denote query)
  | _, .combine first second => R.combine (denote first) (denote second)
  | _, .zero => R.zero

/-- Agreement of values: states agree when every extraction agrees; queries
and evidence agree when equal. -/
def Agree : (s : WMSort) → SortValue State Query V s →
    SortValue State Query V s → Prop
  | .state, first, second => ∀ query, R.extract first query = R.extract second query
  | .query, first, second => first = second
  | .evidence, first, second => first = second

theorem agree_refl : ∀ (s : WMSort) (value : SortValue State Query V s),
    R.Agree s value value
  | .state, _ => fun _ => rfl
  | .query, _ => rfl
  | .evidence, _ => rfl

theorem agree_symm : ∀ (s : WMSort) {first second : SortValue State Query V s},
    R.Agree s first second → R.Agree s second first
  | .state, _, _, agree => fun query => (agree query).symm
  | .query, _, _, agree => agree.symm
  | .evidence, _, _, agree => agree.symm

theorem agree_trans : ∀ (s : WMSort) {first second third : SortValue State Query V s},
    R.Agree s first second → R.Agree s second third → R.Agree s first third
  | .state, _, _, _, left, right => fun query => (left query).trans (right query)
  | .query, _, _, _, left, right => left.trans right
  | .evidence, _, _, _, left, right => left.trans right

/-- The laws under which the five core WM-calculus rules preserve denotation. -/
structure CoreLaws : Prop where
  extract_revise : ∀ first second query,
    R.extract (R.revise first second) query =
      R.combine (R.extract first query) (R.extract second query)
  combine_comm : ∀ first second, R.combine first second = R.combine second first
  combine_assoc : ∀ first second third,
    R.combine (R.combine first second) third =
      R.combine first (R.combine second third)
  combine_zero : ∀ value, R.combine value R.zero = value

variable {R}

/-- Subject reduction for one `WMStep`. -/
theorem CoreLaws.agree_of_step (laws : R.CoreLaws) {s : WMSort}
    {source target : WMTerm s} (step : WMStep source target) :
    R.Agree s (R.denote source) (R.denote target) := by
  cases step with
  | evidence_add first second query =>
      exact laws.extract_revise _ _ _
  | revision_comm first second =>
      intro query
      simp only [denote]
      rw [laws.extract_revise, laws.extract_revise, laws.combine_comm]
  | revision_assoc first second third =>
      intro query
      simp only [denote]
      rw [laws.extract_revise, laws.extract_revise, laws.extract_revise,
        laws.extract_revise, laws.combine_assoc]
  | combine_comm first second =>
      exact laws.combine_comm _ _
  | combine_zero value =>
      exact laws.combine_zero _

/-- Subject reduction for `WMStepStar`. -/
theorem CoreLaws.agree_of_stepStar (laws : R.CoreLaws) {s : WMSort}
    {source target : WMTerm s} (steps : WMStepStar source target) :
    R.Agree s (R.denote source) (R.denote target) := by
  induction steps with
  | refl => exact R.agree_refl s _
  | tail _ last previous =>
      exact R.agree_trans s previous (laws.agree_of_step last)

variable (R)

/-- A pattern denotes `value` at sort `s` when it encodes a sort-`s` term with
that denotation. -/
def PatternDenotes (s : WMSort) (pattern : Pattern)
    (value : SortValue State Query V s) : Prop :=
  ∃ term : WMTerm s, encodeWM term = pattern ∧ R.denote term = value

/-- Pattern denotation is functional. -/
theorem patternDenotes_unique {s : WMSort} {pattern : Pattern}
    {first second : SortValue State Query V s}
    (hasFirst : R.PatternDenotes s pattern first)
    (hasSecond : R.PatternDenotes s pattern second) : first = second := by
  obtain ⟨term, encoded, rfl⟩ := hasFirst
  obtain ⟨term', encoded', rfl⟩ := hasSecond
  rw [encodeWM_injective (encoded.trans encoded'.symm)]

variable {R}

/-- Every `wmCoreLanguageDef` reduct of an encoded term is encoded and agrees
with it. -/
theorem CoreLaws.core_reduct_agrees (laws : R.CoreLaws) {s : WMSort}
    (term : WMTerm s) {pattern : Pattern}
    (reduces : LangReducesStar wmCoreLanguageDef (encodeWM term) pattern) :
    ∃ reduct : WMTerm s, encodeWM reduct = pattern ∧
      R.Agree s (R.denote term) (R.denote reduct) := by
  obtain ⟨reduct, steps, encoded⟩ := wmStepStar_complete term pattern reduces
  exact ⟨reduct, encoded, laws.agree_of_stepStar steps⟩

/-- Every `wmCoreLanguageDef` reduct of an encoded evidence term denotes the
same evidence. -/
theorem CoreLaws.core_evidence_reduct_denotes (laws : R.CoreLaws)
    (term : WMTerm .evidence) {pattern : Pattern}
    (reduces : LangReducesStar wmCoreLanguageDef (encodeWM term) pattern) :
    R.PatternDenotes .evidence pattern (R.denote term) := by
  obtain ⟨reduct, encoded, agree⟩ := laws.core_reduct_agrees term reduces
  exact ⟨reduct, encoded, agree.symm⟩

/-! ## Compositionality -/

variable (R)

/-- Two terms of one sort have agreeing denotations. -/
def DenotationsAgree {s : WMSort} (first second : WMTerm s) : Prop :=
  R.Agree s (R.denote first) (R.denote second)

/-- `Revise` sends state agreement in either argument to state agreement. -/
structure ReviseRespectsAgree : Prop where
  left : ∀ first first' second, R.Agree .state first first' →
    R.Agree .state (R.revise first second) (R.revise first' second)
  right : ∀ first second second', R.Agree .state second second' →
    R.Agree .state (R.revise first second) (R.revise first second')

variable {R}

/-- Compositionality: when `Revise` respects state agreement, agreement of
denotations is a congruence for every constructor in every argument position.
`Extract` in its state argument respects agreement by the definition of state
agreement; `Extract` in its query argument and `Combine` in either argument
respect it because agreement is equality at those sorts. -/
theorem ReviseRespectsAgree.denotationsAgree_congruence (revise : R.ReviseRespectsAgree) :
    WMTermCongruence (fun {_} first second => R.DenotationsAgree first second) where
  revise_left := fun second agree => revise.left _ _ (R.denote second) agree
  revise_right := fun first {_ _} agree => revise.right (R.denote first) _ _ agree
  extract_left := fun query agree => agree (R.denote query)
  extract_right := fun world {_ _} agree => congrArg (R.extract (R.denote world)) agree
  combine_left := fun second agree => congrArg (R.combine · (R.denote second)) agree
  combine_right := fun first {_ _} agree => congrArg (R.combine (R.denote first)) agree

/-- Extraction sending revision to combination makes `Revise` respect state
agreement. -/
theorem CoreLaws.reviseRespectsAgree (laws : R.CoreLaws) : R.ReviseRespectsAgree where
  left first first' second agree query := by
    rw [laws.extract_revise, laws.extract_revise, agree query]
  right first second second' agree query := by
    rw [laws.extract_revise, laws.extract_revise, agree query]

/-- Under `CoreLaws` the denotation is compositional. -/
theorem CoreLaws.denotationsAgree_congruence (laws : R.CoreLaws) :
    WMTermCongruence (fun {_} first second => R.DenotationsAgree first second) :=
  laws.reviseRespectsAgree.denotationsAgree_congruence

/-! ## Subject reduction at every depth -/

/-- Root subject reduction and a `Revise` that respects state agreement give
subject reduction for every contextual step. -/
theorem agree_of_contextStep_of_root (revise : R.ReviseRespectsAgree)
    (root : ∀ {s : WMSort} {source target : WMTerm s},
      WMStep source target → R.Agree s (R.denote source) (R.denote target))
    {s : WMSort} {source target : WMTerm s} (step : WMContextStep source target) :
    R.Agree s (R.denote source) (R.denote target) :=
  revise.denotationsAgree_congruence.holds_of_contextStep root step

/-- Subject reduction for one contextual step. -/
theorem CoreLaws.agree_of_contextStep (laws : R.CoreLaws) {s : WMSort}
    {source target : WMTerm s} (step : WMContextStep source target) :
    R.Agree s (R.denote source) (R.denote target) :=
  agree_of_contextStep_of_root laws.reviseRespectsAgree laws.agree_of_step step

/-- Subject reduction for `WMContextStepStar`. -/
theorem CoreLaws.agree_of_contextStepStar (laws : R.CoreLaws) {s : WMSort}
    {source target : WMTerm s} (steps : WMContextStepStar source target) :
    R.Agree s (R.denote source) (R.denote target) := by
  induction steps with
  | refl => exact R.agree_refl s _
  | tail _ last previous =>
      exact R.agree_trans s previous (laws.agree_of_contextStep last)

/-- Every reduct of an encoded term under the contextual presentation, at any
depth and after any number of steps, is encoded and agrees with it. -/
theorem CoreLaws.contextual_reduct_agrees (laws : R.CoreLaws) {s : WMSort}
    (term : WMTerm s) {pattern : Pattern}
    (reduces : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM term) pattern) :
    ∃ reduct : WMTerm s, encodeWM reduct = pattern ∧
      R.Agree s (R.denote term) (R.denote reduct) := by
  obtain ⟨reduct, steps, encoded⟩ := wmContextStepStar_complete term reduces
  exact ⟨reduct, encoded, laws.agree_of_contextStepStar steps⟩

/-- One step of the contextual presentation's `langGSLT` from an encoded term
reaches an encoded term with agreeing denotation. -/
theorem CoreLaws.contextual_step_agrees (laws : R.CoreLaws) {s : WMSort}
    (term : WMTerm s) {pattern : Pattern}
    (step : (langGSLT (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)).Step
      (encodeWM term) pattern) :
    ∃ reduct : WMTerm s, encodeWM reduct = pattern ∧
      R.Agree s (R.denote term) (R.denote reduct) :=
  laws.contextual_reduct_agrees term (.step step (.refl _))

/-- Every contextual reduct of an encoded evidence term denotes the same
evidence. -/
theorem CoreLaws.contextual_evidence_reduct_denotes (laws : R.CoreLaws)
    (term : WMTerm .evidence) {pattern : Pattern}
    (reduces : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM term) pattern) :
    R.PatternDenotes .evidence pattern (R.denote term) := by
  obtain ⟨reduct, encoded, agree⟩ := laws.contextual_reduct_agrees term reduces
  exact ⟨reduct, encoded, agree.symm⟩

/-! ## What root subject reduction alone gives at every depth

Without `ReviseRespectsAgree`, root subject reduction still transports every
observation the calculus can express: extraction at a named query, and
evidence.  The `evidence_add` instances of root subject reduction make
extraction at a named query of a revision depend only on the extractions of
its arguments. -/

variable (R)

/-- Agreement on the observations the calculus names: states agree at every
query atom; queries and evidence agree when their denotations are equal. -/
def NamedQueryAgree : (s : WMSort) → WMTerm s → WMTerm s → Prop
  | .state, first, second => ∀ name,
      R.extract (R.denote first) (R.query name) = R.extract (R.denote second) (R.query name)
  | .query, first, second => R.denote first = R.denote second
  | .evidence, first, second => R.denote first = R.denote second

variable {R}

/-- Root subject reduction alone makes every contextual step preserve every
named observation. -/
theorem namedQueryAgree_of_contextStep_of_root
    (root : ∀ {s : WMSort} {source target : WMTerm s},
      WMStep source target → R.Agree s (R.denote source) (R.denote target))
    {s : WMSort} {source target : WMTerm s} (step : WMContextStep source target) :
    R.NamedQueryAgree s source target := by
  have additive : ∀ (first second : WMTerm .state) (name : String),
      R.extract (R.revise (R.denote first) (R.denote second)) (R.query name) =
        R.combine (R.extract (R.denote first) (R.query name))
          (R.extract (R.denote second) (R.query name)) :=
    fun first second name => root (.evidence_add first second (.query name))
  induction step with
  | @root s source target rootStep =>
      cases s with
      | state => exact fun name => root rootStep (R.query name)
      | query => exact root rootStep
      | evidence => exact root rootStep
  | revise_left second _ inner =>
      intro name
      change R.extract (R.revise _ (R.denote second)) (R.query name) =
        R.extract (R.revise _ (R.denote second)) (R.query name)
      rw [additive, additive, inner name]
  | revise_right first _ inner =>
      intro name
      change R.extract (R.revise (R.denote first) _) (R.query name) =
        R.extract (R.revise (R.denote first) _) (R.query name)
      rw [additive, additive, inner name]
  | extract_left query _ inner =>
      cases query with
      | query name => exact inner name
  | extract_right world _ inner =>
      exact congrArg (R.extract (R.denote world)) inner
  | combine_left second _ inner =>
      exact congrArg (R.combine · (R.denote second)) inner
  | combine_right first _ inner =>
      exact congrArg (R.combine (R.denote first)) inner

/-- At the evidence sort, root subject reduction alone gives subject
reduction for every contextual step. -/
theorem evidence_denote_eq_of_contextStep_of_root
    (root : ∀ {s : WMSort} {source target : WMTerm s},
      WMStep source target → R.Agree s (R.denote source) (R.denote target))
    {source target : WMTerm .evidence} (step : WMContextStep source target) :
    R.denote source = R.denote target :=
  namedQueryAgree_of_contextStep_of_root root step

end WMReading

/-! ## The minimal six-axis vertex has the core one-step relation -/

theorem minimalVertex_rewrites_eq_core :
    (wmExtVertexLanguageDef wmExtVertexMinimal).rewrites =
      wmCoreLanguageDef.rewrites :=
  rfl

theorem minimalVertex_step_iff_core (source target : Pattern) :
    langSemanticReduces (wmExtVertexLanguageDef wmExtVertexMinimal) source target ↔
      langSemanticReduces wmCoreLanguageDef source target := by
  rw [langSemanticReduces_iff_langReduces_of_equation_free (by rfl),
    langSemanticReduces_iff_langReduces_of_equation_free (by rfl)]
  unfold langReduces langReducesUsing
  constructor
  · exact Mettapedia.OSLF.MeTTaIL.ContextualStep.Step.mono_rules
      (fun _ member => minimalVertex_rewrites_eq_core ▸ member)
  · exact Mettapedia.OSLF.MeTTaIL.ContextualStep.Step.mono_rules
      (fun _ member => minimalVertex_rewrites_eq_core.symm ▸ member)

theorem minimalVertex_reducesStar_to_core {source target : Pattern}
    (reduces : LangReducesStar (wmExtVertexLanguageDef wmExtVertexMinimal)
      source target) :
    LangReducesStar wmCoreLanguageDef source target := by
  induction reduces with
  | refl => exact .refl _
  | step first _ rest => exact .step ((minimalVertex_step_iff_core _ _).mp first) rest

#print axioms WMReading.CoreLaws.agree_of_step
#print axioms WMReading.CoreLaws.core_evidence_reduct_denotes
#print axioms WMReading.ReviseRespectsAgree.denotationsAgree_congruence
#print axioms WMReading.CoreLaws.reviseRespectsAgree
#print axioms WMReading.CoreLaws.denotationsAgree_congruence
#print axioms WMReading.agree_of_contextStep_of_root
#print axioms WMReading.CoreLaws.agree_of_contextStep
#print axioms WMReading.CoreLaws.agree_of_contextStepStar
#print axioms WMReading.CoreLaws.contextual_reduct_agrees
#print axioms WMReading.CoreLaws.contextual_step_agrees
#print axioms WMReading.CoreLaws.contextual_evidence_reduct_denotes
#print axioms WMReading.namedQueryAgree_of_contextStep_of_root
#print axioms WMReading.evidence_denote_eq_of_contextStep_of_root
#print axioms minimalVertex_step_iff_core

end Mettapedia.OSLF.Framework.WMCalculusSemantics
