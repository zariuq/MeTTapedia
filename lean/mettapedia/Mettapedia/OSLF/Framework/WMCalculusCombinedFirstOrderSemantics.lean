import Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading

/-!
# Semantic interpretation of the authored combined WM constructor fragment

The generated binding signature also admits generic lambda, substitution, and
collection forms. A `CombinedReading` does not interpret those forms. Here the
interpreted fragment is therefore an inductive *property of existing intrinsic
terms*, not a replacement WM syntax. Its eight operator cases are the authored
constructors, and its variables remain intrinsically sorted and scoped.

The interpretation is compatible with any simultaneous substitution whose
images remain in this fragment. This makes the operation-level WM laws into
context-indexed semantic equations without pretending that a reading already
models every generic representation form of `signatureOf`.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

set_option autoImplicit false

private abbrev StateSort := TypeExpr.base "State"
private abbrev QuerySort := TypeExpr.base "Query"
private abbrev EvidenceSort := TypeExpr.base "BinaryEvidence"
private abbrev OverlapSort := TypeExpr.base "Overlap"
private abbrev ScopeSort := TypeExpr.base "Scope"

/-- The five semantic carriers, indexed by the *authored* sorts. An
undeclared sort has no values in this model; in particular a generic lambda
or collection form does not acquire a spurious unit-valued interpretation. -/
abbrev Carrier (State Query Ev Ov Scope : Type) (sort : TypeExpr) : Type :=
  match sort with
  | .base tag =>
      if tag = "State" then State
      else if tag = "Query" then Query
      else if tag = "BinaryEvidence" then Ev
      else if tag = "Overlap" then Ov
      else if tag = "Scope" then Scope
      else PEmpty
  | _ => PEmpty

/-- The precisely interpreted fragment of the *existing* intrinsic syntax.
The indexed term in each case uses an operator proved to come from the
combined vertex's authored constructor list. -/
inductive FirstOrder : {Γ : Ctx CombinedSignature} → {sort : TypeExpr} →
    Term CombinedSignature Γ sort → Type where
  | variable {Γ : Ctx CombinedSignature} {sort : TypeExpr}
      (position : Var Γ sort) : FirstOrder (.var position)
  | revise {Γ : Ctx CombinedSignature}
      {first second : Term CombinedSignature Γ StateSort} :
      FirstOrder first → FirstOrder second →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.revise first second)
  | extract {Γ : Ctx CombinedSignature}
      {world : Term CombinedSignature Γ StateSort}
      {query : Term CombinedSignature Γ QuerySort} :
      FirstOrder world → FirstOrder query →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.extract world query)
  | combine {Γ : Ctx CombinedSignature}
      {first second : Term CombinedSignature Γ EvidenceSort} :
      FirstOrder first → FirstOrder second →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.combine first second)
  | zero {Γ : Ctx CombinedSignature} :
      FirstOrder (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))
  | overlapMerge {Γ : Ctx CombinedSignature}
      {first second : Term CombinedSignature Γ StateSort} :
      FirstOrder first → FirstOrder second →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.overlapMerge first second)
  | overlapFactor {Γ : Ctx CombinedSignature}
      {first second : Term CombinedSignature Γ StateSort}
      {query : Term CombinedSignature Γ QuerySort} :
      FirstOrder first → FirstOrder second → FirstOrder query →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.overlapFactor first second query)
  | overlapCorrect {Γ : Ctx CombinedSignature}
      {first second : Term CombinedSignature Γ EvidenceSort}
      {factor : Term CombinedSignature Γ OverlapSort} :
      FirstOrder first → FirstOrder second → FirstOrder factor →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.overlapCorrect first second factor)
  | forget {Γ : Ctx CombinedSignature}
      {scope : Term CombinedSignature Γ ScopeSort}
      {world : Term CombinedSignature Γ StateSort} :
      FirstOrder scope → FirstOrder world →
      FirstOrder (WMCalculusCombinedIntrinsicTransport.forget scope world)

/-- Every supported state, query, overlap or scope term needs a variable
supplied by a typed context. Evidence alone has a closed generator. -/
theorem nonEvidence_requires_context {Γ : Ctx CombinedSignature}
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term)
    (nonEvidence : sort = StateSort ∨ sort = QuerySort ∨
      sort = OverlapSort ∨ sort = ScopeSort) : Γ ≠ [] := by
  induction fragment with
  | «variable» position =>
      intro empty
      subst Γ
      cases position
  | revise _ _ firstIH _ => exact firstIH (Or.inl rfl)
  | extract _ _ _ _ => simp [StateSort, QuerySort, OverlapSort, ScopeSort] at nonEvidence
  | combine _ _ _ _ => simp [StateSort, QuerySort, OverlapSort, ScopeSort] at nonEvidence
  | zero => simp [StateSort, QuerySort, OverlapSort, ScopeSort] at nonEvidence
  | overlapMerge _ _ firstIH _ => exact firstIH (Or.inl rfl)
  | overlapFactor _ _ _ firstIH _ _ => exact firstIH (Or.inl rfl)
  | overlapCorrect _ _ _ _ _ _ =>
      simp [StateSort, QuerySort, OverlapSort, ScopeSort] at nonEvidence
  | forget _ _ _ worldIH => exact worldIH (Or.inl rfl)

/-- The authored first-order fragment has no closed state generator. -/
theorem no_closed_state {term : Term CombinedSignature [] StateSort}
    (fragment : FirstOrder term) : False :=
  nonEvidence_requires_context fragment (Or.inl rfl) rfl

/-- Queries enter this authored fragment through a typed context. -/
theorem no_closed_query {term : Term CombinedSignature [] QuerySort}
    (fragment : FirstOrder term) : False :=
  nonEvidence_requires_context fragment (Or.inr (Or.inl rfl)) rfl

/-- Scope handles are not closed constructor terms of the current language. -/
theorem no_closed_scope {term : Term CombinedSignature [] ScopeSort}
    (fragment : FirstOrder term) : False :=
  nonEvidence_requires_context fragment (Or.inr (Or.inr (Or.inr rfl))) rfl

/-- Producing an overlap value requires an open typed context. -/
theorem no_closed_overlap {term : Term CombinedSignature [] OverlapSort}
    (fragment : FirstOrder term) : False :=
  nonEvidence_requires_context fragment (Or.inr (Or.inr (Or.inl rfl))) rfl

/-- The boundary is not vacuous: EvidenceZero is a supported closed term. -/
theorem closed_evidence_exists :
    Nonempty (Σ term : Term CombinedSignature [] EvidenceSort, FirstOrder term) :=
  ⟨⟨WMCalculusCombinedIntrinsicTransport.zero, .zero⟩⟩

/-- A model valuation of the intrinsically sorted context. -/
abbrev Environment {State Query Ev Ov Scope : Type}
    (Γ : Ctx CombinedSignature) :=
  (sort : TypeExpr) → Var Γ sort → Carrier State Query Ev Ov Scope sort

namespace FirstOrder

variable {State Query Ev Ov Scope : Type}

/-- Simultaneous substitutions must not introduce a generic representation
form that the reading has not interpreted. -/
def substitute {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ (sort : TypeExpr) (position : Var Γ sort),
      FirstOrder (sigma sort position)) :
    {sort : TypeExpr} → {term : Term CombinedSignature Γ sort} →
      FirstOrder term → FirstOrder (bind sigma term)
  | _, _, .variable position => supported _ position
  | _, _, .revise first second =>
      .revise (substitute sigma supported first) (substitute sigma supported second)
  | _, _, .extract world query =>
      .extract (substitute sigma supported world) (substitute sigma supported query)
  | _, _, .combine first second =>
      .combine (substitute sigma supported first) (substitute sigma supported second)
  | _, _, .zero => .zero
  | _, _, .overlapMerge first second =>
      .overlapMerge (substitute sigma supported first) (substitute sigma supported second)
  | _, _, .overlapFactor first second query =>
      .overlapFactor (substitute sigma supported first)
        (substitute sigma supported second) (substitute sigma supported query)
  | _, _, .overlapCorrect first second factor =>
      .overlapCorrect (substitute sigma supported first)
        (substitute sigma supported second) (substitute sigma supported factor)
  | _, _, .forget scope world =>
      .forget (substitute sigma supported scope) (substitute sigma supported world)

/-- Structural interpretation of precisely the constructor fragment into a
combined reading. This is a fold on the intrinsic-fragment certificate. -/
def denote (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    {sort : TypeExpr} → {term : Term CombinedSignature Γ sort} →
      FirstOrder term → Carrier State Query Ev Ov Scope sort
  | _, _, .variable position => environment _ position
  | _, _, .revise first second =>
      reading.core.revise
        (denote reading environment first)
        (denote reading environment second)
  | _, _, .extract world query =>
      reading.core.extract
        (denote reading environment world)
        (denote reading environment query)
  | _, _, .combine first second =>
      reading.core.combine
        (denote reading environment first)
        (denote reading environment second)
  | _, _, .zero => reading.core.zero
  | _, _, .overlapMerge first second =>
      reading.overlapMerge
        (denote reading environment first)
        (denote reading environment second)
  | _, _, .overlapFactor first second query =>
      reading.overlapFactor
        (denote reading environment first)
        (denote reading environment second)
        (denote reading environment query)
  | _, _, .overlapCorrect first second factor =>
      reading.overlapCorrect
        (denote reading environment first)
        (denote reading environment second)
        (denote reading environment factor)
  | _, _, .forget scope world =>
      reading.forget
        (denote reading environment scope)
        (denote reading environment world)

end FirstOrder

open FirstOrder

private theorem congrArg3 {A B C D : Type} (function : A → B → C → D)
    {a a' : A} {b b' : B} {c c' : C}
    (first : a = a') (second : b = b') (third : c = c') :
    function a b c = function a' b' c' := by
  cases first
  cases second
  cases third
  rfl

/-- Interpreting a constructor term after a supported simultaneous
substitution is the same as interpreting it under the environment obtained
by interpreting every substituted variable. This is the nontrivial
reindexing law needed by dependent observation predicates. -/
theorem denote_substitute {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ (sort : TypeExpr) (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) :
    FirstOrder.denote reading environment
        (FirstOrder.substitute sigma supported fragment) =
      FirstOrder.denote reading
        (fun sort position => FirstOrder.denote reading environment
          (supported sort position)) fragment := by
  induction fragment with
  | «variable» position => rfl
  | revise first second firstIH secondIH =>
      exact congrArg₂ reading.core.revise firstIH secondIH
  | extract world query worldIH queryIH =>
      exact congrArg₂ reading.core.extract worldIH queryIH
  | combine first second firstIH secondIH =>
      exact congrArg₂ reading.core.combine firstIH secondIH
  | zero => rfl
  | overlapMerge first second firstIH secondIH =>
      exact congrArg₂ reading.overlapMerge firstIH secondIH
  | overlapFactor first second query firstIH secondIH queryIH =>
      exact congrArg3 reading.overlapFactor firstIH secondIH queryIH
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      exact congrArg3 reading.overlapCorrect firstIH secondIH factorIH
  | forget scope world scopeIH worldIH =>
      exact congrArg₂ reading.forget scopeIH worldIH

/-- A supported substitution acts contravariantly on model environments by
evaluating each intrinsically typed variable image. -/
def reindexEnvironment {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ (sort : TypeExpr) (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ :=
  fun sort position => FirstOrder.denote reading environment
    (supported sort position)

theorem reindexEnvironment_id {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) :
    reindexEnvironment reading (fun _sort position => Term.var position)
      (fun _sort position => FirstOrder.variable position) environment =
        environment := by
  funext sort position
  rfl

/-- Reindexing composes in the contravariant order of substitutions. The
support certificate for the composite uses generic intrinsic `bind`. -/
theorem reindexEnvironment_comp {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ Θ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (tau : Sub CombinedSignature Δ Θ)
    (sigmaSupported : ∀ (sort : TypeExpr) (position : Var Γ sort),
      FirstOrder (sigma sort position))
    (tauSupported : ∀ (sort : TypeExpr) (position : Var Δ sort),
      FirstOrder (tau sort position))
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Θ) :
    reindexEnvironment reading sigma sigmaSupported
        (reindexEnvironment reading tau tauSupported environment) =
      reindexEnvironment reading
        (fun sort position => bind tau (sigma sort position))
        (fun sort position => FirstOrder.substitute tau tauSupported
          (sigmaSupported sort position)) environment := by
  funext sort position
  exact (denote_substitute reading tau tauSupported environment
    (sigmaSupported sort position)).symm

/-- The intrinsic overlap computation is sound in *every* combined reading,
at every sorted variable context and for every interpreted constructor term. -/
theorem overlap_extract_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {first second : Term CombinedSignature Γ StateSort}
    {query : Term CombinedSignature Γ QuerySort}
    (firstTerm : FirstOrder first) (secondTerm : FirstOrder second)
    (queryTerm : FirstOrder query) :
    FirstOrder.denote reading environment
      (FirstOrder.extract (FirstOrder.overlapMerge firstTerm secondTerm) queryTerm) =
    FirstOrder.denote reading environment
      (FirstOrder.overlapCorrect
        (FirstOrder.extract firstTerm queryTerm)
        (FirstOrder.extract secondTerm queryTerm)
        (FirstOrder.overlapFactor firstTerm secondTerm queryTerm)) := by
  change reading.core.extract
      (reading.overlapMerge
        (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment secondTerm))
      (FirstOrder.denote reading environment queryTerm) =
    reading.overlapCorrect
      (reading.core.extract (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment queryTerm))
      (reading.core.extract (FirstOrder.denote reading environment secondTerm)
        (FirstOrder.denote reading environment queryTerm))
      (reading.overlapFactor
        (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment secondTerm)
        (FirstOrder.denote reading environment queryTerm))
  exact reading.overlapExtract _ _ _

/-- Core extraction remains a computation in the extended semantic model. -/
theorem core_extract_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {first second : Term CombinedSignature Γ StateSort}
    {query : Term CombinedSignature Γ QuerySort}
    (firstTerm : FirstOrder first) (secondTerm : FirstOrder second)
    (queryTerm : FirstOrder query) :
    FirstOrder.denote reading environment
      (FirstOrder.extract (FirstOrder.revise firstTerm secondTerm) queryTerm) =
    FirstOrder.denote reading environment
      (FirstOrder.combine (FirstOrder.extract firstTerm queryTerm)
        (FirstOrder.extract secondTerm queryTerm)) := by
  change reading.core.extract
      (reading.core.revise
        (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment secondTerm))
      (FirstOrder.denote reading environment queryTerm) =
    reading.core.combine
      (reading.core.extract (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment queryTerm))
      (reading.core.extract (FirstOrder.denote reading environment secondTerm)
        (FirstOrder.denote reading environment queryTerm))
  exact reading.coreLaws.extract_revise _ _ _

/-- All three authored evidence equations are interpreted in every combined
reading, not only in the concrete count model. -/
theorem combine_comm_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {first second : Term CombinedSignature Γ EvidenceSort}
    (firstTerm : FirstOrder first) (secondTerm : FirstOrder second) :
    FirstOrder.denote reading environment
      (FirstOrder.combine firstTerm secondTerm) =
    FirstOrder.denote reading environment
      (FirstOrder.combine secondTerm firstTerm) := by
  change reading.core.combine
      (FirstOrder.denote reading environment firstTerm)
      (FirstOrder.denote reading environment secondTerm) =
    reading.core.combine
      (FirstOrder.denote reading environment secondTerm)
      (FirstOrder.denote reading environment firstTerm)
  exact reading.coreLaws.combine_comm _ _

theorem combine_assoc_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {first second third : Term CombinedSignature Γ EvidenceSort}
    (firstTerm : FirstOrder first) (secondTerm : FirstOrder second)
    (thirdTerm : FirstOrder third) :
    FirstOrder.denote reading environment
      (FirstOrder.combine (FirstOrder.combine firstTerm secondTerm) thirdTerm) =
    FirstOrder.denote reading environment
      (FirstOrder.combine firstTerm (FirstOrder.combine secondTerm thirdTerm)) := by
  change reading.core.combine
      (reading.core.combine
        (FirstOrder.denote reading environment firstTerm)
        (FirstOrder.denote reading environment secondTerm))
      (FirstOrder.denote reading environment thirdTerm) =
    reading.core.combine
      (FirstOrder.denote reading environment firstTerm)
      (reading.core.combine
        (FirstOrder.denote reading environment secondTerm)
        (FirstOrder.denote reading environment thirdTerm))
  exact reading.coreLaws.combine_assoc _ _ _

theorem combine_zero_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) :
    FirstOrder.denote reading environment
      (FirstOrder.combine fragment (FirstOrder.zero (Γ := Γ))) =
    FirstOrder.denote reading environment fragment := by
  change reading.core.combine
      (FirstOrder.denote reading environment fragment) reading.core.zero =
    FirstOrder.denote reading environment fragment
  exact reading.coreLaws.combine_zero _

/-- The unconditional authored forgetting-idempotence computation is sound
for the same intrinsically typed constructor fragment. -/
theorem forget_idempotent_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {scope : Term CombinedSignature Γ ScopeSort}
    {world : Term CombinedSignature Γ StateSort}
    (scopeTerm : FirstOrder scope) (worldTerm : FirstOrder world) :
    FirstOrder.denote reading environment
      (FirstOrder.forget scopeTerm (FirstOrder.forget scopeTerm worldTerm)) =
    FirstOrder.denote reading environment
      (FirstOrder.forget scopeTerm worldTerm) := by
  change reading.forget (FirstOrder.denote reading environment scopeTerm)
      (reading.forget (FirstOrder.denote reading environment scopeTerm)
        (FirstOrder.denote reading environment worldTerm)) =
    reading.forget (FirstOrder.denote reading environment scopeTerm)
      (FirstOrder.denote reading environment worldTerm)
  exact reading.forgetIdempotent _ _

/-- Soundness of the guarded observation requires the semantic outside-scope
fact, not merely success of an uninterpreted relation-query premise. -/
theorem forget_outside_sound {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {scope : Term CombinedSignature Γ ScopeSort}
    {world : Term CombinedSignature Γ StateSort}
    {query : Term CombinedSignature Γ QuerySort}
    (scopeTerm : FirstOrder scope) (worldTerm : FirstOrder world)
    (queryTerm : FirstOrder query)
    (outside : ¬ reading.inScope
      (FirstOrder.denote reading environment scopeTerm)
      (FirstOrder.denote reading environment queryTerm)) :
    FirstOrder.denote reading environment
      (FirstOrder.extract (FirstOrder.forget scopeTerm worldTerm) queryTerm) =
    FirstOrder.denote reading environment
      (FirstOrder.extract worldTerm queryTerm) := by
  change reading.core.extract
      (reading.forget (FirstOrder.denote reading environment scopeTerm)
        (FirstOrder.denote reading environment worldTerm))
      (FirstOrder.denote reading environment queryTerm) =
    reading.core.extract (FirstOrder.denote reading environment worldTerm)
      (FirstOrder.denote reading environment queryTerm)
  exact reading.forgetOutside outside

/-- The fibre of evidence answers to an intrinsically typed query term. Its
index is a model environment, so source-context substitutions act by
reindexing the environment rather than by erasing dependencies. -/
def EvidenceFibre {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ) : Prop :=
  FirstOrder.denote reading environment fragment = answer

/-- The dependent evidence fibre pulls back along every supported intrinsic
substitution. This is the semantic reindexing square for WM observations. -/
theorem evidenceFibre_reindex {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (supported : ∀ (sort : TypeExpr) (position : Var Γ sort),
      FirstOrder (sigma sort position))
    {term : Term CombinedSignature Γ EvidenceSort}
    (fragment : FirstOrder term) (answer : Ev)
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Δ) :
    EvidenceFibre reading (FirstOrder.substitute sigma supported fragment)
        answer environment ↔
      EvidenceFibre reading fragment answer
        (fun sort position => FirstOrder.denote reading environment
          (supported sort position)) := by
  unfold EvidenceFibre
  rw [denote_substitute reading sigma supported environment fragment]

private abbrev TestContext : Ctx CombinedSignature := [StateSort, QuerySort]

private def testState : Term CombinedSignature TestContext StateSort := .var .zero
private def testQuery : Term CombinedSignature TestContext QuerySort :=
  .var (.succ .zero)

private def testOverlap :
    Term CombinedSignature TestContext EvidenceSort :=
  WMCalculusCombinedIntrinsicTransport.extract
    (WMCalculusCombinedIntrinsicTransport.overlapMerge testState testState)
    testQuery

private def testRevision :
    Term CombinedSignature TestContext EvidenceSort :=
  WMCalculusCombinedIntrinsicTransport.extract
    (WMCalculusCombinedIntrinsicTransport.revise testState testState)
    testQuery

private def testOverlapFragment : FirstOrder testOverlap :=
  .extract (.overlapMerge (.variable .zero) (.variable .zero))
    (.variable (.succ .zero))

private def testRevisionFragment : FirstOrder testRevision :=
  .extract (.revise (.variable .zero) (.variable .zero))
    (.variable (.succ .zero))

/-- A real valuation of the two-sorted context. The query variable receives
`"x"`; the world variable receives one count at that key. -/
def countingEnvironment : Environment
    (State := CountState) (Query := String) (Ev := Nat)
    (Ov := Nat) (Scope := CountScope) TestContext := by
  intro sort position
  cases position with
  | zero => exact countingCore.world "x"
  | succ position =>
      cases position with
      | zero => exact "x"
      | succ position => exact nomatch position

/-- At the same typed query, duplicate provenance merges to one observed
count while additive revision counts both occurrences. -/
theorem typed_overlap_vs_revision :
    FirstOrder.denote countingCombined countingEnvironment
      testOverlapFragment = (1 : Nat) ∧
    FirstOrder.denote countingCombined countingEnvironment
      testRevisionFragment = (2 : Nat) := by
  constructor <;> rfl

theorem typed_overlap_not_revision :
    FirstOrder.denote countingCombined countingEnvironment
      testOverlapFragment ≠
    FirstOrder.denote countingCombined countingEnvironment
      testRevisionFragment := by
  have result := typed_overlap_vs_revision
  rw [result.1, result.2]
  change (1 : Nat) ≠ 2
  decide

/-- Generic lambda is present in `signatureOf`, but a WM reading has not
silently interpreted it as one of the eight authored WM constructors. -/
def genericIdentity :
    Term CombinedSignature [] (.arrow StateSort StateSort) :=
  .op (.lambda StateSort StateSort) (.cons (.var .zero) .nil)

theorem genericIdentity_not_FirstOrder :
    ¬ Nonempty (FirstOrder genericIdentity) := by
  rintro ⟨fragment⟩
  cases fragment

/-- Generic substitution can produce an evidence-sorted term whose value
carrier is inhabited, but the WM reading does not interpret that generic
representation former as an authored WM constructor. -/
def genericEvidenceSubst : Term CombinedSignature [] EvidenceSort :=
  .op (.subst EvidenceSort EvidenceSort)
    (.cons (.var .zero) (.cons (WMCalculusCombinedIntrinsicTransport.zero) .nil))

/-- In one intrinsically sorted context an erased de Bruijn index identifies
the variable position, even when the result sort is not supplied in advance. -/
private theorem variable_heq_of_index_eq
    {Γ : Ctx CombinedSignature} {firstSort secondSort : TypeExpr}
    (first : Var Γ firstSort) (second : Var Γ secondSort)
    (same : variableIndex first = variableIndex second) :
    HEq first second := by
  have firstLookup : Γ[variableIndex first]? = some firstSort := variableIndex_lookup first
  have secondLookup : Γ[variableIndex second]? = some secondSort := variableIndex_lookup second
  rw [same] at firstLookup
  have sorts : firstSort = secondSort :=
    Option.some.inj (firstLookup.symm.trans secondLookup)
  subst secondSort
  clear firstLookup secondLookup
  apply heq_of_eq
  induction first with
  | zero =>
      cases second with
      | zero => rfl
      | succ second => simp [variableIndex] at same
  | succ first ih =>
      cases second with
      | zero => simp [variableIndex] at same
      | succ second =>
          have inner : first = second := ih second (by
            simpa [variableIndex] using same)
          subst second
          rfl

/-- Any semantic environment assigns the same value to two presentations
of one erased variable position. -/
private theorem environment_heq_of_index_eq
    {State Query Ev Ov Scope : Type}
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {firstSort secondSort : TypeExpr}
    (first : Var Γ firstSort) (second : Var Γ secondSort)
    (same : variableIndex first = variableIndex second) :
    HEq (environment firstSort first) (environment secondSort second) := by
  have firstLookup : Γ[variableIndex first]? = some firstSort := variableIndex_lookup first
  have secondLookup : Γ[variableIndex second]? = some secondSort := variableIndex_lookup second
  rw [same] at firstLookup
  have sorts : firstSort = secondSort :=
    Option.some.inj (firstLookup.symm.trans secondLookup)
  subst secondSort
  have positions : first = second := eq_of_heq (variable_heq_of_index_eq first second same)
  subst second
  rfl

attribute [local simp]
  WMCalculusCombinedIntrinsicTransport.erase_revise
  WMCalculusCombinedIntrinsicTransport.erase_extract
  WMCalculusCombinedIntrinsicTransport.erase_combine
  WMCalculusCombinedIntrinsicTransport.erase_zero
  WMCalculusCombinedIntrinsicTransport.erase_overlapMerge
  WMCalculusCombinedIntrinsicTransport.erase_overlapFactor
  WMCalculusCombinedIntrinsicTransport.erase_overlapCorrect
  WMCalculusCombinedIntrinsicTransport.erase_forget
  pRevise pExtract pCombine pEvidenceZero
  pOverlapMerge pOverlapFactor pOverlapCorrect pForget

/-- None of the eight authored WM constructors erases to a generic
substitution form. This rules out an unsupported evidence-sorted term even
though the evidence value carrier itself can be inhabited. -/
theorem subst_erasure_not_FirstOrder
    {Γ : Ctx CombinedSignature} {sort : TypeExpr}
    {term : Term CombinedSignature Γ sort}
    (fragment : FirstOrder term) (body replacement : Pattern)
    (shape : erase term = .subst body replacement) : False := by
  induction fragment <;> simp [erase] at shape

theorem genericEvidenceSubst_not_FirstOrder :
    ¬ Nonempty (FirstOrder genericEvidenceSubst) := by
  rintro ⟨fragment⟩
  exact subst_erasure_not_FirstOrder fragment _ _ rfl

/-- Erasure of supported authored terms determines their semantic values,
even when the two proof-relevant certificates have different result-sort
indices before their common raw shape is examined. -/
theorem denote_heq_of_erase_eq {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {firstSort secondSort : TypeExpr}
    {firstTerm : Term CombinedSignature Γ firstSort}
    {secondTerm : Term CombinedSignature Γ secondSort}
    (firstCertificate : FirstOrder firstTerm)
    (secondCertificate : FirstOrder secondTerm)
    (same : erase firstTerm = erase secondTerm) :
    HEq (FirstOrder.denote reading environment firstCertificate)
      (FirstOrder.denote reading environment secondCertificate) := by
  induction firstCertificate generalizing secondSort with
  | «variable» firstPosition =>
      cases secondCertificate <;> simp [erase] at same
      exact environment_heq_of_index_eq environment firstPosition _ same
  | revise first second firstIH secondIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightFirst rightSecond
      exact heq_of_eq (congrArg₂ reading.core.revise
        (firstIH rightFirst same.1).eq (secondIH rightSecond same.2).eq)
  | extract world query worldIH queryIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightWorld rightQuery
      exact heq_of_eq (congrArg₂ reading.core.extract
        (worldIH rightWorld same.1).eq (queryIH rightQuery same.2).eq)
  | combine first second firstIH secondIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightFirst rightSecond
      exact heq_of_eq (congrArg₂ reading.core.combine
        (firstIH rightFirst same.1).eq (secondIH rightSecond same.2).eq)
  | zero =>
      cases secondCertificate <;> simp [erase] at same
      rfl
  | overlapMerge first second firstIH secondIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightFirst rightSecond
      exact heq_of_eq (congrArg₂ reading.overlapMerge
        (firstIH rightFirst same.1).eq (secondIH rightSecond same.2).eq)
  | overlapFactor first second query firstIH secondIH queryIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightFirst rightSecond rightQuery
      exact heq_of_eq (congrArg3 reading.overlapFactor
        (firstIH rightFirst same.1).eq
        (secondIH rightSecond same.2.1).eq
        (queryIH rightQuery same.2.2).eq)
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightFirst rightSecond rightFactor
      exact heq_of_eq (congrArg3 reading.overlapCorrect
        (firstIH rightFirst same.1).eq
        (secondIH rightSecond same.2.1).eq
        (factorIH rightFactor same.2.2).eq)
  | forget scope world scopeIH worldIH =>
      cases secondCertificate <;> simp [erase] at same
      rename_i rightScope rightWorld
      exact heq_of_eq (congrArg₂ reading.forget
        (scopeIH rightScope same.1).eq (worldIH rightWorld same.2).eq)

/-- Any supported certificate whose erasure is a given bound variable
denotes the value assigned to that context position. -/
theorem variable_erasure_denote {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {expectedSort : TypeExpr} (expected : Var Γ expectedSort)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (certificate : FirstOrder term)
    (isVariable : erase term = .bvar (variableIndex expected)) :
    HEq (FirstOrder.denote reading environment certificate)
      (environment expectedSort expected) := by
  induction certificate with
  | «variable» actual =>
      have sameIndex : variableIndex actual = variableIndex expected := by
        simpa only [erase, Pattern.bvar.injEq] using isVariable
      exact environment_heq_of_index_eq environment actual expected sameIndex
  | revise first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_revise, pRevise] at isVariable
  | extract world query worldIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_extract, pExtract] at isVariable
  | combine first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_combine, pCombine] at isVariable
  | zero =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_zero, pEvidenceZero] at isVariable
  | overlapMerge first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapMerge,
        pOverlapMerge] at isVariable
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapFactor,
        pOverlapFactor] at isVariable
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapCorrect,
        pOverlapCorrect] at isVariable
  | forget scope world scopeIH worldIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_forget, pForget] at isVariable

/-- Erasure distinguishes the authored nullary evidence constructor from
every other constructor in the interpreted first-order fragment. Its
semantic value is therefore independent of which certificate was supplied. -/
theorem zero_erasure_denote {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (certificate : FirstOrder term)
    (isZero : erase term = pEvidenceZero) :
    HEq (FirstOrder.denote reading environment certificate)
      reading.core.zero := by
  induction certificate with
  | «variable» position =>
      simp [erase, pEvidenceZero] at isZero
  | revise first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_revise,
        pRevise, pEvidenceZero] at isZero
  | extract world query worldIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_extract,
        pExtract, pEvidenceZero] at isZero
  | combine first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_combine,
        pCombine, pEvidenceZero] at isZero
  | zero => rfl
  | overlapMerge first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapMerge,
        pOverlapMerge, pEvidenceZero] at isZero
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapFactor,
        pOverlapFactor, pEvidenceZero] at isZero
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapCorrect,
        pOverlapCorrect, pEvidenceZero] at isZero
  | forget scope world scopeIH worldIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_forget,
        pForget, pEvidenceZero] at isZero

/-- Every certificate for the closed authored zero term has the designated
semantic value, without selecting a preferred certificate. -/
theorem zero_certificate_denote {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    (certificate : FirstOrder
      (WMCalculusCombinedIntrinsicTransport.zero (Γ := Γ))) :
    FirstOrder.denote reading environment certificate = reading.core.zero := by
  exact (zero_erasure_denote reading environment certificate
    (WMCalculusCombinedIntrinsicTransport.erase_zero)).eq

/-- The erasure discriminator composes through an authored binary
constructor: every certificate for `Combine(Zero, Zero)` has the same value.
This is a non-nullary test of certificate-independent denotation. -/
theorem combine_zero_zero_erasure_denote {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {Γ : Ctx CombinedSignature}
    (environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) Γ)
    {sort : TypeExpr} {term : Term CombinedSignature Γ sort}
    (certificate : FirstOrder term)
    (shape : erase term = pCombine pEvidenceZero pEvidenceZero) :
    HEq (FirstOrder.denote reading environment certificate)
      (reading.core.combine reading.core.zero reading.core.zero) := by
  induction certificate with
  | «variable» position =>
      simp [erase, pCombine, pEvidenceZero] at shape
  | revise first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_revise,
        pRevise, pCombine] at shape
  | extract world query worldIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_extract,
        pExtract, pCombine] at shape
  | combine first second firstIH secondIH =>
      have parts := shape
      simp [WMCalculusCombinedIntrinsicTransport.erase_combine,
        pCombine] at parts
      have firstValue := (zero_erasure_denote reading environment first parts.1).eq
      have secondValue := (zero_erasure_denote reading environment second parts.2).eq
      change HEq (reading.core.combine
        (FirstOrder.denote reading environment first)
        (FirstOrder.denote reading environment second))
        (reading.core.combine reading.core.zero reading.core.zero)
      rw [firstValue, secondValue]
  | zero =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_zero,
        pEvidenceZero, pCombine] at shape
  | overlapMerge first second firstIH secondIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapMerge,
        pOverlapMerge, pCombine] at shape
  | overlapFactor first second query firstIH secondIH queryIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapFactor,
        pOverlapFactor, pCombine] at shape
  | overlapCorrect first second factor firstIH secondIH factorIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_overlapCorrect,
        pOverlapCorrect, pCombine] at shape
  | forget scope world scopeIH worldIH =>
      simp [WMCalculusCombinedIntrinsicTransport.erase_forget,
        pForget, pCombine] at shape

#print axioms denote_substitute
#print axioms nonEvidence_requires_context
#print axioms no_closed_state
#print axioms no_closed_query
#print axioms no_closed_scope
#print axioms no_closed_overlap
#print axioms closed_evidence_exists
#print axioms reindexEnvironment_id
#print axioms reindexEnvironment_comp
#print axioms core_extract_sound
#print axioms combine_comm_sound
#print axioms combine_assoc_sound
#print axioms combine_zero_sound
#print axioms overlap_extract_sound
#print axioms forget_idempotent_sound
#print axioms forget_outside_sound
#print axioms evidenceFibre_reindex
#print axioms typed_overlap_vs_revision
#print axioms typed_overlap_not_revision
#print axioms genericIdentity_not_FirstOrder
#print axioms genericEvidenceSubst_not_FirstOrder
#print axioms denote_heq_of_erase_eq
#print axioms variable_erasure_denote
#print axioms zero_erasure_denote
#print axioms zero_certificate_denote
#print axioms combine_zero_zero_erasure_denote

end Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
