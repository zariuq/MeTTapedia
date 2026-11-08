import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
import Mettapedia.PLN.WorldModel.WorldModelConservationPack

/-!
# Certified relation-provider boundary for WM forgetting and conservation

An authored `outsideScope` premise receives rows from `RelationEnv`. This
module gives a reusable finite-handle provider whose Boolean decision comes
with a proof that accepted rows are semantically outside. It changes neither
the WM language nor the generic premise evaluator. A backend supplies its
own handle values and proves the decision procedure's soundness.

The conservation rules ask for `erasesInScope` and `outsideScope` rows.
`Conservation.CheckedErasureProvider` answers them for a `ForgettingLayer`;
an accepted erasure row proves `forget S Δ = 0`, so each conservation rule
that fires on decoded handles yields the conclusion of the conservation
pack's `…_of_erases` theorem.  Outside-scope invariance asks for the same
`outsideScope` rows; an accepted row proves that the query lies outside the
scope, so the rule is sound by the layer's outside invariant
(`Conservation.forgetOutside_sound`).

The support-tracked rules ask for `supportedInScope` and `cleanForScope` rows.
`SupportTracked.CheckedSupportProvider` extends the erasure provider and
answers them for a `SupportTrackedForgettingLayer`; an accepted row proves
`Supported` or `Clean`, so absorption and the clean-base identity are sound
wherever they fire on decoded handles.  `SupportTracked.Control` separates
them, on a ledger of observation identities, from the premise-free rule
`Forget(S, Revise(W, D)) ↦ W`; it separates the conservation rules from
premises that name no scope, and outside-scope invariance from its
premise-free form.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

set_option autoImplicit false

structure HandleTable (Scope Query : Type) where
  scopes : List (Pattern × Scope)
  queries : List (Pattern × Query)

/-- Finite handle lookup is deterministic: the first matching row wins. -/
def lookupHandle {Value : Type} :
    List (Pattern × Value) → Pattern → Option Value
  | [], _ => none
  | (handle, value) :: rest, requested =>
      if handle = requested then some value else lookupHandle rest requested

/-- An external Boolean check may be incomplete, but every accepted answer
must be a proof-supported semantic outside-scope fact. -/
structure CheckedProvider (Scope Query : Type)
    (inScope : Scope → Query → Prop) where
  handles : HandleTable Scope Query
  outside : Scope → Query → Bool
  outside_sound : ∀ scope query, outside scope query = true → ¬ inScope scope query

def rows {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope) :
    String → List Pattern → List (List Pattern)
  | "outsideScope", [scopeHandle, queryHandle] =>
      match lookupHandle provider.handles.scopes scopeHandle,
        lookupHandle provider.handles.queries queryHandle with
      | some scope, some query =>
          if provider.outside scope query then
            [[scopeHandle, queryHandle]] else []
      | _, _ => []
  | _, _ => []

def relationEnv {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope) : RelationEnv where
  tuples := rows provider

theorem rows_mem_iff {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) :
    [scopeHandle, queryHandle] ∈
        rows provider "outsideScope" [scopeHandle, queryHandle] ↔
      ∃ scope query,
        lookupHandle provider.handles.scopes scopeHandle = some scope ∧
        lookupHandle provider.handles.queries queryHandle = some query ∧
        provider.outside scope query = true := by
  cases hs : lookupHandle provider.handles.scopes scopeHandle with
  | none => simp [rows, hs]
  | some scope =>
      cases hq : lookupHandle provider.handles.queries queryHandle with
      | none => simp [rows, hs, hq]
      | some query =>
          cases hcheck : provider.outside scope query <;>
            simp [rows, hs, hq, hcheck]

theorem rows_row_eq {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) (row : List Pattern)
    (returned : row ∈ rows provider "outsideScope"
      [scopeHandle, queryHandle]) :
    row = [scopeHandle, queryHandle] := by
  cases hs : lookupHandle provider.handles.scopes scopeHandle with
  | none => simp [rows, hs] at returned
  | some scope =>
      cases hq : lookupHandle provider.handles.queries queryHandle with
      | none => simp [rows, hs, hq] at returned
      | some query =>
          cases hcheck : provider.outside scope query with
          | false => simp [rows, hs, hq, hcheck] at returned
          | true =>
              simp [rows, hs, hq, hcheck] at returned
              exact returned

theorem returned_row_implies_outside
    {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (scopeHandle queryHandle : Pattern) (scope : Scope) (query : Query)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (returned : [scopeHandle, queryHandle] ∈
      (relationEnv provider).tuples "outsideScope" [scopeHandle, queryHandle]) :
    ¬ inScope scope query := by
  obtain ⟨decodedScope, decodedQuery, hs, hq, accepted⟩ :=
    (rows_mem_iff provider scopeHandle queryHandle).mp returned
  have scopeEq : decodedScope = scope := by
    rw [scopeDecode] at hs
    exact (Option.some.inj hs).symm
  have queryEq : decodedQuery = query := by
    rw [queryDecode] at hq
    exact (Option.some.inj hq).symm
  subst decodedScope
  subst decodedQuery
  exact provider.outside_sound scope query accepted

/-- The premise evaluator does not weaken the checked-provider contract:
when its rule variables are already bound, any successful result is backed
by an accepted provider row and hence a semantic outside-scope fact. -/
theorem premise_success_implies_outside
    {Scope Query : Type} {inScope : Scope → Query → Prop}
    (provider : CheckedProvider Scope Query inScope)
    (lang : LanguageDef)
    (scopeHandle worldHandle queryHandle : Pattern)
    (scope : Scope) (query : Query)
    (scopeDecode : lookupHandle provider.handles.scopes scopeHandle = some scope)
    (queryDecode : lookupHandle provider.handles.queries queryHandle = some query)
    (success : [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)] ∈
      applyPremisesWithEnv (relationEnv provider) lang
        ruleForgetOutside.premises
        [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    ¬ inScope scope query := by
  have returned : [scopeHandle, queryHandle] ∈
      (relationEnv provider).tuples "outsideScope"
        [scopeHandle, queryHandle] := by
    simp [applyPremisesWithEnv, ruleForgetOutside,
      premiseStepWithEnv, relationQueryStep, builtinRelationTuples,
      mergeBindings, applyBindings] at success
    obtain ⟨row, rowMember, _⟩ := success
    have rowEq := rows_row_eq provider scopeHandle queryHandle row rowMember
    simpa only [rowEq] using rowMember
  exact returned_row_implies_outside provider scopeHandle queryHandle
    scope query scopeDecode queryDecode returned

#print axioms rows_mem_iff
#print axioms rows_row_eq
#print axioms returned_row_implies_outside
#print axioms premise_success_implies_outside

/-! ## Erasure and outside-scope rows

The conservation rules ask whether forgetting a scope erases a revision
(`erasesInScope`) and whether a query lies outside a scope (`outsideScope`).
A checked erasure provider answers both from finite handle tables, for any
forgetting layer.  Anti-hallucination and Noether conservation ask the erasure
query with the scope unbound, so the provider lists every scope handle whose
scope erases the decoded state; the premise evaluator binds the scope from the
row, or checks it when the rule has bound it already.  Soundness is relative
to the table, as for `outsideScope`. -/

namespace Conservation

open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore (ConjugateEvidence)
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
  (ForgettingLayer GenericWorldModelZeroPreserving)
open Mettapedia.PLN.WorldModel.WorldModelConservationPack
  (OutsideLeakageBudget antiHallucination_outsideScope_of_erases
    outsideScopeEvidence_conserved_of_erases outsideLeakageBudget_zero_of_erases)

section Provider

variable {State Scope Query Ev : Type}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Finite scope, state and query handles. -/
structure ForgettingHandleTable (Scope State Query : Type) where
  scopes : List (Pattern × Scope)
  states : List (Pattern × State)
  queries : List (Pattern × Query)

/-- Boolean erasure and outside-scope checks.  They may be incomplete, but
every accepted answer is proved in the forgetting layer `F`. -/
structure CheckedErasureProvider (F : ForgettingLayer State Scope Query Ev) where
  handles : ForgettingHandleTable Scope State Query
  erases : Scope → State → Bool
  erases_sound : ∀ S Δ, erases S Δ = true → F.forget S Δ = 0
  outside : Scope → Query → Bool
  outside_sound : ∀ S q, outside S q = true → ¬ F.inScope S q

variable {F : ForgettingLayer State Scope Query Ev}

/-- The scope handles whose decoded scope erases `Δ`. -/
def erasingScopeHandles (E : CheckedErasureProvider F) (Δ : State) : List Pattern :=
  (E.handles.scopes.map Prod.fst).filter fun scopeHandle =>
    match lookupHandle E.handles.scopes scopeHandle with
    | some S => E.erases S Δ
    | none => false

/-- An erasure row names a scope handle that erases the decoded state; the
scope position of the query is not read.  An outside-scope row is returned
only after both handles decode and the check accepts. -/
def erasureRows (E : CheckedErasureProvider F) :
    String → List Pattern → List (List Pattern)
  | "erasesInScope", [_, stateHandle] =>
      match lookupHandle E.handles.states stateHandle with
      | some Δ => (erasingScopeHandles E Δ).map fun scopeHandle => [scopeHandle, stateHandle]
      | none => []
  | "outsideScope", [scopeHandle, queryHandle] =>
      match lookupHandle E.handles.scopes scopeHandle,
        lookupHandle E.handles.queries queryHandle with
      | some S, some q => if E.outside S q then [[scopeHandle, queryHandle]] else []
      | _, _ => []
  | _, _ => []

def erasureRelationEnv (E : CheckedErasureProvider F) : RelationEnv where
  tuples := erasureRows E

/-- What a relation environment must certify for the conservation rules: an
erasure row names a scope and a state that decode, with the state erased by
the scope; an outside-scope row names a scope and a query that decode, with
the query outside the scope. -/
structure CertifiesErasure (F : ForgettingLayer State Scope Query Ev)
    (handles : ForgettingHandleTable Scope State Query) (env : RelationEnv) : Prop where
  erased : ∀ {scopeArgument stateHandle : Pattern} {row : List Pattern},
    row ∈ env.tuples "erasesInScope" [scopeArgument, stateHandle] →
      ∃ scopeHandle S Δ, row = [scopeHandle, stateHandle] ∧
        lookupHandle handles.scopes scopeHandle = some S ∧
        lookupHandle handles.states stateHandle = some Δ ∧ F.forget S Δ = 0
  outside : ∀ {scopeHandle queryHandle : Pattern} {row : List Pattern},
    row ∈ env.tuples "outsideScope" [scopeHandle, queryHandle] →
      row = [scopeHandle, queryHandle] ∧ ∃ S q,
        lookupHandle handles.scopes scopeHandle = some S ∧
        lookupHandle handles.queries queryHandle = some q ∧ ¬ F.inScope S q

/-- A returned erasure row proves that forgetting the decoded scope erases the
decoded state. -/
theorem erased_of_row (E : CheckedErasureProvider F)
    {scopeArgument stateHandle : Pattern} {row : List Pattern}
    (returned : row ∈ erasureRows E "erasesInScope" [scopeArgument, stateHandle]) :
    ∃ scopeHandle S Δ, row = [scopeHandle, stateHandle] ∧
      lookupHandle E.handles.scopes scopeHandle = some S ∧
      lookupHandle E.handles.states stateHandle = some Δ ∧ F.forget S Δ = 0 := by
  cases stateDecode : lookupHandle E.handles.states stateHandle with
  | none => simp [erasureRows, stateDecode] at returned
  | some Δ =>
      simp only [erasureRows, stateDecode, List.mem_map] at returned
      obtain ⟨scopeHandle, member, rfl⟩ := returned
      simp only [erasingScopeHandles, List.mem_filter] at member
      obtain ⟨_, accepted⟩ := member
      cases scopeDecode : lookupHandle E.handles.scopes scopeHandle with
      | none => simp [scopeDecode] at accepted
      | some S =>
          simp only [scopeDecode] at accepted
          exact ⟨scopeHandle, S, Δ, rfl, scopeDecode, rfl, E.erases_sound S Δ accepted⟩

/-- A returned outside-scope row proves that the decoded query lies outside
the decoded scope. -/
theorem outside_of_row (E : CheckedErasureProvider F)
    {scopeHandle queryHandle : Pattern} {row : List Pattern}
    (returned : row ∈ erasureRows E "outsideScope" [scopeHandle, queryHandle]) :
    row = [scopeHandle, queryHandle] ∧ ∃ S q,
      lookupHandle E.handles.scopes scopeHandle = some S ∧
      lookupHandle E.handles.queries queryHandle = some q ∧ ¬ F.inScope S q := by
  cases scopeDecode : lookupHandle E.handles.scopes scopeHandle with
  | none => simp [erasureRows, scopeDecode] at returned
  | some S =>
      cases queryDecode : lookupHandle E.handles.queries queryHandle with
      | none => simp [erasureRows, scopeDecode, queryDecode] at returned
      | some q =>
          cases accepted : E.outside S q with
          | false => simp [erasureRows, scopeDecode, queryDecode, accepted] at returned
          | true =>
              simp only [erasureRows, scopeDecode, queryDecode, accepted, if_true,
                List.mem_singleton] at returned
              exact ⟨returned, S, q, rfl, rfl, E.outside_sound S q accepted⟩

theorem erasureRelationEnv_certifies (E : CheckedErasureProvider F) :
    CertifiesErasure F E.handles (erasureRelationEnv E) where
  erased {scopeArgument stateHandle row} returned :=
    erased_of_row E (scopeArgument := scopeArgument) (stateHandle := stateHandle) (row := row)
      returned
  outside {scopeHandle queryHandle row} returned :=
    outside_of_row E (scopeHandle := scopeHandle) (queryHandle := queryHandle) (row := row)
      returned

variable {handles : ForgettingHandleTable Scope State Query} {env : RelationEnv}

/-- Decoding is deterministic. -/
private theorem decode_unique {Value : Type} {table : List (Pattern × Value)}
    {handle : Pattern} {first second : Value}
    (decodesFirst : lookupHandle table handle = some first)
    (decodesSecond : lookupHandle table handle = some second) : first = second := by
  rw [decodesFirst] at decodesSecond
  exact Option.some.inj decodesSecond

/-- When the conservation premises succeed on bindings that bind `D` and `q`
and leave `S` free, some decoded scope erases the decoded revision and
excludes the decoded query. -/
private theorem erasedOutside_of_success (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (bindings : Bindings) (revisionHandle queryHandle : Pattern)
    {Δ : State} {q : Query}
    (freeS : bindings.find? (·.1 == "S") = none)
    (foundD : bindings.find? (·.1 == "D") = some ("D", revisionHandle))
    (foundQ : bindings.find? (·.1 == "q") = some ("q", queryHandle))
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang erasedOutsideScopePremises bindings) :
    ∃ S, F.forget S Δ = 0 ∧ ¬ F.inScope S q := by
  simp only [erasedOutsideScopePremises, applyPremisesWithEnv, List.foldl,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap] at success
  obtain ⟨middle, erasedStep, outsideStep⟩ := success
  simp only [premiseStepWithEnv, relationQueryStep, List.mem_flatMap, List.mem_filterMap,
    List.mem_append] at erasedStep
  obtain ⟨erasedRow, erasedReturned, extension, matched, merged⟩ := erasedStep
  rcases erasedReturned with builtin | erasedReturned
  · simp [builtinRelationTuples] at builtin
  have unboundS : applyBindings bindings (.fvar "S") = .fvar "S" := by
    simp [applyBindings, freeS]
  have boundD : applyBindings bindings (.fvar "D") = revisionHandle := by
    simp [applyBindings, foundD]
  simp only [List.map_cons, List.map_nil, unboundS, boundD] at erasedReturned
  obtain ⟨scopeHandle, S, decoded, rfl, scopeDecode, stateDecode, erased⟩ :=
    certified.erased erasedReturned
  obtain rfl : decoded = Δ := decode_unique stateDecode revisionDecode
  have extensionEq : extension = [("S", scopeHandle)] := by
    simpa [matchRelationArgs, matchRelationArgument, Bindings.lookup, freeS, foundD,
      mergeBindings] using matched
  subst extensionEq
  have middleEq : middle = ("S", scopeHandle) :: bindings := by
    simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil, freeS] at merged
    exact (Option.some.inj merged).symm
  subst middleEq
  simp only [premiseStepWithEnv, relationQueryStep, List.mem_flatMap, List.mem_filterMap,
    List.mem_append] at outsideStep
  obtain ⟨outsideRow, outsideReturned, _⟩ := outsideStep
  rcases outsideReturned with builtin | outsideReturned
  · simp [builtinRelationTuples] at builtin
  have boundS : applyBindings (("S", scopeHandle) :: bindings) (.fvar "S") = scopeHandle := by
    simp [applyBindings]
  have boundQ : applyBindings (("S", scopeHandle) :: bindings) (.fvar "q") = queryHandle := by
    simp [applyBindings, foundQ]
  simp only [List.map_cons, List.map_nil, boundS, boundQ] at outsideReturned
  obtain ⟨_, outsideScope, outsideQuery, scopeDecode', queryDecode', outside⟩ :=
    certified.outside outsideReturned
  rw [decode_unique scopeDecode' scopeDecode, decode_unique queryDecode' queryDecode] at outside
  exact ⟨S, erased, outside⟩

/-- When anti-hallucination's premises succeed on a matched redex
`Extract(D, q)`, some decoded scope erases the decoded revision and excludes
the decoded query. -/
theorem erasedOutside_of_antiHallucination (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (revisionHandle queryHandle : Pattern) {Δ : State} {q : Query}
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleAntiHallucination.premises
      [("q", queryHandle), ("D", revisionHandle)]) :
    ∃ S, F.forget S Δ = 0 ∧ ¬ F.inScope S q :=
  erasedOutside_of_success certified lang _ revisionHandle queryHandle
    (by simp) (by simp) (by simp) revisionDecode queryDecode success

/-- The same for Noether conservation's redex `Extract(Revise(W, D), q)`. -/
theorem erasedOutside_of_noetherConservation (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (worldHandle revisionHandle queryHandle : Pattern)
    {Δ : State} {q : Query}
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleNoetherConservation.premises
      [("q", queryHandle), ("D", revisionHandle), ("W", worldHandle)]) :
    ∃ S, F.forget S Δ = 0 ∧ ¬ F.inScope S q :=
  erasedOutside_of_success certified lang _ revisionHandle queryHandle
    (by simp) (by simp) (by simp) revisionDecode queryDecode success

/-- When zero leakage's premise succeeds on a matched redex
`LeakageBudget(S, D, EvidenceZero)`, forgetting the decoded scope erases the
decoded revision. -/
theorem erased_of_zeroLeakage (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (scopeHandle revisionHandle : Pattern) {S : Scope} {Δ : State}
    (scopeDecode : lookupHandle handles.scopes scopeHandle = some S)
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleZeroLeakage.premises
      [("D", revisionHandle), ("S", scopeHandle)]) :
    F.forget S Δ = 0 := by
  simp only [ruleZeroLeakage, applyPremisesWithEnv, List.foldl, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, premiseStepWithEnv, relationQueryStep,
    List.mem_flatMap, List.mem_filterMap, List.mem_append] at success
  obtain ⟨row, returned, extension, matched, _⟩ := success
  rcases returned with builtin | returned
  · simp [builtinRelationTuples] at builtin
  have boundS : applyBindings [("D", revisionHandle), ("S", scopeHandle)] (.fvar "S") =
      scopeHandle := by
    simp [applyBindings]
  have boundD : applyBindings [("D", revisionHandle), ("S", scopeHandle)] (.fvar "D") =
      revisionHandle := by
    simp [applyBindings]
  simp only [List.map_cons, List.map_nil, boundS, boundD] at returned
  obtain ⟨rowScope, decodedScope, decoded, rfl, rowScopeDecode, stateDecode, erased⟩ :=
    certified.erased returned
  have sameScope : rowScope = scopeHandle := by
    by_contra different
    have differs : scopeHandle ≠ rowScope := fun same => different same.symm
    simp [matchRelationArgs, matchRelationArgument, Bindings.lookup, mergeBindings,
      differs] at matched
  subst sameScope
  rw [decode_unique rowScopeDecode scopeDecode, decode_unique stateDecode revisionDecode]
    at erased
  exact erased

/-- When the outside-scope premise succeeds on a matched redex
`Extract(Forget(S, W), q)`, the decoded query lies outside the decoded
scope. -/
theorem outside_of_forgetOutside (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (scopeHandle worldHandle queryHandle : Pattern)
    {S : Scope} {q : Query}
    (scopeDecode : lookupHandle handles.scopes scopeHandle = some S)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleForgetOutside.premises
      [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    ¬ F.inScope S q := by
  simp only [ruleForgetOutside, applyPremisesWithEnv, List.foldl, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, premiseStepWithEnv, relationQueryStep,
    List.mem_flatMap, List.mem_filterMap, List.mem_append] at success
  obtain ⟨row, returned, _⟩ := success
  rcases returned with builtin | returned
  · simp [builtinRelationTuples] at builtin
  have boundS : applyBindings [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]
      (.fvar "S") = scopeHandle := by
    simp [applyBindings]
  have boundQ : applyBindings [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]
      (.fvar "q") = queryHandle := by
    simp [applyBindings]
  simp only [List.map_cons, List.map_nil, boundS, boundQ] at returned
  obtain ⟨_, decodedScope, decodedQuery, scopeDecode', queryDecode', outside⟩ :=
    certified.outside returned
  rw [decode_unique scopeDecode' scopeDecode, decode_unique queryDecode' queryDecode]
    at outside
  exact outside

/-- **Outside-scope invariance is sound**: when its premise succeeds on decoded
handles, forgetting the scope leaves the query's evidence unchanged on every
base, by the layer's outside invariant. -/
theorem forgetOutside_sound (certified : CertifiesErasure F handles env)
    (lang : LanguageDef) (scopeHandle worldHandle queryHandle : Pattern)
    {S : Scope} {q : Query}
    (scopeDecode : lookupHandle handles.scopes scopeHandle = some S)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleForgetOutside.premises
      [("q", queryHandle), ("W", worldHandle), ("S", scopeHandle)]) :
    ∀ W : State,
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev)
          (F.forget S W) q =
        AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q :=
  fun _ => F.outsideInvariant (outside_of_forgetOutside certified lang scopeHandle
    worldHandle queryHandle scopeDecode queryDecode success)

end Provider

/-! ### Soundness against the conservation pack -/

section Soundness

variable {State Scope Query Ev : Type}
variable [EvidenceType State] [ConjugateEvidence Ev] [AdditiveWorldModel State Query Ev]
variable {F : ForgettingLayer State Scope Query Ev}
variable {handles : ForgettingHandleTable Scope State Query} {env : RelationEnv}

/-- **Anti-hallucination is sound**: when its premises succeed on decoded
handles, the revision carries no evidence at the query, as in
`antiHallucination_outsideScope_of_erases`. -/
theorem antiHallucination_sound (certified : CertifiesErasure F handles env)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    (lang : LanguageDef) (revisionHandle queryHandle : Pattern) {Δ : State} {q : Query}
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleAntiHallucination.premises
      [("q", queryHandle), ("D", revisionHandle)]) :
    AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) Δ q = 0 := by
  obtain ⟨S, erased, outside⟩ := erasedOutside_of_antiHallucination certified lang
    revisionHandle queryHandle revisionDecode queryDecode success
  exact antiHallucination_outsideScope_of_erases F hzero erased q outside

/-- **Noether conservation is sound**: when its premises succeed on decoded
handles, adding the revision changes the query's evidence on no base, as in
`outsideScopeEvidence_conserved_of_erases`. -/
theorem noetherConservation_sound (certified : CertifiesErasure F handles env)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    (lang : LanguageDef) (worldHandle revisionHandle queryHandle : Pattern)
    {Δ : State} {q : Query}
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    (queryDecode : lookupHandle handles.queries queryHandle = some q)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleNoetherConservation.premises
      [("q", queryHandle), ("D", revisionHandle), ("W", worldHandle)]) :
    ∀ W : State,
      AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) (W + Δ) q =
        AdditiveWorldModel.extract (State := State) (Query := Query) (Ev := Ev) W q := by
  obtain ⟨S, erased, outside⟩ := erasedOutside_of_noetherConservation certified lang
    worldHandle revisionHandle queryHandle revisionDecode queryDecode success
  exact fun W => outsideScopeEvidence_conserved_of_erases F hzero erased W q outside

/-- **Zero leakage is sound**: when its premise succeeds on decoded handles,
the revision's outside-scope leakage budget is zero, as in
`outsideLeakageBudget_zero_of_erases`. -/
theorem zeroLeakage_sound (certified : CertifiesErasure F handles env)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    (lang : LanguageDef) (scopeHandle revisionHandle : Pattern) {S : Scope} {Δ : State}
    (scopeDecode : lookupHandle handles.scopes scopeHandle = some S)
    (revisionDecode : lookupHandle handles.states revisionHandle = some Δ)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv env lang ruleZeroLeakage.premises
      [("D", revisionHandle), ("S", scopeHandle)]) :
    OutsideLeakageBudget F S Δ 0 :=
  outsideLeakageBudget_zero_of_erases F hzero
    (erased_of_zeroLeakage certified lang scopeHandle revisionHandle scopeDecode
      revisionDecode success)

end Soundness

end Conservation

/-! ## Support and cleanliness rows

`ruleForgetAbsorbSupported` asks whether a revision is supported in a scope
(`supportedInScope`), and `ruleForgetClean` whether a state is clean for it
(`cleanForScope`).  A checked support provider answers both from finite handle
tables, and every row it returns comes with a proof of `Supported` or `Clean`
in a support-tracked forgetting layer.  Soundness is relative to the table:
the table names values, it does not read arbitrary patterns. -/

namespace SupportTracked

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.PLN.Evidence.EvidenceClass (EvidenceType)
open Mettapedia.PLN.Bridges.ProbabilityTheory.ConjugateEvidenceCore (ConjugateEvidence)
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric (AdditiveWorldModel)
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting (GenericWorldModelZeroPreserving)
open Mettapedia.PLN.WorldModel.WorldModelConservationPack (OutsideLeakageBudget)
open Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
  (SupportTrackedForgettingLayer)

section Provider

variable {State Scope Query Ev Supp : Type}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Boolean support and cleanliness checks, beside the erasure and
outside-scope checks of the underlying forgetting layer.  They may be
incomplete, but every accepted answer is proved in the forgetting layer `F`. -/
structure CheckedSupportProvider
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    extends Conservation.CheckedErasureProvider F.toForgettingLayer where
  supported : Scope → State → Bool
  supported_sound : ∀ S Δ, supported S Δ = true → F.Supported S Δ
  clean : Scope → State → Bool
  clean_sound : ∀ S W, clean S W = true → F.Clean S W

variable {F : SupportTrackedForgettingLayer State Scope Query Ev Supp}

/-- A row is returned only after both handles decode and the check accepts.
Erasure and outside-scope rows are the erasure provider's. -/
def supportRows (P : CheckedSupportProvider F) :
    String → List Pattern → List (List Pattern)
  | "supportedInScope", [scopeHandle, stateHandle] =>
      match lookupHandle P.handles.scopes scopeHandle,
        lookupHandle P.handles.states stateHandle with
      | some S, some Δ => if P.supported S Δ then [[scopeHandle, stateHandle]] else []
      | _, _ => []
  | "cleanForScope", [scopeHandle, stateHandle] =>
      match lookupHandle P.handles.scopes scopeHandle,
        lookupHandle P.handles.states stateHandle with
      | some S, some W => if P.clean S W then [[scopeHandle, stateHandle]] else []
      | _, _ => []
  | relation, arguments =>
      Conservation.erasureRows P.toCheckedErasureProvider relation arguments

def supportRelationEnv (P : CheckedSupportProvider F) : RelationEnv where
  tuples := supportRows P

/-- The support provider's environment certifies the conservation rules'
rows. -/
theorem supportRelationEnv_certifies (P : CheckedSupportProvider F) :
    Conservation.CertifiesErasure F.toForgettingLayer P.handles (supportRelationEnv P) where
  erased {scopeArgument stateHandle row} returned :=
    Conservation.erased_of_row P.toCheckedErasureProvider (scopeArgument := scopeArgument)
      (stateHandle := stateHandle) (row := row)
      (by simpa [supportRelationEnv, supportRows] using returned)
  outside {scopeHandle queryHandle row} returned :=
    Conservation.outside_of_row P.toCheckedErasureProvider (scopeHandle := scopeHandle)
      (queryHandle := queryHandle) (row := row)
      (by simpa [supportRelationEnv, supportRows] using returned)

/-- A returned `supportedInScope` row proves that the decoded revision is
supported in the decoded scope. -/
theorem supported_of_row (P : CheckedSupportProvider F)
    {scopeHandle stateHandle : Pattern} {S : Scope} {Δ : State}
    (scopeDecode : lookupHandle P.handles.scopes scopeHandle = some S)
    (stateDecode : lookupHandle P.handles.states stateHandle = some Δ)
    {row : List Pattern}
    (returned : row ∈ (supportRelationEnv P).tuples "supportedInScope"
      [scopeHandle, stateHandle]) :
    F.Supported S Δ := by
  cases accepted : P.supported S Δ with
  | false =>
      simp [supportRelationEnv, supportRows, scopeDecode, stateDecode, accepted] at returned
  | true => exact P.supported_sound S Δ accepted

/-- A returned `cleanForScope` row proves that the decoded state is clean for
the decoded scope. -/
theorem clean_of_row (P : CheckedSupportProvider F)
    {scopeHandle stateHandle : Pattern} {S : Scope} {W : State}
    (scopeDecode : lookupHandle P.handles.scopes scopeHandle = some S)
    (stateDecode : lookupHandle P.handles.states stateHandle = some W)
    {row : List Pattern}
    (returned : row ∈ (supportRelationEnv P).tuples "cleanForScope"
      [scopeHandle, stateHandle]) :
    F.Clean S W := by
  cases accepted : P.clean S W with
  | false =>
      simp [supportRelationEnv, supportRows, scopeDecode, stateDecode, accepted] at returned
  | true => exact P.clean_sound S W accepted

/-- **Absorption is sound**: when its premise succeeds on decoded handles,
forgetting after the revision equals forgetting before it, on every base. -/
theorem forgetAbsorbSupported_sound (P : CheckedSupportProvider F) (lang : LanguageDef)
    (scopeHandle worldHandle revisionHandle : Pattern) {S : Scope} {Δ : State}
    (scopeDecode : lookupHandle P.handles.scopes scopeHandle = some S)
    (revisionDecode : lookupHandle P.handles.states revisionHandle = some Δ)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv (supportRelationEnv P) lang
      ruleForgetAbsorbSupported.premises
      [("W", worldHandle), ("D", revisionHandle), ("S", scopeHandle)]) :
    ∀ W : State, F.forget S (W + Δ) = F.forget S W := by
  simp [applyPremisesWithEnv, ruleForgetAbsorbSupported, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, applyBindings] at success
  obtain ⟨row, returned, _⟩ := success
  exact F.forget_add_of_supported (supported_of_row P scopeDecode revisionDecode returned)

/-- **The clean-base identity is sound**: when its premise succeeds on decoded
handles, forgetting fixes the decoded state. -/
theorem forgetClean_sound (P : CheckedSupportProvider F) (lang : LanguageDef)
    (scopeHandle worldHandle : Pattern) {S : Scope} {W : State}
    (scopeDecode : lookupHandle P.handles.scopes scopeHandle = some S)
    (worldDecode : lookupHandle P.handles.states worldHandle = some W)
    {final : Bindings}
    (success : final ∈ applyPremisesWithEnv (supportRelationEnv P) lang
      ruleForgetClean.premises [("W", worldHandle), ("S", scopeHandle)]) :
    F.forget S W = W := by
  simp [applyPremisesWithEnv, ruleForgetClean, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, applyBindings] at success
  obtain ⟨row, returned, _⟩ := success
  exact F.forget_eq_self_of_clean (clean_of_row P scopeDecode worldDecode returned)

/-- When both premises succeed, the revision of the clean base is undone
exactly, as in `SupportTrackedForgettingLayer.exactInverse_of_clean`. -/
theorem forgetAbsorbSupported_forgetClean_sound (P : CheckedSupportProvider F)
    (lang : LanguageDef) (scopeHandle worldHandle revisionHandle : Pattern)
    {S : Scope} {W Δ : State}
    (scopeDecode : lookupHandle P.handles.scopes scopeHandle = some S)
    (worldDecode : lookupHandle P.handles.states worldHandle = some W)
    (revisionDecode : lookupHandle P.handles.states revisionHandle = some Δ)
    {absorbed : Bindings}
    (absorbs : absorbed ∈ applyPremisesWithEnv (supportRelationEnv P) lang
      ruleForgetAbsorbSupported.premises
      [("W", worldHandle), ("D", revisionHandle), ("S", scopeHandle)])
    {cleaned : Bindings}
    (cleans : cleaned ∈ applyPremisesWithEnv (supportRelationEnv P) lang
      ruleForgetClean.premises [("W", worldHandle), ("S", scopeHandle)]) :
    F.forget S (W + Δ) = W := by
  rw [forgetAbsorbSupported_sound P lang scopeHandle worldHandle revisionHandle
      scopeDecode revisionDecode absorbs W,
    forgetClean_sound P lang scopeHandle worldHandle scopeDecode worldDecode cleans]

end Provider

/-! ## Control: the premise-free inverse against the rules with premises

A ledger of observation identities is a support-tracked forgetting layer: the
evidence for the claim "`o` was recorded" is the number of times `o` occurs,
the support of that claim is `{o}` when `o` occurs, and forgetting a scope
deletes the scope's identities.  The scope `{0}`, the base `{1}` and the
revision `{0, 2}` separate the rules: the revision is not supported in `{0}`
(it records `2`), and the revised ledger is not clean for `{0}` (it records
`0`).

* The premise-free rule `Forget(S, Revise(W, D)) ↦ W` rewrites
  `Forget({0}, Revise({1}, {0, 2}))` to `{1}`, although forgetting gives
  `{1, 2}` (`premiseFreeInverse_rewrites_unsupported`,
  `premiseFreeInverse_unsound`).
* The maximal calculus has no step from that term
  (`maximal_refuses_unsupported`).
* It undoes the supported revision `{0}` of the clean base `{1}` in two steps
  (`maximal_absorbs_supported`, `maximal_clean_base`).  On the base `{0, 1}`,
  which is not clean, it absorbs the revision and stops at
  `Forget({0}, {0, 1})`, whose value `{1}` is not the base
  (`maximal_absorbs_on_unclean_base`, `maximal_stops_on_unclean_base`,
  `inverse_fails_on_unclean_base`). -/

namespace Control

/-- Claims "observation `o` was recorded", counted in a ledger of identities. -/
local instance idLedger : AdditiveWorldModel (Multiset ℕ) ℕ ℕ where
  extract ledger o := ledger.count o
  extract_add ledger ledger' o := Multiset.count_add o ledger ledger'

/-- Deleting a scope's identities from a ledger. -/
def ledgerForgetting :
    SupportTrackedForgettingLayer (Multiset ℕ) (Finset ℕ) ℕ ℕ ℕ where
  inScope S o := o ∈ S
  forget S ledger := ledger.filter (· ∉ S)
  idempotent S ledger := by simp [Multiset.filter_filter]
  outsideInvariant := by
    intro S ledger o outside
    exact Multiset.count_filter_of_pos outside
  scopeFootprint S := S
  support ledger o := (ledger.filter (· = o)).toFinset
  forget_add S ledger ledger' := Multiset.filter_add _ _ _
  forget_eq_zero_of_supported := by
    intro S Δ supported
    refine Multiset.filter_eq_nil.mpr fun o member outside => outside (supported o ?_)
    simp [member]
  forget_eq_self_of_clean := by
    intro S W clean
    refine Multiset.filter_eq_self.mpr fun o member inside => ?_
    exact Finset.disjoint_left.mp (clean o) (by simp [member]) inside

/-- Exact decisions: forgetting a scope erases a revision, and the revision is
supported in it, when every identity the revision records is in the scope; a
ledger is clean when none is; an identity is outside a scope when it is not in
it. -/
def ledgerProvider
    (handles : Conservation.ForgettingHandleTable (Finset ℕ) (Multiset ℕ) ℕ) :
    CheckedSupportProvider ledgerForgetting where
  handles := handles
  erases S Δ := decide (∀ o ∈ Δ, o ∈ S)
  erases_sound S Δ accepted :=
    Multiset.filter_eq_nil.mpr fun o member outside =>
      outside (of_decide_eq_true accepted o member)
  outside S o := decide (o ∉ S)
  outside_sound S o accepted := (of_decide_eq_true accepted : o ∉ S)
  supported S Δ := decide (∀ o ∈ Δ, o ∈ S)
  supported_sound S Δ accepted := by
    intro q o member
    simp only [ledgerForgetting, Multiset.mem_toFinset, Multiset.mem_filter] at member
    obtain ⟨recorded, rfl⟩ := member
    exact of_decide_eq_true accepted _ recorded
  clean S W := decide (∀ o ∈ W, o ∉ S)
  clean_sound S W accepted := by
    intro q
    rw [Finset.disjoint_left]
    intro o member
    simp only [ledgerForgetting, Multiset.mem_toFinset, Multiset.mem_filter] at member
    exact of_decide_eq_true accepted o member.1

def scopeZero : Pattern := .fvar "scope:{0}"
def baseOne : Pattern := .fvar "state:{1}"
def baseZeroOne : Pattern := .fvar "state:{0,1}"
def revisionZero : Pattern := .fvar "state:{0}"
def revisionZeroTwo : Pattern := .fvar "state:{0,2}"
def scopeOne : Pattern := .fvar "scope:{1}"
def queryZero : Pattern := .fvar "query:0"
def queryOne : Pattern := .fvar "query:1"

/-- One name for the scope `{1}` and for the state `{0}`, as a backend that
numbers the entries of each sort separately would give them. -/
def sharedName : Pattern := .fvar "#1"

/-- The handle table; the revised ledger `Revise({1}, {0, 2})` is named with
its value so that its cleanliness is decided on that value. -/
def controlTable : Conservation.ForgettingHandleTable (Finset ℕ) (Multiset ℕ) ℕ where
  scopes := [(scopeZero, {0}), (scopeOne, {1}), (sharedName, {1})]
  states := [(baseOne, {1}), (baseZeroOne, {0, 1}), (revisionZero, {0}),
    (revisionZeroTwo, {0, 2}), (pRevise baseOne revisionZeroTwo, {1} + {0, 2}),
    (sharedName, {0})]
  queries := [(queryZero, 0), (queryOne, 1)]

def controlEnv : RelationEnv := supportRelationEnv (ledgerProvider controlTable)

/-- The premise-free rule `Forget(S, Revise(W, D)) ↦ W`, the inverse on every
base.  It is in no rule list; it serves only as the negative control. -/
def premiseFreeInverse : RewriteRule := {
  name := "WM_PremiseFreeInverse_Control"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("D", .base "State")]
  premises := []
  left := pForget (.fvar "S") (pRevise (.fvar "W") (.fvar "D"))
  right := .fvar "W"
}

/-- The maximal calculus. -/
abbrev maximalCalculus : LanguageDef := wmFullVertexLanguageDef wmFullVertexMaximal

/-- The maximal calculus with the premise-free rule added. -/
def withPremiseFreeInverse : LanguageDef :=
  { maximalCalculus with rewrites := premiseFreeInverse :: maximalCalculus.rewrites }

def unsupportedRedex : Pattern := pForget scopeZero (pRevise baseOne revisionZeroTwo)

private def noncontextualPremises : List Premise → Bool
  | [] => true
  | .freshness _ :: rest => noncontextualPremises rest
  | .relationQuery _ _ :: rest => noncontextualPremises rest
  | .forAll _ _ _ :: rest => noncontextualPremises rest
  | .congruence _ _ :: _ => false
  | .scopedStep _ :: _ => false

private theorem noncontextualPremises_sound : ∀ {premises : List Premise},
    noncontextualPremises premises = true → NoncontextualPremises premises
  | [], _ => .nil
  | .freshness _ :: _, accepted => .freshness (noncontextualPremises_sound accepted)
  | .relationQuery _ _ :: _, accepted => .relationQuery (noncontextualPremises_sound accepted)
  | .forAll _ _ _ :: _, accepted => .forAll (noncontextualPremises_sound accepted)
  | .congruence _ _ :: _, accepted => by simp [noncontextualPremises] at accepted
  | .scopedStep _ :: _, accepted => by simp [noncontextualPremises] at accepted

/-- No premise of the maximal calculus is contextual, so its steps are
the root steps the executable frontier lists. -/
theorem maximal_noncontextual :
    ∀ rule ∈ maximalCalculus.rewrites, NoncontextualPremises rule.premises := by
  have checked : ∀ rule ∈ maximalCalculus.rewrites,
      noncontextualPremises rule.premises = true := by
    decide +kernel
  exact fun rule member => noncontextualPremises_sound (checked rule member)

theorem withPremiseFreeInverse_noncontextual :
    ∀ rule ∈ withPremiseFreeInverse.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  rcases List.mem_cons.mp member with rfl | member
  · exact .nil
  · exact maximal_noncontextual rule member

/-- The handles name the scope `{0}`, the base `{1}` and the revision `{0, 2}`. -/
theorem unsupported_decodes :
    lookupHandle controlTable.scopes scopeZero = some {0} ∧
      lookupHandle controlTable.states baseOne = some {1} ∧
      lookupHandle controlTable.states revisionZeroTwo = some {0, 2} := by
  decide +kernel

/-- The revision `{0, 2}` is not supported in `{0}`, and the revised ledger is
not clean for `{0}`. -/
theorem unsupported_rows_absent :
    controlEnv.tuples "supportedInScope" [scopeZero, revisionZeroTwo] = [] ∧
      controlEnv.tuples "cleanForScope" [scopeZero, pRevise baseOne revisionZeroTwo] =
        [] := by
  decide +kernel

/-- With the premise-free rule, the unsupported revision has exactly one
reduct: the base. -/
theorem premiseFreeInverse_frontier :
    rewriteStepWithPremisesUsing controlEnv withPremiseFreeInverse unsupportedRedex =
      [baseOne] := by
  decide +kernel

/-- The maximal calculus gives it no reduct. -/
theorem maximal_frontier :
    rewriteStepWithPremisesUsing controlEnv maximalCalculus unsupportedRedex = [] := by
  decide +kernel

theorem premiseFreeInverse_rewrites_unsupported :
    langReducesUsing controlEnv withPremiseFreeInverse unsupportedRedex baseOne := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ withPremiseFreeInverse_noncontextual,
    premiseFreeInverse_frontier]
  exact List.mem_singleton_self _

theorem maximal_refuses_unsupported (target : Pattern) :
    ¬ langReducesUsing controlEnv maximalCalculus unsupportedRedex target := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    maximal_frontier]
  exact List.not_mem_nil

/-- Forgetting `{0}` after the revision `{0, 2}` of `{1}` gives `{1, 2}`, not the
base: the premise-free reduct has the wrong value. -/
theorem premiseFreeInverse_unsound :
    ledgerForgetting.forget {0} ({1} + {0, 2}) = {1, 2} ∧
      ledgerForgetting.forget {0} ({1} + {0, 2}) ≠ ({1} : Multiset ℕ) := by
  decide +kernel

/-- The supported revision `{0}` of the clean base `{1}` is absorbed. -/
theorem maximal_absorbs_supported :
    langReducesUsing controlEnv maximalCalculus
      (pForget scopeZero (pRevise baseOne revisionZero)) (pForget scopeZero baseOne) :=
  wmFullLangReducesUsing_forgetAbsorbSupported controlEnv wmFullVertexMaximal rfl
    scopeZero baseOne revisionZero (by decide +kernel)

/-- Forgetting fixes the clean base `{1}`. -/
theorem maximal_clean_base :
    langReducesUsing controlEnv maximalCalculus (pForget scopeZero baseOne) baseOne :=
  wmFullLangReducesUsing_forgetClean controlEnv wmFullVertexMaximal rfl
    scopeZero baseOne (by decide +kernel)

/-- The row that lets absorption fire certifies absorption on every base. -/
theorem control_absorption_sound (W : Multiset ℕ) :
    ledgerForgetting.forget {0} (W + {0}) = ledgerForgetting.forget {0} W :=
  forgetAbsorbSupported_sound (ledgerProvider controlTable) maximalCalculus
    scopeZero baseOne revisionZero (by decide +kernel) (by decide +kernel)
    (final := [("W", baseOne), ("D", revisionZero), ("S", scopeZero)])
    (by decide +kernel) W

/-- So the revision is undone exactly on the clean base. -/
theorem exact_on_clean_base :
    ledgerForgetting.forget {0} ({1} + {0}) = ({1} : Multiset ℕ) := by
  decide +kernel

/-- On the base `{0, 1}`, which is not clean, the revision is still absorbed. -/
theorem maximal_absorbs_on_unclean_base :
    langReducesUsing controlEnv maximalCalculus
      (pForget scopeZero (pRevise baseZeroOne revisionZero))
      (pForget scopeZero baseZeroOne) :=
  wmFullLangReducesUsing_forgetAbsorbSupported controlEnv wmFullVertexMaximal rfl
    scopeZero baseZeroOne revisionZero (by decide +kernel)

/-- There the calculus stops: `Forget({0}, {0, 1})` has no reduct. -/
theorem maximal_stops_on_unclean_base (target : Pattern) :
    ¬ langReducesUsing controlEnv maximalCalculus (pForget scopeZero baseZeroOne) target := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    show rewriteStepWithPremisesUsing controlEnv maximalCalculus
      (pForget scopeZero baseZeroOne) = [] by decide +kernel]
  exact List.not_mem_nil

/-- Rightly: forgetting gives `{1}`, not the base `{0, 1}`. -/
theorem inverse_fails_on_unclean_base :
    ledgerForgetting.forget {0} ({0, 1} + {0}) = {1} ∧
      ledgerForgetting.forget {0} ({0, 1} + {0}) ≠ ({0, 1} : Multiset ℕ) := by
  decide +kernel

/-! ### The conservation rules against premises that name no scope

The earlier premises named no scope.  Zero leakage asked only whether the
revision had an inverse property, and anti-hallucination also asked whether the
query lay outside the scope named by the revision's own handle.  Read as an
inverse on every base, that property holds only of zero revisions
(`ForgettingLayer.exactInverse_everywhere_degenerate`).  Read by erasure, the
scope it cannot name becomes existential: the one-argument test
`erasedBySomeScope(D)`, which some scope in the table passes when it erases the
decoded state (`scopeFree_sound`).

* On `LeakageBudget({1}, {0}, EvidenceZero)` the test accepts, since `{0}`
  erases `{0}`, but `{0}` leaks its evidence at `0`, outside `{1}`
  (`scopeFree_accepts_wrong_scope`, `wrong_scope_leaks`).  Zero leakage asks
  whether `{1}` erases `{0}` and refuses (`zeroLeakage_refuses_wrong_scope`).
  On `LeakageBudget({0}, {0}, EvidenceZero)` it fires and the budget holds
  (`zeroLeakage_accepts`, `control_zeroLeakage_sound`).
* `sharedName` names the scope `{1}` and the state `{0}`.  On
  `Extract(sharedName, 0)` the earlier anti-hallucination premises read the
  handle as the scope `{1}`, which excludes `0`, and accept, although `{0}` has
  evidence `1` at `0` (`scopeFree_antiHallucination_accepts`,
  `evidence_at_zero`).  The rule binds the scope `{0}` that erases `{0}`, finds
  `0` inside it, and the maximal calculus has no step
  (`maximal_refuses_shared`).  With separate names the earlier premises refuse
  even a correct case, because a state handle names no scope
  (`scopeFree_antiHallucination_refuses_correct`).
* In the maximal calculus anti-hallucination rewrites `Extract({0}, 1)`
  to `EvidenceZero`, and Noether conservation rewrites
  `Extract(Revise({1}, {0}), 1)` to `Extract({1}, 1)`; both conclusions hold
  (`maximal_antiHallucination`, `control_antiHallucination_sound`,
  `maximal_noetherConservation`, `control_noetherConservation_sound`).  At the
  query `0`, inside the erasing scope, neither fires
  (`maximal_refuses_inside`, `maximal_noether_frontier_inside`,
  `maximal_noether_refuses_inside`), and both conclusions would be false there
  (`evidence_at_zero`, `noether_fails_inside`). -/

/-- Observation counts of ledger evidence. -/
local instance countEvidence : ConjugateEvidence ℕ where
  toAddCommMonoid := inferInstance
  observationCount n := n
  observationCount_add a b := Nat.cast_add a b
  observationCount_zero := Nat.cast_zero

/-- The empty ledger records nothing. -/
theorem ledger_zeroPreserving :
    GenericWorldModelZeroPreserving (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ) :=
  fun o => Multiset.count_zero o

/-- The one-argument erasure test: some scope in the table erases the decoded
state.  It names no scope. -/
def scopeFreeRows : String → List Pattern → List (List Pattern)
  | "erasedBySomeScope", [stateHandle] =>
      match lookupHandle controlTable.states stateHandle with
      | some Δ =>
          if (Conservation.erasingScopeHandles
              (ledgerProvider controlTable).toCheckedErasureProvider Δ).isEmpty then []
          else [[stateHandle]]
      | none => []
  | relation, arguments => controlEnv.tuples relation arguments

def scopeFreeEnv : RelationEnv where
  tuples := scopeFreeRows

/-- The test is answered truthfully: a returned row names a state that some
scope in the table erases. -/
theorem scopeFree_sound {stateHandle : Pattern} {row : List Pattern}
    (returned : row ∈ scopeFreeEnv.tuples "erasedBySomeScope" [stateHandle]) :
    ∃ Δ, lookupHandle controlTable.states stateHandle = some Δ ∧
      ∃ scopeHandle S, lookupHandle controlTable.scopes scopeHandle = some S ∧
        ledgerForgetting.forget S Δ = 0 := by
  cases stateDecode : lookupHandle controlTable.states stateHandle with
  | none => simp [scopeFreeEnv, scopeFreeRows, stateDecode] at returned
  | some Δ =>
      refine ⟨Δ, rfl, ?_⟩
      simp only [scopeFreeEnv, scopeFreeRows, stateDecode] at returned
      split at returned
      · simp at returned
      · rename_i nonempty
        obtain ⟨scopeHandle, member⟩ :=
          List.exists_mem_of_ne_nil (Conservation.erasingScopeHandles
            (ledgerProvider controlTable).toCheckedErasureProvider Δ)
            (fun empty => nonempty (by simp [empty]))
        simp only [Conservation.erasingScopeHandles, List.mem_filter] at member
        obtain ⟨_, accepted⟩ := member
        cases scopeDecode :
            lookupHandle (ledgerProvider controlTable).handles.scopes scopeHandle with
        | none => simp [scopeDecode] at accepted
        | some S =>
            simp only [scopeDecode] at accepted
            exact ⟨scopeHandle, S, scopeDecode,
              (ledgerProvider controlTable).erases_sound S Δ accepted⟩

/-- Zero leakage with a premise that names no scope.  It is in no rule list. -/
def scopeFreeZeroLeakage : RewriteRule :=
  { ruleZeroLeakage with
    name := "WM_ScopeFreeZeroLeakage_Control"
    premises := [.relationQuery "erasedBySomeScope" [.fvar "D"]] }

/-- Anti-hallucination with the earlier premises: the revision's handle in the
scope position of `outsideScope`, and a test that names no scope.  It is in no
rule list. -/
def scopeFreeAntiHallucination : RewriteRule :=
  { ruleAntiHallucination with
    name := "WM_ScopeFreeAntiHallucination_Control"
    typeContext := [("D", .base "State"), ("q", .base "Query")]
    premises := [.relationQuery "outsideScope" [.fvar "D", .fvar "q"],
      .relationQuery "erasedBySomeScope" [.fvar "D"]] }

/-- The test accepts the budget term for the scope `{1}` and the revision `{0}`. -/
theorem scopeFree_accepts_wrong_scope :
    applyPremisesWithEnv scopeFreeEnv maximalCalculus scopeFreeZeroLeakage.premises
      [("D", revisionZero), ("S", scopeOne)] ≠ [] := by
  decide +kernel

/-- The state `{0}` has evidence `1` at `0`. -/
theorem evidence_at_zero :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
      ({0} : Multiset ℕ) 0 = 1 := by
  decide +kernel

/-- So `{0}` leaks outside `{1}`: its budget there is not zero. -/
theorem wrong_scope_leaks :
    ¬ OutsideLeakageBudget ledgerForgetting.toForgettingLayer ({1} : Finset ℕ)
      ({0} : Multiset ℕ) 0 := by
  intro budget
  have leak := budget 0 (show (0 : ℕ) ∉ ({1} : Finset ℕ) by decide)
  simp only [AdditiveWorldModel.queryObservationCount, evidence_at_zero] at leak
  exact absurd leak (by simp [ConjugateEvidence.observationCount])

/-- Zero leakage refuses the scope `{1}`, which does not erase `{0}`. -/
theorem zeroLeakage_refuses_wrong_scope :
    applyPremisesWithEnv controlEnv maximalCalculus ruleZeroLeakage.premises
      [("D", revisionZero), ("S", scopeOne)] = [] := by
  decide +kernel

/-- It accepts the scope `{0}`, which erases `{0}`. -/
theorem zeroLeakage_accepts :
    [("D", revisionZero), ("S", scopeZero)] ∈
      applyPremisesWithEnv controlEnv maximalCalculus ruleZeroLeakage.premises
        [("D", revisionZero), ("S", scopeZero)] := by
  decide +kernel

/-- There the zero budget holds, by the conservation pack. -/
theorem control_zeroLeakage_sound :
    OutsideLeakageBudget ledgerForgetting.toForgettingLayer ({0} : Finset ℕ)
      ({0} : Multiset ℕ) 0 :=
  Conservation.zeroLeakage_sound (supportRelationEnv_certifies (ledgerProvider controlTable))
    ledger_zeroPreserving maximalCalculus scopeZero revisionZero (by decide +kernel)
    (by decide +kernel) zeroLeakage_accepts

/-- The shared name decodes as the scope `{1}` and as the state `{0}`. -/
theorem shared_decodes :
    lookupHandle controlTable.scopes sharedName = some {1} ∧
      lookupHandle controlTable.states sharedName = some {0} := by
  decide +kernel

/-- The earlier anti-hallucination premises accept `Extract(sharedName, 0)`. -/
theorem scopeFree_antiHallucination_accepts :
    applyPremisesWithEnv scopeFreeEnv maximalCalculus scopeFreeAntiHallucination.premises
      [("q", queryZero), ("D", sharedName)] ≠ [] := by
  decide +kernel

/-- The maximal calculus has no step from `Extract(sharedName, 0)`. -/
theorem maximal_refuses_shared (target : Pattern) :
    ¬ langReducesUsing controlEnv maximalCalculus (pExtract sharedName queryZero) target := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    show rewriteStepWithPremisesUsing controlEnv maximalCalculus
      (pExtract sharedName queryZero) = [] by decide +kernel]
  exact List.not_mem_nil

/-- With separate names the earlier premises refuse the correct case
`Extract({0}, 1)`: the state handle names no scope. -/
theorem scopeFree_antiHallucination_refuses_correct :
    applyPremisesWithEnv scopeFreeEnv maximalCalculus scopeFreeAntiHallucination.premises
      [("q", queryOne), ("D", revisionZero)] = [] := by
  decide +kernel

/-- Anti-hallucination rewrites `Extract({0}, 1)` to `EvidenceZero`: `{0}` is
erased by `{0}`, which excludes `1`. -/
theorem maximal_antiHallucination :
    langReducesUsing controlEnv maximalCalculus (pExtract revisionZero queryOne)
      pEvidenceZero :=
  wmFullLangReducesUsing_antiHallucination controlEnv wmFullVertexMaximal rfl
    scopeZero revisionZero queryOne (by decide +kernel) (by decide +kernel)

/-- The firing certifies the conclusion: `{0}` has no evidence at `1`. -/
theorem control_antiHallucination_sound :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
      ({0} : Multiset ℕ) 1 = 0 :=
  Conservation.antiHallucination_sound
    (supportRelationEnv_certifies (ledgerProvider controlTable)) ledger_zeroPreserving
    maximalCalculus revisionZero queryOne (by decide +kernel) (by decide +kernel)
    (final := [("S", scopeZero), ("q", queryOne), ("D", revisionZero)]) (by decide +kernel)

/-- At the query `0`, inside the erasing scope, anti-hallucination does not
fire. -/
theorem maximal_refuses_inside (target : Pattern) :
    ¬ langReducesUsing controlEnv maximalCalculus (pExtract revisionZero queryZero) target := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    show rewriteStepWithPremisesUsing controlEnv maximalCalculus
      (pExtract revisionZero queryZero) = [] by decide +kernel]
  exact List.not_mem_nil

/-- Noether conservation rewrites `Extract(Revise({1}, {0}), 1)` to
`Extract({1}, 1)`. -/
theorem maximal_noetherConservation :
    langReducesUsing controlEnv maximalCalculus
      (pExtract (pRevise baseOne revisionZero) queryOne) (pExtract baseOne queryOne) :=
  wmFullLangReducesUsing_noetherConservation controlEnv wmFullVertexMaximal rfl
    scopeZero baseOne revisionZero queryOne (by decide +kernel) (by decide +kernel)

/-- The firing certifies the conclusion on every base. -/
theorem control_noetherConservation_sound (W : Multiset ℕ) :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ) (W + {0}) 1 =
      AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ) W 1 :=
  Conservation.noetherConservation_sound
    (supportRelationEnv_certifies (ledgerProvider controlTable)) ledger_zeroPreserving
    maximalCalculus baseOne revisionZero queryOne (by decide +kernel) (by decide +kernel)
    (final := [("S", scopeZero), ("q", queryOne), ("D", revisionZero), ("W", baseOne)])
    (by decide +kernel) W

/-- At the query `0` only evidence-add fires on `Extract(Revise({1}, {0}), 0)`. -/
theorem maximal_noether_frontier_inside :
    rewriteStepWithPremisesUsing controlEnv maximalCalculus
        (pExtract (pRevise baseOne revisionZero) queryZero) =
      [pCombine (pExtract baseOne queryZero) (pExtract revisionZero queryZero)] := by
  decide +kernel

theorem maximal_noether_refuses_inside :
    ¬ langReducesUsing controlEnv maximalCalculus
      (pExtract (pRevise baseOne revisionZero) queryZero) (pExtract baseOne queryZero) := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    maximal_noether_frontier_inside]
  decide +kernel

/-- Rightly: the revision changes the evidence at `0` on the base `{1}`. -/
theorem noether_fails_inside :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
        (({1} : Multiset ℕ) + {0}) 0 ≠
      AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
        ({1} : Multiset ℕ) 0 := by
  decide +kernel

/-! ### Outside-scope invariance against its premise-free form

* The premise-free rule `Extract(Forget(S, W), q) ↦ Extract(W, q)` rewrites
  `Extract(Forget({0}, {0, 1}), 0)` to `Extract({0, 1}, 0)`, although `0` lies
  inside the scope: after forgetting, the evidence at `0` is `0`, and the base
  has `1` (`premiseFreeForgetOutside_rewrites_inside`,
  `premiseFreeForgetOutside_unsound`).
* The maximal calculus has no step from that term
  (`maximal_refuses_forget_inside`).
* At the query `1`, outside `{0}`, outside-scope invariance is the only step,
  and its conclusion holds on every base (`maximal_forgetOutside_frontier`,
  `maximal_forgetOutside`, `control_forgetOutside_sound`). -/

/-- Outside-scope invariance without its premise.  It is in no rule list. -/
def premiseFreeForgetOutside : RewriteRule :=
  { ruleForgetOutside with
    name := "WM_PremiseFreeForgetOutside_Control"
    premises := [] }

/-- The maximal calculus with the premise-free rule added. -/
def withPremiseFreeForgetOutside : LanguageDef :=
  { maximalCalculus with rewrites := premiseFreeForgetOutside :: maximalCalculus.rewrites }

theorem withPremiseFreeForgetOutside_noncontextual :
    ∀ rule ∈ withPremiseFreeForgetOutside.rewrites, NoncontextualPremises rule.premises := by
  intro rule member
  rcases List.mem_cons.mp member with rfl | member
  · exact .nil
  · exact maximal_noncontextual rule member

/-- `Extract(Forget({0}, {0, 1}), 0)`: a query inside the forgotten scope. -/
def insideForgetRedex : Pattern := pExtract (pForget scopeZero baseZeroOne) queryZero

/-- With the premise-free rule, the inside query has exactly one reduct: the
base's evidence. -/
theorem premiseFreeForgetOutside_frontier :
    rewriteStepWithPremisesUsing controlEnv withPremiseFreeForgetOutside insideForgetRedex =
      [pExtract baseZeroOne queryZero] := by
  decide +kernel

theorem premiseFreeForgetOutside_rewrites_inside :
    langReducesUsing controlEnv withPremiseFreeForgetOutside insideForgetRedex
      (pExtract baseZeroOne queryZero) := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ withPremiseFreeForgetOutside_noncontextual,
    premiseFreeForgetOutside_frontier]
  exact List.mem_singleton_self _

/-- Forgetting `{0}` from `{0, 1}` leaves no evidence at `0`, and the base has
evidence `1` there: the premise-free reduct has the wrong value. -/
theorem premiseFreeForgetOutside_unsound :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
        (ledgerForgetting.forget {0} {0, 1}) 0 = 0 ∧
      AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
        ({0, 1} : Multiset ℕ) 0 = 1 := by
  decide +kernel

/-- The maximal calculus has no step from the inside query. -/
theorem maximal_refuses_forget_inside (target : Pattern) :
    ¬ langReducesUsing controlEnv maximalCalculus insideForgetRedex target := by
  rw [← mem_rootFrontier_iff_langReducesUsing _ _ maximal_noncontextual,
    show rewriteStepWithPremisesUsing controlEnv maximalCalculus insideForgetRedex = [] by
      decide +kernel]
  exact List.not_mem_nil

/-- At the query `1`, outside `{0}`, outside-scope invariance is the only step. -/
theorem maximal_forgetOutside_frontier :
    rewriteStepWithPremisesUsing controlEnv maximalCalculus
        (pExtract (pForget scopeZero baseZeroOne) queryOne) =
      [pExtract baseZeroOne queryOne] := by
  decide +kernel

theorem maximal_forgetOutside :
    langReducesUsing controlEnv maximalCalculus
      (pExtract (pForget scopeZero baseZeroOne) queryOne) (pExtract baseZeroOne queryOne) :=
  wmFullLangReducesUsing_forgetOutside controlEnv wmFullVertexMaximal (Or.inr rfl)
    scopeZero baseZeroOne queryOne (by decide +kernel)

/-- The firing certifies the conclusion on every base. -/
theorem control_forgetOutside_sound (W : Multiset ℕ) :
    AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ)
        (ledgerForgetting.forget {0} W) 1 =
      AdditiveWorldModel.extract (State := Multiset ℕ) (Query := ℕ) (Ev := ℕ) W 1 :=
  Conservation.forgetOutside_sound
    (supportRelationEnv_certifies (ledgerProvider controlTable)) maximalCalculus
    scopeZero baseZeroOne queryOne (by decide +kernel) (by decide +kernel)
    (final := [("q", queryOne), ("W", baseZeroOne), ("S", scopeZero)]) (by decide +kernel) W

end Control

end SupportTracked

#print axioms SupportTracked.supported_of_row
#print axioms SupportTracked.clean_of_row
#print axioms SupportTracked.forgetAbsorbSupported_sound
#print axioms SupportTracked.forgetClean_sound
#print axioms SupportTracked.forgetAbsorbSupported_forgetClean_sound
#print axioms SupportTracked.Control.maximal_noncontextual
#print axioms SupportTracked.Control.unsupported_decodes
#print axioms SupportTracked.Control.unsupported_rows_absent
#print axioms SupportTracked.Control.premiseFreeInverse_frontier
#print axioms SupportTracked.Control.maximal_frontier
#print axioms SupportTracked.Control.premiseFreeInverse_rewrites_unsupported
#print axioms SupportTracked.Control.maximal_refuses_unsupported
#print axioms SupportTracked.Control.premiseFreeInverse_unsound
#print axioms SupportTracked.Control.maximal_absorbs_supported
#print axioms SupportTracked.Control.maximal_clean_base
#print axioms SupportTracked.Control.control_absorption_sound
#print axioms SupportTracked.Control.exact_on_clean_base
#print axioms SupportTracked.Control.maximal_absorbs_on_unclean_base
#print axioms SupportTracked.Control.maximal_stops_on_unclean_base
#print axioms SupportTracked.Control.inverse_fails_on_unclean_base
#print axioms Conservation.erased_of_row
#print axioms Conservation.outside_of_row
#print axioms Conservation.erasureRelationEnv_certifies
#print axioms Conservation.erasedOutside_of_antiHallucination
#print axioms Conservation.erasedOutside_of_noetherConservation
#print axioms Conservation.erased_of_zeroLeakage
#print axioms Conservation.antiHallucination_sound
#print axioms Conservation.noetherConservation_sound
#print axioms Conservation.zeroLeakage_sound
#print axioms SupportTracked.supportRelationEnv_certifies
#print axioms SupportTracked.Control.ledger_zeroPreserving
#print axioms SupportTracked.Control.scopeFree_sound
#print axioms SupportTracked.Control.scopeFree_accepts_wrong_scope
#print axioms SupportTracked.Control.evidence_at_zero
#print axioms SupportTracked.Control.wrong_scope_leaks
#print axioms SupportTracked.Control.zeroLeakage_refuses_wrong_scope
#print axioms SupportTracked.Control.zeroLeakage_accepts
#print axioms SupportTracked.Control.control_zeroLeakage_sound
#print axioms SupportTracked.Control.shared_decodes
#print axioms SupportTracked.Control.scopeFree_antiHallucination_accepts
#print axioms SupportTracked.Control.maximal_refuses_shared
#print axioms SupportTracked.Control.scopeFree_antiHallucination_refuses_correct
#print axioms SupportTracked.Control.maximal_antiHallucination
#print axioms SupportTracked.Control.control_antiHallucination_sound
#print axioms SupportTracked.Control.maximal_refuses_inside
#print axioms SupportTracked.Control.maximal_noetherConservation
#print axioms SupportTracked.Control.control_noetherConservation_sound
#print axioms SupportTracked.Control.maximal_noether_frontier_inside
#print axioms SupportTracked.Control.maximal_noether_refuses_inside
#print axioms SupportTracked.Control.noether_fails_inside
#print axioms Conservation.outside_of_forgetOutside
#print axioms Conservation.forgetOutside_sound
#print axioms SupportTracked.Control.withPremiseFreeForgetOutside_noncontextual
#print axioms SupportTracked.Control.premiseFreeForgetOutside_frontier
#print axioms SupportTracked.Control.premiseFreeForgetOutside_rewrites_inside
#print axioms SupportTracked.Control.premiseFreeForgetOutside_unsound
#print axioms SupportTracked.Control.maximal_refuses_forget_inside
#print axioms SupportTracked.Control.maximal_forgetOutside_frontier
#print axioms SupportTracked.Control.maximal_forgetOutside
#print axioms SupportTracked.Control.control_forgetOutside_sound

end Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
