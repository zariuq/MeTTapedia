import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation
import Mettapedia.GSLT.LanguageDef.TwoPhaseFrameMachinePhysicalRefinement

/-!
# Repetition-admitted caching of immutable generated declarations

A generated proof plan may expose an immutable finite environment of rule
declarations.  Looking up and elaborating the same declaration repeatedly is
then redundant, but retaining every one-off declaration can cost more than it
saves.  This module specifies the generic admission policy used by the C
machine:

* the first occurrence is looked up normally and only records that the key was
  seen;
* the second occurrence is looked up normally and promotes the result;
* later occurrences use the promoted result without consulting the source.

The cache is scoped to one execution.  Thus validity needs no invalidation
protocol: a cached entry cannot outlive the immutable environment that
licensed it.  Metamath assertion frames, Horn-clause schemas, and typed rewrite
rules are independent instances of this same property.
-/

namespace Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation

variable {Key Value : Type} [DecidableEq Key]

/-- Immutable source environment supplied by a generated plan. -/
structure Environment (Key Value : Type) where
  lookup : Key -> Option Value

/-- Call-local physical state.  `resolved` contains only promoted entries. -/
structure State (Key Value : Type) where
  seen : List Key := []
  resolved : List (Key × Value) := []
  deriving Repr

structure Stats where
  sourceLookups : Nat := 0
  cacheHits : Nat := 0
  promotions : Nat := 0
  deriving DecidableEq, Repr

def findResolved? (key : Key) : List (Key × Value) -> Option Value
  | [] => none
  | (candidate, value) :: tail =>
      if candidate = key then some value else findResolved? key tail

/-- Every promoted value is exactly the immutable source value for its key. -/
def State.Valid (environment : Environment Key Value)
    (state : State Key Value) : Prop :=
  forall key value, (key, value) ∈ state.resolved ->
    environment.lookup key = some value

def initial : State Key Value := {}

omit [DecidableEq Key] in
theorem initial_valid (environment : Environment Key Value) :
    (initial : State Key Value).Valid environment := by
  intro key value member
  simp [initial] at member

theorem findResolved?_mem {entries : List (Key × Value)}
    {key : Key} {value : Value}
    (found : findResolved? key entries = some value) :
    (key, value) ∈ entries := by
  induction entries with
  | nil => simp [findResolved?] at found
  | cons head tail inductionHypothesis =>
      rcases head with ⟨candidate, candidateValue⟩
      simp only [findResolved?] at found
      split at found
      · simp_all
      · exact List.mem_cons_of_mem _ (inductionHypothesis found)

theorem findResolved?_sound {state : State Key Value}
    {key : Key} {value : Value}
    (valid : state.Valid environment)
    (found : findResolved? key state.resolved = some value) :
    environment.lookup key = some value :=
  valid key value (findResolved?_mem found)

/-- One admitted lookup.  The Boolean is true exactly on a cache hit. -/
def step (environment : Environment Key Value)
    (state : State Key Value) (key : Key) :
    Option (Value × State Key Value × Bool) :=
  match findResolved? key state.resolved with
  | some value => some (value, state, true)
  | none => do
      let value <- environment.lookup key
      if key ∈ state.seen then
        some (value,
          { state with resolved := (key, value) :: state.resolved }, false)
      else
        some (value, { state with seen := key :: state.seen }, false)

theorem step_value {environment : Environment Key Value}
    {state next : State Key Value} {key : Key} {value : Value} {hit : Bool}
    (valid : state.Valid environment)
    (executed : step environment state key = some (value, next, hit)) :
    environment.lookup key = some value := by
  unfold step at executed
  cases found : findResolved? key state.resolved with
  | some cached =>
      simp [found] at executed
      rcases executed with ⟨rfl, rfl, rfl⟩
      exact findResolved?_sound valid found
  | none =>
      simp [found] at executed
      cases source : environment.lookup key with
      | none => simp [source] at executed
      | some sourceValue =>
          simp [source] at executed
          split at executed <;> simp_all

theorem step_preserves_valid {environment : Environment Key Value}
    {state next : State Key Value} {key : Key} {value : Value} {hit : Bool}
    (valid : state.Valid environment)
    (executed : step environment state key = some (value, next, hit)) :
    next.Valid environment := by
  unfold step at executed
  cases found : findResolved? key state.resolved with
  | some cached =>
      simp [found] at executed
      rcases executed with ⟨rfl, rfl, rfl⟩
      exact valid
  | none =>
      simp [found] at executed
      cases source : environment.lookup key with
      | none => simp [source] at executed
      | some sourceValue =>
          simp [source] at executed
          split at executed
          · rcases executed with ⟨rfl, rfl, rfl⟩
            intro otherKey otherValue member
            simp only [List.mem_cons, Prod.mk.injEq] at member
            rcases member with newEntry | oldEntry
            · rcases newEntry with ⟨rfl, rfl⟩
              exact source
            · exact valid otherKey otherValue oldEntry
          · rcases executed with ⟨rfl, rfl, rfl⟩
            exact valid

def executeFresh (environment : Environment Key Value) :
    List Key -> Option (List Value)
  | [] => some []
  | key :: tail => do
      let value <- environment.lookup key
      let values <- executeFresh environment tail
      some (value :: values)

def run (environment : Environment Key Value) :
    State Key Value -> Stats -> List Key ->
      Option (List Value × State Key Value × Stats)
  | state, stats, [] => some ([], state, stats)
  | state, stats, key :: tail => do
      let (value, next, hit) <- step environment state key
      let nextStats :=
        if hit then
          { stats with cacheHits := stats.cacheHits + 1 }
        else
          { stats with
              sourceLookups := stats.sourceLookups + 1
              promotions := stats.promotions +
                (if key ∈ state.seen then 1 else 0) }
      let (values, finalState, finalStats) <-
        run environment next nextStats tail
      some (value :: values, finalState, finalStats)

theorem run_refines {environment : Environment Key Value}
    {state finalState : State Key Value} {stats finalStats : Stats}
    {keys : List Key} {values : List Value}
    (valid : state.Valid environment)
    (executed : run environment state stats keys =
      some (values, finalState, finalStats)) :
    executeFresh environment keys = some values := by
  induction keys generalizing state stats values finalState finalStats with
  | nil =>
      simp [run] at executed
      rcases executed with ⟨rfl, rfl, rfl⟩
      rfl
  | cons key tail inductionHypothesis =>
      cases stepped : step environment state key with
      | none => simp [run, stepped] at executed
      | some result =>
          rcases result with ⟨value, next, hit⟩
          cases hit <;> simp [run, stepped] at executed
          all_goals
            rcases recursive : run environment next _ tail with
              _ | ⟨⟨tailValues, resultingState, resultingStats⟩⟩
            · rw [recursive] at executed
              contradiction
            · rw [recursive] at executed
              simp only [Option.bind_some, Option.some.injEq,
                Prod.mk.injEq] at executed
              rcases executed with ⟨rfl, rfl, rfl⟩
              simp only [executeFresh, Option.bind_eq_bind]
              rw [step_value valid stepped]
              rw [inductionHypothesis
                (step_preserves_valid valid stepped) recursive]
              rfl

/-- A live immutable-source certificate is an equality of lookup observations,
not merely a carrier tag. -/
def SameLookup (before after : Environment Key Value) : Prop :=
  forall key, before.lookup key = after.lookup key

omit [DecidableEq Key] in
theorem executeFresh_eq_of_sameLookup
    {before after : Environment Key Value}
    (stable : SameLookup before after) (keys : List Key) :
    executeFresh before keys = executeFresh after keys := by
  induction keys with
  | nil => rfl
  | cons key tail inductionHypothesis =>
      simp only [executeFresh, Option.bind_eq_bind]
      rw [stable key, inductionHypothesis]

/-- A cache run against one certified snapshot also refines any later source
observation whose lookup interface is preserved by the physical store. -/
theorem run_refines_preserved_source
    {before after : Environment Key Value}
    {state finalState : State Key Value} {stats finalStats : Stats}
    {keys : List Key} {values : List Value}
    (valid : state.Valid before)
    (stable : SameLookup before after)
    (executed : run before state stats keys =
      some (values, finalState, finalStats)) :
    executeFresh after keys = some values := by
  rw [← executeFresh_eq_of_sameLookup stable]
  exact run_refines valid executed

/-! ## Physical append-only snapshot refinement

The C store exposes a finite ordered inventory of declaration tables.  A live
snapshot records the store identity, table-presence mask, and exact row length
of every table in that inventory.  The store contract says that rows are only
appended during a proof call.  Therefore equal snapshots imply equal table
contents: an append-only prefix with the same length is the same list.

This is deliberately stronger than calling an append-only table immutable.
Appending a declaration changes lookup observations and must invalidate a
cache that was promoted under the earlier snapshot.
-/

namespace PhysicalSnapshot

structure Store (Row : Type) where
  identity : Nat
  present : List Bool
  tables : List (List Row)
  deriving DecidableEq, Repr

structure Snapshot where
  identity : Nat
  present : List Bool
  rowLengths : List Nat
  deriving DecidableEq, Repr

def capture (store : Store Row) : Snapshot :=
  { identity := store.identity
    present := store.present
    rowLengths := store.tables.map List.length }

/-- The physical store may only append rows to tables while a proof call is
live.  The table inventory itself therefore has the same shape. -/
def AppendOnly (before after : Store Row) : Prop :=
  List.Forall₂ (fun earlier later => earlier <+: later)
    before.tables after.tables

theorem tables_eq_of_appendOnly_of_lengths_eq
    {before after : List (List Row)}
    (appendOnly : List.Forall₂ (fun earlier later => earlier <+: later)
      before after)
    (lengthsEqual : before.map List.length = after.map List.length) :
    before = after := by
  induction appendOnly with
  | nil => rfl
  | cons headPrefix tailPrefix inductionHypothesis =>
      simp only [List.map_cons, List.cons.injEq] at lengthsEqual
      rcases lengthsEqual with ⟨headLength, tailLengths⟩
      have headEqual := headPrefix.eq_of_length headLength
      have tailEqual := inductionHypothesis tailLengths
      simp [headEqual, tailEqual]

theorem capture_eq_implies_store_observations_eq
    {before after : Store Row}
    (appendOnly : AppendOnly before after)
    (snapshotEqual : capture before = capture after) :
    before.identity = after.identity ∧
      before.present = after.present ∧
      before.tables = after.tables := by
  have identityEqual := congrArg Snapshot.identity snapshotEqual
  have presenceEqual := congrArg Snapshot.present snapshotEqual
  have lengthsEqual := congrArg Snapshot.rowLengths snapshotEqual
  refine ⟨identityEqual, presenceEqual, ?_⟩
  exact tables_eq_of_appendOnly_of_lengths_eq appendOnly lengthsEqual

/-- A declaration resolver is applied only to the captured table inventory.
Consequently the physical snapshot theorem supplies the semantic `SameLookup`
premise required by cache refinement without postulating immutability. -/
def environmentOf
    (resolve : List Bool -> List (List Row) -> Key -> Option Value)
    (store : Store Row) : Environment Key Value where
  lookup := resolve store.present store.tables

omit [DecidableEq Key] in
theorem sameLookup_of_appendOnly_snapshot
    (resolve : List Bool -> List (List Row) -> Key -> Option Value)
    {before after : Store Row}
    (appendOnly : AppendOnly before after)
    (snapshotEqual : capture before = capture after) :
    SameLookup (environmentOf resolve before) (environmentOf resolve after) := by
  obtain ⟨_identityEqual, presenceEqual, tablesEqual⟩ :=
    capture_eq_implies_store_observations_eq appendOnly snapshotEqual
  intro key
  simp only [environmentOf]
  rw [presenceEqual, tablesEqual]

theorem run_refines_exact_physical_snapshot
    (resolve : List Bool -> List (List Row) -> Key -> Option Value)
    {before after : Store Row}
    {state finalState : State Key Value} {stats finalStats : Stats}
    {keys : List Key} {values : List Value}
    (appendOnly : AppendOnly before after)
    (snapshotEqual : capture before = capture after)
    (valid : state.Valid (environmentOf resolve before))
    (executed : run (environmentOf resolve before) state stats keys =
      some (values, finalState, finalStats)) :
    executeFresh (environmentOf resolve after) keys = some values := by
  exact run_refines_preserved_source valid
    (sameLookup_of_appendOnly_snapshot resolve appendOnly snapshotEqual)
    executed

private def sampleBefore : Store Nat :=
  { identity := 17
    present := [true, false]
    tables := [[10, 20], []] }

private def sampleSame : Store Nat := sampleBefore

private def sampleAppended : Store Nat :=
  { sampleBefore with tables := [[10, 20, 30], []] }

private def samplePresenceChanged : Store Nat :=
  { sampleBefore with present := [true, true] }

example : capture sampleBefore = capture sampleSame := by
  decide

example : capture sampleBefore ≠ capture sampleAppended := by
  decide

example : capture sampleBefore ≠ capture samplePresenceChanged := by
  decide

end PhysicalSnapshot

theorem run_accounting {environment : Environment Key Value}
    {state finalState : State Key Value} {stats finalStats : Stats}
    {keys : List Key} {values : List Value}
    (executed : run environment state stats keys =
      some (values, finalState, finalStats)) :
    finalStats.sourceLookups + finalStats.cacheHits =
      stats.sourceLookups + stats.cacheHits + keys.length := by
  induction keys generalizing state stats values finalState finalStats with
  | nil =>
      simp [run] at executed
      rcases executed with ⟨rfl, rfl, rfl⟩
      simp
  | cons key tail inductionHypothesis =>
      cases stepped : step environment state key with
      | none => simp [run, stepped] at executed
      | some result =>
          rcases result with ⟨value, next, hit⟩
          cases hit <;> simp [run, stepped] at executed
          all_goals
            rcases recursive : run environment next _ tail with
              _ | ⟨⟨tailValues, resultingState, resultingStats⟩⟩
            · rw [recursive] at executed
              contradiction
            · rw [recursive] at executed
              simp only [Option.bind_some, Option.some.injEq,
                Prod.mk.injEq] at executed
              rcases executed with ⟨rfl, rfl, rfl⟩
              have accounted := inductionHypothesis recursive
              simp_all
              omega

/-! ## Generated-plan admission -/

namespace GeneratedPlan

open ReusableSlotBufferCompilation
open TwoPhaseFrameMachinePhysicalRefinement

structure AdmittedRepetitionPlan where
  operation : String
  actionIndex : UInt32
  machine : String
  region : String
  promoteOnOccurrence : Nat
  callLocal : Bool
  requiresImmutableSnapshot : Bool
  deriving DecidableEq, Repr

/-- Serialized cache-policy record emitted by the generic storage-plan
compiler.  The strings form a closed, vocabulary-neutral ABI. -/
structure GeneratedRepetitionCacheRecord where
  operation : String
  actionIndex : UInt32
  machine : String
  keyCarrier : String
  valueCarrier : String
  admissionPolicy : String
  snapshotPolicy : String
  region : String
  deriving DecidableEq, Repr

/-- Independently recognize the closed cache-policy ABI. -/
def admitGeneratedRepetitionCacheRecord?
    (record : GeneratedRepetitionCacheRecord)
    (operation : String) (actionIndex : UInt32)
    (machine region : String) : Option Unit :=
  if record.operation == operation &&
      record.actionIndex == actionIndex &&
      record.machine == machine &&
      record.keyCarrier == "u32-identity-key-v1" &&
      record.valueCarrier == "owned-plan-value-v1" &&
      record.admissionPolicy == "second-occurrence-admission-v1" &&
      record.snapshotPolicy == "immutable-prefix-snapshot-v1" &&
      record.region == region &&
      region == "proof-call-region-v1" then
    some ()
  else none

/-- Independently decode the call, workspace, and frame records.  Static
admission requires all three identities to agree and the physical workspace to
carry the generic repetition state.  It deliberately records that a live
immutable-prefix snapshot is still required before physical promotion. -/
def admitGeneratedRepetitionPlan?
    (callFields workspaceFields : List CallPlanField)
    (frameRecord : GeneratedFramePlanRecord)
    (cacheRecord : GeneratedRepetitionCacheRecord)
    (operation : String) (actionIndex : UInt32)
    (machine workspaceCarrier templateCarrier region : String) :
    Option AdmittedRepetitionPlan := do
  let _ ← admitGeneratedCallPlan? callFields workspaceFields operation
    actionIndex.toNat machine workspaceCarrier region
  let workspace ← decodeGeneratedWorkspacePlan workspaceFields
  let roles ← workspaceCarrierRoles workspace.carrier
  let frame ← admitGeneratedFramePlan? frameRecord
    { operation := operation
      actionIndex := actionIndex
      machine := machine
      templateCarrier := templateCarrier
      region := region }
  let _ ← admitGeneratedRepetitionCacheRecord? cacheRecord
    operation actionIndex machine region
  if workspace.operation == frame.operation &&
      workspace.actionIndex == frame.actionIndex.toNat &&
      workspace.machine == frame.machine &&
      workspace.region == frame.region &&
      roles.contains .declarationSeenIndex &&
      roles.contains .declarationPromotedIndex &&
      roles.contains .promotedDeclarations then
    some
      { operation := operation
        actionIndex := actionIndex
        machine := machine
        region := region
        promoteOnOccurrence := 2
        callLocal := true
        requiresImmutableSnapshot := true }
  else none

theorem admitGeneratedRepetitionPlan?_licenses
    (callFields workspaceFields : List CallPlanField)
    (frameRecord : GeneratedFramePlanRecord)
    (cacheRecord : GeneratedRepetitionCacheRecord)
    (operation : String) (actionIndex : UInt32)
    (machine workspaceCarrier templateCarrier region : String)
    (plan : AdmittedRepetitionPlan)
    (accepted : admitGeneratedRepetitionPlan? callFields workspaceFields
      frameRecord cacheRecord operation actionIndex machine workspaceCarrier
      templateCarrier region = some plan) :
    plan.promoteOnOccurrence = 2 ∧ plan.callLocal = true ∧
      plan.requiresImmutableSnapshot = true := by
  rw [admitGeneratedRepetitionPlan?] at accepted
  obtain ⟨reuse, _reuseDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨workspace, _workspaceDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨roles, _rolesDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨frame, _frameDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  obtain ⟨policy, _policyDecoded, accepted⟩ :=
    Option.bind_eq_some_iff.mp accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst plan
    simp
  · simp at accepted

private def callFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha", .symbol "ProofOwner",
   .symbol "Provable", .symbol "proof-call-region-v1",
   .symbol "flat-symbol-id-vector-v1",
   .symbol "proof-verdict-only-v1"]

private def workspaceFields : List CallPlanField :=
  [.symbol "check-article-v7", .natural 14,
   .symbol "stack-machine-alpha",
   .symbol "stack-proof-call-workspace-v1",
   .symbol "proof-call-region-v1",
   .symbol "proof-verdict-only-v1"]

private def frameRecord : GeneratedFramePlanRecord :=
  { operation := "check-article-v7"
    actionIndex := 14
    machine := "stack-machine-alpha"
    carrier := genericFrameCarrier
    templateCarrier := "literal-hole-run-program-v1"
    literalHeadPolicy := genericLiteralHeadPolicy
    slotCarrier := genericSlotCarrier
    binderValidation := genericBinderValidation
    stackDiscipline := genericStackDiscipline
    region := "proof-call-region-v1" }

private def cacheRecord : GeneratedRepetitionCacheRecord :=
  { operation := "check-article-v7"
    actionIndex := 14
    machine := "stack-machine-alpha"
    keyCarrier := "u32-identity-key-v1"
    valueCarrier := "owned-plan-value-v1"
    admissionPolicy := "second-occurrence-admission-v1"
    snapshotPolicy := "immutable-prefix-snapshot-v1"
    region := "proof-call-region-v1" }

example : (admitGeneratedRepetitionPlan? callFields workspaceFields
    frameRecord cacheRecord "check-article-v7" 14 "stack-machine-alpha"
    "stack-proof-call-workspace-v1" "literal-hole-run-program-v1"
    "proof-call-region-v1").isSome = true := by
  decide

example : (admitGeneratedRepetitionPlan? callFields workspaceFields
    { frameRecord with region := "state-run-region-v1" } cacheRecord
    "check-article-v7" 14 "stack-machine-alpha"
    "stack-proof-call-workspace-v1" "literal-hole-run-program-v1"
    "proof-call-region-v1").isSome = false := by
  decide

example : (admitGeneratedRepetitionPlan? callFields workspaceFields
    frameRecord cacheRecord "check-article-v7" 14 "stack-machine-alpha"
    "action-call-workspace-v1" "literal-hole-run-program-v1"
    "proof-call-region-v1").isSome = false := by
  decide

example : (admitGeneratedRepetitionPlan? callFields workspaceFields
    frameRecord
    { cacheRecord with admissionPolicy := "retain-first-occurrence-v1" }
    "check-article-v7" 14 "stack-machine-alpha"
    "stack-proof-call-workspace-v1" "literal-hole-run-program-v1"
    "proof-call-region-v1").isSome = false := by
  decide

example : (admitGeneratedRepetitionPlan? callFields workspaceFields
    frameRecord
    { cacheRecord with snapshotPolicy := "assumed-immutable-v1" }
    "check-article-v7" 14 "stack-machine-alpha"
    "stack-proof-call-workspace-v1" "literal-hole-run-program-v1"
    "proof-call-region-v1").isSome = false := by
  decide

end GeneratedPlan

/-! ## Computed positive and negative witnesses -/

def sampleEnvironment : Environment Nat Nat where
  lookup
    | 7 => some 70
    | _ => none

example : run sampleEnvironment initial {} [7, 7, 7] =
    some ([70, 70, 70],
      { seen := [7], resolved := [(7, 70)] },
      { sourceLookups := 2, cacheHits := 1, promotions := 1 }) := by
  rfl

example : run sampleEnvironment initial {} [7] =
    some ([70], { seen := [7], resolved := [] },
      { sourceLookups := 1, cacheHits := 0, promotions := 0 }) := by
  rfl

example : run sampleEnvironment initial {} [8] = none := by
  rfl

#print axioms PhysicalSnapshot.run_refines_exact_physical_snapshot

end Mettapedia.GSLT.LanguageDef.RepeatedImmutableLookupCacheCompilation
