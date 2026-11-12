import Mettapedia.Data.List.FiniteLookup
import Mettapedia.Machines.OperatorChoice.ObserverContracts
import Mettapedia.Util.LinearHash

/-!
# Head recognition by table-scoped symbol identities

A symbol table assigns positive IDs to distinct immutable spellings. Compiled
family positions replace spelling comparisons with ID comparisons. A cache
belongs to an address/incarnation pair; ordinary symbol insertion preserves
old positions, while recreation changes the incarnation. Missing compilation
falls back to the spelling-based observation, not an unsupported-form error.

This is recognition, not evaluation or permission to execute a native worker.
Program/profile admission remains live. Addresses and incarnations are model
identities; pointer lifetime, finite counter exhaustion and C correspondence
are separate obligations.

Raw numeric queries explicitly address the current table. Retained references
carry their owner and are refused after that owner changes; they are not
silently reinterpreted as the same number in a new table.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SymbolTableHeadCache

variable {Name Query : Type} [DecidableEq Name] {k : Nat}

structure Table (Name : Type) where
  owner : Nat × Nat
  words : List Name
  distinct : words.Nodup

structure Cache (k : Nat) where
  owner : Nat × Nat
  ids : Fin k → Nat

def decode (table : Table Name) (head : Nat) : Option Name :=
  if head = 0 then none else table.words[head - 1]?

def compile (table : Table Name) (names : Fin k → Name) : Option (Cache k) :=
  (List.findPositions table.words names).map fun positions =>
    ⟨table.owner, fun index => positions index + 1⟩

def Good (table : Table Name) (names : Fin k → Name) (cache : Cache k) : Prop :=
  cache.owner = table.owner ∧ ∀ index, decode table (cache.ids index) = some (names index)

def source (table : Table Name) (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (head : Nat) (question : Query) : Bool :=
  (List.finRange k).any fun index =>
    decide (decode table head = some (names index)) && permits index question

def recognized (cache : Cache k) (permits : Fin k → Query → Bool)
    (head : Nat) (question : Query) : Bool :=
  (List.finRange k).any fun index => decide (head = cache.ids index) && permits index question

def query (table : Table Name) (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (cache : Option (Cache k)) (head : Nat) (question : Query) : Bool × Option (Cache k) :=
  match cache with
  | some known =>
      if known.owner = table.owner then (recognized known permits head question, cache)
      else (source table names permits head question, compile table names)
  | none => (source table names permits head question, compile table names)

theorem compile_good (table : Table Name) (names : Fin k → Name) (cache : Cache k)
    (compiled : compile table names = some cache) : Good table names cache := by
  obtain ⟨positions, found, rfl⟩ := Option.map_eq_some_iff.mp compiled
  refine ⟨rfl, fun index => ?_⟩
  simpa [decode] using List.findPositions_getElem? found index

theorem compile_complete (table : Table Name) (names : Fin k → Name) :
    (compile table names).isSome = true ↔ ∀ index, names index ∈ table.words := by
  simpa [compile] using List.findPositions_isSome_iff table.words names

omit [DecidableEq Name] in
theorem decode_identity (table : Table Name) (first second : Nat) (name : Name)
    (left : decode table first = some name) (right : decode table second = some name) : first = second := by
  have firstPositive : first ≠ 0 := by intro same; simp [decode, same] at left
  have secondPositive : second ≠ 0 := by intro same; simp [decode, same] at right
  have a : table.words[first - 1]? = some name := by simpa [decode, firstPositive] using left
  have b : table.words[second - 1]? = some name := by simpa [decode, secondPositive] using right
  have bound := (List.getElem?_eq_some_iff.mp a).1
  have indices := (List.getElem?_inj bound table.distinct).mp (a.trans b.symm)
  omega

theorem recognized_exact (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Cache k) (good : Good table names cache)
    (head : Nat) (question : Query) :
    recognized cache permits head question = source table names permits head question := by
  have same : ∀ index, head = cache.ids index ↔ decode table head = some (names index) := by
    intro index
    constructor
    · intro equal
      simpa [equal] using good.2 index
    · intro found
      exact decode_identity table head (cache.ids index) (names index) found (good.2 index)
  simp only [recognized, source, same]

theorem query_exact (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Option (Cache k))
    (valid : ∀ known, cache = some known → known.owner = table.owner → Good table names known)
    (head : Nat) (question : Query) :
    (query table names permits cache head question).1 = source table names permits head question := by
  cases cached : cache with
  | none => rfl
  | some known =>
      by_cases owner : known.owner = table.owner
      · simpa [query, owner] using recognized_exact table names permits known
          (valid known cached owner) head question
      · simp [query, owner]

theorem query_good (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Option (Cache k))
    (valid : ∀ known, cache = some known → known.owner = table.owner → Good table names known)
    (head : Nat) (question : Query) (next : Cache k)
    (retained : (query table names permits cache head question).2 = some next) : Good table names next := by
  cases cached : cache with
  | none =>
      apply compile_good table names next
      simpa [query, cached] using retained
  | some known =>
      by_cases owner : known.owner = table.owner
      · have equal : known = next := by simpa [query, cached, owner] using retained
        subst next
        exact valid known cached owner
      · apply compile_good table names next
        simpa [query, cached, owner] using retained

/-- The hit branch uses only the retained IDs and query policy. -/
theorem warm_query (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Cache k) (owner : cache.owner = table.owner)
    (head : Nat) (question : Query) :
    query table names permits (some cache) head question =
      (recognized cache permits head question, some cache) := by simp [query, owner]

def insertName (table : Table Name) (name : Name) : Table Name :=
  if present : name ∈ table.words then table
  else ⟨table.owner, table.words ++ [name], by
    apply List.nodup_append.mpr
    refine ⟨table.distinct, by simp, ?_⟩
    intro old member new singleton equal
    have same : new = name := List.mem_singleton.mp singleton
    exact present ((equal.trans same) ▸ member)⟩

theorem insertion_preserves_owner (table : Table Name) (name : Name) :
    (insertName table name).owner = table.owner := by
  unfold insertName
  split_ifs <;> rfl

theorem insertion_extends_words (table : Table Name) (name : Name) :
    table.words <+: (insertName table name).words := by
  unfold insertName
  split_ifs
  · exact List.prefix_rfl
  · exact ⟨[name], rfl⟩

omit [DecidableEq Name] in
theorem decode_prefix (old fresh : Table Name) (growth : old.words <+: fresh.words)
    (head : Nat) (name : Name) (found : decode old head = some name) :
    decode fresh head = some name := by
  have positive : head ≠ 0 := by intro zero; simp [decode, zero] at found
  have previous : old.words[head - 1]? = some name := by simpa [decode, positive] using found
  have bound := (List.getElem?_eq_some_iff.mp previous).1
  obtain ⟨extra, words⟩ := growth
  simp only [decode, if_neg positive, ← words, List.getElem?_append_left bound]
  exact previous

theorem insertion_preserves_cache (table : Table Name) (names : Fin k → Name)
    (cache : Cache k) (good : Good table names cache) (name : Name) :
    Good (insertName table name) names cache := by
  refine ⟨good.1.trans (insertion_preserves_owner table name).symm, fun index => ?_⟩
  exact decode_prefix table _ (insertion_extends_words table name) _ _ (good.2 index)

def recreate (table : Table Name) (address : Nat) (words : List Name) : Table Name :=
  ⟨(address, table.owner.2 + 1), words.eraseDups, Mettapedia.Util.LinearHash.eraseDups_nodup _⟩

theorem recreation_changes_owner (table : Table Name) (address : Nat) (words : List Name) :
    (recreate table address words).owner ≠ table.owner := by
  intro same
  have generations := congrArg Prod.snd same
  simp [recreate] at generations

/-- The lazy owner guard agrees with eagerly dropping the previous cache
when this table is recreated, including reuse of its address. -/
theorem recreation_ignores_old_cache (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Cache k) (good : Good table names cache)
    (address : Nat) (words : List Name) (head : Nat) (question : Query) :
    query (recreate table address words) names permits (some cache) head question =
      query (recreate table address words) names permits none head question := by
  have different : cache.owner ≠ (recreate table address words).owner := by
    rw [good.1]
    exact Ne.symm (recreation_changes_owner table address words)
  simp [query, different]

theorem insertion_preserves_recognition (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Cache k) (good : Good table names cache)
    (name : Name) (head : Nat) (question : Query) :
    source (insertName table name) names permits head question = source table names permits head question := by
  rw [← recognized_exact _ names permits cache (insertion_preserves_cache table names cache good name),
    ← recognized_exact table names permits cache good]

theorem inserted_name_present (table : Table Name) (name : Name) :
    name ∈ (insertName table name).words := by
  unfold insertName
  split_ifs with present <;> simp [present]

theorem inserted_id_decodes (table : Table Name) (name : Name) :
    decode (insertName table name) ((insertName table name).words.idxOf name + 1) = some name := by
  simpa [decode] using List.getElem?_idxOf (inserted_name_present table name)

structure State (Name : Type) (k : Nat) where
  table : Table Name
  cache : Option (Cache k)

def Valid (names : Fin k → Name) (state : State Name k) : Prop :=
  ∀ cache, state.cache = some cache → Good state.table names cache

inductive Command (Name Query : Type) where
  | inspect (head : Nat) (question : Query)
  | intern (name : Name)
  | recreate (address : Nat) (words : List Name)

inductive Reply where
  | classified (result : Bool)
  | interned (head : Nat)
  | recreated
  deriving DecidableEq, Repr

def sourceStep (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (table : Table Name) : Command Name Query → Reply × Table Name
  | .inspect head question => (.classified (source table names permits head question), table)
  | .intern name =>
      let next := insertName table name
      (.interned (next.words.idxOf name + 1), next)
  | .recreate address words => (.recreated, recreate table address words)

def cachedStep (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) : Command Name Query → Reply × State Name k
  | .inspect head question =>
      let found := query state.table names permits state.cache head question
      (.classified found.1, { state with cache := found.2 })
  | .intern name =>
      let next := insertName state.table name
      (.interned (next.words.idxOf name + 1), { state with table := next })
  | .recreate address words => (.recreated, ⟨recreate state.table address words, none⟩)

omit [DecidableEq Name] in
theorem cold_valid (names : Fin k → Name) (table : Table Name) :
    Valid names ⟨table, none⟩ := by
  intro cache found
  cases found

theorem step_preserves_valid (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (command : Command Name Query) :
    Valid names (cachedStep names permits state command).2 := by
  cases command with
  | inspect head question =>
      intro cache found
      exact query_good state.table names permits state.cache (fun known present _ => valid known present)
        head question cache found
  | intern name =>
      intro cache found
      exact insertion_preserves_cache state.table names cache (valid cache found) name
  | recreate address words => exact cold_valid names _

theorem service_square (names : Fin k → Name) (permits : Fin k → Query → Bool)
    (state : State Name k) (valid : Valid names state) (command : Command Name Query) :
    sourceStep names permits state.table command =
      ((cachedStep names permits state command).1, (cachedStep names permits state command).2.table) := by
  cases command with
  | inspect head question =>
      have same := query_exact state.table names permits state.cache
        (fun known present _ => valid known present) head question
      exact congrArg (fun result => (Reply.classified result, state.table)) same.symm
  | intern name => rfl
  | recreate address words => rfl

/-- All finite adaptive clients observe the same replies and symbol tables,
including clients that recreate a table at the same address between queries. -/
theorem adaptive_exact (names : Fin k → Name) (permits : Fin k → Query → Bool)
    {Answer : Type} (program : ReadOnlyQuery.Program (Command Name Query) Reply Answer)
    (state : State Name k) (valid : Valid names state) :
    QueryState.run (sourceStep names permits) program state.table =
      OperatorChoice.ObserverContracts.eraseObservation State.table
        (QueryState.run (cachedStep names permits) program state) :=
  OperatorChoice.ObserverContracts.run_erasure_on
    (cachedStep names permits) (sourceStep names permits) State.table (Valid names)
    (fun current good command => step_preserves_valid names permits current good command)
    (fun current good command => service_square names permits current good command)
    program state valid

structure Reference where
  owner : Nat × Nat
  head : Nat
  deriving DecidableEq, Repr

def Current (table : Table Name) (reference : Reference) : Prop :=
  reference.owner = table.owner ∧ 0 < reference.head ∧ reference.head ≤ table.words.length

instance (table : Table Name) (reference : Reference) : Decidable (Current table reference) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

omit [DecidableEq Name] in
theorem decoded_reference_current (table : Table Name) (reference : Reference) (name : Name)
    (owner : reference.owner = table.owner) (found : decode table reference.head = some name) :
    Current table reference := by
  have nonzero : reference.head ≠ 0 := by intro zero; simp [decode, zero] at found
  have present : table.words[reference.head - 1]? = some name := by
    simpa [decode, nonzero] using found
  have bounded := (List.getElem?_eq_some_iff.mp present).1
  exact ⟨owner, by omega, by omega⟩

omit [DecidableEq Name] in
theorem cached_reference_current (table : Table Name) (names : Fin k → Name)
    (cache : Cache k) (good : Good table names cache) (index : Fin k) :
    Current table ⟨cache.owner, cache.ids index⟩ :=
  decoded_reference_current table _ (names index) good.1 (good.2 index)

omit [DecidableEq Name] in
theorem current_reference_decodes (table : Table Name) (reference : Reference)
    (current : Current table reference) : ∃ name, decode table reference.head = some name := by
  have positive := current.2.1
  have within := current.2.2
  have bounded : reference.head - 1 < table.words.length := by omega
  refine ⟨table.words[reference.head - 1], ?_⟩
  simp [decode, Nat.ne_of_gt current.2.1, List.getElem?_eq_getElem bounded]

/-- Copy the retained spelling into the target table and obtain its target
identity. The old table must remain readable for this operation. -/
def transport (old target : Table Name) (reference : Reference) : Option (Reference × Table Name) :=
  if Current old reference then do
    let name ← decode old reference.head
    let next := insertName target name
    some (⟨next.owner, next.words.idxOf name + 1⟩, next)
  else none

theorem transport_preserves_name (old target : Table Name) (reference : Reference)
    (current : Current old reference) :
    ∃ nextReference nextTable, transport old target reference = some (nextReference, nextTable) ∧
      Current nextTable nextReference ∧ decode nextTable nextReference.head = decode old reference.head ∧
      target.words <+: nextTable.words := by
  obtain ⟨name, found⟩ := current_reference_decodes old reference current
  let next := insertName target name
  let moved : Reference := ⟨next.owner, next.words.idxOf name + 1⟩
  have decoded : decode next moved.head = some name := inserted_id_decodes target name
  refine ⟨moved, next, ?_, decoded_reference_current next moved name rfl decoded,
    decoded.trans found.symm, insertion_extends_words target name⟩
  simp [transport, current, found, moved, next]

theorem transport_preserves_target_cache (old target : Table Name) (reference : Reference)
    (current : Current old reference) (names : Fin k → Name) (cache : Cache k)
    (good : Good target names cache) (nextReference : Reference) (nextTable : Table Name)
    (moved : transport old target reference = some (nextReference, nextTable)) :
    Good nextTable names cache := by
  obtain ⟨name, found⟩ := current_reference_decodes old reference current
  have same : (⟨(insertName target name).owner, (insertName target name).words.idxOf name + 1⟩,
      insertName target name) = (nextReference, nextTable) := by
    simpa [transport, current, found] using moved
  have tables : insertName target name = nextTable := congrArg Prod.snd same
  rw [← tables]
  exact insertion_preserves_cache target names cache good name

/-- Every successful transfer has the validity and spelling established by
the interning algorithm, including when the destination already knew the name. -/
theorem transport_result (old target : Table Name) (reference : Reference)
    (current : Current old reference) (nextReference : Reference) (nextTable : Table Name)
    (moved : transport old target reference = some (nextReference, nextTable)) :
    Current nextTable nextReference ∧
      decode nextTable nextReference.head = decode old reference.head ∧
      target.words <+: nextTable.words := by
  obtain ⟨saved, extended, produced, valid, spelling, growth⟩ :=
    transport_preserves_name old target reference current
  have same : (saved, extended) = (nextReference, nextTable) :=
    Option.some.inj (produced.symm.trans moved)
  cases same
  exact ⟨valid, spelling, growth⟩

def sourceReference (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (reference : Reference) (question : Query) : Option Bool :=
  if Current table reference then some (source table names permits reference.head question) else none

/-- A name-based policy is preserved by actual transfer. Execution authority
is not part of this policy and need not be shared by the two table owners. -/
theorem transport_recognition (old target : Table Name) (reference : Reference)
    (current : Current old reference) (nextReference : Reference) (nextTable : Table Name)
    (moved : transport old target reference = some (nextReference, nextTable))
    (names : Fin k → Name) (permits : Fin k → Query → Bool) (question : Query) :
    sourceReference nextTable names permits nextReference question =
      sourceReference old names permits reference question := by
  obtain ⟨valid, spelling, _⟩ := transport_result old target reference current
    nextReference nextTable moved
  simp only [sourceReference, valid, current, ↓reduceIte, source, spelling]

def queryReference (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Option (Cache k))
    (reference : Reference) (question : Query) : Option Bool × Option (Cache k) :=
  if Current table reference then
    let found := query table names permits cache reference.head question
    (some found.1, found.2)
  else (none, cache)

theorem reference_query_exact (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Option (Cache k))
    (valid : ∀ known, cache = some known → known.owner = table.owner → Good table names known)
    (reference : Reference) (question : Query) :
    (queryReference table names permits cache reference question).1 =
      sourceReference table names permits reference question := by
  by_cases current : Current table reference
  · simp [queryReference, sourceReference, current, query_exact table names permits cache valid]
  · simp [queryReference, sourceReference, current]

/-- Established ownership discharges the wrapper check; this law does not
require trusted internal callers to perform another validation pass. -/
theorem reference_with_current_evidence (table : Table Name) (names : Fin k → Name)
    (permits : Fin k → Query → Bool) (cache : Option (Cache k))
    (reference : Reference) (question : Query) (current : Current table reference) :
    queryReference table names permits cache reference question =
      (some (query table names permits cache reference.head question).1,
        (query table names permits cache reference.head question).2) := by
  simp [queryReference, current]

omit [DecidableEq Name] in
theorem recreation_invalidates_reference (table : Table Name) (reference : Reference)
    (current : Current table reference) (fresh : Table Name) (different : fresh.owner ≠ table.owner) :
    ¬Current fresh reference := by
  intro next
  exact different (next.1.symm.trans current.1)

namespace Controls

def names : Fin 1 → String := fun _ => "worker"
def permits : Fin 1 → Nat → Bool := fun _ arity => arity == 2
def original : Table String := ⟨(9, 1), ["worker", "other"], by decide⟩
def replaced := recreate original 9 ["other", "worker"]
def retained : Cache 1 := ⟨original.owner, fun _ => 1⟩

theorem same_address_does_not_mean_same_incarnation :
    original.owner.1 = replaced.owner.1 ∧ original.owner ≠ replaced.owner := by decide

theorem stale_ids_change_the_answer :
    recognized retained permits 1 2 = true ∧ source replaced names permits 1 2 = false := by decide

theorem owner_guard_repairs_reused_address :
    (query replaced names permits (some retained) 1 2).1 = false ∧
      (query replaced names permits (some retained) 2 2).1 = true := by decide

theorem arity_stays_part_of_recognition :
    (query original names permits (some retained) 1 2).1 = true ∧
      (query original names permits (some retained) 1 3).1 = false := by decide

def missing : Table String := ⟨(3, 1), ["other"], by decide⟩

theorem missing_compilation_does_not_change_the_source_answer :
    (compile missing names).isNone = true ∧
      (query missing names permits none 1 2).1 = source missing names permits 1 2 := by decide

def foreign : Table String := ⟨(10, 1), ["other", "worker"], by decide⟩

theorem incarnation_without_address_is_insufficient :
    original.owner.2 = foreign.owner.2 ∧
      recognized retained permits 1 2 ≠ (query foreign names permits (some retained) 1 2).1 := by decide

theorem retained_reference_is_not_reinterpreted_after_recreation :
    sourceReference original names permits ⟨original.owner, 1⟩ 2 = some true ∧
      (queryReference replaced names permits (some retained) ⟨original.owner, 1⟩ 2).1 = none := by decide

theorem copying_the_name_repairs_cross_table_transport :
    (transport original replaced ⟨original.owner, 1⟩).map (fun result => result.1.head) = some 2 ∧
      ((transport original replaced ⟨original.owner, 1⟩).bind fun result => decode result.2 result.1.head) =
        some "worker" := by decide

def lifecycle : ReadOnlyQuery.Program (Command String Nat) Reply (List Reply) :=
  .read (.inspect 1 2) fun first =>
    .read (.intern "worker") fun inserted =>
      match inserted with
      | .interned head =>
          .read (.inspect head 2) fun beforeReset =>
            .read (.recreate 3 ["worker", "other"]) fun _ =>
              .read (.inspect head 2) fun afterReset => .pure [first, beforeReset, afterReset]
      | _ => .pure []

theorem adaptive_lifecycle_keeps_the_current_table_meaning :
    (QueryState.run (cachedStep names permits) lifecycle ⟨missing, none⟩).answer =
      [.classified false, .classified true, .classified false] := by decide

end Controls

end Mettapedia.Machines.SymbolTableHeadCache
