import Std

/-!
# Hierarchy compaction requests, retained history, and publication recovery

The concrete request boundary accepts inert wire syntax only after request-ID
computation has produced a grounded string.  In particular,
`(request (space:request-id) compact UUID)` is not a valid call: the second
request field is an expression, not a string.  Binding the ID first and then
constructing `(request ID compact UUID)` repairs that fixture boundary.

The store model retains every `(record identity, revision)` payload.  Compaction
moves all records to an archive without changing hierarchy nodes.  Reopening
requires archive availability and then restores the exact logical store.  This
is deliberately an all-versions retention contract, not a license to discard
unreferenced history.

Publication has separate staging and commit transitions.  Recovery consults
only the committed, already published generation and checks completeness and
referential closure.  Pending or interrupted candidates are invisible.  The
commit transition is the explicit atomic boundary in this model; no unstated
crash-atomic filesystem assumption is used.  These are checked model laws, not
a verification claim about the unmodified native service.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HierarchyCompactionContract

universe u v

variable {Id : Type u} {Payload : Type v}

/-! ## Typed request and response wire boundary -/

inductive Wire where
  | symbol (name : String)
  | string (value : String)
  | expr (items : List Wire)
  deriving Repr

structure CompactRequest where
  requestId : String
  spaceUuid : String
  deriving DecidableEq, Repr

def encodeRequest (request : CompactRequest) : Wire :=
  .expr [.symbol "request", .string request.requestId,
    .symbol "compact", .string request.spaceUuid]

def decodeRequest : Wire → Option CompactRequest
  | .expr [.symbol "request", .string requestId, .symbol "compact", .string spaceUuid] =>
      some ⟨requestId, spaceUuid⟩
  | _ => none

@[simp] theorem decode_encodeRequest (request : CompactRequest) :
    decodeRequest (encodeRequest request) = some request := by
  cases request
  rfl

inductive ReplyBody where
  | ok (answer : String)
  | error (reason : String)
  deriving DecidableEq, Repr

structure Reply where
  requestId : String
  body : ReplyBody
  deriving DecidableEq, Repr

def encodeReply (reply : Reply) : Wire :=
  match reply.body with
  | .ok answer =>
      .expr [.symbol "reply", .string reply.requestId, .symbol "ok", .string answer]
  | .error reason =>
      .expr [.symbol "reply", .string reply.requestId, .symbol "error", .string reason]

def decodeReply : Wire → Option Reply
  | .expr [.symbol "reply", .string requestId, .symbol "ok", .string answer] =>
      some ⟨requestId, .ok answer⟩
  | .expr [.symbol "reply", .string requestId, .symbol "error", .string reason] =>
      some ⟨requestId, .error reason⟩
  | _ => none

@[simp] theorem decode_encodeReply (reply : Reply) :
    decodeReply (encodeReply reply) = some reply := by
  cases reply
  rename_i requestId body
  cases body <;> rfl

structure Call where
  socket : String
  request : Wire
  timeoutMs : Nat
  deriving Repr

/-! ## Logical history and physical compaction -/

inductive RetentionPolicy where
  | allVersions
  deriving DecidableEq, Repr

structure Record (Id : Type u) (Payload : Type v) where
  id : Id
  revision : Nat
  payload : Payload
  deriving DecidableEq, Repr

structure Node (Id : Type u) where
  id : Id
  revision : Nat
  children : List Id
  deriving DecidableEq, Repr

structure Store (Id : Type u) (Payload : Type v) where
  records : List (Record Id Payload)
  nodes : List (Node Id)
  retention : RetentionPolicy
  deriving DecidableEq, Repr

structure PhysicalStore (Id : Type u) (Payload : Type v) where
  current : List (Record Id Payload)
  archive : List (Record Id Payload)
  nodes : List (Node Id)
  retention : RetentionPolicy
  deriving DecidableEq, Repr

/-- A read addresses both record identity and immutable revision. -/
def readRecord [DecidableEq Id] (records : List (Record Id Payload))
    (id : Id) (revision : Nat) : Option Payload :=
  (records.find? fun record => record.id == id && record.revision == revision).map Record.payload

def read [DecidableEq Id] (store : Store Id Payload) (id : Id) (revision : Nat) : Option Payload :=
  readRecord store.records id revision

def resolveNode [DecidableEq Id] (store : Store Id Payload) (id : Id) : Option (Node Id) :=
  store.nodes.find? fun node => node.id == id

/-- Physical compaction changes record placement only. -/
def compact (store : Store Id Payload) : PhysicalStore Id Payload :=
  ⟨[], store.records, store.nodes, store.retention⟩

/-- Archive unavailability is explicit and yields no partial logical view. -/
def reopen (archiveAvailable : Bool) (physical : PhysicalStore Id Payload) :
    Option (Store Id Payload) :=
  if archiveAvailable then
    some ⟨physical.current ++ physical.archive, physical.nodes, physical.retention⟩
  else none

@[simp] theorem reopen_compact (store : Store Id Payload) :
    reopen true (compact store) = some store := by
  cases store
  rfl

@[simp] theorem reopen_unavailable (physical : PhysicalStore Id Payload) :
    reopen false physical = none := rfl

theorem compact_reopen_read [DecidableEq Id] (store : Store Id Payload) (id : Id) (revision : Nat) :
    (reopen true (compact store)).map (fun reopened => read reopened id revision) =
      some (read store id revision) := by
  rw [reopen_compact]
  rfl

theorem compact_reopen_node [DecidableEq Id] (store : Store Id Payload) (id : Id) :
    (reopen true (compact store)).map (fun reopened => resolveNode reopened id) =
      some (resolveNode store id) := by
  rw [reopen_compact]
  rfl

def nodeClosed [DecidableEq Id] (records : List (Record Id Payload))
    (nodes : List (Node Id)) (node : Node Id) : Bool :=
  (records.any fun record => record.id == node.id && record.revision == node.revision) &&
    node.children.all fun child => nodes.any fun candidate => candidate.id == child

def referentiallyClosed [DecidableEq Id] (store : Store Id Payload) : Bool :=
  store.nodes.all (nodeClosed store.records store.nodes)

def ReferentiallyClosed [DecidableEq Id] (store : Store Id Payload) : Prop :=
  ∀ node ∈ store.nodes,
    (∃ record ∈ store.records, record.id = node.id ∧ record.revision = node.revision) ∧
      ∀ child ∈ node.children, ∃ childNode ∈ store.nodes, childNode.id = child

@[simp] theorem compact_reopen_referentially_closed [DecidableEq Id] (store : Store Id Payload)
    (closed : ReferentiallyClosed store) :
    ∃ reopened, reopen true (compact store) = some reopened ∧ ReferentiallyClosed reopened := by
  exact ⟨store, reopen_compact store, closed⟩

/-! ## Requests enter compaction only after complete validation -/

def dispatch (socketValid : String → Bool) (call : Call) (store : Store Id Payload) :
    Option (PhysicalStore Id Payload) :=
  if socketValid call.socket && call.timeoutMs != 0 then
    (decodeRequest call.request).map fun _ => compact store
  else none

theorem malformed_request_does_not_compact (socketValid : String → Bool) (call : Call)
    (store : Store Id Payload) (malformed : decodeRequest call.request = none) :
    dispatch socketValid call store = none := by
  simp [dispatch, malformed]

theorem valid_request_compacts (socketValid : String → Bool) (call : Call)
    (store : Store Id Payload) (socket : socketValid call.socket = true)
    (timeout : call.timeoutMs ≠ 0) {request : CompactRequest}
    (decoded : decodeRequest call.request = some request) :
    dispatch socketValid call store = some (compact store) := by
  simp [dispatch, socket, timeout, decoded]

/-- A validated compact request followed by an available reopen is exactly the
original logical store, including both history and hierarchy references. -/
theorem valid_request_compact_reopen (socketValid : String → Bool) (call : Call)
    (store : Store Id Payload) (socket : socketValid call.socket = true)
    (timeout : call.timeoutMs ≠ 0) {request : CompactRequest}
    (decoded : decodeRequest call.request = some request) :
    (dispatch socketValid call store).bind (reopen true) = some store := by
  rw [valid_request_compacts socketValid call store socket timeout decoded]
  exact reopen_compact store

/-- The failing fixture leaves request-ID computation as an inert expression. -/
def oldFixtureRequest (spaceUuid : String) : Wire :=
  .expr [.symbol "request", .expr [.symbol "space:request-id"],
    .symbol "compact", .string spaceUuid]

/-- The repaired fixture first binds a grounded request ID. -/
def letBoundRequest (requestId spaceUuid : String) : Wire :=
  encodeRequest ⟨requestId, spaceUuid⟩

@[simp] theorem oldFixtureRequest_invalid (spaceUuid : String) :
    decodeRequest (oldFixtureRequest spaceUuid) = none := rfl

theorem old_fixture_refused (socketValid : String → Bool) (socket : String)
    (spaceUuid : String) (store : Store Id Payload) :
    dispatch socketValid ⟨socket, oldFixtureRequest spaceUuid, 5000⟩ store = none := by
  simp [dispatch, decodeRequest, oldFixtureRequest]

theorem let_bound_compact_reopen (socket : String) (store : Store Id Payload) :
    (dispatch (fun _ => true) ⟨socket, letBoundRequest "request-7" "space-9", 5000⟩ store).bind
      (reopen true) = some store := by
  apply valid_request_compact_reopen
  · rfl
  · simp
  · exact decode_encodeRequest _

/-! ## Staging, commit, and recovery -/

structure Generation (Id : Type u) (Payload : Type v) where
  identity : Nat
  store : Store Id Payload
  complete : Bool
  deriving DecidableEq, Repr

structure Publication (Id : Type u) (Payload : Type v) where
  published : List (Generation Id Payload)
  pending : List (Generation Id Payload)
  committed : Option Nat
  deriving DecidableEq, Repr

/-- Only the published generation named by the commit pointer can be recovered. -/
def recover [DecidableEq Id] (publication : Publication Id Payload) : Option (Store Id Payload) :=
  match publication.committed with
  | none => none
  | some identity =>
      match publication.published.find? fun generation => generation.identity == identity with
      | none => none
      | some generation =>
          if generation.complete && referentiallyClosed generation.store then
            some generation.store
          else none

/-- Staging a candidate does not move the commit pointer or publish anything. -/
def stage (publication : Publication Id Payload) (generation : Generation Id Payload) :
    Publication Id Payload :=
  { publication with pending := publication.pending ++ [generation] }

@[simp] theorem recover_stage [DecidableEq Id] (publication : Publication Id Payload)
    (generation : Generation Id Payload) :
    recover (stage publication generation) = recover publication := rfl

/-- Generic publication permits deliberate data replacement; its completeness
and closure checks are not a history-preservation claim. -/
def commit [DecidableEq Id] (publication : Publication Id Payload) (identity : Nat) :
    Option (Publication Id Payload) :=
  match publication.pending.find? fun generation => generation.identity == identity with
  | none => none
  | some generation =>
      if generation.complete && referentiallyClosed generation.store then
        some { publication with
          published := generation :: publication.published
          committed := some identity }
      else none

theorem commit_recovers_generation [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (generation : Generation Id Payload)
    (pending : (publication.pending.find? fun candidate => candidate.identity == identity) =
      some generation)
    (complete : generation.complete = true)
    (closed : referentiallyClosed generation.store = true) :
    (commit publication identity).bind recover = some generation.store := by
  have sameBeq : generation.identity == identity :=
    List.find?_some (p := fun candidate : Generation Id Payload => candidate.identity == identity) pending
  have sameIdentity : generation.identity = identity := by simpa using sameBeq
  subst identity
  simp [commit, pending, complete, closed, recover]

theorem interrupted_incomplete_replacement_not_exposed [DecidableEq Id]
    (publication : Publication Id Payload) (generation : Generation Id Payload) :
    recover (stage publication generation) = recover publication := by
  exact recover_stage publication generation

theorem incomplete_commit_refused [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (generation : Generation Id Payload)
    (pending : (publication.pending.find? fun candidate => candidate.identity == identity) =
      some generation)
    (incomplete : generation.complete = false) : commit publication identity = none := by
  simp [commit, pending, incomplete]

theorem unclosed_commit_refused [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (generation : Generation Id Payload)
    (pending : (publication.pending.find? fun candidate => candidate.identity == identity) =
      some generation)
    (unclosed : referentiallyClosed generation.store = false) : commit publication identity = none := by
  simp [commit, pending, unclosed]

/-- Any successful recovery is backed by a complete, referentially closed,
published generation; a dangling commit pointer never yields a partial store. -/
theorem recover_complete_closed [DecidableEq Id] (publication : Publication Id Payload)
    (store : Store Id Payload) (recovered : recover publication = some store) :
    ∃ generation ∈ publication.published,
      generation.complete = true ∧ referentiallyClosed generation.store = true ∧
        generation.store = store := by
  unfold recover at recovered
  cases committed : publication.committed with
  | none => simp [committed] at recovered
  | some identity =>
      simp only [committed] at recovered
      cases found : (publication.published.find? fun generation => generation.identity == identity) with
      | none => simp [found] at recovered
      | some generation =>
          simp only [found] at recovered
          split at recovered
          · rename_i valid
            cases Option.some.inj recovered
            simp only [Bool.and_eq_true] at valid
            exact ⟨generation, List.mem_of_find?_eq_some found, valid.1, valid.2, rfl⟩
          · contradiction

/-! ## Compaction-specific staging and publication -/

/-- Historical staging constructed the replacement from the recovered base,
but left candidate identity unchecked. An earlier pending candidate could
therefore shadow the one appended here. -/
def legacyStageCompaction [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (archiveAvailable : Bool) : Option (Publication Id Payload) := do
  let base ← recover publication
  let candidate ← reopen archiveAvailable (compact base)
  if referentiallyClosed candidate then
    some (stage publication ⟨identity, candidate, true⟩)
  else none

/-- A compaction candidate cannot shadow an older pending or published
generation. The lookup used by commit is keyed by this identity. -/
def generationUnused (publication : Publication Id Payload) (identity : Nat) : Bool :=
  publication.pending.all (fun generation => generation.identity != identity) &&
    publication.published.all (fun generation => generation.identity != identity)

/-- The candidate is derived from the recovered base and its identity is
checked before staging. The composed publication below is sequential;
interleaved writers require an additional base-revalidation contract. -/
def stageCompaction [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (archiveAvailable : Bool) : Option (Publication Id Payload) :=
  if generationUnused publication identity then
    legacyStageCompaction publication identity archiveAvailable
  else none

theorem stageCompaction_collision_refused [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat) (archiveAvailable : Bool)
    (collision : generationUnused publication identity = false) :
    stageCompaction publication identity archiveAvailable = none := by
  simp [stageCompaction, collision]

theorem stageCompaction_some_unused [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat) (archiveAvailable : Bool)
    {staged : Publication Id Payload}
    (success : stageCompaction publication identity archiveAvailable = some staged) :
    generationUnused publication identity = true := by
  unfold stageCompaction at success
  split at success
  · assumption
  · contradiction

theorem staged_fresh_candidate_found (publication : Publication Id Payload)
    (identity : Nat) (base : Store Id Payload)
    (fresh : generationUnused publication identity = true) :
    ((stage publication ⟨identity, base, true⟩).pending.find?
      fun candidate => candidate.identity == identity) = some ⟨identity, base, true⟩ := by
  have checks :
      publication.pending.all (fun generation => generation.identity != identity) = true ∧
      publication.published.all (fun generation => generation.identity != identity) = true := by
    simpa only [generationUnused, Bool.and_eq_true] using fresh
  have checked := checks.1
  have missing : (publication.pending.find?
      fun candidate => candidate.identity == identity) = none := by
    apply List.find?_eq_none.mpr
    intro candidate member
    have different := List.all_eq_true.mp checked candidate member
    simpa using different
  simp [stage, List.find?_append, missing]

theorem stageCompaction_success [DecidableEq Id] (publication : Publication Id Payload)
    (identity : Nat) (base : Store Id Payload)
    (recovered : recover publication = some base)
    (closed : referentiallyClosed base = true)
    (fresh : generationUnused publication identity = true) :
    stageCompaction publication identity true =
      some (stage publication ⟨identity, base, true⟩) := by
  simp [stageCompaction, fresh, legacyStageCompaction, recovered, closed]

/-- The complete compaction path is tied to its recovered base. Identity
freshness is enforced by staging; the correct lookup is derived from it. -/
theorem compact_stage_commit_recovers_base [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat) (base : Store Id Payload)
    (recovered : recover publication = some base)
    (closed : referentiallyClosed base = true)
    (fresh : generationUnused publication identity = true) :
    ((stageCompaction publication identity true).bind (fun staged =>
      (commit staged identity).bind recover)) = some base := by
  rw [stageCompaction_success publication identity base recovered closed fresh]
  exact commit_recovers_generation _ _ ⟨identity, base, true⟩
    (staged_fresh_candidate_found publication identity base fresh) rfl closed

theorem compact_stage_commit_preserves_read [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat) (base : Store Id Payload)
    (recovered : recover publication = some base)
    (closed : referentiallyClosed base = true)
    (fresh : generationUnused publication identity = true)
    (id : Id) (revision : Nat) :
    ((stageCompaction publication identity true).bind fun staged =>
      (commit staged identity).bind recover).map (fun store => read store id revision) =
        some (read base id revision) := by
  rw [compact_stage_commit_recovers_base publication identity base recovered closed fresh]
  rfl

/-- Successful staging supplies the freshness and valid base needed by commit;
callers need not assume that a particular pending lookup happens to succeed. -/
theorem staged_compaction_commit_preserves_base [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat)
    {staged : Publication Id Payload}
    (success : stageCompaction publication identity true = some staged) :
    ∃ base, recover publication = some base ∧
      (commit staged identity).bind recover = some base := by
  have fresh := stageCompaction_some_unused publication identity true success
  cases recovered : recover publication with
  | none =>
      simp [stageCompaction, fresh, legacyStageCompaction, recovered] at success
  | some base =>
      have closed : referentiallyClosed base = true := by
        obtain ⟨generation, _, _, valid, equal⟩ := recover_complete_closed publication base recovered
        simpa only [equal] using valid
      have same : staged = stage publication ⟨identity, base, true⟩ :=
        Option.some.inj (success.symm.trans
          (stageCompaction_success publication identity base recovered closed fresh))
      refine ⟨base, rfl, ?_⟩
      rw [same]
      exact commit_recovers_generation _ _ ⟨identity, base, true⟩
        (staged_fresh_candidate_found publication identity base fresh) rfl closed

theorem staged_compaction_commit_preserves_read [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat)
    {staged : Publication Id Payload}
    (success : stageCompaction publication identity true = some staged)
    (id : Id) (revision : Nat) :
    ((commit staged identity).bind recover).map (fun store => read store id revision) =
      (recover publication).map (fun store => read store id revision) := by
  obtain ⟨base, recovered, committed⟩ :=
    staged_compaction_commit_preserves_base publication identity success
  rw [recovered, committed]

/-- Archive refusal happens before staging, so no compaction candidate is
silently published with an incomplete logical view. -/
theorem stageCompaction_archive_unavailable [DecidableEq Id]
    (publication : Publication Id Payload) (identity : Nat) :
    stageCompaction publication identity false = none := by
  unfold stageCompaction
  split
  · unfold legacyStageCompaction
    cases recover publication <;> rfl
  · rfl

/-! ## Original-plus-correction regression -/

namespace Controls

abbrev S := Store String String

def original : Record String String := ⟨"e", 1, "original needle Ω"⟩
def task : Record String String := ⟨"t", 1, "Original objective"⟩
def project : Record String String := ⟨"p", 1, "Overview"⟩
def corrected : Record String String := ⟨"e", 2, "corrected"⟩

def seeded : S :=
  { records := [original, task, project, corrected]
    nodes := [⟨"e", 2, []⟩, ⟨"t", 1, ["e"]⟩, ⟨"p", 1, ["t"]⟩]
    retention := .allVersions }

theorem original_and_correction_survive_compact_reopen :
    (reopen true (compact seeded)).map (fun store => read store "e" 1) =
      some (some "original needle Ω") ∧
    (reopen true (compact seeded)).map (fun store => read store "e" 2) =
      some (some "corrected") ∧
    referentiallyClosed seeded = true := by
  decide

theorem exact_fixture_repair_composes :
    (dispatch (fun _ => true) ⟨"/sock", oldFixtureRequest "space-9", 5000⟩ seeded = none) ∧
      ((dispatch (fun _ => true)
        ⟨"/sock", letBoundRequest "request-7" "space-9", 5000⟩ seeded).bind
          (reopen true) = some seeded) := by
  constructor
  · exact old_fixture_refused _ _ _ _
  · exact let_bound_compact_reopen _ _

def initialPublication : Publication String String :=
  { published := [⟨1, seeded, true⟩], pending := [], committed := some 1 }

/-- An interrupted staged replacement leaves the committed original generation
visible; after valid commit, that complete replacement is selected instead. -/
theorem interruption_then_commit :
    recover (stage initialPublication ⟨2, seeded, false⟩) = some seeded ∧
      ((commit (stage initialPublication ⟨2, seeded, true⟩) 2).bind recover = some seeded) := by
  constructor
  · rfl
  · exact commit_recovers_generation _ _ ⟨2, seeded, true⟩ rfl rfl (by decide)

theorem compaction_publication_preserves_original_and_correction :
    ((stageCompaction initialPublication 2 true).bind fun staged =>
      (commit staged 2).bind recover).map (fun store => read store "e" 1) =
        some (some "original needle Ω") ∧
    ((stageCompaction initialPublication 2 true).bind fun staged =>
      (commit staged 2).bind recover).map (fun store => read store "e" 2) =
        some (some "corrected") := by
  constructor <;> decide

end Controls

#print axioms decode_encodeRequest
#print axioms decode_encodeReply
#print axioms reopen_compact
#print axioms compact_reopen_read
#print axioms compact_reopen_node
#print axioms malformed_request_does_not_compact
#print axioms valid_request_compact_reopen
#print axioms old_fixture_refused
#print axioms let_bound_compact_reopen
#print axioms commit_recovers_generation
#print axioms recover_stage
#print axioms recover_complete_closed
#print axioms compact_stage_commit_recovers_base
#print axioms compact_stage_commit_preserves_read
#print axioms stageCompaction_collision_refused
#print axioms stageCompaction_some_unused
#print axioms staged_compaction_commit_preserves_base
#print axioms staged_compaction_commit_preserves_read
#print axioms stageCompaction_archive_unavailable
#print axioms Controls.original_and_correction_survive_compact_reopen
#print axioms Controls.exact_fixture_repair_composes
#print axioms Controls.interruption_then_commit
#print axioms Controls.compaction_publication_preserves_original_and_correction

end Mettapedia.Machines.HierarchyCompactionContract
