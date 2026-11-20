import Mettapedia.Machines.Cursor.ReadScopeComposition

/-!
# Entry views for sequential query trees

A union can open its second branch after its caller has changed the world.
Every such read must still obtain the conjunction's entry view. The finite
query interpreter below retains atomic row lists when they are opened and
opens later branches on demand. Its reference meaning is an independent
list-valued relational join, preserving duplicate occurrences.

The journal construction retains complete semantic read coordinates. A
native head index must prove that its coordinates cover the actual patterns,
including wildcard heads and nonstandard carriers. This is not a C memory,
allocation-failure, or synchronization theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.EntryQueryTree

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Trace Search)

variable {Key Pattern Row Env World : Type}

inductive Query (Key Pattern : Type) where
  | atom (key : Key) (pattern : Pattern)
  | seq (first second : Query Key Pattern)
  | union (first second : Query Key Pattern)
  deriving DecidableEq, Repr

def dependencies : Query Key Pattern → List Key
  | .atom key _ => [key]
  | .seq first second | .union first second =>
      dependencies first ++ dependencies second

/-- The leftmost atomic read opens before the first answer can return. Every
other atomic read may open later, including a first union's second branch. -/
def laterDependencies : Query Key Pattern → List Key
  | .atom _ _ => []
  | .seq first second | .union first second =>
      laterDependencies first ++ dependencies second

/-- An atomic matcher may itself have several answers. Rows and resulting
bindings remain occurrences, rather than sets of equal payloads. -/
def evaluate (matchRow : Pattern → Row → Env → List Env) (entry : Key → List Row) :
    Query Key Pattern → Env → List Env
  | .atom key pattern, env => (entry key).flatMap fun row => matchRow pattern row env
  | .seq first second, env =>
      (evaluate matchRow entry first env).flatMap (evaluate matchRow entry second)
  | .union first second, env =>
      evaluate matchRow entry first env ++ evaluate matchRow entry second env

/-- A later union branch and each later join leg read from the world supplied
by the caller of their continuation. Only an already opened atomic reader
has closed over its row list. -/
def stream (matchRow : Pattern → Row → Env → List Env)
    (readRows : World → Key → List Row) : Query Key Pattern → Env → Search World Env
  | .atom key pattern, env => fun world =>
      Search.superpose ((readRows world key).flatMap fun row => matchRow pattern row env) world
  | .seq first second, env =>
      (stream matchRow readRows first env).bind (stream matchRow readRows second)
  | .union first second, env => fun world =>
      (stream matchRow readRows first env world).append (stream matchRow readRows second env)

theorem append_superpose (first second : List Env) :
    (fun world : World => (Search.superpose first world).append (Search.superpose second)) =
      Search.superpose (first ++ second) := by
  induction first with
  | nil => rfl
  | cons value later ih =>
      funext world
      simp only [Search.superpose, Trace.append, List.cons_append]
      exact congrArg (Trace.answer value world) ih

theorem bind_superpose (values : List Env) (next : Env → List Env) :
    (Search.superpose values : Search World Env).bind (fun value => Search.superpose (next value)) =
      Search.superpose (values.flatMap next) := by
  induction values with
  | nil => rfl
  | cons value later ih =>
      funext world
      change (Search.superpose (next value) world).append
        ((Search.superpose later).bind (fun value => Search.superpose (next value))) = _
      rw [ih]
      exact congrFun (append_superpose (next value) (later.flatMap next)) world

/-- Equality of complete resumable traces is stronger than equality of their
completed bags: the consumer may supply an arbitrary world after any answer. -/
theorem stream_entry (matchRow : Pattern → Row → Env → List Env)
    (entry : Key → List Row) (readRows : World → Key → List Row)
    (query : Query Key Pattern)
    (covered : ∀ world key, key ∈ dependencies query → readRows world key = entry key)
    (env : Env) :
    stream matchRow readRows query env = Search.superpose (evaluate matchRow entry query env) := by
  induction query generalizing env with
  | atom key pattern =>
      funext world
      simp [stream, evaluate, covered world key (by simp [dependencies])]
  | seq first second firstIH secondIH =>
      have firstCovered : ∀ world key, key ∈ dependencies first →
          readRows world key = entry key := by
        intro world key member
        exact covered world key (List.mem_append_left _ member)
      have secondCovered : ∀ world key, key ∈ dependencies second →
          readRows world key = entry key := by
        intro world key member
        exact covered world key (List.mem_append_right _ member)
      have next : stream matchRow readRows second =
          fun state => Search.superpose (evaluate matchRow entry second state) := by
        funext state
        exact secondIH secondCovered state
      simp only [stream, evaluate, firstIH firstCovered, next]
      exact bind_superpose _ _
  | union first second firstIH secondIH =>
      have firstCovered : ∀ world key, key ∈ dependencies first →
          readRows world key = entry key := by
        intro world key member
        exact covered world key (List.mem_append_left _ member)
      have secondCovered : ∀ world key, key ∈ dependencies second →
          readRows world key = entry key := by
        intro world key member
        exact covered world key (List.mem_append_right _ member)
      simp only [stream, evaluate, firstIH firstCovered, secondIH secondCovered]
      exact append_superpose _ _

/-- This is an extensional model of retained entry authority, not a demand
that a native implementation eagerly copy these lists. -/
def journal [DecidableEq Key] (watched : List Key) (entry live : Key → List Row)
    (key : Key) : List Row := if key ∈ watched then entry key else live key

theorem journal_entry [DecidableEq Key] (matchRow : Pattern → Row → Env → List Env)
    (entry : Key → List Row) (live : World → Key → List Row)
    (query : Query Key Pattern) (watched : List Key)
    (coverage : ∀ key ∈ dependencies query, key ∈ watched) (env : Env) :
    stream matchRow (fun world => journal watched entry (live world)) query env =
      Search.superpose (evaluate matchRow entry query env) := by
  apply stream_entry
  intro world key member
  simp [journal, coverage key member]

/-- The first atomic reader may use the live store at opening, then retain
its own rows. Only reads that can open later require persistent entry authority. -/
theorem stream_entry_at_open (matchRow : Pattern → Row → Env → List Env)
    (entry : Key → List Row) (readRows : World → Key → List Row)
    (query : Query Key Pattern) (opened : World)
    (atOpen : ∀ key ∈ dependencies query, readRows opened key = entry key)
    (later : ∀ world key, key ∈ laterDependencies query → readRows world key = entry key)
    (env : Env) :
    stream matchRow readRows query env opened =
      Search.superpose (evaluate matchRow entry query env) opened := by
  induction query generalizing env with
  | atom key pattern => simp [stream, evaluate, atOpen key (by simp [dependencies])]
  | seq first second firstIH _ =>
      have firstOpen : ∀ key ∈ dependencies first, readRows opened key = entry key := by
        intro key member
        exact atOpen key (List.mem_append_left _ member)
      have firstLater : ∀ world key, key ∈ laterDependencies first →
          readRows world key = entry key := by
        intro world key member
        exact later world key (List.mem_append_left _ member)
      have next : stream matchRow readRows second =
          fun state => Search.superpose (evaluate matchRow entry second state) := by
        funext state
        apply stream_entry
        intro world key member
        exact later world key (List.mem_append_right _ member)
      change (stream matchRow readRows first env opened).bind
        (stream matchRow readRows second) = _
      rw [firstIH firstOpen firstLater env, next]
      exact congrFun (bind_superpose _ _) opened
  | union first second firstIH _ =>
      have firstOpen : ∀ key ∈ dependencies first, readRows opened key = entry key := by
        intro key member
        exact atOpen key (List.mem_append_left _ member)
      have firstLater : ∀ world key, key ∈ laterDependencies first →
          readRows world key = entry key := by
        intro world key member
        exact later world key (List.mem_append_left _ member)
      have next : stream matchRow readRows second env =
          Search.superpose (evaluate matchRow entry second env) := by
        apply stream_entry
        intro world key member
        exact later world key (List.mem_append_right _ member)
      change (stream matchRow readRows first env opened).append
        (stream matchRow readRows second env) = _
      rw [firstIH firstOpen firstLater env, next]
      exact congrFun (append_superpose _ _) opened

theorem journal_at_open [DecidableEq Key] (matchRow : Pattern → Row → Env → List Env)
    (live : World → Key → List Row) (query : Query Key Pattern) (watched : List Key)
    (coverage : ∀ key ∈ laterDependencies query, key ∈ watched) (env : Env) (opened : World) :
    stream matchRow (fun world => journal watched (live opened) (live world)) query env opened =
      Search.superpose (evaluate matchRow (live opened) query env) opened := by
  apply stream_entry_at_open
  · intro key _
    simp [journal]
  · intro world key member
    simp [journal, coverage key member]

/-- A native implementation can combine pinned atomic readers and journals;
the theorem requires their union to cover every possible later read. -/
theorem pinned_or_journaled_entry (matchRow : Pattern → Row → Env → List Env)
    (entry : Key → List Row) (pinned journaled : Key → Prop)
    (readRows : World → Key → List Row) (query : Query Key Pattern)
    (coverage : ∀ key ∈ dependencies query, pinned key ∨ journaled key)
    (pinLaw : ∀ key, pinned key → ∀ world, readRows world key = entry key)
    (journalLaw : ∀ key, journaled key → ∀ world, readRows world key = entry key)
    (env : Env) :
    stream matchRow readRows query env = Search.superpose (evaluate matchRow entry query env) := by
  apply stream_entry
  intro world key member
  rcases coverage key member with retained | watched
  · exact pinLaw key retained world
  · exact journalLaw key watched world

theorem seq_associative (matchRow : Pattern → Row → Env → List Env)
    (entry : Key → List Row) (first second third : Query Key Pattern) (env : Env) :
    evaluate matchRow entry (.seq (.seq first second) third) env =
      evaluate matchRow entry (.seq first (.seq second third)) env := by
  simp [evaluate, List.flatMap_assoc]

theorem union_dependencies (first second : Query Key Pattern) (key : Key) :
    key ∈ dependencies (.union first second) ↔
      key ∈ dependencies first ∨ key ∈ dependencies second := by
  simp [dependencies]

end Mettapedia.Machines.Cursor.EntryQueryTree
