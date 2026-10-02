import Mettapedia.GSLT.LanguageDef.NativeControlOutcomeCursor
import Mettapedia.GSLT.LanguageDef.CommittedFallbackFusion
import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Revisioned facts at the live query-cursor boundary

An admitted pure query may reuse immutable facts and materialize its ordered
answers separately for each invocation. The residual retains those answers,
not a pointer to an invalidatable cache entry. A new invocation selects its
stamp from the current world. Unqualified queries continue through the
supplied relational cursor, retaining faults, suspension, effects and order.

The cached provider is implemented independently of the uncached provider.
Forgetting its private cache is a proved polynomial-provider homomorphism.
Consequently all existing bounded cursor clients observe identical replies.
Pure empty/singleton results also discharge the existing committed-fallback
fusion admission, including its uniform residual law after consumer mutation.

`Factorization` is a required pure-service boundary, not a claim that arbitrary
authored classifiers or open-term refinements already satisfy it. Cache
validation, native allocation and concrete dialect admission remain distinct
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RevisionedFactCursor

open HostCalls (Pull)
open Mettapedia.Machines
open RevisionedQueryFacts
open NativeControlOutcomeCursor (mapPull mapOutcome provider)

variable {World Query Stamp Key Fact Answer Live Fault : Type}
variable [DecidableEq Stamp] [DecidableEq Key]

inductive Cursor (Query Answer Live : Type) where
  | pure (query : Query)
  | retained (answers : List Answer)
  | relational (cursor : Live)
  deriving Repr

def emit : List Answer → Pull (Cursor Query Answer Live) Answer
  | [] => .done
  | answer :: answers => .yield answer (.retained answers)

def sourcePull (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer)) :
    Cursor Query Answer Live → World →
      World × Except Fault (Pull (Cursor Query Answer Live) Answer)
  | .pure query, world => (world, .ok (emit (materialize query (admission.service world query))))
  | .retained answers, world => (world, .ok (emit answers))
  | .relational cursor, world =>
      let result := relational cursor world
      (result.1, mapOutcome .relational result.2)

structure Cached (admission : Factorization World Query Stamp Key Fact)
    (Answer Live : Type) where
  cursor : Cursor Query Answer Live
  cache : Cache Stamp Key Fact
  valid : Valid admission.compute cache

def initial (admission : Factorization World Query Stamp Key Fact)
    (cursor : Cursor Query Answer Live) : Cached admission Answer Live :=
  ⟨cursor, [], valid_nil admission.compute⟩

def targetPull (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    (state : Cached admission Answer Live) (world : World) :
    World × Except Fault (Pull (Cached admission Answer Live) Answer) :=
  match state.cursor with
  | .pure query =>
      let filled := request admission.compute
        ⟨admission.stamp world query, admission.key world query⟩ state.cache
      let valid := request_valid admission.compute _ state.cache state.valid
      (world, mapOutcome (fun cursor => ⟨cursor, filled.cache, valid⟩)
        (.ok (emit (materialize query filled.facts))))
  | .retained answers =>
      (world, mapOutcome (fun cursor => ⟨cursor, state.cache, state.valid⟩)
        (.ok (emit answers)))
  | .relational cursor =>
      let result := relational cursor world
      (result.1, mapOutcome (fun cursor => ⟨.relational cursor, state.cache, state.valid⟩)
        result.2)

theorem mapOutcome_comp {First Second Third : Type}
    (first : First → Second) (second : Second → Third)
    (reply : Except Fault (Pull First Answer)) :
    mapOutcome second (mapOutcome first reply) =
      mapOutcome (second ∘ first) reply := by
  cases reply with
  | error error => rfl
  | ok response => cases response <;> rfl

theorem cache_forgetting_exact (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    (state : Cached admission Answer Live) (world : World) :
    sourcePull admission materialize relational state.cursor world =
      ((targetPull admission materialize relational state world).1,
        mapOutcome Cached.cursor (targetPull admission materialize relational state world).2) := by
  cases cursorEq : state.cursor with
  | pure query =>
      have facts := request_exact admission.compute
        ⟨admission.stamp world query, admission.key world query⟩ state.cache state.valid
      rw [← admission.correct world query] at facts
      simp [targetPull, sourcePull, cursorEq, mapOutcome_comp, facts]
      cases materialize query (admission.service world query) <;> rfl
  | retained answers =>
      simp [targetPull, sourcePull, cursorEq, mapOutcome_comp]
      cases answers <;> rfl
  | relational cursor =>
      simp [targetPull, sourcePull, cursorEq, mapOutcome_comp, Function.comp_def]

/-- The direction is implementation to specification: a cache cannot invent
a reply. Every source entry is covered by `initial` with an empty valid cache. -/
def refinement (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer)) :=
  NativeControlOutcomeCursor.hom (targetPull admission materialize relational)
    (sourcePull admission materialize relational) Cached.cursor
    (cache_forgetting_exact admission materialize relational)

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem entries_covered (admission : Factorization World Query Stamp Key Fact)
    (cursor : Cursor Query Answer Live) : (initial admission cursor).cursor = cursor := rfl

/-- All outcome-sensitive clients are retained by the existing protocol
theorem, not just clients collecting successful values. -/
theorem clients_exact (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    {Return : (base : Unit) → Unit → Type}
    (client : Mettapedia.Machines.Cursor.Client
      (P := NativeControlOutcomeCursor.protocol Answer Fault) (Return := Return))
    (targetCharge : Mettapedia.Machines.Cursor.Charge
      (provider (targetPull admission materialize relational)))
    (sourceCharge : Mettapedia.Machines.Cursor.Charge
      (provider (sourcePull admission materialize relational)))
    (budget : Nat)
    (packet : Mettapedia.Machines.Cursor.Packet
      (provider (targetPull admission materialize relational)) client ()) :
    (refinement admission materialize relational).outcome client
        (Mettapedia.Machines.Cursor.advance _ client targetCharge budget packet).2 =
      (Mettapedia.Machines.Cursor.advance _ client sourceCharge budget
        ((refinement admission materialize relational).packet client packet)).2 :=
  NativeControlOutcomeCursor.clients_preserved _ _ Cached.cursor
    (cache_forgetting_exact admission materialize relational)
    client targetCharge sourceCharge budget packet

def queries (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    (fallback : Cursor Query Answer Live → World →
      World × Except Fault (Pull (Cursor Query Answer Live) Answer))
    (startFallback : World → Cursor Query Answer Live) :
    CommittedFallback.Queries (Cursor Query Answer Live) Answer World Fault :=
  ⟨sourcePull admission materialize relational, fallback, startFallback⟩

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem empty_admits_fusion (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    (fallback : Cursor Query Answer Live → World →
      World × Except Fault (Pull (Cursor Query Answer Live) Answer))
    (startFallback : World → Cursor Query Answer Live) (query : Query) (world : World)
    (empty : materialize query (admission.service world query) = []) :
    CommittedFallbackFusion.Admitted
      (queries admission materialize relational fallback startFallback) (.pure query) world none := by
  simp [CommittedFallbackFusion.Admitted, queries, sourcePull, empty, emit]

omit [DecidableEq Stamp] [DecidableEq Key] in
theorem singleton_admits_fusion (admission : Factorization World Query Stamp Key Fact)
    (materialize : Query → List Fact → List Answer)
    (relational : Live → World → World × Except Fault (Pull Live Answer))
    (fallback : Cursor Query Answer Live → World →
      World × Except Fault (Pull (Cursor Query Answer Live) Answer))
    (startFallback : World → Cursor Query Answer Live) (query : Query) (world : World)
    (answer : Answer) (single : materialize query (admission.service world query) = [answer]) :
    CommittedFallbackFusion.Admitted
      (queries admission materialize relational fallback startFallback)
      (.pure query) world (some answer) := by
  refine ⟨.retained [], ?_, ?_⟩
  · simp [queries, sourcePull, single, emit]
  · intro laterWorld
    rfl

namespace Controls

def admission : Factorization Nat Nat Nat Nat Nat :=
  ⟨fun world _ => world, fun _ query => query,
    fun stamp key => [stamp + key, stamp + key],
    fun world query => [world + query, world + query], fun _ _ => rfl⟩

def materialize (activation : Nat) (facts : List Nat) : List (Nat × Nat) :=
  facts.map (fun fact => (activation, fact))

def ordinary (cursor world : Nat) : Nat × Except String (Pull Nat (Nat × Nat)) :=
  (world + 1, .ok (.suspend (cursor + 1)))

theorem duplicates_remain_in_the_residual :
    (sourcePull admission materialize ordinary (.pure 3) 1).2 =
      .ok (.yield (3, 4) (.retained [(3, 4)])) := rfl

theorem old_residual_survives_consumer_revision_change :
    sourcePull admission materialize ordinary (.retained [(3, 4)]) 9 =
      (9, .ok (.yield (3, 4) (.retained []))) := rfl

theorem new_invocation_uses_current_revision :
    (sourcePull admission materialize ordinary (.pure 3) 9).2 =
      .ok (.yield (3, 12) (.retained [(3, 12)])) := rfl

theorem facts_materialize_per_activation :
    materialize 3 [7] ≠ materialize 4 [7] := by decide

theorem relational_suspension_and_effect_are_not_cached :
    sourcePull admission materialize ordinary (.relational 0) 1 =
      (2, .ok (.suspend (.relational 1))) := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.RevisionedFactCursor
