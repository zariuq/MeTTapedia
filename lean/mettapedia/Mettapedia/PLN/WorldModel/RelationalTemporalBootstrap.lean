import Mettapedia.PLN.WorldModel.PredictiveBootstrap
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup

/-!
# Relational and temporal proposals for conditional prediction

A proposal tests several past observations at one object, or asks whether
one related object satisfies all of them. Relation lookup supplies the
complete neighbor list at the forecast cutoff. Missing signal values remain
a distinct predictive context.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.RelationalTemporalBootstrap

open PredictiveBootstrap

structure Forecast (Entity : Type*) where
  subject : Entity
  period : Nat
  deriving DecidableEq

structure History (Entity Relation Signal : Type*) where
  neighbors : Relation → Entity → Nat → List Entity
  value : Signal → Entity → Nat → Option Bool

structure Probe (Signal : Type*) where
  signal : Signal
  /-- Zero reads the immediately preceding period. -/
  lookback : Nat
  deriving DecidableEq

inductive Feature (Relation Signal : Type*) where
  | onSubject (probes : List (Probe Signal))
  | related (relation : Relation) (probes : List (Probe Signal))
  deriving DecidableEq

variable {Entity Relation Signal : Type*}

def Probe.read (probe : Probe Signal) (history : History Entity Relation Signal) (entity : Entity)
    (period : Nat) : Option Bool :=
  if probe.lookback + 1 ≤ period then
    history.value probe.signal entity (period - (probe.lookback + 1))
  else none

theorem Probe.read_congr_past (probe : Probe Signal) (first second : History Entity Relation Signal)
    (entity : Entity) (period : Nat)
    (past : ∀ signal subject time, time < period → first.value signal subject time =
      second.value signal subject time) :
    probe.read first entity period = probe.read second entity period := by
  unfold read
  split
  · apply past
    omega
  · rfl

private def allObserved {α : Type*} (checks : List α) (read : α → Option Bool) : Option Bool :=
  checks.foldr (fun check tail =>
    match read check, tail with
    | some false, _ | _, some false => some false
    | some true, value => value
    | _, _ => none) (some true)

def Feature.read (feature : Feature Relation Signal) (history : History Entity Relation Signal)
    (query : Forecast Entity) : Option Bool :=
  let inspect := fun entity probes =>
    allObserved probes fun probe => (probe : Probe Signal).read history entity query.period
  match feature with
  | .onSubject probes => inspect query.subject probes
  | .related relation probes =>
    let candidates := history.neighbors relation query.subject (query.period - 1)
    if query.period = 0 then none else
      (allObserved candidates (fun entity => (inspect entity probes).map Bool.not)).map Bool.not

theorem Feature.read_congr_past (feature : Feature Relation Signal)
    (first second : History Entity Relation Signal) (query : Forecast Entity)
    (links : ∀ relation subject time, time < query.period → first.neighbors relation subject time =
      second.neighbors relation subject time)
    (past : ∀ signal subject time, time < query.period → first.value signal subject time =
      second.value signal subject time) :
    feature.read first query = feature.read second query := by
  have same (entity : Entity) :
      (fun probe : Probe Signal => probe.read first entity query.period) =
      (fun probe : Probe Signal => probe.read second entity query.period) :=
    funext fun probe => probe.read_congr_past first second entity query.period past
  cases feature with
  | onSubject probes => simp only [Feature.read, same]
  | related relation probes =>
    simp only [Feature.read, same]
    split
    · rfl
    · rw [links relation query.subject _ (by omega)]

/-- Enumerate conjunctions up to the requested size. Related probes in
each body share a witness. -/
def proposals [DecidableEq Signal] [DecidableEq Relation] (signals : List Signal)
    (lookbacks : List Nat) (relations : List Relation) (maxBody : Nat) : List (Feature Relation Signal) :=
  let probes := signals.dedup.flatMap fun signal => lookbacks.dedup.map (Probe.mk signal)
  let bodies := (List.range maxBody).flatMap fun preceding => probes.sublistsLen (preceding + 1)
  bodies.map Feature.onSubject ++ relations.dedup.flatMap fun relation => bodies.map (Feature.related relation)

def Feature.partition (feature : Feature Relation Signal) (history : History Entity Relation Signal)
    (prior : ℚ) (positive : 0 < prior) : Candidate (Forecast Entity) :=
  ⟨3, fun input =>
    match feature.read history input with
    | some false => 0
    | some true => 1
    | none => 2,
    prior, positive⟩

end Mettapedia.PLN.WorldModel.RelationalTemporalBootstrap
