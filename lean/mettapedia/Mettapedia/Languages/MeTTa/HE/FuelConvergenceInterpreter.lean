/-
# Fuel convergence, applied to LeaTTa's `interpretFuel`

`Mettapedia.Languages.MeTTa.HE.FuelConvergence` supplies the abstract notion
that replaces the FALSE "more fuel yields a superset" monotonicity: a
fuel-indexed family is well behaved when it is eventually constant
(`StableFrom` / `Converges`).  This module instantiates that abstraction at
the concrete driver `Metta.Minimal.interpretFuel`.

Why the abstraction is needed here at all is visible in the driver's two exit
arms:

* `| _, [] => (done.reverse.filter (fun p => p.1 != emptyA), st)` — with an
  EMPTY work queue the answer does not mention `fuel`, so every fuel value
  agrees;
* `| 0, w => ...exhaustedPair...` — with a NON-empty queue and no fuel the
  unfinished items are REPLACED by `StackOverflow` pairs, which a larger
  budget overwrites with real results.

The second arm is exactly the shape recorded abstractly by
`FuelConvergence.inclusion_monotonicity_fails`, and it is reproduced here as a
concrete negative witness on the real evaluator
(`interpretFuel_not_stableFrom_zero_of_pending`), so the empty-queue theorems
below cannot be mistaken for a general monotonicity statement.

## How far the positive results reach

Beyond the empty queue there is one genuinely fuel-free family of queues: a
queue whose items are all FINISHED (`isFinal`).  On those `interpretStack1`
returns the item unchanged without consulting its own fuel, so the whole run
is fuel-independent (`interpretFuel_allFinal`).  That is a non-vacuous
non-empty-queue convergence theorem, and it is proved rather than assumed.

## The remaining gap, and why it is a gap

One would like "if the queue empties at fuel `N` then the family is stable
from `N`".  That is not provable, and it is not merely hard: the recursive
call is

    interpretFuel env (f+1) st (it :: rest) done
      = interpretFuel env f st' (more ++ rest) (finals.reverse ++ done)
      where (results, st') := interpretStack1 env f st it

so the per-item step itself receives `f` as its own fuel and passes it on to
nested evaluation (`mettaEval`, `getTypes`, `importSelfFuel`, ...).  Raising
the initial budget therefore raises the budget of every intermediate step as
well; this is not a fuel-independent transition system with a counter bolted
on.  Consequently "the queue empties at one budget" says nothing by itself
about the trace at a larger budget, and any lemma claiming otherwise would be
false.

What IS provable is the induction step such an argument needs, with the
per-step fuel-insensitivity assumption made explicit:
`stableFrom_cons_of_step` says that if the FIRST step's output is the same at
every budget at or above `bound`, and the continuation is stable from `bound`,
then the whole run is stable from `bound + 1`.  Discharging its first
hypothesis for arbitrary items is the work that remains; it is carried as a
hypothesis here instead of being smuggled in as a lemma.
`converges_interpretFuel_pending` discharges it for a concrete unfinished
item, so the step lemma is demonstrably usable and not merely well typed.
-/
import Mettapedia.Languages.MeTTa.HE.FuelConvergence
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution

namespace Mettapedia.Languages.MeTTa.HE.FuelConvergenceInterpreter

open Mettapedia.Languages.MeTTa.HE.FuelConvergence
open Metta (Atom Bindings)
open Metta.Minimal

/-! ## 1. The driver's arms, spelled out

These three lemmas are the only place where `interpretFuel` is unfolded.
Everything below reasons from them, which keeps the fuel bookkeeping visible
instead of hidden inside `simp` calls. -/

/-- With an EMPTY work queue the driver takes the `| _, []` arm, whose right
hand side never mentions `fuel`.  This is the source of every convergence
result in this file. -/
theorem interpretFuel_nil (env : MinEnv) (fuel : Nat) (st : St)
    (done : List (Atom × Bindings)) :
    interpretFuel env fuel st [] done
      = (done.reverse.filter (fun p => p.1 != emptyA), st) := by
  cases fuel <;> simp [interpretFuel]

/-- The fuel-zero arm on a NON-empty queue: unfinished items are replaced by
`exhaustedPair`, which is why extra fuel overwrites rather than extends. -/
theorem interpretFuel_zero_cons (env : MinEnv) (st : St) (it : Item)
    (rest : List Item) (done : List (Atom × Bindings)) :
    interpretFuel env 0 st (it :: rest) done
      = ((done.reverse ++ (it :: rest).map
            (fun i => if isFinal i then finalPair i else exhaustedPair i)).filter
            (fun p => p.1 != emptyA),
         st) := by
  rw [interpretFuel]
  simp

/-- The successor arm: the step's own budget is `f`, one less than the
driver's, and it is threaded into the step.  This is precisely why raising the
initial budget perturbs the whole trace instead of merely extending it. -/
theorem interpretFuel_succ (env : MinEnv) (f : Nat) (st : St) (it : Item)
    (rest : List Item) (done : List (Atom × Bindings)) :
    interpretFuel env (f + 1) st (it :: rest) done
      = interpretFuel env f (interpretStack1 env f st it).2
          (((interpretStack1 env f st it).1.filter (fun r => !isFinal r)) ++ rest)
          ((((interpretStack1 env f st it).1.filter isFinal).map finalPair).reverse
            ++ done) := by
  rw [interpretFuel]

/-- The successor arm with the step's outcome already named, which is the form
every proof below actually consumes. -/
theorem interpretFuel_succ_of (env : MinEnv) (f : Nat) (st st' : St) (it : Item)
    (rest results : List Item) (done : List (Atom × Bindings))
    (h : interpretStack1 env f st it = (results, st')) :
    interpretFuel env (f + 1) st (it :: rest) done
      = interpretFuel env f st' ((results.filter (fun r => !isFinal r)) ++ rest)
          (((results.filter isFinal).map finalPair).reverse ++ done) := by
  rw [interpretFuel_succ, h]

/-! ## 2. An empty work queue is fuel-independent -/

/-- Any two fuel budgets agree once the queue is empty. -/
theorem interpretFuel_nil_fuel_independent (env : MinEnv) (m n : Nat) (st : St)
    (done : List (Atom × Bindings)) :
    interpretFuel env m st [] done = interpretFuel env n st [] done := by
  rw [interpretFuel_nil, interpretFuel_nil]

/-- The empty-queue family is stable from budget `0` — the strongest possible
form of the abstract `StableFrom`. -/
theorem stableFrom_interpretFuel_nil (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) :
    StableFrom (fun n => interpretFuel env n st [] done) 0 :=
  fun n _ => interpretFuel_nil_fuel_independent env n 0 st done

/-- The finished-evaluation case of the completeness argument, stated with the
shared `Converges` so it composes with `StableFrom.mono`, `StableFrom.pair`
and `Converges.map`. -/
theorem converges_interpretFuel_nil (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) :
    Converges (fun n => interpretFuel env n st [] done) :=
  ⟨0, stableFrom_interpretFuel_nil env st done⟩

/-! ## 3. Readouts of a convergent family converge

The completeness induction never consumes the raw `List (Atom × Bindings) × St`
pair; it consumes projections of it (the result list, the atoms, the threaded
state).  `Converges.map` transports stability along any such readout at the
same budget. -/

/-- Every readout of the finished-evaluation family converges. -/
theorem converges_interpretFuel_nil_readout {β : Type _} (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) (k : List (Atom × Bindings) × St → β) :
    Converges (fun n => k (interpretFuel env n st [] done)) :=
  (converges_interpretFuel_nil env st done).map k

/-- The result-list readout (`Prod.fst`) converges. -/
theorem converges_interpretFuel_nil_results (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) :
    Converges (fun n => (interpretFuel env n st [] done).1) :=
  converges_interpretFuel_nil_readout env st done Prod.fst

/-- The threaded-state readout converges. -/
theorem converges_interpretFuel_nil_state (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) :
    Converges (fun n => (interpretFuel env n st [] done).2) :=
  converges_interpretFuel_nil_readout env st done Prod.snd

/-- The user-visible atoms readout (bindings dropped) converges. -/
theorem converges_interpretFuel_nil_atoms (env : MinEnv) (st : St)
    (done : List (Atom × Bindings)) :
    Converges (fun n => (interpretFuel env n st [] done).1.map Prod.fst) :=
  converges_interpretFuel_nil_readout env st done (fun r => r.1.map Prod.fst)

/-- Two independent finished evaluations converge at one common budget: the
`max` step of the completeness induction, instantiated. -/
theorem converges_interpretFuel_nil_pair (env₁ env₂ : MinEnv) (st₁ st₂ : St)
    (done₁ done₂ : List (Atom × Bindings)) :
    Converges (fun n =>
      (interpretFuel env₁ n st₁ [] done₁, interpretFuel env₂ n st₂ [] done₂)) :=
  (converges_interpretFuel_nil env₁ st₁ done₁).pair
    (converges_interpretFuel_nil env₂ st₂ done₂)

/-! ## 4. A NON-empty queue that is still fuel-independent

`isFinal it` holds when `it` is a single finished frame with no parent.  On
such an item `interpretStack1` returns `([it], st)` by the `prev = []` branch,
never reading `fuel`.  A queue made entirely of finished items is therefore
drained identically at every budget — including budget `0`, where the
`| 0, w` arm routes finished items through `finalPair` rather than
`exhaustedPair`.  So the fuel-zero arm is not uniformly destructive, and this
yields a genuine non-empty-queue convergence theorem. -/

/-- A finished item is returned unchanged by one interpreter step, at any
budget. -/
theorem interpretStack1_of_isFinal (env : MinEnv) (f : Nat) (st : St) (it : Item)
    (hit : isFinal it = true) : interpretStack1 env f st it = ([it], st) := by
  obtain ⟨stack, bnd⟩ := it
  match stack, hit with
  | [fr], hit =>
      have hfin : fr.fin = true := by simpa [isFinal] using hit
      simp [interpretStack1, hfin]

/-- A queue of finished items is drained fuel-independently. -/
theorem interpretFuel_allFinal (env : MinEnv) :
    ∀ (work : List Item), (∀ it ∈ work, isFinal it = true) →
      ∀ (fuel : Nat) (st : St) (done : List (Atom × Bindings)),
        interpretFuel env fuel st work done
          = ((done.reverse ++ work.map finalPair).filter (fun p => p.1 != emptyA), st)
  | [], _, fuel, st, done => by
      rw [interpretFuel_nil]; simp
  | it :: rest, hall, fuel, st, done => by
      have hit : isFinal it = true := hall it (by simp)
      have hrest : ∀ j ∈ rest, isFinal j = true := fun j hj => hall j (by simp [hj])
      cases fuel with
      | zero =>
          rw [interpretFuel_zero_cons]
          have hmap : (it :: rest).map
              (fun i => if isFinal i then finalPair i else exhaustedPair i)
              = (it :: rest).map finalPair := by
            apply List.map_congr_left
            intro j hj
            simp [hall j hj]
          rw [hmap]
      | succ f =>
          rw [interpretFuel_succ_of env f st st it rest [it] done
                (interpretStack1_of_isFinal env f st it hit)]
          have h1 : ([it] : List Item).filter (fun r => !isFinal r) = [] := by
            simp [hit]
          have h2 : ([it] : List Item).filter isFinal = [it] := by simp [hit]
          rw [h1, h2]
          simp only [List.map_cons, List.map_nil, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.cons_append]
          rw [interpretFuel_allFinal env rest hrest f st (finalPair it :: done)]
          simp

/-- Stability from budget `0` for a finished queue. -/
theorem stableFrom_interpretFuel_allFinal (env : MinEnv) (work : List Item)
    (hall : ∀ it ∈ work, isFinal it = true) (st : St)
    (done : List (Atom × Bindings)) :
    StableFrom (fun n => interpretFuel env n st work done) 0 := by
  intro n _
  show interpretFuel env n st work done = interpretFuel env 0 st work done
  rw [interpretFuel_allFinal env work hall n st done,
      interpretFuel_allFinal env work hall 0 st done]

/-- A non-empty queue CAN converge: a finished queue does, at budget `0`. -/
theorem converges_interpretFuel_allFinal (env : MinEnv) (work : List Item)
    (hall : ∀ it ∈ work, isFinal it = true) (st : St)
    (done : List (Atom × Bindings)) :
    Converges (fun n => interpretFuel env n st work done) :=
  ⟨0, stableFrom_interpretFuel_allFinal env work hall st done⟩

/-! ## 5. Negative witnesses

A convergence predicate that accepted every queue at every budget would be
worthless.  The witnesses below show the notion has teeth on the real
evaluator: an unfinished item is fuel sensitive, so its family is NOT stable
from `0`, and the fuel-zero result is not contained in the fuel-one result. -/

/-- The witness environment: no equalities and no grounded operations, so the
step below is decided purely by the driver's structural arms. -/
def witnessEnv : MinEnv := MinEnv.ofAtomsGT [] []

/-- The witness queue holds one UNFINISHED frame carrying the inert symbol
`a`. -/
def pendingItem : Item :=
  { stack := [{ atom := Atom.sym "a", fin := false }], bnd := [] }

/-- The result of one step on `pendingItem`: the same frame, now marked
finished. -/
def pendingFinished : Item :=
  { stack := [{ atom := Atom.sym "a", fin := true }], bnd := [] }

/-- The witness item is genuinely unfinished, so it lies outside the reach of
`interpretFuel_allFinal`. -/
theorem pendingItem_not_isFinal : isFinal pendingItem = false := rfl

/-- Its one-step successor, by contrast, is finished. -/
theorem pendingFinished_isFinal : isFinal pendingFinished = true := rfl

/-- One step marks the pending frame finished, at any budget: the step itself
is fuel-free even though the item is not finished yet. -/
theorem interpretStack1_pendingItem (f : Nat) :
    interpretStack1 witnessEnv f St.init pendingItem
      = ([pendingFinished], St.init) := by
  simp [interpretStack1, pendingItem, pendingFinished, isEmbeddedOp]

/-- At budget `0` the unfinished frame is surfaced as a `StackOverflow`
error. -/
theorem interpretFuel_pending_zero :
    (interpretFuel witnessEnv 0 St.init [pendingItem] []).1
      = [(Atom.expr [Atom.sym "Error", Atom.sym "a", Atom.sym "StackOverflow"], [])] := by
  rw [interpretFuel_zero_cons]
  simp [pendingItem, isFinal, exhaustedPair, emptyA, Metta.instantiate_nil]
  rfl

/-- At budget `1` the very same frame is finished and yields the atom itself:
the earlier `StackOverflow` was REPLACED, not extended. -/
theorem interpretFuel_pending_one :
    (interpretFuel witnessEnv 1 St.init [pendingItem] []).1
      = [(Atom.sym "a", [])] := by
  rw [interpretFuel_succ_of witnessEnv 0 St.init St.init pendingItem []
        [pendingFinished] [] (interpretStack1_pendingItem 0),
      interpretFuel_allFinal witnessEnv _ (by simp [pendingFinished_isFinal]) 0 St.init _]
  simp [pendingFinished, isFinal, finalPair, emptyA, Metta.instantiate_nil]
  rfl

/-- Fuel is observable on an unfinished queue: budgets `0` and `1` disagree. -/
theorem interpretFuel_pending_fuel_sensitive :
    (interpretFuel witnessEnv 0 St.init [pendingItem] []).1
      ≠ (interpretFuel witnessEnv 1 St.init [pendingItem] []).1 := by
  rw [interpretFuel_pending_zero, interpretFuel_pending_one]
  simp

/-- The concrete counterpart of the abstract
`FuelConvergence.inclusion_monotonicity_fails`: on the real evaluator the
`StackOverflow` result present at budget `0` is absent at budget `1`. -/
theorem interpretFuel_inclusion_monotonicity_fails :
    ¬ (∀ p ∈ (interpretFuel witnessEnv 0 St.init [pendingItem] []).1,
        p ∈ (interpretFuel witnessEnv 1 St.init [pendingItem] []).1) := by
  intro h
  have hmem := h (Atom.expr [Atom.sym "Error", Atom.sym "a", Atom.sym "StackOverflow"], [])
    (by rw [interpretFuel_pending_zero]; simp)
  rw [interpretFuel_pending_one] at hmem
  simp at hmem

/-- The family for an unfinished queue is NOT stable from budget `0`, so the
positive theorems above are not instances of a vacuous predicate. -/
theorem interpretFuel_not_stableFrom_zero_of_pending :
    ¬ StableFrom (fun n => interpretFuel witnessEnv n St.init [pendingItem] []) 0 := by
  intro h
  have h1 : interpretFuel witnessEnv 1 St.init [pendingItem] []
      = interpretFuel witnessEnv 0 St.init [pendingItem] [] := h 1 (Nat.zero_le 1)
  exact interpretFuel_pending_fuel_sensitive (congrArg Prod.fst h1).symm

/-! ## 6. How far the general non-empty case gets

The induction step a general convergence proof would need, with the per-step
fuel-insensitivity carried as an explicit hypothesis rather than claimed. -/

/-- The honest induction step for a non-empty queue.

`hstep` states that the FIRST step has already stabilised at `bound`.  It is
exactly the fuel-insensitivity the driver does not supply for free, so it is
required rather than derived.  Given it and stability of the continuation, the
whole run is stable one budget higher. -/
theorem stableFrom_cons_of_step (env : MinEnv) (st st' : St) (it : Item)
    (rest : List Item) (results : List Item) (done : List (Atom × Bindings))
    (bound : Nat)
    (hstep : ∀ f, bound ≤ f → interpretStack1 env f st it = (results, st'))
    (hcont : StableFrom
      (fun n => interpretFuel env n st'
        ((results.filter (fun r => !isFinal r)) ++ rest)
        (((results.filter isFinal).map finalPair).reverse ++ done)) bound) :
    StableFrom (fun n => interpretFuel env n st (it :: rest) done) (bound + 1) := by
  have key : ∀ g, bound ≤ g →
      interpretFuel env (g + 1) st (it :: rest) done
        = interpretFuel env g st'
            ((results.filter (fun r => !isFinal r)) ++ rest)
            (((results.filter isFinal).map finalPair).reverse ++ done) :=
    fun g hg => interpretFuel_succ_of env g st st' it rest results done (hstep g hg)
  intro n hn
  obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  have hf : bound ≤ f := by omega
  show interpretFuel env (f + 1) st (it :: rest) done
      = interpretFuel env (bound + 1) st (it :: rest) done
  rw [key f hf, key bound (Nat.le_refl bound)]
  exact hcont f hf

/-- The `Converges` form of the induction step. -/
theorem converges_cons_of_step (env : MinEnv) (st st' : St) (it : Item)
    (rest : List Item) (results : List Item) (done : List (Atom × Bindings))
    (bound : Nat)
    (hstep : ∀ f, bound ≤ f → interpretStack1 env f st it = (results, st'))
    (hcont : StableFrom
      (fun n => interpretFuel env n st'
        ((results.filter (fun r => !isFinal r)) ++ rest)
        (((results.filter isFinal).map finalPair).reverse ++ done)) bound) :
    Converges (fun n => interpretFuel env n st (it :: rest) done) :=
  ⟨bound + 1,
    stableFrom_cons_of_step env st st' it rest results done bound hstep hcont⟩

/-- A worked instance: the witness item's step is constant from budget `0`
upward and its continuation is a finished queue, so the run converges — from
budget `1`, not budget `0`, exactly as
`interpretFuel_not_stableFrom_zero_of_pending` requires. -/
theorem converges_interpretFuel_pending :
    Converges (fun n => interpretFuel witnessEnv n St.init [pendingItem] []) := by
  exact converges_cons_of_step witnessEnv St.init St.init pendingItem []
    [pendingFinished] [] 0 (fun f _ => interpretStack1_pendingItem f)
    (stableFrom_interpretFuel_allFinal witnessEnv _
      (by simp [pendingFinished_isFinal]) St.init _)

end Mettapedia.Languages.MeTTa.HE.FuelConvergenceInterpreter
