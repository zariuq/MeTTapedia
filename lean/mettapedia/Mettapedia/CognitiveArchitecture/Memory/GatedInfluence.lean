import Mettapedia.CognitiveArchitecture.Memory.GateEvidence

/-!
# Influence through a gate: how a gated store's contents are accounted for

Some memory designs, such as OpenClaw's memory core, keep a curated store that
notes reach through a promotion gate. This file describes that external
pattern as information flow, following non-interference (Goguen and Meseguer
1982) in its intransitive form (Rushby 1992), where a gate acts as a
declassifier.

**What this file is.** It is descriptive mathematics. It neither recommends
nor requires anything of any agent. In godelclaw, agents keep full write
authority over their own memory, prompts, timers and instructions, and
nothing here constrains that.

Model: notes from principals, direct edits, and a gate that promotes a text
when enough distinct principals support it (`GateEvidence`).

Results:
* The curated store is a function of the direct edits, the gate's invocations
  and the gate's decisions. Notes affect it only through those decisions
  (`curated_determined_by_decisions`).
* When notes can also be written straight into the store, the gate's
  decisions no longer account for its contents
  (`second_channel_needs_its_own_record`).
* Under a gate counting at least two principals, one principal alone never
  triggers a promotion (`one_principal_no_promotion`). A pivotal principal
  does (`pivotal_principal_changes_curated`). A principal's influence on a
  quorum is exactly its pivotality.
-/

namespace Mettapedia.CognitiveArchitecture.Memory.GatedInfluence

open Mettapedia.CognitiveArchitecture.Memory.GateEvidence

inductive Act where
  /-- Principal `p`'s agent writes an episodic note saying `t`. -/
  | note (p t : Nat)
  /-- A human writes `t` into the curated tier. -/
  | edit (t : Nat)
  /-- The gate is asked to promote `t`. -/
  | promote (t : Nat)
  deriving DecidableEq, Repr

structure State where
  episodic : List (Nat × Nat)
  curated : List Nat
  deriving DecidableEq, Repr

/-- The principals whose notes say `t`. -/
def supporters (s : State) (t : Nat) : List Nat :=
  (s.episodic.filter (fun e => e.2 == t)).map Prod.fst

/-- Run a trace, recording each gate decision in order. -/
def run (k : Nat) : State → List Act → State × List Bool
  | s, [] => (s, [])
  | s, Act.note p t :: rest => run k { s with episodic := (p, t) :: s.episodic } rest
  | s, Act.edit t :: rest => run k { s with curated := t :: s.curated } rest
  | s, Act.promote t :: rest =>
    let ok := decide (k ≤ (distinct (supporters s t)).length)
    let next := run k (if ok then { s with curated := t :: s.curated } else s) rest
    (next.1, ok :: next.2)

/-- Rebuild the curated tier from edits, gate invocations and the gate's
decisions alone. Notes are ignored. -/
def replay : List Nat → List Act → List Bool → List Nat
  | cur, [], _ => cur
  | cur, Act.note _ _ :: rest, ds => replay cur rest ds
  | cur, Act.edit t :: rest, ds => replay (t :: cur) rest ds
  | cur, Act.promote t :: rest, d :: ds => replay (if d then t :: cur else cur) rest ds
  | cur, Act.promote _ :: rest, [] => replay cur rest []

/-- The gate is the only channel: the curated tier is determined by the
edits, the gate invocations and the gate's decisions. -/
theorem curated_determined_by_decisions (k : Nat) (s : State) (acts : List Act) :
    (run k s acts).1.curated = replay s.curated acts (run k s acts).2 := by
  induction acts generalizing s with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | note p t => exact ih _
    | edit t => exact ih _
    | promote t =>
      by_cases ok : k ≤ (distinct (supporters s t)).length
      · simp only [run, ok, decide_true, if_true, replay]
        exact ih _
      · simp only [run, ok, decide_false, Bool.false_eq_true, if_false, replay]
        exact ih _

/-! ## A design with a second, direct channel -/

inductive Act' where
  | note (p t : Nat)
  | edit (t : Nat)
  | promote (t : Nat)
  /-- A direct write into the curated store, a second channel. -/
  | curate (p t : Nat)
  deriving DecidableEq, Repr

def run' (k : Nat) : State → List Act' → State × List Bool
  | s, [] => (s, [])
  | s, Act'.note p t :: rest => run' k { s with episodic := (p, t) :: s.episodic } rest
  | s, Act'.edit t :: rest => run' k { s with curated := t :: s.curated } rest
  | s, Act'.curate _ t :: rest => run' k { s with curated := t :: s.curated } rest
  | s, Act'.promote t :: rest =>
    let ok := decide (k ≤ (distinct (supporters s t)).length)
    let next := run' k (if ok then { s with curated := t :: s.curated } else s) rest
    (next.1, ok :: next.2)

/-- The edits and gate invocations of a trace; other actions dropped. -/
def skeleton : List Act' → List Act'
  | [] => []
  | Act'.edit t :: rest => Act'.edit t :: skeleton rest
  | Act'.promote t :: rest => Act'.promote t :: skeleton rest
  | _ :: rest => skeleton rest

/-- Two traces with the same skeleton and the same gate decisions, yet
different curated stores: the gate's record no longer accounts for them. -/
theorem second_channel_needs_its_own_record :
    let a := [Act'.curate 1 5]
    let b : List Act' := []
    skeleton a = skeleton b ∧ (run' 2 ⟨[], []⟩ a).2 = (run' 2 ⟨[], []⟩ b).2 ∧
      (run' 2 ⟨[], []⟩ a).1.curated ≠ (run' 2 ⟨[], []⟩ b).1.curated := by
  decide

/-! ## What a single principal can do -/

def OnlyBy (p : Nat) (s : State) : Prop := ∀ e ∈ s.episodic, e.1 = p

def notesBy (p : Nat) : List Act → Prop
  | [] => True
  | Act.note q _ :: rest => q = p ∧ notesBy p rest
  | _ :: rest => notesBy p rest

/-- If every note comes from one principal, a gate counting at least two
principals refuses every promotion. -/
theorem one_principal_no_promotion (k p : Nat) (hk : 2 ≤ k) (s : State) (acts : List Act)
    (hs : OnlyBy p s) (ha : notesBy p acts) :
    ∀ d ∈ (run k s acts).2, d = false := by
  induction acts generalizing s with
  | nil => simp [run]
  | cons a rest ih =>
    cases a with
    | note q t =>
      obtain ⟨rfl, hrest⟩ := ha
      apply ih _ _ hrest
      intro e he
      simp at he
      rcases he with rfl | he
      · rfl
      · exact hs e he
    | edit t => exact ih _ hs ha
    | promote t =>
      have all : ∀ x ∈ supporters s t, x = p := by
        intro x hx
        simp only [supporters, List.mem_map, List.mem_filter] at hx
        obtain ⟨e, ⟨he, _⟩, rfl⟩ := hx
        exact hs e he
      have hlen := distinct_length_le_one all
      have notok : ¬ k ≤ (distinct (supporters s t)).length := by omega
      simp only [run, notok, decide_false, Bool.false_eq_true, if_false]
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · rfl
      · exact ih s hs ha d hd

/-- Removing a pivotal principal's notes removes the promotion. -/
theorem pivotal_principal_changes_curated :
    (run 2 ⟨[], []⟩ [Act.note 1 7, Act.note 2 7, Act.promote 7]).1.curated = [7] ∧
      (run 2 ⟨[], []⟩ [Act.note 1 7, Act.promote 7]).1.curated = [] ∧
      (run 2 ⟨[], []⟩ [Act.note 2 7, Act.promote 7]).1.curated = [] := by
  decide

#print axioms curated_determined_by_decisions
#print axioms second_channel_needs_its_own_record
#print axioms one_principal_no_promotion
#print axioms pivotal_principal_changes_curated

end Mettapedia.CognitiveArchitecture.Memory.GatedInfluence
