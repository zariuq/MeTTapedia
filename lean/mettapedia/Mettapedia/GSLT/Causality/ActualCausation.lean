import Mettapedia.GSLT.Distinction.CausalGluing

/-!
# Actual causation on footprinted traces

Halpern's modified definition (*Actual Causality*, 2016, Definition 2.2.1) is
stated for an occurrence word of `CausalGluing`. The actual run is a word. An
observation is a predicate on the store that word reaches. A contingency is a
set of occurrences of the actual word. Pinning replays those occurrences'
writes on top of a retained alternative, so the contingency keeps the values
it wrote in the actual run.

`ActualCause` is the three clauses AC1, AC2(aᵐ), and AC3. `ButFor` is the
empty-contingency case. `UnpinnedCause` is the older clause in which a
contingency may take a value other than its actual write.

The retained alternatives of each scenario are its admissible forks. Swapping
independent occurrences preserves the verdict (`final_eq_of_trace`,
`observe_eq_of_trace`). The Mazurkiewicz causal past is a chain of footprint
dependence along the word. A but-for replacement that shares a cell with a
later effect lies in that past. Double prevention is a but-for cause with no
such cell.
-/

set_option autoImplicit false

open Mettapedia.GSLT.Distinction.CausalGluing
open Mettapedia.GSLT.Distinction.CausalGluing.Occurrences

namespace Mettapedia.GSLT.Causality.ActualCausation

/-! ## Pinning, the three clauses, and the unpinned clause -/

section Definitions

variable {Id Cell Value Channel : Type}
variable (O : Occurrences Id Cell Value Channel)

/-- Replay the actual writes selected by `keep`, in their actual order, on `base`. -/
def pinWrites (keep : Id → Bool) : List Id → Store Id Cell Value → Store Id Cell Value
  | [], store => store
  | i :: rest, store =>
      pinWrites keep rest (cond (keep i) (O.apply i store) store)

/-- `Y` draws its members from `X` and misses at least one member of `X`. -/
def ProperSubset (Y X : List Id) : Prop :=
  (∀ i ∈ Y, i ∈ X) ∧ ∃ i, i ∈ X ∧ i ∉ Y

/-- AC1. `X` is a nonempty set of occurrences of the actual word, and φ holds there. -/
def AC1 (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (X : List Id) : Prop :=
  (∃ i, i ∈ X) ∧ (∀ i ∈ X, i ∈ actual) ∧ φ (O.final actual initial)

/-- A retained alternative falsifies φ with no contingency pinned. -/
def ButFor (_actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  ∃ alt, retained X alt ∧ (∀ i ∈ X, i ∉ alt) ∧ ¬ φ (O.final alt initial)

/-- AC2(aᵐ). Some contingency, pinned to the writes it made in the actual word,
and some retained alternative that drops every member of `X`, falsify φ. -/
def AC2 (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  ∃ keep : Id → Bool, ∃ alt : List Id,
    (∀ i, keep i = true → i ∈ actual) ∧
    (∀ i, keep i = true → i ∉ X) ∧
    retained X alt ∧
    (∀ i ∈ X, i ∉ alt) ∧
    ¬ φ (pinWrites O keep actual (O.final alt initial))

/-- AC3. No proper subset of `X` satisfies AC1 and AC2. -/
def AC3 (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  ∀ Y, ProperSubset Y X →
    ¬ (AC1 O actual initial φ Y ∧ AC2 O actual initial φ retained Y)

/-- Definition 2.2.1: AC1, the actual-write pin AC2(aᵐ), and minimality. -/
def ActualCause (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  AC1 O actual initial φ X ∧
    AC2 O actual initial φ retained X ∧
    AC3 O actual initial φ retained X

/-- The older clause: the alternative may set a contingency off its actual write. -/
def UnpinnedAC2 (_actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retainedFree : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  ∃ alt, retainedFree X alt ∧ (∀ i ∈ X, i ∉ alt) ∧ ¬ φ (O.final alt initial)

def UnpinnedAC3 (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retainedFree : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  ∀ Y, ProperSubset Y X →
    ¬ (AC1 O actual initial φ Y ∧ UnpinnedAC2 O actual initial φ retainedFree Y)

/-- A cause under the clause that does not pin contingencies to actual writes. -/
def UnpinnedCause (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retainedFree : List Id → List Id → Prop)
    (X : List Id) : Prop :=
  AC1 O actual initial φ X ∧
    UnpinnedAC2 O actual initial φ retainedFree X ∧
    UnpinnedAC3 O actual initial φ retainedFree X

theorem pinWrites_const_false (w : List Id) (store : Store Id Cell Value) :
    pinWrites O (fun _ => false) w store = store := by
  induction w generalizing store with
  | nil => rfl
  | cons _ _ ih => exact ih store

theorem pinWrites_append (keep : Id → Bool) (u w : List Id) (store : Store Id Cell Value) :
    pinWrites O keep (u ++ w) store = pinWrites O keep w (pinWrites O keep u store) := by
  induction u generalizing store with
  | nil => rfl
  | cons i _ ih => exact ih (cond (keep i) (O.apply i store) store)

theorem pinWrites_two (keep : Id → Bool) (a b : Id) (v : List Id)
    (store : Store Id Cell Value) :
    pinWrites O keep (a :: b :: v) store =
      pinWrites O keep v
        (cond (keep b) (O.apply b (cond (keep a) (O.apply a store) store))
          (cond (keep a) (O.apply a store) store)) :=
  rfl

theorem step_comm (keep : Id → Bool) (a b : Id) (store : Store Id Cell Value)
    (disj : keep a = true → keep b = true → ∀ cell, ¬ (O.Writes a cell ∧ O.Writes b cell)) :
    (cond (keep b) (O.apply b (cond (keep a) (O.apply a store) store))
      (cond (keep a) (O.apply a store) store)) =
    (cond (keep a) (O.apply a (cond (keep b) (O.apply b store) store))
      (cond (keep b) (O.apply b store) store)) := by
  cases ha : keep a <;> cases hb : keep b
  · rfl
  · rfl
  · rfl
  · exact (O.apply_comm (fun cell => disj ha hb cell) store).symm

theorem pinWrites_swap (keep : Id → Bool) {a b : Id}
    (disj : keep a = true → keep b = true → ∀ cell, ¬ (O.Writes a cell ∧ O.Writes b cell))
    (u v : List Id) (store : Store Id Cell Value) :
    pinWrites O keep (u ++ a :: b :: v) store =
      pinWrites O keep (u ++ b :: a :: v) store := by
  rw [pinWrites_append O keep u (a :: b :: v) store,
    pinWrites_append O keep u (b :: a :: v) store,
    pinWrites_two O keep a b v (pinWrites O keep u store),
    pinWrites_two O keep b a v (pinWrites O keep u store)]
  exact congrArg (pinWrites O keep v)
    (step_comm O keep a b (pinWrites O keep u store) disj)

/-- Independent swaps preserve a pin: pinned occurrences write disjoint cells. -/
theorem pinWrites_eq_of_trace (keep : Id → Bool) {w w' : List Id}
    (equivalent : TraceEquiv O.Independent w w') (store : Store Id Cell Value) :
    pinWrites O keep w store = pinWrites O keep w' store :=
  TraceEquiv.invariant (fun word => pinWrites O keep word store)
    (fun u v _a _b related =>
      pinWrites_swap O keep (fun _ _ cell => related.no_common_write cell) u v store)
    equivalent

theorem ac1_of_trace {w w' : List Id} (equivalent : TraceEquiv O.Independent w w')
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop) {X : List Id}
    (held : AC1 O w initial φ X) : AC1 O w' initial φ X := by
  rcases held with ⟨nonempty, members, observed⟩
  refine ⟨nonempty, ?_, ?_⟩
  · intro i hi
    exact (List.Perm.mem_iff (TraceEquiv.perm equivalent)).1 (members i hi)
  · rw [O.final_eq_of_trace equivalent initial] at observed
    exact observed

theorem ac2_of_trace {w w' : List Id} (equivalent : TraceEquiv O.Independent w w')
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) {X : List Id}
    (held : AC2 O w initial φ retained X) : AC2 O w' initial φ retained X := by
  rcases held with ⟨keep, alt, inActual, outside, fork, dropped, falsifies⟩
  refine ⟨keep, alt, ?_, outside, fork, dropped, ?_⟩
  · intro i hi
    exact (List.Perm.mem_iff (TraceEquiv.perm equivalent)).1 (inActual i hi)
  · rw [pinWrites_eq_of_trace O keep equivalent (O.final alt initial)] at falsifies
    exact falsifies

theorem ac3_of_trace {w w' : List Id} (equivalent : TraceEquiv O.Independent w w')
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) {X : List Id}
    (minimal : AC3 O w initial φ retained X) : AC3 O w' initial φ retained X := by
  intro Y subset both
  apply minimal Y subset
  exact ⟨ac1_of_trace O (Relation.EqvGen.symm w w' equivalent) initial φ both.1,
    ac2_of_trace O (Relation.EqvGen.symm w w' equivalent) initial φ retained both.2⟩

theorem actualCause_of_trace {w w' : List Id}
    (equivalent : TraceEquiv O.Independent w w')
    (initial : Store Id Cell Value) (φ : Store Id Cell Value → Prop)
    (retained : List Id → List Id → Prop) {X : List Id}
    (cause : ActualCause O w initial φ retained X) :
    ActualCause O w' initial φ retained X :=
  ⟨ac1_of_trace O equivalent initial φ cause.1,
    ac2_of_trace O equivalent initial φ retained cause.2.1,
    ac3_of_trace O equivalent initial φ retained cause.2.2⟩

theorem not_writes_of_none {i : Id} {cell : Cell}
    (h : (O.footprint i).writes cell = none) : ¬ O.Writes i cell := by
  intro written
  unfold Writes at written
  rw [h] at written
  cases written

theorem not_reads_of_false {i : Id} {cell : Cell}
    (h : (O.footprint i).reads cell = false) : ¬ O.Reads i cell := by
  intro reading
  unfold Reads at reading
  rw [h] at reading
  cases reading

theorem writes_of_some {i : Id} {cell : Cell} {payload : Value}
    (h : (O.footprint i).writes cell = some payload) : O.Writes i cell := by
  unfold Writes
  rw [h]
  rfl

theorem reads_of_true {i : Id} {cell : Cell}
    (h : (O.footprint i).reads cell = true) : O.Reads i cell := by
  unfold Reads
  rw [h]

theorem not_shares_of_left_none {a b : Id} (ha : O.channel a = none) :
    ¬ O.SharesChannel a b := by
  intro shared
  obtain ⟨_, h1, _⟩ := shared
  rw [ha] at h1
  cases h1

theorem not_shares_of_right_none {a b : Id} (hb : O.channel b = none) :
    ¬ O.SharesChannel a b := by
  intro shared
  obtain ⟨_, _, h2⟩ := shared
  rw [hb] at h2
  cases h2

theorem not_dependent_of {a b : Id} (nh : ¬ O.Hazard a b) (ns : ¬ O.SharesChannel a b) :
    ¬ O.Dependent a b := by
  intro dependent
  cases dependent with
  | inl hazard => exact nh hazard
  | inr shared => exact ns shared

theorem pinWrites_keeps_payload (keep : Id → Bool) (w : List Id) (cell : Cell)
    (payload : Value) (store : Store Id Cell Value) (base : (store cell).1 = payload)
    (ok : ∀ i ∈ w,
      (O.footprint i).writes cell = none ∨ (O.footprint i).writes cell = some payload) :
    ((pinWrites O keep w store) cell).1 = payload := by
  induction w generalizing store with
  | nil => exact base
  | cons i w ih =>
      have okRest : ∀ j ∈ w,
          (O.footprint j).writes cell = none ∨
            (O.footprint j).writes cell = some payload :=
        fun j hj => ok j (List.mem_cons_of_mem i hj)
      cases hk : keep i with
      | false =>
          unfold pinWrites
          rw [hk]
          exact ih store base okRest
      | true =>
          unfold pinWrites
          rw [hk]
          cases ok i List.mem_cons_self with
          | inl noneWrite =>
              have same := O.apply_of_not_writes (not_writes_of_none O noneWrite) store
              have kept : ((O.apply i store) cell).1 = payload := by
                rw [same]
                exact base
              exact ih (O.apply i store) kept okRest
          | inr someWrite =>
              have set := O.apply_of_writes someWrite store
              have kept : ((O.apply i store) cell).1 = payload := by
                rw [set]
              exact ih (O.apply i store) kept okRest

theorem not_or_bool {a b : Bool} (ha : a = false) (hb : b = false) :
    ¬ (a = true ∨ b = true) := by
  intro held
  cases held with
  | inl h => cases h.symm.trans ha
  | inr h => cases h.symm.trans hb

/-- A singleton has no proper subset that meets AC1. -/
theorem singleton_blocks_subset (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) {a : Id} {X : List Id}
    (char : ∀ i, i ∈ X ↔ i = a) {Y : List Id} (subset : ProperSubset Y X)
    {rest : Prop} (both : AC1 O actual initial φ Y ∧ rest) : False := by
  rcases subset with ⟨into, missing, inX, notInY⟩
  rcases both.1 with ⟨⟨j, jIn⟩, _, _⟩
  have missing_a : missing = a := (char missing).1 inX
  have j_a : j = a := (char j).1 (into j jIn)
  exact notInY (missing_a.symm ▸ j_a ▸ jIn)

theorem mem_singleton {a i : Id} : i ∈ [a] ↔ i = a := by
  constructor
  · intro hi
    cases hi with
    | head _ => rfl
    | tail _ hi => cases hi
  · intro hi
    subst hi
    exact List.mem_cons_self

theorem ac3_singleton (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retained : List Id → List Id → Prop)
    {a : Id} {X : List Id} (char : ∀ i, i ∈ X ↔ i = a) :
    AC3 O actual initial φ retained X := by
  intro Y subset both
  exact singleton_blocks_subset O actual initial φ char subset both

theorem unpinnedAc3_singleton (actual : List Id) (initial : Store Id Cell Value)
    (φ : Store Id Cell Value → Prop) (retainedFree : List Id → List Id → Prop)
    {a : Id} {X : List Id} (char : ∀ i, i ∈ X ↔ i = a) :
    UnpinnedAC3 O actual initial φ retainedFree X := by
  intro Y subset both
  exact singleton_blocks_subset O actual initial φ char subset both

theorem not_true_of_false {b : Bool} (h : b = false) : ¬ b = true := by
  intro broken
  cases broken.symm.trans h

theorem singleton_members {α : Type} {a : α} {actual : List α} (ha : a ∈ actual) :
    ∀ i ∈ [a], i ∈ actual := by
  intro i hi
  cases hi with
  | head _ => exact ha
  | tail _ hi => cases hi

theorem pair_members {α : Type} {a b : α} {actual : List α}
    (ha : a ∈ actual) (hb : b ∈ actual) : ∀ i ∈ [a, b], i ∈ actual := by
  intro i hi
  cases hi with
  | head _ => exact ha
  | tail _ hi =>
      cases hi with
      | head _ => exact hb
      | tail _ hi => cases hi

theorem singleton_absent {α : Type} {a : α} {alt : List α} (ha : a ∉ alt) :
    ∀ i ∈ [a], i ∉ alt := by
  intro i hi
  cases hi with
  | head _ => exact ha
  | tail _ hi => cases hi

end Definitions

/-! ## Causal past along a word -/

/-- A step is two occurrences of the word, earlier then later, that share a
hazard or a channel. A chain is the transitive closure. This is the
Mazurkiewicz causal past: independent occurrences do not enter it. -/
inductive CausalLink {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) (w : List Id) : Id → Id → Prop
  | step {a b : Id} {pre mid post : List Id}
      (shape : w = pre ++ (a :: mid) ++ (b :: post))
      (dep : O.Dependent a b ∨ O.Dependent b a) : CausalLink O w a b
  | trans {a b c : Id} : CausalLink O w a b → CausalLink O w b c → CausalLink O w a c

abbrev InCausalPast {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) (w : List Id) (cause effect : Id) : Prop :=
  CausalLink O w cause effect

/-- Sharing a cell with a later occurrence puts the writer in its causal past. -/
theorem in_past_of_hazard {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) {c e : Id} {pre mid post : List Id}
    (shared : O.Hazard c e) :
    InCausalPast O (pre ++ (c :: mid) ++ (e :: post)) c e :=
  CausalLink.step rfl (Or.inl (Or.inl shared))

theorem two_cons_split {α : Type} {a b c d : α} {pre mid post : List α}
    (h : pre ++ (c :: mid) ++ (d :: post) = [a, b]) :
    pre = [] ∧ c = a ∧ mid = [] ∧ d = b ∧ post = [] := by
  cases pre with
  | cons _ ps =>
      injection h with _ ht
      cases ps with
      | cons _ ps2 =>
          injection ht with _ ht2
          cases ps2 with
          | nil => cases ht2
          | cons _ _ => cases ht2
      | nil =>
          injection ht with _ ht2
          cases mid with
          | nil => cases ht2
          | cons _ _ => cases ht2
  | nil =>
      injection h with hc ht
      cases mid with
      | cons _ ms =>
          injection ht with _ ht2
          cases ms with
          | nil => cases ht2
          | cons _ _ => cases ht2
      | nil =>
          injection ht with hd hp
          cases post with
          | cons _ _ => cases hp
          | nil => exact ⟨rfl, hc, rfl, hd, rfl⟩

theorem no_causalLink_two {Id Cell Value Channel : Type}
    (O : Occurrences Id Cell Value Channel) {a b : Id}
    (nd : ¬ (O.Dependent a b ∨ O.Dependent b a)) :
    ∀ {x y : Id}, ¬ CausalLink O [a, b] x y := by
  intro x y link
  induction link with
  | step shape dep =>
      obtain ⟨_, rfl, _, rfl, _⟩ := two_cons_split shape.symm
      exact nd dep
  | trans _ _ ih1 _ => exact ih1

/-! ## Late preemption -/

inductive PreemptId where
  | suzyThrow | suzyHit | billyThrow | billyMiss
  | suzyAbsent | suzyNoHit | billyHits | billyAbsent
  deriving DecidableEq

inductive PreemptCell where
  | arm | sh | billyArm | bh
  deriving DecidableEq

def preemptWrite : PreemptId → PreemptCell → Option Bool
  | .suzyThrow, .arm => some true
  | .suzyAbsent, .arm => some false
  | .suzyHit, .sh => some true
  | .suzyNoHit, .sh => some false
  | .billyThrow, .billyArm => some true
  | .billyAbsent, .billyArm => some false
  | .billyMiss, .bh => some false
  | .billyHits, .bh => some true
  | _, _ => none

def preemptRead : PreemptId → PreemptCell → Bool
  | .suzyHit, .arm | .suzyNoHit, .arm => true
  | .billyMiss, .billyArm | .billyHits, .billyArm => true
  | _, _ => false

def preemptChannel : PreemptId → Option Unit
  | .suzyHit | .suzyNoHit | .billyMiss | .billyHits => some ()
  | _ => none

def preemptO : Occurrences PreemptId PreemptCell Bool Unit where
  footprint i := { reads := preemptRead i, writes := preemptWrite i }
  channel := preemptChannel

def preemptInitial : Store PreemptId PreemptCell Bool := fun _ => (false, none)

def preemptActual : List PreemptId := [.suzyThrow, .suzyHit, .billyThrow, .billyMiss]

/-- Suzy stays out and Billy's rock hits. The structural fork, before the pin. -/
def suzyAlt : List PreemptId := [.suzyAbsent, .suzyNoHit, .billyThrow, .billyHits]

/-- Billy stays out. Suzy's hit remains. -/
def billyAlt : List PreemptId := [.suzyThrow, .suzyHit, .billyAbsent, .billyMiss]

/-- Both throws stay out, so neither rock hits. -/
def bothAlt : List PreemptId := [.suzyAbsent, .suzyNoHit, .billyAbsent, .billyMiss]

/-- Suzy's hit is set off its actual value. Used only by the unpinned clause. -/
def unpinnedAlt : List PreemptId := [.suzyAbsent, .suzyNoHit, .billyAbsent, .billyMiss]

def preemptBreaks (store : Store PreemptId PreemptCell Bool) : Prop :=
  (store .sh).1 = true ∨ (store .bh).1 = true

inductive PreemptRetained : List PreemptId → List PreemptId → Prop
  | suzy {X : List PreemptId} : .suzyThrow ∈ X → .billyThrow ∉ X → PreemptRetained X suzyAlt
  | billy {X : List PreemptId} : .billyThrow ∈ X → .suzyThrow ∉ X → PreemptRetained X billyAlt
  | both {X : List PreemptId} : .suzyThrow ∈ X → .billyThrow ∈ X → PreemptRetained X bothAlt

inductive PreemptUnpinned : List PreemptId → List PreemptId → Prop
  | billy {X : List PreemptId} : .billyThrow ∈ X → PreemptUnpinned X unpinnedAlt

def pinBillyMiss : PreemptId → Bool
  | .billyMiss => true
  | _ => false

theorem preempt_actual_sh :
    ((preemptO.final preemptActual preemptInitial) .sh).1 = true := rfl

theorem preempt_actual_bh :
    ((preemptO.final preemptActual preemptInitial) .bh).1 = false := rfl

theorem suzyAlt_bh : ((preemptO.final suzyAlt preemptInitial) .bh).1 = true := rfl

theorem suzy_pinned_sh :
    ((pinWrites preemptO pinBillyMiss preemptActual (preemptO.final suzyAlt preemptInitial)) .sh).1
      = false := rfl

theorem suzy_pinned_bh :
    ((pinWrites preemptO pinBillyMiss preemptActual (preemptO.final suzyAlt preemptInitial)) .bh).1
      = false := rfl

theorem bothAlt_sh : ((preemptO.final bothAlt preemptInitial) .sh).1 = false := rfl

theorem bothAlt_bh : ((preemptO.final bothAlt preemptInitial) .bh).1 = false := rfl

theorem billyAlt_sh : ((preemptO.final billyAlt preemptInitial) .sh).1 = true := rfl

theorem unpinned_sh : ((preemptO.final unpinnedAlt preemptInitial) .sh).1 = false := rfl

theorem unpinned_bh : ((preemptO.final unpinnedAlt preemptInitial) .bh).1 = false := rfl

theorem preempt_sh_ok :
    ∀ i ∈ preemptActual,
      (preemptO.footprint i).writes .sh = none ∨
        (preemptO.footprint i).writes .sh = some true := by
  intro i hi
  cases hi with
  | head _ => exact Or.inl rfl
  | tail _ hi =>
      cases hi with
      | head _ => exact Or.inr rfl
      | tail _ hi =>
          cases hi with
          | head _ => exact Or.inl rfl
          | tail _ hi =>
              cases hi with
              | head _ => exact Or.inl rfl
              | tail _ hi => cases hi

theorem preemption_billy_pin_sh (keep : PreemptId → Bool) :
    ((pinWrites preemptO keep preemptActual (preemptO.final billyAlt preemptInitial)) .sh).1
      = true :=
  pinWrites_keeps_payload preemptO keep preemptActual .sh true
    (preemptO.final billyAlt preemptInitial) billyAlt_sh preempt_sh_ok

theorem preemption_suzy_ac1 :
    AC1 preemptO preemptActual preemptInitial preemptBreaks [.suzyThrow] :=
  ⟨⟨PreemptId.suzyThrow, List.mem_cons_self⟩,
    singleton_members (by decide : PreemptId.suzyThrow ∈ preemptActual),
    Or.inl preempt_actual_sh⟩

theorem preemption_suzy_ac2 :
    AC2 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained [.suzyThrow] := by
  refine ⟨pinBillyMiss, suzyAlt, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | billyMiss => exact (by decide : PreemptId.billyMiss ∈ preemptActual)
    | suzyThrow => cases hi
    | suzyHit => cases hi
    | billyThrow => cases hi
    | suzyAbsent => cases hi
    | suzyNoHit => cases hi
    | billyHits => cases hi
    | billyAbsent => cases hi
  · intro i hi
    cases i with
    | billyMiss => decide
    | suzyThrow => cases hi
    | suzyHit => cases hi
    | billyThrow => cases hi
    | suzyAbsent => cases hi
    | suzyNoHit => cases hi
    | billyHits => cases hi
    | billyAbsent => cases hi
  · exact PreemptRetained.suzy List.mem_cons_self (by decide)
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi => cases hi
  · exact not_or_bool suzy_pinned_sh suzy_pinned_bh

theorem preemption_suzy_ac3 :
    AC3 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained [.suzyThrow] :=
  ac3_singleton preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
    (fun i => mem_singleton (a := PreemptId.suzyThrow) (i := i))

/-- Suzy's throw is an actual cause. The witness pins Billy's miss. -/
theorem preemption_suzy_actualCause :
    ActualCause preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
      [.suzyThrow] :=
  ⟨preemption_suzy_ac1, preemption_suzy_ac2, preemption_suzy_ac3⟩

/-- Suzy's throw is not a but-for cause: without the pin, Billy hits. -/
theorem preemption_suzy_not_butFor :
    ¬ ButFor preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
        [.suzyThrow] := by
  intro held
  rcases held with ⟨_, fork, _, falsifies⟩
  cases fork with
  | suzy _ _ => exact falsifies (Or.inr suzyAlt_bh)
  | billy _ noSuzy => exact noSuzy List.mem_cons_self
  | both _ billyIn =>
      exact (by decide : PreemptId.billyThrow ∉ [PreemptId.suzyThrow]) billyIn

theorem preemption_throw_hazard : preemptO.Hazard .suzyThrow .suzyHit :=
  ⟨.arm, writes_of_some preemptO rfl, Or.inr (reads_of_true preemptO rfl)⟩

theorem preemption_actual_shape :
    preemptActual = [] ++ (.suzyThrow :: []) ++ (.suzyHit :: [.billyThrow, .billyMiss]) := rfl

/-- Suzy's throw is in the causal past of her hit: the throw writes the arm her hit reads. -/
theorem preemption_suzy_in_past :
    InCausalPast preemptO preemptActual .suzyThrow .suzyHit :=
  preemption_actual_shape.symm ▸
    in_past_of_hazard preemptO (pre := []) (mid := []) (post := [.billyThrow, .billyMiss])
      preemption_throw_hazard

theorem preemption_not_hazard_hit_throw : ¬ preemptO.Hazard .suzyHit .billyThrow := by
  intro hazard
  obtain ⟨cell, written, used⟩ := hazard
  cases cell with
  | arm => exact not_writes_of_none preemptO rfl written
  | sh =>
      cases used with
      | inl w => exact not_writes_of_none preemptO rfl w
      | inr r => exact not_reads_of_false preemptO rfl r
  | billyArm => exact not_writes_of_none preemptO rfl written
  | bh => exact not_writes_of_none preemptO rfl written

theorem preemption_not_hazard_throw_hit : ¬ preemptO.Hazard .billyThrow .suzyHit := by
  intro hazard
  obtain ⟨cell, written, used⟩ := hazard
  cases cell with
  | arm => exact not_writes_of_none preemptO rfl written
  | sh => exact not_writes_of_none preemptO rfl written
  | billyArm =>
      cases used with
      | inl w => exact not_writes_of_none preemptO rfl w
      | inr r => exact not_reads_of_false preemptO rfl r
  | bh => exact not_writes_of_none preemptO rfl written

theorem preemption_hit_throw_independent : preemptO.Independent .suzyHit .billyThrow := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    cases h
  · exact not_dependent_of preemptO preemption_not_hazard_hit_throw
      (not_shares_of_right_none (b := PreemptId.billyThrow) preemptO rfl)
  · exact not_dependent_of preemptO preemption_not_hazard_throw_hit
      (not_shares_of_left_none (a := PreemptId.billyThrow) preemptO rfl)

def preemptSwapped : List PreemptId := [.suzyThrow, .billyThrow, .suzyHit, .billyMiss]

theorem preemption_trace :
    TraceEquiv preemptO.Independent preemptActual preemptSwapped :=
  Relation.EqvGen.rel preemptActual preemptSwapped
    (Swap.swap [PreemptId.suzyThrow] [PreemptId.billyMiss]
      (a := PreemptId.suzyHit) (b := PreemptId.billyThrow)
      preemption_hit_throw_independent)

theorem preemption_final_invariant :
    preemptO.final preemptActual preemptInitial =
      preemptO.final preemptSwapped preemptInitial :=
  preemptO.final_eq_of_trace preemption_trace preemptInitial

theorem preemption_observe_invariant :
    preemptO.observe preemptActual preemptInitial =
      preemptO.observe preemptSwapped preemptInitial :=
  preemptO.observe_eq_of_trace preemption_trace preemptInitial

/-- The preemption verdict survives the independent swap of Suzy's hit and Billy's throw. -/
theorem preemption_cause_trace_invariant :
    ActualCause preemptO preemptSwapped preemptInitial preemptBreaks PreemptRetained
      [.suzyThrow] :=
  actualCause_of_trace preemptO preemption_trace preemptInitial preemptBreaks PreemptRetained
    preemption_suzy_actualCause

theorem preemption_billy_not_ac2 :
    ¬ AC2 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained [.billyThrow] := by
  intro held
  rcases held with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | billy _ _ => exact falsifies (Or.inl (preemption_billy_pin_sh keep))
  | suzy _ noBilly => exact noBilly List.mem_cons_self
  | both noRoom _ =>
      exact (by decide : PreemptId.suzyThrow ∉ [PreemptId.billyThrow]) noRoom

theorem preemption_billy_not_actualCause :
    ¬ ActualCause preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
        [.billyThrow] :=
  fun held => preemption_billy_not_ac2 held.2.1

theorem preemption_pair_ac1 :
    AC1 preemptO preemptActual preemptInitial preemptBreaks [.suzyThrow, .billyThrow] :=
  ⟨⟨PreemptId.suzyThrow, List.mem_cons_self⟩,
    pair_members
      (by decide : PreemptId.suzyThrow ∈ preemptActual)
      (by decide : PreemptId.billyThrow ∈ preemptActual),
    Or.inl preempt_actual_sh⟩

theorem preemption_pair_ac2 :
    AC2 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
      [.suzyThrow, .billyThrow] := by
  refine ⟨fun _ => false, bothAlt, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · exact PreemptRetained.both (by decide) (by decide)
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi =>
        cases hi with
        | head _ => decide
        | tail _ hi => cases hi
  · rw [pinWrites_const_false preemptO preemptActual (preemptO.final bothAlt preemptInitial)]
    exact not_or_bool bothAlt_sh bothAlt_bh

theorem preemption_pair_proper :
    ProperSubset [PreemptId.suzyThrow] [PreemptId.suzyThrow, PreemptId.billyThrow] :=
  ⟨singleton_members
      (by decide : PreemptId.suzyThrow ∈ [PreemptId.suzyThrow, PreemptId.billyThrow]),
    PreemptId.billyThrow, by decide, by decide⟩

/-- `{Suzy's throw, Billy's throw}` meets AC1 and AC2, and AC3 removes it. -/
theorem preemption_pair_removed_by_ac3 :
    AC1 preemptO preemptActual preemptInitial preemptBreaks [.suzyThrow, .billyThrow] ∧
      AC2 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
        [.suzyThrow, .billyThrow] ∧
      ¬ AC3 preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
          [.suzyThrow, .billyThrow] := by
  refine ⟨preemption_pair_ac1, preemption_pair_ac2, ?_⟩
  intro minimal
  exact minimal [.suzyThrow] preemption_pair_proper ⟨preemption_suzy_ac1, preemption_suzy_ac2⟩

theorem preemption_pair_not_actualCause :
    ¬ ActualCause preemptO preemptActual preemptInitial preemptBreaks PreemptRetained
        [.suzyThrow, .billyThrow] :=
  fun held => preemption_pair_removed_by_ac3.2.2 held.2.2

theorem preemption_billy_unpinned_ac1 :
    AC1 preemptO preemptActual preemptInitial preemptBreaks [.billyThrow] :=
  ⟨⟨PreemptId.billyThrow, List.mem_cons_self⟩,
    singleton_members (by decide : PreemptId.billyThrow ∈ preemptActual),
    Or.inl preempt_actual_sh⟩

theorem preemption_billy_unpinned_ac2 :
    UnpinnedAC2 preemptO preemptActual preemptInitial preemptBreaks PreemptUnpinned
      [.billyThrow] :=
  ⟨unpinnedAlt, PreemptUnpinned.billy List.mem_cons_self,
    singleton_absent (by decide : PreemptId.billyThrow ∉ unpinnedAlt),
    not_or_bool unpinned_sh unpinned_bh⟩

theorem preemption_billy_unpinned_ac3 :
    UnpinnedAC3 preemptO preemptActual preemptInitial preemptBreaks PreemptUnpinned
      [.billyThrow] :=
  unpinnedAc3_singleton preemptO preemptActual preemptInitial preemptBreaks PreemptUnpinned
    (fun i => mem_singleton (a := PreemptId.billyThrow) (i := i))

/-- Dropping the actual-write pin licenses Billy's throw. -/
theorem preemption_billy_unpinnedCause :
    UnpinnedCause preemptO preemptActual preemptInitial preemptBreaks PreemptUnpinned
      [.billyThrow] :=
  ⟨preemption_billy_unpinned_ac1, preemption_billy_unpinned_ac2, preemption_billy_unpinned_ac3⟩

/-- The falsifying world changes Suzy's hit, which is outside the candidate and
outside the actual write of that hit. -/
theorem preemption_unpinned_changes_suzy :
    (preemptO.footprint .suzyNoHit).writes .sh = some false ∧
      (preemptO.footprint .suzyHit).writes .sh = some true ∧
      .suzyNoHit ∈ unpinnedAlt ∧ .suzyHit ∈ preemptActual ∧
      PreemptId.suzyHit ∉ [PreemptId.billyThrow] ∧ .suzyHit ∉ unpinnedAlt :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- No actual-write pin of Billy's admissible fork reaches that falsifying world. -/
theorem preemption_false_cause_not_pinned (keep : PreemptId → Bool) :
    pinWrites preemptO keep preemptActual (preemptO.final billyAlt preemptInitial) ≠
      preemptO.final unpinnedAlt preemptInitial := by
  intro same
  have values := congrArg (fun store : Store PreemptId PreemptCell Bool => (store .sh).1) same
  cases ((preemption_billy_pin_sh keep).symm.trans values).trans unpinned_sh

/-! ## Symmetric overdetermination -/

inductive OverId where
  | suzyHit | billyHit | suzyMiss | billyMiss
  deriving DecidableEq

inductive OverCell where
  | sh | bh
  deriving DecidableEq

def overWrite : OverId → OverCell → Option Bool
  | .suzyHit, .sh => some true
  | .suzyMiss, .sh => some false
  | .billyHit, .bh => some true
  | .billyMiss, .bh => some false
  | _, _ => none

def overO : Occurrences OverId OverCell Bool Unit where
  footprint i := { reads := fun _ => false, writes := overWrite i }
  channel := fun _ => none

def overInitial : Store OverId OverCell Bool := fun _ => (false, none)

def overActual : List OverId := [.suzyHit, .billyHit]

def overSuzyAlt : List OverId := [.suzyMiss, .billyHit]

def overBillyAlt : List OverId := [.suzyHit, .billyMiss]

def overBothAlt : List OverId := [.suzyMiss, .billyMiss]

def overBreaks (store : Store OverId OverCell Bool) : Prop :=
  (store .sh).1 = true ∨ (store .bh).1 = true

/-- Admissible forks for the pinned clause. One hit is replaced and the other stays. -/
inductive OverRetained : List OverId → List OverId → Prop
  | onlySuzy {X : List OverId} : .suzyHit ∈ X → .billyHit ∉ X → OverRetained X overSuzyAlt
  | onlyBilly {X : List OverId} : .billyHit ∈ X → .suzyHit ∉ X → OverRetained X overBillyAlt
  | both {X : List OverId} : .suzyHit ∈ X → .billyHit ∈ X → OverRetained X overBothAlt

/-- Forks that set the other hit off its actual write. -/
inductive OverUnpinned : List OverId → List OverId → Prop
  | suzy {X : List OverId} : .suzyHit ∈ X → .billyHit ∉ X → OverUnpinned X overBothAlt
  | billy {X : List OverId} : .billyHit ∈ X → .suzyHit ∉ X → OverUnpinned X overBothAlt

theorem over_actual_sh : ((overO.final overActual overInitial) .sh).1 = true := rfl

theorem overSuzyAlt_bh : ((overO.final overSuzyAlt overInitial) .bh).1 = true := rfl

theorem overBillyAlt_sh : ((overO.final overBillyAlt overInitial) .sh).1 = true := rfl

theorem overBoth_sh : ((overO.final overBothAlt overInitial) .sh).1 = false := rfl

theorem overBoth_bh : ((overO.final overBothAlt overInitial) .bh).1 = false := rfl

theorem over_bh_ok :
    ∀ i ∈ overActual,
      (overO.footprint i).writes .bh = none ∨ (overO.footprint i).writes .bh = some true := by
  intro _ hi
  cases hi with
  | head _ => exact Or.inl rfl
  | tail _ hi =>
      cases hi with
      | head _ => exact Or.inr rfl
      | tail _ hi => cases hi

theorem over_sh_ok :
    ∀ i ∈ overActual,
      (overO.footprint i).writes .sh = none ∨ (overO.footprint i).writes .sh = some true := by
  intro _ hi
  cases hi with
  | head _ => exact Or.inr rfl
  | tail _ hi =>
      cases hi with
      | head _ => exact Or.inl rfl
      | tail _ hi => cases hi

theorem over_suzy_pin_bh (keep : OverId → Bool) :
    ((pinWrites overO keep overActual (overO.final overSuzyAlt overInitial)) .bh).1 = true :=
  pinWrites_keeps_payload overO keep overActual .bh true (overO.final overSuzyAlt overInitial)
    overSuzyAlt_bh over_bh_ok

theorem over_billy_pin_sh (keep : OverId → Bool) :
    ((pinWrites overO keep overActual (overO.final overBillyAlt overInitial)) .sh).1 = true :=
  pinWrites_keeps_payload overO keep overActual .sh true (overO.final overBillyAlt overInitial)
    overBillyAlt_sh over_sh_ok

theorem over_suzy_not_butFor :
    ¬ ButFor overO overActual overInitial overBreaks OverRetained [.suzyHit] := by
  intro held
  rcases held with ⟨_, fork, _, falsifies⟩
  cases fork with
  | onlySuzy _ _ => exact falsifies (Or.inr overSuzyAlt_bh)
  | onlyBilly _ noSuzy => exact noSuzy List.mem_cons_self
  | both _ billyIn =>
      exact (by decide : OverId.billyHit ∉ [OverId.suzyHit]) billyIn

theorem over_billy_not_butFor :
    ¬ ButFor overO overActual overInitial overBreaks OverRetained [.billyHit] := by
  intro held
  rcases held with ⟨_, fork, _, falsifies⟩
  cases fork with
  | onlyBilly _ _ => exact falsifies (Or.inl overBillyAlt_sh)
  | onlySuzy _ noBilly => exact noBilly List.mem_cons_self
  | both suzyIn _ =>
      exact (by decide : OverId.suzyHit ∉ [OverId.billyHit]) suzyIn

theorem over_suzy_not_ac2 :
    ¬ AC2 overO overActual overInitial overBreaks OverRetained [.suzyHit] := by
  intro held
  rcases held with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | onlySuzy _ _ => exact falsifies (Or.inr (over_suzy_pin_bh keep))
  | onlyBilly _ noSuzy => exact noSuzy List.mem_cons_self
  | both _ billyIn =>
      exact (by decide : OverId.billyHit ∉ [OverId.suzyHit]) billyIn

theorem over_billy_not_ac2 :
    ¬ AC2 overO overActual overInitial overBreaks OverRetained [.billyHit] := by
  intro held
  rcases held with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | onlyBilly _ _ => exact falsifies (Or.inl (over_billy_pin_sh keep))
  | onlySuzy _ noBilly => exact noBilly List.mem_cons_self
  | both suzyIn _ =>
      exact (by decide : OverId.suzyHit ∉ [OverId.billyHit]) suzyIn

theorem over_suzy_not_actualCause :
    ¬ ActualCause overO overActual overInitial overBreaks OverRetained [.suzyHit] :=
  fun held => over_suzy_not_ac2 held.2.1

theorem over_billy_not_actualCause :
    ¬ ActualCause overO overActual overInitial overBreaks OverRetained [.billyHit] :=
  fun held => over_billy_not_ac2 held.2.1

theorem over_both_ac1 :
    AC1 overO overActual overInitial overBreaks [.suzyHit, .billyHit] :=
  ⟨⟨OverId.suzyHit, List.mem_cons_self⟩,
    pair_members
      (by decide : OverId.suzyHit ∈ overActual)
      (by decide : OverId.billyHit ∈ overActual),
    Or.inl over_actual_sh⟩

theorem over_both_ac2 :
    AC2 overO overActual overInitial overBreaks OverRetained [.suzyHit, .billyHit] := by
  refine ⟨fun _ => false, overBothAlt, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · exact OverRetained.both (by decide) (by decide)
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi =>
        cases hi with
        | head _ => decide
        | tail _ hi => cases hi
  · rw [pinWrites_const_false overO overActual (overO.final overBothAlt overInitial)]
    exact not_or_bool overBoth_sh overBoth_bh

theorem over_both_ac3 :
    AC3 overO overActual overInitial overBreaks OverRetained [.suzyHit, .billyHit] := by
  intro _ subset bothHeld
  rcases subset with ⟨_, missing, inX, notInY⟩
  rcases bothHeld with ⟨_, ac2⟩
  rcases ac2 with ⟨keep, _, _, _, fork, _, falsifies⟩
  cases fork with
  | onlySuzy _ _ => exact falsifies (Or.inr (over_suzy_pin_bh keep))
  | onlyBilly _ _ => exact falsifies (Or.inl (over_billy_pin_sh keep))
  | both suzyIn billyIn =>
      cases inX with
      | head _ => exact notInY (suzyIn)
      | tail _ rest =>
          cases rest with
          | head _ => exact notInY billyIn
          | tail _ rest => cases rest

/-- Under the pinned clause the cause is the pair. Each hit stays at its actual write. -/
theorem overdetermination_conjunction_actualCause :
    ActualCause overO overActual overInitial overBreaks OverRetained [.suzyHit, .billyHit] :=
  ⟨over_both_ac1, over_both_ac2, over_both_ac3⟩

theorem over_suzy_unpinned_ac2 :
    UnpinnedAC2 overO overActual overInitial overBreaks OverUnpinned [.suzyHit] :=
  ⟨overBothAlt,
    OverUnpinned.suzy List.mem_cons_self
      (by decide : OverId.billyHit ∉ [OverId.suzyHit]),
    singleton_absent (by decide : OverId.suzyHit ∉ overBothAlt),
    not_or_bool overBoth_sh overBoth_bh⟩

theorem over_billy_unpinned_ac2 :
    UnpinnedAC2 overO overActual overInitial overBreaks OverUnpinned [.billyHit] :=
  ⟨overBothAlt,
    OverUnpinned.billy List.mem_cons_self
      (by decide : OverId.suzyHit ∉ [OverId.billyHit]),
    singleton_absent (by decide : OverId.billyHit ∉ overBothAlt),
    not_or_bool overBoth_sh overBoth_bh⟩

theorem over_suzy_unpinnedCause :
    UnpinnedCause overO overActual overInitial overBreaks OverUnpinned [.suzyHit] :=
  ⟨⟨⟨OverId.suzyHit, List.mem_cons_self⟩,
      singleton_members (by decide : OverId.suzyHit ∈ overActual),
      Or.inl over_actual_sh⟩,
    over_suzy_unpinned_ac2,
    unpinnedAc3_singleton overO overActual overInitial overBreaks OverUnpinned
      (fun i => mem_singleton (a := OverId.suzyHit) (i := i))⟩

theorem over_billy_unpinnedCause :
    UnpinnedCause overO overActual overInitial overBreaks OverUnpinned [.billyHit] :=
  ⟨⟨⟨OverId.billyHit, List.mem_cons_self⟩,
      singleton_members (by decide : OverId.billyHit ∈ overActual),
      Or.inl over_actual_sh⟩,
    over_billy_unpinned_ac2,
    unpinnedAc3_singleton overO overActual overInitial overBreaks OverUnpinned
      (fun i => mem_singleton (a := OverId.billyHit) (i := i))⟩

/-- The unpinned fork writes Billy's cell false. His actual write is true. -/
theorem overdetermination_unpinned_not_actual_write :
    (overO.footprint .billyMiss).writes .bh = some false ∧
      (overO.footprint .billyHit).writes .bh = some true ∧
      .billyMiss ∈ overBothAlt ∧ .billyHit ∈ overActual ∧ .billyHit ∉ overBothAlt :=
  ⟨rfl, rfl, by decide, by decide, by decide⟩

/-! ## Double prevention -/

inductive DblId where
  | billy | suzy | catcher | suzyMiss
  deriving DecidableEq

inductive DblCell where
  | escort | bottle
  deriving DecidableEq

def dblWrite : DblId → DblCell → Option Bool
  | .billy, .escort => some true
  | .suzy, .bottle => some true
  | .catcher, .bottle => some false
  | .suzyMiss, .bottle => some false
  | _, _ => none

def dblChannel : DblId → Option Unit
  | .suzy | .suzyMiss | .catcher => some ()
  | .billy => none

def dblO : Occurrences DblId DblCell Bool Unit where
  footprint i := { reads := fun _ => false, writes := dblWrite i }
  channel := dblChannel

def dblInitial : Store DblId DblCell Bool := fun _ => (false, none)

def dblActual : List DblId := [.billy, .suzy]

/-- The retained fork inserts the catcher and Suzy's rock does not break the bottle. -/
def dblAlt : List DblId := [.catcher, .suzyMiss]

def dblBreaks (store : Store DblId DblCell Bool) : Prop := (store .bottle).1 = true

inductive DblRetained : List DblId → List DblId → Prop
  | removeBilly {X : List DblId} : .billy ∈ X → DblRetained X dblAlt

theorem dbl_actual_bottle : ((dblO.final dblActual dblInitial) .bottle).1 = true := rfl

theorem dbl_alt_bottle : ((dblO.final dblAlt dblInitial) .bottle).1 = false := rfl

theorem dbl_not_hazard_billy_suzy : ¬ dblO.Hazard .billy .suzy := by
  intro hazard
  obtain ⟨cell, written, used⟩ := hazard
  cases cell with
  | escort =>
      cases used with
      | inl w => exact not_writes_of_none dblO rfl w
      | inr r => exact not_reads_of_false dblO rfl r
  | bottle => exact not_writes_of_none dblO rfl written

theorem dbl_not_hazard_suzy_billy : ¬ dblO.Hazard .suzy .billy := by
  intro hazard
  obtain ⟨cell, written, used⟩ := hazard
  cases cell with
  | bottle =>
      cases used with
      | inl w => exact not_writes_of_none dblO rfl w
      | inr r => exact not_reads_of_false dblO rfl r
  | escort => exact not_writes_of_none dblO rfl written

theorem dbl_not_dependent_or :
    ¬ (dblO.Dependent .billy .suzy ∨ dblO.Dependent .suzy .billy) := by
  intro held
  cases held with
  | inl d =>
      exact not_dependent_of dblO dbl_not_hazard_billy_suzy
        (not_shares_of_left_none (a := DblId.billy) dblO rfl) d
  | inr d =>
      exact not_dependent_of dblO dbl_not_hazard_suzy_billy
        (not_shares_of_right_none (b := DblId.billy) dblO rfl) d

theorem doublePrevention_butFor :
    ButFor dblO dblActual dblInitial dblBreaks DblRetained [.billy] :=
  ⟨dblAlt, DblRetained.removeBilly List.mem_cons_self,
    singleton_absent (by decide : DblId.billy ∉ dblAlt),
    not_true_of_false dbl_alt_bottle⟩

theorem doublePrevention_ac1 :
    AC1 dblO dblActual dblInitial dblBreaks [.billy] :=
  ⟨⟨DblId.billy, List.mem_cons_self⟩,
    singleton_members (by decide : DblId.billy ∈ dblActual),
    dbl_actual_bottle⟩

theorem doublePrevention_ac2 :
    AC2 dblO dblActual dblInitial dblBreaks DblRetained [.billy] := by
  refine ⟨fun _ => false, dblAlt, ?_, ?_, DblRetained.removeBilly (by decide), ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi => cases hi
  · rw [pinWrites_const_false dblO dblActual (dblO.final dblAlt dblInitial)]
    exact fun broken => by cases broken.symm.trans dbl_alt_bottle

theorem doublePrevention_ac3 :
    AC3 dblO dblActual dblInitial dblBreaks DblRetained [.billy] :=
  ac3_singleton dblO dblActual dblInitial dblBreaks DblRetained
    (fun i => mem_singleton (a := DblId.billy) (i := i))

theorem doublePrevention_actualCause :
    ActualCause dblO dblActual dblInitial dblBreaks DblRetained [.billy] :=
  ⟨doublePrevention_ac1, doublePrevention_ac2, doublePrevention_ac3⟩

theorem doublePrevention_outside_past :
    ¬ InCausalPast dblO dblActual .billy .suzy :=
  no_causalLink_two dblO dbl_not_dependent_or

theorem doublePrevention_suzy_not_in_alt : .suzy ∉ dblAlt := by decide

/-- The retained fork is not a pointwise replacement that keeps Suzy's occurrence. -/
theorem doublePrevention_not_pointwise (pre mid post : List DblId) (replaced : DblId) :
    dblAlt ≠ pre ++ (replaced :: mid) ++ (.suzy :: post) := by
  intro same
  have member : .suzy ∈ pre ++ (replaced :: mid) ++ (.suzy :: post) :=
    List.mem_append_right (pre ++ (replaced :: mid)) List.mem_cons_self
  rw [← same] at member
  exact doublePrevention_suzy_not_in_alt member

/-- Billy is a but-for cause and an actual cause, and he lies outside Suzy's causal past. -/
theorem doublePrevention_dependence_not_production :
    ButFor dblO dblActual dblInitial dblBreaks DblRetained [.billy] ∧
      ActualCause dblO dblActual dblInitial dblBreaks DblRetained [.billy] ∧
      ¬ InCausalPast dblO dblActual .billy .suzy :=
  ⟨doublePrevention_butFor, doublePrevention_actualCause, doublePrevention_outside_past⟩

/-! ## A but-for replacement on a shared cell lies in the past -/

inductive ProdId where
  | cause | absent | effect
  deriving DecidableEq

inductive ProdCell where
  | signal | out
  deriving DecidableEq

def prodWrite : ProdId → ProdCell → Option Bool
  | .cause, .signal => some true
  | .absent, .signal => some false
  | .effect, .out => some true
  | _, _ => none

def prodRead : ProdId → ProdCell → Bool
  | .effect, .signal => true
  | _, _ => false

def prodO : Occurrences ProdId ProdCell Bool Unit where
  footprint i := { reads := prodRead i, writes := prodWrite i }
  channel i := match i with
    | .effect => some ()
    | _ => none

def prodInitial : Store ProdId ProdCell Bool := fun _ => (false, none)

def prodActual : List ProdId := [.cause, .effect]

def prodAlt : List ProdId := [.absent, .effect]

def prodHolds (store : Store ProdId ProdCell Bool) : Prop := (store .signal).1 = true

inductive ProdRetained : List ProdId → List ProdId → Prop
  | replace {X : List ProdId} : .cause ∈ X → ProdRetained X prodAlt

theorem prod_actual_signal : ((prodO.final prodActual prodInitial) .signal).1 = true := rfl

theorem prod_alt_signal : ((prodO.final prodAlt prodInitial) .signal).1 = false := rfl

theorem prod_actual_shape :
    prodActual = [] ++ (.cause :: []) ++ (.effect :: []) := rfl

theorem prod_alt_shape :
    prodAlt = [] ++ (.absent :: []) ++ (.effect :: []) := rfl

theorem production_hazard : prodO.Hazard .cause .effect :=
  ⟨.signal, writes_of_some prodO rfl, Or.inr (reads_of_true prodO rfl)⟩

theorem production_in_past :
    InCausalPast prodO prodActual .cause .effect :=
  prod_actual_shape.symm ▸
    in_past_of_hazard prodO (pre := []) (mid := []) (post := []) production_hazard

theorem production_butFor :
    ButFor prodO prodActual prodInitial prodHolds ProdRetained [.cause] :=
  ⟨prodAlt, ProdRetained.replace List.mem_cons_self,
    singleton_absent (by decide : ProdId.cause ∉ prodAlt),
    not_true_of_false prod_alt_signal⟩

theorem production_ac2 :
    AC2 prodO prodActual prodInitial prodHolds ProdRetained [.cause] := by
  refine ⟨fun _ => false, prodAlt, ?_, ?_, ProdRetained.replace (by decide), ?_, ?_⟩
  · intro _ hi; cases hi
  · intro _ hi; cases hi
  · intro i hi
    cases hi with
    | head _ => decide
    | tail _ hi => cases hi
  · rw [pinWrites_const_false prodO prodActual (prodO.final prodAlt prodInitial)]
    exact fun held => by cases held.symm.trans prod_alt_signal

theorem production_actualCause :
    ActualCause prodO prodActual prodInitial prodHolds ProdRetained [.cause] :=
  ⟨⟨⟨ProdId.cause, List.mem_cons_self⟩,
      singleton_members (by decide : ProdId.cause ∈ prodActual),
      prod_actual_signal⟩,
    production_ac2,
    ac3_singleton prodO prodActual prodInitial prodHolds ProdRetained
      (fun i => mem_singleton (a := ProdId.cause) (i := i))⟩

/-- Replacing the earlier writer and keeping the effect puts that writer in the past. -/
theorem production_butFor_in_past :
    ButFor prodO prodActual prodInitial prodHolds ProdRetained [.cause] ∧
      ActualCause prodO prodActual prodInitial prodHolds ProdRetained [.cause] ∧
      InCausalPast prodO prodActual .cause .effect :=
  ⟨production_butFor, production_actualCause, production_in_past⟩

end Mettapedia.GSLT.Causality.ActualCausation
