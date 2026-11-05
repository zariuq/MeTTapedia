import Mathlib.Tactic

/-!
# Per-step tiering: a fast engine that hands over exactly where it cannot simulate

A compiled route that declines a whole call graph because one step it cannot run
*might* be reached turns a program into a slow one even when that step never runs.
Measured (11/04, frozen opt binary): a member scan over constructor lists runs in
register code at 74M instructions; adding a branch that is never taken but contains
`superpose` or `println!` declines the whole call graph at compile time, and the same
answers cost 198-200M instructions (2.7x).

The remedy is tiering per step: the fast engine runs every step it supports; at a step
it does not support it *deoptimizes*, encoding its state as the general engine's state;
the general engine runs that step; and when the resulting state decodes into a fast
state, execution re-enters the fast engine.

The model: an instruction stream `List ι`, a general engine `gen` on states `σg`, a
partial fast engine `fast` on states `σf`, an encoding `enc : σf → σg` (frame
reification), and a partial decoding `dec : σg → Option σf` (re-entry).  The two
hypotheses are the commuting square of each supported step (`sim`) and soundness of
re-entry (`dec_enc`).

This file proves:
* `runTiered_eq`: the tiered run observes exactly what the general run observes from the
  encoded initial state (exact transfer);
* `costTiered_le_costDecline`: when a supported step is never dearer on the fast
  engine, per-step tiering never costs more than declining the whole stream (whenever
  every step is supported the two coincide);
* `costTiered_lt_costDecline`: with one unsupported step and one supported step that is
  strictly cheaper fast, tiering is strictly cheaper: the whole-stream decline is a cliff;
* `costTieredCharged_le`: with a transfer charge `d` for each hand-over, tiering costs at
  most the decline plus `d` per unsupported step, so the only price of tiering is the
  hand-overs actually made.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TierDeoptimization

/-- A fast engine and a general engine over one instruction stream. -/
structure Tiered (ι σf σg : Type) where
  /-- The general engine: every instruction. -/
  gen : ι → σg → σg
  /-- The fast engine: the instructions it supports. -/
  fast : ι → Option (σf → σf)
  /-- Deoptimization: the fast state as a general state. -/
  enc : σf → σg
  /-- Re-entry: a general state the fast engine can continue from, if any. -/
  dec : σg → Option σf
  /-- Each supported step commutes with the encoding. -/
  sim : ∀ i f, fast i = some f → ∀ s, enc (f s) = gen i (enc s)
  /-- Re-entry is sound: a decoded state encodes back to the state it came from. -/
  dec_enc : ∀ g s, dec g = some s → enc s = g

variable {ι σf σg : Type}

/-- The general engine on the whole stream. -/
def runGen (T : Tiered ι σf σg) : List ι → σg → σg
  | [], g => g
  | i :: is, g => runGen T is (T.gen i g)

/-- Tiering per step: supported steps run fast; an unsupported step deoptimizes, runs
generally, and re-enters the fast engine when the resulting state decodes. -/
def runTiered (T : Tiered ι σf σg) : List ι → σf → σg
  | [], s => T.enc s
  | i :: is, s =>
    match T.fast i with
    | some f => runTiered T is (f s)
    | none =>
      match T.dec (T.gen i (T.enc s)) with
      | some s' => runTiered T is s'
      | none => runGen T is (T.gen i (T.enc s))

/-- Exact transfer: tiering observes what the general engine observes. -/
theorem runTiered_eq (T : Tiered ι σf σg) (is : List ι) (s : σf) :
    runTiered T is s = runGen T is (T.enc s) := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    cases hf : T.fast i with
    | some f =>
      simp only [runTiered, hf, runGen]
      rw [ih, T.sim i f hf s]
    | none =>
      cases hd : T.dec (T.gen i (T.enc s)) with
      | some s' =>
        simp only [runTiered, hf, hd, runGen]
        rw [ih, T.dec_enc _ _ hd]
      | none =>
        simp only [runTiered, hf, hd, runGen]

/-- Whether the fast engine supports an instruction. -/
def supported (T : Tiered ι σf σg) (i : ι) : Bool := (T.fast i).isSome

/-- The cost of tiering: each step pays its own engine's price. -/
def costTiered (T : Tiered ι σf σg) (cf cg : ι → ℕ) (is : List ι) : ℕ :=
  (is.map fun i => if supported T i then cf i else cg i).sum

/-- The cost of declining the whole stream unless every step is supported. -/
def costDecline (T : Tiered ι σf σg) (cf cg : ι → ℕ) (is : List ι) : ℕ :=
  if is.all (supported T) then (is.map cf).sum else (is.map cg).sum

theorem costTiered_le_general (T : Tiered ι σf σg) (cf cg : ι → ℕ)
    (h : ∀ i, supported T i = true → cf i ≤ cg i) (is : List ι) :
    costTiered T cf cg is ≤ (is.map cg).sum := by
  induction is with
  | nil => simp [costTiered]
  | cons i is ih =>
    simp only [costTiered, List.map_cons, List.sum_cons] at ih ⊢
    have hi : (if supported T i then cf i else cg i) ≤ cg i := by
      by_cases hs : supported T i = true
      · simp only [hs, if_true]; exact h i hs
      · simp only [Bool.not_eq_true] at hs; simp [hs]
    omega

theorem costTiered_all_supported (T : Tiered ι σf σg) (cf cg : ι → ℕ) (is : List ι)
    (hall : is.all (supported T) = true) :
    costTiered T cf cg is = (is.map cf).sum := by
  induction is with
  | nil => simp [costTiered]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    have := ih hall.2
    simp only [costTiered, List.map_cons, List.sum_cons] at this ⊢
    simp [hall.1, this]

/-- Tiering never costs more than declining the whole stream. -/
theorem costTiered_le_costDecline (T : Tiered ι σf σg) (cf cg : ι → ℕ)
    (h : ∀ i, supported T i = true → cf i ≤ cg i) (is : List ι) :
    costTiered T cf cg is ≤ costDecline T cf cg is := by
  unfold costDecline
  split
  · next hall => exact le_of_eq (costTiered_all_supported T cf cg is hall)
  · exact costTiered_le_general T cf cg h is

/-- One supported step strictly cheaper fast makes tiering strictly cheaper than running
every step generally. -/
theorem costTiered_lt_general (T : Tiered ι σf σg) (cf cg : ι → ℕ)
    (h : ∀ i, supported T i = true → cf i ≤ cg i) (is : List ι) (j : ι) (hj : j ∈ is)
    (hsj : supported T j = true) (hlt : cf j < cg j) :
    costTiered T cf cg is < (is.map cg).sum := by
  induction is with
  | nil => simp at hj
  | cons i is ih =>
    have hrest := costTiered_le_general T cf cg h is
    simp only [costTiered, List.map_cons, List.sum_cons] at hrest ih ⊢
    have hle_i : (if supported T i then cf i else cg i) ≤ cg i := by
      by_cases hs : supported T i = true
      · simp only [hs, if_true]; exact h i hs
      · simp only [Bool.not_eq_true] at hs; simp [hs]
    rcases List.mem_cons.mp hj with rfl | hj'
    · have : (if supported T j then cf j else cg j) < cg j := by simp [hsj, hlt]
      omega
    · have := ih hj'
      omega

/-- With one unsupported step and one supported step strictly cheaper fast, tiering is
strictly cheaper than the whole-stream decline: the decline is a cliff. -/
theorem costTiered_lt_costDecline (T : Tiered ι σf σg) (cf cg : ι → ℕ)
    (h : ∀ i, supported T i = true → cf i ≤ cg i) (is : List ι)
    (hu : ∃ u ∈ is, supported T u = false)
    (hc : ∃ j ∈ is, supported T j = true ∧ cf j < cg j) :
    costTiered T cf cg is < costDecline T cf cg is := by
  have hnot : is.all (supported T) = false := by
    obtain ⟨u, hu, hfalse⟩ := hu
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    have := hall u hu
    rw [hfalse] at this
    exact Bool.false_ne_true this
  simp only [costDecline, hnot, Bool.false_eq_true, if_false]
  obtain ⟨j, hj, hsj, hlt⟩ := hc
  exact costTiered_lt_general T cf cg h is j hj hsj hlt

/-- The cost of tiering with a charge `d` for each hand-over. -/
def costTieredCharged (T : Tiered ι σf σg) (cf cg : ι → ℕ) (d : ℕ) (is : List ι) : ℕ :=
  (is.map fun i => if supported T i then cf i else cg i + d).sum

/-- The number of unsupported steps. -/
def unsupportedCount (T : Tiered ι σf σg) (is : List ι) : ℕ :=
  (is.filter fun i => !supported T i).length

theorem costTieredCharged_eq (T : Tiered ι σf σg) (cf cg : ι → ℕ) (d : ℕ) (is : List ι) :
    costTieredCharged T cf cg d is = costTiered T cf cg is + d * unsupportedCount T is := by
  induction is with
  | nil => simp [costTieredCharged, costTiered, unsupportedCount]
  | cons i is ih =>
    simp only [costTieredCharged, costTiered, unsupportedCount, List.map_cons,
      List.sum_cons, List.filter_cons] at ih ⊢
    by_cases hs : supported T i = true
    · simp only [hs, if_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [ih]; ring
    · simp only [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, if_false, Bool.not_false, if_true,
        List.length_cons]
      rw [ih]; ring

/-- The only price of tiering is the hand-overs actually made. -/
theorem costTieredCharged_le (T : Tiered ι σf σg) (cf cg : ι → ℕ) (d : ℕ)
    (h : ∀ i, supported T i = true → cf i ≤ cg i) (is : List ι) :
    costTieredCharged T cf cg d is ≤
      costDecline T cf cg is + d * unsupportedCount T is := by
  rw [costTieredCharged_eq]
  have := costTiered_le_costDecline T cf cg h is
  omega

/-- A stream whose unsupported steps are never reached pays no hand-over: with every
step on the path supported, the charged tiered cost is the fast cost. -/
theorem costTieredCharged_unreached (T : Tiered ι σf σg) (cf cg : ι → ℕ) (d : ℕ)
    (is : List ι) (hall : is.all (supported T) = true) :
    costTieredCharged T cf cg d is = (is.map cf).sum := by
  rw [costTieredCharged_eq, costTiered_all_supported T cf cg is hall]
  have : unsupportedCount T is = 0 := by
    simp only [unsupportedCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx
    rw [List.all_eq_true] at hall
    simp [hall x hx]
  rw [this]; ring

end Mettapedia.Machines.TierDeoptimization
