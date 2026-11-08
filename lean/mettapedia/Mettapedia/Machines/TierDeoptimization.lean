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
re-entry (`dec_enc`).  `runTiered_eq`: the tiered run observes exactly what the general
run observes from the encoded initial state.

**The faithful cost.**  A refused re-entry leaves the rest of the stream to the general
engine, supported steps included.  `events` lists the transitions the run performs (fast
steps, general steps, hand-overs, re-entries, refused decodings), and `costRun` prices
them.  The per-step sum `costTiered`, which charges every supported step its fast price,
is the cost of a run exactly when no re-entry is refused and hand-overs are free
(`costRun_eq_costTiered`); otherwise it undercharges (`Controls.costTiered_undercharges`).
On the faithful cost:
* `costRun_all_supported`: with every step supported the run costs the fast prices;
* `costRun_le_costDecline`: per-step tiering costs at most declining the whole stream,
  plus `deopt` and the dearer of `reenter` and `refused` per unsupported step;
  `costRun_le_costDecline_free`: at most the decline when hand-overs are free;
* `costRun_lt_costDecline`: with free hand-overs, one unsupported step and one step that
  is strictly cheaper fast *and runs on the fast engine*, tiering is strictly cheaper;
* `costRun_eq_charged`: with no refused re-entry, the run costs the per-step prices with
  `deopt + reenter` per unsupported step.
Of the per-step results, `costTiered_le_costDecline`, `costTieredCharged_le` and
`costTieredCharged_unreached` hold of the faithful cost as stated above;
`costTiered_lt_costDecline` needs its cheaper step to run fast, not only to occur in the
stream: after a refused re-entry it runs on the general engine.

**Local residual execution.**  A tier that chooses, at each step, whether to run it fast
(if supported) or hand it to the general engine, and at each boundary whether to resume
the fast engine (where the state decodes) or keep the general one, never restarts
completed work.  `Path` is the relation of its runs.  Every run observes the general run
(`Path.final`); the forced tier and the whole-stream decline are runs
(`events_path`, `gen_path`); `leastCost` is the least faithful cost over the runs, and is
attained (`leastCost_attained`), never above the forced tier (`leastCost_le_costRun`) or
the decline (`leastCost_le_costDecline`).

**More knowledge, more choices.**  A tier that supports more steps or decodes more states
(`Extends`) has every run of the smaller one, at no greater cost (`Path.extend`), so its
least cost is no greater (`leastCost_mono`).  The forced tier has no such property: one
more supported step can force a stretch onto the fast engine that then pays an extra
hand-over (`Controls.forced_not_monotone`).
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

/-- The per-step price list: each step at its own engine's price.  It is the cost of the
run when no re-entry is refused and hand-overs are free (`costRun_eq_costTiered`). -/
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

/-- The per-step price list with a charge `d` for each hand-over. -/
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

/-! ## The transitions a run performs -/

/-- What the engines do. -/
inductive Event (ι : Type) where
  /-- A supported step on the fast engine. -/
  | fast (i : ι)
  /-- A step on the general engine. -/
  | gen (i : ι)
  /-- The fast state handed to the general engine. -/
  | deopt
  /-- A decoding that succeeds: the fast engine resumes. -/
  | reenter
  /-- A decoding attempted and refused. -/
  | refused
  deriving DecidableEq

/-- The general engine on every step. -/
def eventsGen (is : List ι) : List (Event ι) := is.map Event.gen

/-- The transitions of the tiered run. -/
def events (T : Tiered ι σf σg) : List ι → σf → List (Event ι)
  | [], _ => []
  | i :: is, s =>
    match T.fast i with
    | some f => .fast i :: events T is (f s)
    | none =>
      match T.dec (T.gen i (T.enc s)) with
      | some s' => .deopt :: .gen i :: .reenter :: events T is s'
      | none => .deopt :: .gen i :: .refused :: eventsGen is

/-- Prices of the transitions. -/
structure Prices (ι : Type) where
  /-- A step on the fast engine. -/
  fast : ι → ℕ
  /-- A step on the general engine. -/
  gen : ι → ℕ
  /-- A hand-over to the general engine. -/
  deopt : ℕ
  /-- A decoding that succeeds. -/
  reenter : ℕ
  /-- A decoding refused. -/
  refused : ℕ

namespace Prices

variable (p : Prices ι)

/-- The price of one transition. -/
def price : Event ι → ℕ
  | .fast i => p.fast i
  | .gen i => p.gen i
  | .deopt => p.deopt
  | .reenter => p.reenter
  | .refused => p.refused

/-- The price of a list of transitions. -/
def cost (es : List (Event ι)) : ℕ := (es.map p.price).sum

/-- Hand-overs, re-entries and refusals cost nothing. -/
def Free : Prop := p.deopt = 0 ∧ p.reenter = 0 ∧ p.refused = 0

/-- The dearest hand-over: a deoptimization and either outcome of its decoding. -/
def handOver : ℕ := p.deopt + max p.reenter p.refused

@[simp] theorem cost_nil : p.cost [] = 0 := rfl

@[simp] theorem cost_cons (e : Event ι) (es : List (Event ι)) :
    p.cost (e :: es) = p.price e + p.cost es := by
  simp [cost]

theorem cost_eventsGen (is : List ι) : p.cost (eventsGen is) = (is.map p.gen).sum := by
  simp [cost, eventsGen, List.map_map, Function.comp_def, price]

theorem handOver_free (h : p.Free) : p.handOver = 0 := by
  simp [handOver, h.1, h.2.1, h.2.2]

end Prices

/-- **The faithful cost** of the tiered run: the price of every transition it performs. -/
def costRun (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) : ℕ :=
  p.cost (events T is s)

/-- Supported steps are never dearer fast. -/
def FastCheaper (T : Tiered ι σf σg) (p : Prices ι) : Prop :=
  ∀ i, supported T i = true → p.fast i ≤ p.gen i

theorem events_cons_fast {T : Tiered ι σf σg} {i : ι} {is : List ι} {s : σf} {f : σf → σf}
    (hf : T.fast i = some f) : events T (i :: is) s = .fast i :: events T is (f s) := by
  simp [events, hf]

theorem events_cons_reenter {T : Tiered ι σf σg} {i : ι} {is : List ι} {s s' : σf}
    (hf : T.fast i = none) (hd : T.dec (T.gen i (T.enc s)) = some s') :
    events T (i :: is) s = .deopt :: .gen i :: .reenter :: events T is s' := by
  simp [events, hf, hd]

theorem events_cons_refused {T : Tiered ι σf σg} {i : ι} {is : List ι} {s : σf}
    (hf : T.fast i = none) (hd : T.dec (T.gen i (T.enc s)) = none) :
    events T (i :: is) s = .deopt :: .gen i :: .refused :: eventsGen is := by
  simp [events, hf, hd]

theorem supported_of_fast {T : Tiered ι σf σg} {i : ι} {f : σf → σf} (hf : T.fast i = some f) :
    supported T i = true := by
  simp [supported, hf]

theorem unsupported_of_fast {T : Tiered ι σf σg} {i : ι} (hf : T.fast i = none) :
    supported T i = false := by
  simp [supported, hf]

theorem unsupportedCount_cons (T : Tiered ι σf σg) (i : ι) (is : List ι) :
    unsupportedCount T (i :: is) =
      unsupportedCount T is + if supported T i then 0 else 1 := by
  by_cases h : supported T i = true
  · simp [unsupportedCount, h]
  · simp only [Bool.not_eq_true] at h
    simp [unsupportedCount, h]

/-- With every step supported, the run costs the fast prices and makes no hand-over. -/
theorem costRun_all_supported (T : Tiered ι σf σg) (p : Prices ι) :
    ∀ (is : List ι) (s : σf), is.all (supported T) = true →
      costRun T p is s = (is.map p.fast).sum
  | [], _, _ => rfl
  | i :: is, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp h.1
    have ih := costRun_all_supported T p is (f s) h.2
    simp only [costRun] at ih ⊢
    rw [events_cons_fast hf, Prices.cost_cons, ih]
    simp [Prices.price]

/-- The faithful cost is at most the general cost of the stream plus the dearest
hand-over at each unsupported step. -/
theorem costRun_le_gen_add (T : Tiered ι σf σg) (p : Prices ι) (h : FastCheaper T p) :
    ∀ (is : List ι) (s : σf),
      costRun T p is s ≤ (is.map p.gen).sum + p.handOver * unsupportedCount T is
  | [], _ => by simp [costRun, events]
  | i :: is, s => by
    cases hf : T.fast i with
    | some f =>
      have ih := costRun_le_gen_add T p h is (f s)
      have hle := h i (supported_of_fast hf)
      simp only [costRun] at ih ⊢
      rw [events_cons_fast hf, Prices.cost_cons, unsupportedCount_cons,
        if_pos (supported_of_fast hf)]
      simp only [Prices.price, List.map_cons, List.sum_cons, add_zero]
      omega
    | none =>
      have hs := unsupported_of_fast hf
      cases hd : T.dec (T.gen i (T.enc s)) with
      | some s' =>
        have ih := costRun_le_gen_add T p h is s'
        have hh : p.deopt + p.reenter ≤ p.handOver := by
          simp only [Prices.handOver]
          have := le_max_left p.reenter p.refused
          omega
        simp only [costRun] at ih ⊢
        rw [events_cons_reenter hf hd, unsupportedCount_cons, hs]
        simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons,
          Prices.cost_cons, Prices.price]
        rw [mul_add, mul_one]
        omega
      | none =>
        have hh : p.deopt + p.refused ≤ p.handOver := by
          simp only [Prices.handOver]
          have := le_max_right p.reenter p.refused
          omega
        simp only [costRun]
        rw [events_cons_refused hf hd, unsupportedCount_cons, hs]
        simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons,
          Prices.cost_cons, Prices.price, Prices.cost_eventsGen]
        rw [mul_add, mul_one]
        omega

/-- **Tiering against the decline, faithfully.**  The run costs at most declining the
whole stream, plus the dearest hand-over at each unsupported step. -/
theorem costRun_le_costDecline (T : Tiered ι σf σg) (p : Prices ι) (h : FastCheaper T p)
    (is : List ι) (s : σf) :
    costRun T p is s ≤ costDecline T p.fast p.gen is + p.handOver * unsupportedCount T is := by
  unfold costDecline
  split
  · next hall => rw [costRun_all_supported T p is s hall]; omega
  · exact costRun_le_gen_add T p h is s

/-- With free hand-overs, tiering never costs more than declining the whole stream. -/
theorem costRun_le_costDecline_free (T : Tiered ι σf σg) (p : Prices ι) (hfree : p.Free)
    (h : FastCheaper T p) (is : List ι) (s : σf) :
    costRun T p is s ≤ costDecline T p.fast p.gen is := by
  have := costRun_le_costDecline T p h is s
  rw [p.handOver_free hfree, zero_mul, add_zero] at this
  exact this

/-- With no refused re-entry, the run costs the per-step prices with `deopt + reenter`
for each hand-over. -/
theorem costRun_eq_charged (T : Tiered ι σf σg) (p : Prices ι) :
    ∀ (is : List ι) (s : σf), Event.refused ∉ events T is s →
      costRun T p is s = costTieredCharged T p.fast p.gen (p.deopt + p.reenter) is
  | [], _, _ => rfl
  | i :: is, s, hnr => by
    simp only [costRun] at *
    cases hf : T.fast i with
    | some f =>
      rw [events_cons_fast hf] at hnr ⊢
      have ih := costRun_eq_charged T p is (f s) (fun hm => hnr (List.mem_cons_of_mem _ hm))
      simp only [costRun] at ih
      rw [Prices.cost_cons, ih]
      simp [costTieredCharged, supported_of_fast hf, Prices.price]
    | none =>
      cases hd : T.dec (T.gen i (T.enc s)) with
      | some s' =>
        rw [events_cons_reenter hf hd] at hnr ⊢
        have ih := costRun_eq_charged T p is s' (fun hm => hnr (by simp [hm]))
        simp only [costRun] at ih
        simp only [Prices.cost_cons, ih, Prices.price]
        simp only [costTieredCharged, List.map_cons, List.sum_cons, unsupported_of_fast hf,
          Bool.false_eq_true, if_false]
        omega
      | none =>
        rw [events_cons_refused hf hd] at hnr
        exact absurd (by simp) hnr

/-- **When the per-step sum is the cost.**  With free hand-overs and no refused
re-entry, the faithful cost is `costTiered`. -/
theorem costRun_eq_costTiered (T : Tiered ι σf σg) (p : Prices ι) (hfree : p.Free)
    (is : List ι) (s : σf) (hnr : Event.refused ∉ events T is s) :
    costRun T p is s = costTiered T p.fast p.gen is := by
  rw [costRun_eq_charged T p is s hnr, hfree.1, hfree.2.1, costTieredCharged_eq]
  simp

/-- A run with free hand-overs whose fast engine runs a strictly cheaper step costs strictly
less than the general engine on the whole stream. -/
theorem costRun_lt_gen (T : Tiered ι σf σg) (p : Prices ι) (hfree : p.Free)
    (h : FastCheaper T p) (j : ι) (hj : p.fast j < p.gen j) :
    ∀ (is : List ι) (s : σf), Event.fast j ∈ events T is s →
      costRun T p is s < (is.map p.gen).sum
  | [], _, hm => by simp [events] at hm
  | i :: is, s, hm => by
    have hle_rest : ∀ s', costRun T p is s' ≤ (is.map p.gen).sum := fun s' => by
      have := costRun_le_gen_add T p h is s'
      rwa [p.handOver_free hfree, zero_mul, add_zero] at this
    simp only [costRun] at *
    cases hf : T.fast i with
    | some f =>
      rw [events_cons_fast hf] at hm ⊢
      rw [Prices.cost_cons]
      simp only [Prices.price, List.map_cons, List.sum_cons]
      have hle := h i (supported_of_fast hf)
      rcases List.mem_cons.mp hm with he | hm'
      · cases he
        have := hle_rest (f s)
        omega
      · have := costRun_lt_gen T p hfree h j hj is (f s) hm'
        simp only [costRun] at this
        omega
    | none =>
      cases hd : T.dec (T.gen i (T.enc s)) with
      | some s' =>
        rw [events_cons_reenter hf hd] at hm ⊢
        have hm' : Event.fast j ∈ events T is s' := by simpa using hm
        have := costRun_lt_gen T p hfree h j hj is s' hm'
        simp only [costRun] at this
        simp only [Prices.cost_cons, Prices.price, hfree.1, hfree.2.1, List.map_cons,
          List.sum_cons]
        omega
      | none =>
        rw [events_cons_refused hf hd] at hm
        simp [eventsGen] at hm

/-- **The cliff, faithfully.**  With free hand-overs, one unsupported step, and one step
strictly cheaper fast that the fast engine runs, tiering is strictly cheaper than the
whole-stream decline. -/
theorem costRun_lt_costDecline (T : Tiered ι σf σg) (p : Prices ι) (hfree : p.Free)
    (h : FastCheaper T p) (is : List ι) (s : σf)
    (hu : ∃ u ∈ is, supported T u = false) (j : ι) (hj : Event.fast j ∈ events T is s)
    (hlt : p.fast j < p.gen j) :
    costRun T p is s < costDecline T p.fast p.gen is := by
  have hnot : is.all (supported T) = false := by
    obtain ⟨u, hu, hfalse⟩ := hu
    rw [Bool.eq_false_iff]
    intro hall
    rw [List.all_eq_true] at hall
    rw [hall u hu] at hfalse
    exact absurd hfalse (by decide)
  simp only [costDecline, hnot, Bool.false_eq_true, if_false]
  exact costRun_lt_gen T p hfree h j hlt is s hj

/-! ## Local residual execution: the tier that chooses -/

/-- Where a run of the choosing tier is. -/
inductive Mode (σf σg : Type) where
  /-- On the fast engine. -/
  | onFast (s : σf)
  /-- At a boundary: the step before it ran on the general engine. -/
  | boundary (g : σg)
  /-- On the general engine. -/
  | onGen (g : σg)

/-- The general state a mode stands for. -/
def Mode.state (T : Tiered ι σf σg) : Mode σf σg → σg
  | .onFast s => T.enc s
  | .boundary g => g
  | .onGen g => g

/-- The runs of the tier that chooses.  On the fast engine a supported step may run fast,
and any step may be handed over: the general engine runs it, as a residual, from the
encoded state.  At the boundary after a general step the run may resume the fast engine
where the state decodes, attempt a decoding that is refused, or keep the general engine.
Nothing already done is done again. -/
inductive Path (T : Tiered ι σf σg) : List ι → Mode σf σg → List (Event ι) → σg → Prop
  | fastDone (s : σf) : Path T [] (.onFast s) [] (T.enc s)
  | fast {i : ι} {is : List ι} {s : σf} {f : σf → σf} {es : List (Event ι)} {g : σg}
      (hf : T.fast i = some f) (h : Path T is (.onFast (f s)) es g) :
      Path T (i :: is) (.onFast s) (.fast i :: es) g
  | handOver {i : ι} {is : List ι} {s : σf} {es : List (Event ι)} {g : σg}
      (h : Path T is (.boundary (T.gen i (T.enc s))) es g) :
      Path T (i :: is) (.onFast s) (.deopt :: .gen i :: es) g
  | resume {is : List ι} {g : σg} {s : σf} {es : List (Event ι)} {g' : σg}
      (hd : T.dec g = some s) (h : Path T is (.onFast s) es g') :
      Path T is (.boundary g) (.reenter :: es) g'
  | refuse {is : List ι} {g : σg} {es : List (Event ι)} {g' : σg}
      (hd : T.dec g = none) (h : Path T is (.onGen g) es g') :
      Path T is (.boundary g) (.refused :: es) g'
  | keep {is : List ι} {g : σg} {es : List (Event ι)} {g' : σg}
      (h : Path T is (.onGen g) es g') : Path T is (.boundary g) es g'
  | genDone (g : σg) : Path T [] (.onGen g) [] g
  | gen {i : ι} {is : List ι} {g : σg} {es : List (Event ι)} {g' : σg}
      (h : Path T is (.boundary (T.gen i g)) es g') :
      Path T (i :: is) (.onGen g) (.gen i :: es) g'

/-- **Every run observes the general run**: whatever it chooses, it ends where the general
engine ends from the state it started in. -/
theorem Path.final {T : Tiered ι σf σg} {is : List ι} {m : Mode σf σg} {es : List (Event ι)}
    {g : σg} (h : Path T is m es g) : g = runGen T is (m.state T) := by
  induction h with
  | fastDone s => rfl
  | fast hf _ ih =>
    simp only [Mode.state] at ih ⊢
    rw [ih, T.sim _ _ hf]
    rfl
  | handOver _ ih =>
    simp only [Mode.state] at ih ⊢
    rw [ih]
    rfl
  | resume hd _ ih =>
    simp only [Mode.state] at ih ⊢
    rw [ih, T.dec_enc _ _ hd]
  | refuse _ _ ih => simpa [Mode.state] using ih
  | keep _ ih => simpa [Mode.state] using ih
  | genDone g => rfl
  | gen _ ih =>
    simp only [Mode.state] at ih ⊢
    rw [ih]
    rfl

/-- The general engine on the rest of the stream is a run. -/
theorem gen_path (T : Tiered ι σf σg) :
    ∀ (is : List ι) (g : σg), Path T is (.onGen g) (eventsGen is) (runGen T is g)
  | [], g => .genDone g
  | i :: is, g => .gen (.keep (gen_path T is (T.gen i g)))

/-- The forced tier is a run. -/
theorem events_path (T : Tiered ι σf σg) :
    ∀ (is : List ι) (s : σf), Path T is (.onFast s) (events T is s) (runTiered T is s)
  | [], s => .fastDone s
  | i :: is, s => by
    cases hf : T.fast i with
    | some f =>
      rw [events_cons_fast hf]
      simp only [runTiered, hf]
      exact .fast hf (events_path T is (f s))
    | none =>
      cases hd : T.dec (T.gen i (T.enc s)) with
      | some s' =>
        rw [events_cons_reenter hf hd]
        simp only [runTiered, hf, hd]
        exact .handOver (.resume hd (events_path T is s'))
      | none =>
        rw [events_cons_refused hf hd]
        simp only [runTiered, hf, hd]
        exact .handOver (.refuse hd (gen_path T is _))

/-- A run from the start: on the fast engine, or declining the stream at once. -/
def RootPath (T : Tiered ι σf σg) (is : List ι) (s : σf) (es : List (Event ι)) (g : σg) :
    Prop :=
  Path T is (.onFast s) es g ∨ Path T is (.onGen (T.enc s)) es g

theorem RootPath.final {T : Tiered ι σf σg} {is : List ι} {s : σf} {es : List (Event ι)}
    {g : σg} (h : RootPath T is s es g) : g = runGen T is (T.enc s) := by
  rcases h with h | h
  · exact h.final
  · exact h.final

/-- The faithful costs of the choosing tier's runs from the start. -/
def runCosts (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) : Set ℕ :=
  {c | ∃ es g, RootPath T is s es g ∧ p.cost es = c}

/-- The least faithful cost of a run of the choosing tier. -/
noncomputable def leastCost (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) : ℕ :=
  sInf (runCosts T p is s)

theorem runCosts_nonempty (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) :
    (runCosts T p is s).Nonempty :=
  ⟨_, _, _, Or.inl (events_path T is s), rfl⟩

theorem leastCost_le {T : Tiered ι σf σg} (p : Prices ι) {is : List ι} {s : σf}
    {es : List (Event ι)} {g : σg} (h : RootPath T is s es g) : leastCost T p is s ≤ p.cost es :=
  Nat.sInf_le ⟨es, g, h, rfl⟩

/-- **The least cost is a run's**: some run has it, and it observes the general run. -/
theorem leastCost_attained (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) :
    ∃ es g, RootPath T is s es g ∧ p.cost es = leastCost T p is s ∧
      g = runGen T is (T.enc s) := by
  obtain ⟨es, g, h, hc⟩ := Nat.sInf_mem (runCosts_nonempty T p is s)
  exact ⟨es, g, h, hc, h.final⟩

/-- Choosing never costs more than the forced tier. -/
theorem leastCost_le_costRun (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) :
    leastCost T p is s ≤ costRun T p is s :=
  leastCost_le p (Or.inl (events_path T is s))

/-- **Never costlier than the general route.**  Choosing never costs more than declining
the whole stream, whatever the prices of hand-overs. -/
theorem leastCost_le_costDecline (T : Tiered ι σf σg) (p : Prices ι) (is : List ι) (s : σf) :
    leastCost T p is s ≤ costDecline T p.fast p.gen is := by
  unfold costDecline
  split
  · next hall =>
    rw [← costRun_all_supported T p is s hall]
    exact leastCost_le_costRun T p is s
  · have := leastCost_le p (Or.inr (gen_path T is (T.enc s)))
    rwa [Prices.cost_eventsGen] at this

/-- `T'` knows at least what `T` knows: the same general engine and encoding, every step
`T` runs fast run the same way, and every state `T` decodes decoded the same way. -/
structure Extends (T T' : Tiered ι σf σg) : Prop where
  gen : T'.gen = T.gen
  enc : T'.enc = T.enc
  fast : ∀ i f, T.fast i = some f → T'.fast i = some f
  dec : ∀ g s, T.dec g = some s → T'.dec g = some s

theorem Prices.cost_le_of_sublist (p : Prices ι) {es es' : List (Event ι)}
    (h : es'.Sublist es) : p.cost es' ≤ p.cost es := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => simp only [Prices.cost_cons]; omega
  | cons_cons a _ ih => simp only [Prices.cost_cons]; omega

theorem Prices.cost_congr {p q : Prices ι} {es : List (Event ι)}
    (h : ∀ e ∈ es, p.price e = q.price e) : p.cost es = q.cost es := by
  simp only [Prices.cost]
  congr 1
  exact List.map_congr_left h

/-- The instruction of a fast step. -/
def Event.fastOf : Event ι → Option ι
  | .fast i => some i
  | _ => none

/-- The steps a run takes on the fast engine are steps of its stream, in order. -/
theorem Path.fast_sublist {T : Tiered ι σf σg} {is : List ι} {m : Mode σf σg}
    {es : List (Event ι)} {g : σg} (h : Path T is m es g) :
    (es.filterMap Event.fastOf).Sublist is := by
  induction h with
  | fastDone s => exact List.Sublist.slnil
  | fast _ _ ih =>
    simp only [List.filterMap_cons, Event.fastOf]
    exact ih.cons_cons _
  | handOver _ ih =>
    simp only [List.filterMap_cons, Event.fastOf]
    exact ih.cons _
  | resume _ _ ih =>
    simp only [List.filterMap_cons, Event.fastOf]
    exact ih
  | refuse _ _ ih =>
    simp only [List.filterMap_cons, Event.fastOf]
    exact ih
  | keep _ ih => exact ih
  | genDone g => exact List.Sublist.slnil
  | gen _ ih =>
    simp only [List.filterMap_cons, Event.fastOf]
    exact ih.cons _

/-- Every run of a tier is a run of any tier that knows more, but for refusals the larger
tier no longer makes: its transitions are a sublist of the original's. -/
theorem Path.extend {T T' : Tiered ι σf σg} (hx : Extends T T') {is : List ι}
    {m : Mode σf σg} {es : List (Event ι)} {g : σg} (h : Path T is m es g) :
    ∃ es', Path T' is m es' g ∧ es'.Sublist es := by
  induction h with
  | fastDone s =>
    have := Path.fastDone (T := T') s
    rw [hx.enc] at this
    exact ⟨[], this, List.Sublist.slnil⟩
  | fast hf _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    exact ⟨_, .fast (hx.fast _ _ hf) h', hs.cons_cons _⟩
  | @handOver i is s es g _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    refine ⟨.deopt :: .gen i :: es', ?_, (hs.cons_cons _).cons_cons _⟩
    apply Path.handOver
    rw [hx.gen, hx.enc]
    exact h'
  | resume hd _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    exact ⟨_, .resume (hx.dec _ _ hd) h', hs.cons_cons _⟩
  | @refuse is g es g' hd _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    cases hd' : T'.dec g with
    | none => exact ⟨_, .refuse hd' h', hs.cons_cons _⟩
    | some _ => exact ⟨es', .keep h', hs.cons _⟩
  | keep _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    exact ⟨es', .keep h', hs⟩
  | genDone g => exact ⟨[], .genDone g, List.Sublist.slnil⟩
  | @gen i is g es g' _ ih =>
    obtain ⟨es', h', hs⟩ := ih
    refine ⟨.gen i :: es', ?_, hs.cons_cons _⟩
    apply Path.gen
    rw [hx.gen]
    exact h'

/-- A root run of a tier is, up to refusals, a root run of any tier that knows more. -/
theorem RootPath.extend {T T' : Tiered ι σf σg} (hx : Extends T T') {is : List ι} {s : σf}
    {es : List (Event ι)} {g : σg} (h : RootPath T is s es g) :
    ∃ es', RootPath T' is s es' g ∧ es'.Sublist es := by
  rcases h with h | h
  · obtain ⟨es', h', hs⟩ := h.extend hx
    exact ⟨es', Or.inl h', hs⟩
  · obtain ⟨es', h', hs⟩ := h.extend hx
    rw [← hx.enc] at h'
    exact ⟨es', Or.inr h', hs⟩

theorem RootPath.fast_sublist {T : Tiered ι σf σg} {is : List ι} {s : σf}
    {es : List (Event ι)} {g : σg} (h : RootPath T is s es g) :
    (es.filterMap Event.fastOf).Sublist is := by
  rcases h with h | h
  · exact h.fast_sublist
  · exact h.fast_sublist

/-- **More knowledge, more choices.**  A tier that knows more has a least cost no greater:
nothing it learns forces it off a run it had. -/
theorem leastCost_mono {T T' : Tiered ι σf σg} (hx : Extends T T') (p : Prices ι)
    (is : List ι) (s : σf) : leastCost T' p is s ≤ leastCost T p is s := by
  obtain ⟨es, g, h, hc, -⟩ := leastCost_attained T p is s
  obtain ⟨es', h', hs⟩ := h.extend hx
  exact (leastCost_le p h').trans ((p.cost_le_of_sublist hs).trans hc.le)

/-! ## Controls -/

namespace Controls

/-- A tier whose decoding is always refused: `true` steps are supported, `false` steps are
not. -/
def refusing : Tiered Bool Unit Unit where
  gen := fun _ _ => ()
  fast := fun b => if b then some id else none
  enc := id
  dec := fun _ => none
  sim := fun _ _ _ _ => rfl
  dec_enc := fun _ _ h => by cases h

/-- Fast steps cost 1, general steps 30, hand-overs nothing. -/
def flat : Prices Bool := ⟨fun _ => 1, fun _ => 30, 0, 0, 0⟩

/-- **The per-step sum undercharges.**  On `[false, true]` the decoding after the first step
is refused, so the general engine runs both steps (60); the per-step sum charges the
second at its fast price (31). -/
theorem costTiered_undercharges :
    costTiered refusing flat.fast flat.gen [false, true] = 31 ∧
      costRun refusing flat [false, true] () = 60 ∧
      events refusing [false, true] () = [.deopt, .gen false, .refused, .gen true] := by
  refine ⟨rfl, rfl, rfl⟩

/-- A counter: the general state counts steps, and only the count `2` decodes. -/
def counter (supports : ℕ → Bool) : Tiered ℕ ℕ ℕ where
  gen := fun _ g => g + 1
  fast := fun i => if supports i then some (· + 1) else none
  enc := id
  dec := fun g => if g = 2 then some g else none
  sim := by
    intro i f hf s
    by_cases h : supports i = true
    · simp only [h, if_true, Option.some.injEq] at hf
      subst hf
      rfl
    · simp [h] at hf
  dec_enc := by
    intro g s h
    change (if g = 2 then some g else none) = some s at h
    split at h
    · cases h; rfl
    · cases h

/-- Hand-overs cost 20 and successful decodings 20, refusals nothing. -/
def charged : Prices ℕ := ⟨fun _ => 1, fun _ => 30, 20, 20, 0⟩

/-- **The forced tier is not monotone.**  Supporting step `0` as well keeps the run on the
fast engine until step `1`, whose hand-over now decodes, so step `2` is handed over
again: the run with more support costs 121, the one with less 110.  The choosing tier
loses nothing by the extra support (`leastCost_mono`). -/
theorem forced_not_monotone :
    Extends (counter fun _ => false) (counter fun i => decide (i = 0)) ∧
      costRun (counter fun _ => false) charged [0, 1, 2] 0 = 110 ∧
      costRun (counter fun i => decide (i = 0)) charged [0, 1, 2] 0 = 121 := by
  refine ⟨⟨rfl, rfl, fun i f h => by simp [counter] at h, fun _ _ h => h⟩, ?_, ?_⟩
  · decide
  · decide

end Controls

end Mettapedia.Machines.TierDeoptimization
