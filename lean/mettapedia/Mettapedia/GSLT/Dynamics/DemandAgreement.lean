import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# When eager, lazy, and resampling evaluation agree

A specification does not choose an evaluation order. Eager evaluation, lazy
evaluation with sharing, and deliberate resampling are commitments inside that
specification. They agree on answers exactly along two lines.

**Discarding.** `k a b = a`. Lazily `b` is never run, so the answer is one `a`.
Eagerly `b` is run and thrown away, and each of its answers still contributes
one `a`. Over bags (multisets: lists up to permutation) the two agree exactly
when `b` has one answer. Over supports (the set of answers) they agree exactly
when `b` has at least one answer. No answer at all is the split: eager
discarding returns nothing, and lazy discarding returns one `a`.

**Copying.** `let x = b in (x, x)`. Sharing observes one answer and uses it
twice. Resampling draws once per use. Over bags the two agree exactly when `b`
has at most one answer. Over supports they agree exactly when the support has
at most one element. Two copies of one answer therefore copy the same way as
sets and not as bags.

**Several uses.** A let-bound computation used `n` times, eagerly and with
sharing, agrees with the same computation used lazily and with sharing exactly
when `n` is at least one or `b` is discardable. Sharing agrees with resampling
exactly when `n` is at most one or `b` is copyable. On supports of bags the
lines are at least one use or at least one answer, and at most one use or a
support of at most one element.

A coin with answers `heads` and `tails` is the negative example. Eager
discarding returns two copies and lazy discarding one, while the supports
agree. Sharing returns two pairs and resampling four, and the supports still
disagree: two diagonal pairs against four.

These statements compare bags and supports of values. An effect emitted while a
value is produced is not part of either carrier, so agreement of values says
nothing about the event trace.

The same line is the one a Markov category draws with `copy` and `discard`: a
deterministic map is one that can be copied, and a normalized map is one that
can be discarded (Fritz 2020; Führmann 1999). This module does not build that
layer.
-/

namespace Mettapedia.GSLT.Dynamics.DemandAgreement

set_option autoImplicit false

/-- `n` copies of one answer, in one list. Zero copies is the empty list. -/
def shareTuple {α : Type} (n : Nat) (x : α) : List α :=
  List.replicate n x

/-! ## Bags -/

section Bags

variable {α : Type}

open Multiset

/-- Lazy discarding never runs `b`. -/
def lazyDiscard (a : α) : Multiset α :=
  {a}

/-- Eager discarding runs `b` and drops every answer. Each answer still yields one `a`. -/
def eagerDiscard (b : Multiset α) (a : α) : Multiset α :=
  b.bind fun _ => {a}

/-- One shared answer in both components. -/
def sharedPair (b : Multiset α) : Multiset (α × α) :=
  b.bind fun x => {(x, x)}

/-- Each component draws its own answer. -/
def resampledPair (b : Multiset α) : Multiset (α × α) :=
  b.bind fun x => b.bind fun y => {(x, y)}

/-- Eager, with sharing: `b` is run once, and each answer is used `n` times.
Zero uses still run `b`; each answer yields one empty use. -/
def eagerShared (n : Nat) (b : Multiset α) : Multiset (List α) :=
  b.bind fun x => {shareTuple n x}

/-- Lazy, with sharing. Zero uses never demand `b`, so there is one empty use.
One or more uses demand the cell once and share it. -/
def lazyShared (n : Nat) (b : Multiset α) : Multiset (List α) :=
  if n = 0 then {[]} else b.bind fun x => {shareTuple n x}

/-- Resampling: each of the `n` uses draws its own answer. Zero uses draw nothing. -/
def resampledUses : Nat → Multiset α → Multiset (List α)
  | 0, _ => {[]}
  | n + 1, b => b.bind fun x => (resampledUses n b).map fun xs => x :: xs

theorem resampledUses_zero (b : Multiset α) : resampledUses 0 b = {[]} :=
  rfl

theorem resampledUses_succ (n : Nat) (b : Multiset α) :
    resampledUses (n + 1) b =
      b.bind fun x => (resampledUses n b).map fun xs => x :: xs :=
  rfl

theorem eagerDiscard_eq_replicate (b : Multiset α) (a : α) :
    eagerDiscard b a = replicate b.card a := by
  refine Multiset.induction_on b ?_ ?_
  · simp [eagerDiscard]
  · intro x b ih
    calc
      eagerDiscard (x ::ₘ b) a = {a} + eagerDiscard b a := by
        simp [eagerDiscard]
      _ = {a} + replicate b.card a := by rw [ih]
      _ = replicate (b.card + 1) a := by
        rw [singleton_add, ← replicate_succ]
      _ = replicate (x ::ₘ b).card a := by simp [card_cons]

/-- Eager and lazy discarding agree over bags exactly when there is one answer. -/
theorem eagerDiscard_eq_lazyDiscard_iff (b : Multiset α) (a : α) :
    eagerDiscard b a = lazyDiscard a ↔ b.card = 1 := by
  rw [eagerDiscard_eq_replicate, lazyDiscard]
  constructor
  · intro h
    have := congrArg card h
    simpa [card_replicate, card_singleton] using this
  · intro h
    simp [h]

theorem card_sharedPair (b : Multiset α) : (sharedPair b).card = b.card := by
  simp [sharedPair, bind_singleton, card_map]

private theorem card_bind_square (b : Multiset α) :
    (b.bind fun x => b.bind fun y => ({(x, y)} : Multiset (α × α))).card =
      b.card * b.card := by
  have hinner :
      ∀ x, (b.bind fun y => ({(x, y)} : Multiset (α × α))).card = b.card := by
    intro x
    simp [bind_singleton, card_map]
  rw [card_bind]
  have hmap :
      b.map (card ∘ fun x => b.bind fun y => ({(x, y)} : Multiset (α × α))) =
        b.map fun _ => b.card := by
    refine map_congr rfl ?_
    intro x _
    exact hinner x
  rw [hmap, map_const', sum_replicate, smul_eq_mul]

theorem card_resampledPair (b : Multiset α) :
    (resampledPair b).card = b.card * b.card :=
  card_bind_square b

private theorem mul_self_eq_iff (n : Nat) : n * n = n ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    cases n with
    | zero => exact Or.inl rfl
    | succ n =>
        cases n with
        | zero => exact Or.inr rfl
        | succ n =>
            have hlt :=
              Nat.mul_lt_mul_of_pos_left
                (n := 1) (m := Nat.succ (Nat.succ n))
                (k := Nat.succ (Nat.succ n)) (by omega) (by omega)
            rw [Nat.mul_one] at hlt
            exact absurd (h ▸ hlt) (Nat.lt_irrefl _)
  · rintro (rfl | rfl) <;> simp

/-- Sharing and resampling one pair agree over bags exactly when there is at most one answer. -/
theorem sharedPair_eq_resampledPair_iff (b : Multiset α) :
    sharedPair b = resampledPair b ↔ b.card ≤ 1 := by
  constructor
  · intro h
    have hc := congrArg card h
    rw [card_sharedPair, card_resampledPair] at hc
    have hself : b.card * b.card = b.card := hc.symm
    rcases (mul_self_eq_iff b.card).mp hself with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro h
    have h01 : b.card = 0 ∨ b.card = 1 := by omega
    rcases h01 with h0 | h1
    · have hb : b = 0 := card_eq_zero.mp h0
      subst hb
      simp [sharedPair, resampledPair]
    · obtain ⟨a, rfl⟩ := card_eq_one.mp h1
      simp [sharedPair, resampledPair]

theorem card_resampledUses (n : Nat) (b : Multiset α) :
    (resampledUses n b).card = b.card ^ n := by
  induction n with
  | zero => simp [resampledUses_zero]
  | succ n ih =>
      rw [resampledUses_succ, card_bind]
      have hmap :
          ∀ x, ((resampledUses n b).map fun xs => x :: xs).card =
            (resampledUses n b).card := by
        intro x
        simp [card_map]
      have hconst :
          b.map (card ∘ fun x => (resampledUses n b).map fun xs => x :: xs) =
            b.map fun _ => (resampledUses n b).card := by
        refine map_congr rfl ?_
        intro x _
        exact hmap x
      rw [hconst, map_const', sum_replicate, smul_eq_mul, ih, Nat.mul_comm, ← Nat.pow_succ]

theorem card_lazyShared (n : Nat) (b : Multiset α) :
    (lazyShared n b).card = if n = 0 then 1 else b.card := by
  by_cases hn : n = 0
  · simp [lazyShared, hn]
  · simp [lazyShared, hn, bind_singleton, card_map]

private theorem pow_ne_self {c n : Nat} (hc : 2 ≤ c) (hn : 2 ≤ n) : c ^ n ≠ c := by
  have hsq : c ^ 2 ≤ c ^ n := Nat.pow_le_pow_right (by omega : 0 < c) hn
  have hlt : c < c ^ 2 := by
    rw [Nat.pow_two]
    have hm : c * 1 < c * c :=
      Nat.mul_lt_mul_of_pos_left (by omega : 1 < c) (by omega : 0 < c)
    simpa using hm
  exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hsq)).symm

/-- Eager sharing and lazy sharing agree exactly when the binding is used at least once,
or the bound computation has one answer. -/
theorem eagerShared_eq_lazyShared_iff (n : Nat) (b : Multiset α) :
    eagerShared n b = lazyShared n b ↔ 1 ≤ n ∨ b.card = 1 := by
  by_cases hn : n = 0
  · subst hn
    have hL : lazyShared 0 b = {([] : List α)} := by simp [lazyShared]
    have hE : eagerShared 0 b = replicate b.card ([] : List α) := by
      simp only [eagerShared, shareTuple, bind_singleton]
      have hfun : (List.replicate (0 : Nat) : α → List α) = fun _ => [] := by
        funext _
        exact List.replicate_zero
      rw [hfun]
      exact map_const' _ _
    rw [hL, hE]
    constructor
    · intro h
      have hc := congrArg card h
      have hcard : b.card = 1 := by
        rw [card_replicate, card_singleton] at hc
        exact hc
      exact Or.inr hcard
    · intro h
      rcases h with h | h
      · omega
      · simp [h]
  · have hsame : lazyShared n b = eagerShared n b := by
      simp [lazyShared, eagerShared, hn]
    rw [hsame]
    constructor
    · intro _
      exact Or.inl (Nat.one_le_iff_ne_zero.mpr hn)
    · intro _
      rfl

private theorem lazyShared_eq_resampled_of_card_le_one (n : Nat) (b : Multiset α)
    (h : b.card ≤ 1) : lazyShared n b = resampledUses n b := by
  have h01 : b.card = 0 ∨ b.card = 1 := by omega
  rcases h01 with h0 | h1
  · have hb : b = 0 := card_eq_zero.mp h0
    subst hb
    induction n with
    | zero => simp [lazyShared, resampledUses_zero]
    | succ n _ih =>
        simp [lazyShared, resampledUses_succ]
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h1
    induction n with
    | zero => simp [lazyShared, resampledUses_zero]
    | succ n ih =>
        rw [resampledUses_succ, singleton_bind, ← ih]
        by_cases hn : n = 0
        · subst hn
          simp [lazyShared, shareTuple, map_singleton]
        · simp [lazyShared, hn, shareTuple, map_singleton, List.replicate_succ]

/-- Sharing and resampling `n` uses agree exactly when there is at most one use,
or the bound computation has at most one answer. -/
theorem lazyShared_eq_resampledUses_iff (n : Nat) (b : Multiset α) :
    lazyShared n b = resampledUses n b ↔ n ≤ 1 ∨ b.card ≤ 1 := by
  constructor
  · intro h
    by_contra hbad
    have hn : 2 ≤ n := by omega
    have hb : 2 ≤ b.card := by omega
    have hn0 : n ≠ 0 := by omega
    have hc := congrArg card h
    rw [card_lazyShared, card_resampledUses, if_neg hn0] at hc
    exact absurd hc.symm (pow_ne_self hb hn)
  · intro h
    rcases h with hn | hc
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl
      · simp [lazyShared, resampledUses_zero]
      · rw [resampledUses_succ, resampledUses_zero]
        simp [lazyShared, shareTuple, map_singleton, bind_singleton,
          List.replicate_succ, List.replicate_zero]
    · exact lazyShared_eq_resampled_of_card_le_one n b hc

/-- The three readings of `n` uses agree together exactly on the discarding line and the
copying line. -/
theorem strategies_agree_iff (n : Nat) (b : Multiset α) :
    eagerShared n b = lazyShared n b ∧ lazyShared n b = resampledUses n b ↔
      (1 ≤ n ∨ b.card = 1) ∧ (n ≤ 1 ∨ b.card ≤ 1) :=
  and_congr (eagerShared_eq_lazyShared_iff n b) (lazyShared_eq_resampledUses_iff n b)

end Bags

/-! ## Sets -/

section Sets

variable {α : Type} [DecidableEq α]

open Finset

/-- Eager discarding over a set of answers. -/
def eagerDiscardSet (b : Finset α) (a : α) : Finset α :=
  b.biUnion fun _ => {a}

/-- Lazy discarding over a set of answers. -/
def lazyDiscardSet (a : α) : Finset α :=
  {a}

/-- One shared answer in both components, as a set. -/
def sharedPairSet (b : Finset α) : Finset (α × α) :=
  b.image fun x => (x, x)

/-- Each component draws its own answer, as a set. -/
def resampledPairSet (b : Finset α) : Finset (α × α) :=
  b.biUnion fun x => b.image fun y => (x, y)

/-- Eager and with sharing, over a set. Zero uses still run `b`. -/
def eagerSharedSet (n : Nat) (b : Finset α) : Finset (List α) :=
  b.image (shareTuple n)

/-- Lazy and with sharing, over a set. Zero uses do not run `b`. -/
def lazySharedSet (n : Nat) (b : Finset α) : Finset (List α) :=
  if n = 0 then {[]} else b.image (shareTuple n)

/-- Resampling over a set. -/
def resampledUsesSet : Nat → Finset α → Finset (List α)
  | 0, _ => {[]}
  | n + 1, b => b.biUnion fun x => (resampledUsesSet n b).image fun xs => x :: xs

theorem resampledUsesSet_zero (b : Finset α) : resampledUsesSet 0 b = {[]} :=
  rfl

theorem resampledUsesSet_succ (n : Nat) (b : Finset α) :
    resampledUsesSet (n + 1) b =
      b.biUnion fun x => (resampledUsesSet n b).image fun xs => x :: xs :=
  rfl

private theorem exists_mem_ne {b : Finset α} (h : 2 ≤ b.card) :
    ∃ x y, x ∈ b ∧ y ∈ b ∧ x ≠ y := by
  have hb : b.Nonempty := card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hb
  have hpos : 0 < (b.erase x).card := by
    rw [card_erase_of_mem hx]
    omega
  obtain ⟨y, hy⟩ := card_pos.mp hpos
  exact ⟨x, y, hx, mem_of_mem_erase hy, (ne_of_mem_erase hy).symm⟩

/-- Eager and lazy discarding agree over sets exactly when there is at least one answer. -/
theorem eagerDiscardSet_eq_lazyDiscardSet_iff (b : Finset α) (a : α) :
    eagerDiscardSet b a = lazyDiscardSet a ↔ b.Nonempty := by
  constructor
  · intro h
    by_contra hempty
    have hb : b = ∅ := not_nonempty_iff_eq_empty.mp hempty
    subst hb
    simp [eagerDiscardSet, lazyDiscardSet] at h
  · intro h
    ext x
    simp only [eagerDiscardSet, lazyDiscardSet, mem_biUnion, mem_singleton]
    constructor
    · rintro ⟨_, _, rfl⟩
      rfl
    · intro hx
      obtain ⟨y, hy⟩ := h
      exact ⟨y, hy, hx⟩

/-- Sharing and resampling one pair agree over sets exactly when there is at most one answer. -/
theorem sharedPairSet_eq_resampledPairSet_iff (b : Finset α) :
    sharedPairSet b = resampledPairSet b ↔ b.card ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_mem_ne (by omega : 2 ≤ b.card)
    have hin : (x, y) ∈ resampledPairSet b := by
      refine mem_biUnion.mpr ⟨x, hx, ?_⟩
      exact mem_image.mpr ⟨y, hy, rfl⟩
    have hout : (x, y) ∉ sharedPairSet b := by
      intro hmem
      obtain ⟨z, _, heq⟩ := mem_image.mp hmem
      exact hxy ((congrArg Prod.fst heq).symm.trans (congrArg Prod.snd heq))
    rw [← h] at hin
    exact hout hin
  · intro h
    have h01 : b.card = 0 ∨ b.card = 1 := by omega
    rcases h01 with h0 | h1
    · have hb : b = ∅ := card_eq_zero.mp h0
      subst hb
      simp [sharedPairSet, resampledPairSet]
    · obtain ⟨x, rfl⟩ := card_eq_one.mp h1
      simp [sharedPairSet, resampledPairSet, image_singleton, singleton_biUnion]

private theorem mem_resampledUsesSet (n : Nat) (b : Finset α) (xs : List α) :
    xs ∈ resampledUsesSet n b ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ b := by
  induction n generalizing xs with
  | zero =>
      simp only [resampledUsesSet_zero, mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl
        exact ⟨rfl, fun _ hx => by cases hx⟩
      · rintro ⟨rfl, _⟩
        rfl
  | succ n ih =>
      simp only [resampledUsesSet_succ, mem_biUnion, mem_image]
      constructor
      · rintro ⟨x, hx, ys, hys, rfl⟩
        rw [ih] at hys
        rcases hys with ⟨hlen, hall⟩
        refine ⟨by simp [hlen], ?_⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hx
        · exact hall z hz
      · rintro ⟨hlen, hall⟩
        cases xs with
        | nil => simp at hlen
        | cons x ys =>
            refine ⟨x, hall x (by simp), ys, ?_, rfl⟩
            rw [ih]
            refine ⟨?_, ?_⟩
            · simp [List.length_cons] at hlen
              omega
            · intro z hz
              exact hall z (List.mem_cons_of_mem x hz)

/-- Eager sharing and lazy sharing agree over sets exactly when the binding is used at least
once, or the bound set has at least one answer. -/
theorem eagerSharedSet_eq_lazySharedSet_iff (n : Nat) (b : Finset α) :
    eagerSharedSet n b = lazySharedSet n b ↔ 1 ≤ n ∨ b.Nonempty := by
  by_cases hn : n = 0
  · subst hn
    change b.image (shareTuple 0) = ({[]} : Finset (List α)) ↔ 1 ≤ 0 ∨ b.Nonempty
    constructor
    · intro h
      right
      by_contra hempty
      have hb : b = ∅ := not_nonempty_iff_eq_empty.mp hempty
      subst hb
      simp [image_empty] at h
    · intro h
      rcases h with h | h
      · omega
      · ext xs
        simp only [mem_image, mem_singleton, shareTuple]
        constructor
        · rintro ⟨_, _, rfl⟩
          rfl
        · intro hxs
          obtain ⟨y, hy⟩ := h
          subst hxs
          exact ⟨y, hy, rfl⟩
  · rw [eagerSharedSet, lazySharedSet, if_neg hn]
    constructor
    · intro _
      exact Or.inl (Nat.one_le_iff_ne_zero.mpr hn)
    · intro _
      trivial

private theorem lazySharedSet_eq_resampled_of_card_le_one (n : Nat) (b : Finset α)
    (h : b.card ≤ 1) : lazySharedSet n b = resampledUsesSet n b := by
  have h01 : b.card = 0 ∨ b.card = 1 := by omega
  rcases h01 with h0 | h1
  · have hb : b = ∅ := card_eq_zero.mp h0
    subst hb
    cases n with
    | zero => simp [lazySharedSet, resampledUsesSet_zero]
    | succ n =>
        simp [lazySharedSet, resampledUsesSet_succ]
  · obtain ⟨a, rfl⟩ := card_eq_one.mp h1
    induction n with
    | zero => simp [lazySharedSet, resampledUsesSet_zero]
    | succ n ih =>
        by_cases hn : n = 0
        · subst hn
          simp [lazySharedSet, resampledUsesSet_succ, resampledUsesSet_zero, shareTuple,
            singleton_biUnion, image_singleton]
        · rw [resampledUsesSet_succ, ← ih]
          simp [lazySharedSet, hn, singleton_biUnion, image_singleton, shareTuple,
            List.replicate_succ]

private theorem lazySharedSet_ne_resampled_of_branching (n : Nat) (b : Finset α)
    (hn : 2 ≤ n) (hb : 2 ≤ b.card) :
    lazySharedSet n b ≠ resampledUsesSet n b := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_mem_ne hb
  obtain ⟨k, rfl⟩ := show ∃ k, n = k + 2 from ⟨n - 2, by omega⟩
  let xs : List α := x :: List.replicate (k + 1) y
  have hmem : xs ∈ resampledUsesSet (k + 2) b := by
    rw [mem_resampledUsesSet]
    refine ⟨?_, ?_⟩
    · simp [xs, List.length_replicate]
    · intro z hz
      simp only [xs, List.mem_cons, List.mem_replicate] at hz
      rcases hz with rfl | ⟨_, rfl⟩
      · exact hx
      · exact hy
  have hnot : xs ∉ lazySharedSet (k + 2) b := by
    rw [lazySharedSet, if_neg (by omega : k + 2 ≠ 0)]
    intro hxs
    obtain ⟨z, _, heq⟩ := mem_image.mp hxs
    have hrep : shareTuple (k + 2) z = z :: z :: List.replicate k z := by
      simp [shareTuple, List.replicate_succ]
    have hxs' : xs = x :: y :: List.replicate k y := by
      simp [xs, List.replicate_succ]
    rw [hrep, hxs'] at heq
    injection heq with hzx hrest
    injection hrest with hzy _
    exact hxy (hzx.symm.trans hzy)
  intro h
  rw [← h] at hmem
  exact hnot hmem

/-- Sharing and resampling `n` uses agree over sets exactly when there is at most one use,
or the bound set has at most one answer. -/
theorem lazySharedSet_eq_resampledUsesSet_iff (n : Nat) (b : Finset α) :
    lazySharedSet n b = resampledUsesSet n b ↔ n ≤ 1 ∨ b.card ≤ 1 := by
  constructor
  · intro h
    by_contra hbad
    exact lazySharedSet_ne_resampled_of_branching n b (by omega) (by omega) h
  · intro h
    rcases h with hn | hc
    · have h01 : n = 0 ∨ n = 1 := by omega
      rcases h01 with rfl | rfl
      · simp [lazySharedSet, resampledUsesSet_zero]
      · simp only [lazySharedSet, resampledUsesSet_succ, resampledUsesSet_zero,
          biUnion_singleton, image_singleton]
        rw [show shareTuple 1 = fun a => [a] from funext fun _ => rfl]
        rfl
    · exact lazySharedSet_eq_resampled_of_card_le_one n b hc

/-- The three readings of `n` uses agree over sets on the set-shaped discarding and copying lines:
at least one use or a nonempty set, and at most one use or a set of at most one answer. -/
theorem strategies_agree_set_iff (n : Nat) (b : Finset α) :
    eagerSharedSet n b = lazySharedSet n b ∧
        lazySharedSet n b = resampledUsesSet n b ↔
      (1 ≤ n ∨ b.Nonempty) ∧ (n ≤ 1 ∨ b.card ≤ 1) :=
  and_congr (eagerSharedSet_eq_lazySharedSet_iff n b)
    (lazySharedSet_eq_resampledUsesSet_iff n b)

end Sets

/-! ## Supports of bags -/

section Supports

variable {α : Type} [DecidableEq α]

open Multiset

private theorem sharedPair_toFinset (b : Multiset α) :
    (sharedPair b).toFinset = b.toFinset.image fun x => (x, x) := by
  rw [sharedPair, Finset.bind_toFinset]
  simp [toFinset_singleton, Finset.biUnion_singleton]

private theorem resampledPair_toFinset (b : Multiset α) :
    (resampledPair b).toFinset =
      b.toFinset.biUnion fun x => b.toFinset.image fun y => (x, y) := by
  rw [resampledPair, Finset.bind_toFinset]
  refine Finset.biUnion_congr rfl ?_
  intro x _
  rw [Finset.bind_toFinset]
  simp [toFinset_singleton, Finset.biUnion_singleton]

/-- Eager and lazy discarding agree on the support exactly when there is at least one answer. -/
theorem discard_support_iff (b : Multiset α) (a : α) :
    (eagerDiscard b a).toFinset = (lazyDiscard a).toFinset ↔ b ≠ 0 := by
  rw [eagerDiscard_eq_replicate, lazyDiscard, toFinset_singleton]
  constructor
  · intro h hb
    rw [card_eq_zero.mpr hb, replicate_zero, toFinset_zero] at h
    exact Finset.singleton_ne_empty a h.symm
  · intro hb
    have hne : b.card ≠ 0 := fun h0 => hb (card_eq_zero.mp h0)
    rw [toFinset_replicate]
    split_ifs with h0
    · exact absurd h0 hne
    · rfl

/-- Sharing and resampling agree on the support exactly when the support has at most one element.
Two copies of one answer have a one-element support, so they agree here and not as bags. -/
theorem copy_support_iff (b : Multiset α) :
    (sharedPair b).toFinset = (resampledPair b).toFinset ↔ b.toFinset.card ≤ 1 := by
  rw [sharedPair_toFinset, resampledPair_toFinset]
  exact sharedPairSet_eq_resampledPairSet_iff b.toFinset

theorem eagerShared_toFinset (n : Nat) (b : Multiset α) :
    (eagerShared n b).toFinset = eagerSharedSet n b.toFinset := by
  simp only [eagerShared, bind_singleton, toFinset_map, eagerSharedSet]

theorem lazyShared_toFinset (n : Nat) (b : Multiset α) :
    (lazyShared n b).toFinset = lazySharedSet n b.toFinset := by
  by_cases hn : n = 0
  · simp [lazyShared, lazySharedSet, hn]
  · simp only [lazyShared, lazySharedSet, if_neg hn, bind_singleton, toFinset_map]

theorem resampledUses_toFinset (n : Nat) (b : Multiset α) :
    (resampledUses n b).toFinset = resampledUsesSet n b.toFinset := by
  induction n with
  | zero => simp [resampledUses_zero, resampledUsesSet_zero]
  | succ n ih =>
      rw [resampledUses_succ, resampledUsesSet_succ, Finset.bind_toFinset]
      refine Finset.biUnion_congr rfl ?_
      intro x _
      rw [toFinset_map, ih]

/-- Eager and lazy sharing of `n` uses agree on the support exactly when the binding is used at
least once, or there is at least one answer. -/
theorem eagerShared_lazyShared_support_iff (n : Nat) (b : Multiset α) :
    (eagerShared n b).toFinset = (lazyShared n b).toFinset ↔ 1 ≤ n ∨ b ≠ 0 := by
  rw [eagerShared_toFinset, lazyShared_toFinset, eagerSharedSet_eq_lazySharedSet_iff,
    toFinset_nonempty]

/-- Sharing and resampling `n` uses agree on the support exactly when there is at most one use, or
the support has at most one element. -/
theorem lazyShared_resampledUses_support_iff (n : Nat) (b : Multiset α) :
    (lazyShared n b).toFinset = (resampledUses n b).toFinset ↔ n ≤ 1 ∨ b.toFinset.card ≤ 1 := by
  rw [lazyShared_toFinset, resampledUses_toFinset]
  exact lazySharedSet_eq_resampledUsesSet_iff n b.toFinset

/-- The three readings of `n` uses agree on the support exactly on the set-shaped lines: at least
one use or at least one answer, and at most one use or a support of at most one element. -/
theorem strategies_agree_support_iff (n : Nat) (b : Multiset α) :
    (eagerShared n b).toFinset = (lazyShared n b).toFinset ∧
        (lazyShared n b).toFinset = (resampledUses n b).toFinset ↔
      (1 ≤ n ∨ b ≠ 0) ∧ (n ≤ 1 ∨ b.toFinset.card ≤ 1) :=
  and_congr (eagerShared_lazyShared_support_iff n b) (lazyShared_resampledUses_support_iff n b)

end Supports

/-! ## Controls -/

/-- The probe with two answers. -/
inductive Coin where
  | heads
  | tails
deriving DecidableEq, Repr

open Multiset

def coinBag : Multiset Coin :=
  Coin.heads ::ₘ Coin.tails ::ₘ 0

private theorem coinBag_card : coinBag.card = 2 := by
  simp only [coinBag, card_cons, card_zero, Nat.zero_add]

/-- `coin` over bags: eager discarding returns two copies, lazy discarding one. -/
theorem coin_discard_bags :
    (eagerDiscard coinBag Coin.heads).card = 2 ∧
      (lazyDiscard Coin.heads).card = 1 ∧
        eagerDiscard coinBag Coin.heads ≠ lazyDiscard Coin.heads := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eagerDiscard_eq_replicate, coinBag_card, card_replicate]
  · simp [lazyDiscard]
  · intro h
    have := congrArg card h
    rw [eagerDiscard_eq_replicate, coinBag_card, card_replicate, lazyDiscard,
      card_singleton] at this
    omega

/-- `coin` over supports: both discardings are the singleton `{heads}`. -/
theorem coin_discard_sets :
    (eagerDiscard coinBag Coin.heads).toFinset = ({Coin.heads} : Finset Coin) ∧
      (lazyDiscard Coin.heads).toFinset = ({Coin.heads} : Finset Coin) := by
  refine ⟨?_, ?_⟩
  · rw [eagerDiscard_eq_replicate, coinBag_card, toFinset_replicate]
    simp
  · simp [lazyDiscard]

/-- `coin` over bags: sharing returns two pairs, resampling four. -/
theorem coin_copy_bags :
    (sharedPair coinBag).card = 2 ∧
      (resampledPair coinBag).card = 4 ∧
        sharedPair coinBag ≠ resampledPair coinBag := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_sharedPair, coinBag_card]
  · rw [card_resampledPair, coinBag_card]
  · intro h
    have := congrArg card h
    rw [card_sharedPair, card_resampledPair, coinBag_card] at this
    omega

private theorem coinBag_nodup : coinBag.Nodup := by
  decide

private theorem heads_mem_coin : Coin.heads ∈ coinBag := by
  simp [coinBag]

private theorem tails_mem_coin : Coin.tails ∈ coinBag := by
  simp [coinBag]

private theorem mem_resampledPair {x y : Coin} (hx : x ∈ coinBag) (hy : y ∈ coinBag) :
    (x, y) ∈ resampledPair coinBag := by
  refine mem_bind.mpr ⟨x, hx, ?_⟩
  refine mem_bind.mpr ⟨y, hy, ?_⟩
  simp

/-- `coin` over supports: two shared pairs, four resampled pairs. -/
theorem coin_copy_sets :
    (sharedPair coinBag).toFinset.card = 2 ∧ (resampledPair coinBag).toFinset.card = 4 := by
  refine ⟨?_, ?_⟩
  · have hnodup : (sharedPair coinBag).Nodup := by
      have hmap : sharedPair coinBag = coinBag.map fun x => (x, x) := by
        simp [sharedPair, bind_singleton]
      rw [hmap]
      exact Nodup.map (fun _ _ h => congrArg Prod.fst h) coinBag_nodup
    rw [toFinset_card_of_nodup hnodup, card_sharedPair, coinBag_card]
  · let pairs : Finset (Coin × Coin) :=
      insert (Coin.heads, Coin.heads)
        (insert (Coin.heads, Coin.tails)
          (insert (Coin.tails, Coin.heads) {(Coin.tails, Coin.tails)}))
    have hpairs : pairs.card = 4 := by
      rw [Finset.card_insert_of_notMem (by decide)]
      rw [Finset.card_insert_of_notMem (by decide)]
      rw [Finset.card_insert_of_notMem (by decide)]
      rw [Finset.card_singleton]
    have hsub : pairs ⊆ (resampledPair coinBag).toFinset := by
      intro p hp
      simp [pairs, Finset.mem_insert] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_toFinset.mpr (mem_resampledPair heads_mem_coin heads_mem_coin)
      · exact mem_toFinset.mpr (mem_resampledPair heads_mem_coin tails_mem_coin)
      · exact mem_toFinset.mpr (mem_resampledPair tails_mem_coin heads_mem_coin)
      · exact mem_toFinset.mpr (mem_resampledPair tails_mem_coin tails_mem_coin)
    have hge : 4 ≤ (resampledPair coinBag).toFinset.card := by
      simpa [hpairs] using Finset.card_le_card hsub
    have hle : (resampledPair coinBag).toFinset.card ≤ 4 := by
      have hcard : (resampledPair coinBag).card = 4 := by
        rw [card_resampledPair, coinBag_card]
      simpa [hcard] using toFinset_card_le (resampledPair coinBag)
    exact Nat.le_antisymm hle hge

/-- No answer: eager discarding returns nothing, lazy discarding returns one `a`. -/
theorem empty_discard {α : Type} (a : α) :
    eagerDiscard (0 : Multiset α) a = 0 ∧ lazyDiscard a = {a} := by
  simp [eagerDiscard, lazyDiscard]

/-- Two copies of one answer. The bags disagree (two pairs against four) and the supports
agree: both are the singleton pair. -/
theorem twoEqualAnswers_bagsDiffer_setsAgree {α : Type} [DecidableEq α] (a : α) :
    (sharedPair (replicate 2 a)).card = 2 ∧
      (resampledPair (replicate 2 a)).card = 4 ∧
        sharedPair (replicate 2 a) ≠ resampledPair (replicate 2 a) ∧
          (sharedPair (replicate 2 a)).toFinset = ({(a, a)} : Finset (α × α)) ∧
            (resampledPair (replicate 2 a)).toFinset = ({(a, a)} : Finset (α × α)) := by
  have hc : (replicate 2 a).card = 2 := by simp
  have hs : sharedPair (replicate 2 a) = replicate 2 (a, a) := by
    simp [sharedPair, bind_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [card_sharedPair, hc]
  · rw [card_resampledPair, hc]
  · intro h
    have := congrArg card h
    rw [card_sharedPair, card_resampledPair, hc] at this
    omega
  · rw [hs, toFinset_replicate]
    simp
  · have hsup : (replicate 2 a).toFinset.card ≤ 1 := by
      rw [toFinset_replicate]
      simp
    have heq := (copy_support_iff (replicate 2 a)).mpr hsup
    rw [← heq, hs, toFinset_replicate]
    simp

private theorem coinBag_toFinset_card : coinBag.toFinset.card = 2 := by
  rw [toFinset_card_of_nodup coinBag_nodup, coinBag_card]

/-- `coin` bound and used zero times: eager sharing returns two empty uses and lazy sharing one, and
both supports are the one empty use. Used twice, sharing and resampling disagree on the support
too. -/
theorem coin_uses :
    eagerShared 0 coinBag ≠ lazyShared 0 coinBag ∧
      (eagerShared 0 coinBag).toFinset = (lazyShared 0 coinBag).toFinset ∧
        (lazyShared 2 coinBag).toFinset ≠ (resampledUses 2 coinBag).toFinset := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ne, eagerShared_eq_lazyShared_iff, coinBag_card]
    omega
  · exact (eagerShared_lazyShared_support_iff 0 coinBag).mpr (Or.inr (by simp [coinBag]))
  · rw [Ne, lazyShared_resampledUses_support_iff, coinBag_toFinset_card]
    omega

/-- No answer, bound and used zero times: eager sharing returns nothing and lazy sharing one empty
use, so the supports disagree too. -/
theorem empty_uses {α : Type} [DecidableEq α] :
    (eagerShared 0 (0 : Multiset α)).toFinset ≠ (lazyShared 0 (0 : Multiset α)).toFinset := by
  rw [Ne, eagerShared_lazyShared_support_iff]
  simp

/-- Two copies of one answer, used twice: sharing and resampling differ as bags and agree on the
support. -/
theorem twoEqualAnswers_uses {α : Type} [DecidableEq α] (a : α) :
    lazyShared 2 (replicate 2 a) ≠ resampledUses 2 (replicate 2 a) ∧
      (lazyShared 2 (replicate 2 a)).toFinset = (resampledUses 2 (replicate 2 a)).toFinset := by
  refine ⟨?_, ?_⟩
  · rw [Ne, lazyShared_eq_resampledUses_iff]
    simp
  · exact (lazyShared_resampledUses_support_iff 2 _).mpr (Or.inr (by simp))

/-- Weakening "exactly one answer" to "at least one answer" does not make eager and lazy
discarding agree over bags. `coinBag` has two answers. -/
theorem discard_atLeastOne_fails_on_coin :
    ¬ ∀ b : Multiset Coin, ∀ a : Coin,
        1 ≤ b.card → eagerDiscard b a = lazyDiscard a := by
  intro h
  have hcard : 1 ≤ coinBag.card := by simp [coinBag_card]
  exact coin_discard_bags.2.2 (h coinBag Coin.heads hcard)

end Mettapedia.GSLT.Dynamics.DemandAgreement

#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.eagerDiscard_eq_lazyDiscard_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.discard_support_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.eagerDiscardSet_eq_lazyDiscardSet_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.sharedPair_eq_resampledPair_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.copy_support_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.sharedPairSet_eq_resampledPairSet_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.strategies_agree_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.strategies_agree_set_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.strategies_agree_support_iff
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.coin_uses
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.discard_atLeastOne_fails_on_coin
#print axioms Mettapedia.GSLT.Dynamics.DemandAgreement.twoEqualAnswers_bagsDiffer_setsAgree
