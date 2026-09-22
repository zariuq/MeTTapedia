/-
# Routing a metavariable to all of its occurrences

The MeTTa census says the structural obstructions are absent from that
presentation: no term-level binder, no pattern binder, no variadic position. It
also says what is left, which is the whole of the remaining work — **metavariable
routing.** A rule's left side matches and binds a metavariable; the right side
uses it, possibly many times, in arbitrary positions. The compiled rule has to
deliver the matched name to every one of those positions.

A single occurrence is `assemble`: the name arrives, a one-hole context places
it, and the result is emitted. Several occurrences need duplication, and that is
what this file adds.

A `Placement` is the shape of a metavariable's occurrences in a right-hand side:
a binary tree whose leaves are one-hole contexts — one per occurrence — and whose
internal nodes are the points where the name has to be duplicated. `build`
compiles one, and `build_reaches` proves the compiled soup delivers the matched
value to every occurrence and assembles the result:

```
    build s p inName outName path ‖ mm inName v   ⟶*   mm outName (p.fill v)
```

That is the preservation statement for a metavariable, general in the number of
occurrences and in where they sit.

## The cost

`atomCount_build` is again an equality: `cost`, computed from the placement
alone. And `cost_eq_occurrences` turns it into the law:

```
    cost p + 2 = leafWeight p + 3 * occurrences p
```

**Three atoms per occurrence**, plus the arity sum of the contexts that place
them. A duplication node costs two — one `dd` to split the name and one
constructor to rejoin the results — and a binary tree with `n` leaves has `n-1`
of them, which is where the `3` comes from. So routing is linear in the number
of occurrences, with an exact constant rather than a bound.

## What is and is not proved

`build_reaches` exhibits the intended trace, `atomCount_build` gives the exact
cost, and `build_linear` rules out the unintended traces: no name in a compiled
soup has two possible partners. So `build` carries the same three guarantees
`assemble` does, and `build_verified` states them together.

Linearity is what the offset indexing is for. `assemble` earns it from a single
arithmetic counter; `build` branches, so each duplication node reserves four
slots for its own wiring and hands its two sides **disjoint ranges**. The range
bookkeeping is `slotsUsed`, and `build_listening_structure` carries the
two-sided bound that makes the branches provably disjoint.

Still open, and not affected by this file: that a `Placement` is extracted from
a real `Pattern`. `build` compiles any placement; the function taking a
metavariable and a right-hand side to its placement is not written, so the
preservation result applies to placements rather than yet to MeTTa rules as
authored.

-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.CollapsedConstructor

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Placements -/

/-- The shape of one metavariable's occurrences in a right-hand side: each leaf
is an occurrence together with the one-hole context that places it, and each
internal node is a point where the matched name must be duplicated. -/
inductive Placement where
  | single : NameContext → Placement
  | splitPar : Placement → Placement → Placement
  | splitMsg : Placement → Placement → Placement

namespace Placement

/-- The right-hand side a placement denotes, with the matched value in every
occurrence. -/
def fill : Placement → Comb → Comb
  | single ctx, v => ctx.fill v
  | splitPar p q, v => par (p.fill v) (q.fill v)
  | splitMsg p q, v => mm (p.fill v) (q.fill v)

/-- How many occurrences the metavariable has. -/
def occurrences : Placement → ℕ
  | single _ => 1
  | splitPar p q => p.occurrences + q.occurrences
  | splitMsg p q => p.occurrences + q.occurrences

/-- The arity sum of the contexts that place the occurrences. -/
def leafWeight : Placement → ℕ
  | single ctx => ctx.weight
  | splitPar p q => p.leafWeight + q.leafWeight
  | splitMsg p q => p.leafWeight + q.leafWeight

/-- How many slots a compiled placement reserves.  A duplication node takes four
— two to split the name, two to collect the results — and hands disjoint ranges
to its two sides. -/
def slotsUsed : Placement → ℕ
  | single ctx => ctx.slotsUsed
  | splitPar p q => p.slotsUsed + q.slotsUsed + 4
  | splitMsg p q => p.slotsUsed + q.slotsUsed + 4

/-- What compiling a placement costs. -/
def cost : Placement → ℕ
  | single ctx => ctx.weight + 1
  | splitPar p q => p.cost + q.cost + 2
  | splitMsg p q => p.cost + q.cost + 2

/-- **Routing is three atoms per occurrence.**  A duplication node costs two —
one `dd` to split the name, one constructor to rejoin the results — and a binary
tree with `n` leaves has `n-1` of them, so the per-occurrence constant is three
on top of the placing contexts' own weight. -/
theorem cost_eq_occurrences :
    ∀ p : Placement, p.cost + 2 = p.leafWeight + 3 * p.occurrences
  | single ctx => by simp [cost, leafWeight, occurrences]
  | splitPar p q | splitMsg p q => by
      have ihp := cost_eq_occurrences p
      have ihq := cost_eq_occurrences q
      simp only [cost, leafWeight, occurrences]
      omega

/-- Every occurrence costs at least one atom, so the compiled soup is never
smaller than the number of places it has to reach. -/
theorem occurrences_le_cost (p : Placement) : p.occurrences ≤ p.cost := by
  have law := cost_eq_occurrences p
  omega

end Placement

/-! ## The compiler -/

/-- **Compile a placement.**  A leaf is an `assemble` chain; a duplication node
splits the arriving name with `dd`, compiles both sides in disjoint slot ranges,
and rejoins their results with a constructor. -/
def build (s : Comb) : Placement → Comb → Comb → ℕ → Comb
  | .single ctx, inName, outName, offset => assemble s ctx inName outName offset
  | .splitPar p q, inName, outName, offset =>
      par (dd inName (slot s offset) (slot s (offset + 1)))
        (par (build s p (slot s offset) (slot s (offset + 2)) (offset + 4))
          (par (build s q (slot s (offset + 1)) (slot s (offset + 3))
                (offset + 4 + p.slotsUsed))
            (consPar (slot s (offset + 2)) (slot s (offset + 3)) outName)))
  | .splitMsg p q, inName, outName, offset =>
      par (dd inName (slot s offset) (slot s (offset + 1)))
        (par (build s p (slot s offset) (slot s (offset + 2)) (offset + 4))
          (par (build s q (slot s (offset + 1)) (slot s (offset + 3))
                (offset + 4 + p.slotsUsed))
            (consMsg (slot s (offset + 2)) (slot s (offset + 3)) outName)))

/-- **One duplication node.**  The arriving name is split, both sides are
compiled, and their results are rejoined.  Both split cases are this lemma, so
the soup rearrangements are done once. -/
theorem split_reaches {sub₁ sub₂ inName v m₁ m₂ o₁ o₂ r₁ r₂ atom result : Comb}
    (ih₁ : ReachesFull (par sub₁ (mm m₁ v)) (mm o₁ r₁))
    (ih₂ : ReachesFull (par sub₂ (mm m₂ v)) (mm o₂ r₂))
    (fire : ReachesFull (par atom (par (mm o₁ r₁) (mm o₂ r₂))) result) :
    ReachesFull (par (par (dd inName m₁ m₂) (par sub₁ (par sub₂ atom)))
      (mm inName v)) result := by
  -- bring the arriving message beside the duplicator
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par (dd inName m₁ m₂) (par sub₁ (par sub₂ atom)))
          (mm inName v))
        = components (par (par (dd inName m₁ m₂) (mm inName v))
          (par sub₁ (par sub₂ atom)))
      from by simp only [components]; ac_rfl))) ?_
  -- split the name
  refine ReachesFull.trans (ReachesFull.ofReaches (Reaches.parLeft _
    (Reaches.single (StepMinus.duplicate m₁ m₂ v (Cong.refl inName))))) ?_
  -- run the first side
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par (mm m₁ v) (mm m₂ v)) (par sub₁ (par sub₂ atom)))
        = components (par (par sub₁ (mm m₁ v)) (par (mm m₂ v) (par sub₂ atom)))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih₁) ?_
  -- run the second side
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm o₁ r₁) (par (mm m₂ v) (par sub₂ atom)))
        = components (par (par sub₂ (mm m₂ v)) (par (mm o₁ r₁) atom))
      from by simp only [components]; ac_rfl))) ?_
  refine ReachesFull.trans (ReachesFull.parLeft _ ih₂) ?_
  -- rejoin
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (mm o₂ r₂) (par (mm o₁ r₁) atom))
        = components (par atom (par (mm o₁ r₁) (mm o₂ r₂)))
      from by simp only [components]; ac_rfl))) ?_
  exact fire

/-- **The compiled rule delivers the matched value to every occurrence.**  This
is the preservation statement for one metavariable, general in the number of
occurrences and in where they sit. -/
theorem build_reaches (s : Comb) : ∀ (p : Placement) (inName outName : Comb)
    (offset : ℕ) (v : Comb),
    ReachesFull (par (build s p inName outName offset) (mm inName v))
      (mm outName (p.fill v))
  | .single ctx, inName, outName, offset, v =>
      assemble_reaches s ctx inName outName offset v
  | .splitPar p q, _inName, outName, offset, v =>
      split_reaches
        (build_reaches s p (slot s offset) (slot s (offset + 2)) (offset + 4) v)
        (build_reaches s q (slot s (offset + 1)) (slot s (offset + 3))
          (offset + 4 + p.slotsUsed) v)
        (ReachesFull.single (Step.buildPar outName (p.fill v) (q.fill v)
          (Cong.refl _) (Cong.refl _)))
  | .splitMsg p q, _inName, outName, offset, v =>
      split_reaches
        (build_reaches s p (slot s offset) (slot s (offset + 2)) (offset + 4) v)
        (build_reaches s q (slot s (offset + 1)) (slot s (offset + 3))
          (offset + 4 + p.slotsUsed) v)
        (ReachesFull.single (Step.buildMsg outName (p.fill v) (q.fill v)
          (Cong.refl _) (Cong.refl _)))

/-! ## The cost is exact -/

/-- **The compiled soup has exactly `cost` atoms.**  An equality, so the
per-occurrence constant of three is both an upper and a lower bound on this
compiler's output. -/
theorem atomCount_build (s : Comb) : ∀ (p : Placement) (inName outName : Comb)
    (offset : ℕ),
    atomCount (build s p inName outName offset) = p.cost
  | .single ctx, inName, outName, offset => by
      simpa only [build, Placement.cost] using
        atomCount_assemble s ctx inName outName offset
  | .splitPar p q, _inName, _outName, offset
  | .splitMsg p q, _inName, _outName, offset => by
      have ihp := atomCount_build s p (slot s offset) (slot s (offset + 2)) (offset + 4)
      have ihq := atomCount_build s q (slot s (offset + 1)) (slot s (offset + 3))
        (offset + 4 + p.slotsUsed)
      simp only [atomCount, build, componentList, List.length_append,
        List.length_cons, List.length_nil, Placement.cost] at ihp ihq ⊢
      omega

/-- **Reachability and cost together**, since neither is the claim alone. -/
theorem build_reaches_at_exact_cost (s : Comb) (p : Placement)
    (inName outName v : Comb) :
    ReachesFull (par (build s p inName outName 0) (mm inName v))
        (mm outName (p.fill v))
      ∧ atomCount (build s p inName outName 0) = p.cost
      ∧ p.cost + 2 = p.leafWeight + 3 * p.occurrences :=
  ⟨build_reaches s p inName outName 0 v,
    atomCount_build s p inName outName 0,
    Placement.cost_eq_occurrences p⟩

/-! ## The compiled soup is linear

`assemble` earns linearity from a single arithmetic counter.  `build` branches,
so each duplication node reserves four slots for its own wiring and hands its
two sides **disjoint ranges** — which is what the offset indexing was for.
-/

theorem nodup_four_add {a b c e : Comb}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    (({a} + ({b} + ({c} + {e})) : Multiset Comb)).Nodup := by
  rw [show ({a} + ({b} + ({c} + {e})) : Multiset Comb)
      = ((([a, b, c, e] : List Comb)) : Multiset Comb) from rfl, Multiset.coe_nodup]
  simp [hab, hac, hae, hbc, hbe, hce]

/-- **The listening positions of a compiled placement.**  One is the name it
waits for; every other is a wiring slot inside the range the placement
reserved, and they are pairwise distinct. -/
theorem build_listening_structure (s : Comb) :
    ∀ (p : Placement) (inName outName : Comb) (offset : ℕ),
    ∃ wiring : Multiset Comb,
      listeningSubjects (build s p inName outName offset) = {inName} + wiring
        ∧ wiring.Nodup
        ∧ ∀ x ∈ wiring, ∃ i, offset ≤ i ∧ i < offset + p.slotsUsed ∧ x = slot s i
  | .single ctx, inName, outName, offset =>
      listening_structure s ctx inName outName offset
  | .splitPar p q, inName, outName, offset
  | .splitMsg p q, inName, outName, offset => by
      obtain ⟨w₁, hEq₁, hN₁, hS₁⟩ :=
        build_listening_structure s p (slot s offset) (slot s (offset + 2)) (offset + 4)
      obtain ⟨w₂, hEq₂, hN₂, hS₂⟩ :=
        build_listening_structure s q (slot s (offset + 1)) (slot s (offset + 3))
          (offset + 4 + p.slotsUsed)
      refine ⟨(w₁ + w₂) + ({slot s offset} + ({slot s (offset + 1)} +
        ({slot s (offset + 2)} + {slot s (offset + 3)}))), ?_, ?_, ?_⟩
      · rw [build, listeningSubjects_par, listeningSubjects_par,
          listeningSubjects_par, hEq₁, hEq₂]
        simp only [listeningSubjects, components, Multiset.singleton_bind,
          listenSubjects, coe_single, coe_pair]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨?_, ?_, ?_⟩
        · rw [Multiset.nodup_add]
          refine ⟨hN₁, hN₂, Multiset.disjoint_left.mpr ?_⟩
          intro a ha hb
          obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ a ha
          obtain ⟨j, hj, hjLt, hslot⟩ := hS₂ _ hb
          have := slot_injective s hslot
          omega
        · exact nodup_four_add (slot_ne (by omega)) (slot_ne (by omega))
            (slot_ne (by omega)) (slot_ne (by omega)) (slot_ne (by omega))
            (slot_ne (by omega))
        · refine Multiset.disjoint_left.mpr ?_
          intro a ha hb
          simp only [Multiset.mem_add, Multiset.mem_singleton] at ha hb
          rcases ha with h | h
          · obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ a h
            rcases hb with hb | hb | hb | hb <;>
              exact absurd (slot_injective s hb) (by omega)
          · obtain ⟨i, hi, hiLt, rfl⟩ := hS₂ a h
            rcases hb with hb | hb | hb | hb <;>
              exact absurd (slot_injective s hb) (by omega)
      · intro x hx
        simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
        simp only [Placement.slotsUsed]
        rcases hx with (h | h) | hb | hb | hb | hb
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ x h; exact ⟨i, by omega, by omega, rfl⟩
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₂ x h; exact ⟨i, by omega, by omega, rfl⟩
        · exact ⟨offset, by omega, by omega, hb⟩
        · exact ⟨offset + 1, by omega, by omega, hb⟩
        · exact ⟨offset + 2, by omega, by omega, hb⟩
        · exact ⟨offset + 3, by omega, by omega, hb⟩

/-- **The speaking positions of a compiled placement.**  Only the leaves speak:
a duplication node's atoms read names and write none until they fire. -/
theorem build_speaking_structure (s : Comb) :
    ∀ (p : Placement) (inName outName : Comb) (offset : ℕ),
    ∃ wiring : Multiset Comb,
      speakingSubjects (build s p inName outName offset) = wiring
        ∧ wiring.Nodup
        ∧ ∀ x ∈ wiring, ∃ i, offset ≤ i ∧ i < offset + p.slotsUsed ∧ x = slot s i
  | .single ctx, inName, outName, offset =>
      speaking_structure s ctx inName outName offset
  | .splitPar p q, inName, outName, offset
  | .splitMsg p q, inName, outName, offset => by
      obtain ⟨w₁, hEq₁, hN₁, hS₁⟩ :=
        build_speaking_structure s p (slot s offset) (slot s (offset + 2)) (offset + 4)
      obtain ⟨w₂, hEq₂, hN₂, hS₂⟩ :=
        build_speaking_structure s q (slot s (offset + 1)) (slot s (offset + 3))
          (offset + 4 + p.slotsUsed)
      refine ⟨w₁ + w₂, ?_, ?_, ?_⟩
      · rw [build, speakingSubjects_par, speakingSubjects_par,
          speakingSubjects_par, hEq₁, hEq₂]
        simp only [speakingSubjects, components, Multiset.singleton_bind,
          speakSubjects, Multiset.coe_nil]
        ac_rfl
      · rw [Multiset.nodup_add]
        refine ⟨hN₁, hN₂, Multiset.disjoint_left.mpr ?_⟩
        intro a ha hb
        obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ a ha
        obtain ⟨j, hj, hjLt, hslot⟩ := hS₂ _ hb
        have := slot_injective s hslot
        omega
      · intro x hx
        simp only [Multiset.mem_add] at hx
        simp only [Placement.slotsUsed]
        rcases hx with h | h
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₁ x h; exact ⟨i, by omega, by omega, rfl⟩
        · obtain ⟨i, hi, hiLt, rfl⟩ := hS₂ x h; exact ⟨i, by omega, by omega, rfl⟩

/-- **The compiled rule is linear.**  Wired from the slots of the very term it
waits at, no name in the compiled soup has two possible partners.  With
`build_reaches` and `atomCount_build` this makes `build` a compiler carrying the
same three guarantees `assemble` does. -/
theorem build_linear (s : Comb) (p : Placement) (outName : Comb) :
    Linear (build s p s outName 0) where
  listening := by
    obtain ⟨wiring, hEq, hN, hS⟩ := build_listening_structure s p s outName 0
    rw [hEq, Multiset.nodup_add]
    refine ⟨Multiset.nodup_singleton _, hN, Multiset.disjoint_left.mpr ?_⟩
    intro a ha hb
    simp only [Multiset.mem_singleton] at ha
    subst ha
    obtain ⟨i, -, -, hi⟩ := hS a hb
    exact ne_slot_self a i hi
  speaking := by
    obtain ⟨wiring, hEq, hN, -⟩ := build_speaking_structure s p s outName 0
    rw [hEq]; exact hN

/-! ## A worked rule

The shape a MeTTa rule of the form `f(X) → g(X, X)` compiles to: one
metavariable, two occurrences, each placed directly.
-/

/-- Two occurrences of the matched name, rejoined in parallel. -/
def twiceInParallel : Placement :=
  .splitPar (.single .hole) (.single .hole)

theorem twiceInParallel_fill (v : Comb) : twiceInParallel.fill v = par v v := rfl

theorem twiceInParallel_occurrences : twiceInParallel.occurrences = 2 := rfl

/-- **All three guarantees for a compiled metavariable.**  The compiled soup
delivers the matched value to every occurrence, has exactly `cost` atoms, and is
linear — so the trace it has is the only one available at any name. -/
theorem build_verified (s : Comb) (p : Placement) (outName v : Comb) :
    ReachesFull (par (build s p s outName 0) (mm s v)) (mm outName (p.fill v))
      ∧ atomCount (build s p s outName 0) = p.cost
      ∧ Linear (build s p s outName 0) :=
  ⟨build_reaches s p s outName 0 v,
    atomCount_build s p s outName 0,
    build_linear s p outName⟩

/-- **The worked rule, compiled and proved.**  Four atoms deliver the matched
name to both of its occurrences and rebuild the right-hand side: the two
forwarders that place the occurrences, the duplicator that splits the name, and
the constructor that rejoins the results. -/
theorem twiceInParallel_compiles (s outName v : Comb) :
    ReachesFull (par (build s twiceInParallel s outName 0) (mm s v))
        (mm outName (par v v))
      ∧ atomCount (build s twiceInParallel s outName 0) = 4
      ∧ Linear (build s twiceInParallel s outName 0) :=
  ⟨build_reaches s twiceInParallel s outName 0 v,
    atomCount_build s twiceInParallel s outName 0,
    build_linear s twiceInParallel outName⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
