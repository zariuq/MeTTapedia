import Mettapedia.Logic.ASP.WeightRules
import Mettapedia.Logic.ASP.Enumeration

/-!
# Controls for weight rules and their normalization

For every program below, its stable models are stated and computed by the kernel
(`decide +kernel`) from the executable checker of `WeightRules`, and read as a statement about
stable models through `mem_stableModels` and `stable_iff_mem_stableModels`.

Then the normalization is checked against them, independently of the normalization theorem:
the stable models of the normalized normal program are enumerated by the normal-program
checker over its negated atoms (`Program.stableModelsNeg`, proved complete and sound by
`Program.mem_stableModelsNeg`); restricted to the original atoms they are exactly the weight
program's stable models, and there are as many of them, so each weight stable model has
exactly one extension (`Agrees`, read semantically by `Agrees.stable_iff`). Agreement is run
for every program (`#guard`), and decided by the kernel for the even loop, the choice with a
weight body, the positive loop and the single mixed rule. On the even loop, the positive loop
and the single rule, the reference driver's enumeration of the normalized program agrees as
well (`driverAgrees`).

* **Cardinality rules**, `{a; b; c}. p :- L ≤ {a, b, c}.`, with the bounds `0`, `1`, `3` (the
  number of literals) and `4` (one more): `p` is in the model with `X ⊆ {a, b, c}` exactly when
  `|X| ≥ L`, so always for `0` and never for `4`. The constraint form,
  `{a; b; c}. :- 2 ≤ {a, b, c}.`, keeps the sets with at most one atom.
* **Mixed literals**: `{a; b; c}. p :- 3 ≤ {a = 2, not b = 2, c = 1}.`, and an even loop through
  negated weight literals, `p :- 2 ≤ {not q = 2}. q :- 1 ≤ {not p = 1}.`, with the models `{p}`
  and `{q}`.
* **`{a; b; c} = 2`**: the choice, the lower-bound rule `two :- 2 ≤ {a, b, c}.` with the
  constraint `:- 1 ≤ {not two = 1}.`, and the upper-bound constraint `:- 3 ≤ {a, b, c}.`; the
  models are the three pairs, with `two`. The stable models of its normalization are exactly
  the extensions of these three (`exactlyTwo_normalize_stable_iff`).
* **A choice with a weight body**: `{c}. {a; b} :- 2 ≤ {c = 2}.`
* **A positive loop through a weight body**: `{q}. p :- 2 ≤ {p = 1, q = 1}.` Its stable models
  are `{}` and `{q}`. `{p, q}` satisfies every rule and is a fixed point of the immediate
  consequences, but it is not stable: `p` supports itself.
* **The normalization itself**, on one rule, `p :- 2 ≤ {a = 1, not b = 2}.`, is the stated list
  of fourteen normal rules (`mixedRule_normalize`), the reference output for an implementation
  that mirrors it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.WeightRulesControls

open WProgram

/-- The atoms of the controls. -/
inductive Atom
  | a
  | b
  | c
  | p
  | q
  | two
  deriving DecidableEq, Repr

open Atom

/-- `x = 1`. -/
abbrev one (x : Atom) : WTerm Atom := ⟨.pos x, 1⟩

/-- `not x = 1`. -/
abbrev notOne (x : Atom) : WTerm Atom := ⟨.neg x, 1⟩

/-- `{a; b; c}.` -/
def abc : WRule Atom := ⟨.choice [a, b, c], 0, []⟩

/-- The original atoms of the stable models of the normalized program, which are found by the
normal-program enumerator over the negated atoms (`Program.mem_stableModelsNeg`). -/
def normalizedModels (W : WProgram Atom) : Finset (Finset Atom) := W.normalize.stableModelsNeg.image restrictFin

/-- **Agreement**: restricted to the original atoms, the stable models of the normalized program
are the weight program's, and there are as many of them, so no two have the same original
atoms. -/
def Agrees (W : WProgram Atom) : Prop :=
  normalizedModels W = W.stableModels ∧ W.normalize.stableModelsNeg.card = W.stableModels.card

instance : DecidablePred Agrees := fun W => by
  unfold Agrees
  infer_instance

/-- Agreement, computed. -/
def agrees (W : WProgram Atom) : Bool := decide (Agrees W)

/-- **What agreement says**: the stable models of the weight program are the restrictions of the
stable models of the normalized program. This reads `Agrees` through the two checkers alone,
without the normalization theorem. -/
theorem Agrees.stable_iff {W : WProgram Atom} (h : Agrees W) (S : Finset Atom) :
    W.Stable ↑S ↔ ∃ M : Finset (Atom ⊕ Aux Atom), W.normalize.Stable ↑M ∧ restrictFin M = S := by
  rw [← mem_stableModels, ← h.1, normalizedModels, Finset.mem_image]
  simp only [Program.mem_stableModelsNeg]

/-- The same agreement with the reference driver's enumeration of the normalized program. -/
def driverAgrees (W : WProgram Atom) : Bool :=
  match W.normalize.enumerate.models? with
  | some Ms =>
    decide ((Ms.map fun M => (M.filterMap Sum.getLeft?).toFinset).toFinset = W.stableModels) &&
      Ms.length == W.stableModels.card
  | none => false

/-! ## Cardinality rules: the bounds `0`, `1`, `n` and `n + 1` -/

/-- `{a; b; c}. p :- L ≤ {a, b, c}.` -/
def card (L : ℕ) : WProgram Atom := [abc, ⟨.atom p, L, [one a, one b, one c]⟩]

theorem card0_stableModels :
    (card 0).stableModels = {{p}, {a, p}, {b, p}, {c, p}, {a, b, p}, {a, c, p}, {b, c, p}, {a, b, c, p}} := by
  decide +kernel

theorem card1_stableModels :
    (card 1).stableModels = {∅, {a, p}, {b, p}, {c, p}, {a, b, p}, {a, c, p}, {b, c, p}, {a, b, c, p}} := by
  decide +kernel

theorem card3_stableModels :
    (card 3).stableModels = {∅, {a}, {b}, {c}, {a, b}, {a, c}, {b, c}, {a, b, c, p}} := by
  decide +kernel

theorem card4_stableModels :
    (card 4).stableModels = {∅, {a}, {b}, {c}, {a, b}, {a, c}, {b, c}, {a, b, c}} := by
  decide +kernel

/-- With the bound one more than the number of literals, `p` is in no stable model. -/
theorem card4_no_p (S : Set Atom) (h : (card 4).Stable S) : p ∉ S := by
  obtain ⟨M, hM, rfl⟩ := ((card 4).stable_iff_mem_stableModels S).mp h
  rw [card4_stableModels] at hM
  simp only [Finset.mem_insert, Finset.mem_singleton] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `{a; b; c}. :- 2 ≤ {a, b, c}.`: a cardinality constraint. -/
def atMostOne : WProgram Atom := [abc, ⟨.empty, 2, [one a, one b, one c]⟩]

theorem atMostOne_stableModels : atMostOne.stableModels = {∅, {a}, {b}, {c}} := by
  decide +kernel

#guard agrees (card 0)
#guard agrees (card 1)
#guard agrees (card 3)
#guard agrees (card 4)
#guard agrees atMostOne

/-! ## Mixed positive and negated literals -/

/-- `{a; b; c}. p :- 3 ≤ {a = 2, not b = 2, c = 1}.` -/
def mixed : WProgram Atom := [abc, ⟨.atom p, 3, [⟨.pos a, 2⟩, ⟨.neg b, 2⟩, ⟨.pos c, 1⟩]⟩]

theorem mixed_stableModels :
    mixed.stableModels = {∅, {a, p}, {b}, {c, p}, {a, b}, {a, c, p}, {b, c}, {a, b, c, p}} := by
  decide +kernel

/-- `p :- 2 ≤ {not q = 2}. q :- 1 ≤ {not p = 1}.`: an even loop through negated weight literals. -/
def evenLoop : WProgram Atom := [⟨.atom p, 2, [⟨.neg q, 2⟩]⟩, ⟨.atom q, 1, [notOne p]⟩]

theorem evenLoop_stableModels : evenLoop.stableModels = {{p}, {q}} := by
  decide +kernel

theorem evenLoop_stable_iff (S : Set Atom) : evenLoop.Stable S ↔ S = {p} ∨ S = {q} := by
  rw [stable_iff_mem_stableModels, evenLoop_stableModels]
  simp [eq_comm]

theorem evenLoop_agrees : Agrees evenLoop := by
  decide +kernel

#guard agrees mixed
#guard driverAgrees evenLoop

/-! ## `{a; b; c} = 2` -/

/-- `{a; b; c}. two :- 2 ≤ {a, b, c}. :- 1 ≤ {not two = 1}. :- 3 ≤ {a, b, c}.` -/
def exactlyTwo : WProgram Atom :=
  [abc, ⟨.atom two, 2, [one a, one b, one c]⟩, ⟨.empty, 1, [notOne two]⟩, ⟨.empty, 3, [one a, one b, one c]⟩]

theorem exactlyTwo_stableModels : exactlyTwo.stableModels = {{a, b, two}, {a, c, two}, {b, c, two}} := by
  decide +kernel

/-- **The stable models of the normalization of `{a; b; c} = 2`** are the extensions of the three
pairs, by the normalization theorem. -/
theorem exactlyTwo_normalize_stable_iff (M : Set (Atom ⊕ Aux Atom)) :
    exactlyTwo.normalize.Stable M ↔
      M = exactlyTwo.extend {a, b, two} ∨ M = exactlyTwo.extend {a, c, two} ∨
        M = exactlyTwo.extend {b, c, two} := by
  rw [stable_normalize_iff, stable_iff_mem_stableModels, exactlyTwo_stableModels]
  constructor
  · rintro ⟨⟨S, hS, same⟩, hM⟩
    rw [hM, ← same]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨{a, b, two}, by simp, by rw [preimage_inl_extend]; simp⟩, rfl⟩
    · exact ⟨⟨{a, c, two}, by simp, by rw [preimage_inl_extend]; simp⟩, rfl⟩
    · exact ⟨⟨{b, c, two}, by simp, by rw [preimage_inl_extend]; simp⟩, rfl⟩

#guard agrees exactlyTwo

/-! ## A choice with a weight body -/

/-- `{c}. {a; b} :- 2 ≤ {c = 2}.` -/
def choiceBody : WProgram Atom := [⟨.choice [c], 0, []⟩, ⟨.choice [a, b], 2, [⟨.pos c, 2⟩]⟩]

theorem choiceBody_stableModels : choiceBody.stableModels = {∅, {c}, {a, c}, {b, c}, {a, b, c}} := by
  decide +kernel

theorem choiceBody_agrees : Agrees choiceBody := by
  decide +kernel

/-! ## A positive loop through a weight body -/

/-- `{q}. p :- 2 ≤ {p = 1, q = 1}.` -/
def selfLoop : WProgram Atom := [⟨.choice [q], 0, []⟩, ⟨.atom p, 2, [one p, one q]⟩]

theorem selfLoop_stableModels : selfLoop.stableModels = {∅, {q}} := by
  decide +kernel

/-- `{p, q}` satisfies every rule. -/
theorem selfLoop_pq_models : selfLoop.Models ↑({p, q} : Finset Atom) :=
  (selfLoop.modelsFin_iff _).mp (by decide)

/-- `{p, q}` is a fixed point of the immediate consequences read against itself. -/
theorem selfLoop_pq_supported : selfLoop.step ↑({p, q} : Finset Atom) ↑({p, q} : Finset Atom) = ↑({p, q} : Finset Atom) := by
  rw [← coe_stepFin, Finset.coe_inj]
  decide

/-- **A self-supporting atom is not stable**: `{p, q}` is not the least model of its reduct. -/
theorem selfLoop_pq_not_stable : ¬ selfLoop.Stable ↑({p, q} : Finset Atom) := by
  rw [← isStable_iff]
  decide

theorem selfLoop_agrees : Agrees selfLoop := by
  decide +kernel

#guard driverAgrees selfLoop

/-! ## The normalization of one rule -/

/-- `p :- 2 ≤ {a = 1, not b = 2}.` -/
def mixedRule : WProgram Atom := [⟨.atom p, 2, [one a, ⟨.neg b, 2⟩]⟩]

/-- The counter atom `c(0, i, k)`. -/
abbrev cnt (i k : ℕ) : Atom ⊕ Aux Atom := .inr (.count 0 i k)

/-- **The sequential weight counter of `p :- 2 ≤ {a = 1, not b = 2}.`**, rule by rule. -/
theorem mixedRule_normalize : mixedRule.normalize =
    [⟨cnt 0 0, [], []⟩,
      ⟨cnt 1 0, [cnt 0 0], []⟩, ⟨cnt 1 1, [cnt 0 0, .inl a], []⟩,
      ⟨cnt 1 1, [cnt 0 1], []⟩, ⟨cnt 1 2, [cnt 0 1, .inl a], []⟩,
      ⟨cnt 1 2, [cnt 0 2], []⟩, ⟨cnt 1 2, [cnt 0 2, .inl a], []⟩,
      ⟨cnt 2 0, [cnt 1 0], []⟩, ⟨cnt 2 2, [cnt 1 0], [.inl b]⟩,
      ⟨cnt 2 1, [cnt 1 1], []⟩, ⟨cnt 2 2, [cnt 1 1], [.inl b]⟩,
      ⟨cnt 2 2, [cnt 1 2], []⟩, ⟨cnt 2 2, [cnt 1 2], [.inl b]⟩,
      ⟨.inl p, [cnt 2 2], []⟩] := by
  decide

theorem mixedRule_stableModels : mixedRule.stableModels = {{p}} := by
  decide +kernel

theorem mixedRule_agrees : Agrees mixedRule := by
  decide +kernel

#guard driverAgrees mixedRule

#eval mixedRule.normalize.length
#eval (card 3).normalize.length
#eval exactlyTwo.normalize.length
#eval normalizedModels exactlyTwo

end Mettapedia.Logic.ASP.WeightRulesControls
