import Mettapedia.Logic.ASP.WeightRules
import Mettapedia.Logic.ASP.HallStep

/-!
# Programs with weight definitions

A **weight definition** (`WeightDef`) is an atom `W`, a bound `L` and weighted literals, positive
`(a, w)` and negative `(a, w)`: `W` holds exactly when the true literals weigh at least `L`, a
positive literal being true when its atom holds and a negative one when its atom does not. A
**program with definitions** (`DefProgram`) is a normal program together with definitions. This
is what CeTTa's C solver (`AspWeightDef`) propagates natively: it does not unfold a definition
into rules, it keeps the sums of its true and false literals and explains each consequence by a
clause the definition implies.

## Stable models

The semantics is the one the C solver's model check (`asp_model_check_weighted`) decides:

* `DefProgram.Stable Q S`: every definition's atom is in `S` exactly when its body weighs at least
  its bound in `S` (`WeightDef.Holds`), and `S` is a stable model of the rules together with the
  facts `W.` for the definitions' atoms `W` in `S` (`DefProgram.given`).

The executable checker `DefProgram.isStable` decides it for a finite set (`isStable_iff`).

## Well-formedness and acyclicity

The C solver refuses a program unless no definition's atom is another's, no definition's atom heads
a rule, weights are positive and their sum fits in 64 bits, and no definition's atom lies on a cycle
of positive dependencies, a rule's head depending on its positive body atoms and a definition's atom
on its positive literals (`DefProgram.PosDep`, `DefProgram.Acyclic`).

* `DefProgram.WellFormed` is the part the semantics needs: definition atoms distinct and heading no
  rule.
* `DefProgram.wellFormedB` is the Boolean refusal test of the C solver's setup. It tests
  acyclicity by closing the dependencies of each definition's atom for as many rounds as there are
  atoms and requiring the result closed and without that atom (`DefProgram.acyclicB`); passing it
  implies `WellFormed` and `Acyclic` (`wellFormed_of_wellFormedB`, `acyclic_of_wellFormedB`). The
  converse, that every acyclic program passes, is not proved here.

The correspondence with the normalization by sequential weight counters is in
`WeightDefsNormalize`; acyclicity is exactly what it needs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

/-- A weight definition: `atom` holds exactly when the true literals among `pos` (atoms that hold)
and `neg` (atoms that do not), each with its weight, weigh at least `bound`. -/
structure WeightDef (A : Type u) where
  atom : A
  bound : ℕ
  pos : List (A × ℕ)
  neg : List (A × ℕ)
  deriving DecidableEq, Repr

/-- A normal program with weight definitions. -/
structure DefProgram (A : Type u) where
  rules : Program A
  defs : List (WeightDef A)
  deriving DecidableEq, Repr

namespace WLit

/-- The atom of a literal. -/
def atom : WLit A → A
  | pos a => a
  | neg a => a

end WLit

namespace WeightDef

variable (d : WeightDef A)

/-- The body as weighted literals: the positive literals, then the negative ones. -/
def terms : List (WTerm A) := d.pos.map (fun p => ⟨.pos p.1, p.2⟩) ++ d.neg.map fun p => ⟨.neg p.1, p.2⟩

/-- The body holds in `S`: its literals true in `S` weigh at least the bound. -/
def Holds (S : Set A) : Prop := d.bound ≤ weightIn d.terms S S

/-- The total weight of the literals. -/
def total : ℕ := (d.terms.map WTerm.weight).sum

/-- The definition as the weight rule `atom :- bound ≤ {terms}`. -/
def toWRule : WRule A := ⟨.atom d.atom, d.bound, d.terms⟩

/-- The fact for the definition's atom. -/
def fact : Rule A := ⟨d.atom, [], []⟩

variable {d}

theorem mem_terms {t : WTerm A} :
    t ∈ d.terms ↔ (∃ p ∈ d.pos, t = ⟨.pos p.1, p.2⟩) ∨ ∃ p ∈ d.neg, t = ⟨.neg p.1, p.2⟩ := by
  simp only [terms, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr ⟨p, hp, rfl⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact .inl ⟨p, hp, rfl⟩
    · exact .inr ⟨p, hp, rfl⟩

/-- The atom of a positive literal of the body is among the positive atoms. -/
theorem pos_of_mem_terms {t : WTerm A} {b : A} (ht : t ∈ d.terms) (hb : t.lit = .pos b) :
    b ∈ d.pos.map Prod.fst := by
  rcases mem_terms.mp ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · cases hb
    exact List.mem_map_of_mem hp
  · cases hb

/-- The atom of every literal of the body is among its positive or negative atoms. -/
theorem atom_of_mem_terms {t : WTerm A} (ht : t ∈ d.terms) :
    t.lit.atom ∈ d.pos.map Prod.fst ∨ t.lit.atom ∈ d.neg.map Prod.fst := by
  rcases mem_terms.mp ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact .inl (List.mem_map_of_mem hp)
  · exact .inr (List.mem_map_of_mem hp)

end WeightDef

namespace DefProgram

variable (Q : DefProgram A)

/-- The definitions' atoms, in order. -/
def defAtoms : List A := Q.defs.map WeightDef.atom

theorem atom_mem_defAtoms {d : WeightDef A} (hd : d ∈ Q.defs) : d.atom ∈ Q.defAtoms :=
  List.mem_map_of_mem hd

open Classical in
/-- The rules with the facts of the definitions' atoms in `S`: the program whose reduct by `S` the
C solver's model check takes the least model of. -/
noncomputable def given (S : Set A) : Program A :=
  Q.rules ++ (Q.defs.filter fun d => d.atom ∈ S).map WeightDef.fact

/-- **Stable model of a program with definitions**: each definition's atom is in `S` exactly when
its body holds in `S`, and `S` is the least model of the reduct by `S` of the rules with the facts
of the definitions' atoms in `S`. -/
def Stable (S : Set A) : Prop := (∀ d ∈ Q.defs, d.atom ∈ S ↔ d.Holds S) ∧ (Q.given S).Stable S

/-- The definitions are well formed for the semantics: their atoms are distinct and head no rule. -/
structure WellFormed : Prop where
  nodup : Q.defAtoms.Nodup
  noHead : ∀ r ∈ Q.rules, r.head ∉ Q.defAtoms

/-- Positive dependency: `a` depends on `b` when `b` is a positive body atom of a rule for `a`, or a
positive literal of the definition of `a`. -/
def PosDep (b a : A) : Prop :=
  (∃ r ∈ Q.rules, r.head = a ∧ b ∈ r.pos) ∨ ∃ d ∈ Q.defs, d.atom = a ∧ b ∈ d.pos.map Prod.fst

/-- **Acyclicity**: no definition's atom lies on a cycle of positive dependencies. -/
def Acyclic : Prop := ∀ d ∈ Q.defs, ¬ Relation.TransGen Q.PosDep d.atom d.atom

/-! ## The program with the facts -/

theorem mem_given {S : Set A} {r : Rule A} :
    r ∈ Q.given S ↔ r ∈ Q.rules ∨ ∃ d ∈ Q.defs, d.atom ∈ S ∧ r = d.fact := by
  classical
  simp only [given, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨d, ⟨hd, hS⟩, rfl⟩)
    · exact .inl h
    · exact .inr ⟨d, hd, hS, rfl⟩
  · rintro (h | ⟨d, hd, hS, rfl⟩)
    · exact .inl h
    · exact .inr ⟨d, ⟨hd, hS⟩, rfl⟩

/-- The immediate consequences of the rules with the facts: those of the rules, and the
definitions' atoms in `S`. -/
theorem step_given (S I N : Set A) :
    (Q.given S).step I N = Q.rules.step I N ∪ {a | ∃ d ∈ Q.defs, d.atom = a ∧ a ∈ S} := by
  ext a
  simp only [Program.step, Set.mem_union, Set.mem_ofPred_eq, mem_given]
  constructor
  · rintro ⟨r, hr | ⟨d, hd, hS, rfl⟩, rfl, holds⟩
    · exact .inl ⟨r, hr, rfl, holds⟩
    · exact .inr ⟨d, hd, rfl, hS⟩
  · rintro (⟨r, hr, rfl, holds⟩ | ⟨d, hd, rfl, hS⟩)
    · exact ⟨r, .inl hr, rfl, holds⟩
    · exact ⟨d.fact, .inr ⟨d, hd, hS, rfl⟩, rfl, by simp [Rule.Holds, WeightDef.fact]⟩

theorem rules_step_subset_given (S I N : Set A) : Q.rules.step I N ⊆ (Q.given S).step I N := by
  rw [step_given]
  exact Set.subset_union_left

variable {Q} in
/-- A stable model is closed under the rules. -/
theorem Stable.rules_step_subset {S : Set A} (h : Q.Stable S) : Q.rules.step S S ⊆ S := by
  intro a ha
  have := Q.rules_step_subset_given S S S ha
  rwa [(Q.given S).stable_step_eq h.2] at this

variable {Q} in
/-- An atom of a stable model that is no definition's atom has a rule whose body holds. -/
theorem Stable.supported {S : Set A} (h : Q.Stable S) {a : A} (ha : a ∈ S) (notDef : a ∉ Q.defAtoms) :
    ∃ r ∈ Q.rules, r.head = a ∧ r.Holds S S := by
  have := (Q.given S).stable_step_eq h.2
  rw [← this, step_given] at ha
  rcases ha with ha | ⟨d, hd, rfl, -⟩
  · exact ha
  · exact absurd (Q.atom_mem_defAtoms hd) notDef

/-! ## Deciding stability -/

section Executable

variable [DecidableEq A]

/-- The executable body test. -/
def _root_.Mettapedia.Logic.ASP.WeightDef.holdsFin (d : WeightDef A) (S : Finset A) : Bool :=
  decide (d.bound ≤ weightFin d.terms S S)

theorem _root_.Mettapedia.Logic.ASP.WeightDef.holdsFin_iff (d : WeightDef A) (S : Finset A) :
    d.holdsFin S = true ↔ d.Holds ↑S := by
  simp [WeightDef.holdsFin, WeightDef.Holds, weightFin_eq]

/-- The rules with the facts of the definitions' atoms in `S`, computed. -/
def givenFin (S : Finset A) : Program A :=
  Q.rules ++ (Q.defs.filter fun d => decide (d.atom ∈ S)).map WeightDef.fact

theorem given_coe (S : Finset A) : Q.given ↑S = Q.givenFin S := by
  classical
  unfold given givenFin
  congr 3
  funext d
  exact decide_eq_decide.mpr Finset.mem_coe

/-- **The executable stable-model check**, as `asp_model_check_weighted` makes it. -/
def isStable (S : Finset A) : Bool :=
  Q.defs.all (fun d => decide (d.atom ∈ S) == d.holdsFin S) && (Q.givenFin S).isStable S

theorem isStable_iff (S : Finset A) : Q.isStable S = true ↔ Q.Stable ↑S := by
  simp only [isStable, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Stable, given_coe,
    Program.isStable_iff]
  refine and_congr (forall₂_congr fun d _ => ?_) Iff.rfl
  rw [Finset.mem_coe, ← WeightDef.holdsFin_iff]
  constructor
  · intro h
    rw [← h, decide_eq_true_iff]
  · intro h
    by_cases hm : d.atom ∈ S
    · simp [hm, h.mp hm]
    · have : d.holdsFin S = false := by
        cases hh : d.holdsFin S
        · rfl
        · exact absurd (h.mpr hh) hm
      simp [hm, this]

end Executable

/-! ## The C solver's refusal test -/

section Refusal

variable [DecidableEq A]

/-- The atoms in the order the C solver numbers them: their last occurrences in `head :: pos ++ neg`
over the rules, then in `atom :: pos ++ neg` over the definitions. -/
def atomList : List A :=
  (Q.rules.flatMap (fun r => r.head :: (r.pos ++ r.neg)) ++
    Q.defs.flatMap fun d => d.atom :: (d.pos.map Prod.fst ++ d.neg.map Prod.fst)).dedup

theorem mem_atomList {a : A} :
    a ∈ Q.atomList ↔ (∃ r ∈ Q.rules, a = r.head ∨ a ∈ r.pos ∨ a ∈ r.neg) ∨
      ∃ d ∈ Q.defs, a = d.atom ∨ a ∈ d.pos.map Prod.fst ∨ a ∈ d.neg.map Prod.fst := by
  simp only [atomList, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_cons]

theorem head_mem_atomList {r : Rule A} (hr : r ∈ Q.rules) : r.head ∈ Q.atomList :=
  Q.mem_atomList.mpr (.inl ⟨r, hr, .inl rfl⟩)

theorem pos_mem_atomList {r : Rule A} (hr : r ∈ Q.rules) {a : A} (ha : a ∈ r.pos) : a ∈ Q.atomList :=
  Q.mem_atomList.mpr (.inl ⟨r, hr, .inr (.inl ha)⟩)

theorem neg_mem_atomList {r : Rule A} (hr : r ∈ Q.rules) {a : A} (ha : a ∈ r.neg) : a ∈ Q.atomList :=
  Q.mem_atomList.mpr (.inl ⟨r, hr, .inr (.inr ha)⟩)

theorem defAtom_mem_atomList {d : WeightDef A} (hd : d ∈ Q.defs) : d.atom ∈ Q.atomList :=
  Q.mem_atomList.mpr (.inr ⟨d, hd, .inl rfl⟩)

theorem termAtom_mem_atomList {d : WeightDef A} (hd : d ∈ Q.defs) {t : WTerm A} (ht : t ∈ d.terms) :
    t.lit.atom ∈ Q.atomList :=
  Q.mem_atomList.mpr (.inr ⟨d, hd, .inr (WeightDef.atom_of_mem_terms ht)⟩)

/-- The atoms `a` depends on positively in one step. -/
def succ (a : A) : List A :=
  (Q.rules.filter fun r => r.head = a).flatMap Rule.pos ++
    (Q.defs.filter fun d => d.atom = a).flatMap fun d => d.pos.map Prod.fst

theorem mem_succ {a b : A} : b ∈ Q.succ a ↔ Q.PosDep b a := by
  simp only [succ, List.mem_append, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, PosDep]
  constructor
  · rintro (⟨r, ⟨hr, rfl⟩, hb⟩ | ⟨d, ⟨hd, rfl⟩, hb⟩)
    · exact .inl ⟨r, hr, rfl, hb⟩
    · exact .inr ⟨d, hd, rfl, hb⟩
  · rintro (⟨r, hr, rfl, hb⟩ | ⟨d, hd, rfl, hb⟩)
    · exact .inl ⟨r, ⟨hr, rfl⟩, hb⟩
    · exact .inr ⟨d, ⟨hd, rfl⟩, hb⟩

/-- `n` rounds of adding the atoms the listed ones depend on. -/
def closure : ℕ → List A → List A
  | 0, l => l
  | n + 1, l => closure n (l ++ l.flatMap Q.succ).dedup

theorem subset_closure : ∀ (n : ℕ) (l : List A), ∀ a ∈ l, a ∈ Q.closure n l
  | 0, _, _, h => h
  | n + 1, _, a, h => subset_closure n _ a (List.mem_dedup.mpr (List.mem_append_left _ h))

/-- The listed atoms depend on no atom outside the list. -/
def closedB (l : List A) : Bool := l.all fun x => (Q.succ x).all (· ∈ l)

/-- The C solver's acyclicity test, by closure: for each definition's atom, the atoms it depends on
through at least one step, closed after as many rounds as there are atoms, do not contain it. -/
def acyclicB : Bool :=
  Q.defs.all fun d =>
    Q.closedB (Q.closure Q.atomList.length (Q.succ d.atom)) &&
      !decide (d.atom ∈ Q.closure Q.atomList.length (Q.succ d.atom))

/-- **The C solver's refusal test** (`weights_setup`): definition atoms distinct and heading no rule,
weights positive with a total that fits in 64 bits, and no definition atom on a positive cycle. -/
def wellFormedB : Bool :=
  decide Q.defAtoms.Nodup && Q.rules.all (fun r => !decide (r.head ∈ Q.defAtoms)) &&
    Q.defs.all (fun d => d.terms.all (fun t => decide (0 < t.weight)) && decide (d.total < 2 ^ 64)) &&
    Q.acyclicB

/-- A closed list containing the direct dependencies of `a` contains all its dependencies. -/
theorem mem_of_transGen {l : List A} (closed : Q.closedB l = true) {a : A} (start : ∀ b ∈ Q.succ a, b ∈ l)
    {b : A} (h : Relation.TransGen Q.PosDep b a) : b ∈ l := by
  simp only [closedB, List.all_eq_true, decide_eq_true_eq] at closed
  induction h using Relation.TransGen.head_induction_on with
  | single hb => exact start _ ((Q.mem_succ).mpr hb)
  | head hxy _ ih => exact closed _ ih _ ((Q.mem_succ).mpr hxy)

theorem acyclic_of_acyclicB (h : Q.acyclicB = true) : Q.Acyclic := by
  intro d hd cyc
  have := List.all_eq_true.mp h d hd
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
  exact this.2 (Q.mem_of_transGen this.1 (Q.subset_closure _ _) cyc)

theorem acyclic_of_wellFormedB (h : Q.wellFormedB = true) : Q.Acyclic := by
  simp only [wellFormedB, Bool.and_eq_true] at h
  exact Q.acyclic_of_acyclicB h.2

theorem wellFormed_of_wellFormedB (h : Q.wellFormedB = true) : Q.WellFormed := by
  simp only [wellFormedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

end Refusal

end DefProgram

end Mettapedia.Logic.ASP
