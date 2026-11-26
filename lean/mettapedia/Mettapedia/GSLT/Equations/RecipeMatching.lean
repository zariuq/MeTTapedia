import Mettapedia.UniversalAlgebra.FreeModel
import Mathlib.Data.Finset.Image

/-! # Compound matching in a finite catalogue of constructor recipes

An operation is indexed by its declared arity. A recipe records its result
class and its argument classes. This factors representation of a value from
the (possibly many) occurrences of that value in a store.

There are two different completeness questions. Running a query over a
catalogue is exact for its recipes. Comparing that catalogue against the
mathematical term quotient additionally needs coverage of the instantiated
constructors. In particular, a finite catalogue need not contain every
constructor application possible in the freely generated quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.RecipeMatching

open UniversalAlgebra

variable {S : Signature} {C A : Type*}

abbrev Children (S : Signature) (C : Type*) (f : S.Operation) :=
  Fin (S.arity f) → C

/-- A finite family of relations; all index orders are views of these tuples. -/
structure Catalogue (S : Signature) (C : Type*) where
  rows (f : S.Operation) : List (C × Children S C f)

namespace Catalogue

variable (g : Catalogue S C)

/-- Check a finite pattern over the relations with one shared variable valuation.
Local variables for intermediate nodes are existentially joined on their
class. Cycles in the catalogue do not cause recursion on the catalogue. -/
def Matches (ρ : Nat → C) : Term S → C → Prop
  | .var v, c => ρ v = c
  | .op f ps, c =>
    ∃ args, (c, args) ∈ g.rows f ∧ ∀ i, Matches ρ (ps i) (args i)

/-- Bottom-up evaluation of the query with the variable classes fixed.
Child result sets are computed once per pattern position, even if many
recipes have that child class. This is the relation-scan algorithm; a trie
cursor can restrict the scan using any bound coordinate. -/
def roots [DecidableEq C] (ρ : Nat → C) : Term S → Finset C
  | .var v => {ρ v}
  | .op f ps =>
    let eligible := Vector.ofFn (fun i => roots ρ (ps i))
    ((g.rows f).filterMap fun (c, args) =>
      if ∀ i, args i ∈ eligible[i.val] then some c else none).toFinset

theorem mem_roots_iff [DecidableEq C] (ρ : Nat → C) (p : Term S) (c : C) :
    c ∈ g.roots ρ p ↔ g.Matches ρ p c := by
  induction p generalizing c with
  | var v => simp [roots, Matches, eq_comm]
  | op f ps ih =>
    simp only [roots, Matches, List.mem_toFinset, List.mem_filterMap, Prod.exists,
      Vector.getElem_ofFn]
    constructor
    · rintro ⟨root, args, mem, h⟩
      split at h
      · rename_i hs
        cases h
        exact ⟨args, mem, fun i => (ih i _).1 (hs i)⟩
      · cases h
    · rintro ⟨args, mem, hs⟩
      refine ⟨c, args, mem, ?_⟩
      simp [fun i => (ih i _).2 (hs i)]

/-- Functional dependencies of a congruence-closed e-node table. A tuple of
children and an operation determine at most one result class, not conversely. -/
def Functional : Prop :=
  ∀ f args a b, (a, args) ∈ g.rows f → (b, args) ∈ g.rows f → a = b

theorem unique_root (funct : g.Functional) (ρ : Nat → C) (p : Term S)
    {a b : C} (ha : g.Matches ρ p a) (hb : g.Matches ρ p b) : a = b := by
  induction p generalizing a b with
  | var v => exact ha.symm.trans hb
  | op f ps ih =>
    obtain ⟨as, arow, achild⟩ := ha
    obtain ⟨bs, brow, bchild⟩ := hb
    have : as = bs := funext fun i => ih i (achild i) (bchild i)
    subst bs
    exact funct f as a b arow brow

/-- Every stored recipe interprets correctly in the independent algebra. -/
def Sound (m : Model S A) (denote : C → A) : Prop :=
  ∀ f c args, (c, args) ∈ g.rows f → m.interpret f (denote ∘ args) = denote c

/-- The support of a pattern instance. All child patterns have support, and
the table contains at least one recipe whose child denotations match their
values. The relation does not ask for any particular result class. -/
def Covered (m : Model S A) (denote : C → A) (ρ : Nat → C) : Term S → Prop
  | .var v => ∃ c, denote c = denote (ρ v)
  | .op f ps =>
    (∀ i, Covered m denote ρ (ps i)) ∧
    ∃ c args, (c, args) ∈ g.rows f ∧ ∀ i, denote (args i) = (ps i).evaluate m (denote ∘ ρ)

/-- No invented match, and no loss on the represented instances.
Injectivity means class identifiers have been reconciled, not that the
underlying syntax-to-class map is injective. -/
theorem matches_iff (m : Model S A) (denote : C → A) (sound : g.Sound m denote)
    (inj : Function.Injective denote) (ρ : Nat → C) (p : Term S) (c : C) :
    g.Matches ρ p c ↔ g.Covered m denote ρ p ∧ p.evaluate m (denote ∘ ρ) = denote c := by
  induction p generalizing c with
  | var v =>
    exact ⟨fun h => ⟨⟨ρ v, rfl⟩, congrArg denote h⟩, fun h => inj h.2⟩
  | op f ps ih =>
    simp only [Matches, Covered, Term.evaluate]
    constructor
    · rintro ⟨args, mem, hs⟩
      have child := fun i => (ih i (args i)).1 (hs i)
      have eq : (fun i => (ps i).evaluate m (denote ∘ ρ)) = denote ∘ args :=
        funext fun i => (child i).2
      exact ⟨⟨fun i => (child i).1, c, args, mem, fun i => (child i).2.symm⟩,
        eq ▸ sound f c args mem⟩
    · rintro ⟨⟨cs, root, args, mem, hs⟩, result⟩
      have eq : denote ∘ args = (fun i => (ps i).evaluate m (denote ∘ ρ)) := funext hs
      have same := inj ((sound f root args mem).symm.trans (eq ▸ result))
      exact ⟨args, same ▸ mem, fun i => (ih i _).2 ⟨cs i, (hs i).symm⟩⟩

/-- A well-formed semantic index has the functional dependencies expected by
relational e-matching. -/
theorem functional_of_sound (m : Model S A) (denote : C → A) (sound : g.Sound m denote)
    (inj : Function.Injective denote) : g.Functional :=
  fun f args a b ha hb => inj ((sound f a args ha).symm.trans (sound f b args hb))

/-- Instance for actual generated equation consequence, not equality in a
second copy of the matcher. Coverage is the same algebraic obligation above. -/
theorem roots_iff_generated [DecidableEq C] (E : EquationSystem S) (rep : C → Term S)
    (sound : g.Sound (TermQuotient.model E) (TermQuotient.classOf E ∘ rep))
    (inj : Function.Injective (TermQuotient.classOf E ∘ rep))
    (ρ : Nat → C) (p : Term S) (c : C) :
    c ∈ g.roots ρ p ↔
      g.Covered (TermQuotient.model E) (TermQuotient.classOf E ∘ rep) ρ p ∧
      EquationalConsequence E (p.subst (rep ∘ ρ), rep c) := by
  rw [g.mem_roots_iff, g.matches_iff _ _ sound inj]
  have eval : p.evaluate (TermQuotient.model E) ((TermQuotient.classOf E ∘ rep) ∘ ρ) =
      TermQuotient.classOf E (p.subst (rep ∘ ρ)) := by
    rw [← TermQuotient.evaluate_canonical E (p.subst (rep ∘ ρ)), Term.evaluate_subst]
    simp only [TermQuotient.evaluate_canonical]
    rfl
  rw [eval]
  exact and_congr_right fun _ => TermQuotient.classOf_eq_iff E _ _

/-! ## A head signature is a one-sided filter -/

def HeadSummary {Bit : Type*} (code : S.Operation → Bit) (bits : C → Finset Bit) : Prop :=
  ∀ f c args, (c, args) ∈ g.rows f → code f ∈ bits c

theorem missing_bit_excludes {Bit : Type*} {code : S.Operation → Bit} {bits : C → Finset Bit}
    (summary : g.HeadSummary code bits) (ρ : Nat → C) (f : S.Operation)
    (ps : Fin (S.arity f) → Term S) (c : C) (missing : code f ∉ bits c) :
    ¬ g.Matches ρ (.op f ps) c := by
  rintro ⟨args, hc, _⟩
  exact missing (summary f c args hc)

end Catalogue

end Mettapedia.GSLT.Equations.RecipeMatching
