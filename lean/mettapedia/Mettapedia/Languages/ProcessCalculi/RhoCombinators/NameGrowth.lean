/-
# Name equivalence is decidable; names are not bounded by the program

Under the constructors, a name is no longer a subterm of the program: it is
assembled at runtime. Two questions follow, and the cost account cannot be
extended to a constructor calculus until both are answered.

**Is name equivalence still decidable?** Yes, and cheaply. The congruence of
this calculus is component-bag equality, and component bags are computable over
a decidable term type, so `Cong` is a decidable relation — `decidableCong`.
Deciding it does not need a search; it needs one bag comparison.

**Is the cost of deciding it bounded by the program?** No, and that is the
finding. A soup of `2 * k` atoms reduces to a message whose name has size at
least `2 ^ k`. The program is linear in the number of doubling stages and the
name it builds is exponential in it, so no accounting that decorates a fixed
term structure can bound the sizes it will be asked to compare. Concretely:
`growth_is_exponential_in_atom_count`.

The mechanism is unremarkable, which is what makes the result solid rather than
contrived. One stage duplicates a message with `dd` and rejoins the two copies
with `consPar`; the rejoined name is twice the size of what arrived. Chaining
stages composes the doubling. Nothing in the gadget is adversarial — it is the
ordinary use of the two rules the paper's translation already needs.

The consequence for the existing cost development is stated, not assumed: that
development decorates a fixed term structure and its saturation condition wants
a predicate constant on merged bisimilarity classes. Runtime-grown names break
the first premise outright, since the carrier of names is not a set of subterms
of the program. Whether the second survives is a separate question about the
classifier and is not settled here.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.RedexDecomposition
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Seeds
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Gate

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Deciding name equivalence -/

/-- Congruence is exactly component-bag equality. -/
theorem cong_iff_components {p q : Comb} : Cong p q ↔ components p = components q :=
  ⟨cong_components, cong_of_components⟩

/-- **Name equivalence is decidable**, by one comparison of component bags.  So
the constructors do not cost decidability; what they cost is a bound on the size
of what must be compared. -/
def decidableCong (p q : Comb) : Decidable (Cong p q) :=
  decidable_of_iff _ cong_iff_components.symm

instance : DecidableRel (fun p q : Comb => Cong p q) := decidableCong

/-! ## The doubling gadget -/

/-- `x` rejoined with itself `k` times. -/
def doubled : ℕ → Comb → Comb
  | 0, x => x
  | k + 1, x => par (doubled k x) (doubled k x)

theorem one_le_size (t : Comb) : 1 ≤ size t := by
  cases t <;> simp only [size] <;> omega

/-- The rejoined name is exponential in the number of stages. -/
theorem pow_le_size_doubled (x : Comb) : ∀ k : ℕ, 2 ^ k ≤ size (doubled k x)
  | 0 => by simpa only [doubled, pow_zero] using one_le_size x
  | k + 1 => by
      have ih := pow_le_size_doubled x k
      simp only [doubled, size, pow_succ]
      omega

/-- The name a stage listens at. -/
def inName (s : Comb) (i : ℕ) : Comb := slot s (2 * i)

/-- The name a stage duplicates through. -/
def midName (s : Comb) (i : ℕ) : Comb := slot s (2 * i + 1)

/-- **One doubling stage.**  It duplicates the message that arrives and rejoins
the two copies into a single name, which it forwards to the next stage. -/
def stage (s : Comb) (i : ℕ) : Comb :=
  par (dd (inName s i) (midName s i) (midName s i))
    (consPar (midName s i) (midName s i) (inName s (i + 1)))

/-- A stage doubles its argument in two steps. -/
theorem stage_reaches (s : Comb) (i : ℕ) (x : Comb) :
    ReachesFull (par (stage s i) (mm (inName s i) x))
      (mm (inName s (i + 1)) (par x x)) := by
  -- bring the arriving message beside the duplicator
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (stage s i) (mm (inName s i) x))
        = components (par (par (dd (inName s i) (midName s i) (midName s i))
            (mm (inName s i) x))
          (consPar (midName s i) (midName s i) (inName s (i + 1)))) from by
        simp only [components, stage]; ac_rfl))) ?_
  -- duplicate it through the middle name
  refine ReachesFull.trans (ReachesFull.ofReaches (Reaches.parLeft _
    (Reaches.single (StepMinus.duplicate (midName s i) (midName s i) x
      (Cong.refl _))))) ?_
  -- bring the two copies beside the constructor
  refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
      components (par (par (mm (midName s i) x) (mm (midName s i) x))
          (consPar (midName s i) (midName s i) (inName s (i + 1))))
        = components (par (consPar (midName s i) (midName s i) (inName s (i + 1)))
          (par (mm (midName s i) x) (mm (midName s i) x))) from by
        simp only [components]; ac_rfl))) ?_
  -- rejoin them into one name
  exact ReachesFull.single
    (Step.buildPar (inName s (i + 1)) x x (Cong.refl _) (Cong.refl _))

/-- `k` doubling stages, composed. -/
def chain (s : Comb) : ℕ → Comb
  | 0 => nil
  | k + 1 => par (chain s k) (stage s k)

/-- **`k` stages double `k` times.**  The whole chain is consumed; what remains
is one message carrying a name of exponential size. -/
theorem chain_reaches (s : Comb) (x : Comb) : ∀ k : ℕ,
    ReachesFull (par (chain s k) (mm (inName s 0) x))
      (mm (inName s k) (doubled k x))
  | 0 =>
      ReachesFull.congruent (cong_of_components (by
        simp only [components, chain, doubled]; ac_rfl))
  | k + 1 => by
      have ih := chain_reaches s x k
      refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
          components (par (chain s (k + 1)) (mm (inName s 0) x))
            = components (par (par (chain s k) (mm (inName s 0) x))
              (stage s k)) from by
            simp only [components, chain]; ac_rfl))) ?_
      refine ReachesFull.trans (ReachesFull.parLeft _ ih) ?_
      refine ReachesFull.trans (ReachesFull.congruent (cong_of_components (show
          components (par (mm (inName s k) (doubled k x)) (stage s k))
            = components (par (stage s k)
              (mm (inName s k) (doubled k x))) from by
            simp only [components]; ac_rfl))) ?_
      exact stage_reaches s k (doubled k x)

/-! ## The finding -/

/-- The atoms a soup is made of. -/
def atomCount (t : Comb) : ℕ := (componentList t).length

/-- A chain of `k` stages is `2 * k` atoms. -/
theorem atomCount_chain (s : Comb) : ∀ k : ℕ, atomCount (chain s k) = 2 * k
  | 0 => rfl
  | k + 1 => by
      have ih := atomCount_chain s k
      simp only [atomCount, chain, stage, componentList, List.length_append,
        List.length_cons, List.length_nil] at ih ⊢
      omega

/-- **Names are not bounded by the program.**  A soup of `2 * k` atoms reduces
to a message whose name has size at least `2 ^ k`.  So a cost account that
decorates a fixed term structure cannot bound the names it will be asked to
compare: the carrier of names is not a set of subterms of the program, and its
sizes are exponential in the program's atom count. -/
theorem growth_is_exponential_in_atom_count (s x : Comb) (k : ℕ) :
    atomCount (chain s k) = 2 * k ∧
      ∃ target : Comb,
        ReachesFull (par (chain s k) (mm (inName s 0) x)) target ∧
        ∃ name ∈ names target, 2 ^ k ≤ size name :=
  ⟨atomCount_chain s k,
    mm (inName s k) (doubled k x),
    chain_reaches s x k,
    doubled k x,
    by simp [names],
    pow_le_size_doubled x k⟩

/-! ## Where the work goes

Deciding name equivalence is one bag comparison (`decidableCong`).  The
comparison is therefore cheap in the number of *components* — and the number of
components of a runtime-built name is what grows.  So the work does not leave
the system when a combinator target replaces substitution: it moves out of the
binding layer and into name construction and name comparison, and its size
there is not bounded by the program.
-/

/-- A doubled name has exponentially many components. -/
theorem card_components_doubled {x : Comb} (hx : components x = {x}) :
    ∀ k : ℕ, Multiset.card (components (doubled k x)) = 2 ^ k
  | 0 => by simp only [doubled, hx, pow_zero, Multiset.card_singleton]
  | k + 1 => by
      have ih := card_components_doubled hx k
      simp only [doubled, components, Multiset.card_add, ih, pow_succ]
      omega

/-- **The comparison cost is not bounded by the program.**  From a soup of
`2 * k` atoms the calculus reaches a message whose name has `2 ^ k` components,
so deciding whether two such names are equivalent compares bags of exponential
size.  Name equivalence stays decidable; what is lost is any bound, in terms of
the program, on the size of what gets compared.

This is the negative half of the cost question, and it is derived rather than
benchmarked.  There is no combinator backend on the live tree to measure, which
is itself part of the answer: no speedup can be claimed for a target that has
not been built, and this theorem says where the work would have to go if it
were — out of the binding layer and into name construction and name equality,
at sizes the program does not bound. -/
theorem comparison_cost_unbounded (s : Comb) (k : ℕ) :
    atomCount (chain s k) = 2 * k ∧
      ∃ target : Comb,
        ReachesFull (par (chain s k) (mm (inName s 0) (kk nil))) target ∧
        ∃ name ∈ names target,
          2 ^ k ≤ size name ∧ Multiset.card (components name) = 2 ^ k :=
  ⟨atomCount_chain s k,
    mm (inName s k) (doubled k (kk nil)),
    chain_reaches s (kk nil) k,
    doubled k (kk nil),
    by simp [names],
    pow_le_size_doubled (kk nil) k,
    card_components_doubled rfl k⟩

/-- The one-step version, for the record: a constructor step produces a name
strictly larger than either of the names it was given. -/
theorem buildPar_name_grows (a b c p q : Comb) :
    Step Cong (par (consPar a b c) (par (mm a p) (mm b q))) (mm c (par p q)) ∧
      size p < size (par p q) ∧ size q < size (par p q) :=
  ⟨Step.buildPar c p q (Cong.refl a) (Cong.refl b),
    by simp only [size]; omega,
    by simp only [size]; omega⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
