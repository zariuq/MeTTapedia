/-
# Descent interface: the tower's index, de-Natted

The bootstrap tower's **descent-only laws** consume only a well-founded strict
order — never successor structure, arithmetic, or initiality.  This file
extracts that interface, proves those laws once at interface strength, and
supplies three witnesses that pin its intended use.  It does not claim that
the current successor-indexed quotation and universe constructions have
already migrated to this interface.

* **Nat carrier conservativity** — `StrictlyBelow` over `ℕ` is exactly `Fin`,
  so statements using only a host level and a strictly lower target transport
  without loss; successor-sensitive statements remain separate;
* **transfinite room** — `Ordinal` satisfies the interface, with all finite
  levels strictly below `ω`;
* **upward openness** — `NoMaxOrder` is the "no felt ceiling" condition: an
  agent climbing the tower never hits a top level, while every downward
  trust chain still terminates.

Two guard theorems close known error routes:

* `no_infinite_descent` — trust chains ground out (the point of the tower);
* `dense_pair_impossible` — a well-founded strict order admits **no** dense
  pair, so "insert an administrative level between any two levels by
  density" is a false hope.  The correct interpolation mechanism is
  lexicographic refinement (`Level ×ₗ ℕ`), which stays well-founded and
  preallocates countably many sublevel coordinates within a band — witnessed
  below.  This is refinement, not density: adjacent coordinates are still
  adjacent.

Successor-sensitive structure (adjacent quotation, recursively generated
universes) is a deliberately separate, stronger capability: add `SuccOrder`
or ordinal recursion explicitly when a theorem pays for it.  Nothing here
claims semantic self-consistency or supplies a model — longer indices give
longer stratification, not soundness.
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Max

namespace Mettapedia.GSLT.LanguageDef.DescentInterface

universe u

variable {Level : Type u} [PartialOrder Level] [WellFoundedLT Level]

/-! ## The descent laws, at interface strength -/

omit [WellFoundedLT Level] in
/-- No level trusts itself: no same-level edge. -/
theorem no_self_trust (l : Level) : ¬ l < l := lt_irrefl l

omit [WellFoundedLT Level] in
/-- No two-level certification cycle. -/
theorem no_two_cycle {l m : Level} (h : l < m) : ¬ m < l := fun h' =>
  lt_irrefl l (lt_trans h h')

omit [WellFoundedLT Level] in
/-- Composed descent is descent. -/
theorem descent_composes {l m n : Level} (h₁ : l < m) (h₂ : m < n) : l < n :=
  lt_trans h₁ h₂

/-- Trust chains ground out: there is no infinite strictly descending
sequence of levels. -/
theorem no_infinite_descent (f : ℕ → Level)
    (desc : ∀ n, f (n + 1) < f n) : False := by
  have wf : WellFounded fun a b : Level => a < b := IsWellFounded.wf
  have key : ∀ l : Level, ∀ n, f n ≠ l := fun l =>
    wf.induction (C := fun l => ∀ n, f n ≠ l) l fun x ih n hn =>
      ih (f (n + 1)) (hn ▸ desc n) (n + 1) rfl
  exact key (f 0) 0 rfl

/-! ## The generalized `Fin`: levels strictly below a host -/

/-- A strictly lower level, packaged with its descent witness — the
generalization of `Fin hostLevel` to an arbitrary descent order. -/
structure StrictlyBelow (hostLevel : Level) where
  target : Level
  below : target < hostLevel

/-- **Nat carrier conservativity**: over `ℕ`, `StrictlyBelow n` is exactly
`Fin n`.  This transports tower statements whose only index structure is a
host and a strictly lower target; it deliberately says nothing about
successor-sensitive constructions. -/
def natBelowEquivFin (n : ℕ) : StrictlyBelow (Level := ℕ) n ≃ Fin n where
  toFun s := ⟨s.target, s.below⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## Guard: density is unavailable — refine lexicographically instead -/

/-- **No dense pair.**  In a well-founded strict order, no two levels contain
interpolants all the way down: assuming every pair can be split yields an
infinite descending chain.  "Administrative levels by density" is therefore
structurally impossible — use lexicographic refinement instead. -/
theorem dense_pair_impossible
    (dense : ∀ ⦃a b : Level⦄, a < b → ∃ c, a < c ∧ c < b)
    {a b : Level} (hab : a < b) : False := by
  let f : ℕ → {x : Level // a < x} := fun n =>
    Nat.rec ⟨b, hab⟩
      (fun _ p => ⟨(dense p.2).choose, (dense p.2).choose_spec.1⟩) n
  exact no_infinite_descent (fun n => (f n).1)
    (fun n => (dense (f n).2).choose_spec.2)

/-- **A correct refinement mechanism**: lexicographic refinement keeps
well-foundedness while preallocating unboundedly many administrative
coordinates inside every band — `(l, 0) < (l, 1) < … < (l', 0)` for
`l < l'`.  It does not make the order dense or permit arbitrary later
insertion between adjacent coordinates. -/
example : WellFoundedLT (ℕ ×ₗ ℕ) := inferInstance

/-! ## Upward openness: the no-felt-ceiling condition -/

omit [WellFoundedLT Level] in
/-- With `NoMaxOrder`, every level has a strictly higher one: an agent
climbing the tower — simulating minds that model minds that model
translations — never encounters a top.  Downward, `no_infinite_descent`
still grounds every justification chain.  Upward-open, downward-grounded. -/
theorem no_felt_ceiling [NoMaxOrder Level] (l : Level) : ∃ l', l < l' :=
  exists_gt l

/-! ## Transfinite witness -/

/-- Ordinals satisfy the descent interface. -/
example : WellFoundedLT Ordinal := inferInstance

/-- Ordinals satisfy upward openness. -/
example : NoMaxOrder Ordinal := inferInstance

/-- Genuinely transfinite room for the descent-only interface: every finite
level sits strictly below `ω`.  Existing successor-sensitive tower structure
still requires an explicit migration or a stronger index capability. -/
theorem transfinite_room (n : ℕ) : (n : Ordinal) < Ordinal.omega0 :=
  Ordinal.natCast_lt_omega0 n

end Mettapedia.GSLT.LanguageDef.DescentInterface
