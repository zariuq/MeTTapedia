import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Correctness

/-!
# Negative control for T0 and T1: a right side with an unbound variable

The module `tests/tcalc/modules/refused_unbound.module` of CeTTa: `next-any. |- n:next(x) ~> w`, with
`w` bound by nothing. The library refuses it ("a variable used before any read binds it").

* It is not range-restricted (`not_rangeRestricted`), and the library's check fails
  (`not_boundOk`).
* T0's negative side: its reading's one rule makes `(value (n:next $x) $w)` from
  `(demand (n:next $x))`, a made variable no read binds, so it is not `Propagates`
  (`final_not_propagates`, `not_madeScoped`).
* T1 fails without range restriction: the semantics gives `n:next(a)` every term as a value
  (`derives_any`), while the closure holds no value row at all (`no_value_rows`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Unbound

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open SetStoreSyntax (consequence varsIn Propagates)
open Mettapedia.GSLT.OpenEnded.ChaoticIteration (isLeast_target)

/-- The constructors `n:a`, `n:next`. -/
inductive Con where
  | a | next
  deriving DecidableEq

def Con.arity : Con → ℕ
  | .next => 1
  | .a => 0

/-- The one rule `next-any`. -/
inductive Label where
  | nextAny
  deriving DecidableEq

abbrev σ : LPSignature.{0, 0, 0, 0} := ⟨Empty, ℕ, Empty, (fun e => nomatch e), Con, Con.arity⟩

abbrev T := Term (readingSignature σ Label)

def a : T := .app (Head.con Con.a) ![]
def next (t : T) : T := .app (Head.con Con.next) ![t]
def x : T := .var 0
def w : T := .var 1

def module : Label → ModuleRule (readingSignature σ Label)
  | .nextAny => ⟨next x, [], w⟩

def rows : Finset (Atom (readingSignature σ Label)) := ∅

theorem freeVars_next (t : T) : (next t).freeVars = t.freeVars := by
  change (Finset.univ : Finset (Fin 1)).biUnion (fun i => (![t] i).freeVars) = t.freeVars
  simp

theorem apply_next (θ : Subst (readingSignature σ Label)) (t : T) :
    θ.applyTerm (next t) = next (θ.applyTerm t) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.next) (fun i : Fin 1 => θ.applyTerm (![t] i)) =
    Term.app (Head.con Con.next) ![θ.applyTerm t]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by omega
  rfl

/-- `w` is not bound: the right side uses a variable the left side does not. -/
theorem not_rangeRestricted : ¬ RangeRestricted (module .nextAny) := by
  intro rr
  have one : (1 : ℕ) ∈ (module .nextAny).bound (module .nextAny).premises := rr.rhs (by simp [module, w, Term.freeVars])
  simp [ModuleRule.bound, module, freeVars_next, x, Term.freeVars, bindsAll] at one

/-- The library's own check fails, which is why it refuses the module. -/
theorem not_boundOk : ¬ BoundOk (module .nextAny).lhs.freeVars (module .nextAny).premises (module .nextAny).rhs :=
  fun ok => not_rangeRestricted ((rangeRestricted_iff_boundOk (module .nextAny)).mpr ok)

/-- The reading's one rule `next-any`: read `(demand (n:next $x))`, make `(value (n:next $x) $w)`. -/
theorem readRule_eq : (readRule .nextAny (module .nextAny)).map Prod.snd =
    [makeRule [demandRow (next x)] [valueRow (next x) w]] := rfl

theorem reading_eq : reading module = {makeRule [demandRow (next x)] [valueRow (next x) w]} := by
  ext rule
  constructor
  · rintro ⟨l, inside⟩
    cases l
    rw [readRule_eq] at inside
    exact List.mem_singleton.mp inside
  · intro inside
    exact ⟨.nextAny, by rw [readRule_eq]; exact List.mem_singleton.mpr inside⟩

/-- **T0, negative**: the made variable `w` is not read. -/
theorem not_madeScoped : ¬ varsIn [valueRow (next x) w] ⊆ varsIn [demandRow (next x)] := by
  intro scopedMade
  have one : (1 : ℕ) ∈ varsIn [valueRow (next x) w] := by
    rw [varsIn_singleton (valueRow (next x) w), freeVars_valueRow (next x) w]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  have inside := scopedMade one
  rw [varsIn_singleton (demandRow (next x)), freeVars_demandRow (next x), freeVars_next] at inside
  exact absurd (Finset.mem_singleton.mp inside) (by decide)

/-- **T0, negative**: the reading's rule is not `Propagates`. -/
theorem final_not_propagates : ¬ Propagates (makeRule [demandRow (next x)] [valueRow (next x) w]) :=
  fun pure => not_madeScoped ((makeRule_propagates_iff [demandRow (next x)] [valueRow (next x) w]).mp pure)

/-- Values for `x` and `w`. -/
def sub (p q : T) : Subst (readingSignature σ Label) := fun
  | 0 => p
  | _ => q

/-- Every term is a value of `n:next(a)`. -/
theorem derives_any (t : T) : Derives module ↑rows (next a) t :=
  derives_iff.mpr ⟨.nextAny, sub a t, (apply_next (sub a t) x).symm, rfl,
    fun _ inside => by simp [module] at inside⟩

/-- No ground instance of the reading exists: its one rule is not `Propagates`. -/
theorem no_match (m : SetStoreSyntax.GroundMatch (reading module)) : False := by
  have member := (Set.ext_iff.mp reading_eq m.rule).mp m.member
  exact final_not_propagates (Set.mem_singleton_iff.mp member ▸ m.propagates)

/-- **T1 fails without range restriction**: `n:next(a)` is demanded and has every value, but the
closure holds no value row. -/
theorem no_value_rows (C t : T) :
    Demanded module ↑rows (next a) (next a) ∧ Derives module ↑rows (next a) t ∧
      valueRow C t ∉ SetStoreClosure.closure (consequence (P := reading module)) (seed (next a) rows) := by
  refine ⟨.seed, derives_any t, fun inside => ?_⟩
  have least : SetStoreClosure.closure (consequence (P := reading module)) (seed (next a) rows) ⊆
      (seed (next a) rows : Set T) :=
    (isLeast_target (fun m => SetStoreClosure.action (consequence (P := reading module) m))
      (seed (next a) rows : Set T)).2 ⟨subset_refl _, fun m => (no_match m).elim⟩
  have seeded := Finset.mem_coe.mp (least inside)
  simp only [seed, rows, Finset.image_empty, Finset.mem_insert, Finset.notMem_empty, or_false] at seeded
  exact demandRow_ne_valueRow _ _ _ seeded.symm

/-! ## Range restriction is needed for T2 too -/

/-- One rule is exclusive. -/
theorem exclusive : Exclusive module ↑rows := by
  intro l₁ l₂ _ _ different
  cases l₁
  cases l₂
  exact absurd rfl different

/-- No premise, so no query binds anything. -/
theorem queriesBound : QueriesBound (module .nextAny) := by
  intro pre atom post split
  simp [module] at split

theorem a_ne_next : a ≠ next a := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

/-- **Without range restriction `Derives` is not functional**, though the module is exclusive and has
no query: `n:next(a)` has the values `a` and `n:next(a)`. -/
theorem not_functional :
    Derives module ↑rows (next a) a ∧ Derives module ↑rows (next a) (next a) ∧ a ≠ next a :=
  ⟨derives_any a, derives_any (next a), a_ne_next⟩

#print axioms not_rangeRestricted
#print axioms not_boundOk
#print axioms readRule_eq
#print axioms reading_eq
#print axioms not_madeScoped
#print axioms final_not_propagates
#print axioms derives_any
#print axioms no_value_rows
#print axioms exclusive
#print axioms queriesBound
#print axioms not_functional

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Unbound
