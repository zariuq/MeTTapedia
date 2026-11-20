import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Functional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Print

/-!
# Controls for T2: each breaks one hypothesis of the functional licence

* `Toss` (`tests/tcalc/modules/choice.module`): `toss-heads. |- c:toss(x) ~> c:heads` and
  `toss-tails. |- c:toss(x) ~> c:tails`. Range-restricted, no query, not exclusive
  (`Toss.not_exclusive`): the closure holds two values for `toss(coin)` (`Toss.two_values`). Its
  reading prints as the library's (`Toss.reading_text`).
* `Next`: the one rule `next-edge. edge(x, y) |- next(x) ~> y` with the rows `a -> b`, `a -> c`.
  Range-restricted and exclusive (one rule, `Next.exclusive`); its query binds `y`
  (`Next.not_queriesBound`): `next(a)` has the two values `b`, `c` (`Next.two_values`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open SetStoreSyntax (consequence)

namespace Toss

/-- The constructors `c:coin`, `c:heads`, `c:tails`, `c:toss`. -/
inductive Con where
  | coin | heads | tails | toss
  deriving DecidableEq

def Con.arity : Con → ℕ
  | .toss => 1
  | _ => 0

/-- The rules `toss-heads` and `toss-tails`. -/
inductive Label where
  | heads | tails
  deriving DecidableEq

/-- No relation, no constant, variables numbered. -/
abbrev σ : LPSignature.{0, 0, 0, 0} := ⟨Empty, ℕ, Empty, (fun e => nomatch e), Con, Con.arity⟩

abbrev T := Term (readingSignature σ Label)

def coin : T := .app (Head.con Con.coin) ![]
def heads : T := .app (Head.con Con.heads) ![]
def tails : T := .app (Head.con Con.tails) ![]
def toss (t : T) : T := .app (Head.con Con.toss) ![t]
def x : T := .var 0

def module : Label → ModuleRule (readingSignature σ Label)
  | .heads => ⟨toss x, [], heads⟩
  | .tails => ⟨toss x, [], tails⟩

def rows : Finset (Atom (readingSignature σ Label)) := ∅

def names : Names σ Label where
  con := fun | .coin => "c:coin" | .heads => "c:heads" | .tails => "c:tails" | .toss => "c:toss"
  rel := fun e => nomatch e
  const := fun e => nomatch e
  var := fun | 0 => "x" | n => "v" ++ toString n
  label := fun | .heads => "toss-heads" | .tails => "toss-tails"

/-- **The reading prints as the library's** `tcalc:module-text` of `choice.module`. -/
theorem reading_text : readingText names module [.heads, .tails] =
    "(rule toss-heads (read (demand (c:toss $x))) (make (value (c:toss $x) (c:heads))))\n" ++
    "(rule toss-tails (read (demand (c:toss $x))) (make (value (c:toss $x) (c:tails))))\n" := by
  decide +kernel

theorem apply_toss (θ : Subst (readingSignature σ Label)) (t : T) :
    θ.applyTerm (toss t) = toss (θ.applyTerm t) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.toss) (fun i : Fin 1 => θ.applyTerm (![t] i)) =
    Term.app (Head.con Con.toss) ![θ.applyTerm t]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by omega
  rfl

theorem apply_nullary {n : Con} (zero : Con.arity n = 0) (θ : Subst (readingSignature σ Label))
    (args : Fin (Con.arity n) → T) :
    θ.applyTerm (Term.app (σ := readingSignature σ Label) (Head.con n) args) = Term.app (Head.con n) args := by
  show Term.app (σ := readingSignature σ Label) (Head.con n) (fun i : Fin (Con.arity n) => θ.applyTerm (args i)) =
    Term.app (Head.con n) args
  congr 1
  funext i
  exact absurd i.2 (by omega)

theorem heads_ne_tails : heads ≠ tails := fun same => by
  have different := Head.con.inj (Term.app.inj same).1
  cases different

theorem freeVars_nullary {n : Con} (zero : Con.arity n = 0) (args : Fin (Con.arity n) → T) :
    (Term.app (σ := readingSignature σ Label) (Head.con n) args).freeVars = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v inside
  simp only [Term.freeVars, Finset.mem_biUnion] at inside
  obtain ⟨i, _, _⟩ := inside
  exact absurd i.2 (by change ¬ (i : ℕ) < Con.arity n; omega)

theorem rangeRestricted : ∀ l, RangeRestricted (module l) := by
  intro l
  apply (rangeRestricted_iff_boundOk (module l)).mpr
  cases l
  · show heads.freeVars ⊆ (toss x).freeVars
    rw [show heads.freeVars = ∅ from freeVars_nullary rfl _]
    exact Finset.empty_subset _
  · show tails.freeVars ⊆ (toss x).freeVars
    rw [show tails.freeVars = ∅ from freeVars_nullary rfl _]
    exact Finset.empty_subset _

theorem queriesBound : ∀ l, QueriesBound (module l) := by
  intro l pre atom post split
  cases l <;> simp [module] at split

/-- The value `w` of `toss(t)` by the rule `l`, with no premise. -/
theorem derives (l : Label) (t : T) : Derives module ↑rows (toss t) (module l).rhs := by
  have rule := Derives.rule (M := module) (Rel := ↑rows) l (fun _ => t)
    (fun _ _ inside => by cases l <;> simp [module] at inside)
    (fun _ inside => by cases l <;> simp [module] at inside)
  have lhs : Subst.applyTerm (fun _ => t) (module l).lhs = toss t := by
    cases l <;> exact apply_toss (fun _ => t) x
  have rhs : Subst.applyTerm (fun _ => t) (module l).rhs = (module l).rhs := by
    cases l <;> exact apply_nullary rfl (fun _ => t) _
  rwa [lhs, rhs] at rule

/-- Both rules hold at `toss(coin)`. -/
theorem not_exclusive : ¬ Exclusive module ↑rows := fun exclusive =>
  exclusive .heads .tails (fun _ => coin) (fun _ => coin) (by decide) rfl
    (fun _ inside => by simp [module] at inside) (fun _ inside => by simp [module] at inside)

theorem ground : (toss coin).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by change k < 1 at bound; omega
  exact fun j => absurd j.2 (by change ¬ (j : ℕ) < 0; omega)

theorem rows_ground : ∀ e ∈ rows, e.isGround := fun _ inside => absurd inside (Finset.notMem_empty _)

/-- **T2's conclusion fails without exclusivity**: the closure holds two values for `toss(coin)`. -/
theorem two_values :
    valueRow (toss coin) heads ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (toss coin) rows) ∧
      valueRow (toss coin) tails ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (toss coin) rows) ∧
      heads ≠ tails :=
  ⟨(valueRow_mem_closure_iff rangeRestricted ground rows_ground _ _).mpr ⟨.seed, derives .heads coin⟩,
    (valueRow_mem_closure_iff rangeRestricted ground rows_ground _ _).mpr ⟨.seed, derives .tails coin⟩,
    heads_ne_tails⟩

end Toss

namespace Next

/-- The constructors `a`, `b`, `c`, `next`. -/
inductive Con where
  | a | b | c | next
  deriving DecidableEq

def Con.arity : Con → ℕ
  | .next => 1
  | _ => 0

/-- The relation `edge`. -/
inductive RelSym where
  | edge
  deriving DecidableEq

def RelSym.arity : RelSym → ℕ
  | .edge => 2

/-- The one rule `next-edge`. -/
inductive Label where
  | edge
  deriving DecidableEq

abbrev σ : LPSignature.{0, 0, 0, 0} := ⟨Empty, ℕ, RelSym, RelSym.arity, Con, Con.arity⟩

abbrev T := Term (readingSignature σ Label)

def a : T := .app (Head.con Con.a) ![]
def b : T := .app (Head.con Con.b) ![]
def c : T := .app (Head.con Con.c) ![]
def next (t : T) : T := .app (Head.con Con.next) ![t]
def edge (s t : T) : Atom (readingSignature σ Label) := ⟨RelSym.edge, ![s, t]⟩
def x : T := .var 0
def y : T := .var 1

def module : Label → ModuleRule (readingSignature σ Label)
  | .edge => ⟨next x, [.query (edge x y)], y⟩

/-- The rows `a -> b`, `a -> c`. -/
def rows : Finset (Atom (readingSignature σ Label)) := {edge a b, edge a c}

theorem apply_next (θ : Subst (readingSignature σ Label)) (t : T) :
    θ.applyTerm (next t) = next (θ.applyTerm t) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.next) (fun i : Fin 1 => θ.applyTerm (![t] i)) =
    Term.app (Head.con Con.next) ![θ.applyTerm t]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by omega
  rfl

theorem applyAtom_edge (θ : Subst (readingSignature σ Label)) (s t : T) :
    θ.applyAtom (edge s t) = edge (θ.applyTerm s) (θ.applyTerm t) := by
  show (⟨RelSym.edge, fun i : Fin 2 => θ.applyTerm (![s, t] i)⟩ : Atom (readingSignature σ Label)) =
    ⟨RelSym.edge, ![θ.applyTerm s, θ.applyTerm t]⟩
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem freeVars_next (t : T) : (next t).freeVars = t.freeVars := by
  change (Finset.univ : Finset (Fin 1)).biUnion (fun i => (![t] i).freeVars) = t.freeVars
  simp

theorem freeVars_edge (s t : T) : (edge s t).freeVars = s.freeVars ∪ t.freeVars := by
  change (Finset.univ : Finset (Fin 2)).biUnion (fun i => (![s, t] i).freeVars) = s.freeVars ∪ t.freeVars
  ext v
  simp [Fin.exists_fin_two]

theorem b_ne_c : b ≠ c := fun same => by
  have different := Head.con.inj (Term.app.inj same).1
  cases different

theorem rangeRestricted : ∀ l, RangeRestricted (module l) := by
  intro l
  apply (rangeRestricted_iff_boundOk (module l)).mpr
  cases l
  simp [BoundOk, module, freeVars_next, freeVars_edge, x, y, Term.freeVars]

/-- One rule is exclusive. -/
theorem exclusive : Exclusive module ↑rows := by
  intro l₁ l₂ _ _ different
  cases l₁
  cases l₂
  exact absurd rfl different

/-- The query `edge(x, y)` binds `y`. -/
theorem not_queriesBound : ¬ QueriesBound (module .edge) := by
  intro bounded
  have inside := bounded [] (edge x y) [] rfl
  have one : (1 : ℕ) ∈ (module .edge).bound [] :=
    inside (by rw [freeVars_edge]; simp [y, Term.freeVars])
  simp [ModuleRule.bound, module, freeVars_next, x, Term.freeVars, bindsAll] at one

/-- Values for `x` and `y`. -/
def sub (p q : T) : Subst (readingSignature σ Label) := fun
  | 0 => p
  | _ => q

theorem derives_edge {t : T} (member : edge a t ∈ rows) : Derives module ↑rows (next a) t := by
  refine derives_iff.mpr ⟨.edge, sub a t, (apply_next (sub a t) x).symm, rfl, ?_⟩
  intro p inside
  simp only [module, List.mem_singleton] at inside
  subst inside
  show (sub a t).applyAtom (edge x y) ∈ (↑rows : Set (Atom (readingSignature σ Label)))
  rw [applyAtom_edge]
  exact Finset.mem_coe.mpr member

theorem ground : (next a).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by change k < 1 at bound; omega
  exact fun j => absurd j.2 (by change ¬ (j : ℕ) < 0; omega)

theorem node_ground {n : Con} (zero : Con.arity n = 0) (args : Fin (Con.arity n) → T) :
    (Term.app (σ := readingSignature σ Label) (Head.con n) args).isGround :=
  fun i => absurd i.2 (by change ¬ (i : ℕ) < Con.arity n; omega)

theorem rows_ground : ∀ e ∈ rows, e.isGround := by
  intro e inside
  simp only [rows, Finset.mem_insert, Finset.mem_singleton] at inside
  rcases inside with rfl | rfl <;>
  · intro i
    obtain ⟨k, bound⟩ := i
    rcases k with _ | _ | k
    · exact node_ground rfl _
    · exact node_ground rfl _
    · change k + 2 < 2 at bound
      omega

/-- **T2's conclusion fails when a query binds a variable**, exclusivity notwithstanding: `next(a)` has
two values in the closure. -/
theorem two_values :
    valueRow (next a) b ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (next a) rows) ∧
      valueRow (next a) c ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (next a) rows) ∧
      b ≠ c :=
  ⟨(valueRow_mem_closure_iff rangeRestricted ground rows_ground _ _).mpr
      ⟨.seed, derives_edge (by simp [rows])⟩,
    (valueRow_mem_closure_iff rangeRestricted ground rows_ground _ _).mpr
      ⟨.seed, derives_edge (by simp [rows])⟩,
    b_ne_c⟩

end Next

#print axioms Toss.reading_text
#print axioms Toss.rangeRestricted
#print axioms Toss.queriesBound
#print axioms Toss.not_exclusive
#print axioms Toss.two_values
#print axioms Next.rangeRestricted
#print axioms Next.exclusive
#print axioms Next.not_queriesBound
#print axioms Next.two_values

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
