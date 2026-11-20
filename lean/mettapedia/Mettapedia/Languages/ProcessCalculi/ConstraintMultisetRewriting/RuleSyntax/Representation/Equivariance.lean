import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Characterization

/-!
# A finite program cannot tell apart two constants it does not mention

A rule mentions finitely many constants of rows, and so does a finite list of rules (`programBound`). Exchanging
two constants beyond them in every row (`swapRow`) commutes with instantiation of the rule's patterns
(`inst_swap`). So:

* **Invariance** (`rewrites_swap`, `rewrites_equivariant`): if a finite list of rules rewrites a bag to another,
  it rewrites the bag with two such constants exchanged to the other bag with them exchanged. This holds for
  takes, reads, tells and equation guards alike.
* **The oracle of the even constants is the rewriting of no finite list of rules**
  (`oracle_evens_not_finite`): it has a transition from an even constant beyond the rules' constants, and none
  from the next odd one (`oracle_evens_not_odd`), and the exchange of the two would carry the one to the other.

The oracle of the even constants is the rewriting of a set of positive ground rules, one for each even constant
(`oracle_presented`). The hypothesis it fails is finiteness of the program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

/-! ## Exchanging two constants -/

/-- **Exchange two constants in a row.** -/
def swapRow (c d : ℕ) : Expr → Expr
  | .sym k => if k = c then .sym d else if k = d then .sym c else .sym k
  | .app f a => .app (swapRow c d f) (swapRow c d a)
  | .name n => .name n
  | .code e => .code (swapRow c d e)

/-- A bound beyond every constant a pattern mentions. -/
def constantBound : Tm → ℕ
  | .var _ => 0
  | .const (.sym k) => k + 1
  | .const (.name _) => 0
  | .app .app ts => max (constantBound (ts head)) (constantBound (ts tail))
  | .app .code ts => constantBound (ts body)

/-- **Exchanging two constants a pattern does not mention commutes with its instantiation.** -/
theorem inst_swap {c d : ℕ} (θ : ℕ → Expr) : ∀ t : Tm, constantBound t ≤ c → constantBound t ≤ d →
    inst (fun x => swapRow c d (θ x)) t = swapRow c d (inst θ t)
  | .var _, _, _ => rfl
  | .const (.sym k), boundC, boundD => by
      have notC : k ≠ c := Nat.ne_of_lt boundC
      have notD : k ≠ d := Nat.ne_of_lt boundD
      show Expr.sym k = (if k = c then Expr.sym d else if k = d then Expr.sym c else Expr.sym k)
      rw [if_neg notC, if_neg notD]
  | .const (.name _), _, _ => rfl
  | .app .app ts, boundC, boundD => by
      show Expr.app (inst _ (ts head)) (inst _ (ts tail)) =
        Expr.app (swapRow c d (inst θ (ts head))) (swapRow c d (inst θ (ts tail)))
      rw [inst_swap θ (ts head) (le_trans (le_max_left _ _) boundC) (le_trans (le_max_left _ _) boundD),
        inst_swap θ (ts tail) (le_trans (le_max_right _ _) boundC) (le_trans (le_max_right _ _) boundD)]
  | .app .code ts, boundC, boundD => by
      show Expr.code (inst _ (ts body)) = Expr.code (swapRow c d (inst θ (ts body)))
      rw [inst_swap θ (ts body) boundC boundD]

/-! ## The constants a rule mentions -/

/-- A bound beyond the constants of a list of patterns. -/
def listBound (l : List Tm) : ℕ := (l.map constantBound).foldr max 0

theorem le_listBound {l : List Tm} {t : Tm} (member : t ∈ l) : constantBound t ≤ listBound l :=
  le_foldr_max (List.mem_map_of_mem member)

/-- A bound beyond the constants of the two sides of an equation. -/
def pairBound (e : Tm × Tm) : ℕ := max (constantBound e.1) (constantBound e.2)

/-- **A bound beyond every constant a rule mentions** in its takes, reads, made rows, tells and equation
guards. -/
def ruleBound (r : SRule) : ℕ :=
  max (listBound r.body.take) (max (listBound r.body.read)
    (max (listBound r.body.produce) (((equationsOf r).map pairBound).foldr max 0)))

theorem take_le_ruleBound {r : SRule} {t : Tm} (member : t ∈ r.body.take) : constantBound t ≤ ruleBound r :=
  (le_listBound member).trans (le_max_left _ _)

theorem read_le_ruleBound {r : SRule} {t : Tm} (member : t ∈ r.body.read) : constantBound t ≤ ruleBound r :=
  (le_listBound member).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem produce_le_ruleBound {r : SRule} {t : Tm} (member : t ∈ r.body.produce) :
    constantBound t ≤ ruleBound r :=
  (le_listBound member).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem equation_le_ruleBound {r : SRule} {e : Tm × Tm} (member : e ∈ equationsOf r) :
    constantBound e.1 ≤ ruleBound r ∧ constantBound e.2 ≤ ruleBound r := by
  have small : pairBound e ≤ ((equationsOf r).map pairBound).foldr max 0 :=
    le_foldr_max (List.mem_map_of_mem member)
  have inRule : ((equationsOf r).map pairBound).foldr max 0 ≤ ruleBound r :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨(le_max_left _ _).trans (small.trans inRule), (le_max_right _ _).trans (small.trans inRule)⟩

/-- A bound beyond every constant the rules of a list mention. -/
def programBound (rules : List SRule) : ℕ := (rules.map ruleBound).foldr max 0

/-! ## Invariance -/

/-- **A rule rewrites the exchanged bag to the exchanged bag**, for two constants it does not mention. -/
theorem rewrites_swap {r : SRule} {c d : ℕ} (boundC : ruleBound r ≤ c) (boundD : ruleBound r ≤ d)
    {M M' : Multiset Expr} (rewrites : Rewrites [r] M M') :
    Rewrites [r] (M.map (swapRow c d)) (M'.map (swapRow c d)) := by
  obtain ⟨r', inside, θ, rest, split, readsIn, equations, made⟩ := rewrites
  have isRule : r = r' := (List.mem_singleton.mp inside).symm
  subst isRule
  have takesEq : r.body.take.map (inst fun x => swapRow c d (θ x)) =
      (r.body.take.map (inst θ)).map (swapRow c d) := by
    rw [List.map_map]
    exact List.map_congr_left fun t member =>
      inst_swap θ t ((take_le_ruleBound member).trans boundC) ((take_le_ruleBound member).trans boundD)
  have makesEq : r.body.produce.map (inst fun x => swapRow c d (θ x)) =
      (r.body.produce.map (inst θ)).map (swapRow c d) := by
    rw [List.map_map]
    exact List.map_congr_left fun t member =>
      inst_swap θ t ((produce_le_ruleBound member).trans boundC) ((produce_le_ruleBound member).trans boundD)
  refine ⟨r, List.mem_singleton_self r, fun x => swapRow c d (θ x), rest.map (swapRow c d), ?_, ?_, ?_, ?_⟩
  · rw [takesEq, ← Multiset.map_coe, ← Multiset.map_add, split]
  · intro q member
    rw [inst_swap θ q ((read_le_ruleBound member).trans boundC) ((read_le_ruleBound member).trans boundD)]
    exact Multiset.mem_map_of_mem _ (readsIn q member)
  · intro e member
    rw [inst_swap θ e.1 ((equation_le_ruleBound member).1.trans boundC)
        ((equation_le_ruleBound member).1.trans boundD),
      inst_swap θ e.2 ((equation_le_ruleBound member).2.trans boundC)
        ((equation_le_ruleBound member).2.trans boundD),
      equations e member]
  · rw [makesEq, made, Multiset.map_add, Multiset.map_coe]

/-- **The rewriting of a finite list of rules is unchanged by exchanging two constants beyond those the rules
mention.** -/
theorem rewrites_equivariant (rules : List SRule) {c d : ℕ} (largeC : programBound rules ≤ c)
    (largeD : programBound rules ≤ d) {M M' : Multiset Expr} (rewrites : Rewrites rules M M') :
    Rewrites rules (M.map (swapRow c d)) (M'.map (swapRow c d)) := by
  obtain ⟨r, member, rewritten⟩ := rewrites
  have small : ruleBound r ≤ programBound rules := le_foldr_max (List.mem_map_of_mem member)
  exact rewrites_of_mem member
    (rewrites_swap (small.trans largeC) (small.trans largeD) ⟨r, List.mem_singleton_self r, rewritten⟩)

/-! ## The oracle of the even constants -/

/-- The rows that are even constants. -/
def evens : Set Expr := {e | ∃ j : ℕ, e = .sym (2 * j)}

/-- The oracle of the even constants has no transition from an odd constant. -/
theorem oracle_evens_not_odd (c : ℕ) (bag' : Multiset Expr) :
    ¬ Oracle evens {.sym (2 * c + 1)} bag' := by
  rintro ⟨e, ⟨j, rfl⟩, rest, split, -⟩
  have inside : Expr.sym (2 * j) ∈ ({.sym (2 * c + 1)} : Multiset Expr) := by
    rw [← split]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))
  have equal : 2 * j = 2 * c + 1 := Expr.sym.inj (Multiset.mem_singleton.mp inside)
  omega

/-- **No finite list of rules rewrites as the oracle of the even constants.** -/
theorem oracle_evens_not_finite (rules : List SRule) :
    ¬ ∀ M M', Rewrites rules M M' ↔ Oracle evens M M' := by
  intro same
  have related : Oracle evens {.sym (2 * (programBound rules + 1))} {yes} :=
    ⟨.sym (2 * (programBound rules + 1)), ⟨programBound rules + 1, rfl⟩, 0, add_zero _, (add_zero _).symm⟩
  have swapped := rewrites_equivariant rules (c := 2 * (programBound rules + 1))
    (d := 2 * (programBound rules + 1) + 1) (by omega) (by omega) ((same _ _).mpr related)
  rw [Multiset.map_singleton, Multiset.map_singleton] at swapped
  have moved : swapRow (2 * (programBound rules + 1)) (2 * (programBound rules + 1) + 1)
      (.sym (2 * (programBound rules + 1))) = .sym (2 * (programBound rules + 1) + 1) := if_pos rfl
  rw [moved] at swapped
  have atOdd : Rewrites rules {.sym (2 * (programBound rules + 1) + 1)} {yes} := swapped
  exact oracle_evens_not_odd _ _ ((same _ _).mp atOdd)

#print axioms inst_swap
#print axioms rewrites_swap
#print axioms rewrites_equivariant
#print axioms oracle_evens_not_odd
#print axioms oracle_evens_not_finite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation
