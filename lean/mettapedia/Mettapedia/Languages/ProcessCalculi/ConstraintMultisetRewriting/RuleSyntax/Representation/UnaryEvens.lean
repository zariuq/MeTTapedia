import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.RootOnly
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Equivariance

/-!
# The oracle of the even numerals in unary notation is the rewriting of no finite list of range-restricted rules

`Representation.Characterization` proves four necessary conditions for a relation on bags to be the rewriting
of a finite list of rules: frame closure, bounded consumption, invariance under exchanging constants beyond
finitely many, and finitely many successors of each bag. They are not sufficient: the oracle of the even
numerals in unary notation (`PartialRecursive.eNat`) has all four and is the rewriting of no finite list of
range-restricted rules.

* `spine`: a pattern whose instance is the numeral `n` either is at least `n + 1` high
  (`Machines.RootOnly.height`), or reaches the numeral through one unknown on its spine, every other unknown
  standing for the successor's constant; then sending that unknown one successor further sends the pattern to
  the numeral `n + 1`.
* `pump_eq`: an equation between patterns at most `D` high whose instances agree, where one unknown stands for
  a numeral deeper than `D` and the others for the successor's constant, still holds when that unknown is sent
  one successor further: a deep numeral is matched only by the unknown itself (`deep_is_var`).
* `unaryEvens_not_finite`: so a finite list of range-restricted rules that rewrites the one-row bag of an even
  numeral deeper than its patterns to the answer also rewrites the next odd numeral to it.
* `unaryEvens_not_presented`: on the step, no finite range-restricted positive program presents the oracle.
* The relation has the necessary conditions: frame closed (`unaryEvens_frameClosed`), each transition consumes
  one row (its definition), finitely many successors of each bag (`unaryEvens_successors_finite`), unchanged by
  exchanging two constants beyond the three it mentions (`unaryEvens_swap`).
* Control: `zeroTwo_presented`, the oracle of the numerals `0` and `2` is the rewriting of two ground rules; the
  set must be infinite.

So no finite range-restricted positive program presents the oracle of the even constants
(`Unfolded.evens_not_presented`) or of the even unary numerals, though both sets are decidable; along runs, one
fixed finite program computes every partial recursive function (`Machines.PartialRecursive.computes_partrec`).
What one step of a finite program can do is bounded by its patterns; what it computes is a matter of runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.UnaryEvens

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
  (eNat eNat_injective)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.RootOnly (height)

/-! ## Heights and sizes of rows -/

/-- The height of a row. -/
def eHeight : Expr → ℕ
  | .sym _ => 1
  | .name _ => 1
  | .app f a => max (eHeight f) (eHeight a) + 1
  | .code e => eHeight e + 1

/-- The size of a row. -/
def eSize : Expr → ℕ
  | .sym _ => 1
  | .name _ => 1
  | .app f a => eSize f + eSize a + 1
  | .code e => eSize e + 1

theorem eHeight_eNat : ∀ i : ℕ, eHeight (eNat i) = i + 1
  | 0 => rfl
  | i + 1 => by
      show max 1 (eHeight (eNat i)) + 1 = i + 1 + 1
      rw [eHeight_eNat i]
      omega

theorem eSize_eNat : ∀ i : ℕ, eSize (eNat i) = 2 * i + 1
  | 0 => rfl
  | i + 1 => by
      show 1 + eSize (eNat i) + 1 = 2 * (i + 1) + 1
      rw [eSize_eNat i]
      omega

/-! ## Instances away from one unknown -/

/-- Instantiations that agree off `x` agree on a pattern without `x`. -/
theorem inst_off (θ θ' : ℕ → Expr) (x : ℕ) (others : ∀ v, v ≠ x → θ' v = θ v) :
    ∀ t : Tm, x ∉ unknowns t → inst θ' t = inst θ t
  | .var v, absent => others v fun same => absent (by rw [same]; exact List.mem_singleton_self _)
  | .const (.sym _), _ => rfl
  | .const (.name _), _ => rfl
  | .app .app ts, absent => by
      show Expr.app (inst θ' (ts head)) (inst θ' (ts tail)) = Expr.app (inst θ (ts head)) (inst θ (ts tail))
      rw [inst_off θ θ' x others (ts head) fun inside => absent (List.mem_append_left _ inside),
        inst_off θ θ' x others (ts tail) fun inside => absent (List.mem_append_right _ inside)]
  | .app .code ts, absent => by
      show Expr.code (inst θ' (ts body)) = Expr.code (inst θ (ts body))
      rw [inst_off θ θ' x others (ts body) absent]

/-- **Without `x`, and with every other unknown standing for a constant, a pattern's instance is at most one
higher than the pattern.** -/
theorem eHeight_inst_le (θ : ℕ → Expr) (x : ℕ) :
    ∀ t : Tm, x ∉ unknowns t → (∀ v ∈ unknowns t, v ≠ x → θ v = .sym 1) → eHeight (inst θ t) ≤ height t + 1
  | .var v, absent, shallow => by
      have other : v ≠ x := fun same => absent (by rw [same]; exact List.mem_singleton_self _)
      show eHeight (θ v) ≤ 0 + 1
      rw [shallow v (List.mem_singleton_self _) other]
      rfl
  | .const (.sym _), _, _ => by show 1 ≤ 1 + 1; omega
  | .const (.name _), _, _ => by show 1 ≤ 1 + 1; omega
  | .app .app ts, absent, shallow => by
      have left := eHeight_inst_le θ x (ts head) (fun inside => absent (List.mem_append_left _ inside))
        fun v inside => shallow v (List.mem_append_left _ inside)
      have right := eHeight_inst_le θ x (ts tail) (fun inside => absent (List.mem_append_right _ inside))
        fun v inside => shallow v (List.mem_append_right _ inside)
      show max (eHeight (inst θ (ts head))) (eHeight (inst θ (ts tail))) + 1 ≤
        max (height (ts head)) (height (ts tail)) + 1 + 1
      omega
  | .app .code ts, absent, shallow => by
      have inner := eHeight_inst_le θ x (ts body) absent shallow
      show eHeight (inst θ (ts body)) + 1 ≤ height (ts body) + 1 + 1
      omega

/-- An unknown's value is no larger than the instance of a pattern that holds it. -/
theorem eSize_le_inst (θ : ℕ → Expr) (x : ℕ) : ∀ t : Tm, x ∈ unknowns t → eSize (θ x) ≤ eSize (inst θ t)
  | .var v, inside => by
      rw [List.mem_singleton.mp inside]
      exact le_refl _
  | .const (.sym _), inside => absurd inside List.not_mem_nil
  | .const (.name _), inside => absurd inside List.not_mem_nil
  | .app .app ts, inside => by
      show eSize (θ x) ≤ eSize (inst θ (ts head)) + eSize (inst θ (ts tail)) + 1
      rcases List.mem_append.mp inside with inHead | inTail
      · have := eSize_le_inst θ x (ts head) inHead
        omega
      · have := eSize_le_inst θ x (ts tail) inTail
        omega
  | .app .code ts, inside => by
      show eSize (θ x) ≤ eSize (inst θ (ts body)) + 1
      have := eSize_le_inst θ x (ts body) inside
      omega

/-- **Strictly larger when the pattern is not the unknown itself.** -/
theorem eSize_lt_inst (θ : ℕ → Expr) (x : ℕ) :
    ∀ t : Tm, x ∈ unknowns t → t ≠ .var x → eSize (θ x) < eSize (inst θ t)
  | .var v, inside, notX => by
      rw [List.mem_singleton.mp inside] at notX
      exact absurd rfl notX
  | .const (.sym _), inside, _ => absurd inside List.not_mem_nil
  | .const (.name _), inside, _ => absurd inside List.not_mem_nil
  | .app .app ts, inside, _ => by
      show eSize (θ x) < eSize (inst θ (ts head)) + eSize (inst θ (ts tail)) + 1
      rcases List.mem_append.mp inside with inHead | inTail
      · have := eSize_le_inst θ x (ts head) inHead
        omega
      · have := eSize_le_inst θ x (ts tail) inTail
        omega
  | .app .code ts, inside, _ => by
      show eSize (θ x) < eSize (inst θ (ts body)) + 1
      have := eSize_le_inst θ x (ts body) inside
      omega

/-- **A deep numeral is matched only by the unknown that stands for it.** -/
theorem deep_is_var (θ : ℕ → Expr) (x j D : ℕ) (deep : θ x = eNat j) (big : D + 1 ≤ j) (t : Tm)
    (low : height t ≤ D) (shallow : ∀ v ∈ unknowns t, v ≠ x → θ v = .sym 1) (same : inst θ t = eNat j) :
    t = .var x := by
  by_cases inside : x ∈ unknowns t
  · by_contra notX
    have bigger := eSize_lt_inst θ x t inside notX
    rw [same, deep] at bigger
    exact lt_irrefl _ bigger
  · have lowInst := eHeight_inst_le θ x t inside shallow
    rw [same, eHeight_eNat] at lowInst
    omega

/-- A pattern that holds `x` has an instance of size at least `3` when `x` stands for a positive numeral. -/
theorem size_three (θ : ℕ → Expr) (x j : ℕ) (deep : θ x = eNat j) (positive : 1 ≤ j) (t : Tm)
    (inside : x ∈ unknowns t) : 3 ≤ eSize (inst θ t) := by
  have := eSize_le_inst θ x t inside
  rw [deep, eSize_eNat] at this
  omega

/-! ## Pumping -/

/-- **An equation that holds where one unknown stands for a deep numeral still holds one successor
further.** -/
theorem pump_eq (θ θ' : ℕ → Expr) (x j D : ℕ) (deep : θ x = eNat j) (big : D + 1 ≤ j)
    (pumped : θ' x = eNat (j + 1)) (others : ∀ v, v ≠ x → θ' v = θ v) :
    ∀ l r : Tm, height l ≤ D → height r ≤ D → (∀ v ∈ unknowns l, v ≠ x → θ v = .sym 1) →
      (∀ v ∈ unknowns r, v ≠ x → θ v = .sym 1) → inst θ l = inst θ r → inst θ' l = inst θ' r
  | .var v, r, _, lowR, shallowL, shallowR, same => by
      by_cases isX : v = x
      · rw [isX] at same ⊢
        rw [deep_is_var θ x j D deep big r lowR shallowR (same.symm.trans deep)]
      · have isOne : θ v = .sym 1 := shallowL v (List.mem_singleton_self _) isX
        have notInR : x ∉ unknowns r := fun inside => by
          have := size_three θ x j deep (by omega) r inside
          rw [← same] at this
          change 3 ≤ eSize (θ v) at this
          rw [isOne] at this
          change 3 ≤ 1 at this
          omega
        rw [inst_off θ θ' x others r notInR, ← same]
        exact others v isX
  | .const c, r, _, _, _, _, same => by
      have notInR : x ∉ unknowns r := fun inside => by
        have := size_three θ x j deep (by omega) r inside
        rw [← same] at this
        cases c <;> (change 3 ≤ 1 at this; omega)
      rw [inst_off θ θ' x others r notInR, ← same]
      cases c <;> rfl
  | .app .app ts, .var w, lowL, _, shallowL, shallowR, same => by
      by_cases isX : w = x
      · rw [isX] at same
        have := deep_is_var θ x j D deep big _ lowL shallowL (same.trans deep)
        cases this
      · have isOne : θ w = .sym 1 := shallowR w (List.mem_singleton_self _) isX
        change Expr.app _ _ = θ w at same
        rw [isOne] at same
        cases same
  | .app .app _, .const c, _, _, _, _, same => by cases c <;> cases same
  | .app .app _, .app .code _, _, _, _, _, same => by cases same
  | .app .app ts, .app .app us, lowL, lowR, shallowL, shallowR, same => by
      have parts := Expr.app.inj same
      have lowL' : max (height (ts head)) (height (ts tail)) + 1 ≤ D := lowL
      have lowR' : max (height (us head)) (height (us tail)) + 1 ≤ D := lowR
      show Expr.app (inst θ' (ts head)) (inst θ' (ts tail)) = Expr.app (inst θ' (us head)) (inst θ' (us tail))
      rw [pump_eq θ θ' x j D deep big pumped others (ts head) (us head) (by omega) (by omega)
          (fun v inside => shallowL v (List.mem_append_left _ inside))
          (fun v inside => shallowR v (List.mem_append_left _ inside)) parts.1,
        pump_eq θ θ' x j D deep big pumped others (ts tail) (us tail) (by omega) (by omega)
          (fun v inside => shallowL v (List.mem_append_right _ inside))
          (fun v inside => shallowR v (List.mem_append_right _ inside)) parts.2]
  | .app .code ts, .var w, lowL, _, shallowL, shallowR, same => by
      by_cases isX : w = x
      · rw [isX] at same
        have := deep_is_var θ x j D deep big _ lowL shallowL (same.trans deep)
        cases this
      · have isOne : θ w = .sym 1 := shallowR w (List.mem_singleton_self _) isX
        change Expr.code _ = θ w at same
        rw [isOne] at same
        cases same
  | .app .code _, .const c, _, _, _, _, same => by cases c <;> cases same
  | .app .code _, .app .app _, _, _, _, _, same => by cases same
  | .app .code ts, .app .code us, lowL, lowR, shallowL, shallowR, same => by
      have inner := Expr.code.inj same
      have lowL' : height (ts body) + 1 ≤ D := lowL
      have lowR' : height (us body) + 1 ≤ D := lowR
      show Expr.code (inst θ' (ts body)) = Expr.code (inst θ' (us body))
      rw [pump_eq θ θ' x j D deep big pumped others (ts body) (us body) (by omega) (by omega)
        shallowL shallowR inner]

/-! ## The spine of a numeral pattern -/

/-- The unknowns of a pattern whose instance is the successor's constant stand for it. -/
theorem constant_vars (θ : ℕ → Expr) : ∀ t : Tm, inst θ t = .sym 1 → ∀ v ∈ unknowns t, θ v = .sym 1
  | .var w, same, v, inside => by
      rw [List.mem_singleton.mp inside]
      exact same
  | .const (.sym _), _, _, inside => absurd inside List.not_mem_nil
  | .const (.name _), _, _, inside => absurd inside List.not_mem_nil
  | .app .app _, same, _, _ => by cases same
  | .app .code _, same, _, _ => by cases same

/-- **A pattern whose instance is the numeral `n`** either is at least `n + 1` high, or holds one unknown on its
spine that stands for a numeral, every other unknown standing for the successor's constant; sending that unknown
one successor further sends the pattern to `n + 1`. -/
theorem spine (θ : ℕ → Expr) : ∀ (n : ℕ) (p : Tm), inst θ p = eNat n →
    (∃ x ∈ unknowns p, (∃ i, θ x = eNat i ∧ n ≤ i + height p) ∧ (∀ v ∈ unknowns p, v ≠ x → θ v = .sym 1) ∧
      ∀ θ' : ℕ → Expr, θ' x = .app (.sym 1) (θ x) → (∀ v, v ≠ x → θ' v = θ v) → inst θ' p = eNat (n + 1))
    ∨ n + 1 ≤ height p
  | n, .var x, same => Or.inl ⟨x, List.mem_singleton_self _, ⟨n, same, by show n ≤ n + 0; omega⟩,
      fun v inside other => absurd (List.mem_singleton.mp inside) other,
      fun θ' pumpX _ => by
        show θ' x = Expr.app (.sym 1) (eNat n)
        rw [pumpX]
        exact congrArg (Expr.app (.sym 1)) same⟩
  | 0, .const (.sym _), _ => Or.inr (le_refl _)
  | n + 1, .const (.sym _), same => by cases same
  | 0, .const (.name _), same => by cases same
  | n + 1, .const (.name _), same => by cases same
  | 0, .app .code _, same => by cases same
  | n + 1, .app .code _, same => by cases same
  | 0, .app .app _, same => by cases same
  | n + 1, .app .app ts, same => by
      have parts := Expr.app.inj same
      have headOne : inst θ (ts head) = .sym 1 := parts.1
      have tailN : inst θ (ts tail) = eNat n := parts.2
      rcases spine θ n (ts tail) tailN with ⟨x, xIn, ⟨i, θx, bound⟩, shallow, pump⟩ | high
      · have xNotHead : x ∉ unknowns (ts head) := fun inside => by
          have isOne := constant_vars θ (ts head) headOne x inside
          rw [θx] at isOne
          cases i with
          | zero => cases isOne
          | succ i => cases isOne
        refine Or.inl ⟨x, List.mem_append_right _ xIn, ⟨i, θx, ?_⟩, fun v inside other => ?_,
          fun θ' pumpX others => ?_⟩
        · show n + 1 ≤ i + (max (height (ts head)) (height (ts tail)) + 1)
          omega
        · rcases List.mem_append.mp inside with inHead | inTail
          · exact constant_vars θ (ts head) headOne v inHead
          · exact shallow v inTail other
        · show Expr.app (inst θ' (ts head)) (inst θ' (ts tail)) = Expr.app (.sym 1) (eNat (n + 1))
          rw [inst_off θ θ' x others (ts head) xNotHead, headOne, pump θ' pumpX others]
      · exact Or.inr (show n + 1 + 1 ≤ max (height (ts head)) (height (ts tail)) + 1 by omega)

/-! ## No finite list -/

/-- The even numerals in unary notation. -/
def evenNumerals : Set Expr := {e | ∃ j, e = eNat (2 * j)}

/-- The terms of a rule: its takes, its reads, and what it tells, asks and makes. -/
def ruleTerms (r : SRule) : List Tm := r.body.take ++ r.body.read ++ written r

/-- **The height of a program**: the highest of the terms of its rules. -/
def programHeight (rules : List SRule) : ℕ :=
  (rules.map fun r => ((ruleTerms r).map height).foldr max 0).foldr max 0

theorem height_le_program {rules : List SRule} {r : SRule} (member : r ∈ rules) {t : Tm}
    (inside : t ∈ ruleTerms r) : height t ≤ programHeight rules :=
  (le_foldr_max (List.mem_map_of_mem inside)).trans
    (le_foldr_max (List.mem_map_of_mem (f := fun r : SRule => ((ruleTerms r).map height).foldr max 0) member))

/-- **The oracle of the even numerals in unary notation is the rewriting of no finite list of range-restricted
rules.** -/
theorem unaryEvens_not_finite (rules : List SRule) (restricted : ∀ r ∈ rules, RangeRestricted r) :
    ¬ ∀ M M', Rewrites rules M M' ↔ Oracle evenNumerals M M' := by
  intro same
  obtain ⟨D, isD⟩ : ∃ D, D = programHeight rules := ⟨_, rfl⟩
  have related : Oracle evenNumerals {eNat (2 * (D + 1))} {yes} :=
    ⟨_, ⟨D + 1, rfl⟩, 0, add_zero _, (add_zero _).symm⟩
  obtain ⟨r, member, θ, rest, split, readsIn, equations, made⟩ := (same _ _).mpr related
  have low : ∀ t ∈ ruleTerms r, height t ≤ D := fun t inside => isD ▸ height_le_program member inside
  match takes : r.body.take with
  | [] =>
      rw [takes] at split
      have restIs : rest = {eNat (2 * (D + 1))} := by simpa using split
      rw [restIs] at made
      have inside : eNat (2 * (D + 1)) ∈ ({yes} : Multiset Expr) := by
        rw [made]
        exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
      have isYes := Multiset.mem_singleton.mp inside
      cases D with
      | zero => cases isYes
      | succ D => cases isYes
  | [p] =>
      rw [takes] at split
      obtain ⟨matched, restZero⟩ := row_of_singleton split
      have noReads : r.body.read = [] := by
        match readList : r.body.read with
        | [] => rfl
        | q :: _ =>
            have inRest := readsIn q (by rw [readList]; exact List.mem_cons_self)
            rw [restZero] at inRest
            exact absurd inRest (Multiset.notMem_zero _)
      rw [restZero, add_zero] at made
      have counted := congrArg Multiset.card made
      rw [Multiset.card_singleton, Multiset.coe_card, List.length_map] at counted
      obtain ⟨q, isQ⟩ := List.length_eq_one_iff.mp counted.symm
      rw [isQ] at made
      have madeQ : inst θ q = yes := by simpa using made.symm
      have pLow : height p ≤ D := low p (List.mem_append_left _ (List.mem_append_left _ (by
        rw [takes]; exact List.mem_cons_self)))
      -- the unknowns a written term mentions are the taken pattern's
      have boundIn : ∀ t ∈ written r, ∀ v ∈ unknowns t, v ∈ unknowns p := by
        intro t inWritten v inside
        obtain ⟨t', inPatterns, vars⟩ := restricted r member t inWritten v (vars_of_mem_unknowns t inside)
        rw [takes, noReads, List.append_nil, List.mem_singleton] at inPatterns
        rw [inPatterns] at vars
        exact mem_unknowns p vars
      rcases spine θ _ p matched with ⟨x, -, ⟨i, θx, bound⟩, shallow, pump⟩ | high
      · have deepEnough : D + 1 ≤ i := by omega
        let θ' : ℕ → Expr := fun v => if v = x then .app (.sym 1) (θ x) else θ v
        have pumpX : θ' x = .app (.sym 1) (θ x) := if_pos rfl
        have others : ∀ v, v ≠ x → θ' v = θ v := fun v other => if_neg other
        have pumpedX : θ' x = eNat (i + 1) := by
          rw [pumpX, θx]
          rfl
        have pumpedP : inst θ' p = eNat (2 * (D + 1) + 1) := pump θ' pumpX others
        have shallowOf : ∀ t ∈ written r, ∀ v ∈ unknowns t, v ≠ x → θ v = .sym 1 :=
          fun t inWritten v inside other => shallow v (boundIn t inWritten v inside) other
        have equations' : ∀ e ∈ equationsOf r, inst θ' e.1 = inst θ' e.2 := by
          intro e inEquations
          have written' := mem_written_of_equation inEquations
          exact pump_eq θ θ' x i D θx deepEnough pumpedX others e.1 e.2
            (low e.1 (List.mem_append_right _ written'.1)) (low e.2 (List.mem_append_right _ written'.2))
            (shallowOf e.1 written'.1) (shallowOf e.2 written'.2) (equations e inEquations)
        have qWritten : q ∈ written r := mem_written_of_produce (by rw [isQ]; exact List.mem_cons_self)
        have xNotQ : x ∉ unknowns q := fun inside => by
          have size := eSize_le_inst θ x q inside
          rw [madeQ, θx, eSize_eNat] at size
          change 2 * i + 1 ≤ 1 at size
          omega
        have madeQ' : inst θ' q = yes := (inst_off θ θ' x others q xNotQ).trans madeQ
        have odd : Rewrites rules {eNat (2 * (D + 1) + 1)} {yes} := by
          refine ⟨r, member, θ', 0, ?_, fun q' inside => ?_, equations', ?_⟩
          · rw [takes]
            show (([inst θ' p] : List Expr) : Multiset Expr) + 0 = {eNat (2 * (D + 1) + 1)}
            rw [pumpedP]
            simp
          · rw [noReads] at inside
            exact absurd inside List.not_mem_nil
          · rw [isQ]
            show {yes} = (([inst θ' q] : List Expr) : Multiset Expr) + 0
            rw [madeQ']
            simp
        obtain ⟨e, ⟨j, rfl⟩, rest', split', -⟩ := (same _ _).mp odd
        have inside : eNat (2 * j) ∈ ({eNat (2 * (D + 1) + 1)} : Multiset Expr) := by
          rw [← split']
          exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))
        have equal := eNat_injective (Multiset.mem_singleton.mp inside)
        omega
      · omega
  | _ :: _ :: _ =>
      rw [takes] at split
      have counted := congrArg Multiset.card split
      simp at counted
      omega

/-- **On the step: no finite range-restricted positive program presents the oracle of the even unary
numerals.** -/
theorem unaryEvens_not_presented (rules : List SRule) (fragment : ∀ r ∈ rules, RangeRestrictedPositive r) :
    ¬ Presents ℕ {r | r ∈ rules} (Oracle evenNumerals) := fun presents =>
  unaryEvens_not_finite rules (fun r member => (fragment r member).2.2) fun M M' =>
    (rewrites_iff_set rules M M').trans
      (setRewrites_of_presents (fun r member => fragment r member) presents M M')

/-! ## The necessary conditions hold -/

/-- **Finitely many successors of each bag.** -/
theorem unaryEvens_successors_finite (M : Multiset Expr) : {M' | Oracle evenNumerals M M'}.Finite := by
  refine ((M.toFinset.image fun e => ({yes} : Multiset Expr) + M.erase e) : Set (Multiset Expr)).toFinite.subset ?_
  rintro M' ⟨e, -, rest, split, rfl⟩
  have inM : e ∈ M := by
    rw [← split]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self e))
  have restIs : rest = M.erase e := by
    rw [← split, Multiset.singleton_add, Multiset.erase_cons_head]
  rw [restIs]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, Multiset.mem_toFinset.mpr inM, rfl⟩)

theorem swap_eNat {c d : ℕ} (largeC : 2 ≤ c) (largeD : 2 ≤ d) : ∀ n : ℕ, swapRow c d (eNat n) = eNat n
  | 0 => by
      show (if 0 = c then Expr.sym d else if 0 = d then Expr.sym c else Expr.sym 0) = Expr.sym 0
      rw [if_neg (by omega), if_neg (by omega)]
  | n + 1 => by
      show Expr.app (swapRow c d (.sym 1)) (swapRow c d (eNat n)) = Expr.app (.sym 1) (eNat n)
      rw [swap_eNat largeC largeD n]
      show Expr.app (if 1 = c then Expr.sym d else if 1 = d then Expr.sym c else Expr.sym 1) (eNat n) = _
      rw [if_neg (by omega), if_neg (by omega)]

/-- **Exchanging two constants beyond the three the relation mentions leaves it unchanged.** -/
theorem unaryEvens_swap {c d : ℕ} (largeC : 2 ≤ c) (largeD : 2 ≤ d) {M M' : Multiset Expr}
    (related : Oracle evenNumerals M M') :
    Oracle evenNumerals (M.map (swapRow c d)) (M'.map (swapRow c d)) := by
  obtain ⟨e, ⟨j, rfl⟩, rest, rfl, rfl⟩ := related
  refine ⟨eNat (2 * j), ⟨j, rfl⟩, rest.map (swapRow c d), ?_, ?_⟩
  · rw [Multiset.map_add, Multiset.map_singleton, swap_eNat largeC largeD]
  · rw [Multiset.map_add, Multiset.map_singleton]
    rfl

/-- The relation is frame closed (`Representation.oracle_frameClosed`). -/
theorem unaryEvens_frameClosed : FrameClosed (Oracle evenNumerals) := oracle_frameClosed _

/-! ## Control: a finite set of numerals is the rewriting of a finite list -/

/-- **Control**: the oracle of the numerals `0` and `2` is the rewriting of two ground rules. The restriction to
an infinite set of numerals is needed. -/
theorem zeroTwo_presented (M M' : Multiset Expr) :
    Rewrites [groundRule [eNat 0] [yes], groundRule [eNat 2] [yes]] M M' ↔ Oracle {eNat 0, eNat 2} M M' := by
  constructor
  · rintro ⟨r, member, rewritten⟩
    have single : Rewrites [r] M M' := ⟨r, List.mem_singleton_self r, rewritten⟩
    rcases List.mem_cons.mp member with rfl | inRest
    · obtain ⟨rest, split, made⟩ := (rewrites_groundRule_iff _ _ M M').mp single
      exact ⟨eNat 0, Or.inl rfl, rest, split, made⟩
    · rw [List.mem_singleton.mp inRest] at single
      obtain ⟨rest, split, made⟩ := (rewrites_groundRule_iff _ _ M M').mp single
      exact ⟨eNat 2, Or.inr rfl, rest, split, made⟩
  · rintro ⟨e, inK, rest, split, made⟩
    rcases inK with rfl | isTwo
    · exact rewrites_of_mem List.mem_cons_self
        ((rewrites_groundRule_iff _ _ M M').mpr ⟨rest, split, made⟩)
    · rw [Set.mem_singleton_iff.mp isTwo] at split
      exact rewrites_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
        ((rewrites_groundRule_iff _ _ M M').mpr ⟨rest, split, made⟩)

#print axioms zeroTwo_presented
#print axioms pump_eq
#print axioms spine
#print axioms unaryEvens_not_finite
#print axioms unaryEvens_not_presented
#print axioms unaryEvens_successors_finite
#print axioms unaryEvens_swap
#print axioms unaryEvens_frameClosed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.UnaryEvens
