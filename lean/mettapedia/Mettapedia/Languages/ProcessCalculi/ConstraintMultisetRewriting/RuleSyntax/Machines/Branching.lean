import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Interpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Hosting

/-!
# Finitely many successors, computed: the computation is silent and one firing chooses

A code `c` of Mathlib's `Turing.ToPartrec` computes, from `[n]`, the list of the successors of `n`: the system
`Choose c` steps from `n` to every member of the list `c` evaluates `[n]` to. Its branching is finite and
computed.

## The program (`branchRules c`)

The nineteen schemas of the machine, and six rules over new rows (`candRow`, `spreadRow`, `pickRow`,
`cleanRow`), each telling its rows apart from the machine's by the constant at the left end of the row
(`spineHead`):

* `startSpread` takes the halted row with output `l` and makes the spreading row of `l` with count `0`;
* `spreadCons` takes the spreading row of `x :: rest` with count `j`, makes the spreading row of `rest` with
  count `j + 1` and the candidate row of `x`;
* `spreadEnd` takes the spreading row of the empty list with count `j + 1` and makes the choosing row `j`;
* `choose` takes the choosing row `j` and one candidate row `x`, and makes the cleaning row `j, x`;
* `cleanStep` takes the cleaning row `j + 1, x` and one candidate row, and makes the cleaning row `j, x`;
* `restartAt c` takes the cleaning row `0, x` and makes the pending evaluation of `c` on `[x]`.

Every rule only takes rows and makes rows (`multiRule`, `rowRule`: no read, tell or check), and the program is
range-restricted and positive (`branch_fragment`). The leftover candidates are removed by counting them, so no
none check is needed.

## The correspondence

* The bags of a number with the number of silent firings left before the choice (`PhaseIn`): computing,
  spreading, choosing, cleaning. Every firing at such a bag either lowers the count by exactly one and stays
  with the number (silent) or is `choose`, a step of the system to the chosen candidate, landing on a cleaning
  bag that shows it (`phase_step`). Choosing bags have count zero (`pick_count`).
* **The weak correspondence** (`bagWeak`, at the level of bags; `stepWeak`, on the one-match step through
  `liftWeak`): when the code has a value at every number. The potential is the least count (`potentialOf`). So:
  an `OperationalCorrespondence` (`stepCorrespondence`), silent firings that end, no added divergence
  (`Hosting.WeakCorrespondence.infinite_run_reflected`), divergence preserved (`infinite_run_preserved`).
* **Where the list has no value, no weak correspondence exists** (`no_weak_of_none` for rewriting of bags,
  `no_weak_of_none_step` on the one-match step): the program runs for ever from the number's pending evaluation
  (`branch_runs_forever`), while the number has no successor; a weak correspondence adds no divergence.

## Cost

From the pending evaluation of `n`, whose computation takes `r` reductions to the halted configuration with
output `l`, the count is `r + l.length + 2` (`start_count`); every firing at a counted bag with a positive count
lowers it by exactly one and stays with the number, and a firing at count zero is a choice (`phase_step`); count
zero is only reached at choosing bags (`pick_count`). So when `l` is not empty, every run from the pending
evaluation makes exactly `r + l.length + 2` silent firings before its choice: `r` reductions of the machine, one
firing to start spreading, `l.length` firings spreading and one ending the spreading; the choice is one firing;
then `l.length - 1` firings clean and one restarts. Numbers are unary rows.

## Instances

* `twoCode` computes `[n + 1, n + 2]` from `[n]` and has a value everywhere (`twoCode_choose`,
  `twoCode_total`): a weak correspondence with two successors at each number (`twoCode_weak`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Branching

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic
open PartialRecursive
open Representation.Hosting (WeakCorrespondence SilentStep)

/-! ## Rows by the constant at their left end -/

/-- **The spine head of a row**: the constant at the left end of its applications. -/
def spineHead : Expr → Option ℕ
  | .sym k => some k
  | .app f _ => spineHead f
  | .name _ => none
  | .code _ => none

/-- A candidate row. -/
def candRow (x : ℕ) : Expr := .app (.sym 19) (eNat x)

/-- A spreading row: the rest of the list, and how many candidates are spread. -/
def spreadRow (rest : List ℕ) (j : ℕ) : Expr := .app (.app (.sym 20) (eNats rest)) (eNat j)

/-- A choosing row: one less than the number of candidates. -/
def pickRow (j : ℕ) : Expr := .app (.sym 21) (eNat j)

/-- A cleaning row: how many candidates are left, and the chosen one. -/
def cleanRow (j x : ℕ) : Expr := .app (.app (.sym 22) (eNat j)) (eNat x)

/-- The candidate rows of a bag of numbers. -/
def candBag (C : Multiset ℕ) : Multiset Expr := C.map candRow

/-- A spreading bag. -/
def spreadBag (rest : List ℕ) (j : ℕ) (C : Multiset ℕ) : Multiset Expr := spreadRow rest j ::ₘ candBag C

/-- A choosing bag. -/
def pickBag (j : ℕ) (C : Multiset ℕ) : Multiset Expr := pickRow j ::ₘ candBag C

/-- A cleaning bag. -/
def cleanBag (j x : ℕ) (C : Multiset ℕ) : Multiset Expr := cleanRow j x ::ₘ candBag C

theorem head_of_mem_candBag {a : Expr} {C : Multiset ℕ} (member : a ∈ candBag C) : spineHead a = some 19 := by
  obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp member
  rfl

theorem candBag_zero : candBag 0 = 0 := Multiset.map_zero _

theorem candBag_cons (x : ℕ) (C : Multiset ℕ) : candBag (x ::ₘ C) = candRow x ::ₘ candBag C :=
  Multiset.map_cons _ _ _

theorem candBag_cons_erase {y : ℕ} {C : Multiset ℕ} (member : y ∈ C) :
    candBag C = candRow y ::ₘ candBag (C.erase y) := by
  rw [candBag, candBag, ← Multiset.map_cons, Multiset.cons_erase member]

/-- A row of a bag with one distinguished row and candidates, which is not a candidate, is the distinguished
row. -/
theorem eq_of_mem_cons_head {a e : Expr} {C : Multiset ℕ} (member : a ∈ e ::ₘ candBag C)
    (notCand : spineHead a ≠ some 19) : a = e := by
  rcases Multiset.mem_cons.mp member with same | inCands
  · exact same
  · exact absurd (head_of_mem_candBag inCands) notCand

/-- **One take**: a rule that takes one row which is not a candidate takes the distinguished row. -/
theorem take_one {a e : Expr} {rest : Multiset Expr} {C : Multiset ℕ} (split : a ::ₘ rest = e ::ₘ candBag C)
    (notCand : spineHead a ≠ some 19) : a = e ∧ rest = candBag C := by
  have same : a = e := eq_of_mem_cons_head (split ▸ Multiset.mem_cons_self a rest) notCand
  subst same
  exact ⟨rfl, (Multiset.cons_inj_right a).mp split⟩

/-- **Two takes**: a rule that takes a row which is not a candidate and a second row takes the distinguished
row and one candidate. -/
theorem take_two {a b e : Expr} {rest : Multiset Expr} {C : Multiset ℕ}
    (split : a ::ₘ b ::ₘ rest = e ::ₘ candBag C) (notCand : spineHead a ≠ some 19) :
    a = e ∧ ∃ y ∈ C, b = candRow y ∧ rest = candBag (C.erase y) := by
  obtain ⟨same, restSplit⟩ := take_one split notCand
  refine ⟨same, ?_⟩
  have inCands : b ∈ candBag C := restSplit ▸ Multiset.mem_cons_self b rest
  obtain ⟨y, member, rfl⟩ := Multiset.mem_map.mp inCands
  refine ⟨y, member, rfl, ?_⟩
  rw [candBag_cons_erase member] at restSplit
  exact (Multiset.cons_inj_right _).mp restSplit

/-! ## Rules with several takes and makes -/

/-- **A rule that takes the rows of the first list and makes the rows of the second.** -/
def multiRule (takes makes : List Tm) : SRule := ⟨PUnit.unit, ⟨takes, [], [], [], makes⟩, []⟩

/-- A rule whose made rows have only unknowns of its taken rows is range-restricted and positive. -/
theorem multiRule_fragment {takes makes : List Tm}
    (range : ∀ m ∈ makes, ∀ x ∈ unknowns m, ∃ t ∈ takes, x ∈ unknowns t) :
    RangeRestrictedPositive (multiRule takes makes) := by
  refine ⟨rfl, rfl, fun t inWritten x vars => ?_⟩
  have isMade : t ∈ makes := by simpa [written, multiRule] using inWritten
  obtain ⟨t', inTakes, inside⟩ := range t isMade x (mem_unknowns t vars)
  exact ⟨t', List.mem_append_left _ inTakes, vars_of_mem_unknowns t' inside⟩

theorem rewrites_multiRule_iff (takes makes : List Tm) (M M' : Multiset Expr) :
    Rewrites [multiRule takes makes] M M' ↔ ∃ (θ : ℕ → Expr) (rest : Multiset Expr),
      ((takes.map (inst θ) : List Expr) : Multiset Expr) + rest = M ∧
        M' = ((makes.map (inst θ) : List Expr) : Multiset Expr) + rest := by
  constructor
  · rintro ⟨r, member, θ, rest, split, -, -, made⟩
    obtain rfl := List.mem_singleton.mp member
    exact ⟨θ, rest, split, made⟩
  · rintro ⟨θ, rest, split, made⟩
    exact ⟨_, List.mem_singleton_self _, θ, rest, split, fun q member => absurd member List.not_mem_nil,
      fun e member => absurd member List.not_mem_nil, made⟩

theorem coe_one_add (a : Expr) (rest : Multiset Expr) :
    (([a] : List Expr) : Multiset Expr) + rest = a ::ₘ rest := by
  rw [← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_add, zero_add]

theorem coe_two_add (a b : Expr) (rest : Multiset Expr) :
    (([a, b] : List Expr) : Multiset Expr) + rest = a ::ₘ b ::ₘ rest := by
  rw [← Multiset.cons_coe, Multiset.cons_add, coe_one_add]

/-- One take, one make. -/
theorem rewrites_one_one {t m : Tm} {M M' : Multiset Expr} (rewrites : Rewrites [multiRule [t] [m]] M M') :
    ∃ (θ : ℕ → Expr) (rest : Multiset Expr), inst θ t ::ₘ rest = M ∧ M' = inst θ m ::ₘ rest := by
  obtain ⟨θ, rest, split, made⟩ := (rewrites_multiRule_iff _ _ M M').mp rewrites
  refine ⟨θ, rest, ?_, ?_⟩
  · rw [← coe_one_add]
    exact split
  · rw [← coe_one_add]
    exact made

/-- Two takes, one make. -/
theorem rewrites_two_one {t₁ t₂ m : Tm} {M M' : Multiset Expr}
    (rewrites : Rewrites [multiRule [t₁, t₂] [m]] M M') :
    ∃ (θ : ℕ → Expr) (rest : Multiset Expr), inst θ t₁ ::ₘ inst θ t₂ ::ₘ rest = M ∧ M' = inst θ m ::ₘ rest := by
  obtain ⟨θ, rest, split, made⟩ := (rewrites_multiRule_iff _ _ M M').mp rewrites
  refine ⟨θ, rest, ?_, ?_⟩
  · rw [← coe_two_add]
    exact split
  · rw [← coe_one_add]
    exact made

/-- One take, two makes. -/
theorem rewrites_one_two {t m₁ m₂ : Tm} {M M' : Multiset Expr}
    (rewrites : Rewrites [multiRule [t] [m₁, m₂]] M M') :
    ∃ (θ : ℕ → Expr) (rest : Multiset Expr), inst θ t ::ₘ rest = M ∧ M' = inst θ m₁ ::ₘ inst θ m₂ ::ₘ rest := by
  obtain ⟨θ, rest, split, made⟩ := (rewrites_multiRule_iff _ _ M M').mp rewrites
  refine ⟨θ, rest, ?_, ?_⟩
  · rw [← coe_one_add]
    exact split
  · rw [← coe_two_add]
    exact made

/-- Building a rewrite by a rule with one take and one make. -/
theorem rewrites_one_one_mk {t m : Tm} {M M' : Multiset Expr} (θ : ℕ → Expr) (rest : Multiset Expr)
    (split : inst θ t ::ₘ rest = M) (made : M' = inst θ m ::ₘ rest) : Rewrites [multiRule [t] [m]] M M' :=
  (rewrites_multiRule_iff _ _ M M').mpr
    ⟨θ, rest, (coe_one_add _ _).trans split, made.trans (coe_one_add _ _).symm⟩

/-- Building a rewrite by a rule with two takes and one make. -/
theorem rewrites_two_one_mk {t₁ t₂ m : Tm} {M M' : Multiset Expr} (θ : ℕ → Expr) (rest : Multiset Expr)
    (split : inst θ t₁ ::ₘ inst θ t₂ ::ₘ rest = M) (made : M' = inst θ m ::ₘ rest) :
    Rewrites [multiRule [t₁, t₂] [m]] M M' :=
  (rewrites_multiRule_iff _ _ M M').mpr
    ⟨θ, rest, (coe_two_add _ _ _).trans split, made.trans (coe_one_add _ _).symm⟩

/-- Building a rewrite by a rule with one take and two makes. -/
theorem rewrites_one_two_mk {t m₁ m₂ : Tm} {M M' : Multiset Expr} (θ : ℕ → Expr) (rest : Multiset Expr)
    (split : inst θ t ::ₘ rest = M) (made : M' = inst θ m₁ ::ₘ inst θ m₂ ::ₘ rest) :
    Rewrites [multiRule [t] [m₁, m₂]] M M' :=
  (rewrites_multiRule_iff _ _ M M').mpr
    ⟨θ, rest, (coe_one_add _ _).trans split, made.trans (coe_two_add _ _ _).symm⟩

/-! ## The program -/

/-- A candidate, as a pattern. -/
def candP (x : Tm) : Tm := ap (con 19) x

/-- A spreading row, as a pattern. -/
def spreadP (rest j : Tm) : Tm := ap (ap (con 20) rest) j

/-- A choosing row, as a pattern. -/
def pickP (j : Tm) : Tm := ap (con 21) j

/-- A cleaning row, as a pattern. -/
def cleanP (j x : Tm) : Tm := ap (ap (con 22) j) x

/-- A successor numeral, as a pattern. -/
def sucP (x : Tm) : Tm := ap (con 1) x

/-- Take the halted row with output `l`, make the spreading row of `l` with count `0`. -/
def startSpread : SRule := multiRule [ap (con 16) (unk 0)] [spreadP (unk 0) (con 0)]

/-- Take the spreading row of `x :: rest`, make the spreading row of `rest` and the candidate `x`. -/
def spreadCons : SRule :=
  multiRule [spreadP (consP (unk 0) (unk 1)) (unk 2)] [spreadP (unk 1) (sucP (unk 2)), candP (unk 0)]

/-- Take the spreading row of the empty list with count `j + 1`, make the choosing row `j`. -/
def spreadEnd : SRule := multiRule [spreadP (con 2) (sucP (unk 0))] [pickP (unk 0)]

/-- Take the choosing row `j` and a candidate `x`, make the cleaning row `j, x`. -/
def choose : SRule := multiRule [pickP (unk 0), candP (unk 1)] [cleanP (unk 0) (unk 1)]

/-- Take the cleaning row `j + 1, x` and a candidate, make the cleaning row `j, x`. -/
def cleanStep : SRule := multiRule [cleanP (sucP (unk 0)) (unk 1), candP (unk 2)] [cleanP (unk 0) (unk 1)]

/-- Take the cleaning row `0, x`, make the pending evaluation of the code on `[x]`. -/
def restartAt (c : Code) : SRule :=
  multiRule [cleanP (con 0) (unk 0)] [normalP (toTerm (eCode c)) (con 11) (consP (unk 0) (con 2))]

/-- The six rules over the new rows. -/
def controlRules (c : Code) : List SRule := [startSpread, spreadCons, spreadEnd, choose, cleanStep, restartAt c]

/-- **The program**: the machine's schemas and the six rules. -/
def branchRules (c : Code) : List SRule := rootRules schemas ++ controlRules c

theorem schemas_closed : ∀ p ∈ schemas, ∀ x ∈ unknowns p.2, x ∈ unknowns p.1 := by
  intro p member x inside
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
  exact range n x inside

theorem restartAt_fragment (c : Code) : RangeRestrictedPositive (restartAt c) := by
  refine multiRule_fragment fun m member x inside => ?_
  rw [List.mem_singleton.mp member] at inside
  have unfolded : x ∈ ((([] ++ unknowns (toTerm (eCode c))) ++ []) ++ (([] ++ [0]) ++ [])) := inside
  rw [unknowns_toTerm] at unfolded
  have isZero : x = 0 := by simpa using unfolded
  subst isZero
  exact ⟨cleanP (con 0) (unk 0), List.mem_singleton_self _, by decide⟩

/-- **Every rule of the program is range-restricted and positive.** -/
theorem branch_fragment (c : Code) : ∀ r ∈ branchRules c, RangeRestrictedPositive r := by
  intro r member
  rcases List.mem_append.mp member with machine | control
  · exact rootRules_fragment schemas_closed r machine
  · simp only [controlRules, List.mem_cons, List.not_mem_nil, or_false] at control
    rcases control with rfl | rfl | rfl | rfl | rfl | rfl
    · exact multiRule_fragment (by decide)
    · exact multiRule_fragment (by decide)
    · exact multiRule_fragment (by decide)
    · exact multiRule_fragment (by decide)
    · exact multiRule_fragment (by decide)
    · exact restartAt_fragment c

/-! ## Which rule rewrites -/

/-- **A rewrite by the program** is a root rewrite of one row by the machine's schemas, or a rewrite by one of
the six rules. -/
theorem rewrites_branch_cases {c : Code} {M M' : Multiset Expr} (rewrites : Rewrites (branchRules c) M M') :
    (∃ e rest e', e ::ₘ rest = M ∧ RootStep schemas e e' ∧ M' = e' ::ₘ rest) ∨
      Rewrites [startSpread] M M' ∨ Rewrites [spreadCons] M M' ∨ Rewrites [spreadEnd] M M' ∨
      Rewrites [choose] M M' ∨ Rewrites [cleanStep] M M' ∨ Rewrites [restartAt c] M M' := by
  obtain ⟨r, member, θ, rest, split, readsIn, equations, made⟩ := rewrites
  rcases List.mem_append.mp member with machine | control
  · left
    obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp machine
    refine ⟨inst θ pair.1, rest, inst θ pair.2, ?_, ⟨pair, inside, θ, rfl, rfl⟩, ?_⟩
    · rw [← coe_one_add]
      exact split
    · rw [← coe_one_add]
      exact made
  · right
    have single : ∀ r', r = r' → Rewrites [r'] M M' := by
      rintro r' rfl
      exact ⟨r, List.mem_singleton_self r, θ, rest, split, readsIn, equations, made⟩
    simp only [controlRules, List.mem_cons, List.not_mem_nil, or_false] at control
    rcases control with same | same | same | same | same | same
    · exact Or.inl (single _ same)
    · exact Or.inr (Or.inl (single _ same))
    · exact Or.inr (Or.inr (Or.inl (single _ same)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (single _ same))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (single _ same)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (single _ same)))))

/-- A root rewrite by the machine's schemas takes a row whose spine head is `18` or `17`. -/
theorem rootStep_head {e e' : Expr} (rooted : RootStep schemas e e') :
    spineHead e = some 18 ∨ spineHead e = some 17 := by
  obtain ⟨pair, member, θ, rfl, -⟩ := rooted
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp member
  cases n <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- The row of a point has spine head `18`, `17` or `16`. -/
theorem row_head (p : Point) : spineHead p.row = some 18 ∨ spineHead p.row = some 17 ∨ spineHead p.row = some 16 := by
  cases p with
  | normal c k v => exact Or.inl rfl
  | config cfg =>
      cases cfg with
      | ret k v => exact Or.inr (Or.inl rfl)
      | halt v => exact Or.inr (Or.inr rfl)

/-! ## The rewrites at each kind of bag -/

/-- **At the one-row bag of a point**: the point's advance, or the start of the spreading of a halted
output. -/
theorem rewrites_point {c : Code} {p : Point} {M' : Multiset Expr}
    (rewrites : Rewrites (branchRules c) {p.row} M') :
    (∃ p', Advances p p' ∧ M' = {p'.row}) ∨ (∃ l, p = .config (.halt l) ∧ M' = spreadBag l 0 0) := by
  have bag : ({p.row} : Multiset Expr) = p.row ::ₘ candBag 0 := by rw [candBag_zero]; rfl
  rw [bag] at rewrites
  rcases rewrites_branch_cases rewrites with ⟨e, rest, e', split, rooted, rfl⟩ | single | single | single |
    single | single | single
  · obtain ⟨rfl, rfl⟩ := take_one split (by rcases rootStep_head rooted with h | h <;> rw [h] <;> decide)
    obtain ⟨p', advanced, rfl⟩ := (rootStep_schemas_iff p e').mp rooted
    exact Or.inl ⟨p', advanced, by rw [candBag_zero]; rfl⟩
  · obtain ⟨θ, rest, split, rfl⟩ := rewrites_one_one single
    obtain ⟨same, rfl⟩ := take_one split (by intro h; cases h)
    cases p with
    | normal c' k v => cases (Expr.app.inj same).1
    | config cfg =>
        cases cfg with
        | ret k v => cases (Expr.app.inj same).1
        | halt l =>
            have isList : θ 0 = eNats l := (Expr.app.inj same).2
            refine Or.inr ⟨l, rfl, ?_⟩
            show Expr.app (Expr.app (Expr.sym 20) (θ 0)) (Expr.sym 0) ::ₘ candBag 0 = spreadBag l 0 0
            rw [isList]
            rfl
  · obtain ⟨θ, rest, split, -⟩ := rewrites_one_two single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    rcases row_head p with h | h | h <;> rw [← same] at h <;> cases h
  · obtain ⟨θ, rest, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    rcases row_head p with h | h | h <;> rw [← same] at h <;> cases h
  · obtain ⟨θ, rest, split, -⟩ := rewrites_two_one single
    obtain ⟨-, y, member, -⟩ := take_two split (by intro h; cases h)
    exact absurd member (Multiset.notMem_zero y)
  · obtain ⟨θ, rest, split, -⟩ := rewrites_two_one single
    obtain ⟨-, y, member, -⟩ := take_two split (by intro h; cases h)
    exact absurd member (Multiset.notMem_zero y)
  · obtain ⟨θ, rest, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    rcases row_head p with h | h | h <;> rw [← same] at h <;> cases h

/-- **At a spreading bag**: one more candidate, or the end of the spreading. -/
theorem rewrites_spread {c : Code} {rest : List ℕ} {j : ℕ} {C : Multiset ℕ} {M' : Multiset Expr}
    (rewrites : Rewrites (branchRules c) (spreadBag rest j C) M') :
    (∃ x rest', rest = x :: rest' ∧ M' = spreadBag rest' (j + 1) (x ::ₘ C)) ∨
      (rest = [] ∧ ∃ j', j = j' + 1 ∧ M' = pickBag j' C) := by
  rcases rewrites_branch_cases rewrites with ⟨e, rest₀, e', split, rooted, -⟩ | single | single | single |
    single | single | single
  · obtain ⟨same, -⟩ := take_one split (by rcases rootStep_head rooted with h | h <;> rw [h] <;> decide)
    rcases rootStep_head rooted with h | h <;> rw [same] at h <;> cases h
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, rfl⟩ := rewrites_one_two single
    obtain ⟨same, rfl⟩ := take_one split (by intro h; cases h)
    have parts := Expr.app.inj same
    have listPart : Expr.app (Expr.app (Expr.sym 3) (θ 0)) (θ 1) = eNats rest := (Expr.app.inj parts.1).2
    have countPart : θ 2 = eNat j := parts.2
    cases rest with
    | nil => cases listPart
    | cons x rest' =>
        have pieces := Expr.app.inj listPart
        have head : θ 0 = eNat x := (Expr.app.inj pieces.1).2
        have tail : θ 1 = eNats rest' := pieces.2
        refine Or.inl ⟨x, rest', rfl, ?_⟩
        show Expr.app (Expr.app (Expr.sym 20) (θ 1)) (Expr.app (Expr.sym 1) (θ 2)) ::ₘ
            Expr.app (Expr.sym 19) (θ 0) ::ₘ candBag C = spreadBag rest' (j + 1) (x ::ₘ C)
        rw [head, tail, countPart, spreadBag, candBag_cons]
        rfl
  · obtain ⟨θ, rest₀, split, rfl⟩ := rewrites_one_one single
    obtain ⟨same, rfl⟩ := take_one split (by intro h; cases h)
    have parts := Expr.app.inj same
    have listPart : Expr.sym 2 = eNats rest := (Expr.app.inj parts.1).2
    have countPart : Expr.app (Expr.sym 1) (θ 0) = eNat j := parts.2
    cases rest with
    | cons x rest' => cases listPart
    | nil =>
        cases j with
        | zero => cases countPart
        | succ j' =>
            have previous : θ 0 = eNat j' := (Expr.app.inj countPart).2
            refine Or.inr ⟨rfl, j', rfl, ?_⟩
            show Expr.app (Expr.sym 21) (θ 0) ::ₘ candBag C = pickBag j' C
            rw [previous]
            rfl
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_two_one single
    obtain ⟨same, -⟩ := take_two split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_two_one single
    obtain ⟨same, -⟩ := take_two split (by intro h; cases h)
    cases (Expr.app.inj (Expr.app.inj same).1).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj (Expr.app.inj same).1).1

/-- **At a choosing bag**: the choice of one candidate. -/
theorem rewrites_pick {c : Code} {j : ℕ} {C : Multiset ℕ} {M' : Multiset Expr}
    (rewrites : Rewrites (branchRules c) (pickBag j C) M') :
    ∃ x ∈ C, M' = cleanBag j x (C.erase x) := by
  rcases rewrites_branch_cases rewrites with ⟨e, rest₀, e', split, rooted, -⟩ | single | single | single |
    single | single | single
  · obtain ⟨same, -⟩ := take_one split (by rcases rootStep_head rooted with h | h <;> rw [h] <;> decide)
    rcases rootStep_head rooted with h | h <;> rw [same] at h <;> cases h
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_two single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, rfl⟩ := rewrites_two_one single
    obtain ⟨same, x, member, isCand, rfl⟩ := take_two split (by intro h; cases h)
    have count : θ 0 = eNat j := (Expr.app.inj same).2
    have chosen : θ 1 = eNat x := (Expr.app.inj isCand).2
    refine ⟨x, member, ?_⟩
    show Expr.app (Expr.app (Expr.sym 22) (θ 0)) (θ 1) ::ₘ candBag (C.erase x) = cleanBag j x (C.erase x)
    rw [count, chosen]
    rfl
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_two_one single
    obtain ⟨same, -⟩ := take_two split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1

/-- **At a cleaning bag**: one candidate less, or the restart on the chosen number. -/
theorem rewrites_clean {c : Code} {j x : ℕ} {C : Multiset ℕ} {M' : Multiset Expr}
    (rewrites : Rewrites (branchRules c) (cleanBag j x C) M') :
    (∃ j' y, j = j' + 1 ∧ y ∈ C ∧ M' = cleanBag j' x (C.erase y)) ∨
      (j = 0 ∧ M' = (Point.normal c .halt [x]).row ::ₘ candBag C) := by
  rcases rewrites_branch_cases rewrites with ⟨e, rest₀, e', split, rooted, -⟩ | single | single | single |
    single | single | single
  · obtain ⟨same, -⟩ := take_one split (by rcases rootStep_head rooted with h | h <;> rw [h] <;> decide)
    rcases rootStep_head rooted with h | h <;> rw [same] at h <;> cases h
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_two single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj (Expr.app.inj same).1).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_one_one single
    obtain ⟨same, -⟩ := take_one split (by intro h; cases h)
    cases (Expr.app.inj (Expr.app.inj same).1).1
  · obtain ⟨θ, rest₀, split, -⟩ := rewrites_two_one single
    obtain ⟨same, -⟩ := take_two split (by intro h; cases h)
    cases (Expr.app.inj same).1
  · obtain ⟨θ, rest₀, split, rfl⟩ := rewrites_two_one single
    obtain ⟨same, y, member, -, rfl⟩ := take_two split (by intro h; cases h)
    have parts := Expr.app.inj same
    have countPart : Expr.app (Expr.sym 1) (θ 0) = eNat j := (Expr.app.inj parts.1).2
    have chosen : θ 1 = eNat x := parts.2
    cases j with
    | zero => cases countPart
    | succ j' =>
        have previous : θ 0 = eNat j' := (Expr.app.inj countPart).2
        refine Or.inl ⟨j', y, rfl, member, ?_⟩
        show Expr.app (Expr.app (Expr.sym 22) (θ 0)) (θ 1) ::ₘ candBag (C.erase y) = cleanBag j' x (C.erase y)
        rw [previous, chosen]
        rfl
  · obtain ⟨θ, rest₀, split, rfl⟩ := rewrites_one_one single
    obtain ⟨same, rfl⟩ := take_one split (by intro h; cases h)
    have parts := Expr.app.inj same
    have countPart : Expr.sym 0 = eNat j := (Expr.app.inj parts.1).2
    have chosen : θ 0 = eNat x := parts.2
    cases j with
    | succ j' => cases countPart
    | zero =>
        refine Or.inr ⟨rfl, ?_⟩
        show Expr.app (Expr.app (Expr.app (Expr.sym 18) (inst θ (toTerm (eCode c)))) (Expr.sym 11))
            (Expr.app (Expr.app (Expr.sym 3) (θ 0)) (Expr.sym 2)) ::ₘ candBag C = _
        rw [inst_toTerm, chosen]
        rfl

/-! ## The rewrites the program does -/

theorem rewrites_of_control {c : Code} {r : SRule} (member : r ∈ controlRules c) {M M' : Multiset Expr}
    (single : Rewrites [r] M M') : Rewrites (branchRules c) M M' :=
  rewrites_of_mem (List.mem_append_right _ member) single

theorem rewrites_advance (c : Code) {p p' : Point} (advanced : Advances p p') :
    Rewrites (branchRules c) {p.row} {p'.row} := by
  obtain ⟨pair, member, θ, matched, made⟩ := (rootStep_schemas_iff p p'.row).mpr ⟨p', advanced, rfl⟩
  exact ⟨rowRule pair.1 pair.2, List.mem_append_left _ (List.mem_map_of_mem member), θ, 0,
    (add_zero _).trans (congrArg (fun e => ({e} : Multiset Expr)) matched),
    fun q member => absurd member List.not_mem_nil, fun e member => absurd member List.not_mem_nil,
    ((add_zero _).trans (congrArg (fun e => ({e} : Multiset Expr)) made)).symm⟩

theorem rewrites_startSpread (c : Code) (l : List ℕ) :
    Rewrites (branchRules c) {(Point.config (.halt l)).row} (spreadBag l 0 0) :=
  rewrites_of_control (r := startSpread) (by simp [controlRules])
    (rewrites_one_one_mk (fun _ => eNats l) 0 rfl (by rw [spreadBag, candBag_zero]; rfl))

theorem rewrites_spreadCons (c : Code) (x : ℕ) (rest : List ℕ) (j : ℕ) (C : Multiset ℕ) :
    Rewrites (branchRules c) (spreadBag (x :: rest) j C) (spreadBag rest (j + 1) (x ::ₘ C)) :=
  rewrites_of_control (r := spreadCons) (by simp [controlRules])
    (rewrites_one_two_mk (assign [eNat x, eNats rest, eNat j]) (candBag C) rfl
      (by rw [spreadBag, candBag_cons]; rfl))

theorem rewrites_spreadEnd (c : Code) (j : ℕ) (C : Multiset ℕ) :
    Rewrites (branchRules c) (spreadBag [] (j + 1) C) (pickBag j C) :=
  rewrites_of_control (r := spreadEnd) (by simp [controlRules])
    (rewrites_one_one_mk (fun _ => eNat j) (candBag C) rfl rfl)

theorem rewrites_choose (c : Code) {x : ℕ} {C : Multiset ℕ} (member : x ∈ C) (j : ℕ) :
    Rewrites (branchRules c) (pickBag j C) (cleanBag j x (C.erase x)) :=
  rewrites_of_control (r := choose) (by simp [controlRules])
    (rewrites_two_one_mk (assign [eNat j, eNat x]) (candBag (C.erase x))
      (by rw [pickBag, candBag_cons_erase member]; rfl) rfl)

theorem rewrites_cleanStep (c : Code) {y : ℕ} {C : Multiset ℕ} (member : y ∈ C) (j x : ℕ) :
    Rewrites (branchRules c) (cleanBag (j + 1) x C) (cleanBag j x (C.erase y)) :=
  rewrites_of_control (r := cleanStep) (by simp [controlRules])
    (rewrites_two_one_mk (assign [eNat j, eNat x, eNat y]) (candBag (C.erase y))
      (by rw [cleanBag, candBag_cons_erase member]; rfl) rfl)

theorem rewrites_restart (c : Code) (x : ℕ) (C : Multiset ℕ) :
    Rewrites (branchRules c) (cleanBag 0 x C) ((Point.normal c .halt [x]).row ::ₘ candBag C) := by
  refine rewrites_of_control (r := restartAt c) (by simp [controlRules])
    (rewrites_one_one_mk (fun _ => eNat x) (candBag C) rfl ?_)
  show _ = Expr.app (Expr.app (Expr.app (Expr.sym 18) (inst (fun _ => eNat x) (toTerm (eCode c))))
    (Expr.sym 11)) (Expr.app (Expr.app (Expr.sym 3) (eNat x)) (Expr.sym 2)) ::ₘ candBag C
  rw [inst_toTerm]
  rfl

/-! ## The system and its runs -/

/-- **The system of a code that lists successors**: `n` steps to every member of the list `c` evaluates `[n]`
to. -/
def Choose (c : Code) (n m : ℕ) : Prop := ∃ l ∈ c.eval [n], m ∈ l

/-- The system, with equality as its equations. -/
def chooseSystem (c : Code) : GSLT := equalityGSLT ℕ (Choose c)

/-- **A value of the code is a counted run of the machine to the halted configuration with that output.** -/
theorem eval_iff_runFor (c : Code) (v w : List ℕ) :
    w ∈ c.eval v ↔ ∃ r, runFor r (.normal c .halt v) = some (.config (.halt w)) := by
  constructor
  · intro member
    obtain ⟨q, isHalt, path⟩ := points_of_reduces (p := .normal c .halt v) ((adequacy c v w).mpr member)
    rw [pattern_halt isHalt.symm] at path
    exact reaches_iff_runFor.mp path
  · intro ran
    exact (adequacy c v w).mp (reduces_of_points (reaches_iff_runFor.mpr ran))

/-- A counted run to a halted configuration from a point that advances goes through the successor. -/
theorem runFor_advance {r : ℕ} {p p' : Point} {l : List ℕ} (ran : runFor r p = some (.config (.halt l)))
    (advanced : Advances p p') : ∃ r', r = r' + 1 ∧ runFor r' p' = some (.config (.halt l)) := by
  cases r with
  | zero =>
      have same : p = .config (.halt l) := Option.some.inj ran
      subst same
      cases advanced
  | succ r' =>
      have stepped : successor p = some p' := advanced
      refine ⟨r', rfl, ?_⟩
      simpa [runFor, stepped] using ran

/-! ## The bags of a number, counted -/

/-- **The bags of a number, with the number of silent firings left before the choice.** Computing: a point the
machine reaches from the pending evaluation of `n`, `r` reductions from its halted output `l`. Spreading: some of
the output is spread as candidates. Choosing: all of it is. Cleaning: `n` was chosen, `j` leftover candidates
remain, and the computation for `n` takes `r` reductions to its output `l`. -/
inductive PhaseIn (c : Code) (n : ℕ) : ℕ → Multiset Expr → Prop
  | computing {p : Point} {r : ℕ} {l : List ℕ} :
      Relation.ReflTransGen Advances (.normal c .halt [n]) p → runFor r p = some (.config (.halt l)) →
      PhaseIn c n (r + l.length + 2) {p.row}
  | spreading {l consumed rest : List ℕ} : l ∈ c.eval [n] → l = consumed ++ rest →
      PhaseIn c n (rest.length + 1) (spreadBag rest consumed.length (consumed : Multiset ℕ))
  | picking {l : List ℕ} {j : ℕ} : l ∈ c.eval [n] → l.length = j + 1 → PhaseIn c n 0 (pickBag j (l : Multiset ℕ))
  | cleaning {j r : ℕ} {C : Multiset ℕ} {l : List ℕ} : Multiset.card C = j →
      runFor r (.normal c .halt [n]) = some (.config (.halt l)) →
      PhaseIn c n (j + 1 + (r + l.length + 2)) (cleanBag j n C)

/-- **The bag a number is shown on**: a cleaning bag of the number, with as many candidates as its count. -/
def Shows (n : ℕ) (M : Multiset Expr) : Prop := ∃ j C, Multiset.card C = j ∧ M = cleanBag j n C

theorem cleanRow_inj {j x j' x' : ℕ} (same : cleanRow j x = cleanRow j' x') : j = j' ∧ x = x' :=
  ⟨eNat_injective (Expr.app.inj (Expr.app.inj same).1).2, eNat_injective (Expr.app.inj same).2⟩

theorem shows_unique {a b : ℕ} {M : Multiset Expr} (first : Shows a M) (second : Shows b M) : a = b := by
  obtain ⟨j, C, -, rfl⟩ := first
  obtain ⟨j', C', -, same⟩ := second
  have inside : cleanRow j a ∈ cleanBag j' b C' := same ▸ Multiset.mem_cons_self _ _
  have isClean : cleanRow j a = cleanRow j' b := eq_of_mem_cons_head inside (by intro h; cases h)
  exact (cleanRow_inj isClean).2

theorem coe_append_single (l : List ℕ) (x : ℕ) : ((l ++ [x] : List ℕ) : Multiset ℕ) = x ::ₘ (l : Multiset ℕ) := by
  rw [← Multiset.coe_add, Multiset.coe_singleton, add_comm, Multiset.singleton_add]

/-- **Every firing at a counted bag of `n`** lowers the count by exactly one and stays with `n`, or is the
choice of a successor `m`, landing on a bag of `m` that shows `m`. -/
theorem phase_step {c : Code} (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) {n k : ℕ} {M M' : Multiset Expr}
    (phase : PhaseIn c n k M) (rewrites : Rewrites (branchRules c) M M') :
    (0 < k ∧ PhaseIn c n (k - 1) M') ∨
      (k = 0 ∧ ∃ m, Choose c n m ∧ (∃ k', PhaseIn c m k' M') ∧ Shows m M') := by
  cases phase with
  | @computing p r l path ran =>
      rcases rewrites_point rewrites with ⟨p', advanced, rfl⟩ | ⟨l', rfl, rfl⟩
      · obtain ⟨r', rfl, ran'⟩ := runFor_advance ran advanced
        refine Or.inl ⟨by omega, ?_⟩
        rw [show r' + 1 + l.length + 2 - 1 = r' + l.length + 2 by omega]
        exact .computing (path.tail advanced) ran'
      · obtain ⟨zero, same⟩ := runFor_halt_unique (rfl : runFor 0 (.config (.halt l')) = _) ran
        subst zero
        subst same
        have member : l' ∈ c.eval [n] := (eval_iff_runFor c [n] l').mpr (reaches_iff_runFor.mp path)
        refine Or.inl ⟨by omega, ?_⟩
        rw [show 0 + l'.length + 2 - 1 = l'.length + 1 by omega]
        exact .spreading (consumed := []) member rfl
  | @spreading l consumed rest member split =>
      rcases rewrites_spread rewrites with ⟨x, rest', rfl, rfl⟩ | ⟨rfl, j', count, rfl⟩
      · refine Or.inl ⟨by simp, ?_⟩
        have moved : l = (consumed ++ [x]) ++ rest' := by rw [split]; simp
        have spread := PhaseIn.spreading member moved
        rw [List.length_append, List.length_singleton, coe_append_single] at spread
        simpa using spread
      · refine Or.inl ⟨by simp, ?_⟩
        rw [List.append_nil] at split
        subst split
        exact .picking member count
  | @picking l j member length =>
      obtain ⟨x, inside, rfl⟩ := rewrites_pick rewrites
      obtain ⟨l₀, valued⟩ := total x
      obtain ⟨r₀, ran₀⟩ := (eval_iff_runFor c [x] l₀).mp valued
      have count : Multiset.card ((l : Multiset ℕ).erase x) = j := by
        rw [Multiset.card_erase_of_mem inside, Multiset.coe_card, length]
        rfl
      exact Or.inr ⟨rfl, x, ⟨l, member, Multiset.mem_coe.mp inside⟩, ⟨_, .cleaning count ran₀⟩,
        ⟨j, _, count, rfl⟩⟩
  | @cleaning j r C l count ran =>
      rcases rewrites_clean rewrites with ⟨j', y, rfl, inside, rfl⟩ | ⟨rfl, rfl⟩
      · refine Or.inl ⟨by omega, ?_⟩
        have count' : Multiset.card (C.erase y) = j' := by
          rw [Multiset.card_erase_of_mem inside, count]
          rfl
        rw [show j' + 1 + 1 + (r + l.length + 2) - 1 = j' + 1 + (r + l.length + 2) by omega]
        exact .cleaning count' ran
      · refine Or.inl ⟨by omega, ?_⟩
        have empty : C = 0 := Multiset.card_eq_zero.mp count
        subst empty
        rw [candBag_zero, show 0 + 1 + (r + l.length + 2) - 1 = r + l.length + 2 by omega]
        exact .computing .refl ran

/-- **Choosing bags have count zero.** -/
theorem pick_count {c : Code} {n k : ℕ} {M : Multiset Expr} (phase : PhaseIn c n k M) {j : ℕ}
    {C : Multiset ℕ} (isPick : M = pickBag j C) : k = 0 := by
  cases phase with
  | @computing p r l path ran =>
      have inside : p.row ∈ pickBag j C := isPick ▸ Multiset.mem_singleton_self p.row
      have same : p.row = pickRow j :=
        eq_of_mem_cons_head inside (by rcases row_head p with h | h | h <;> rw [h] <;> decide)
      rcases row_head p with h | h | h <;> rw [same] at h <;> cases h
  | @spreading l consumed rest member split =>
      have inside : spreadRow rest consumed.length ∈ pickBag j C := isPick ▸ Multiset.mem_cons_self _ _
      cases (Expr.app.inj (eq_of_mem_cons_head inside (by intro h; cases h))).1
  | picking _ _ => rfl
  | @cleaning j' r C' l count ran =>
      have inside : cleanRow j' n ∈ pickBag j C := isPick ▸ Multiset.mem_cons_self _ _
      cases (Expr.app.inj (eq_of_mem_cons_head inside (by intro h; cases h))).1

/-- **The count at the pending evaluation of `n`**: the machine's reductions, the spreading of the output, its
end. -/
theorem start_count {c : Code} {n r : ℕ} {l : List ℕ} (ran : runFor r (.normal c .halt [n]) = some (.config (.halt l))) :
    PhaseIn c n (r + l.length + 2) {(Point.normal c .halt [n]).row} :=
  .computing .refl ran

/-- **Progress**: at a counted bag of `n`, if `n` has a successor, the bag is a choosing bag of the output, or a
silent firing lowers the count by one. -/
theorem phase_progress {c : Code} {n k m : ℕ} {M : Multiset Expr} (phase : PhaseIn c n k M)
    (successor : Choose c n m) :
    (∃ (j : ℕ) (l : List ℕ), M = pickBag j (l : Multiset ℕ) ∧ l ∈ c.eval [n] ∧ l.length = j + 1 ∧ m ∈ l) ∨
      (0 < k ∧ ∃ M', Rewrites (branchRules c) M M' ∧ PhaseIn c n (k - 1) M') := by
  obtain ⟨l₀, valued, chosen⟩ := successor
  cases phase with
  | @computing p r l path ran =>
      cases r with
      | zero =>
          have same : p = .config (.halt l) := Option.some.inj ran
          subst same
          have member : l ∈ c.eval [n] := (eval_iff_runFor c [n] l).mpr (reaches_iff_runFor.mp path)
          refine Or.inr ⟨by omega, _, rewrites_startSpread c l, ?_⟩
          rw [show 0 + l.length + 2 - 1 = l.length + 1 by omega]
          exact .spreading (consumed := []) member rfl
      | succ r' =>
          cases stepped : successor p with
          | none => simp [runFor, stepped] at ran
          | some p' =>
              have ran' : runFor r' p' = some (.config (.halt l)) := by simpa [runFor, stepped] using ran
              refine Or.inr ⟨by omega, _, rewrites_advance c stepped, ?_⟩
              rw [show r' + 1 + l.length + 2 - 1 = r' + l.length + 2 by omega]
              exact .computing (path.tail stepped) ran'
  | @spreading l consumed rest member split =>
      cases rest with
      | cons x rest' =>
          refine Or.inr ⟨by simp, _, rewrites_spreadCons c x rest' consumed.length consumed, ?_⟩
          have moved : l = (consumed ++ [x]) ++ rest' := by rw [split]; simp
          have spread := PhaseIn.spreading member moved
          rw [List.length_append, List.length_singleton, coe_append_single] at spread
          simpa using spread
      | nil =>
          rw [List.append_nil] at split
          subst split
          have same : l₀ = l := Part.mem_unique valued member
          subst same
          obtain ⟨j', length⟩ : ∃ j', l₀.length = j' + 1 :=
            ⟨l₀.length - 1, by have := List.length_pos_of_mem chosen; omega⟩
          refine Or.inr ⟨by simp, _, by rw [length]; exact rewrites_spreadEnd c j' l₀, ?_⟩
          exact .picking member length
  | @picking l j member length =>
      have same : l₀ = l := Part.mem_unique valued member
      subst same
      exact Or.inl ⟨j, l₀, rfl, member, length, chosen⟩
  | @cleaning j r C l count ran =>
      cases j with
      | succ j' =>
          obtain ⟨y, inside⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card C)
          refine Or.inr ⟨by omega, _, rewrites_cleanStep c inside j' n, ?_⟩
          have count' : Multiset.card (C.erase y) = j' := by
            rw [Multiset.card_erase_of_mem inside, count]
            rfl
          rw [show j' + 1 + 1 + (r + l.length + 2) - 1 = j' + 1 + (r + l.length + 2) by omega]
          exact .cleaning count' ran
      | zero =>
          have empty : C = 0 := Multiset.card_eq_zero.mp count
          subst empty
          refine Or.inr ⟨by omega, _, rewrites_restart c n 0, ?_⟩
          rw [candBag_zero, show 0 + 1 + (r + l.length + 2) - 1 = r + l.length + 2 by omega]
          exact .computing .refl ran

/-! ## The weak correspondence at the level of bags -/

/-- **The potential**: the least count of a bag of `n`. -/
noncomputable def potentialOf (c : Code) (n : ℕ) (M : Multiset Expr) : ℕ := by
  classical
  exact if h : ∃ k, PhaseIn c n k M then Nat.find h else 0

theorem potentialOf_spec {c : Code} {n k : ℕ} {M : Multiset Expr} (phase : PhaseIn c n k M) :
    PhaseIn c n (potentialOf c n M) M ∧ potentialOf c n M ≤ k := by
  classical
  unfold potentialOf
  rw [dif_pos ⟨k, phase⟩]
  exact ⟨Nat.find_spec (⟨k, phase⟩ : ∃ k, PhaseIn c n k M),
    Nat.find_min' (⟨k, phase⟩ : ∃ k, PhaseIn c n k M) phase⟩

/-- **Silent firings, then the choice**: from a counted bag of `n`, for every successor `m`, silent firings that
lower the potential lead to a choosing bag, and one firing chooses `m`. -/
theorem bag_forward {c : Code} (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) {n m : ℕ} {M : Multiset Expr}
    (related : ∃ k, PhaseIn c n k M) (chosen : Choose c n m) :
    ∃ M₁ M₂, Relation.ReflTransGen (SilentStep (rewriting (branchRules c)) (fun a X => ∃ k, PhaseIn c a k X)
      (potentialOf c) n) M M₁ ∧ Rewrites (branchRules c) M₁ M₂ ∧ (∃ k, PhaseIn c m k M₂) ∧ Shows m M₂ := by
    obtain ⟨k, phase⟩ := related
    have run : ∀ (bound : ℕ) (M : Multiset Expr), potentialOf c n M = bound → (∃ k, PhaseIn c n k M) →
        ∃ M₁ M₂, Relation.ReflTransGen (SilentStep (rewriting (branchRules c)) (fun a X => ∃ k, PhaseIn c a k X)
          (potentialOf c) n) M M₁ ∧ Rewrites (branchRules c) M₁ M₂ ∧ (∃ k, PhaseIn c m k M₂) ∧ Shows m M₂ := by
      intro bound
      refine Nat.strong_induction_on bound ?_
      intro bound smaller M atBound ⟨k₀, phase₀⟩
      have least := (potentialOf_spec phase₀).1
      rcases phase_progress least chosen with ⟨j, l, rfl, member, length, inside⟩ |
        ⟨positive, M', rewrites, phase'⟩
      · obtain ⟨l₀, valued⟩ := total m
        obtain ⟨r₀, ran₀⟩ := (eval_iff_runFor c [m] l₀).mp valued
        have count : Multiset.card ((l : Multiset ℕ).erase m) = j := by
          rw [Multiset.card_erase_of_mem (Multiset.mem_coe.mpr inside), Multiset.coe_card, length]
          rfl
        exact ⟨_, _, .refl, rewrites_choose c (Multiset.mem_coe.mpr inside) j, ⟨_, .cleaning count ran₀⟩,
          ⟨j, _, count, rfl⟩⟩
      · have lower : potentialOf c n M' < bound := by
          have := (potentialOf_spec phase').2
          omega
        obtain ⟨M₁, M₂, silentPath, stepped, related', shown⟩ := smaller _ lower M' rfl ⟨_, phase'⟩
        exact ⟨M₁, M₂, Relation.ReflTransGen.head ⟨rewrites, ⟨_, phase'⟩, by omega⟩ silentPath,
          stepped, related', shown⟩
    exact run _ M rfl ⟨k, phase⟩

/-- **The weak correspondence at the level of bags**, for a code with a value at every number. -/
noncomputable def bagWeak (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) :
    WeakCorrespondence (chooseSystem c) (rewriting (branchRules c)) where
  related n M := ∃ k, PhaseIn c n k M
  shows := Shows
  shows_unique := shows_unique
  potential := potentialOf c
  readStep := by
    intro n M M' ⟨k, phase⟩ rewrites
    have least := (potentialOf_spec phase).1
    rcases phase_step total least rewrites with ⟨positive, phase'⟩ | ⟨-, m, chosen, related', shown⟩
    · refine Or.inl ⟨⟨_, phase'⟩, ?_⟩
      have := (potentialOf_spec phase').2
      omega
    · exact Or.inr ⟨m, chosen, related', shown⟩
  forward := fun related chosen => bag_forward total related chosen

/-! ## On the one-match step -/

/-- The bag a state reads as, if any. -/
noncomputable def bagOf (s : SState ℕ) : Multiset Expr := by
  classical
  exact if h : ∃ M, ReadsBag s M then Classical.choose h else 0

theorem bagOf_eq {s : SState ℕ} {M : Multiset Expr} (reads : ReadsBag s M) : bagOf s = M := by
  classical
  unfold bagOf
  rw [dif_pos ⟨M, reads⟩]
  have chosen := Classical.choose_spec (⟨M, reads⟩ : ∃ M, ReadsBag s M)
  exact readsAs_unique (ReadsBag.readsAs chosen).1 (ReadsBag.readsAs chosen).2 (ReadsBag.readsAs reads).2

section Lift

variable {source : GSLT} {rules : List SRule}

/-- A silent path is a path of steps. -/
theorem steps_of_silent {target : GSLT} (C : WeakCorrespondence source target) {a : source.Term}
    {t t' : target.Term} (path : Relation.ReflTransGen (SilentStep target C.related C.potential a) t t') :
    Relation.ReflTransGen target.Step t t' := by
  induction path with
  | refl => exact .refl
  | tail _ silent reached => exact reached.tail silent.1

/-- **A weak correspondence to rewriting of bags is one to the step of the program**, reading a state as the
bag it reads as: one firing for one rewrite, the same potential, the same observation. -/
noncomputable def liftWeak (fragment : ∀ r ∈ rules, RangeRestrictedPositive r)
    (C : WeakCorrespondence source (rewriting rules)) : WeakCorrespondence source (stepSystem ℕ rules) where
  related a s := ∃ M, C.related a M ∧ ReadsBag s M
  shows a s := ∃ M, C.shows a M ∧ ReadsBag s M
  shows_unique := by
    rintro a b s ⟨M, shownA, readsA⟩ ⟨M', shownB, readsB⟩
    have same : M = M' :=
      readsAs_unique (ReadsBag.readsAs readsA).1 (ReadsBag.readsAs readsA).2 (ReadsBag.readsAs readsB).2
    subst same
    exact C.shows_unique shownA shownB
  potential a s := C.potential a (bagOf s)
  readStep := by
    rintro a s s' ⟨M, related, reads⟩ ⟨g, admitted, rfl⟩
    obtain ⟨M', rewrites, reads'⟩ := readsBag_backward fragment reads g admitted
    rcases C.readStep related rewrites with ⟨related', lower⟩ | ⟨b, sourceStep, related', shown⟩
    · refine Or.inl ⟨⟨M', related', reads'⟩, ?_⟩
      rw [bagOf_eq reads', bagOf_eq reads]
      exact lower
    · exact Or.inr ⟨b, sourceStep, ⟨M', related', reads'⟩, ⟨M', shown, reads'⟩⟩
  forward := by
    rintro a b s ⟨M, related, reads⟩ sourceStep
    obtain ⟨M₁, M₂, silentPath, stepped, related₂, shown₂⟩ := C.forward related sourceStep
    have lifted : ∀ {X Y : Multiset Expr},
        Relation.ReflTransGen (SilentStep (rewriting rules) C.related C.potential a) X Y →
        ∀ {x : SState ℕ}, ReadsBag x X → ∃ y, Relation.ReflTransGen (SilentStep (stepSystem ℕ rules)
          (fun a s => ∃ M, C.related a M ∧ ReadsBag s M) (fun a s => C.potential a (bagOf s)) a) x y ∧
          ReadsBag y Y := by
      intro X Y path
      induction path with
      | refl => exact fun {x} readsX => ⟨x, .refl, readsX⟩
      | tail _ silent reached =>
          intro x readsX
          obtain ⟨y₁, path₁, reads₁⟩ := reached readsX
          obtain ⟨g, admitted, reads₂⟩ := readsBag_forward fragment reads₁ silent.1
          refine ⟨_, path₁.tail ⟨⟨g, admitted, rfl⟩, ⟨_, silent.2.1, reads₂⟩, ?_⟩, reads₂⟩
          show C.potential a (bagOf _) < C.potential a (bagOf y₁)
          rw [bagOf_eq reads₂, bagOf_eq reads₁]
          exact silent.2.2
    obtain ⟨y₁, path, reads₁⟩ := lifted silentPath reads
    obtain ⟨g, admitted, reads₂⟩ := readsBag_forward fragment reads₁ stepped
    exact ⟨y₁, _, path, ⟨g, admitted, rfl⟩, ⟨M₂, related₂, reads₂⟩, ⟨M₂, shown₂, reads₂⟩⟩

/-- **Divergence is preserved by a weak correspondence**: every source step is realized by at least one target
step, so an infinite source run from a related state gives an infinite target run. -/
theorem acc_source_of_acc_target {target : GSLT} (C : WeakCorrespondence source target) {t : target.Term}
    (accessible : Acc (Relation.TransGen fun next state => target.Step state next) t) :
    ∀ {a : source.Term}, C.related a t → Acc (fun after before => source.Step before after) a := by
  induction accessible with
  | intro t _ ih =>
      intro a related
      refine Acc.intro a fun b sourceStep => ?_
      obtain ⟨t₁, t₂, silentPath, stepped, related₂, -⟩ := C.forward related sourceStep
      have path : Relation.TransGen target.Step t t₂ :=
        Relation.TransGen.tail' (steps_of_silent C silentPath) stepped
      exact ih t₂ ((Relation.transGen_swap (r := target.Step)).mpr path) related₂

theorem infinite_run_preserved {target : GSLT} (C : WeakCorrespondence source target) {a : source.Term}
    {t : target.Term} (related : C.related a t) (run : ℕ → source.Term) (starts : run 0 = a)
    (steps : ∀ i, source.Step (run i) (run (i + 1))) :
    ∃ targetRun : ℕ → target.Term, targetRun 0 = t ∧ ∀ i, target.Step (targetRun i) (targetRun (i + 1)) := by
  have sourceDiverges : ¬ Acc (fun after before => source.Step before after) a :=
    not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩
  have targetDiverges : ¬ Acc (fun next state => target.Step state next) t :=
    fun accessible => sourceDiverges (acc_source_of_acc_target C accessible.transGen related)
  exact not_acc_iff_exists_descending_chain.mp targetDiverges

end Lift

/-- **The weak correspondence on the one-match step**, for a code with a value at every number. -/
noncomputable def stepWeak (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) :
    WeakCorrespondence (chooseSystem c) (stepSystem ℕ (branchRules c)) :=
  liftWeak (branch_fragment c) (bagWeak c total)

/-- **The state of the pending evaluation of `n` is related to `n`.** -/
theorem stepWeak_start (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) (n : ℕ) :
    (stepWeak c total).related n (start c [n]) := by
  obtain ⟨l, valued⟩ := total n
  obtain ⟨r, ran⟩ := (eval_iff_runFor c [n] l).mp valued
  exact ⟨_, ⟨_, start_count ran⟩, rowState_reads _⟩

/-- **The operational correspondence** from the system to the step of the program. -/
noncomputable def stepCorrespondence (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) :
    OperationalCorrespondence (chooseSystem c) (stepSystem ℕ (branchRules c)) :=
  (stepWeak c total).toCorrespondence

/-- **Weak bisimulation without added divergence**: from the state of `n`, the step of the program has an
infinite run exactly when the system has one from `n`; and the correspondence realizes every step and reads
back every firing. -/
theorem divergence_iff (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]) (n : ℕ) :
    (∃ run : ℕ → ℕ, run 0 = n ∧ ∀ i, Choose c (run i) (run (i + 1))) ↔
      ∃ firings : ℕ → SState ℕ, firings 0 = start c [n] ∧
        ∀ i, (stepSystem ℕ (branchRules c)).Step (firings i) (firings (i + 1)) := by
  constructor
  · rintro ⟨run, starts, steps⟩
    exact infinite_run_preserved (stepWeak c total) (stepWeak_start c total n) run starts steps
  · rintro ⟨firings, starts, steps⟩
    exact (stepWeak c total).infinite_run_reflected (stepWeak_start c total n) firings starts steps

/-! ## Where the list has no value -/

/-- From the bag of the pending evaluation of `n`, where the code has no value, the program only advances the
machine. -/
theorem branch_reached {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) {M : Multiset Expr}
    (reached : (rewriting (branchRules c)).MultiStep ({(Point.normal c .halt [n]).row} : Multiset Expr) M) :
    ∃ p, M = {p.row} ∧ Relation.ReflTransGen Advances (.normal c .halt [n]) p := by
  have path := steps_of_multiStep reached
  clear reached
  induction path with
  | refl => exact ⟨_, rfl, .refl⟩
  | tail _ stepped reached' =>
      obtain ⟨p, rfl, points⟩ := reached'
      rcases rewrites_point stepped with ⟨p', advanced, rfl⟩ | ⟨l, rfl, -⟩
      · exact ⟨p', rfl, points.tail advanced⟩
      · have member : l ∈ c.eval [n] := (eval_iff_runFor c [n] l).mpr (reaches_iff_runFor.mp points)
        rw [none] at member
        exact absurd member (Part.notMem_none _)

/-- **Where the code has no value the program runs for ever** from the bag of the pending evaluation, while the
number has no successor. -/
theorem branch_runs_forever {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) :
    (∀ m, ¬ Choose c n m) ∧ ∃ run : ℕ → Multiset Expr, run 0 = {(Point.normal c .halt [n]).row} ∧
      ∀ i, Rewrites (branchRules c) (run i) (run (i + 1)) := by
  refine ⟨fun m ⟨l, member, _⟩ => by rw [none] at member; exact Part.notMem_none _ member, ?_⟩
  exact exists_infinite_run (S := rewriting (branchRules c)) fun M reached => by
    obtain ⟨p, rfl, points⟩ := branch_reached none reached
    obtain ⟨p', advanced⟩ : ∃ p', Advances p p' := by
      cases p with
      | normal c' k v => exact ⟨_, rfl⟩
      | config cfg =>
          cases cfg with
          | ret k v => exact ⟨_, rfl⟩
          | halt w =>
              have member : w ∈ c.eval [n] := (eval_iff_runFor c [n] w).mpr (reaches_iff_runFor.mp points)
              rw [none] at member
              exact absurd member (Part.notMem_none _)
    exact ⟨_, rewrites_advance c advanced⟩

/-- **The exact reason the weak sense fails where the list has no value**: no weak correspondence to the
program's rewriting relates `n` to the bag of its pending evaluation, because the number has no successor and
the program runs for ever from there, and a weak correspondence adds no divergence. -/
theorem no_weak_of_none {c : Code} {n : ℕ} (none : c.eval [n] = Part.none)
    (C : WeakCorrespondence (chooseSystem c) (rewriting (branchRules c))) :
    ¬ C.related n ({(Point.normal c .halt [n]).row} : Multiset Expr) := by
  intro related
  obtain ⟨stuck, run, starts, steps⟩ := branch_runs_forever none
  have accessible : Acc (fun after before => Choose c before after) n :=
    Acc.intro n fun m chosen => absurd chosen (stuck m)
  exact (not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩) (C.acc_of_acc accessible related)

/-- A point of the computation of a code with no value always advances. -/
theorem advances_of_none {c : Code} {n : ℕ} (none : c.eval [n] = Part.none) {p : Point}
    (points : Relation.ReflTransGen Advances (.normal c .halt [n]) p) : ∃ p', Advances p p' := by
  cases p with
  | normal c' k v => exact ⟨_, rfl⟩
  | config cfg =>
      cases cfg with
      | ret k v => exact ⟨_, rfl⟩
      | halt w =>
          have member : w ∈ c.eval [n] := (eval_iff_runFor c [n] w).mpr (reaches_iff_runFor.mp points)
          rw [none] at member
          exact absurd member (Part.notMem_none _)

/-- **The same on the one-match step**: no weak correspondence to the step of the program relates `n` to the
state of its pending evaluation, where the code has no value. The step runs for ever from there: every state it
reaches reads as a bag the rewriting reaches (`readsBag_backward`), the row of a point that advances. -/
theorem no_weak_of_none_step {c : Code} {n : ℕ} (none : c.eval [n] = Part.none)
    (C : WeakCorrespondence (chooseSystem c) (stepSystem ℕ (branchRules c))) :
    ¬ C.related n (start c [n]) := by
  intro related
  obtain ⟨stuck, -⟩ := branch_runs_forever none
  have accessible : Acc (fun after before => Choose c before after) n :=
    Acc.intro n fun m chosen => absurd chosen (stuck m)
  have reach : ∀ s, (stepSystem ℕ (branchRules c)).MultiStep (start c [n]) s → ∃ M, ReadsBag s M ∧
      (rewriting (branchRules c)).MultiStep ({(Point.normal c .halt [n]).row} : Multiset Expr) M := by
    intro s run
    have path := steps_of_multiStep run
    clear run
    induction path with
    | refl => exact ⟨_, rowState_reads _, .refl _⟩
    | tail _ stepped reached =>
        obtain ⟨M, reads, bagRun⟩ := reached
        obtain ⟨g, admitted, rfl⟩ := stepped
        obtain ⟨M', rewrites, reads'⟩ := readsBag_backward (branch_fragment c) reads g admitted
        exact ⟨M', reads', multiStepAppend bagRun (.step rewrites (.refl _))⟩
  obtain ⟨run, starts, steps⟩ :=
    exists_infinite_run (S := stepSystem ℕ (branchRules c)) (start := start c [n]) fun s run => by
      obtain ⟨M, reads, bagRun⟩ := reach s run
      obtain ⟨p, rfl, points⟩ := branch_reached none bagRun
      obtain ⟨p', advanced⟩ := advances_of_none none points
      obtain ⟨g, admitted, -⟩ := readsBag_forward (branch_fragment c) reads (rewrites_advance c advanced)
      exact ⟨_, g, admitted, rfl⟩
  exact (not_acc_iff_exists_descending_chain.mpr ⟨run, starts, steps⟩) (C.acc_of_acc accessible related)

/-! ## An instance with two successors at every number -/

/-- **A code that lists two successors**: `[n + 1, n + 2]` from `[n]`. -/
def twoCode : Code := .cons .succ (.cons (.comp .succ .succ) Code.nil)

theorem twoCode_eval (n : ℕ) : twoCode.eval [n] = pure [n + 1, n + 2] := by
  simp [twoCode]

theorem twoCode_total (x : ℕ) : ∃ l, l ∈ twoCode.eval [x] :=
  ⟨[x + 1, x + 2], by rw [twoCode_eval]; exact Part.mem_some _⟩

theorem twoCode_choose (n m : ℕ) : Choose twoCode n m ↔ m = n + 1 ∨ m = n + 2 := by
  constructor
  · rintro ⟨l, member, inside⟩
    rw [twoCode_eval] at member
    have same : l = [n + 1, n + 2] := Part.mem_some_iff.mp member
    subst same
    simpa using inside
  · intro either
    refine ⟨[n + 1, n + 2], by rw [twoCode_eval]; exact Part.mem_some _, ?_⟩
    rcases either with rfl | rfl <;> simp

/-- **The instance**: a weak correspondence on the one-match step for the system with two successors at every
number, related at every pending evaluation. -/
theorem twoCode_weak (n : ℕ) :
    (stepWeak twoCode twoCode_total).related n (start twoCode [n]) ∧ {m | Choose twoCode n m} = {n + 1, n + 2} :=
  ⟨stepWeak_start twoCode twoCode_total n, Set.ext fun m => (twoCode_choose n m).trans (by simp)⟩

#print axioms liftWeak
#print axioms acc_source_of_acc_target
#print axioms infinite_run_preserved
#print axioms stepWeak
#print axioms stepWeak_start
#print axioms stepCorrespondence
#print axioms divergence_iff
#print axioms branch_reached
#print axioms branch_runs_forever
#print axioms no_weak_of_none
#print axioms no_weak_of_none_step
#print axioms twoCode_eval
#print axioms twoCode_choose
#print axioms twoCode_weak
#print axioms start_count
#print axioms bag_forward

#print axioms branch_fragment
#print axioms rewrites_point
#print axioms rewrites_spread
#print axioms rewrites_pick
#print axioms rewrites_clean
#print axioms phase_step
#print axioms pick_count
#print axioms phase_progress
#print axioms bagWeak

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Branching
