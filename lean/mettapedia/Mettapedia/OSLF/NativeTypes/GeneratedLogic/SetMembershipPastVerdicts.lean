import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastSentences

/-!
# Verdicts on past modalities and quantifiers over a type, from representatives

For a plain body, the representatives grown by adjunction (`plainReps`) carry every type of a hereditarily finite set.
The verdicts read them:

- **A conflict** (`PlainFormula.conflict`) of a representative with a member `x`: a node `◇ψ` the representative
  refutes while `ψ` holds at `x`, or a node `□ψ` it proves while `ψ` fails at `x`. A set of the representative's type
  cannot contain `x` (`conflict_false_of_member`), and without a conflict adjoining `x` keeps the type
  (`eval_insert_of_conflict`).
- **`⧫ψ` at `x`** holds when some representative has `ψ` and no conflict with `x`; **`■ψ`** when every representative
  without a conflict has `ψ`; **`∃ T. ψ`** when some representative has the type and `ψ`; **`∀ T. ψ`** when every
  representative with the type has `ψ` (`beforeVerdict`, `alwaysVerdict`, `someVerdict`, `everyVerdict`).
- **Each verdict is exact** among the hereditarily finite sets (`beforeVerdict_iff` and the others): a witness is the
  representative itself, or `x` adjoined to it; and every set has a representative's type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace PlainFormula

theorem plain_parts_and {left right : PlainFormula} (plain : (PlainFormula.and left right).toFormula.plainModal = true) :
    left.toFormula.plainModal = true ∧ right.toFormula.plainModal = true := by
  simpa [toFormula, Formula.plainModal] using plain

theorem plain_parts_or {left right : PlainFormula} (plain : (PlainFormula.or left right).toFormula.plainModal = true) :
    left.toFormula.plainModal = true ∧ right.toFormula.plainModal = true := by
  simpa [toFormula, Formula.plainModal] using plain

theorem plain_inner_possibly {label : StepLabel} {inner : PlainFormula}
    (plain : (PlainFormula.possibly label inner).toFormula.plainModal = true) : inner.toFormula.plainModal = true := by
  simp only [toFormula, Formula.plainModal, Bool.and_eq_true] at plain
  exact plain.2

theorem plain_inner_necessarily {label : StepLabel} {inner : PlainFormula}
    (plain : (PlainFormula.necessarily label inner).toFormula.plainModal = true) :
    inner.toFormula.plainModal = true := by
  simp only [toFormula, Formula.plainModal, Bool.and_eq_true] at plain
  exact plain.2

/-- A plain formula with its own labels is modal. -/
theorem modal_of_plain : ∀ (formula : PlainFormula), formula.toFormula.plainModal = true →
    formula.toFormula.modal = true
  | .top, _ | .bot, _ => rfl
  | .and left right, plain | .or left right, plain => by
    simp only [toFormula, Formula.plainModal, Bool.and_eq_true] at plain
    simp only [toFormula, Formula.modal, modal_of_plain left plain.1, modal_of_plain right plain.2, Bool.and_self]
  | .possibly _ inner, plain | .necessarily _ inner, plain => by
    simp only [toFormula, Formula.plainModal, Bool.and_eq_true] at plain
    simp only [toFormula, Formula.modal, plain.1, modal_of_plain inner plain.2, Bool.and_self]

/-! ## Conflicts -/

/-- **A conflict of a representative `r` with a member `term`**: a node `◇ψ` that `r` refutes while `ψ` holds at
`term`, or a node `□ψ` that `r` proves while `ψ` fails at `term`. -/
def conflict : PlainFormula → Pattern → Pattern → Bool
  | .top, _, _ | .bot, _, _ => false
  | .and left right, r, term | .or left right, r, term => left.conflict r term || right.conflict r term
  | .possibly label inner, r, term =>
    (decide (memberLabel label) && !(PlainFormula.possibly label inner).eval r && inner.eval term) ||
      inner.conflict r term
  | .necessarily label inner, r, term =>
    (decide (memberLabel label) && (PlainFormula.necessarily label inner).eval r && !inner.eval term) ||
      inner.conflict r term

/-- **Without a conflict, adjoining the member keeps every node's value.** -/
theorem eval_insert_of_conflict : ∀ (formula : PlainFormula) {r term : Pattern}, formula.conflict r term = false →
    ∀ node ∈ formula.nodes, node.eval (insertTerm term r) = node.eval r
  | .top, _, _, _, node, inside => by
    rw [List.mem_singleton.mp inside]
    rfl
  | .bot, _, _, _, node, inside => by
    rw [List.mem_singleton.mp inside]
    rfl
  | .and left right, r, term, free, node, inside | .or left right, r, term, free, node, inside => by
    simp only [conflict, Bool.or_eq_false_iff] at free
    have leftKeeps := eval_insert_of_conflict left free.1
    have rightKeeps := eval_insert_of_conflict right free.2
    rcases List.mem_cons.mp inside with rfl | found
    · simp only [eval, leftKeeps left (self_mem_nodes left), rightKeeps right (self_mem_nodes right)]
    · rcases List.mem_append.mp found with found | found
      · exact leftKeeps node found
      · exact rightKeeps node found
  | .possibly label inner, r, term, free, node, inside => by
    simp only [conflict, Bool.or_eq_false_iff] at free
    rcases List.mem_cons.mp inside with rfl | found
    · rw [eval_insert_possibly]
      have first := free.1
      revert first
      cases decide (memberLabel label) <;> cases (PlainFormula.possibly label inner).eval r <;>
        cases inner.eval term <;> simp
    · exact eval_insert_of_conflict inner free.2 node found
  | .necessarily label inner, r, term, free, node, inside => by
    simp only [conflict, Bool.or_eq_false_iff] at free
    rcases List.mem_cons.mp inside with rfl | found
    · rw [eval_insert_necessarily]
      have first := free.1
      revert first
      cases decide (memberLabel label) <;> cases (PlainFormula.necessarily label inner).eval r <;>
        cases inner.eval term <;> simp
    · exact eval_insert_of_conflict inner free.2 node found

/-- **A set of a representative's type containing the member has no conflict with it.** -/
theorem conflict_false_of_member : ∀ (formula : PlainFormula) {r term whole : Pattern}, IsHF term → IsHF whole →
    zfOf term ∈ zfOf whole → (∀ node ∈ formula.nodes, node.eval r = node.eval whole) → formula.conflict r term = false
  | .top, _, _, _, _, _, _, _ | .bot, _, _, _, _, _, _, _ => rfl
  | .and left right, _, _, _, holds, wholeHolds, inside, same | .or left right, _, _, _, holds, wholeHolds, inside, same => by
    simp only [conflict, Bool.or_eq_false_iff]
    exact ⟨conflict_false_of_member left holds wholeHolds inside fun node found =>
        same node (List.mem_cons_of_mem _ (List.mem_append_left _ found)),
      conflict_false_of_member right holds wholeHolds inside fun node found =>
        same node (List.mem_cons_of_mem _ (List.mem_append_right _ found))⟩
  | .possibly label inner, r, term, whole, holds, wholeHolds, inside, same => by
    simp only [conflict, Bool.or_eq_false_iff]
    refine ⟨?_, conflict_false_of_member inner holds wholeHolds inside fun node found =>
      same node (List.mem_cons_of_mem _ found)⟩
    obtain ⟨value, valueMember, valueEq⟩ := (mem_zfOf_hf wholeHolds).mp inside
    have valueSame : inner.eval value = inner.eval term :=
      eval_congr inner (hf_members wholeHolds value valueMember) holds valueEq
    rw [same _ List.mem_cons_self]
    cases labelled : decide (memberLabel label)
    · rfl
    · cases holdsAt : inner.eval term
      · simp
      · have present : (PlainFormula.possibly label inner).eval whole = true := by
          simp only [eval, labelled, Bool.true_and, List.any_eq_true]
          exact ⟨value, valueMember, valueSame.trans holdsAt⟩
        simp [present]
  | .necessarily label inner, r, term, whole, holds, wholeHolds, inside, same => by
    simp only [conflict, Bool.or_eq_false_iff]
    refine ⟨?_, conflict_false_of_member inner holds wholeHolds inside fun node found =>
      same node (List.mem_cons_of_mem _ found)⟩
    obtain ⟨value, valueMember, valueEq⟩ := (mem_zfOf_hf wholeHolds).mp inside
    have valueSame : inner.eval value = inner.eval term :=
      eval_congr inner (hf_members wholeHolds value valueMember) holds valueEq
    rw [same _ List.mem_cons_self]
    cases labelled : decide (memberLabel label)
    · rfl
    · cases holdsAt : inner.eval term
      · have absent : (PlainFormula.necessarily label inner).eval whole = false := by
          simp only [eval, labelled, Bool.not_true, Bool.false_or, List.all_eq_false]
          exact ⟨value, valueMember, by rw [valueSame, holdsAt]; exact Bool.false_ne_true⟩
        simp [absent]
      · simp

end PlainFormula

/-! ## The verdicts -/

/-- **`⧫ψ` at a term**: some representative has `ψ` and no conflict with the term. -/
def beforeVerdict (label : StepLabel) (body : PlainFormula) (term : Pattern) : Bool :=
  decide (memberLabel label) && (plainReps body).any fun r => !body.conflict r term && body.eval r

/-- **`■ψ` at a term**: every representative without a conflict with the term has `ψ`. -/
def alwaysVerdict (label : StepLabel) (body : PlainFormula) (term : Pattern) : Bool :=
  !decide (memberLabel label) || (plainReps body).all fun r => body.conflict r term || body.eval r

/-- The formula a quantifier over a type classifies by: the type and the body. -/
abbrev typedBody (type : TypeExpr) (body : PlainFormula) : PlainFormula := .and (typePlain type) body

/-- **`∃ T. ψ`**: some representative has the type and `ψ`. -/
def someVerdict (type : TypeExpr) (body : PlainFormula) : Bool :=
  (plainReps (typedBody type body)).any (typedBody type body).eval

/-- **`∀ T. ψ`**: every representative with the type has `ψ`. -/
def everyVerdict (type : TypeExpr) (body : PlainFormula) : Bool :=
  (plainReps (typedBody type body)).all fun r => !(typePlain type).eval r || body.eval r

variable {body : PlainFormula}

theorem sat_iff_eval (plain : body.toFormula.plainModal = true) {term : Pattern} (holds : IsHF term) :
    HFSets.sat Env.closed body.toFormula (hfOf holds) ↔ body.eval term = true :=
  (hfSets_sat_iff plain _).trans (body.eval_iff Env.closed holds).symm

theorem covers_eval {term : Pattern} (holds : IsHF term) :
    ∃ r ∈ plainReps body, ∀ node ∈ body.nodes, node.eval r = node.eval term := by
  obtain ⟨r, inside, same⟩ := plainReps_covers body holds
  exact ⟨r, inside, PlainFormula.eval_of_vec same⟩

theorem mem_insertTerm {term whole : Pattern} (wholeHolds : IsHF whole) : zfOf term ∈ zfOf (insertTerm term whole) := by
  rw [zfOf_insertTerm term wholeHolds]
  exact ZFSet.mem_insert _ _

/-- **`⧫ψ` is exact.** -/
theorem beforeVerdict_iff (plain : body.toFormula.plainModal = true) (label : StepLabel) {term : Pattern}
    (holds : IsHF term) :
    beforeVerdict label body term = true ↔ HFSets.sat Env.closed (.sometimeBefore label body.toFormula) (hfOf holds) := by
  simp only [beforeVerdict, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨labelled, r, inside, free, holdsAt⟩
    have containerHolds := insertTerm_hf holds (plainReps_hf body r inside)
    refine ⟨hfOf containerHolds, ⟨labelled, mem_insertTerm (plainReps_hf body r inside)⟩, ?_⟩
    rw [sat_iff_eval plain containerHolds, body.eval_insert_of_conflict free body (body.self_mem_nodes)]
    exact holdsAt
  · rintro ⟨previous, ⟨labelled, inside⟩, holdsAt⟩
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term previous
    obtain ⟨r, rIn, same⟩ := covers_eval (body := body) wholeHolds
    refine ⟨labelled, r, rIn, body.conflict_false_of_member holds wholeHolds inside same, ?_⟩
    rw [same body body.self_mem_nodes]
    exact (sat_iff_eval plain wholeHolds).mp holdsAt

/-- **`■ψ` is exact.** -/
theorem alwaysVerdict_iff (plain : body.toFormula.plainModal = true) (label : StepLabel) {term : Pattern}
    (holds : IsHF term) :
    alwaysVerdict label body term = true ↔ HFSets.sat Env.closed (.alwaysBefore label body.toFormula) (hfOf holds) := by
  simp only [alwaysVerdict, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
  constructor
  · intro verdict previous step
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term previous
    obtain ⟨r, rIn, same⟩ := covers_eval (body := body) wholeHolds
    rcases verdict with unlabelled | every
    · exact absurd step.1 unlabelled
    · have free := body.conflict_false_of_member holds wholeHolds step.2 same
      rcases every r rIn with conflicting | holdsAt
      · rw [free] at conflicting
        exact absurd conflicting Bool.false_ne_true
      · rw [sat_iff_eval plain wholeHolds, ← same body body.self_mem_nodes]
        exact holdsAt
  · intro every
    by_cases labelled : memberLabel label
    · refine Or.inr fun r inside => ?_
      cases conflicting : body.conflict r term
      · have containerHolds := insertTerm_hf holds (plainReps_hf body r inside)
        have there := every (hfOf containerHolds) ⟨labelled, mem_insertTerm (plainReps_hf body r inside)⟩
        rw [sat_iff_eval plain containerHolds, body.eval_insert_of_conflict conflicting body body.self_mem_nodes] at there
        exact Or.inr there
      · exact Or.inl rfl
    · exact Or.inl labelled

/-- **`∃ T. ψ` is exact.** -/
theorem someVerdict_iff (plain : body.toFormula.plainModal = true) (type : TypeExpr) (x : HF) :
    someVerdict type body = true ↔ HFSets.sat Env.closed (.someOf type body.toFormula) x := by
  simp only [someVerdict, List.any_eq_true, typedBody, PlainFormula.eval, Bool.and_eq_true]
  constructor
  · rintro ⟨r, inside, typed, holdsAt⟩
    have rHolds := plainReps_hf _ r inside
    exact ⟨hfOf rHolds, (typePlain_eval_iff type rHolds).mp typed, (sat_iff_eval plain rHolds).mpr holdsAt⟩
  · rintro ⟨witness, typed, holdsAt⟩
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := covers_eval (body := typedBody type body) wholeHolds
    refine ⟨r, rIn, ?_, ?_⟩
    · rw [same (typePlain type) (List.mem_cons_of_mem _ (List.mem_append_left _ (typePlain type).self_mem_nodes))]
      exact (typePlain_eval_iff type wholeHolds).mpr typed
    · rw [same body (List.mem_cons_of_mem _ (List.mem_append_right _ body.self_mem_nodes))]
      exact (sat_iff_eval plain wholeHolds).mp holdsAt

/-- **`∀ T. ψ` is exact.** -/
theorem everyVerdict_iff (plain : body.toFormula.plainModal = true) (type : TypeExpr) (x : HF) :
    everyVerdict type body = true ↔ HFSets.sat Env.closed (.everyOf type body.toFormula) x := by
  simp only [everyVerdict, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro every witness typed
    obtain ⟨whole, wholeHolds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := covers_eval (body := typedBody type body) wholeHolds
    have typeSame := same (typePlain type) (List.mem_cons_of_mem _ (List.mem_append_left _ (typePlain type).self_mem_nodes))
    have bodySame := same body (List.mem_cons_of_mem _ (List.mem_append_right _ body.self_mem_nodes))
    rcases every r rIn with untyped | holdsAt
    · rw [typeSame] at untyped
      rw [(typePlain_eval_iff type wholeHolds).mpr typed] at untyped
      exact absurd untyped (by decide)
    · rw [sat_iff_eval plain wholeHolds, ← bodySame]
      exact holdsAt
  · intro every r inside
    have rHolds := plainReps_hf _ r inside
    cases typed : (typePlain type).eval r
    · exact Or.inl rfl
    · exact Or.inr ((sat_iff_eval plain rHolds).mp (every (hfOf rHolds) ((typePlain_eval_iff type rHolds).mp typed)))

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
