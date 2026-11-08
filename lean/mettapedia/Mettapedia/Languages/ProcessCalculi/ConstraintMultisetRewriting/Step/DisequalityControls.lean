import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Disequality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Disequality tells over first-order terms: controls

Terms over constants, variables and unary heads `app k`. The variable `X` is `X₀`, and `a`, `b` are
the constants `1`, `2`. Row `0` records `X = a` as data; row `1` is a marker.

## A disequality is checked by later bindings

`tellApart` tells `X ≠ a` by a firing of the step (`tellApart_admitted`). At every state whose
knowledge has no equations and whose disequations are `X ≠ a`, the binding `X = b` is admitted
(`other_admitted`) and the binding `X = a` is refused (`same_refused`): no solution separates.
`disequality_checked` runs this from the empty state.

## A disequality is not the absence of a row

* **Absence changes with the space.** With no row recording `X = a`, the absence guard of that row
  is admitted (`absent_record_admitted`) and so is the binding `X = a` (`same_admitted_open`).
  After the row is made, the guard is refused (`absent_record_refused`).
* **The disequation does not.** After the same insertion at the disequal state the binding `X = a`
  stays refused (`apart_persists_after_insert`): the disequation lives in the knowledge, not in the
  space. `absence_vs_disequality` collects the four verdicts.

## Principal answers

`X ≠ a` is separated by the identity and violated by `X := a`, so no single substitution presents its
solutions (`no_presenting_answer`). In the frames it has a principal answer, the identity with the
residual `X ≠ a` (`identity_principal_at_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Disequality.Controls

open Mettapedia.Logic.LP
open MeTTaCalculus.OccurrenceCommits (Enabled)

/-- Constants and variables are numbers; every head is unary. -/
abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Nat
  functionArity _ := 1

abbrev A := FirstOrder.action signature

/-- The unary head `k` applied to a term. -/
def app (k : Nat) (t : Term signature) : Term signature := .app k (fun _ => t)

/-- The variable `X₀`. -/
def X : Term signature := .var 0
def a : Term signature := .const 1
def b : Term signature := .const 2

/-! ## The term laws used below -/

@[simp] theorem E_iff (s t : Term signature) : A.E s t ↔ s = t := Iff.rfl
@[simp] theorem apply_X (σ : Subst signature) : A.apply σ X = σ 0 := rfl
@[simp] theorem apply_a (σ : Subst signature) : A.apply σ a = a := rfl
@[simp] theorem apply_b (σ : Subst signature) : A.apply σ b = b := rfl
@[simp] theorem apply_const (σ : Subst signature) (n : Nat) :
    A.apply σ (.const n) = .const n := rfl
@[simp] theorem apply_app (σ : Subst signature) (k : Nat) (t : Term signature) :
    A.apply σ (app k t) = app k (A.apply σ t) := rfl
@[simp high] theorem apply_identity (t : Term signature) : A.apply A.identity t = t :=
  A.apply_identity t

theorem app_inj {k k' : Nat} {t t' : Term signature} (same : app k t = app k' t') :
    k = k' ∧ t = t' := by
  simp only [app] at same
  obtain ⟨rfl, children⟩ := Term.app.inj same
  exact ⟨rfl, congrFun (eq_of_heq children) 0⟩

@[simp] theorem app_eq_app (k k' : Nat) (t t' : Term signature) :
    app k t = app k' t' ↔ k = k' ∧ t = t' :=
  ⟨app_inj, fun ⟨h, h'⟩ => h ▸ h' ▸ rfl⟩

@[simp] theorem app_ne_const (k n : Nat) (t : Term signature) : app k t ≠ .const n := by
  intro same
  cases same

@[simp] theorem const_ne_app (k n : Nat) (t : Term signature) :
    (.const n : Term signature) ≠ app k t := by
  intro same
  cases same

@[simp] theorem const_eq_const (m n : Nat) : (.const m : Term signature) = .const n ↔ m = n :=
  ⟨Term.const.inj, fun h => h ▸ rfl⟩

@[simp] theorem var_ne_const (v n : Nat) : (.var v : Term signature) ≠ .const n := by
  intro same
  cases same

@[simp] theorem a_ne_b : a ≠ b := by simp [a, b]
@[simp] theorem b_ne_a : b ≠ a := by simp [a, b]
@[simp] theorem X_ne_a : X ≠ a := by simp [X, a]

/-- `X := t`. -/
def bind (t : Term signature) : Subst signature := Subst.single 0 t

@[simp] theorem bind_zero (t : Term signature) : bind t 0 = t := by
  simp [bind, Subst.single]

/-- The empty selection is enabled everywhere. -/
theorem enabled_empty {label : Nat → Term signature} (store : Finset Nat) :
    Enabled label store ((⟨[], [], []⟩ : Selection Nat).commit (T := Term signature)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

/-- A selection that only makes `o` is enabled where `o` is absent. -/
theorem enabled_make {label : Nat → Term signature} {store : Finset Nat} {o : Nat}
    (absent : o ∉ store) :
    Enabled label store ((⟨[], [], [o]⟩ : Selection Nat).commit (T := Term signature)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simpa [Selection.commit] using absent, by simp [Selection.commit]⟩

/-! ## States and firings -/

/-- Row `0` records `X = a` as data; row `1` is a marker; row `2` is `p(X)`. -/
def rows : Nat → Term signature
  | 0 => app 4 a
  | 1 => .const 9
  | 2 => app 0 X
  | _ => .const 0

abbrev P := step A rows

/-- The disequation `X ≠ a` as a frame. -/
def apartFrame : Frame A := ⟨[(X, a)], by simp [Separates]⟩

/-- Nothing known, nothing present. -/
def openState : State A Nat := plain ⟨[], ∅⟩

/-- A firing that tells the equation `X = t`. -/
def tellEq (s : State A Nat) (t : Term signature) : Firing A Nat s :=
  Firing.ofBase s ⟨⟨[], [], [(X, t)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- A firing that tells the disequation `X ≠ a`, at a state without disequations. -/
def tellApart (s : State A Nat) (empty : s.disequations.1 = []) : Firing A Nat s :=
  ⟨⟨⟨[], [], [], [], []⟩, [], ⟨[], [], []⟩⟩, [(X, a)], by rw [empty]; simp [Separates]⟩

/-- A firing that makes row `0`, the record of `X = a`. -/
def insertRecord (s : State A Nat) : Firing A Nat s :=
  Firing.ofBase s ⟨⟨[], [], [], [], [rows 0]⟩, [], ⟨[], [], [0]⟩⟩

/-- A firing guarded by the absence of the record of `X = a`; it makes the marker. -/
def absentRecord (s : State A Nat) : Firing A Nat s :=
  Firing.ofBase s ⟨⟨[], [], [], [.absent (rows 0)], [rows 1]⟩, [], ⟨[], [], [1]⟩⟩

/-! ## A disequality is checked by later bindings -/

theorem tellApart_admitted : P.Admits (tellApart openState rfl) :=
  ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled_empty _,
    ⟨A.identity, by
        intro e member
        simp [Selection.problem, Selection.equations, tellApart, openState, plain] at member,
      by simp [Separates, Firing.target, tellApart, openState, plain]⟩,
    fun _ _ _ => ⟨by simp [tellApart], by simp [tellApart]⟩⟩

/-- The state after telling `X ≠ a`. -/
def afterApart : State A Nat := P.result (tellApart openState rfl) tellApart_admitted

theorem afterApart_equations : afterApart.configuration.equations = [] := rfl
theorem afterApart_disequations : afterApart.disequations.1 = [(X, a)] := rfl

theorem tellEq_problem (s : State A Nat) (equations : s.configuration.equations = [])
    (t : Term signature) {e : Equation (Term signature)}
    (member : e ∈ (tellEq s t).base.selection.problem rows (tellEq s t).base.rule s.configuration) :
    e = (X, t) := by
  simpa [Selection.problem, Selection.equations, tellEq, Firing.ofBase, equations] using member

/-- **A binding that keeps the disequation is admitted.** -/
theorem other_admitted (s : State A Nat) (equations : s.configuration.equations = [])
    (apart : s.disequations.1 = [(X, a)]) : P.Admits (tellEq s b) := by
  refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled_empty _, ⟨bind b, ?_, ?_⟩,
    fun _ _ _ => ⟨by simp [tellEq, Firing.ofBase], by simp [tellEq, Firing.ofBase]⟩⟩
  · intro e member
    rw [tellEq_problem s equations b member]
    simp [SubstitutionAction.Solves]
  · show Separates A (bind b) (s.disequations.1 ++ [])
    rw [apart]
    simp [Separates]

/-- **A binding that identifies a told disequation is refused.** -/
theorem same_refused (s : State A Nat) (apart : (X, a) ∈ s.disequations.1) :
    ¬ P.Admits (tellEq s a) := by
  rintro ⟨-, -, -, -, -, -, ⟨σ, solved, separated⟩, -⟩
  have bound : A.E (A.apply σ X) (A.apply σ a) := solved (X, a) (by
    simp [Selection.problem, Selection.equations, tellEq, Firing.ofBase])
  exact separated (X, a) (List.mem_append_left _ apart) bound

/-- **The disequation is told by a firing and checked by every later binding.** -/
theorem disequality_checked :
    (∃ r : P.Run openState, r.last = afterApart) ∧
      P.Admits (tellEq afterApart b) ∧ ¬ P.Admits (tellEq afterApart a) :=
  ⟨⟨.cons _ tellApart_admitted (.nil _), rfl⟩,
    other_admitted afterApart afterApart_equations afterApart_disequations,
    same_refused afterApart (by rw [afterApart_disequations]; exact List.mem_singleton_self _)⟩

/-! ## Absence changes with the space; the disequation does not -/

/-- With nothing known, the binding `X = a` is admitted. -/
theorem same_admitted_open : P.Admits (tellEq openState a) := by
  refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled_empty _, ⟨bind a, ?_, ?_⟩,
    fun _ _ _ => ⟨by simp [tellEq, Firing.ofBase], by simp [tellEq, Firing.ofBase]⟩⟩
  · intro e member
    rw [tellEq_problem openState rfl a member]
    simp [SubstitutionAction.Solves]
  · show Separates A (bind a) ([] ++ [])
    simp

/-- With no record of `X = a` present, its absence guard is admitted. -/
theorem absent_record_admitted (s : State A Nat) (equations : s.configuration.equations = [])
    (empty : s.configuration.present = ∅) (consistent : Separates A A.identity s.disequations.1) :
    P.Admits (absentRecord s) := by
  refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, enabled_make (by simp [empty]),
    ⟨A.identity, ?_, ?_⟩, fun _ _ _ => ⟨?_, by simp [absentRecord, Firing.ofBase]⟩⟩
  · intro e member
    simp [Selection.problem, Selection.equations, absentRecord, Firing.ofBase, equations] at member
  · show Separates A A.identity (s.disequations.1 ++ [])
    simpa using consistent
  · intro check member
    simp only [absentRecord, Firing.ofBase, List.mem_singleton] at member
    subst member
    intro o present
    simp [empty] at present

/-- Making the record of `X = a` at a state with nothing present. -/
theorem insert_admitted (s : State A Nat) (equations : s.configuration.equations = [])
    (empty : s.configuration.present = ∅) (consistent : Separates A A.identity s.disequations.1) :
    P.Admits (insertRecord s) := by
  refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, enabled_make (by simp [empty]),
    ⟨A.identity, ?_, ?_⟩, fun _ _ _ => ⟨by simp [insertRecord, Firing.ofBase],
      by simp [insertRecord, Firing.ofBase]⟩⟩
  · intro e member
    simp [Selection.problem, Selection.equations, insertRecord, Firing.ofBase, equations] at member
  · show Separates A A.identity (s.disequations.1 ++ [])
    simpa using consistent

/-- Once the record of `X = a` is present, its absence guard is refused. -/
theorem absent_record_refused (s : State A Nat) (present : 0 ∈ s.configuration.present) :
    ¬ P.Admits (absentRecord s) := by
  rintro ⟨-, -, -, -, -, -, ⟨σ, solved, separated⟩, asks⟩
  exact (asks σ solved separated).1 _ (List.mem_singleton_self _) 0 present rfl

/-- The open state after inserting the record. -/
def openInserted : State A Nat :=
  P.result (insertRecord openState) (insert_admitted openState rfl rfl (by simp [Separates, openState, plain]))

/-- The disequal state after inserting the record. -/
def apartInserted : State A Nat :=
  P.result (insertRecord afterApart) (insert_admitted afterApart rfl (by
    show MeTTaCalculus.OccurrenceCommits.fire _ _ = _
    decide) (by rw [afterApart_disequations]; simp [Separates]))

theorem openInserted_present : 0 ∈ openInserted.configuration.present := by
  show 0 ∈ MeTTaCalculus.OccurrenceCommits.fire _ _
  decide

theorem apartInserted_disequations : apartInserted.disequations.1 = [(X, a)] := rfl

/-- **A disequality is not the absence of a row.** Without disequations, the absence guard of the
record of `X = a` is admitted and so is the binding `X = a`; after the record is made, the guard is
refused. Under `X ≠ a`, the binding `X = a` is refused before and after the same insertion: absence
changed with the space, the disequation did not. -/
theorem absence_vs_disequality :
    P.Admits (absentRecord openState) ∧ P.Admits (tellEq openState a) ∧
      ¬ P.Admits (absentRecord openInserted) ∧
      ¬ P.Admits (tellEq afterApart a) ∧ ¬ P.Admits (tellEq apartInserted a) :=
  ⟨absent_record_admitted openState rfl rfl (by simp [Separates, openState, plain]),
    same_admitted_open, absent_record_refused openInserted openInserted_present,
    same_refused afterApart (by rw [afterApart_disequations]; exact List.mem_singleton_self _),
    same_refused apartInserted (by rw [apartInserted_disequations]; exact List.mem_singleton_self _)⟩

/-! ## Principal answers -/

/-- **No single substitution presents the solutions of `X ≠ a`**: the identity separates it and
`X := a` does not. -/
theorem no_presenting_answer : ¬ ∃ answer, Presents A [(X, a)] answer := by
  intro presented
  have every := (presents_iff A [(X, a)]).mp presented (bind a)
  exact every (X, a) (List.mem_singleton_self _) (by simp)

/-- **In the frames, `X ≠ a` has a principal answer**: the identity, with `X ≠ a` as its residual
frame. -/
theorem identity_principal_at_apart :
    (frames A).Principal (a := apartFrame) [] (toImage apartFrame A.identity apartFrame.2) :=
  principal ⟨fun _ member => absurd member (List.not_mem_nil), fun δ _ =>
    ⟨δ, fun t => by
      show A.apply δ t = A.apply (A.compose δ A.identity) t
      rw [A.apply_compose, A.apply_identity]⟩⟩ apartFrame.2

#print axioms tellApart_admitted
#print axioms other_admitted
#print axioms same_refused
#print axioms disequality_checked
#print axioms same_admitted_open
#print axioms absent_record_admitted
#print axioms insert_admitted
#print axioms absent_record_refused
#print axioms absence_vs_disequality
#print axioms no_presenting_answer
#print axioms identity_principal_at_apart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Disequality.Controls
