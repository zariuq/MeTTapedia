import Mettapedia.GSLT.LanguageDef.RFC8259ValueSemantics

/-!
# Agreement at the JSON value boundary

A packed forest may retain distinct whitespace derivations of one JSON
document. This value-only projection succeeds exactly when its nonempty
candidate family elaborates everywhere to one value. It neither selects a
syntax occurrence nor changes the occurrence fibres of the source forest.
Resource bounds, C allocation and the completeness of a supplied candidate
family are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RFC8259ValueAgreement

open Mettapedia.GSLT.LanguageDef.RFC8259ValueSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics

inductive Agreement (Value Error : Type) where
  | value (value : Value)
  | failure (error : Error)
  | ambiguous
  | empty

def checkTail {Value Error : Type} [DecidableEq Value]
    (expected : Value) : List (Except Error Value) → Agreement Value Error
  | [] => .value expected
  | .error error :: _ => .failure error
  | .ok value :: rest =>
      if value = expected then checkTail expected rest else .ambiguous

def agree {Value Error : Type} [DecidableEq Value] :
    List (Except Error Value) → Agreement Value Error
  | [] => .empty
  | .error error :: _ => .failure error
  | .ok value :: rest => checkTail value rest

theorem checkTail_value_iff {Value Error : Type} [DecidableEq Value]
    (expected value : Value) (candidates : List (Except Error Value)) :
    checkTail expected candidates = .value value ↔
      expected = value ∧ ∀ candidate ∈ candidates, candidate = .ok expected := by
  induction candidates with
  | nil => simp [checkTail]
  | cons candidate rest ih =>
    cases candidate with
    | error error => simp [checkTail]
    | ok actual =>
      by_cases h : actual = expected
      · subst actual
        simpa [checkTail] using ih
      · simp [checkTail, h]

theorem agree_value_iff {Value Error : Type} [DecidableEq Value]
    (candidates : List (Except Error Value)) (value : Value) :
    agree candidates = .value value ↔
      candidates ≠ [] ∧ ∀ candidate ∈ candidates, candidate = .ok value := by
  cases candidates with
  | nil => simp [agree]
  | cons candidate rest =>
    cases candidate with
    | error error => simp [agree]
    | ok actual =>
      simp only [agree, checkTail_value_iff, List.cons_ne_nil, ne_eq,
        not_false_eq_true, true_and, List.mem_cons, forall_eq_or_imp,
        Except.ok.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, h⟩
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, h⟩

theorem agreement_no_invention {Value Error : Type} [DecidableEq Value]
    (candidates : List (Except Error Value)) (value : Value)
    (h : agree candidates = .value value) :
    .ok value ∈ candidates := by
  obtain ⟨hne, hall⟩ := (agree_value_iff candidates value).mp h
  cases candidates with
  | nil => exact False.elim (hne rfl)
  | cons candidate rest =>
    have hc := hall candidate (by simp)
    simp [hc]

def jsonCandidate (tree : CST) : Except ElaborationOutcome JSONValue :=
  match elaborateRootCST tree with
  | .value value => .ok value
  | failure => .error failure

theorem jsonCandidate_ok_iff (tree : CST) (value : JSONValue) :
    jsonCandidate tree = .ok value ↔ elaborateRootCST tree = .value value := by
  unfold jsonCandidate
  cases elaborateRootCST tree <;> simp

/-- The projection uses exact mathematical value equality. This definition
does not assert that a particular native equality implementation refines it. -/
noncomputable def projectValues (trees : List CST) :
    Agreement JSONValue ElaborationOutcome := by
  classical
  exact agree (trees.map jsonCandidate)

theorem projectValues_value_iff (trees : List CST) (value : JSONValue) :
    projectValues trees = .value value ↔
      trees ≠ [] ∧ ∀ tree ∈ trees, elaborateRootCST tree = .value value := by
  classical
  simp [projectValues, agree_value_iff, jsonCandidate_ok_iff]

private def wsEmpty (cursor : Nat) : CST :=
  .node "json:ws-empty" cursor cursor []

private def wsOne : CST :=
  .node "json:ws-cons" 1 2
    [.node "json:lex-ws" 1 2 [.terminal [32] 1 2], wsEmpty 2]

/-- Two source trees of `{ }`: the space can belong to either whitespace
field surrounding the empty member list. -/
def emptyObjectTree (spaceOnLeft : Bool) : CST :=
  let middle := if spaceOnLeft then 2 else 1
  .node "json:text" 0 3
    [wsEmpty 0,
     .node "json:value-object" 0 3
       [.node "json:object" 0 3
         [if spaceOnLeft then wsOne else wsEmpty 1,
          .node "json:members-none" middle middle [],
          if spaceOnLeft then wsEmpty 2 else wsOne]],
     wsEmpty 3]

theorem whitespace_trees_are_distinct :
    emptyObjectTree true ≠ emptyObjectTree false := by
  decide

theorem whitespace_values_agree (side : Bool) :
    elaborateRootCST (emptyObjectTree side) = .value (.object []) := by
  cases side <;> rfl

theorem whitespace_family_projects :
    projectValues [emptyObjectTree true, emptyObjectTree false] =
      .value (.object []) := by
  apply (projectValues_value_iff _ _).mpr
  simp [whitespace_values_agree]

def nullTree : CST :=
  .node "json:text" 0 4
    [wsEmpty 0, .node "json:value-null" 0 4 [], wsEmpty 4]

theorem different_values_do_not_project (value : JSONValue) :
    projectValues [emptyObjectTree true, nullTree] ≠ .value value := by
  intro h
  have hall := ((projectValues_value_iff _ _).mp h).2
  have first := hall (emptyObjectTree true) (by simp)
  have second := hall nullTree (by simp)
  have second' : elaborateRootCST nullTree = .value (.null) := by rfl
  rw [whitespace_values_agree] at first
  rw [second'] at second
  cases first
  cases second

#print axioms checkTail_value_iff
#print axioms agree_value_iff
#print axioms agreement_no_invention
#print axioms jsonCandidate_ok_iff
#print axioms projectValues_value_iff
#print axioms whitespace_trees_are_distinct
#print axioms whitespace_values_agree
#print axioms whitespace_family_projects
#print axioms different_values_do_not_project

end Mettapedia.GSLT.LanguageDef.RFC8259ValueAgreement
