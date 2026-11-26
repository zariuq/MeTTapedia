import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-! # Ordered matching of closed atom components -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ClosedAtomMatching

open Metta QueryOpBridge

private theorem not_var_of_closed {atom : Atom} (closed : atom.vars = []) :
    ∀ name, atom ≠ .var name := by
  intro name equality
  subst atom
  simp [Atom.vars] at closed

/-- Binding merge prepends fresh closed values in the order of insertion. -/
theorem merge_closed_fresh {acc delta : Bindings}
    (before : ClosedValueBindings acc) (incoming : ClosedValueBindings delta)
    (distinct : (bindingValueKeys delta).Nodup)
    (fresh : ∀ key ∈ bindingValueKeys delta, key ∉ bindingValueKeys acc) :
    Bindings.merge acc delta = [delta.reverse ++ acc] := by
  induction incoming generalizing acc with
  | nil => rfl
  | @val name value rest closed tail ih =>
      have keys := List.nodup_cons.mp distinct
      have headFresh : name ∉ bindingValueKeys acc :=
        fresh name (by simp [bindingValueKeys])
      have one := ValueBindings.merge_singleton_val_eq_of_not_key before.toValueBindings
        (not_var_of_closed closed) headFresh
      have restFresh : ∀ key ∈ bindingValueKeys rest,
          key ∉ bindingValueKeys (BindingRel.val name value :: acc) := by
        intro key present rejected
        simp only [bindingValueKeys, List.mem_cons] at rejected
        rcases rejected with rfl | conflict
        · exact keys.1 present
        · exact fresh key (by simp [bindingValueKeys, present]) conflict
      have restMatch := ih (.val closed before) keys.2 restFresh
      change rest.foldl Bindings.mergeOne (Bindings.merge acc [.val name value]) = _
      rw [one]
      change Bindings.merge (.val name value :: acc) rest = _
      rw [restMatch]
      simp [List.reverse_cons, List.append_assoc]

/-- One source component with its exact ordered match and closed bindings. -/
structure AtomMatch where
  pattern : Atom
  target : Atom
  bindings : Bindings
  matched : matchAtomsWith none pattern target = [bindings]
  closed : ClosedValueBindings bindings

namespace AtomMatch

def symbol (name : String) : AtomMatch where
  pattern := .sym name
  target := .sym name
  bindings := []
  matched := by simp [matchAtomsWith]
  closed := .nil

def bind (name : VarName) (value : Atom) (closed : value.vars = []) : AtomMatch where
  pattern := .var name
  target := value
  bindings := [.val name value]
  matched := by
    have fresh := occurs_eq_false_of_not_mem_vars name value (by simp [closed])
    cases value with
    | var _ => simp [Atom.vars] at closed
    | sym _ | gnd _ | expr _ => simp [matchAtomsWith, fresh]
  closed := .val closed .nil

/-- A matched literal with no new bindings. -/
def literal (atom : Atom) (exactMatch : matchAtomsWith none atom atom = [[]]) : AtomMatch where
  pattern := atom
  target := atom
  bindings := []
  matched := exactMatch
  closed := .nil

def captured (rows : List AtomMatch) : Bindings :=
  rows.flatMap (·.bindings)

theorem captured_closed (rows : List AtomMatch) : ClosedValueBindings (captured rows) := by
  induction rows with
  | nil => exact .nil
  | cons row rest ih => exact row.closed.append ih

/-- Pointwise matching composes closed rows while retaining binding order. -/
theorem matchAll_of_fresh (rows : List AtomMatch) {acc : Bindings}
    (before : ClosedValueBindings acc)
    (distinct : (bindingValueKeys (captured rows)).Nodup)
    (fresh : ∀ key ∈ bindingValueKeys (captured rows), key ∉ bindingValueKeys acc) :
    matchAll none [acc] (rows.map (·.pattern)) (rows.map (·.target)) =
      [(captured rows).reverse ++ acc] := by
  induction rows generalizing acc with
  | nil => rfl
  | cons row rest ih =>
      simp only [captured, List.flatMap_cons, bindingValueKeys_append] at distinct fresh
      obtain ⟨headKeys, restKeys, distinctKeys⟩ := List.nodup_append.mp distinct
      have merged := merge_closed_fresh before row.closed headKeys
        (fun key here => fresh key (List.mem_append_left _ here))
      have restFresh : ∀ key ∈ bindingValueKeys (captured rest),
          key ∉ bindingValueKeys (row.bindings.reverse ++ acc) := by
        intro key here duplicate
        rw [bindingValueKeys_append, row.closed.toValueBindings.bindingValueKeys_reverse,
          List.mem_append, List.mem_reverse] at duplicate
        rcases duplicate with left | right
        · exact distinctKeys key left key here rfl
        · exact fresh key (List.mem_append_right _ here) right
      change matchAll none [acc] (row.pattern :: _) (row.target :: _) = _
      rw [matchAll, row.matched]
      simp only [row.closed.hasLoop_false, Bool.not_false, List.filter_cons, List.filter_nil,
        if_true, List.flatMap_singleton]
      rw [merged, ih (row.closed.reverse.append before) restKeys restFresh]
      simp [captured, List.reverse_append, List.append_assoc]

/-- The expression plan uses the same ordered merge as each source match. -/
def expression (rows : List AtomMatch) (distinct : (bindingValueKeys (captured rows)).Nodup) :
    AtomMatch where
  pattern := .expr (rows.map (·.pattern))
  target := .expr (rows.map (·.target))
  bindings := (captured rows).reverse
  matched := by
    change matchAll none [[]] (rows.map (·.pattern)) (rows.map (·.target)) = _
    simpa only [List.append_nil] using matchAll_of_fresh rows .nil distinct
      (fun _ _ => by simp [bindingValueKeys])
  closed := (captured_closed rows).reverse

theorem checked (row : AtomMatch) :
    Metta.matchAtoms row.pattern row.target = [row.bindings] := by
  simp [Metta.matchAtoms, row.matched, row.closed.hasLoop_false]

end AtomMatch

/-- A spine of the wrong length produces no result, including after a seed. -/
theorem matchAll_ne_length {acc : List Bindings} {pattern target : List Atom}
    (different : pattern.length ≠ target.length) : matchAll none acc pattern target = [] := by
  induction pattern generalizing target acc with
  | nil => cases target <;> simp [matchAll] at different ⊢
  | cons first rest ih =>
      cases target with
      | nil => rfl
      | cons next tail =>
          rw [matchAll]
          exact ih (by simpa using different)

section Controls

open AtomMatch

example :
    Metta.matchAtoms
      (.expr [.sym "pair", .var "x", .expr [.sym "one", .var "y", .var "z"]])
      (.expr [.sym "pair", .sym "a", .expr [.sym "one", .sym "b", .sym "c"]]) =
      [[.val "y" (.sym "b"), .val "z" (.sym "c"), .val "x" (.sym "a")]] :=
  (expression [symbol "pair", bind "x" (.sym "a") (by simp [Atom.vars]),
    expression [symbol "one", bind "y" (.sym "b") (by simp [Atom.vars]),
      bind "z" (.sym "c") (by simp [Atom.vars])]
      (by decide)] (by decide)).checked

example :
    ¬ (bindingValueKeys (captured [bind "x" (.sym "a") (by simp [Atom.vars]),
      bind "x" (.sym "b") (by simp [Atom.vars])])).Nodup := by decide

example : matchAll none [[]] [.sym "pair", .var "x"] [.sym "pair"] = [] :=
  matchAll_ne_length (by decide)

end Controls

#print axioms merge_closed_fresh
#print axioms AtomMatch.matchAll_of_fresh
#print axioms AtomMatch.checked

end Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.ClosedAtomMatching
