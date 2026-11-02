import Mettapedia.Languages.MeTTa.PeTTa.UnifyingTransform

/-!
# Renaming apart, against matching

`Eval.step` runs an equation's body under a fresh environment: the matching
substitution of its argument patterns. `Unifying.step` renames the equation's
variables apart (`$x` becomes `$x#use`) and runs the renamed body under one
substitution shared with the caller. Matching a renamed pattern is matching the
pattern, renamed (`matchAtom_rename`, `matchValue_rename`), so on ground
arguments a call of `Unifying.step` selects the same equations as
`Eval.clauses`, in the same order, each under the matching substitution
renamed for its use and followed by the caller's bindings
(`selections_eq_renamedClauses`).

Example: with `(= (f $x) (a $x))` and the call `(f 1)` at use `0`, `Eval.clauses`
gives the body `(a $x)` under `{$x ↦ 1}`; `Unifying.step` gives `(a $x#0)` under
`{$x#0 ↦ 1}` followed by the caller's bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst isGroundAtom matchAtom)
open Mettapedia.Languages.ProcessCalculi
open UnifyingTransform (consView_renameList renameList_eq_map)

/-! ## Renaming apart, against matching -/

/-- The keys of a substitution renamed for the use `use`. -/
def renameKeys (use : Nat) (bindings : Subst) : Subst :=
  bindings.map fun binding => (freshName use binding.1, binding.2)

theorem freshName_injective (use : Nat) {first second : String}
    (same : freshName use first = freshName use second) : first = second := by
  unfold freshName at same
  simpa using same

/-- No name of the use `use` is bound. -/
def FreshFor (use : Nat) (bindings : Subst) : Prop :=
  ∀ name, bindings.lookup (freshName use name) = none

theorem lookup_renameKeys (use : Nat) (bindings : Subst) (name : String) :
    (renameKeys use bindings).lookup (freshName use name) = bindings.lookup name := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.1 = name
      · simp [renameKeys, MORK.Subst.lookup, same]
      · have different : (freshName use first.1 == freshName use name) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun equal => same (freshName_injective use equal)
        have plain : (first.1 == name) = false := by simpa using same
        simp only [renameKeys, MORK.Subst.lookup, List.map_cons, List.find?_cons, different, plain]
          at ih ⊢
        exact ih

theorem lookup_append_renamed {use : Nat} {bindings outer : Subst} (fresh : FreshFor use outer)
    (name : String) :
    (renameKeys use bindings ++ outer).lookup (freshName use name) = bindings.lookup name := by
  unfold MORK.Subst.lookup
  rw [List.find?_append]
  have renamed := lookup_renameKeys use bindings name
  unfold MORK.Subst.lookup at renamed
  cases found : (renameKeys use bindings).find? (fun binding => binding.1 == freshName use name) with
  | some binding => rw [found] at renamed; simp [renamed]
  | none =>
      rw [found] at renamed
      have outerFree := fresh name
      unfold MORK.Subst.lookup at outerFree
      simp only [Option.none_or]
      rw [outerFree]
      simpa using renamed.symm

/-- **Matching a renamed pattern is matching the pattern, renamed**: with the
caller's substitution `outer` binding no name of the use, the matching of the
renamed pattern from `renameKeys use σ ++ outer` is the matching of the pattern
from `σ`, renamed and followed by `outer`. -/
theorem matchAtom_rename {use : Nat} {outer : Subst} (fresh : FreshFor use outer) :
    ∀ (bindings : Subst) (pattern value : Atom),
      matchAtom (renameKeys use bindings ++ outer) (rename use pattern) value =
        (matchAtom bindings pattern value).map fun bound => renameKeys use bound ++ outer
  | bindings, .var name, value => by
      simp only [rename, matchAtom, lookup_append_renamed fresh]
      cases bindings.lookup name with
      | none => simp [renameKeys]
      | some old => by_cases same : (value == old) = true <;> simp [same]
  | bindings, .symbol name, value => by
      cases value <;> simp [rename, matchAtom]
  | bindings, .grounded item, value => by
      cases value <;> simp [rename, matchAtom]
  | bindings, .expression patterns, value => by
      cases value with
      | expression values =>
          simp only [rename, matchAtom]
          exact list patterns values bindings
      | _ => simp [rename, matchAtom]
where
  list : ∀ (patterns values : List Atom) (bindings : Subst),
      matchAtom.matchAtomList (renameKeys use bindings ++ outer) (rename.renameList use patterns) values =
        (matchAtom.matchAtomList bindings patterns values).map fun bound => renameKeys use bound ++ outer
    | [], [], _ => rfl
    | [], _ :: _, _ => rfl
    | _ :: _, [], _ => rfl
    | pattern :: patterns, value :: values, bindings => by
        simp only [rename.renameList, matchAtom.matchAtomList, matchAtom_rename fresh bindings pattern value]
        cases matchAtom bindings pattern value with
        | none => rfl
        | some middle => exact list patterns values middle

theorem renameKeys_cons (use : Nat) (name : String) (value : Atom) (bindings : Subst) :
    renameKeys use ((name, value) :: bindings) = (freshName use name, value) :: renameKeys use bindings := rfl

/-- **Matching a renamed pattern with the list view is matching the pattern,
renamed** (`matchAtom_rename` for `SpaceSemantics.matchValue`). -/
theorem matchValue_rename {use : Nat} {outer : Subst} (fresh : FreshFor use outer) :
    ∀ (size : Nat) (bindings : Subst) (pattern value : Atom), Unifying.atomSize pattern ≤ size →
      SpaceSemantics.matchValue (renameKeys use bindings ++ outer) (rename use pattern) value =
        (SpaceSemantics.matchValue bindings pattern value).map fun bound => renameKeys use bound ++ outer := by
  intro size
  induction size with
  | zero => intro _ pattern _ small; have := Unifying.atomSize_pos pattern; omega
  | succ size ih =>
      intro bindings pattern value small
      have lists : ∀ (patterns values : List Atom) (current : Subst),
          (∀ item ∈ patterns, Unifying.atomSize item ≤ size) →
          SpaceSemantics.matchValue.matchValues (renameKeys use current ++ outer)
              (rename.renameList use patterns) values =
            (SpaceSemantics.matchValue.matchValues current patterns values).map
              fun bound => renameKeys use bound ++ outer := by
        intro patterns
        induction patterns with
        | nil =>
            intro values current _
            cases values <;> simp [rename.renameList, SpaceSemantics.matchValue.matchValues]
        | cons first rest restIh =>
            intro values current smallItems
            cases values with
            | nil => simp [rename.renameList, SpaceSemantics.matchValue.matchValues]
            | cons value remaining =>
                simp only [rename.renameList, SpaceSemantics.matchValue.matchValues]
                rw [ih current first value (smallItems first List.mem_cons_self)]
                cases SpaceSemantics.matchValue current first value with
                | none => rfl
                | some middle =>
                    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
                    exact restIh remaining middle
                      (fun item member => smallItems item (List.mem_cons_of_mem _ member))
      cases pattern with
      | var name =>
          rw [Unifying.matchValue_atom _ _ _ rfl, Unifying.matchValue_atom _ _ _ rfl]
          exact matchAtom_rename fresh bindings _ value
      | symbol name =>
          rw [Unifying.matchValue_atom _ _ _ rfl, Unifying.matchValue_atom _ _ _ rfl]
          exact matchAtom_rename fresh bindings _ value
      | grounded item =>
          rw [Unifying.matchValue_atom _ _ _ rfl, Unifying.matchValue_atom _ _ _ rfl]
          exact matchAtom_rename fresh bindings _ value
      | expression patterns =>
          cases view : Unifying.consView patterns
          · have renamedView : Unifying.consView (rename.renameList use patterns) = false := by
              rw [consView_renameList]; exact view
            cases value with
            | expression values =>
                simp only [rename]
                rw [SpaceSemantics.matchValue_expression_of_not_cons _ _ _
                    (Unifying.not_cons_of_consView renamedView),
                  SpaceSemantics.matchValue_expression_of_not_cons _ _ _
                    (Unifying.not_cons_of_consView view)]
                exact lists patterns values bindings (fun item member => by
                  have := Unifying.atomSize_lt_of_mem member
                  omega)
            | var _ =>
                simp only [rename]
                rw [Unifying.matchValue_expression_constant _ _ _ rfl,
                  Unifying.matchValue_expression_constant _ _ _ rfl]
                rfl
            | symbol _ =>
                simp only [rename]
                rw [Unifying.matchValue_expression_constant _ _ _ rfl,
                  Unifying.matchValue_expression_constant _ _ _ rfl]
                rfl
            | grounded _ =>
                simp only [rename]
                rw [Unifying.matchValue_expression_constant _ _ _ rfl,
                  Unifying.matchValue_expression_constant _ _ _ rfl]
                rfl
          · obtain ⟨first, rest, rfl⟩ := Unifying.consView_true view
            simp only [Unifying.atomSize, Unifying.atomSize.listSize] at small
            have renamed : rename use (.expression [.symbol "cons", first, rest]) =
                .expression [.symbol "cons", rename use first, rename use rest] := rfl
            rw [renamed]
            cases value with
            | expression values =>
                cases values with
                | nil =>
                    rw [Unifying.matchValue_cons_view_other _ _ _ _ rfl,
                      Unifying.matchValue_cons_view_other _ _ _ _ rfl]
                    rfl
                | cons head tail =>
                    rw [Unifying.matchValue_cons_view, Unifying.matchValue_cons_view,
                      ih bindings first head (by omega)]
                    cases SpaceSemantics.matchValue bindings first head with
                    | none => rfl
                    | some middle =>
                        simp only [Option.map_some, Option.bind_some]
                        exact ih middle rest (.expression tail) (by omega)
            | var _ =>
                rw [Unifying.matchValue_cons_view_other _ _ _ _ rfl,
                  Unifying.matchValue_cons_view_other _ _ _ _ rfl]
                rfl
            | symbol _ =>
                rw [Unifying.matchValue_cons_view_other _ _ _ _ rfl,
                  Unifying.matchValue_cons_view_other _ _ _ _ rfl]
                rfl
            | grounded _ =>
                rw [Unifying.matchValue_cons_view_other _ _ _ _ rfl,
                  Unifying.matchValue_cons_view_other _ _ _ _ rfl]
                rfl

/-- The alternatives `Eval.clauses` selects, each equation renamed for its own use
and its matching substitution followed by the caller's. -/
def renamedClauses (outer : Subst) (values : List Atom) :
    Nat → List SpaceSemantics.Equation → List Unifying.Control
  | _, [] => []
  | use, equation :: rest =>
      match SpaceSemantics.matchValue.matchValues [] equation.arguments values with
      | some bound => .evaluate (renameKeys use bound ++ outer) (rename use equation.body) ::
          renamedClauses outer values (use + 1) rest
      | none => renamedClauses outer values (use + 1) rest

theorem renameKeys_nil (use : Nat) : renameKeys use [] = [] := rfl

/-- `matchValue_rename` for argument lists. -/
theorem matchValues_rename {use : Nat} {outer : Subst} (fresh : FreshFor use outer) :
    ∀ (patterns values : List Atom) (bindings : Subst),
      SpaceSemantics.matchValue.matchValues (renameKeys use bindings ++ outer)
          (patterns.map (rename use)) values =
        (SpaceSemantics.matchValue.matchValues bindings patterns values).map
          fun bound => renameKeys use bound ++ outer
  | [], values, bindings => by cases values <;> simp [SpaceSemantics.matchValue.matchValues]
  | first :: rest, [], bindings => by simp [SpaceSemantics.matchValue.matchValues]
  | first :: rest, value :: remaining, bindings => by
      simp only [List.map_cons, SpaceSemantics.matchValue.matchValues]
      rw [matchValue_rename fresh (Unifying.atomSize first) bindings first value le_rfl]
      cases SpaceSemantics.matchValue bindings first value with
      | none => rfl
      | some middle =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          exact matchValues_rename fresh rest remaining middle

theorem matchedBodies_eq_renamedClauses {outer : Subst} {values : List Atom} :
    ∀ (use : Nat) (chosen : List SpaceSemantics.Equation), (∀ step, FreshFor (use + step) outer) →
      Unifying.matchedBodies outer values use chosen = renamedClauses outer values use chosen
  | _, [], _ => rfl
  | use, equation :: rest, fresh => by
      have restFresh : ∀ step, FreshFor (use + 1 + step) outer := by
        intro step
        have := fresh (1 + step)
        rwa [← Nat.add_assoc] at this
      have here := matchValues_rename (use := use) (outer := outer) (by simpa using fresh 0)
        equation.arguments values []
      rw [renameKeys_nil, List.nil_append] at here
      simp only [Unifying.matchedBodies, renamedClauses, here]
      cases SpaceSemantics.matchValue.matchValues [] equation.arguments values with
      | none => exact matchedBodies_eq_renamedClauses (use + 1) rest restFresh
      | some bound =>
          simp only [Option.map_some]
          rw [matchedBodies_eq_renamedClauses (use + 1) rest restFresh]

/-- **A call with ground arguments selects what matching selects, renamed apart**:
the same equations, in the same order, each body renamed for its use and run
under the matching substitution of its argument patterns (the substitution
`Eval.clauses` gives), renamed and followed by the caller's bindings. -/
theorem selections_eq_renamedClauses {outer : Subst} {values : List Atom}
    (range : GroundRange outer) (ground : ∀ value ∈ values, isGroundAtom value = true)
    (use : Nat) (chosen : List SpaceSemantics.Equation) (fresh : ∀ step, FreshFor (use + step) outer) :
    Unifying.selections outer values use chosen = some (renamedClauses outer values use chosen) := by
  rw [Unifying.selections_ground range ground, matchedBodies_eq_renamedClauses use chosen fresh]


end Mettapedia.Languages.MeTTa.PeTTa.Unifying
