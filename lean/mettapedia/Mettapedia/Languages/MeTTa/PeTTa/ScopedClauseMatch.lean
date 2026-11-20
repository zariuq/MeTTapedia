import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRename

/-!
# Clause matching commutes with fresh instantiation

One scope extends every successful binding of a clause. Freshness excludes
the renamed variables from the caller. Later substitutions can refine a
shared binding without changing which clause variable it came from.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ScopedClauseMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst applySubst_compose)
open SpaceSemantics (matchValue)
open Unifying (freshName rename FreshFor renameKeys lookup_append_renamed)

private def suffix (ticket : Nat) : List Char := ("#" ++ toString ticket).toList.reverse

def checkFresh (ticket : Nat) (caller : Subst) : Bool :=
  caller.all fun binding =>
    decide (binding.1.toList.reverse.take (suffix ticket).length ≠ suffix ticket)

private theorem freshName_ends_with_ticket (ticket : Nat) (name : String) :
    (freshName ticket name).toList.reverse.take (suffix ticket).length = suffix ticket := by
  have joined : (freshName ticket name).toList.reverse = suffix ticket ++ name.toList.reverse := by
    simp [freshName, suffix, List.append_assoc]
  rw [joined, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

theorem checked_fresh (ticket : Nat) (caller : Subst)
    (checked : checkFresh ticket caller = true) : FreshFor ticket caller := by
  intro name
  unfold Subst.lookup
  cases found : caller.find? (fun binding => binding.1 == freshName ticket name) with
  | none => rfl
  | some binding =>
    have member := List.mem_of_find?_eq_some found
    have nameTest : (binding.1 == freshName ticket name) = true :=
      List.find?_some (p := fun entry : String × Atom => entry.1 == freshName ticket name) found
    have names : binding.1 = freshName ticket name := beq_iff_eq.mp nameTest
    have avoids : binding.1.toList.reverse.take (suffix ticket).length ≠ suffix ticket :=
      of_decide_eq_true ((List.all_eq_true.mp checked) binding member)
    exact False.elim (avoids (by rw [names]; exact freshName_ends_with_ticket ticket name))

structure FreshMatch (ticket : Nat) (caller : Subst) (patterns values : List Atom) where
  bindings : Subst
  canonical : matchValue.matchValues [] patterns values = some bindings
  fresh : FreshFor ticket caller

def FreshMatch.prepare (ticket : Nat) (caller : Subst) (patterns values : List Atom) :
    Option (FreshMatch ticket caller patterns values) :=
  if fresh : checkFresh ticket caller = true then
    match found : matchValue.matchValues [] patterns values with
    | none => none
    | some bindings => some ⟨bindings, found, checked_fresh ticket caller fresh⟩
  else none

def FreshMatch.environment {ticket : Nat} {caller : Subst} {patterns values : List Atom}
    (matched : FreshMatch ticket caller patterns values) : Subst :=
  renameKeys ticket matched.bindings ++ caller

theorem FreshMatch.match_renamed {ticket : Nat} {caller : Subst} {patterns values : List Atom}
    (matched : FreshMatch ticket caller patterns values) :
    matchValue.matchValues caller (patterns.map (rename ticket)) values = some matched.environment := by
  simpa [Unifying.renameKeys, matched.canonical, FreshMatch.environment] using
    Unifying.matchValues_rename matched.fresh patterns values []

theorem FreshMatch.lookup_slot {ticket : Nat} {caller : Subst} {patterns values : List Atom}
    (matched : FreshMatch ticket caller patterns values) (name : String) :
    matched.environment.lookup (freshName ticket name) = matched.bindings.lookup name :=
  lookup_append_renamed matched.fresh name

theorem FreshMatch.composed_slot {ticket : Nat} {caller : Subst} {patterns values : List Atom}
    (matched : FreshMatch ticket caller patterns values) (name : String) (later : Subst)
    {value : Atom} (bound : matched.bindings.lookup name = some value) :
    applySubst (matched.environment.compose later) (.var (freshName ticket name)) =
      applySubst later value := by
  rw [applySubst_compose]
  simp [applySubst, matched.lookup_slot name, bound]

namespace Controls

theorem caller_with_the_new_scope_is_refused :
    checkFresh 3 [("saved#3", .symbol "value")] = false := by decide +kernel

theorem a_repeated_source_variable_checks_both_occurrences :
    (FreshMatch.prepare 3 [] [.var "a", .var "a"] [.symbol "x", .symbol "x"]).isSome = true ∧
    (FreshMatch.prepare 3 [] [.var "a", .var "a"] [.symbol "x", .symbol "y"]).isNone = true := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.ScopedClauseMatch
