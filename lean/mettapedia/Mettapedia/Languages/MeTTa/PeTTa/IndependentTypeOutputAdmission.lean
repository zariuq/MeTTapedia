import Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeTraversal

/-!
# Name support of recursive intrinsic type queries

Fresh allocation locality and the recursive coordinate law establish that a
query cannot invent an absent caller or parent name. This is the support
condition needed when an output alias is moved across child queries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Admission

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.UnificationRenaming
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open SupplyLocality

private def names (terms : List TypeTerm) : Finset Nat :=
  terms.foldr (fun term tail => term.freeVars ∪ tail) ∅

private theorem name_mem {terms : List TypeTerm} {term : TypeTerm} {name : Nat}
    (present : term ∈ terms) (occurs : name ∈ term.freeVars) : name ∈ names terms := by
  induction terms with
  | nil => simp at present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Finset.mem_union_left _ occurs
      · exact Finset.mem_union_right _ (ih later)

/-- The caller namespace has a name outside any finite set of terms. -/
theorem unused_caller (terms : List TypeTerm) :
    ∃ slot, ∀ term ∈ terms, callerName slot ∉ term.freeVars := by
  let slot := (names terms).sup id + 1
  refine ⟨slot, ?_⟩
  intro term present occurs
  have small : callerName slot ≤ (names terms).sup id :=
    Finset.le_sup (f := id) (name_mem present occurs)
  have large : slot ≤ callerName slot := Nat.right_le_pair 0 slot
  dsimp only [slot] at small large
  omega

/-- Renaming two absent variables changes no part of a term. -/
theorem swap_fixes_term (left right : Nat) (term : TypeTerm)
    (leftAbsent : left ∉ term.freeVars) (rightAbsent : right ∉ term.freeVars) :
    Coordinates.R (Equiv.swap left right) term = term := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  have notLeft : name ≠ left := fun equal => leftAbsent (equal ▸ occurs)
  have notRight : name ≠ right := fun equal => rightAbsent (equal ▸ occurs)
  simp only [Equiv.swap_apply_of_ne_of_ne notLeft notRight]

private theorem map_fixes {α : Type} (f : α → α) (items : List α)
    (same : items.map f = items) : ∀ item ∈ items, f item = item := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at same
      intro item member
      rcases List.mem_cons.mp member with rfl | later
      · exact same.1
      · exact ih same.2 item later

/-- Every returned term is supported by the incoming operands and names
allocated below this invocation. Failed trials and ordered alternatives are
covered by the same concrete recursive execution theorem. -/
theorem run_excludes_name (library : List Declaration) (fuel : Nat) (path : Path)
    (subject : TypeTerm) (required : Option TypeTerm) (answers : List TypeTerm)
    (excluded : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ excluded)
    (subjectAbsent : excluded ∉ subject.freeVars)
    (requirementAbsent : ∀ term ∈ required.toList, excluded ∉ term.freeVars)
    (returned : run library freshSupply fuel path subject required = some answers) :
    ∀ answer ∈ answers, excluded ∉ answer.freeVars := by
  obtain ⟨slot, unused⟩ := unused_caller
    ((Term.var excluded) :: subject :: (required.toList ++ answers))
  let witness := callerName slot
  have distinct : excluded ≠ witness := by
    have fresh := unused (.var excluded) List.mem_cons_self
    simpa only [Term.freeVars, Finset.mem_singleton, ne_eq, eq_comm] using fresh
  have subjectFixed : Coordinates.R (Equiv.swap excluded witness) subject = subject :=
    swap_fixes_term excluded witness subject subjectAbsent
      (unused subject (by simp))
  have requiredFixed : required.map (Coordinates.R (Equiv.swap excluded witness)) = required := by
    cases required with
    | none => rfl
    | some term =>
        simp only [Option.map_some, Option.some.injEq]
        exact swap_fixes_term excluded witness term
          (requirementAbsent term (by simp)) (unused term (by simp))
  have supplyFixed : SuppliesAgreeAt path freshSupply
      (Coordinates.S (Equiv.swap excluded witness) freshSupply) := by
    intro stem childSlot
    dsimp only [Coordinates.S]
    symm
    exact Equiv.swap_apply_of_ne_of_ne (notAllocated stem childSlot)
      (fresh_supply_separate _ childSlot slot)
  have same := run_equivariant_of_local_supply (Equiv.swap excluded witness)
    library freshSupply freshSupply fuel path supplyFixed subject required
  rw [subjectFixed, requiredFixed, returned] at same
  simp only [Option.map_some, Option.some.injEq] at same
  have fixes : ∀ answer ∈ answers,
      Coordinates.R (Equiv.swap excluded witness) answer = answer := by
    exact map_fixes _ answers same.symm
  intro answer present occurs
  have nameFixed := Subst.var_fixed_of_applyTerm_eq_self (fixes answer present)
    excluded occurs
  have impossible : witness = excluded := by
    simpa only [Equiv.swap_apply_left, Term.var.injEq] using nameFixed
  exact distinct impossible.symm

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Admission
