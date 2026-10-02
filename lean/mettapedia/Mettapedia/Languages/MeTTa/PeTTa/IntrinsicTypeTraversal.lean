import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput

/-!
# Allocation locality of intrinsic type traversal

An intrinsic query allocates only below its invocation path. Its function
trials, negative probes, structural products and refinement branches retain
this property. Consequently a change to an unrelated allocation subtree
cannot affect the query, including its ordered answer multiplicity.

The statements below concern the existing recursive intrinsic service.
They do not introduce another typing relation or assume its answers agree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SupplyLocality

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration)

/-- Paths extend by prepending; `base` is the invocation's suffix. -/
def SuppliesAgreeAt (base : Path) (left right : Supply) : Prop :=
  ∀ stem slot, left (stem ++ base) slot = right (stem ++ base) slot

/-- Equality of recursive services on the invocation's allocation subtree. -/
def QueriesAgreeAt (base : Path) (left right : Query) : Prop :=
  ∀ stem subject required,
    left (stem ++ base) subject required = right (stem ++ base) subject required

theorem SuppliesAgreeAt.prepend {base : Path} {left right : Supply}
    (same : SuppliesAgreeAt base left right) (stem : Path) :
    SuppliesAgreeAt (stem ++ base) left right := by
  intro more slot
  simpa only [List.append_assoc] using same (more ++ stem) slot

theorem QueriesAgreeAt.prepend {base : Path} {left right : Query}
    (same : QueriesAgreeAt base left right) (stem : Path) :
    QueriesAgreeAt (stem ++ base) left right := by
  intro more subject required
  simpa only [List.append_assoc] using same (more ++ stem) subject required

theorem declarations_eq (library : List Declaration) (left right : Supply)
    (path : Path) (same : SuppliesAgreeAt path left right) (subject : TypeTerm) :
    declarations library left path subject = declarations library right path subject := by
  cases subject with
  | var _ => rfl
  | app _ _ => rfl
  | const scalar =>
      cases scalar with
      | number _ => rfl
      | string _ => rfl
      | boolean _ => rfl
      | symbol name =>
          unfold declarations
          apply List.flatMap_congr
          intro declaration _
          have names : left (1 :: declaration.occurrence :: path) =
              right (1 :: declaration.occurrence :: path) := by
            funext slot
            exact same [1, declaration.occurrence] slot
          rw [names]

theorem arguments_eq (left right : Query) (path : Path)
    (same : QueriesAgreeAt path left right) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm) (store : Subst signature) :
    arguments left path position pending result store =
      arguments right path position pending result store := by
  induction pending generalizing position store with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨subject, formal⟩
      simp only [arguments]
      by_cases rootVar : isVariable (store.applyTerm subject) = true
      · simp only [rootVar, ↓reduceIte]
        exact ih (position + 1) store
      · simp only [rootVar, Bool.false_eq_true, ↓reduceIte]
        have child : left (0 :: position :: path) (store.applyTerm subject)
            (some (store.applyTerm formal)) =
            right (0 :: position :: path) (store.applyTerm subject)
              (some (store.applyTerm formal)) :=
          same [0, position] (store.applyTerm subject) (some (store.applyTerm formal))
        rw [child]
        cases right (0 :: position :: path) (store.applyTerm subject)
            (some (store.applyTerm formal)) with
        | none => rfl
        | some candidates =>
            dsimp only [bind, Option.bind]
            apply Coordinates.collect_congr
            intro candidate _
            cases unifyTotal [(candidate, store.applyTerm formal)] with
            | none => rfl
            | some refinement => exact ih (position + 1) (refinement ∘ₛ store)

theorem functions_eq (library : List Declaration) (leftSupply rightSupply : Supply)
    (left right : Query) (path : Path)
    (supplySame : SuppliesAgreeAt path leftSupply rightSupply)
    (querySame : QueriesAgreeAt path left right)
    (items : List TypeTerm) (required : Option TypeTerm) :
    functions library leftSupply left path items required =
      functions library rightSupply right path items required := by
  cases items with
  | nil => rfl
  | cons head actuals =>
      simp only [functions, declarations_eq library leftSupply rightSupply path supplySame]
      apply Coordinates.collect_congr
      intro scheme _
      cases callParts actuals.length scheme with
      | none => rfl
      | some pair =>
          rcases pair with ⟨domains, result⟩
          cases required with
          | none =>
              exact arguments_eq left right path querySame 0
                (actuals.zip domains) result (Subst.id signature)
          | some target =>
              dsimp only
              cases unifyTotal [(result, target)] with
              | none => rfl
              | some initial =>
                  exact arguments_eq left right path querySame 0
                    (actuals.zip domains) result initial

theorem freshRows_eq (left right : Query) (path : Path)
    (same : QueriesAgreeAt path left right) (position : Nat) (items : List TypeTerm) :
    freshRows left path position items = freshRows right path position items := by
  induction items generalizing position with
  | nil => rfl
  | cons subject rest ih =>
      simp only [freshRows]
      have child : left (0 :: position :: path) subject none =
          right (0 :: position :: path) subject none := same [0, position] subject none
      rw [child, ih]

theorem structural_eq (leftSupply rightSupply : Supply) (left right : Query)
    (path : Path) (supplySame : SuppliesAgreeAt path leftSupply rightSupply)
    (querySame : QueriesAgreeAt path left right)
    (items : List TypeTerm) (required : Option TypeTerm) :
    structural leftSupply left path items required =
      structural rightSupply right path items required := by
  have childSame : QueriesAgreeAt (4 :: path) left right := querySame.prepend [4]
  cases required with
  | none =>
      simp only [structural, freshRows_eq left right (4 :: path) childSame]
  | some target =>
      have names : leftSupply (3 :: path) = rightSupply (3 :: path) := by
        funext slot
        exact supplySame [3] slot
      simp only [structural, names]
      split
      · rfl
      · exact arguments_eq left right (4 :: path) childSame 0 _ _ _

theorem expression_eq (library : List Declaration) (leftSupply rightSupply : Supply)
    (left right : Query) (path : Path)
    (supplySame : SuppliesAgreeAt path leftSupply rightSupply)
    (querySame : QueriesAgreeAt path left right)
    (items : List TypeTerm) (required : Option TypeTerm) :
    expression library leftSupply left path items required =
      expression library rightSupply right path items required := by
  unfold expression
  simp only [functions_eq library leftSupply rightSupply left right path
    supplySame querySame, structural_eq leftSupply rightSupply left right path
    supplySame querySame]

theorem step_eq (library : List Declaration) (leftSupply rightSupply : Supply)
    (left right : Query) (path : Path)
    (supplySame : SuppliesAgreeAt path leftSupply rightSupply)
    (querySame : QueriesAgreeAt path left right)
    (subject : TypeTerm) (required : Option TypeTerm) :
    step library leftSupply left path subject required =
      step library rightSupply right path subject required := by
  have variableName := supplySame [5] 0
  simp only [List.cons_append, List.nil_append] at variableName
  unfold step
  rw [variableName]
  simp only [declarations_eq library leftSupply rightSupply path supplySame,
    expression_eq library leftSupply rightSupply left right path supplySame querySame]

/-- No allocation outside this invocation's subtree can influence the
recursive query, even through an unsuccessful signature trial or probe. -/
theorem run_eq_of_supply_suffix (library : List Declaration)
    (left right : Supply) (fuel : Nat) (path : Path)
    (same : SuppliesAgreeAt path left right)
    (subject : TypeTerm) (required : Option TypeTerm) :
    run library left fuel path subject required =
      run library right fuel path subject required := by
  induction fuel generalizing path subject required with
  | zero => rfl
  | succ fuel ih =>
      apply step_eq library left right (run library left fuel)
        (run library right fuel) path same
      intro stem child target
      exact ih (stem ++ path) (same.prepend stem) child target

/-- Coordinate transport needs agreement only on the queried allocation
subtree; the rest of the fresh-name supply may remain unchanged. -/
theorem run_equivariant_of_local_supply (names : Nat ≃ Nat)
    (library : List Declaration) (source localSupply : Supply)
    (fuel : Nat) (path : Path)
    (same : SuppliesAgreeAt path localSupply (Coordinates.S names source))
    (subject : TypeTerm) (required : Option TypeTerm) :
    run library localSupply fuel path (Coordinates.R names subject)
        (required.map (Coordinates.R names)) =
      (run library source fuel path subject required).map
        (List.map (Coordinates.R names)) := by
  rw [run_eq_of_supply_suffix library localSupply (Coordinates.S names source)
    fuel path same]
  exact Coordinates.run_equivariant names library source fuel path subject required

/-- A parent signature allocation is outside every argument-query subtree. -/
theorem function_name_ne_recursive_supply (path stem : Path)
    (occurrence parentSlot position childSlot : Nat) :
    freshSupply (1 :: occurrence :: path) parentSlot ≠
      freshSupply (stem ++ 0 :: position :: path) childSlot := by
  intro equal
  have paths := (fresh_supply_injective _ _ _ _).mp equal |>.1
  have lengths := congrArg List.length paths
  simp only [List.length_cons, List.length_append] at lengths
  have empty : stem.length = 0 := by omega
  have stemNil : stem = [] := List.length_eq_zero_iff.mp empty
  subst stem
  simp at paths

/-- Swapping a parent signature name with a caller output leaves all child
allocations fixed. This is established from the actual allocation scheme. -/
theorem parent_swap_fixes_child_supply (path : Path)
    (occurrence parentSlot callerSlot position : Nat) :
    SuppliesAgreeAt (0 :: position :: path) freshSupply
      (Coordinates.S
        (Equiv.swap (freshSupply (1 :: occurrence :: path) parentSlot)
          (callerName callerSlot)) freshSupply) := by
  intro stem slot
  dsimp only [Coordinates.S]
  symm
  exact Equiv.swap_apply_of_ne_of_ne
    (Ne.symm (function_name_ne_recursive_supply path stem occurrence parentSlot position slot))
    (fresh_supply_separate _ slot callerSlot)

/-- The recursive query remains equivariant under the parent/caller swap
without renaming any of its fresh allocations. -/
theorem parent_swap_child_query (library : List Declaration) (fuel : Nat)
    (path : Path) (occurrence parentSlot callerSlot position : Nat)
    (subject : TypeTerm) (required : Option TypeTerm) :
    let names := Equiv.swap (freshSupply (1 :: occurrence :: path) parentSlot)
      (callerName callerSlot)
    run library freshSupply fuel (0 :: position :: path)
        (Coordinates.R names subject) (required.map (Coordinates.R names)) =
      (run library freshSupply fuel (0 :: position :: path) subject required).map
        (List.map (Coordinates.R names)) := by
  exact run_equivariant_of_local_supply _ library freshSupply freshSupply fuel _
    (parent_swap_fixes_child_supply path occurrence parentSlot callerSlot position)
    subject required

/-- Allocation inside the queried subtree is observable; locality cannot
be weakened to agreement merely on declarations or caller variables. -/
theorem current_allocation_is_observable :
    run [] (fun _ _ => 0) 1 [] (.var 7) none ≠
      run [] (fun _ _ => 1) 1 [] (.var 7) none := by
  simp [run, step, isVariable]

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SupplyLocality
