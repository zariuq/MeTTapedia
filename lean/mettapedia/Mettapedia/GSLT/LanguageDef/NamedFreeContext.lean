import Mettapedia.GSLT.LanguageDef.BindingSignature

/-!
# Finite named contexts from used free names

An authored pattern has a finite list of free names, while a sorted binding
signature uses context positions. This module builds a sorted intrinsic
context from exactly those names with assignments in the supplied free-type
context. It introduces no new constructor declarations or typing rules.
-/

namespace Mettapedia.GSLT.LanguageDef.NamedFreeContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

set_option autoImplicit false

/-- The intrinsic context contains the sorts of the recorded named entries
in the same order. No extra sort or name inventory is introduced. -/
def contextSorts (entries : List (String × TypeExpr)) : List TypeExpr :=
  entries.map Prod.snd

/-- Read the name at one intrinsically sorted position of the entry list. -/
def nameAt : (entries : List (String × TypeExpr)) →
    {sort : TypeExpr} → Var (contextSorts entries) sort → String
  | [], _, position => nomatch position
  | (name, _) :: _, _, .zero => name
  | _ :: tail, _, .succ position => nameAt tail position

/-- The same naming as an explicitly sorted context map, for consumers that
use the binding-signature renaming interface. -/
def names (entries : List (String × TypeExpr)) :
    (sort : TypeExpr) → Var (contextSorts entries) sort → String :=
  fun _ position => nameAt entries position

/-- Find an intrinsically sorted position by its authored name and sort.
This computes a position rather than selecting one from an existence proof;
for duplicate entries it chooses the first matching occurrence. -/
def lookupPosition? : (entries : List (String × TypeExpr)) →
    (name : String) → (sort : TypeExpr) →
      Option (Var (contextSorts entries) sort)
  | [], _, _ => none
  | (entryName, entrySort) :: rest, name, sort =>
      if _sameName : entryName = name then
        if sameSort : entrySort = sort then
          some (Eq.mp (congrArg (Var (entrySort :: contextSorts rest)) sameSort)
            Var.zero)
        else
          (lookupPosition? rest name sort).map Var.succ
      else
        (lookupPosition? rest name sort).map Var.succ

/-- Computed lookup succeeds exactly for an entry with the requested name
and sort. Wrong-sort aliases do not count as successful lookup. -/
theorem lookupPosition?_isSome_iff :
    ∀ (entries : List (String × TypeExpr)) (name : String) (sort : TypeExpr),
      (lookupPosition? entries name sort).isSome = true ↔
        (name, sort) ∈ entries := by
  intro entries
  induction entries with
  | nil =>
      intro name sort
      simp [lookupPosition?]
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort
      by_cases sameName : headName = name
      · by_cases sameSort : headSort = sort
        · simp [lookupPosition?, sameName, sameSort]
        · simp [lookupPosition?, sameName, sameSort,
            List.mem_cons, Prod.mk.injEq]
          have noHead : sort ≠ headSort := Ne.symm sameSort
          simp only [noHead, false_or]
          cases found : lookupPosition? tail name sort <;>
            simpa [found, Option.map, Option.isSome] using ih name sort
      · simp [lookupPosition?, sameName,
          List.mem_cons, Prod.mk.injEq]
        have noHead : name ≠ headName := Ne.symm sameName
        simp only [noHead, false_and, false_or]
        cases found : lookupPosition? tail name sort <;>
          simpa [found, Option.map, Option.isSome] using ih name sort

/-- A computed position really has the requested authored name. Its sort is
already enforced by the result type of `lookupPosition?`. -/
theorem lookupPosition?_sound :
    ∀ (entries : List (String × TypeExpr)) (name : String) (sort : TypeExpr)
      {position : Var (contextSorts entries) sort},
      lookupPosition? entries name sort = some position →
        nameAt entries position = name := by
  intro entries
  induction entries with
  | nil =>
      intro name sort position accepted
      simp [lookupPosition?] at accepted
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort position accepted
      by_cases sameName : headName = name
      · by_cases sameSort : headSort = sort
        · subst sort
          simp [lookupPosition?, sameName] at accepted
          subst position
          exact sameName
        · cases found : lookupPosition? tail name sort with
          | none => simp [lookupPosition?, sameName, sameSort, found,
              Option.map] at accepted
          | some prior =>
              simp [lookupPosition?, sameName, sameSort, found,
                Option.map] at accepted
              cases accepted
              exact ih name sort found
      · cases found : lookupPosition? tail name sort with
        | none => simp [lookupPosition?, sameName, found, Option.map] at accepted
        | some prior =>
            simp [lookupPosition?, sameName, found, Option.map] at accepted
            cases accepted
            exact ih name sort found

/-- A total executable construction from the names actually used by a
pattern. Names lacking a free-type assignment are omitted; a checked typed
pattern supplies assignments for all names that matter. -/
def fromUsed (free : FreeTypeContext) : List String → List (String × TypeExpr)
  | [] => []
  | name :: rest =>
      match free name with
      | none => fromUsed free rest
      | some sort => (name, sort) :: fromUsed free rest

/-- No finite name list acquires an intrinsic position from an empty typing
assignment. -/
theorem fromUsed_empty (used : List String) :
    fromUsed FreeTypeContext.empty used = [] := by
  induction used with
  | nil => rfl
  | cons name rest ih =>
      simpa [fromUsed, FreeTypeContext.empty] using ih

/-- Every assigned input name appears with its assigned sort in the computed
entry list. Duplicate occurrences are retained, so no deduplication policy
is silently imposed. -/
theorem fromUsed_has_assigned_pair (free : FreeTypeContext) :
    ∀ (used : List String) (name : String) (sort : TypeExpr),
      name ∈ used → free name = some sort →
        (name, sort) ∈ fromUsed free used := by
  intro used
  induction used with
  | nil =>
      intro name sort membership _
      cases membership
  | cons head tail ih =>
      intro name sort membership assigned
      rcases List.mem_cons.mp membership with same | later
      · subst name
        simp [fromUsed, assigned]
      · cases found : free head with
        | none => simpa [fromUsed, found] using ih name sort later assigned
        | some headSort =>
            simpa [fromUsed, found] using
              (List.mem_cons_of_mem (head, headSort)
                (ih name sort later assigned))

/-- A pair in the finite entry list has a sorted intrinsic position whose
name is exactly the pair's first coordinate. -/
theorem member_has_position :
    ∀ (entries : List (String × TypeExpr)) {name : String} {sort : TypeExpr},
      (name, sort) ∈ entries →
        ∃ position : Var (contextSorts entries) sort,
          nameAt entries position = name := by
  intro entries
  induction entries with
  | nil =>
      intro name sort membership
      cases membership
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro name sort membership
      rcases List.mem_cons.mp membership with same | later
      · cases Prod.mk.inj same with
        | intro nameEq sortEq =>
            subst name
            subst sort
            exact ⟨.zero, rfl⟩
      · obtain ⟨position, named⟩ := ih later
        exact ⟨.succ position, named⟩

/-- Every intrinsic position points to an actual pair in its entry list. -/
theorem position_pair_mem :
    ∀ (entries : List (String × TypeExpr)) (sort : TypeExpr)
      (position : Var (contextSorts entries) sort),
      (nameAt entries position, sort) ∈ entries := by
  intro entries
  induction entries with
  | nil =>
      intro sort position
      nomatch position
  | cons head tail ih =>
      rcases head with ⟨headName, headSort⟩
      intro sort position
      cases position with
      | zero => exact List.mem_cons_self
      | succ earlier => exact List.mem_cons_of_mem _ (ih sort earlier)

/-- A generated pair's name really came from the input name list. -/
theorem fromUsed_pair_name_mem (free : FreeTypeContext) :
    ∀ (used : List String) (entry : String × TypeExpr),
      entry ∈ fromUsed free used → entry.1 ∈ used := by
  intro used
  induction used with
  | nil =>
      intro entry membership
      cases membership
  | cons head tail ih =>
      intro entry membership
      cases found : free head with
      | none =>
          exact List.mem_cons_of_mem head
            (ih entry (by simpa [fromUsed, found] using membership))
      | some sort =>
          have member : entry = (head, sort) ∨
              entry ∈ fromUsed free tail := by
            simpa [fromUsed, found] using membership
          rcases member with same | later
          · subst entry
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem head (ih entry later)

/-- A typed used name always resolves in the computed intrinsic context. -/
theorem fromUsed_resolves (free : FreeTypeContext) (used : List String)
    {name : String} {sort : TypeExpr}
    (membership : name ∈ used) (assigned : free name = some sort) :
    ∃ position : Var (contextSorts (fromUsed free used)) sort,
      nameAt (fromUsed free used) position = name :=
  member_has_position _
    (fromUsed_has_assigned_pair free used name sort membership assigned)

/-- The same resolution is executable: a used name with an assignment gives
a computed intrinsic position, not merely an existential one. -/
theorem lookupPosition?_fromUsed_complete (free : FreeTypeContext)
    (used : List String) {name : String} {sort : TypeExpr}
    (membership : name ∈ used) (assigned : free name = some sort) :
    (lookupPosition? (fromUsed free used) name sort).isSome = true :=
  (lookupPosition?_isSome_iff _ _ _).mpr
    (fromUsed_has_assigned_pair free used name sort membership assigned)

/-- No generated context position names something outside the input list. -/
theorem fromUsed_positions_named_in_input (free : FreeTypeContext)
    (used : List String) (sort : TypeExpr)
    (position : Var (contextSorts (fromUsed free used)) sort) :
    nameAt (fromUsed free used) position ∈ used :=
  fromUsed_pair_name_mem free used _
    (position_pair_mem (fromUsed free used) sort position)

example : (lookupPosition?
    [("w", .base "State"), ("q", .base "Query")]
    "q" (.base "Query")).isSome = true := by
  decide +kernel

example : lookupPosition?
    [("w", .base "State"), ("q", .base "Query")]
    "q" (.base "State") = none := by
  decide +kernel

example : (lookupPosition?
    [("w", .base "State"), ("w", .base "Query")]
    "w" (.base "Query")).isSome = true := by
  decide +kernel

#print axioms fromUsed_resolves
#print axioms fromUsed_positions_named_in_input
#print axioms lookupPosition?_isSome_iff
#print axioms lookupPosition?_sound
#print axioms lookupPosition?_fromUsed_complete

end Mettapedia.GSLT.LanguageDef.NamedFreeContext
