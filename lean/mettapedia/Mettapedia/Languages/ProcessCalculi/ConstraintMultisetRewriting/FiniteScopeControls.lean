import Mettapedia.OSLF.Syntax.BindingScopePullbackFinite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshAnswerControls

/-!
# Executed finite-scope intersection controls

Computed interfaces cover a genuine overlap, no overlap, reordered distinct
sorts, and repeated parameter slots. Equal declared sorts do not identify
different ambient variables. Repeated slots remain distinct when their pair
identities differ, even if one projection shares a variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FiniteScope.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ScopePullback.Finite (sortOf rows leftValue rightValue pair_mem)
open ScopePullback.Controls (base leftMap rightMap)
open ContextualFlexPair.Controls (others)

abbrev overlap := Mettapedia.OSLF.Binding.ScopePullback.Finite.build leftMap rightMap

theorem overlap_context_is_the_single_shared_parameter : overlap.context = [()] := by
  with_unfolding_all rfl

def overlapPair : Mettapedia.OSLF.Binding.ScopePullback.Finite.Pair leftMap rightMap :=
  ⟨(⟨1, by decide⟩, ⟨0, by decide⟩), rfl⟩

def overlapParameter : Var overlap.context () :=
  ContextRows.select (Mettapedia.OSLF.Binding.ScopePullback.Finite.sortOf leftMap rightMap)
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.rows leftMap rightMap) overlapPair
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.pair_mem leftMap rightMap overlapPair)

theorem computed_projection_selects_the_left_second_parameter :
    overlap.toLeft () overlapParameter = Var.succ Var.zero :=
  ContextRows.project_select (S := base) (sortOf leftMap rightMap) (rows leftMap rightMap)
    (leftValue leftMap rightMap) overlapPair (pair_mem leftMap rightMap overlapPair)

theorem computed_projection_selects_the_right_first_parameter :
    overlap.toRight () overlapParameter = Var.zero :=
  ContextRows.project_select (S := base) (sortOf leftMap rightMap) (rows leftMap rightMap)
    (rightValue leftMap rightMap) overlapPair (pair_mem leftMap rightMap overlapPair)

theorem computed_fresh_answer_has_the_retained_principal_interface
    (observed : List (Term
      (ContextualFamily.signature base (ContextualFreshAnswer.oldDeclarations [(), ()] [(), ()] () others))
      [(), (), ()] ())) :
    (ContextualFamilies.action
      (ContextualFreshAnswer.activeDeclarations [(), ()] [(), ()] overlap.context () others)
      [(), (), ()] ()).PrincipalOn
        (ContextualFreshAnswer.problem (left := leftMap) (right := rightMap) overlap.context () others)
        (ContextualFreshAnswer.answer overlap () others)
        (observed.map (ContextualFamily.instantiate
          (ContextualFreshAnswer.includeOld (L := [(), ()]) (R := [(), ()]) overlap.context () others))) :=
  ContextualFreshAnswer.principal_on overlap () others observed

def repeatedLeft : Ren base [(), ()] [()]
  | _, .zero => .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

def singleRight : Ren base [()] [()]
  | _, .zero => .zero
  | _, .succ impossible => nomatch impossible

abbrev repeated := Mettapedia.OSLF.Binding.ScopePullback.Finite.build repeatedLeft singleRight

theorem repeated_slots_retain_both_pair_identities : repeated.context = [(), ()] := by
  change (Mettapedia.OSLF.Binding.ScopePullback.Finite.rows repeatedLeft singleRight).map
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.sortOf repeatedLeft singleRight) = _
  simp only [Mettapedia.OSLF.Binding.ScopePullback.Finite.rows, Finset.sort, Multiset.sort,
    List.mergeSort_eq_insertionSort]
  with_unfolding_all rfl

def firstPair : Mettapedia.OSLF.Binding.ScopePullback.Finite.Pair repeatedLeft singleRight :=
  ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), rfl⟩

def secondPair : Mettapedia.OSLF.Binding.ScopePullback.Finite.Pair repeatedLeft singleRight :=
  ⟨(⟨1, by decide⟩, ⟨0, by decide⟩), rfl⟩

def firstRepeated : Var repeated.context () :=
  ContextRows.select (Mettapedia.OSLF.Binding.ScopePullback.Finite.sortOf repeatedLeft singleRight)
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.rows repeatedLeft singleRight) firstPair
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.pair_mem repeatedLeft singleRight firstPair)

def secondRepeated : Var repeated.context () :=
  ContextRows.select (Mettapedia.OSLF.Binding.ScopePullback.Finite.sortOf repeatedLeft singleRight)
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.rows repeatedLeft singleRight) secondPair
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.pair_mem repeatedLeft singleRight secondPair)

theorem right_projection_can_share_a_variable :
    repeated.toRight () firstRepeated = repeated.toRight () secondRepeated := by
  have first : repeated.toRight () firstRepeated = Var.zero :=
    ContextRows.project_select (S := base) (sortOf repeatedLeft singleRight) (rows repeatedLeft singleRight)
      (rightValue repeatedLeft singleRight) firstPair (pair_mem repeatedLeft singleRight firstPair)
  have second : repeated.toRight () secondRepeated = Var.zero :=
    ContextRows.project_select (S := base) (sortOf repeatedLeft singleRight) (rows repeatedLeft singleRight)
      (rightValue repeatedLeft singleRight) secondPair (pair_mem repeatedLeft singleRight secondPair)
  exact first.trans second.symm

theorem left_projection_still_distinguishes_the_slots :
    repeated.toLeft () firstRepeated ≠ repeated.toLeft () secondRepeated := by
  have first : repeated.toLeft () firstRepeated = Var.zero :=
    ContextRows.project_select (S := base) (sortOf repeatedLeft singleRight) (rows repeatedLeft singleRight)
      (leftValue repeatedLeft singleRight) firstPair (pair_mem repeatedLeft singleRight firstPair)
  have second : repeated.toLeft () secondRepeated = Var.succ Var.zero :=
    ContextRows.project_select (S := base) (sortOf repeatedLeft singleRight) (rows repeatedLeft singleRight)
      (leftValue repeatedLeft singleRight) secondPair (pair_mem repeatedLeft singleRight secondPair)
  rw [first, second]
  intro same
  cases same

theorem a_repeated_flexible_pair_has_a_sound_generated_answer :
    ContextualFamily.instantiate (ContextualFlexPair.answer repeated () others)
        (rename (S := ContextualFamily.signature base
          (ContextualFlexPair.sourceDeclarations [(), ()] [()] () others)) repeatedLeft
          (ContextualFamily.generator
            (ContextualFlexPair.sourceDeclarations [(), ()] [()] () others) (.inl false))) =
      ContextualFamily.instantiate (ContextualFlexPair.answer repeated () others)
        (rename (S := ContextualFamily.signature base
          (ContextualFlexPair.sourceDeclarations [(), ()] [()] () others)) singleRight
          (ContextualFamily.generator
            (ContextualFlexPair.sourceDeclarations [(), ()] [()] () others) (.inl true))) :=
  ContextualFlexPair.sound repeated () others

def nullary : Ren base [] [()] := fun _ position => nomatch position

theorem nullary_and_unary_interfaces_have_no_shared_parameter :
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.build nullary singleRight).context = [] := by
  with_unfolding_all rfl

theorem an_unrecoverable_flexible_pair_gets_a_shared_nullary_helper :
    ContextualFamily.instantiate
        (ContextualFlexPair.answer (Mettapedia.OSLF.Binding.ScopePullback.Finite.build nullary singleRight) () others)
        (rename (S := ContextualFamily.signature base
          (ContextualFlexPair.sourceDeclarations [] [()] () others)) nullary
          (ContextualFamily.generator
            (ContextualFlexPair.sourceDeclarations [] [()] () others) (.inl false))) =
      ContextualFamily.instantiate
        (ContextualFlexPair.answer (Mettapedia.OSLF.Binding.ScopePullback.Finite.build nullary singleRight) () others)
        (rename (S := ContextualFamily.signature base
          (ContextualFlexPair.sourceDeclarations [] [()] () others)) singleRight
          (ContextualFamily.generator
            (ContextualFlexPair.sourceDeclarations [] [()] () others) (.inl true))) :=
  ContextualFlexPair.sound (Mettapedia.OSLF.Binding.ScopePullback.Finite.build nullary singleRight) () others

def twoSorts : Signature where
  Srt := Bool
  Op _ := Unit
  arity _ := []

def typedLeft : Ren twoSorts [false, true] [true, false, true]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

def typedRight : Ren twoSorts [true, false] [true, false, true]
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero
  | _, .succ (.succ impossible) => nomatch impossible

theorem computed_interfaces_preserve_both_declared_sorts :
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.build typedLeft typedRight).context = [false, true] := by
  change (Mettapedia.OSLF.Binding.ScopePullback.Finite.rows typedLeft typedRight).map
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.sortOf typedLeft typedRight) = _
  simp only [Mettapedia.OSLF.Binding.ScopePullback.Finite.rows, Finset.sort, Multiset.sort,
    List.mergeSort_eq_insertionSort]
  with_unfolding_all rfl

def firstTrue : Ren twoSorts [true] [true, false, true]
  | _, .zero => .zero
  | _, .succ impossible => nomatch impossible

def lastTrue : Ren twoSorts [true] [true, false, true]
  | _, .zero => .succ (.succ .zero)
  | _, .succ impossible => nomatch impossible

theorem equal_sorts_do_not_merge_different_ambient_positions :
    (Mettapedia.OSLF.Binding.ScopePullback.Finite.build firstTrue lastTrue).context = [] := by
  with_unfolding_all rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FiniteScope.Controls
