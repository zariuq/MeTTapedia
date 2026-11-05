import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedSource

/-!
# Typed projections of the actual EU seed append

Each captured goal occurrence contributes its satisfaction row followed by
its round-zero frontier row. These laws retain that bag and its order while
identifying the graph and other source views left unchanged by seeding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedViews

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows graphView satisfactionView frontSelect)
open CTLUntilSeedSource (seedRows)

variable {Label : Type} [DecidableEq Label]

omit [DecidableEq Label] in
theorem graph_unchanged (label : Label) (goals : List Nat) (rows : List (Row Label)) :
    graphView (rows ++ goals.flatMap (seedRows label)) = graphView rows := by
  simp [graphView, List.filterMap_flatMap, seedRows]

theorem satisfaction_other (label observed : Label) (different : label ≠ observed)
    (goals : List Nat) (rows : List (Row Label)) :
    satisfactionView observed (rows ++ goals.flatMap (seedRows label)) = satisfactionView observed rows := by
  simp [satisfactionView, List.filterMap_flatMap, seedRows, different]

theorem satisfaction_output (label : Label) (goals : List Nat) (rows : List (Row Label)) :
    satisfactionView label (rows ++ goals.flatMap (seedRows label)) = satisfactionView label rows ++ goals := by
  simp [satisfactionView, List.filterMap_flatMap, seedRows]

theorem frontier_zero (label : Label) (goals : List Nat) (rows : List (Row Label)) :
    (rows ++ goals.flatMap (seedRows label)).filterMap (frontSelect label 0) =
      rows.filterMap (frontSelect label 0) ++ goals := by
  simp [List.filterMap_flatMap, seedRows, List.filterMap_cons, frontSelect]

theorem frontier_other_round (label : Label) (round : Nat) (nonzero : round ≠ 0)
    (goals : List Nat) (rows : List (Row Label)) :
    (rows ++ goals.flatMap (seedRows label)).filterMap (frontSelect label round) =
      rows.filterMap (frontSelect label round) := by
  simp [List.filterMap_flatMap, seedRows, frontSelect, Ne.symm nonzero]

theorem frontier_other_label (label observed : Label) (different : label ≠ observed) (round : Nat)
    (goals : List Nat) (rows : List (Row Label)) :
    (rows ++ goals.flatMap (seedRows label)).filterMap (frontSelect observed round) =
      rows.filterMap (frontSelect observed round) := by
  simp [List.filterMap_flatMap, seedRows, frontSelect, different]

omit [DecidableEq Label] in
theorem admitted_append (label : Label) (goals : List Nat) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    ∀ row ∈ rows ++ goals.flatMap (seedRows label), row.admitted := by
  intro row member
  rcases List.mem_append.mp member with old | added
  · exact admitted row old
  · obtain ⟨node, _, selected⟩ := List.mem_flatMap.mp added
    simp only [seedRows, List.mem_cons, List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl <;> trivial

omit [DecidableEq Label] in
theorem decode_appended (codec : Codec Label) (label : Label) (goals : List Nat)
    (atoms : List Atom) (rows : List (Row Label)) (decoded : decodeRows codec atoms = some rows) :
    decodeRows codec (atoms ++ (goals.flatMap (seedRows label)).map (render codec)) =
      some (rows ++ goals.flatMap (seedRows label)) := by
  obtain ⟨rendered, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  rw [← rendered, ← List.map_append]
  exact CTLUntilMixedStore.decode_rows_complete codec _ (admitted_append label goals rows admitted)

namespace Controls

theorem duplicate_goals_remain_duplicate_in_both_views :
    satisfactionView (10 : Nat) ([1, 1, 2].flatMap (seedRows 10)) = [1, 1, 2] ∧
      ([1, 1, 2].flatMap (seedRows (10 : Nat))).filterMap (frontSelect 10 0) = [1, 1, 2] := by decide +kernel

theorem deduplicating_goals_changes_the_seed_view :
    satisfactionView (10 : Nat) ([1, 1, 2].flatMap (seedRows 10)) ≠
      satisfactionView (10 : Nat) ([1, 2].flatMap (seedRows 10)) := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSeedViews
