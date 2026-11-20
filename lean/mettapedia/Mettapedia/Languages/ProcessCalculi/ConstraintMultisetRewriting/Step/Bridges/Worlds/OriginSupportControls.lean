import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.OriginSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Controls

/-!
# Origin erasure on a concrete world execution

Two persistent copies of a rule supply four origin-decorated runs over one
specified two-firing base run. They project to the same world path, while
their held-origin words remain distinct. The projected world path still
contains both physical firings and reaches the actual two produced rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.OriginSupport.Controls

open RuleSyntax RuleSyntax.RuleOccurrences
open LiveRules.Origins LiveRules.Controls

theorem support_path_length (firstOrigin secondOrigin : Fin 2) :
    (worldPath _ _ _ offered_twice (selectedRun firstOrigin secondOrigin)).length = 2 :=
  worldPath_length _ _ _ offered_twice _

/-- Equality includes the entire represented execution path, not only the
set of final answers. Heterogeneous equality accounts for its indexed end. -/
theorem selected_world_paths_equal (firstOrigin secondOrigin firstOrigin' secondOrigin' : Fin 2) :
    HEq (worldPath _ _ _ offered_twice (selectedRun firstOrigin secondOrigin))
      (worldPath _ _ _ offered_twice (selectedRun firstOrigin' secondOrigin')) := by
  unfold worldPath
  rw [selected_run_projects, selected_run_projects]

theorem same_world_path_distinct_origins :
    HEq (worldPath _ _ _ offered_twice (selectedRun 0 0))
      (worldPath _ _ _ offered_twice (selectedRun 1 1)) ∧
    (selectedRun 0 0).val.word.map (fun entry => entry.2.use) ≠
      (selectedRun 1 1).val.word.map (fun entry => entry.2.use) := by
  refine ⟨selected_world_paths_equal 0 0 1 1, ?_⟩
  rw [selected_run_origin_word, selected_run_origin_word]
  intro same
  have impossible : (0 : Fin 2) = 1 := Use.held.inj (List.cons.inj same).1
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

theorem projected_rows (firstOrigin secondOrigin : Fin 2) :
    let final := (projectRun _ _ _ offered_twice start 2
      (selectedRun firstOrigin secondOrigin)).val.last
    final.label 2 = 2 ∧ final.label 3 = 2 := by
  dsimp only
  rw [selected_run_projects]
  exact same_row_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.OriginSupport.Controls
