import Mettapedia.Languages.MM0.Kernel.FreshDummies

/-! # Fresh unfolding controls: parameters, dependency support and distinct dummies -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.FreshDummiesControls

private def target : Context := [.bound 0, .bound 0, .bound 0, .regular 1 {0}, .bound 1]

theorem distinct_fresh_images_accepted :
    Definition.checkDummies target [.var 0] [0, 0] [1, 2] = true := by decide

theorem parameter_capture_rejected :
    Definition.checkDummies target [.var 0] [0] [0] = false := by decide

theorem earlier_dummy_collision_rejected :
    Definition.checkDummies target [.var 0] [0, 0] [1, 1] = false := by decide

theorem declared_dependency_capture_rejected :
    Definition.checkDummies target [.var 3] [0] [0] = false := by decide

theorem declared_dependency_fresh_image_accepted :
    Definition.checkDummies target [.var 3] [0] [1] = true := by decide

theorem wrong_sort_rejected : Definition.checkDummies target [] [0] [4] = false := by decide

theorem regular_image_rejected : Definition.checkDummies target [] [1] [3] = false := by decide

theorem missing_image_rejected : Definition.checkDummies target [] [0] [] = false := by decide

theorem extra_image_rejected : Definition.checkDummies target [] [] [0] = false := by decide

theorem unknown_parameter_is_not_fresh :
    Preterm.checkFreshFor target 0 (.var 5) = false := by decide

theorem colliding_images_have_no_freshness_derivation :
    ¬ Definition.FreshDummies target [.var 0] [0, 0] [1, 1] := by
  intro admitted
  have accepted := (Definition.checkDummies_iff _ _ _ _).mpr admitted
  rw [earlier_dummy_collision_rejected] at accepted
  contradiction

end Mettapedia.Languages.MM0.Kernel.FreshDummiesControls
