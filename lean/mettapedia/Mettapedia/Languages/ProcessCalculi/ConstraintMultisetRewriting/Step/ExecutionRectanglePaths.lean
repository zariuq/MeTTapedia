import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardedPaths

/-! # Proposed rectangle paths and exact permission lifting -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle

universe uV uE
variable {V : Type uV} [Quiver.{uE} V]

def proposal : ∀ {width height : Nat} (_shuffle : Shuffle width height)
    (grid : Rectangle V width height), Quiver.Path grid.entry grid.exit
  | _, _, .nil, _ => .nil
  | _, _, .horizontal rest, grid => grid.firstHorizontal.toPath.comp (proposal rest grid.dropHorizontal)
  | _, _, .vertical rest, grid => grid.firstVertical.toPath.comp (proposal rest grid.dropVertical)

theorem proposal_permitted_iff (permit : WideSubquiver V) :
    ∀ {width height : Nat} (shuffle : Shuffle width height) (grid : Rectangle V width height),
      GuardedPaths.Permitted permit (proposal shuffle grid) ↔ Admitted permit grid shuffle
  | _, _, .nil, grid => ⟨fun _ => .nil grid, fun _ => .nil _⟩
  | _, _, .horizontal rest, grid => by
      rw [proposal, GuardedPaths.permitted_comp_iff, GuardedPaths.permitted_toPath_iff,
        proposal_permitted_iff, admitted_horizontal_iff]
  | _, _, .vertical rest, grid => by
      rw [proposal, GuardedPaths.permitted_comp_iff, GuardedPaths.permitted_toPath_iff,
        proposal_permitted_iff, admitted_vertical_iff]

theorem allPermitted_iff_unique_lifts (permit : WideSubquiver V) {width height : Nat}
    (grid : Rectangle V width height) :
    AllPermitted permit grid ↔ ∀ shuffle : Shuffle width height,
      ∃! lifted : @Quiver.Path permit _ grid.entry grid.exit,
        (GuardedPaths.inclusion permit).mapPath lifted = proposal shuffle grid := by
  constructor
  · intro all shuffle
    apply (GuardedPaths.lift_exists_unique_iff permit (proposal shuffle grid)).mpr
    exact (proposal_permitted_iff permit shuffle grid).mpr (admitted_of_all shuffle grid all)
  · intro all
    apply allPermitted_of_all_shuffles permit grid
    intro shuffle
    exact (proposal_permitted_iff permit shuffle grid).mp
      ((GuardedPaths.lift_exists_unique_iff permit (proposal shuffle grid)).mp (all shuffle))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ExecutionGeometry.Rectangle
