import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBlockNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopesControls

/-!
# Typed and provenance controls for three helper blocks

The two-variable path block contains a term and a proof depending on it.
Exchanging this entire block preserves that dependency. Equal-typed point
blocks still have different origins, so their exchange is not the identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TelescopeControls

theorem three_points_arity : (frame pointHelpers pointHelpers pointHelpers).arity = 4 := rfl

theorem point_blocks_exchange_origins :
    (swapFirst pointHelpers pointHelpers pointHelpers).substitution ⟨1, by decide⟩ = .var ⟨2, by decide⟩ ∧
      (swapFirst pointHelpers pointHelpers pointHelpers).substitution ⟨2, by decide⟩ = .var ⟨1, by decide⟩ :=
  ⟨rfl, rfl⟩

theorem equal_typed_blocks_not_identity :
    swapFirst pointHelpers pointHelpers pointHelpers ≠ 𝟙 (frame pointHelpers pointHelpers pointHelpers) := by
  intro same
  have atSecond := congrArg (fun map => map.substitution ⟨1, by decide⟩) same
  change (Tm.var (2 : Fin 4) : Tm Tower.Head 4) = .var (1 : Fin 4) at atSecond
  exact (by decide : (2 : Fin 4) ≠ 1) (Tm.var.inj atSecond)

theorem dependent_path_block_arity : (frame pathHelpers pointHelpers pointHelpers).arity = 5 := rfl

theorem path_and_point_positions :
    (swapFirst pathHelpers pointHelpers pointHelpers).substitution ⟨1, by decide⟩ = .var ⟨2, by decide⟩ ∧
      (swapFirst pathHelpers pointHelpers pointHelpers).substitution ⟨2, by decide⟩ = .var ⟨3, by decide⟩ ∧
      (swapFirst pathHelpers pointHelpers pointHelpers).substitution ⟨3, by decide⟩ = .var ⟨1, by decide⟩ :=
  ⟨rfl, rfl, rfl⟩

theorem path_dependency_is_kept :
    subst (swapFirst pathHelpers pointHelpers pointHelpers).substitution
        (.id (.var 4) (.var 2) (.var 2) : Tm Tower.Head 5) =
      (.id (.var 4) (.var 3) (.var 3) : Tm Tower.Head 5) := rfl

theorem path_typed_row_is_kept :
    (pathRow.reindex (toSecond pointHelpers pathHelpers pointHelpers)).reindex
        (swapFirst pathHelpers pointHelpers pointHelpers) =
      pathRow.reindex (toFirst pathHelpers pointHelpers pointHelpers) := by
  rw [← ContextualDependentEta.reindex_comp, swapFirst_second]

theorem dependent_braid :
    swapFirst pathHelpers pointHelpers pointHelpers ≫
        swapLast pointHelpers pathHelpers pointHelpers ≫
        swapFirst pointHelpers pointHelpers pathHelpers =
      swapLast pathHelpers pointHelpers pointHelpers ≫
        swapFirst pathHelpers pointHelpers pointHelpers ≫
        swapLast pointHelpers pathHelpers pointHelpers := braid _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.Controls.equal_typed_blocks_not_identity
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.Controls.path_typed_row_is_kept
