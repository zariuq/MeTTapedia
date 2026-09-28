import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Identity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportReadout

/-!
# Identity elimination and large elimination at every level in the transport value model

On the skeleton-free value side of the transport value model (`vmodel`):

* **Identity elimination** is a valid term of `elimType u w` for every carrier
  universe `u` and every motive universe `w` (`vmodel_valid_j_at`): on the value
  side it transports its method along its motive, and the transport table holds
  (`vmodel_coeRules`). At universes of the tower the type is typed without
  constants, so the validity holds without hypotheses (`vmodel_valid_j_sorts`).
  At instances of the motive related in a universe at a level, the endpoint
  instance has the base instance's pack, and identity elimination is related to
  its method there (`vmodel_transportJ_rel_of_universe`).
* **The recursor on the numbers** is valid with its motive into every universe
  of the tower (`valid_numRecS_sorts`), from `valid_numRecS_at` and the typing
  of its type in the stage of the numbers and their constructors
  (`numRecTypeAt_typed`).
* **The iterator** is valid with its carrier and its family in any universes of
  the tower (`vmodel_valid_iter_sorts`), from `vmodel_valid_iter_at` and the
  typing of its type in the stage of the numbers (`iterTypeAt_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Realizability (transportJ_step)
open Package (jName numRecName iterName)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## The tower without constants -/

/-- **The tower is sound for the model**: its universe rules are the model's, and
it has no constants and no computations. -/
theorem vtower_soundS : ModelS.TypedSoundS Tower.rules (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => step.elim
  constants := fun declared => nomatch declared

/-! ## Identity elimination -/

/-- On the value side of the model, identity elimination transports its method
along its motive. -/
theorem vmodel_j_rootStep {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm m) :
    (vmodel v).rules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅])
      (ValueSide.coeApp coeN (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃) :=
  tmodel_step v (tmodelListed v 3 (by decide)) (transportJ_step a₀ a₁ a₂ a₃ a₄ a₅)

/-- **Identity transport at related instances of the motive, in the transport
value model.** If the motive's instances at the base point with reflexivity and
at the endpoint with the path are related in the universe relation over the
interpretation at a level `l`, as a valid motive's instances are at related
endpoints, then the endpoint instance has the pack `Q` of the base instance at
`l`, and `J A x P d y e` is related to `d` at `Q`: identity elimination
transports its method along the motive, and the transport between types of one
shape with one pack is related to its method. -/
theorem vmodel_transportJ_rel_of_universe (l : Nat) {n : Nat}
    {ξ : Consistency.World (vmodel v).reading n} {A x P d y e : Tower.Tm n}
    {Q : ValueSide.Pack (vmodel v).value n}
    (related : (ValueSide.universePack (vmodel v).value (ValueSide.InterpAt (vmodel v).value l)
      ξ).rel (.app (.app P x) (.refl x)) (.app (.app P y) e))
    (hQ : ValueSide.InterpAt (vmodel v).value l ξ (.app (.app P x) (.refl x)) Q)
    (hd : Q.Val d) :
    ValueSide.InterpAt (vmodel v).value l ξ (.app (.app P y) e) Q ∧
      Q.rel (appSpine (.const jName) [A, x, P, d, y, e]) d :=
  ValueSide.InterpAt.transportJ_rel_of_universe (vmodel_valueLaws v) (vmodel_coeRules v) l
    (vmodel_j_rootStep v) related hQ hd

/-- On the realizer side identity elimination computes at six arguments,
inspecting its path for reflexivity. -/
theorem objectRoles_j :
    objectRealizers.roles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_j

/-- **Identity elimination is valid at every carrier universe `u` and every
motive universe `w`** in the transport value model, when its type is valid with
valid parts. There is no premise on the level of `u`. -/
theorem vmodel_valid_j_at {u w : Tower.Head} (hw : (vmodel v).rules.isUniverse w)
    (validType : ModelS.ValidTyS (vmodel v) .nil (elimType u w))
    (partsType : ModelS.StructuredS (vmodel v) .nil (elimType u w)) :
    ModelS.ValidTmS (vmodel v) .nil (.const jName) (elimType u w) :=
  ModelS.ValidTmS.transportEliminator (vmodel_laws v) hw (vmodel_j_rootStep v)
    (vmodel_coeRules v) objectRoles_j objectStep_j validType partsType

/-- **Identity elimination is valid at every pair of universes of the tower**:
carrier `U lu` and motive `U lw`, for all level expressions `lu` and `lw`. The
eliminator's type is typed in the tower without constants, whose soundness gives
the validity of the type and of its parts. -/
theorem vmodel_valid_j_sorts (lu lw : LevelExpr) :
    ModelS.ValidTmS (vmodel v) .nil (.const jName) (elimType (.sort lu) (.sort lw)) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed lu lw
  obtain ⟨validT, partsT, _⟩ := ModelS.Derivable.validS (vtower_soundS v) typed trivial
  exact vmodel_valid_j_at v (Tower.IsUniverse.sort lw) (validT.validTy hw) partsT

/-- The declared eliminator of the package, at the lowest universes, is
valid. -/
theorem vmodel_valid_j : ModelS.ValidTmS (vmodel v) .nil (.const jName) Package.jType :=
  vmodel_valid_j_sorts v Tower.zero Tower.zero

/-! ## Large elimination of the numbers -/

/-- **Large elimination of the numbers**: the recursor with its motive into every
universe of the tower is valid in the transport value model. -/
theorem valid_numRecS_sorts (lw : LevelExpr) :
    ModelS.ValidTmS (vmodel v) .nil (.const numRecName) (numRecTypeAt (.sort lw)) := by
  have sound₀ := vstage_soundS_of v (names := [numN, zeroN, sucN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
  obtain ⟨validT, partsT, _⟩ := ModelS.Derivable.validS sound₀ (numRecTypeAt_typed lw) trivial
  exact valid_numRecS_at v (.sort lw) (Tower.IsUniverse.sort lw)
    (validT.validTy (Tower.IsUniverse.sort _)) partsT

/-! ## The iterator at large families -/

/-- **The iterator is valid at large families**: with its carrier in any
universe `U lk` and its family into any universe `U ll` of the tower. -/
theorem vmodel_valid_iter_sorts (lk ll : LevelExpr) :
    ModelS.ValidTmS (vmodel v) .nil (.const iterName) (iterTypeAt (.sort lk) (.sort ll)) := by
  have sound₀ := vstage_soundS_of v (names := [numN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst mem
      obtain rfl := Option.some.inj declared
      exact vmodel_valid_num v
  obtain ⟨validT, partsT, _⟩ := ModelS.Derivable.validS sound₀ (iterTypeAt_typed lk ll) trivial
  exact vmodel_valid_iter_at v (.sort lk) (.sort ll) (validT.validTy (Tower.IsUniverse.sort _))
    partsT

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
