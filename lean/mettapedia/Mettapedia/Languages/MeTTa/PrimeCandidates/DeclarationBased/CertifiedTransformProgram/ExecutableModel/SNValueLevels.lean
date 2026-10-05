import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Identity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.TransportReadout

/-!
# Identity elimination and large elimination at every level in the transport value model

On the skeleton-free value side of the model of every extension of the transport value model
(`TExtension.model`):

* **Identity elimination** is a valid term of `elimType u w` for every carrier
  universe `u` and every motive universe `w` (`TExtension.valid_j_at`): on the value
  side it transports its method along its motive, and the transport table holds
  (`TExtension.coeRules`). At universes of the tower the type is typed without
  constants, so the validity holds without hypotheses (`TExtension.valid_j_sorts`).
  At instances of the motive related in a universe at a level, the endpoint
  instance has the base instance's pack, and identity elimination is related to
  its method there (`TExtension.transportJ_rel_of_universe`).
* **The recursor on the numbers** is valid with its motive into every universe
  of the tower (`TExtension.valid_numRecS_sorts`), from `TExtension.valid_numRecS_at` and the typing
  of its type in the stage of the numbers and their constructors
  (`numRecTypeAt_typed`).
* **The iterator** is valid with its carrier and its family in any universes of
  the tower (`TExtension.valid_iter_sorts`), from `TExtension.valid_iter_at` and the
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

namespace TExtension

variable (X : TExtension) (v : Nat → Nat)

/-! ## The tower without constants -/

/-- **The tower is sound for the model**: its universe rules are the model's, and
it has no constants and no computations. -/
theorem tower_soundS : ModelSN.TypedSoundS Tower.rules (X.model v) where
  laws := X.laws v
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
theorem j_rootStep {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm m) :
    (X.model v).rules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅])
      (ValueSide.coeApp coeN (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃) :=
  X.step v (tmodelListedAt X.roles v 3 (by decide)) (transportJ_step a₀ a₁ a₂ a₃ a₄ a₅)

/-- **Identity transport at related instances of the motive, in the transport
value model.** If the motive's instances at the base point with reflexivity and
at the endpoint with the path are related in the universe relation over the
interpretation at a level `l`, as a valid motive's instances are at related
endpoints, then the endpoint instance has the pack `Q` of the base instance at
`l`, and `J A x P d y e` is related to `d` at `Q`: identity elimination
transports its method along the motive, and the transport between types of one
shape with one pack is related to its method. -/
theorem transportJ_rel_of_universe (l : Nat) {n : Nat}
    {ξ : Consistency.World (X.model v).reading n} {A x P d y e : Tower.Tm n}
    {Q : ValueSide.Pack (X.model v).value n}
    (related : (ValueSide.universePack (X.model v).value (ValueSide.InterpAt (X.model v).value l)
      ξ).rel (.app (.app P x) (.refl x)) (.app (.app P y) e))
    (hQ : ValueSide.InterpAt (X.model v).value l ξ (.app (.app P x) (.refl x)) Q)
    (hd : Q.Val d) :
    ValueSide.InterpAt (X.model v).value l ξ (.app (.app P y) e) Q ∧
      Q.rel (appSpine (.const jName) [A, x, P, d, y, e]) d :=
  ValueSide.InterpAt.transportJ_rel_of_universe (X.valueLaws v) (X.coeRules v) l
    (X.j_rootStep v) related hQ hd

/-- **Identity elimination is valid at every carrier universe `u` and every
motive universe `w`** in the transport value model, when its type is valid with
valid parts. There is no premise on the level of `u`. -/
theorem valid_j_at {u w : Tower.Head} (hw : (X.model v).rules.isUniverse w)
    (validType : ModelSN.ValidTyS (X.model v) .nil (elimType u w))
    (partsType : ModelSN.StructuredS (X.model v) .nil (elimType u w)) :
    ModelSN.ValidTmS (X.model v) .nil (.const jName) (elimType u w) :=
  ModelSN.ValidTmS.transportEliminator (X.laws v) hw (X.j_rootStep v)
    (X.coeRules v) X.realRoles_j
    (fun step => objectStep_j (X.realStep_declared (by decide) step)) validType partsType

/-- **Identity elimination is valid at every pair of universes of the tower**:
carrier `U lu` and motive `U lw`, for all level expressions `lu` and `lw`. The
eliminator's type is typed in the tower without constants, whose soundness gives
the validity of the type and of its parts. -/
theorem valid_j_sorts (lu lw : LevelExpr Nat) :
    ModelSN.ValidTmS (X.model v) .nil (.const jName) (elimType (.sort lu) (.sort lw)) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed lu lw
  obtain ⟨validT, partsT, _⟩ := ModelSN.Derivable.validS (X.tower_soundS v) typed trivial
  exact X.valid_j_at v (LevelTower.IsUniverse.sort lw) (validT.validTy hw) partsT

/-- The declared eliminator of the package, at the lowest universes, is
valid. -/
theorem valid_j : ModelSN.ValidTmS (X.model v) .nil (.const jName) Package.jType :=
  X.valid_j_sorts v Tower.zero Tower.zero

/-! ## Large elimination of the numbers -/

/-- **Large elimination of the numbers**: the recursor with its motive into every
universe of the tower is valid in the transport value model. -/
theorem valid_numRecS_sorts (lw : LevelExpr Nat) :
    ModelSN.ValidTmS (X.model v) .nil (.const numRecName) (numRecTypeAt (.sort lw)) := by
  have sound₀ := X.stage_soundS_of v (names := [numN, zeroN, sucN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact X.valid_num v
      · exact X.valid_zero v
      · exact X.valid_suc v
  obtain ⟨validT, partsT, _⟩ := ModelSN.Derivable.validS sound₀ (numRecTypeAt_typed lw) trivial
  exact X.valid_numRecS_at v (.sort lw) (LevelTower.IsUniverse.sort lw)
    (validT.validTy (LevelTower.IsUniverse.sort _)) partsT

/-! ## The iterator at large families -/

/-- **The iterator is valid at large families**: with its carrier in any
universe `U lk` and its family into any universe `U ll` of the tower. -/
theorem valid_iter_sorts (lk ll : LevelExpr Nat) :
    ModelSN.ValidTmS (X.model v) .nil (.const iterName) (iterTypeAt (.sort lk) (.sort ll)) := by
  have sound₀ := X.stage_soundS_of v (names := [numN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst mem
      obtain rfl := Option.some.inj declared
      exact X.valid_num v
  obtain ⟨validT, partsT, _⟩ := ModelSN.Derivable.validS sound₀ (iterTypeAt_typed lk ll) trivial
  exact X.valid_iter_at v (.sort lk) (.sort ll) (validT.validTy (LevelTower.IsUniverse.sort _))
    partsT

end TExtension

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
