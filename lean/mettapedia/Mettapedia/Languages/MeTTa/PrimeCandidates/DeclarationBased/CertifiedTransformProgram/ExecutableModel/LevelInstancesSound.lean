import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelInstances
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValuePackage
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyLevels
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Renaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Renaming

/-!
# The package with every level instance is strongly normalizing and consistent

Every instance of identity elimination is read by the models as identity
elimination, and every instance of the recursor as the recursor: the models read
the package with every instance (`objectRulesInstances`) through erasing the
levels of the instances (`eraseLevels`).

**Strong normalization.** In the transport value model (`vmodel`):

* each instance `jAt lu lw` erases to `id:eliminate`, a valid term of
  `elimType (U lu) (U lw)` (`TExtension.valid_j_sorts`), each `numRecAt lr` to
  `num-rec`, a valid term of `numRecTypeAt (U lr)` (`valid_numRecS_sorts`), and
  every other constant is the object package's;
* each root step erases to a root step of the object package, which the model
  validates semantically or at its typed instances; the typing facts of an
  instance's redex are those of the erased redex at the instance's declared type,
  the declared type of `id:eliminate` in the package at the instance's levels,
  whose typed step the model validates (`vmodel_soundS_at`).

So the package is sound for the model through erasing levels
(`vmodel_soundSR_instances`). A term typed in a formed context is strongly
normalizing once erased, and erasing sends each step of the package to a step of
the object package, so the term is strongly normalizing under the package's own
reduction, and so is its type (`objectRulesInstances_sn`, `objectRulesInstances_equal_sn`).

**Consistency.** In the consistency model (`model`), identity elimination is
valid at every pair of universes and the recursor at every universe, so the
package is sound for it through erasing levels (`modelSoundR_instances`), and no
closed term proves `∀ n : num, zero = suc n` (`objectRulesInstances_consistent`).
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
open Presentation.TypedEquality.Impredicative.Consistency (SoundR no_closed_proof_renamed World
  numClass numClass_injective sucClass_numClass)
open Package (jName numRecName)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## The transport value model -/

/-- **Every declared constant of the package with every instance, erased, is a
valid term of its declared type**: an instance of identity elimination by
transport at its universes, an instance of the recursor by large elimination, and
every other constant as in the object package. -/
theorem vmodel_valid_instances {name : DeclName} {type : Tower.Tm 0}
    (declared : objectRulesInstances.constantType name = some type) :
    ModelSN.ValidTmS (vmodel v) .nil (.const (eraseLevels name)) (type.mapConst eraseLevels) := by
  rw [objectRulesInstances_type_erased declared]
  rcases objectRulesInstances_declared_cases declared with
    ⟨lu, lw, rfl, rfl⟩ | ⟨lr, rfl, rfl⟩ | ⟨-, -, declared'⟩
  · rw [eraseLevels_jAt]
    exact objectTExt.valid_j_sorts v lu lw
  · rw [eraseLevels_numRecAt]
    exact objectTExt.valid_numRecS_sorts v lr
  · rw [eraseLevels_of_readLevel (readLevel_of_declared declared')]
    exact (vmodel_soundS_objectRules v).constants declared'

/-- **Every root step of the package with every instance, erased, is validated by
the model**: a step of the object package as the object package's, and the step
of an instance as the step of its constant in the package at the instance's
levels, at its typed instances. -/
theorem vmodel_root_instances {n : Nat} {l r : Tower.Tm n}
    (step : objectRulesInstances.computation.step l r) :
    ModelSN.RootSemanticS (vmodel v) (l.mapConst eraseLevels) (r.mapConst eraseLevels) ∨
      ModelSN.TypedRootSR objectRulesInstances (vmodel v) eraseLevels l r := by
  have erased := objectRulesInstances_eraseLevels step
  rcases step with step | ⟨⟨lu, lw, h⟩ | ⟨lr, h⟩⟩
  · obtain ⟨c, args, rfl, plain⟩ := objectRules_step_head step
    rcases (vmodel_soundS_objectRules v).root erased with semantic | typed
    · exact .inl semantic
    · refine .inr fun {Γ A} facts validL validR => typed (facts.spineFacts ?_) validL validR
      intro T₀ declared₀
      rw [eraseLevels_of_readLevel plain] at declared₀
      exact ⟨T₀, (objectRulesInstances_other plain).trans declared₀,
        objectRules_type_fixed eraseLevels_plain declared₀⟩
  · obtain ⟨args, rfl⟩ := eliminatorComputation_headed h
    rcases (vmodel_soundS_at v lu lw Tower.zero).root erased with semantic | typed
    · exact .inl semantic
    · refine .inr fun {Γ A} facts validL validR => typed (facts.spineFacts ?_) validL validR
      intro T₀ declared₀
      rw [eraseLevels_jAt, objectRulesAt_j] at declared₀
      cases declared₀
      exact ⟨_, objectRulesInstances_j lu lw, mapConst_plain eraseLevels_plain rfl⟩
  · obtain ⟨args, rfl⟩ := iotaComputation_headed h
    rcases (vmodel_soundS_at v Tower.zero Tower.zero lr).root erased with semantic | typed
    · exact .inl semantic
    · refine .inr fun {Γ A} facts validL validR => typed (facts.spineFacts ?_) validL validR
      intro T₀ declared₀
      rw [eraseLevels_numRecAt, objectRulesAt_numRec] at declared₀
      cases declared₀
      exact ⟨_, objectRulesInstances_numRec lr, mapConst_plain eraseLevels_plain rfl⟩

/-- **The package with every instance is sound for the transport value model
through erasing levels.** -/
theorem vmodel_soundSR_instances :
    ModelSN.TypedSoundSR objectRulesInstances (vmodel v) eraseLevels where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := vmodel_root_instances v
  constants := vmodel_valid_instances v

end CodeModel

/-! ## Strong normalization -/

open CodeModel in
/-- **Strong normalization of the package with every level instance.** Every term
typed in a formed context of the package is strongly normalizing under the
package's own reduction, and so is its type. -/
theorem objectRulesInstances_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed objectRulesInstances Γ) (typed : Typed objectRulesInstances Γ t A) :
    SN objectRulesInstances t ∧ SN objectRulesInstances A :=
  have erased := ModelSN.Typed.snR (vmodel_soundSR_instances fun _ => 0) formed typed
  ⟨SN.of_mapConst objectRulesInstances_eraseLevels erased.1,
    SN.of_mapConst objectRulesInstances_eraseLevels erased.2⟩

open CodeModel in
/-- Both sides of a derivable equality of the package with every level instance,
in a formed context, are strongly normalizing, and so is their type. -/
theorem objectRulesInstances_equal_sn {n : Nat} {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
    (formed : CtxFormed objectRulesInstances Γ)
    (equal : Derivable objectRulesInstances (.equality Γ a b A)) :
    SN objectRulesInstances a ∧ SN objectRulesInstances b ∧ SN objectRulesInstances A :=
  have erased := ModelSN.Equal.snR (vmodel_soundSR_instances fun _ => 0) formed equal
  ⟨SN.of_mapConst objectRulesInstances_eraseLevels erased.1,
    SN.of_mapConst objectRulesInstances_eraseLevels erased.2.1,
    SN.of_mapConst objectRulesInstances_eraseLevels erased.2.2⟩

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Consistency -/

/-- **The package with every instance is sound for the consistency model through
erasing levels**: identity elimination is valid at every pair of universes and
the recursor at every universe, and every root step erases to a step of the
object package. -/
theorem modelSoundR_instances : SoundR objectRulesInstances (model v) eraseLevels where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => (objectSound v).root (objectRulesInstances_eraseLevels step)
  constants := by
    intro name type declared
    rw [objectRulesInstances_type_erased declared]
    rcases objectRulesInstances_declared_cases declared with
      ⟨lu, lw, rfl, rfl⟩ | ⟨lr, rfl, rfl⟩ | ⟨-, -, declared'⟩
    · rw [eraseLevels_jAt]
      exact valid_j_sorts v lu lw
    · rw [eraseLevels_numRecAt]
      exact valid_numRec_sorts v lr
    · rw [eraseLevels_of_readLevel (readLevel_of_declared declared')]
      exact (objectSound v).constants declared'

/-- **Consistency of the package with every level instance**: no closed term
proves `∀ n : num, zero = suc n`. -/
theorem objectRulesInstances_consistent (t : Tower.Tm 0) :
    ¬ Typed objectRulesInstances .nil t (programCodes.holdsOf (falseCode (n := 0))) :=
  no_closed_proof_renamed (modelSoundR_instances fun _ => 0) (falseCode_truth fun _ => 0)
    (fun all => Nat.zero_ne_one (numClass_injective (model_laws fun _ => 0).truth.numerals
      ((all (numClass _ 0)).trans (sucClass_numClass 0))))
    rfl (mapConst_plain eraseLevels_plain (by decide)) t

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
