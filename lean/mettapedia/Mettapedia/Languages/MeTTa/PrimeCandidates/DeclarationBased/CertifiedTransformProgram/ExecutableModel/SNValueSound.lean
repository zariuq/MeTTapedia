import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLevels
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelPackage

/-!
# The object package with identity elimination is sound for the transport value model

On the skeleton-free value side of the transport value model (`vmodel`), every
root step of the executable package is validated:

* a step of a computation other than identity elimination is a step of the
  model's reduction, and a decoding of a code is coherent, so both preserve
  meaning semantically;
* the linear rule of identity elimination, `J A x P d y (refl z) ⟶ d`, holds at
  its typed instances (`vmodel_jRoot_typed`): the typing facts of the redex's
  spine make its path a valid path from the base point to the endpoint, and the
  transport of the method along the motive is then related to the method
  (`ModelSN.TypedRootS.transport`).

So every stage of the package whose constants are valid is sound with typed
root steps (`vstage_typedSoundS`), and so is the program's codes over it
(`vcodes_typedSoundS`). The definitions whose right-hand sides use identity
elimination, `sucMove` and `sucStep`, are valid by one equation from the
fundamental lemma of such a stage (`vmodel_valid_sucMove`, `vmodel_valid_sucStep`),
so every declaration is valid, and the whole object package is sound
(`vmodel_soundS_objectRules`). Strong normalization of the object package
follows through the skeleton-free value side (`objectRules_sn_values`), and it
is the package's strong normalization theorem (`objectRules_sn`,
`objectRules_equal_sn`).

## Controls

* The untyped reading is still refuted: `objectRules_not_soundS_vmodel` states
  that the object package is not sound when every root step must preserve
  meaning without its typing.
* The typed reading holds exactly where the redex is typed. At every typed
  redex of identity elimination the two sides of the linear rule are validly
  equal (`vmodel_jRoot_valid`). At the untypable redex `mismatchJ`, where the
  untyped obligation fails, the typing facts fail
  (`mismatchJ_not_spineFacts`), so the redex has no typing at `U0`
  (`mismatchJ_untypable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Package (U0 numT jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numRecType eqAtType sucMoveType keepType transportType
  composeType iterType returnIterType sucStepType eqAtTelescope transportTelescope
  composeTelescope returnIterResult)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Root steps -/

/-- **The typed root step of identity elimination in the model**: at every redex
`J a₀ a₁ a₂ a₃ a₄ (refl z)` of a package that declares identity elimination at
`elimType u w`, with `w` a universe, read with the typing facts of its spine,
the two sides of the linear rule are validly equal. -/
theorem vmodel_jRoot_typed_at {R : Rules Tower.Head} {u w : Tower.Head}
    (hw : (vmodel v).rules.isUniverse w) (declared : R.constantType jName = some (elimType u w))
    {n : Nat} {a₀ a₁ a₂ a₃ a₄ z : Tower.Tm n} :
    ModelSN.TypedRootS R (vmodel v) (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ :=
  ModelSN.TypedRootS.transport (vmodel_laws v) hw declared (vmodel_j_rootStep v)
    (vmodel_coeRules v)

/-- The typed root step of identity elimination, for a package that declares it
at the lowest universes. -/
theorem vmodel_jRoot_typed {R : Rules Tower.Head}
    (declared : R.constantType jName = some Package.jType) {n : Nat}
    {a₀ a₁ a₂ a₃ a₄ z : Tower.Tm n} :
    ModelSN.TypedRootS R (vmodel v) (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ :=
  vmodel_jRoot_typed_at v (LevelTower.IsUniverse.sort _) (declared.trans (by rw [jType_eq]))

/-- **Every root step of a stage is validated by the model**: a computation other
than identity elimination is a step of the model's reduction, and identity
elimination holds at its typed instances, in every package that declares it,
where the stage lists it, at `elimType u w` with `w` a universe. -/
theorem vstage_root {allowed : DeclName → Bool} {R : Rules Tower.Head}
    (declaredJ : allowed jName = true → ∃ u w, (vmodel v).rules.isUniverse w ∧
      R.constantType jName = some (elimType u w))
    {n : Nat} {l r : Tower.Tm n} (step : (stage allowed).computation.step l r) :
    ModelSN.RootSemanticS (vmodel v) l r ∨ ModelSN.TypedRootS R (vmodel v) l r := by
  change (RootComputation.unionAll (computations.filter fun entry => allowed entry.1)).step l r
    at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  obtain ⟨listedIn, allowedIn⟩ := List.mem_filter.mp mem
  have semantic : (vmodel v).rules.computation.step l r → ModelSN.RootSemanticS (vmodel v) l r :=
    fun s => ModelSN.ModelRootS.semantic (vmodel_laws v) (vprogramDecodes v) (.inl s)
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (semantic (tmodel_step v (tmodelListed v 0 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 1 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 2 (by decide)) h))
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := h
    obtain ⟨u, w, hw, declared⟩ := declaredJ allowedIn
    exact .inr (vmodel_jRoot_typed_at v hw declared)
  · exact .inl (semantic (tmodel_step v (tmodelListed v 4 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 5 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 6 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 7 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 8 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 9 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 10 (by decide)) h))
  · exact .inl (semantic (tmodel_step v (tmodelListed v 11 (by decide)) h))

/-! ## Stages -/

/-- **A stage whose constants are valid is sound for the model with typed root
steps.** -/
theorem vstage_typedSoundS {allowed : DeclName → Bool}
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ModelSN.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelSN.TypedSoundS (stage allowed) (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := vstage_root v fun allowedJ => by
    refine ⟨.sort Tower.zero, .sort Tower.zero, LevelTower.IsUniverse.sort _, ?_⟩
    change (if allowed jName then allTypes jName else none) = some Package.jType
    rw [if_pos allowedJ]
    exact allTypes_j
  constants := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    split_ifs at declared with h
    exact constants h declared

/-- A stage of the listed names whose constants are valid is sound for the model
with typed root steps. -/
theorem vstage_typedSoundS_of {names : List DeclName}
    (constants : ∀ name ∈ names, ∀ {type : Tower.Tm 0}, allTypes name = some type →
      ModelSN.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelSN.TypedSoundS (stage (allowedIn names)) (vmodel v) :=
  vstage_typedSoundS v fun {name _} allowed declared =>
    constants name (by simpa [allowedIn] using allowed) declared

/-- **The program's codes over a stage whose constants are valid are sound for
the model with typed root steps**: the decodings are coherent, and the stage's
root steps are validated. -/
theorem vcodes_typedSoundS {allowed : DeclName → Bool}
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ModelSN.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelSN.TypedSoundS (programCodes.extend (stage allowed)) (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := by
    intro n l r step
    rcases step with step | step
    · refine vstage_root v
        (fun allowedJ => ⟨.sort Tower.zero, .sort Tower.zero, LevelTower.IsUniverse.sort _, ?_⟩) step
      change (programCodes.codeType jName).orElse
        (fun _ => if allowed jName then allTypes jName else none) = some Package.jType
      rw [codeType_j, if_pos allowedJ]
      exact allTypes_j
    · exact .inl (ModelSN.ModelRootS.semantic (vmodel_laws v) (vprogramDecodes v) (.inr step))
  constants := by
    intro name type declared
    change (programCodes.codeType name).orElse
      (fun _ => if allowed name then allTypes name else none) = some type at declared
    cases code : programCodes.codeType name with
    | some T =>
        rw [code] at declared
        cases declared
        exact ModelSN.valid_codeS (vmodel_laws v) (vprogramCodes_readS v) code
    | none =>
        rw [code] at declared
        change (if allowed name then allTypes name else none) = some type at declared
        split_ifs at declared with h
        exact constants h declared

/-! ## The definitions through identity elimination -/

/-- **`sucMove` is valid**: its right-hand side, an identity elimination, is typed
in the stage of the numbers, addition, identity elimination and `eqAt`, which
is sound with typed root steps. -/
theorem vmodel_valid_sucMove :
    ModelSN.ValidTmS (vmodel v) .nil (.const sucMoveName) sucMoveType := by
  have sound₀ := vstage_typedSoundS_of v (names := [numN, zeroN, sucN, addN, jName, eqAtName])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
      · exact vmodel_valid_add v
      · exact vmodel_valid_j v
      · exact vmodel_valid_eqAt v
  exact ModelSN.ValidTmS.definition (Θ := eqAtTelescope)
    (C := Package.eqAtApp (SetProfile.sucNative (.var 1))) (rhs := sucMoveRhs) sound₀
    ⟨_, .sort _, sucMoveType_typed (by simp) (by simp) (by simp)⟩
    (sucMoveBody_typed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    (fun σ => vmodel_rule v (listed 5 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_sucMove
      (objectStep_definition (listed 5 (by decide)) (by decide)) sns h)

/-- **`sucStep` is valid**: its right-hand side is typed in the stage with
`sucMove` and the transport, which is sound with typed root steps. -/
theorem vmodel_valid_sucStep :
    ModelSN.ValidTmS (vmodel v) .nil (.const sucStepName) sucStepType := by
  have sound₀ := vstage_typedSoundS_of v
    (names := [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
      · exact vmodel_valid_add v
      · exact vmodel_valid_j v
      · exact vmodel_valid_eqAt v
      · exact vmodel_valid_sucMove v
      · exact vmodel_valid_transport v
  exact ModelSN.ValidTmS.definition (Θ := eqAtTelescope)
    (C := .sigma numT (Package.eqAtApp (.var 0))) (rhs := sucStepRhs) sound₀
    ⟨_, .sort _, sucStepType_typed⟩ sucStepBody_typed
    (fun σ => vmodel_rule v (listed 11 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_sucStep
      (objectStep_definition (listed 11 (by decide)) (by decide)) sns h)

/-! ## The package -/

/-- **Every declared constant of the executable package is a valid term of its
declared type in the model**, identity elimination and the definitions through
it included. -/
theorem vmodel_valid_declared {name : DeclName} {type : Tower.Tm 0}
    (declared : allTypes name = some type) :
    ModelSN.ValidTmS (vmodel v) .nil (.const name) type := by
  have mem := mem_of_lookup declared
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact vmodel_valid_num v
  · exact vmodel_valid_set v
  · exact vmodel_valid_zero v
  · exact vmodel_valid_suc v
  · exact vmodel_valid_add v
  · exact vmodel_valid_power v
  · exact vmodel_valid_pow v
  · exact vmodel_valid_numRec' v
  · exact vmodel_valid_j v
  · exact vmodel_valid_eqAt v
  · exact vmodel_valid_sucMove v
  · exact vmodel_valid_keep v
  · exact vmodel_valid_transport v
  · exact vmodel_valid_compose v
  · exact vmodel_valid_iter' v
  · exact vmodel_valid_returnIter v
  · exact vmodel_valid_sucStep v

/-- **The object package is sound for the transport value model on the
skeleton-free value side, with its root steps read with their typing**: the
program's codes over the whole executable package, identity elimination
included. -/
theorem vmodel_soundS_objectRules : ModelSN.TypedSoundS objectRules (vmodel v) :=
  vcodes_typedSoundS v fun {_ _} _ declared => vmodel_valid_declared v declared

end CodeModel

/-! ## Strong normalization -/

open CodeModel in
/-- **Strong normalization of the object package, through the transport value
model on the skeleton-free value side.** Every term typed in a formed context of
the executable package with the program's codes is strongly normalizing under
the package's own reduction, and so is its type. -/
theorem objectRules_sn_values {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (typed : Typed objectRules Γ t A) :
    SN objectRules t ∧ SN objectRules A :=
  ModelSN.Typed.sn (vmodel_soundS_objectRules fun _ => 0) formed typed

open CodeModel in
/-- Both sides of a derivable equality of the object package in a formed context
are strongly normalizing, and so is their type, through the skeleton-free value
side. -/
theorem objectRules_equal_sn_values {n : Nat} {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (equal : Derivable objectRules (.equality Γ a b A)) :
    SN objectRules a ∧ SN objectRules b ∧ SN objectRules A :=
  ModelSN.Equal.sn (vmodel_soundS_objectRules fun _ => 0) formed equal

open CodeModel in
/-- **Strong normalization of the object package.** Every term typed in a
formed context of the executable package with the program's codes is strongly
normalizing under the package's own reduction, and so is its type. -/
theorem objectRules_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (typed : Typed objectRules Γ t A) :
    SN objectRules t ∧ SN objectRules A :=
  objectRules_sn_values formed typed

open CodeModel in
/-- Both sides of a derivable equality of the object package in a formed
context are strongly normalizing, and so is their type. -/
theorem objectRules_equal_sn {n : Nat} {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (equal : Derivable objectRules (.equality Γ a b A)) :
    SN objectRules a ∧ SN objectRules b ∧ SN objectRules A :=
  objectRules_equal_sn_values formed equal

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Controls: the typed root holds exactly on typed redexes -/

/-- The object package computes identity elimination at reflexivity to its
method. -/
theorem objectStep_jRefl {n : Nat} (a₀ a₁ a₂ a₃ a₄ z : Tower.Tm n) :
    objectRules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ :=
  .inl (rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩)

/-- **At every typed redex of identity elimination the two sides of the linear
rule are validly equal** in the model, in every formed context. -/
theorem vmodel_jRoot_valid {n : Nat} {Γ : Tower.Ctx n} {a₀ a₁ a₂ a₃ a₄ z A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ)
    (typedL : Typed objectRules Γ (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, .refl z]) A)
    (typedR : Typed objectRules Γ a₃ A) :
    ModelSN.ValidEqS (vmodel v) Γ (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, .refl z]) a₃ A :=
  (ModelSN.Derivable.validTS (vmodel_soundS_objectRules v)
    (.root (objectStep_jRefl a₀ a₁ a₂ a₃ a₄ z) typedL typedR)
    (ModelSN.CtxFormed.validS (vmodel_soundS_objectRules v) formed)).1

/-- **The untypable redex has no typing facts.** At `mismatchJ`, where the linear
rule's untyped root obligation fails (`vmodel_jRoot_not_semantic`), the typing
facts of its spine would validate the rule, so they fail. -/
theorem mismatchJ_not_spineFacts :
    ¬ ModelSN.SpineFacts objectRules (vmodel v) .nil mismatchJ U0 := fun facts =>
  vmodel_mismatchJ_not_equal v
    (ModelSN.ValidEqS.transportStep (vmodel_laws v) (u := .sort Tower.zero)
      (w := .sort Tower.zero) (LevelTower.IsUniverse.sort _) objectRules_declared_j
      (vmodel_j_rootStep v) (vmodel_coeRules v) facts (vmodel_mismatchJ_valid v)
      (vmodel_valid_num v))

/-- **The untypable redex is not typed**: every typing of the object package has
the typing facts of its spines, which `mismatchJ` has not. -/
theorem mismatchJ_untypable : ¬ Typed objectRules .nil (mismatchJ : Tower.Tm 0) U0 :=
  fun typed => mismatchJ_not_spineFacts (fun _ => 0)
    (ModelSN.Typed.spineFacts (vmodel_soundS_objectRules fun _ => 0) typed trivial)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
