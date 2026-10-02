import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvIterator

/-!
# The executable package is sound for its conversion model

Every declared constant of the executable package `rules` is a valid term of its
declared type in the conversion model over every realizer side over the
executable package (`valid_declared`), in particular over the executable
package itself at every lawful generic equality that respects typed weak-head
reduction: the numbers, the
sets and their constants, the recursor, addition, the iterated power set and
the iterator by their own proofs; identity elimination by transport, its type
typed without constants; and each definition by one equation from the
fundamental lemma of the stage that types its right-hand side. With the root
steps of every stage validated, the package is sound for the model, its root
steps read with their typing (`rules_typedSoundN`).

**Completeness of the conversion algorithm from the conversion model.** At the
algorithmic equality the realizer side is the one with the conversion
algorithm (`rulesAlgorithmicSide`). The fundamental lemma relates derivably
equal terms by the candidate of their value at the daimon valuation, which
escapes to the algorithmic equality; at the identity renaming this is a
derivation of the conversion algorithm (`algorithm_completeN`, with the
statement of `algorithm_complete`).

A closed term of the numbers typed in the package reaches `zero`, `suc` of a
term of a smaller shape, or a neutral term: the evaluated candidate of its value
records its shape (`closed_num_shape`).

## Controls

* The escape relates exactly typed-equal terms: a computation of addition is
  compared by the algorithm (`add_zero_compared`), while `zero` and `suc zero`,
  which are not typed-equal, are not related by the algorithmic equality
  (`zero_suc_not_convertible`).
* The executable package with one more root step, identifying `zero` with
  `suc zero`, is not sound for the model (`zeroSucRules_not_typedSoundN`): the
  step makes them typed-equal, and numbers of different shapes are not related
  on the value side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Morph)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape)
open TelescopeAbstraction (closeType applyClosed liftClosed_zero)
open SetProfile (zeroNative sucNative)
open Package (U0 numT jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName eqAtTelescope transportTelescope composeTelescope
  returnIterResult eqAtApp)

namespace CodeModel
namespace ConvRules

section Model

variable (v : Nat → Nat) {T : RealizerSide Tower.Head ℕ} (ext : OverRules T)
include ext

/-! ## Identity elimination -/

/-- The package with the executable package's universes and no constant or
computation is sound for the model. -/
theorem constantFree_typedSoundN :
    TypedSoundN (constantFreeRules rules) (nmodel v T) where
  laws := nmodel_laws v T
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := ext.sub.headTyping
  isUniverse' := ext.sub.isUniverse
  join' := ext.sub.join
  cumulative' := ext.sub.cumulative
  headEq' := ext.sub.headEq
  root := fun step => nomatch step
  constants := fun declared => nomatch declared

/-- **Identity elimination is valid**: on the value side it transports its
method along its motive, and on the realizer side it is declared as an
eliminator at the lowest universes; its type is typed without constants. -/
theorem valid_j : ValidTmN (nmodel v T) .nil (.const jName) Package.jType := by
  have laws := nmodel_laws v T
  obtain ⟨w, hw, typed⟩ := (declaresJ (fun _ => 0) (E := T.E)).typed
  have sound₀ := constantFree_typedSoundN v ext
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN sound₀ typed trivial
  exact ValidTmN.transportEliminator laws (LevelTower.IsUniverse.sort _) (nmodel_jStep v)
    (nmodel_coeRules v) ext.declaresJ
    (validT.validTy (sound₀.isUniverse hw) (sound₀.isUniverse' hw)) partsT

/-! ## Definitions by one equation -/

/-- A constant declared by one equation on the realizer side, whose declared type
and right-hand side are typed in a stage sound for the model, and which computes
on the value side to its right-hand side, is valid. -/
theorem valid_of_declaresDefinition {allowed : DeclName → Bool}
    (sound₀ : TypedSoundN (stage allowed) (nmodel v T)) {f : DeclName} {k : Nat}
    {Θ : Tower.Ctx k} {C rhs : Tower.Tm k}
    (decl : DeclaresDefinition (setting fun _ => 0) (stage allowed) f Θ C rhs)
    (rule : ∀ {n : Nat} (σ : Sub Tower.Head k n), WhRed (nmodel v T).rules
      (nmodel v T).roles (applyClosed Θ σ (.const f)) (Presentation.subst σ rhs)) :
    ValidTmN (nmodel v T) .nil (.const f) (closeType Θ C) := by
  obtain ⟨w, hw, typed⟩ := decl.typed
  have declared : Typed T.R .nil (.const f) (closeType Θ C) := by
    have h := ext.typed (decl.typing (Γ := .nil))
    rwa [liftClosed_zero] at h
  exact ValidTmN.definition sound₀ ⟨w, hw, typed⟩ decl.body declared
    ⟨.leaf, ext.keep decl.role nofun⟩ rule fun σ => ext.step (decl.rule σ)

/-- `eqAt` is valid. -/
theorem valid_eqAt : ValidTmN (nmodel v T) .nil (.const eqAtName) Package.eqAtType :=
  valid_of_declaresDefinition v ext
    (stage_typedSoundN_of v ext (names := [numN, zeroN, sucN, addN])
      fun name mem type declared => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
        · exact valid_num v ext
        · exact valid_zero v ext
        · exact valid_suc v ext
        · exact valid_add v ext)
    (declaresEqAt (fun _ => 0) (laws fun _ => 0))
    fun σ => vmodel_rule v (listed 4 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- `sucMove` is valid: its right-hand side, an identity elimination, is typed in
the stage of the numbers, addition, identity elimination and `eqAt`. -/
theorem valid_sucMove :
    ValidTmN (nmodel v T) .nil (.const sucMoveName) Package.sucMoveType :=
  valid_of_declaresDefinition v ext
    (stage_typedSoundN_of v ext (names := [numN, zeroN, sucN, addN, jName, eqAtName])
      fun name mem type declared => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;>
          obtain rfl := Option.some.inj declared
        · exact valid_num v ext
        · exact valid_zero v ext
        · exact valid_suc v ext
        · exact valid_add v ext
        · exact valid_j v ext
        · exact valid_eqAt v ext)
    (declaresSucMove (fun _ => 0) (laws fun _ => 0))
    fun σ => vmodel_rule v (listed 5 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- The stage without constants is sound for the model. -/
theorem emptyStage_typedSoundN : TypedSoundN emptyStage (nmodel v T) :=
  stage_typedSoundN_of v ext fun _ mem => absurd mem List.not_mem_nil

/-- `keep` is valid. -/
theorem valid_keep : ValidTmN (nmodel v T) .nil (.const keepName) Package.keepType :=
  valid_of_declaresDefinition v ext (emptyStage_typedSoundN v ext)
    (declaresKeep (fun _ => 0))
    fun σ => vmodel_rule v (listed 6 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- The transport of a value and its evidence is valid. -/
theorem valid_transport :
    ValidTmN (nmodel v T) .nil (.const transportName) Package.transportType :=
  valid_of_declaresDefinition v ext (emptyStage_typedSoundN v ext)
    (declaresTransport (fun _ => 0))
    fun σ => vmodel_rule v (listed 7 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- The composition of steps is valid. -/
theorem valid_compose :
    ValidTmN (nmodel v T) .nil (.const composeName) Package.composeType :=
  valid_of_declaresDefinition v ext (emptyStage_typedSoundN v ext)
    (declaresCompose (fun _ => 0))
    fun σ => vmodel_rule v (listed 8 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- `returnIter` is valid: its right-hand side is typed with the iterator. -/
theorem valid_returnIter :
    ValidTmN (nmodel v T) .nil (.const returnIterName) Package.returnIterType :=
  valid_of_declaresDefinition v ext
    (stage_typedSoundN_of v ext (names := [numN, zeroN, sucN, iterName])
      fun name mem type declared => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
        · exact valid_num v ext
        · exact valid_zero v ext
        · exact valid_suc v ext
        · exact valid_iter v ext)
    (declaresReturnIter (fun _ => 0) (laws fun _ => 0))
    fun σ => vmodel_rule v (listed 10 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-- `sucStep` is valid: its right-hand side is typed with `sucMove` and the
transport. -/
theorem valid_sucStep :
    ValidTmN (nmodel v T) .nil (.const sucStepName) Package.sucStepType :=
  valid_of_declaresDefinition v ext
    (stage_typedSoundN_of v ext
      (names := [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName])
      fun name mem type declared => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          obtain rfl := Option.some.inj declared
        · exact valid_num v ext
        · exact valid_zero v ext
        · exact valid_suc v ext
        · exact valid_add v ext
        · exact valid_j v ext
        · exact valid_eqAt v ext
        · exact valid_sucMove v ext
        · exact valid_transport v ext)
    (declaresSucStep (fun _ => 0) (laws fun _ => 0))
    fun σ => vmodel_rule v (listed 11 (by decide)) (by decide) ⟨σ, rfl, rfl⟩

/-! ## The package -/

/-- **Every declared constant of the executable package is a valid term of its
declared type in the conversion model.** -/
theorem valid_declared {name : DeclName} {type : Tower.Tm 0}
    (declared : allTypes name = some type) :
    ValidTmN (nmodel v T) .nil (.const name) type := by
  have mem := mem_of_lookup declared
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact valid_num v ext
  · exact valid_set v ext
  · exact valid_zero v ext
  · exact valid_suc v ext
  · exact valid_add v ext
  · exact valid_power v ext
  · exact valid_pow v ext
  · exact valid_numRec v ext
  · exact valid_j v ext
  · exact valid_eqAt v ext
  · exact valid_sucMove v ext
  · exact valid_keep v ext
  · exact valid_transport v ext
  · exact valid_compose v ext
  · exact valid_iter v ext
  · exact valid_returnIter v ext
  · exact valid_sucStep v ext

/-- **The executable package is sound for the conversion model over every
realizer side over it**, its root steps read with their typing. -/
theorem rules_typedSoundN : TypedSoundN rules (nmodel v T) :=
  stage_typedSoundN v ext fun _ declared => valid_declared v ext declared

end Model

/-! ## Completeness of the conversion algorithm -/

/-- The realizer side with the conversion algorithm is over the executable
package. -/
theorem rulesAlgorithmicSide_over : OverRules rulesAlgorithmicSide :=
  sideAt_over _ rulesAlgorithmicSide.laws rulesAlgorithmicSide.reduce

/-- **The executable package is sound for its conversion model with the
conversion algorithm.** -/
theorem rules_typedSoundN_algorithmic (v : Nat → Nat) :
    TypedSoundN rules (nmodel v rulesAlgorithmicSide) :=
  rules_typedSoundN v rulesAlgorithmicSide_over

section Consequences

variable {n : Nat} {Γ : Tower.Ctx n}

/-- **Completeness of the conversion algorithm, from the conversion model**:
derivably equal terms of a formed context are compared by it. The statement is
that of `algorithm_complete`. -/
theorem algorithm_completeN {t u T : Tower.Tm n} (formed : CtxFormed rules Γ)
    (equal : Equal rules Γ t u T) : Algorithm rules (.compare Γ t u T) := by
  have escaped := Equal.escapeN (rules_typedSoundN_algorithmic fun _ => 0) formed equal
  have derivation := escaped.2 (CtxRen.id Γ) formed
  rw [rename_id, rename_id, rename_id] at derivation
  exact derivation.refines

end Consequences

/-! ## Shapes -/

/-- **The evaluated candidate records the shape**: a closed term of the numbers
typed in the package is related to itself by the realizers of the shape of its
value, so it reaches, by typed reduction, `zero`, `suc` of a term of a smaller
shape, or a neutral term. -/
theorem closed_num_shape {t : Tower.Tm 0} (typing : Typed rules .nil t numT) :
    ∃ s, NumShapeRel rulesAlgorithmicSide numN zeroN sucN s .nil numT t t := by
  obtain ⟨P, den, val, real⟩ :=
    Typed.shapeN (rules_typedSoundN_algorithmic fun _ => 0) .nil typing
  have closed : ∀ σ : Sub Tower.Head 0 0, Presentation.subst σ t = t := fun σ => by
    rw [show σ = ids from funext fun i => Fin.elim0 i, subst_ids]
  rw [closed] at val real
  have val' := val
  rw [num_den (fun _ => 0) den] at val'
  obtain ⟨s, hs, -⟩ := ValueSide.numIndPack_rel.mp val'
  exact ⟨s, (num_real (fun _ => 0) rulesAlgorithmicSide_over den hs .nil numT t t).mp real⟩

/-! ## Controls -/

/-- `add zero zero` computes to `zero` in the package. -/
theorem add_zero_equal : Equal rules (.nil : Tower.Ctx 0) (addApp zeroNative zeroNative) zeroNative numT :=
  have tz : Typed rules (.nil : Tower.Ctx 0) zeroNative numT := rules_zero_typed
  .root (rules_add_zero zeroNative) (addApp_typed' rulesAlgorithmicSide_over tz tz) tz

/-- **The escape compares a computation**: `add zero zero` and `zero` are compared
by the conversion algorithm, through the conversion model. -/
theorem add_zero_compared :
    Algorithm rules (.compare (.nil : Tower.Ctx 0) (addApp zeroNative zeroNative) zeroNative numT) :=
  algorithm_completeN .nil add_zero_equal

/-- **The escape relates only typed-equal terms**: `zero` and `suc zero` are not
related by the algorithmic equality. -/
theorem zero_suc_not_convertible :
    ¬ (nmodel (fun _ => 0) rulesAlgorithmicSide).side.E.convTm (.nil : Tower.Ctx 0)
      (.const zeroN) (.app (.const sucN) (.const zeroN)) numT :=
  fun convertible => zero_ne_suc .nil convertible.1

/-- The root step identifying `zero` with `suc zero`. -/
def zeroSucStep : RootComputation Tower.Head where
  step := fun l r => l = .const zeroN ∧ r = .app (.const sucN) (.const zeroN)
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The executable package with one more root step, identifying `zero` with
`suc zero`. -/
def zeroSucRules : Rules Tower.Head :=
  { rules with computation := RootComputation.union rules.computation zeroSucStep }

/-- The executable package is included in the one with the additional step. -/
theorem rules_sub_zeroSucRules : RulesSub rules zeroSucRules :=
  ⟨id, id, id, id, id, id, fun step => .inl step⟩

/-- **A package deriving `zero` equal to `suc zero` is sound for no conversion
model over any realizer side**: on the value side numbers of different shapes
are not related. -/
theorem not_typedSoundN_of_zero_eq_suc (v : Nat → Nat) (T : RealizerSide Tower.Head ℕ)
    {R : Rules Tower.Head}
    (equal : Equal R (.nil : Tower.Ctx 0) (.const zeroN) (.app (.const sucN) (.const zeroN)) numT) :
    ¬ TypedSoundN R (nmodel v T) := by
  intro sound
  have valid := Equal.validN sound equal trivial
  have laws := (nmodel_laws v T).value
  have e : EqSubstN (nmodel v T) .nil World.closed (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) .nil (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) := CtxFormed.nil
  have den : DenN (nmodel v T) World.closed numT (ValueSide.numIndPack (nmodel v T).value 0) :=
    ⟨0, ValueSide.InterpAt.num laws 0 .refl⟩
  obtain ⟨s, hz, hs⟩ := ValueSide.numIndPack_rel.mp (valid.2.2 e den).1
  have zero := HasShape.deterministic laws.values.truth laws.star hz (.zero .refl)
  have suc := HasShape.deterministic laws.values.truth laws.star hs (.suc .refl (.zero .refl))
  rw [zero] at suc
  cases suc

/-- **The executable package with a root step identifying `zero` with `suc zero`
is not sound for the conversion model**: the step makes them typed-equal, and
on the value side numbers of different shapes are not related. -/
theorem zeroSucRules_not_typedSoundN (v : Nat → Nat) :
    ¬ TypedSoundN zeroSucRules (nmodel v rulesAlgorithmicSide) := by
  have typed₀ : Typed zeroSucRules (.nil : Tower.Ctx 0) (.const zeroN) numT :=
    Derivable.mono rules_sub_zeroSucRules rules_zero_typed
  have typed₁ : Typed zeroSucRules (.nil : Tower.Ctx 0) (.app (.const sucN) (.const zeroN)) numT :=
    Derivable.mono rules_sub_zeroSucRules (sucApp_typed' rulesAlgorithmicSide_over rules_zero_typed)
  exact not_typedSoundN_of_zero_eq_suc v rulesAlgorithmicSide
    (.root (.inr ⟨rfl, rfl⟩) typed₀ typed₁)

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
