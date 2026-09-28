import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremStability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.TheoremModels

/-!
# Theorems published in the object package

The object package keeps strong normalization and consistency when a theorem is
published by name. For a name the package does not declare, a statement that is
a type, and a body typed at it:

* every term typed in a formed context of the extended package is strongly
  normalizing, and so is its type (`objectRules_withTheorem_sn`);
* no closed term of the extended package proves `∀ n : num, zero = suc n`
  (`objectRules_withTheorem_consistent`).

The proofs unfold the published name. The declared types of the package mention
only its own names (`declared_names`), and its computation is stable under
replacing a name it does not declare (`objectRules_unfoldStable`), so every
derivation of the extended package unfolds to one of the package.

**The models must compute the new δ-rule.** Publishing `zero` again with the body
`1` (`zeroIsOne`) starts from a package that model S and the consistency model
validate, with a body that is valid at `num` in both; neither model validates
the extended package (`withTheorem_soundS_design_false`,
`withTheorem_sound_design_false`). In model S `zero` and `1` have different
shapes; in the consistency model the extended package proves `zero = 1`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open ConstantExpansion (constantNames)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName iterName
  returnIterName sucStepName numT)
open SetProfile (numTy)
open CertifiedTransformProgram.Execution (numeral)

namespace CodeModel

/-! ## The names of the object package -/

/-- The names of the object package other than its quantifier and equation
instances: the declarations of the executable package and the codes `prop`,
`holds` and `imp`. -/
def objectNames : List DeclName :=
  declarations.map Prod.fst ++ [propN, holdsN, impN]

theorem objectNames_declared : ∀ c ∈ objectNames, (objectRules.constantType c).isSome := by
  decide

theorem not_mem_objectNames {name : DeclName} (fresh : objectRules.constantType name = none) :
    name ∉ objectNames := fun mem => by
  have declared := objectNames_declared name mem
  rw [fresh] at declared
  cases declared

/-- The simple types of the profile mention only `prop`, `num` and `set`. -/
theorem typeAt_names : ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat},
    ∀ c ∈ constantNames (FormationSensitiveHOLInterface.typeAt SetProfile.types n type),
      c ∈ objectNames
  | .prop, _ => by
      intro c mem
      rw [FormationSensitiveHOLInterface.typeAt, ConstantExpansion.constantNames_liftClosed] at mem
      change c ∈ [SetProfile.propName] at mem
      rw [List.mem_singleton] at mem
      subst mem
      decide
  | .base sort, _ => by
      intro c mem
      rw [FormationSensitiveHOLInterface.typeAt, ConstantExpansion.constantNames_liftClosed] at mem
      change c ∈ [SetProfile.baseName sort] at mem
      rw [List.mem_singleton] at mem
      subst mem
      cases sort <;> decide
  | .arr a b, _ => by
      intro c mem
      change c ∈ constantNames _ ++ constantNames _ at mem
      rcases List.mem_append.mp mem with mem | mem
      · exact typeAt_names a c mem
      · exact typeAt_names b c mem

theorem declarations_names :
    ∀ entry ∈ declarations, ∀ c ∈ constantNames entry.2, c ∈ objectNames := by
  decide

/-- The types of the codes mention only the object package's names. -/
theorem codeType_names {c : DeclName} {T : Tower.Tm 0} (code : programCodes.codeType c = some T) :
    ∀ d ∈ constantNames T, d ∈ objectNames := by
  have propMem : propN ∈ objectNames := by decide
  unfold Codes.codeType at code
  split_ifs at code
  · cases code
    exact fun _ mem => absurd mem List.not_mem_nil
  · cases code
    intro d mem
    change d ∈ [propN] ++ [] at mem
    simp only [List.append_nil, List.mem_singleton] at mem
    exact mem ▸ propMem
  · cases code
    intro d mem
    change d ∈ [propN] ++ ([propN] ++ [propN]) at mem
    simp only [List.mem_append, List.mem_singleton, or_self] at mem
    exact mem ▸ propMem
  · split at code
    · rename_i A carrier
      cases code
      obtain ⟨type, -, rfl⟩ := Option.map_eq_some_iff.mp carrier
      intro d mem
      change d ∈ (constantNames (typeTerm type) ++ [propN]) ++ [propN] at mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with (mem | rfl) | rfl
      · exact typeAt_names type d mem
      · exact propMem
      · exact propMem
    · obtain ⟨A, carrier, rfl⟩ := Option.map_eq_some_iff.mp code
      have carrier' : (SetProfile.eqInstance? c).map typeTerm = some A := by
        change (if true = true then _ else none) = some A at carrier
        rwa [if_pos rfl] at carrier
      obtain ⟨type, -, rfl⟩ := Option.map_eq_some_iff.mp carrier'
      intro d mem
      change d ∈ constantNames (typeTerm type) ++
        (constantNames (Presentation.rename wk (typeTerm type)) ++ [propN]) at mem
      simp only [ConstantExpansion.constantNames_rename, List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | mem | rfl
      · exact typeAt_names type d mem
      · exact typeAt_names type d mem
      · exact propMem

/-- **The declared types of the object package mention only its own names.** -/
theorem declared_names {c : DeclName} {A : Tower.Tm 0}
    (declared : objectRules.constantType c = some A) : ∀ d ∈ constantNames A, d ∈ objectNames := by
  change (programCodes.codeType c).orElse (fun _ => rules.constantType c) = some A at declared
  cases code : programCodes.codeType c with
  | none =>
      rw [code] at declared
      change (if true then allTypes c else none) = some A at declared
      rw [if_pos rfl] at declared
      exact declarations_names (c, A) (mem_of_lookup declared)
  | some T =>
      rw [code] at declared
      change some T = some A at declared
      cases declared
      exact codeType_names code

/-- A name the object package does not declare occurs in none of its declared
types. -/
theorem declaredFree {name : DeclName} (fresh : objectRules.constantType name = none)
    {c : DeclName} {A : Tower.Tm 0} (declared : objectRules.constantType c = some A) :
    name ∉ constantNames A :=
  fun mem => not_mem_objectNames fresh (declared_names declared name mem)

/-! ## The computation is stable under unfolding -/

theorem ctors_names : ∀ c ∈ ctors, c.1 ∈ objectNames := by decide

theorem addBody_names : ∀ c ∈ ctors, ∀ d ∈ constantNames (addBody c.1 c.2), d ∈ objectNames := by
  decide

theorem powBody_names : ∀ c ∈ ctors, ∀ d ∈ constantNames (powBody c.1 c.2), d ∈ objectNames := by
  decide

theorem iterBody_names : ∀ c ∈ ctors, ∀ d ∈ constantNames (iterBody c.1 c.2), d ∈ objectNames := by
  decide

/-- **The computation of the object package is stable under unfolding a name it
does not declare.** Every rule of the package inspects only the package's own
names. -/
theorem objectRules_unfoldStable {name : DeclName} {body : Tower.Tm 0}
    (fresh : objectRules.constantType name = none) :
    objectRules.computation.ExpandStable (unfoldBodies name body) := by
  have absent := not_mem_objectNames fresh
  have fixedName : ∀ {c : DeclName}, c ∈ objectNames → unfoldBodies name body c = .const c :=
    fun mem => unfoldBodies_of_ne fun same => absent (same ▸ mem)
  have fixes : ∀ {n : Nat} {t : Tower.Tm n}, (∀ c ∈ constantNames t, c ∈ objectNames) →
      FixesTm (unfoldBodies name body) t :=
    fun names c mem => fixedName (names c mem)
  have fixedCode : ∀ {c : DeclName}, (programCodes.codeType c).isSome →
      unfoldBodies name body c = .const c := fun code =>
    unfoldBodies_of_ne fun same => by
      have declared := programCodes.extend_constantType_isSome rules code
      rw [same] at declared
      change (objectRules.constantType name).isSome at declared
      rw [fresh] at declared
      cases declared
  have fixedCtors : ∀ c ∈ ctors, unfoldBodies name body c.1 = .const c.1 :=
    fun c mem => fixedName (ctors_names c mem)
  have baseStable : rules.computation.ExpandStable (unfoldBodies name body) := by
    intro n l r step
    refine unionAll_expandStable (fun entry mem => ?_) step
    have listed := (List.mem_filter.mp mem).1
    simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      intro n l r step
    · exact iotaComputation_expandStable (fixedName (c := numRecName) (by decide)) fixedCtors step
    · exact recursionComputation_expandStable (fixedName (c := addN) (by decide)) fixedCtors
        (fun c mem => fixes (addBody_names c mem)) step
    · exact recursionComputation_expandStable (fixedName (c := powN) (by decide)) fixedCtors
        (fun c mem => fixes (powBody_names c mem)) step
    · exact eliminatorComputation_expandStable (fixedName (c := jName) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := eqAtName) (by decide))
        (fixes (t := eqAtRhs) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := sucMoveName) (by decide))
        (fixes (t := sucMoveRhs) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := keepName) (by decide))
        (fixes (t := keepRhs) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := transportName) (by decide))
        (fixes (t := transportRhs) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := composeName) (by decide))
        (fixes (t := composeRhs) (by decide)) step
    · exact recursionComputation_expandStable (fixedName (c := iterName) (by decide)) fixedCtors
        (fun c mem => fixes (iterBody_names c mem)) step
    · exact definitionComputation_expandStable (fixedName (c := returnIterName) (by decide))
        (fixes (t := returnIterRhs) (by decide)) step
    · exact definitionComputation_expandStable (fixedName (c := sucStepName) (by decide))
        (fixes (t := sucStepRhs) (by decide)) step
  have fixedAll : ∀ {a : DeclName} {A : Tower.Tm 0}, programCodes.quantifiers a = some A →
      unfoldBodies name body a = .const a ∧ FixesTm (unfoldBodies name body) A := by
    intro a A carrier
    obtain ⟨type, -, rfl⟩ := Option.map_eq_some_iff.mp carrier
    exact ⟨fixedCode (programCodes.codeType_isSome_of_quantifier carrier),
      fixes (typeAt_names type)⟩
  have fixedEq : ∀ {e : DeclName} {A : Tower.Tm 0}, programCodes.equationCarrier e = some A →
      unfoldBodies name body e = .const e ∧ FixesTm (unfoldBodies name body) A := by
    intro e A carrier
    have carrier' : (SetProfile.eqInstance? e).map typeTerm = some A := by
      change (if true = true then _ else none) = some A at carrier
      rwa [if_pos rfl] at carrier
    obtain ⟨type, -, rfl⟩ := Option.map_eq_some_iff.mp carrier'
    exact ⟨fixedCode (programCodes.codeType_isSome_of_equation carrier),
      fixes (typeAt_names type)⟩
  intro n l r step
  exact programCodes.extend_expandStable baseStable (fixedName (c := holdsN) (by decide))
    (fixedName (c := impN) (by decide)) fixedAll fixedEq step

/-! ## Strong normalization and consistency carry over -/

/-- **Strong normalization with a published theorem.** For a name the object
package does not declare, a statement that is a type and a body typed at it,
every term typed in a formed context of the extended package is strongly
normalizing under the extended package's reduction, and so is its type. -/
theorem objectRules_withTheorem_sn {name : DeclName} {T body : Tower.Tm 0}
    (fresh : objectRules.constantType name = none) (formed : IsType objectRules .nil T)
    (typed : Typed objectRules .nil body T) {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formedΓ : CtxFormed (objectRules.withTheorem name T body) Γ)
    (typedT : Typed (objectRules.withTheorem name T body) Γ t A) :
    SN (objectRules.withTheorem name T body) t ∧ SN (objectRules.withTheorem name T body) A :=
  withTheorem_sn objectRules_sn fresh formed typed (declaredFree fresh)
    (objectRules_unfoldStable fresh) formedΓ typedT

/-- **Consistency with a published theorem.** For a name the object package does
not declare, a statement that is a type and a body typed at it, no closed term
of the extended package proves `∀ n : num, zero = suc n`. -/
theorem objectRules_withTheorem_consistent {name : DeclName} {T body : Tower.Tm 0}
    (fresh : objectRules.constantType name = none) (formed : IsType objectRules .nil T)
    (typed : Typed objectRules .nil body T) (t : Tower.Tm 0) :
    ¬ Typed (objectRules.withTheorem name T body) .nil t
      (programCodes.holdsOf (falseCode (n := 0))) :=
  withTheorem_uninhabited fresh formed typed (declaredFree fresh) (objectRules_unfoldStable fresh)
    ((falseProposition_typed (Γ := .nil)).avoids fresh) consistent t

/-! ## The model laws need the δ-rule in the model -/

/-- The object package with `zero` published again, with the body `1`. -/
abbrev zeroIsOne : Rules Tower.Head := objectRules.withTheorem zeroN numT (numeral 1)

theorem zeroIsOne_sub : RulesSub objectRules zeroIsOne :=
  withTheorem_sub_of_declared declared_zero

theorem zeroIsOne_delta : zeroIsOne.computation.step (.const zeroN : Tower.Tm 0) (numeral 1) := by
  have step := withTheorem_delta (R := objectRules) (name := zeroN) (T := numT) (body := numeral 1)
    (n := 0)
  rwa [TelescopeAbstraction.liftClosed_zero] at step

/-- **The design's model-S law is false.** Model S validates the object package
and the body `1` at `num`, but not the package with `zero` published again as
`1` at its own declared type: the δ-step relates `zero` and `1`, which have
different shapes, at every typed instance. The law holds when the model computes
the δ-rule (`withTheorem_soundS`). -/
theorem withTheorem_soundS_design_false :
    ∃ (R : Rules Tower.Head) (M : ModelS.SModel Tower.Head ℕ) (name : DeclName)
      (T body : Tower.Tm 0),
      ModelS.TypedSoundS R M ∧ ModelS.ValidTmS M .nil body T ∧
        ¬ ModelS.TypedSoundS (R.withTheorem name T body) M := by
  have sound := vmodel_soundS_objectRules fun _ => 0
  have validOne := ModelS.Typed.validS sound (numeral_typedO (Γ := .nil) 1) trivial
  refine ⟨objectRules, vmodel fun _ => 0, zeroN, numT, numeral 1, sound, validOne,
    fun sound' => ?_⟩
  have validZero := ModelS.Typed.validS sound (zero_typedO (Γ := .nil)) trivial
  have equal : ModelS.ValidEqS (vmodel fun _ => 0) .nil (.const zeroN) (numeral 1) numT := by
    rcases sound'.root zeroIsOne_delta with semantic | typedRoot
    · exact semantic validZero validOne
    · exact typedRoot (ModelS.Typed.spineFacts sound'
        (Normalization.Derivable.mono zeroIsOne_sub (zero_typedO (Γ := .nil))) trivial) validZero
        validOne
  have laws := vmodel_valueLaws fun _ => 0
  let empty : Sub Tower.Head 0 0 := fun i => Fin.elim0 i
  have den : ValueSide.DenS (vmodel fun _ => 0).value Consistency.World.closed
      (Presentation.subst empty numT) (ValueSide.numIndPack (vmodel fun _ => 0).value 0) :=
    ⟨0, ValueSide.InterpAt.num laws 0 .refl⟩
  obtain ⟨s, shapeZero, shapeOne⟩ := ValueSide.numIndPack_rel.mp
    (equal.2.2 (σ := empty) (σ' := empty) (ς := empty) trivial den)
  have atZero := Realizability.HasShape.deterministic laws.values.truth laws.star shapeZero
    (Realizability.HasShape.numeral 0)
  have atOne := Realizability.HasShape.deterministic laws.values.truth laws.star shapeOne
    (Realizability.HasShape.numeral 1)
  exact absurd (Realizability.HasShape.ofNat_injective (atZero.symm.trans atOne)) (by decide)

/-- **The design's consistency-model law is false.** The consistency model
validates the object package and the body `1` at `num`, but not the package
with `zero` published again as `1`, which proves `zero = 1`. The law holds when
the model computes the δ-rule (`withTheorem_sound`). -/
theorem withTheorem_sound_design_false :
    ∃ (R : Rules Tower.Head) (M : Consistency.Model Tower.Head ℕ) (name : DeclName)
      (T body : Tower.Tm 0),
      Consistency.Sound R M ∧ Consistency.ValidTm M .nil body T ∧
        ¬ Consistency.Sound (R.withTheorem name T body) M := by
  have sound := objectSound fun _ => 0
  refine ⟨objectRules, model fun _ => 0, zeroN, numT, numeral 1, sound,
    Consistency.Typed.valid sound (numeral_typedO (Γ := .nil) 1) trivial, fun sound' => ?_⟩
  have mono : ∀ {st : Statement Tower.Head}, Derivable objectRules st → Derivable zeroIsOne st :=
    fun derivation => Normalization.Derivable.mono zeroIsOne_sub derivation
  have one := mono (numeral_typedO (Γ := .nil) 1)
  have equal : Equal zeroIsOne .nil (.const zeroN) (numeral 1) numT :=
    .root zeroIsOne_delta (mono zero_typedO) one
  have identity : Typed zeroIsOne .nil (.refl (numeral 1)) (.id numT (numeral 0) (numeral 1)) :=
    .conv (.reflIntro one) (.idCong (.refl (mono num_typedO)) (.sort _) (.symm equal) (.refl one))
      (.sort _)
  have coded : Typed zeroIsOne .nil (.refl (numeral 1))
      (programCodes.holdsOf (setReading.eqOf numTy (numeral 0) (numeral 1))) :=
    .conv identity (.symm (mono (setReading_laws.equal_holds_eq (τ := numTy) (numeral_typedO 0)
      (numeral_typedO 1)))) (.sort _)
  have eqNum : (model fun _ => 0).reading.eqCarrier eqNumN = some ⟨.data, .num⟩ := by
    change (SetProfile.eqInstance? (SetProfile.eqName SetProfile.numTy)).map carrierOf = _
    rw [SetProfile.eqInstance?_eqName]
    rfl
  have truth : Consistency.Truth (model fun _ => 0).reading Consistency.World.closed
      (setReading.eqOf numTy (numeral 0) (numeral 1))
      (Consistency.numClass (model fun _ => 0).toSetting.numerals 0 =
        Consistency.numClass (model fun _ => 0).toSetting.numerals 1) := by
    rw [numeral_model (fun _ => 0) 0, numeral_model (fun _ => 0) 1,
      ← dataValue_numeral (fun _ => 0) 0 (Consistency.DataEq.numeral 0),
      ← dataValue_numeral (fun _ => 0) 1 (Consistency.DataEq.numeral 1)]
    exact Consistency.Truth.eq eqNum .refl (.data (Consistency.DataEq.numeral 0))
      (.data (Consistency.DataEq.numeral 1))
  exact Consistency.no_closed_proof sound' truth
    (fun same => absurd (Consistency.numClass_injective (model_laws fun _ => 0).truth.numerals same)
      (by decide)) _ coded

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
