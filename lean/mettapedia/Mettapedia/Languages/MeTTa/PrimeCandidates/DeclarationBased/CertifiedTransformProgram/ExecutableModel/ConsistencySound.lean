import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyNumbers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencyIterJ
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Typings
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.CodeConstants

/-!
# Consistency of the executable package with the program's codes

The program's propositions are codes over the executable package:
implication, and the quantifier `all@A` and the equation `eq@A` at every
simple type `A` over `prop`, the numbers and the sets, decoded under the
identity reading. The instances are declared at the profile's own types, so
the package declares every quantifier and equation instance exactly as the
profile's signature does. The package with these codes is sound for the
consistency model:

* its universe rules are the model's;
* each of its root steps is a step of the model, or a decoding of a code;
* each of its constants is a valid term of its declared type. The code
  constants follow from the coherence of decoding, the numbers and their
  recursions by induction on numerals, identity elimination by the cast, and
  each definition by one equation from the fundamental lemma of the stage that
  types its right-hand side.

Hence no closed term proves `∀ n : num, zero = suc n`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency
open TelescopeAbstraction (closeType applyClosed)
open Mettapedia.Logic
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName U0 numT jType numRecType eqAtType sucMoveType keepType
  transportType composeType iterType returnIterType sucStepType stepFamily familyTelescope
  eqAtTelescope transportTelescope composeTelescope iterTelescope returnIterResult)

namespace CodeModel

variable (v : Nat → Nat)

/-- The carrier of every simple type is interpreted by the model. -/
theorem carrierOf_interpretable :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.Interpretable (model v)
  | .prop => .prop
  | .base .num => .num
  | .base .set =>
      .rigid ((modelRoles_of (name := setN) (by decide) (by decide) (by decide)
        (by decide)).trans roles_set)
        (by change setN ≠ propN; decide) (by change setN ≠ holdsN; decide)
  | .arr a b => .arr (carrierOf_interpretable a) (carrierOf_interpretable b)

/-- The carrier of a simple type, as a type of the package, is the profile's
type. -/
theorem carrierOf_term :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.term (model v) = typeTerm type
  | .prop => rfl
  | .base .num => rfl
  | .base .set => rfl
  | .arr a b => by
      have ha := carrierOf_term a
      have hb := carrierOf_term b
      simp only [carrierOf, Carrier.term, typeTerm, FormationSensitiveHOLInterface.typeAt] at ha hb ⊢
      rw [ha, hb, FormationSensitiveHOLInterface.typeAt_rename]

theorem programCodes_read : CodesRead (model v) programCodes where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := by
    intro a T found
    change (SetProfile.allInstance? a).map typeTerm = some T at found
    cases found' : SetProfile.allInstance? a with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, carrierOf_interpretable v type,
          (carrierOf_term v type).symm⟩
        change (SetProfile.allInstance? a).map carrierOf = _
        rw [found']
        rfl
  eq := by
    intro e T found
    change (SetProfile.eqInstance? e).map typeTerm = some T at found
    cases found' : SetProfile.eqInstance? e with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, carrierOf_interpretable v type,
          (carrierOf_term v type).symm⟩
        change (SetProfile.eqInstance? e).map carrierOf = _
        rw [found']
        rfl

/-! ## Stages -/

/-- A stage of the package whose constants are valid is sound for the model. -/
theorem stage_sound {allowed : DeclName → Bool}
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ValidTm (model v) .nil (.const name) type) :
    Sound (stage allowed) (model v) where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => ModelRoot.semantic (model_laws v) (programCodes_read v).decodes
    (.inl (model_step_of_rules ((stage_sub_rules _).computation step)))
  constants := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    split_ifs at declared with h
    exact constants h declared

theorem stage_sound_of {names : List DeclName}
    (constants : ∀ name ∈ names, ∀ {type : Tower.Tm 0}, allTypes name = some type →
      ValidTm (model v) .nil (.const name) type) :
    Sound (stage (allowedIn names)) (model v) :=
  stage_sound v fun {name _} allowed declared =>
    constants name (by simpa [allowedIn] using allowed) declared

/-- The package without constants or computations is sound. -/
theorem constantFree_sound : Sound (constantFreeRules rules) (model v) where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => nomatch step
  constants := fun declared => nomatch declared

/-! ## The constants with dependent types -/

theorem valid_numRec' : ValidTm (model v) .nil (.const numRecName) numRecType := by
  have sound₀ := stage_sound_of v (names := [numN, zeroN, sucN]) fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact valid_num v
    · exact valid_zero v
    · exact valid_suc v
  obtain ⟨validT, partsT, _⟩ := Derivable.valid sound₀ numRecType_typed trivial
  exact valid_numRec v (validT.validTy (.sort _)) partsT

theorem valid_j' : ValidTm (model v) .nil (.const jName) jType := by
  obtain ⟨w, hw, typed⟩ := jType_typed
  obtain ⟨validT, partsT, _⟩ := Derivable.valid (constantFree_sound v) typed trivial
  exact valid_j v (validT.validTy hw) partsT

theorem valid_iter' : ValidTm (model v) .nil (.const iterName) iterType := by
  have sound₀ := stage_sound_of v (names := [numN]) fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    obtain rfl := Option.some.inj declared
    exact valid_num v
  obtain ⟨validT, partsT, _⟩ := Derivable.valid sound₀ (iterType_typed (by simp)) trivial
  exact valid_iter v (validT.validTy (.sort _)) partsT

/-! ## Definitions by one equation -/

theorem model_rule {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ computations)
    {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    WhRed (model v).rules (model v).roles l r :=
  .single (WhStep.root (model_step_of_rules (rules_step mem h)))

theorem valid_eqAt : ValidTm (model v) .nil (.const eqAtName) eqAtType := by
  have sound₀ := stage_sound_of v (names := [numN, zeroN, sucN, addN])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact valid_num v
      · exact valid_zero v
      · exact valid_suc v
      · exact valid_add v
  exact ValidTm.definition (Θ := eqAtTele) (C := Package.U0) (rhs := eqAtRhs) sound₀
    ⟨_, .sort _, eqAtType_typed⟩ eqAtBody_typed
    fun σ => model_rule v (listed 4 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_keep : ValidTm (model v) .nil (.const keepName) keepType :=
  ValidTm.definition (Θ := keepTele) (C := .sigma (.var 3) (.app (.var 3) (.var 0)))
    (rhs := keepRhs)
    (stage_sound_of v (names := []) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, keepType_typed⟩ keepBody_typed
    fun σ => model_rule v (listed 6 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_transport : ValidTm (model v) .nil (.const transportName) transportType :=
  ValidTm.definition (Θ := transportTelescope) (C := .sigma (.var 5) (.app (.var 5) (.var 0)))
    (rhs := transportRhs)
    (stage_sound_of v (names := []) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, transportType_typed⟩ transportBody_typed
    fun σ => model_rule v (listed 7 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_compose : ValidTm (model v) .nil (.const composeName) composeType :=
  ValidTm.definition (Θ := composeTelescope) (C := .sigma (.var 5) (.app (.var 5) (.var 0)))
    (rhs := composeRhs)
    (stage_sound_of v (names := []) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, composeType_typed⟩ composeBody_typed
    fun σ => model_rule v (listed 8 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_sucMove : ValidTm (model v) .nil (.const sucMoveName) sucMoveType := by
  have sound₀ := stage_sound_of v (names := [numN, zeroN, sucN, addN, jName, eqAtName])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact valid_num v
      · exact valid_zero v
      · exact valid_suc v
      · exact valid_add v
      · exact valid_j' v
      · exact valid_eqAt v
  exact ValidTm.definition (Θ := eqAtTelescope) (C := Package.eqAtApp (SetProfile.sucNative (.var 1)))
    (rhs := sucMoveRhs) sound₀ ⟨_, .sort _, sucMoveType_typed (by simp) (by simp) (by simp)⟩
    (sucMoveBody_typed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    fun σ => model_rule v (listed 5 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_returnIter : ValidTm (model v) .nil (.const returnIterName) returnIterType := by
  have sound₀ := stage_sound_of v (names := [numN, zeroN, sucN, iterName])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact valid_num v
      · exact valid_zero v
      · exact valid_suc v
      · exact valid_iter' v
  exact ValidTm.definition (Θ := returnIterTele) (C := returnIterResult) (rhs := returnIterRhs)
    sound₀ ⟨_, .sort _, returnIterType_typed (by simp)⟩
    (returnIterBody_typed (by simp) (by simp))
    fun σ => model_rule v (listed 10 (by decide)) ⟨σ, rfl, rfl⟩

theorem valid_sucStep : ValidTm (model v) .nil (.const sucStepName) sucStepType := by
  have sound₀ := stage_sound_of v
    (names := [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName])
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        obtain rfl := Option.some.inj declared
      · exact valid_num v
      · exact valid_zero v
      · exact valid_suc v
      · exact valid_add v
      · exact valid_j' v
      · exact valid_eqAt v
      · exact valid_sucMove v
      · exact valid_transport v
  exact ValidTm.definition (Θ := eqAtTelescope) (C := .sigma numT (Package.eqAtApp (.var 0)))
    (rhs := sucStepRhs) sound₀ ⟨_, .sort _, sucStepType_typed⟩ sucStepBody_typed
    fun σ => model_rule v (listed 11 (by decide)) ⟨σ, rfl, rfl⟩

/-! ## The package -/

/-- Every declared constant of the executable package is a valid term of its
declared type. -/
theorem valid_declared {name : DeclName} {type : Tower.Tm 0} (declared : allTypes name = some type) :
    ValidTm (model v) .nil (.const name) type := by
  have mem := mem_of_lookup declared
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact valid_num v
  · exact valid_set v
  · exact valid_zero v
  · exact valid_suc v
  · exact valid_add v
  · exact valid_power v
  · exact valid_pow v
  · exact valid_numRec' v
  · exact valid_j' v
  · exact valid_eqAt v
  · exact valid_sucMove v
  · exact valid_keep v
  · exact valid_transport v
  · exact valid_compose v
  · exact valid_iter' v
  · exact valid_returnIter v
  · exact valid_sucStep v

/-- The executable package with the program's codes is sound for the model. -/
theorem objectSound : Sound objectRules (model v) where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := by
    intro n l r step
    refine ModelRoot.semantic (model_laws v) (programCodes_read v).decodes ?_
    rcases step with step | step
    · exact .inl (model_step_of_rules step)
    · exact .inr step
  constants := by
    intro name type declared
    change (programCodes.codeType name).orElse (fun _ => rules.constantType name) = some type
      at declared
    cases code : programCodes.codeType name with
    | some T =>
        rw [code] at declared
        cases declared
        exact valid_code (model_laws v) (programCodes_read v) code
    | none =>
        rw [code] at declared
        exact valid_declared v declared

/-! ## Consistency -/

/-- The code `∀ n : num, zero = suc n`, in any context. -/
def falseCode {n : Nat} : Tower.Tm n :=
  .app (.const allNumN)
    (.lam (.app (.app (.const eqNumN) (.const zeroN)) (.app (.const sucN) (.var 0))))

/-- Its truth value is that every value of the numbers is the successor of
zero's value: `∀ q, 0 = q + 1` in the model's numbers. -/
theorem falseCode_truth :
    Truth (model v).reading World.closed (falseCode (n := 0))
      (∀ q : Carrier.num.V (model v).reading,
        numClass (model v).toSetting.numerals 0 = sucClass (model v).toSetting.numerals q) := by
  have allNum : (model v).reading.allCarrier allNumN = some ⟨.data, .num⟩ := by
    change (SetProfile.allInstance? (SetProfile.allName SetProfile.numTy)).map carrierOf = _
    rw [SetProfile.allInstance?_allName]
    rfl
  have eqNum : (model v).reading.eqCarrier eqNumN = some ⟨.data, .num⟩ := by
    change (SetProfile.eqInstance? (SetProfile.eqName SetProfile.numTy)).map carrierOf = _
    rw [SetProfile.eqInstance?_eqName]
    rfl
  refine .all (A := .num) (φ := fun q => numClass _ 0 = sucClass _ q) allNum .refl
    (.dataArg fun {_ _ _} _ {s} related => ?_)
  refine Read.expand (.single (WhStep.beta _ _)) (.prop ?_)
  exact .eq (A := .num) eqNum .refl (.data DataEq.zero) (.data (DataEq.suc related))

/-- **Consistency.** No closed term of the executable package with the
program's codes proves `∀ n : num, zero = suc n`. -/
theorem consistent (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (programCodes.holdsOf (falseCode (n := 0))) :=
  no_closed_proof (objectSound fun _ => 0) (falseCode_truth fun _ => 0)
    (fun all => Nat.zero_ne_one (numClass_injective (model_laws fun _ => 0).truth.numerals
      ((all (numClass _ 0)).trans (sucClass_numClass 0)))) t

/-! ## Controls

The false proposition of the consistency theorem is a well-formed type of the
package, and the package proves some propositions: `holds (falseCode ⇒ falseCode)`
has the proof `λ x. x`, through the decoding of implication. -/

section Controls

variable {n : Nat} {Γ : Tower.Ctx n}

theorem declared_prop : objectRules.constantType propN = some Package.U0 :=
  programCodes.extend_constantType_of_code rules programCodes.codeType_prop

theorem declared_holds : objectRules.constantType holdsN = some programCodes.holdsType :=
  programCodes.extend_constantType_of_code rules (programCodes.codeType_holds (by decide))

theorem declared_imp : objectRules.constantType impN = some programCodes.impType :=
  programCodes.extend_constantType_of_code rules
    (programCodes.codeType_imp ⟨by decide, by decide⟩)

theorem declared_allNum : objectRules.constantType allNumN = some (programCodes.allType numT) :=
  declared_allName SetProfile.numTy

theorem declared_eqNum : objectRules.constantType eqNumN = some (programCodes.eqType numT) :=
  declared_eqName SetProfile.numTy

theorem declared_num : objectRules.constantType numN = some Package.U0 := rfl
theorem declared_zero : objectRules.constantType zeroN = some numT := rfl
theorem declared_suc : objectRules.constantType sucN = some (.pi numT numT) := rfl

theorem piO {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {level : LevelExpr}
    (hA : Typed objectRules Γ A (sortTm level))
    (hB : Typed objectRules (.snoc Γ A) B (sortTm level)) :
    Typed objectRules Γ (.pi A B) (sortTm level) :=
  .cumul (.piForm hA (.sort level) hB (.sort level) (.sorts level level))
    (fun _ => Nat.le_of_eq (Nat.max_self _))

theorem raiseO {T : Tower.Tm n} (typed : Typed objectRules Γ T Package.U0) :
    Typed objectRules Γ T U1 :=
  .cumul typed (fun _ => Nat.le_succ _)

theorem U0_typedO : Typed objectRules Γ Package.U0 U1 := .headType (.sort _)

theorem prop_typedO : Typed objectRules Γ (.const propN) Package.U0 :=
  .const declared_prop (.headType (.sort _)) (.sort _)

theorem num_typedO : Typed objectRules Γ numT Package.U0 :=
  .const declared_num (.headType (.sort _)) (.sort _)

theorem zero_typedO : Typed objectRules Γ (.const zeroN) numT :=
  .const declared_zero num_typedO (.sort _)

theorem suc_typedO : Typed objectRules Γ (.const sucN) (.pi numT numT) :=
  .const declared_suc (piO num_typedO num_typedO) (.sort Tower.zero)

theorem eqNum_typedO : Typed objectRules Γ (.const eqNumN) (.pi numT (.pi numT (.const propN))) :=
  .const declared_eqNum (piO num_typedO (piO num_typedO prop_typedO)) (.sort Tower.zero)

theorem allNum_typedO :
    Typed objectRules Γ (.const allNumN) (.pi (.pi numT (.const propN)) (.const propN)) :=
  .const declared_allNum (piO (piO num_typedO prop_typedO) prop_typedO) (.sort Tower.zero)

theorem holds_typedO : Typed objectRules Γ (.const holdsN) (.pi (.const propN) Package.U0) :=
  .const declared_holds (piO (raiseO prop_typedO) U0_typedO) (.sort _)

theorem imp_typedO :
    Typed objectRules Γ (.const impN) (.pi (.const propN) (.pi (.const propN) (.const propN))) :=
  .const declared_imp (piO prop_typedO (piO prop_typedO prop_typedO)) (.sort Tower.zero)

/-- The false code is a code of the package. -/
theorem falseCode_typed : Typed objectRules Γ falseCode (.const propN) := by
  have eqZero : Typed objectRules (.snoc Γ numT) (.app (.const eqNumN) (.const zeroN))
      (.pi numT (.const propN)) := .appElim eqNum_typedO zero_typedO
  have sucVar : Typed objectRules (.snoc Γ numT) (.app (.const sucN) (.var 0)) numT :=
    .appElim suc_typedO (.var 0)
  have body : Typed objectRules (.snoc Γ numT)
      (.app (.app (.const eqNumN) (.const zeroN)) (.app (.const sucN) (.var 0))) (.const propN) :=
    .appElim eqZero sucVar
  have predicate : Typed objectRules Γ
      (.lam (.app (.app (.const eqNumN) (.const zeroN)) (.app (.const sucN) (.var 0))))
      (.pi numT (.const propN)) :=
    .lamIntro (piO num_typedO prop_typedO) (.sort _) body
  exact .appElim allNum_typedO predicate

/-- `holds falseCode` is a type of the lowest universe. -/
theorem falseProposition_typed : Typed objectRules Γ (programCodes.holdsOf falseCode) Package.U0 :=
  .appElim holds_typedO falseCode_typed

/-- The package proves `holds (falseCode ⇒ falseCode)`, by `λ x. x`. -/
theorem selfImplication_proved :
    Typed objectRules .nil (.lam (.var 0))
      (programCodes.holdsOf (programCodes.impOf falseCode falseCode)) := by
  have decoded : Typed objectRules .nil
      (.pi (programCodes.holdsOf falseCode) (programCodes.holdsOf falseCode)) Package.U0 :=
    piO falseProposition_typed falseProposition_typed
  have impFalse : Typed objectRules .nil (.app (.const impN) falseCode)
      (.pi (.const propN) (.const propN)) := .appElim imp_typedO falseCode_typed
  have implication : Typed objectRules .nil (programCodes.impOf falseCode falseCode)
      (.const propN) := .appElim impFalse falseCode_typed
  have coded : Typed objectRules .nil
      (programCodes.holdsOf (programCodes.impOf falseCode falseCode)) Package.U0 :=
    .appElim holds_typedO implication
  have step : objectRules.computation.step
      (programCodes.holdsOf (programCodes.impOf (falseCode (n := 0)) falseCode))
      (.pi (programCodes.holdsOf falseCode) (programCodes.holdsOf falseCode)) :=
    programCodes.extend_decoder_step rules (DecoderStep.imp _ _)
  exact .conv (.lamIntro decoded (.sort _) (.var 0)) (.symm (.root step coded decoded)) (.sort _)

end Controls

/-! ## Controls at the higher carriers

Impredicative falsity `∀ p : prop. p`, built from `all@prop`, is a code of the
package whose truth value is `∀ P : Prop, P`, so no closed term proves it.
Equality of functions on the numbers is read extensionally and is not
trivial: `λ n. n` and `λ n. suc n` are unequal at `num → num`. -/

section HigherCarriers

variable {n : Nat} {Γ : Tower.Ctx n}

abbrev allPropN : DeclName := SetProfile.allName .prop
abbrev eqFunN : DeclName := SetProfile.eqName (.arr SetProfile.numTy SetProfile.numTy)

/-- Impredicative falsity: `∀ p : prop. p`. -/
def botCode {n : Nat} : Tower.Tm n := .app (.const allPropN) (.lam (.var 0))

theorem allProp_typedO :
    Typed objectRules Γ (.const allPropN) (.pi (.pi (.const propN) (.const propN)) (.const propN)) :=
  .const (declared_allName .prop) (piO (piO prop_typedO prop_typedO) prop_typedO) (.sort Tower.zero)

/-- Impredicative falsity is a code of the package. -/
theorem botCode_typed : Typed objectRules Γ botCode (.const propN) :=
  .appElim allProp_typedO (.lamIntro (piO prop_typedO prop_typedO) (.sort _) (.var 0))

/-- Its truth value is `∀ P : Prop, P`. -/
theorem botCode_truth :
    Truth (model v).reading World.closed (botCode (n := 0)) (∀ P : Prop, P) := by
  have allProp : (model v).reading.allCarrier allPropN = some ⟨.gen, .prop⟩ := by
    change (SetProfile.allInstance? (SetProfile.allName .prop)).map carrierOf = _
    rw [SetProfile.allInstance?_allName]
    rfl
  refine .all (A := .prop) (φ := fun P => P) allProp .refl (.genericArg fun P => ?_)
  exact Read.expand (.single (WhStep.beta _ _)) (Read.generic_prop _ rfl)

/-- **Consistency for impredicative falsity.** No closed term proves
`∀ p : prop. p`. -/
theorem consistent_bot (t : Tower.Tm 0) :
    ¬ Typed objectRules .nil t (programCodes.holdsOf (botCode (n := 0))) :=
  no_closed_proof (objectSound fun _ => 0) (botCode_truth fun _ => 0) (fun all => all False) t

/-- The identity and the successor on the numbers. -/
def idFun {n : Nat} : Tower.Tm n := .lam (.var 0)
def sucFun {n : Nat} : Tower.Tm n := .lam (.app (.const sucN) (.var 0))

theorem idFun_related {m : Nat} :
    DataEq (model v).toSetting.numerals (.arr .num .num) (idFun : Tower.Tm m) idFun := by
  intro _ ρ s s' related
  exact DataEq.expand (.single (WhStep.beta _ _)) (.single (WhStep.beta _ _)) related

theorem sucFun_related {m : Nat} :
    DataEq (model v).toSetting.numerals (.arr .num .num) (sucFun : Tower.Tm m) sucFun := by
  intro _ ρ s s' related
  exact DataEq.expand (.single (WhStep.beta _ _)) (.single (WhStep.beta _ _)) (DataEq.suc related)

/-- `eq@(num → num) (λ n. n) (λ n. suc n)` has a truth value, and it is false. -/
theorem funEq_false :
    ∃ P, Truth (model v).reading World.closed
      (.app (.app (.const eqFunN) (idFun (n := 0))) sucFun) P ∧ ¬ P := by
  have eqFun : (model v).reading.eqCarrier eqFunN = some ⟨.data, .arr .num .num⟩ := by
    change (SetProfile.eqInstance? (SetProfile.eqName (.arr SetProfile.numTy
      SetProfile.numTy))).map carrierOf = _
    rw [SetProfile.eqInstance?_eqName]
    rfl
  refine ⟨_, .eq eqFun .refl (.data (D := .arr .num .num) (idFun_related v))
    (.data (D := .arr .num .num) (sucFun_related v)), ?_⟩
  intro equal
  obtain ⟨k, first, second⟩ :=
    (dataValue_exact (model_laws v).truth.numerals equal : DataEq (model v).toSetting.numerals (.arr .num .num)
      (idFun : Tower.Tm 0) sucFun) idRen DataEq.zero
  have zero : NumVal (model v).toSetting (.app (Presentation.rename idRen idFun)
      (.const zeroN) : Tower.Tm 0) 0 := (NumVal.zero .refl).expand (.single (WhStep.beta _ _))
  have one : NumVal (model v).toSetting (.app (Presentation.rename idRen sucFun)
      (.const zeroN) : Tower.Tm 0) 1 :=
    (NumVal.suc .refl (NumVal.zero .refl)).expand (.single (WhStep.beta _ _))
  exact Nat.zero_ne_one ((NumVal.deterministic (model_laws v).truth zero first).trans
    (NumVal.deterministic (model_laws v).truth second one))

end HigherCarriers

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
