import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.CheckedDefinitionalExpansion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.OpaqueRelatorExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationAdmissionReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay

/-!
# Transparent definitions over native List, identity and relator computation

Ordered definitions expand relative to the existing native computation, not
to a root-empty calculus. A finite guard retains native declaration names.
The actual five root cases commute with expansion, so the existing native
conversion boundary transfers to the extended package. Prefix replay earns
definition-body typing, giving contextual preservation for the combined rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.TransparentRelatorExtension

open Presentation Presentation.Declaration NativeIndexedFamilies
open Presentation.ConstantExpansion
open Presentation.FormationSensitive (Typing Judgment ContextFormation)

variable {n : Nat}

def nativeNames : List DeclName :=
  [Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName,
    IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName,
    IntrinsicRelator.consRelName, IntrinsicRelator.eliminateName]

/-- Native declarations retain their original computation; this guard follows
selected lookup, not mere membership in an authored list. -/
def protectsNative (entries : List (DeclName × Entry Tower.Head)) : Bool :=
  nativeNames.all fun name => ((Signature.ofList entries).valueOf? name).isNone

abbrev rules (entries : List (DeclName × Entry Tower.Head)) : Rules Tower.Head :=
  extendRules IntrinsicRelator.rules (Signature.ofList entries)

def bodies (entries : List (DeclName × Entry Tower.Head)) : Bodies Tower.Head :=
  Checked.bodies (Signature.ofList entries) (entries.length + 1)

theorem native_fixed (entries : List (DeclName × Entry Tower.Head))
    (nativeSafe : protectsNative entries = true) :
    ∀ name ∈ nativeNames, bodies entries name = .const name := by
  intro name member
  have opaqueName := List.all_eq_true.mp nativeSafe name member
  exact Checked.bodies_of_opaque _ _ (Option.isNone_iff_eq_none.mp opaqueName)

/-- Expansion retains all five native root shapes and their actual reducts,
including the recursive relator call and the selected reflexivity method. -/
theorem native_root_expands (replacement : Bodies Tower.Head)
    (fixed : ∀ name ∈ nativeNames, replacement name = .const name)
    {left right : Tower.Tm n}
    (root : IntrinsicRelator.rules.computation.step left right) :
    IntrinsicRelator.rules.computation.step (expand replacement left) (expand replacement right) := by
  have nilFixed := fixed Intrinsic.nilName (by simp [nativeNames])
  have consFixed := fixed Intrinsic.consName (by simp [nativeNames])
  have listElimFixed := fixed Intrinsic.eliminateName (by simp [nativeNames])
  have identityFixed := fixed Intrinsic.identityEliminateName (by simp [nativeNames])
  have nilRelFixed := fixed IntrinsicRelator.nilRelName (by simp [nativeNames])
  have consRelFixed := fixed IntrinsicRelator.consRelName (by simp [nativeNames])
  have relElimFixed := fixed IntrinsicRelator.eliminateName (by simp [nativeNames])
  cases root with
  | inherited impossible => exact impossible.elim
  | delta lookup =>
      rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup
      cases lookup
  | declared evidence =>
      obtain ⟨evidence⟩ := evidence
      cases evidence with
      | list evidence =>
          cases evidence <;>
            simp only [Intrinsic.nilApp, Intrinsic.consApp, Intrinsic.eliminateApp,
              Intrinsic.identityEliminateApp, expand, nilFixed, consFixed,
              listElimFixed, identityFixed, liftClosed, rename]
          · exact .declared ⟨.list (.nil _ _ _ _)⟩
          · exact .declared ⟨.list (.cons _ _ _ _ _ _)⟩
          · exact .declared ⟨.list (.identity _ _ _ _)⟩
      | rel evidence =>
          cases evidence <;>
            simp only [Intrinsic.nilApp, Intrinsic.consApp, IntrinsicRelator.nilRelApp,
              IntrinsicRelator.consRelApp, IntrinsicRelator.eliminateApp, expand,
              nilFixed, consFixed, nilRelFixed, consRelFixed, relElimFixed, liftClosed, rename]
          · exact .declared ⟨.rel (.nil _ _ _ _ _ _)⟩
          · exact .declared ⟨.rel (.cons _ _ _ _ _ _ _ _ _ _ _ _)⟩

/-- Every open conversion in the extended calculus is exactly native
conversion after the computed transparent expansion. Native roots remain
available on the target side; no confluence assumption is supplied here. -/
theorem conversion_iff (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true) (left right : Tower.Tm n) :
    Conv (rules entries).headEq left right (rules entries).computation ↔
      Conv IntrinsicRelator.rules.headEq (expand (bodies entries) left)
        (expand (bodies entries) right) IntrinsicRelator.rules.computation := by
  apply conversion_iff_of_roots (bodies entries)
    (Checked.constants_convert IntrinsicRelator.rules (Signature.ofList entries) (entries.length + 1))
    ?_ (fun root => RootStep.inherited root) left right
  intro k source target root
  cases root with
  | inherited native =>
      exact .rel _ _ (.root (native_root_expands _ (native_fixed entries nativeSafe) native))
  | @delta name value lookup =>
      change Conv IntrinsicRelator.rules.headEq (liftClosed (bodies entries name))
        (expand (bodies entries) (liftClosed value)) IntrinsicRelator.rules.computation
      rw [expand_liftClosed]
      have fixed := Checked.check_definitions entries (entries.length + 1)
        (Checked.Ordered.expansion_checked entries ordered) lookup
      change Conv IntrinsicRelator.rules.headEq
        (liftClosed (Checked.bodies (Signature.ofList entries) (entries.length + 1) name))
        (liftClosed (expand (Checked.bodies (Signature.ofList entries) (entries.length + 1)) value))
        IntrinsicRelator.rules.computation
      rw [fixed]
      exact .refl _
  | declared impossible =>
      rw [Signature.computation_ofList] at impossible
      exact impossible.elim

theorem pi_boundary (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true) : PiConversionBoundary (rules entries) where
  components conversion := by
    obtain ⟨domain, codomain⟩ := NativeRelatorConversionParallel.nativePiConversionBoundary.components
      ((conversion_iff entries ordered nativeSafe _ _).mp conversion)
    exact ⟨(conversion_iff entries ordered nativeSafe _ _).mpr domain,
      (conversion_iff entries ordered nativeSafe _ _).mpr codomain⟩
  headDisjoint conversion := NativeRelatorConversionParallel.nativePiConversionBoundary.headDisjoint
    ((conversion_iff entries ordered nativeSafe _ _).mp conversion)

theorem sigma_boundary (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true) : SigmaConversionBoundary (rules entries) where
  components conversion := by
    obtain ⟨domain, codomain⟩ := NativeRelatorConversionParallel.nativeSigmaConversionBoundary.components
      ((conversion_iff entries ordered nativeSafe _ _).mp conversion)
    exact ⟨(conversion_iff entries ordered nativeSafe _ _).mpr domain,
      (conversion_iff entries ordered nativeSafe _ _).mpr codomain⟩
  headDisjoint conversion := NativeRelatorConversionParallel.nativeSigmaConversionBoundary.headDisjoint
    ((conversion_iff entries ordered nativeSafe _ _).mp conversion)

/-- The existing conversion-certificate checker covers the extended relation
after expansion. This is evidence checking, not total search for a code. -/
theorem checked_conversion_iff (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true) (left right : Tower.Tm n) :
    Conv (rules entries).headEq left right (rules entries).computation ↔
      ∃ code, NativeRelatorConversionChecking.check code
        (expand (bodies entries) left) (expand (bodies entries) right) = true :=
  (conversion_iff entries ordered nativeSafe left right).trans
    NativeRelatorConversionChecking.conversion_iff_checked

/-- Root preservation checks definition bodies and reuses the five existing
native schema proofs on arbitrary judgments of the extended package. -/
theorem root_preservation (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true)
    (typed : ∀ name body, (Signature.ofList entries).valueOf? name = some body →
      ∃ declared, (rules entries).constantType name = some declared ∧
        Typing (rules entries) .nil body declared) :
    FormationSensitive.RootPreservation (rules entries) := by
  intro k context source target type formed observed root
  have boundary := pi_boundary entries ordered nativeSafe
  cases root with
  | inherited native =>
      cases native with
      | inherited impossible => exact impossible.elim
      | delta lookup =>
          rw [IntrinsicRelator.rawSignature_valueOf_none] at lookup
          cases lookup
      | declared evidence =>
          obtain ⟨evidence⟩ := evidence
          cases evidence with
          | list evidence =>
              cases evidence with
              | nil => exact OpaqueRelatorExtension.list_nil_preserves boundary formed observed
              | cons => exact OpaqueRelatorExtension.list_cons_preserves boundary formed observed
              | identity => exact OpaqueRelatorExtension.identity_preserves boundary formed observed
          | rel evidence =>
              cases evidence with
              | nil => exact OpaqueRelatorExtension.relator_nil_preserves boundary formed observed
              | cons => exact OpaqueRelatorExtension.relator_cons_preserves boundary formed observed
  | delta lookup =>
      obtain ⟨declared, known, checked⟩ := typed _ _ lookup
      exact observed.unfoldConstant known checked
  | declared impossible =>
      rw [Signature.computation_ofList] at impossible
      exact impossible.elim

/-- Arbitrary finite contextual beta/delta/native runs retain the original
displayed dependent type, including conversions involving the new aliases. -/
theorem steps_preserve (entries : List (DeclName × Entry Tower.Head))
    (ordered : Checked.Ordered.check entries = true)
    (nativeSafe : protectsNative entries = true)
    (typed : ∀ name body, (Signature.ofList entries).valueOf? name = some body →
      ∃ declared, (rules entries).constantType name = some declared ∧
        Typing (rules entries) .nil body declared)
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment (rules entries) context source displayed)
    (steps : ConversionCoherence.StepStar (rules entries) source target) :
    Judgment (rules entries) context target displayed :=
  judgment.steps_preserve OpaqueRelatorExtension.universes
    (pi_boundary entries ordered nativeSafe) (sigma_boundary entries ordered nativeSafe)
    (FormationSensitive.HeadPreservation.includeSignature
      (FormationSensitive.HeadPreservation.includeSignature
        FormationSensitive.towerHeadPreservation IntrinsicRelator.rawSignature)
      (Signature.ofList entries))
    (root_preservation entries ordered nativeSafe typed) steps

local instance : DecidableRel IntrinsicRelator.rules.headEq := Tower.instDecidableHeadEq

namespace Admission

abbrev Certificate := DeclarationAdmissionReplay.Certificate Tower.Head NativeRelatorRootConversionCode.Code
abbrev Code := StructuralTypingReplay.Code Tower.Head
  (DeclarationAdmissionReplay.ConversionCode Tower.Head NativeRelatorRootConversionCode.Code)

/-- Replay every supplied declaration at its actual source prefix, then
qualify the combined conversion and native-operation boundary. -/
def check (entries : List (DeclName × Entry Tower.Head)) (certificates : List Certificate) : Bool :=
  Checked.Ordered.check entries && protectsNative entries &&
    DeclarationAdmissionReplay.check IntrinsicRelator.rules NativeRelatorRootConversionCode.rootDecoder
      [] entries certificates

theorem checked_bodies {entries : List (DeclName × Entry Tower.Head)} {certificates : List Certificate}
    (accepted : check entries certificates = true) :
    ∀ name body, (Signature.ofList entries).valueOf? name = some body →
      ∃ declared, (rules entries).constantType name = some declared ∧
        Typing (rules entries) .nil body declared := by
  simp only [check, Bool.and_eq_true] at accepted
  have replay := accepted.2
  exact (DeclarationAdmissionReplay.check_sound IntrinsicRelator.rules
    NativeRelatorRootConversionCode.rootDecoder replay).selected_bodies_typed IntrinsicRelator.rules

/-- Successful library checking discharges all definition-body premises of
the existing combined subject-preservation theorem. -/
theorem checked_runs_preserve {entries : List (DeclName × Entry Tower.Head)}
    {certificates : List Certificate} (accepted : check entries certificates = true)
    {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment (rules entries) context source displayed)
    (steps : ConversionCoherence.StepStar (rules entries) source target) :
    Judgment (rules entries) context target displayed := by
  have bodies := checked_bodies accepted
  simp only [check, Bool.and_eq_true] at accepted
  exact steps_preserve entries accepted.1.1 accepted.1.2 bodies judgment steps

end Admission

namespace Examples

def firstName : DeclName := `TransparentExtension.JFirst
def secondName : DeclName := `TransparentExtension.JSecond

def entries : List (DeclName × Entry Tower.Head) :=
  [(firstName, ⟨Intrinsic.identityEliminateType, some (.const Intrinsic.identityEliminateName)⟩),
    (secondName, ⟨Intrinsic.identityEliminateType, some (.const firstName)⟩)]

theorem ordered : Checked.Ordered.check entries = true := by decide +kernel
theorem native_safe : protectsNative entries = true := by decide +kernel

/-- A finite structural certificate for the actual dependent J declaration.
Its applications retain the equality-indexed motive, not an STT surrogate. -/
def motiveFormation : Admission.Code 2 :=
  .piForm (.sort Intrinsic.elementLevel) (.sort Intrinsic.identityMotiveInnerLevel) .var
    (.piForm (.sort Intrinsic.elementLevel) (.sort (.succ Intrinsic.motiveLevel))
      (.idForm (.sort Intrinsic.elementLevel) .var .var .var) .headType)

def methodFormation : Admission.Code 3 :=
  .appElim (.id (.var 2) (.var 1) (.var 1)) (sortTm Intrinsic.motiveLevel)
    (.appElim (.var 2)
      (.pi (.id (.var 3) (.var 2) (.var 0)) (sortTm Intrinsic.motiveLevel)) .var .var)
    (.reflIntro (.var 2) .var)

def resultFormation : Admission.Code 4 :=
  .piForm (.sort Intrinsic.elementLevel) (.sort (.max Intrinsic.elementLevel Intrinsic.motiveLevel)) .var
    (.piForm (.sort Intrinsic.elementLevel) (.sort Intrinsic.motiveLevel)
      (.idForm (.sort Intrinsic.elementLevel) .var .var .var)
      (.appElim (.id (.var 5) (.var 4) (.var 1)) (sortTm Intrinsic.motiveLevel)
        (.appElim (.var 5)
          (.pi (.id (.var 6) (.var 5) (.var 0)) (sortTm Intrinsic.motiveLevel)) .var .var) .var))

def declarationFormation : Admission.Code 0 :=
  .piForm (.sort (.succ Intrinsic.elementLevel)) (.sort Intrinsic.identityAfterPointLevel) .headType
    (.piForm (.sort Intrinsic.elementLevel) (.sort Intrinsic.identityAfterMotiveLevel) .var
      (.piForm (.sort Intrinsic.identityMotiveLevel) (.sort Intrinsic.identityAfterReflLevel) motiveFormation
        (.piForm (.sort Intrinsic.motiveLevel) (.sort Intrinsic.identityEliminateResultLevel)
          methodFormation resultFormation)))

def certificate : Admission.Certificate :=
  ⟨.sort Intrinsic.identityEliminateDeclarationLevel, declarationFormation,
    some (.const (.sort Intrinsic.identityEliminateDeclarationLevel) declarationFormation)⟩

theorem library_checked : Admission.check entries [certificate, certificate] = true := by decide +kernel

theorem forward_reference_rejected : Admission.check entries.reverse [certificate, certificate] = false :=
  by decide +kernel

/-- Prefix replay itself rejects the future reference, independently of the
additional dependency-order guard used to qualify execution. -/
theorem forward_reference_replay_rejected :
    DeclarationAdmissionReplay.check IntrinsicRelator.rules NativeRelatorRootConversionCode.rootDecoder
      [] entries.reverse [certificate, certificate] = false := by decide +kernel

theorem malformed_formation_rejected :
    Admission.check entries [{ certificate with formation := .var }, certificate] = false := by decide +kernel

theorem missing_body_certificate_rejected :
    Admission.check entries [{ certificate with value? := none }, certificate] = false := by decide +kernel

theorem duplicate_name_rejected :
    Admission.check (entries ++ entries.take 1) [certificate, certificate, certificate] = false := by decide +kernel

theorem alias_typed {name : DeclName} {context : Tower.Ctx n}
    (known : (rules entries).constantType name = some Intrinsic.identityEliminateType) :
    Typing (rules entries) context (.const name) (liftClosed Intrinsic.identityEliminateType) :=
  .const known
    (FormationSensitiveNativeIdentity.identityEliminateType_hasType.includeSignature (Signature.ofList entries))
    (.sort Intrinsic.identityEliminateDeclarationLevel)

/-- Prefix replay earns both definitions' typing against the final combined
declarations. Native-name preservation alone does not supply this premise. -/
theorem bodies_typed (name : DeclName) (body : Tower.Tm 0)
    (lookup : (Signature.ofList entries).valueOf? name = some body) :
    ∃ declared, (rules entries).constantType name = some declared ∧
      Typing (rules entries) .nil body declared :=
  Admission.checked_bodies library_checked name body lookup

def applyAtParameters (function : Tower.Tm 4) : Tower.Tm 4 :=
  .app (.app (.app (.app (.app (.app function (.var 3)) (.var 2)) (.var 1))
    (.var 0)) (.var 2)) (.refl (.var 2))

def source : Tower.Tm 4 := applyAtParameters (.const secondName)

/-- The aliased operation is admitted before it executes, in the actual
endpoint-and-equality-indexed motive telescope of J. -/
theorem source_admitted : Judgment (rules entries) Intrinsic.contextAXPD source
    Intrinsic.identityIotaResultType := by
  refine ⟨FormationSensitiveNativeIdentity.contextAXPD_formed.includeSignature
    (Signature.ofList entries), ?_⟩
  have element : Typing (rules entries) Intrinsic.contextAXPD (.var 3)
      (sortTm Intrinsic.elementLevel) := .var 3
  have point : Typing (rules entries) Intrinsic.contextAXPD (.var 2) (.var 3) := .var 2
  have motive : Typing (rules entries) Intrinsic.contextAXPD (.var 1)
      (rename wk (rename wk Intrinsic.identityMotiveType)) := .var 1
  have method : Typing (rules entries) Intrinsic.contextAXPD (.var 0)
      (rename wk Intrinsic.identityReflCaseType) := .var 0
  have first := Typing.appElim
    (alias_typed (context := Intrinsic.contextAXPD) (name := secondName) (by decide)) element
  have second := Typing.appElim first point
  have third := Typing.appElim second motive
  have fourth := Typing.appElim third method
  have fifth := Typing.appElim fourth point
  have sixth := Typing.appElim fifth (.reflIntro point)
  convert sixth using 1 <;> decide +kernel

private theorem apply_step {first second : Tower.Tm 4}
    (step : Step (rules entries).headEq first second (rules entries).computation) :
    Step (rules entries).headEq (applyAtParameters first) (applyAtParameters second)
      (rules entries).computation :=
  .congAppFun (.congAppFun (.congAppFun (.congAppFun (.congAppFun (.congAppFun step)))))

/-- The actual run contains two delta steps followed by the existing J root.
It is not merely a conversion proof between the endpoints. -/
theorem selected_run : ConversionCoherence.StepStar (rules entries) source (.var 0) := by
  have second : Step (rules entries).headEq (.const secondName : Tower.Tm 4)
      (.const firstName) (rules entries).computation :=
    .root (RootStep.delta (base := IntrinsicRelator.rules) (signature := Signature.ofList entries)
      (n := 4) (name := secondName) (value := .const firstName) (by decide))
  have first : Step (rules entries).headEq (.const firstName : Tower.Tm 4)
      (.const Intrinsic.identityEliminateName) (rules entries).computation :=
    .root (RootStep.delta (base := IntrinsicRelator.rules) (signature := Signature.ofList entries)
      (n := 4) (name := firstName) (value := .const Intrinsic.identityEliminateName) (by decide))
  exact .tail (.tail (.tail .refl (apply_step second)) (apply_step first))
    (.root (.inherited FormationSensitiveNativeIdentity.canonical_identity_root))

theorem selected_run_preserves : Judgment (rules entries) Intrinsic.contextAXPD (.var 0)
    Intrinsic.identityIotaResultType :=
  Admission.checked_runs_preserve library_checked source_admitted selected_run

def nativeCode : NativeRelatorConversionChecking.Code 4 :=
  .single (.root (.indexed (.identity (.var 3) (.var 2) (.var 1) (.var 0))))

abbrev ExtendedCode :=
  DeclarationAdmissionReplay.ConversionCode Tower.Head NativeRelatorRootConversionCode.Code

def appliedDelta (name : DeclName) : ExtendedCode 4 :=
  .single (.congAppFun (.congAppFun (.congAppFun (.congAppFun (.congAppFun
    (.congAppFun (.root (.delta name)) (.var 3)) (.var 2)) (.var 1)) (.var 0))
    (.var 2)) (.refl (.var 2)))

/-- The finite code retains both source unfolding steps before the native
identity step; no pre-expansion of the endpoints is needed. -/
def sourceCode : ExtendedCode 4 :=
  .trans (appliedDelta secondName) (.trans (appliedDelta firstName)
    (.single (.root (.inherited (.indexed (.identity (.var 3) (.var 2) (.var 1) (.var 0)))))))

theorem source_conversion_checked :
    DeclarationAdmissionReplay.conversionCheck IntrinsicRelator.rules
      NativeRelatorRootConversionCode.rootDecoder entries sourceCode source (.var 0) = true := by
  decide +kernel

theorem source_changed_result_rejected :
    DeclarationAdmissionReplay.conversionCheck IntrinsicRelator.rules
      NativeRelatorRootConversionCode.rootDecoder entries sourceCode source (.var 1) = false := by
  decide +kernel

theorem source_missing_definition_rejected :
    DeclarationAdmissionReplay.conversionCheck IntrinsicRelator.rules
      NativeRelatorRootConversionCode.rootDecoder (entries.take 1) sourceCode source (.var 0) = false := by
  decide +kernel

/-- The unchanged native conversion checker accepts the computed expansion of
the aliased source. It does not pretend to be a source delta-step decoder. -/
theorem expanded_conversion_checked :
    NativeRelatorConversionChecking.check nativeCode (expand (bodies entries) source)
      (expand (bodies entries) (.var 0)) = true := by decide +kernel

theorem changed_result_rejected :
    NativeRelatorConversionChecking.check nativeCode (expand (bodies entries) source)
      (expand (bodies entries) (.var 1)) = false := by decide +kernel

/-- Replacing the native eliminator itself is outside this extension class,
even if the replacement has no dependencies and passes the order check. -/
theorem native_replacement_rejected :
    let replacement : List (DeclName × Entry Tower.Head) :=
      [(Intrinsic.identityEliminateName, ⟨Intrinsic.identityEliminateType, some (.head .legacyGround)⟩)]
    Checked.Ordered.check replacement = true ∧ protectsNative replacement = false := by decide +kernel

end Examples

namespace DependentConversionExample

def carrierName : DeclName := `TransparentExtension.Carrier
def functionName : DeclName := `TransparentExtension.forgetCarrierAlias

def functionType : Tower.Tm 0 := .pi (.const carrierName) (.head .legacyGround)

def entries : List (DeclName × Entry Tower.Head) :=
  [(carrierName, ⟨sortTm Tower.zero, some (.head .legacyGround)⟩),
    (functionName, ⟨functionType, some (.lam (.var 0))⟩)]

def formation : Admission.Code 0 :=
  .piForm (.sort Tower.zero) (.sort Tower.zero)
    (.const (.sort (.succ Tower.zero)) .headType) .headType

def carrierCertificate : Admission.Certificate :=
  ⟨.sort (.succ Tower.zero), .headType, some .headType⟩

/-- A formed opaque declaration is admitted as an assumption, with no
definition body or claim that the base calculus supplies a witness. -/
theorem formed_assumption_checked :
    Admission.check [(carrierName, ⟨.head .legacyGround, none⟩)]
      [⟨.sort Tower.zero, .headType, none⟩] = true := by decide +kernel

theorem unformed_assumption_rejected :
    Admission.check [(carrierName, ⟨.lam (.var 0), none⟩)]
      [⟨.sort Tower.zero, .headType, none⟩] = false := by decide +kernel

theorem opaque_body_evidence_rejected :
    Admission.check [(carrierName, ⟨.head .legacyGround, none⟩)]
      [⟨.sort Tower.zero, .headType, some .headType⟩] = false := by decide +kernel

/-- The bound variable has the declared alias type; its return type is the
underlying carrier. A selected delta code justifies that conversion. -/
def bodyCertificate : Admission.Code 0 :=
  .lamIntro (.sort (.max Tower.zero Tower.zero)) formation
    (.convert (.const carrierName) (.sort Tower.zero) .var .headType
      (.single (.root (.delta carrierName))))

def functionCertificate : Admission.Certificate :=
  ⟨.sort (.max Tower.zero Tower.zero), formation, some bodyCertificate⟩

theorem library_checked :
    Admission.check entries [carrierCertificate, functionCertificate] = true := by decide +kernel

/-- Merely reusing the variable certificate cannot change its displayed type. -/
theorem omitted_conversion_rejected :
    Admission.check entries [carrierCertificate,
      { functionCertificate with value? := (some (.lamIntro
          (.sort (.max Tower.zero Tower.zero)) formation .var)) }] = false := by decide +kernel

theorem function_typed : Typing (rules entries) .nil (.lam (.var 0)) functionType := by
  obtain ⟨declared, selected, typed⟩ :=
    Admission.checked_bodies library_checked functionName (.lam (.var 0)) (by decide)
  have actual : (rules entries).constantType functionName = some functionType := by decide
  rw [actual] at selected
  cases Option.some.inj selected
  exact typed

end DependentConversionExample

#print axioms native_root_expands
#print axioms conversion_iff
#print axioms pi_boundary
#print axioms sigma_boundary
#print axioms checked_conversion_iff
#print axioms root_preservation
#print axioms steps_preserve
#print axioms Admission.checked_bodies
#print axioms Admission.checked_runs_preserve
#print axioms Examples.library_checked
#print axioms Examples.forward_reference_replay_rejected
#print axioms Examples.malformed_formation_rejected
#print axioms Examples.missing_body_certificate_rejected
#print axioms Examples.duplicate_name_rejected
#print axioms Examples.bodies_typed
#print axioms Examples.source_admitted
#print axioms Examples.selected_run
#print axioms Examples.selected_run_preserves
#print axioms Examples.source_conversion_checked
#print axioms Examples.source_changed_result_rejected
#print axioms Examples.source_missing_definition_rejected
#print axioms Examples.expanded_conversion_checked
#print axioms Examples.changed_result_rejected
#print axioms Examples.native_replacement_rejected
#print axioms DependentConversionExample.library_checked
#print axioms DependentConversionExample.formed_assumption_checked
#print axioms DependentConversionExample.unformed_assumption_rejected
#print axioms DependentConversionExample.opaque_body_evidence_rejected
#print axioms DependentConversionExample.omitted_conversion_rejected
#print axioms DependentConversionExample.function_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.TransparentRelatorExtension
