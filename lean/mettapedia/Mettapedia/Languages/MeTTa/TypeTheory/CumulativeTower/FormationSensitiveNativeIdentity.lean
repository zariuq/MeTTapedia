import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveNativeListEliminationPreservation

/-!
# Refined formation and reflexivity computation for native identity elimination

The original identity eliminator and its original iota rule are qualified in
the existing combined List, identity and mapRel package. Formation certificates
are constructed in the refined judgment, independently of the raw certificates.
The declaration telescope recovers every argument from an arbitrary admitted
application and replays the result at its original displayed type.

The conversion boundary is an explicit hypothesis of argument recovery and
preservation. No new computation rule, equality principle, runtime strategy,
normalization theorem or combined-package conversion boundary is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveNativeIdentity

open Presentation Presentation.Declaration NativeIndexedFamilies RussellTarski
open Intrinsic
open FormationSensitiveNativeList (Typing)
open FormationSensitive (DeclarationSpine ContextFormation)

variable {n : Nat}

theorem identityMotiveType_hasType :
    Typing contextAX identityMotiveType (sortTm identityMotiveLevel) := by
  unfold contextAX identityMotiveType identityMotiveLevel identityMotiveInnerLevel
  apply FormationSensitive.Typing.piForm
  · exact .var 1
  · exact .sort elementLevel
  · apply FormationSensitive.Typing.piForm
    · exact .idForm (.var 2) (.sort elementLevel) (.var 1) (.var 0)
    · exact .sort elementLevel
    · exact .headType (.sort motiveLevel)
    · exact .sort (.succ motiveLevel)
    · exact .sorts elementLevel (.succ motiveLevel)
  · exact .sort (.max elementLevel (.succ motiveLevel))
  · exact .sorts elementLevel (.max elementLevel (.succ motiveLevel))

theorem identityReflCaseType_hasType :
    Typing contextAXP identityReflCaseType (sortTm motiveLevel) := by
  have motiveTyped : Typing contextAXP (.var 0)
      (.pi (.var 2) (.pi (.id (.var 3) (.var 2) (.var 0)) (sortTm motiveLevel))) :=
    .var 0
  have pointTyped : Typing contextAXP (.var 1) (.var 2) := .var 1
  have first := FormationSensitive.Typing.appElim motiveTyped pointTyped
  have firstTyped : Typing contextAXP (.app (.var 0) (.var 1))
      (.pi (.id (.var 2) (.var 1) (.var 1)) (sortTm motiveLevel)) := by
    convert first using 1
    decide
  have result := FormationSensitive.Typing.appElim firstTyped (.reflIntro pointTyped)
  convert result using 1 <;> decide

theorem identityEliminateResultType_hasType :
    Typing contextAXPD identityEliminateResultType (sortTm identityEliminateResultLevel) := by
  unfold identityEliminateResultType identityEliminateResultLevel
  apply FormationSensitive.Typing.piForm
  · exact .var 3
  · exact .sort elementLevel
  · apply FormationSensitive.Typing.piForm
    · exact .idForm (.var 4) (.sort elementLevel) (.var 3) (.var 0)
    · exact .sort elementLevel
    · have motiveTyped : Typing contextAXPDYQ (.var 3)
          (.pi (.var 5) (.pi (.id (.var 6) (.var 5) (.var 0)) (sortTm motiveLevel))) :=
        .var 3
      have endpointTyped : Typing contextAXPDYQ (.var 1) (.var 5) := .var 1
      have first := FormationSensitive.Typing.appElim motiveTyped endpointTyped
      have firstTyped : Typing contextAXPDYQ (.app (.var 3) (.var 1))
          (.pi (.id (.var 5) (.var 4) (.var 1)) (sortTm motiveLevel)) := by
        convert first using 1
        decide
      have equalityTyped : Typing contextAXPDYQ (.var 0)
          (.id (.var 5) (.var 4) (.var 1)) := .var 0
      have result := FormationSensitive.Typing.appElim firstTyped equalityTyped
      simpa only [contextAXPDYQ, contextAXPDY, sortTm, inst0, subst] using result
    · exact .sort motiveLevel
    · exact .sorts elementLevel motiveLevel
  · exact .sort (.max elementLevel motiveLevel)
  · exact .sorts elementLevel (.max elementLevel motiveLevel)

/-- The complete original declaration, including the equality-indexed motive,
is independently formed in the combined package's refined judgment. -/
theorem identityEliminateType_hasType :
    Typing (.nil : Tower.Ctx 0) identityEliminateType
      (sortTm identityEliminateDeclarationLevel) := by
  unfold identityEliminateType identityEliminateDeclarationLevel
    identityAfterPointLevel identityAfterMotiveLevel identityAfterReflLevel
  apply FormationSensitive.Typing.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply FormationSensitive.Typing.piForm
    · exact .var 0
    · exact .sort elementLevel
    · apply FormationSensitive.Typing.piForm
      · exact identityMotiveType_hasType
      · exact .sort identityMotiveLevel
      · apply FormationSensitive.Typing.piForm
        · exact identityReflCaseType_hasType
        · exact .sort motiveLevel
        · exact identityEliminateResultType_hasType
        · exact .sort identityEliminateResultLevel
        · exact .sorts motiveLevel identityEliminateResultLevel
      · exact .sort identityAfterReflLevel
      · exact .sorts identityMotiveLevel identityAfterReflLevel
    · exact .sort identityAfterMotiveLevel
    · exact .sorts elementLevel identityAfterMotiveLevel
  · exact .sort identityAfterPointLevel
  · exact .sorts (.succ elementLevel) identityAfterPointLevel

theorem identityEliminateConstant_hasType {context : Tower.Ctx n} :
    Typing context (.const identityEliminateName) (liftClosed identityEliminateType) := by
  apply FormationSensitive.Typing.const (u := .sort identityEliminateDeclarationLevel)
  · decide
  · exact identityEliminateType_hasType
  · exact .sort identityEliminateDeclarationLevel

theorem contextAXPD_formed : ContextFormation IntrinsicRelator.rules contextAXPD :=
  .snoc
    (.snoc
      (.snoc
        (.snoc .nil (.headType (.sort elementLevel)) (.sort (.succ elementLevel)))
        (.var 0) (.sort elementLevel))
      identityMotiveType_hasType (.sort identityMotiveLevel))
    identityReflCaseType_hasType (.sort motiveLevel)

theorem contextAXPDYQ_formed : ContextFormation IntrinsicRelator.rules contextAXPDYQ :=
  .snoc (.snoc contextAXPD_formed (.var 3) (.sort elementLevel))
    (.idForm (.var 4) (.sort elementLevel) (.var 3) (.var 0)) (.sort elementLevel)

theorem identityEliminateAtParameters_hasType :
    Typing contextAXPD identityEliminateAtParameters identityEliminateAtParametersType := by
  have elementTyped : Typing contextAXPD (.var 3) (sortTm elementLevel) := .var 3
  have pointTyped : Typing contextAXPD (.var 2) (.var 3) := .var 2
  have motiveTyped : Typing contextAXPD (.var 1)
      (rename wk (rename wk identityMotiveType)) := .var 1
  have methodTyped : Typing contextAXPD (.var 0) (rename wk identityReflCaseType) := .var 0
  have first := FormationSensitive.Typing.appElim
    (identityEliminateConstant_hasType (context := contextAXPD)) elementTyped
  have second := FormationSensitive.Typing.appElim first pointTyped
  have third := FormationSensitive.Typing.appElim second motiveTyped
  have fourth := FormationSensitive.Typing.appElim third methodTyped
  convert fourth using 1 <;> decide

theorem identityIotaLeft_hasType : Typing contextAXPD identityIotaLeft identityIotaResultType := by
  have pointTyped : Typing contextAXPD (.var 2) (.var 3) := .var 2
  have first := FormationSensitive.Typing.appElim identityEliminateAtParameters_hasType pointTyped
  have result := FormationSensitive.Typing.appElim first (.reflIntro pointTyped)
  convert result using 1 <;> decide

theorem identityIotaRight_hasType : Typing contextAXPD identityIotaRight identityIotaResultType :=
  .var 0

theorem identityIota_judgments :
    FormationSensitive.Judgment IntrinsicRelator.rules contextAXPD identityIotaLeft identityIotaResultType ∧
    FormationSensitive.Judgment IntrinsicRelator.rules contextAXPD identityIotaRight identityIotaResultType :=
  ⟨⟨contextAXPD_formed, identityIotaLeft_hasType⟩,
    ⟨contextAXPD_formed, identityIotaRight_hasType⟩⟩

/-- Typed substitution keeps the exact endpoint and reflexivity witness in
the selected motive; the ambient context is independently formed. -/
theorem identityIota_substitute {context : Tower.Ctx n} {substitution : Sub Tower.Head 4 n}
    (formed : ContextFormation IntrinsicRelator.rules context)
    (typed : FormationSensitive.CtxMor IntrinsicRelator.rules contextAXPD context substitution) :
    FormationSensitive.Judgment IntrinsicRelator.rules context
        (subst substitution identityIotaLeft) (subst substitution identityIotaResultType) ∧
      FormationSensitive.Judgment IntrinsicRelator.rules context
        (subst substitution identityIotaRight) (subst substitution identityIotaResultType) :=
  ⟨identityIota_judgments.1.substitute formed typed,
    identityIota_judgments.2.substitute formed typed⟩

def identityIota_substitutedEvidence (substitution : Sub Tower.Head 4 n) :
    Intrinsic.IotaEvidence n (subst substitution identityIotaLeft) (subst substitution identityIotaRight) :=
  (Intrinsic.IotaEvidence.identity (.var 3) (.var 2) (.var 1) (.var 0)).substitute substitution

theorem identityIota_substitutedRoot (substitution : Sub Tower.Head 4 n) :
    IntrinsicRelator.rules.computation.step
      (subst substitution identityIotaLeft) (subst substitution identityIotaRight) :=
  .declared ⟨.list (identityIota_substitutedEvidence substitution)⟩

/-! ## Recovery from arbitrary refined applications -/

def identityResult : Tower.Tm 6 := .app (.app (.var 3) (.var 1)) (.var 0)

def identitySubstitution
    (element point motive reflCase endpoint equality : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub equality (consSub endpoint (identitySchemaSubstitution element point motive reflCase))

theorem identitySpine (context : Tower.Ctx n) :
    DeclarationSpine IntrinsicRelator.rules context
      (.const identityEliminateName) (liftClosed identityEliminateType) := by
  apply DeclarationSpine.constant (u := .sort identityEliminateDeclarationLevel)
  · decide
  · exact identityEliminateType_hasType
  · exact .sort identityEliminateDeclarationLevel

/-- Recovery fixes all declared argument types, including the exact identity
endpoints, then supplies replay at the observed displayed result type. -/
theorem identityArguments (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element point motive reflCase endpoint equality displayed : Tower.Tm n}
    (observed : Typing context
      (identityEliminateApp element point motive reflCase endpoint equality) displayed) :
    FormationSensitive.CtxMor IntrinsicRelator.rules contextAXPD context
        (identitySchemaSubstitution element point motive reflCase) ∧
      Typing context endpoint element ∧ Typing context equality (.id element point endpoint) ∧
      (∀ {replacement}, Typing context replacement (.app (.app motive endpoint) equality) →
        Typing context replacement displayed) := by
  obtain ⟨typed, _, _, replay⟩ := DeclarationSpine.recoverTelescope
    FormationSensitiveNativeListElimination.universes boundary formed
    contextAXPDYQ identityResult
    (identitySubstitution element point motive reflCase endpoint equality)
    (identitySpine context) observed
  exact ⟨typed.dropNewest.dropNewest, typed (1 : Fin 6), typed (0 : Fin 6), replay⟩

/-- Every admitted actual identity root preserves its original displayed
result, including the conversions and cumulativity used by that derivation. -/
theorem identity_preserves (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} (formed : ContextFormation IntrinsicRelator.rules context)
    {element point motive reflCase displayed : Tower.Tm n}
    (observed : Typing context
      (identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    Typing context reflCase displayed := by
  obtain ⟨parameters, _, _, replay⟩ := identityArguments boundary formed observed
  exact replay (identityIota_substitute formed parameters).2.typing

theorem identity_judgment_preserved (boundary : PiConversionBoundary IntrinsicRelator.rules)
    {context : Tower.Ctx n} {element point motive reflCase displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicRelator.rules context
      (identityEliminateApp element point motive reflCase point (.refl point)) displayed) :
    FormationSensitive.Judgment IntrinsicRelator.rules context reflCase displayed :=
  ⟨judgment.context, identity_preserves boundary judgment.context judgment.typing⟩

/-! ## Endpoint and branch controls -/

/-- At the actual combined root relation, identity elimination computes only
at the repeated endpoint and its reflexivity witness, to the selected method.
This is exact authored root inversion, not a conversion normal-form theorem. -/
theorem identity_root_iff
    {element point motive reflCase endpoint equality output : Tower.Tm n} :
    IntrinsicRelator.rules.computation.step
        (identityEliminateApp element point motive reflCase endpoint equality) output ↔
      endpoint = point ∧ equality = .refl point ∧ output = reflCase := by
  constructor
  · intro root
    cases root with
    | inherited impossible => exact impossible.elim
    | declared evidence =>
        rcases evidence with ⟨evidence⟩
        cases evidence with
        | list evidence =>
            cases evidence with
            | identity => exact ⟨rfl, rfl, rfl⟩
        | rel evidence => cases evidence
  · rintro ⟨rfl, rfl, rfl⟩
    exact .declared ⟨.list (.identity _ _ _ _)⟩

/-- The motive really consumes both an endpoint and its identity evidence;
changing only that evidence changes the raw displayed motive application. -/
theorem endpoint_and_path_remain_in_result :
    (identityResult : Tower.Tm 6) ≠ .app (.app (.var 3) (.var 1)) (.refl (.var 4)) := by
  decide

/-- The original combined root computes the independently admitted canonical
redex to its selected method. -/
theorem canonical_identity_root :
    IntrinsicRelator.rules.computation.step identityIotaLeft identityIotaRight :=
  .declared ⟨.list (.identity (.var 3) (.var 2) (.var 1) (.var 0))⟩

/-- Selecting the motive instead of the reflexivity method is not an
authored root step. This does not assert nonconvertibility. -/
theorem wrong_method_not_root :
    ¬ IntrinsicRelator.rules.computation.step identityIotaLeft (.var 1 : Tower.Tm 4) := by
  intro root
  have selected := (identity_root_iff.mp root).2.2
  cases selected

/-- Changing only the selected endpoint does not preserve the original
reflexivity computation, even with all other parameters retained. -/
theorem changed_endpoint_not_root (output : Tower.Tm 5) :
    ¬ IntrinsicRelator.rules.computation.step
      (identityEliminateApp (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) (.refl (.var 3))) output := by
  intro root
  have endpoints := (identity_root_iff.mp root).1
  cases endpoints

#print axioms identityMotiveType_hasType
#print axioms identityReflCaseType_hasType
#print axioms identityEliminateResultType_hasType
#print axioms identityEliminateType_hasType
#print axioms contextAXPDYQ_formed
#print axioms identityIota_judgments
#print axioms identityIota_substitute
#print axioms identityIota_substitutedRoot
#print axioms identityArguments
#print axioms identity_preserves
#print axioms identity_judgment_preserved
#print axioms identity_root_iff
#print axioms endpoint_and_path_remain_in_result
#print axioms canonical_identity_root
#print axioms wrong_method_not_root
#print axioms changed_endpoint_not_root

end FormationSensitiveNativeIdentity
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
