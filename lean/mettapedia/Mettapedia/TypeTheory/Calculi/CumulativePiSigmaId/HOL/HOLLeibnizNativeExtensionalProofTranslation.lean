import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalApplications
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation

/-!
# Native attachment of the HOL propositional-extensionality rule

The constructive Leibniz compiler remains unchanged and continues to reject
extensional proof constructors.  This module attaches one source
propositional-extensionality node to the explicitly declared extensional HOL
profile.  Its two implication subproofs must be accepted by the constructive
compiler, and the emitted native term applies the profile constant to those
actual compiled premises.

The result is converted back to the source equality proposition only through
the already proved equality-decoder conversion.  No extensional declaration
is installed as a computation rule.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeExtensionalProofTranslation

open Presentation Presentation.FormationSensitive Mettapedia.Logic
open HOL.UniformListInduction
open HOLLeibnizNativeProofTranslation
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLUniformList (rawImp rawAll)

abbrev SourceContext := HOLLeibnizNativeProofTranslation.SourceContext
abbrev Formula := HOLLeibnizNativeProofTranslation.Formula

/-- Transport a base proof-family conversion into the extensional profile.
The head map is the identity and the added declarations are opaque. -/
theorem include_conversion {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv FormationSensitiveHOLProofFamily.rules.headEq left right
      FormationSensitiveHOLProofFamily.rules.computation) :
    Conv FormationSensitiveHOLExtensionalProfile.rules.headEq left right
      FormationSensitiveHOLExtensionalProfile.rules.computation := by
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head)
      FormationSensitiveHOLExtensionalProfile.baseMorphism.headEq
      FormationSensitiveHOLExtensionalProfile.baseMorphism.computation

/-- Compile the two premises of one actual HOL `eqPropI` node and apply the
native proposition-extensionality declaration to their emitted proof terms. -/
def compilePropositionExtensionality
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {p q : Formula gamma}
    (forward : HOL.ProofSyntax Symbol delta (.imp p q))
    (backward : HOL.ProofSyntax Symbol delta (.imp q p))
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) := do
  let pc ← represent p
  let qc ← represent q
  let forwardNative ← compile forward objects hypotheses
  let backwardNative ← compile backward objects hypotheses
  pure (FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp
    (subst objects pc) (subst objects qc) forwardNative backwardNative)

/-- Successful attachment preserves the exact source conclusion.  The output
is an ordinary native term typed in the qualified extensional profile. -/
theorem compilePropositionExtensionality_typed
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {p q : Formula gamma}
    (forward : HOL.ProofSyntax Symbol delta (.imp p q))
    (backward : HOL.ProofSyntax Symbol delta (.imp q p))
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    {native : Tower.Tm n}
    (objectTyped : HOLLeibnizNativeProofTranslation.NativeTyping.Objects
      target objects)
    (hypothesisTyped : HOLLeibnizNativeProofTranslation.NativeTyping.Hypotheses
      target objects hypotheses)
    (success : compilePropositionExtensionality forward backward objects hypotheses =
      some native) :
    ∃ code, represent (.eq p q) = some code ∧
      Typing FormationSensitiveHOLExtensionalProfile.rules target native
        (proof (subst objects code)) := by
  cases hp : represent p with
  | none => simp [compilePropositionExtensionality, hp] at success
  | some pc =>
      cases hq : represent q with
      | none => simp [compilePropositionExtensionality, hp, hq] at success
      | some qc =>
          cases hf : compile forward objects hypotheses with
          | none =>
              simp [compilePropositionExtensionality, hp, hq, hf] at success
          | some forwardNative =>
              cases hb : compile backward objects hypotheses with
              | none =>
                  simp [compilePropositionExtensionality, hp, hq, hf, hb] at success
              | some backwardNative =>
                  simp [compilePropositionExtensionality, hp, hq, hf, hb] at success
                  subst native
                  obtain ⟨forwardCode, forwardRepresented, forwardTyped⟩ :=
                    HOLLeibnizNativeProofTranslation.NativeTyping.compile_typed
                      forward objectTyped hypothesisTyped hf
                  obtain ⟨backwardCode, backwardRepresented, backwardTyped⟩ :=
                    HOLLeibnizNativeProofTranslation.NativeTyping.compile_typed
                      backward objectTyped hypothesisTyped hb
                  have forwardShape : forwardCode = rawImp pc qc := by
                    simpa [represent_imp, hp, hq, eq_comm] using forwardRepresented
                  have backwardShape : backwardCode = rawImp qc pc := by
                    simpa [represent_imp, hp, hq, eq_comm] using backwardRepresented
                  subst forwardCode
                  subst backwardCode
                  let pcTarget := subst objects pc
                  let qcTarget := subst objects qc
                  have pTypedBase :=
                    HOLLeibnizNativeProofTranslation.NativeTyping.represented_typed
                      hp objectTyped
                  have qTypedBase :=
                    HOLLeibnizNativeProofTranslation.NativeTyping.represented_typed
                      hq objectTyped
                  have pTyped : Typing FormationSensitiveHOLExtensionalProfile.rules
                      target pcTarget
                      (liftClosed FormationSensitiveHOLExtensionalProfile.proposition) := by
                    simpa [pcTarget, FormationSensitiveHOLExtensionalProfile.proposition,
                      FormationSensitiveHOLUniformList.types,
                      FormationSensitiveHOLInterface.typeAt] using
                      FormationSensitiveHOLExtensionalProfile.include_typed pTypedBase
                  have qTyped : Typing FormationSensitiveHOLExtensionalProfile.rules
                      target qcTarget
                      (liftClosed FormationSensitiveHOLExtensionalProfile.proposition) := by
                    simpa [qcTarget, FormationSensitiveHOLExtensionalProfile.proposition,
                      FormationSensitiveHOLUniformList.types,
                      FormationSensitiveHOLInterface.typeAt] using
                      FormationSensitiveHOLExtensionalProfile.include_typed qTypedBase
                  have forwardTypedProfile :
                      Typing FormationSensitiveHOLExtensionalProfile.rules target
                        forwardNative (proof (rawImp pcTarget qcTarget)) := by
                    simpa [pcTarget, qcTarget, rawImp, subst] using
                      FormationSensitiveHOLExtensionalProfile.include_typed forwardTyped
                  have backwardTypedProfile :
                      Typing FormationSensitiveHOLExtensionalProfile.rules target
                        backwardNative (proof (rawImp qcTarget pcTarget)) := by
                    simpa [pcTarget, qcTarget, rawImp, subst] using
                      FormationSensitiveHOLExtensionalProfile.include_typed backwardTyped
                  have applied :=
                    FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp_typed
                      pTyped qTyped forwardTypedProfile backwardTypedProfile
                  have propositionCode :
                      liftClosed FormationSensitiveHOLExtensionalProfile.proposition =
                        FormationSensitiveHOLInterface.typeAt
                          FormationSensitiveHOLUniformList.types n (.prop) := by
                    rfl
                  rw [propositionCode,
                    FormationSensitiveHOLExtensionalProfile.rawLeibnizAt_typeAt] at applied
                  have targetPropositionBase :=
                    HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
                      pTypedBase qTypedBase
                  have targetTypeFormed :=
                    FormationSensitiveHOLExtensionalProfile.include_typed
                      (FormationSensitiveHOLProofFamily.proof_formed
                        targetPropositionBase)
                  have converted : Typing FormationSensitiveHOLExtensionalProfile.rules
                      target
                      (FormationSensitiveHOLExtensionalApplications.propositionExtensionalityApp
                        pcTarget qcTarget forwardNative backwardNative)
                      (proof (rawEquality .prop pcTarget qcTarget)) :=
                    .conv applied targetTypeFormed (.sort Tower.zero)
                      (.symm _ _ (include_conversion
                        (HOLLeibnizNativeProofTranslation.NativeTyping.equality_conversion
                          .prop pcTarget qcTarget)))
                  refine ⟨rawEquality .prop pc qc, ?_, ?_⟩
                  · simp [represent_eq, hp, hq]
                  · simpa only [rawEquality_subst, pcTarget, qcTarget] using converted

/-- The premise carried by HOL function extensionality, retained separately so
its source representation and native dependent family can be compared. -/
def pointwiseFormula {gamma : SourceContext} {domain codomain : HOL.Ty BaseSort}
    (function other : HOL.Term Symbol gamma (.arr domain codomain)) :
    Formula gamma :=
  .all (.eq
    (.app (HOL.weaken (Base := BaseSort) (σ := domain) function) (.var .vz))
    (.app (HOL.weaken (Base := BaseSort) (σ := domain) other) (.var .vz)))

theorem represent_pointwiseFormula
    {gamma : SourceContext} {domain codomain : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain codomain)}
    {functionCode otherCode : Tower.Tm gamma.length}
    (functionRepresented : represent function = some functionCode)
    (otherRepresented : represent other = some otherCode) :
    represent (pointwiseFormula function other) =
      some (rawAll domain
        (rawEquality codomain
          (.app (rename wk functionCode) (.var 0))
          (.app (rename wk otherCode) (.var 0)))) := by
  unfold pointwiseFormula
  rw [represent_all, represent_eq]
  rw [represent_app, represent_weaken, functionRepresented]
  rw [represent_app, represent_weaken, otherRepresented]
  rfl

@[simp] theorem rawAll_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (body : Tower.Tm (n + 1)) :
    subst sigma (rawAll type body) = rawAll type (subst (liftSub sigma) body) := by
  simp [rawAll, FormationSensitiveHOLUniformList.universal, subst]

/-- A represented universal proof of pointwise source equality is convertible
to the dependent method expected by native function extensionality. -/
theorem pointwise_conversion {n : Nat} (domain codomain : HOL.Ty BaseSort)
    (function other : Tower.Tm n) :
    Conv FormationSensitiveHOLExtensionalProfile.rules.headEq
      (proof (rawAll domain
        (rawEquality codomain
          (.app (rename wk function) (.var 0))
          (.app (rename wk other) (.var 0)))))
      (FormationSensitiveHOLExtensionalProfile.pointwiseEquality
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n domain)
        (FormationSensitiveHOLInterface.typeAt
          FormationSensitiveHOLUniformList.types n codomain)
        function other)
      FormationSensitiveHOLExtensionalProfile.rules.computation := by
  let body := rawEquality codomain
    (.app (rename wk function) (.var 0))
    (.app (rename wk other) (.var 0))
  refine .trans _ _ _
    (include_conversion
      (FormationSensitiveHOLProofFamily.rawAll_conversion domain body)) ?_
  have decoded := include_conversion
    (HOLLeibnizNativeProofTranslation.NativeTyping.equality_conversion codomain
      (.app (rename wk function) (.var 0))
      (.app (rename wk other) (.var 0)))
  simpa [body, FormationSensitiveHOLExtensionalProfile.pointwiseEquality,
    FormationSensitiveHOLExtensionalProfile.rawLeibnizAt_typeAt] using
    (Conv.congPi
      (.refl (FormationSensitiveHOLInterface.typeAt
        FormationSensitiveHOLUniformList.types n domain)) decoded)

/-- Compile the actual universally quantified pointwise premise of one HOL
`funExt` node and pass the resulting dependent section to the native profile. -/
def compileFunctionExtensionality
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {domain codomain : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain codomain)}
    (pointwise : HOL.ProofSyntax Symbol delta
      (pointwiseFormula function other))
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) := do
  let functionCode ← represent function
  let otherCode ← represent other
  let pointwiseNative ← compile pointwise objects hypotheses
  pure (FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp
    (FormationSensitiveHOLInterface.typeAt
      FormationSensitiveHOLUniformList.types n domain)
    (FormationSensitiveHOLInterface.typeAt
      FormationSensitiveHOLUniformList.types n codomain)
    (subst objects functionCode) (subst objects otherCode) pointwiseNative)

theorem compileFunctionExtensionality_typed
    {gamma : SourceContext} {delta : List (Formula gamma)}
    {domain codomain : HOL.Ty BaseSort}
    {function other : HOL.Term Symbol gamma (.arr domain codomain)}
    (pointwise : HOL.ProofSyntax Symbol delta
      (pointwiseFormula function other))
    {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n}
    {native : Tower.Tm n}
    (objectTyped : HOLLeibnizNativeProofTranslation.NativeTyping.Objects
      target objects)
    (hypothesisTyped : HOLLeibnizNativeProofTranslation.NativeTyping.Hypotheses
      target objects hypotheses)
    (success : compileFunctionExtensionality pointwise objects hypotheses =
      some native) :
    ∃ code, represent (.eq function other) = some code ∧
      Typing FormationSensitiveHOLExtensionalProfile.rules target native
        (proof (subst objects code)) := by
  cases hf : represent function with
  | none => simp [compileFunctionExtensionality, hf] at success
  | some functionCode =>
      cases hg : represent other with
      | none => simp [compileFunctionExtensionality, hf, hg] at success
      | some otherCode =>
          cases hp : compile pointwise objects hypotheses with
          | none =>
              simp [compileFunctionExtensionality, hf, hg, hp] at success
          | some pointwiseNative =>
              simp [compileFunctionExtensionality, hf, hg, hp] at success
              subst native
              obtain ⟨pointwiseCode, pointwiseRepresented, pointwiseTyped⟩ :=
                HOLLeibnizNativeProofTranslation.NativeTyping.compile_typed
                  pointwise objectTyped hypothesisTyped hp
              have pointwiseShape : pointwiseCode =
                  rawAll domain
                    (rawEquality codomain
                      (.app (rename wk functionCode) (.var 0))
                      (.app (rename wk otherCode) (.var 0))) := by
                simpa [represent_pointwiseFormula hf hg, eq_comm] using
                  pointwiseRepresented
              subst pointwiseCode
              let domainCode := FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n domain
              let codomainCode := FormationSensitiveHOLInterface.typeAt
                FormationSensitiveHOLUniformList.types n codomain
              let functionTarget := subst objects functionCode
              let otherTarget := subst objects otherCode
              let pointwiseBody := rawEquality codomain
                (.app (rename wk functionTarget) (.var 0))
                (.app (rename wk otherTarget) (.var 0))
              have domainTypedBase : Typing FormationSensitiveHOLProofFamily.rules
                  target domainCode (sortTm Tower.zero) := by
                exact FormationSensitiveHOLProofFamily.simple_type_formed domain target
              have codomainTypedBase : Typing FormationSensitiveHOLProofFamily.rules
                  target codomainCode (sortTm Tower.zero) := by
                exact FormationSensitiveHOLProofFamily.simple_type_formed codomain target
              have functionTypedBaseRaw :=
                HOLLeibnizNativeProofTranslation.NativeTyping.represented_typed
                  hf objectTyped
              have otherTypedBaseRaw :=
                HOLLeibnizNativeProofTranslation.NativeTyping.represented_typed
                  hg objectTyped
              have functionTypedBase : Typing FormationSensitiveHOLProofFamily.rules
                  target functionTarget
                  (FormationSensitiveHOLExtensionalProfile.arrow
                    domainCode codomainCode) := by
                simpa [functionTarget, domainCode, codomainCode,
                  FormationSensitiveHOLExtensionalProfile.arrow,
                  FormationSensitiveHOLInterface.typeAt] using functionTypedBaseRaw
              have otherTypedBase : Typing FormationSensitiveHOLProofFamily.rules
                  target otherTarget
                  (FormationSensitiveHOLExtensionalProfile.arrow
                    domainCode codomainCode) := by
                simpa [otherTarget, domainCode, codomainCode,
                  FormationSensitiveHOLExtensionalProfile.arrow,
                  FormationSensitiveHOLInterface.typeAt] using otherTypedBaseRaw
              have pointwiseTypedRaw :
                  Typing FormationSensitiveHOLExtensionalProfile.rules target
                    pointwiseNative (proof (rawAll domain pointwiseBody)) := by
                simpa [pointwiseBody, functionTarget, otherTarget,
                  subst, subst_liftSub_wk] using
                  FormationSensitiveHOLExtensionalProfile.include_typed pointwiseTyped
              have pointwiseTypeFormed :=
                FormationSensitiveHOLExtensionalProfile.include_typed
                  (FormationSensitiveHOLExtensionalProfile.pointwiseEquality_formed
                    domainTypedBase codomainTypedBase functionTypedBase otherTypedBase)
              have pointwiseTypedProfile :
                  Typing FormationSensitiveHOLExtensionalProfile.rules target
                    pointwiseNative
                    (FormationSensitiveHOLExtensionalProfile.pointwiseEquality
                      domainCode codomainCode functionTarget otherTarget) :=
                .conv pointwiseTypedRaw pointwiseTypeFormed (.sort Tower.zero)
                  (pointwise_conversion domain codomain functionTarget otherTarget)
              have applied :=
                FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp_typed
                  (FormationSensitiveHOLExtensionalProfile.include_typed domainTypedBase)
                  (FormationSensitiveHOLExtensionalProfile.include_typed codomainTypedBase)
                  (FormationSensitiveHOLExtensionalProfile.include_typed functionTypedBase)
                  (FormationSensitiveHOLExtensionalProfile.include_typed otherTypedBase)
                  pointwiseTypedProfile
              have functionTypeCode :
                  FormationSensitiveHOLExtensionalProfile.arrow
                    domainCode codomainCode =
                    FormationSensitiveHOLInterface.typeAt
                      FormationSensitiveHOLUniformList.types n
                      (.arr domain codomain) := by
                simp [domainCode, codomainCode,
                  FormationSensitiveHOLExtensionalProfile.arrow,
                  FormationSensitiveHOLInterface.typeAt]
              rw [functionTypeCode,
                FormationSensitiveHOLExtensionalProfile.rawLeibnizAt_typeAt] at applied
              have targetPropositionBase :=
                HOLLeibnizNativeProofTranslation.NativeTyping.equality_proposition
                  functionTypedBaseRaw otherTypedBaseRaw
              have targetTypeFormed :=
                FormationSensitiveHOLExtensionalProfile.include_typed
                  (FormationSensitiveHOLProofFamily.proof_formed
                    targetPropositionBase)
              have converted : Typing FormationSensitiveHOLExtensionalProfile.rules
                  target
                  (FormationSensitiveHOLExtensionalApplications.functionExtensionalityApp
                    domainCode codomainCode functionTarget otherTarget pointwiseNative)
                  (proof (rawEquality (.arr domain codomain)
                    functionTarget otherTarget)) :=
                .conv applied targetTypeFormed (.sort Tower.zero)
                  (.symm _ _ (include_conversion
                    (HOLLeibnizNativeProofTranslation.NativeTyping.equality_conversion
                      (.arr domain codomain) functionTarget otherTarget)))
              refine ⟨rawEquality (.arr domain codomain) functionCode otherCode, ?_, ?_⟩
              · simp [represent_eq, hf, hg]
              · simpa only [rawEquality_subst, functionTarget, otherTarget] using converted

namespace Controls

def propositionIdentityFunction :
    HOL.Term Symbol [] (.arr .prop .prop) :=
  .lam (.var .vz)

def propositionIdentityPointwise :
    HOL.ProofSyntax Symbol []
      (pointwiseFormula propositionIdentityFunction propositionIdentityFunction) :=
  .allI (.eqRefl
    (.app (HOL.weaken propositionIdentityFunction) (.var .vz)))

def propositionIdentityFunctionExtensionality :
    HOL.ProofSyntax Symbol []
      (.eq propositionIdentityFunction propositionIdentityFunction) :=
  .funExt propositionIdentityPointwise

/-- The qualified attachment accepts the real source `funExt` premise and
emits a native application. -/
theorem function_extensionality_attachment_succeeds :
    ∃ native, compileFunctionExtensionality propositionIdentityPointwise
      (n := 0) Fin.elim0 Fin.elim0 = some native := by
  refine ⟨_, rfl⟩

/-- The same source rule remains outside the constructive compiler. -/
theorem function_extensionality_base_compiler_rejects :
    compile propositionIdentityFunctionExtensionality
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

def propositionVariable : Formula [.prop] :=
  .var .vz

def propositionVariableForward :
    HOL.ProofSyntax Symbol [] (.imp propositionVariable propositionVariable) :=
  .impI (.hyp 0)

/-- The proposition attachment likewise accepts the actual two-premise source
rule when both constructive implication proofs are available. -/
theorem proposition_extensionality_attachment_succeeds :
    ∃ native, compilePropositionExtensionality propositionVariableForward
      propositionVariableForward (n := 1) ids Fin.elim0 = some native := by
  refine ⟨_, rfl⟩

/-- The constructive compiler still rejects the extensional node itself; the
attachment is a separately visible capability. -/
theorem base_compiler_remains_constructive
    {p q : Formula []}
    (forward : HOL.ProofSyntax Symbol [] (.imp p q))
    (backward : HOL.ProofSyntax Symbol [] (.imp q p)) :
    compile (HOL.ProofSyntax.eqPropI forward backward)
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

end Controls

#print axioms include_conversion
#print axioms compilePropositionExtensionality_typed
#print axioms represent_pointwiseFormula
#print axioms pointwise_conversion
#print axioms compileFunctionExtensionality_typed
#print axioms Controls.function_extensionality_attachment_succeeds
#print axioms Controls.function_extensionality_base_compiler_rejects
#print axioms Controls.proposition_extensionality_attachment_succeeds
#print axioms Controls.base_compiler_remains_constructive

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeExtensionalProofTranslation
