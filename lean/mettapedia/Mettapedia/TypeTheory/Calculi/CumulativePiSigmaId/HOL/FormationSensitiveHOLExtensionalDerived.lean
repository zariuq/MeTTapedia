import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalApplications
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveProofAttachment

/-!
# Constructive proof operations in the opaque extensional HOL profile

An extensional proof may occur beneath an otherwise constructive proof rule.
The old derived combinators were proved in the base profile, so their open
typing derivations cannot be applied directly to such a premise.

The common mechanism is context comprehension.  Type the combinator body in
the base profile with one newest proof variable, include that open derivation
in the opaque extension, and substitute the actual extensional proof for the
variable.  This derives profile-stable combinators without adding declarations
or duplicating their logical implementation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalDerived

open Presentation Presentation.FormationSensitive Mettapedia.Logic
open HOL.UniformListInduction
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLLeibnizInterface (rawLeibniz)
open FormationSensitiveHOLUniformList (rawImp types)

abbrev baseRules := FormationSensitiveHOLProofFamily.rules
abbrev rules := FormationSensitiveHOLExtensionalProfile.rules

/-- Base proof-family conversion remains available in the opaque extension.
The added declarations contribute no computation equations. -/
theorem include_conversion {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv baseRules.headEq left right baseRules.computation) :
    Conv rules.headEq left right rules.computation := by
  simpa only [Tm.mapHead_id, subst_ids] using
    FormationSensitiveProofAttachment.attachConversion
      FormationSensitiveHOLExtensionalProfile.baseMorphism ids conversion

/-- Include a base-profile derivation in the opaque extension and reindex it
along any substitution typed in that extension.  This is the telescope-level
attachment law; the proof arguments supplied by the substitution may use the
new extensional constants even though the open operation does not. -/
theorem attach_base_derivation {k n : Nat} {source : Tower.Ctx k}
    {target : Tower.Ctx n} {body type : Tower.Tm k}
    {sigma : Sub Tower.Head k n}
    (bodyTyped : Typing baseRules source body type)
    (sigmaTyped : Presentation.FormationSensitive.CtxMor
      rules source target sigma) :
    Typing rules target (subst sigma body) (subst sigma type) := by
  have sigmaMapped : Presentation.FormationSensitive.CtxMor rules
      (source.mapHead (fun head => head)) target sigma := by
    simpa only [Ctx.mapHead_id] using sigmaTyped
  simpa only [Tm.mapHead_id, Ctx.mapHead_id] using
    FormationSensitiveProofAttachment.attachTyping
      FormationSensitiveHOLExtensionalProfile.baseMorphism bodyTyped sigmaMapped

/-- Instantiate one open base-profile operation with an argument that is typed
only in the opaque extension.  This is the general proof-attachment step. -/
theorem instantiate_base_operation {n : Nat} {context : Tower.Ctx n}
    {domain result : Tower.Tm n} {body : Tower.Tm (n + 1)}
    {argument : Tower.Tm n}
    (bodyTyped : Typing baseRules (.snoc context domain) body (rename wk result))
    (argumentTyped : Typing rules context argument domain) :
    Typing rules context (subst (consSub argument ids) body) result :=
  FormationSensitiveProofAttachment.instantiateOperation
    FormationSensitiveHOLExtensionalProfile.baseMorphism bodyTyped argumentTyped

/-- Two proof arguments can be attached at once.  The second open domain is
weakened over the first, so the substitution is a genuine two-entry telescope
rather than two unrelated casts. -/
theorem instantiate_base_operation2 {n : Nat} {context : Tower.Ctx n}
    {firstDomain secondDomain result : Tower.Tm n}
    {body : Tower.Tm (n + 2)} {firstArgument secondArgument : Tower.Tm n}
    (bodyTyped : Typing baseRules
      (.snoc (.snoc context firstDomain) (rename wk secondDomain)) body
      (rename wk (rename wk result)))
    (firstTyped : Typing rules context firstArgument firstDomain)
    (secondTyped : Typing rules context secondArgument secondDomain) :
    Typing rules context
      (subst (consSub secondArgument (consSub firstArgument ids)) body)
      result :=
  FormationSensitiveProofAttachment.instantiateOperation2
    FormationSensitiveHOLExtensionalProfile.baseMorphism bodyTyped firstTyped secondTyped

/-! The proof-family connectives themselves are profile-stable.  Their
premises may use the opaque extensional declarations, while their formation
and decoder conversions are inherited from the constructive profile. -/

theorem implication_intro {n : Nat} {context : Tower.Ctx n}
    {p q : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (pTyped : Typing baseRules context p (.const `HOLUniformList.prop))
    (qTyped : Typing baseRules context q (.const `HOLUniformList.prop))
    (bodyTyped : Typing rules (.snoc context (proof p)) body
      (rename wk (proof q))) :
    Typing rules context (.lam body) (proof (rawImp p q)) :=
  .conv
    (.lamIntro
      (FormationSensitiveHOLExtensionalProfile.include_typed
        (FormationSensitiveHOLProofFamily.implication_formed pTyped qTyped))
      (.sort Tower.zero) bodyTyped)
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.proof_formed
        (FormationSensitiveHOLProofFamily.implication_proposition
          pTyped qTyped)))
    (.sort Tower.zero)
    (.symm _ _ (include_conversion
      (FormationSensitiveHOLProofFamily.implication_conversion p q)))

theorem implication_elim {n : Nat} {context : Tower.Ctx n}
    {p q major minor : Tower.Tm n}
    (pTyped : Typing baseRules context p (.const `HOLUniformList.prop))
    (qTyped : Typing baseRules context q (.const `HOLUniformList.prop))
    (majorTyped : Typing rules context major (proof (rawImp p q)))
    (minorTyped : Typing rules context minor (proof p)) :
    Typing rules context (.app major minor) (proof q) := by
  have converted := Typing.conv majorTyped
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.implication_formed pTyped qTyped))
    (.sort Tower.zero)
    (include_conversion
      (FormationSensitiveHOLProofFamily.implication_conversion p q))
  simpa only [FormationSensitiveHOLProofFamily.implicationFamily,
    inst0_rename_wk] using Typing.appElim converted minorTyped

theorem universal_intro {n : Nat} {context : Tower.Ctx n}
    {domain : Tower.Tm n} {proposition body : Tower.Tm (n + 1)}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (propositionTyped : Typing baseRules (.snoc context domain) proposition
      (.const `HOLUniformList.prop))
    (bodyTyped : Typing rules (.snoc context domain) body
      (proof proposition)) :
    Typing rules context (.lam body)
      (proof (FormationSensitiveHOLProofFamily.universalProposition
        domain (.lam proposition))) :=
  .conv
    (.lamIntro
      (FormationSensitiveHOLExtensionalProfile.include_typed
        (FormationSensitiveHOLProofFamily.pi_zero domainTyped
          (FormationSensitiveHOLProofFamily.proof_formed propositionTyped)))
      (.sort Tower.zero) bodyTyped)
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.proof_formed
        (FormationSensitiveHOLProofFamily.universal_lambda_proposition
          domainTyped propositionTyped)))
    (.sort Tower.zero)
    (.symm _ _ (include_conversion
      (FormationSensitiveHOLProofFamily.universal_lambda_conversion
        domain proposition)))

theorem universal_elim {n : Nat} {context : Tower.Ctx n}
    {domain major argument : Tower.Tm n}
    {proposition : Tower.Tm (n + 1)}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (propositionTyped : Typing baseRules (.snoc context domain) proposition
      (.const `HOLUniformList.prop))
    (majorTyped : Typing rules context major
      (proof (FormationSensitiveHOLProofFamily.universalProposition
        domain (.lam proposition))))
    (argumentTyped : Typing baseRules context argument domain) :
    Typing rules context (.app major argument)
      (proof (inst0 argument proposition)) := by
  have converted := Typing.conv majorTyped
    (FormationSensitiveHOLExtensionalProfile.include_typed
      (FormationSensitiveHOLProofFamily.pi_zero domainTyped
        (FormationSensitiveHOLProofFamily.proof_formed propositionTyped)))
    (.sort Tower.zero)
    (include_conversion
      (FormationSensitiveHOLProofFamily.universal_lambda_conversion
        domain proposition))
  have argumentTypedProfile :=
    FormationSensitiveHOLExtensionalProfile.include_typed argumentTyped
  simpa only [inst0, FormationSensitiveHOLProofFamily.proof_subst] using
    Typing.appElim converted argumentTypedProfile

/-- Leibniz symmetry accepts a comparison produced anywhere in the opaque
extensional profile. -/
theorem symmetry_typed {n : Nat} {context : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {x y comparison : Tower.Tm n}
    (xTyped : Typing baseRules context x
      (FormationSensitiveHOLInterface.typeAt types n type))
    (yTyped : Typing baseRules context y
      (FormationSensitiveHOLInterface.typeAt types n type))
    (comparisonTyped : Typing rules context comparison
      (proof (rawLeibniz type x y))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.symmetry type x comparison)
      (proof (rawLeibniz type y x)) := by
  let comparisonType := proof (rawLeibniz type x y)
  let resultType := proof (rawLeibniz type y x)
  have comparisonVariable : Typing baseRules
      (.snoc context comparisonType) (.var 0)
      (proof (rawLeibniz type (rename wk x) (rename wk y))) := by
    simpa [comparisonType, FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := .snoc context comparisonType) 0)
  have bodyTypedRaw := FormationSensitiveHOLLeibnizDerived.symmetry_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed xTyped comparisonType)
    (FormationSensitiveHOLLeibnizDerived.weaken_typed yTyped comparisonType)
    comparisonVariable
  have bodyTyped : Typing baseRules (.snoc context comparisonType)
      (FormationSensitiveHOLLeibnizDerived.symmetry type
        (rename wk x) (.var 0))
      (rename wk resultType) := by
    simpa [resultType, FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using bodyTypedRaw
  have instantiated := instantiate_base_operation bodyTyped comparisonTyped
  simpa [comparisonType, resultType] using instantiated

/-- Leibniz transitivity accepts both comparisons from the opaque extension. -/
theorem transitivity_typed {n : Nat} {context : Tower.Ctx n}
    {type : HOL.Ty BaseSort} {x y z first second : Tower.Tm n}
    (xTyped : Typing baseRules context x
      (FormationSensitiveHOLInterface.typeAt types n type))
    (yTyped : Typing baseRules context y
      (FormationSensitiveHOLInterface.typeAt types n type))
    (zTyped : Typing baseRules context z
      (FormationSensitiveHOLInterface.typeAt types n type))
    (firstTyped : Typing rules context first
      (proof (rawLeibniz type x y)))
    (secondTyped : Typing rules context second
      (proof (rawLeibniz type y z))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.transitivity type x first second)
      (proof (rawLeibniz type x z)) := by
  let firstType := proof (rawLeibniz type x y)
  let secondType := proof (rawLeibniz type y z)
  let resultType := proof (rawLeibniz type x z)
  let once : Tower.Ctx (n + 1) := .snoc context firstType
  let twice : Tower.Ctx (n + 2) := .snoc once (rename wk secondType)
  have xTwice := FormationSensitiveHOLLeibnizDerived.weaken_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed xTyped firstType)
    (rename wk secondType)
  have yTwice := FormationSensitiveHOLLeibnizDerived.weaken_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed yTyped firstType)
    (rename wk secondType)
  have zTwice := FormationSensitiveHOLLeibnizDerived.weaken_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed zTyped firstType)
    (rename wk secondType)
  have firstVariableOnce : Typing baseRules once (.var 0)
      (proof (rawLeibniz type (rename wk x) (rename wk y))) := by
    simpa only [once, firstType, Ctx.lookup_snoc_zero,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := once) (0 : Fin (n + 1)))
  have firstVariableRaw := firstVariableOnce.weaken
    (extension := rename wk secondType)
  have firstVariable : Typing baseRules twice (.var 1)
      (proof (rawLeibniz type (rename wk (rename wk x))
        (rename wk (rename wk y)))) := by
    simpa only [twice, Presentation.rename, wk, Fin.succ_zero_eq_one,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      firstVariableRaw
  have secondVariable : Typing baseRules twice (.var 0)
      (proof (rawLeibniz type (rename wk (rename wk y))
        (rename wk (rename wk z)))) := by
    simpa only [once, twice, secondType, Ctx.lookup_snoc_zero,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := twice) (0 : Fin (n + 2)))
  have bodyTypedRaw := FormationSensitiveHOLLeibnizDerived.transitivity_typed
    xTwice yTwice zTwice firstVariable secondVariable
  have bodyTyped : Typing baseRules twice
      (FormationSensitiveHOLLeibnizDerived.transitivity type
        (rename wk (rename wk x)) (.var 1) (.var 0))
      (rename wk (rename wk resultType)) := by
    simpa [resultType, Presentation.rename,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using bodyTypedRaw
  have instantiated := instantiate_base_operation2 bodyTyped firstTyped secondTyped
  have firstAtSub :
      consSub second (consSub first ids) (1 : Fin (n + 2)) = first := by
    rw [← Fin.succ_zero_eq_one]
    simp only [consSub_succ, consSub_zero]
  simpa only [firstType, secondType, resultType,
    FormationSensitiveHOLLeibnizDerived.transitivity_subst,
    subst_consSub_rename_wk, subst_ids, Presentation.subst, ids,
    consSub_zero, consSub_succ, firstAtSub] using instantiated

/-- Application congruence accepts its equality premise from the opaque
extension while retaining the constructive term former. -/
theorem congruence_typed {n : Nat} {context : Tower.Ctx n}
    {a b : HOL.Ty BaseSort} {function x y comparison : Tower.Tm n}
    (functionTyped : Typing baseRules context function
      (FormationSensitiveHOLInterface.typeAt types n (.arr a b)))
    (xTyped : Typing baseRules context x
      (FormationSensitiveHOLInterface.typeAt types n a))
    (yTyped : Typing baseRules context y
      (FormationSensitiveHOLInterface.typeAt types n a))
    (comparisonTyped : Typing rules context comparison
      (proof (rawLeibniz a x y))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.congruence b function x comparison)
      (proof (rawLeibniz b (.app function x) (.app function y))) := by
  let comparisonType := proof (rawLeibniz a x y)
  let resultType := proof (rawLeibniz b (.app function x) (.app function y))
  have comparisonVariable : Typing baseRules
      (.snoc context comparisonType) (.var 0)
      (proof (rawLeibniz a (rename wk x) (rename wk y))) := by
    simpa [comparisonType, FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := .snoc context comparisonType) 0)
  have bodyTypedRaw := FormationSensitiveHOLLeibnizDerived.congruence_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed functionTyped comparisonType)
    (FormationSensitiveHOLLeibnizDerived.weaken_typed xTyped comparisonType)
    (FormationSensitiveHOLLeibnizDerived.weaken_typed yTyped comparisonType)
    comparisonVariable
  have bodyTyped : Typing baseRules (.snoc context comparisonType)
      (FormationSensitiveHOLLeibnizDerived.congruence b
        (rename wk function) (rename wk x) (.var 0))
      (rename wk resultType) := by
    simpa [resultType, Presentation.rename,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using bodyTypedRaw
  have instantiated := instantiate_base_operation bodyTyped comparisonTyped
  simpa [comparisonType, resultType] using instantiated

/-- Function congruence likewise accepts an equality between functions
produced by the opaque extension. -/
theorem functionCongruence_typed {n : Nat} {context : Tower.Ctx n}
    {a b : HOL.Ty BaseSort} {function other x comparison : Tower.Tm n}
    (functionTyped : Typing baseRules context function
      (FormationSensitiveHOLInterface.typeAt types n (.arr a b)))
    (otherTyped : Typing baseRules context other
      (FormationSensitiveHOLInterface.typeAt types n (.arr a b)))
    (xTyped : Typing baseRules context x
      (FormationSensitiveHOLInterface.typeAt types n a))
    (comparisonTyped : Typing rules context comparison
      (proof (rawLeibniz (.arr a b) function other))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.functionCongruence b
        function x comparison)
      (proof (rawLeibniz b (.app function x) (.app other x))) := by
  let comparisonType := proof (rawLeibniz (.arr a b) function other)
  let resultType := proof (rawLeibniz b (.app function x) (.app other x))
  have comparisonVariable : Typing baseRules
      (.snoc context comparisonType) (.var 0)
      (proof (rawLeibniz (.arr a b) (rename wk function) (rename wk other))) := by
    simpa [comparisonType, FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := .snoc context comparisonType) 0)
  have bodyTypedRaw :=
    FormationSensitiveHOLLeibnizDerived.functionCongruence_typed
      (FormationSensitiveHOLLeibnizDerived.weaken_typed
        functionTyped comparisonType)
      (FormationSensitiveHOLLeibnizDerived.weaken_typed otherTyped comparisonType)
      (FormationSensitiveHOLLeibnizDerived.weaken_typed xTyped comparisonType)
      comparisonVariable
  have bodyTyped : Typing baseRules (.snoc context comparisonType)
      (FormationSensitiveHOLLeibnizDerived.functionCongruence b
        (rename wk function) (rename wk x) (.var 0))
      (rename wk resultType) := by
    simpa only [resultType, Presentation.rename,
      FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using bodyTypedRaw
  have instantiated := instantiate_base_operation bodyTyped comparisonTyped
  simpa [comparisonType, resultType] using instantiated

/-- Proposition transport accepts an equality proof produced by the opaque
extension and returns the original constructive implication term. -/
theorem propForward_typed {n : Nat} {context : Tower.Ctx n}
    {p q comparison : Tower.Tm n}
    (pTyped : Typing baseRules context p (.const `HOLUniformList.prop))
    (qTyped : Typing baseRules context q (.const `HOLUniformList.prop))
    (comparisonTyped : Typing rules context comparison
      (proof (rawLeibniz .prop p q))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.propForward comparison)
      (proof (rawImp p q)) := by
  let comparisonType := proof (rawLeibniz .prop p q)
  let resultType := proof (rawImp p q)
  have comparisonVariable : Typing baseRules
      (.snoc context comparisonType) (.var 0)
      (proof (rawLeibniz .prop (rename wk p) (rename wk q))) := by
    simpa [comparisonType, FormationSensitiveHOLProofFamily.proof_rename,
      FormationSensitiveHOLLeibnizInterface.rawLeibniz_rename] using
      (Typing.var (R := baseRules) (Γ := .snoc context comparisonType) 0)
  have pTypedAsSimple : Typing baseRules context p
      (FormationSensitiveHOLInterface.typeAt types n .prop) := by
    simpa only [FormationSensitiveHOLInterface.typeAt, types, liftClosed,
      Presentation.rename] using pTyped
  have qTypedAsSimple : Typing baseRules context q
      (FormationSensitiveHOLInterface.typeAt types n .prop) := by
    simpa only [FormationSensitiveHOLInterface.typeAt, types, liftClosed,
      Presentation.rename] using qTyped
  have bodyTypedRaw := FormationSensitiveHOLLeibnizDerived.propForward_typed
    (FormationSensitiveHOLLeibnizDerived.weaken_typed
      pTypedAsSimple comparisonType)
    (FormationSensitiveHOLLeibnizDerived.weaken_typed
      qTypedAsSimple comparisonType)
    comparisonVariable
  have bodyTyped : Typing baseRules (.snoc context comparisonType)
      (FormationSensitiveHOLLeibnizDerived.propForward (.var 0))
      (rename wk resultType) := by
    change Typing baseRules (.snoc context comparisonType)
      (FormationSensitiveHOLLeibnizDerived.propForward (.var 0))
      (proof (rawImp (rename wk p) (rename wk q)))
    exact bodyTypedRaw
  have instantiated := instantiate_base_operation bodyTyped comparisonTyped
  simpa [comparisonType, resultType] using instantiated

/-- Reverse proposition transport has the same profile-stable attachment
property. -/
theorem propBackward_typed {n : Nat} {context : Tower.Ctx n}
    {p q comparison : Tower.Tm n}
    (pTyped : Typing baseRules context p (.const `HOLUniformList.prop))
    (qTyped : Typing baseRules context q (.const `HOLUniformList.prop))
    (comparisonTyped : Typing rules context comparison
      (proof (rawLeibniz .prop p q))) :
    Typing rules context
      (FormationSensitiveHOLLeibnizDerived.propForward
        (FormationSensitiveHOLLeibnizDerived.symmetry .prop p comparison))
      (proof (rawImp q p)) :=
  propForward_typed qTyped pTyped (symmetry_typed pTyped qTyped comparisonTyped)

#print axioms attach_base_derivation
#print axioms instantiate_base_operation
#print axioms instantiate_base_operation2
#print axioms implication_intro
#print axioms implication_elim
#print axioms universal_intro
#print axioms universal_elim
#print axioms symmetry_typed
#print axioms transitivity_typed
#print axioms congruence_typed
#print axioms functionCongruence_typed
#print axioms propForward_typed
#print axioms propBackward_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalDerived
