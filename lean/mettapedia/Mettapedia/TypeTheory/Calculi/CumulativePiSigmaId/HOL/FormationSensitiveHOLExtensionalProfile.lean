import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizDerived

/-!
# A declared extensional HOL profile over the native dependent kernel

The intensional kernel and constructive Leibniz fragment are left unchanged.
This module adds exactly two opaque object-theory constants: propositional
extensionality and function extensionality.  Their types are ordinary native
dependent products.  In particular, the constants are not kernel reduction
rules and their declarations do not identify native intensional identity with
HOL equality.

The function principle is genuinely type-polymorphic in the native universe.
Specialized applications therefore support every represented simple function
type without an infinite family of privileged names.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalProfile

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic HOL.UniformListInduction
open FormationSensitiveHOLUniformList (types rawImp)
open FormationSensitiveHOLProofFamily (proof universalProposition)

abbrev baseRules := FormationSensitiveHOLProofFamily.rules

def proposition : Tower.Tm 0 := .const `HOLUniformList.prop

def arrow {n : Nat} (domain codomain : Tower.Tm n) : Tower.Tm n :=
  .pi domain (rename wk codomain)

def predicateType {n : Nat} (type : Tower.Tm n) : Tower.Tm n :=
  arrow type (liftClosed proposition)

/-- Leibniz equality at an arbitrary small native type, rather than at a
meta-level selected source type. -/
def rawLeibnizAt {n : Nat} (type left right : Tower.Tm n) : Tower.Tm n :=
  universalProposition (predicateType type)
    (.lam (rawImp
      (.app (.var 0) (rename wk left))
      (.app (.var 0) (rename wk right))))

@[simp] theorem liftClosed_typeAt {n : Nat} (type : HOL.Ty BaseSort) :
    (liftClosed (typeAt types 0 type) : Tower.Tm n) = typeAt types n type := by
  simpa only [liftClosed] using
    (typeAt_rename types (Fin.elim0 : Ren 0 n) type)

@[simp] theorem arrow_rename {n m : Nat} (rho : Ren n m)
    (domain codomain : Tower.Tm n) :
    rename rho (arrow domain codomain) =
      arrow (rename rho domain) (rename rho codomain) := by
  simp [arrow, rename, rename_comp, liftRen, wk]

@[simp] theorem rawLeibnizAt_rename {n m : Nat} (rho : Ren n m)
    (type left right : Tower.Tm n) :
    rename rho (rawLeibnizAt type left right) =
      rawLeibnizAt (rename rho type) (rename rho left) (rename rho right) := by
  simp [rawLeibnizAt, predicateType, universalProposition, arrow,
    rename, rename_comp, liftRen, wk, rawImp]

@[simp] theorem rawLeibnizAt_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type left right : Tower.Tm n) :
    subst sigma (rawLeibnizAt type left right) =
      rawLeibnizAt (subst sigma type) (subst sigma left) (subst sigma right) := by
  simp [rawLeibnizAt, predicateType, universalProposition, arrow,
    subst, subst_rename, rename_subst, liftSub, wk, rawImp]

theorem rawLeibnizAt_typeAt {n : Nat} (type : HOL.Ty BaseSort)
    (left right : Tower.Tm n) :
    rawLeibnizAt (typeAt types n type) left right =
      FormationSensitiveHOLLeibnizInterface.rawLeibniz type left right := by
  simp [rawLeibnizAt, predicateType, arrow,
    FormationSensitiveHOLLeibnizInterface.rawLeibniz,
    FormationSensitiveHOLUniformList.rawAll,
    FormationSensitiveHOLUniformList.universal, universalProposition, typeAt,
    FormationSensitiveHOLUniformList.types, proposition, liftClosed, rename,
    wk]

theorem pi_zero {n : Nat} {context : Tower.Ctx n}
    {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (codomainTyped : Typing baseRules (.snoc context domain) codomain
      (sortTm Tower.zero)) :
    Typing baseRules context (.pi domain codomain) (sortTm Tower.zero) := by
  apply Typing.cumul
    (.piForm domainTyped (.sort Tower.zero) codomainTyped (.sort Tower.zero)
      (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, LevelTower.zero]

theorem proposition_formed {n : Nat} (context : Tower.Ctx n) :
    Typing baseRules context (liftClosed proposition) (sortTm Tower.zero) := by
  simpa [proposition, liftClosed, rename] using
    FormationSensitiveHOLProofFamily.proposition_formed context

theorem arrow_formed {n : Nat} {context : Tower.Ctx n}
    {domain codomain : Tower.Tm n}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (codomainTyped : Typing baseRules context codomain (sortTm Tower.zero)) :
    Typing baseRules context (arrow domain codomain) (sortTm Tower.zero) := by
  apply pi_zero domainTyped
  simpa [arrow, sortTm, rename] using codomainTyped.weaken (extension := domain)

theorem application_typed {n : Nat} {context : Tower.Ctx n}
    {domain codomain function argument : Tower.Tm n}
    (functionTyped : Typing baseRules context function (arrow domain codomain))
    (argumentTyped : Typing baseRules context argument domain) :
    Typing baseRules context (.app function argument) codomain := by
  have applied := Typing.appElim functionTyped argumentTyped
  simpa only [arrow, inst0_rename_wk] using applied

theorem rawLeibnizAt_typed {n : Nat} {context : Tower.Ctx n}
    {type left right : Tower.Tm n}
    (typeTyped : Typing baseRules context type (sortTm Tower.zero))
    (leftTyped : Typing baseRules context left type)
    (rightTyped : Typing baseRules context right type) :
    Typing baseRules context (rawLeibnizAt type left right)
      (liftClosed proposition) := by
  let predicates := predicateType type
  have predicatesTyped : Typing baseRules context predicates (sortTm Tower.zero) :=
    arrow_formed typeTyped (proposition_formed context)
  have predicateVariable : Typing baseRules (.snoc context predicates) (.var 0)
      (rename wk predicates) := by
    simpa only [Ctx.lookup_snoc_zero] using
      (Typing.var (R := baseRules) (Γ := .snoc context predicates) 0)
  have leftWeakened : Typing baseRules (.snoc context predicates) (rename wk left)
      (rename wk type) := leftTyped.weaken
  have rightWeakened : Typing baseRules (.snoc context predicates) (rename wk right)
      (rename wk type) := rightTyped.weaken
  have predicateShape : rename wk predicates =
      arrow (rename wk type) (liftClosed proposition) := by
    simp only [predicates, predicateType, arrow_rename, rename_liftClosed]
  rw [predicateShape] at predicateVariable
  have leftProposition := application_typed predicateVariable leftWeakened
  have rightProposition := application_typed predicateVariable rightWeakened
  have bodyTyped := FormationSensitiveHOLProofFamily.implication_proposition
    leftProposition rightProposition
  have universal := FormationSensitiveHOLProofFamily.universal_lambda_proposition
    predicatesTyped bodyTyped
  simpa [rawLeibnizAt, predicates, predicateType, proposition,
    liftClosed, rename] using universal

def propositionExtensionalityName : DeclName :=
  `HOLUniformList.Extensional.proposition

def functionExtensionalityName : DeclName :=
  `HOLUniformList.Extensional.function

/-- The proposition rule takes both implication directions explicitly. -/
def propositionExtensionalityType : Tower.Tm 0 :=
  .pi proposition
    (.pi (liftClosed proposition)
      (.pi (proof (rawImp (.var 1) (.var 0)))
        (.pi (proof (rawImp (.var 1) (.var 2)))
          (proof (rawLeibnizAt (liftClosed proposition) (.var 3) (.var 2))))))

theorem propositionExtensionalityType_formed :
    Typing baseRules .nil propositionExtensionalityType (sortTm Tower.zero) := by
  have pTyped : Typing baseRules (.snoc (.nil) proposition) (.var 0)
      (liftClosed proposition) := by
    simpa [Ctx.lookup_snoc_zero, proposition, liftClosed, rename] using
      (Typing.var (R := baseRules) (Γ := .snoc (.nil) proposition) 0)
  let two := (.snoc (.snoc (.nil) proposition) (liftClosed proposition) : Tower.Ctx 2)
  have pTwo : Typing baseRules two (.var 1) (liftClosed proposition) := by
    have lookup : two.lookup 1 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := two) 1)
  have qTwo : Typing baseRules two (.var 0) (liftClosed proposition) := by
    simpa only [two, Ctx.lookup_snoc_zero, rename_liftClosed] using
      (Typing.var (R := baseRules) (Γ := two) 0)
  have forwardProp := FormationSensitiveHOLProofFamily.implication_proposition pTwo qTwo
  let withForward := two.snoc (proof (rawImp (.var 1) (.var 0)))
  have pForward : Typing baseRules withForward (.var 2) (liftClosed proposition) := by
    have lookup : withForward.lookup 2 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withForward) 2)
  have qForward : Typing baseRules withForward (.var 1) (liftClosed proposition) := by
    have lookup : withForward.lookup 1 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withForward) 1)
  have backwardProp := FormationSensitiveHOLProofFamily.implication_proposition qForward pForward
  let withBackward := withForward.snoc (proof (rawImp (.var 1) (.var 2)))
  have pBackward : Typing baseRules withBackward (.var 3) (liftClosed proposition) := by
    have lookup : withBackward.lookup 3 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withBackward) 3)
  have qBackward : Typing baseRules withBackward (.var 2) (liftClosed proposition) := by
    have lookup : withBackward.lookup 2 = liftClosed proposition := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withBackward) 2)
  have equalityProp := rawLeibnizAt_typed
    (proposition_formed withBackward) pBackward qBackward
  have result := pi_zero (proposition_formed .nil)
    (pi_zero (proposition_formed (.snoc .nil proposition))
      (pi_zero (FormationSensitiveHOLProofFamily.proof_formed forwardProp)
        (pi_zero (FormationSensitiveHOLProofFamily.proof_formed backwardProp)
          (FormationSensitiveHOLProofFamily.proof_formed equalityProp))))
  simpa only [propositionExtensionalityType, two, withForward, withBackward,
    proposition, liftClosed, rename] using result

/-- Pointwise Leibniz equality over arbitrary small native types. -/
def pointwiseEquality {n : Nat}
    (domain codomain function other : Tower.Tm n) : Tower.Tm n :=
  .pi domain
    (proof (rawLeibnizAt (rename wk codomain)
      (.app (rename wk function) (.var 0))
      (.app (rename wk other) (.var 0))))

def functionExtensionalityBody {n : Nat}
    (domain codomain function other : Tower.Tm n) : Tower.Tm n :=
  .pi (pointwiseEquality domain codomain function other)
    (rename wk (proof (rawLeibnizAt (arrow domain codomain) function other)))

/-- One universe-polymorphic declaration covers all represented simple
function types. -/
def functionExtensionalityType : Tower.Tm 0 :=
  .pi (sortTm Tower.zero)
    (.pi (sortTm Tower.zero)
      (.pi (arrow (.var 1) (.var 0))
        (.pi (arrow (.var 2) (.var 1))
          (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0)))))

theorem pointwiseEquality_formed {n : Nat} {context : Tower.Ctx n}
    {domain codomain function other : Tower.Tm n}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (codomainTyped : Typing baseRules context codomain (sortTm Tower.zero))
    (functionTyped : Typing baseRules context function (arrow domain codomain))
    (otherTyped : Typing baseRules context other (arrow domain codomain)) :
    Typing baseRules context (pointwiseEquality domain codomain function other)
      (sortTm Tower.zero) := by
  have argumentTyped : Typing baseRules (.snoc context domain) (.var 0)
      (rename wk domain) := by
    simpa only [Ctx.lookup_snoc_zero] using
      (Typing.var (R := baseRules) (Γ := .snoc context domain) 0)
  have functionWeakened := functionTyped.weaken (extension := domain)
  have otherWeakened := otherTyped.weaken (extension := domain)
  rw [arrow_rename] at functionWeakened otherWeakened
  have leftApplied := application_typed functionWeakened argumentTyped
  have rightApplied := application_typed otherWeakened argumentTyped
  have equalityProp := rawLeibnizAt_typed codomainTyped.weaken
    leftApplied rightApplied
  exact pi_zero domainTyped (FormationSensitiveHOLProofFamily.proof_formed equalityProp)

theorem functionExtensionalityBody_formed {n : Nat} {context : Tower.Ctx n}
    {domain codomain function other : Tower.Tm n}
    (domainTyped : Typing baseRules context domain (sortTm Tower.zero))
    (codomainTyped : Typing baseRules context codomain (sortTm Tower.zero))
    (functionTyped : Typing baseRules context function (arrow domain codomain))
    (otherTyped : Typing baseRules context other (arrow domain codomain)) :
    Typing baseRules context
      (functionExtensionalityBody domain codomain function other)
      (sortTm Tower.zero) := by
  have pointwise := pointwiseEquality_formed domainTyped codomainTyped
    functionTyped otherTyped
  have equalityProp := rawLeibnizAt_typed
    (arrow_formed domainTyped codomainTyped) functionTyped otherTyped
  have weakened := (FormationSensitiveHOLProofFamily.proof_formed equalityProp).weaken
    (extension := pointwiseEquality domain codomain function other)
  exact pi_zero pointwise (by
    simpa [FormationSensitiveHOLProofFamily.proof_rename, sortTm, rename] using weakened)

theorem functionExtensionalityType_formed :
    Typing baseRules .nil functionExtensionalityType
      (sortTm (.succ Tower.zero)) := by
  let withDomain := (.snoc (.nil) (sortTm Tower.zero) : Tower.Ctx 1)
  let withTypes := (withDomain.snoc (sortTm Tower.zero) : Tower.Ctx 2)
  have domainType : Typing baseRules withTypes (.var 1) (sortTm Tower.zero) := by
    have lookup : withTypes.lookup 1 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withTypes) 1)
  have codomainType : Typing baseRules withTypes (.var 0) (sortTm Tower.zero) := by
    have lookup : withTypes.lookup 0 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withTypes) 0)
  let functionType : Tower.Tm 2 := arrow (.var 1) (.var 0)
  have functionTypeFormed : Typing baseRules withTypes functionType
      (sortTm Tower.zero) := arrow_formed domainType codomainType
  let withFunction := withTypes.snoc functionType
  let otherType : Tower.Tm 3 := arrow (.var 2) (.var 1)
  have functionTyped : Typing baseRules withFunction (.var 0) otherType := by
    have lookup : withFunction.lookup 0 = otherType := by decide
    simpa only [lookup] using (Typing.var (R := baseRules) (Γ := withFunction) 0)
  have domainFunction : Typing baseRules withFunction (.var 2) (sortTm Tower.zero) := by
    have lookup : withFunction.lookup 2 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := baseRules) (Γ := withFunction) 2)
  have codomainFunction : Typing baseRules withFunction (.var 1)
      (sortTm Tower.zero) := by
    have lookup : withFunction.lookup 1 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := baseRules) (Γ := withFunction) 1)
  have otherTypeFormed : Typing baseRules withFunction otherType
      (sortTm Tower.zero) := arrow_formed domainFunction codomainFunction
  let withOther := withFunction.snoc otherType
  have domainOther : Typing baseRules withOther (.var 3) (sortTm Tower.zero) := by
    have lookup : withOther.lookup 3 = sortTm Tower.zero := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withOther) 3)
  have codomainOther : Typing baseRules withOther (.var 2)
      (sortTm Tower.zero) := by
    have lookup : withOther.lookup 2 = sortTm Tower.zero := by decide
    simpa only [lookup] using (Typing.var (R := baseRules) (Γ := withOther) 2)
  have firstFunction : Typing baseRules withOther (.var 1)
      (arrow (.var 3) (.var 2)) := by
    have lookup : withOther.lookup 1 = arrow (.var 3) (.var 2) := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withOther) 1)
  have secondFunction : Typing baseRules withOther (.var 0)
      (arrow (.var 3) (.var 2)) := by
    have lookup : withOther.lookup 0 = arrow (.var 3) (.var 2) := by decide
    simpa only [lookup] using
      (Typing.var (R := baseRules) (Γ := withOther) 0)
  have bodyFormed := functionExtensionalityBody_formed domainOther codomainOther
    firstFunction secondFunction
  have functionsFormed := pi_zero functionTypeFormed
    (pi_zero otherTypeFormed bodyFormed)
  have overCodomain : Typing baseRules withDomain
      (.pi (sortTm Tower.zero)
        (.pi functionType
          (.pi otherType
            (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0)))))
      (sortTm (.succ Tower.zero)) := by
    apply Typing.cumul
      (Typing.piForm (R := baseRules)
        (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
        functionsFormed (.sort Tower.zero)
        (.sorts (.succ Tower.zero) Tower.zero))
    intro valuation
    simp [LevelExpr.eval, LevelTower.zero]
  have complete : Typing baseRules .nil
      (.pi (sortTm Tower.zero)
        (.pi (sortTm Tower.zero)
          (.pi functionType
            (.pi otherType
              (functionExtensionalityBody (.var 3) (.var 2) (.var 1) (.var 0))))))
      (sortTm (.succ Tower.zero)) := by
    apply Typing.cumul
      (Typing.piForm (R := baseRules)
        (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
        overCodomain (.sort (.succ Tower.zero))
        (.sorts (.succ Tower.zero) (.succ Tower.zero)))
    intro valuation
    simp [LevelExpr.eval, LevelTower.zero]
  simpa only [functionExtensionalityType, withDomain, withTypes, functionType,
    withFunction, otherType, withOther] using complete

def declarations : Signature Tower.Head :=
  (FormationSensitiveHOLProofFamily.declarations.insert
    propositionExtensionalityName ⟨propositionExtensionalityType, none⟩).insert
      functionExtensionalityName ⟨functionExtensionalityType, none⟩

def rules : Rules Tower.Head := extendRules Tower.rules declarations

theorem extendsBase : FormationSensitiveHOLProofFamily.declarations.Extends declarations where
  entries := by
    intro name entry known
    have propositionFresh :
        FormationSensitiveHOLProofFamily.declarations.entries
          propositionExtensionalityName = none := by
      decide
    have functionFresh :
        FormationSensitiveHOLProofFamily.declarations.entries
          functionExtensionalityName = none := by
      decide
    by_cases functionEqual : name = functionExtensionalityName
    · subst name
      rw [functionFresh] at known
      cases known
    by_cases propositionEqual : name = propositionExtensionalityName
    · subst name
      rw [propositionFresh] at known
      cases known
    · simpa [declarations, Signature.insert, functionEqual, propositionEqual] using known
  computation := fun step => step

theorem baseMorphism : baseRules.Morphism rules (fun head => head) :=
  extensionMorphism Tower.rules extendsBase

theorem include_typed {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing baseRules context term type) :
    Typing rules context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typed.mapHead baseMorphism

theorem propositionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (.const propositionExtensionalityName)
      (liftClosed propositionExtensionalityType) := by
  apply Typing.const
  · change combinedType Tower.rules declarations propositionExtensionalityName =
      some propositionExtensionalityType
    apply combinedType_of_signature
    · decide
    · decide
  · exact include_typed propositionExtensionalityType_formed
  · exact .sort Tower.zero

theorem functionExtensionality_typed {n : Nat} (context : Tower.Ctx n) :
    Typing rules context (.const functionExtensionalityName)
      (liftClosed functionExtensionalityType) := by
  apply Typing.const
  · change combinedType Tower.rules declarations functionExtensionalityName =
      some functionExtensionalityType
    apply combinedType_of_signature
    · decide
    · decide
  · exact include_typed functionExtensionalityType_formed
  · exact .sort (.succ Tower.zero)

namespace Controls

/-- Removing the profile removes the proposition-extensionality constant. -/
theorem proposition_extensionality_absent_from_base :
    baseRules.constantType propositionExtensionalityName = none := by
  decide

/-- Removing the profile removes the function-extensionality constant. -/
theorem function_extensionality_absent_from_base :
    baseRules.constantType functionExtensionalityName = none := by
  decide

end Controls

#print axioms rawLeibnizAt_typed
#print axioms propositionExtensionalityType_formed
#print axioms functionExtensionalityType_formed
#print axioms propositionExtensionality_typed
#print axioms functionExtensionality_typed
#print axioms Controls.proposition_extensionality_absent_from_base
#print axioms Controls.function_extensionality_absent_from_base

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalProfile
