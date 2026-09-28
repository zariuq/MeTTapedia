import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation

/-!
# Native controls for the certified-transform program

The linearized program's conversion is Church–Rosser, so it separates terms
without computation steps.  It contains every step of the draft's program, so
each control below also holds for the draft.

* Reflexivity at the open index `k : num` is not evidence for `eqAt k`, while
  reflexivity at every numeral is: `add zero k` does not compute to `k`.
* The represented equation `Holds (eq a b)` never converts to an identity
  type.  No conversion turns equation evidence into identity evidence, and
  reflexivity is never evidence for `holdsAt`.
* The reflexivity assumption states `∀ x. eq x x`; the constant is not itself
  a proof of an equation.
* The base evidence at index zero is not evidence at any other numeral.
* Without the assumption declarations, their constants have no type.
* The call the runtime rejects with `BadArgType 6`, a number in the evidence
  slot, has no type; nor has a call whose family `λ k. k` is not a type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (instanceOf Normal)
open SetProfile (baseName constantName numTy zeroNative sucNative addNative
  eqNumNative holdsName targetRules)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence CertifiedTransformProgram.Preservation
open CertifiedTransformProgram.Execution (numeral holdsBase)
open Mettapedia.Logic

/-! ## Terms without computation steps -/

/-- A term that no equation left side matches has no root step. -/
theorem no_root {n : Nat} {term target : Tower.Tm n}
    (step : linearRules.computation.step term target)
    (natives : SetProfile.nativeEquations.all
      (fun equation => !instanceOf equation.2.1 term) = true)
    (package : linearEquations.all (fun equation => !instanceOf equation.2.1 term) = true)
    (implication : instanceOf implicationLeft term = false)
    (universal : ∀ type, instanceOf (universalLeft type) term = false) : False := by
  obtain ⟨m, left, right, rule, meets⟩ := linearConstructors.root_instance step
  cases rule with
  | implication => rw [implication] at meets; cases meets
  | universal type => rw [universal type] at meets; cases meets
  | native listed =>
      have excluded : (!instanceOf left term) = true := List.all_eq_true.mp natives _ listed
      rw [meets] at excluded
      cases excluded
  | package listed =>
      have excluded : (!instanceOf left term) = true := List.all_eq_true.mp package _ listed
      rw [meets] at excluded
      cases excluded

/-- Numerals have no computation steps. -/
theorem numeral_normal {n : Nat} : ∀ count : Nat, Normal linearRules (numeral count : Tower.Tm n)
  | 0 => Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl))
  | count + 1 =>
      Normal.app (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
        (numeral_normal count) (fun _ equal => by cases equal)
        (fun step => no_root step rfl rfl rfl (fun _ => rfl))

/-- `add zero k` at a variable `k` has no computation step: neither equation of
`add` matches a variable in its second argument. -/
theorem addZeroVar_normal {n : Nat} (index : Fin n) :
    Normal linearRules (addNative zeroNative (.var index) : Tower.Tm n) :=
  Normal.app
    (Normal.app (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
      (Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
      (fun _ equal => by cases equal)
      (fun step => no_root step rfl rfl rfl (fun _ => rfl)))
    (linearConstructors.normal_var index) (fun _ equal => by cases equal)
    (fun step => no_root step rfl rfl rfl (fun _ => rfl))

/-! ## The represented equation -/

/-- `Holds (eq@num left right)`. -/
abbrev equation {n : Nat} (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.const holdsName) (.app (.app (.const (SetProfile.eqName numTy)) left) right)

theorem step_equation {n : Nat} {left right target : Tower.Tm n}
    (step : Step linearRules.headEq (equation left right) target linearRules.computation) :
    ∃ left' right', target = equation left' right' ∧
      StepStar linearRules left left' ∧ StepStar linearRules right right' := by
  cases step with
  | root rootStep => exact (no_root rootStep rfl rfl rfl (fun _ => rfl)).elim
  | congAppFun inner =>
      cases inner with
      | root rootStep => exact (no_root rootStep rfl rfl rfl (fun _ => rfl)).elim
  | congAppArg inner =>
      cases inner with
      | root rootStep => exact (no_root rootStep rfl rfl rfl (fun _ => rfl)).elim
      | congAppFun inner =>
          cases inner with
          | root rootStep => exact (no_root rootStep rfl rfl rfl (fun _ => rfl)).elim
          | congAppFun inner =>
              cases inner with
              | root rootStep => exact (no_root rootStep rfl rfl rfl (fun _ => rfl)).elim
          | congAppArg inner => exact ⟨_, _, rfl, .tail .refl inner, .refl⟩
      | congAppArg inner => exact ⟨_, _, rfl, .refl, .tail .refl inner⟩

theorem stepStar_equation {n : Nat} {left right target : Tower.Tm n}
    (steps : StepStar linearRules (equation left right) target) :
    ∃ left' right', target = equation left' right' ∧
      StepStar linearRules left left' ∧ StepStar linearRules right right' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail _ finalStep ih =>
      obtain ⟨_, _, rfl, first, second⟩ := ih
      obtain ⟨_, _, rfl, lastFirst, lastSecond⟩ := step_equation finalStep
      exact ⟨_, _, rfl, first.trans lastFirst, second.trans lastSecond⟩

/-- Convertible equations have convertible sides. -/
theorem equation_components {n : Nat} {left left' right right' : Tower.Tm n}
    (conversion : Conv linearRules.headEq (equation left right) (equation left' right')
      linearRules.computation) :
    Conv linearRules.headEq left left' linearRules.computation ∧
      Conv linearRules.headEq right right' linearRules.computation := by
  obtain ⟨_, firstPath, secondPath⟩ := churchRosser conversion
  obtain ⟨_, _, firstShape, firstLeft, firstRight⟩ := stepStar_equation firstPath
  obtain ⟨_, _, secondShape, secondLeft, secondRight⟩ := stepStar_equation secondPath
  rw [firstShape] at secondShape
  simp only [Tm.app.injEq, true_and] at secondShape
  obtain ⟨rfl, rfl⟩ := secondShape
  exact ⟨.trans _ _ _ (stepStar_implies_conv firstLeft) (.symm _ _ (stepStar_implies_conv secondLeft)),
    .trans _ _ _ (stepStar_implies_conv firstRight) (.symm _ _ (stepStar_implies_conv secondRight))⟩

/-- No conversion identifies a represented equation with an identity type, at
any terms. -/
theorem equation_not_identity {n : Nat} {left right carrier point endpoint : Tower.Tm n}
    (conversion : Conv linearRules.headEq (equation left right) (.id carrier point endpoint)
      linearRules.computation) : False := by
  obtain ⟨_, firstPath, secondPath⟩ := churchRosser conversion
  obtain ⟨_, _, firstShape, _, _⟩ := stepStar_equation firstPath
  obtain ⟨_, _, _, secondShape, _⟩ := linearConstructors.stepStar_identity secondPath
  rw [firstShape] at secondShape
  cases secondShape

theorem equation_not_head {n : Nat} {left right : Tower.Tm n} {head : Tower.Head}
    (conversion : Conv linearRules.headEq (equation left right) (.head head)
      linearRules.computation) : False := by
  obtain ⟨_, firstPath, secondPath⟩ := churchRosser conversion
  obtain ⟨_, _, firstShape, _, _⟩ := stepStar_equation firstPath
  obtain ⟨_, secondShape⟩ := linearConstructors.stepStar_head secondPath
  rw [firstShape] at secondShape
  cases secondShape

theorem equation_not_pi {n : Nat} {left right domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (conversion : Conv linearRules.headEq (equation left right) (.pi domain codomain)
      linearRules.computation) : False := by
  obtain ⟨_, firstPath, secondPath⟩ := churchRosser conversion
  obtain ⟨_, _, firstShape, _, _⟩ := stepStar_equation firstPath
  obtain ⟨_, _, secondShape⟩ := linearConstructors.stepStar_pi secondPath
  rw [firstShape] at secondShape
  cases secondShape

/-! ## The stored families -/

/-- `eqAt k = Id num (add zero k) k`. -/
theorem eqAt_converts {n : Nat} (index : Tower.Tm n) :
    Conv linearRules.headEq (eqAtApp index) (.id numT (addNative zeroNative index) index)
      linearRules.computation :=
  .rel _ _ (.root (linearSchema_sound
    (.package (List.getElem_mem (l := linearEquations) (n := 3) (by decide))) (fun _ => index)))

/-- `holdsAt k = Holds (eq (add zero k) k)`. -/
theorem holdsAt_converts {n : Nat} (index : Tower.Tm n) :
    Conv linearRules.headEq (holdsAtApp index) (equation (addNative zeroNative index) index)
      linearRules.computation :=
  .rel _ _ (.root (linearSchema_sound
    (.package (List.getElem_mem (l := linearEquations) (n := 12) (by decide))) (fun _ => index)))

/-! ## Reflexivity at an open index -/

/-- At the open index `k : num`, reflexivity is not evidence for `eqAt k`. -/
theorem refl_not_eqAt_open :
    ¬ Typing linearRules (.snoc .nil numT) (.refl (.var 0)) (eqAtApp (.var 0)) := by
  intro typed
  obtain ⟨_, _, adjustment⟩ := CertifiedTransforms.reflGeneration typed
  have unfolded := eqAt_converts (n := 1) (.var 0)
  have conversion := adjustment.toConvOfTargetDisjointHeads
    (fun _ toHead => linearConstructors.identity_not_head (.trans _ _ _ (.symm _ _ unfolded) toHead))
  obtain ⟨_, toPoint, _⟩ := linearConstructors.identity_components (.trans _ _ _ conversion unfolded)
  have same := linearConstructors.eq_of_normal (linearConstructors.normal_var 0) (addZeroVar_normal 0) toPoint
  cases same

/-- Reflexivity is evidence for `eqAt` at every numeral, and not at the open
index. -/
theorem refl_eqAt_numerals_only :
    (∀ count : Nat, Typing linearRules .nil (.refl (numeral count)) (eqAtApp (numeral count))) ∧
      ¬ Typing linearRules (.snoc .nil numT) (.refl (.var 0)) (eqAtApp (.var 0)) :=
  ⟨fun count => linearHost.typed (CertifiedTransformProgram.Execution.refl_eqAt count), refl_not_eqAt_open⟩

/-- Native induction proves `eqAt k` at an open index:
`num-rec eqAt (refl zero) sucMove k`.  This is a native proof of the same
statement, built from the recursor and the identity step; it does not use the
source proof. -/
def nativeZeroAdd {n : Nat} (number : Tower.Tm n) : Tower.Tm n :=
  numRecApp (.const eqAtName) (.refl zeroNative) (.const sucMoveName) number

theorem nativeZeroAdd_typed {n : Nat} {Γ : Tower.Ctx n} {number : Tower.Tm n}
    (numberTyped : Typing R Γ number numT) :
    Typing R Γ (nativeZeroAdd number) (eqAtApp number) :=
  Typing.appElim
    (Typing.appElim
      (Typing.appElim (Typing.appElim (numRec_typed Γ) (declared_typed lookup_eqAt eqAtType_formed Γ))
        (CertifiedTransformProgram.Execution.refl_eqAt (Γ := Γ) 0))
      (sucMove_typed Γ))
    numberTyped

/-- At the open index, native induction is evidence for `eqAt k` and
reflexivity is not. -/
theorem open_index_evidence :
    Typing R (.snoc .nil numT) (nativeZeroAdd (.var 0)) (eqAtApp (.var 0)) ∧
      ¬ Typing linearRules (.snoc .nil numT) (.refl (.var 0)) (eqAtApp (.var 0)) :=
  ⟨nativeZeroAdd_typed (Typing.var 0), refl_not_eqAt_open⟩

/-- Reflexivity is never evidence for `holdsAt`, at any index. -/
theorem refl_not_holdsAt {n : Nat} {Γ : Tower.Ctx n} (witness index : Tower.Tm n) :
    ¬ Typing linearRules Γ (.refl witness) (holdsAtApp index) := by
  intro typed
  obtain ⟨_, _, adjustment⟩ := CertifiedTransforms.reflGeneration typed
  have unfolded := holdsAt_converts index
  have conversion := adjustment.toConvOfTargetDisjointHeads
    (fun _ toHead => equation_not_head (.trans _ _ _ (.symm _ _ unfolded) toHead))
  exact equation_not_identity (.symm _ _ (.trans _ _ _ conversion unfolded))

/-! ## The reflexivity assumption -/

/-- The predicate of the reflexivity assumption: `λ x. eq x x`. -/
abbrev reflPredicate : Tower.Tm 0 :=
  .lam (.app (.app (.const (SetProfile.eqName numTy)) (.var 0)) (.var 0))

theorem reflLookup :
    linearRules.constantType SetProfile.reflName =
      some (FormationSensitiveHOLGenericProofFamily.proof holdsName SetProfile.reflCode) := by
  have known := (includeMorphism targetRules linearDeclarations).constantType
    (SetProfile.target_lookup 1)
  simp only [Tm.mapHead_id] at known
  exact known

/-- The declared type of the reflexivity assumption decodes to
`Π x : num. Holds ((λ x. eq x x) x)`. -/
theorem reflDecoded {n : Nat} :
    Conv linearRules.headEq
      (liftClosed (FormationSensitiveHOLGenericProofFamily.proof holdsName
        SetProfile.reflCode) : Tower.Tm n)
      (.pi numT (.app (.const holdsName) (.app (liftClosed reflPredicate) (.var 0))))
      linearRules.computation :=
  .rel _ _ (.root (linearSchema_sound (.universal numTy) (fun _ => liftClosed reflPredicate)))

/-- The reflexivity assumption is not itself a proof of an equation. -/
theorem reflAssumption_not_equation {n : Nat} {Γ : Tower.Ctx n} (left right : Tower.Tm n) :
    ¬ Typing linearRules Γ (.const SetProfile.reflName) (equation left right) := by
  intro typed
  have conversion := (typed.constantAdjustment reflLookup).toConvOfTargetDisjointHeads
    (fun _ toHead => equation_not_head toHead)
  exact equation_not_pi (.trans _ _ _ (.symm _ _ conversion) reflDecoded)

/-! ## A wrong index -/

/-- The base evidence `refl@ zero` proves the equation at zero only: it is not
evidence for `holdsAt` at any successor numeral. -/
theorem holdsBase_not_successor {n : Nat} {Γ : Tower.Ctx n} (count : Nat) :
    ¬ Typing linearRules Γ holdsBase (holdsAtApp (numeral (count + 1))) := by
  intro typed
  obtain ⟨_, codomain, functionTyped, _, adjustment, _⟩ := typed.appGeneration
  have toPi := (functionTyped.constantAdjustment reflLookup).toConvOfPiTarget piConversionBoundary
  obtain ⟨_, codomains⟩ := piConversionBoundary.components (.trans _ _ _ (.symm _ _ reflDecoded) toPi)
  have atZero := codomains.substitute (subst0 zeroNative)
  have reduced : (subst (subst0 zeroNative)
      (.app (.const holdsName) (.app (liftClosed reflPredicate) (.var 0))) : Tower.Tm n) =
      .app (.const holdsName)
        (.app (.lam (.app (.app (.const (SetProfile.eqName numTy)) (.var 0)) (.var 0)))
          zeroNative) :=
    rfl
  rw [reduced] at atZero
  have beta : Conv linearRules.headEq
      (.app (.const holdsName)
        (.app (.lam (.app (.app (.const (SetProfile.eqName numTy)) (.var 0)) (.var 0)))
          zeroNative) : Tower.Tm n)
      (equation zeroNative zeroNative) linearRules.computation :=
    .rel _ _ (.congAppArg (.betaPi _ _))
  have unfolded := holdsAt_converts (numeral (count + 1) : Tower.Tm n)
  have toDisplayed := adjustment.toConvOfTargetDisjointHeads
    (fun _ toHead => equation_not_head (.trans _ _ _ (.symm _ _ unfolded) toHead))
  have chain := Relation.EqvGen.trans _ _ _ (.symm _ _ beta)
    (.trans _ _ _ atZero (.trans _ _ _ toDisplayed unfolded))
  obtain ⟨_, sides⟩ := equation_components chain
  have same := linearConstructors.eq_of_normal (numeral_normal 0) (numeral_normal (count + 1)) sides
  cases same

/-- Index faithfulness of the consumer's family: `holdsAt a` and `holdsAt b`
convert only when `a` and `b` do. -/
theorem holdsAt_injective {n : Nat} {first second : Tower.Tm n}
    (conversion : Conv linearRules.headEq (holdsAtApp first) (holdsAtApp second)
      linearRules.computation) :
    Conv linearRules.headEq first second linearRules.computation :=
  (equation_components (.trans _ _ _ (.symm _ _ (holdsAt_converts first))
    (.trans _ _ _ conversion (holdsAt_converts second)))).2

/-! ## Dropped assumptions -/

/-- Without the assumption declarations, the reflexivity assumption has no
type: the proof family alone does not declare it. -/
theorem reflAssumption_undeclared {n : Nat} {Γ : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Typing SetProfile.proofRules Γ (.const SetProfile.reflName) type := by
  intro typed
  obtain ⟨_, known, _⟩ := typed.toRaw.constantGeneration
  rw [SetProfile.proofRules_lookup_none SetProfile.reflName_fresh
    (by decide)] at known
  cases known

/-! ## Malformed calls -/

/-- `num` is a declared sort without equations: it has no computation step. -/
theorem numT_normal {n : Nat} : Normal linearRules (numT : Tower.Tm n) :=
  Normal.const _ (fun step => no_root step rfl rfl rfl (fun _ => rfl))

theorem numT_not_head {n : Nat} {head : Tower.Head}
    (conversion : Conv linearRules.headEq (numT : Tower.Tm n) (.head head)
      linearRules.computation) : False := by
  obtain ⟨_, first, second⟩ := churchRosser conversion
  have same := Normal.stepStar numT_normal first
  obtain ⟨_, shape⟩ := linearConstructors.stepStar_head second
  rw [same] at shape
  cases shape

theorem numT_not_identity {n : Nat} {carrier point endpoint : Tower.Tm n}
    (conversion : Conv linearRules.headEq numT (.id carrier point endpoint)
      linearRules.computation) : False := by
  obtain ⟨_, first, second⟩ := churchRosser conversion
  have same := Normal.stepStar numT_normal first
  obtain ⟨_, _, _, shape, _⟩ := linearConstructors.stepStar_identity second
  rw [same] at shape
  cases shape

theorem zeroLookup :
    linearRules.constantType (constantName .zero) =
      some (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 numTy) := by
  have known := proofToLinear.constantType
    ((FormationSensitiveHOLGenericProofFamily.sourceMorphism SetProfile.signature
      holdsName).constantType (SetProfile.lookup_constant .zero))
  simp only [Tm.mapHead_id] at known
  exact known

/-- The runtime rejects `iterCert (suc zero) num eqAt sucStep zero zero` with
`BadArgType 6`: the evidence slot holds a number where `eqAt zero` is due.
The call has no type. -/
theorem iterCall_numberAsEvidence {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation linearRules Γ) {type : Tower.Tm n} :
    ¬ Typing linearRules Γ
      (iterApp (numeral 1) numT (.const eqAtName) (.const sucStepName) zeroNative zeroNative)
      type := by
  intro typed
  obtain ⟨morphism, _, _, _⟩ := DeclarationSpine.recoverTelescope universes
    piConversionBoundary formed iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0)))
    (CertifiedTransformProgram.Execution.patternValues
      ![numT, .const eqAtName, .const sucStepName, zeroNative, zeroNative])
    (linearHost.iterSpine (linearHost.typed (CertifiedTransformProgram.Execution.numeral_typed 1))) typed
  have evidenceTyped : Typing linearRules Γ zeroNative (eqAtApp zeroNative) := morphism 0
  have conversion : Conv linearRules.headEq numT (eqAtApp zeroNative) linearRules.computation :=
    (evidenceTyped.constantAdjustment zeroLookup).toConvOfTargetDisjointHeads
      (fun _ toHead => linearConstructors.identity_not_head (.trans _ _ _ (.symm _ _ (eqAt_converts zeroNative)) toHead))
  exact numT_not_identity (.trans _ _ _ conversion (eqAt_converts zeroNative))

/-- A family whose body is not a type, `λ k. k`, does not fit the iterator's
family slot `num → Type`: a call with it has no type. -/
theorem iterCall_malformedFamily {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation linearRules Γ) {count step value evidence type : Tower.Tm n}
    (countTyped : Typing linearRules Γ count numT) :
    ¬ Typing linearRules Γ (iterApp count numT (.lam (.var 0)) step value evidence) type := by
  intro typed
  obtain ⟨morphism, _, _, _⟩ := DeclarationSpine.recoverTelescope universes
    piConversionBoundary formed iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0)))
    (CertifiedTransformProgram.Execution.patternValues ![numT, .lam (.var 0), step, value, evidence])
    (linearHost.iterSpine countTyped) typed
  have familyTyped : Typing linearRules Γ (.lam (.var 0)) (.pi numT U0) := morphism 3
  obtain ⟨domain, codomain, _, _, _, bodyTyped, adjustment⟩ := familyTyped.lamGeneration
  obtain ⟨domains, codomains⟩ :=
    piConversionBoundary.components (adjustment.toConvOfPiTarget piConversionBoundary)
  have shifted : Conv linearRules.headEq (rename wk domain) numT linearRules.computation :=
    domains.renameTerms wk
  have toBody := bodyTyped.toRaw.variableAdjustment.toConvOfSourceDisjointHeads
    (fun _ toHead => numT_not_head (.trans _ _ _ (.symm _ _ shifted) toHead))
  exact numT_not_head (.trans _ _ _ (.symm _ _ shifted) (.trans _ _ _ toBody codomains))

/-! ## Binding -/

/-- Substitution does not capture: `((λ x. λ y. x) y) z` runs to `y`.  In de
Bruijn form this is also `((λ x. λ w. x) y) z`, so renaming the inner binder
cannot change the value. -/
theorem binding_control :
    CertifiedTransformProgram.Execution.Runs
      (.app (.app (.lam (.lam (.var 1))) (.var 1)) (.var 0) : Tower.Tm 2) (.var 1) :=
  .tail (.tail .refl (.congAppFun (.betaPi _ _))) (.betaPi _ _)

/-! ## Axiom audit -/

#print axioms no_root
#print axioms numeral_normal
#print axioms addZeroVar_normal
#print axioms equation_components
#print axioms equation_not_identity
#print axioms refl_not_eqAt_open
#print axioms refl_eqAt_numerals_only
#print axioms refl_not_holdsAt
#print axioms reflAssumption_not_equation
#print axioms holdsBase_not_successor
#print axioms holdsAt_injective
#print axioms reflAssumption_undeclared
#print axioms open_index_evidence
#print axioms binding_control
#print axioms iterCall_numberAsEvidence
#print axioms iterCall_malformedFamily

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Controls
