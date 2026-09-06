import Mettapedia.Logic.HOL.Syntax.TypeSubstitution
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Derivation transport under substitution of simple types

Base types may be interpreted as arbitrary simple types.  The resulting typed
term translation preserves extensional HOL derivations, including quantifiers,
substitution, beta equality, and eta equality.  This is proof transport, not a
construction of model reducts for arbitrary Henkin domains.

The positive example transports a quantified beta law to a function type.  The
negative example identifies two base types: the target proves the translated
sentence, but a standard source model refutes the original sentence.  No
constants are identified in this example; there are no constants.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u u' v v'

variable {Base : Type u} {Base' : Type u'}
  {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}

namespace ExtDerivation

/-- Weakening hypotheses commutes with retyping every term and its context. -/
theorem mapTypes_weakenHyps
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {A : Ty Base} (Δ : List (Formula Const Γ)) :
    (weakenHyps (σ := A) Δ).map (HOL.mapTypes σ constants) =
      weakenHyps (σ := Ty.substitute σ A)
        (Δ.map (HOL.mapTypes σ constants)) := by
  simp only [weakenHyps, List.map_map]
  apply List.map_congr_left
  intro formula _membership
  exact HOL.mapTypes_weaken σ constants formula

/-- Type-derived interpretations preserve actual extensional derivations. -/
theorem mapTypes
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    ExtDerivation Const Δ φ →
      ExtDerivation Const'
        (Δ.map (HOL.mapTypes σ constants))
        (HOL.mapTypes σ constants φ) := by
  intro derivation
  induction derivation with
  | hyp membership =>
      exact .hyp (List.mem_map.mpr ⟨_, membership, rfl⟩)
  | topI => exact .topI
  | botE _ induction => exact .botE induction
  | andI _ _ left right => exact .andI left right
  | andEL _ induction => exact .andEL induction
  | andER _ induction => exact .andER induction
  | orIL _ induction => exact .orIL induction
  | orIR _ induction => exact .orIR induction
  | orE _ _ _ disjunction left right => exact .orE disjunction left right
  | impI _ induction => exact .impI induction
  | impE _ _ implication premise => exact .impE implication premise
  | notI _ induction => exact .notI induction
  | notE _ _ negation premise => exact .notE negation premise
  | allI _ induction =>
      exact .allI (by
        simpa only [Ty.substitute, List.map_cons, weakenHyps, List.map_map,
          Function.comp_def, HOL.mapTypes_weaken] using induction)
  | allE term _ induction =>
      simpa only [HOL.mapTypes_instantiate] using
        (.allE (HOL.mapTypes σ constants term) induction)
  | exI term premise induction =>
      rename_i Γ' Δ' A body
      have translated : ExtDerivation Const'
          (Δ'.map (HOL.mapTypes σ constants))
          (instantiate (HOL.mapTypes σ constants term)
            (HOL.mapTypes σ constants body)) := by
        simpa only [Ty.substitute, HOL.mapTypes_instantiate] using induction
      exact .exI (HOL.mapTypes σ constants term) translated
  | exE _ _ existential body =>
      exact .exE existential (by
        simpa only [Ty.substitute, List.map_cons, weakenHyps, List.map_map,
          Function.comp_def, HOL.mapTypes_weaken] using body)
  | eqRefl term => exact .eqRefl (HOL.mapTypes σ constants term)
  | eqSymm _ induction => exact .eqSymm induction
  | eqTrans _ _ left right => exact .eqTrans left right
  | eqPropI _ _ forward backward => exact .eqPropI forward backward
  | eqPropEL _ induction => exact .eqPropEL induction
  | eqPropER _ induction => exact .eqPropER induction
  | eqApp term _ induction => exact .eqApp (HOL.mapTypes σ constants term) induction
  | eqAppArg function _ induction =>
      exact .eqAppArg (HOL.mapTypes σ constants function) induction
  | eqLam _ induction =>
      exact .eqLam (by
        simpa only [Ty.substitute, List.map_cons, HOL.mapTypes, weakenHyps,
          List.map_map, Function.comp_def, HOL.mapTypes_weaken] using induction)
  | funExt premise induction =>
      rename_i Γ' Δ' A B f g
      exact .funExt (σ := Ty.substitute σ A) (τ := Ty.substitute σ B)
        (f := HOL.mapTypes σ constants f) (g := HOL.mapTypes σ constants g) (by
        simpa only [Ty.substitute, List.map_cons, HOL.mapTypes,
          HOL.mapTypes_weaken, Var.mapTypes] using induction)
  | beta argument body =>
      simpa only [HOL.mapTypes, HOL.mapTypes_instantiate] using
        (.beta (HOL.mapTypes σ constants argument) (HOL.mapTypes σ constants body))
  | eta function =>
      simpa only [HOL.mapTypes, HOL.mapTypes_weaken, Var.mapTypes] using
        (.eta (HOL.mapTypes σ constants function))

/-- In particular, closed theorems transport without adding target assumptions. -/
theorem theorem_mapTypes
    (σ : Base → Ty Base')
    (constants : ∀ {A}, Const A → Const' (Ty.substitute σ A))
    {φ : ClosedFormula Const} (proof : Theorem Const φ) :
    Theorem Const' (HOL.mapTypes σ constants φ) :=
  mapTypes σ constants proof

end ExtDerivation

namespace TypeSubstitutionExample

universe w

/-- The empty constant signature isolates what type substitution itself does. -/
abbrev NoConstants (B : Type) : Ty B → Type := fun _ => Empty

/-- The beta equation for the identity function, universally quantified. -/
def quantifiedBeta {B : Type} (A : Ty B) : ClosedFormula (NoConstants B) :=
  .all (.eq (.app (.lam (.var .vz)) (.var (.vz : Var [A] A))) (.var .vz))

/-- A beta rule under a genuine object-language universal quantifier. -/
theorem quantifiedBeta_provable {B : Type} (A : Ty B) :
    ExtDerivation.Theorem (NoConstants B) (quantifiedBeta A) := by
  apply ExtDerivation.allI
  exact .beta (.var (.vz : Var [A] A)) (.var .vz)

/-- Interpret the source ground type as a target function type. -/
def functionInterpretation : Unit → Ty Unit :=
  fun _ => .arr (.base ()) (.base ())

def noConstantsMap {B B' : Type} (σ : B → Ty B') :
    ∀ {A}, NoConstants B A → NoConstants B' (Ty.substitute σ A) :=
  fun {_} constant => nomatch constant

/-- The source quantifier becomes a quantifier over functions, not ground values. -/
theorem mapTypes_quantifiedBeta :
    HOL.mapTypes functionInterpretation (noConstantsMap functionInterpretation)
        (quantifiedBeta (.base ())) =
      quantifiedBeta (.arr (.base ()) (.base ())) := rfl

/-- The function-typed beta theorem is obtained by transporting its source proof. -/
theorem function_quantifiedBeta_provable :
    ExtDerivation.Theorem (NoConstants Unit)
      (quantifiedBeta (.arr (.base ()) (.base ()))) := by
  rw [← mapTypes_quantifiedBeta]
  exact ExtDerivation.theorem_mapTypes functionInterpretation
    (noConstantsMap functionInterpretation) (quantifiedBeta_provable (.base ()))

/-- Every two elements of the selected type are equal. -/
def subsingletonSentence {B : Type} (A : Ty B) : ClosedFormula (NoConstants B) :=
  .all (.all (.eq (.var (.vs (.vz : Var [A] A))) (.var .vz)))

/-- A relation between two distinct source base domains. -/
def sourceClaim : ClosedFormula (NoConstants Bool) :=
  .imp (subsingletonSentence (.base false)) (subsingletonSentence (.base true))

/-- Both source base domains are sent to the same target base type. -/
def collapseTypes : Bool → Ty Unit := fun _ => .base ()

def targetClaim : ClosedFormula (NoConstants Unit) :=
  .imp (subsingletonSentence (.base ())) (subsingletonSentence (.base ()))

theorem mapTypes_sourceClaim :
    HOL.mapTypes collapseTypes (noConstantsMap collapseTypes) sourceClaim =
      targetClaim := rfl

/-- The collapsed target claim is implication reflexivity. -/
theorem targetClaim_provable :
    ExtDerivation.Theorem (NoConstants Unit) targetClaim :=
  .impI (.hyp List.mem_cons_self)

/-- The target implication is valid without fullness or extensionality assumptions. -/
theorem targetClaim_valid (model : HenkinModel.{0, 0, w} Unit (NoConstants Unit)) :
    model.models targetClaim := by
  change model.models (subsingletonSentence (.base ())) →
    model.models (subsingletonSentence (.base ()))
  exact id

/-- The two source base domains have different cardinalities. -/
def separatingCarrier : Bool → Type 1
  | false => ULift.{1} Unit
  | true => ULift.{1} Bool

def separatingModel : HenkinModel.{0, 0, 0} Bool (NoConstants Bool) :=
  HenkinModel.standard separatingCarrier (fun {_} constant => nomatch constant)

/-- A singleton source domain and a two-element source domain refute the claim. -/
theorem separatingModel_refutes_sourceClaim :
    ¬ separatingModel.models sourceClaim := by
  change ¬ ((∀ x : ULift.{1} Unit, True →
      ∀ y : ULift.{1} Unit, True → x = y) →
    ∀ x : ULift.{1} Bool, True → ∀ y : ULift.{1} Bool, True → x = y)
  intro claim
  have singleton : ∀ x : ULift.{1} Unit, True →
      ∀ y : ULift.{1} Unit, True → x = y := by
    intro x _ y _
    exact Subsingleton.elim x y
  have impossible := claim singleton ⟨false⟩ True.intro ⟨true⟩ True.intro
  cases impossible

/-- Soundness rules out a source derivation independently of the translation. -/
theorem sourceClaim_not_provable :
    ¬ ExtDerivation.Theorem (NoConstants Bool) sourceClaim := by
  intro proof
  apply separatingModel_refutes_sourceClaim
  exact Soundness.extTheorem_sound proof separatingModel
    (separatingModel.functionsRespectEqv_of_fullDomains
      (HenkinModel.fullDomains_standard _ _))

/-- Arbitrary type substitution preserves proofs but need not reflect them. -/
theorem collapseTypes_does_not_reflect_theorems :
    ExtDerivation.Theorem (NoConstants Unit)
        (HOL.mapTypes collapseTypes (noConstantsMap collapseTypes) sourceClaim) ∧
      ¬ ExtDerivation.Theorem (NoConstants Bool) sourceClaim := by
  rw [mapTypes_sourceClaim]
  exact ⟨targetClaim_provable, sourceClaim_not_provable⟩

/-- This particular source model has no target model agreeing on all translated
sentences. The obstruction is the chosen type collapse, not model expansion in
general, and the target may have arbitrary Henkin domains. -/
theorem no_satisfaction_expansion :
    ¬ ∃ target : HenkinModel.{0, 0, w} Unit (NoConstants Unit),
      ∀ sentence : ClosedFormula (NoConstants Bool),
        separatingModel.models sentence ↔
          target.models (HOL.mapTypes collapseTypes (noConstantsMap collapseTypes) sentence) := by
  rintro ⟨target, agreement⟩
  apply separatingModel_refutes_sourceClaim
  apply (agreement sourceClaim).mpr
  rw [mapTypes_sourceClaim]
  exact targetClaim_valid target

end TypeSubstitutionExample

#print axioms ExtDerivation.mapTypes
#print axioms TypeSubstitutionExample.function_quantifiedBeta_provable
#print axioms TypeSubstitutionExample.collapseTypes_does_not_reflect_theorems
#print axioms TypeSubstitutionExample.no_satisfaction_expansion

end Mettapedia.Logic.HOL
