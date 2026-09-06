import Mettapedia.Languages.Megalodon.NativeProofEnvironment
import Mettapedia.Languages.Megalodon.PreambleFragmentVertical
import Mettapedia.Languages.Megalodon.HenkinProofSoundness

/-!
# A declaration-sensitive restriction of the native powerset proof

The existing proof of `forall z, z in Power z` uses powerset introduction,
membership, and powerset. Its finite dependency manifest permits restriction
of the five-principle preamble environment to precisely those three entries.
The native checker is unchanged, and its verdict is preserved at the same
fuel. Removing or changing the used axiom instead rejects this proof.

The independent Henkin interpretation below distinguishes proof-local
restriction from conservativity of theories: powerset elimination is unused
by this proof but is not valid in every interpretation satisfying powerset
introduction. Known propositions must be true in the chosen interpretation;
successful native lookup does not establish their truth.

The separating interpretation is over the retained HOL signature. It is not
a model of the existing extensional set-operation class: that class already
requires the full powerset specification, including elimination. Weakening
authored axioms inside that fixed class would not weaken those model laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.PreambleDependencyRestriction

universe u

open MathdataKernel NativeSupport NativeProofEnvironment
open SetOperationSemanticAuthority PreambleFragmentVertical

/-- The retained native declarations, with their original types and proposition. -/
def restrictedEnvironment : Environment where
  terms := [membershipDeclaration, powerDeclaration]
  known := [AxiomTag.powerIntro.knownDeclaration]

/-- Direct proof dependencies closed through the retained known proposition. -/
def manifest : Support :=
  {.knownName AxiomTag.powerIntro.name, .termName membershipName, .termName powerName}

theorem manifest_accepted :
    proofFrameCheck environment restrictedEnvironment manifest [] subsetPowerProof
      subsetPowerFormula.erase = true := by decide

/-- Reuse concerns the actual checker verdict, including failure, at every fuel. -/
theorem native_verdict_restricted (fuel depth : Nat) (context : List Tp) :
    checkProof restrictedEnvironment fuel depth context [] subsetPowerProof
        subsetPowerFormula.erase =
      checkProof environment fuel depth context [] subsetPowerProof
        subsetPowerFormula.erase :=
  checkProof_frame_of_check manifest_accepted fuel depth context

theorem restricted_native_accepted :
    checkProof restrictedEnvironment 32 0 [] [] subsetPowerProof
      subsetPowerFormula.erase = true := by
  rw [native_verdict_restricted]
  exact subsetPower_native_accepted

theorem restricted_propositions_formed :
    checkProposition restrictedEnvironment 0 [] subsetPowerFormula.erase = true ∧
      checkProposition restrictedEnvironment 0 [] powerIntroFormula.erase = true := by decide

/-- Powerset elimination really is absent, rather than hidden behind an alias. -/
theorem unused_axiom_removed :
    environment.lookupKnown? AxiomTag.powerElim.name = some powerElimFormula.erase ∧
      restrictedEnvironment.lookupKnown? AxiomTag.powerElim.name = none := by decide

theorem unused_symbols_removed :
    restrictedEnvironment.lookupTerm? emptyName = none ∧
      restrictedEnvironment.lookupTerm? unionName = none := by decide

/-- The omitted axiom's own proof does not survive the restriction. The
frame result for `subsetPowerProof` is not a claim about every source proof. -/
theorem omitted_axiom_native_verdict_differs :
    checkProof environment 32 0 [] [] (.known AxiomTag.powerElim.name)
        powerElimFormula.erase = true ∧
      checkProof restrictedEnvironment 32 0 [] [] (.known AxiomTag.powerElim.name)
        powerElimFormula.erase = false := by
  refine ⟨AxiomTag.powerElim.native_accepted, ?_⟩
  unfold checkProof
  split <;> simp [checkNormalizedProof, inferProof, unused_axiom_removed.2]

def missingAxiom : Environment := { restrictedEnvironment with known := [] }

/-- Keep the used name but change the proposition it denotes. -/
def changedAxiom : Environment :=
  { restrictedEnvironment with
    known := [⟨AxiomTag.powerIntro.name, subsetPowerFormula.erase⟩] }

theorem missing_axiom_manifest_rejected :
    proofFrameCheck environment missingAxiom manifest [] subsetPowerProof
      subsetPowerFormula.erase = false := by decide

theorem changed_axiom_manifest_rejected :
    proofFrameCheck environment changedAxiom manifest [] subsetPowerProof
      subsetPowerFormula.erase = false := by decide

private theorem noDefinitions (selected : Environment)
    (terms : selected.terms = [membershipDeclaration, powerDeclaration])
    (name : Name) (declaration : TermDecl)
    (lookup : selected.lookupTerm? name = some declaration) :
    declaration.definition = none := by
  have member := lookupTermList?_mem selected.terms name lookup
  rw [terms] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem missing_axiom_native_rejected :
    checkProof missingAxiom 32 0 [] [] subsetPowerProof
      subsetPowerFormula.erase = false := by
  have inferred : inferProof missingAxiom 32 0 [] [] subsetPowerProof = none := by
    simp [inferProof, subsetPowerProof, missingAxiom, Environment.lookupKnown?, lookupKnownList?]
  unfold checkProof
  split <;> simp [checkNormalizedProof, inferred]

theorem changed_axiom_native_rejected :
    checkProof changedAxiom 32 0 [] [] subsetPowerProof
      subsetPowerFormula.erase = false := by
  have delta := deltaNormalize_of_primitive changedAxiom (noDefinitions changedAxiom rfl)
  have lookup : changedAxiom.lookupKnown? AxiomTag.powerIntro.name =
      some subsetPowerFormula.erase := rfl
  have inferred : inferProof changedAxiom 32 0 [] [] subsetPowerProof = none := by
    simp +decide [inferProof, inferTerm, MathdataKernel.normalize, delta, lookup,
      subsetPowerProof, subsetPowerFormula, Formula.erase, SetTerm.erase,
      Tm.normalize, Tm.normalizeOne, Tm.instantiate]
  unfold checkProof
  split <;> simp [checkNormalizedProof, inferred]

/-! ## Independent intrinsic interpretation of the retained signature -/

open Mettapedia.Logic.HOL HenkinTermInterpretation

abbrev NativeConstant := Constant restrictedEnvironment

def setType : Ty Base := .base (.inr 0)

def membershipConstant : NativeConstant (setType ⇒ setType ⇒ .prop) :=
  .named membershipName membershipDeclaration rfl rfl

def powerConstant : NativeConstant (setType ⇒ setType) :=
  .named powerName powerDeclaration rfl rfl

def member {context : Ctx Base} (left right : Term NativeConstant context setType) :
    Term NativeConstant context .prop :=
  .app (.app (.const membershipConstant) left) right

def power {context : Ctx Base} (value : Term NativeConstant context setType) :
    Term NativeConstant context setType := .app (.const powerConstant) value

def conclusion : Mettapedia.Logic.HOL.ClosedFormula NativeConstant :=
  .all (member (.var .vz) (power (.var .vz)))

def introduction : Mettapedia.Logic.HOL.ClosedFormula NativeConstant :=
  .all (.all (.imp
    (.all (.imp (member (.var .vz) (.var (.vs .vz)))
      (member (.var .vz) (.var (.vs (.vs .vz))))))
    (member (.var .vz) (power (.var (.vs .vz))))))

def elimination : Mettapedia.Logic.HOL.ClosedFormula NativeConstant :=
  .all (.all (.all (.imp
    (member (.var (.vs .vz)) (power (.var (.vs (.vs .vz)))))
    (.imp (member (.var .vz) (.var (.vs .vz)))
      (member (.var .vz) (.var (.vs (.vs .vz))))))))

theorem conclusion_erased : erase conclusion = some subsetPowerFormula.erase := rfl
theorem introduction_erased : erase introduction = some powerIntroFormula.erase := rfl
theorem elimination_erased : erase elimination = some powerElimFormula.erase := rfl

/-- All schematic base symbols share a carrier; the proof uses only base zero. -/
def carrier (α : Type u) : Base → Type (max 1 u) := fun _ => ULift.{1} α

def constantDenotation {α : Type u} (membership : α → α → Prop) (powerset : α → α)
    {type : Ty Base} (constant : NativeConstant type) :
    Ty.denote.{0, u} (carrier α) type := by
  cases constant with
  | primitive index lookup => simp [restrictedEnvironment] at lookup
  | named name declaration lookup typed =>
      simp only [restrictedEnvironment, Environment.lookupTerm?, lookupTermList?,
        membershipDeclaration, powerDeclaration] at lookup
      split at lookup
      · cases lookup
        have typeEq : type = (setType ⇒ setType ⇒ .prop) := reifyType_injective typed.symm
        subst type
        exact fun left right => .up (membership left.down right.down)
      · split at lookup
        · cases lookup
          have typeEq : type = (setType ⇒ setType) := reifyType_injective typed.symm
          subst type
          exact fun value => .up (powerset value.down)
        · cases lookup

def model {α : Type u} (membership : α → α → Prop) (powerset : α → α) :
    HenkinModel.{0, 0, u} Base NativeConstant :=
  HenkinModel.standard (carrier α) (constantDenotation membership powerset)

theorem models_introduction_iff {α : Type u} (membership : α → α → Prop)
    (powerset : α → α) :
    (model membership powerset).models introduction ↔
      ∀ collection candidate, (∀ value, membership value candidate → membership value collection) →
        membership candidate (powerset collection) := by
  simp only [HenkinModel.models, PreModel.models, introduction, member, power,
    PreModel.denote, model, HenkinModel.standard, true_implies]
  change (∀ collection candidate : ULift.{1} α,
    (∀ value : ULift.{1} α, membership value.down candidate.down →
      membership value.down collection.down) → membership candidate.down (powerset collection.down)) ↔ _
  constructor
  · intro holds collection candidate subset
    exact holds (.up collection) (.up candidate) (fun value => subset value.down)
  · intro holds collection candidate subset
    exact holds collection.down candidate.down (fun value => subset (.up value))

theorem models_elimination_iff {α : Type u} (membership : α → α → Prop)
    (powerset : α → α) :
    (model membership powerset).models elimination ↔
      ∀ collection candidate value, membership candidate (powerset collection) →
        membership value candidate → membership value collection := by
  simp only [HenkinModel.models, PreModel.models, elimination, member, power,
    PreModel.denote, model, HenkinModel.standard, true_implies]
  change (∀ collection candidate value : ULift.{1} α,
    membership candidate.down (powerset collection.down) →
      membership value.down candidate.down → membership value.down collection.down) ↔ _
  constructor
  · intro holds collection candidate value
    exact holds (.up collection) (.up candidate) (.up value)
  · intro holds collection candidate value
    exact holds collection.down candidate.down value.down

theorem models_conclusion_iff {α : Type u} (membership : α → α → Prop) (powerset : α → α) :
    (model membership powerset).models conclusion ↔
      ∀ value, membership value (powerset value) := by
  simp only [HenkinModel.models, PreModel.models, conclusion, member, power,
    PreModel.denote, model, HenkinModel.standard, true_implies]
  change (∀ value : ULift.{1} α, membership value.down (powerset value.down)) ↔ _
  constructor
  · intro holds value; exact holds (.up value)
  · intro holds value; exact holds value.down

def checkedDefinitions : CheckedPlainDefinitions restrictedEnvironment where
  body := by
    intro name declaration body lookup defined eligible
    have primitive := noDefinitions restrictedEnvironment rfl name declaration lookup
    rw [primitive] at defined
    cases defined

theorem definitionEquations {α : Type u} (membership : α → α → Prop) (powerset : α → α) :
    DefinitionEquations checkedDefinitions (model membership powerset) where
  equation := by
    intro type name declaration lookup typed body defined
    have primitive := noDefinitions restrictedEnvironment rfl name declaration lookup
    rw [primitive] at defined
    cases defined

theorem knownValidity_iff {α : Type u} (membership : α → α → Prop) (powerset : α → α) :
    NativeProof.KnownValidity (model membership powerset) ↔
      (model membership powerset).models introduction := by
  constructor
  · intro validity
    obtain ⟨formula, erased, holds⟩ := validity AxiomTag.powerIntro.name
      powerIntroFormula.erase rfl
    have same : formula = introduction := erase_injective_of_eq_some erased introduction_erased
    simpa only [same] using holds
  · intro valid name raw lookup
    simp only [restrictedEnvironment, Environment.lookupKnown?, lookupKnownList?] at lookup
    split at lookup
    · cases lookup
      exact ⟨introduction, introduction_erased, valid⟩
    · cases lookup

private theorem plainEnvironment : PlainEnvironment restrictedEnvironment 0 where
  named := by
    intro name declaration lookup
    have member := lookupTermList?_mem restrictedEnvironment.terms name lookup
    simp only [restrictedEnvironment, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  primitive := by
    intro index type lookup
    simp [restrictedEnvironment] at lookup

theorem proof_fragment : NativeProof.Fragment restrictedEnvironment 0 subsetPowerProof := by
  unfold subsetPowerProof
  repeat' first
    | apply NativeProof.Fragment.termLam
    | apply NativeProof.Fragment.proofLam
    | apply NativeProof.Fragment.proofApp
    | apply NativeProof.Fragment.termApp
    | exact NativeProof.Fragment.known _
    | exact NativeProof.Fragment.hyp _
    | exact plainEnvironment.plainLookups (by rfl)
    | rfl

/-- The actual accepted source proof establishes the interpreted theorem under
the one retained axiom, using generic native proof soundness. -/
theorem restricted_native_sound {α : Type u} (membership : α → α → Prop) (powerset : α → α)
    (axiomValid : (model membership powerset).models introduction) :
    (model membership powerset).models conclusion := by
  exact NativeProof.checkProof_sound checkedDefinitions (model membership powerset)
    (definitionEquations membership powerset) ((knownValidity_iff membership powerset).mpr axiomValid)
    (Γ := []) (hypotheses := []) (rawHypotheses := []) proof_fragment rfl
    conclusion conclusion_erased restricted_native_accepted (fun v => nomatch v)
    (by intro type index; nomatch index) (by intro formula member; nomatch member)

/-- The same source proof is sound in the existing ZFC set interpretation.
Only powerset introduction is supplied to the native proof-soundness theorem. -/
theorem restricted_native_valid_zfc :
    (model zfcModel.member zfcModel.power).models conclusion := by
  apply restricted_native_sound
  apply (models_introduction_iff _ _).mpr
  intro collection candidate subset
  exact (zfcModel.power_spec collection candidate).mpr subset

theorem native_zfc_subset_reflexivity (value : ZFSet.{0}) :
    value ∈ ZFSet.powerset value :=
  (models_conclusion_iff zfcModel.member zfcModel.power).mp restricted_native_valid_zfc value

/-! ## Proof-local restriction is not theory conservativity -/

/-- This interpretation satisfies the retained axiom but not the omitted one. -/
theorem omitted_axiom_not_entailed :
    (model (fun _ collection : Bool => collection = true) (fun _ => true)).models introduction ∧
      ¬ (model (fun _ collection : Bool => collection = true) (fun _ => true)).models elimination := by
  constructor
  · apply (models_introduction_iff _ _).mpr
    intro collection candidate subset
    rfl
  · rw [models_elimination_iff]
    intro holds
    have impossible := holds false true false rfl rfl
    cases impossible

theorem restricted_theorem_holds_in_separating_model :
    (model (fun _ collection : Bool => collection = true) (fun _ => true)).models conclusion :=
  restricted_native_sound _ _ omitted_axiom_not_entailed.1

/-- Changing the interpretation of the used axiom does not change syntax
checking. It invalidates the independent semantic premise and the conclusion. -/
theorem used_axiom_semantic_boundary :
    checkProof restrictedEnvironment 32 0 [] [] subsetPowerProof
        subsetPowerFormula.erase = true ∧
      ¬ NativeProof.KnownValidity (model (fun _ _ : Bool => False) id) ∧
      ¬ (model (fun _ _ : Bool => False) id).models conclusion := by
  refine ⟨restricted_native_accepted, ?_, ?_⟩
  · rw [knownValidity_iff, models_introduction_iff]
    intro holds
    exact holds false false (fun _ impossible => impossible)
  · rw [models_conclusion_iff]
    exact fun holds => holds false

#print axioms manifest_accepted
#print axioms native_verdict_restricted
#print axioms restricted_native_accepted
#print axioms omitted_axiom_native_verdict_differs
#print axioms missing_axiom_native_rejected
#print axioms changed_axiom_native_rejected
#print axioms restricted_native_sound
#print axioms restricted_native_valid_zfc
#print axioms native_zfc_subset_reflexivity
#print axioms omitted_axiom_not_entailed
#print axioms restricted_theorem_holds_in_separating_model
#print axioms used_axiom_semantic_boundary

end Mettapedia.Languages.Megalodon.PreambleDependencyRestriction
