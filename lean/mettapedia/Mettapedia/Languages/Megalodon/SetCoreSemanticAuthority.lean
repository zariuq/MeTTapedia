import Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-!
# External set-core semantics for a selected Megalodon profile

This module gives a small, honest model-semantic profile over Megalodon's live
Mathdata checker.  Its formulas contain a unary predicate, membership,
implication, and quantification over the selected `set` base type.  Meaning is
validity in every extensional membership model with an empty set; it is not
defined by native proof acceptance.

The covered native scope is the reflexive-implication fragment.  A structural
coverage test guards the selected Mathdata checker, and every covered formula
is compiled to Megalodon's ordinary implication-introduction proof term.  A
universal-membership sentence supplies both an outside-coverage control and a
genuine external countermodel.

This is a semantic profile for a proper set-theoretic fragment, not a model of
the full Egal/HOTG preamble.  Extending coverage or the model signature must
add the corresponding native-compilation and model-soundness proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.NIKNativeProof
open Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-! ## Intrinsic set-core formulas -/

/-- Set terms in the selected fragment are de Bruijn variables. -/
inductive SetTerm (arity : Nat) where
  | var : Fin arity -> SetTerm arity
deriving DecidableEq, Repr

/-- A typed set-core formula.  `all` introduces the newest set variable. -/
inductive Formula : Nat -> Type where
  | predicate {arity} : SetTerm arity -> Formula arity
  | member {arity} : SetTerm arity -> SetTerm arity -> Formula arity
  | imp {arity} : Formula arity -> Formula arity -> Formula arity
  | all {arity} : Formula (arity + 1) -> Formula arity
deriving DecidableEq, Repr

abbrev ClosedFormula := Formula 0

/-! ## Independent extensional set semantics -/

/-- The exact model signature used by this experiment: membership,
extensionality, an empty set, and one freely interpreted unary predicate.
Every ordinary HOTG model has such a reduct, but this structure deliberately
does not claim the remaining HOTG axioms. -/
structure Model where
  Carrier : Type
  member : Carrier -> Carrier -> Prop
  empty : Carrier
  predicate : Carrier -> Prop
  empty_not_member : forall value, Not (member value empty)
  extensional : forall left right,
    (forall value, member value left <-> member value right) -> left = right

abbrev Assignment (model : Model) (arity : Nat) :=
  Fin arity -> model.Carrier

/-- Extend an assignment by its newest bound set. -/
def Assignment.extend {model : Model} {arity : Nat}
    (value : model.Carrier) (assignment : Assignment model arity) :
    Assignment model (arity + 1) :=
  Fin.cases value assignment

def SetTerm.denote {arity : Nat} (model : Model)
    (term : SetTerm arity) (assignment : Assignment model arity) :
    model.Carrier :=
  match term with
  | .var index => assignment index

def Formula.Holds (model : Model) : {arity : Nat} ->
    Formula arity -> Assignment model arity -> Prop
  | _, .predicate term, assignment =>
      model.predicate (term.denote model assignment)
  | _, .member left right, assignment =>
      model.member (left.denote model assignment)
        (right.denote model assignment)
  | _, .imp domain codomain, assignment =>
      domain.Holds model assignment -> codomain.Holds model assignment
  | _, .all body, assignment =>
      forall value, body.Holds model (Assignment.extend value assignment)

/-- Closed model validity, independently of native theoremhood. -/
def Valid (formula : ClosedFormula) : Prop :=
  forall model : Model,
    formula.Holds model (fun index => Fin.elim0 index)

/-- Reflexive implications are valid in every selected set model. -/
theorem reflexive_valid (body : ClosedFormula) :
    Valid (.imp body body) := by
  intro model bodyHolds
  exact bodyHolds

/-! ## A concrete countermodel -/

/-- The one-point empty-membership model is extensional and has an empty set. -/
def emptyMembershipModel : Model where
  Carrier := Unit
  member := fun _ _ => False
  empty := ()
  predicate := fun _ => False
  empty_not_member := by
    intro value memberEvidence
    exact memberEvidence
  extensional := by
    intro left right _pointwise
    exact Subsingleton.elim left right

/-- The sentence saying every set belongs to every set. -/
def universalMembership : ClosedFormula :=
  .all (.all (.member (.var 1) (.var 0)))

/-- Empty membership is a genuine countermodel to universal membership. -/
theorem universalMembership_not_valid : Not (Valid universalMembership) := by
  intro valid
  have impossible := valid emptyMembershipModel () ()
  exact impossible

/-! ## Erasure to live Mathdata syntax -/

def predicateName : Name := "P"
def membershipName : Name := "In"

/-- The unary predicate declaration used by the selected profile. -/
def predicateDeclaration : TermDecl where
  name := predicateName
  type := .arr (.base 0) .prop

/-- The binary membership declaration used by the selected profile. -/
def membershipDeclaration : TermDecl where
  name := membershipName
  type := .arr (.base 0) (.arr (.base 0) .prop)

/-- The fixed selected Mathdata environment for this semantic fragment. -/
def environment : Environment where
  terms := [predicateDeclaration, membershipDeclaration]

@[simp] theorem environment_lookup_predicate :
    environment.lookupTerm? predicateName =
      some predicateDeclaration := by
  rfl

@[simp] theorem environment_lookup_membership :
    environment.lookupTerm? membershipName =
      some membershipDeclaration := by
  rfl

@[simp] theorem environment_lookupKnown (name : Name) :
    environment.lookupKnown? name = none := by
  rfl

def setContext (arity : Nat) : List Tp :=
  List.replicate arity (.base 0)

def SetTerm.erase {arity : Nat} : SetTerm arity -> Tm
  | .var index => .db index.val

def Formula.erase : {arity : Nat} -> Formula arity -> Tm
  | _, .predicate term => .app (.named predicateName) term.erase
  | _, .member left right =>
      .app (.app (.named membershipName) left.erase) right.erase
  | _, .imp domain codomain => .imp domain.erase codomain.erase
  | _, .all body => .all (.base 0) body.erase

@[simp] theorem SetTerm.infer_erase {arity : Nat}
    (term : SetTerm arity) :
    inferTerm environment 0 (setContext arity) term.erase =
      some (.base 0) := by
  cases term with
  | var index =>
      simp [SetTerm.erase, inferTerm, setContext, index.isLt]

@[simp] theorem Formula.infer_erase {arity : Nat}
    (formula : Formula arity) :
    inferTerm environment 0 (setContext arity) formula.erase = some .prop := by
  induction formula with
  | predicate term =>
      simp [Formula.erase, inferTerm, predicateDeclaration]
  | member left right =>
      simp [Formula.erase, inferTerm, membershipDeclaration]
  | imp domain codomain domainIH codomainIH =>
      simp [Formula.erase, inferTerm, domainIH, codomainIH]
  | @all arity body bodyIH =>
      have contextEquality :
          setContext (arity + 1) = .base 0 :: setContext arity := by
        simp [setContext, List.replicate_succ]
      rw [contextEquality] at bodyIH
      simp [Formula.erase, inferTerm, Tp.plainWellFormed, bodyIH]

@[simp] theorem Formula.checkProposition_erase {arity : Nat}
    (formula : Formula arity) :
    checkProposition environment 0 (setContext arity) formula.erase = true := by
  have typed := Formula.infer_erase formula
  cases formula <;>
    simp only [Formula.erase, checkProposition] <;>
    exact decide_eq_true typed

@[simp] theorem SetTerm.deltaNormalize_erase {arity : Nat}
    (term : SetTerm arity) (fuel : Nat) :
    deltaNormalize environment fuel term.erase = some term.erase := by
  cases term
  cases fuel <;> simp [SetTerm.erase, deltaNormalize]

@[simp] theorem deltaNormalize_predicateName (fuel : Nat) :
    deltaNormalize environment fuel (.named predicateName) =
      some (.named predicateName) := by
  cases fuel <;> simp [deltaNormalize, predicateDeclaration]

@[simp] theorem deltaNormalize_membershipName (fuel : Nat) :
    deltaNormalize environment fuel (.named membershipName) =
      some (.named membershipName) := by
  cases fuel <;> simp [deltaNormalize, membershipDeclaration]

@[simp] theorem Formula.deltaNormalize_erase {arity : Nat}
    (formula : Formula arity) (fuel : Nat) :
    deltaNormalize environment fuel formula.erase = some formula.erase := by
  induction formula with
  | predicate term =>
      simp [Formula.erase, deltaNormalize]
  | member left right =>
      simp [Formula.erase, deltaNormalize]
  | imp domain codomain domainIH codomainIH =>
      simp [Formula.erase, deltaNormalize, domainIH, codomainIH]
  | all body bodyIH =>
      simp [Formula.erase, deltaNormalize, bodyIH]

@[simp] theorem SetTerm.normalizeOne_erase {arity : Nat}
    (term : SetTerm arity) :
    Tm.normalizeOne term.erase = (term.erase, true) := by
  cases term
  rfl

@[simp] theorem Formula.normalizeOne_erase {arity : Nat}
    (formula : Formula arity) :
    Tm.normalizeOne formula.erase = (formula.erase, true) := by
  induction formula with
  | predicate term =>
      cases term
      simp [Formula.erase, SetTerm.erase, Tm.normalizeOne]
  | member left right =>
      cases left
      cases right
      simp [Formula.erase, SetTerm.erase, Tm.normalizeOne]
  | imp domain codomain domainIH codomainIH =>
      simp [Formula.erase, Tm.normalizeOne, domainIH, codomainIH]
  | all body bodyIH =>
      simp [Formula.erase, Tm.normalizeOne, bodyIH]

@[simp] theorem Formula.tmNormalize_erase {arity : Nat}
    (formula : Formula arity) (fuel : Nat) :
    Tm.normalize fuel formula.erase = some formula.erase := by
  cases fuel <;> simp [Tm.normalize]

@[simp] theorem Formula.mathdataNormalize_erase {arity : Nat}
    (formula : Formula arity) (fuel : Nat) :
    MathdataKernel.normalize environment fuel formula.erase =
      some formula.erase := by
  simp [MathdataKernel.normalize]

/-! ## Selected native realization -/

def profileClaim (formula : ClosedFormula) : ProfileClaim where
  fuel := 16
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := formula.erase

/-- Structural native coverage: exactly reflexive implications. -/
def Covered (formula : ClosedFormula) : Prop :=
  exists body : ClosedFormula, formula = .imp body body

def covered? : ClosedFormula -> Bool
  | .imp left right => decide (left = right)
  | _ => false

@[simp] theorem covered?_eq_true_iff (formula : ClosedFormula) :
    covered? formula = true <-> Covered formula := by
  cases formula with
  | predicate term => simp [covered?, Covered]
  | member left right => simp [covered?, Covered]
  | imp left right =>
      constructor
      · intro equalDecision
        have equal : left = right := by
          simpa [covered?] using equalDecision
        subst left
        exact ⟨right, rfl⟩
      · rintro ⟨body, equality⟩
        cases equality
        simp [covered?]
  | all body => simp [covered?, Covered]

/-- The ordinary Mathdata implication-introduction certificate. -/
def reflexiveProof (body : ClosedFormula) : Pf :=
  .proofLam body.erase (.hyp 0)

theorem reflexive_native_accepted (body : ClosedFormula) :
    (SelectedTheoryProfile.checker environment).check
      (profileClaim (.imp body body)) (reflexiveProof body) = true := by
  change checkProof environment 16 0 [] []
    (reflexiveProof body) (Formula.erase (.imp body body)) = true
  unfold checkProof
  rw [Formula.mathdataNormalize_erase]
  have bodyType : inferTerm environment 0 [] body.erase = some .prop := by
    simpa [setContext] using Formula.infer_erase body
  simp [checkNormalizedProof, reflexiveProof, inferProof,
    Formula.erase, bodyType]

/-- Every covered semantic claim has a concrete witness in the live selected
Mathdata theorem scope. -/
theorem covered_has_native_witness {formula : ClosedFormula}
    (covered : Covered formula) :
    NativeTheoremScope environment (profileClaim formula) := by
  rcases covered with ⟨body, rfl⟩
  refine ⟨reflexiveProof body, ?_⟩
  exact (nativeKernel.correct
    (attach environment (profileClaim (.imp body body)))
    (reflexiveProof body)).mp (reflexive_native_accepted body)

/-- Covered formulas have independent model-theoretic meaning. -/
theorem covered_valid {formula : ClosedFormula}
    (covered : Covered formula) : Valid formula := by
  rcases covered with ⟨body, rfl⟩
  exact reflexive_valid body

/-- The selected checker is guarded by the independently declared semantic
coverage boundary. -/
def checker : Checker ClosedFormula Pf where
  check formula proof :=
    if covered? formula then
      (SelectedTheoryProfile.checker environment).check
        (profileClaim formula) proof
    else false

/-- Exact checker authority for the covered set-core scope. -/
theorem checker_authority : checker.Authority Covered where
  sound := by
    intro formula proof accepted
    change (if covered? formula then
        (SelectedTheoryProfile.checker environment).check
          (profileClaim formula) proof
      else false) = true at accepted
    cases coveredDecision : covered? formula with
    | false => simp [coveredDecision] at accepted
    | true => exact (covered?_eq_true_iff formula).mp coveredDecision
  complete := by
    intro formula covered
    rcases covered with ⟨body, rfl⟩
    refine ⟨reflexiveProof body, ?_⟩
    change (if covered? (.imp body body) then
        (SelectedTheoryProfile.checker environment).check
          (profileClaim (.imp body body)) (reflexiveProof body)
      else false) = true
    simp [covered?, reflexive_native_accepted]

/-- The external model-semantic theory for this one selected environment. -/
def theory : TheoryFamily Unit where
  Signature := Environment
  signatureOf := fun _ => environment
  Claim := fun _ => ClosedFormula
  Scope := fun _ => Covered
  Meaning := fun _ => Valid
  scope_sound := by
    intro _kind formula covered
    exact covered_valid covered

def contract : AuthorityContract theory where
  Certificate := fun _ => Pf
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

/-! ## Positive, reflection, and countermodel controls -/

def predicateFormula : ClosedFormula :=
  .all (.predicate (.var 0))

def identityFormula : ClosedFormula :=
  .imp predicateFormula predicateFormula

theorem identity_replays :
    (contract.checker ()).check identityFormula
      (reflexiveProof predicateFormula) = true := by
  exact reflexive_native_accepted predicateFormula

theorem identity_has_external_meaning :
    theory.Meaning () identityFormula := by
  exact reflexive_valid predicateFormula

theorem selected_checker_agrees_on_covered
    {formula : ClosedFormula} (covered : Covered formula) (proof : Pf) :
    (contract.checker ()).check formula proof =
      (SelectedTheoryProfile.checker environment).check
        (profileClaim formula) proof := by
  have coveredDecision : covered? formula = true :=
    (covered?_eq_true_iff formula).mpr covered
  simp [contract, checker, coveredDecision]

theorem missing_known_rejected :
    (contract.checker ()).check identityFormula
      (.known "not-in-selected-environment") = false := by
  have covered : Covered identityFormula := ⟨predicateFormula, rfl⟩
  rw [selected_checker_agrees_on_covered covered]
  change checkProof environment 16 0 [] []
    (.known "not-in-selected-environment") identityFormula.erase = false
  unfold checkProof
  rw [Formula.mathdataNormalize_erase]
  simp [checkNormalizedProof, inferProof]

theorem universalMembership_not_covered : Not (Covered universalMembership) := by
  rintro ⟨body, equality⟩
  cases equality

theorem universalMembership_rejected (proof : Pf) :
    (contract.checker ()).check universalMembership proof = false := by
  simp [contract, checker, universalMembership, covered?]

theorem accepted_has_external_meaning
    (formula : ClosedFormula) (proof : Pf)
    (accepted : (contract.checker ()).check formula proof = true) :
    theory.Meaning () formula :=
  (contract.projection ()).sound formula proof accepted

/-! ## Axiom audit -/

#print axioms reflexive_valid
#print axioms universalMembership_not_valid
#print axioms Formula.infer_erase
#print axioms Formula.mathdataNormalize_erase
#print axioms reflexive_native_accepted
#print axioms covered_has_native_witness
#print axioms checker_authority
#print axioms identity_replays
#print axioms identity_has_external_meaning
#print axioms missing_known_rejected
#print axioms universalMembership_rejected
#print axioms accepted_has_external_meaning

end Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority
