import Mathlib.SetTheory.ZFC.Basic
import Mettapedia.Languages.Megalodon.SetCoreSemanticAuthority

/-!
# External semantics for a selected Megalodon set-operation fragment

This module extends the externally interpreted set vocabulary with empty set,
big union, and powerset.  Five introduction/elimination principles are
selected from the shape of the Egal/HOTG preamble:

* elimination from membership in the empty set;
* introduction and impredicative elimination for big union; and
* introduction and elimination for powerset.

Their native certificates are ordinary Megalodon `known` proof terms in one
explicit finite Mathdata environment.  Their meaning is independently defined
as validity in every extensional membership model satisfying the exact empty,
union, and powerset laws.

Mathlib's `ZFSet` supplies a concrete model of the full selected signature, so
the semantics is non-vacuous.  This remains a proper operation fragment: it
does not claim replacement, foundation, choice, Grothendieck universes, or the
full HOTG preamble.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.SelectedTheoryProfile

universe u

/-! ## Intrinsic selected syntax -/

/-- Set terms with the three selected operations. -/
inductive SetTerm (arity : Nat) where
  | var : Fin arity -> SetTerm arity
  | empty : SetTerm arity
  | union : SetTerm arity -> SetTerm arity
  | power : SetTerm arity -> SetTerm arity
deriving DecidableEq, Repr

/-- The proposition fragment needed by the selected operation rules. -/
inductive Formula : Nat -> Type where
  | predicate {arity} : SetTerm arity -> Formula arity
  | member {arity} : SetTerm arity -> SetTerm arity -> Formula arity
  | imp {arity} : Formula arity -> Formula arity -> Formula arity
  | all {arity} : Formula (arity + 1) -> Formula arity
deriving DecidableEq, Repr

abbrev ClosedFormula := Formula 0

/-! ## Independent model semantics -/

/-- Extensional membership models with exact empty, union, and powerset
operations.  The unary predicate remains freely interpreted so the selected
elimination rules cannot obtain soundness from a special predicate choice. -/
structure Model where
  Carrier : Type u
  member : Carrier -> Carrier -> Prop
  empty : Carrier
  union : Carrier -> Carrier
  power : Carrier -> Carrier
  predicate : Carrier -> Prop
  empty_not_member : forall value, Not (member value empty)
  extensional : forall left right,
    (forall value, member value left <-> member value right) -> left = right
  union_spec : forall collection value,
    member value (union collection) <->
      exists memberSet, member memberSet collection /\ member value memberSet
  power_spec : forall collection candidate,
    member candidate (power collection) <->
      forall value, member value candidate -> member value collection

abbrev Assignment (model : Model.{u}) (arity : Nat) :=
  Fin arity -> model.Carrier

def Assignment.extend {model : Model.{u}} {arity : Nat}
    (value : model.Carrier) (assignment : Assignment model arity) :
    Assignment model (arity + 1) :=
  Fin.cases value assignment

def SetTerm.denote {arity : Nat} (model : Model.{u})
    (term : SetTerm arity) (assignment : Assignment model arity) :
    model.Carrier :=
  match term with
  | .var index => assignment index
  | .empty => model.empty
  | .union collection => model.union (collection.denote model assignment)
  | .power collection => model.power (collection.denote model assignment)

def Formula.Holds (model : Model.{u}) : {arity : Nat} ->
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

/-- Validity in every selected operation model. -/
def Valid (formula : ClosedFormula) : Prop :=
  forall model : Model.{1},
    formula.Holds model (fun index => Fin.elim0 index)

/-! ## Five selected preamble-shaped formulas -/

/-- Membership in empty entails any freely interpreted predicate. -/
def emptyElimFormula : ClosedFormula :=
  .all (.imp
    (.member (.var 0) .empty)
    (.predicate (.var 0)))

/-- `x ∈ Y -> Y ∈ X -> x ∈ ⋃X`. -/
def unionIntroFormula : ClosedFormula :=
  .all (.all (.all
    (.imp
      (.member (.var 0) (.var 1))
      (.imp
        (.member (.var 1) (.var 2))
        (.member (.var 0) (.union (.var 2)))))))

/-- Impredicative elimination for `x ∈ ⋃X`, using the freely interpreted
predicate as the conclusion. -/
def unionElimFormula : ClosedFormula :=
  .all (.all
    (.imp
      (.member (.var 0) (.union (.var 1)))
      (.imp
        (.all
          (.imp
            (.member (.var 1) (.var 0))
            (.imp
              (.member (.var 0) (.var 2))
              (.predicate (.var 1)))))
        (.predicate (.var 0)))))

/-- `Y ⊆ X -> Y ∈ Power X`, with subset expanded intensionally. -/
def powerIntroFormula : ClosedFormula :=
  .all (.all
    (.imp
      (.all
        (.imp
          (.member (.var 0) (.var 1))
          (.member (.var 0) (.var 2))))
      (.member (.var 0) (.power (.var 1)))))

/-- `Y ∈ Power X -> z ∈ Y -> z ∈ X`. -/
def powerElimFormula : ClosedFormula :=
  .all (.all (.all
    (.imp
      (.member (.var 1) (.power (.var 2)))
      (.imp
        (.member (.var 0) (.var 1))
        (.member (.var 0) (.var 2))))))

theorem emptyElim_valid : Valid emptyElimFormula := by
  intro model value inEmpty
  exact (model.empty_not_member value inEmpty).elim

theorem unionIntro_valid : Valid unionIntroFormula := by
  intro model collection memberSet value inMemberSet memberSetInCollection
  exact (model.union_spec collection value).mpr
    ⟨memberSet, memberSetInCollection, inMemberSet⟩

theorem unionElim_valid : Valid unionElimFormula := by
  intro model collection value inUnion eliminate
  obtain ⟨memberSet, memberSetInCollection, inMemberSet⟩ :=
    (model.union_spec collection value).mp inUnion
  exact eliminate memberSet inMemberSet memberSetInCollection

theorem powerIntro_valid : Valid powerIntroFormula := by
  intro model collection candidate subset
  exact (model.power_spec collection candidate).mpr subset

theorem powerElim_valid : Valid powerElimFormula := by
  intro model collection candidate value candidateInPower valueInCandidate
  exact (model.power_spec collection candidate).mp candidateInPower
    value valueInCandidate

/-! ## A concrete non-vacuity model -/

/-- Mathlib's extensional ZFC sets instantiate all selected operation laws. -/
noncomputable def zfcModel : Model.{1} where
  Carrier := ZFSet.{0}
  member := fun left right => left ∈ right
  empty := ∅
  union := ZFSet.sUnion
  power := ZFSet.powerset
  predicate := fun _ => False
  empty_not_member := ZFSet.notMem_empty
  extensional := by
    intro left right pointwise
    exact ZFSet.ext pointwise
  union_spec := by
    intro collection value
    exact ZFSet.mem_sUnion
  power_spec := by
    intro collection candidate
    exact ZFSet.mem_powerset

/-- The concrete model is not a degenerate one-point interpretation: the
powerset of empty is distinct from empty. -/
theorem zfc_empty_ne_power_empty :
    zfcModel.empty ≠ zfcModel.power zfcModel.empty := by
  intro equality
  change (∅ : ZFSet.{0}) = ZFSet.powerset (∅ : ZFSet.{0}) at equality
  have emptyInPower :
      (∅ : ZFSet.{0}) ∈ ZFSet.powerset (∅ : ZFSet.{0}) :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← equality] at emptyInPower
  exact ZFSet.notMem_empty _ emptyInPower

/-- The sentence claiming universal membership. -/
def universalMembership : ClosedFormula :=
  .all (.all (.member (.var 1) (.var 0)))

/-- The concrete ZFC model refutes universal membership. -/
theorem universalMembership_not_valid : Not (Valid universalMembership) := by
  intro valid
  have impossible := valid zfcModel (∅ : ZFSet) (∅ : ZFSet)
  exact ZFSet.notMem_empty _ impossible

/-! ## Exact erasure to the live Mathdata syntax -/

def predicateName : Name := "P"
def membershipName : Name := "In"
def emptyName : Name := "Empty"
def unionName : Name := "Union"
def powerName : Name := "Power"

def predicateDeclaration : TermDecl where
  name := predicateName
  type := .arr (.base 0) .prop

def membershipDeclaration : TermDecl where
  name := membershipName
  type := .arr (.base 0) (.arr (.base 0) .prop)

def emptyDeclaration : TermDecl where
  name := emptyName
  type := .base 0

def unionDeclaration : TermDecl where
  name := unionName
  type := .arr (.base 0) (.base 0)

def powerDeclaration : TermDecl where
  name := powerName
  type := .arr (.base 0) (.base 0)

def SetTerm.erase {arity : Nat} : SetTerm arity -> Tm
  | .var index => .db index.val
  | .empty => .named emptyName
  | .union collection => .app (.named unionName) collection.erase
  | .power collection => .app (.named powerName) collection.erase

def Formula.erase : {arity : Nat} -> Formula arity -> Tm
  | _, .predicate term => .app (.named predicateName) term.erase
  | _, .member left right =>
      .app (.app (.named membershipName) left.erase) right.erase
  | _, .imp domain codomain => .imp domain.erase codomain.erase
  | _, .all body => .all (.base 0) body.erase

/-! ## Selected native propositions and environment -/

inductive AxiomTag where
  | emptyElim
  | unionIntro
  | unionElim
  | powerIntro
  | powerElim
deriving DecidableEq, Repr, Fintype

def AxiomTag.formula : AxiomTag -> ClosedFormula
  | .emptyElim => emptyElimFormula
  | .unionIntro => unionIntroFormula
  | .unionElim => unionElimFormula
  | .powerIntro => powerIntroFormula
  | .powerElim => powerElimFormula

def AxiomTag.name : AxiomTag -> Name
  | .emptyElim => "EmptyE"
  | .unionIntro => "UnionI"
  | .unionElim => "UnionE_impred"
  | .powerIntro => "PowerI"
  | .powerElim => "PowerE"

def AxiomTag.knownDeclaration (tag : AxiomTag) : KnownDecl where
  name := tag.name
  proposition := tag.formula.erase

/-- The selected finite Mathdata environment.  Known propositions are
authored assumptions of this profile; their independent soundness is proved
above rather than inferred from lookup. -/
def environment : Environment where
  terms := [predicateDeclaration, membershipDeclaration, emptyDeclaration,
    unionDeclaration, powerDeclaration]
  known := [AxiomTag.emptyElim.knownDeclaration,
    AxiomTag.unionIntro.knownDeclaration,
    AxiomTag.unionElim.knownDeclaration,
    AxiomTag.powerIntro.knownDeclaration,
    AxiomTag.powerElim.knownDeclaration]

@[simp] theorem environment_lookup_predicate :
    environment.lookupTerm? predicateName = some predicateDeclaration := by
  rfl

@[simp] theorem environment_lookup_membership :
    environment.lookupTerm? membershipName = some membershipDeclaration := by
  rfl

@[simp] theorem environment_lookup_empty :
    environment.lookupTerm? emptyName = some emptyDeclaration := by
  rfl

@[simp] theorem environment_lookup_union :
    environment.lookupTerm? unionName = some unionDeclaration := by
  rfl

@[simp] theorem environment_lookup_power :
    environment.lookupTerm? powerName = some powerDeclaration := by
  rfl

@[simp] theorem environment_lookup_known (tag : AxiomTag) :
    environment.lookupKnown? tag.name = some tag.formula.erase := by
  cases tag <;> rfl

def setContext (arity : Nat) : List Tp :=
  List.replicate arity (.base 0)

@[simp] theorem SetTerm.infer_erase {arity : Nat}
    (term : SetTerm arity) :
    inferTerm environment 0 (setContext arity) term.erase =
      some (.base 0) := by
  induction term with
  | var index =>
      simp [SetTerm.erase, inferTerm, setContext, index.isLt]
  | empty =>
      simp [SetTerm.erase, inferTerm, emptyDeclaration]
  | union collection inductionHypothesis =>
      simp [SetTerm.erase, inferTerm, unionDeclaration,
        inductionHypothesis]
  | power collection inductionHypothesis =>
      simp [SetTerm.erase, inferTerm, powerDeclaration,
        inductionHypothesis]

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
  induction term with
  | var index =>
      cases fuel <;> simp [SetTerm.erase, deltaNormalize]
  | empty =>
      cases fuel <;> simp [SetTerm.erase, deltaNormalize, emptyDeclaration]
  | union collection inductionHypothesis =>
      cases fuel <;>
        simp [SetTerm.erase, deltaNormalize, unionDeclaration,
          inductionHypothesis]
  | power collection inductionHypothesis =>
      cases fuel <;>
        simp [SetTerm.erase, deltaNormalize, powerDeclaration,
          inductionHypothesis]

@[simp] theorem Formula.deltaNormalize_erase {arity : Nat}
    (formula : Formula arity) (fuel : Nat) :
    deltaNormalize environment fuel formula.erase = some formula.erase := by
  induction formula with
  | predicate term =>
      cases fuel <;>
        simp [Formula.erase, deltaNormalize, predicateDeclaration]
  | member left right =>
      cases fuel <;>
        simp [Formula.erase, deltaNormalize, membershipDeclaration]
  | imp domain codomain domainIH codomainIH =>
      cases fuel <;>
        simp [Formula.erase, deltaNormalize, domainIH, codomainIH]
  | all body bodyIH =>
      cases fuel <;> simp [Formula.erase, deltaNormalize, bodyIH]

@[simp] theorem SetTerm.normalizeOne_erase {arity : Nat}
    (term : SetTerm arity) :
    Tm.normalizeOne term.erase = (term.erase, true) := by
  induction term with
  | var index => rfl
  | empty => rfl
  | union collection inductionHypothesis =>
      simp [SetTerm.erase, Tm.normalizeOne, inductionHypothesis]
  | power collection inductionHypothesis =>
      simp [SetTerm.erase, Tm.normalizeOne, inductionHypothesis]

@[simp] theorem Formula.normalizeOne_erase {arity : Nat}
    (formula : Formula arity) :
    Tm.normalizeOne formula.erase = (formula.erase, true) := by
  induction formula with
  | predicate term =>
      simp [Formula.erase, Tm.normalizeOne]
  | member left right =>
      simp [Formula.erase, Tm.normalizeOne]
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

def profileClaim (formula : ClosedFormula) : ProfileClaim where
  fuel := 32
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := formula.erase

def AxiomTag.proof (tag : AxiomTag) : Pf :=
  .known tag.name

theorem AxiomTag.native_accepted (tag : AxiomTag) :
    (SelectedTheoryProfile.checker environment).check
      (profileClaim tag.formula) tag.proof = true := by
  change checkProof environment 32 0 [] []
    tag.proof tag.formula.erase = true
  unfold checkProof
  rw [Formula.mathdataNormalize_erase]
  simp [checkNormalizedProof, inferProof, AxiomTag.proof]

/-! ## Qualified authority -/

/-- Exactly the five selected operation rules. -/
def Covered (formula : ClosedFormula) : Prop :=
  exists tag : AxiomTag, formula = tag.formula

instance coveredDecidable (formula : ClosedFormula) :
    Decidable (Covered formula) := by
  unfold Covered
  exact Fintype.decidableExistsFintype

def covered? (formula : ClosedFormula) : Bool :=
  decide (Covered formula)

@[simp] theorem covered?_eq_true_iff (formula : ClosedFormula) :
    covered? formula = true <-> Covered formula := by
  exact decide_eq_true_iff

theorem covered_valid {formula : ClosedFormula}
    (covered : Covered formula) : Valid formula := by
  rcases covered with ⟨tag, rfl⟩
  cases tag with
  | emptyElim => exact emptyElim_valid
  | unionIntro => exact unionIntro_valid
  | unionElim => exact unionElim_valid
  | powerIntro => exact powerIntro_valid
  | powerElim => exact powerElim_valid

def checker : Checker ClosedFormula Pf where
  check formula proof :=
    if covered? formula then
      (SelectedTheoryProfile.checker environment).check
        (profileClaim formula) proof
    else false

theorem AxiomTag.covered (tag : AxiomTag) : Covered tag.formula :=
  ⟨tag, rfl⟩

@[simp] theorem AxiomTag.covered?_eq_true (tag : AxiomTag) :
    covered? tag.formula = true :=
  (covered?_eq_true_iff tag.formula).mpr tag.covered

theorem AxiomTag.checker_accepted (tag : AxiomTag) :
    checker.check tag.formula tag.proof = true := by
  change (if covered? tag.formula then
      (SelectedTheoryProfile.checker environment).check
        (profileClaim tag.formula) tag.proof
    else false) = true
  simp only [tag.covered?_eq_true, if_true]
  exact tag.native_accepted

theorem checker_authority : checker.Authority Covered where
  sound := by
    intro formula proof accepted
    change (if covered? formula then
        (SelectedTheoryProfile.checker environment).check
          (profileClaim formula) proof
      else false) = true at accepted
    cases coverage : covered? formula with
    | false => simp [coverage] at accepted
    | true => exact (covered?_eq_true_iff formula).mp coverage
  complete := by
    intro formula covered
    rcases covered with ⟨tag, rfl⟩
    exact ⟨tag.proof, tag.checker_accepted⟩

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

/-! ## Semantic gap and discriminating controls -/

def predicateFormula : ClosedFormula :=
  .all (.predicate (.var 0))

def identityFormula : ClosedFormula :=
  .imp predicateFormula predicateFormula

theorem identity_valid : Valid identityFormula := by
  intro model predicateHolds
  exact predicateHolds

theorem identity_not_covered : Not (Covered identityFormula) := by
  rintro ⟨tag, equality⟩
  cases tag <;> cases equality

theorem qualification_not_conservative :
    Not (forall formula, Valid formula -> Covered formula) := by
  intro completeness
  exact identity_not_covered (completeness identityFormula identity_valid)

namespace Canary

theorem emptyElim_replays :
    (contract.checker ()).check emptyElimFormula
      AxiomTag.emptyElim.proof = true := by
  exact AxiomTag.emptyElim.checker_accepted

theorem unionIntro_replays :
    (contract.checker ()).check unionIntroFormula
      AxiomTag.unionIntro.proof = true := by
  exact AxiomTag.unionIntro.checker_accepted

theorem unionElim_replays :
    (contract.checker ()).check unionElimFormula
      AxiomTag.unionElim.proof = true := by
  exact AxiomTag.unionElim.checker_accepted

theorem powerIntro_replays :
    (contract.checker ()).check powerIntroFormula
      AxiomTag.powerIntro.proof = true := by
  exact AxiomTag.powerIntro.checker_accepted

theorem powerElim_replays :
    (contract.checker ()).check powerElimFormula
      AxiomTag.powerElim.proof = true := by
  exact AxiomTag.powerElim.checker_accepted

theorem universalMembership_not_covered :
    Not (Covered universalMembership) := by
  rintro ⟨tag, equality⟩
  cases tag <;> cases equality

theorem universalMembership_rejected (proof : Pf) :
    (contract.checker ()).check universalMembership proof = false := by
  change checker.check universalMembership proof = false
  have coverage : covered? universalMembership = false := by
    apply Bool.eq_false_of_not_eq_true
    intro accepted
    exact universalMembership_not_covered
      ((covered?_eq_true_iff universalMembership).mp accepted)
  simp only [checker, coverage, Bool.false_eq_true, if_false]

@[simp] theorem environment_lookup_unknown :
    environment.lookupKnown? "not-in-selected-operation-environment" = none := by
  rfl

theorem unknown_known_rejected (tag : AxiomTag) :
    (contract.checker ()).check tag.formula
      (.known "not-in-selected-operation-environment") = false := by
  change checker.check tag.formula
    (.known "not-in-selected-operation-environment") = false
  change (if covered? tag.formula then
      (SelectedTheoryProfile.checker environment).check
        (profileClaim tag.formula)
        (.known "not-in-selected-operation-environment")
    else false) = false
  simp only [tag.covered?_eq_true, if_true]
  change checkProof environment 32 0 [] []
    (.known "not-in-selected-operation-environment") tag.formula.erase = false
  unfold checkProof
  rw [Formula.mathdataNormalize_erase]
  simp [checkNormalizedProof, inferProof]

/-- A certificate for one loaded operation proposition cannot be replayed at
a different selected proposition. -/
theorem empty_certificate_rejected_at_unionIntro :
    (contract.checker ()).check unionIntroFormula
      AxiomTag.emptyElim.proof = false := by
  change checker.check unionIntroFormula AxiomTag.emptyElim.proof = false
  change (if covered? unionIntroFormula then
      (SelectedTheoryProfile.checker environment).check
        (profileClaim unionIntroFormula) AxiomTag.emptyElim.proof
    else false) = false
  have coverage : covered? unionIntroFormula = true :=
    (covered?_eq_true_iff unionIntroFormula).mpr ⟨.unionIntro, rfl⟩
  simp only [coverage, if_true]
  change checkProof environment 32 0 [] []
    AxiomTag.emptyElim.proof unionIntroFormula.erase = false
  unfold checkProof
  rw [Formula.mathdataNormalize_erase]
  simp [checkNormalizedProof, inferProof, AxiomTag.proof,
    Formula.mathdataNormalize_erase]
  decide

end Canary

#print axioms emptyElim_valid
#print axioms unionIntro_valid
#print axioms unionElim_valid
#print axioms powerIntro_valid
#print axioms powerElim_valid
#print axioms zfcModel
#print axioms zfc_empty_ne_power_empty
#print axioms universalMembership_not_valid
#print axioms Formula.infer_erase
#print axioms Formula.mathdataNormalize_erase
#print axioms AxiomTag.native_accepted
#print axioms covered_valid
#print axioms checker_authority
#print axioms identity_valid
#print axioms identity_not_covered
#print axioms qualification_not_conservative
#print axioms Canary.emptyElim_replays
#print axioms Canary.unionIntro_replays
#print axioms Canary.unionElim_replays
#print axioms Canary.powerIntro_replays
#print axioms Canary.powerElim_replays
#print axioms Canary.universalMembership_rejected
#print axioms Canary.unknown_known_rejected
#print axioms Canary.empty_certificate_rejected_at_unionIntro

end Mettapedia.Languages.Megalodon.SetOperationSemanticAuthority
