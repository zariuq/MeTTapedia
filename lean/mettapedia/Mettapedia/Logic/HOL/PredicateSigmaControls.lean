import Mettapedia.Logic.HOL.PredicateSigmaInterpretation
import Mettapedia.Logic.HOL.EqualityWitness

/-!
# A concrete fixed evidence carrier with guarded-pair controls

Tree evidence and natural index endpoints have distinct HOL carriers. Pair
projection laws hold in the actual model; the reflexivity leaf is outside
the pair image. This selected tagged model tests the stronger guard without
requiring tags of every representation. Source identity interpretation and
native implementation refinement are not asserted by these controls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateSigma.Controls

inductive Base where
  | index | evidence
  deriving DecidableEq, Repr

abbrev E : Ty Base := .base .evidence
abbrev N : Ty Base := .base .index

inductive Evidence where
  | refl | pair (first second : Evidence)
  deriving DecidableEq, Repr

def Evidence.first : Evidence → Evidence
  | .refl => .refl
  | .pair first _ => first
def Evidence.second : Evidence → Evidence
  | .refl => .refl
  | .pair _ second => second

inductive Const : Ty Base → Type where
  | pair : Const (E ⇒ E ⇒ E)
  | first : Const (E ⇒ E)
  | second : Const (E ⇒ E)
  | refl : Const E
  | zero : Const N
  | one : Const N
  deriving DecidableEq

def carrier : Base → Type 1
  | .index => ULift.{1} Nat
  | .evidence => ULift.{1} Evidence

def constants : {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
  | _, .pair => fun first second => ULift.up (.pair first.down second.down)
  | _, .first => fun point => ULift.up point.down.first
  | _, .second => fun point => ULift.up point.down.second
  | _, .refl => ULift.up .refl
  | _, .zero => ULift.up 0
  | _, .one => ULift.up 1

def model : HenkinModel.{0,0,0} Base Const := HenkinModel.standard carrier constants

def operations : Operations Const E where
  pair := .const .pair
  first := .const .first
  second := .const .second

theorem first_law : model.models (firstLaw operations) := by
  rw [firstLaw_denote]
  intro head _ tail _
  cases head
  cases tail
  rfl

theorem second_law : model.models (secondLaw operations) := by
  rw [secondLaw_denote]
  intro head _ tail _
  cases head
  cases tail
  rfl

def domain : ClosedTerm Const (E ⇒ .prop) := PredicateProducts.full E
def family : ClosedTerm Const (E ⇒ E ⇒ .prop) := .lam (.lam .top)

theorem pair_admitted (head tail : Evidence) :
    (model.denote (sigma operations domain family) (emptyValues model) (ULift.up (.pair head tail))).down := by
  rw [sigma_apply_denote_base model operations first_law second_law]
  exact ⟨ULift.up head, ULift.up tail, rfl, True.intro, True.intro⟩

theorem reflexivity_not_pair :
    ¬ (model.denote (sigma operations domain family) (emptyValues model) (ULift.up .refl)).down := by
  rw [sigma_apply_denote_base model operations first_law second_law]
  rintro ⟨head, tail, same, _, _⟩
  have impossible := congrArg ULift.down same
  cases impossible

def projectionOnly (point : ClosedTerm Const E) : ClosedFormula Const :=
  .and (.app domain (first operations point)) (familyAt family (first operations point) (second operations point))

theorem projection_only_admits_reflexivity : model.models (projectionOnly (.const .refl)) :=
  And.intro True.intro True.intro

theorem empty_domain_refused (value : Evidence) :
    ¬ (model.denote (sigma operations (.lam .bot) family) (emptyValues model) (ULift.up value)).down := by
  rw [sigma_apply_denote_base model operations first_law second_law]
  rintro ⟨_, _, _, impossible, _⟩
  exact impossible

theorem distinct_endpoint_carrier : N ≠ E := by decide +kernel

def equalityAtZero : ClosedTerm Const (E ⇒ .prop) :=
  EqualityWitness.predicate (.const .refl) (.const .zero) (.const .zero)

theorem equal_endpoint_admitted :
    (model.denote (.app equalityAtZero (.const .refl)) (emptyValues model)).down := by
  change (ULift.up Evidence.refl = (ULift.up Evidence.refl : ULift.{1} Evidence)) ∧
    (ULift.up 0 = (ULift.up 0 : ULift.{1} Nat))
  exact ⟨rfl, rfl⟩

theorem unequal_endpoint_refused :
    ¬ (model.denote (.app (EqualityWitness.predicate (.const .refl) (.const .zero) (.const .one)) (.const .refl))
      (emptyValues model)).down := by
  change ¬ ((ULift.up Evidence.refl = (ULift.up Evidence.refl : ULift.{1} Evidence)) ∧
    (ULift.up 0 = (ULift.up 1 : ULift.{1} Nat)))
  rintro ⟨_, same⟩
  exact Nat.zero_ne_one (congrArg ULift.down same)

def head : ClosedTerm Const E := .const .refl
def tail : ClosedTerm Const E := pair operations head head

def domainMember (point : ClosedTerm Const E) : ProofSyntax Const [] (.app domain point) :=
  .impE (.eqPropER (.beta point .top)) .topI

def familyMember (first second : ClosedTerm Const E) : ProofSyntax Const [] (familyAt family first second) :=
  .impE (.eqPropER (.eqTrans (.eqApp second (.beta first (.lam .top))) (.beta second .top))) .topI

def introductionProof : ProofSyntax Const [] (.app (sigma operations domain family) (pair operations head tail)) :=
  introduce operations domain family head tail (domainMember head) (familyMember head tail)

theorem introduction_free : introductionProof.FunctionExtensionalityFree := by
  apply introduce_free
  · simp [domainMember, ProofSyntax.FunctionExtensionalityFree]
  · simp [familyMember, ProofSyntax.FunctionExtensionalityFree]

abbrev parameters : Ctx Base := [E]
def parameterDomain : Term Const parameters (E ⇒ .prop) := weakenCtx parameters domain
def parameterFamily : Term Const parameters (E ⇒ E ⇒ .prop) := weakenCtx parameters family
def point : Term Const parameters E := .var .vz

def assumptions : List (Formula Const parameters) :=
  [weakenCtx parameters (firstLaw operations), weakenCtx parameters (secondLaw operations),
    .app (sigma operations parameterDomain parameterFamily) point]

def projectionProof : ProofSyntax Const assumptions (decoded operations parameterDomain parameterFamily point) :=
  projection operations parameterDomain parameterFamily point
    (.hyp (Δ := assumptions) ⟨0, by decide +kernel⟩)
    (.hyp (Δ := assumptions) ⟨1, by decide +kernel⟩)
    (.hyp (Δ := assumptions) ⟨2, by decide +kernel⟩)

theorem projection_free : projectionProof.FunctionExtensionalityFree := by
  unfold projectionProof
  apply PredicateSigma.projection_free <;> trivial

def equalityProof : ProofSyntax Const [] (.app equalityAtZero (.const .refl)) :=
  EqualityWitness.introduce (.const Const.refl) (.const Const.zero) (.const Const.zero) (.eqRefl _)

theorem equality_free : equalityProof.FunctionExtensionalityFree := by
  unfold equalityProof
  apply EqualityWitness.introduce_free
  trivial

def values (head tail : Evidence) : model.Valuation parameters
  | _, .vz => ULift.up (.pair head tail)

theorem assumptions_realizable (head tail : Evidence) : Soundness.SatisfiesHyps model (values head tail) assumptions := by
  intro formula inside
  simp only [assumptions, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl
  · rw [model.denote_weakenCtx]
    exact first_law
  · rw [model.denote_weakenCtx]
    exact second_law
  · change (model.denote (sigma operations parameterDomain parameterFamily) (values head tail) (ULift.up (.pair head tail))).down
    rw [sigma_apply_denote_base model operations first_law second_law]
    refine ⟨ULift.up head, ULift.up tail, rfl, ?_, ?_⟩
    · change True
      trivial
    · change True
      trivial

theorem projected_result_holds (head tail : Evidence) :
    (model.denote (decoded operations parameterDomain parameterFamily point) (values head tail)).down :=
  Soundness.extDerivation_sound projectionProof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (assumptions_realizable head tail)

#print axioms pair_admitted
#print axioms reflexivity_not_pair
#print axioms projected_result_holds

end Mettapedia.Logic.HOL.PredicateSigma.Controls
