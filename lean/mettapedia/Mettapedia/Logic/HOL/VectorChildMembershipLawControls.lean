import Mettapedia.Logic.HOL.VectorChildMembershipLawProduction
import Mettapedia.Logic.HOL.VectorChildArrayControls

/-!
# Array-law assembly and a necessary lookup premise

The actual natural/list model realizes all primitive laws. The predicate
selects seven and excludes padding zero. A second array has the same boundary
values but zero-valued interior entries: all other interface premises hold,
yet interior membership fails. Thus its missing lookup law cannot be treated
as an assumed implementation detail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildMembershipLaws.Controls
open VectorChildArrays.Controls (Base Const N E V ops model emptyValues numeral vector)
open OrderedPositionPrograms SuccessorOrder

def seven : ClosedTerm Const E := .const (.element 7)
def zeroElement : ClosedTerm Const E := .const (.element 0)
def predicate : ClosedTerm Const (E ⇒ .prop) := .lam (.eq (.var .vz) (weaken seven))
def fullPredicate : ClosedTerm Const (E ⇒ .prop) := .lam .top
def separationLaw := NaturalNumeralProofs.separation ops.zero ops.successor
def injectivityLaw := NaturalNumeralProofs.injectivity ops.successor
def inductionLaw := NaturalRecursionProofs.inductionPrinciple ops.zero ops.successor
def assumptions : List (ClosedFormula Const) := separationLaw :: injectivityLaw :: inductionLaw :: ops.assumptions []
def arithmetic : PeanoEvidence ops.successor ops.zero assumptions :=
  ⟨.hyp ⟨0,by decide⟩,.hyp ⟨1,by decide⟩,.hyp ⟨2,by decide⟩⟩
def premises : ops.ComputationPremises assumptions :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend separationLaw
theorem arithmetic_free : arithmetic.Free := by trivial
theorem premises_free : premises.FunctionExtensionalityFree :=
  ((ops.assumptionPremises.prepend inductionLaw).prepend injectivityLaw).prepend_free _
    ((ops.assumptionPremises.prepend inductionLaw).prepend_free _
      (ops.assumptionPremises.prepend_free _ ops.assumptionPremises_free))

def sevenMember {Δ : List (ClosedFormula Const)} : ProofSyntax Const Δ (.app predicate seven) := by
  apply ProofSyntax.impE (.eqPropER (.beta seven (.eq (.var .vz) (weaken seven))))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl seven)
  simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]
theorem sevenMember_free {Δ : List (ClosedFormula Const)} : (sevenMember (Δ := Δ)).FunctionExtensionalityFree := by
  unfold sevenMember
  exact ⟨True.intro,(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩
def fullMember {Δ : List (ClosedFormula Const)} (value : ClosedTerm Const E) : ProofSyntax Const Δ (.app fullPredicate value) :=
  .impE (.eqPropER (.beta value .top)) .topI

def sevens : Nat → ClosedTerm Const V
  | 0 => ops.nil
  | n+1 => ops.toSignature.consValue (numeral n) seven (sevens n)
def sevensMember {Δ : List (ClosedFormula Const)} : (n : Nat) →
    ProofSyntax Const Δ (ops.toSignature.member predicate (numeral n) (sevens n))
  | 0 => ops.toSignature.nil_member predicate
  | n+1 => ops.toSignature.cons_member predicate (numeral n) seven (sevens n) sevenMember (sevensMember n)
theorem sevensMember_free {Δ : List (ClosedFormula Const)} (n : Nat) : (sevensMember (Δ := Δ) n).FunctionExtensionalityFree := by
  induction n with
  | zero => exact ops.toSignature.nil_member_free predicate
  | succ n previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ sevenMember_free previous

def array (n : Nat) := ops.mixed (numeral n) seven (sevens n) seven zeroElement
def firstCase (n : Nat) : ProofSyntax Const assumptions
    (mixedCases ops.zero ops.successor (numeral n) (numeral 0) (.top : ClosedFormula Const) .top .top .top) :=
  .orIL (.andI (.eqRefl _) (.eqRefl _))
def lastCase (n : Nat) : ProofSyntax Const assumptions
    (mixedCases ops.zero ops.successor (numeral n) (numeral (n+1)) (.top : ClosedFormula Const) .top .top .top) :=
  .orIR (.orIR (.andI (.eqRefl _) (.eqRefl _)))
def first (n : Nat) : ProofSyntax Const assumptions (.app predicate (.app (array n) (numeral 0))) :=
  ops.assembleMembership predicate (numeral n) (numeral 0) seven (sevens n) seven zeroElement
    (.top : ClosedFormula Const) .top .top .top premises arithmetic sevenMember (sevensMember n) sevenMember (firstCase n)
def last (n : Nat) : ProofSyntax Const assumptions (.app predicate (.app (array n) (numeral (n+1)))) :=
  ops.assembleMembership predicate (numeral n) (numeral (n+1)) seven (sevens n) seven zeroElement
    (.top : ClosedFormula Const) .top .top .top premises arithmetic sevenMember (sevensMember n) sevenMember (lastCase n)

def sourceLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) (sevens 2) (numeral 0) seven) :=
  IndexedVectorPositions.here ops.toSignature (numeral 1) seven (sevens 1)
def sourceBound : ProofSyntax Const assumptions (.app (.app (SuccessorOrder.less ops.successor) (numeral 0)) (numeral 2)) :=
  IndexedVectorPositionBounds.lessOfLookup ops.toSignature (numeral 2) (sevens 2) (numeral 0) seven arithmetic.induction sourceLookup
def interiorCase : ProofSyntax Const assumptions
    (mixedCases ops.zero ops.successor (numeral 2) (numeral 1) (.top : ClosedFormula Const) .top .top .top) := by
  apply ProofSyntax.orIR
  apply ProofSyntax.orIL
  apply ProofSyntax.exI (numeral 0)
  apply ProofSyntax.castIndices rfl ?_ (.andI (.eqRefl (numeral 1)) (.andI sourceBound (.eqRefl (Term.top : ClosedFormula Const))))
  simp only [instantiate,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]
  rfl
def interior : ProofSyntax Const assumptions (.app predicate (.app (array 2) (numeral 1))) :=
  ops.assembleMembership predicate (numeral 2) (numeral 1) seven (sevens 2) seven zeroElement
    (.top : ClosedFormula Const) .top .top .top premises arithmetic sevenMember (sevensMember 2) sevenMember interiorCase

theorem assumptions_realizable : Soundness.SatisfiesHyps model emptyValues assumptions := by
  intro formula present
  simp only [assumptions,List.mem_cons] at present
  rcases present with rfl | rfl | rfl | present
  · intro n _ same
    have impossible : n.down+1 = (0:Nat) := congrArg ULift.down same
    exact Nat.noConfusion impossible
  · intro n _ m _
    constructor
    · intro same; apply ULift.ext; exact Nat.succ.inj (congrArg ULift.down same)
    · intro same; cases same; rfl
  · intro p _ clauses n _
    rcases n with ⟨n⟩
    induction n with
    | zero => exact clauses.1
    | succ n previous => exact clauses.2 (ULift.up n) trivial (previous trivial)
  · exact VectorChildArrays.Controls.assumptions_realizable _ present
theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula emptyValues).down :=
  Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable
theorem all_lengths_boundaries_hold (n : Nat) :
    (model.denote (.app predicate (.app (array n) (numeral 0))) emptyValues).down ∧
    (model.denote (.app predicate (.app (array n) (numeral (n+1)))) emptyValues).down :=
  ⟨sound (first n),sound (last n)⟩
theorem interior_holds : (model.denote (.app predicate (.app (array 2) (numeral 1))) emptyValues).down := sound interior

def wrongArray := ops.mixed (numeral 2) seven (vector [0,0]) seven zeroElement
def wrongVectorMember : ProofSyntax Const assumptions (ops.toSignature.member fullPredicate (numeral 2) (vector [0,0])) :=
  ops.toSignature.cons_member fullPredicate (numeral 1) zeroElement (vector [0]) (fullMember zeroElement)
    (ops.toSignature.cons_member fullPredicate (numeral 0) zeroElement (vector []) (fullMember zeroElement)
      (ops.toSignature.nil_member fullPredicate))
def wrongLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) (vector [0,0]) (numeral 0) zeroElement) :=
  IndexedVectorPositions.here ops.toSignature (numeral 1) zeroElement (vector [0])
def wrongValue : ProofSyntax Const assumptions (.eq (.app wrongArray (numeral 1)) zeroElement) :=
  ops.mixedAtLookup (numeral 2) seven (vector [0,0]) seven zeroElement (numeral 0) zeroElement premises wrongLookup
def wrongGoal : ClosedFormula Const := .app predicate (.app wrongArray (numeral 1))
theorem wrongGoal_false : ¬ (model.denote wrongGoal emptyValues).down := by
  intro member
  have value := sound wrongValue
  change model.denote (.app wrongArray (numeral 1)) emptyValues = ULift.up 0 at value
  change model.denote (.app wrongArray (numeral 1)) emptyValues = ULift.up 7 at member
  have impossible : (0:Nat) = 7 := congrArg ULift.down (value.symm.trans member)
  exact Nat.noConfusion impossible

def otherLaws : List (ClosedFormula Const) :=
  [.eq (.app wrongArray (numeral 0)) seven,.eq (.app wrongArray (numeral 3)) seven,
   IndexedVectorLookupCoverage.condition ops.toSignature predicate (numeral 2) (sevens 2),
   .app predicate seven,
   mixedCases ops.zero ops.successor (numeral 2) (numeral 1) (.top : ClosedFormula Const) .top .top .top]
theorem otherLaws_hold : Soundness.SatisfiesHyps model emptyValues otherLaws := by
  intro formula present
  simp only [otherLaws,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl
  · exact sound (ops.mixedLeading (numeral 2) seven (vector [0,0]) seven zeroElement premises)
  · exact sound (ops.mixedTrailing fullPredicate (numeral 2) seven (vector [0,0]) seven zeroElement premises wrongVectorMember)
  · exact sound (IndexedVectorLookupCoverage.fromMembership ops.toSignature predicate (numeral 2) (sevens 2) arithmetic (sevensMember 2))
  · exact sound sevenMember
  · exact sound interiorCase
theorem dropping_lookup_law_refused : ¬ Nonempty (ProofSyntax Const otherLaws wrongGoal) := by
  rintro ⟨claimed⟩
  exact wrongGoal_false (Soundness.extDerivation_sound claimed.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)) (fun _ => trivial) otherLaws_hold)

#print axioms all_lengths_boundaries_hold
#print axioms interior_holds
#print axioms dropping_lookup_law_refused
end Mettapedia.Logic.HOL.VectorChildMembershipLaws.Controls
