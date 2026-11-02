import Mettapedia.Logic.HOL.IndexedVectorLookupCoverage
import Mettapedia.Logic.HOL.VectorChildArrayBoundaryControls

/-!
# Independent natural/list controls for bounded lookup coverage

Every concrete source list supplies its own membership evidence. The three
arithmetic premises hold in the existing natural/list interpretation. A bound
therefore yields a real scoped lookup for every list and position. End positions
and replacing the element predicate by false are independently refuted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorLookupCoverage.Controls
open VectorChildArrays.Controls
open IndexedVectorLookupWitnesses SuccessorOrder

def separationLaw := NaturalNumeralProofs.separation ops.zero ops.successor
def injectivityLaw := NaturalNumeralProofs.injectivity ops.successor
def inductionLaw := NaturalRecursionProofs.inductionPrinciple ops.zero ops.successor
def arithmeticHyps : List (ClosedFormula Const) := [separationLaw,injectivityLaw,inductionLaw]
def arithmetic : PeanoEvidence ops.successor ops.zero arithmeticHyps :=
  ⟨.hyp (Δ := arithmeticHyps) ⟨0,by decide⟩,.hyp (Δ := arithmeticHyps) ⟨1,by decide⟩,
    .hyp (Δ := arithmeticHyps) ⟨2,by decide⟩⟩
theorem arithmetic_free : arithmetic.Free := by trivial

theorem separation_holds : model.models separationLaw := by
  intro n _ same
  exact Nat.noConfusion (congrArg ULift.down same)

theorem injectivity_holds : model.models injectivityLaw := by
  intro n _ m _
  constructor
  · intro same
    apply ULift.ext
    exact Nat.succ.inj (congrArg ULift.down same)
  · intro same
    cases same
    rfl

theorem induction_holds : model.models inductionLaw := by
  intro predicate _ clauses n _
  rcases n with ⟨n⟩
  induction n with
  | zero => exact clauses.1
  | succ n previous => exact clauses.2 (ULift.up n) trivial (previous trivial)

theorem arithmetic_realizable : Soundness.SatisfiesHyps model emptyValues arithmeticHyps := by
  intro formula present
  simp only [arithmeticHyps,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · exact separation_holds
  · exact injectivity_holds
  · exact induction_holds

def memberFormula (xs : List Nat) := ops.toSignature.member VectorChildArrays.BoundaryControls.full
  (numeral xs.length) (vector xs)
def boundFormula (length position : Nat) : ClosedFormula Const :=
  .app (.app (less ops.successor) (numeral position)) (numeral length)
def sourceHyps (xs : List Nat) := memberFormula xs :: arithmeticHyps
def inputHyps (xs : List Nat) (position : Nat) := boundFormula xs.length position :: sourceHyps xs

theorem member_holds (xs : List Nat) : (model.denote (memberFormula xs) emptyValues).down :=
  VectorChildArrays.Controls.sound (VectorChildArrays.BoundaryControls.member xs)

theorem bound_iff (length position : Nat) :
    (model.denote (boundFormula length position) emptyValues).down ↔ position < length := by
  change (model.denote (less ops.successor) emptyValues
    (model.denote (numeral position) emptyValues) (model.denote (numeral length) emptyValues)).down ↔ _
  rw [VectorChildArrays.BoundaryControls.numeral_denote,VectorChildArrays.BoundaryControls.numeral_denote]
  exact less_iff model (HenkinModel.fullDomains_standard _ _) ops.successor emptyValues Equiv.ulift.symm
    (fun _ => rfl) (ULift.up position) (ULift.up length)

theorem source_realizable (xs : List Nat) : Soundness.SatisfiesHyps model emptyValues (sourceHyps xs) := by
  intro formula present
  simp only [sourceHyps,List.mem_cons] at present
  rcases present with rfl | present
  · exact member_holds xs
  · exact arithmetic_realizable _ present

theorem input_realizable (xs : List Nat) (position : Nat) (bounded : position < xs.length) :
    Soundness.SatisfiesHyps model emptyValues (inputHyps xs position) := by
  intro formula present
  simp only [inputHyps,List.mem_cons] at present
  rcases present with rfl | present
  · exact (bound_iff _ _).mpr bounded
  · exact source_realizable xs _ present

def produced (xs : List Nat) (position : Nat) : ProofSyntax Const (inputHyps xs position)
    (evidence ops.toSignature VectorChildArrays.BoundaryControls.full (numeral xs.length) (vector xs) (numeral position)) :=
  witnessFromBound ops.toSignature VectorChildArrays.BoundaryControls.full (numeral xs.length) (vector xs) (numeral position)
    ((arithmetic.prepend (memberFormula xs)).prepend (boundFormula xs.length position))
    (.hyp (Δ := inputHyps xs position) ⟨1,by change 1 < 5; decide⟩)
    (.hyp (Δ := inputHyps xs position) ⟨0,by change 0 < 5; decide⟩)

theorem produced_free (xs : List Nat) (position : Nat) : (produced xs position).FunctionExtensionalityFree :=
  witnessFromBound_free _ _ _ _ _ _ _ _
    ((arithmetic.prepend _).prepend_free _ (arithmetic.prepend_free _ arithmetic_free)) trivial trivial

theorem every_bounded_position_has_witness (xs : List Nat) (position : Nat) (bounded : position < xs.length) :
    (model.denote (evidence ops.toSignature VectorChildArrays.BoundaryControls.full
      (numeral xs.length) (vector xs) (numeral position)) emptyValues).down :=
  Soundness.extDerivation_sound (produced xs position).erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (input_realizable xs position bounded)

theorem end_position_refused (xs : List Nat) :
    ¬ Nonempty (ProofSyntax Const (sourceHyps xs)
      (evidence ops.toSignature VectorChildArrays.BoundaryControls.full (numeral xs.length) (vector xs) (numeral xs.length))) := by
  rintro ⟨claimed⟩
  have outside := boundFromWitness ops.toSignature VectorChildArrays.BoundaryControls.full
    (numeral xs.length) (vector xs) (numeral xs.length) ((arithmetic.prepend (memberFormula xs)).induction) claimed
  have impossible := Soundness.extDerivation_sound outside.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (source_realizable xs)
  exact Nat.lt_irrefl _ ((bound_iff xs.length xs.length).mp impossible)

def emptyPredicate : ClosedTerm Const (E ⇒ .prop) := .lam .bot

theorem changed_element_predicate_refused (xs : List Nat) (position : Nat) (bounded : position < xs.length) :
    ¬ Nonempty (ProofSyntax Const (inputHyps xs position)
      (evidence ops.toSignature emptyPredicate (numeral xs.length) (vector xs) (numeral position))) := by
  rintro ⟨claimed⟩
  have impossible := Soundness.extDerivation_sound claimed.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (input_realizable xs position bounded)
  rcases impossible with ⟨element,_,_,absurd⟩
  exact absurd

theorem repeated_values_keep_both_positions :
    (model.denote (evidence ops.toSignature VectorChildArrays.BoundaryControls.full
      (numeral 2) (vector [7,7]) (numeral 0)) emptyValues).down ∧
    (model.denote (evidence ops.toSignature VectorChildArrays.BoundaryControls.full
      (numeral 2) (vector [7,7]) (numeral 1)) emptyValues).down :=
  ⟨every_bounded_position_has_witness [7,7] 0 (by decide),
    every_bounded_position_has_witness [7,7] 1 (by decide)⟩

#print axioms arithmetic_realizable
#print axioms every_bounded_position_has_witness
#print axioms end_position_refused
#print axioms changed_element_predicate_refused
end Mettapedia.Logic.HOL.IndexedVectorLookupCoverage.Controls
