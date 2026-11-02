import Mettapedia.Languages.Micromath.Kernel
import Mettapedia.Logic.Derivation

/-!
# Static Micromath on the common finitary proof checker

An independent rule-instance relation presents the finite axiom list and
five static inference rules. The six-tag validator checks actual claim
fields and the original substitution algorithms. Its exact witness theorem
connects common certificate replay to the independent source calculus.

This concerns static finite proof trees. Fresh definitions, mutable slots,
UInt64 limits, binary decoding, native C and GSLT categories are separate
connections. Equal premise formulas need not identify their proof trees.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Micromath.Checking

def basis (axioms : List Claim) : Set Claim := fun claim => claim ∈ axioms

inductive RuleInstance (axioms : List Claim) : List Claim → Claim → Prop where
  | assumption {claim : Claim} : claim ∈ axioms → RuleInstance axioms [] claim
  | projectionFirst (a b : Symbol) : RuleInstance axioms [] (Micromath.projectionFirst a b)
  | projectionSecond (a b : Symbol) : RuleInstance axioms [] (Micromath.projectionSecond a b)
  | reflexivity (a : Symbol) : RuleInstance axioms [] (Micromath.reflexivity a)
  | substitute1 (main left right result : Claim) : Substitute1Guard main left right result →
      RuleInstance axioms [main,left,right,result] ⟨result.out,main.f,left.out,right.out⟩
  | substitute2 (main left right result : Claim) : Substitute2Guard main left right result →
      RuleInstance axioms [main,left,right,result] ⟨result.out,main.out,left.x,left.y⟩

inductive RuleTag where
  | assumption | projectionFirst | projectionSecond | reflexivity | substitute1 | substitute2
  deriving DecidableEq, Repr

def validate (axioms : List Claim) (tag : RuleTag) (premises : List Claim) (conclusion : Claim) : Bool :=
  match tag with
  | .assumption => decide (premises = [] ∧ conclusion ∈ axioms)
  | .projectionFirst => decide (premises = [] ∧ conclusion = Micromath.projectionFirst conclusion.out conclusion.y)
  | .projectionSecond => decide (premises = [] ∧ conclusion = Micromath.projectionSecond conclusion.x conclusion.out)
  | .reflexivity => decide (premises = [] ∧ conclusion = Micromath.reflexivity conclusion.out)
  | .substitute1 => match premises with
      | [main,left,right,result] => decide (Micromath.substitute1? main left right result = some conclusion)
      | _ => false
  | .substitute2 => match premises with
      | [main,left,right,result] => decide (Micromath.substitute2? main left right result = some conclusion)
      | _ => false

private theorem substitute1_accepted (main left right result conclusion : Claim) :
    substitute1? main left right result = some conclusion ↔
      Substitute1Guard main left right result ∧ conclusion = ⟨result.out,main.f,left.out,right.out⟩ := by
  unfold substitute1?
  by_cases guard : Substitute1Guard main left right result
  · simp [guard,eq_comm]
  · simp [guard]

private theorem substitute2_accepted (main left right result conclusion : Claim) :
    substitute2? main left right result = some conclusion ↔
      Substitute2Guard main left right result ∧ conclusion = ⟨result.out,main.out,left.x,left.y⟩ := by
  unfold substitute2?
  by_cases guard : Substitute2Guard main left right result
  · simp [guard,eq_comm]
  · simp [guard]

theorem validate_sound (axioms : List Claim) (tag : RuleTag) (premises : List Claim) (conclusion : Claim)
    (accepted : validate axioms tag premises conclusion = true) : RuleInstance axioms premises conclusion := by
  cases tag with
  | assumption =>
    obtain ⟨rfl,member⟩ := of_decide_eq_true accepted
    exact .assumption member
  | projectionFirst =>
    obtain ⟨rfl,same⟩ := of_decide_eq_true accepted
    rw [same]
    exact .projectionFirst _ _
  | projectionSecond =>
    obtain ⟨rfl,same⟩ := of_decide_eq_true accepted
    rw [same]
    exact .projectionSecond _ _
  | reflexivity =>
    obtain ⟨rfl,same⟩ := of_decide_eq_true accepted
    rw [same]
    exact .reflexivity _
  | substitute1 =>
    simp only [validate] at accepted
    split at accepted
    next main left right result =>
      obtain ⟨guard,same⟩ := (substitute1_accepted main left right result conclusion).mp (of_decide_eq_true accepted)
      rw [same]
      exact .substitute1 _ _ _ _ guard
    next => contradiction
  | substitute2 =>
    simp only [validate] at accepted
    split at accepted
    next main left right result =>
      obtain ⟨guard,same⟩ := (substitute2_accepted main left right result conclusion).mp (of_decide_eq_true accepted)
      rw [same]
      exact .substitute2 _ _ _ _ guard
    next => contradiction

theorem validate_complete (axioms : List Claim) (premises : List Claim) (conclusion : Claim)
    (rule : RuleInstance axioms premises conclusion) :
    ∃ tag, validate axioms tag premises conclusion = true := by
  cases rule with
  | assumption member => exact ⟨.assumption, by simp [validate,member]⟩
  | projectionFirst a b => exact ⟨.projectionFirst, by simp [validate,Micromath.projectionFirst]⟩
  | projectionSecond a b => exact ⟨.projectionSecond, by simp [validate,Micromath.projectionSecond]⟩
  | reflexivity a => exact ⟨.reflexivity, by simp [validate,Micromath.reflexivity]⟩
  | substitute1 main left right result guard => exact ⟨.substitute1, by simp [validate,substitute1?,guard]⟩
  | substitute2 main left right result guard => exact ⟨.substitute2, by simp [validate,substitute2?,guard]⟩

def interface (axioms : List Claim) : Mettapedia.Logic.RuleWitness (RuleInstance axioms) where
  W := RuleTag
  isInstance := validate axioms
  sound := validate_sound axioms
  complete := validate_complete axioms

theorem generic_derives_source (axioms : List Claim) {claim : Claim}
    (proof : Mettapedia.Logic.Derives (RuleInstance axioms) claim) : Micromath.Derives (basis axioms) claim := by
  apply Mettapedia.Logic.Derives.least (Micromath.Derives (basis axioms)) ?_ proof
  intro premises conclusion rule children
  cases rule with
  | assumption member => exact .assumption member
  | projectionFirst a b => exact .projectionFirst a b
  | projectionSecond a b => exact .projectionSecond a b
  | reflexivity a => exact .reflexivity a
  | substitute1 main left right result guard =>
    exact .substitute1 (children main (by simp)) (children left (by simp))
      (children right (by simp)) (children result (by simp))
      ((substitute1_accepted _ _ _ _ _).mpr ⟨guard,rfl⟩)
  | substitute2 main left right result guard =>
    exact .substitute2 (children main (by simp)) (children left (by simp))
      (children right (by simp)) (children result (by simp))
      ((substitute2_accepted _ _ _ _ _).mpr ⟨guard,rfl⟩)

private theorem four_premises {predicate : Claim → Prop} {main left right result : Claim}
    (mainProof : predicate main) (leftProof : predicate left) (rightProof : predicate right)
    (resultProof : predicate result) : ∀ claim ∈ [main,left,right,result], predicate claim := by
  intro claim member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact mainProof
  · exact leftProof
  · exact rightProof
  · exact resultProof

theorem source_derives_generic (axioms : List Claim) {claim : Claim}
    (proof : Micromath.Derives (basis axioms) claim) : Mettapedia.Logic.Derives (RuleInstance axioms) claim := by
  induction proof with
  | assumption member => exact .node [] _ (.assumption member) (by simp)
  | projectionFirst a b => exact .node [] _ (.projectionFirst a b) (by simp)
  | projectionSecond a b => exact .node [] _ (.projectionSecond a b) (by simp)
  | reflexivity a => exact .node [] _ (.reflexivity a) (by simp)
  | substitute1 _ _ _ _ accepted mainProof leftProof rightProof resultProof =>
    obtain ⟨guard,rfl⟩ := (substitute1_accepted _ _ _ _ _).mp accepted
    exact .node _ _ (.substitute1 _ _ _ _ guard) (four_premises mainProof leftProof rightProof resultProof)
  | substitute2 _ _ _ _ accepted mainProof leftProof rightProof resultProof =>
    obtain ⟨guard,rfl⟩ := (substitute2_accepted _ _ _ _ _).mp accepted
    exact .node _ _ (.substitute2 _ _ _ _ guard) (four_premises mainProof leftProof rightProof resultProof)

theorem generic_derives_iff_source (axioms : List Claim) (claim : Claim) :
    Mettapedia.Logic.Derives (RuleInstance axioms) claim ↔ Micromath.Derives (basis axioms) claim :=
  ⟨generic_derives_source axioms,source_derives_generic axioms⟩

abbrev Certificate := Mettapedia.Logic.Derivation Claim RuleTag

def accepted (axioms : List Claim) (certificate : Certificate) : Bool := certificate.valid (interface axioms)

theorem accepted_derives (axioms : List Claim) (certificate : Certificate)
    (checked : accepted axioms certificate = true) : Micromath.Derives (basis axioms) certificate.concl :=
  generic_derives_source axioms (Mettapedia.Logic.Derivation.valid_sound (interface axioms) certificate checked)

theorem derives_has_certificate (axioms : List Claim) {claim : Claim}
    (proof : Micromath.Derives (basis axioms) claim) :
    ∃ certificate : Certificate, accepted axioms certificate = true ∧ certificate.concl = claim :=
  Mettapedia.Logic.Derives.exists_derivation (interface axioms) (source_derives_generic axioms proof)

theorem derives_iff_certificate (axioms : List Claim) (claim : Claim) :
    Micromath.Derives (basis axioms) claim ↔
      ∃ certificate : Certificate, accepted axioms certificate = true ∧ certificate.concl = claim := by
  constructor
  · exact derives_has_certificate axioms
  · rintro ⟨certificate,checked,rfl⟩
    exact accepted_derives axioms certificate checked

universe u
theorem accepted_holds {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    (axioms : List Claim) (axiomsValid : ∀ claim ∈ axioms, Holds interpret claim)
    (certificate : Certificate) (checked : accepted axioms certificate = true) : Holds interpret certificate.concl :=
  derives_sound interpret projections axiomsValid (accepted_derives axioms certificate checked)

#print axioms validate_sound
#print axioms generic_derives_iff_source
#print axioms derives_iff_certificate
#print axioms accepted_holds
end Mettapedia.Languages.Micromath.Checking
