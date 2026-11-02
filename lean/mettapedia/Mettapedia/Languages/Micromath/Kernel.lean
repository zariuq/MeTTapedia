import Mathlib.Data.Set.Basic

/-!
# Micromath's static binary-superposition inference rules

The source reference is `kernel.c` at revision
`41ea90e86d04762b411bac67af43d75986297ecb`:
https://git.olsak.net/mirek/Micromath/src/commit/41ea90e86d04762b411bac67af43d75986297ecb/kernel.c

A claim describes an equality of binary functions. Both substitution
operations check the seven source field equalities before returning their
conclusion. Natural symbol addresses specify the unbounded mathematical
calculus. Allocation, theorem slots, UInt64 bounds, binary decoding and the
C implementation are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Micromath

abbrev Symbol := Nat

structure Claim where
  out : Symbol
  f : Symbol
  x : Symbol
  y : Symbol
  deriving DecidableEq, Repr

universe u
abbrev Assignment (D : Type u) := Symbol → D → D → D

structure Projects {D : Type u} (interpret : Assignment D) : Prop where
  first : ∀ a b, interpret 0 a b = a
  second : ∀ a b, interpret 1 a b = b

def Holds {D : Type u} (interpret : Assignment D) (claim : Claim) : Prop :=
  ∀ a b, interpret claim.out a b = interpret claim.f (interpret claim.x a b) (interpret claim.y a b)

def projectionFirst (a b : Symbol) : Claim := ⟨a,0,a,b⟩
def projectionSecond (a b : Symbol) : Claim := ⟨b,1,a,b⟩
def reflexivity (a : Symbol) : Claim := ⟨a,a,0,1⟩

def Substitute1Guard (main left right result : Claim) : Prop :=
  left.f = main.x ∧ right.f = main.y ∧ right.x = left.x ∧ right.y = left.y ∧
  result.f = main.out ∧ result.x = left.x ∧ result.y = left.y

def Substitute2Guard (main left right result : Claim) : Prop :=
  left.f = main.x ∧ right.f = main.y ∧ right.x = left.x ∧ right.y = left.y ∧
  result.f = main.f ∧ result.x = left.out ∧ result.y = right.out

instance (main left right result : Claim) : Decidable (Substitute1Guard main left right result) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
instance (main left right result : Claim) : Decidable (Substitute2Guard main left right result) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def substitute1? (main left right result : Claim) : Option Claim :=
  if Substitute1Guard main left right result then some ⟨result.out,main.f,left.out,right.out⟩ else none

def substitute2? (main left right result : Claim) : Option Claim :=
  if Substitute2Guard main left right result then some ⟨result.out,main.out,left.x,left.y⟩ else none

theorem projectionFirst_holds {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    (a b : Symbol) : Holds interpret (projectionFirst a b) := by
  intro x y
  exact (projections.first _ _).symm

theorem projectionSecond_holds {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    (a b : Symbol) : Holds interpret (projectionSecond a b) := by
  intro x y
  exact (projections.second _ _).symm

theorem reflexivity_holds {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    (a : Symbol) : Holds interpret (reflexivity a) := by
  intro x y
  exact congrArg₂ (interpret a) (projections.first x y).symm (projections.second x y).symm

/-- The four premise proofs are used at the same pair of input expressions.
The source guard enforces that shared pair explicitly. -/
theorem substitute1_holds {D : Type u} (interpret : Assignment D)
    (main left right result conclusion : Claim)
    (mainValid : Holds interpret main) (leftValid : Holds interpret left)
    (rightValid : Holds interpret right) (resultValid : Holds interpret result)
    (accepted : substitute1? main left right result = some conclusion) : Holds interpret conclusion := by
  unfold substitute1? at accepted
  split at accepted
  next guard =>
    cases Option.some.inj accepted
    rcases guard with ⟨leftFunction,rightFunction,rightFirst,rightSecond,resultFunction,resultFirst,resultSecond⟩
    intro a b
    have l := leftValid a b
    have r := rightValid a b
    have z := resultValid a b
    rw [leftFunction] at l
    rw [rightFunction,rightFirst,rightSecond] at r
    rw [resultFunction,resultFirst,resultSecond] at z
    exact z.trans ((mainValid _ _).trans (congrArg₂ (interpret main.f) l.symm r.symm))
  next rejected => contradiction

theorem substitute2_holds {D : Type u} (interpret : Assignment D)
    (main left right result conclusion : Claim)
    (mainValid : Holds interpret main) (leftValid : Holds interpret left)
    (rightValid : Holds interpret right) (resultValid : Holds interpret result)
    (accepted : substitute2? main left right result = some conclusion) : Holds interpret conclusion := by
  unfold substitute2? at accepted
  split at accepted
  next guard =>
    cases Option.some.inj accepted
    rcases guard with ⟨leftFunction,rightFunction,rightFirst,rightSecond,resultFunction,resultFirst,resultSecond⟩
    intro a b
    have l := leftValid a b
    have r := rightValid a b
    have z := resultValid a b
    rw [leftFunction] at l
    rw [rightFunction,rightFirst,rightSecond] at r
    rw [resultFunction,resultFirst,resultSecond] at z
    exact z.trans ((congrArg₂ (interpret main.f) l r).trans (mainValid _ _).symm)
  next rejected => contradiction

inductive Derives (axioms : Set Claim) : Claim → Prop where
  | assumption {claim : Claim} : claim ∈ axioms → Derives axioms claim
  | projectionFirst (a b : Symbol) : Derives axioms (projectionFirst a b)
  | projectionSecond (a b : Symbol) : Derives axioms (projectionSecond a b)
  | reflexivity (a : Symbol) : Derives axioms (reflexivity a)
  | substitute1 {main left right result conclusion : Claim} :
      Derives axioms main → Derives axioms left → Derives axioms right → Derives axioms result →
      substitute1? main left right result = some conclusion → Derives axioms conclusion
  | substitute2 {main left right result conclusion : Claim} :
      Derives axioms main → Derives axioms left → Derives axioms right → Derives axioms result →
      substitute2? main left right result = some conclusion → Derives axioms conclusion

theorem derives_sound {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    {axioms : Set Claim} (axiomsValid : ∀ claim ∈ axioms, Holds interpret claim)
    {claim : Claim} (proof : Derives axioms claim) : Holds interpret claim := by
  induction proof with
  | assumption member => exact axiomsValid _ member
  | projectionFirst a b => exact projectionFirst_holds interpret projections a b
  | projectionSecond a b => exact projectionSecond_holds interpret projections a b
  | reflexivity a => exact reflexivity_holds interpret projections a
  | substitute1 _ _ _ _ accepted mainValid leftValid rightValid resultValid =>
    exact substitute1_holds interpret _ _ _ _ _ mainValid leftValid rightValid resultValid accepted
  | substitute2 _ _ _ _ accepted mainValid leftValid rightValid resultValid =>
    exact substitute2_holds interpret _ _ _ _ _ mainValid leftValid rightValid resultValid accepted

/-- Equality of named binary operations uses the ordinary theorem format. -/
def symbolEquality (first second : Symbol) : Claim := ⟨first,second,0,1⟩

theorem symbolEquality_holds_iff {D : Type u} (interpret : Assignment D) (projections : Projects interpret)
    (first second : Symbol) : Holds interpret (symbolEquality first second) ↔
      ∀ a b, interpret first a b = interpret second a b := by
  constructor
  · intro equality a b
    exact (equality a b).trans (congrArg₂ (interpret second) (projections.first a b) (projections.second a b))
  · intro equality a b
    exact (equality a b).trans
      (congrArg₂ (interpret second) (projections.first a b).symm (projections.second a b).symm)

namespace Derives
theorem equality_symmetry {axioms : Set Claim} {first second : Symbol}
    (equality : Derives axioms (symbolEquality first second)) : Derives axioms (symbolEquality second first) := by
  apply substitute2 equality (projectionFirst 0 1) (projectionSecond 0 1) (reflexivity second)
  unfold substitute2?
  exact if_pos ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem equality_transitivity {axioms : Set Claim} {first second third : Symbol}
    (earlier : Derives axioms (symbolEquality first second))
    (later : Derives axioms (symbolEquality second third)) : Derives axioms (symbolEquality first third) := by
  apply substitute1 later (projectionFirst 0 1) (projectionSecond 0 1) earlier
  unfold substitute1?
  exact if_pos ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end Derives

#print axioms substitute1_holds
#print axioms substitute2_holds
#print axioms derives_sound
#print axioms Derives.equality_transitivity

end Mettapedia.Languages.Micromath
