import Mettapedia.OSLF.Framework.GeneratedScope

/-!
# The generated name scope of rho, with the drop coercion

`GeneratedScope` builds a scope over rho's quote and parallel formers, and its
header lists four ways it departs from the source material.  The second is the
one that matters for termination: the recursive occurrence there is the *quote*
of a part, not the **drop** of a name in the extension, and the source needs its
no-self-code property precisely because the drop makes the recursive argument
something other than a syntactic subterm.

This module builds the generator with the coercion, so the source's generator

    N = µX. @((φ ∨ X) | (ψ ∨ X))

is what is written: the two parts of the composition under the quote are each
either an atom or the drop of a name already in the scope.

## What the coercion costs, and what it does not

**Disjointness is free and is proved.**  A name of the scope determines its two
parts, because the quote of a composition determines the composition and the
composition of two determines them: `quote_par_injective`.  So the descent is
deterministic, and membership is decided rather than searched.

**No-self-code is free too, and is proved rather than assumed** — for the
syntactic reading.  A name cannot be the quote of a composition that drops it,
because such a term would be a proper subterm of itself; `no_selfCode` is that
argument, and it is what makes the descent terminate with no side condition.

**Where it stops being free is stated and not crossed.**  Modulo rho's
equations the property is not a size argument, since `@(*n) = n` lets a name be
rewritten to a term mentioning it, and nothing here proves the equational form.
The descent below decides membership for representatives; deciding it for
equation classes is a different statement and is not claimed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneratedScopeRho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.FormulaFixpoint

/-! ## Rho's three formers

Quotation and parallel composition are `GeneratedScope`'s; the drop is added
here. -/

open Mettapedia.OSLF.Framework.GeneratedScope (quote par)

/-- The drop of a name: the coercion the source's generator recurses through. -/
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]

/-! ## Disjointness -/

/-- **The decomposition is unique.**  A name of the scope determines both parts
of the composition under its quote, so the descent has no choice to make. -/
theorem quote_par_injective {leftOne rightOne leftTwo rightTwo : Pattern}
    (equal : quote (par leftOne rightOne) = quote (par leftTwo rightTwo)) :
    leftOne = leftTwo ∧ rightOne = rightTwo := by
  simp only [quote, par, Pattern.apply.injEq, Pattern.collection.injEq,
    List.cons.injEq, and_true, true_and] at equal
  exact equal

/-! ## No self code -/

/-- **A name is never its own code.**  It cannot be the quote of a composition
one of whose parts drops it, because that term contains it properly.  The
source assumes this; for representatives it is a theorem. -/
theorem no_selfCode_left (name right : Pattern) :
    name ≠ quote (par (drop name) right) := by
  intro equal
  have measured := congrArg sizeOf equal
  simp +arith [quote, drop, par, Pattern.apply.sizeOf_spec,
    Pattern.collection.sizeOf_spec] at measured

theorem no_selfCode_right (left name : Pattern) :
    name ≠ quote (par left (drop name)) := by
  intro equal
  have measured := congrArg sizeOf equal
  simp +arith [quote, drop, par, Pattern.apply.sizeOf_spec,
    Pattern.collection.sizeOf_spec] at measured

/-- And the descent's measure decreases: the name a part drops is a proper
subterm of the name being decomposed.  This is the no-self-code property in the
form the termination argument needs. -/
theorem sizeOf_drop_lt_left (name right : Pattern) :
    sizeOf name < sizeOf (quote (par (drop name) right)) := by
  simp +arith [quote, drop, par, Pattern.apply.sizeOf_spec,
    Pattern.collection.sizeOf_spec]

theorem sizeOf_drop_lt_right (left name : Pattern) :
    sizeOf name < sizeOf (quote (par left (drop name))) := by
  simp +arith [quote, drop, par, Pattern.apply.sizeOf_spec,
    Pattern.collection.sizeOf_spec]

/-! ## The generator -/

/-- A part of the composition is admitted when it satisfies the part's atom, or
when it is the drop of a name already in the scope.  This is the coercion the
source's generator recurses through. -/
def PartAdmitted (atom : Pred) (inScope : Pred) (part : Pattern) : Prop :=
  atom part ∨ ∃ name, part = drop name ∧ inScope name

/-- **The source's generator.**  A name is in the scope when it is the quote of
a composition both of whose parts are admitted. -/
def scopeStep (atomLeft atomRight : Pred) : Pred →o Pred where
  toFun := fun inScope name =>
    ∃ left right, name = quote (par left right) ∧
      PartAdmitted atomLeft inScope left ∧ PartAdmitted atomRight inScope right
  monotone' := by
    intro first second inclusion name
    rintro ⟨left, right, shape, leftAdmitted, rightAdmitted⟩
    refine ⟨left, right, shape, ?_, ?_⟩
    · rcases leftAdmitted with atom | ⟨inner, isDrop, member⟩
      · exact Or.inl atom
      · exact Or.inr ⟨inner, isDrop, inclusion inner member⟩
    · rcases rightAdmitted with atom | ⟨inner, isDrop, member⟩
      · exact Or.inl atom
      · exact Or.inr ⟨inner, isDrop, inclusion inner member⟩

/-- The scope generated by two part atoms. -/
def generatedScope (atomLeft atomRight : Pred) : Pred := lfp (scopeStep atomLeft atomRight)

/-- **The unfolding.**  A quote of two admitted parts is in the scope. -/
theorem mem_of_parts {atomLeft atomRight : Pred} {left right : Pattern}
    (leftAdmitted : PartAdmitted atomLeft (generatedScope atomLeft atomRight) left)
    (rightAdmitted : PartAdmitted atomRight (generatedScope atomLeft atomRight) right) :
    generatedScope atomLeft atomRight (quote (par left right)) :=
  mem_lfp_of_mem_apply ⟨left, right, rfl, leftAdmitted, rightAdmitted⟩

/-- The atomic case: both parts satisfy their atoms. -/
theorem mem_of_atoms {atomLeft atomRight : Pred} {left right : Pattern}
    (leftAtom : atomLeft left) (rightAtom : atomRight right) :
    generatedScope atomLeft atomRight (quote (par left right)) :=
  mem_of_parts (Or.inl leftAtom) (Or.inl rightAtom)

/-- And the reflective case: a part may be the drop of a name already in. -/
theorem mem_of_drop_left {atomLeft atomRight : Pred} {inner right : Pattern}
    (member : generatedScope atomLeft atomRight inner) (rightAtom : atomRight right) :
    generatedScope atomLeft atomRight (quote (par (drop inner) right)) :=
  mem_of_parts (Or.inr ⟨inner, rfl, member⟩) (Or.inl rightAtom)

/-- **Survey by induction.**  Anything true of the atomic quotes and preserved by
the coercion is true throughout the scope. -/
theorem scope_induction {atomLeft atomRight invariant : Pred}
    (step : ∀ left right,
      PartAdmitted atomLeft invariant left →
      PartAdmitted atomRight invariant right →
      invariant (quote (par left right))) :
    ∀ name, generatedScope atomLeft atomRight name → invariant name := by
  have pre : (scopeStep atomLeft atomRight) invariant ≤ invariant := by
    intro name
    rintro ⟨left, right, shape, leftAdmitted, rightAdmitted⟩
    rw [shape]
    exact step left right leftAdmitted rightAdmitted
  exact fun name member => lfp_le pre name member

/-! ## Membership by descent

The split is unique, so the descent is deterministic; the name a part drops is
strictly smaller, so it terminates.  Both are the theorems above. -/

/-- Membership decided by descent through the drop coercion.  The four cases are
the four shapes a decomposition can take: each part is either the drop of a name,
which the descent follows, or something the part's atom must accept. -/
def inScope (atomLeft atomRight : Pattern → Bool) : Pattern → Bool
  | .apply "NQuote"
      [.collection .hashBag [.apply "PDrop" [innerLeft], .apply "PDrop" [innerRight]] none] =>
      inScope atomLeft atomRight innerLeft && inScope atomLeft atomRight innerRight
  | .apply "NQuote"
      [.collection .hashBag [.apply "PDrop" [innerLeft], right] none] =>
      inScope atomLeft atomRight innerLeft && atomRight right
  | .apply "NQuote"
      [.collection .hashBag [left, .apply "PDrop" [innerRight]] none] =>
      atomLeft left && inScope atomLeft atomRight innerRight
  | .apply "NQuote" [.collection .hashBag [left, right] none] =>
      atomLeft left && atomRight right
  | _ => false
termination_by name => sizeOf name
decreasing_by
  · exact sizeOf_drop_lt_left _ _
  · exact sizeOf_drop_lt_right _ _
  · exact sizeOf_drop_lt_left _ _
  · exact sizeOf_drop_lt_right _ _

/-- **The procedure never reports a name the generator excludes.** -/
theorem generatedScope_of_inScope {atomLeft atomRight : Pattern → Bool} (name : Pattern) :
    inScope atomLeft atomRight name = true →
      generatedScope (fun t => atomLeft t = true) (fun t => atomRight t = true) name := by
  induction name using inScope.induct with
  | case1 innerLeft innerRight leftIH rightIH =>
      intro decision
      rw [inScope] at decision
      obtain ⟨leftDecision, rightDecision⟩ := Bool.and_eq_true_iff.mp decision
      exact mem_of_parts (Or.inr ⟨innerLeft, rfl, leftIH leftDecision⟩)
        (Or.inr ⟨innerRight, rfl, rightIH rightDecision⟩)
  | case2 innerLeft right rightNotDrop leftIH =>
      intro decision
      rw [inScope] at decision
      · obtain ⟨leftDecision, rightDecision⟩ := Bool.and_eq_true_iff.mp decision
        exact mem_of_parts (Or.inr ⟨innerLeft, rfl, leftIH leftDecision⟩) (Or.inl rightDecision)
      · exact rightNotDrop
  | case3 left innerRight leftNotDrop rightIH =>
      intro decision
      rw [inScope] at decision
      · obtain ⟨leftDecision, rightDecision⟩ := Bool.and_eq_true_iff.mp decision
        exact mem_of_parts (Or.inl leftDecision)
          (Or.inr ⟨innerRight, rfl, rightIH rightDecision⟩)
      · exact leftNotDrop
  | case4 left right notBoth notLeft notRight =>
      intro decision
      rw [inScope] at decision
      · obtain ⟨leftDecision, rightDecision⟩ := Bool.and_eq_true_iff.mp decision
        exact mem_of_parts (Or.inl leftDecision) (Or.inl rightDecision)
      · exact notBoth
      · exact notLeft
      · exact notRight
  | case5 name notOne notTwo notThree notFour =>
      intro decision
      rw [inScope.eq_def] at decision
      split at decision <;> simp_all

/-! ## Disjointness, and what it buys

The descent reads a part as a drop when it is one.  The generator allows a part
that is *both* a drop and an atom to be read either way.  Where the two readings
overlap the procedure is incomplete, and closing that is exactly the source's
disjointness hypothesis.  Here it is named, and both sides of it are proved. -/

/-- **Disjointness**: an atom never accepts a drop, so a part has one reading. -/
def AtomsAvoidDrops (atom : Pattern → Bool) : Prop :=
  ∀ inner, atom (drop inner) = false

/-- Under disjointness, a part an atom accepts is not a drop. -/
theorem not_drop_of_atom {atom : Pattern → Bool} (disjoint : AtomsAvoidDrops atom)
    {part : Pattern} (accepted : atom part = true) (inner : Pattern) :
    part ≠ drop inner := by
  intro isDrop
  rw [isDrop, disjoint inner] at accepted
  exact Bool.noConfusion accepted

/-- **The procedure reports every name the generator includes**, provided the
two readings of a part do not overlap. -/
theorem inScope_of_generatedScope {atomLeft atomRight : Pattern → Bool}
    (leftDisjoint : AtomsAvoidDrops atomLeft) (rightDisjoint : AtomsAvoidDrops atomRight) :
    ∀ name, generatedScope (fun t => atomLeft t = true) (fun t => atomRight t = true) name →
      inScope atomLeft atomRight name = true := by
  refine scope_induction (invariant := fun name => inScope atomLeft atomRight name = true) ?_
  intro left right leftAdmitted rightAdmitted
  rcases leftAdmitted with leftAtom | ⟨innerLeft, leftIsDrop, leftMember⟩ <;>
    rcases rightAdmitted with rightAtom | ⟨innerRight, rightIsDrop, rightMember⟩
  · rw [quote, par, inScope]
    · exact Bool.and_eq_true_iff.mpr ⟨leftAtom, rightAtom⟩
    · intro a b isLeft _
      exact not_drop_of_atom leftDisjoint leftAtom a isLeft
    · intro a isLeft
      exact not_drop_of_atom leftDisjoint leftAtom a isLeft
    · intro b isRight
      exact not_drop_of_atom rightDisjoint rightAtom b isRight
  · subst rightIsDrop
    rw [quote, par, drop, inScope]
    · exact Bool.and_eq_true_iff.mpr ⟨leftAtom, rightMember⟩
    · intro a isLeft
      exact not_drop_of_atom leftDisjoint leftAtom a isLeft
  · subst leftIsDrop
    rw [quote, par, drop, inScope]
    · exact Bool.and_eq_true_iff.mpr ⟨leftMember, rightAtom⟩
    · intro b isRight
      exact not_drop_of_atom rightDisjoint rightAtom b isRight
  · subst leftIsDrop
    subst rightIsDrop
    rw [quote, par, drop, drop, inScope]
    exact Bool.and_eq_true_iff.mpr ⟨leftMember, rightMember⟩

/-- **Membership is decidable by descent.**  The procedure and the generated
scope agree, under disjointness — with no-self-code discharged by the size
argument above rather than assumed. -/
theorem inScope_iff {atomLeft atomRight : Pattern → Bool}
    (leftDisjoint : AtomsAvoidDrops atomLeft) (rightDisjoint : AtomsAvoidDrops atomRight)
    (name : Pattern) :
    inScope atomLeft atomRight name = true ↔
      generatedScope (fun t => atomLeft t = true) (fun t => atomRight t = true) name :=
  ⟨generatedScope_of_inScope name,
    inScope_of_generatedScope leftDisjoint rightDisjoint name⟩

/-! ## Instances -/

namespace Specimen

/-- The terminated process. -/
def nil : Pattern := .apply "PZero" []

/-- An atom accepting only the terminated process: it accepts no drop, so it is
disjoint. -/
def isNil : Pattern → Bool := fun term => term == nil

theorem isNil_disjoint : AtomsAvoidDrops isNil := by
  intro inner
  simp [isNil, nil, drop]

/-- **Positive.**  The quote of two terminated processes is in the scope. -/
theorem base_in_scope : inScope isNil isNil (quote (par nil nil)) = true := by
  rw [quote, par, inScope] <;> simp [isNil, nil]

/-- **And the coercion works**: the quote of that name's drop beside a
terminated process is in the scope too, which is the step a generator without
the drop could not take. -/
theorem drop_in_scope :
    inScope isNil isNil (quote (par (drop (quote (par nil nil))) nil)) = true := by
  rw [quote, par, drop, inScope]
  · exact Bool.and_eq_true_iff.mpr ⟨base_in_scope, by simp [isNil, nil]⟩
  · intro b isRight
    simp [nil] at isRight

/-- **Negative.**  A name that is not a quote at all is not in the scope. -/
theorem nil_not_in_scope : inScope isNil isNil nil = false := by
  rw [nil, inScope.eq_def]
  split <;> simp_all

/-- And a quote whose parts the atoms reject is not in the scope either. -/
theorem other_not_in_scope :
    inScope isNil isNil (quote (par (.apply "Other" []) nil)) = false := by
  rw [quote, par, inScope] <;> simp [isNil, nil]

/-- **The scope is generated, and the two directions agree at these terms.** -/
theorem specimen_agrees :
    generatedScope (fun t => isNil t = true) (fun t => isNil t = true)
        (quote (par (drop (quote (par nil nil))) nil)) ∧
      ¬ generatedScope (fun t => isNil t = true) (fun t => isNil t = true) nil := by
  refine ⟨(inScope_iff isNil_disjoint isNil_disjoint _).mp drop_in_scope, ?_⟩
  intro member
  have := (inScope_iff isNil_disjoint isNil_disjoint nil).mpr member
  rw [nil_not_in_scope] at this
  exact Bool.noConfusion this

end Specimen

end Mettapedia.OSLF.Framework.GeneratedScopeRho
