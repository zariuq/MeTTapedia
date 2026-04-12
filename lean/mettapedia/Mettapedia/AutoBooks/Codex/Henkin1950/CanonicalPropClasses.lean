import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalFrame

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Proposition-class interface for the canonical frame.

`CanonicalFrame.lean` interprets proposition-valued terms as quotient classes in
`TermClass T o` while formulas are interpreted separately via `Holds`.  This
file reconciles those two views: over a complete consistent theory, a
proposition class is canonically true exactly when it is the quotient class of
`⊤`, and false exactly when it is the quotient class of `⊥`.
-/

namespace CanonicalFrame

/-- The canonical truth-value class in the paper-faithful canonical frame. -/
abbrev trueClass {T : ClosedTheorySet} : Carrier T o :=
  classOf (T := T) (.top : Sentence)

/-- The canonical falsity class in the paper-faithful canonical frame. -/
abbrev falseClass {T : ClosedTheorySet} : Carrier T o :=
  classOf (T := T) (.bot : Sentence)

/-- A proposition class holds when it is the quotient class of `⊤`. -/
def PropClassHolds {T : ClosedTheorySet}
    (_hT : CompleteConsistentTheory T) (p : Carrier T o) : Prop :=
  p = trueClass (T := T)

@[simp] theorem propClassHolds_trueClass
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T) :
    PropClassHolds hT (trueClass (T := T)) :=
  rfl

/-- The proposition classes of `⊤` and `⊥` stay distinct in the canonical
frame. -/
theorem trueClass_ne_falseClass
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T) :
    trueClass (T := T) ≠ falseClass (T := T) := by
  intro hEq
  have hTermEq : TermEquivalent T (.top : Sentence) (.bot : Sentence) :=
    (classOf_eq_iff (T := T)).1 hEq
  have hEqv :
      Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
        (Const := Primitive) T (.top : Sentence) (.bot : Sentence) :=
    provablyEquivalent_of_termEquivalent_prop hTermEq
  have hTopMem : (.top : Sentence) ∈ T := by
    exact hT.closed <|
      Mettapedia.Logic.HOL.ClosedTheorySet.provable_top
        (Const := Primitive) T
  have hBotMem : (.bot : Sentence) ∈ T :=
    (mem_iff_of_provablyEquivalent_prop (T := T) hT hEqv).mp hTopMem
  exact hT.consistent <|
    Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
      (Const := Primitive) hBotMem

@[simp] theorem propClassHolds_falseClass_iff_false
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T) :
    PropClassHolds hT (falseClass (T := T)) ↔ False := by
  constructor
  · intro hFalse
    exact trueClass_ne_falseClass (T := T) hT hFalse.symm
  · intro h
    cases h

/-- Closed proposition classes are canonically true exactly when the
corresponding closed formula belongs to the theory. -/
@[simp] theorem propClassHolds_classOf_iff_mem
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (φ : Sentence) :
    PropClassHolds hT (classOf (T := T) φ) ↔ φ ∈ T := by
  constructor
  · intro hφ
    have hEq : TermEquivalent T φ (.top : Sentence) :=
      (classOf_eq_iff (T := T)).1 hφ
    have hEqv :
        Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
          (Const := Primitive) T φ (.top : Sentence) :=
      provablyEquivalent_of_termEquivalent_prop hEq
    have hTopMem : (.top : Sentence) ∈ T := by
      exact hT.closed <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_top
          (Const := Primitive) T
    exact
      (mem_iff_of_provablyEquivalent_prop (T := T) hT hEqv).mpr hTopMem
  · intro hφ
    have hTopMem : (.top : Sentence) ∈ T := by
      exact hT.closed <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_top
          (Const := Primitive) T
    have hEq :
        TermEquivalent T φ (.top : Sentence) :=
      termEquivalent_of_membership_iff
        (T := T)
        hT
        (φ := φ)
        (ψ := (.top : Sentence))
        (by
          constructor
          · intro _
            exact hTopMem
          · intro _
            exact hφ)
    exact (classOf_eq_iff (T := T)).2 hEq

/-- Closed proposition classes are canonically false exactly when the
corresponding closed formula does not belong to the theory. -/
@[simp] theorem classOf_eq_falseClass_iff_not_mem
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (φ : Sentence) :
    classOf (T := T) φ = falseClass (T := T) ↔ φ ∉ T := by
  constructor
  · intro hEq
    have hTermEq : TermEquivalent T φ (.bot : Sentence) :=
      (classOf_eq_iff (T := T)).1 hEq
    have hEqv :
        Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
          (Const := Primitive) T φ (.bot : Sentence) :=
      provablyEquivalent_of_termEquivalent_prop hTermEq
    have hBotNotMem : (.bot : Sentence) ∉ T := by
      intro hBotMem
      exact hT.consistent <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) hBotMem
    intro hφ
    exact hBotNotMem <|
      (mem_iff_of_provablyEquivalent_prop (T := T) hT hEqv).mp hφ
  · intro hφ
    have hBotNotMem : (.bot : Sentence) ∉ T := by
      intro hBotMem
      exact hT.consistent <|
        Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
          (Const := Primitive) hBotMem
    have hEq :
        TermEquivalent T φ (.bot : Sentence) :=
      termEquivalent_of_membership_iff
        (T := T)
        hT
        (φ := φ)
        (ψ := (.bot : Sentence))
        (by
          constructor
          · intro hMem
            exact False.elim (hφ hMem)
          · intro hMem
            exact False.elim (hBotNotMem hMem))
    exact (classOf_eq_iff (T := T)).2 hEq

/-- The proposition-class reading of a formula agrees with canonical truth. -/
@[simp] theorem propClassHolds_denoteTerm_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ : Formula Γ) :
    PropClassHolds hT (denoteTerm ν φ) ↔ denoteFormula T ν φ := by
  unfold denoteFormula Holds
  change PropClassHolds hT (classOf (T := T) (ClassAssignment.closeTerm ν φ)) ↔
    ClassAssignment.closeTerm ν φ ∈ T
  exact propClassHolds_classOf_iff_mem (T := T) hT (ClassAssignment.closeTerm ν φ)

/-- Negative canary: a formula denotes the canonical falsity class exactly when
it fails in the canonical truth relation. -/
@[simp] theorem denoteTerm_eq_falseClass_iff_not_denoteFormula
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ : Formula Γ) :
    denoteTerm ν φ = falseClass (T := T) ↔ ¬ denoteFormula T ν φ := by
  unfold denoteFormula Holds
  change classOf (T := T) (ClassAssignment.closeTerm ν φ) = falseClass (T := T) ↔
    ClassAssignment.closeTerm ν φ ∉ T
  exact classOf_eq_falseClass_iff_not_mem
    (T := T) hT (ClassAssignment.closeTerm ν φ)

/-- Predicate-class application holds exactly when the corresponding open
formula holds in the canonical frame. -/
@[simp] theorem propClassHolds_appClass_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    {σ : HTy}
    (p : Term Γ (Pred σ)) (t : Term Γ σ) :
    PropClassHolds hT
      (appClass (T := T) (denoteTerm ν p) (denoteTerm ν t)) ↔
        denoteFormula T ν (.app p t) := by
  rw [← denoteTerm_app (T := T) (ν := ν) (f := p) (t := t)]
  exact propClassHolds_denoteTerm_iff (T := T) hT ν (.app p t)

end CanonicalFrame

end Mettapedia.AutoBooks.Codex.Henkin1950
