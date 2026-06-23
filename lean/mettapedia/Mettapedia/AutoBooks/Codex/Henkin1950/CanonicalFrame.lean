import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalTruthLaws

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Paper-faithful class-based canonical frame for Henkin pp. 86-88.

Instead of prematurely forcing the quotient construction through the trusted
`HenkinModel` interface, this file records the canonical frame exactly at the
paper-facing abstraction level already available in Codex:

- the carrier at each type is the quotient `TermClass T τ` of closed terms;
- application is descended application `appClass`;
- open terms are interpreted by closing them under a quotient-valued class
  assignment and then taking the resulting quotient class;
- open formulas are interpreted by the canonical truth relation `Holds`.

This is the smallest honest denotation layer that can already be built on the
current foundations without smuggling in an incorrect proposition domain.
-/

namespace CanonicalFrame

/-- The carrier of the paper-faithful canonical frame at type `τ`. -/
abbrev Carrier (T : ClosedTheorySet) (τ : HTy) : Type :=
  TermClass T τ

/-- Variable assignments into the class-based canonical frame. -/
abbrev Assignment (T : ClosedTheorySet) (Γ : Ctx Atom) : Type :=
  ClassAssignment T Γ

/-- Constants denote as their closed-term quotient classes. -/
def constValue {T : ClosedTheorySet} {τ : HTy} (c : Primitive τ) :
    Carrier T τ :=
  classOf (T := T) (.const c)

/-- Open terms denote by closing them with the chosen representatives of a
quotient-valued assignment and then taking the resulting quotient class. -/
noncomputable def denoteTerm
    {T : ClosedTheorySet}
    (ν : Assignment T Γ) (t : Term Γ τ) :
    Carrier T τ :=
  classOf (T := T) (ClassAssignment.closeTerm ν t)

/-- Open formulas denote by the canonical truth relation. -/
def denoteFormula
    (T : ClosedTheorySet)
    (ν : Assignment T Γ) (φ : Formula Γ) : Prop :=
  Holds T ν φ

@[simp] theorem denoteTerm_var
    {T : ClosedTheorySet}
    (ν : Assignment T Γ) (v : Var Γ τ) :
    denoteTerm ν (.var v : Term Γ τ) = ν v := by
  unfold denoteTerm
  simpa [ClassAssignment.closeTerm, RepresentativeAssignment.toClassAssignment] using
    (ClassAssignment.toClassAssignment_chooseRepresentatives
      (T := T) (ν := ν) (v := v))

@[simp] theorem denoteTerm_const
    {T : ClosedTheorySet}
    (ν : Assignment T Γ) (c : Primitive τ) :
    denoteTerm ν (.const c : Term Γ τ) = constValue (T := T) c := by
  unfold denoteTerm constValue
  rfl

@[simp] theorem denoteTerm_app
    {T : ClosedTheorySet}
    (ν : Assignment T Γ)
    (f : Term Γ (σ ⇒ τ)) (t : Term Γ σ) :
    denoteTerm ν (.app f t) =
      appClass (T := T) (denoteTerm ν f) (denoteTerm ν t) := by
  unfold denoteTerm ClassAssignment.closeTerm
  unfold Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
  rfl

/-- If an equality formula holds in the canonical frame, then the denotations of
its two sides are equal quotient classes. -/
theorem denoteFormula_eq_implies_denoteTerm_eq
    {T : ClosedTheorySet}
    (ν : Assignment T Γ)
    {τ : HTy} {t u : Term Γ τ} :
    denoteFormula T ν (eq t u) →
      denoteTerm ν t = denoteTerm ν u := by
  intro hEq
  apply (classOf_eq_iff (T := T)).2
  exact
    extSetProvable_of_mem
      (T := T)
      (by
        simpa [denoteFormula, Holds, denoteTerm, ClassAssignment.closeFormula, ClassAssignment.closeTerm,
            closeTerm, subst, eq]
          using hEq)

/-- Conversely, over a complete consistent theory, equal denotations yield
canonical truth of the corresponding equality formula. -/
theorem denoteFormula_eq_of_denoteTerm_eq
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    {τ : HTy} {t u : Term Γ τ} :
    denoteTerm ν t = denoteTerm ν u →
      denoteFormula T ν (eq t u) := by
  intro hEq
  have hTermEq :
      TermEquivalent T
        (ClassAssignment.closeTerm ν t)
        (ClassAssignment.closeTerm ν u) :=
    (classOf_eq_iff (T := T)).1 hEq
  have hEqMem :
      eq (ClassAssignment.closeTerm ν t) (ClassAssignment.closeTerm ν u) ∈ T :=
    hT.closed hTermEq
  simpa [denoteFormula, Holds, denoteTerm, ClassAssignment.closeFormula, ClassAssignment.closeTerm,
      closeTerm, subst, eq]
    using hEqMem

@[simp] theorem denoteFormula_eq_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    {τ : HTy} (t u : Term Γ τ) :
    denoteFormula T ν (eq t u) ↔
      denoteTerm ν t = denoteTerm ν u := by
  constructor
  · exact denoteFormula_eq_implies_denoteTerm_eq ν
  · exact denoteFormula_eq_of_denoteTerm_eq hT ν

theorem denoteFormula_top
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ) :
    denoteFormula T ν (.top : Formula Γ) :=
  holds_top (T := T) (ν := ν) hT

@[simp] theorem denoteFormula_bot_iff_false
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ) :
    denoteFormula T ν (.bot : Formula Γ) ↔ False :=
  holds_bot_iff_false (T := T) (ν := ν) hT

theorem not_denoteFormula_bot
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ) :
    ¬ denoteFormula T ν (.bot : Formula Γ) :=
  not_holds_bot (T := T) (ν := ν) hT

@[simp] theorem denoteFormula_not_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ : Formula Γ) :
    denoteFormula T ν (not φ) ↔ ¬ denoteFormula T ν φ :=
  holds_not_iff_not_holds (T := T) (ν := ν) hT φ

@[simp] theorem denoteFormula_and_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ ψ : Formula Γ) :
    denoteFormula T ν (and φ ψ) ↔
      denoteFormula T ν φ ∧ denoteFormula T ν ψ :=
  holds_and_iff (T := T) (ν := ν) hT φ ψ

@[simp] theorem denoteFormula_or_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ ψ : Formula Γ) :
    denoteFormula T ν (or φ ψ) ↔
      denoteFormula T ν φ ∨ denoteFormula T ν ψ :=
  holds_or_iff (T := T) (ν := ν) hT φ ψ

theorem denoteFormula_imp_mp
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    {φ ψ : Formula Γ} :
    denoteFormula T ν (imp φ ψ) →
      denoteFormula T ν φ →
        denoteFormula T ν ψ :=
  holds_imp_mp (T := T) (ν := ν) hT

@[simp] theorem denoteFormula_imp_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : Assignment T Γ)
    (φ ψ : Formula Γ) :
    denoteFormula T ν (imp φ ψ) ↔
      (denoteFormula T ν φ → denoteFormula T ν ψ) :=
  holds_imp_iff (T := T) (ν := ν) hT φ ψ

@[simp] theorem denoteFormula_all_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (ν : Assignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    denoteFormula T ν (.all φ) ↔
      ∀ c : Carrier T σ, denoteFormula T (ClassAssignment.extend ν c) φ :=
  holds_all_iff_forall_class_extensions
    (T := T) hT hEx hAll ν φ

@[simp] theorem denoteFormula_ex_iff
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (ν : Assignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    denoteFormula T ν (.ex φ) ↔
      ∃ c : Carrier T σ, denoteFormula T (ClassAssignment.extend ν c) φ :=
  holds_ex_iff_exists_class_witness
    (T := T) hT hEx hAll ν φ

end CanonicalFrame

end Mettapedia.AutoBooks.Codex.Henkin1950
