import Mettapedia.Logic.LP.TotalUnification

/-!
# Constant restrictions preserved by total unification

A successful most general unifier cannot introduce forbidden constants when
the input equations contain only permitted constants. Variables and function
symbols remain unrestricted. The argument sanitizes constants in a competing
unifier, then uses the actual solver's most-generality theorem: substitution
cannot remove a constant already present in an image of the returned unifier.
-/

namespace Mettapedia.Logic.LP.UnificationRestriction

variable {σ : LPSignature}

/-- Every constant in a term satisfies the restriction. -/
def Respect (safe : σ.constants → Prop) : Term σ → Prop
  | .var _ => True
  | .const constant => safe constant
  | .app _ children => ∀ index, Respect safe (children index)

/-- Replace forbidden constants, leaving variables and all function symbols
unchanged. A permitted fallback is required only by the preservation laws. -/
def sanitize (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) : Term σ → Term σ
  | .var name => .var name
  | .const constant => .const (if safe constant then constant else fallback)
  | .app function children =>
      .app function (fun index => sanitize safe fallback (children index))

theorem sanitize_fixes (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) (term : Term σ) (respected : Respect safe term) :
    sanitize safe fallback term = term := by
  induction term with
  | var name => rfl
  | const constant =>
      change safe constant at respected
      simp only [sanitize, if_pos respected]
  | app function children ih =>
      simp only [sanitize]
      congr 1
      funext index
      exact ih index (respected index)

theorem sanitize_respects (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) (fallbackSafe : safe fallback) (term : Term σ) :
    Respect safe (sanitize safe fallback term) := by
  induction term with
  | var name => trivial
  | const constant =>
      change safe (if safe constant then constant else fallback)
      split
      · assumption
      · exact fallbackSafe
  | app function children ih => exact ih

/-- A substitution cannot erase constants already present in its input. -/
theorem respect_of_apply (safe : σ.constants → Prop) (theta : Subst σ)
    (term : Term σ) (respected : Respect safe (theta.applyTerm term)) :
    Respect safe term := by
  induction term with
  | var name => trivial
  | const constant => exact respected
  | app function children ih =>
      exact fun index => ih index (respected index)

/-- Sanitizing substitution images commutes with applying the substitution,
provided the source term is sanitized as well. -/
theorem sanitize_apply (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) (theta : Subst σ) (term : Term σ) :
    sanitize safe fallback (theta.applyTerm term) =
      Subst.applyTerm (fun name => sanitize safe fallback (theta name))
        (sanitize safe fallback term) := by
  induction term with
  | var name => rfl
  | const constant => rfl
  | app function children ih =>
      simp only [Subst.applyTerm, sanitize]
      congr 1
      funext index
      exact ih index

/-- On restricted equations, sanitizing any unifier yields another unifier. -/
theorem sanitize_unifies (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) (equations : List (Term σ × Term σ))
    (theta : Subst σ) (unifies : Unifies theta equations)
    (inputs : ∀ equation ∈ equations,
      Respect safe equation.1 ∧ Respect safe equation.2) :
    Unifies (fun name => sanitize safe fallback (theta name)) equations := by
  intro equation member
  have cleaned := congrArg (sanitize safe fallback) (unifies equation member)
  rw [sanitize_apply, sanitize_apply,
    sanitize_fixes safe fallback equation.1 (inputs equation member).1,
    sanitize_fixes safe fallback equation.2 (inputs equation member).2] at cleaned
  exact cleaned

/-- The actual total solver preserves a constant restriction in every returned
substitution image. The fallback is an explicit permitted constant; no
inhabitance of the constant type is silently assumed. -/
theorem unifyTotal_respects (safe : σ.constants → Prop) [DecidablePred safe]
    (fallback : σ.constants) (fallbackSafe : safe fallback)
    [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (equations : List (Term σ × Term σ)) (theta : Subst σ)
    (accepted : unifyTotal equations = some theta)
    (inputs : ∀ equation ∈ equations,
      Respect safe equation.1 ∧ Respect safe equation.2) :
    ∀ name, Respect safe (theta name) := by
  let candidate : Subst σ := fun name => sanitize safe fallback (theta name)
  have candidateUnifies : Unifies candidate equations :=
    sanitize_unifies safe fallback equations theta
      (unifyTotal_sound equations theta accepted) inputs
  obtain ⟨residual, factors⟩ :=
    unifyTotal_mgu equations theta accepted candidate candidateUnifies
  intro name
  have respected : Respect safe (candidate name) :=
    sanitize_respects safe fallback fallbackSafe (theta name)
  rw [factors name] at respected
  exact respect_of_apply safe residual (theta name) respected

/-! Small controls distinguish constant restriction from unifiability. -/

namespace Controls

private abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 1

private def allowed (constant : signature.constants) : Prop := constant = 0

private instance : DecidablePred allowed := fun constant => inferInstanceAs (Decidable (constant = 0))
private instance : DecidableEq signature.vars := inferInstanceAs (DecidableEq Nat)
private instance : DecidableEq signature.constants := inferInstanceAs (DecidableEq Nat)
private instance : DecidableEq signature.functionSymbols := inferInstanceAs (DecidableEq Unit)

theorem nested_sanitize :
    sanitize allowed 0 (.app () (fun _ => .const 1)) =
      .app () (fun _ => .const 0) := by
  simp [sanitize, allowed]

/-- A clean equation really has a successful actual solver result whose every
image is clean, including variables absent from the equation. -/
theorem permitted_equation :
    ∃ theta : Subst signature,
      unifyTotal (σ := signature) [(.var 0, .const 0)] = some theta ∧
        ∀ name, Respect allowed (theta name) := by
  obtain ⟨theta, accepted⟩ :=
    unifyTotal_complete (σ := signature) (equations := [(.var 0, .const 0)])
      ⟨Subst.single 0 (.const 0), by
        intro equation member
        simp only [List.mem_singleton] at member
        subst equation
        simp [Subst.applyTerm, Subst.single]⟩
  refine ⟨theta, accepted, unifyTotal_respects allowed 0 rfl _ theta accepted ?_⟩
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  exact ⟨trivial, rfl⟩

/-- Forbidden constants do not make equations unifiable only by clean images:
the input restriction is essential, and soundness forces the bad image here. -/
theorem forbidden_equation (theta : Subst signature)
    (accepted : unifyTotal (σ := signature) [(.var 0, .const 1)] = some theta) :
    ¬ Respect allowed (theta 0) := by
  have assigned := unifyTotal_sound _ theta accepted (.var 0, .const 1)
    (List.mem_singleton_self _)
  change theta 0 = .const 1 at assigned
  rw [assigned]
  simp [Respect, allowed]

/-- Merely solving clean equations is insufficient: an arbitrary unifier may
assign a forbidden constant to a variable absent from those equations. -/
theorem unifier_alone_insufficient :
    Unifies (Subst.single (σ := signature) 0 (.const 1)) [(.const 0, .const 0)] ∧
      ¬ Respect allowed (Subst.single (σ := signature) 0 (.const 1) 0) := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    rfl
  · simp [Subst.single, Respect, allowed]

end Controls

#print axioms unifyTotal_respects

end Mettapedia.Logic.LP.UnificationRestriction
