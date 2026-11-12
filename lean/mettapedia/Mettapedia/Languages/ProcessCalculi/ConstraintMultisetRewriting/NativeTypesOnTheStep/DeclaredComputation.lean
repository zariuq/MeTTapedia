import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.MatchAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Fundamental

/-!
# Declared computing rules: conversion extended in the style of λΠ-modulo

A package's conversion already carries a declared root computation (`Rules.computation`), closed
under renaming and substitution, and typed equality uses it only between terms of one type
(`Equal.root`). Here a program **declares** computing rules: the package's computation is joined
with the declared one (`declare`). This is Dedukti's λΠ-modulo discipline: conversion is
β, η and the declared rewrite rules.

* **Declaring preserves typing** (`sub_declare`, `typed_declare`, `equal_declare`): the old package
  is a sub-package of the declared one, so every typing and equality judgment survives. This is
  forward preservation only, not conservativity: a declaration adds equalities, so terms that had no
  typing may gain one, and stores may become solvable. Refutations and non-typings are not kept.
* **The level model carries over unchanged** (`declareLevels`): it does not mention computation.
* **Coherence: telling an instance of a computing rule changes nothing observable**
  (`tell_computing_equivalent`): an equation between the two sides of a declared step at one type
  is solved by every substitution, so adding it to a store keeps the solutions. On the dependent full
  step, a firing that tells it in addition is admitted exactly when the firing without it is
  (`admits_tellMore_iff`, `admitsAfterMatch_tellMore_iff`), and the results have the same frame,
  occurrences and rows and knowledge with the same solutions (`result_tellMore`).

**What a declaration must satisfy.** Typed equality applies a declared step only between two terms
of one type, so a declaration cannot make an ill-typed term typed. It can identify distinct values:
soundness of the knowledge needs uniqueness of normal forms, that is confluence of the declared
rules with β, and termination is what makes conversion decidable. `RootDeterministic` is the
decidable part of the check that the vector instance runs: no term has two different declared
reducts at its root.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing relabel)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head : Type}

/-! ## Declaring computing rules -/

section Declare

/-- Two root computations side by side: a step of either. -/
def joinComputation (c d : RootComputation Head) : RootComputation Head where
  step l r := c.step l r ∨ d.step l r
  rename := by
    intro n m ρ left right h
    exact h.elim (fun h => Or.inl (c.rename ρ h)) (fun h => Or.inr (d.rename ρ h))
  substitute := by
    intro n m σ left right h
    exact h.elim (fun h => Or.inl (c.substitute σ h)) (fun h => Or.inr (d.substitute σ h))

/-- **Declaring computing rules** in a package: its conversion is extended by the declared root
steps. -/
def declare (R : Rules Head) (d : RootComputation Head) : Rules Head :=
  { R with computation := joinComputation R.computation d }

/-- **The old package is a sub-package of the declared one.** -/
theorem sub_declare (R : Rules Head) (d : RootComputation Head) : RulesSub R (declare R d) :=
  ⟨id, id, id, id, id, id, Or.inl⟩

/-- The declared steps are steps of the declared package. -/
theorem declare_step {R : Rules Head} {d : RootComputation Head} {n : Nat} {l r : Tm Head n}
    (step : d.step l r) : (declare R d).computation.step l r :=
  Or.inr step

/-- **Typing survives declaring.** -/
theorem typed_declare {R : Rules Head} (d : RootComputation Head) {n : Nat} {Γ : Ctx Head n}
    {t A : Tm Head n} (typed : Typed R Γ t A) : Typed (declare R d) Γ t A :=
  Derivable.mono (sub_declare R d) typed

/-- **Equality survives declaring.** -/
theorem equal_declare {R : Rules Head} (d : RootComputation Head) {n : Nat} {Γ : Ctx Head n}
    {a b A : Tm Head n} (equal : Equal R Γ a b A) : Equal (declare R d) Γ a b A :=
  Derivable.mono (sub_declare R d) equal

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- **The level model carries over**: it mentions no computation. -/
def declareLevels {R : Rules Head} (levels : LevelModel R L) (d : RootComputation Head) :
    LevelModel (declare R d) L := { levels with }

/-- **No term has two different declared reducts at its root.** -/
def RootDeterministic (d : RootComputation Head) : Prop :=
  ∀ {n : Nat} (l r r' : Tm Head n), d.step l r → d.step l r' → r = r'

end Declare

/-! ## Coherence: telling an instance of a computing rule -/

section Coherence

variable {L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)

/-- The equation between the two sides of a declared step, at one type. -/
def computingEquation {Γ : Context rules} (A : TypeOver Γ) {l r : Tm Head Γ.arity}
    (tl : Typed rules Γ.raw l A.code) (tr : Typed rules Γ.raw r A.code) : Equation (TotalTerm Γ) :=
  (⟨A, ⟨l, tl⟩⟩, ⟨A, ⟨r, tr⟩⟩)

/-- **Every substitution solves an instance of a computing rule.** -/
theorem computing_solves {Γ Θ : Context rules} (A : TypeOver Γ) {l r : Tm Head Γ.arity}
    (step : rules.computation.step l r) (tl : Typed rules Γ.raw l A.code)
    (tr : Typed rules Γ.raw r A.code) (τ : Θ ⟶ Γ) :
    (frames levels).Solves τ (computingEquation A tl tr) :=
  ⟨(A.reindex τ).isType.refl,
    .root (rules.computation.substitute τ.substitution step) (tl.substitute τ.typed) (tr.substitute τ.typed)⟩

/-- **Coherence for stores**: telling an instance of a computing rule keeps the solutions. -/
theorem tell_computing_equivalent {Γ : Context rules} (I : EquationStore (TotalTerm Γ))
    (A : TypeOver Γ) {l r : Tm Head Γ.arity} (step : rules.computation.step l r)
    (tl : Typed rules Γ.raw l A.code) (tr : Typed rules Γ.raw r A.code) :
    (frames levels).Equivalent (I ++ [computingEquation A tl tr]) I := by
  intro Θ τ
  rw [Frames.models_append]
  constructor
  · exact fun solved => solved.1
  · intro solved
    refine ⟨solved, fun e member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    exact computing_solves levels A step tl tr τ

/-- The comprehension does not change. -/
theorem solutions_tell_computing {Γ : Context rules} (I : EquationStore (TotalTerm Γ))
    (A : TypeOver Γ) {l r : Tm Head Γ.arity} (step : rules.computation.step l r)
    (tl : Typed rules Γ.raw l A.code) (tr : Typed rules Γ.raw r A.code) :
    solutions levels (I ++ [computingEquation A tl tr]) = solutions levels I := by
  ext Θ τ
  exact tell_computing_equivalent levels I A step tl tr Θ.unop τ

variable {O : Type} [DecidableEq O]

/-- A firing that tells one more equation. -/
abbrev tellMore {s : State rules O} (f : Firing levels s) (e : Equation (TotalTerm f.helpers.frame)) :
    Firing levels s :=
  { f with tells := f.tells ++ [e] }

omit [DecidableEq O] in
theorem information_tellMore {s : State rules O} (f : Firing levels s)
    (e : Equation (TotalTerm f.helpers.frame)) :
    (tellMore levels f e).information = f.information ++ [e] := by
  simp only [tellMore, Firing.information, List.append_assoc]
  rfl

/-- **Coherence on the step**: the present step admits a firing that also tells an instance of a
computing rule exactly when it admits the firing without it. -/
theorem admits_tellMore_iff {s : State rules O} (f : Firing levels s) (A : TypeOver f.helpers.frame)
    {l r : Tm Head f.helpers.frame.arity} (step : rules.computation.step l r)
    (tl : Typed rules f.helpers.frame.raw l A.code) (tr : Typed rules f.helpers.frame.raw r A.code) :
    (DependentFull.step levels O).Admits (tellMore levels f (computingEquation A tl tr)) ↔
      (DependentFull.step levels O).Admits f := by
  have same := tell_computing_equivalent levels f.information A step tl tr
  have info := information_tellMore levels f (computingEquation A tl tr)
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    rw [info] at solvable holds
    exact ⟨shapes, enabled, same.solvable_iff.mp solvable, (same.entails_iff _).mp holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    refine ⟨shapes, enabled, ?_, ?_⟩
    · rw [info]
      exact same.solvable_iff.mpr solvable
    · rw [info]
      exact (same.entails_iff _).mpr holds

/-- ... and so does admission after the match. -/
theorem admitsAfterMatch_tellMore_iff {s : State rules O} (f : Firing levels s)
    (A : TypeOver f.helpers.frame) {l r : Tm Head f.helpers.frame.arity}
    (step : rules.computation.step l r) (tl : Typed rules f.helpers.frame.raw l A.code)
    (tr : Typed rules f.helpers.frame.raw r A.code) :
    AdmitsAfterMatch levels (tellMore levels f (computingEquation A tl tr)) ↔ AdmitsAfterMatch levels f := by
  have same := tell_computing_equivalent levels f.information A step tl tr
  have info := information_tellMore levels f (computingEquation A tl tr)
  have same' : (frames levels).Equivalent (tellMore levels f (computingEquation A tl tr)).information
      f.information := by
    rw [info]
    exact same
  have typing : ∀ m : Make f.helpers.frame,
      TypedAfterMatch levels (tellMore levels f (computingEquation A tl tr)).information m ↔
        TypedAfterMatch levels f.information m := by
    intro m
    rw [typedAfterMatch_iff, typedAfterMatch_iff]
    constructor
    · exact fun typed Θ τ solved => typed Θ τ ((same' Θ τ).mpr solved)
    · exact fun typed Θ τ solved => typed Θ τ ((same' Θ τ).mp solved)
  constructor
  · rintro ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩
    rw [info] at solvable holds
    exact ⟨⟨a, b, c, d, fun m member => (typing m.2).mp (typed m member)⟩, enabled,
      same.solvable_iff.mp solvable, (same.entails_iff _).mp holds⟩
  · rintro ⟨⟨a, b, c, d, typed⟩, enabled, solvable, holds⟩
    refine ⟨⟨a, b, c, d, fun m member => (typing m.2).mpr (typed m member)⟩, enabled, ?_, ?_⟩
    · rw [info]
      exact same.solvable_iff.mpr solvable
    · rw [info]
      exact (same.entails_iff _).mpr holds

/-- **The results agree on everything observable**: frame, occurrences and rows are the same, and
the knowledge has the same solutions. -/
theorem result_tellMore {s : State rules O} (f : Firing levels s) (A : TypeOver f.helpers.frame)
    {l r : Tm Head f.helpers.frame.arity} (step : rules.computation.step l r)
    (tl : Typed rules f.helpers.frame.raw l A.code) (tr : Typed rules f.helpers.frame.raw r A.code)
    (admitted : (DependentFull.step levels O).Admits (tellMore levels f (computingEquation A tl tr)))
    (admitted' : (DependentFull.step levels O).Admits f) :
    ((DependentFull.step levels O).result _ admitted).frame = ((DependentFull.step levels O).result f admitted').frame ∧
      ((DependentFull.step levels O).result _ admitted).present =
        ((DependentFull.step levels O).result f admitted').present ∧
      ((DependentFull.step levels O).result _ admitted).label = ((DependentFull.step levels O).result f admitted').label ∧
      (frames levels).Equivalent ((DependentFull.step levels O).result _ admitted).knowledge
        ((DependentFull.step levels O).result f admitted').knowledge := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (frames levels).Equivalent (tellMore levels f (computingEquation A tl tr)).information f.information
  rw [information_tellMore]
  exact tell_computing_equivalent levels f.information A step tl tr

end Coherence

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.sub_declare
#print axioms NativeTypesOnTheStep.typed_declare
#print axioms NativeTypesOnTheStep.equal_declare
#print axioms NativeTypesOnTheStep.declareLevels
#print axioms NativeTypesOnTheStep.computing_solves
#print axioms NativeTypesOnTheStep.tell_computing_equivalent
#print axioms NativeTypesOnTheStep.solutions_tell_computing
#print axioms NativeTypesOnTheStep.information_tellMore
#print axioms NativeTypesOnTheStep.admits_tellMore_iff
#print axioms NativeTypesOnTheStep.admitsAfterMatch_tellMore_iff
#print axioms NativeTypesOnTheStep.result_tellMore

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
