import Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
import Mathlib.Data.Bool.AllAny

/-!
# Deciding the finite profile language of atomless Boolean algebras

Finite Venn-cell profiles are a normal semantic interface for tuples in an
atomless Boolean algebra.  This module gives that interface an explicit
first-order language and a terminating decision function.  An existential
quantifier enumerates finite child profiles, not elements of the semantic
carrier.  The atomless extension theorem proves that every compatible child
profile found by the finite search has a genuine semantic witness.

This is quantifier elimination for the profile language.  A later module must
compile ordinary Boolean-algebra terms and equations into profile formulas
before this can be called quantifier elimination for the full first-order
language of Boolean algebras.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension

universe u

/-- Formulas whose atoms observe whether a selected Venn cell is nonzero.
Quantification adds one de Bruijn-zero Boolean-algebra variable. -/
inductive Formula : Nat -> Type where
  | cellNonzero {arity : Nat} (cell : Cell arity) : Formula arity
  | falsum {arity : Nat} : Formula arity
  | conjunction {arity : Nat} (left right : Formula arity) : Formula arity
  | negation {arity : Nat} (body : Formula arity) : Formula arity
  | existsF {arity : Nat} (body : Formula (arity + 1)) : Formula arity
  deriving DecidableEq

/-- Cold semantics in an arbitrary Boolean algebra. -/
def Satisfies {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> Formula arity -> (Fin arity -> B) -> Prop
  | _, .cellNonzero cell, valuation => cellValue valuation cell ≠ ⊥
  | _, .falsum, _valuation => False
  | _, .conjunction left right, valuation =>
      Satisfies left valuation /\ Satisfies right valuation
  | _, .negation body, valuation => ¬ Satisfies body valuation
  | _, .existsF body, valuation =>
      ∃ value : B, Satisfies body (extendValuation value valuation)

/-! ## Canonical executable enumeration of profiles -/

/-- Remove the head polarity from a cell. -/
def tailCell {arity : Nat} (cell : Cell (arity + 1)) : Cell arity :=
  fun index => cell index.succ

theorem extendCell_head_tail {arity : Nat} (cell : Cell (arity + 1)) :
    extendCell (cell 0) (tailCell cell) = cell := by
  funext index
  refine Fin.cases ?_ (fun _tailIndex => ?_) index
  · rfl
  · rfl

/-- Restrict a child profile to one polarity of its newest variable. -/
def restrictProfile {arity : Nat} (polarity : Bool)
    (profile : Profile (arity + 1)) : Profile arity :=
  fun cell => profile (extendCell polarity cell)

/-- Assemble the two polarity restrictions into one child profile. -/
def combineProfile {arity : Nat}
    (negative positive : Profile arity) : Profile (arity + 1) :=
  fun cell =>
    if cell 0 then positive (tailCell cell) else negative (tailCell cell)

theorem combine_restrictions {arity : Nat}
    (profile : Profile (arity + 1)) :
    combineProfile (restrictProfile false profile)
        (restrictProfile true profile) = profile := by
  funext cell
  cases headValue : cell 0
  · simpa only [combineProfile, headValue, Bool.false_eq_true, ↓reduceIte,
      restrictProfile] using congrArg profile (extendCell_head_tail cell)
  · simpa only [combineProfile, headValue, ↓reduceIte, restrictProfile] using
      congrArg profile (extendCell_head_tail cell)

/-- Every profile is enumerated by recursively choosing its negative and
positive restrictions.  This avoids any noncomputable ordering of a generic
finite type. -/
def allProfiles : (arity : Nat) -> List (Profile arity)
  | 0 => [fun _cell => false, fun _cell => true]
  | arity + 1 =>
      (allProfiles arity).flatMap fun negative =>
        (allProfiles arity).map fun positive =>
          combineProfile negative positive

theorem mem_allProfiles : {arity : Nat} -> (profile : Profile arity) ->
    profile ∈ allProfiles arity
  | 0, profile => by
      let emptyCell : Cell 0 := Fin.elim0
      cases profileValue : profile emptyCell
      · have profileEq : profile = fun _cell => false := by
          funext cell
          rw [Subsingleton.elim cell emptyCell, profileValue]
        simp [allProfiles, profileEq]
      · have profileEq : profile = fun _cell => true := by
          funext cell
          rw [Subsingleton.elim cell emptyCell, profileValue]
        simp [allProfiles, profileEq]
  | arity + 1, profile => by
      rw [← combine_restrictions profile]
      simp only [allProfiles, List.mem_flatMap, List.mem_map]
      exact ⟨restrictProfile false profile,
        mem_allProfiles (restrictProfile false profile),
        restrictProfile true profile,
        mem_allProfiles (restrictProfile true profile), rfl⟩

/-- Finite evaluation on profiles.  Existential quantification is an
exhaustive search over child profiles satisfying the exact projection
equation. -/
def decideAt : {arity : Nat} -> Formula arity -> Profile arity -> Bool
  | _, .cellNonzero cell, profile => profile cell
  | _, .falsum, _profile => false
  | _, .conjunction left right, profile =>
      decideAt left profile && decideAt right profile
  | _, .negation body, profile => !decideAt body profile
  | arity, .existsF body, profile =>
      (allProfiles (arity + 1)).any
        (fun child => decide (project child = profile) && decideAt body child)

/-- The finite evaluator is exact for the independently defined semantics in
every atomless Boolean algebra. -/
theorem decideAt_eq_true_iff_satisfies
    {B : Type u} [BooleanAlgebra B] (gunky : IsGunky B) :
    {arity : Nat} -> (formula : Formula arity) ->
      (valuation : Fin arity -> B) ->
      decideAt formula (profileOf valuation) = true <->
        Satisfies formula valuation
  | _, .cellNonzero cell, valuation =>
      profileOf_eq_true_iff valuation cell
  | _, .falsum, _valuation => by
      simp only [decideAt, Satisfies, Bool.false_eq_true]
  | _, .conjunction left right, valuation => by
      simp only [decideAt, Satisfies, Bool.and_eq_true]
      exact and_congr
        (decideAt_eq_true_iff_satisfies gunky left valuation)
        (decideAt_eq_true_iff_satisfies gunky right valuation)
  | _, .negation body, valuation => by
      simp only [decideAt, Satisfies, Bool.not_eq_true_eq_eq_false]
      rw [← Bool.eq_false_eq_not_eq_true]
      exact not_congr
        (decideAt_eq_true_iff_satisfies gunky body valuation)
  | arity, .existsF body, valuation => by
      simp only [decideAt, List.any_eq_true]
      constructor
      · rintro ⟨child, _member, accepted⟩
        rw [Bool.and_eq_true] at accepted
        have projected : project child = profileOf valuation :=
          of_decide_eq_true accepted.1
        have compatible : Compatible valuation child := projected
        let value := witness gunky valuation child compatible
        refine ⟨value, ?_⟩
        apply (decideAt_eq_true_iff_satisfies gunky body
          (extendValuation value valuation)).mp
        rw [profileOf_witness gunky valuation child compatible]
        exact accepted.2
      · rintro ⟨value, bodySatisfied⟩
        let child : Profile (arity + 1) :=
          profileOf (extendValuation value valuation)
        refine ⟨child, mem_allProfiles child, ?_⟩
        rw [Bool.and_eq_true]
        constructor
        · apply decide_eq_true_eq.mpr
          exact profileOf_extend_projects value valuation
        · exact (decideAt_eq_true_iff_satisfies gunky body
            (extendValuation value valuation)).mpr bodySatisfied

/-- Closed profile formulas have a canonical empty valuation. -/
def emptyValuation {B : Type u} : Fin 0 -> B := Fin.elim0

/-- The finite decision procedure for closed profile formulas. -/
def decideClosed (formula : Formula 0) : Bool :=
  decideAt formula (fun _cell => true)

theorem empty_profile_eq_true
    {B : Type u} [BooleanAlgebra B] [Nontrivial B] :
    profileOf (emptyValuation (B := B)) = fun _cell => true := by
  funext cell
  exact (profileOf_eq_true_iff emptyValuation cell).mpr top_ne_bot

/-- Closed decision is exact in every atomless Boolean algebra. -/
theorem decideClosed_eq_true_iff_satisfies
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) (formula : Formula 0) :
    decideClosed formula = true <->
      Satisfies formula (emptyValuation (B := B)) := by
  rw [decideClosed, ← empty_profile_eq_true (B := B)]
  exact decideAt_eq_true_iff_satisfies gunky formula emptyValuation

/-! ## Positive and negative semantic canaries -/

def emptyCell : Cell 0 := Fin.elim0

def positiveCell : Cell 1 := extendCell true emptyCell

def negativeCell : Cell 1 := extendCell false emptyCell

/-- There exists a value whose positive and negative cells are both
nonzero: equivalently, a proper nonzero part of the unit exists. -/
def splitFormula : Formula 0 :=
  .existsF (.conjunction (.cellNonzero positiveCell)
    (.cellNonzero negativeCell))

theorem splitFormula_decides_true :
    decideClosed splitFormula = true := by
  decide

/-- Every atomless Boolean algebra satisfies the split sentence. -/
theorem splitFormula_holds_in_atomless
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) :
    Satisfies splitFormula (emptyValuation (B := B)) :=
  (decideClosed_eq_true_iff_satisfies gunky splitFormula).mp
    splitFormula_decides_true

/-- Negative canary: the finite two-element Boolean algebra cannot realize
the split profile, so atomlessness is a necessary hypothesis of the decision
theorem. -/
theorem splitFormula_fails_in_bool :
    ¬ Satisfies splitFormula (emptyValuation (B := Bool)) := by
  rintro ⟨value, positiveNonzero, negativeNonzero⟩
  cases value <;>
    simp [positiveCell, negativeCell, emptyCell, Satisfies,
      cellValue, extendValuation, extendCell] at *

#print axioms decideAt_eq_true_iff_satisfies
#print axioms empty_profile_eq_true
#print axioms decideClosed_eq_true_iff_satisfies
#print axioms splitFormula_decides_true
#print axioms splitFormula_holds_in_atomless
#print axioms splitFormula_fails_in_bool

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision
