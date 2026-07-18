import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-!
# Computable canonical section for the pure rho quotient

The shared `Pattern` carrier also contains the optional finite-set extension.
Pure rho is the `hashSet`-free subcarrier.  On that subcarrier, the proved rho
canonicalizer respects structural congruence and therefore descends to a
computable section of the quotient.

This module does not claim a canonical section for the larger extended
carrier.  Its set equations are intentionally outside the pure canonicalizer.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureCanonicalSection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-- The conservative carrier on which the pure rho equational theory has the
proved computable canonical form. -/
abbrev PurePattern := { pattern : Pattern // HashSetFree pattern }

/-- Structural congruence restricted to the pure carrier. -/
def pureEquations : Setoid PurePattern where
  r left right := StructuralCongruence left.1 right.1
  iseqv :=
    { refl := fun pattern => StructuralCongruence.refl pattern.1
      symm := fun relation => StructuralCongruence.symm _ _ relation
      trans := fun first second => StructuralCongruence.trans _ _ _ first second }

namespace PurePattern

/-- Canonicalize a pure pattern while retaining its pure-carrier proof. -/
def canonicalize (pattern : PurePattern) : PurePattern :=
  ⟨Canonical.canonicalize pattern.1,
    (hashSetFree_iff_of_structuralCongruence
      (Canonical.canonicalize_sound pattern.1)).mp pattern.2⟩

@[simp]
theorem canonicalize_value (pattern : PurePattern) :
    pattern.canonicalize.1 = Canonical.canonicalize pattern.1 :=
  rfl

/-- Equivalent pure patterns compute to the same subtype representative. -/
theorem canonicalize_eq_of_equivalent {left right : PurePattern}
    (equivalent : pureEquations.r left right) :
    left.canonicalize = right.canonicalize := by
  apply Subtype.ext
  exact canonicalize_eq_of_structuralCongruence equivalent left.2 right.2

end PurePattern

/-- The pure quotient's representative is computed by rho canonicalization,
not selected by classical choice. -/
def representative : Quotient pureEquations → PurePattern :=
  Quotient.lift PurePattern.canonicalize
    (fun _ _ equivalent => PurePattern.canonicalize_eq_of_equivalent equivalent)

/-- The computed representative belongs to the original equivalence class. -/
theorem representative_spec (equivalenceClass : Quotient pureEquations) :
    Quotient.mk pureEquations (representative equivalenceClass) = equivalenceClass := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro pattern
  apply Quotient.sound
  exact StructuralCongruence.symm _ _
    (Canonical.canonicalize_sound pattern.1)

/-- Section evaluation on an explicit class is computational. -/
@[simp]
theorem representative_mk (pattern : PurePattern) :
    representative (Quotient.mk pureEquations pattern) = pattern.canonicalize :=
  rfl

/-- Re-canonicalizing the representative has no effect. -/
theorem representative_canonical (equivalenceClass : Quotient pureEquations) :
    Canonical.canonicalize (representative equivalenceClass).1 =
      (representative equivalenceClass).1 := by
  refine Quotient.inductionOn equivalenceClass ?_
  intro pattern
  exact Canonical.canonicalize_idempotent pattern.1

/-- Positive control: quote-drop cancellation is computed in the pure
section. -/
theorem representative_quote_drop (name : String) :
    let pattern : PurePattern :=
      ⟨.apply "NQuote" [.apply "PDrop" [.fvar name]], by
        simp [HashSetFree, HashSetFreeList]⟩
    (representative (Quotient.mk pureEquations pattern)).1 = .fvar name := by
  rfl

/-- Negative boundary: a finite-set process cannot inhabit the pure carrier. -/
theorem hashSet_not_pure :
    ¬HashSetFree (.collection .hashSet [.apply "PZero" []] none) := by
  simp [HashSetFree]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureCanonicalSection
