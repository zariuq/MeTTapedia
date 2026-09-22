import Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Finite-support binding spaces

A finite-support multiplicity space supplies its own complete, duplicate-free
candidate enumeration. Its query is a MeTTaIL pattern, and its answer is the
bag of binding maps returned by the actual matcher, weighted by stored atom
multiplicity. The resulting extraction is additive under source union and so
is a world-model reading without an external candidate-list parameter.

This certifies the abstract finite-support implementation, not the candidate
index or scoping rules of a particular MeTTa runtime.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.WMCalculusAdditiveReading
open Mettapedia.PLN.WorldModel.WMCalculusNativeBindingSpace

/-- A finite-support bag of authored patterns. -/
abbrev FinitePatternSpace := Pattern →₀ ℕ

noncomputable instance : EvidenceType FinitePatternSpace := by
  classical
  exact {}

/-- The complete candidate list supplied by the support of a finite bag. -/
noncomputable def indexedCandidates (space : FinitePatternSpace) : List Pattern :=
  space.support.toList

/-- Every stored atom is enumerated once. -/
theorem indexedCandidates_nodup (space : FinitePatternSpace) :
    (indexedCandidates space).Nodup := by
  classical
  exact Finset.nodup_toList space.support

/-- Candidate enumeration is exact for positive stored multiplicity. -/
theorem mem_indexedCandidates_iff (space : FinitePatternSpace) (atom : Pattern) :
    atom ∈ indexedCandidates space ↔ 0 < space atom := by
  classical
  simp [indexedCandidates, Finsupp.mem_support_iff]

/-- The finite-support backend's matcher-produced bag of bindings. -/
noncomputable def indexedBindingAnswers (space : FinitePatternSpace)
    (pattern : Pattern) : BindingBag :=
  fun bindings =>
    space.sum (fun atom count => count * bindingMultiplicity pattern atom bindings)

/-- Self-enumeration agrees with the explicit-candidate WM extraction. -/
theorem indexedBindingAnswers_eq_bindingAnswers
    (space : FinitePatternSpace) (pattern : Pattern) :
    indexedBindingAnswers space pattern =
      bindingAnswers (fun atom => space atom) (pattern, indexedCandidates space) := by
  classical
  funext bindings
  simp [indexedBindingAnswers, indexedCandidates, bindingAnswers, Finsupp.sum]

/-- Source union adds complete binding bags, including all matcher solutions. -/
theorem indexedBindingAnswers_add
    (first second : FinitePatternSpace) (pattern : Pattern) :
    indexedBindingAnswers (first + second) pattern =
      indexedBindingAnswers first pattern + indexedBindingAnswers second pattern := by
  classical
  funext bindings
  exact Finsupp.sum_add_index'
    (h := fun atom count => count * bindingMultiplicity pattern atom bindings)
    (by intro atom; simp)
    (by intro atom left right; simp [Nat.add_mul])

/-- This backend satisfies the existing additive world-model interface. -/
noncomputable instance :
    AdditiveWorldModel FinitePatternSpace Pattern BindingBag where
  extract := indexedBindingAnswers
  extract_add := indexedBindingAnswers_add

/-- The finite-support reading inherits the world-model calculus laws. -/
theorem indexedReading_coreLaws
    (world : String → FinitePatternSpace) (query : String → Pattern) :
    (additiveReading (Ev := BindingBag) world query).CoreLaws :=
  additiveReading_coreLaws world query

/-- A singleton atom answers a variable pattern with its stored multiplicity. -/
theorem singleton_variable_binding_count (atom : Pattern) (count : ℕ) :
    indexedBindingAnswers (Finsupp.single atom count) (.fvar "x")
      [("x", atom)] = count := by
  classical
  simp [indexedBindingAnswers, bindingMultiplicity, matchPattern]

/-- A variable-pattern query reads the exact multiplicity of every stored
atom from the indexed binding bag, without naming candidates in the query. -/
theorem variable_binding_recovers_multiplicity
    (space : FinitePatternSpace) (atom : Pattern) :
    indexedBindingAnswers space (.fvar "x") [("x", atom)] = space atom := by
  classical
  change space.sum (fun candidate count =>
    count * bindingMultiplicity (.fvar "x") candidate [("x", atom)]) = space atom
  rw [Finsupp.sum_eq_single atom]
  · simp [bindingMultiplicity, matchPattern]
  · intro candidate _ different
    simp [bindingMultiplicity, matchPattern, different]
  · intro _
    simp

/-- Indexed binding observations distinguish exactly the finite-support
states. This is behavioral equality for all pattern queries, not literal
equality of arbitrary world-model backends. -/
theorem indexedSpaceAgree_iff_eq
    (world : String → FinitePatternSpace) (query : String → Pattern)
    (first second : FinitePatternSpace) :
    (additiveReading (Ev := BindingBag) world query).Agree .state first second ↔
      first = second := by
  constructor
  · intro agree
    ext atom
    have answers := agree (.fvar "x")
    change indexedBindingAnswers first (.fvar "x") =
      indexedBindingAnswers second (.fvar "x") at answers
    have count := congrArg (fun bag : BindingBag => bag [("x", atom)]) answers
    simpa only [variable_binding_recovers_multiplicity] using count
  · intro equal
    subst second
    intro pattern
    rfl

/-- An incomplete candidate list misses a real binding answer. -/
theorem missing_candidate_loses_binding (atom : Pattern) :
    bindingAnswers (fun _ => 1) (.fvar "x", []) [("x", atom)] = 0 ∧
      indexedBindingAnswers (Finsupp.single atom 1) (.fvar "x")
        [("x", atom)] = 1 := by
  constructor
  · rfl
  · exact singleton_variable_binding_count atom 1

/-- Duplicate candidates double-count one stored occurrence. -/
theorem duplicate_candidate_overcounts (atom : Pattern) :
    bindingAnswers (fun _ => 1) (.fvar "x", [atom, atom])
        [("x", atom)] = 2 ∧
      indexedBindingAnswers (Finsupp.single atom 1) (.fvar "x")
        [("x", atom)] = 1 := by
  constructor
  · simp [bindingAnswers, bindingMultiplicity, matchPattern]
  · exact singleton_variable_binding_count atom 1

end Mettapedia.PLN.WorldModel.WMCalculusIndexedBindingSpace
