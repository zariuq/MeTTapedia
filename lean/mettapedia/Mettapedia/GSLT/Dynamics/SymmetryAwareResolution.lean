import Mettapedia.GSLT.Dynamics.TypedValueGeometry
import Mathlib.Tactic

/-!
# Symmetry-aware resolution

Candidate values can respect a symmetry without determining a unique choice.
This module isolates the missing law at the whole-family resolution boundary.

An equivariant resolver commutes with the authored action on occurrence bags.
If a bag is fixed by a symmetry and the resolver returns one occurrence, that
occurrence must itself be fixed.  Hence a family on which a symmetry exchanges
all candidates cannot be reduced to one candidate by a deterministic
symmetry-respecting resolver.  Retaining the family remains equivariant, and
an explicit seed can supply the additional asymmetry without pretending it was
present in the candidate-local values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.SymmetryAwareResolution

universe uSymmetry uCandidate

variable {Symmetry : Type uSymmetry} {Candidate : Type uCandidate}

/-! ## Equivariance on occurrence bags -/

/-- A candidate-local value respects an authored symmetry when values are
unchanged along every symmetry orbit.  This is the value-side law; it is
strictly weaker than supplying a resolver. -/
def InvariantValuation (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    {Value : Type*} (value : Candidate → Value) : Prop :=
  ∀ (symmetry : Symmetry) (candidate : Candidate),
    value (symmetry • candidate) = value candidate

/-- Two candidates lie in the same authored symmetry orbit. -/
def SameOrbit (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    (first second : Candidate) : Prop :=
  ∃ symmetry : Symmetry, symmetry • first = second

/-- An invariant valuation cannot distinguish candidates in one orbit. -/
theorem invariantValuation_eq_of_sameOrbit
    (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    {Value : Type*} {value : Candidate → Value}
    (invariant : InvariantValuation Symmetry Candidate value)
    {first second : Candidate}
    (sameOrbit : SameOrbit Symmetry Candidate first second) :
    value first = value second := by
  rcases sameOrbit with ⟨symmetry, rfl⟩
  exact (invariant symmetry first).symm

/-- Transport every occurrence through one authored symmetry. -/
def actBag (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    (symmetry : Symmetry) (candidates : Multiset Candidate) :
    Multiset Candidate :=
  candidates.map fun candidate => symmetry • candidate

/-- A whole-family resolver is equivariant when resolving before or after a
symmetry gives the same occurrence bag. -/
def EquivariantResolver (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    (resolver : Multiset Candidate → Multiset Candidate) : Prop :=
  ∀ symmetry candidates,
    resolver (actBag Symmetry Candidate symmetry candidates) =
      actBag Symmetry Candidate symmetry (resolver candidates)

/-- Retaining every occurrence respects every authored symmetry. -/
theorem retain_equivariant
    (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate] :
    EquivariantResolver Symmetry Candidate id := by
  intro symmetry candidates
  rfl

/-- The central obstruction: equivariant singleton resolution of a fixed
family can select only a fixed occurrence. -/
theorem fixed_family_singleton_choice_forces_fixed_occurrence
    (Symmetry : Type uSymmetry) [Group Symmetry]
    (Candidate : Type uCandidate) [MulAction Symmetry Candidate]
    {resolver : Multiset Candidate → Multiset Candidate}
    (equivariant : EquivariantResolver Symmetry Candidate resolver)
    (symmetry : Symmetry) (candidates : Multiset Candidate)
    (fixedFamily : actBag Symmetry Candidate symmetry candidates = candidates)
    (chosen : Candidate) (selectsOne : resolver candidates = {chosen}) :
    symmetry • chosen = chosen := by
  have transported := equivariant symmetry candidates
  rw [fixedFamily, selectsOne] at transported
  have singletonEquality :
      ({chosen} : Multiset Candidate) = {symmetry • chosen} := by
    simpa [actBag] using transported
  exact (Multiset.singleton_inj.mp singletonEquality).symm

/-! ## A two-candidate no-go theorem -/

/-- The nontrivial permutation of two Boolean candidates. -/
def boolSwap : Equiv.Perm Bool :=
  Equiv.swap false true

/-- One occurrence of each Boolean candidate. -/
def boolPair : Multiset Bool :=
  {false, true}

/-- The two-candidate family is fixed as a bag even though its occurrences are
exchanged. -/
theorem boolPair_fixed :
    actBag (Equiv.Perm Bool) Bool boolSwap boolPair = boolPair := by
  decide

/-- Neither Boolean candidate is fixed by the exchange symmetry. -/
theorem boolSwap_no_fixed_occurrence (candidate : Bool) :
    boolSwap • candidate ≠ candidate := by
  cases candidate <;> decide

/-- A symmetry-respecting local value necessarily ties the exchanged pair.
It may describe the family but cannot be the missing symmetry breaker. -/
theorem invariantValuation_ties_boolPair
    {Value : Type*} (value : Bool → Value)
    (invariant : InvariantValuation (Equiv.Perm Bool) Bool value) :
    value false = value true := by
  have transported := invariant boolSwap false
  simpa [boolSwap] using transported.symm

/-- Negative control: there is no deterministic, symmetry-respecting resolver
that returns exactly one member of the symmetric pair. -/
theorem no_equivariant_singleton_resolution_of_boolPair :
    ¬ ∃ resolver : Multiset Bool → Multiset Bool,
      EquivariantResolver (Equiv.Perm Bool) Bool resolver ∧
        ∃ chosen : Bool, resolver boolPair = {chosen} := by
  rintro ⟨resolver, equivariant, chosen, selectsOne⟩
  have fixedOccurrence : boolSwap • chosen = chosen :=
    fixed_family_singleton_choice_forces_fixed_occurrence
      (Equiv.Perm Bool) Bool equivariant boolSwap boolPair
      boolPair_fixed chosen selectsOne
  exact boolSwap_no_fixed_occurrence chosen fixedOccurrence

/-! ## Explicit symmetry-breaking data -/

/-- Selecting from the symmetric pair by an explicit seed.  The seed is part
of the request rather than a hidden order on the bag. -/
def selectBoolPairBySeed (seed : Bool) : Multiset Bool :=
  {seed}

/-- Transporting the seed transports the selected occurrence.  This is the
positive counterpart of the no-go theorem: choice becomes equivariant after
the symmetry-breaking input is represented explicitly. -/
theorem selectBoolPairBySeed_transports (seed : Bool) :
    actBag (Equiv.Perm Bool) Bool boolSwap (selectBoolPairBySeed seed) =
      selectBoolPairBySeed (boolSwap • seed) := by
  simp [actBag, selectBoolPairBySeed]

/-- A uniform unresolved law is invariant even though no deterministic sample
is.  Random sampling may preserve symmetry at the distribution level while an
individual run records a random seed or draw receipt. -/
def uniformBoolWeight (_candidate : Bool) : Rat :=
  1 / 2

theorem uniformBoolWeight_invariant (candidate : Bool) :
    uniformBoolWeight (boolSwap • candidate) = uniformBoolWeight candidate := by
  rfl

/-! ## Axiom audit -/

#print axioms retain_equivariant
#print axioms invariantValuation_eq_of_sameOrbit
#print axioms invariantValuation_ties_boolPair
#print axioms fixed_family_singleton_choice_forces_fixed_occurrence
#print axioms no_equivariant_singleton_resolution_of_boolPair
#print axioms selectBoolPairBySeed_transports
#print axioms uniformBoolWeight_invariant

end Mettapedia.GSLT.Dynamics.SymmetryAwareResolution
