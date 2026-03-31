import Mettapedia.Computability.PNP.SharedABTargetInterface

/-!
# P vs NP grassroots: canonical raw `(a, b)` specialization of the target route

This file backward-chains from the shared-basis target interface to the closest
fully concrete raw-bit route.

The shared-basis route asks for:

* quotient invariance under the reduced raw visible surface `(a, b)`,
* one shared affine basis on that reduced surface,
* realization by one downstream combiner class.

Here we specialize the shared basis to the canonical coordinate basis on the raw
`2k` visible bits.  That turns the generic target burden into the simpler raw
decision-list burden already studied elsewhere:

* quotient invariance, and
* realization by a fixed-order decision list on the raw `(a, b)` bits.

So this file is a backward-chaining bridge from the clean target interface back
toward the most concrete current route.
-/

namespace Mettapedia.Computability.PNP

section

variable {n : ℕ}

/-- The affine probe selecting one raw visible bit. -/
def coordinateAffineColumn (j : Fin n) : AffineColumnCode n :=
  ((fun i => decide (i = j)), false)

/-- The canonical shared affine basis on `n` raw visible bits. -/
def canonicalAffineBasis (n : ℕ) : Fin n → AffineColumnCode n :=
  fun j => coordinateAffineColumn (n := n) j

lemma coordinateAffineColumn_support
    (a : BitVec n) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter
      fun i => (coordinateAffineColumn (n := n) j).1 i && a i)
      = if a j then {j} else ∅ := by
  by_cases h : a j
  · ext i
    by_cases hij : i = j
    · subst hij
      simp [coordinateAffineColumn, h]
    · simp [coordinateAffineColumn, h, hij]
  · ext i
    by_cases hij : i = j
    · subst hij
      simp [coordinateAffineColumn, h]
    · simp [coordinateAffineColumn, h, hij]

lemma columnParity_coordinateAffineColumn
    (a : BitVec n) (j : Fin n) :
    columnParity (coordinateAffineColumn (n := n) j).1 a = a j := by
  by_cases h : a j
  · rw [columnParity, coordinateAffineColumn_support (n := n) a j, if_pos h]
    simp [h]
  · rw [columnParity, coordinateAffineColumn_support (n := n) a j, if_neg h]
    simp [h]

lemma affineColumnPredict_coordinateAffineColumn
    (a : BitVec n) (j : Fin n) :
    affineColumnPredict (coordinateAffineColumn (n := n) j).1
      (coordinateAffineColumn (n := n) j).2 a = a j := by
  rw [affineColumnPredict, columnParity_coordinateAffineColumn (n := n) a j]
  simp [coordinateAffineColumn]

lemma affineFeatureVector_canonicalAffineBasis
    (a : BitVec n) :
    affineFeatureVector (canonicalAffineBasis n) a = a := by
  funext j
  simp [canonicalAffineBasis, affineFeatureVector,
    affineColumnPredict_coordinateAffineColumn]

end

section

variable {Z : Type*} {k : ℕ}

lemma sharedABAffineDecisionListPredict_canonicalAffineBasis
    (code : SharedAffineDecisionListCode (k + k)) :
    sharedABAffineDecisionListPredict (r := k + k) (k := k)
      (canonicalAffineBasis (k + k)) code
      = abDecisionListPredict (k := k) code := by
  funext x
  rw [sharedABAffineDecisionListPredict, abDecisionListPredict,
    affineFeatureVector_canonicalAffineBasis]
  cases h : firstActiveFeature? (abVisibleBits x) <;> simp

theorem realizedBySharedABAffineDecisionListFamily_canonicalAffineBasis_of_decisionList
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    (hreal : RealizedByABDecisionListFamily (k := k) H) :
    RealizedBySharedABAffineDecisionListFamily (r := k + k) (k := k)
      (canonicalAffineBasis (k + k)) H := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  calc
    H.predict i = abDecisionListPredict (k := k) code := hi
    _ = sharedABAffineDecisionListPredict (r := k + k) (k := k)
          (canonicalAffineBasis (k + k)) code := by
            symm
            exact sharedABAffineDecisionListPredict_canonicalAffineBasis
              (k := k) code

section

variable [Inhabited Z]

/-- The canonical raw-bit decision-list route is a concrete instance of the
shared-basis target interface. -/
def canonicalABDecisionListTargetData
    {Index : Type*}
    (G : ExactVisibleSwitchedFamily Z k Index)
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedByABDecisionListFamily (k := k)
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    SharedABDecisionListTargetData (Z := Z) (r := k + k) (k := k) (Index := Index) G where
  features := canonicalAffineBasis (k + k)
  invariant := hinv
  realized :=
    realizedBySharedABAffineDecisionListFamily_canonicalAffineBasis_of_decisionList
      (k := k) hreal

theorem exactVisibleCompressionTarget_of_invariant_and_canonicalABDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedByABDecisionListFamily (k := k)
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (k + k + 1) := by
  exact
    (canonicalABDecisionListTargetData (Z := Z) (k := k) (Index := Index)
      G hinv hreal).compressionTarget

theorem exactVisibleCompressionTarget_of_invariant_and_canonicalABDecisionList_twoMul
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedByABDecisionListFamily (k := k)
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * k + 1) := by
  simpa [two_mul, Nat.mul_comm, Nat.add_assoc] using
    exactVisibleCompressionTarget_of_invariant_and_canonicalABDecisionList
      (Z := Z) (k := k) hinv hreal

end

end

end Mettapedia.Computability.PNP
