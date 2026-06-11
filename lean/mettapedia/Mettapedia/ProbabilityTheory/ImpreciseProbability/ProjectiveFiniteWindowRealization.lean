import Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-!
# Finite-Window Realization for Projective Credal Systems

This file supplies the non-circular bridge from finite joint-window feasibility
to the `finiteWindowCompatibleInCarrier` hypothesis consumed by the compact/FIP
projective completion theorem in `ProjectiveCredal`.

Positive example: a finite family of local windows has a genuine joint state
space, a precise prevision on that joint state space, and a carrier realization
whose projected marginals are exactly the joint marginals.

Negative example: individually coherent one-window lower previsions that demand
incompatible values of the same global coordinate cannot satisfy the joint
local-coherence predicate for the two-window family, or cannot satisfy the
carrier-realization predicate.
-/

namespace Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

namespace ProjectiveLocalLowerPrevisionSpec

variable {Window Global : Type*} [LE Window]

/-- Explicit finite joint-window data for a projective local lower-prevision
specification.

For each finite set of windows `u`, `Joint u` is the joint state space on which
finite local assessments are checked.  The `restrict` maps are the only
structure needed to read each member window inside that joint state space. -/
structure FiniteJointWindowSystem
    (S : ProjectiveLocalLowerPrevisionSpec Window Global) where
  Joint : Finset Window → Type*
  restrict :
    ∀ (u : Finset Window) (i : Window), i ∈ u → Joint u → S.cylinders.Local i

namespace FiniteJointWindowSystem

variable {S : ProjectiveLocalLowerPrevisionSpec Window Global}

/-- Pull a local gamble back to a finite joint-window gamble. -/
def jointCylinderGamble
    (J : FiniteJointWindowSystem S) (u : Finset Window)
    (i : Window) (hi : i ∈ u)
    (X : Gamble (S.cylinders.Local i)) : Gamble (J.Joint u) :=
  fun ξ => X (J.restrict u i hi ξ)

/-- Marginalize a finite joint-window precise prevision to one of its member
windows by evaluating pulled-back local gambles. -/
def jointMarginalPrevision
    (J : FiniteJointWindowSystem S) (u : Finset Window)
    (i : Window) (hi : i ∈ u)
    (R : PrecisePrevision (J.Joint u)) :
    PrecisePrevision (S.cylinders.Local i) where
  toFun X := R (J.jointCylinderGamble u i hi X)
  lower_bound := by
    intro X c hc
    exact R.lower_bound (J.jointCylinderGamble u i hi X) c
      (fun ξ => hc (J.restrict u i hi ξ))
  pos_homog := by
    intro r X hr
    exact R.pos_homog r (J.jointCylinderGamble u i hi X) hr
  add := by
    intro X Y
    exact R.add (J.jointCylinderGamble u i hi X)
      (J.jointCylinderGamble u i hi Y)

@[simp] theorem jointMarginalPrevision_apply
    (J : FiniteJointWindowSystem S) (u : Finset Window)
    (i : Window) (hi : i ∈ u)
    (R : PrecisePrevision (J.Joint u))
    (X : Gamble (S.cylinders.Local i)) :
    J.jointMarginalPrevision u i hi R X =
      R (J.jointCylinderGamble u i hi X) :=
  rfl

end FiniteJointWindowSystem

/-- Finite joint-window local coherence.

This is deliberately weaker than global FIP: it only asks for a precise
prevision on each finite joint-window state space whose member-window marginals
dominate the stipulated local lower previsions.  It does not say that the joint
prevision is already realized by a global precise prevision in the carrier. -/
def finiteWindowLocalCoherent
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (J : FiniteJointWindowSystem S) : Prop :=
  ∀ u : Finset Window,
    ∃ R : PrecisePrevision (J.Joint u),
      ∀ i (hi : i ∈ u),
        J.jointMarginalPrevision u i hi R ∈
          dominatingPreciseCompletions (S.localLower i)

/-- Realization of finite joint-window previsions inside a global carrier.

This is the explicit lift/amalgamation assumption: every locally coherent
finite joint prevision has a global carrier realization whose local marginals
agree with the joint marginals on the requested finite window family. -/
def jointPrevisionsRealizedInCarrier
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (J : FiniteJointWindowSystem S)
    (carrier : CredalPrevisionSet Global) : Prop :=
  ∀ (u : Finset Window) (R : PrecisePrevision (J.Joint u)),
    (∀ i (hi : i ∈ u),
      J.jointMarginalPrevision u i hi R ∈
        dominatingPreciseCompletions (S.localLower i)) →
    ∃ P : PrecisePrevision Global,
      P ∈ carrier ∧
        ∀ i (hi : i ∈ u),
          S.cylinders.marginalPrevision i P =
            J.jointMarginalPrevision u i hi R

/-- Finite joint-window coherence plus explicit carrier realization supplies
the finite-window compatibility/FIP hypothesis needed by the compact projective
completion theorem.

The proof is intentionally thin: all mathematical content lives in the two
transparent assumptions above.  In particular, this theorem does not infer
global compatibility from per-window coherence alone. -/
theorem finiteWindowCompatibleInCarrier_of_jointPrevisionsRealizedInCarrier
    (S : ProjectiveLocalLowerPrevisionSpec Window Global)
    (J : FiniteJointWindowSystem S)
    (carrier : CredalPrevisionSet Global)
    (hLocal : S.finiteWindowLocalCoherent J)
    (hRealize : S.jointPrevisionsRealizedInCarrier J carrier) :
    S.finiteWindowCompatibleInCarrier carrier := by
  intro u
  rcases hLocal u with ⟨R, hR⟩
  rcases hRealize u R hR with ⟨P, hPcarrier, hPmarg⟩
  refine ⟨P, hPcarrier, ?_⟩
  intro i hi
  rw [hPmarg i hi]
  exact hR i hi

end ProjectiveLocalLowerPrevisionSpec

end Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal
