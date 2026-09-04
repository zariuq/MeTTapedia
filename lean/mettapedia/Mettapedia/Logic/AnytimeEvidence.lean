/-!
# Monotone finite-stage evidence

An open-ended procedure need not choose a final observation horizon in order
to produce useful finite evidence.  This file isolates the small order-theoretic
interface shared by such procedures.

A `MonotoneCertificate claim` has a proposition saying that the claim has
been certified at each natural-number stage.  Certification is persistent as
the stage grows, and every accepted stage is sound.  `EventuallyComplete`
adds positive completeness: whenever the claim is true, some finite stage
accepts it.  This is intentionally weaker than a total decision procedure.
No conclusion follows merely from the absence of a certificate at a finite
stage.

The interface is independent of an object logic, scheduler, probability
model, or programming language.  Later modules instantiate it with finite
prefix observations and replayed GSLT proof search.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.AnytimeEvidence

/-- Sound evidence which, once visible at a finite stage, remains visible at
every later stage. -/
structure MonotoneCertificate (claim : Prop) where
  acceptsAt : Nat → Prop
  monotone : ∀ {earlier later : Nat}, earlier ≤ later →
    acceptsAt earlier → acceptsAt later
  sound : ∀ {stage : Nat}, acceptsAt stage → claim

namespace MonotoneCertificate

variable {claim : Prop}

/-- A certificate has positive limit-completeness when every true claim is
accepted at some finite stage. -/
def EventuallyComplete (certificate : MonotoneCertificate claim) : Prop :=
  claim → ∃ stage, certificate.acceptsAt stage

/-- Evidence visible at one stage persists at every stage obtained by adding
more finite work. -/
theorem acceptsAt_add (certificate : MonotoneCertificate claim)
    {stage : Nat} (accepted : certificate.acceptsAt stage) (extra : Nat) :
    certificate.acceptsAt (stage + extra) :=
  certificate.monotone (Nat.le_add_right stage extra) accepted

/-- A known finite bound on positive discovery implies eventual
completeness. -/
theorem eventuallyComplete_of_completeBy
    (certificate : MonotoneCertificate claim) (stage : Nat)
    (completeBy : claim → certificate.acceptsAt stage) :
    certificate.EventuallyComplete := by
  intro holds
  exact ⟨stage, completeBy holds⟩

/-- Monotone evidence can be transported along a sound implication without
changing its finite-stage behavior. -/
def map {target : Prop} (certificate : MonotoneCertificate claim)
    (implication : claim → target) : MonotoneCertificate target where
  acceptsAt := certificate.acceptsAt
  monotone := certificate.monotone
  sound accepted := implication (certificate.sound accepted)

/-- Positive completeness is preserved by a logically equivalent change of
the claim. -/
theorem map_eventuallyComplete_iff {target : Prop}
    (certificate : MonotoneCertificate claim) (equivalence : claim ↔ target) :
    (certificate.map equivalence.mp).EventuallyComplete ↔
      certificate.EventuallyComplete := by
  constructor
  · intro complete holds
    exact complete (equivalence.mp holds)
  · intro complete holds
    exact complete (equivalence.mpr holds)

end MonotoneCertificate

/-- A certificate that never accepts is sound for every claim, demonstrating
that soundness alone does not imply positive completeness. -/
def never (claim : Prop) : MonotoneCertificate claim where
  acceptsAt := fun _ => False
  monotone _ impossible := impossible.elim
  sound impossible := impossible.elim

/-- Negative control: the never-accepting certificate for `True` is not
eventually complete. -/
theorem never_true_not_eventuallyComplete :
    ¬ (never True).EventuallyComplete := by
  intro complete
  obtain ⟨stage, accepted⟩ := complete True.intro
  exact accepted

/-! ## Coherent finite obligations -/

/-- A global claim presented as the limit of compatible finite obligations.
Later obligations imply all earlier ones, and the claim holds exactly when
every finite obligation holds.  This is the universal, inverse-limit-shaped
counterpart of a monotone positive certificate. -/
structure CoherentObligationTower (claim : Prop) where
  holdsAt : Nat → Prop
  restrict : ∀ {earlier later : Nat}, earlier ≤ later →
    holdsAt later → holdsAt earlier
  exact : claim ↔ ∀ stage, holdsAt stage

namespace CoherentObligationTower

variable {claim : Prop}

/-- A global proof discharges each finite obligation. -/
theorem holdsAt_of_claim (tower : CoherentObligationTower claim)
    (holds : claim) (stage : Nat) : tower.holdsAt stage :=
  tower.exact.mp holds stage

/-- A later obligation restricts to any stage obtained by removing finite
work. -/
theorem restrict_add (tower : CoherentObligationTower claim)
    {stage : Nat} (holds : tower.holdsAt (stage + 1)) :
    tower.holdsAt stage :=
  tower.restrict (Nat.le_succ stage) holds

end CoherentObligationTower

/-! ## Audited theorem crowns -/

#print axioms MonotoneCertificate.acceptsAt_add
#print axioms MonotoneCertificate.map_eventuallyComplete_iff
#print axioms never_true_not_eventuallyComplete
#print axioms CoherentObligationTower.holdsAt_of_claim
#print axioms CoherentObligationTower.restrict_add

end Mettapedia.Logic.AnytimeEvidence
