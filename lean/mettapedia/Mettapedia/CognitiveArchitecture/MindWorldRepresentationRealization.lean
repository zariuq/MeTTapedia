import Mettapedia.Cybernetics.MindWorldApproximateFunctor
import Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection

/-!
# Representation and realization are opposite, evidence-distinct interfaces

A world-to-mind path correspondence is a model: it may be partial in use and
approximate in composition.  A mind-to-world realization is an execution
interface: it produces a world effect only from a proof-relevant receipt.
Neither direction determines the other.

The realization below is indexed over the image objects of a representation.
This avoids assuming that every mind object has a decoded world object.  A
covered fragment selects receipts for some represented paths; `Commutes` then
states the nontrivial round-trip equation.  A separate empty realization shows
that representation alone cannot manufacture completion evidence.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.MindWorldRepresentationRealization

open CategoryTheory
open Mettapedia.Cybernetics.MindWorldApproximateFunctor

universe uWorld vWorld uMind vMind uReceipt uCover

variable {World : Type uWorld} [Category.{vWorld} World]
variable {Mind : Type uMind} [Category.{vMind} Mind]

/-! ## Receipt-bearing realization on represented objects -/

/-- A proof-relevant mind-action-to-world-effect interface over the objects
selected by `representation`.  `Receipt action` may be empty: representation
does not imply that an action can be executed. -/
structure ImageRealization
    (representation : PathCorrespondence World Mind) where
  Receipt : {source target : World} →
    (representation.obj source ⟶ representation.obj target) → Type uReceipt
  effect : {source target : World} →
    {action : representation.obj source ⟶ representation.obj target} →
    Receipt action → (source ⟶ target)

namespace ImageRealization

variable {representation : PathCorrespondence World Mind}

/-- The action has at least one execution receipt.  This deliberately says
nothing about which world path the receipt records. -/
def Realizable (realization : ImageRealization representation)
    {source target : World}
    (action : representation.obj source ⟶ representation.obj target) : Prop :=
  Nonempty (realization.Receipt action)

/-- Transport a receipt along equality of mind actions. -/
def castReceipt (realization : ImageRealization representation)
    {source target : World}
    {first second : representation.obj source ⟶ representation.obj target}
    (equality : first = second) :
    realization.Receipt first → realization.Receipt second := by
  intro receipt
  cases equality
  exact receipt

@[simp] theorem effect_castReceipt
    (realization : ImageRealization representation)
    {source target : World}
    {first second : representation.obj source ⟶ representation.obj target}
    (equality : first = second) (receipt : realization.Receipt first) :
    realization.effect (realization.castReceipt equality receipt) =
      realization.effect receipt := by
  cases equality
  rfl

/-- A selected, proof-relevant fragment of world paths for which realization
receipts have actually been supplied. -/
structure CoveredFragment
    (realization : ImageRealization representation) where
  Cover : {source target : World} → (source ⟶ target) → Type uCover
  receipt : {source target : World} → (path : source ⟶ target) →
    Cover path → realization.Receipt (representation.map path)

namespace CoveredFragment

variable {realization : ImageRealization representation}

/-- The representation/realization square commutes on the selected fragment.
Both sides are independently defined: `representation.map` chooses the mind
action, while `realization.effect` reads the supplied execution receipt. -/
def Commutes
    (fragment : CoveredFragment realization) : Prop :=
  ∀ {source target : World} (path : source ⟶ target)
    (covered : fragment.Cover path),
    realization.effect (fragment.receipt path covered) = path

end CoveredFragment

/-! ## Composition of independently received effects -/

/-- A realization whose receipts can be composed without hiding the two
constituent occurrences. -/
structure Compositional
    (representation : PathCorrespondence World Mind)
    extends ImageRealization representation where
  compReceipt : {first middle last : World} →
    {earlier : representation.obj first ⟶ representation.obj middle} →
    {later : representation.obj middle ⟶ representation.obj last} →
    toImageRealization.Receipt earlier →
    toImageRealization.Receipt later →
    toImageRealization.Receipt (earlier ≫ later)
  effect_comp : ∀ {first middle last : World}
    {earlier : representation.obj first ⟶ representation.obj middle}
    {later : representation.obj middle ⟶ representation.obj last}
    (earlierReceipt : toImageRealization.Receipt earlier)
    (laterReceipt : toImageRealization.Receipt later),
    toImageRealization.effect
        (compReceipt earlierReceipt laterReceipt) =
      toImageRealization.effect earlierReceipt ≫
        toImageRealization.effect laterReceipt

namespace Compositional

/-- Compose receipts for mapped world paths.  Exact composition of the
representation is required only at this boundary. -/
def composeMapped
    (realization : Compositional representation)
    (preserves : representation.PreservesComposition)
    {first middle last : World}
    {earlier : first ⟶ middle} {later : middle ⟶ last}
    (earlierReceipt : realization.Receipt (representation.map earlier))
    (laterReceipt : realization.Receipt (representation.map later)) :
    realization.Receipt (representation.map (earlier ≫ later)) :=
  realization.toImageRealization.castReceipt
    (preserves earlier later).symm
    (realization.compReceipt earlierReceipt laterReceipt)

theorem effect_composeMapped
    (realization : Compositional representation)
    (preserves : representation.PreservesComposition)
    {first middle last : World}
    {earlier : first ⟶ middle} {later : middle ⟶ last}
    (earlierReceipt : realization.Receipt (representation.map earlier))
    (laterReceipt : realization.Receipt (representation.map later)) :
    realization.effect
        (realization.composeMapped preserves earlierReceipt laterReceipt) =
      realization.effect earlierReceipt ≫
        realization.effect laterReceipt := by
  simp only [composeMapped, ImageRealization.effect_castReceipt]
  exact realization.effect_comp earlierReceipt laterReceipt

/-- Two commuting receipt squares compose to a commuting square. -/
theorem composed_square_commutes
    (realization : Compositional representation)
    (preserves : representation.PreservesComposition)
    {first middle last : World}
    {earlier : first ⟶ middle} {later : middle ⟶ last}
    (earlierReceipt : realization.Receipt (representation.map earlier))
    (laterReceipt : realization.Receipt (representation.map later))
    (earlierExact : realization.effect earlierReceipt = earlier)
    (laterExact : realization.effect laterReceipt = later) :
    realization.effect
        (realization.composeMapped preserves earlierReceipt laterReceipt) =
      earlier ≫ later := by
  rw [realization.effect_composeMapped preserves,
    earlierExact, laterExact]

end Compositional

/-! ## Canonical covered image and an outside-coverage obstruction -/

/-- The conservative image realization.  A receipt for a mind action retains
the world path whose representation is that action; arbitrary mind actions
need not have receipts. -/
def ofRepresentation
    (representation : PathCorrespondence World Mind) :
    ImageRealization representation where
  Receipt := fun {source target} action =>
    { path : source ⟶ target // representation.map path = action }
  effect := fun receipt => receipt.1

/-- Every represented world path has a canonical image receipt. -/
def representedFragment
    (representation : PathCorrespondence World Mind) :
    CoveredFragment (ofRepresentation representation) where
  Cover := fun _ => PUnit
  receipt := fun path _ => ⟨path, rfl⟩

/-- The canonical image construction gives a genuine covered commuting
square.  This theorem does not claim that an external actuator realizes the
image; it identifies the exact proof obligation such an actuator must meet. -/
theorem representedFragment_commutes
    (representation : PathCorrespondence World Mind) :
    (representedFragment representation).Commutes := by
  intro source target path covered
  rfl

/-- A representation can coexist with an actuator that supplies no execution
receipts at all. -/
def noRealization
    (representation : PathCorrespondence World Mind) :
    ImageRealization representation where
  Receipt := fun _ => Empty
  effect := fun receipt => nomatch receipt

/-- Outside-coverage counterexample: mapping a world path into the mind does
not, by itself, make that action realizable. -/
theorem represented_but_not_realizable
    (representation : PathCorrespondence World Mind)
    {source target : World} (path : source ⟶ target) :
    ¬ (noRealization representation).Realizable (representation.map path) := by
  rintro ⟨receipt⟩
  exact nomatch receipt

/-! ## Explicit approximate-representation bridge -/

/-- Receipt-bearing realization for a defect-bounded representation.  The
approximation budget remains part of the representation and is not reclassified
as execution uncertainty. -/
abbrev ApproximateImageRealization
    (representation : BoundedPathCorrespondence World Mind) :=
  ImageRealization representation.toPathCorrespondence

/-- A bounded approximate representation still has a canonical covered-image
square, one represented path at a time.  No exact composition law is assumed. -/
theorem approximate_representedFragment_commutes
    (representation : BoundedPathCorrespondence World Mind) :
    (representedFragment representation.toPathCorrespondence).Commutes :=
  representedFragment_commutes representation.toPathCorrespondence

/-- Even a defect-bounded representation does not supply actuator receipts. -/
theorem approximate_representation_does_not_imply_realization
    (representation : BoundedPathCorrespondence World Mind)
    {source target : World} (path : source ⟶ target) :
    ¬ (noRealization representation.toPathCorrespondence).Realizable
        (representation.map path) :=
  represented_but_not_realizable representation.toPathCorrespondence path

/-! ## Receipt-semantics anchor -/

/-- The existing effect-history model supplies an independent reminder that
proposal identity is insufficient for successful completion. -/
theorem proposal_equality_does_not_supply_completion :
    Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.proposalOnly
        Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.successful =
      Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.proposalOnly
        Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.withheld ∧
    Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.Completed
        Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.successful ∧
    ¬ Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.Completed
        Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.withheld :=
  Mettapedia.CognitiveArchitecture.Agent.EffectReceiptProjection.same_proposal_can_have_different_completion

#print axioms ImageRealization.effect_castReceipt
#print axioms Compositional.effect_composeMapped
#print axioms Compositional.composed_square_commutes
#print axioms representedFragment_commutes
#print axioms represented_but_not_realizable
#print axioms approximate_representedFragment_commutes
#print axioms approximate_representation_does_not_imply_realization
#print axioms proposal_equality_does_not_supply_completion

end ImageRealization

end Mettapedia.CognitiveArchitecture.MindWorldRepresentationRealization
