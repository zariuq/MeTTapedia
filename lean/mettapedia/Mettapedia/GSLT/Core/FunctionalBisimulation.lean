import Mettapedia.GSLT.Core.GSLT

set_option linter.dupNamespace false

/-!
# Maps that transport bisimilarity

A map between the carriers of two theories carries bisimilar terms to
bisimilar terms when it preserves steps and every step out of an image is, up
to bisimilarity in the target, the image of a step.  Neither injectivity nor
surjectivity is asked: the map may identify terms, and the target may have
terms outside the image.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GSLT

/-- **Zig-zag.**  A step-preserving map whose image steps lift, up to
bisimilarity, transports bisimilarity. -/
theorem bisimilar_map_of_zigzag {source target : GSLT}
    (carrier : source.Term → target.Term)
    (zig : ∀ {left right : source.Term},
      source.Step left right → target.Step (carrier left) (carrier right))
    (zag : ∀ {left : source.Term} {next : target.Term},
      target.Step (carrier left) next →
        ∃ right, source.Step left right ∧ target.Bisimilar (carrier right) next)
    {left right : source.Term} (equivalent : source.Bisimilar left right) :
    target.Bisimilar (carrier left) (carrier right) := by
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ := equivalent
  let transported : target.Term → target.Term → Prop := fun first second =>
    ∃ origin companion, relation origin companion ∧
      target.Bisimilar (carrier origin) first ∧ target.Bisimilar (carrier companion) second
  refine ⟨transported, ⟨?_, ?_⟩, left, right, related,
    target.bisimilar_refl _, target.bisimilar_refl _⟩
  · rintro first second ⟨origin, companion, originRelated, originClose, companionClose⟩
      next firstStep
    obtain ⟨closeRelation, ⟨_, closeBackward⟩, closeRelated⟩ := originClose
    obtain ⟨imageNext, imageStep, imageClose⟩ := closeBackward closeRelated firstStep
    obtain ⟨originNext, originStep, liftedClose⟩ := zag imageStep
    obtain ⟨companionNext, companionStep, nextRelated⟩ := forward originRelated originStep
    obtain ⟨farRelation, ⟨farForward, _⟩, farRelated⟩ := companionClose
    obtain ⟨secondNext, secondStep, secondClose⟩ := farForward farRelated (zig companionStep)
    exact ⟨secondNext, secondStep, originNext, companionNext, nextRelated,
      target.bisimilar_trans liftedClose ⟨closeRelation, ⟨by assumption, closeBackward⟩, imageClose⟩,
      ⟨farRelation, ⟨farForward, by assumption⟩, secondClose⟩⟩
  · rintro first second ⟨origin, companion, originRelated, originClose, companionClose⟩
      next secondStep
    obtain ⟨farRelation, ⟨_, farBackward⟩, farRelated⟩ := companionClose
    obtain ⟨imageNext, imageStep, imageClose⟩ := farBackward farRelated secondStep
    obtain ⟨companionNext, companionStep, liftedClose⟩ := zag imageStep
    obtain ⟨originNext, originStep, nextRelated⟩ := backward originRelated companionStep
    obtain ⟨closeRelation, ⟨closeForward, _⟩, closeRelated⟩ := originClose
    obtain ⟨firstNext, firstStep, firstClose⟩ := closeForward closeRelated (zig originStep)
    exact ⟨firstNext, firstStep, originNext, companionNext, nextRelated,
      ⟨closeRelation, ⟨closeForward, by assumption⟩, firstClose⟩,
      target.bisimilar_trans liftedClose ⟨farRelation, ⟨by assumption, farBackward⟩, imageClose⟩⟩

end Mettapedia.GSLT.GSLT
