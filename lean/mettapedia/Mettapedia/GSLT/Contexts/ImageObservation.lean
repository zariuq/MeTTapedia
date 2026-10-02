import Mettapedia.GSLT.Contexts.ContextMorphism

/-!
# What the image of the source's observers sees

A morphism compares the images of two terms by the images of the source's
contexts.  Two questions about that comparison are answered here.

*Is anything lost?*  A map that preserves and reflects transitions reflects
bisimilarity as well as preserving it: two terms are bisimilar as a probe
sees them exactly when their images are bisimilar as the carried probe sees
them.

*Does the target see more?*  The target has its own contexts between the
images of interfaces, and in general they separate images that the images of
the source's contexts do not.  When the map is exhausting they see the same:
bisimilarity over the image of the source's contexts is bisimilarity over
all contexts of the target between images of interfaces.

Together: an exhausting map that preserves and reflects transitions carries
bisimilarity over all contexts of the source to bisimilarity over all
contexts of the target between images of interfaces, and back.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-! ## Reflection of bisimilarity -/

/-- **A map that preserves and reflects transitions reflects what every
probe sees.** -/
theorem bisimilar_of_push_of_transitions (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)}
    (bisimilar : (map.push probe).Bisimilar (index := index) (map.term left)
      (map.term right)) :
    probe.Bisimilar left right := by
  refine ⟨fun index first second =>
    (map.push probe).Bisimilar (index := index) (map.term first) (map.term second),
    ⟨?_, ?_⟩, bisimilar⟩
  · intro origin first second related result observer next transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, imageRelated⟩ :=
      forward pair observer (preserves _ transition)
    obtain ⟨next', step, equivalent⟩ := reflects _ imageStep
    exact ⟨next', step,
      ContextTheory.Probe.bisimilar_of_equations_of_equations
        ((target.equations _).iseqv.refl _) ⟨relation, ⟨forward, backward⟩, imageRelated⟩
        equivalent⟩
  · intro origin first second related result observer next' transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, imageRelated⟩ :=
      backward pair observer (preserves _ transition)
    obtain ⟨next, step, equivalent⟩ := reflects _ imageStep
    exact ⟨next, step,
      ContextTheory.Probe.bisimilar_of_equations_of_equations
        ((target.equations _).iseqv.symm equivalent)
        ⟨relation, ⟨forward, backward⟩, imageRelated⟩ ((target.equations _).iseqv.refl _)⟩

/-- **A map that preserves and reflects transitions neither adds nor loses
bisimilarity**, as any probe sees it. -/
theorem bisimilar_push_iff_of_transitions (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)} :
    (map.push probe).Bisimilar (index := index) (map.term left) (map.term right) ↔
      probe.Bisimilar left right :=
  ⟨map.bisimilar_of_push_of_transitions preserves reflects probe,
    map.bisimilar_push_of_transitions preserves reflects probe⟩

/-- Hosting reflects and preserves what every transported probe observes. -/
theorem Hosting.bisimilar_push_iff (hosting : map.Hosting) (probe : source.Probe)
    {index : probe.Index} {left right : source.Term (probe.interface index)} :
    (map.push probe).Bisimilar (index := index) (map.term left) (map.term right) ↔
      probe.Bisimilar left right :=
  map.bisimilar_push_iff_of_transitions hosting.preserves hosting.reflects probe

/-! ## The contexts of the target between images of interfaces -/

/-- Every context of the target between images of interfaces observes. -/
def targetProbe : target.Probe where
  Index := source.Interface
  interface := map.interface
  Observer := fun origin result => target.Label (map.interface origin) (map.interface result)
  label := fun observer => observer

/-- What all contexts of the target see, its contexts between images of
interfaces see. -/
theorem bisimilar_targetProbe_of_fullProbe {origin : source.Interface}
    {left right : target.Term (map.interface origin)}
    (bisimilar : target.fullProbe.Bisimilar (index := map.interface origin) left right) :
    map.targetProbe.Bisimilar (index := origin) left right := by
  refine ⟨fun index first second =>
    target.fullProbe.Bisimilar (index := map.interface index) first second, ⟨?_, ?_⟩,
    bisimilar⟩
  · intro origin first second related result observer next transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨next', step, nextRelated⟩ :=
      forward pair (target := map.interface result) observer transition
    exact ⟨next', step, relation, ⟨forward, backward⟩, nextRelated⟩
  · intro origin first second related result observer next' transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨next, step, nextRelated⟩ :=
      backward pair (target := map.interface result) observer transition
    exact ⟨next, step, relation, ⟨forward, backward⟩, nextRelated⟩

/-- The images of the source's contexts are among the contexts of the target:
what the contexts of the target see, the images see. -/
theorem bisimilar_push_of_targetProbe {origin : source.Interface}
    {left right : target.Term (map.interface origin)}
    (bisimilar : map.targetProbe.Bisimilar (index := origin) left right) :
    (map.push source.fullProbe).Bisimilar (index := origin) left right := by
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ := bisimilar
  refine ⟨relation, ⟨?_, ?_⟩, related⟩
  · intro origin first second pair result observer next transition
    exact forward pair (target := result) (map.context observer) transition
  · intro origin first second pair result observer next' transition
    exact backward pair (target := result) (map.context observer) transition

/-! ## Exhausting maps -/

/-- Under an exhausting map a context of the target between images of
interfaces acts on every term at its hole as the image of some context of the
source does. -/
theorem Exhausting.label_on_terms (exhausting : map.Exhausting)
    {origin result : source.Interface}
    (observer : target.Label (map.interface origin) (map.interface result)) :
    ∃ label : source.Label origin result, ∀ term : target.Term (map.interface origin),
      (target.equations (map.interface result)).r (target.apply (map.context label) term)
        (target.apply observer term) := by
  obtain ⟨label, agrees⟩ :=
    exhausting (holes := fun _ : Unit => origin) (result := result) observer
  refine ⟨label, fun term => ?_⟩
  obtain ⟨preimage, image⟩ := ContextMap.Exhausting.term_surjective map exhausting term
  exact (target.equations _).iseqv.trans (target.apply_resp (map.context label) image)
    ((target.equations _).iseqv.trans (agrees fun _ => preimage)
      (target.apply_resp observer ((target.equations _).iseqv.symm image)))

/-- **Under an exhausting map the contexts of the target see nothing that the
images of the source's contexts do not.** -/
theorem Exhausting.bisimilar_targetProbe_of_push (exhausting : map.Exhausting)
    {origin : source.Interface} {left right : target.Term (map.interface origin)}
    (bisimilar : (map.push source.fullProbe).Bisimilar (index := origin) left right) :
    map.targetProbe.Bisimilar (index := origin) left right := by
  refine ⟨fun index first second =>
    (map.push source.fullProbe).Bisimilar (index := index) first second, ⟨?_, ?_⟩, bisimilar⟩
  · intro origin first second related result observer next transition
    obtain ⟨label, acts⟩ := Exhausting.label_on_terms map exhausting observer
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, nextEquivalent⟩ :=
      target.rewrites_resp_left ((target.equations _).iseqv.symm (acts first)) transition
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward pair (target := result) label imageStep
    obtain ⟨answer, answerStep, answerEquivalent⟩ :=
      target.rewrites_resp_left (acts second) matchedStep
    exact ⟨answer, answerStep,
      ContextTheory.Probe.bisimilar_of_equations_of_equations nextEquivalent
        ⟨relation, ⟨forward, backward⟩, matchedRelated⟩ answerEquivalent⟩
  · intro origin first second related result observer next' transition
    obtain ⟨label, acts⟩ := Exhausting.label_on_terms map exhausting observer
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, nextEquivalent⟩ :=
      target.rewrites_resp_left ((target.equations _).iseqv.symm (acts second)) transition
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      backward pair (target := result) label imageStep
    obtain ⟨answer, answerStep, answerEquivalent⟩ :=
      target.rewrites_resp_left (acts first) matchedStep
    exact ⟨answer, answerStep,
      ContextTheory.Probe.bisimilar_of_equations_of_equations
        ((target.equations _).iseqv.symm answerEquivalent)
        ⟨relation, ⟨forward, backward⟩, matchedRelated⟩
        ((target.equations _).iseqv.symm nextEquivalent)⟩

/-- **Exhausting: bisimilarity over the image of the source's contexts is
bisimilarity over the contexts of the target.** -/
theorem Exhausting.bisimilar_targetProbe_iff (exhausting : map.Exhausting)
    {origin : source.Interface} {left right : target.Term (map.interface origin)} :
    map.targetProbe.Bisimilar (index := origin) left right ↔
      (map.push source.fullProbe).Bisimilar (index := origin) left right :=
  ⟨map.bisimilar_push_of_targetProbe, Exhausting.bisimilar_targetProbe_of_push map exhausting⟩

/-- **An exhausting map that preserves and reflects transitions carries
bisimilarity over all contexts of the source to bisimilarity over the
contexts of the target, and back.** -/
theorem Exhausting.bisimilar_targetProbe_iff_source (exhausting : map.Exhausting)
    (preserves : map.PreservesTransitions) (reflects : map.ReflectsTransitions)
    {origin : source.Interface} {left right : source.Term origin} :
    map.targetProbe.Bisimilar (index := origin) (map.term left) (map.term right) ↔
      source.fullProbe.Bisimilar (index := origin) left right :=
  (Exhausting.bisimilar_targetProbe_iff map exhausting).trans
    (map.bisimilar_push_iff_of_transitions preserves reflects source.fullProbe)

end ContextMap

/-- **An exhausting morphism preserves bisimilarity over all contexts**, the
bisimilarity of the target being computed over all its contexts between
images of interfaces: for such a morphism the restriction to the image of the
source's contexts changes nothing. -/
theorem ContextMorphism.preserves_targetProbe {source target : ContextTheory.{u}}
    (morphism : ContextMorphism source target) (exhausting : morphism.Exhausting)
    {origin : source.Interface} {left right : source.Term origin}
    (bisimilar : source.fullProbe.Bisimilar (index := origin) left right) :
    morphism.targetProbe.Bisimilar (index := origin) (morphism.term left)
      (morphism.term right) :=
  ContextMap.Exhausting.bisimilar_targetProbe_of_push morphism.toContextMap exhausting
    (morphism.preserves_full bisimilar)

end Mettapedia.GSLT
