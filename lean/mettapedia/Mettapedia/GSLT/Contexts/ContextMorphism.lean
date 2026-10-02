import Mettapedia.GSLT.Contexts.ContextTheory
import Mathlib.CategoryTheory.Category.Basic

/-!
# Morphisms of theories

A map of theories is a pair: a map on terms and a map on contexts, with the
map on terms commuting with filling up to the static equivalence of the
target.  That one law makes the map on contexts functorial on everything the
map on terms reaches: the image of a plugged context acts on images as the
plugged images do.

A morphism is such a pair that transports transitions and preserves bisimilarity, the bisimilarity of
the target being computed only over the image of the source's observers.  The
law is stated for every probe: what a probe sees in the source, the same
probe carried along the map sees in the target.  The statement for the full
probe is the one about all contexts; the statement for every probe is what
makes morphisms compose.

Faithfulness of the context action, forward transition transport and backward
transition lifting are separate properties.  Hosting requires all three;
faithfulness alone does not establish operational correspondence.  A map is exhausting when every
context of the target between images of interfaces acts on images as the
image of a source context does.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

/-- A map of theories as a pair: a map on terms and a map on contexts. -/
structure ContextMap (source target : ContextTheory.{u}) where
  /-- The map on interfaces. -/
  interface : source.Interface → target.Interface
  /-- The map on terms. -/
  term : {origin : source.Interface} → source.Term origin → target.Term (interface origin)
  /-- The map on contexts. -/
  context : {arity : Type} → {holes : arity → source.Interface} →
    {result : source.Interface} → source.Context holes result →
      target.Context (fun index => interface (holes index)) (interface result)
  term_resp : ∀ {origin : source.Interface} {first second : source.Term origin},
    (source.equations origin).r first second →
      (target.equations (interface origin)).r (term first) (term second)
  /-- The image of a filled context is the image context filled with the
  images, up to the static equivalence. -/
  equivariant : ∀ {arity : Type} {holes : arity → source.Interface}
    {result : source.Interface} (context' : source.Context holes result)
    (filling : (index : arity) → source.Term (holes index)),
    (target.equations (interface result)).r (term (source.fill context' filling))
      (target.fill (context context') fun index => term (filling index))

namespace ContextMap

variable {source middle target : ContextTheory.{u}}

/-- The identity map. -/
def id (theory : ContextTheory.{u}) : ContextMap theory theory where
  interface := fun origin => origin
  term := fun term => term
  context := fun context => context
  term_resp := fun equivalent => equivalent
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- Composition of maps. -/
def comp (second : ContextMap middle target) (first : ContextMap source middle) :
    ContextMap source target where
  interface := fun origin => second.interface (first.interface origin)
  term := fun term => second.term (first.term term)
  context := fun context => second.context (first.context context)
  term_resp := fun equivalent => second.term_resp (first.term_resp equivalent)
  equivariant := fun context filling =>
    (target.equations _).iseqv.trans
      (second.term_resp (first.equivariant context filling))
      (second.equivariant (first.context context) fun index => first.term (filling index))

variable (map : ContextMap source target)

/-- The image of a label applied to an image is the image of the
application. -/
theorem apply_equivariant {origin result : source.Interface}
    (label : source.Label origin result) (term : source.Term origin) :
    (target.equations (map.interface result)).r (map.term (source.apply label term))
      (target.apply (map.context label) (map.term term)) :=
  map.equivariant label fun _ => term

/-! ## Functoriality on the image -/

/-- The image of a hole acts on images as a hole. -/
theorem context_identity_on_image {origin : source.Interface} (term : source.Term origin) :
    (target.equations (map.interface origin)).r
      (target.apply (map.context (source.identity origin)) (map.term term)) (map.term term) := by
  have image := map.apply_equivariant (source.identity origin) term
  rw [source.apply_identity] at image
  exact (target.equations _).iseqv.symm image

/-- **The image of a plugged context acts on images as the plugged images.** -/
theorem context_plug_on_image {arity : Type} {holes : arity → source.Interface}
    {result : source.Interface} {innerArity : arity → Type}
    {innerHoles : (index : arity) → innerArity index → source.Interface}
    (context : source.Context holes result)
    (inner : (index : arity) → source.Context (innerHoles index) (holes index))
    (filling : (position : Σ index, innerArity index) →
      source.Term (innerHoles position.1 position.2)) :
    (target.equations (map.interface result)).r
      (target.fill (map.context (source.plug context inner)) fun position =>
        map.term (filling position))
      (target.fill (target.plug (map.context context) fun index => map.context (inner index))
        fun position => map.term (filling position)) := by
  rw [target.fill_plug]
  refine (target.equations _).iseqv.trans
    ((target.equations _).iseqv.symm (map.equivariant (source.plug context inner) filling)) ?_
  rw [source.fill_plug]
  refine (target.equations _).iseqv.trans (map.equivariant context _) ?_
  exact target.fill_resp _ fun index => map.equivariant (inner index) _

/-- The image of a term, as a context with no hole, fills to the image of
the term. -/
theorem context_constant_on_image {holes : Empty → source.Interface}
    {result : source.Interface} (term : source.Term result)
    (filling : (index : Empty) → target.Term (map.interface (holes index))) :
    (target.equations (map.interface result)).r
      (target.fill (map.context (source.constant (holes := holes) term)) filling)
      (map.term term) := by
  have image := map.equivariant (source.constant (holes := holes) term)
    fun index => index.elim
  rw [source.fill_constant] at image
  have same : (fun index : Empty => map.term (index.elim : source.Term (holes index))) =
      filling := funext fun index => index.elim
  rw [same] at image
  exact (target.equations _).iseqv.symm image

/-- Target contexts agree on the terms reached by the map.  Fillings outside
that image are deliberately not quantified over. -/
def ContextEquivOnImage {arity : Type} {holes : arity → source.Interface}
    {result : source.Interface}
    (first second : target.Context (fun index => map.interface (holes index))
      (map.interface result)) : Prop :=
  ∀ filling : (index : arity) → source.Term (holes index),
    (target.equations (map.interface result)).r
      (target.fill first fun index => map.term (filling index))
      (target.fill second fun index => map.term (filling index))

/-- Source context equivalence is carried to agreement on image fillings.
This does not assert agreement on arbitrary new target terms. -/
theorem context_resp_on_image {arity : Type} {holes : arity → source.Interface}
    {result : source.Interface} {first second : source.Context holes result}
    (equivalent : source.ContextEquiv first second) :
    map.ContextEquivOnImage (map.context first) (map.context second) := by
  intro filling
  exact (target.equations _).iseqv.trans
    ((target.equations _).iseqv.symm (map.equivariant first filling))
    ((target.equations _).iseqv.trans (map.term_resp (equivalent filling))
      (map.equivariant second filling))

/-! ## Probes carried along a map -/

/-- Carry a probe along the map: the same observers, acting through the map
on contexts. -/
def push (probe : source.Probe) : target.Probe where
  Index := probe.Index
  interface := fun index => map.interface (probe.interface index)
  Observer := probe.Observer
  label := fun observer => map.context (probe.label observer)

/-- Transitions are preserved along the map on contexts. -/
def PreservesTransitions : Prop :=
  ∀ {origin result : source.Interface} (label : source.Label origin result)
    {term : source.Term origin} {next : source.Term result},
    source.Transition term label next →
      target.Transition (map.term term) (map.context label) (map.term next)

/-- Transitions of an image along the image of a label come from the
source. -/
def ReflectsTransitions : Prop :=
  ∀ {origin result : source.Interface} (label : source.Label origin result)
    {term : source.Term origin} {next : target.Term (map.interface result)},
    target.Transition (map.term term) (map.context label) next →
      ∃ next', source.Transition term label next' ∧
        (target.equations (map.interface result)).r next (map.term next')

theorem preservesTransitions_id (theory : ContextTheory.{u}) :
    (ContextMap.id theory).PreservesTransitions := by
  intro origin result label term next step
  exact step

theorem reflectsTransitions_id (theory : ContextTheory.{u}) :
    (ContextMap.id theory).ReflectsTransitions := by
  intro origin result label term next step
  exact ⟨next, step, (theory.equations _).iseqv.refl _⟩

/-- Forward transport composes at the image of the source label. -/
theorem PreservesTransitions.comp {second : ContextMap middle target}
    {first : ContextMap source middle} (secondPreserves : second.PreservesTransitions)
    (firstPreserves : first.PreservesTransitions) :
    (second.comp first).PreservesTransitions := by
  intro origin result label term next step
  exact secondPreserves (first.context label) (firstPreserves label step)

/-- Backward lifting composes, including the intermediate equation witness. -/
theorem ReflectsTransitions.comp {second : ContextMap middle target}
    {first : ContextMap source middle} (secondReflects : second.ReflectsTransitions)
    (firstReflects : first.ReflectsTransitions) :
    (second.comp first).ReflectsTransitions := by
  intro origin result label term next step
  obtain ⟨middleNext, middleStep, targetEq⟩ := secondReflects (first.context label) step
  obtain ⟨sourceNext, sourceStep, middleEq⟩ := firstReflects label middleStep
  exact ⟨sourceNext, sourceStep,
    (target.equations _).iseqv.trans targetEq (second.term_resp middleEq)⟩

/-- **A map that preserves and reflects transitions preserves what every
probe sees.** -/
theorem bisimilar_push_of_transitions (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)} (bisimilar : probe.Bisimilar left right) :
    (map.push probe).Bisimilar (index := index) (map.term left) (map.term right) := by
  refine ⟨fun index first second =>
    ∃ a b : source.Term (probe.interface index), probe.Bisimilar a b ∧
      (target.equations _).r first (map.term a) ∧ (target.equations _).r second (map.term b),
    ⟨?_, ?_⟩, left, right, bisimilar,
    (target.equations _).iseqv.refl _, (target.equations _).iseqv.refl _⟩
  · rintro origin first second ⟨a, b, related, firstImage, secondImage⟩ result observer next
      transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, nextEquivalent⟩ :=
      target.rewrites_resp_left (target.apply_resp _ firstImage) transition
    obtain ⟨sourceNext, sourceStep, imageEquivalent⟩ := reflects _ imageStep
    obtain ⟨matched, matchedStep, matchedRelated⟩ := forward pair observer sourceStep
    obtain ⟨answer, answerStep, answerEquivalent⟩ :=
      target.rewrites_resp_left
        (target.apply_resp _ ((target.equations _).iseqv.symm secondImage))
        (preserves _ matchedStep)
    exact ⟨answer, answerStep, sourceNext, matched,
      ⟨relation, ⟨forward, backward⟩, matchedRelated⟩,
      (target.equations _).iseqv.trans nextEquivalent imageEquivalent,
      (target.equations _).iseqv.symm answerEquivalent⟩
  · rintro origin first second ⟨a, b, related, firstImage, secondImage⟩ result observer next'
      transition
    obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
    obtain ⟨imageNext, imageStep, nextEquivalent⟩ :=
      target.rewrites_resp_left (target.apply_resp _ secondImage) transition
    obtain ⟨sourceNext, sourceStep, imageEquivalent⟩ := reflects _ imageStep
    obtain ⟨matched, matchedStep, matchedRelated⟩ := backward pair observer sourceStep
    obtain ⟨answer, answerStep, answerEquivalent⟩ :=
      target.rewrites_resp_left
        (target.apply_resp _ ((target.equations _).iseqv.symm firstImage))
        (preserves _ matchedStep)
    exact ⟨answer, answerStep, matched, sourceNext,
      ⟨relation, ⟨forward, backward⟩, matchedRelated⟩,
      (target.equations _).iseqv.symm answerEquivalent,
      (target.equations _).iseqv.trans nextEquivalent imageEquivalent⟩

/-! ## Hosting -/

/-- The map on terms reflects the static equivalence. -/
def ReflectsEquations : Prop :=
  ∀ {origin : source.Interface} {first second : source.Term origin},
    (target.equations (map.interface origin)).r (map.term first) (map.term second) →
      (source.equations origin).r first second

/-- The map on contexts is faithful, contexts being compared by their action
on every term of the target. -/
def Faithful : Prop :=
  ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
    (first second : source.Context holes result),
    target.ContextEquiv (map.context first) (map.context second) →
      source.ContextEquiv first second

theorem faithful_of_reflectsEquations (reflects : map.ReflectsEquations) : map.Faithful := by
  intro arity holes result first second agree filling
  apply reflects
  exact (target.equations _).iseqv.trans (map.equivariant first filling)
    ((target.equations _).iseqv.trans (agree fun index => map.term (filling index))
      ((target.equations _).iseqv.symm (map.equivariant second filling)))

theorem reflectsEquations_of_faithful (faithful : map.Faithful) : map.ReflectsEquations := by
  intro origin first second equivalent
  have contexts : source.ContextEquiv
      (source.constant (holes := fun index : Empty => index.elim) first)
      (source.constant second) := by
    apply faithful
    intro filling
    exact (target.equations _).iseqv.trans (map.context_constant_on_image first filling)
      ((target.equations _).iseqv.trans equivalent
        ((target.equations _).iseqv.symm (map.context_constant_on_image second filling)))
  have filled := contexts fun index => index.elim
  rwa [source.fill_constant, source.fill_constant] at filled

/-- Context faithfulness is the map on terms reflecting static equivalence.
A term is a context with no hole,
so a faithful map on contexts is injective on classes of terms; and the map
on terms commutes with filling, so an injective map on classes is faithful on
every context. -/
theorem faithful_iff_reflectsEquations : map.Faithful ↔ map.ReflectsEquations :=
  ⟨map.reflectsEquations_of_faithful, map.faithful_of_reflectsEquations⟩

/-- A hosting map is faithful on contexts and has operational correspondence
for the transition relations selected by the two theories. -/
structure Hosting : Prop where
  faithful : map.Faithful
  preserves : map.PreservesTransitions
  reflects : map.ReflectsTransitions

/-- Static faithfulness and the two operational laws jointly characterize
hosting; none of the three is silently inferred from another. -/
theorem hosting_iff : map.Hosting ↔
    map.ReflectsEquations ∧ map.PreservesTransitions ∧ map.ReflectsTransitions :=
  ⟨fun hosting => ⟨map.reflectsEquations_of_faithful hosting.faithful,
      hosting.preserves, hosting.reflects⟩,
    fun laws => ⟨map.faithful_of_reflectsEquations laws.1, laws.2.1, laws.2.2⟩⟩

/-- **A map that identifies two inequivalent terms is not hosting.**  In
particular a constant map is not hosting, as soon as its source has two
inequivalent terms at one interface. -/
theorem not_hosting_of_identifies {origin : source.Interface} {first second : source.Term origin}
    (distinct : ¬ (source.equations origin).r first second)
    (identified : (target.equations (map.interface origin)).r (map.term first)
      (map.term second)) : ¬ map.Hosting :=
  fun hosting => distinct (map.reflectsEquations_of_faithful hosting.faithful identified)

/-- **No branching is lost.** Under a hosting map, two transitions
of a term with one label and inequivalent
results are sent to two transitions of its image with inequivalent results. -/
theorem Hosting.branches (hosting : map.Hosting)
    {origin result : source.Interface} {label : source.Label origin result}
    {term : source.Term origin} {first second : source.Term result}
    (firstStep : source.Transition term label first)
    (secondStep : source.Transition term label second)
    (distinct : ¬ (source.equations result).r first second) :
    target.Transition (map.term term) (map.context label) (map.term first) ∧
      target.Transition (map.term term) (map.context label) (map.term second) ∧
        ¬ (target.equations (map.interface result)).r (map.term first) (map.term second) :=
  ⟨hosting.preserves label firstStep, hosting.preserves label secondStep,
    fun identified => distinct (map.reflectsEquations_of_faithful hosting.faithful identified)⟩

/-! ## Exhausting -/

/-- **Exhausting**: every context of the target between images of interfaces
acts on images as the image of a context of the source. -/
def Exhausting : Prop :=
  ∀ {arity : Type} {holes : arity → source.Interface} {result : source.Interface}
    (observer : target.Context (fun index => map.interface (holes index))
      (map.interface result)),
    ∃ context : source.Context holes result,
      ∀ filling : (index : arity) → source.Term (holes index),
        (target.equations (map.interface result)).r
          (target.fill (map.context context) fun index => map.term (filling index))
          (target.fill observer fun index => map.term (filling index))

/-- Under an exhausting map every term of the target at the image of an
interface is, up to the static equivalence, the image of a term: the target
is nothing the source cannot assemble. -/
theorem Exhausting.term_surjective (exhausting : map.Exhausting) {origin : source.Interface}
    (term : target.Term (map.interface origin)) :
    ∃ preimage : source.Term origin,
      (target.equations (map.interface origin)).r term (map.term preimage) := by
  obtain ⟨context, agrees⟩ := exhausting
    (holes := fun index : Empty => index.elim) (result := origin) (target.constant term)
  refine ⟨source.fill context fun index => index.elim, ?_⟩
  have filled := agrees fun index => index.elim
  rw [target.fill_constant] at filled
  exact (target.equations _).iseqv.trans ((target.equations _).iseqv.symm filled)
    ((target.equations _).iseqv.symm (map.equivariant context _))

end ContextMap

/-! ## Morphisms -/

/-- **A morphism of theories**: a map on terms and on contexts that preserves
bisimilarity, the bisimilarity of the target being computed over the image
of the source's observers. -/
structure ContextMorphism (source target : ContextTheory.{u})
    extends ContextMap source target where
  /-- Transport at the transition profile declared by the two theories. -/
  transitions : toContextMap.PreservesTransitions
  preserves : ∀ (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)},
    probe.Bisimilar left right →
      (toContextMap.push probe).Bisimilar (index := index) (term left) (term right)

namespace ContextMorphism

variable {source middle target : ContextTheory.{u}}

/-- **Bisimilarity over all contexts of the source is carried to bisimilarity
over their images.**  The instance of the law at the full probe. -/
theorem preserves_full (morphism : ContextMorphism source target) {origin : source.Interface}
    {left right : source.Term origin}
    (bisimilar : source.fullProbe.Bisimilar (index := origin) left right) :
    (morphism.push source.fullProbe).Bisimilar (index := origin) (morphism.term left)
      (morphism.term right) :=
  morphism.preserves source.fullProbe bisimilar

/-- The identity morphism. -/
def id (theory : ContextTheory.{u}) : ContextMorphism theory theory where
  toContextMap := ContextMap.id theory
  transitions := ContextMap.preservesTransitions_id theory
  preserves := fun _ _ _ _ bisimilar => bisimilar

/-- Composition of morphisms: what a probe sees is carried twice. -/
def comp (second : ContextMorphism middle target) (first : ContextMorphism source middle) :
    ContextMorphism source target where
  toContextMap := second.toContextMap.comp first.toContextMap
  transitions := ContextMap.PreservesTransitions.comp second.transitions first.transitions
  preserves := fun probe _ _ _ bisimilar =>
    second.preserves (first.push probe) (first.preserves probe bisimilar)

/-- A map that preserves and reflects transitions is a morphism. -/
def ofTransitions (map : ContextMap source target) (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) : ContextMorphism source target where
  toContextMap := map
  transitions := preserves
  preserves := fun probe _ _ _ bisimilar =>
    map.bisimilar_push_of_transitions preserves reflects probe bisimilar

end ContextMorphism

/-- **The category of theories**: theories presented through their contexts,
with morphisms preserving what every probe sees. -/
instance : CategoryTheory.Category ContextTheory.{u} where
  Hom := ContextMorphism
  id := ContextMorphism.id
  comp first second := ContextMorphism.comp second first
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace ContextMap

variable {source middle target : ContextTheory.{u}}

theorem Hosting.comp {second : ContextMap middle target} {first : ContextMap source middle}
    (secondHosting : second.Hosting) (firstHosting : first.Hosting) :
    (second.comp first).Hosting := by
  refine ⟨?_, PreservesTransitions.comp secondHosting.preserves firstHosting.preserves,
    ReflectsTransitions.comp secondHosting.reflects firstHosting.reflects⟩
  apply faithful_of_reflectsEquations
  exact fun equivalent =>
    first.reflectsEquations_of_faithful firstHosting.faithful
      (second.reflectsEquations_of_faithful secondHosting.faithful equivalent)

theorem Exhausting.comp {second : ContextMap middle target} {first : ContextMap source middle}
    (secondExhausting : second.Exhausting) (firstExhausting : first.Exhausting) :
    (second.comp first).Exhausting := by
  intro arity holes result observer
  obtain ⟨between, betweenAgrees⟩ := secondExhausting
    (holes := fun index => first.interface (holes index)) (result := first.interface result)
    observer
  obtain ⟨context, agrees⟩ := firstExhausting between
  refine ⟨context, fun filling => ?_⟩
  refine (target.equations _).iseqv.trans ?_ (betweenAgrees fun index => first.term (filling index))
  refine (target.equations _).iseqv.trans
    ((target.equations _).iseqv.symm
      (second.equivariant (first.context context) fun index => first.term (filling index))) ?_
  refine (target.equations _).iseqv.trans (second.term_resp (agrees filling)) ?_
  exact second.equivariant between fun index => first.term (filling index)

theorem hosting_id (theory : ContextTheory.{u}) : (ContextMap.id theory).Hosting :=
  ⟨fun _ _ agree => agree, preservesTransitions_id theory, reflectsTransitions_id theory⟩

theorem exhausting_id (theory : ContextTheory.{u}) : (ContextMap.id theory).Exhausting :=
  fun observer => ⟨observer, fun _ => (theory.equations _).iseqv.refl _⟩

end ContextMap

/-- One theory hosts and exhausts another when some morphism between them is
hosting and exhausting. -/
def ContextTheory.Embeds (source target : ContextTheory.{u}) : Prop :=
  ∃ morphism : ContextMorphism source target,
    morphism.toContextMap.Hosting ∧ morphism.toContextMap.Exhausting

/-- **The two conditions induce a preorder on theories.** -/
theorem ContextTheory.embeds_refl (theory : ContextTheory.{u}) : theory.Embeds theory :=
  ⟨ContextMorphism.id theory, ContextMap.hosting_id theory, ContextMap.exhausting_id theory⟩

theorem ContextTheory.embeds_trans {first second third : ContextTheory.{u}}
    (firstSecond : first.Embeds second) (secondThird : second.Embeds third) :
    first.Embeds third := by
  obtain ⟨lower, lowerHosting, lowerExhausting⟩ := firstSecond
  obtain ⟨upper, upperHosting, upperExhausting⟩ := secondThird
  exact ⟨upper.comp lower, upperHosting.comp lowerHosting, upperExhausting.comp lowerExhausting⟩

end Mettapedia.GSLT
