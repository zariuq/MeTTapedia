import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Split extensional readouts and observer descent

An extensional account of an intensional carrier is often a surjective
readout with a selected canonical representative.  Such a readout need not be
faithful: proof routes, occurrences, provenance, evidence, or cost may remain
distinct inside one visible fibre.

`SplitReadout` records only the standard split-epimorphism data.  Its universal
observer theorem says that a source observation descends to the extensional
carrier exactly when it is constant on readout fibres.  This criterion keeps
the choice of retained observations explicit rather than identifying an
extensional companion with the intensional source.

The Boolean canary instantiates the construction with a function carrier that
retains an unobserved route tag.  Extensional behavior is complete and has a
canonical section, but the tag neither descends nor can be reconstructed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ExtensionalReadout

universe uSource uTarget uObservation

/-- A surjective readout together with one selected representative of every
target value.  This is split-epimorphism data, not an equivalence. -/
structure SplitReadout (Source : Type uSource) (Target : Type uTarget) where
  observe : Source -> Target
  representative : Target -> Source
  observe_representative : Function.LeftInverse observe representative

namespace SplitReadout

variable {Source : Type uSource} {Target : Type uTarget}
variable (readout : SplitReadout Source Target)

/-- The readout is faithful when it retains every source distinction. -/
def Faithful : Prop := Function.Injective readout.observe

/-- The readout is exact when it is bijective.  Surjectivity follows from the
section; faithfulness is the genuinely additional condition. -/
def Exact : Prop := Function.Bijective readout.observe

/-- A source observer is invariant on the fibres identified by the readout. -/
def FibreInvariant {Observation : Type uObservation}
    (observer : Source -> Observation) : Prop :=
  forall {left right}, readout.observe left = readout.observe right ->
    observer left = observer right

/-- A source observer factors through the extensional target. -/
def FactorsObserver {Observation : Type uObservation}
    (observer : Source -> Observation) : Prop :=
  exists summarize : Target -> Observation,
    forall source, summarize (readout.observe source) = observer source

/-- The canonical representative selected for a source value's visible
readout. -/
def canonicalize (source : Source) : Source :=
  readout.representative (readout.observe source)

@[simp] theorem observe_canonicalize (source : Source) :
    readout.observe (readout.canonicalize source) = readout.observe source :=
  readout.observe_representative (readout.observe source)

@[simp] theorem canonicalize_idempotent (source : Source) :
    readout.canonicalize (readout.canonicalize source) =
      readout.canonicalize source := by
  unfold canonicalize
  rw [readout.observe_representative]

/-- Every split readout is complete on visible target values. -/
theorem surjective : Function.Surjective readout.observe :=
  readout.observe_representative.surjective

/-- Exactness adds only faithfulness to the completeness already supplied by
the section. -/
theorem exact_iff_faithful : readout.Exact <-> readout.Faithful := by
  constructor
  · exact fun exact => exact.1
  · exact fun faithful => ⟨faithful, readout.surjective⟩

/-- Faithfulness is equivalent to every source already being its canonical
representative. -/
theorem faithful_iff_canonicalize_eq :
    readout.Faithful <-> forall source, readout.canonicalize source = source := by
  constructor
  · intro faithful source
    apply faithful
    exact readout.observe_canonicalize source
  · intro canonical left right sameObservation
    calc
      left = readout.canonicalize left := (canonical left).symm
      _ = readout.canonicalize right := by
        unfold canonicalize
        rw [sameObservation]
      _ = right := canonical right

/-- The canonical descent of a source observer along a selected section. -/
def descendObserver {Observation : Type uObservation}
    (observer : Source -> Observation) : Target -> Observation :=
  fun target => observer (readout.representative target)

/-- Fibre invariance is sufficient for the canonical descent to recover the
source observer. -/
theorem descendObserver_observe {Observation : Type uObservation}
    {observer : Source -> Observation}
    (invariant : readout.FibreInvariant observer) (source : Source) :
    readout.descendObserver observer (readout.observe source) = observer source :=
  invariant (readout.observe_representative (readout.observe source))

/-- Any factorization through the readout is the canonical descent. -/
theorem descendedObserver_unique {Observation : Type uObservation}
    (observer : Source -> Observation) (summarize : Target -> Observation)
    (factors : forall source,
      summarize (readout.observe source) = observer source) :
    summarize = readout.descendObserver observer := by
  funext target
  calc
    summarize target =
        summarize (readout.observe (readout.representative target)) :=
      congrArg summarize (readout.observe_representative target).symm
    _ = observer (readout.representative target) :=
      factors (readout.representative target)
    _ = readout.descendObserver observer target := rfl

/-- Observer descent is possible exactly for fibre-invariant observations. -/
theorem factorsObserver_iff_fibreInvariant
    {Observation : Type uObservation} (observer : Source -> Observation) :
    readout.FactorsObserver observer <-> readout.FibreInvariant observer := by
  constructor
  · rintro ⟨summarize, factors⟩ left right sameObservation
    rw [← factors left, ← factors right, sameObservation]
  · intro invariant
    exact ⟨readout.descendObserver observer,
      readout.descendObserver_observe invariant⟩

/-- Fibre-invariant observations are exactly observations of the extensional
target.  The equivalence is induced by precomposition with the readout and
canonical descent along its section. -/
def invariantObserverEquiv (Observation : Type uObservation) :
    {observer : Source -> Observation // readout.FibreInvariant observer} ≃
      (Target -> Observation) where
  toFun := fun observer => readout.descendObserver observer.1
  invFun := fun summarize =>
    ⟨fun source => summarize (readout.observe source), by
      intro left right sameObservation
      exact congrArg summarize sameObservation⟩
  left_inv := by
    intro observer
    apply Subtype.ext
    funext source
    exact readout.descendObserver_observe observer.2 source
  right_inv := by
    intro summarize
    funext target
    exact congrArg summarize (readout.observe_representative target)

end SplitReadout

/-! ## Route-sensitive function canary -/

namespace Canary

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- Extensional behavior is a split readout of the route-sensitive simple
function carrier. -/
def routeReadout : SplitReadout simpleRouteSensitive.Function Bool where
  observe := simpleBehavior
  representative := canonicalSimpleFunction
  observe_representative := simpleBehavior_canonicalSimpleFunction

theorem routeReadout_complete :
    Function.Surjective routeReadout.observe :=
  routeReadout.surjective

/-- The readout forgets the retained route coordinate. -/
theorem routeReadout_not_faithful : ¬ routeReadout.Faithful := by
  intro faithful
  have same : (false, false) = (false, true) := faithful rfl
  exact Bool.false_ne_true (congrArg Prod.snd same)

theorem routeReadout_not_exact : ¬ routeReadout.Exact := by
  rw [routeReadout.exact_iff_faithful]
  exact routeReadout_not_faithful

/-- Extensional behavior itself descends, as every visible observer should. -/
theorem behavior_fibreInvariant :
    routeReadout.FibreInvariant simpleBehavior :=
  fun sameBehavior => sameBehavior

/-- The retained route tag is not constant on extensional fibres. -/
theorem routeTag_not_fibreInvariant :
    ¬ routeReadout.FibreInvariant simpleRouteTag := by
  intro invariant
  have tagsEqual := invariant
    (left := (false, false)) (right := (false, true)) rfl
  exact Bool.false_ne_true tagsEqual

/-- Consequently the route tag cannot be an observation of the extensional
target. -/
theorem routeTag_does_not_descend :
    ¬ routeReadout.FactorsObserver simpleRouteTag := by
  rw [routeReadout.factorsObserver_iff_fibreInvariant]
  exact routeTag_not_fibreInvariant

/-- Canonicalization preserves visible behavior while replacing the retained
route tag by the selected route-free representative. -/
theorem canonicalization_is_visible_not_exact :
    routeReadout.canonicalize (false, true) = (false, false) ∧
      routeReadout.observe (routeReadout.canonicalize (false, true)) =
        routeReadout.observe (false, true) ∧
      routeReadout.canonicalize (false, true) ≠ (false, true) := by
  exact ⟨rfl, rfl, by intro equality; cases equality⟩

end Canary

#print axioms SplitReadout.surjective
#print axioms SplitReadout.exact_iff_faithful
#print axioms SplitReadout.faithful_iff_canonicalize_eq
#print axioms SplitReadout.factorsObserver_iff_fibreInvariant
#print axioms SplitReadout.invariantObserverEquiv
#print axioms Canary.routeReadout_not_faithful
#print axioms Canary.routeTag_does_not_descend
#print axioms Canary.canonicalization_is_visible_not_exact

end Mettapedia.TypeTheory.ExtensionalReadout
