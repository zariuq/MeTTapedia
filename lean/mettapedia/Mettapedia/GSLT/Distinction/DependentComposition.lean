import Mettapedia.TypeTheory.DependentFamilySectionDescent
import Mettapedia.GSLT.Distinction.Isometry
import Mettapedia.GSLT.Distinction.Constructive.Transport
import Mettapedia.GSLT.Distinction.SpanTransport

/-!
# Coherent composition of observations with exact dependent transport

The observation maps of the distinction calculus compose: observation-preserving
functional bisimulations (`ObservationBisimulation.comp`), observation maps with
error (`Constructive.ObservationMap.comp`), span relations
(`SpanTransport.SpanRelation.comp`), and the state relations of cost
simulations.  Dependent transport along an observation is the exact data of
`DependentFamilySectionDescent`: a family factorization (fibre equivalences)
and a compatible section.  This module proves when the two compose, and that
bounds on distances are never a substitute for the fibre equivalences.

* **Functional composites** (`composeFactorization`).  A factorization through
  `first` and a factorization of its target family through `second` compose to
  a factorization through `second ∘ first`; section pullback composes on the
  nose (`liftSection_compose`).  A section descending through the composite
  descends through `first` (`compatible_of_compose`), and with a split readout
  of `first` the exact condition is that both stages descend, the second for
  the descended section (`compatible_compose_iff`).  Descent along composed
  readouts is descent in two stages (`composeReadout`, `descendSection_compose`), and the section
  equivalence of the composite is the composite of the stage equivalences
  (`sectionEquiv_compose_apply`).  The term maps of composed bisimulations and
  observation maps are the composed term maps, so these apply verbatim
  (`bisimulationComposeFamily`, `observationMapComposeFamily`).
* **Relational composites** (`RelTransport`, `Path`, `PathIndependent`).
  Transport along a relation is a fibre equivalence for each related pair.
  Along the composite relation, every path through a middle point carries the
  composed equivalence (`pathTransport`).  A transport along the composite
  relation that agrees with all paths exists exactly when the path transports
  are independent of the middle point; for a supplied selection of middle
  points this is choice-free (`exists_descends_iff_of_selection`), and from the
  bare existential of the composite relation the selection is made with
  `Classical.choice` (`MiddleSelection.classical`, `exists_descends_iff`).
  Related sections compose along paths and along any descended transport
  (`path_sections`, `sectionsRelated_of_descends`).  Graphs of functions have
  unique paths, so functional composites are always path-independent
  (`pathIndependent_graph`) and have a choice-free selection
  (`MiddleSelection.graph`).  Span relations compose by `SpanTransport.compose`
  on states and on events, so the criterion applies to their composites
  (`spanRelation_states_descends_iff`, `spanRelation_events_descends_iff`).
* **Dependence records** (`DependenceRecord`, `Retains`).  A record names the
  observation a family factors through and the finer observation its term
  descends through, with the evidence.  An observation retaining the term key
  (it decodes the key) transports the family and the term
  (`DependenceRecord.familyAlong`, `DependenceRecord.term_along`); retaining
  only the family key transports the family alone.  Retention composes along
  composites (`Retains.compose`), and transport along a composite retention is
  the composite of the stage transports (`familyAlong_compose_identify`).
  Records pull back along every term map with the composed keys
  (`DependenceRecord.pullback`).  A
  term whose identified values differ on a pair that an observation identifies
  is blocked there (`blocked`), and stays blocked after every further
  observation (`not_compatible_compose`).
* **Bounds are not transport** (`universal_transport_iff`,
  `universal_term_transport_iff`).  Transport of every family, or agreement of
  every term, along a closeness relation holds exactly when the relation is
  contained in equality.  For depth bounds of presented systems this says that
  a bound, even `0`, transports every family only when it separates terms
  (`depthBound_universal_transport_iff`).  Along an exact observation map every
  reading-indexed family transports (`readingFactorization`,
  `formulaFactorization`), exact maps compose to an exact map
  (`exactComp`), and reading transport along the composite is the composite of
  the stage transports (`readingFactorization_compose`); at a reading moved by
  a positive error no such universal transport exists (`readingTransport_iff`).

The controls are in `DependentCompositionControls`; the identity-type
counterpart is `DependentCompositionIdentity`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.DependentComposition

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe uA uB uC uD uF uG uH uK uL

/-! ## Values of compatible sections -/

section Values

variable {A : Type uA} {B : Type uB} {observe : A → B} {family : A → Type uF}

/-- A section is compatible exactly when its identified values are heterogeneously
equal on every pair that the observation identifies. -/
theorem compatible_iff_heq (d : FamilyFactorization observe family) (term : ∀ a, family a) :
    Compatible d term ↔
      ∀ left right, observe left = observe right →
        HEq (d.identify left (term left)) (d.identify right (term right)) := by
  constructor
  · intro compatible left right same
    exact (Sigma.mk.inj_iff.mp (compatible left right same)).2
  · intro values left right same
    exact Sigma.mk.inj_iff.mpr ⟨same, values left right same⟩

/-- A term whose identified values differ on a pair identified by the observation
does not descend, even though its family does. -/
theorem blocked (d : FamilyFactorization observe family) (term : ∀ a, family a)
    {left right : A} (same : observe left = observe right)
    (differ : ¬ HEq (d.identify left (term left)) (d.identify right (term right))) :
    ¬ Compatible d term :=
  fun compatible => differ ((compatible_iff_heq d term).mp compatible left right same)

/-- Fibre equivalences reflect heterogeneous equality over equal base points. -/
theorem heq_of_identify_heq {C : Type uC} {G : B → Type uG} {H : C → Type uH} {g : B → C}
    (e : ∀ b, G b ≃ H (g b)) {b b' : B} (same : b = b') {x : G b} {y : G b'}
    (mapped : HEq (e b x) (e b' y)) : HEq x y := by
  subst same
  exact heq_of_eq ((e b).injective (eq_of_heq mapped))

end Values

/-! ## Functional composites -/

section Functional

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable {first : A → B} {second : B → C} {family : A → Type uF}

/-- Compose a factorization through `first` with a factorization of its target
family through `second`. -/
def composeFactorization (d₁ : FamilyFactorization first family)
    (d₂ : FamilyFactorization second d₁.targetFamily) :
    FamilyFactorization (second ∘ first) family where
  targetFamily := d₂.targetFamily
  identify a := (d₁.identify a).trans (d₂.identify (first a))

variable (d₁ : FamilyFactorization first family) (d₂ : FamilyFactorization second d₁.targetFamily)

@[simp] theorem composeFactorization_identify (a : A) (value : family a) :
    (composeFactorization d₁ d₂).identify a value = d₂.identify (first a) (d₁.identify a value) :=
  rfl

/-- The composite total observation is the composite of the total observations. -/
theorem totalObservation_compose (value : Sigma family) :
    (composeFactorization d₁ d₂).totalObservation value =
      d₂.totalObservation (d₁.totalObservation value) := by
  obtain ⟨a, value⟩ := value
  rfl

theorem sectionObservation_compose (term : ∀ a, family a) (a : A) :
    sectionObservation (composeFactorization d₁ d₂) term a =
      d₂.totalObservation (sectionObservation d₁ term a) :=
  rfl

/-- **Section pullback composes on the nose.** -/
theorem liftSection_compose (term : ∀ c, d₂.targetFamily c) :
    liftSection (composeFactorization d₁ d₂) term = liftSection d₁ (liftSection d₂ term) :=
  rfl

/-- **A section descending through the composite descends through the first
observation.**  No readout is needed: the second fibre equivalence is injective. -/
theorem compatible_of_compose (term : ∀ a, family a)
    (compatible : Compatible (composeFactorization d₁ d₂) term) : Compatible d₁ term := by
  rw [compatible_iff_heq] at compatible ⊢
  intro left right same
  exact heq_of_identify_heq d₂.identify same (compatible left right (congrArg second same))

/-- **Blocking persists through composites**: a section blocked at the first
observation is blocked after every further observation. -/
theorem not_compatible_compose (term : ∀ a, family a) (notFirst : ¬ Compatible d₁ term) :
    ¬ Compatible (composeFactorization d₁ d₂) term :=
  fun compatible => notFirst (compatible_of_compose d₁ d₂ term compatible)

/-- Two stages give the composite: a section pulled back from a section that
descends through the second observation descends through the composite. -/
theorem compatible_compose_of_lift (middle : ∀ b, d₁.targetFamily b)
    (compatible : Compatible d₂ middle) :
    Compatible (composeFactorization d₁ d₂) (liftSection d₁ middle) := by
  intro left right same
  rw [sectionObservation_compose, sectionObservation_compose, observe_liftSection,
    observe_liftSection]
  exact compatible (first left) (first right) same

end Functional

section Split

variable {A : Type uA} {B : Type uB} {C : Type uC} {second : B → C} {family : A → Type uF}
variable (readout : SplitReadout A B) (d₁ : FamilyFactorization readout.observe family)
variable (d₂ : FamilyFactorization second d₁.targetFamily)

/-- A compatible section is observed as its descended section. -/
theorem sectionObservation_eq_descend (term : ∀ a, family a) (compatible : Compatible d₁ term)
    (a : A) :
    sectionObservation d₁ term a =
      ⟨readout.observe a, descendSection readout d₁ term (readout.observe a)⟩ :=
  (compatible a (readout.representative (readout.observe a))
    (readout.observe_representative (readout.observe a)).symm).trans
    (pair_descendSection readout d₁ term (readout.observe a)).symm

/-- **The exact condition for composite descent.**  With a split readout of the
first observation, a section descends through the composite exactly when it
descends through the first observation and its descended section descends
through the second. -/
theorem compatible_compose_iff (term : ∀ a, family a) :
    Compatible (composeFactorization d₁ d₂) term ↔
      Compatible d₁ term ∧ Compatible d₂ (descendSection readout d₁ term) := by
  constructor
  · intro compatible
    refine ⟨compatible_of_compose d₁ d₂ term compatible, ?_⟩
    intro left right same
    have leftPair := congrArg d₂.totalObservation
      (pair_descendSection readout d₁ term left)
    have rightPair := congrArg d₂.totalObservation
      (pair_descendSection readout d₁ term right)
    refine leftPair.trans (Eq.trans ?_ rightPair.symm)
    rw [← sectionObservation_compose, ← sectionObservation_compose]
    apply compatible
    change second (readout.observe (readout.representative left)) =
      second (readout.observe (readout.representative right))
    rw [readout.observe_representative, readout.observe_representative]
    exact same
  · rintro ⟨compatibleFirst, compatibleSecond⟩ left right same
    rw [sectionObservation_compose, sectionObservation_compose,
      sectionObservation_eq_descend readout d₁ term compatibleFirst left,
      sectionObservation_eq_descend readout d₁ term compatibleFirst right]
    exact compatibleSecond (readout.observe left) (readout.observe right) same

end Split

/-! ## Composed readouts -/

/-- Split readouts compose; the representative is selected in two stages. -/
def composeReadout {A : Type uA} {B : Type uB} {C : Type uC}
    (earlier : SplitReadout A B) (later : SplitReadout B C) : SplitReadout A C where
  observe := later.observe ∘ earlier.observe
  representative := earlier.representative ∘ later.representative
  observe_representative target := by
    change later.observe (earlier.observe (earlier.representative (later.representative target))) =
      target
    rw [earlier.observe_representative, later.observe_representative]

section ComposedReadouts

variable {A : Type uA} {B : Type uB} {C : Type uC} {family : A → Type uF}
variable (earlier : SplitReadout A B) (later : SplitReadout B C)
variable (d₁ : FamilyFactorization earlier.observe family)
variable (d₂ : FamilyFactorization later.observe d₁.targetFamily)

/-- The composite factorization, read through the composed readout. -/
abbrev stagedFactorization : FamilyFactorization (composeReadout earlier later).observe family :=
  composeFactorization (first := earlier.observe) (second := later.observe) d₁ d₂

/-- **Descent along composed readouts is descent in two stages**, for every
section, compatible or not. -/
theorem descendSection_compose (term : ∀ a, family a) :
    descendSection (composeReadout earlier later) (stagedFactorization earlier later d₁ d₂) term =
      descendSection later d₂ (descendSection earlier d₁ term) := by
  funext target
  have composite := pair_descendSection (composeReadout earlier later) (stagedFactorization earlier later d₁ d₂) term
    target
  have staged := (pair_descendSection later d₂ (descendSection earlier d₁ term) target).trans
    (congrArg d₂.totalObservation
      (pair_descendSection earlier d₁ term (later.representative target)))
  exact eq_of_heq (Sigma.mk.inj_iff.mp (composite.trans staged.symm)).2

/-- **The section equivalence of the composite is the composite of the stage
equivalences.** -/
theorem sectionEquiv_compose_apply (term : ∀ c, d₂.targetFamily c) :
    (sectionEquiv (composeReadout earlier later) (stagedFactorization earlier later d₁ d₂) term).1 =
      (sectionEquiv earlier d₁ (sectionEquiv later d₂ term).1).1 :=
  rfl

theorem sectionEquiv_compose_symm_apply (term : {term : ∀ a, family a //
    Compatible (stagedFactorization earlier later d₁ d₂) term}) :
    (sectionEquiv (composeReadout earlier later) (stagedFactorization earlier later d₁ d₂)).symm term =
      descendSection later d₂ (descendSection earlier d₁ term.1) :=
  descendSection_compose earlier later d₁ d₂ term.1

end ComposedReadouts

/-! ## The d-calc term maps compose -/

section Maps

open Mettapedia.GSLT

universe uS uT uP uA' uL' uO' uA'' uL'' uO''' uO uL₀ uA₀ uV

/-- The term map of composed bisimulations is the composite term map. -/
theorem bisimulation_comp_mapTerm {S : GSLT.{uS}} {T : GSLT.{uT}} {P : GSLT.{uP}}
    {Q : GradedSystem.{uS, uA₀, uL₀, uO} S} {R : GradedSystem.{uT, uA', uL', uO'} T}
    {W : GradedSystem.{uP, uA'', uL'', uO'''} P}
    (earlier : ObservationBisimulation Q R) (later : ObservationBisimulation R W) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

/-- A family transported along one bisimulation and then the next is
transported along their composite. -/
def bisimulationComposeFamily {S : GSLT.{uS}} {T : GSLT.{uT}} {P : GSLT.{uP}}
    {Q : GradedSystem.{uS, uA₀, uL₀, uO} S} {R : GradedSystem.{uT, uA', uL', uO'} T}
    {W : GradedSystem.{uP, uA'', uL'', uO'''} P}
    {earlier : ObservationBisimulation Q R} {later : ObservationBisimulation R W}
    {family : S.Term → Type uF} (d₁ : FamilyFactorization earlier.mapTerm family)
    (d₂ : FamilyFactorization later.mapTerm d₁.targetFamily) :
    FamilyFactorization (earlier.comp later).mapTerm family :=
  composeFactorization (first := earlier.mapTerm) (second := later.mapTerm) d₁ d₂

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- The term map of composed observation maps is the composite term map,
whatever the errors. -/
theorem observationMap_comp_mapTerm {S : GSLT.{uS}} {T : GSLT.{uT}} {P : GSLT.{uP}}
    {K : Constructive.Scale V}
    {Q : Constructive.PresentedSystem.{uS, uA₀, uL₀, uO} S K}
    {R : Constructive.PresentedSystem.{uT, uA', uL', uO'} T K}
    {W : Constructive.PresentedSystem.{uP, uA'', uL'', uO'''} P K} {e₁ e₂ : V}
    (earlier : Constructive.ObservationMap Q R e₁) (later : Constructive.ObservationMap R W e₂) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

/-- A family transported along one observation map and then the next is
transported along their composite. -/
def observationMapComposeFamily {S : GSLT.{uS}} {T : GSLT.{uT}} {P : GSLT.{uP}}
    {K : Constructive.Scale V}
    {Q : Constructive.PresentedSystem.{uS, uA₀, uL₀, uO} S K}
    {R : Constructive.PresentedSystem.{uT, uA', uL', uO'} T K}
    {W : Constructive.PresentedSystem.{uP, uA'', uL'', uO'''} P K} {e₁ e₂ : V}
    {earlier : Constructive.ObservationMap Q R e₁} {later : Constructive.ObservationMap R W e₂}
    {family : S.Term → Type uF} (d₁ : FamilyFactorization earlier.mapTerm family)
    (d₂ : FamilyFactorization later.mapTerm d₁.targetFamily) :
    FamilyFactorization (earlier.comp later).mapTerm family :=
  composeFactorization (first := earlier.mapTerm) (second := later.mapTerm) d₁ d₂

end Maps

/-! ## Relational composites -/

section Relational

open Mettapedia.GSLT.Distinction.SpanTransport (compose)

variable {X : Type uA} {Y : Type uB} {Z : Type uC}

/-- **Exact transport along a relation**: a fibre equivalence for each related pair. -/
def RelTransport (R : X → Y → Prop) (F : X → Type uF) (G : Y → Type uG) :=
  ∀ ⦃x y⦄, R x y → F x ≃ G y

/-- Sections related along a transport: each related pair carries one section
to the other. -/
def SectionsRelated {R : X → Y → Prop} {F : X → Type uF} {G : Y → Type uG}
    (T : RelTransport R F G) (source : ∀ x, F x) (target : ∀ y, G y) : Prop :=
  ∀ ⦃x y⦄ (related : R x y), T related (source x) = target y

/-- A path through a composite relation retains its middle point. -/
def Path (R : X → Y → Prop) (S : Y → Z → Prop) (x : X) (z : Z) : Type uB :=
  {y : Y // R x y ∧ S y z}

/-- The composite relation holds along a path. -/
theorem Path.compose {R : X → Y → Prop} {S : Y → Z → Prop} {x : X} {z : Z} (path : Path R S x z) :
    compose R S x z :=
  ⟨path.1, path.2.1, path.2.2⟩

variable {R : X → Y → Prop} {S : Y → Z → Prop}
variable {F : X → Type uF} {G : Y → Type uG} {H : Z → Type uH}
variable (T₁ : RelTransport R F G) (T₂ : RelTransport S G H)

/-- The composed equivalence along one path. -/
def pathTransport {x : X} {z : Z} (path : Path R S x z) : F x ≃ H z :=
  (T₁ path.2.1).trans (T₂ path.2.2)

/-- **The coherence condition of a relational composite**: the composed
equivalence does not depend on the middle point. -/
def PathIndependent : Prop :=
  ∀ ⦃x z⦄ (first second : Path R S x z), pathTransport T₁ T₂ first = pathTransport T₁ T₂ second

/-- A transport along the composite relation descends the path transports when
it agrees with every one of them. -/
def Descends (T : RelTransport (compose R S) F H) : Prop :=
  ∀ ⦃x z⦄ (path : Path R S x z), T path.compose = pathTransport T₁ T₂ path

/-- **A descended composite forces path independence.**  Choice-free. -/
theorem pathIndependent_of_descends (T : RelTransport (compose R S) F H)
    (descends : Descends T₁ T₂ T) : PathIndependent T₁ T₂ :=
  fun _ _ first second => (descends first).symm.trans (descends second)

/-- A supplied middle point for each composite pair, as data. -/
def MiddleSelection (R : X → Y → Prop) (S : Y → Z → Prop) :=
  ∀ ⦃x z⦄, compose R S x z → Path R S x z

/-- The transport along the composite relation through a supplied selection. -/
def descend (select : MiddleSelection R S) : RelTransport (compose R S) F H :=
  fun _ _ related => pathTransport T₁ T₂ (select related)

/-- **Path independence and a supplied selection give a descended composite.**
Choice-free. -/
theorem descend_descends (select : MiddleSelection R S) (independent : PathIndependent T₁ T₂) :
    Descends T₁ T₂ (descend T₁ T₂ select) :=
  fun _ _ path => independent (select path.compose) path

/-- **The exact condition for relational composites, choice-free**: given a
selection of middle points, a transport along the composite relation agreeing
with every path exists exactly when the path transports are independent of the
middle point. -/
theorem exists_descends_iff_of_selection (select : MiddleSelection R S) :
    (∃ T : RelTransport (compose R S) F H, Descends T₁ T₂ T) ↔ PathIndependent T₁ T₂ :=
  ⟨fun ⟨T, descends⟩ => pathIndependent_of_descends T₁ T₂ T descends,
    fun independent => ⟨descend T₁ T₂ select, descend_descends T₁ T₂ select independent⟩⟩

/-- **Where `Classical.choice` enters**: a middle point selected from the bare
existential of the composite relation. -/
noncomputable def MiddleSelection.classical (R : X → Y → Prop) (S : Y → Z → Prop) :
    MiddleSelection R S :=
  fun _ _ related => ⟨Classical.choose related, Classical.choose_spec related⟩

/-- **The exact condition for relational composites**: a transport along the
composite relation agreeing with every path exists exactly when the path
transports are independent of the middle point.  The converse uses the
classical selection of middle points. -/
theorem exists_descends_iff :
    (∃ T : RelTransport (compose R S) F H, Descends T₁ T₂ T) ↔ PathIndependent T₁ T₂ :=
  exists_descends_iff_of_selection T₁ T₂ (MiddleSelection.classical R S)

/-- **Related sections compose along every path.** -/
theorem path_sections {source : ∀ x, F x} {middle : ∀ y, G y} {target : ∀ z, H z}
    (firstRelated : SectionsRelated T₁ source middle)
    (secondRelated : SectionsRelated T₂ middle target) {x : X} {z : Z} (path : Path R S x z) :
    pathTransport T₁ T₂ path (source x) = target z := by
  change T₂ path.2.2 (T₁ path.2.1 (source x)) = target z
  rw [firstRelated path.2.1, secondRelated path.2.2]

/-- **Related sections are related along every descended composite.** -/
theorem sectionsRelated_of_descends (T : RelTransport (compose R S) F H)
    (descends : Descends T₁ T₂ T) {source : ∀ x, F x} {middle : ∀ y, G y} {target : ∀ z, H z}
    (firstRelated : SectionsRelated T₁ source middle)
    (secondRelated : SectionsRelated T₂ middle target) : SectionsRelated T source target := by
  rintro x z ⟨y, firstStep, secondStep⟩
  have along := congrArg (fun equivalence : F x ≃ H z => equivalence (source x))
    (descends (⟨y, firstStep, secondStep⟩ : Path R S x z))
  exact along.trans (path_sections T₁ T₂ firstRelated secondRelated _)

/-! ### Graphs of functions -/

/-- The graph of a function as a relation. -/
def graph (f : X → Y) : X → Y → Prop := fun x y => f x = y

/-- Paths through composed graphs are unique. -/
theorem path_graph_eq {f : X → Y} {g : Y → Z} {x : X} {z : Z}
    (first second : Path (graph f) (graph g) x z) : first = second :=
  Subtype.ext (first.2.1.symm.trans second.2.1)

/-- **Functional composites are always path-independent.** -/
theorem pathIndependent_graph {f : X → Y} {g : Y → Z} (T₁ : RelTransport (graph f) F G)
    (T₂ : RelTransport (graph g) G H) : PathIndependent T₁ T₂ :=
  fun _ _ first second => by rw [path_graph_eq first second]

/-- Composed graphs have a choice-free selection of middle points. -/
def MiddleSelection.graph (f : X → Y) (g : Y → Z) :
    MiddleSelection (DependentComposition.graph f) (DependentComposition.graph g) :=
  fun x _ related => ⟨f x, rfl, by
    obtain ⟨y, same, stepped⟩ := related
    exact (congrArg g same).trans stepped⟩

/-- A family factorization is transport along the graph of its observation. -/
def ofFactorization {f : X → Y} (d : FamilyFactorization f F) :
    RelTransport (graph f) F d.targetFamily :=
  fun x _ same => (d.identify x).trans (equalityEquiv (congrArg d.targetFamily same))

end Relational

/-! ### Span relations -/

section Spans

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Distinction.SpanTransport

universe e f g

variable {X : Type uA} {Y : Type uB} {Z : Type uC}
variable {A : ReductionSpan.{uA, e} X} {B : ReductionSpan.{uB, f} Y} {C : ReductionSpan.{uC, g} Z}

/-- **Span composites**: transports along the state relations of two span
relations descend to the state relation of their composite exactly when they
are path-independent.  Choice-free for a supplied selection of middle states;
`MiddleSelection.classical` supplies one with choice. -/
theorem spanRelation_states_descends_iff (first : SpanRelation A B) (second : SpanRelation B C)
    {F : X → Type uF} {G : Y → Type uG} {H : Z → Type uH}
    (T₁ : RelTransport first.states F G) (T₂ : RelTransport second.states G H)
    (select : MiddleSelection first.states second.states) :
    (∃ T : RelTransport (first.comp second).states F H, Descends T₁ T₂ T) ↔
      PathIndependent T₁ T₂ :=
  exists_descends_iff_of_selection T₁ T₂ select

/-- The same for families of event occurrences (readings, provenance, accounts)
along the event relations. -/
theorem spanRelation_events_descends_iff (first : SpanRelation A B) (second : SpanRelation B C)
    {F : A.Edge → Type uF} {G : B.Edge → Type uG} {H : C.Edge → Type uH}
    (T₁ : RelTransport first.events F G) (T₂ : RelTransport second.events G H)
    (select : MiddleSelection first.events second.events) :
    (∃ T : RelTransport (first.comp second).events F H, Descends T₁ T₂ T) ↔
      PathIndependent T₁ T₂ :=
  exists_descends_iff_of_selection T₁ T₂ select

end Spans

/-! ## Dependence records -/

section Records

variable {A : Type uA} {B : Type uB} {C : Type uC} {family : A → Type uF}

/-- An observation **retains** a key when it decodes the key. -/
structure Retains {K : Type uK} (observe : A → B) (key : A → K) where
  decode : B → K
  decode_observe : ∀ a, decode (observe a) = key a

/-- **Retention composes along composites**: the second observation must
retain the first stage's decoder. -/
def Retains.compose {K : Type uK} {first : A → B} {second : B → C} {key : A → K}
    (earlier : Retains first key) (later : Retains second earlier.decode) :
    Retains (second ∘ first) key where
  decode := later.decode
  decode_observe a := (later.decode_observe (first a)).trans (earlier.decode_observe a)

/-- Retaining a finer key retains every coarsening of it. -/
def Retains.coarsen {K : Type uK} {L : Type uL} {observe : A → B} {key : A → K}
    (retains : Retains observe key) (coarsen : K → L) : Retains observe (coarsen ∘ key) where
  decode := coarsen ∘ retains.decode
  decode_observe a := congrArg coarsen (retains.decode_observe a)

/-- **A factorization through a key transports along every observation that
retains the key.** -/
def familyAlong {K : Type uK} {key : A → K} {observe : A → B}
    (d : FamilyFactorization key family) (retains : Retains observe key) :
    FamilyFactorization observe family where
  targetFamily b := d.targetFamily (retains.decode b)
  identify a := (d.identify a).trans
    (equalityEquiv (congrArg d.targetFamily (retains.decode_observe a).symm))

theorem familyAlong_identify_heq {K : Type uK} {key : A → K} {observe : A → B}
    (d : FamilyFactorization key family) (retains : Retains observe key) (a : A)
    (value : family a) : HEq ((familyAlong d retains).identify a value) (d.identify a value) :=
  equalityEquiv_apply_heq _ _

/-- **Compatibility along a retaining observation is agreement of the key's
identified values on the observation's kernel.** -/
theorem compatible_familyAlong_iff {K : Type uK} {key : A → K} {observe : A → B}
    (d : FamilyFactorization key family) (retains : Retains observe key) (term : ∀ a, family a) :
    Compatible (familyAlong d retains) term ↔
      ∀ left right, observe left = observe right →
        HEq (d.identify left (term left)) (d.identify right (term right)) := by
  rw [compatible_iff_heq]
  constructor
  · intro values left right same
    exact (familyAlong_identify_heq d retains left (term left)).symm.trans
      ((values left right same).trans (familyAlong_identify_heq d retains right (term right)))
  · intro values left right same
    exact (familyAlong_identify_heq d retains left (term left)).trans
      ((values left right same).trans (familyAlong_identify_heq d retains right (term right)).symm)

/-- **A term descending through a key descends through every observation that
retains the key.** -/
theorem compatible_familyAlong {K : Type uK} {key : A → K} {observe : A → B}
    (d : FamilyFactorization key family) (retains : Retains observe key) (term : ∀ a, family a)
    (compatible : Compatible d term) : Compatible (familyAlong d retains) term := by
  rw [compatible_familyAlong_iff]
  intro left right same
  apply (compatible_iff_heq d term).mp compatible
  rw [← retains.decode_observe left, ← retains.decode_observe right, same]

/-- Reindexed fibre identifications are the original ones up to transport. -/
theorem reindexFamily_identify_heq {A' : Type uD} {K : Type uK} {K' : Type uL} {key : A → K}
    (d : FamilyFactorization key family) (sourceMap : A' → A) (key' : A' → K') (targetMap : K' → K)
    (commutes : ∀ a', key (sourceMap a') = targetMap (key' a')) (a' : A')
    (value : family (sourceMap a')) :
    HEq ((reindexFamily d sourceMap key' targetMap commutes).identify a' value)
      (d.identify (sourceMap a') value) :=
  equalityEquiv_apply_heq _ _

set_option linter.checkUnivs false in
/-- **A dependence record** of a family and one of its terms: the family
factors through `familyKey`; the term descends through the finer `termKey`,
which determines `familyKey`.  The two evidence fields are the content: a
record without them is a declaration, not a licence. -/
structure DependenceRecord (family : A → Type uF) (term : ∀ a, family a) where
  FamilyKey : Type uK
  TermKey : Type uL
  familyKey : A → FamilyKey
  termKey : A → TermKey
  coarsen : TermKey → FamilyKey
  coarsen_termKey : ∀ a, coarsen (termKey a) = familyKey a
  family : FamilyFactorization familyKey family
  term : Compatible (familyAlong family ⟨coarsen, coarsen_termKey⟩) term

namespace DependenceRecord

variable {term : ∀ a, family a} (record : DependenceRecord.{uA, uF, uK, uL} family term)

/-- The family transports along every observation retaining the family key. -/
def familyAlong {observe : A → B} (retains : Retains observe record.familyKey) :
    FamilyFactorization observe family :=
  DependentComposition.familyAlong record.family retains

/-- An observation retaining the term key retains the family key. -/
def familyRetention {observe : A → B} (retains : Retains observe record.termKey) :
    Retains observe record.familyKey where
  decode := record.coarsen ∘ retains.decode
  decode_observe a := (congrArg record.coarsen (retains.decode_observe a)).trans
    (record.coarsen_termKey a)

/-- **Transport follows the record**: an observation retaining the term key
transports the family and its term. -/
theorem term_along {observe : A → B} (retains : Retains observe record.termKey) :
    Compatible (record.familyAlong (record.familyRetention retains)) term := by
  rw [familyAlong, compatible_familyAlong_iff]
  have recorded := (compatible_familyAlong_iff record.family _ term).mp record.term
  intro left right same
  apply recorded
  rw [← retains.decode_observe left, ← retains.decode_observe right, same]

/-- Along a composite retention the term is transported by the composite. -/
theorem term_along_compose {first : A → B} {second : B → C}
    (earlier : Retains first record.termKey) (later : Retains second earlier.decode) :
    Compatible (record.familyAlong (record.familyRetention (earlier.compose later))) term :=
  record.term_along (earlier.compose later)

/-- **Records pull back along every map**: a record of a family and term on
`A` is a record of their substitution along `f`, with the composed keys. -/
def pullback {A' : Type uD} (f : A' → A) :
    DependenceRecord.{uD, uF, uK, uL} (fun a' => family (f a')) (fun a' => term (f a')) where
  FamilyKey := record.FamilyKey
  TermKey := record.TermKey
  familyKey := record.familyKey ∘ f
  termKey := record.termKey ∘ f
  coarsen := record.coarsen
  coarsen_termKey a' := record.coarsen_termKey (f a')
  family := reindexFamily record.family f (record.familyKey ∘ f) id (fun _ => rfl)
  term := by
    rw [compatible_familyAlong_iff]
    have recorded := (compatible_familyAlong_iff record.family _ term).mp record.term
    intro left right same
    exact (reindexFamily_identify_heq _ _ _ _ _ left _).trans
      ((recorded (f left) (f right) same).trans
        (reindexFamily_identify_heq _ _ _ _ _ right _).symm)

/-- Pulling back along a composite has the composed keys. -/
theorem pullback_compose_keys {A' : Type uD} {A'' : Type uB} (f : A' → A) (g : A'' → A') :
    ((record.pullback f).pullback g).termKey = (record.pullback (f ∘ g)).termKey ∧
      ((record.pullback f).pullback g).familyKey = (record.pullback (f ∘ g)).familyKey :=
  ⟨rfl, rfl⟩

end DependenceRecord

/-- The second-stage factorization of a transported family: its target family
through the next observation, retaining the first decoder. -/
def familyAlongNext {K : Type uK} {key : A → K} {first : A → B} {second : B → C}
    (d : FamilyFactorization key family) (earlier : Retains first key)
    (later : Retains second earlier.decode) :
    FamilyFactorization second (familyAlong d earlier).targetFamily :=
  familyAlong (FamilyFactorization.pullback earlier.decode d.targetFamily) later

/-- **Coherence**: transport along a composite retention is the composite of the
stage transports, fibre by fibre. -/
theorem familyAlong_compose_identify {K : Type uK} {key : A → K} {first : A → B}
    {second : B → C} (d : FamilyFactorization key family) (earlier : Retains first key)
    (later : Retains second earlier.decode) (a : A) (value : family a) :
    (composeFactorization (familyAlong d earlier) (familyAlongNext d earlier later)).identify
        a value = (familyAlong d (earlier.compose later)).identify a value := by
  apply eq_of_heq
  change HEq (equalityEquiv _ (equalityEquiv _ (d.identify a value)))
    (equalityEquiv _ (d.identify a value))
  exact ((equalityEquiv_apply_heq _ _).trans (equalityEquiv_apply_heq _ _)).trans
    (equalityEquiv_apply_heq _ _).symm

end Records

/-! ## Bounds are not transport -/

section Bounds

variable {X : Type uA}

/-- **Transport of every family along a closeness relation exists exactly when
the relation is contained in equality.**  A bound, even at distance `0`,
supplies dependent transport only when it separates the points it relates. -/
theorem universal_transport_iff (close : X → X → Prop) :
    (∀ F : X → Type uF, Nonempty (RelTransport close F F)) ↔ ∀ ⦃x y⦄, close x y → x = y := by
  constructor
  · intro transports x y related
    obtain ⟨T⟩ := transports (fun z => ULift.{uF} (PLift (x = z)))
    exact (T related ⟨⟨rfl⟩⟩).down.down
  · intro discrete F
    exact ⟨fun _ _ related => equalityEquiv (congrArg F (discrete related))⟩

/-- **Agreement of every term along a closeness relation holds exactly when the
relation is contained in equality**, already for the constant family of
propositions, which factors through every observation. -/
theorem universal_term_transport_iff (close : X → X → Prop) :
    (∀ term : X → Prop, ∀ ⦃x y⦄, close x y → term x = term y) ↔
      ∀ ⦃x y⦄, close x y → x = y := by
  constructor
  · intro agree x y related
    exact (agree (fun z => x = z) related).mp rfl
  · intro discrete term x y related
    rw [discrete related]

open Mettapedia.GSLT

universe uS uAt uLb uO uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]

/-- **For depth bounds**: transport of every family along "within `bound` at
`depth`" exists exactly when that closeness separates terms. -/
theorem depthBound_universal_transport_iff {S : GSLT.{uS}} {K : Constructive.Scale V}
    (Q : Constructive.PresentedSystem.{uS, uAt, uLb, uO} S K) (W : Q.Vocabulary) (depth : ℕ)
    (bound : V) :
    (∀ F : S.Term → Type uF,
        Nonempty (RelTransport (fun x y => Q.depthBound W depth x y ≤ bound) F F)) ↔
      ∀ ⦃x y⦄, Q.depthBound W depth x y ≤ bound → x = y :=
  universal_transport_iff _

end Bounds

section Readings

open Mettapedia.GSLT

universe uS uT uAt uLb uO uAt' uLb' uO' uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {T : GSLT.{uT}} {K : Constructive.Scale V}
variable {Q : Constructive.PresentedSystem.{uS, uAt, uLb, uO} S K}
variable {R : Constructive.PresentedSystem.{uT, uAt', uLb', uO'} T K}

theorem exact_value (map : Constructive.ObservationMap Q R 0) (observation : Q.Obs)
    (term : S.Term) : R.value (map.atom observation) (map.mapTerm term) = Q.value observation term :=
  Constructive.eq_of_abs_sub_nonpos (map.value_close observation term)

/-- **Along an exact observation map every reading-indexed family transports
exactly.** -/
def readingFactorization (map : Constructive.ObservationMap Q R 0) (observation : Q.Obs)
    (Φ : V → Type uF) :
    FamilyFactorization map.mapTerm (fun term => Φ (Q.value observation term)) where
  targetFamily target := Φ (R.value (map.atom observation) target)
  identify term := equalityEquiv (congrArg Φ (exact_value map observation term).symm)

/-- The same for the values of every formula, at every depth. -/
def formulaFactorization (map : Constructive.ObservationMap Q R 0) (formula : Q.Formula)
    (Φ : V → Type uF) :
    FamilyFactorization map.mapTerm (fun term => Φ (Q.val formula term)) where
  targetFamily target := Φ (R.val (map.translate formula) target)
  identify term := equalityEquiv
    (congrArg Φ (Constructive.ObservationMap.val_translate map formula term).symm)

/-- **Universal transport of reading-indexed families at a term holds exactly
when the map keeps that reading.**  A reading moved within a positive error
transports no such family universally. -/
theorem readingTransport_iff {error : V} (map : Constructive.ObservationMap Q R error)
    (observation : Q.Obs) (term : S.Term) :
    (∀ Φ : V → Type uF,
        Nonempty (Φ (Q.value observation term) ≃ Φ (R.value (map.atom observation) (map.mapTerm term)))) ↔
      R.value (map.atom observation) (map.mapTerm term) = Q.value observation term := by
  constructor
  · intro transports
    obtain ⟨equivalence⟩ := transports (fun value => ULift.{uF} (PLift (Q.value observation term = value)))
    exact (equivalence ⟨⟨rfl⟩⟩).down.down.symm
  · intro same Φ
    exact ⟨equalityEquiv (congrArg Φ same.symm)⟩

section Composite

universe uU uAt'' uLb'' uO''

variable {U : GSLT.{uU}} {P : Constructive.PresentedSystem.{uU, uAt'', uLb'', uO''} U K}

/-- The same observation map, at an equal error. -/
def withError {error error' : V} (same : error = error')
    (map : Constructive.ObservationMap Q R error) : Constructive.ObservationMap Q R error' where
  error_nonneg := same ▸ map.error_nonneg
  mapTerm := map.mapTerm
  mapEquiv := map.mapEquiv
  atom := map.atom
  label := map.label
  value_close observation term := same ▸ map.value_close observation term
  mapAct := map.mapAct
  liftAct := map.liftAct

/-- **Exact observation maps compose to an exact map.** -/
def exactComp (earlier : Constructive.ObservationMap Q R 0)
    (later : Constructive.ObservationMap R P 0) : Constructive.ObservationMap Q P 0 :=
  withError (add_zero 0) (earlier.comp later)

theorem exactComp_mapTerm (earlier : Constructive.ObservationMap Q R 0)
    (later : Constructive.ObservationMap R P 0) :
    (exactComp earlier later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

/-- **Reading transport along composed exact maps is the composite of the
stage transports**, value by value. -/
theorem readingFactorization_compose (earlier : Constructive.ObservationMap Q R 0)
    (later : Constructive.ObservationMap R P 0) (observation : Q.Obs) (Φ : V → Type uF)
    (term : S.Term) (value : Φ (Q.value observation term)) :
    (readingFactorization (exactComp earlier later) observation Φ).identify term value =
      (composeFactorization (first := earlier.mapTerm) (second := later.mapTerm)
        (readingFactorization earlier observation Φ)
        (readingFactorization later (earlier.atom observation) Φ)).identify term value := by
  apply eq_of_heq
  refine (equalityEquiv_apply_heq _ _).trans ?_
  exact ((equalityEquiv_apply_heq _ _).trans (equalityEquiv_apply_heq _ _)).symm

end Composite

end Readings

end Mettapedia.GSLT.Distinction.DependentComposition
