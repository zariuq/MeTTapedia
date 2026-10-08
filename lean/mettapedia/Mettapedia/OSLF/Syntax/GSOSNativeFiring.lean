import Mettapedia.OSLF.Syntax.GSOSNativeGuard
import Mettapedia.TypeTheory.PresheafEventNativeLogic

/-!
# Native finite-premise firings with retained occurrences

A firing stores the authored rule origin, every child source, one selected
operational edge at each positive premise address, and native negative
premises. It does not require an edge for an untested or negatively tested
argument. Independent overlap consistency earns the actual conclusion of
the authored clause. Context maps retain all supplied premise occurrences,
and the conclusion is the actual operational event, with its complete
dependent target certificate available through the existing event span.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeFiring

open _root_.CategoryTheory Mettapedia.TypeTheory
open PresheafEventCertificates EdgeReadout NativeGuard
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]

/-- Positive premises are indexed by their actual tested argument/action
addresses. Several positive actions may belong to one argument. -/
abbrev PositiveAddress {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) :=
  { address : {a // a ∈ rule.observed} // rule.pattern address = true }

abbrev NegativeAddress {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) :=
  { address : {a // a ∈ rule.observed} // rule.pattern address = false }

/-- An admitted finite derivative has its actual positive premise address. -/
noncomputable def positiveAddress {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (address : Address Actions operator)
    (available : observedGuard Actions rule.observed rule.pattern address = true) :
    PositiveAddress rule := by
  classical
  have present : address ∈ rule.observed := by
    by_contra missing
    simp [observedGuard, missing] at available
  exact ⟨⟨address, present⟩, by simpa only [observedGuard, dif_pos present] using available⟩

variable (presentation : AuthoredFinitePresentation (S := S) Actions)
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

/-- Native negative atoms use an explicitly inhabited origin-free support
carrier. The independently supplied positive edge origins remain below. -/
abbrev SupportOrigin := PUnit.{u + 1}

@[ext] structure Firing (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) where
  origin : presentation.Origin sort operator action
  children : (NativeGuard.children worlds operator).obj world
  positive : ∀ address : PositiveAddress (presentation.rule sort operator action origin),
    Event presentation.toLaw worlds steps PremiseOrigins (S.argument operator address.val.val.1) world
  positive_source : ∀ address, (positive address).source = children address.val.val.1
  positive_action : ∀ address, (positive address).action = address.val.val.2
  negative : ∀ address : NegativeAddress (presentation.rule sort operator action origin),
    children address.val.val.1 ∈
      (noAction presentation.toLaw worlds steps SupportOrigin _ address.val.val.2).obj world

namespace Firing

variable {presentation worlds steps}
variable {PremiseOrigins : Type u} {sort : S.Srt}
variable {operator : S.Operator sort} {action : Actions sort} {world : Cᵒᵖ}

/-- The exact independently authored finite clause. -/
abbrev rule (firing : Firing presentation worlds steps PremiseOrigins world operator action) :=
  presentation.rule sort operator action firing.origin

/-- Supplied positive edges compute the actual complete child transition. -/
theorem positive_step (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (address : PositiveAddress firing.rule) :
    Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
      (firing.children address.val.val.1) address.val.val.2 = some (firing.positive address).target := by
  simpa only [← firing.positive_source address, ← firing.positive_action address]
    using (firing.positive address).valid

/-- Both positive event witnesses and native negative atoms earn the whole
finite Boolean matching judgment. -/
theorem matching (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    firing.rule.Matches (actualGuard presentation.toLaw worlds steps world firing.children) := by
  intro address present
  cases polarity : firing.rule.pattern ⟨address, present⟩ with
  | false =>
      have none := (noAction_iff_none presentation.toLaw worlds steps _ address.2 world
        (firing.children address.1)).mp (firing.negative ⟨⟨address, present⟩, polarity⟩)
      change (Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
        (firing.children address.1) address.2).isSome = _
      rw [none]
      rfl
  | true =>
      have some := firing.positive_step ⟨⟨address, present⟩, polarity⟩
      change (Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
        (firing.children address.1) address.2).isSome = _
      rw [some]
      rfl

theorem native_guard (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    firing.children ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin firing.rule).obj world :=
  (finiteGuard_iff_matches presentation.toLaw worlds steps firing.rule world firing.children).mpr firing.matching

/-- Independent target filling reads the exact supplied positive events,
not chosen witnesses of their existential support. -/
noncomputable def suppliedAssignment
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    ruleVariables Actions operator (observedGuard Actions firing.rule.observed firing.rule.pattern) ⟶
      S.polynomial.Free (worlds.obj world) :=
  fun base index => ↾fun name => match base, name with
    | .unit, .original position => firing.children position
    | .unit, .derivative address available =>
        (firing.positive (positiveAddress firing.rule address available)).target

/-- The operational derivative getter is the supplied event's complete
endpoint. Original arguments follow their independently supplied sources. -/
theorem assignment_agrees
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    firing.rule.matchedInclusion _ firing.matching ≫
      assignmentAt Actions (actualGuard presentation.toLaw worlds steps world firing.children)
        (fun position => (firing.children position,
          Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _ (firing.children position))) rfl =
      firing.suppliedAssignment := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name with
  | original position => rfl
  | derivative address available =>
      change (Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
        (firing.children address.1) address.2).get _ =
          (firing.positive (positiveAddress firing.rule address available)).target
      obtain ⟨_, target⟩ := Option.eq_some_iff_get_eq.mp
        (firing.positive_step (positiveAddress firing.rule address available))
      exact target

/-- Contextual transport acts on each supplied positive occurrence, and
native negative predicates act on the same actual child-source maps. -/
noncomputable def map {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    Firing presentation worlds steps PremiseOrigins future operator action where
  origin := firing.origin
  children := (NativeGuard.children worlds operator).map change firing.children
  positive address := mapEvent presentation.toLaw worlds steps change (firing.positive address)
  positive_source address := congrArg (S.rename (worlds.map change)) (firing.positive_source address)
  positive_action address := firing.positive_action address
  negative address :=
    (noAction presentation.toLaw worlds steps SupportOrigin _ address.val.val.2).map change (firing.negative address)

theorem map_origin {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.map change).origin = firing.origin := rfl

theorem map_positive_origin {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (address : PositiveAddress firing.rule) :
    ((firing.map change).positive address).origin = (firing.positive address).origin := rfl

theorem map_positive_target {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (address : PositiveAddress firing.rule) :
    ((firing.map change).positive address).target =
      S.rename (worlds.map change) (firing.positive address).target := rfl

variable (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)
include consistent

/-- Local deterministic consistency gives the exact clause target, before
instantiating its original arguments and supplied derivatives. -/
theorem schema_readout (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    fromLaw Actions presentation.toLaw sort operator
        (actualGuard presentation.toLaw worlds steps world firing.children) action =
      some (S.rename (firing.rule.matchedInclusion _ firing.matching) firing.rule.target) := by
  change fromLaw Actions (DeterministicGSOS.toLaw Actions
    (FinitePresentation.toSchemas Actions presentation.readoutSet)) sort operator _ action = _
  rw [fromLaw_toLaw]
  exact FinitePresentation.toSchemas_firing Actions presentation.readoutSet consistent action _ firing.rule
    ⟨firing.origin, rfl⟩ firing.matching

/-- The actual conclusion retains the authored rule origin, not a selected
representative of the denotational set of clauses. -/
noncomputable def conclusion (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    Event presentation.toLaw worlds steps (presentation.Origin sort operator action) sort world :=
  behaviorRule presentation.toLaw worlds steps firing.origin world operator firing.children
    (actualGuard presentation.toLaw worlds steps world firing.children) action
    (S.rename (firing.rule.matchedInclusion _ firing.matching) firing.rule.target) rfl
    (firing.schema_readout consistent)

theorem conclusion_origin (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.conclusion consistent).origin = firing.origin := rfl

theorem conclusion_source (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.conclusion consistent).source = IndexedPolynomial.Free.node S.polynomial operator firing.children := rfl

/-- The entire authored target constructor tree is filled by the supplied
originals and positive endpoints, then flattened by the actual free monad. -/
theorem conclusion_target (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.conclusion consistent).target =
      IndexedPolynomial.Free.join S.polynomial (S.rename firing.suppliedAssignment firing.rule.target) := by
  change IndexedPolynomial.Free.join S.polynomial
    (S.rename (assignmentAt Actions _ _ rfl)
      (S.rename (firing.rule.matchedInclusion _ firing.matching) firing.rule.target)) = _
  have composed := IndexedPolynomial.Free.map_comp S.polynomial
    (fun base sort => firing.rule.matchedInclusion _ firing.matching base sort)
    (fun base sort => assignmentAt Actions
      (actualGuard presentation.toLaw worlds steps world firing.children)
      (fun position => (firing.children position,
        Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _ (firing.children position)))
      rfl base sort) firing.rule.target
  change S.rename (assignmentAt Actions _ _ rfl)
      (S.rename (firing.rule.matchedInclusion _ firing.matching) firing.rule.target) =
    S.rename (firing.rule.matchedInclusion _ firing.matching ≫ assignmentAt Actions _ _ rfl) firing.rule.target
      at composed
  rw [composed, firing.assignment_agrees]

/-- Exact contextual naturality of the independently authored firing result. -/
theorem conclusion_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    mapEvent presentation.toLaw worlds steps change (firing.conclusion consistent) =
      (firing.map change).conclusion consistent := by
  apply Event.ext
  · rfl
  · exact IndexedPolynomial.Free.map_node S.polynomial
      (fun base sort => worlds.map change base sort) operator firing.children
  · rfl
  · have carried := (mapEvent presentation.toLaw worlds steps change (firing.conclusion consistent)).valid
    have issued := ((firing.map change).conclusion consistent).valid
    have sources : (mapEvent presentation.toLaw worlds steps change (firing.conclusion consistent)).source =
        ((firing.map change).conclusion consistent).source :=
      IndexedPolynomial.Free.map_node S.polynomial (fun base sort => worlds.map change base sort)
        operator firing.children
    rw [sources] at carried
    exact Option.some.inj (carried.symm.trans issued)

/-- Native introduction retains this complete authored operational event
and the independently supplied dependent postcondition witness. -/
noncomputable def certificate
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :=
  (eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).introduce
    A world (firing.conclusion consistent) evidence

theorem certificate_event
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).eventReadout A).app
      world ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩ =
        firing.conclusion consistent := rfl

theorem certificate_result
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).resultReadout A).app
      world ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩ =
        ⟨(firing.conclusion consistent).target, evidence⟩ := rfl

/-- Substitution reads the actually transported authored conclusion. -/
theorem certificate_event_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).eventReadout A).app
      future ((totalSpace ((eventSpan presentation.toLaw worlds steps
        (presentation.Origin sort operator action) sort).certificates A)).map change
          ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩) =
      (firing.map change).conclusion consistent := by
  let span := eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort
  exact ((span.eventReadout_reindex A change
    ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩).trans
      (congrArg (span.events.map change) (firing.certificate_event consistent A evidence))).trans
        (firing.conclusion_natural consistent change)

/-- Substitution retains the complete endpoint and dependent evidence,
using the actual section action of the supplied target family. -/
theorem certificate_result_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).resultReadout A).app
      future ((totalSpace ((eventSpan presentation.toLaw worlds steps
        (presentation.Origin sort operator action) sort).certificates A)).map change
          ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩) =
      (totalSpace A).map change ⟨(firing.conclusion consistent).target, evidence⟩ := by
  let span := eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort
  exact (span.resultReadout_reindex A change
    ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩).trans
      (congrArg ((totalSpace A).map change) (firing.certificate_result consistent A evidence))

end Firing

/-- The complete finite-premise occurrences are a presheaf; no supplied
positive event is replaced by one chosen from its existential support. -/
noncomputable def firingFunctor (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) : Cᵒᵖ ⥤ Type u where
  obj world := Firing presentation worlds steps PremiseOrigins world operator action
  map change := ↾(Firing.map change)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply Firing.ext
    · rfl
    · exact ConcreteCategory.congr_hom ((NativeGuard.children worlds operator).map_id world) firing.children
    · apply heq_of_eq
      funext address
      exact ConcreteCategory.congr_hom
        ((events presentation.toLaw worlds steps PremiseOrigins _).map_id world) (firing.positive address)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply Firing.ext
    · rfl
    · exact ConcreteCategory.congr_hom
        ((NativeGuard.children worlds operator).map_comp earlier later) firing.children
    · apply heq_of_eq
      funext address
      exact ConcreteCategory.congr_hom
        ((events presentation.toLaw worlds steps PremiseOrigins _).map_comp earlier later) (firing.positive address)

/-- The actual operational conclusion is natural on complete retained
firings, including the authored clause origin. -/
noncomputable def conclusionMap
    (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)
    (PremiseOrigins : Type u) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) :
    firingFunctor presentation worlds steps PremiseOrigins operator action ⟶
      events presentation.toLaw worlds steps (presentation.Origin sort operator action) sort where
  app _ := ↾(Firing.conclusion consistent)
  naturality {first second} change := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact (firing.conclusion_natural consistent change).symm

/-- Every finite native guard has a retained firing when positive premise
identifiers can be supplied. Negative-only clauses need no premise edge. -/
theorem firing_exists_iff_nativeGuard (PremiseOrigins : Type u) [Nonempty PremiseOrigins]
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : presentation.Origin sort operator action) (world : Cᵒᵖ)
    (given : (NativeGuard.children worlds operator).obj world) :
    (∃ firing : Firing presentation worlds steps PremiseOrigins world operator action,
        firing.origin = origin ∧ firing.children = given) ↔
      given ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
        (presentation.rule sort operator action origin)).obj world := by
  constructor
  · rintro ⟨firing, rfl, rfl⟩
    exact firing.native_guard
  · intro holds
    have matching := (finiteGuard_iff_matches presentation.toLaw worlds steps _ world given).mp holds
    classical
    let positive : ∀ address : PositiveAddress (presentation.rule sort operator action origin),
        Event presentation.toLaw worlds steps PremiseOrigins (S.argument operator address.val.val.1) world :=
      fun address =>
        let available := (matching address.val.val address.val.property).trans address.property
        let input := Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
          (given address.val.val.1) address.val.val.2
        { origin := Classical.choice ‹Nonempty PremiseOrigins›
          source := given address.val.val.1
          action := address.val.val.2
          target := input.get available
          valid := (Option.some_get available).symm }
    refine ⟨⟨origin, given, positive, fun _ => rfl, fun _ => rfl, ?_⟩, rfl, rfl⟩
    intro address
    exact (premise_iff_guard presentation.toLaw worlds steps operator address.val.val false world given).mpr
      ((matching address.val.val address.val.property).trans address.property)

end Mettapedia.OSLF.DeterministicGSOS.NativeFiring
