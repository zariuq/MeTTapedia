import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassMembers

/-!
# Constructive material families and terms over observation classes

Nonempty canonical fibre predicates form a small observed base. A supplied
graph-valued family descends by union of its graph-family range. A selected
material section descends by enumerating every child of each family graph
that pictures the section value, followed by range and union. No source,
graph occurrence, or graph of the section value is selected.

Family invariance and selected-value compatibility remain distinct laws.
The class carrier uses full proposition-valued subsets of the source; the
material decoders use graph-family range and union. These constructions do
not assert their availability in an exponentiation-only foundation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent

open AccessiblePointedGraph
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent

universe u v w

variable {Source : Type u} {Target : Type v}

def observationFibre (observe : Source → Target) (source : Source) : Set Source :=
  {other | observe other = observe source}

/-- The represented observation classes, without a selected source witness. -/
def ObservationClass (observe : Source → Target) : Type u :=
  {predicate : Set Source // ∃ source, predicate = observationFibre observe source}

def classOf (observe : Source → Target) (source : Source) : ObservationClass observe :=
  ⟨observationFibre observe source, source, rfl⟩

theorem classOf_eq_iff (observe : Source → Target) (left right : Source) :
    classOf observe left = classOf observe right ↔ observe left = observe right := by
  constructor
  · intro same
    have predicates := congrArg Subtype.val same
    have predicates' : observationFibre observe left = observationFibre observe right := predicates
    have holds : left ∈ observationFibre observe right := by
      rw [← predicates']
      rfl
    exact holds
  · intro same
    apply Subtype.ext
    funext source
    exact propext ⟨fun member => member.trans same, fun member => member.trans same.symm⟩

theorem classOf_surjective (observe : Source → Target) : Function.Surjective (classOf observe) := by
  intro observed
  obtain ⟨source, same⟩ := observed.2
  exact ⟨source, Subtype.ext same.symm⟩

theorem classOf_of_mem (observe : Source → Target) (observed : ObservationClass observe)
    (source : Source) (member : source ∈ observed.1) : classOf observe source = observed := by
  obtain ⟨representative, same⟩ := observed.2
  have related : observe source = observe representative := by
    rw [same] at member
    exact member
  exact ((classOf_eq_iff observe source representative).mpr related).trans (Subtype.ext same.symm)

def FamilyInvariant (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u}) : Prop :=
  ∀ ⦃left right⦄, observe left = observe right → HSet.mk (graphs left) = HSet.mk (graphs right)

def familyRange (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) : HSet.{u} :=
  HSet.range (fun source : {source // source ∈ observed.1} => graphs source.1)

def decodedFamily (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) : HSet.{u} :=
  HSet.sUnion (familyRange graphs observed)

theorem familyRange_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (source : Source) :
    familyRange graphs (classOf observe source) = {HSet.mk (graphs source)} := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨witness, same⟩ := HSet.mem_range.mp member
    exact HSet.mem_singleton.mpr (same.symm.trans (invariant witness.2))
  · intro member
    exact HSet.mem_range.mpr ⟨⟨source, rfl⟩, (HSet.mem_singleton.mp member).symm⟩

theorem family_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (source : Source) :
    decodedFamily graphs (classOf observe source) = HSet.mk (graphs source) := by
  rw [decodedFamily, familyRange_beta observe graphs invariant, HSet.sUnion_singleton]

theorem family_at_class (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (observed : ObservationClass observe)
    (source : Source) (member : source ∈ observed.1) :
    decodedFamily graphs observed = HSet.mk (graphs source) :=
  (congrArg (decodedFamily graphs) (classOf_of_mem observe observed source member).symm).trans
    (family_beta observe graphs invariant source)

theorem familyInvariant_iff_beta (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) :
    FamilyInvariant observe graphs ↔
      ∀ source, decodedFamily graphs (classOf observe source) = HSet.mk (graphs source) := by
  constructor
  · exact family_beta observe graphs
  · intro reflects left right same
    exact (reflects left).symm.trans
      ((congrArg (decodedFamily graphs) ((classOf_eq_iff observe left right).mpr same)).trans
        (reflects right))

/-- Enumerate all children of all family graphs represented in this class. -/
def FamilyChild (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) : Type u :=
  Σ source : {source // source ∈ observed.1},
    {child : (graphs source.1).Node // (graphs source.1).edge (graphs source.1).point child}

/-- An explicit graph for the descended family, constructed from the supplied
family graphs without a presentation selector. -/
def familyGraph (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) : AccessiblePointedGraph.{u} :=
  sup (fun child : FamilyChild graphs observed => (graphs child.1.1).repoint child.2.1)

theorem familyGraph_decode (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) :
    HSet.mk (familyGraph graphs observed) = decodedFamily graphs observed := by
  apply HSet.ext
  intro value
  change value ∈ HSet.range (fun child : FamilyChild graphs observed =>
    (graphs child.1.1).repoint child.2.1) ↔ value ∈ HSet.sUnion (familyRange graphs observed)
  rw [HSet.mem_range, HSet.mem_sUnion]
  constructor
  · rintro ⟨⟨source, child⟩, same⟩
    refine ⟨HSet.mk (graphs source.1), HSet.mem_range.mpr ⟨source, rfl⟩, ?_⟩
    exact HSet.mem_mk.mpr ⟨child.1, child.2, same⟩
  · rintro ⟨set, inRange, member⟩
    obtain ⟨source, rfl⟩ := HSet.mem_range.mp inRange
    obtain ⟨child, edge, same⟩ := HSet.mem_mk.mp member
    exact ⟨⟨source, ⟨child, edge⟩⟩, same⟩

private theorem memberTransport_value {X Y : HSet.{u}} (same : X = Y)
    (member : El (· ∈ ·) X) :
    (equalityEquiv (congrArg (fun Z => El (· ∈ ·) Z) same) member).1 = member.1 := by
  cases same
  rfl

/-- The constructed material family gives an actual typed factorization. -/
def familyFactorization (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) :
    FamilyFactorization (classOf observe) (fun source => El (· ∈ ·) (HSet.mk (graphs source))) where
  targetFamily observed := El (· ∈ ·) (decodedFamily graphs observed)
  identify source := equalityEquiv
    (congrArg (fun set => El (· ∈ ·) set) (family_beta observe graphs invariant source).symm)

theorem identify_value (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (source : Source)
    (member : El (· ∈ ·) (HSet.mk (graphs source))) :
    ((familyFactorization observe graphs invariant).identify source member).1 = member.1 :=
  memberTransport_value (family_beta observe graphs invariant source).symm member

theorem identify_symm_value (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (source : Source)
    (member : El (· ∈ ·) (decodedFamily graphs (classOf observe source))) :
    (((familyFactorization observe graphs invariant).identify source).symm member).1 = member.1 := by
  have same := identify_value observe graphs invariant source
    (((familyFactorization observe graphs invariant).identify source).symm member)
  exact same.symm.trans (congrArg (fun value => value.1)
    (((familyFactorization observe graphs invariant).identify source).apply_symm_apply member))

abbrev SourceSection (graphs : Source → AccessiblePointedGraph.{u}) :=
  (source : Source) → El (· ∈ ·) (HSet.mk (graphs source))

def TermCompatible (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (term : SourceSection graphs) : Prop :=
  ∀ ⦃left right⦄, observe left = observe right → (term left).1 = (term right).1

/-- Every child that pictures the selected value is retained as enumeration
data. Mere membership is never turned into a chosen child. -/
def TermChild (graphs : Source → AccessiblePointedGraph.{u}) (term : SourceSection graphs)
    {observe : Source → Target} (observed : ObservationClass observe) : Type u :=
  Σ source : {source // source ∈ observed.1},
    {child : (graphs source.1).Node //
      (graphs source.1).edge (graphs source.1).point child ∧
        HSet.decorate (graphs source.1).edge child = (term source.1).1}

def termRange (graphs : Source → AccessiblePointedGraph.{u}) (term : SourceSection graphs)
    {observe : Source → Target} (observed : ObservationClass observe) : HSet.{u} :=
  HSet.range (fun child : TermChild graphs term observed => (graphs child.1.1).repoint child.2.1)

def termValue (graphs : Source → AccessiblePointedGraph.{u}) (term : SourceSection graphs)
    {observe : Source → Target} (observed : ObservationClass observe) : HSet.{u} :=
  HSet.sUnion (termRange graphs term observed)

theorem termRange_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (term : SourceSection graphs) (compatible : TermCompatible observe graphs term) (source : Source) :
    termRange graphs term (classOf observe source) = {(term source).1} := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    obtain ⟨⟨witness, child⟩, same⟩ := HSet.mem_range.mp member
    exact HSet.mem_singleton.mpr (same.symm.trans
      (child.2.2.trans (compatible witness.2)))
  · intro member
    obtain ⟨child, edge, same⟩ := HSet.mem_mk.mp (term source).2
    exact HSet.mem_range.mpr ⟨⟨⟨source, rfl⟩, ⟨child, edge, same⟩⟩,
      same.trans (HSet.mem_singleton.mp member).symm⟩

theorem termValue_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (term : SourceSection graphs) (compatible : TermCompatible observe graphs term) (source : Source) :
    termValue graphs term (classOf observe source) = (term source).1 := by
  rw [termValue, termRange_beta observe graphs term compatible, HSet.sUnion_singleton]

theorem termCompatible_iff_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (term : SourceSection graphs) :
    TermCompatible observe graphs term ↔
      ∀ source, termValue graphs term (classOf observe source) = (term source).1 := by
  constructor
  · exact termValue_beta observe graphs term
  · intro reflects left right same
    exact (reflects left).symm.trans
      ((congrArg (termValue graphs term) ((classOf_eq_iff observe left right).mpr same)).trans
        (reflects right))

/-- This section is an actual material-value decoder plus a membership proof.
Only the membership proof eliminates the existential class witness. -/
def descendTerm (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) :
    ∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed) :=
  fun observed => ⟨termValue graphs term observed, by
    obtain ⟨source, same⟩ := classOf_surjective observe observed
    rw [← same, termValue_beta observe graphs term compatible, family_beta observe graphs invariant]
    exact (term source).2⟩

theorem descendTerm_beta_value (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) (source : Source) :
    (descendTerm observe graphs invariant term compatible (classOf observe source)).1 = (term source).1 :=
  termValue_beta observe graphs term compatible source

theorem descendTerm_beta (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) (source : Source) :
    descendTerm observe graphs invariant term compatible (classOf observe source) =
      (familyFactorization observe graphs invariant).identify source (term source) :=
  El.ext HSet.propositional
    ((descendTerm_beta_value observe graphs invariant term compatible source).trans
      (identify_value observe graphs invariant source (term source)).symm)

def pullSection (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs)
    (term : ∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) :
    SourceSection graphs :=
  liftSection (familyFactorization observe graphs invariant) term

theorem pullSection_value (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs)
    (term : ∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed))
    (source : Source) :
    (pullSection observe graphs invariant term source).1 = (term (classOf observe source)).1 :=
  identify_symm_value observe graphs invariant source (term (classOf observe source))

theorem pullSection_compatible (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs)
    (term : ∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) :
    TermCompatible observe graphs (pullSection observe graphs invariant term) := by
  intro left right same
  exact (pullSection_value observe graphs invariant term left).trans
    ((congrArg (fun observed => (term observed).1) ((classOf_eq_iff observe left right).mpr same)).trans
      (pullSection_value observe graphs invariant term right).symm)

theorem pull_descendTerm (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) :
    pullSection observe graphs invariant (descendTerm observe graphs invariant term compatible) = term := by
  funext source
  apply El.ext HSet.propositional
  exact (pullSection_value observe graphs invariant _ source).trans
    (descendTerm_beta_value observe graphs invariant term compatible source)

theorem descend_pullSection (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs)
    (term : ∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) :
    descendTerm observe graphs invariant (pullSection observe graphs invariant term)
      (pullSection_compatible observe graphs invariant term) = term := by
  funext observed
  obtain ⟨source, rfl⟩ := classOf_surjective observe observed
  apply El.ext HSet.propositional
  exact (descendTerm_beta_value observe graphs invariant _ _ source).trans
    (pullSection_value observe graphs invariant term source)

/-- Observed sections and compatible source sections are equivalent by actual
material decoders, with no supplied split readout. -/
def materialSectionEquiv (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) :
    (∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) ≃
      {term : SourceSection graphs // TermCompatible observe graphs term} where
  toFun term := ⟨pullSection observe graphs invariant term, pullSection_compatible observe graphs invariant term⟩
  invFun term := descendTerm observe graphs invariant term.1 term.2
  left_inv := descend_pullSection observe graphs invariant
  right_inv term := Subtype.ext (pull_descendTerm observe graphs invariant term.1 term.2)

section Reindex

variable {Source' : Type u} {Target' : Type w}

/-- Complete the image of a source class to the entire old observation fibre.
This is a predicate construction, rather than a chosen image representative. -/
def classMap (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (observed : ObservationClass observe') : ObservationClass observe :=
  ⟨{source | ∃ witness : Source', witness ∈ observed.1 ∧
      observe source = observe (sourceMap witness)}, by
    obtain ⟨source, same⟩ := observed.2
    refine ⟨sourceMap source, ?_⟩
    funext candidate
    apply propext
    constructor
    · rintro ⟨witness, member, endpointEq⟩
      have related : observe' witness = observe' source := by
        rw [same] at member
        exact member
      exact endpointEq.trans ((commutes witness).trans
        ((congrArg targetMap related).trans (commutes source).symm))
    · intro endpointEq
      exact ⟨source, by rw [same]; rfl, endpointEq⟩⟩

theorem classMap_beta (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (source : Source') :
    classMap observe observe' sourceMap targetMap commutes (classOf observe' source) =
      classOf observe (sourceMap source) := by
  apply Subtype.ext
  funext candidate
  apply propext
  constructor
  · rintro ⟨witness, related, endpointEq⟩
    exact endpointEq.trans ((commutes witness).trans
      ((congrArg targetMap related).trans (commutes source).symm))
  · intro endpointEq
    exact ⟨source, rfl, endpointEq⟩

theorem classMap_id (observe : Source → Target) :
    classMap observe observe id id (fun _ => rfl) = id := by
  funext observed
  obtain ⟨source, rfl⟩ := classOf_surjective observe observed
  exact classMap_beta observe observe id id (fun _ => rfl) source

theorem classMap_comp {Source'' : Type u} {Target'' : Type*}
    (observe : Source → Target) (observe' : Source' → Target') (observe'' : Source'' → Target'')
    (firstSource : Source' → Source) (firstTarget : Target' → Target)
    (firstSquare : ∀ source, observe (firstSource source) = firstTarget (observe' source))
    (secondSource : Source'' → Source') (secondTarget : Target'' → Target')
    (secondSquare : ∀ source, observe' (secondSource source) = secondTarget (observe'' source)) :
    (classMap observe observe' firstSource firstTarget firstSquare) ∘
        (classMap observe' observe'' secondSource secondTarget secondSquare) =
      classMap observe observe'' (firstSource ∘ secondSource) (firstTarget ∘ secondTarget)
        (fun source => (firstSquare _).trans (congrArg firstTarget (secondSquare source))) := by
  funext observed
  obtain ⟨source, rfl⟩ := classOf_surjective observe'' observed
  simp only [Function.comp_apply, classMap_beta]

theorem reindexInvariant (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs) :
    FamilyInvariant observe' (graphs ∘ sourceMap) := by
  intro left right related
  exact invariant ((commutes left).trans ((congrArg targetMap related).trans (commutes right).symm))

theorem reindexCompatible (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (graphs : Source → AccessiblePointedGraph.{u}) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) :
    TermCompatible observe' (graphs ∘ sourceMap) (fun source => term (sourceMap source)) := by
  intro left right related
  exact compatible ((commutes left).trans ((congrArg targetMap related).trans (commutes right).symm))

/-- The separately constructed class decoder commutes with actual restriction
of the supplied graph family. -/
theorem decodedFamily_reindex (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (observed : ObservationClass observe') :
    decodedFamily (graphs ∘ sourceMap) observed =
      decodedFamily graphs (classMap observe observe' sourceMap targetMap commutes observed) := by
  obtain ⟨source, rfl⟩ := classOf_surjective observe' observed
  rw [classMap_beta, family_beta observe' (graphs ∘ sourceMap)
    (reindexInvariant observe observe' sourceMap targetMap commutes graphs invariant),
    family_beta observe graphs invariant]
  rfl

theorem termValue_reindex (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (graphs : Source → AccessiblePointedGraph.{u}) (term : SourceSection graphs)
    (compatible : TermCompatible observe graphs term) (observed : ObservationClass observe') :
    termValue (graphs ∘ sourceMap) (fun source => term (sourceMap source)) observed =
      termValue graphs term (classMap observe observe' sourceMap targetMap commutes observed) := by
  obtain ⟨source, rfl⟩ := classOf_surjective observe' observed
  rw [classMap_beta, termValue_beta observe' (graphs ∘ sourceMap) _
    (reindexCompatible observe observe' sourceMap targetMap commutes graphs term compatible),
    termValue_beta observe graphs term compatible]

theorem descendTerm_reindex_value (observe : Source → Target) (observe' : Source' → Target')
    (sourceMap : Source' → Source) (targetMap : Target' → Target)
    (commutes : ∀ source, observe (sourceMap source) = targetMap (observe' source))
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (term : SourceSection graphs) (compatible : TermCompatible observe graphs term)
    (observed : ObservationClass observe') :
    (descendTerm observe' (graphs ∘ sourceMap)
        (reindexInvariant observe observe' sourceMap targetMap commutes graphs invariant)
        (fun source => term (sourceMap source))
        (reindexCompatible observe observe' sourceMap targetMap commutes graphs term compatible)
        observed).1 =
      (descendTerm observe graphs invariant term compatible
        (classMap observe observe' sourceMap targetMap commutes observed)).1 :=
  termValue_reindex observe observe' sourceMap targetMap commutes graphs term compatible observed

end Reindex

/-- In material comprehension, equality uses the observed base and actual
member value. Membership proof irrelevance does not erase source occurrences. -/
theorem totalElPair_eq_iff {Base : Type*} (family : Base → HSet.{u})
    (left right : Σ base, El (· ∈ ·) (family base)) :
    left = right ↔ left.1 = right.1 ∧ left.2.1 = right.2.1 := by
  constructor
  · intro same
    exact ⟨congrArg Sigma.fst same, congrArg (fun value => value.2.1) same⟩
  · rintro ⟨baseEq, valueEq⟩
    obtain ⟨leftBase, leftMember⟩ := left
    obtain ⟨rightBase, rightMember⟩ := right
    dsimp at baseEq valueEq
    cases baseEq
    exact congrArg (Sigma.mk leftBase) (El.ext HSet.propositional valueEq)

theorem totalObservation_eq_iff (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (left right : Σ source, El (· ∈ ·) (HSet.mk (graphs source))) :
    (familyFactorization observe graphs invariant).totalObservation left =
        (familyFactorization observe graphs invariant).totalObservation right ↔
      observe left.1 = observe right.1 ∧ left.2.1 = right.2.1 := by
  have pairs := totalElPair_eq_iff (decodedFamily graphs)
    ((familyFactorization observe graphs invariant).totalObservation left)
    ((familyFactorization observe graphs invariant).totalObservation right)
  refine pairs.trans ?_
  change classOf observe left.1 = classOf observe right.1 ∧
    ((familyFactorization observe graphs invariant).identify left.1 left.2).1 =
      ((familyFactorization observe graphs invariant).identify right.1 right.2).1 ↔ _
  rw [classOf_eq_iff, identify_value, identify_value]

theorem compatible_iff_termCompatible (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (term : SourceSection graphs) :
    Compatible (familyFactorization observe graphs invariant) term ↔ TermCompatible observe graphs term := by
  constructor
  · intro compatible left right related
    exact ((totalObservation_eq_iff observe graphs invariant _ _).mp
      (compatible left right ((classOf_eq_iff observe left right).mpr related))).2
  · intro compatible left right related
    exact (totalObservation_eq_iff observe graphs invariant _ _).mpr
      ⟨(classOf_eq_iff observe left right).mp related,
        compatible ((classOf_eq_iff observe left right).mp related)⟩

/-- Small data for each actual decoded material fibre, constructed from its
explicit all-children graph rather than a presentation of arbitrary sets. -/
def FamilyMemberModel (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) : Type u :=
  PowerMemberClass (familyGraph graphs observed)

def familyMemberEquiv (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe) :
    FamilyMemberModel graphs observed ≃ El (· ∈ ·) (decodedFamily graphs observed) :=
  (powerElEquiv (familyGraph graphs observed)).trans (equalityEquiv
    (congrArg (fun set => El (· ∈ ·) set)
      ((picture_eq_mk _).trans (familyGraph_decode graphs observed))))

theorem familyMemberEquiv_value (graphs : Source → AccessiblePointedGraph.{u})
    {observe : Source → Target} (observed : ObservationClass observe)
    (member : FamilyMemberModel graphs observed) :
    (familyMemberEquiv graphs observed member).1 =
      classValue (familyGraph graphs observed) member.1 :=
  memberTransport_value ((picture_eq_mk _).trans (familyGraph_decode graphs observed)) _

def ObservedSectionModel (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u}) : Type u :=
  ∀ observed : ObservationClass observe, FamilyMemberModel graphs observed

def observedSectionEquiv (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u}) :
    ObservedSectionModel observe graphs ≃
      (∀ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) :=
  Equiv.piCongrRight (familyMemberEquiv graphs)

/-- A same-bound carrier for compatible source sections. Both inverse maps are
constructed, with the decoded values and their actual membership retained. -/
def compatibleSectionEquiv (observe : Source → Target) (graphs : Source → AccessiblePointedGraph.{u})
    (invariant : FamilyInvariant observe graphs) :
    ObservedSectionModel observe graphs ≃
      {term : SourceSection graphs // TermCompatible observe graphs term} :=
  (observedSectionEquiv observe graphs).trans (materialSectionEquiv observe graphs invariant)

theorem compatibleSectionEquiv_value (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) (invariant : FamilyInvariant observe graphs)
    (term : ObservedSectionModel observe graphs) (source : Source) :
    ((compatibleSectionEquiv observe graphs invariant term).1 source).1 =
      classValue (familyGraph graphs (classOf observe source)) (term (classOf observe source)).1 :=
  (pullSection_value observe graphs invariant _ source).trans
    (familyMemberEquiv_value graphs _ _)

def ObservedComprehensionModel (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) : Type u :=
  Σ observed : ObservationClass observe, FamilyMemberModel graphs observed

def observedComprehensionEquiv (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) :
    ObservedComprehensionModel observe graphs ≃
      (Σ observed : ObservationClass observe, El (· ∈ ·) (decodedFamily graphs observed)) where
  toFun member := ⟨member.1, familyMemberEquiv graphs member.1 member.2⟩
  invFun member := ⟨member.1, (familyMemberEquiv graphs member.1).symm member.2⟩
  left_inv member := congrArg (Sigma.mk member.1) ((familyMemberEquiv graphs member.1).symm_apply_apply member.2)
  right_inv member := congrArg (Sigma.mk member.1) ((familyMemberEquiv graphs member.1).apply_symm_apply member.2)

theorem observedComprehensionEquiv_projection (observe : Source → Target)
    (graphs : Source → AccessiblePointedGraph.{u}) (member : ObservedComprehensionModel observe graphs) :
    (observedComprehensionEquiv observe graphs member).1 = member.1 := rfl

namespace Controls

abbrev TaggedStage : Type u := ULift.{u} Bool × ULift.{u} Bool

def stageObservation (source : TaggedStage.{u}) : Bool := source.1.down

def stageGraph : Bool → AccessiblePointedGraph.{u}
  | false => empty
  | true => twoChildren

def varyingGraphs (source : TaggedStage.{u}) : AccessiblePointedGraph.{u} :=
  stageGraph (stageObservation source)

def stage (level tag : Bool) : TaggedStage.{u} := ⟨⟨level⟩, ⟨tag⟩⟩

theorem varying_invariant : FamilyInvariant stageObservation varyingGraphs.{u} := by
  intro left right same
  exact congrArg (fun level => HSet.mk (stageGraph level)) same

theorem varying_empty :
    decodedFamily varyingGraphs (classOf stageObservation (stage.{u} false false)) = ∅ :=
  (family_beta stageObservation varyingGraphs varying_invariant _).trans HSet.mk_empty

theorem varying_nonempty :
    decodedFamily varyingGraphs (classOf stageObservation (stage.{u} true false)) = {∅} :=
  (family_beta stageObservation varyingGraphs varying_invariant _).trans mk_twoChildren

theorem genuinely_nonconstant :
    decodedFamily varyingGraphs (classOf stageObservation (stage.{u} false false)) ≠
      decodedFamily varyingGraphs (classOf stageObservation (stage true false)) := by
  rw [varying_empty, varying_nonempty]
  exact HSet.empty_ne_singleton_empty

theorem varying_no_section :
    ¬ Nonempty (∀ observed : ObservationClass stageObservation.{u},
      El (· ∈ ·) (decodedFamily varyingGraphs observed)) := by
  rintro ⟨term⟩
  let value := (term (classOf stageObservation (stage false false))).1
  have member : value ∈ decodedFamily varyingGraphs (classOf stageObservation (stage false false)) :=
    (term (classOf stageObservation (stage false false))).2
  rw [varying_empty] at member
  exact HSet.notMem_empty _ member

def selectedGraph : Bool → AccessiblePointedGraph.{u}
  | false => empty
  | true => oneChild empty

def alternatives : AccessiblePointedGraph.{u} :=
  sup fun tag : ULift.{u} Bool => selectedGraph tag.down

def duplicateGraphs (_source : Occurrence twoChildren.{u}) : AccessiblePointedGraph.{u} :=
  alternatives

def duplicateTerm (source : Occurrence twoChildren.{u}) : El (· ∈ ·) (HSet.mk (duplicateGraphs source)) :=
  ⟨HSet.mk (selectedGraph (edgeTag source)),
    HSet.mem_range.mpr ⟨⟨edgeTag source⟩, rfl⟩⟩

theorem duplicate_family_invariant :
    FamilyInvariant (memberObservation twoChildren.{u}) duplicateGraphs := by
  intro _ _ _
  rfl

theorem duplicate_term_true : (duplicateTerm (twoChildrenOccurrence.{u} true)).1 = {∅} :=
  (picture_eq_mk _).symm.trans picture_oneChild_empty

theorem duplicate_term_false : (duplicateTerm (twoChildrenOccurrence.{u} false)).1 = ∅ :=
  HSet.mk_empty

theorem duplicate_term_not_compatible :
    ¬ TermCompatible (memberObservation twoChildren.{u}) duplicateGraphs duplicateTerm := by
  intro compatible
  have same := compatible twoChildren_same_member
  have values : (∅ : HSet.{u}) = {∅} := duplicate_term_false.symm.trans
    (same.symm.trans duplicate_term_true)
  exact HSet.empty_ne_singleton_empty values

theorem duplicate_term_no_descent :
    ¬ ∃ observedTerm : ∀ observed : ObservationClass (memberObservation twoChildren.{u}),
        El (· ∈ ·) (decodedFamily duplicateGraphs observed),
      ∀ source, (observedTerm (classOf (memberObservation twoChildren) source)).1 =
        (duplicateTerm source).1 := by
  rintro ⟨observedTerm, reflects⟩
  apply duplicate_term_not_compatible
  intro left right same
  exact (reflects left).symm.trans
    ((congrArg (fun observed => (observedTerm observed).1)
      ((classOf_eq_iff _ left right).mpr same)).trans (reflects right))

def cyclicGraphs (_source : Occurrence twoChildren.{u}) : AccessiblePointedGraph.{u} := HSet.loop

def cyclicTerm (_source : Occurrence twoChildren.{u}) : El (· ∈ ·) (HSet.mk (cyclicGraphs _source)) :=
  ⟨HSet.quineAtom, by rw [cyclicGraphs, HSet.mk_loop]; exact HSet.quineAtom_mem_self⟩

theorem cyclic_invariant : FamilyInvariant (memberObservation twoChildren.{u}) cyclicGraphs := by
  intro _ _ _
  rfl

theorem cyclic_compatible : TermCompatible (memberObservation twoChildren.{u}) cyclicGraphs cyclicTerm := by
  intro _ _ _
  rfl

theorem cyclic_decoder_beta (source : Occurrence twoChildren.{u}) :
    (descendTerm (memberObservation twoChildren) cyclicGraphs cyclic_invariant cyclicTerm cyclic_compatible
      (classOf (memberObservation twoChildren) source)).1 = HSet.quineAtom :=
  descendTerm_beta_value _ _ _ _ _ source

theorem cyclic_decoder_not_wf (source : Occurrence twoChildren.{u}) :
    ¬ (descendTerm (memberObservation twoChildren) cyclicGraphs cyclic_invariant cyclicTerm cyclic_compatible
      (classOf (memberObservation twoChildren) source)).1.WF := by
  rw [cyclic_decoder_beta]
  exact HSet.not_wf_quineAtom

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
