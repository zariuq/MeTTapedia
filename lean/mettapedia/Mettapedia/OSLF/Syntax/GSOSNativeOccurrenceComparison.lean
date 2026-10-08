import Mettapedia.OSLF.Syntax.GSOSNativeFiringOccurrences

/-!
# Occurrence expansion, normalization and complete native receipts

An authored finite positive-premise inventory may repeat an address. Expanding
a normalized firing duplicates its selected edge at those positions, while
normalizing selects one of the original occurrences. Expansion is a section
of normalization; the converse need not hold. The occurrence event span
retains the entire inventory and the exact dependent target certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeFiring

open _root_.CategoryTheory Mettapedia.TypeTheory EdgeReadout NativeGuard
open PresheafEventCertificates DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]
variable (presentation : AuthoredFinitePresentation (S := S) Actions)
variable (inventories : ∀ sort operator action (origin : presentation.Origin sort operator action),
  PositiveInventory (presentation.rule sort operator action origin))
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

namespace OccurrenceFiring

variable {presentation inventories worlds steps}
variable {PremiseOrigins : Type u} {sort : S.Srt}
variable {operator : S.Operator sort} {action : Actions sort} {world : Cᵒᵖ}

private abbrev Packet (given : (NativeGuard.children worlds operator).obj world)
    {rule : FiniteRule Actions operator} (address : PositiveAddress rule) :=
  {event : Event presentation.toLaw worlds steps PremiseOrigins
      (S.argument operator address.val.val.1) world //
    event.source = given address.val.val.1 ∧ event.action = address.val.val.2}

private noncomputable def mapPacket {future : Cᵒᵖ} (change : world ⟶ future)
    {given : (NativeGuard.children worlds operator).obj world}
    {rule : FiniteRule Actions operator} {address : PositiveAddress rule}
    (packet : Packet (presentation := presentation) (steps := steps) (PremiseOrigins := PremiseOrigins)
      given address) :
    Packet (presentation := presentation) (steps := steps) (PremiseOrigins := PremiseOrigins)
      ((NativeGuard.children worlds operator).map change given) address :=
  ⟨mapEvent presentation.toLaw worlds steps change packet.val,
    congrArg (S.rename (worlds.map change)) packet.property.1, packet.property.2⟩

private theorem mapPacket_transport {future : Cᵒᵖ} (change : world ⟶ future)
    {given : (NativeGuard.children worlds operator).obj world}
    {rule : FiniteRule Actions operator} (first second : PositiveAddress rule)
    (same : first = second)
    (packet : Packet (presentation := presentation) (steps := steps) (PremiseOrigins := PremiseOrigins)
      given first) :
    mapPacket change (same ▸ packet) = same ▸ mapPacket change packet := by
  subst second
  rfl

private theorem section_transport
    {given : (NativeGuard.children worlds operator).obj world}
    {rule : FiniteRule Actions operator}
    (supplied : ∀ address : PositiveAddress rule,
      Packet (presentation := presentation) (steps := steps) (PremiseOrigins := PremiseOrigins)
        given address)
    (first second : PositiveAddress rule) (same : first = second) :
    same ▸ supplied first = supplied second := by
  subst second
  rfl

/-- Selection commutes with the actual map of every supplied occurrence;
the coverage witness and selected inventory position are world-independent. -/
theorem selected_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (address : PositiveAddress (presentation.rule sort operator action firing.origin)) :
    mapEvent presentation.toLaw worlds steps change (firing.selected address).val =
      ((firing.map change).selected address).val := by
  let chosen := (inventories sort operator action firing.origin).select address
  have comparison := mapPacket_transport change _ _ chosen.property
    (⟨firing.positive chosen.val, firing.positive_source chosen.val,
      firing.positive_action chosen.val⟩ : Packet firing.children _)
  exact congrArg Subtype.val comparison

/-- Normalization is natural on the full independently supplied history. -/
theorem normalize_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :
    firing.normalize.map change = (firing.map change).normalize := by
  apply Firing.ext
  · rfl
  · rfl
  · apply heq_of_eq
    funext address
    exact firing.selected_natural change address

end OccurrenceFiring

namespace Firing

variable {presentation inventories worlds steps}
variable {PremiseOrigins : Type u} {sort : S.Srt}
variable {operator : S.Operator sort} {action : Actions sort} {world : Cᵒᵖ}

/-- Every authored positive position receives the corresponding supplied
normalized edge. This duplicates data only where the inventory repeats an
address, and does not invent a new premise occurrence identifier. -/
noncomputable def expand
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action where
  origin := firing.origin
  children := firing.children
  positive position := firing.positive ((inventories sort operator action firing.origin).address position)
  positive_source position := firing.positive_source ((inventories sort operator action firing.origin).address position)
  positive_action position := firing.positive_action ((inventories sort operator action firing.origin).address position)
  negative := firing.negative

theorem expand_positive
    (firing : Firing presentation worlds steps PremiseOrigins world operator action)
    (position : (inventories sort operator action firing.origin).Position) :
    (firing.expand (inventories := inventories)).positive position =
      firing.positive ((inventories sort operator action firing.origin).address position) := rfl

/-- Expansion is a section of normalization, not an equivalence of the
distinct supplied premise histories. -/
theorem normalize_expand
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.expand (inventories := inventories)).normalize = firing := by
  apply Firing.ext
  · rfl
  · rfl
  · apply heq_of_eq
    funext address
    let chosen := (inventories sort operator action firing.origin).select address
    have comparison := OccurrenceFiring.section_transport
      (fun address => ⟨firing.positive address, firing.positive_source address,
        firing.positive_action address⟩) _ _ chosen.property
    exact congrArg Subtype.val comparison

theorem expand_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : Firing presentation worlds steps PremiseOrigins world operator action) :
    (firing.expand (inventories := inventories)).map change = (firing.map change).expand := by
  apply OccurrenceFiring.ext
  · rfl
  · rfl
  · rfl

end Firing

/-- The natural normalization comparison retains the chosen positive
edge at every normalized address and the complete rule origin. -/
noncomputable def normalizationMap (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :
    occurrenceFunctor presentation inventories worlds steps PremiseOrigins operator action ⟶
      firingFunctor presentation worlds steps PremiseOrigins operator action where
  app _ := ↾OccurrenceFiring.normalize
  naturality {first second} change := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact (firing.normalize_natural change).symm

noncomputable def expansionMap (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :
    firingFunctor presentation worlds steps PremiseOrigins operator action ⟶
      occurrenceFunctor presentation inventories worlds steps PremiseOrigins operator action where
  app _ := ↾Firing.expand
  naturality {first second} change := by
    apply ConcreteCategory.hom_ext
    intro firing
    exact (firing.expand_natural change).symm

theorem expansion_normalization (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :
    expansionMap presentation inventories worlds steps PremiseOrigins operator action ≫
      normalizationMap presentation inventories worlds steps PremiseOrigins operator action = 𝟙 _ := by
  ext world firing
  exact firing.normalize_expand

/-- The native finite guard is exactly the support of authored firings
when positive event identifiers are inhabited. Supplied firings themselves
need no global inhabitance, including the negative-only case. -/
theorem occurrence_exists_iff_nativeGuard (PremiseOrigins : Type u) [Nonempty PremiseOrigins]
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : presentation.Origin sort operator action) (world : Cᵒᵖ)
    (given : (NativeGuard.children worlds operator).obj world) :
    (∃ firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action,
      firing.origin = origin ∧ firing.children = given) ↔
      given ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
        (presentation.rule sort operator action origin)).obj world := by
  constructor
  · rintro ⟨firing, rfl, rfl⟩
    exact firing.native_guard
  · intro holds
    obtain ⟨firing, originRead, childrenRead⟩ :=
      (firing_exists_iff_nativeGuard presentation worlds steps PremiseOrigins operator action origin world given).mpr holds
    exact ⟨firing.expand, originRead, childrenRead⟩

/-- A supplied identifier at each actual positive position realizes the
native guard. There is no global inhabitance requirement: a negative-only
inventory can have an empty identifier carrier. Endpoints are computed by
the actual operational transition, independently at every position. -/
noncomputable def realizeGuard (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : presentation.Origin sort operator action) (world : Cᵒᵖ)
    (given : (NativeGuard.children worlds operator).obj world)
    (identifiers : (inventories sort operator action origin).Position → PremiseOrigins)
    (holds : given ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
      (presentation.rule sort operator action origin)).obj world) :
    OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action := by
  have matching := (finiteGuard_iff_matches presentation.toLaw worlds steps _ world given).mp holds
  let positive : ∀ position : (inventories sort operator action origin).Position,
      Event presentation.toLaw worlds steps PremiseOrigins
        (S.argument operator ((inventories sort operator action origin).address position).val.val.1) world :=
    fun position =>
      let address := (inventories sort operator action origin).address position
      let available := (matching address.val.val address.val.property).trans address.property
      let input := Operational.coalgebra presentation.toLaw (steps.app world) PUnit.unit _
        (given address.val.val.1) address.val.val.2
      { origin := identifiers position
        source := given address.val.val.1
        action := address.val.val.2
        target := input.get available
        valid := (Option.some_get available).symm }
  refine ⟨origin, given, positive, fun _ => rfl, fun _ => rfl, ?_⟩
  intro address
  exact (premise_iff_guard presentation.toLaw worlds steps operator address.val.val false world given).mpr
    ((matching address.val.val address.val.property).trans address.property)

theorem realizeGuard_positive_origin (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : presentation.Origin sort operator action) (world : Cᵒᵖ)
    (given : (NativeGuard.children worlds operator).obj world)
    (identifiers : (inventories sort operator action origin).Position → PremiseOrigins)
    (holds : given ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
      (presentation.rule sort operator action origin)).obj world)
    (position : (inventories sort operator action origin).Position) :
    ((realizeGuard presentation inventories worlds steps PremiseOrigins operator action
      origin world given identifiers holds).positive position).origin = identifiers position := rfl

theorem occurrence_exists_iff_nativeGuard_withIdentifiers (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (origin : presentation.Origin sort operator action) (world : Cᵒᵖ)
    (given : (NativeGuard.children worlds operator).obj world)
    (identifiers : (inventories sort operator action origin).Position → PremiseOrigins) :
    (∃ firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action,
      firing.origin = origin ∧ firing.children = given ∧
        HEq (fun position => (firing.positive position).origin) identifiers) ↔
      given ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
        (presentation.rule sort operator action origin)).obj world := by
  constructor
  · rintro ⟨firing, rfl, rfl, _⟩
    exact firing.native_guard
  · intro holds
    exact ⟨realizeGuard presentation inventories worlds steps PremiseOrigins operator action
      origin world given identifiers holds, rfl, rfl, HEq.rfl⟩

/-- The native occurrence span uses every authored premise history as its
event, while its actual conclusion supplies the two operational endpoints. -/
noncomputable def occurrenceSpan
    (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)
    (PremiseOrigins : Type u) {sort : S.Srt}
    (operator : S.Operator sort) (action : Actions sort) :
    EventSpan (terms worlds sort) (terms worlds sort) where
  events := occurrenceFunctor presentation inventories worlds steps PremiseOrigins operator action
  source := normalizationMap presentation inventories worlds steps PremiseOrigins operator action ≫
    conclusionMap presentation worlds steps consistent PremiseOrigins operator action ≫
      (eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).source
  target := normalizationMap presentation inventories worlds steps PremiseOrigins operator action ≫
    conclusionMap presentation worlds steps consistent PremiseOrigins operator action ≫
      (eventSpan presentation.toLaw worlds steps (presentation.Origin sort operator action) sort).target

namespace OccurrenceFiring

variable {presentation inventories worlds steps}
variable {PremiseOrigins : Type u} {sort : S.Srt}
variable {operator : S.Operator sort} {action : Actions sort} {world : Cᵒᵖ}
variable (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)

/-- The actual native sum stores the entire original occurrence firing,
alongside the dependent witness at its exact operational target. -/
noncomputable def certificate
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :=
  (occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action).introduce
    A world firing evidence

theorem certificate_firing
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action).eventReadout A).app
      world ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩ = firing := rfl

theorem certificate_result
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action).resultReadout A).app
      world ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩ =
        ⟨(firing.conclusion consistent).target, evidence⟩ := rfl

/-- Future substitution reads every transported premise occurrence,
rather than merely a chosen edge at each normalized address. -/
theorem certificate_firing_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action).eventReadout A).app
      future ((totalSpace ((occurrenceSpan presentation inventories worlds steps consistent
        PremiseOrigins operator action).certificates A)).map change
          ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩) =
      firing.map change := by
  let span := occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action
  exact (span.eventReadout_reindex A change
    ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩).trans
      (congrArg (span.events.map change) (firing.certificate_firing consistent A evidence))

theorem certificate_result_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (A : DisplayedFamily (terms worlds sort))
    (evidence : A.obj ⟨world, (firing.conclusion consistent).target⟩) :
    ((occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action).resultReadout A).app
      future ((totalSpace ((occurrenceSpan presentation inventories worlds steps consistent
        PremiseOrigins operator action).certificates A)).map change
          ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩) =
      (totalSpace A).map change ⟨(firing.conclusion consistent).target, evidence⟩ := by
  let span := occurrenceSpan presentation inventories worlds steps consistent PremiseOrigins operator action
  exact (span.resultReadout_reindex A change
    ⟨(firing.conclusion consistent).source, firing.certificate consistent A evidence⟩).trans
      (congrArg ((totalSpace A).map change) (firing.certificate_result consistent A evidence))

end OccurrenceFiring

end Mettapedia.OSLF.DeterministicGSOS.NativeFiring
