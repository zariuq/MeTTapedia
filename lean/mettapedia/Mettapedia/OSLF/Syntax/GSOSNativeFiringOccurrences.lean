import Mettapedia.OSLF.Syntax.GSOSNativeFiring

/-!
# Authored positive-premise occurrence inventories

Normalization of a finite GSOS clause identifies repeated argument/action
addresses. An independent finite inventory restores those authored premise
positions. Coverage supplies a representative of each normalized positive
address, but the complete firing retains every original occurrence. The
normalization comparison preserves targets and does not identify histories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.NativeFiring

open _root_.CategoryTheory Mettapedia.TypeTheory EdgeReadout NativeGuard

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]

/-- Independently authored positive positions and their normalized
addresses. Coverage is a local premise-inventory condition. -/
structure PositiveInventory {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) where
  Position : Type u
  finite : Finite Position
  address : Position → PositiveAddress rule
  covered : Function.Surjective address

namespace PositiveInventory

/-- A selected index is chosen from the independently proved coverage;
the complete occurrence inventory is retained independently below. -/
noncomputable def select {sort : S.Srt} {operator : S.Operator sort}
    {rule : FiniteRule Actions operator} (inventory : PositiveInventory rule)
    (address : PositiveAddress rule) : {position : inventory.Position // inventory.address position = address} :=
  ⟨(inventory.covered address).choose, (inventory.covered address).choose_spec⟩

end PositiveInventory

variable (presentation : AuthoredFinitePresentation (S := S) Actions)
variable (inventories : ∀ sort operator action (origin : presentation.Origin sort operator action),
  PositiveInventory (presentation.rule sort operator action origin))
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

/-- A genuine authored firing retains each positive occurrence separately,
including different supplied origins at the same normalized address. -/
@[ext] structure OccurrenceFiring (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) where
  origin : presentation.Origin sort operator action
  children : (NativeGuard.children worlds operator).obj world
  positive : ∀ position : (inventories sort operator action origin).Position,
    Event presentation.toLaw worlds steps PremiseOrigins
      (S.argument operator ((inventories sort operator action origin).address position).val.val.1) world
  positive_source : ∀ position, (positive position).source =
    children ((inventories sort operator action origin).address position).val.val.1
  positive_action : ∀ position, (positive position).action =
    ((inventories sort operator action origin).address position).val.val.2
  negative : ∀ address : NegativeAddress (presentation.rule sort operator action origin),
    children address.val.val.1 ∈
      (noAction presentation.toLaw worlds steps SupportOrigin _ address.val.val.2).obj world

namespace OccurrenceFiring

variable {presentation inventories worlds steps}
variable {PremiseOrigins : Type u} {sort : S.Srt}
variable {operator : S.Operator sort} {action : Actions sort} {world : Cᵒᵖ}

/-- Select one typed positive edge for normalization without erasing any
of the other supplied occurrences in the original firing. -/
noncomputable def selected
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (address : PositiveAddress (presentation.rule sort operator action firing.origin)) :
    {event : Event presentation.toLaw worlds steps PremiseOrigins (S.argument operator address.val.val.1) world //
      event.source = firing.children address.val.val.1 ∧ event.action = address.val.val.2} := by
  let chosen := (inventories sort operator action firing.origin).select address
  have supplied : {event : Event presentation.toLaw worlds steps PremiseOrigins
      (S.argument operator ((inventories sort operator action firing.origin).address chosen.val).val.val.1) world //
      event.source = firing.children ((inventories sort operator action firing.origin).address chosen.val).val.val.1 ∧
      event.action = ((inventories sort operator action firing.origin).address chosen.val).val.val.2} :=
    ⟨firing.positive chosen.val, firing.positive_source chosen.val, firing.positive_action chosen.val⟩
  exact chosen.property ▸ supplied

/-- Actual normalized-address firing data, with the same authored origin,
children and native negative guards. This map need not be injective. -/
noncomputable def normalize
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :
    Firing presentation worlds steps PremiseOrigins world operator action where
  origin := firing.origin
  children := firing.children
  positive address := (firing.selected address).val
  positive_source address := (firing.selected address).property.1
  positive_action address := (firing.selected address).property.2
  negative := firing.negative

/-- The finite native guard is earned from the actual occurrence inventory. -/
theorem native_guard
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :
    firing.children ∈ (finiteGuard presentation.toLaw worlds steps SupportOrigin
      (presentation.rule sort operator action firing.origin)).obj world :=
  firing.normalize.native_guard

/-- All supplied occurrences act directly under the genuine event map. -/
noncomputable def map {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :
    OccurrenceFiring presentation inventories worlds steps PremiseOrigins future operator action where
  origin := firing.origin
  children := (NativeGuard.children worlds operator).map change firing.children
  positive position := mapEvent presentation.toLaw worlds steps change (firing.positive position)
  positive_source position := congrArg (S.rename (worlds.map change)) (firing.positive_source position)
  positive_action position := firing.positive_action position
  negative address :=
    (noAction presentation.toLaw worlds steps SupportOrigin _ address.val.val.2).map change (firing.negative address)

theorem map_positive_origin {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (position : (inventories sort operator action firing.origin).Position) :
    ((firing.map change).positive position).origin = (firing.positive position).origin := rfl

private theorem labelled_targets_heq
    {rule : FiniteRule Actions operator}
    (children : (NativeGuard.children worlds operator).obj world)
    (first second : PositiveAddress rule)
    (firstEvent : Event presentation.toLaw worlds steps PremiseOrigins
      (S.argument operator first.val.val.1) world)
    (secondEvent : Event presentation.toLaw worlds steps PremiseOrigins
      (S.argument operator second.val.val.1) world)
    (firstSource : firstEvent.source = children first.val.val.1)
    (secondSource : secondEvent.source = children second.val.val.1)
    (firstAction : firstEvent.action = first.val.val.2)
    (secondAction : secondEvent.action = second.val.val.2)
    (same : first = second) : HEq firstEvent.target secondEvent.target := by
  subst second
  have firstValid := firstEvent.valid
  have secondValid := secondEvent.valid
  rw [firstSource, firstAction] at firstValid
  rw [secondSource, secondAction] at secondValid
  exact heq_of_eq (Option.some.inj (firstValid.symm.trans secondValid))

/-- Repeated positive premises have the same derivative only because both
are valid transitions of the deterministic coalgebra. Their origins remain
independent data in the complete firing. -/
theorem equal_address_targets
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action)
    (first second : (inventories sort operator action firing.origin).Position)
    (same : (inventories sort operator action firing.origin).address first =
      (inventories sort operator action firing.origin).address second) :
    HEq (firing.positive first).target (firing.positive second).target :=
  labelled_targets_heq firing.children _ _ (firing.positive first) (firing.positive second)
    (firing.positive_source first) (firing.positive_source second)
    (firing.positive_action first) (firing.positive_action second) same

variable (consistent : FinitePresentation.Consistent Actions presentation.readoutSet)

noncomputable def conclusion
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :=
  firing.normalize.conclusion consistent

/-- Complete result naturality does not assume an identity of supplied
positive histories. It follows from exact operational validity. -/
theorem conclusion_natural {future : Cᵒᵖ} (change : world ⟶ future)
    (firing : OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action) :
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

end OccurrenceFiring

/-- The full authored inventory, rather than its normalized guard support,
is the payload of this presheaf. -/
noncomputable def occurrenceFunctor (PremiseOrigins : Type u)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) : Cᵒᵖ ⥤ Type u where
  obj world := OccurrenceFiring presentation inventories worlds steps PremiseOrigins world operator action
  map change := ↾(OccurrenceFiring.map change)
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply OccurrenceFiring.ext
    · rfl
    · exact ConcreteCategory.congr_hom ((NativeGuard.children worlds operator).map_id world) firing.children
    · apply heq_of_eq
      funext position
      exact ConcreteCategory.congr_hom
        ((events presentation.toLaw worlds steps PremiseOrigins _).map_id world) (firing.positive position)
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro firing
    apply OccurrenceFiring.ext
    · rfl
    · exact ConcreteCategory.congr_hom
        ((NativeGuard.children worlds operator).map_comp earlier later) firing.children
    · apply heq_of_eq
      funext position
      exact ConcreteCategory.congr_hom
        ((events presentation.toLaw worlds steps PremiseOrigins _).map_comp earlier later) (firing.positive position)

end Mettapedia.OSLF.DeterministicGSOS.NativeFiring
