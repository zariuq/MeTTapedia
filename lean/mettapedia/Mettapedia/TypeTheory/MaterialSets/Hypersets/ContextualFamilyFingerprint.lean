import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualUniverseCodes

/-!
# Complete future material carrier and transport observations

Every table row is constructed from the actual displayed family and its
material dictionaries. The observation records carriers at all reachable
future points and function graphs for every arrow from those points. Its
kernel is proved to be exactly equality of those carriers and material
transport actions. Actual arrow labels distinguish parallel arrows.

This is a material observation of semantic families. It does not identify
formation codes or restore authored term and reduction provenance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyFingerprint

open CategoryTheory ContextualGeneratedUniverse

universe u
variable {C : Type u} [Category.{u} C]

section Tables

variable {A : Type u} (coding : ArgumentCoding A)

def tableGraph (values : A → AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (fun index =>
    AccessiblePointedGraph.kpairGraph (coding.graph index) (values index))

theorem tableGraph_entry (values : A → AccessiblePointedGraph.{u}) (row : HSet.{u}) :
    row ∈ HSet.mk (tableGraph coding values) ↔
      ∃ index, HSet.kpair (coding.reading index) (HSet.mk (values index)) = row := by
  change row ∈ HSet.range (fun index =>
    AccessiblePointedGraph.kpairGraph (coding.graph index) (values index)) ↔ _
  rw [HSet.mem_range]
  constructor <;> rintro ⟨index, same⟩ <;> refine ⟨index, ?_⟩
  · rw [AccessiblePointedGraph.mk_kpairGraph] at same
    exact same
  · rw [AccessiblePointedGraph.mk_kpairGraph]
    exact same

theorem tableGraph_eq_iff (first second : A → AccessiblePointedGraph.{u}) :
    HSet.mk (tableGraph coding first) = HSet.mk (tableGraph coding second) ↔
      ∀ index, HSet.mk (first index) = HSet.mk (second index) := by
  constructor
  · intro same index
    have entry : HSet.kpair (coding.reading index) (HSet.mk (first index)) ∈
        HSet.mk (tableGraph coding second) :=
      same ▸ (tableGraph_entry coding first _).mpr ⟨index, rfl⟩
    obtain ⟨other, rowSame⟩ := (tableGraph_entry coding second _).mp entry
    have indices : other = index := coding.injective (HSet.kpair_inj.mp rowSame).1
    subst other
    exact (HSet.kpair_inj.mp rowSame).2.symm
  · intro values
    apply HSet.ext
    intro row
    rw [tableGraph_entry, tableGraph_entry]
    constructor <;> rintro ⟨index, same⟩ <;> refine ⟨index, ?_⟩
    · rw [← values index]
      exact same
    · rw [values index]
      exact same

end Tables

variable {context : LabelledContext C}
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

/-- Reachability needs no choice of a path. Every actual outgoing arrow is
nevertheless retained in the transport table below. -/
def Reachable (point : context.base.Elements) :=
  {future : context.base.Elements // Nonempty (point ⟶ future)}

def TransportIndex (point : context.base.Elements) :=
  Sigma fun source : Reachable point => Sigma fun target : context.base.Elements => source.1 ⟶ target

def carrierCoding (point : context.base.Elements) : ArgumentCoding (Reachable point) :=
  context.labels.subtype (fun future => Nonempty (point ⟶ future))

def transportCoding (point : context.base.Elements) : ArgumentCoding (TransportIndex point) :=
  (carrierCoding point).sigma (fun source =>
    context.labels.sigma (fun target => MaterialFamily.elementArrowCoding arrows source.1 target))

def materialMapGraph (family : MaterialFamily context) {source target : context.base.Elements}
    (step : source ⟶ target) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (fun term : family.family.obj source =>
    AccessiblePointedGraph.kpairGraph ((family.model source).termGraph term)
      ((family.model target).termGraph (family.family.map step term)))

theorem materialMapGraph_entry (family : MaterialFamily context) {source target : context.base.Elements}
    (step : source ⟶ target) (row : HSet.{u}) :
    row ∈ HSet.mk (materialMapGraph family step) ↔
      ∃ term, HSet.kpair ((family.model source).value term)
        ((family.model target).value (family.family.map step term)) = row := by
  change row ∈ HSet.range (fun term : family.family.obj source =>
    AccessiblePointedGraph.kpairGraph ((family.model source).termGraph term)
      ((family.model target).termGraph (family.family.map step term))) ↔ _
  rw [HSet.mem_range]
  constructor <;> rintro ⟨term, same⟩ <;> refine ⟨term, ?_⟩
  · rw [AccessiblePointedGraph.mk_kpairGraph, PresentedType.mk_termGraph,
      PresentedType.mk_termGraph] at same
    exact same
  · rw [AccessiblePointedGraph.mk_kpairGraph, PresentedType.mk_termGraph,
      PresentedType.mk_termGraph]
    exact same

def carrierTableGraph (family : MaterialFamily context) (point : context.base.Elements) :
    AccessiblePointedGraph.{u} :=
  tableGraph (carrierCoding point) (fun future => (family.model future.1).graph)

def transportTableGraph (family : MaterialFamily context) (point : context.base.Elements) :
    AccessiblePointedGraph.{u} :=
  tableGraph (transportCoding arrows point) (fun row => materialMapGraph family row.2.2)

def graph (family : MaterialFamily context) (point : context.base.Elements) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.kpairGraph (carrierTableGraph family point) (transportTableGraph arrows family point)

def reading (family : MaterialFamily context) (point : context.base.Elements) : HSet.{u} :=
  HSet.mk (graph arrows family point)

/-- Complete material tables contain every reachable carrier and every
transport graph, including all parallel arrows with the same endpoints. -/
def TablesAgree (first second : MaterialFamily context) (point : context.base.Elements) : Prop :=
  (∀ future : Reachable point, (first.model future.1).carrier = (second.model future.1).carrier) ∧
  (∀ row : TransportIndex point,
    HSet.mk (materialMapGraph first row.2.2) = HSet.mk (materialMapGraph second row.2.2))

theorem reading_eq_iff_tables (first second : MaterialFamily context) (point : context.base.Elements) :
    reading arrows first point = reading arrows second point ↔ TablesAgree first second point := by
  change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
    HSet.mk (AccessiblePointedGraph.kpairGraph _ _) ↔ _
  rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph, HSet.kpair_inj]
  exact and_congr (tableGraph_eq_iff (carrierCoding point) _ _)
    (tableGraph_eq_iff (transportCoding arrows point) _ _)

/-- Compatibility compares actual members with equal material values,
without equating their external typed representations. -/
def MaterialMapsAgree (first second : MaterialFamily context)
    {source target : context.base.Elements} (step : source ⟶ target) : Prop :=
  ∀ left : first.family.obj source, ∀ right : second.family.obj source,
    (first.model source).value left = (second.model source).value right →
      (first.model target).value (first.family.map step left) =
        (second.model target).value (second.family.map step right)

theorem materialMapGraph_eq_iff (first second : MaterialFamily context)
    {source target : context.base.Elements} (step : source ⟶ target)
    (carriers : (first.model source).carrier = (second.model source).carrier) :
    HSet.mk (materialMapGraph first step) = HSet.mk (materialMapGraph second step) ↔
      MaterialMapsAgree first second step := by
  constructor
  · intro same left right inputSame
    have entry : HSet.kpair ((first.model source).value left)
        ((first.model target).value (first.family.map step left)) ∈
        HSet.mk (materialMapGraph second step) :=
      same ▸ (materialMapGraph_entry first step _).mpr ⟨left, rfl⟩
    obtain ⟨other, rowSame⟩ := (materialMapGraph_entry second step _).mp entry
    have input : (second.model source).value other = (second.model source).value right :=
      (HSet.kpair_inj.mp rowSame).1.trans inputSame
    have members := (second.model source).value_injective input
    subst other
    exact (HSet.kpair_inj.mp rowSame).2.symm
  · intro compatible
    apply HSet.ext
    intro row
    rw [materialMapGraph_entry, materialMapGraph_entry]
    constructor
    · rintro ⟨left, rowSame⟩
      let input : {value : HSet.{u} // value ∈ (second.model source).carrier} :=
        ⟨(first.model source).value left, carriers ▸ (first.model source).value_mem left⟩
      let right := (second.model source).decode input
      have inputSame : (first.model source).value left = (second.model source).value right :=
        ((second.model source).value_decode input).symm
      refine ⟨right, ?_⟩
      exact (congrArg₂ HSet.kpair inputSame (compatible left right inputSame)).symm.trans rowSame
    · rintro ⟨right, rowSame⟩
      let input : {value : HSet.{u} // value ∈ (first.model source).carrier} :=
        ⟨(second.model source).value right, carriers.symm ▸ (second.model source).value_mem right⟩
      let left := (first.model source).decode input
      have inputSame : (first.model source).value left = (second.model source).value right :=
        (first.model source).value_decode input
      refine ⟨left, ?_⟩
      exact (congrArg₂ HSet.kpair inputSame (compatible left right inputSame)).trans rowSame

def FutureActionsAgree (first second : MaterialFamily context) (point : context.base.Elements) : Prop :=
  (∀ future : Reachable point, (first.model future.1).carrier = (second.model future.1).carrier) ∧
  (∀ row : TransportIndex point, MaterialMapsAgree first second row.2.2)

theorem reading_eq_iff (first second : MaterialFamily context) (point : context.base.Elements) :
    reading arrows first point = reading arrows second point ↔ FutureActionsAgree first second point := by
  rw [reading_eq_iff_tables]
  constructor
  · rintro ⟨carriers, maps⟩
    refine ⟨carriers, fun row => ?_⟩
    exact (materialMapGraph_eq_iff first second row.2.2 (carriers row.1)).mp (maps row)
  · rintro ⟨carriers, maps⟩
    refine ⟨carriers, fun row => ?_⟩
    exact (materialMapGraph_eq_iff first second row.2.2 (carriers row.1)).mpr (maps row)

/-- Future observations are stable under actual context-arrow composition.
No past matching or cancellation property is needed. -/
theorem reading_kernel_restriction (first second : MaterialFamily context)
    {point next : context.base.Elements} (step : point ⟶ next)
    (same : reading arrows first point = reading arrows second point) :
    reading arrows first next = reading arrows second next := by
  obtain ⟨carriers, maps⟩ := (reading_eq_iff arrows first second point).mp same
  apply (reading_eq_iff arrows first second next).mpr
  have reachable : ∀ future : Reachable next, Nonempty (point ⟶ future.1) := by
    intro future
    obtain ⟨later⟩ := future.2
    exact ⟨step ≫ later⟩
  exact ⟨fun future => carriers ⟨future.1, reachable future⟩,
    fun row => maps ⟨⟨row.1.1, reachable row.1⟩, row.2⟩⟩


/-- The quotient retains a complete future-table observation. It is not a
quotient of formation evidence and does not identify generated codes. -/
def observationSetoid (point : context.base.Elements) : Setoid (MaterialFamily context) where
  r first second := reading arrows first point = reading arrows second point
  iseqv := ⟨fun _ => rfl, fun same => same.symm, fun earlier later => earlier.trans later⟩

def Observation (point : context.base.Elements) : Type (u + 1) :=
  Quotient (observationSetoid arrows point)

def observe (point : context.base.Elements) (family : MaterialFamily context) : Observation arrows point :=
  Quotient.mk (observationSetoid arrows point) family

def decodeObservation (point : context.base.Elements) : Observation arrows point → HSet.{u} :=
  Quotient.lift (fun family => reading arrows family point) (fun _ _ same => same)

theorem decode_observe (point : context.base.Elements) (family : MaterialFamily context) :
    decodeObservation arrows point (observe arrows point family) = reading arrows family point := rfl

theorem decodeObservation_injective (point : context.base.Elements) :
    Function.Injective (decodeObservation arrows point) := by
  intro first second
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      intro same
      exact @Quotient.sound _ (observationSetoid arrows point) first second same

/-- The source family is retained through the quotient eliminator. The proved
future kernel stability, rather than a selected representative, defines the map. -/
def observationRestrict {point next : context.base.Elements} (step : point ⟶ next) :
    Observation arrows point → Observation arrows next :=
  Quotient.map id (fun first second same => reading_kernel_restriction arrows first second step same)

theorem restrict_observe {point next : context.base.Elements} (step : point ⟶ next)
    (family : MaterialFamily context) :
    observationRestrict arrows step (observe arrows point family) = observe arrows next family := rfl

def observationFunctor : context.base.Elements ⥤ Type (u + 1) where
  obj := Observation arrows
  map step := TypeCat.ofHom (observationRestrict arrows step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro observed
    induction observed using Quotient.inductionOn with
    | _ family => rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro observed
    induction observed using Quotient.inductionOn with
    | _ family => rfl

/-- The observed table at a future is the actual independently constructed
future table of the same semantic family. This is not a function on bare
present carrier values. -/
theorem future_decode_square {point next : context.base.Elements} (step : point ⟶ next)
    (family : MaterialFamily context) :
    decodeObservation arrows next ((observationFunctor arrows).map step (observe arrows point family)) =
      reading arrows family next := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualFamilyFingerprint
