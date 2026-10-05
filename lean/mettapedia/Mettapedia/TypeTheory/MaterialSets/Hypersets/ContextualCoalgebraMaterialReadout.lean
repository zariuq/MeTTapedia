import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraLabelledGraph
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# Faithful material readings of small contextual coalgebras

Authored world and arrow graph dictionaries construct every transition
label. Context and child labels have distinct material tags. The graph
decoration has exactly contextual bisimulation as its equality kernel at
one context; equality also reflects the context of every state.

All source states, labels and attached label nodes inhabit `Type u`.
The resulting values and collecting carriers inhabit `HSet.{u}`. These
graph dictionaries are actual data, not selected from countability or
existential presentation claims. No dictionary for arguments is needed.

Material context rows retain the deterministic transport; child rows retain
the actual future arrow and the behavioral value of the admitted child.
Occurrences with equal behavioral readings remain distinct in the source.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover
open ContextualCoalgebraLabelledGraph

universe u
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type u}

def arrowCoding (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target)) :
    ArgumentCoding ((source : D) × (target : D) × (source ⟶ target)) :=
  worlds.sigma fun source => worlds.sigma fun target => arrows source target

def labelGraph (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target)) :
    Label D → AccessiblePointedGraph.{u}
  | .context source target arrow => AccessiblePointedGraph.kpairGraph
      AccessiblePointedGraph.empty ((arrowCoding worlds arrows).graph ⟨source, target, arrow⟩)
  | .child source target arrow => AccessiblePointedGraph.kpairGraph
      (AccessiblePointedGraph.singletonGraph AccessiblePointedGraph.empty)
      ((arrowCoding worlds arrows).graph ⟨source, target, arrow⟩)

theorem labelGraph_injective (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target)) :
    Function.Injective (fun label => HSet.mk (labelGraph worlds arrows label)) := by
  intro first second same
  cases first with
  | context source target arrow =>
      cases second with
      | context otherSource otherTarget otherArrow =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
          have arrowsEq := (arrowCoding worlds arrows).injective (HSet.kpair_inj.mp same).2
          exact congrArg (fun receipt : (source : D) × (target : D) × (source ⟶ target) =>
            Label.context receipt.1 receipt.2.1 receipt.2.2) arrowsEq
      | child otherSource otherTarget otherArrow =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
            AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty] at same
          exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1).elim
  | child source target arrow =>
      cases second with
      | context otherSource otherTarget otherArrow =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
            AccessiblePointedGraph.mk_singletonGraph, HSet.mk_empty] at same
          exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp same).1.symm).elim
      | child otherSource otherTarget otherArrow =>
          change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) =
            HSet.mk (AccessiblePointedGraph.kpairGraph _ _) at same
          rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph] at same
          have arrowsEq := (arrowCoding worlds arrows).injective (HSet.kpair_inj.mp same).2
          exact congrArg (fun receipt : (source : D) × (target : D) × (source ⟶ target) =>
            Label.child receipt.1 receipt.2.1 receipt.2.2) arrowsEq

def labels (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target)) : ArgumentCoding (Label D) :=
  ⟨labelGraph worlds arrows, labelGraph_injective worlds arrows⟩

def labelPresentation (worlds : ArgumentCoding D)
    (arrows : (source target : D) → ArgumentCoding (source ⟶ target)) :
    HSet.PresentedLabels (labels worlds arrows).reading :=
  HSet.PresentedLabels.ofGraphs (labelGraph worlds arrows)

variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))

def value (state : State A) : HSet.{u} :=
  (labelPresentation worlds arrows).decorate (Step coalgebra) state

def valueGraph (state : State A) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated ((labelPresentation worlds arrows).edge (Step coalgebra))
    (HSet.LabelCarrier.atom state)

theorem mk_valueGraph (state : State A) :
    HSet.mk (valueGraph coalgebra worlds arrows state) = value coalgebra worlds arrows state := rfl

theorem value_eq_iff (point : D) (left right : A.obj point) :
    value coalgebra worlds arrows ⟨point, left⟩ = value coalgebra worlds arrows ⟨point, right⟩ ↔
      ContextualCoalgebraBisimulation.Bisimilar coalgebra point left right :=
  ((labelPresentation worlds arrows).decorate_eq_iff_labelledBisimilar
    (labelPresentation worlds arrows)).trans
      (labelledBisimilar_iff_contextual coalgebra (labels worlds arrows).reading
        (labels worlds arrows).injective point left right)

theorem value_contexts_eq {first second : State A}
    (same : value coalgebra worlds arrows first = value coalgebra worlds arrows second) :
    first.1 = second.1 :=
  labelledBisimilar_contexts_eq coalgebra (labels worlds arrows).reading (labels worlds arrows).injective
    (((labelPresentation worlds arrows).decorate_eq_iff_labelledBisimilar
      (labelPresentation worlds arrows)).mp same)

theorem value_eq_iff_liftRelation (first second : State A) :
    value coalgebra worlds arrows first = value coalgebra worlds arrows second ↔
      liftRelation (ContextualCoalgebraBisimulation.Bisimilar coalgebra) first second := by
  constructor
  · intro same
    rcases first with ⟨point, left⟩
    rcases second with ⟨other, right⟩
    have contexts := value_contexts_eq coalgebra worlds arrows same
    cases contexts
    exact ⟨point, left, right, rfl, rfl,
      (value_eq_iff coalgebra worlds arrows point left right).mp same⟩
  · rintro ⟨point, left, right, rfl, rfl, related⟩
    exact (value_eq_iff coalgebra worlds arrows point left right).mpr related

theorem mem_value (state : State A) (member : HSet.{u}) :
    member ∈ value coalgebra worlds arrows state ↔
      ∃ label next, Step coalgebra state label next ∧
        member = HSet.kpair ((labels worlds arrows).reading label)
          (value coalgebra worlds arrows next) :=
  (labelPresentation worlds arrows).mem_decorate

theorem row_mem_iff (state : State A) (label : Label D) (next : State A) :
    HSet.kpair ((labels worlds arrows).reading label) (value coalgebra worlds arrows next) ∈
        value coalgebra worlds arrows state ↔
      ∃ matching, Step coalgebra state label matching ∧
        value coalgebra worlds arrows next = value coalgebra worlds arrows matching := by
  rw [mem_value]
  constructor
  · rintro ⟨other, matching, step, same⟩
    have pairEq := HSet.kpair_inj.mp same
    have labelsEq := (labels worlds arrows).injective pairEq.1
    cases labelsEq
    exact ⟨matching, step, pairEq.2⟩
  · rintro ⟨matching, step, same⟩
    exact ⟨label, matching, step, congrArg (HSet.kpair ((labels worlds arrows).reading label)) same⟩

theorem context_row_iff {source target : D} (arrow : source ⟶ target)
    (argument : A.obj source) (next : A.obj target) :
    HSet.kpair ((labels worlds arrows).reading (.context source target arrow))
        (value coalgebra worlds arrows ⟨target, next⟩) ∈
      value coalgebra worlds arrows ⟨source, argument⟩ ↔
        ContextualCoalgebraBisimulation.Bisimilar coalgebra target next (A.map arrow argument) := by
  rw [row_mem_iff]
  constructor
  · rintro ⟨matching, step, same⟩
    have result := (context_step_iff coalgebra arrow argument matching).mp step
    cases result
    exact (value_eq_iff coalgebra worlds arrows target _ _).mp same
  · intro related
    exact ⟨⟨target, A.map arrow argument⟩, context_step coalgebra arrow argument,
      (value_eq_iff coalgebra worlds arrows target _ _).mpr related⟩

theorem child_row_iff {source target : D} (arrow : source ⟶ target)
    (argument : A.obj source) (next : A.obj target) :
    HSet.kpair ((labels worlds arrows).reading (.child source target arrow))
        (value coalgebra worlds arrows ⟨target, next⟩) ∈
      value coalgebra worlds arrows ⟨source, argument⟩ ↔
        ∃ matching, (coalgebra.app source argument).val.holds ⟨⟨target, arrow⟩, matching⟩ ∧
          ContextualCoalgebraBisimulation.Bisimilar coalgebra target next matching := by
  rw [row_mem_iff]
  constructor
  · rintro ⟨matching, step, same⟩
    obtain ⟨child, result, available⟩ := (child_step_iff coalgebra arrow argument matching).mp step
    cases result
    exact ⟨child, available, (value_eq_iff coalgebra worlds arrows target _ _).mp same⟩
  · rintro ⟨matching, available, related⟩
    exact ⟨⟨target, matching⟩, child_step coalgebra arrow argument matching available,
      (value_eq_iff coalgebra worlds arrows target _ _).mpr related⟩

def classValue (point : D) : (ContextualCoalgebraQuotient.family coalgebra).obj point → HSet.{u} :=
  Quotient.lift (fun argument => value coalgebra worlds arrows ⟨point, argument⟩)
    (fun _ _ related => (value_eq_iff coalgebra worlds arrows point _ _).mpr related)

theorem classValue_projection (point : D) (argument : A.obj point) :
    classValue coalgebra worlds arrows point
      ((ContextualCoalgebraQuotient.projection coalgebra).app point argument) =
        value coalgebra worlds arrows ⟨point, argument⟩ := rfl

theorem classValue_injective (point : D) :
    Function.Injective (classValue coalgebra worlds arrows point) := by
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro left right same
  exact Quotient.sound ((value_eq_iff coalgebra worlds arrows point left right).mp same)

def carrier (point : D) : HSet.{u} :=
  HSet.range fun argument : A.obj point => valueGraph coalgebra worlds arrows ⟨point, argument⟩

theorem mem_carrier_iff (point : D) (member : HSet.{u}) :
    member ∈ carrier coalgebra worlds arrows point ↔
      ∃ argument : A.obj point, value coalgebra worlds arrows ⟨point, argument⟩ = member :=
  HSet.mem_range

theorem classValue_mem (point : D) (observed : (ContextualCoalgebraQuotient.family coalgebra).obj point) :
    classValue coalgebra worlds arrows point observed ∈ carrier coalgebra worlds arrows point := by
  refine Quotient.inductionOn observed ?_
  intro argument
  exact (mem_carrier_iff coalgebra worlds arrows point _).mpr ⟨argument, rfl⟩

theorem mem_carrier_iff_classValue (point : D) (member : HSet.{u}) :
    member ∈ carrier coalgebra worlds arrows point ↔
      ∃ observed : (ContextualCoalgebraQuotient.family coalgebra).obj point,
        classValue coalgebra worlds arrows point observed = member := by
  constructor
  · intro present
    obtain ⟨argument, same⟩ := (mem_carrier_iff coalgebra worlds arrows point member).mp present
    exact ⟨(ContextualCoalgebraQuotient.projection coalgebra).app point argument, same⟩
  · rintro ⟨observed, rfl⟩
    exact classValue_mem coalgebra worlds arrows point observed

/-- A natural coalgebra morphism preserves the complete labelled material
value, using both directions of its future-child image equation. -/
theorem coalgebra_map_value {B : D ⥤ Type u} (operation : NaturalHom A B)
    (target : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom operation) = operation.comp target)
    (point : D) (argument : A.obj point) :
    value coalgebra worlds arrows ⟨point, argument⟩ =
      value target worlds arrows ⟨point, operation.app point argument⟩ :=
  (labelPresentation worlds arrows).decorate_eq_of_labelledBisimilar
    (labelPresentation worlds arrows)
    ⟨_, coalgebra_map_isLabelledBisimulation coalgebra (labels worlds arrows).reading
      operation target square, rfl⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout
