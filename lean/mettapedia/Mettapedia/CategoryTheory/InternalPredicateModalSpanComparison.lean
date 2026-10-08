import Mettapedia.CategoryTheory.PredicateDoctrineQuantifierCoherence
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier

/-!
# Predicate operators of retained event spans

A span retains its event object and both endpoint maps. An endpoint-preserving
map into another span earns an inclusion of existential predicate operators.
An actual event isomorphism earns equality. The higher-order arrows act on
complete predicate functions, with supplied-input and parameter substitution
readouts. Adding events therefore does not implicitly preserve a global
modality as an equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateModalSpanComparison

open _root_.CategoryTheory
open MonoidalCategory CartesianMonoidalCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier

universe u v p w z

/-- An event span, retaining its actual event carrier. -/
structure Span (C : Type u) [Category.{v} C] (input output : C) where
  events : C
  source : events ⟶ input
  target : events ⟶ output

variable {C : Type u} [Category.{v} C] {input output : C}

namespace Span

/-- A comparison retains the full event map and its two local endpoint squares. -/
structure Map (first second : Span C input output) where
  event : first.events ⟶ second.events
  source : event ≫ second.source = first.source
  target : event ≫ second.target = first.target

namespace Map

def identity (span : Span C input output) : Map span span where
  event := 𝟙 span.events
  source := Category.id_comp _
  target := Category.id_comp _

def comp {first second third : Span C input output}
    (earlier : Map first second) (later : Map second third) : Map first third where
  event := earlier.event ≫ later.event
  source := by rw [Category.assoc, later.source, earlier.source]
  target := by rw [Category.assoc, later.target, earlier.target]

theorem comp_event {first second third : Span C input output}
    (earlier : Map first second) (later : Map second third) :
    (comp earlier later).event = earlier.event ≫ later.event := rfl

end Map

/-- An isomorphism of event carriers with both endpoint equations. -/
structure Iso (first second : Span C input output) where
  events : first.events ≅ second.events
  source : events.hom ≫ second.source = first.source
  target : events.hom ≫ second.target = first.target

namespace Iso

def toMap {first second : Span C input output} (comparison : Iso first second) :
    Map first second := ⟨comparison.events.hom, comparison.source, comparison.target⟩

def symm {first second : Span C input output} (comparison : Iso first second) :
    Iso second first where
  events := comparison.events.symm
  source := by
    change comparison.events.inv ≫ first.source = second.source
    rw [← comparison.source, ← Category.assoc,
      comparison.events.inv_hom_id, Category.id_comp]
  target := by
    change comparison.events.inv ≫ first.target = second.target
    rw [← comparison.target, ← Category.assoc,
      comparison.events.inv_hom_id, Category.id_comp]

end Iso

/-- The image span under an actual functor, with no identification of its events
with all events of any larger target relation. -/
def image {D : Type w} [Category.{z} D] (F : C ⥤ D) (span : Span C input output) :
    Span D (F.obj input) (F.obj output) where
  events := F.obj span.events
  source := F.map span.source
  target := F.map span.target

def Map.image {D : Type w} [Category.{z} D] (F : C ⥤ D)
    {first second : Span C input output} (comparison : Map first second) :
    Map (image F first) (image F second) where
  event := F.map comparison.event
  source := (F.map_comp _ _).symm.trans (congrArg F.map comparison.source)
  target := (F.map_comp _ _).symm.trans (congrArg F.map comparison.target)

def Iso.image {D : Type w} [Category.{z} D] (F : C ⥤ D)
    {first second : Span C input output} (comparison : Iso first second) :
    Iso (image F first) (image F second) where
  events := F.mapIso comparison.events
  source := (F.map_comp _ _).symm.trans (congrArg F.map comparison.source)
  target := (F.map_comp _ _).symm.trans (congrArg F.map comparison.target)

variable (D : PredicateDoctrine.FirstOrder.{u,v,p} C)

/-- Existential postcondition transport along the retained span. -/
def possibility (span : Span C input output) (post : D.Fiber output) : D.Fiber input :=
  D.existsAlong span.source (D.reindex span.target post)

theorem possibility_mono (span : Span C input output) : Monotone (possibility D span) :=
  (D.exists_mono span.source).comp (D.reindex_mono span.target)

theorem Map.possibility_le {first second : Span C input output}
    (comparison : Map first second) (post : D.Fiber output) :
    possibility D first post ≤ possibility D second post := by
  unfold possibility
  rw [← comparison.source, D.existsAlong_comp, ← comparison.target, D.reindex_comp]
  exact D.exists_mono second.source (D.exists_counit comparison.event _)

theorem Iso.possibility_eq {first second : Span C input output}
    (comparison : Iso first second) (post : D.Fiber output) :
    possibility D first post = possibility D second post :=
  le_antisymm (comparison.toMap.possibility_le D post)
    (comparison.symm.toMap.possibility_le D post)

variable [CartesianMonoidalCategory C]

/-- Parameters are retained in both endpoints and in the complete event carrier. -/
def parameterized (span : Span C input output) (parameter : C) :
    Span C (input ⊗ parameter) (output ⊗ parameter) where
  events := span.events ⊗ parameter
  source := span.source ▷ parameter
  target := span.target ▷ parameter

def Map.parameterized {first second : Span C input output}
    (comparison : Map first second) (parameter : C) :
    Map (parameterized first parameter) (parameterized second parameter) where
  event := comparison.event ▷ parameter
  source := (comp_whiskerRight _ _ _).symm.trans
    (congrArg (fun arrow => arrow ▷ parameter) comparison.source)
  target := (comp_whiskerRight _ _ _).symm.trans
    (congrArg (fun arrow => arrow ▷ parameter) comparison.target)

def Iso.parameterized {first second : Span C input output}
    (comparison : Iso first second) (parameter : C) :
    Iso (parameterized first parameter) (parameterized second parameter) where
  events := whiskerRightIso comparison.events parameter
  source := (comp_whiskerRight _ _ _).symm.trans
    (congrArg (fun arrow => arrow ▷ parameter) comparison.source)
  target := (comp_whiskerRight _ _ _).symm.trans
    (congrArg (fun arrow => arrow ▷ parameter) comparison.target)

end Span

variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

/-- The actual powerobject arrow derived from the two retained span endpoints. -/
def operation (span : Span C input output) : power doctrine output ⟶ power doctrine input :=
  InternalPredicateQuantifier.precomposition (operations doctrine) span.target ≫
    existsOperation doctrine span.source

theorem operation_supplied (span : Span C input output) {parameter : C}
    (post : parameter ⟶ power doctrine output) :
    family doctrine (post ≫ operation doctrine span) =
      Span.possibility doctrine.toFirstOrder (span.parameterized parameter) (family doctrine post) := by
  rw [operation, ← Category.assoc, exists_supplied, precomposition_supplied]
  rfl

theorem operation_generic (span : Span C input output) :
    family doctrine (operation doctrine span) =
      Span.possibility doctrine.toFirstOrder (span.parameterized (power doctrine output))
        (family doctrine (𝟙 _)) := by
  simpa only [Category.id_comp] using operation_supplied doctrine span (𝟙 _)

theorem operation_supplied_inclusion {first second : Span C input output}
    (comparison : Span.Map first second) {parameter : C}
    (post : parameter ⟶ power doctrine output) :
    family doctrine (post ≫ operation doctrine first) ≤
      family doctrine (post ≫ operation doctrine second) := by
  rw [operation_supplied, operation_supplied]
  exact (comparison.parameterized parameter).possibility_le doctrine.toFirstOrder _

theorem operation_equal {first second : Span C input output}
    (comparison : Span.Iso first second) : operation doctrine first = operation doctrine second := by
  apply family_injective doctrine
  rw [operation_generic, operation_generic]
  exact (comparison.parameterized (power doctrine output)).possibility_eq doctrine.toFirstOrder _

theorem operation_supplied_equal {first second : Span C input output}
    (comparison : Span.Iso first second) {parameter : C}
    (post : parameter ⟶ power doctrine output) :
    post ≫ operation doctrine first = post ≫ operation doctrine second :=
  congrArg (fun arrow => post ≫ arrow) (operation_equal doctrine comparison)

theorem operation_future (span : Span C input output) {first second : C}
    (future : first ⟶ second) (post : second ⟶ power doctrine output) :
    family doctrine ((future ≫ post) ≫ operation doctrine span) =
      doctrine.reindex (input ◁ future) (family doctrine (post ≫ operation doctrine span)) := by
  rw [Category.assoc]
  exact family_substitution doctrine future _

end Mettapedia.CategoryTheory.InternalPredicateModalSpanComparison
