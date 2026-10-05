import Mettapedia.GSLT.Logic.ObservedMaterialization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout

/-!
# Declared observations of actual contextual coalgebras

An actual contextual coalgebra is read as a labelled GSLT with distinct
context and child actions. Declared atomic observations are emitted into
the material value, including at states with no execution children.

Its behavioral equivalence is precisely a stable complete-future
bisimulation that also preserves every declared observation. The same
relation must do both jobs; intersecting ordinary bisimilarity with present
reading agreement does not establish this stronger equivalence.

Authored graph dictionaries give faithful atom, world and actual-arrow
labels. Material observation/action membership, exact behavioral kernels
and formula interpretation are constructed without selecting presentations.
Predecessor observations need a two-sided declared system; none are inferred
from this future-only coalgebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebra

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph
open HennessyMilner

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (observes : Atom → State A → Prop)

def theory : GSLT.{u} where
  Term := State A
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites first second := ∃ label, ContextualCoalgebraLabelledGraph.Step coalgebra first label second
  rewrites_resp_left := by
    intro first other second same action
    exact ⟨second, same ▸ action, rfl⟩
  rewrites_resp_right := by
    intro first second other action same
    exact same ▸ action

def system : System.{u, u} (theory coalgebra) where
  Atom := Atom
  observes := observes
  observes_resp := by
    intro atom first second same
    exact same ▸ Iff.rfl
  Label := ContextualCoalgebraLabelledGraph.Label D
  act label first second := ContextualCoalgebraLabelledGraph.Step coalgebra first label second
  act_resp_left := by
    intro label first other second same action
    exact ⟨second, same ▸ action, rfl⟩
  act_resp_right := by
    intro label first second other action same
    exact same ▸ action

structure IsObservedBisimulation (relation : ∀ point, A.obj point → A.obj point → Prop) : Prop where
  underlying : ContextualCoalgebraBisimulation.IsBisimulation coalgebra relation
  atoms : ∀ {point left right}, relation point left right → ∀ atom,
    observes atom ⟨point, left⟩ ↔ observes atom ⟨point, right⟩

def ObservedBisimilar (point : D) (left right : A.obj point) : Prop :=
  ∃ relation, IsObservedBisimulation coalgebra observes relation ∧ relation point left right

variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))

def readings (atoms : ArgumentCoding Atom) : ObservedMaterialization.LabelReadings (system coalgebra observes) where
  atom := atoms.reading
  action := (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
  atomPresentation := HSet.PresentedLabels.ofGraphs atoms.graph
  actionPresentation := ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows

theorem faithful (atoms : ArgumentCoding Atom) : (readings coalgebra observes worlds arrows atoms).Faithful :=
  ⟨atoms.injective, (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective⟩

theorem system_bisimulation_labelled {relation : State A → State A → Prop}
    (bisimulation : (system coalgebra observes).IsBisimulation relation) :
    IsLabelledBisimulation (ContextualCoalgebraLabelledGraph.Step coalgebra)
      (ContextualCoalgebraLabelledGraph.Step coalgebra)
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading relation := by
  intro first second related
  constructor
  · intro label next action
    obtain ⟨matching, matched, children⟩ := bisimulation.1 related label action
    exact ⟨label, matching, matched, rfl, children⟩
  · intro label next action
    obtain ⟨matching, matched, children⟩ := bisimulation.2.1 related label action
    exact ⟨label, matching, matched, rfl, children⟩

include worlds arrows in
theorem observed_lift_bisimulation {relation : ∀ point, A.obj point → A.obj point → Prop}
    (bisimulation : IsObservedBisimulation coalgebra observes relation) :
    (system coalgebra observes).IsBisimulation (liftRelation relation) := by
  have labelled := lift_isLabelledBisimulation coalgebra
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading bisimulation.underlying
  refine ⟨?_, ?_, ?_⟩
  · intro first second related label next action
    obtain ⟨matchingLabel, matching, matched, labelsEq, children⟩ := (labelled related).1 label next action
    have same := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective labelsEq
    cases same
    exact ⟨matching, matched, children⟩
  · intro first second related label next action
    obtain ⟨matchingLabel, matching, matched, labelsEq, children⟩ := (labelled related).2 label next action
    have same := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective labelsEq
    cases same
    exact ⟨matching, matched, children⟩
  · rintro first second ⟨point, left, right, rfl, rfl, related⟩ atom
    exact bisimulation.atoms related atom

include worlds arrows in
theorem system_observed_bisimulation {relation : State A → State A → Prop}
    (bisimulation : (system coalgebra observes).IsBisimulation relation) :
    IsObservedBisimulation coalgebra observes (fun point left right => relation ⟨point, left⟩ ⟨point, right⟩) where
  underlying := contextual_isBisimulation coalgebra
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective
    (system_bisimulation_labelled coalgebra observes worlds arrows bisimulation)
  atoms related atom := bisimulation.2.2 related atom

include worlds arrows in
theorem system_bisimilar_iff (point : D) (left right : A.obj point) :
    (system coalgebra observes).Bisimilar ⟨point, left⟩ ⟨point, right⟩ ↔
      ObservedBisimilar coalgebra observes point left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨_, system_observed_bisimulation coalgebra observes worlds arrows bisimulation, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨liftRelation relation, observed_lift_bisimulation coalgebra observes worlds arrows bisimulation,
      point, left, right, rfl, rfl, related⟩

include worlds arrows in
theorem system_bisimilar_contexts_eq {left right : State A}
    (related : (system coalgebra observes).Bisimilar left right) : left.1 = right.1 := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact related_contexts_eq coalgebra (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective
    (system_bisimulation_labelled coalgebra observes worlds arrows bisimulation) related

variable (atoms : ArgumentCoding Atom)

def value (state : State A) : HSet.{u} := (readings coalgebra observes worlds arrows atoms).value state

def valueGraph (state : State A) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.generated
    ((readings coalgebra observes worlds arrows atoms).taggedPresentation.edge
      (ObservedMaterialization.encodedStep (system coalgebra observes)))
    (HSet.LabelCarrier.atom (some state))

theorem mk_valueGraph (state : State A) :
    HSet.mk (valueGraph coalgebra observes worlds arrows atoms state) =
      value coalgebra observes worlds arrows atoms state := rfl

theorem value_eq_iff (point : D) (left right : A.obj point) :
    value coalgebra observes worlds arrows atoms ⟨point, left⟩ =
        value coalgebra observes worlds arrows atoms ⟨point, right⟩ ↔
      ObservedBisimilar coalgebra observes point left right :=
  ((readings coalgebra observes worlds arrows atoms).value_eq_iff_bisimilar
    (faithful coalgebra observes worlds arrows atoms) _ _).trans
      (system_bisimilar_iff coalgebra observes worlds arrows point left right)

theorem value_contexts_eq {left right : State A}
    (same : value coalgebra observes worlds arrows atoms left = value coalgebra observes worlds arrows atoms right) :
    left.1 = right.1 :=
  system_bisimilar_contexts_eq coalgebra observes worlds arrows
    (((readings coalgebra observes worlds arrows atoms).value_eq_iff_bisimilar
      (faithful coalgebra observes worlds arrows atoms) left right).mp same)

theorem observation_row_iff (state : State A) (atom : Atom) :
    HSet.kpair ((readings coalgebra observes worlds arrows atoms).taggedReading (.inl atom)) ∅ ∈
      value coalgebra observes worlds arrows atoms state ↔ observes atom state :=
  (readings coalgebra observes worlds arrows atoms).observation_iff
    (faithful coalgebra observes worlds arrows atoms) state atom

theorem child_row_iff {source target : D} (arrow : source ⟶ target)
    (argument : A.obj source) (next : A.obj target) :
    HSet.kpair ((readings coalgebra observes worlds arrows atoms).taggedReading
      (.inr (.child source target arrow))) (value coalgebra observes worlds arrows atoms ⟨target, next⟩) ∈
        value coalgebra observes worlds arrows atoms ⟨source, argument⟩ ↔
      ∃ matching, (coalgebra.app source argument).val.holds ⟨⟨target, arrow⟩, matching⟩ ∧
        value coalgebra observes worlds arrows atoms ⟨target, next⟩ =
          value coalgebra observes worlds arrows atoms ⟨target, matching⟩ := by
  constructor
  · intro entry
    obtain ⟨matching, action, same⟩ :=
      ((readings coalgebra observes worlds arrows atoms).action_iff
        (faithful coalgebra observes worlds arrows atoms) ⟨source, argument⟩ (.child source target arrow)
        (value coalgebra observes worlds arrows atoms ⟨target, next⟩)).mp entry
    obtain ⟨child, targetEq, admitted⟩ :=
      (ContextualCoalgebraLabelledGraph.child_step_iff coalgebra arrow argument matching).mp action
    cases targetEq
    exact ⟨child, admitted, same⟩
  · rintro ⟨matching, admitted, same⟩
    exact ((readings coalgebra observes worlds arrows atoms).action_iff
      (faithful coalgebra observes worlds arrows atoms) ⟨source, argument⟩ (.child source target arrow)
      (value coalgebra observes worlds arrows atoms ⟨target, next⟩)).mpr
        ⟨⟨target, matching⟩, child_step coalgebra arrow argument matching admitted, same⟩

theorem context_row_iff {source target : D} (arrow : source ⟶ target)
    (argument : A.obj source) (next : A.obj target) :
    HSet.kpair ((readings coalgebra observes worlds arrows atoms).taggedReading
      (.inr (.context source target arrow))) (value coalgebra observes worlds arrows atoms ⟨target, next⟩) ∈
        value coalgebra observes worlds arrows atoms ⟨source, argument⟩ ↔
      value coalgebra observes worlds arrows atoms ⟨target, next⟩ =
        value coalgebra observes worlds arrows atoms ⟨target, A.map arrow argument⟩ := by
  constructor
  · intro entry
    obtain ⟨matching, action, same⟩ :=
      ((readings coalgebra observes worlds arrows atoms).action_iff
        (faithful coalgebra observes worlds arrows atoms) ⟨source, argument⟩ (.context source target arrow)
        (value coalgebra observes worlds arrows atoms ⟨target, next⟩)).mp entry
    have targetEq := (context_step_iff coalgebra arrow argument matching).mp action
    cases targetEq
    exact same
  · intro same
    exact ((readings coalgebra observes worlds arrows atoms).action_iff
      (faithful coalgebra observes worlds arrows atoms) ⟨source, argument⟩ (.context source target arrow)
      (value coalgebra observes worlds arrows atoms ⟨target, next⟩)).mpr
        ⟨⟨target, A.map arrow argument⟩, context_step coalgebra arrow argument, same⟩

theorem material_formula_iff (formula : Formula Atom (ContextualCoalgebraLabelledGraph.Label D)) (state : State A) :
    (readings coalgebra observes worlds arrows atoms).materialSat formula
        (value coalgebra observes worlds arrows atoms state) ↔ (system coalgebra observes).sat formula state :=
  (readings coalgebra observes worlds arrows atoms).materialSat_value
    (faithful coalgebra observes worlds arrows atoms) formula state

theorem observed_bisimilar_forgets_atoms {point : D} {left right : A.obj point}
    (related : ObservedBisimilar coalgebra observes point left right) :
    ContextualCoalgebraBisimulation.Bisimilar coalgebra point left right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact ⟨relation, bisimulation.underlying, related⟩

theorem observed_bisimilar_atoms {point : D} {left right : A.obj point}
    (related : ObservedBisimilar coalgebra observes point left right) (atom : Atom) :
    observes atom ⟨point, left⟩ ↔ observes atom ⟨point, right⟩ := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact bisimulation.atoms related atom

end Mettapedia.GSLT.ContextualObservedCoalgebra
