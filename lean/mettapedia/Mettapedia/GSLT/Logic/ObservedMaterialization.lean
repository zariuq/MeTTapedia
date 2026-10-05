import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.GSLT.Logic.ObservationSpans
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedLabelledBisimulation

/-!
# Material readings of observed labelled GSLTs

Atomic observations and actions occupy disjoint tags in an explicitly
presented labelled graph. An observation points to a childless endpoint;
an action points to the observed successor state. Their material readings
therefore retain both the atomic valuation and the labelled branching.

Literal observations and action labels are reflected when their supplied
readings are injective. Material HML satisfaction uses actual Kuratowski
membership, with no reconstruction of syntax representatives. The source
equation theory is unchanged by this behavioural interpretation.

Readings and their small graph presentations are supplied in one universe.
The construction, its exact equality kernel, and formula interpretation use
these presentations directly. The finite-cover Hennessy--Milner converse
uses the existing classical separator argument. Authored event identities
remain in type-valued fibres; observing them as labels is a separate profile.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedMaterialization

open Mettapedia.TypeTheory.MaterialSets.Hypersets HennessyMilner

universe u

variable {S : GSLT.{u}}

private def singletonGraph (graph : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (fun _ : PUnit.{u + 1} => graph)

private theorem mk_singletonGraph (graph : AccessiblePointedGraph.{u}) :
    HSet.mk (singletonGraph graph) = {HSet.mk graph} := by
  change HSet.range (fun _ : PUnit.{u + 1} => graph) = {HSet.mk graph}
  ext y
  rw [HSet.mem_range, HSet.mem_singleton]
  exact ⟨fun ⟨_, equal⟩ => equal.symm, fun equal => ⟨PUnit.unit, equal.symm⟩⟩

private def pairGraph (left right : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  AccessiblePointedGraph.sup (fun b : ULift.{u} Bool => if b.down then left else right)

private theorem mk_pairGraph (left right : AccessiblePointedGraph.{u}) :
    HSet.mk (pairGraph left right) = {HSet.mk left, HSet.mk right} := by
  change HSet.range (fun b : ULift.{u} Bool => if b.down then left else right) = _
  ext y
  rw [HSet.mem_range, HSet.mem_pair]
  constructor
  · rintro ⟨⟨b⟩, equal⟩
    cases b with
    | false => exact Or.inr equal.symm
    | true => exact Or.inl equal.symm
  · rintro (equal | equal)
    · exact ⟨⟨true⟩, equal.symm⟩
    · exact ⟨⟨false⟩, equal.symm⟩

/-- The authored graph of a Kuratowski pair of two supplied presentations. -/
def kuratowskiGraph (left right : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  pairGraph (singletonGraph left) (pairGraph left right)

theorem mk_kuratowskiGraph (left right : AccessiblePointedGraph.{u}) :
    HSet.mk (kuratowskiGraph left right) = HSet.kpair (HSet.mk left) (HSet.mk right) := by
  rw [kuratowskiGraph, mk_pairGraph, mk_singletonGraph, mk_pairGraph]
  rfl

/-- Presented readings for the system's two observable namespaces. -/
structure LabelReadings (M : System.{u, u} S) : Type (u + 1) where
  atom : M.Atom → HSet.{u}
  action : M.Label → HSet.{u}
  atomPresentation : HSet.PresentedLabels atom
  actionPresentation : HSet.PresentedLabels action

namespace LabelReadings

variable {M : System.{u, u} S}

/-- Literal label reflection is an explicit property of the chosen readings. -/
def Faithful (readings : LabelReadings M) : Prop :=
  Function.Injective readings.atom ∧ Function.Injective readings.action

/-- Atomic observations and actions have distinct material tags. -/
def taggedReading (readings : LabelReadings M) : Sum M.Atom M.Label → HSet.{u}
  | .inl atom => HSet.kpair ∅ (readings.atom atom)
  | .inr label => HSet.kpair {∅} (readings.action label)

def taggedGraph (readings : LabelReadings M) : Sum M.Atom M.Label → AccessiblePointedGraph.{u}
  | .inl atom => kuratowskiGraph AccessiblePointedGraph.empty (readings.atomPresentation.graph atom)
  | .inr label => kuratowskiGraph (singletonGraph AccessiblePointedGraph.empty)
      (readings.actionPresentation.graph label)

/-- Tagging combines the supplied graphs by pairing; it makes no new choice. -/
def taggedPresentation (readings : LabelReadings M) : HSet.PresentedLabels readings.taggedReading where
  graph := readings.taggedGraph
  mk_graph label := by
    cases label with
    | inl atom =>
      rw [taggedGraph, mk_kuratowskiGraph, HSet.mk_empty, readings.atomPresentation.mk_graph]
      rfl
    | inr label =>
      rw [taggedGraph, mk_kuratowskiGraph, mk_singletonGraph, HSet.mk_empty,
        readings.actionPresentation.mk_graph]
      rfl

theorem taggedReading_injective (readings : LabelReadings M) (faithful : readings.Faithful) :
    Function.Injective readings.taggedReading := by
  intro first second equal
  cases first with
  | inl atom =>
    cases second with
    | inl atom' =>
      exact congrArg Sum.inl (faithful.1 (HSet.kpair_inj.mp equal).2)
    | inr label =>
      exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp equal).1).elim
  | inr label =>
    cases second with
    | inl atom =>
      exact (HSet.empty_ne_singleton_empty (HSet.kpair_inj.mp equal).1.symm).elim
    | inr label' =>
      exact congrArg Sum.inr (faithful.2 (HSet.kpair_inj.mp equal).2)

end LabelReadings

/-- Observations terminate; actions continue at an actual source-system state. -/
def encodedStep (M : System.{u, u} S) :
    Option S.Term → Sum M.Atom M.Label → Option S.Term → Prop
  | some source, .inl atom, none => M.observes atom source
  | some source, .inr label, some target => M.act label source target
  | _, _, _ => False

namespace LabelReadings

variable {M : System.{u, u} S}

def value (readings : LabelReadings M) (term : S.Term) : HSet.{u} :=
  readings.taggedPresentation.decorate (encodedStep M) (some term)

theorem terminal_value (readings : LabelReadings M) :
    readings.taggedPresentation.decorate (encodedStep M) none = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro y member
  obtain ⟨label, target, step, _⟩ := readings.taggedPresentation.mem_decorate.mp member
  cases label <;> cases target <;> cases step

/-- Exact decoding of a material pair entry recovers its literal tag and
its actual successor value. -/
theorem entry_iff (readings : LabelReadings M) (faithful : readings.Faithful)
    (term : S.Term) (label : Sum M.Atom M.Label) (target : HSet.{u}) :
    HSet.kpair (readings.taggedReading label) target ∈ readings.value term ↔
      ∃ next, encodedStep M (some term) label next ∧
        target = readings.taggedPresentation.decorate (encodedStep M) next := by
  rw [value, readings.taggedPresentation.mem_decorate]
  constructor
  · rintro ⟨label', next, step, equal⟩
    have components := HSet.kpair_inj.mp equal
    have labels := readings.taggedReading_injective faithful components.1
    subst label'
    exact ⟨next, step, components.2⟩
  · rintro ⟨next, step, equal⟩
    exact ⟨label, next, step, by rw [equal]⟩

/-- Atomic observations are read from actual material membership. -/
theorem observation_iff (readings : LabelReadings M) (faithful : readings.Faithful)
    (term : S.Term) (atom : M.Atom) :
    HSet.kpair (readings.taggedReading (.inl atom)) ∅ ∈ readings.value term ↔
      M.observes atom term := by
  rw [readings.entry_iff faithful]
  constructor
  · rintro ⟨next, step, _⟩
    cases next with
    | none => exact step
    | some next => cases step
  · intro observes
    exact ⟨none, observes, readings.terminal_value.symm⟩

/-- Action entries recover exactly the interpreted values of actual labelled
successors, with no additional transitions. -/
theorem action_iff (readings : LabelReadings M) (faithful : readings.Faithful)
    (term : S.Term) (label : M.Label) (target : HSet.{u}) :
    HSet.kpair (readings.taggedReading (.inr label)) target ∈ readings.value term ↔
      ∃ next, M.act label term next ∧ target = readings.value next := by
  rw [readings.entry_iff faithful]
  constructor
  · rintro ⟨next, step, equal⟩
    cases next with
    | none => cases step
    | some next => exact ⟨next, step, equal⟩
  · rintro ⟨next, step, equal⟩
    exact ⟨some next, step, equal⟩

/-- HML interpretation directly on material sets, using the separately
tagged atomic entries and labelled action entries. -/
def materialSat (readings : LabelReadings M) : Formula M.Atom M.Label → HSet.{u} → Prop
  | .top, _ => True
  | .atom atom, value => HSet.kpair (readings.taggedReading (.inl atom)) ∅ ∈ value
  | .conj left right, value => materialSat readings left value ∧ materialSat readings right value
  | .neg inner, value => ¬ materialSat readings inner value
  | .dia label inner, value =>
      ∃ target, HSet.kpair (readings.taggedReading (.inr label)) target ∈ value ∧
        materialSat readings inner target

/-- Every HML formula has the same truth value in the source and its actual
material interpretation. This statement requires no image-finiteness. -/
theorem materialSat_value (readings : LabelReadings M) (faithful : readings.Faithful) :
    ∀ (formula : Formula M.Atom M.Label) (term : S.Term),
      readings.materialSat formula (readings.value term) ↔ M.sat formula term
  | .top, _ => Iff.rfl
  | .atom atom, term => readings.observation_iff faithful term atom
  | .conj left right, term =>
      and_congr (materialSat_value readings faithful left term)
        (materialSat_value readings faithful right term)
  | .neg inner, term => not_congr (materialSat_value readings faithful inner term)
  | .dia label inner, term => by
      constructor
      · rintro ⟨target, entry, holds⟩
        obtain ⟨next, step, rfl⟩ := (readings.action_iff faithful term label target).mp entry
        exact ⟨next, step, (materialSat_value readings faithful inner next).mp holds⟩
      · rintro ⟨next, step, holds⟩
        exact ⟨readings.value next,
          (readings.action_iff faithful term label _).mpr ⟨next, step, rfl⟩,
          (materialSat_value readings faithful inner next).mpr holds⟩

private def extendRelation (relation : S.Term → S.Term → Prop) :
    Option S.Term → Option S.Term → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

/-- An observed source bisimulation matches the encoded observation entries
as well as the encoded labelled action entries. -/
theorem encoded_isLabelledBisimulation (readings : LabelReadings M)
    {relation : S.Term → S.Term → Prop} (bisimulation : M.IsBisimulation relation) :
    IsLabelledBisimulation (encodedStep M) (encodedStep M)
      readings.taggedReading readings.taggedReading (extendRelation relation) := by
  intro left right related
  cases left with
  | none =>
    cases right with
    | none =>
      constructor <;> intro label next step <;> cases label <;> cases next <;> cases step
    | some right => cases related
  | some left =>
    cases right with
    | none => cases related
    | some right =>
      constructor
      · intro label next step
        cases label with
        | inl atom =>
          cases next with
          | none => exact ⟨.inl atom, none, (bisimulation.2.2 related atom).mp step, rfl, trivial⟩
          | some next => cases step
        | inr label =>
          cases next with
          | none => cases step
          | some next =>
            obtain ⟨matched, action, successors⟩ := bisimulation.1 related label step
            exact ⟨.inr label, some matched, action, rfl, successors⟩
      · intro label next step
        cases label with
        | inl atom =>
          cases next with
          | none => exact ⟨.inl atom, none, (bisimulation.2.2 related atom).mpr step, rfl, trivial⟩
          | some next => cases step
        | inr label =>
          cases next with
          | none => cases step
          | some next =>
            obtain ⟨matched, action, successors⟩ := bisimulation.2.1 related label step
            exact ⟨.inr label, some matched, action, rfl, successors⟩

/-- Observed labelled bisimilarity preserves the material value even when the
chosen readings identify some literal observation or label names. -/
theorem value_eq_of_bisimilar (readings : LabelReadings M) {left right : S.Term}
    (related : M.Bisimilar left right) : readings.value left = readings.value right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact readings.taggedPresentation.decorate_eq_of_labelledBisimilar readings.taggedPresentation
    ⟨extendRelation relation, readings.encoded_isLabelledBisimulation bisimulation, related⟩

/-- When readings identify literal labels, material equality still has an
exact characterization by the readout-labelled bisimilarity of the encoded
observation/action system. Literal source-system reflection is stronger. -/
theorem value_eq_iff_readoutBisimilar (readings : LabelReadings M) (left right : S.Term) :
    readings.value left = readings.value right ↔
      LabelledBisimilar (encodedStep M) (encodedStep M)
        readings.taggedReading readings.taggedReading (some left) (some right) :=
  readings.taggedPresentation.decorate_eq_iff_labelledBisimilar readings.taggedPresentation

/-- With faithful readings, the value kernel preserves every action and every
atomic observation in the original System. -/
theorem kernel_isBisimulation (readings : LabelReadings M) (faithful : readings.Faithful) :
    M.IsBisimulation (fun left right => readings.value left = readings.value right) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right equal label next step
    have entry := (readings.action_iff faithful left label (readings.value next)).mpr
      ⟨next, step, rfl⟩
    rw [equal] at entry
    obtain ⟨matched, action, successors⟩ :=
      (readings.action_iff faithful right label _).mp entry
    exact ⟨matched, action, successors⟩
  · intro left right equal label next step
    have entry := (readings.action_iff faithful right label (readings.value next)).mpr
      ⟨next, step, rfl⟩
    rw [← equal] at entry
    obtain ⟨matched, action, successors⟩ :=
      (readings.action_iff faithful left label _).mp entry
    exact ⟨matched, action, successors.symm⟩
  · intro left right equal atom
    rw [← readings.observation_iff faithful left atom,
      ← readings.observation_iff faithful right atom, equal]

/-- The material equality kernel is exactly the existing observed labelled
bisimilarity, including its atomic valuation clause. -/
theorem value_eq_iff_bisimilar (readings : LabelReadings M) (faithful : readings.Faithful)
    (left right : S.Term) : readings.value left = readings.value right ↔ M.Bisimilar left right :=
  ⟨fun equal => ⟨_, readings.kernel_isBisimulation faithful, equal⟩,
    readings.value_eq_of_bisimilar⟩

theorem value_eq_of_equiv (readings : LabelReadings M) {left right : S.Term}
    (equivalent : S.Equiv left right) : readings.value left = readings.value right :=
  readings.value_eq_of_bisimilar (M.bisimilar_of_equiv equivalent)

/-- The authored equation quotient has a representative-independent material
reading; its equality remains the source theory's own equality. -/
def equationValue (readings : LabelReadings M) : Quotient S.equations → HSet.{u} :=
  Quotient.lift readings.value (fun _ _ equivalent => readings.value_eq_of_equiv equivalent)

theorem equationValue_mk (readings : LabelReadings M) (term : S.Term) :
    readings.equationValue (Quotient.mk S.equations term) = readings.value term :=
  rfl

/-- Equality of material readings always preserves every interpreted formula. -/
theorem material_logicallyEquivalent_of_value_eq (readings : LabelReadings M)
    {left right : S.Term} (equal : readings.value left = readings.value right) :
    ∀ formula, readings.materialSat formula (readings.value left) ↔
      readings.materialSat formula (readings.value right) :=
  fun _ => equal ▸ Iff.rfl

/-- Finite behavioural covers supply the existing Hennessy--Milner converse.
Its hypotheses concern the source System, without changing its equations. -/
theorem value_eq_iff_material_logicallyEquivalent (readings : LabelReadings M)
    (faithful : readings.Faithful) (finite : M.ImageFiniteBisimilar) (left right : S.Term) :
    readings.value left = readings.value right ↔
      ∀ formula, readings.materialSat formula (readings.value left) ↔
        readings.materialSat formula (readings.value right) := by
  rw [readings.value_eq_iff_bisimilar faithful]
  constructor
  · intro related formula
    exact (readings.materialSat_value faithful formula left).trans
      ((M.logicallyEquivalent_of_bisimilar related formula).trans
        (readings.materialSat_value faithful formula right).symm)
  · intro agrees
    apply M.bisimilar_of_logicallyEquivalent_of_imageFiniteBisimilar finite
    intro formula
    exact (readings.materialSat_value faithful formula left).symm.trans
      ((agrees formula).trans (readings.materialSat_value faithful formula right))

theorem value_eq_iff_material_logicallyEquivalent_of_imageFiniteModulo
    (readings : LabelReadings M) (faithful : readings.Faithful)
    (finite : M.ImageFiniteModulo) (left right : S.Term) :
    readings.value left = readings.value right ↔
      ∀ formula, readings.materialSat formula (readings.value left) ↔
        readings.materialSat formula (readings.value right) :=
  readings.value_eq_iff_material_logicallyEquivalent faithful
    (M.imageFiniteBisimilar_of_imageFiniteModulo finite) left right

end LabelReadings

/-! ## Retained authored action occurrences -/

/-- Authored occurrence fibres are data, whose existence realizes the
labelled action relation. Their identities need not descend to a set value. -/
structure ActionOccurrences (M : System.{u, u} S) : Type (u + 1) where
  Occurrence : M.Label → S.Term → S.Term → Type u
  erases : ∀ label source target, Nonempty (Occurrence label source target) ↔ M.act label source target

namespace ActionOccurrences

open Mettapedia.OSLF.Framework.DerivedModalities ObservationSpans

variable {M : System.{u, u} S}

structure Event (occurrences : ActionOccurrences M) : Type u where
  label : M.Label
  source : S.Term
  target : S.Term
  occurrence : occurrences.Occurrence label source target

def sourceSpan (occurrences : ActionOccurrences M) : ReductionSpan S.Term where
  Edge := Event occurrences
  source event := event.source
  target event := event.target

/-- The material span retains the complete authored event; only its endpoint
observations change. -/
def materialSpan (occurrences : ActionOccurrences M) (readings : LabelReadings M) :
    ReductionSpan HSet.{u} where
  Edge := Event occurrences
  source event := readings.value event.source
  target event := readings.value event.target

def observation (occurrences : ActionOccurrences M) (readings : LabelReadings M) :
    SpanMap occurrences.sourceSpan (occurrences.materialSpan readings) where
  states := readings.value
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

theorem events_injective (occurrences : ActionOccurrences M) (readings : LabelReadings M) :
    Function.Injective (occurrences.observation readings).events :=
  fun _ _ equal => equal

theorem label_preserved (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (event : Event occurrences) :
    ((occurrences.observation readings).events event).label = event.label :=
  rfl

/-- Observed bisimulation produces an actual labelled action at the requested
source representative, and the supplied occurrence fibre realizes it. -/
theorem sourceLifts (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (faithful : readings.Faithful) : (occurrences.observation readings).SourceLifts := by
  intro state event sourceEqual
  change readings.value event.source = readings.value state at sourceEqual
  have action := (occurrences.erases event.label event.source event.target).mp ⟨event.occurrence⟩
  obtain ⟨target, reduction, targetEqual⟩ :=
    (readings.kernel_isBisimulation faithful).2.1 sourceEqual.symm event.label action
  obtain ⟨occurrence⟩ := (occurrences.erases event.label state target).mpr reduction
  exact ⟨⟨event.label, state, target, occurrence⟩, rfl, targetEqual⟩

theorem diamond_pullback (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (faithful : readings.Faithful) (predicate : HSet.{u} → Prop) (state : S.Term) :
    derivedDiamond (occurrences.materialSpan readings) predicate (readings.value state) ↔
      derivedDiamond occurrences.sourceSpan (predicate ∘ readings.value) state :=
  (occurrences.observation readings).diamond_pullback
    (occurrences.sourceLifts readings faithful) predicate state

/-- The incoming lifting obligation is separate from observed future
bisimulation. Supplying it gives OSLF's actual predecessor box law. -/
theorem box_pullback (occurrences : ActionOccurrences M) (readings : LabelReadings M)
    (incoming : (occurrences.observation readings).TargetLifts)
    (predicate : HSet.{u} → Prop) (state : S.Term) :
    derivedBox (occurrences.materialSpan readings) predicate (readings.value state) ↔
      derivedBox occurrences.sourceSpan (predicate ∘ readings.value) state :=
  (occurrences.observation readings).box_pullback incoming predicate state

end ActionOccurrences

namespace LabelReadings

variable {M : System.{u, u} S}

/-- A predicate descends precisely when observed labelled bisimilarity cannot
separate its truth values. This is a restriction of the full native frame. -/
theorem predicateDescends_iff (readings : LabelReadings M) (faithful : readings.Faithful)
    (predicate : S.Term → Prop) :
    ObservationSpans.PredicateDescends readings.value predicate ↔
      ∀ ⦃left right⦄, M.Bisimilar left right → (predicate left ↔ predicate right) := by
  rw [ObservationSpans.predicateDescends_iff]
  constructor
  · intro constant left right related
    exact Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant (readings.value_eq_of_bisimilar related)
  · intro invariant left right equal
    exact propext (invariant ((readings.value_eq_iff_bisimilar faithful left right).mp equal))

end LabelReadings

/-! ## Saturated contextual systems -/

namespace Relative

open MinimalEnablingContext AdmissibleContextCongruence ObservationSpans
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {rules : ContextualRules.{u, u} S}
variable (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{u} S)
variable (readings : LabelReadings (A.saturated observations))

/-- The actual context-relative behavioural classes have a material reading,
constructed by quotient elimination rather than representative selection. -/
def valueOnClasses : RelativeState A observations → HSet.{u} :=
  Quotient.lift readings.value (fun _ _ related => readings.value_eq_of_bisimilar related)

theorem valueOnClasses_observe (state : S.Term) :
    valueOnClasses A observations readings (relativeObserve A observations state) =
      readings.value state :=
  rfl

theorem valueOnClasses_injective (faithful : readings.Faithful) :
    Function.Injective (valueOnClasses A observations readings) := by
  intro left right equal
  induction left using Quotient.inductionOn with
  | _ left =>
    induction right using Quotient.inductionOn with
    | _ right =>
      exact Quotient.sound ((readings.value_eq_iff_bisimilar faithful left right).mp equal)

theorem context_preserves_value_eq (faithful : readings.Faithful)
    (context : rules.Context) (admissible : A.Admissible context)
    {left right : S.Term} (equal : readings.value left = readings.value right) :
    readings.value (rules.plug context left) = readings.value (rules.plug context right) :=
  readings.value_eq_of_bisimilar
    (A.relEquiv_closedUnder observations admissible
      ((readings.value_eq_iff_bisimilar faithful left right).mp equal))

/-- The existing actual quotient context action commutes with the material
reading on authored representatives. -/
theorem contextAction_value (context : rules.Context) (admissible : A.Admissible context)
    (state : S.Term) :
    valueOnClasses A observations readings
        (contextAction A observations context admissible (relativeObserve A observations state)) =
      readings.value (rules.plug context state) :=
  rfl

theorem contextAction_identity_value (state : RelativeState A observations) :
    valueOnClasses A observations readings
        (contextAction A observations rules.identity A.identity_mem state) =
      valueOnClasses A observations readings state :=
  congrArg (valueOnClasses A observations readings) (contextAction_identity A observations state)

theorem contextAction_compose_value (outer inner : rules.Context)
    (outerAdmissible : A.Admissible outer) (innerAdmissible : A.Admissible inner)
    (state : RelativeState A observations) :
    valueOnClasses A observations readings
        (contextAction A observations (rules.compose outer inner)
          (A.compose_mem outerAdmissible innerAdmissible) state) =
      valueOnClasses A observations readings
        (contextAction A observations outer outerAdmissible
          (contextAction A observations inner innerAdmissible state)) :=
  congrArg (valueOnClasses A observations readings)
    (contextAction_compose A observations outer inner outerAdmissible innerAdmissible state)

theorem substitution_value (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right)) (state : S.Term) :
    valueOnClasses A observations readings
        (quotientSubstitution A observations substitution respects (relativeObserve A observations state)) =
      readings.value (substitution state) :=
  rfl

theorem context_substitution_value (context : rules.Context) (admissible : A.Admissible context)
    (substitution : S.Term → S.Term)
    (respects : ∀ ⦃left right⦄, A.RelEquiv observations left right →
      A.RelEquiv observations (substitution left) (substitution right))
    (commutes : ∀ state, S.Equiv (substitution (rules.plug context state))
      (rules.plug context (substitution state))) (state : RelativeState A observations) :
    valueOnClasses A observations readings
        (quotientSubstitution A observations substitution respects
          (contextAction A observations context admissible state)) =
      valueOnClasses A observations readings
        (contextAction A observations context admissible
          (quotientSubstitution A observations substitution respects state)) :=
  congrArg (valueOnClasses A observations readings)
    (contextAction_substitution A observations context admissible substitution respects commutes state)

/-- The relative reduction span retains its authored edge carrier while
exposing the actual material values of both endpoint classes. -/
def materialSpan : ReductionSpan HSet.{u} where
  Edge := (relativeSpan A observations).Edge
  source event := valueOnClasses A observations readings ((relativeSpan A observations).source event)
  target event := valueOnClasses A observations readings ((relativeSpan A observations).target event)

def spanMap : SpanMap (relativeSpan A observations) (materialSpan A observations readings) where
  states := valueOnClasses A observations readings
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

theorem sourceLifts (faithful : readings.Faithful) :
    (spanMap A observations readings).SourceLifts := by
  intro state event equal
  exact ⟨event, valueOnClasses_injective A observations readings faithful equal, rfl⟩

theorem targetLifts (faithful : readings.Faithful) :
    (spanMap A observations readings).TargetLifts := by
  intro state event equal
  exact ⟨event, valueOnClasses_injective A observations readings faithful equal, rfl⟩

/-- Material future diamond agrees with the actual GSLT reduction diamond
through the proved relative source lifting and the faithful material embedding. -/
theorem material_diamond (faithful : readings.Faithful) (predicate : HSet.{u} → Prop)
    (state : S.Term) :
    derivedDiamond (materialSpan A observations readings) predicate (readings.value state) ↔
      gsltDiamond S (predicate ∘ readings.value) state := by
  exact ((spanMap A observations readings).diamond_pullback
    (sourceLifts A observations readings faithful) predicate (relativeObserve A observations state)).trans
      (relative_diamond A observations (predicate ∘ valueOnClasses A observations readings) state)

/-- Agreement with the source predecessor box still requires the source
relative equivalence to match incoming reductions. -/
theorem material_box (faithful : readings.Faithful)
    (past : PastMatching (gsltSpan S) (relativeSetoid A observations))
    (predicate : HSet.{u} → Prop) (state : S.Term) :
    derivedBox (materialSpan A observations readings) predicate (readings.value state) ↔
      gsltBox S (predicate ∘ readings.value) state := by
  exact ((spanMap A observations readings).box_pullback
    (targetLifts A observations readings faithful) predicate (relativeObserve A observations state)).trans
      (relative_box A observations past (predicate ∘ valueOnClasses A observations readings) state)

end Relative

namespace Controls

open OutcomeLabels

/-- Observable terminal outcomes and a genuinely advancing two-state cycle. -/
inductive State : Type u where
  | terminal (outcome : Outcome.{u})
  | cycle (outcome : Outcome.{u}) (phase : Bool)
  deriving DecidableEq

def outcome : State.{u} → Outcome.{u}
  | .terminal result => result
  | .cycle result _ => result

def step : State.{u} → State.{u} → Prop
  | .cycle result phase, .cycle result' phase' => result = result' ∧ phase' = !phase
  | _, _ => False

/-- The example's source equations are literal equality; its reductions
really advance the cycle phase. -/
def theory : GSLT.{u} where
  Term := State.{u}
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := step
  rewrites_resp_left := by
    intro left right target equal reduction
    exact ⟨target, equal ▸ reduction, rfl⟩
  rewrites_resp_right := by
    intro source target target' reduction equal
    exact equal ▸ reduction

/-- Results and faults are actual atoms of an observed labelled System. -/
def system : System.{u, u} theory.{u} where
  Atom := Outcome.{u}
  observes atom state := atom = outcome state
  observes_resp := by
    intro atom left right equal
    exact equal ▸ Iff.rfl
  Label := PUnit.{u + 1}
  act _ := step
  act_resp_left := by
    intro label left right target equal reduction
    exact ⟨target, equal ▸ reduction, rfl⟩
  act_resp_right := by
    intro label source target target' reduction equal
    exact equal ▸ reduction

/-- This instance uses the concrete result/fault graphs and a concrete
empty graph for the single action label. -/
def readings : LabelReadings system.{u} where
  atom := OutcomeLabels.reading
  action _ := ∅
  atomPresentation := OutcomeLabels.presented
  actionPresentation :=
    ⟨fun _ => AccessiblePointedGraph.empty, fun _ => HSet.mk_empty⟩

theorem faithful : readings.{u}.Faithful := by
  constructor
  · exact OutcomeLabels.reading_injective
  · change Function.Injective (fun _ : PUnit.{u + 1} => (∅ : HSet.{u}))
    exact fun _ _ _ => Subsingleton.elim _ _

theorem terminal_values_injective :
    Function.Injective (fun result : Outcome.{u} => readings.value (State.terminal result)) := by
  intro first second equal
  change readings.value (State.terminal first) = readings.value (State.terminal second) at equal
  have entry := (readings.observation_iff faithful (State.terminal first) first).mpr rfl
  rw [equal] at entry
  exact (readings.observation_iff faithful (State.terminal second) first).mp entry

theorem different_results {n m : Nat} (different : n ≠ m) :
    readings.value (State.terminal (Outcome.result n : Outcome.{u})) ≠
      readings.value (State.terminal (Outcome.result m)) := by
  intro equal
  exact different (Outcome.result.inj (terminal_values_injective equal))

theorem result_ne_fault (n : Nat) (fault : Fault.{u}) :
    readings.value (State.terminal (Outcome.result n)) ≠
      readings.value (State.terminal (Outcome.fault fault)) := by
  intro equal
  exact Outcome.noConfusion (terminal_values_injective equal)

theorem faults_distinguished :
    readings.value (State.terminal (Outcome.fault Fault.divisionByZero : Outcome.{u})) ≠
      readings.value (State.terminal (Outcome.fault Fault.unboundSymbol)) := by
  intro equal
  exact Fault.noConfusion (Outcome.fault.inj (terminal_values_injective equal))

private def sameCycleOutcome (left right : State.{u}) : Prop :=
  ∃ result first second, left = .cycle result first ∧ right = .cycle result second

private theorem sameCycleOutcome_isBisimulation :
    system.{u}.IsBisimulation sameCycleOutcome := by
  refine ⟨?_, ?_, ?_⟩
  · rintro left right ⟨result, first, second, rfl, rfl⟩ label next action
    cases next with
    | terminal _ => cases action
    | cycle result' nextPhase =>
      change result = result' ∧ nextPhase = !first at action
      rcases action with ⟨rfl, rfl⟩
      exact ⟨State.cycle result (!second), ⟨rfl, rfl⟩, result, !first, !second, rfl, rfl⟩
  · rintro left right ⟨result, first, second, rfl, rfl⟩ label next action
    cases next with
    | terminal _ => cases action
    | cycle result' nextPhase =>
      change result = result' ∧ nextPhase = !second at action
      rcases action with ⟨rfl, rfl⟩
      exact ⟨State.cycle result (!first), ⟨rfl, rfl⟩, result, !first, !second, rfl, rfl⟩
  · rintro left right ⟨result, first, second, rfl, rfl⟩ atom
    exact Iff.rfl

/-- Two different phases have the same observations and matching cyclic futures. -/
theorem cycle_values_eq (result : Outcome.{u}) (first second : Bool) :
    readings.value (State.cycle result first) = readings.value (State.cycle result second) :=
  readings.value_eq_of_bisimilar
    ⟨sameCycleOutcome, sameCycleOutcome_isBisimulation, result, first, second, rfl, rfl⟩

/-- A genuine source reduction changes its authored state while preserving
the declared observed behaviour. -/
theorem cycle_advances (result : Outcome.{u}) (phase : Bool) :
    theory.Step (State.cycle result phase) (State.cycle result (!phase)) ∧
      State.cycle result phase ≠ State.cycle result (!phase) ∧
      readings.value (State.cycle result phase) = readings.value (State.cycle result (!phase)) := by
  refine ⟨⟨rfl, rfl⟩, ?_, cycle_values_eq result phase (!phase)⟩
  intro equal
  have phases := (State.cycle.inj equal).2
  cases phase <;> cases phases

/-- Termination and cyclic continuation are separated by action membership,
even when they report the same outcome. -/
theorem terminal_ne_cycle (result : Outcome.{u}) (phase : Bool) :
    readings.value (State.terminal result) ≠ readings.value (State.cycle result phase) := by
  intro equal
  have entry :=
    (readings.action_iff faithful (State.cycle result phase) PUnit.unit
      (readings.value (State.cycle result (!phase)))).mpr
        ⟨State.cycle result (!phase), ⟨rfl, rfl⟩, rfl⟩
  rw [← equal] at entry
  obtain ⟨next, action, _⟩ :=
    (readings.action_iff faithful (State.terminal result) PUnit.unit _).mp entry
  cases next <;> cases action

theorem cycle_not_wf (result : Outcome.{u}) (phase : Bool) :
    ¬ (readings.value (State.cycle result phase)).WF := by
  let value := readings.value (State.cycle result phase)
  let label := readings.taggedReading (.inr PUnit.unit)
  apply HSet.not_wf_of_cycle (y := HSet.kpair label value) (z := {label, value})
  · exact (readings.action_iff faithful (State.cycle result phase) PUnit.unit value).mpr
      ⟨State.cycle result (!phase), ⟨rfl, rfl⟩, cycle_values_eq result phase (!phase)⟩
  · exact HSet.mem_kpair.mpr (Or.inr rfl)
  · exact HSet.mem_pair.mpr (Or.inr rfl)

theorem plain_terminal_empty (result : Outcome.{u}) :
    HSet.decorate theory.Step (State.terminal result) = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro y member
  obtain ⟨next, reduction, _⟩ := HSet.mem_decorate.mp member
  cases next <;> cases reduction

/-- Omitting atomic observations collapses a result and a fault; the observed
material construction separates these actual source-system states. -/
theorem plain_decoration_loses_outcomes :
    HSet.decorate theory.Step (State.terminal (Outcome.result 0 : Outcome.{u})) =
        HSet.decorate theory.Step (State.terminal (Outcome.fault Fault.divisionByZero)) ∧
      readings.value (State.terminal (Outcome.result 0)) ≠
        readings.value (State.terminal (Outcome.fault Fault.divisionByZero)) :=
  ⟨(plain_terminal_empty _).trans (plain_terminal_empty _).symm, result_ne_fault 0 _⟩

/-- The singleton cover is finite by an explicit enumeration. -/
private theorem singletonFinite (state : State.{u}) : ({state} : Set State.{u}).Finite := by
  change Finite {value : State.{u} // value ∈ ({state} : Set State.{u})}
  exact Finite.intro {
    toFun _ := (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)
    invFun _ := ⟨state, Set.mem_singleton state⟩
    left_inv value := Subtype.ext (Set.mem_singleton_iff.mp value.property).symm
    right_inv index := Fin.ext (Nat.lt_one_iff.mp index.isLt).symm }

private theorem emptyFinite : (∅ : Set State.{u}).Finite := by
  change Finite {value : State.{u} // value ∈ (∅ : Set State.{u})}
  let enumeration : {value : State.{u} // value ∈ (∅ : Set State.{u})} ≃ Fin 0 := {
    toFun value := False.elim value.property
    invFun index := Fin.elim0 index
    left_inv value := False.elim value.property
    right_inv index := Fin.elim0 index }
  exact Finite.intro enumeration

/-- The actual system has at most one labelled successor at every state. -/
theorem imageFiniteModulo : system.{u}.ImageFiniteModulo := by
  intro label state
  cases state with
  | terminal result =>
    refine ⟨∅, emptyFinite, ?_⟩
    intro target action
    cases target <;> cases action
  | cycle result phase =>
    refine ⟨{State.cycle result (!phase)}, singletonFinite _, ?_⟩
    intro target action
    cases target with
    | terminal _ => cases action
    | cycle result' nextPhase =>
      change result = result' ∧ nextPhase = !phase at action
      rcases action with ⟨rfl, rfl⟩
      exact ⟨State.cycle result (!phase), Set.mem_singleton _, rfl⟩

end Controls

namespace ProvenanceControls

open OutcomeLabels

/-- The two initial states have the same result and successor, but the second
has an additional authored provenance occurrence. -/
inductive State : Type u where
  | single
  | double
  | done
  deriving DecidableEq

def step (source target : State.{u}) : Prop := source ≠ .done ∧ target = .done

private theorem single_ne_done : State.single ≠ (State.done : State.{u}) :=
  fun impossible => State.noConfusion impossible

private theorem double_ne_done : State.double ≠ (State.done : State.{u}) :=
  fun impossible => State.noConfusion impossible

def theory : GSLT.{u} where
  Term := State.{u}
  equations := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  rewrites := step
  rewrites_resp_left := by
    intro left right target equal reduction
    exact ⟨target, equal ▸ reduction, rfl⟩
  rewrites_resp_right := by
    intro source target target' reduction equal
    exact equal ▸ reduction

/-- A provenance occurrence is observed as a label only in the richer profile. -/
def authored (source : State.{u}) (provenance : ULift.{u} Bool) (target : State.{u}) : Prop :=
  step source target ∧ (source = .single → provenance.down = false)

def plain (result : Outcome.{u}) : System.{u, u} theory.{u} where
  Atom := Outcome.{u}
  observes atom state := state = .done ∧ atom = result
  observes_resp := by
    intro atom left right equal
    exact equal ▸ Iff.rfl
  Label := PUnit.{u + 1}
  act _ := step
  act_resp_left := by
    intro label left right target equal reduction
    exact ⟨target, equal ▸ reduction, rfl⟩
  act_resp_right := by
    intro label source target target' reduction equal
    exact equal ▸ reduction

def rich (result : Outcome.{u}) : System.{u, u} theory.{u} where
  Atom := Outcome.{u}
  observes atom state := state = .done ∧ atom = result
  observes_resp := by
    intro atom left right equal
    exact equal ▸ Iff.rfl
  Label := ULift.{u} Bool
  act provenance source target := authored source provenance target
  act_resp_left := by
    intro label left right target equal reduction
    exact ⟨target, equal ▸ reduction, rfl⟩
  act_resp_right := by
    intro label source target target' reduction equal
    exact equal ▸ reduction

def plainReadings (result : Outcome.{u}) : LabelReadings (plain result) where
  atom := OutcomeLabels.reading
  action _ := ∅
  atomPresentation := OutcomeLabels.presented
  actionPresentation := ⟨fun _ => AccessiblePointedGraph.empty, fun _ => HSet.mk_empty⟩

def richReadings (result : Outcome.{u}) : LabelReadings (rich result) where
  atom := OutcomeLabels.reading
  action provenance := chainValue (if provenance.down then 1 else 0)
  atomPresentation := OutcomeLabels.presented
  actionPresentation :=
    ⟨fun provenance => chainGraph (if provenance.down then 1 else 0),
      fun provenance => mk_chainGraph (if provenance.down then 1 else 0)⟩

theorem plainFaithful (result : Outcome.{u}) : (plainReadings result).Faithful := by
  constructor
  · exact OutcomeLabels.reading_injective
  · change Function.Injective (fun _ : PUnit.{u + 1} => (∅ : HSet.{u}))
    exact fun _ _ _ => Subsingleton.elim _ _

theorem richFaithful (result : Outcome.{u}) : (richReadings result).Faithful := by
  constructor
  · exact OutcomeLabels.reading_injective
  · intro first second equal
    apply ULift.ext
    have codes := chainValue_injective equal
    cases first with
    | up first =>
      cases second with
      | up second => cases first <;> cases second <;> simp_all

private def sameTermination (left right : State.{u}) : Prop :=
  left = .done ↔ right = .done

private theorem sameTermination_isBisimulation (result : Outcome.{u}) :
    (plain result).IsBisimulation sameTermination := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label target action
    change left ≠ .done ∧ target = .done at action
    rcases action with ⟨notDone, rfl⟩
    exact ⟨State.done, ⟨fun equal => notDone (related.mpr equal), rfl⟩, Iff.rfl⟩
  · intro left right related label target action
    change right ≠ .done ∧ target = .done at action
    rcases action with ⟨notDone, rfl⟩
    exact ⟨State.done, ⟨fun equal => notDone (related.mp equal), rfl⟩, Iff.rfl⟩
  · intro left right related atom
    exact and_congr related Iff.rfl

theorem plain_values_eq (result : Outcome.{u}) :
    (plainReadings result).value State.single = (plainReadings result).value State.double :=
  (plainReadings result).value_eq_of_bisimilar
    ⟨sameTermination, sameTermination_isBisimulation result,
      ⟨fun impossible => State.noConfusion impossible, fun impossible => State.noConfusion impossible⟩⟩

/-- Literal provenance labels are reflected by the material kernel. -/
theorem rich_values_ne (result : Outcome.{u}) :
    (richReadings result).value State.single ≠ (richReadings result).value State.double := by
  intro equal
  have entry := ((richReadings result).action_iff (richFaithful result) State.double
    ⟨true⟩ ((richReadings result).value State.done)).mpr
      ⟨State.done, ⟨⟨double_ne_done, rfl⟩,
        fun impossible => State.noConfusion impossible⟩, rfl⟩
  rw [← equal] at entry
  obtain ⟨target, action, _⟩ := ((richReadings result).action_iff
    (richFaithful result) State.single ⟨true⟩ _).mp entry
  exact Bool.noConfusion (action.2 rfl)

/-- Every concrete step is retained as a type-valued fibre of authored
provenance occurrences, even in the profile that ignores provenance labels. -/
def occurrences (result : Outcome.{u}) : ActionOccurrences (plain result) where
  Occurrence _ source target := Σ provenance : ULift.{u} Bool, PLift (authored source provenance target)
  erases _ source target := by
    constructor
    · rintro ⟨⟨provenance, action⟩⟩
      exact action.down.1
    · intro action
      exact ⟨⟨⟨false⟩, ⟨action, fun _ => rfl⟩⟩⟩

def doubleEvent (result : Outcome.{u}) (provenance : Bool) :
    ActionOccurrences.Event (occurrences result) where
  label := PUnit.unit
  source := State.double
  target := State.done
  occurrence := ⟨⟨provenance⟩, ⟨⟨double_ne_done, rfl⟩,
    fun impossible => State.noConfusion impossible⟩⟩

def singleEvent (result : Outcome.{u}) : ActionOccurrences.Event (occurrences result) where
  label := PUnit.unit
  source := State.single
  target := State.done
  occurrence := ⟨⟨false⟩, ⟨⟨single_ne_done, rfl⟩, fun _ => rfl⟩⟩

/-- The richer profile observes precisely the provenance retained by the
plain profile's actual occurrence fibres. -/
theorem rich_action_iff_occurrence (result : Outcome.{u}) (tag : ULift.{u} Bool)
    (source target : State.{u}) :
    (rich result).act tag source target ↔
      ∃ occurrence : (occurrences result).Occurrence PUnit.unit source target,
        occurrence.1 = tag := by
  constructor
  · intro action
    exact ⟨⟨tag, ⟨action⟩⟩, rfl⟩
  · rintro ⟨⟨provenance, action⟩, equal⟩
    exact equal ▸ action.down

def provenance (result : Outcome.{u}) (event : ActionOccurrences.Event (occurrences result)) : Bool :=
  event.occurrence.1.down

def materialEntry (result : Outcome.{u}) (event : ActionOccurrences.Event (occurrences result)) :
    HSet.{u} :=
  HSet.kpair ((plainReadings result).taggedReading (.inr event.label))
    ((plainReadings result).value event.target)

theorem double_events_distinct (result : Outcome.{u}) :
    doubleEvent result false ≠ doubleEvent result true := by
  intro equal
  exact Bool.noConfusion (congrArg (provenance result) equal)

theorem material_events_distinct (result : Outcome.{u}) :
    ((occurrences result).observation (plainReadings result)).events (doubleEvent result false) ≠
      ((occurrences result).observation (plainReadings result)).events (doubleEvent result true) := by
  intro equal
  exact double_events_distinct result
    ((occurrences result).events_injective (plainReadings result) equal)

theorem double_entries_eq (result : Outcome.{u}) :
    materialEntry result (doubleEvent result false) = materialEntry result (doubleEvent result true) :=
  rfl

/-- The material entry seen by the plain observer cannot recover the
provenance-dependent continuation carried by the source event fibre. -/
theorem provenance_does_not_factor (result : Outcome.{u}) :
    ¬ ∃ read : HSet.{u} → Bool,
      ∀ event, read (materialEntry result event) = provenance result event := by
  rintro ⟨read, recovers⟩
  have equal := (recovers (doubleEvent result false)).symm.trans
    ((congrArg read (double_entries_eq result)).trans (recovers (doubleEvent result true)))
  exact Bool.noConfusion equal

/-- Endpoint lifting does not promise that the same authored occurrence is
available at every behaviourally equal source representative. -/
theorem no_source_occurrence_lifting (result : Outcome.{u}) :
    ¬ ((occurrences result).observation (plainReadings result)).SourceOccurrenceLifts := by
  intro lifts
  obtain ⟨event, source, observed⟩ := lifts State.single (doubleEvent result false)
    (plain_values_eq result).symm
  change event = doubleEvent result false at observed
  subst event
  exact State.noConfusion source

/-- A real one-step computation changes the observed value when its pending
action disappears and its declared result or fault becomes observable. -/
theorem step_changes_value (result : Outcome.{u}) :
    theory.Step State.single State.done ∧
      (plainReadings result).value State.single ≠ (plainReadings result).value State.done := by
  refine ⟨⟨single_ne_done, rfl⟩, ?_⟩
  intro equal
  have entry := ((plainReadings result).action_iff (plainFaithful result) State.single PUnit.unit
    ((plainReadings result).value State.done)).mpr
      ⟨State.done, ⟨single_ne_done, rfl⟩, rfl⟩
  rw [equal] at entry
  obtain ⟨target, action, _⟩ := ((plainReadings result).action_iff
    (plainFaithful result) State.done PUnit.unit _).mp entry
  exact action.1 rfl

theorem done_observes_result (result : Outcome.{u}) :
    HSet.kpair ((plainReadings result).taggedReading (.inl result)) ∅ ∈
      (plainReadings result).value State.done :=
  ((plainReadings result).observation_iff (plainFaithful result) State.done result).mpr ⟨rfl, rfl⟩

/-- The full native predicate frame contains a predicate that separates
behaviourally equal sources and therefore has no material descent. -/
theorem native_predicate_does_not_descend (result : Outcome.{u}) :
    ¬ ObservationSpans.PredicateDescends (plainReadings result).value
      (fun state => state = State.single) := by
  intro descends
  have constant := (ObservationSpans.predicateDescends_iff _ _).mp descends
  have truth := Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant (plain_values_eq result)
  exact State.noConfusion (truth.mp rfl)

end ProvenanceControls

end Mettapedia.GSLT.ObservedMaterialization
