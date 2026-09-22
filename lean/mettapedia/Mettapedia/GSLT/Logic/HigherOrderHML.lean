import Mettapedia.GSLT.Logic.HigherOrderBisimulation
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Interface-indexed systems through the existing HML semantics

Typed state and label sums retain both endpoint interfaces. Atomic observations
are precisely interface tags and the system's declared observations. Behavioral
label classes give the higher-order relation its exact literal-label bridge;
raw process-bearing labels give a different, more discriminating instance.

The packed equations are literal equality: the indexed system supplies no
authored equation relation. Completeness uses explicit finite successor covers,
either by the equations or by the already established behavioral relation.
Behavioral covers do not install behavioral equivalence as authored equations.
This constructs neither minimal reflective contexts nor executable label
classification, and is not a blanket source context-HML adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HigherOrderHML

open HigherOrderBisimulation

universe uInterface uState uLabel uAtom

variable {Interface : Type uInterface} {State : Interface → Type uState}
  {Skeleton : Interface → Interface → Type uLabel}

abbrev PackedState (State : Interface → Type uState) := Sigma State
abbrev PackedLabel (Skeleton : Interface → Interface → Type uLabel) :=
  Σ source, Σ target, Skeleton source target

variable (system : HigherOrderBisimulation.System (literalVocabulary Skeleton) State)

/-- The actual indexed transition, with neither endpoint interface erased. -/
inductive Act : PackedLabel Skeleton → PackedState State → PackedState State → Prop
  | mk {source target : Interface} (shape : Skeleton source target)
      (agent : State source) (next : State target)
      (step : system.act (literalLabel shape) agent next) :
      Act ⟨source, target, shape⟩ ⟨source, agent⟩ ⟨target, next⟩

/-- No new state-equality atoms: only tags and the existing declared atoms. -/
def observes (atom : Interface ⊕ (Σ interface, system.Atom interface))
    (term : PackedState State) : Prop :=
  match atom with
  | .inl interface => term.1 = interface
  | .inr ⟨interface, atom⟩ =>
      ∃ state : State interface, term = ⟨interface, state⟩ ∧ system.observes atom state

/-- Forget only the label on the actual packed steps. There are no added equations. -/
def packedGSLT : GSLT where
  Term := PackedState State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ label, Act system label source target
  rewrites_resp_left := by
    rintro source _ target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target _ step rfl
    exact step

/-- One packing construction, reused for literal labels and behavioral label classes. -/
def packedSystem : HennessyMilner.System (packedGSLT system) where
  Atom := Interface ⊕ (Σ interface, system.Atom interface)
  observes := observes system
  observes_resp := by
    rintro atom left _ rfl
    exact Iff.rfl
  Label := PackedLabel Skeleton
  act := Act system
  act_resp_left := by
    rintro label left _ target rfl step
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    rintro label source target _ step rfl
    exact step

theorem literalLabel_eta {source target : Interface}
    (label : Label (literalVocabulary Skeleton) State source target) :
    literalLabel label.skeleton = label := by
  cases label with
  | mk shape payload =>
      simp only [literalLabel]
      congr 1
      funext slot
      nomatch slot

theorem act_target_iff {source target : Interface} (shape : Skeleton source target)
    (agent : State source) (next : PackedState State) :
    Act system ⟨source, target, shape⟩ ⟨source, agent⟩ next ↔
      ∃ state : State target, next = ⟨target, state⟩ ∧
        system.act (literalLabel shape) agent state := by
  constructor
  · intro step
    cases step with
    | mk shape agent next step => exact ⟨next, rfl, step⟩
  · rintro ⟨state, rfl, step⟩
    exact .mk shape agent state step

theorem observes_atom_iff {interface : Interface} (atom : system.Atom interface)
    (state : State interface) :
    observes system (.inr ⟨interface, atom⟩) ⟨interface, state⟩ ↔
      system.observes atom state := by
  constructor
  · rintro ⟨other, same, observed⟩
    have hState : state = other := eq_of_heq (Sigma.mk.inj same).2
    exact hState.symm ▸ observed
  · intro observed
    exact ⟨state, rfl, observed⟩

/-- Packing a candidate does not invent cross-interface pairs. -/
inductive Related (relation : RelationFamily State) :
    PackedState State → PackedState State → Prop
  | mk {interface : Interface} {left right : State interface}
      (related : relation interface left right) : Related relation ⟨interface, left⟩ ⟨interface, right⟩

theorem packed_isBisimulation :
    (packedSystem system).IsBisimulation (Related system.Bisimilar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label next step
    cases related with
    | @mk interface left right related =>
      cases step with
      | mk shape agent next step =>
        obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
          (system.bisimilar_unfold.mp related).1 (literalLabel shape) next step
        have same := (relates_literal_iff system.Bisimilar _ _).mp labels
        change shape = matchedLabel.skeleton at same
        have actual : system.act (literalLabel shape) right matched := by
          have sameLabel : literalLabel shape = matchedLabel :=
            (congrArg (fun shape => literalLabel (State := State) shape) same).trans
              (literalLabel_eta matchedLabel)
          exact sameLabel.symm ▸ matchedStep
        exact ⟨_, Act.mk shape _ matched actual, Related.mk successors⟩
  · intro left right related label next step
    cases related with
    | @mk interface left right related =>
      cases step with
      | mk shape agent next step =>
        obtain ⟨matchedLabel, matched, matchedStep, labels, successors⟩ :=
          (system.bisimilar_unfold.mp related).2.1 (literalLabel shape) next step
        have same := (relates_literal_iff system.Bisimilar _ _).mp labels
        change matchedLabel.skeleton = shape at same
        have actual : system.act (literalLabel shape) left matched := by
          have sameLabel : literalLabel shape = matchedLabel :=
            (congrArg (fun shape => literalLabel (State := State) shape) same.symm).trans
              (literalLabel_eta matchedLabel)
          exact sameLabel.symm ▸ matchedStep
        exact ⟨_, Act.mk shape _ matched actual, Related.mk successors⟩
  · intro left right related atom
    cases related with
    | @mk interface left right related =>
      cases atom with
      | inl tag => exact Iff.rfl
      | inr indexedAtom =>
        obtain ⟨observedInterface, atom⟩ := indexedAtom
        constructor
        · rintro ⟨observed, same, observedAtom⟩
          have interfaceEq := (Sigma.mk.inj same).1
          subst observedInterface
          have hState : left = observed := eq_of_heq (Sigma.mk.inj same).2
          exact ⟨right, rfl, (system.observes_iff related atom).mp (hState.symm ▸ observedAtom)⟩
        · rintro ⟨observed, same, observedAtom⟩
          have interfaceEq := (Sigma.mk.inj same).1
          subst observedInterface
          have hState : right = observed := eq_of_heq (Sigma.mk.inj same).2
          exact ⟨left, rfl, (system.observes_iff related atom).mpr (hState.symm ▸ observedAtom)⟩

theorem packed_bisimilar_of_indexed {interface : Interface} {left right : State interface}
    (related : system.Bisimilar interface left right) :
    (packedSystem system).Bisimilar ⟨interface, left⟩ ⟨interface, right⟩ :=
  ⟨Related system.Bisimilar, packed_isBisimulation system, Related.mk related⟩

theorem indexed_bisimilar_of_packed {interface : Interface} {left right : State interface}
    (related : (packedSystem system).Bisimilar ⟨interface, left⟩ ⟨interface, right⟩) :
    system.Bisimilar interface left right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  apply system.coinduction
    (relation := fun interface left right => relation ⟨interface, left⟩ ⟨interface, right⟩)
    ?_ interface left right related
  intro current first second pair
  refine ⟨?_, ?_, ?_⟩
  · intro nextInterface label next step
    have packedStep : Act system ⟨current, nextInterface, label.skeleton⟩
        ⟨current, first⟩ ⟨nextInterface, next⟩ :=
      .mk label.skeleton first next (literalLabel_eta label ▸ step)
    obtain ⟨matched, matchedStep, successors⟩ := bisimulation.1 pair _ packedStep
    obtain ⟨state, rfl, actual⟩ := (act_target_iff system _ second matched).mp matchedStep
    exact ⟨literalLabel label.skeleton, state, actual,
      (relates_literal_iff _ _ _).mpr rfl, successors⟩
  · intro nextInterface label next step
    have packedStep : Act system ⟨current, nextInterface, label.skeleton⟩
        ⟨current, second⟩ ⟨nextInterface, next⟩ :=
      .mk label.skeleton second next (literalLabel_eta label ▸ step)
    obtain ⟨matched, matchedStep, successors⟩ := bisimulation.2.1 pair _ packedStep
    obtain ⟨state, rfl, actual⟩ := (act_target_iff system _ first matched).mp matchedStep
    exact ⟨literalLabel label.skeleton, state, actual,
      (relates_literal_iff _ _ _).mpr rfl, successors⟩
  · intro atom
    exact (observes_atom_iff system atom first).symm.trans
      ((bisimulation.2.2 pair (.inr ⟨current, atom⟩)).trans
        (observes_atom_iff system atom second))

theorem packed_bisimilar_iff {interface : Interface} (left right : State interface) :
    (packedSystem system).Bisimilar ⟨interface, left⟩ ⟨interface, right⟩ ↔
      system.Bisimilar interface left right :=
  ⟨indexed_bisimilar_of_packed system, packed_bisimilar_of_indexed system⟩

/-- Different tags are distinguishable without a state-equality oracle. -/
theorem not_packed_bisimilar_of_interface_ne {leftInterface rightInterface : Interface}
    (different : leftInterface ≠ rightInterface) (left : State leftInterface)
    (right : State rightInterface) :
    ¬(packedSystem system).Bisimilar ⟨leftInterface, left⟩ ⟨rightInterface, right⟩ := by
  intro related
  have observations := (packedSystem system).logicallyEquivalent_of_bisimilar related
  have same := (observations (.atom (.inl leftInterface))).mp rfl
  exact different same.symm

variable {vocabulary : Vocabulary.{uInterface, uLabel} Interface}
  (higherOrder : HigherOrderBisimulation.System vocabulary State)

def classSystem := packedSystem higherOrder.classLabelSystem

/-- Exact higher-order relation, using the already constructed behavioral label classes. -/
theorem class_bisimilar_iff {interface : Interface} (left right : State interface) :
    (classSystem higherOrder).Bisimilar ⟨interface, left⟩ ⟨interface, right⟩ ↔
      higherOrder.Bisimilar interface left right :=
  (packed_bisimilar_iff higherOrder.classLabelSystem left right).trans
    (higherOrder.bisimilar_classLabel_iff left right)

theorem class_logicallyEquivalent_of_bisimilar {interface : Interface}
    {left right : State interface} (related : higherOrder.Bisimilar interface left right) :
    (classSystem higherOrder).LogicallyEquivalent ⟨interface, left⟩ ⟨interface, right⟩ :=
  (classSystem higherOrder).logicallyEquivalent_of_bisimilar
    ((class_bisimilar_iff higherOrder left right).mpr related)

/-- Behavioral successor covers suffice for adequacy without replacing the
packed system's literal equations by behavioral equality. -/
theorem class_logicallyEquivalent_iff_of_behavioral_cover
    (finite : (classSystem higherOrder).ImageFiniteBisimilar)
    {interface : Interface} (left right : State interface) :
    (classSystem higherOrder).LogicallyEquivalent ⟨interface, left⟩ ⟨interface, right⟩ ↔
      higherOrder.Bisimilar interface left right :=
  ((classSystem higherOrder).logicallyEquivalent_iff_bisimilar_of_imageFiniteBisimilar
    finite _ _).trans (class_bisimilar_iff higherOrder left right)

/-- Existing HML completeness under actual packed image-finiteness modulo literal equations. -/
theorem class_logicallyEquivalent_iff (finite : (classSystem higherOrder).ImageFiniteModulo)
    {interface : Interface} (left right : State interface) :
    (classSystem higherOrder).LogicallyEquivalent ⟨interface, left⟩ ⟨interface, right⟩ ↔
      higherOrder.Bisimilar interface left right :=
  class_logicallyEquivalent_iff_of_behavioral_cover higherOrder
    ((classSystem higherOrder).imageFiniteBisimilar_of_imageFiniteModulo finite) left right

end Mettapedia.GSLT.HigherOrderHML
