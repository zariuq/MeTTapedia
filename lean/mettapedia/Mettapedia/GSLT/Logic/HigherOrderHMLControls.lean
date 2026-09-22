import Mettapedia.GSLT.Logic.HigherOrderHML

/-!
# Typed and process-bearing controls for the HML packing bridge

The mixed-interface instance has genuinely different Bool and Nat carriers.
The literal-label diamond separates behaviorally related process payloads,
whereas the class-label instance uses the proved higher-order relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HigherOrderHMLControls

open HigherOrderBisimulation HigherOrderHML

private abbrev typed := TypedPayloadControls.system

theorem mixed_interface_false_computes_zero :
    (classSystem typed).act
      ⟨false, true, typed.toLabelClass (TypedPayloadControls.pairLabel false 0)⟩
      ⟨false, false⟩ ⟨true, 0⟩ :=
  Act.mk _ _ _ ⟨_, rfl, TypedPayloadControls.false_computes_zero⟩

theorem mixed_interface_true_computes_one :
    (classSystem typed).act
      ⟨false, true, typed.toLabelClass (TypedPayloadControls.pairLabel true 1)⟩
      ⟨false, true⟩ ⟨true, 1⟩ :=
  Act.mk _ _ _ ⟨_, rfl, TypedPayloadControls.true_computes_one⟩

theorem distinct_interfaces_are_not_bisimilar :
    ¬(classSystem typed).Bisimilar ⟨false, false⟩ ⟨true, 0⟩ :=
  not_packed_bisimilar_of_interface_ne typed.classLabelSystem Bool.false_ne_true false 0

theorem mixed_successors_are_distinguished :
    ¬(classSystem typed).Bisimilar ⟨true, 0⟩ ⟨true, 1⟩ := by
  intro related
  have original := (class_bisimilar_iff typed _ _).mp related
  have observed := typed.observes_iff original (0 : Nat)
  exact Nat.zero_ne_one (observed.mp rfl)

theorem mixed_successor_formula_separates :
    (classSystem typed).sat (.atom (.inr ⟨true, (0 : Nat)⟩)) ⟨true, 0⟩ ∧
      ¬(classSystem typed).sat (.atom (.inr ⟨true, (0 : Nat)⟩)) ⟨true, 1⟩ := by
  constructor
  · exact (observes_atom_iff typed.classLabelSystem (interface := true) (0 : Nat) 0).mpr rfl
  · intro observed
    exact Nat.zero_ne_one
      ((observes_atom_iff typed.classLabelSystem (interface := true) (0 : Nat) 1).mp observed)

private abbrev processes := PayloadControls.system

theorem nested_class_payloads_are_bisimilar :
    (classSystem processes).Bisimilar
      ⟨(), .send false (.send true (.halt false))⟩
      ⟨(), .send false (.send true (.halt true))⟩ :=
  (class_bisimilar_iff processes _ _).mpr PayloadControls.nested_payloads_are_bisimilar

theorem nested_class_payloads_satisfy_same_formulas :
    (classSystem processes).LogicallyEquivalent
      ⟨(), .send false (.send true (.halt false))⟩
      ⟨(), .send false (.send true (.halt true))⟩ :=
  class_logicallyEquivalent_of_bisimilar processes PayloadControls.nested_payloads_are_bisimilar

theorem distinct_channels_are_not_packed_bisimilar :
    ¬(classSystem processes).Bisimilar
      ⟨(), .send false (.halt false)⟩ ⟨(), .send true (.halt false)⟩ := by
  intro related
  exact PayloadControls.different_channels_are_distinguished
    ((class_bisimilar_iff processes _ _).mp related)

theorem observed_payloads_are_not_packed_bisimilar :
    ¬(classSystem processes).Bisimilar
      ⟨(), .send false .alarm⟩ ⟨(), .send false (.halt false)⟩ := by
  intro related
  exact PayloadControls.observed_payloads_are_distinguished
    ((class_bisimilar_iff processes _ _).mp related)

private def rawPayloadDiamond :
    HennessyMilner.Formula (packedSystem processes.literalSystem).Atom
      (packedSystem processes.literalSystem).Label :=
  .dia ⟨(), (), PayloadControls.sendLabel false (.halt false)⟩ .top

/-- A raw literal-label modality really separates the two states; this is not
merely a failed literal-bisimulation proof. -/
theorem literal_payload_diamond_separates :
    (packedSystem processes.literalSystem).sat rawPayloadDiamond
      ⟨(), .send false (.halt false)⟩ ∧
      ¬(packedSystem processes.literalSystem).sat rawPayloadDiamond
        ⟨(), .send false (.halt true)⟩ := by
  constructor
  · exact ⟨⟨(), .halt false⟩, Act.mk _ _ _ ⟨rfl, rfl⟩, trivial⟩
  · rintro ⟨target, step, _⟩
    obtain ⟨state, _, actual⟩ :=
      (act_target_iff processes.literalSystem _ _ target).mp step
    change PayloadControls.Process.send false (.halt true) = .send false (.halt false) ∧
      state = .halt false at actual
    cases actual.1

/-- Source higher-order agreement cannot be silently replaced by raw literal HML. -/
theorem higher_order_related_but_raw_HML_inequivalent :
    processes.Bisimilar () (.send false (.halt false)) (.send false (.halt true)) ∧
      ¬(packedSystem processes.literalSystem).LogicallyEquivalent
        ⟨(), .send false (.halt false)⟩ ⟨(), .send false (.halt true)⟩ := by
  refine ⟨PayloadControls.bisimilar_of_code_eq rfl, ?_⟩
  intro equivalent
  exact literal_payload_diamond_separates.2
    ((equivalent rawPayloadDiamond).mp literal_payload_diamond_separates.1)

/-- The actual class-labelled model satisfies the completeness hypothesis:
every matched step has its single literal terminal successor. -/
theorem process_class_system_image_finite : (classSystem processes).ImageFiniteModulo := by
  intro label term
  obtain ⟨source, target, shape⟩ := label
  cases source
  cases target
  obtain ⟨interface, agent⟩ := term
  cases interface
  refine ⟨{⟨(), PayloadControls.Process.halt false⟩}, Set.finite_singleton _, ?_⟩
  intro next step
  obtain ⟨state, hNext, actual⟩ :=
    (act_target_iff processes.classLabelSystem shape agent next).mp step
  obtain ⟨representative, _, hActual⟩ := actual
  have hState : state = PayloadControls.Process.halt false := hActual.2
  exact ⟨_, Set.mem_singleton _, hNext.trans
    (congrArg (fun value => (⟨(), value⟩ : PackedState PayloadControls.States)) hState)⟩

theorem actual_class_system_adequacy (left right : PayloadControls.Process) :
    (classSystem processes).LogicallyEquivalent ⟨(), left⟩ ⟨(), right⟩ ↔
      processes.Bisimilar () left right :=
  class_logicallyEquivalent_iff processes process_class_system_image_finite left right

end Mettapedia.GSLT.HigherOrderHMLControls
