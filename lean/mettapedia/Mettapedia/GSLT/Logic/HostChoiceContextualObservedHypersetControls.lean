import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetContinuations
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# Growing observed execution, member and continuation controls

An actual infinite execution family gains new source occurrences at every
stage. Its old state initially has no present child, then gains a cyclic
child and a terminal child. Their actual set readings give a changing
member family and an argument-dependent body. Declared result tags retain
terminal distinctions erased by the unlabelled final set readout.

A shrinking declared atom has no natural membership encoding. These
controls concern the actual optional set interpretation over the same
site, with its original small continuation and member fibres.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualHypersetModel HostChoiceContextualHypersetFamilyClosure
open HostChoiceContextualObservedHypersetTriangle
open PowerClassPresheafDescent.Controls

abbrev raw := growingSource
abbrev worlds := ContextualObservedCoalgebraControls.worlds
abbrev arrows := ContextualObservedCoalgebraControls.arrows
abbrev atomCoding := ContextualObservedCoalgebraControls.naturalAtoms

def admitted (parent : Nat) (child : Nat) : Prop :=
  (parent = 1 ∧ child = 1) ∨ (parent = 0 ∧ (child = 1 ∨ child = 2 ∨ child = 3))

def dynamics : NaturalHom raw (CoveredFuturePowerFamilies.family raw) where
  app _ argument := CoveredFuturePowerFamilies.ofFull {
    holds := fun future => admitted argument.1.val future.2.1.val
    closed := by
      intro first second step available
      have indexes := congrArg (fun value : raw.obj second.1.1 => value.1.val) step.2
      change first.2.1.val = second.2.1.val at indexes
      exact indexes ▸ available }
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

def atoms (reading : Nat) (state : ContextualCoalgebraLabelledGraph.State raw) : Prop := reading = state.2.1.val

abbrev classes := observedClasses dynamics atoms worlds arrows atomCoding
abbrev parameters := structured dynamics atoms worlds arrows atomCoding
noncomputable abbrev projection := structuredReadout dynamics atoms worlds arrows atomCoding
abbrev parent := materialProjection dynamics atoms worlds arrows atomCoding
noncomputable abbrev members := HostChoiceContextualObservedHypersetTypes.members dynamics atoms worlds arrows atomCoding

noncomputable def initial : parameters.Elements := ⟨world 0, projection.app (world 0) (stageValue 0 0 (by omega) false)⟩
def arrow (stage : Nat) : world 0 ⟶ world stage := (homOfLE (Nat.zero_le stage)).op.op
noncomputable def later (stage : Nat) : parameters.Elements :=
  ⟨world stage, parameters.map (arrow stage) initial.2⟩
noncomputable def initialToLater (stage : Nat) : initial ⟶ later stage := CategoryOfElements.homMk _ _ (arrow stage) rfl

theorem later_parent (stage : Nat) : parent.app (world stage) (later stage).2 =
    (setReadout dynamics).app (world stage) (stageValue stage 0 (by omega) false) := by
  have triangle := congrArg
    (fun map : NaturalHom raw sets => map.app (world 0) (stageValue 0 0 (by omega) false))
    (structured_material_square dynamics atoms worlds arrows atomCoding)
  change sets.map (arrow stage) (parent.app (world 0) initial.2) = _
  exact (congrArg (sets.map (arrow stage)) triangle).trans
    ((setReadout dynamics).naturality (arrow stage) (stageValue 0 0 (by omega) false))

noncomputable def terminalValue : sets.obj (world 2) := (setReadout dynamics).app (world 2) (stageValue 2 2 (by omega) false)
noncomputable def cyclicValue : sets.obj (world 2) := (setReadout dynamics).app (world 2) (stageValue 2 1 (by omega) false)

theorem terminal_has_no_member (child : sets.obj (world 2)) : ¬ Member (world 2) child terminalValue := by
  intro available
  obtain ⟨original, _reads, admitted⟩ :=
    (setReadout_future dynamics (world 2) (world 2) (𝟙 _) (stageValue 2 2 (by omega) false) child).mp available
  change (2 = 1 ∧ original.1.val = 1) ∨
    (2 = 0 ∧ (original.1.val = 1 ∨ original.1.val = 2 ∨ original.1.val = 3)) at admitted
  rcases admitted with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

theorem cyclic_is_own_member : Member (world 2) cyclicValue cyclicValue :=
  (setReadout_future dynamics (world 2) (world 2) (𝟙 _) (stageValue 2 1 (by omega) false) cyclicValue).mpr
    ⟨stageValue 2 1 (by omega) false, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem terminal_cyclic_distinct : terminalValue ≠ cyclicValue := by
  intro same
  exact terminal_has_no_member cyclicValue (same ▸ cyclic_is_own_member)

theorem terminal_later_member : Member (world 2) terminalValue (parent.app (world 2) (later 2).2) := by
  rw [later_parent]
  exact (setReadout_future dynamics (world 2) (world 2) (𝟙 _) (stageValue 2 0 (by omega) false) terminalValue).mpr
    ⟨stageValue 2 2 (by omega) false, rfl, Or.inr ⟨rfl, Or.inr (Or.inl rfl)⟩⟩

theorem cyclic_later_member : Member (world 2) cyclicValue (parent.app (world 2) (later 2).2) := by
  rw [later_parent]
  exact (setReadout_future dynamics (world 2) (world 2) (𝟙 _) (stageValue 2 0 (by omega) false) cyclicValue).mpr
    ⟨stageValue 2 1 (by omega) false, rfl, Or.inr ⟨rfl, Or.inl rfl⟩⟩

theorem initial_member_family_empty : ¬ Nonempty (members.obj initial) := by
  rintro ⟨code⟩
  have available := (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding initial code).property
  have triangle := congrArg
    (fun map : NaturalHom raw sets => map.app (world 0) (stageValue 0 0 (by omega) false))
    (structured_material_square dynamics atoms worlds arrows atomCoding)
  change parent.app (world 0) initial.2 = (setReadout dynamics).app (world 0) (stageValue 0 0 (by omega) false) at triangle
  change Member (world 0) _ (parent.app (world 0) initial.2) at available
  have currentAvailable := triangle ▸ available
  obtain ⟨original, _reads, action⟩ :=
    (setReadout_future dynamics (world 0) (world 0) (𝟙 _) (stageValue 0 0 (by omega) false) _).mp currentAvailable
  have bound := original.1.isLt
  change original.1.val < 1 at bound
  change (0 = 1 ∧ original.1.val = 1) ∨
    (0 = 0 ∧ (original.1.val = 1 ∨ original.1.val = 2 ∨ original.1.val = 3)) at action
  rcases action with ⟨impossible, _⟩ | ⟨_, alternatives⟩
  · omega
  · rcases alternatives with first | second | third <;> omega

noncomputable def terminalCode : members.obj (later 2) :=
  (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2)).symm
    ⟨terminalValue, terminal_later_member⟩

noncomputable def cyclicCode : members.obj (later 2) :=
  (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2)).symm
    ⟨cyclicValue, cyclic_later_member⟩

theorem terminalCode_value : (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
    (later 2) terminalCode).val = terminalValue := congrArg Subtype.val
  ((HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2)).apply_symm_apply _)

theorem cyclicCode_value : (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
    (later 2) cyclicCode).val = cyclicValue := congrArg Subtype.val
  ((HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2)).apply_symm_apply _)

theorem actual_member_family_changes :
    ¬ Nonempty (members.obj initial) ∧ Nonempty (members.obj (later 2)) ∧ terminalCode ≠ cyclicCode := by
  refine ⟨initial_member_family_empty, ⟨terminalCode⟩, ?_⟩
  intro same
  exact terminal_cyclic_distinct (terminalCode_value.symm.trans
    ((congrArg (fun code => (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
      (later 2) code).val) same).trans cyclicCode_value))

noncomputable abbrev selectedBody := HostChoiceContextualObservedHypersetTypes.selectedBody dynamics atoms worlds arrows atomCoding
noncomputable abbrev selectedSet := HostChoiceContextualObservedHypersetTypes.selectedSet dynamics atoms worlds arrows atomCoding
noncomputable abbrev singletonBody := HostChoiceContextualObservedHypersetTypes.singletonBody dynamics atoms worlds arrows atomCoding
noncomputable abbrev singletonOfSelected := HostChoiceContextualObservedHypersetTypes.singletonOfSelected dynamics atoms worlds arrows atomCoding

theorem terminal_selected_body_empty : ¬ Nonempty (selectedBody.obj ⟨later 2, terminalCode⟩) := by
  rintro ⟨code⟩
  have available := (bodyDecoder parent selectedSet ⟨later 2, terminalCode⟩ code).property
  change Member (world 2) _
    (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2) terminalCode).val at available
  rw [terminalCode_value] at available
  exact terminal_has_no_member _ available

noncomputable def cyclicBodyMember : selectedBody.obj ⟨later 2, cyclicCode⟩ :=
  (bodyDecoder parent selectedSet ⟨later 2, cyclicCode⟩).symm ⟨cyclicValue, by
    change Member (world 2) cyclicValue
      (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding (later 2) cyclicCode).val
    rw [cyclicCode_value]
    exact cyclic_is_own_member⟩

theorem actual_body_depends_on_argument : ¬ Nonempty (selectedBody.obj ⟨later 2, terminalCode⟩) ∧
    Nonempty (selectedBody.obj ⟨later 2, cyclicCode⟩) :=
  ⟨terminal_selected_body_empty, ⟨cyclicBodyMember⟩⟩

noncomputable def cyclicEndpoints : (ContextualSmallFamilyIdentity.endpoints members).Elements :=
  ⟨world 2, ⟨⟨(later 2).2, cyclicCode⟩, cyclicCode⟩⟩

noncomputable def differentEndpoints : (ContextualSmallFamilyIdentity.endpoints members).Elements :=
  ⟨world 2, ⟨⟨(later 2).2, terminalCode⟩, cyclicCode⟩⟩

noncomputable def cyclicReflexivity : (ContextualSmallFamilyIdentity.witnessFamily members).obj cyclicEndpoints :=
  PresheafIdentityWitness.encode rfl

theorem actual_cyclic_identity_inhabited :
    Nonempty ((ContextualSmallFamilyIdentity.witnessFamily members).obj cyclicEndpoints) := ⟨cyclicReflexivity⟩

theorem actual_distinct_member_identity_empty :
    ¬ Nonempty ((ContextualSmallFamilyIdentity.witnessFamily members).obj differentEndpoints) := by
  rintro ⟨witness⟩
  exact actual_member_family_changes.2.2 (PresheafIdentityWitness.decode witness)

theorem initial_W_empty :
    ¬ Nonempty ((HostChoiceContextualObservedHypersetTypes.treeFamily dynamics atoms worlds arrows atomCoding).obj initial) := by
  rintro ⟨tree⟩
  have node := ContextualSmallFamilyWAlgebra.destructorValue members selectedBody initial tree
  exact initial_member_family_empty
    ⟨(ContextualSmallFamilyUniverse.evaluationEquiv members initial.1 initial.2) node.1⟩

theorem terminal_future_has_no_member {target : Stagesᵒᵖ} (step : world 2 ⟶ target)
    (child : sets.obj target) : ¬ Member target child (sets.map step terminalValue) := by
  intro available
  obtain ⟨original, _reads, action⟩ :=
    (setReadout_future dynamics (world 2) target step (stageValue 2 2 (by omega) false) child).mp
      ((futureMember_iff step child terminalValue).mpr available)
  change (2 = 1 ∧ original.1.val = 1) ∨
    (2 = 0 ∧ (original.1.val = 1 ∨ original.1.val = 2 ∨ original.1.val = 3)) at action
  rcases action with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

theorem memberValue_heq {first second : parameters.Elements} (same : first = second)
    (left : members.obj first) (right : members.obj second) (codes : HEq left right) :
    HEq (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding first left).val
      (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding second right).val := by
  cases same
  cases eq_of_heq codes
  rfl

set_option maxHeartbeats 1000000 in
theorem terminal_shape_no_future_positions
    (future : PowerClassPresheafBaseChange.Future.Objects (world 2))
    (step : ContextualSmallFamilyUniverse.root (world 2) ⟶ future) :
    ¬ Nonempty (ContextualWTypes.Position
      (ContextualSmallFamilyTypeFormers.futureDomain members (later 2))
      (ContextualSmallFamilyTypeFormers.futureBody members selectedBody (later 2))
      (ContextualSmallFamilyTypeFormers.currentArgument members (later 2) terminalCode).2 step) := by
  rintro ⟨position⟩
  let current := ContextualSmallFamilyTypeFormers.currentArgument members (later 2) terminalCode
  let next : (ContextualSmallFamilyTypeFormers.futureDomain members (later 2)).Elements :=
    ⟨future, (ContextualSmallFamilyTypeFormers.futureDomain members (later 2)).map step current.2⟩
  let elementStep : current ⟶ next := CategoryOfElements.homMk _ _ step rfl
  let actualStep := (ContextualSmallFamilyTypeFormers.futureArguments members (later 2)).map elementStep
  have currentValue := eq_of_heq
    (memberValue_heq (congrArg Sigma.fst
      (ContextualSmallFamilyTypeFormers.currentArgument_embedding members (later 2) terminalCode))
      current.2 terminalCode (ContextualSmallFamilyTypeFormers.currentArgument_value members (later 2) terminalCode))
  have moved := HostChoiceContextualObservedHypersetTypes.actualMembers_restriction
    dynamics atoms worlds arrows atomCoding actualStep.1 current.2
  have targetValue : (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
      ((ContextualSmallFamilyTypeFormers.futureArguments members (later 2)).obj next).1 next.2).val =
        sets.map step.1 terminalValue :=
    moved.symm.trans (congrArg (sets.map step.1) (currentValue.trans terminalCode_value))
  have available := (bodyDecoder parent selectedSet
    ((ContextualSmallFamilyTypeFormers.futureArguments members (later 2)).obj next) position).property
  change Member future.1 _ (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
    ((ContextualSmallFamilyTypeFormers.futureArguments members (later 2)).obj next).1 next.2).val at available
  rw [targetValue] at available
  exact terminal_future_has_no_member step.1 _ available

noncomputable def actualTerminalLeaf :
    (HostChoiceContextualObservedHypersetTypes.treeFamily dynamics atoms worlds arrows atomCoding).obj (later 2) :=
  ContextualWTypes.sup
    (ContextualSmallFamilyTypeFormers.futureDomain members (later 2))
    (ContextualSmallFamilyTypeFormers.futureBody members selectedBody (later 2))
    (ContextualSmallFamilyTypeFormers.currentArgument members (later 2) terminalCode).2
    (fun future step position => False.elim (terminal_shape_no_future_positions future step ⟨position⟩))
    (fun _ _ first _ position => False.elim (terminal_shape_no_future_positions _ first ⟨position⟩))

theorem actual_empty_position_W_leaf :
    Nonempty ((HostChoiceContextualObservedHypersetTypes.treeFamily dynamics atoms worlds arrows atomCoding).obj (later 2)) :=
  ⟨actualTerminalLeaf⟩

noncomputable def singletonChild (point : members.Elements) : singletonBody.obj point :=
  (bodyDecoder parent singletonOfSelected point).symm
    ⟨(HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding point.1 point.2).val,
      (member_singleton _ _ _).mpr rfl⟩

theorem singletonChild_value (point : members.Elements) :
    (bodyDecoder parent singletonOfSelected point (singletonChild point)).val =
      (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding point.1 point.2).val :=
  congrArg Subtype.val ((bodyDecoder parent singletonOfSelected point).apply_symm_apply _)

theorem singletonChild_natural {first second : members.Elements} (step : first ⟶ second) :
    singletonBody.map step (singletonChild first) = singletonChild second := by
  apply (bodyDecoder parent singletonOfSelected second).injective
  apply Subtype.ext
  exact (bodyDecoder_value_natural parent singletonOfSelected step (singletonChild first)).symm.trans
    ((congrArg (sets.map step.1.1) (singletonChild_value first)).trans
      ((HostChoiceContextualObservedHypersetTypes.actualMembers_restriction dynamics atoms worlds arrows atomCoding step.1 first.2).trans
        ((congrArg (fun code => (HostChoiceContextualObservedHypersetTypes.actualMembers dynamics atoms worlds arrows atomCoding
          second.1 code).val) step.2).trans (singletonChild_value second).symm)))

def unitParameters : parameters.Elements ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def singletonOperation : NatTrans (ContextualSmallFamilyTypeFormers.overArguments members unitParameters)
    singletonBody where
  app point := TypeCat.ofHom fun _ => singletonChild point
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro _
    exact (singletonChild_natural step).symm

noncomputable def singletonFunction (point : parameters.Elements) :
    ContextualSmallFamilyTypeFormers.ProductAt members singletonBody point :=
  (ContextualSmallFamilyTypeFormers.piCurry members singletonBody singletonOperation).app point PUnit.unit

set_option maxHeartbeats 1000000 in
theorem singletonFunction_beta (point : parameters.Elements) (argument : members.obj point) :
    ContextualSmallFamilyTypeFormers.evaluateValue members singletonBody point (singletonFunction point) argument =
      singletonChild ⟨point, argument⟩ :=
  HostChoiceContextualObservedHypersetTypes.smallLambda_beta (P := parameters) (consumer := unitParameters)
    members singletonBody singletonOperation point PUnit.unit argument

theorem singletonFunction_cyclic_material_beta :
    (bodyDecoder parent singletonOfSelected ⟨later 2, cyclicCode⟩
      (ContextualSmallFamilyTypeFormers.evaluateValue members singletonBody (later 2) (singletonFunction _) cyclicCode)).val =
      cyclicValue := by
  rw [singletonFunction_beta]
  exact (singletonChild_value _).trans cyclicCode_value

theorem initial_full_function_exists : Nonempty
    ((HostChoiceContextualObservedHypersetTypes.singletonProductFamily dynamics atoms worlds arrows atomCoding).obj initial) :=
  ⟨singletonFunction initial⟩

noncomputable def futureTerminalArgument : (ContextualSmallFamilyTypeFormers.futureDomain members initial).Elements :=
  ⟨⟨world 2, arrow 2⟩, terminalCode⟩

theorem selected_full_product_empty : ¬ Nonempty
    ((HostChoiceContextualObservedHypersetTypes.productFamily dynamics atoms worlds arrows atomCoding).obj initial) := by
  rintro ⟨function⟩
  exact terminal_selected_body_empty ⟨function.val futureTerminalArgument⟩

def unstableAtom (_atom : PUnit) (state : ContextualCoalgebraLabelledGraph.State raw) : Prop :=
  stageIndex state.1 = 0

def unitAtoms : ArgumentCoding PUnit where
  graph _ := AccessiblePointedGraph.empty
  injective _ _ _ := Subsingleton.elim _ _

theorem unstable_atom_not_stable : ¬ AtomStable unstableAtom PUnit.unit := by
  intro stable
  have impossible := stable (arrow 1) (stageValue 0 0 (by omega) false) rfl
  change 1 = 0 at impossible
  omega

theorem unstable_atom_has_no_natural_member_encoding :
    ¬ ∃ encoding : NaturalHom (observedClasses dynamics unstableAtom worlds arrows unitAtoms) sets,
      ∀ point argument, unstableAtom PUnit.unit ⟨point, argument⟩ ↔
        Member point (emptySet.val point)
          (encoding.app point ((observedProjection dynamics unstableAtom worlds arrows unitAtoms).app point argument)) :=
  fun encoding => unstable_atom_not_stable
    ((natural_atomic_membership_iff_stable dynamics unstableAtom worlds arrows unitAtoms PUnit.unit).mp encoding)

theorem result_atom_stable (reading : Nat) : AtomStable atoms reading := fun {_ _} _ _ holds => holds

theorem result_atom_has_natural_member_encoding (reading : Nat) :
    ∃ encoding : NaturalHom classes sets, ∀ point argument, atoms reading ⟨point, argument⟩ ↔
      Member point (emptySet.val point) (encoding.app point ((observedProjection dynamics atoms worlds arrows atomCoding).app point argument)) :=
  (natural_atomic_membership_iff_stable dynamics atoms worlds arrows atomCoding reading).mpr (result_atom_stable reading)

theorem terminal_bisimilar (stage : Nat) (left right : raw.obj (world stage))
    (first : 2 ≤ left.1.val) (second : 2 ≤ right.1.val) :
    ContextualCoalgebraBisimulation.Bisimilar dynamics (world stage) left right := by
  refine ⟨fun _ first second => 2 ≤ first.1.val ∧ 2 ≤ second.1.val, {
    stable := fun {_ _} _ {_ _} related => related
    forth := ?_
    back := ?_ }, first, second⟩
  · intro point first second related future child action
    change admitted first.1.val child.1.val at action
    rcases action with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega
  · intro point first second related future child action
    change admitted second.1.val child.1.val at action
    rcases action with ⟨impossible, _⟩ | ⟨impossible, _⟩ <;> omega

theorem same_terminal_set_different_observed_results :
    (setReadout dynamics).app (world 3) (stageValue 3 2 (by omega) false) =
      (setReadout dynamics).app (world 3) (stageValue 3 3 (by omega) false) ∧
    projection.app (world 3) (stageValue 3 2 (by omega) false) ≠
      projection.app (world 3) (stageValue 3 3 (by omega) false) := by
  refine ⟨(setReadout_kernel dynamics _ _ _).mpr (terminal_bisimilar 3 _ _ (by decide) (by decide)), ?_⟩
  intro same
  have related := (structured_kernel dynamics atoms worlds arrows atomCoding _ _ _).mp same
  have equality := ContextualObservedCoalgebra.observed_bisimilar_atoms dynamics atoms related 2
  have impossible : (2 : Nat) = 3 := equality.mp rfl
  omega

abbrev classProjection := observedProjection dynamics atoms worlds arrows atomCoding
def continuationPoint : classes.Elements := ⟨world 3, classProjection.app (world 3) (stageValue 3 0 (by omega) false)⟩

def terminalContinuation (reading : Fin 2) :
    HostChoiceContextualObservedHypersetContinuations.At dynamics atoms worlds arrows atomCoding continuationPoint :=
  ⟨classProjection.app (world 3) (stageValue 3 (2 + reading.val) (by omega) false), by
    apply (ContextualCoalgebraBisimulation.coalgebra_map_truth dynamics classProjection
      (observedCoalgebra dynamics atoms worlds arrows atomCoding)
      (ContextualObservedMaterialFamily.classObservation_square dynamics atoms worlds arrows atomCoding)
      (world 3) (stageValue 3 0 (by omega) false) ⟨world 3, 𝟙 _⟩ _).mpr
    refine ⟨stageValue 3 (2 + reading.val) (by omega) false, rfl, ?_⟩
    change admitted 0 (2 + reading.val)
    exact Or.inr ⟨rfl, Or.inr (by omega)⟩⟩

theorem terminal_continuations_distinct : terminalContinuation 0 ≠ terminalContinuation 1 := by
  intro same
  have classesSame := congrArg Subtype.val same
  have related := (ContextualObservedMaterialFamily.classObservation_eq_iff dynamics atoms worlds arrows atomCoding _ _ _).mp classesSame
  have equality := ContextualObservedCoalgebra.observed_bisimilar_atoms dynamics atoms related 2
  have impossible : (2 : Nat) = 3 := equality.mp rfl
  omega

theorem terminal_continuation_members_equal :
    (HostChoiceContextualObservedHypersetContinuations.toMember dynamics atoms worlds arrows atomCoding).app continuationPoint
        (terminalContinuation 0) =
      (HostChoiceContextualObservedHypersetContinuations.toMember dynamics atoms worlds arrows atomCoding).app continuationPoint
        (terminalContinuation 1) := by
  apply (memberDecoder _).injective
  apply Subtype.ext
  rw [HostChoiceContextualObservedHypersetContinuations.toMember_value,
    HostChoiceContextualObservedHypersetContinuations.toMember_value]
  have firstSquare := congrArg (fun map : NaturalHom raw sets => map.app (world 3) (stageValue 3 2 (by omega) false))
    (source_class_set_square dynamics atoms worlds arrows atomCoding)
  have secondSquare := congrArg (fun map : NaturalHom raw sets => map.app (world 3) (stageValue 3 3 (by omega) false))
    (source_class_set_square dynamics atoms worlds arrows atomCoding)
  exact firstSquare.trans (same_terminal_set_different_observed_results.1.trans secondSquare.symm)

theorem continuation_to_member_not_injective : ¬ Function.Injective
    ((HostChoiceContextualObservedHypersetContinuations.toMember dynamics atoms worlds arrows atomCoding).app continuationPoint) :=
  fun injective => terminal_continuations_distinct (injective terminal_continuation_members_equal)

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetControls
