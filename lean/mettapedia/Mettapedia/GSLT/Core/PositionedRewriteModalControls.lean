import Mettapedia.GSLT.Core.PositionedRewriteModal
import Mettapedia.CategoryTheory.ElementaryTypePredicateReadout

/-!
# Proper rely guards and a typed reduct without source conversion

The rule adds a positive rely input and the supplied focus, then takes one
successor step. The postcondition depends on the actual rely input. The
native modality admits exactly positive focuses. The complete supplied
event goes from two to three: its reduct satisfies the postcondition and
its source does not. A zero focus is rejected although a zero rely input
makes the conditional premise vacuous.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.PositionedRewriteModalControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory AuthoredClosedTheory PositionedRewriteModal
open ElementaryTypePredicateReadout

abbrev closed : LambdaTheory.{1,0} where
  Obj := Type
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance

def successor : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

def graph : Nat ⟶ Nat ⨯ Nat := prod.lift (𝟙 Nat) successor

instance graph_mono : Mono graph := by
  change Mono (prod.lift (𝟙 Nat) successor)
  infer_instance

abbrev theory : Theory.{1,0} where
  closed := closed
  program := Nat
  reduction := Subobject.mk graph

def before : Nat × Nat ⟶ Nat := TypeCat.ofHom fun pair => pair.1 + pair.2

def after : Nat × Nat ⟶ Nat := before ≫ successor

abbrev rule : Rule theory where
  parameters := Nat × Nat
  left := before
  right := after
  action := before ≫ (Subobject.underlyingIso graph).inv
  source := by
    change (before ≫ (Subobject.underlyingIso graph).inv) ≫
      ((Subobject.mk graph).arrow ≫ prod.fst) = before
    rw [← Category.assoc, Category.assoc before, Subobject.underlyingIso_arrow,
      graph, Category.assoc, prod.lift_fst, Category.comp_id]
  target := by
    change (before ≫ (Subobject.underlyingIso graph).inv) ≫
      ((Subobject.mk graph).arrow ≫ prod.snd) = after
    rw [← Category.assoc, Category.assoc before, Subobject.underlyingIso_arrow,
      graph, Category.assoc, prod.lift_snd]
    rfl

def forget : Nat × Nat ⟶ Nat := TypeCat.ofHom Prod.snd

abbrev frame : Frame rule where
  assignments := Nat
  carrier := Nat
  assay := Nat × Nat
  forget := forget
  focus := 𝟙 Nat
  instantiate := 𝟙 (Nat × Nat)
  hole := forget
  plug := before
  square := IsPullback.of_id_snd
  source := Category.id_comp before

def relies : Subobject frame.assay := fromSet {pair | 0 < pair.1}

def postcondition : Subobject (frame.assay ⨯ theory.program) :=
  fromSet {supplied | (prod.snd : (Nat × Nat) ⨯ Nat ⟶ Nat) supplied > ((prod.fst : (Nat × Nat) ⨯ Nat ⟶ Nat × Nat) supplied).1 + 1}

abbrev classifier := TypeSubobjectClassifier.classifier

theorem relies_read (pair : Nat × Nat) : Contains relies pair ↔ 0 < pair.1 :=
  contains_fromSet _ pair

theorem postcondition_read (pair : Nat × Nat) :
    Contains (doctrine.reindex frame.outgoing postcondition) pair ↔ 0 < pair.2 := by
  rw [contains_reindex]
  unfold postcondition
  rw [contains_fromSet]
  have first := congrArg (fun arrow : Nat × Nat ⟶ Nat × Nat => arrow pair)
    (prod.lift_fst frame.instantiate rule.right)
  have second := congrArg (fun arrow : Nat × Nat ⟶ Nat => arrow pair)
    (prod.lift_snd frame.instantiate rule.right)
  change (prod.snd : (Nat × Nat) ⨯ Nat ⟶ Nat)
      ((frame.outgoing : Nat × Nat ⟶ (Nat × Nat) ⨯ Nat) pair) >
    ((prod.fst : (Nat × Nat) ⨯ Nat ⟶ Nat × Nat)
      ((frame.outgoing : Nat × Nat ⟶ (Nat × Nat) ⨯ Nat) pair)).1 + 1 ↔ _
  change (prod.fst : (Nat × Nat) ⨯ Nat ⟶ Nat × Nat)
      ((frame.outgoing : Nat × Nat ⟶ (Nat × Nat) ⨯ Nat) pair) = pair at first
  change (prod.snd : (Nat × Nat) ⨯ Nat ⟶ Nat)
      ((frame.outgoing : Nat × Nat ⟶ (Nat × Nat) ⨯ Nat) pair) = pair.1 + pair.2 + 1 at second
  rw [first, second]
  change pair.1 + pair.2 + 1 > pair.1 + 1 ↔ 0 < pair.2
  omega

theorem condition_read (pair : Nat × Nat) :
    Contains (frame.condition classifier relies postcondition) pair ↔
      (0 < pair.1 → 0 < pair.2) := by
  change Contains (doctrine.algebra (Nat × Nat) |>.himp
    (doctrine.reindex frame.instantiate relies)
    (doctrine.reindex frame.outgoing postcondition)) pair ↔ _
  rw [contains_implication, contains_reindex, relies_read, postcondition_read]
  rfl

theorem introduction_read (value : Nat) :
    Contains (frame.introductionScope classifier relies postcondition) value ↔ 0 < value := by
  change Contains (doctrine.forallAlong forget (frame.condition classifier relies postcondition)) value ↔ _
  rw [contains_forall]
  constructor
  · intro held
    exact (condition_read (1, value)).mp (held (1, value) rfl) (by omega)
  · intro held pair reading
    apply (condition_read pair).mpr
    intro _
    change pair.2 = value at reading
    exact reading.symm ▸ held

theorem modal_read (value : Nat) :
    Contains (frame.modal classifier relies postcondition) value ↔ 0 < value := by
  change Contains (doctrine.existsAlong (𝟙 Nat)
    (frame.introductionScope classifier relies postcondition)) value ↔ _
  rw [contains_exists]
  constructor
  · rintro ⟨supplied, held, reading⟩
    exact reading ▸ (introduction_read supplied).mp held
  · intro held
    exact ⟨value, (introduction_read value).mpr held, rfl⟩

def assignment : PUnit ⟶ frame.assignments := TypeCat.ofHom fun _ => 1

def assay : PUnit ⟶ frame.assay := TypeCat.ofHom fun _ => (1, 1)

theorem compatible : assignment ≫ frame.focus = assay ≫ frame.hole := rfl

theorem supplied_introduction : doctrine.reindex assignment
    (frame.introductionScope classifier relies postcondition) = ⊤ := by
  apply (eq_top_iff_contains _).mpr
  intro point
  apply (contains_reindex assignment _ point).mpr
  exact (introduction_read 1).mpr (by omega)

theorem supplied_rely : doctrine.reindex assay relies = ⊤ := by
  apply (eq_top_iff_contains _).mpr
  intro point
  apply (contains_reindex assay _ point).mpr
  exact (relies_read (1, 1)).mpr (by omega)

def event : PUnit ⟶ theory.Event := frame.step assignment assay compatible

theorem event_source : event ≫ theory.source = TypeCat.ofHom (fun _ : PUnit => 2) :=
  frame.step_source assignment assay compatible

theorem event_target : event ≫ theory.target = TypeCat.ofHom (fun _ : PUnit => 3) := by
  have exactInstance : frame.suppliedInstance assignment assay compatible = assay :=
    (Category.comp_id _).symm.trans (frame.suppliedInstance_assay assignment assay compatible)
  exact (frame.step_target assignment assay compatible).trans
    (congrArg (fun arrow => arrow ≫ rule.right) exactInstance)

theorem exact_reduct_has_postcondition : doctrine.reindex
    (prod.lift assay (event ≫ theory.target)) postcondition = ⊤ :=
  frame.supplied_reduct classifier relies postcondition assignment assay compatible
    supplied_introduction supplied_rely

theorem actual_step_is_not_conversion : event ≫ theory.source ≠ event ≫ theory.target := by
  intro same
  have reading := congrArg (fun arrow : PUnit ⟶ Nat => arrow PUnit.unit) same
  rw [event_source, event_target] at reading
  change (2 : Nat) = 3 at reading
  omega

theorem source_does_not_have_the_reduct_postcondition :
    doctrine.reindex (prod.lift assay (event ≫ theory.source)) postcondition ≠ ⊤ := by
  intro admitted
  have member := (eq_top_iff_contains _).mp admitted PUnit.unit
  have typed := (contains_reindex _ _ _).mp member
  have condition := (contains_fromSet _ _).mp typed
  have first := congrArg (fun arrow : PUnit ⟶ Nat × Nat => arrow PUnit.unit)
    (prod.lift_fst assay (event ≫ theory.source))
  have second := congrArg (fun arrow : PUnit ⟶ Nat => arrow PUnit.unit)
    (prod.lift_snd assay (event ≫ theory.source))
  change (prod.fst : (Nat × Nat) ⨯ Nat ⟶ Nat × Nat)
    ((prod.lift assay (event ≫ theory.source)) PUnit.unit) = (1, 1) at first
  change (prod.snd : (Nat × Nat) ⨯ Nat ⟶ Nat)
    ((prod.lift assay (event ≫ theory.source)) PUnit.unit) =
      (event ≫ theory.source) PUnit.unit at second
  change (prod.snd : (Nat × Nat) ⨯ Nat ⟶ Nat) ((prod.lift assay (event ≫ theory.source)) PUnit.unit) >
    ((prod.fst : (Nat × Nat) ⨯ Nat ⟶ Nat × Nat) ((prod.lift assay (event ≫ theory.source)) PUnit.unit)).1 + 1 at condition
  rw [first, second, event_source] at condition
  change (2 : Nat) > 1 + 1 at condition
  omega

theorem zero_focus_is_rejected : ¬ Contains (frame.modal classifier relies postcondition) 0 := by
  rw [modal_read]
  exact Nat.lt_irrefl 0

theorem a_disabled_rely_input_is_insufficient :
    Contains (frame.condition classifier relies postcondition) (0, 0) ∧
      ¬ Contains (frame.introductionScope classifier relies postcondition) 0 := by
  constructor
  · exact (condition_read (0, 0)).mpr (fun held => (Nat.lt_irrefl 0 held).elim)
  · rw [introduction_read]
    exact Nat.lt_irrefl 0

def varyingAssignment : Nat ⟶ frame.assignments := TypeCat.ofHom Nat.succ

def varyingAssay : Nat ⟶ frame.assay := TypeCat.ofHom fun n => (n + 1, n + 1)

theorem varying_match : varyingAssignment ≫ frame.focus = varyingAssay ≫ frame.hole := rfl

def varyingEvent : Nat ⟶ theory.Event := frame.step varyingAssignment varyingAssay varying_match

theorem varying_target_read : varyingEvent ≫ theory.target =
    TypeCat.ofHom (fun n : Nat => 2 * n + 3) := by
  have wholeInstance : frame.suppliedInstance varyingAssignment varyingAssay varying_match = varyingAssay :=
    (Category.comp_id _).symm.trans
      (frame.suppliedInstance_assay varyingAssignment varyingAssay varying_match)
  refine (frame.step_target varyingAssignment varyingAssay varying_match).trans
    ((congrArg (fun arrow => arrow ≫ rule.right) wholeInstance).trans ?_)
  ext n
  change n + 1 + (n + 1) + 1 = 2 * n + 3
  omega

theorem complete_event_is_not_a_constant :
    (varyingEvent ≫ theory.target) 0 = 3 ∧
      (varyingEvent ≫ theory.target) 4 = 11 := by
  rw [varying_target_read]
  exact ⟨rfl, rfl⟩

def futureMap : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem future_context_retains_the_exact_event :
    frame.step (futureMap ≫ varyingAssignment) (futureMap ≫ varyingAssay)
      (frame.precomposed_match varyingAssignment varyingAssay varying_match futureMap) =
    futureMap ≫ varyingEvent :=
  frame.step_precompose varyingAssignment varyingAssay varying_match futureMap

theorem future_context_changes_the_actual_reduct :
    ((futureMap ≫ varyingEvent) ≫ theory.target) 0 = 5 := by
  rw [Category.assoc, varying_target_read]
  rfl

end Mettapedia.GSLT.Core.PositionedRewriteModalControls
