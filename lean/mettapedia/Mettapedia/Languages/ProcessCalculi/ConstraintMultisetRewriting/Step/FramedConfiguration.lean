import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FrameFamilies

/-!
# Joint configurations over finite frame families

Configurations from unrelated original frames coexist in one family frame.
The original equation-store and occurrence representations are retained.
Inclusions change only the term-validity witness: frame names and term data
remain intact. Units and associativity hold literally; symmetry preserves
solutions through the declared frame reindexing.

This is the spatial configuration view. Complete native control states and
event identities remain in their respective families and runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence

universe uO uT uH uOcc

structure FramedConfiguration {Obj : Type uO} (Tm : Obj → Type uT) (O : Type uOcc) where
  frames : List Obj
  content : Configuration (Frames.Families.Term Tm frames) O

namespace FramedConfiguration

variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc}

def eraseEquation {family : List Obj}
    (equation : Equation (Frames.Families.Term Tm family)) : Equation ((a : Obj) × Tm a) :=
  (equation.1.val, equation.2.val)

theorem eraseEquation_injective {family : List Obj} :
    Function.Injective (eraseEquation (Tm := Tm) (family := family)) := by
  intro left right same
  exact Prod.ext (Subtype.ext (congrArg Prod.fst same)) (Subtype.ext (congrArg Prod.snd same))

def eraseConfiguration {family : List Obj}
    (state : Configuration (Frames.Families.Term Tm family) O) : Configuration ((a : Obj) × Tm a) O :=
  ⟨state.equations.map eraseEquation, state.present⟩

theorem eraseConfiguration_injective {family : List Obj} :
    Function.Injective (eraseConfiguration (Tm := Tm) (O := O) (family := family)) := by
  rintro ⟨leftKnowledge, leftPresent⟩ ⟨rightKnowledge, rightPresent⟩ same
  have knowledge := congrArg Configuration.equations same
  have occurrences := congrArg Configuration.present same
  change leftKnowledge.map eraseEquation = rightKnowledge.map eraseEquation at knowledge
  have original := (List.map_injective_iff.mpr eraseEquation_injective) knowledge
  cases original
  cases occurrences
  rfl

def erase (state : FramedConfiguration Tm O) : Configuration ((a : Obj) × Tm a) O :=
  eraseConfiguration state.content

theorem ext {left right : FramedConfiguration Tm O} (frames : left.frames = right.frames)
    (contents : erase left = erase right) : left = right := by
  rcases left with ⟨leftFrames, leftContent⟩
  rcases right with ⟨rightFrames, rightContent⟩
  change leftFrames = rightFrames at frames
  cases frames
  change eraseConfiguration leftContent = eraseConfiguration rightContent at contents
  have same := eraseConfiguration_injective contents
  cases same
  rfl

def widenTerm {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (term : Frames.Families.Term Tm source) : Frames.Families.Term Tm target :=
  ⟨term.val, included term.val.1 term.property⟩

def widen {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (state : Configuration (Frames.Families.Term Tm source) O) :
    Configuration (Frames.Families.Term Tm target) O :=
  ⟨state.equations.map (fun equation => (widenTerm included equation.1, widenTerm included equation.2)),
    state.present⟩

theorem erase_widen {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (state : Configuration (Frames.Families.Term Tm source) O) :
    eraseConfiguration (widen included state) = eraseConfiguration state := by
  simp only [eraseConfiguration, widen, List.map_map]
  rfl

theorem widen_self {family : List Obj} (included : ∀ a ∈ family, a ∈ family)
    (state : Configuration (Frames.Families.Term Tm family) O) : widen included state = state := by
  apply eraseConfiguration_injective
  exact erase_widen included state

theorem widen_comp {first middle last : List Obj} (one : ∀ a ∈ first, a ∈ middle)
    (two : ∀ a ∈ middle, a ∈ last) (state : Configuration (Frames.Families.Term Tm first) O) :
    widen two (widen one state) = widen (fun a member => two a (one a member)) state := by
  apply eraseConfiguration_injective
  rw [erase_widen, erase_widen, erase_widen]

variable [DecidableEq O]

def unit : FramedConfiguration Tm O := ⟨[], Coexistence.unit⟩

def tensor (left right : FramedConfiguration Tm O) : FramedConfiguration Tm O where
  frames := left.frames ++ right.frames
  content := Coexistence.tensor
    (widen (fun _ member => List.mem_append_left _ member) left.content)
    (widen (fun _ member => List.mem_append_right _ member) right.content)

theorem erase_tensor (left right : FramedConfiguration Tm O) :
    erase (tensor left right) = Coexistence.tensor (erase left) (erase right) := by
  simp only [erase, tensor, Coexistence.tensor, eraseConfiguration, widen,
    List.map_append, List.map_map]
  rfl

@[simp] theorem unit_tensor (state : FramedConfiguration Tm O) : tensor unit state = state := by
  apply ext (left := tensor unit state) (right := state) rfl
  rw [erase_tensor]
  exact Coexistence.unit_tensor _

@[simp] theorem tensor_unit (state : FramedConfiguration Tm O) : tensor state unit = state := by
  apply ext (left := tensor state unit) (right := state) (List.append_nil _)
  rw [erase_tensor]
  exact Coexistence.tensor_unit _

theorem tensor_assoc (left middle right : FramedConfiguration Tm O) :
    tensor (tensor left middle) right = tensor left (tensor middle right) := by
  apply ext (left := tensor (tensor left middle) right) (right := tensor left (tensor middle right))
    (List.append_assoc _ _ _)
  rw [erase_tensor, erase_tensor, erase_tensor, erase_tensor]
  exact Coexistence.tensor_assoc _ _ _

instance : Monoid (FramedConfiguration Tm O) where
  one := unit
  mul := tensor
  mul_assoc := tensor_assoc
  one_mul := unit_tensor
  mul_one := tensor_unit

theorem widen_tensor {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (left right : Configuration (Frames.Families.Term Tm source) O) :
    widen included (Coexistence.tensor left right) =
      Coexistence.tensor (widen included left) (widen included right) := by
  simp [widen, Coexistence.tensor, List.map_append]

variable {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

omit [DecidableEq O] in
theorem transport_inclusion {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    (state : Configuration (Frames.Families.Term Tm source) O) :
    Coexistence.transport X.families (Frames.Families.inclusion X included) state =
      widen included state := by
  rcases state with ⟨knowledge, present⟩
  unfold Coexistence.transport Frames.applyStore widen
  congr 1
  apply List.map_congr_left
  intro equation _
  apply Prod.ext <;> apply Subtype.ext <;> exact Frames.Families.act_inclusion X included _

theorem models_tensor (left right : FramedConfiguration Tm O) {target : List Obj}
    (mapping : Frames.Families.Map Hom (left.frames ++ right.frames) target) :
    X.families.Models mapping (tensor left right).content.equations ↔
      X.families.Models (Frames.Families.compose X mapping
        (Frames.Families.left X left.frames right.frames)) left.content.equations ∧
      X.families.Models (Frames.Families.compose X mapping
        (Frames.Families.right X left.frames right.frames)) right.content.equations := by
  change X.families.Models mapping (Coexistence.tensor
    (widen (fun _ member => List.mem_append_left _ member) left.content)
    (widen (fun _ member => List.mem_append_right _ member) right.content)).equations ↔ _
  rw [Coexistence.models_tensor, ← transport_inclusion X, ← transport_inclusion X,
    Coexistence.models_transport, Coexistence.models_transport]
  rfl

def Similar (left right : FramedConfiguration Tm O) : Prop :=
  ∃ support : ∀ a, a ∈ left.frames ↔ a ∈ right.frames,
    Coexistence.Same X.families
      (widen (fun a member => (support a).mp member) left.content) right.content

omit [DecidableEq O] in
theorem widen_congr {source target : List Obj} (included : ∀ a ∈ source, a ∈ target)
    {left right : Configuration (Frames.Families.Term Tm source) O}
    (same : Coexistence.Same X.families left right) :
    Coexistence.Same X.families (widen included left) (widen included right) := by
  rw [← transport_inclusion X, ← transport_inclusion X]
  exact Coexistence.transport_congr X.families _ same

omit [DecidableEq O] in
theorem Similar.refl (state : FramedConfiguration Tm O) : Similar X state state := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  rw [widen_self]
  exact Coexistence.Same.refl X.families _

omit [DecidableEq O] in
theorem Similar.symm {left right : FramedConfiguration Tm O} (same : Similar X left right) :
    Similar X right left := by
  obtain ⟨support, contents⟩ := same
  refine ⟨fun a => (support a).symm, ?_⟩
  have carried := widen_congr X (fun a member => (support a).mpr member) contents
  rw [widen_comp, widen_self] at carried
  exact Coexistence.Same.symm X.families carried

omit [DecidableEq O] in
theorem Similar.trans {left middle right : FramedConfiguration Tm O}
    (one : Similar X left middle) (two : Similar X middle right) : Similar X left right := by
  obtain ⟨first, firstContents⟩ := one
  obtain ⟨second, secondContents⟩ := two
  refine ⟨fun a => (first a).trans (second a), ?_⟩
  have carried := widen_congr X (fun a member => (second a).mp member) firstContents
  rw [widen_comp] at carried
  exact Coexistence.Same.trans X.families carried secondContents

theorem tensor_comm (left right : FramedConfiguration Tm O) :
    Similar X (tensor left right) (tensor right left) := by
  have support : ∀ a, a ∈ left.frames ++ right.frames ↔ a ∈ right.frames ++ left.frames := by
    intro a
    simp only [List.mem_append]
    exact or_comm
  refine ⟨support, ?_⟩
  change Coexistence.Same X.families (a := right.frames ++ left.frames)
    (widen (fun a member => (support a).mp member)
      (Coexistence.tensor
        (widen (fun _ member => List.mem_append_left _ member) left.content)
        (widen (fun _ member => List.mem_append_right _ member) right.content)))
    (Coexistence.tensor
      (widen (fun _ member => List.mem_append_left _ member) right.content)
      (widen (fun _ member => List.mem_append_right _ member) left.content))
  rw [widen_tensor, widen_comp, widen_comp]
  exact Coexistence.tensor_comm X.families _ _

omit [DecidableEq O] in
theorem Similar.solvable_pullback {left right : FramedConfiguration Tm O}
    (same : Similar X left right) (solved : X.families.Solvable right.content.equations) :
    X.families.Solvable left.content.equations := by
  obtain ⟨support, contents⟩ := same
  obtain ⟨target, mapping, model⟩ := solved
  have moved := (contents.2 target mapping).mpr model
  rw [← transport_inclusion X] at moved
  exact ⟨target, X.families.comp mapping (Frames.Families.inclusion X
    (fun a member => (support a).mp member)),
    (Coexistence.models_transport X.families _ mapping left.content).mp moved⟩

omit [DecidableEq O] in
theorem Similar.solvable_iff {left right : FramedConfiguration Tm O} (same : Similar X left right) :
    X.families.Solvable left.content.equations ↔ X.families.Solvable right.content.equations :=
  ⟨fun solved => (same.symm X).solvable_pullback X solved,
    fun solved => same.solvable_pullback X solved⟩

end FramedConfiguration
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence
