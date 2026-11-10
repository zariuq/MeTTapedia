import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ModelHenkin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EvidenceInterface

/-! # Refinement is relative to the declared solution morphisms

The frame has three terms and two substitutions: identity and collapse to
zero. The equations `0 = 1` and `1 = 2` therefore have exactly the same
solutions in the frame. A Henkin point may distinguish zero while identifying
one and two; that point is not represented by either substitution. Even exact
frame-relative refinement need not preserve such a model point. The free-model
transfer theorem consequently needs its stated representation hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ModelRefinementControls

def act (collapse : Bool) (term : Fin 3) : Fin 3 := if collapse then 0 else term

def frame : Frames (fun _ : Unit => Fin 3) (fun _ _ : Unit => Bool) where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act := act
  id _ := false
  comp g f := g || f
  act_id _ := rfl
  act_comp g f t := by cases g <;> cases f <;> rfl
  preserves := by intro a b f s t same; exact congrArg (act f) same

def knowledge (after : Bool) : EquationStore (Fin 3) :=
  if after then [(1, 2)] else [(0, 1)]

def effect : EffectCore frame Nat Bool (fun _ => Unit) where
  frame _ := ()
  knowledge := knowledge
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target _ := ()
  extension _ := false
  information {s} _ := knowledge s
  information_refines _ := by intro b σ solved; cases σ <;> exact solved
  Shapes _ := ([] : List Nat).Nodup
  preparedResult _ _ := true
  present_preparedResult _ _ := by
    ext o
    simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]
  preparedSettle _ _ := false
  result_refines _ _ := by
    intro b σ solved
    cases σ with
    | false =>
        have impossible : (1 : Fin 3) = 2 := solved (1, 2) (List.mem_singleton_self _)
        contradiction
    | true => intro e _; rfl

def step : Step frame Nat Bool (fun _ => Unit) := Step.ofEffect effect (fun _ _ => True)

theorem prepared (s : Bool) : effect.Prepares (s := s) () :=
  ⟨List.nodup_nil, EvidenceInterface.Controls.enabled_nothing ∅,
    ⟨(), true, by intro e _; rfl⟩⟩

theorem admitted : step.Admits (s := false) () := ⟨prepared false, trivial⟩

instance exact_step : step.Exact where
  exactness {s} _ _ := by
    intro b σ solved
    cases σ with
    | true => intro e _; rfl
    | false =>
        cases s with
        | false =>
            have impossible : (0 : Fin 3) = 1 := solved (0, 1) (List.mem_singleton_self _)
            contradiction
        | true => exact solved

def model : frame.HenkinModel Bool (fun _ : Unit => Fin 3 → Bool) where
  eval term point := point term
  pull f point := point ∘ act f
  eval_act _ _ _ := rfl
  eval_E := by intro a s t same point; cases same; rfl

def point (term : Fin 3) : Bool := term != 0

theorem result_point : model.Models (a := ()) point (step.knowledge (step.result () admitted)) := by
  intro e member
  change e ∈ [(1, 2)] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem source_point_fails :
    ¬model.Models (a := ()) (model.pull (a := ()) (b := ()) (step.along () admitted) point) (step.knowledge false) := by
  intro solved
  have impossible : false = true := solved (0, 1) (List.mem_singleton_self _)
  contradiction

theorem model_not_free : ¬model.Free := by
  intro free
  exact source_point_fails (step.model_transition_free model free admitted point result_point).2

theorem exact_refinement_does_not_cover_all_Henkin_points :
    step.Exact ∧ model.Models (a := ()) point (step.knowledge (step.result () admitted)) ∧
      ¬model.Models (a := ()) (model.pull (a := ()) (b := ()) (step.along () admitted) point) (step.knowledge false) :=
  ⟨inferInstance, result_point, source_point_fails⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ModelRefinementControls
