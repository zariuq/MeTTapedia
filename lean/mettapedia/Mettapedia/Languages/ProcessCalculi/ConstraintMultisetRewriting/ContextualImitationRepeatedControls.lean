import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitationControls

/-!
# Repeated spines preserve alternative contextual images

Imitating a rigid pair through `F[x,x]` is sound and complete as a residual
transformation. Both formal projections remain possible. Their instantiated
occurrences coincide, but their original contextual images differ; this is
not the uniquely recoverable distinct-variable fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation.RepeatedControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualBinding.Controls (base)
open ContextualImitation.Controls (others original)

abbrev source := sourceDeclarations [(), ()] () others
abbrev target := targetDeclarations (S := base) [(), ()] (result := ()) ContextualFrame.Controls.Operator.pair others
abbrev pairSlots := ArgumentSlots.Slot (base.arity (s := ()) ContextualFrame.Controls.Operator.pair)

def firstSlot : pairSlots := ⟨([], ()), .zero⟩
def secondSlot : pairSlots := ⟨([], ()), .succ .zero⟩

def repeatedMap : Ren base [(), ()] [()] := fun _ position => match position with
  | .zero => .zero
  | .succ .zero => .zero
  | .succ (.succ impossible) => nomatch impossible

def left : Term (signature base source) [()] () :=
  rename (S := signature base source) repeatedMap (generator source original)

def right : Term (signature base source) [()] () :=
  .op (.inl .pair) (.cons (.var .zero) (.cons (.var .zero) .nil))

def problem : Problem source := [(observe left, observe right)]
def first : Assignment source target := answer [(), ()] ContextualFrame.Controls.Operator.pair others

theorem imitation_accepts_the_repeated_spine_without_claiming_unique_recovery :
    Reduction problem first (mapProblem first problem) :=
  reduction [(), ()] ContextualFrame.Controls.Operator.pair others repeatedMap
    (.cons (.var .zero) (.cons (.var .zero) .nil)) problem (by
      with_unfolding_all exact List.mem_singleton_self _)

def projectFirst : Assignment target target
  | .inl ⟨_, .zero⟩ => .var .zero
  | .inl ⟨_, .succ .zero⟩ => .var .zero
  | .inl ⟨_, .succ (.succ impossible)⟩ => nomatch impossible
  | .inr identity => generator target (.inr identity)

def projectSecond : Assignment target target
  | .inl ⟨_, .zero⟩ => .var (.succ .zero)
  | .inl ⟨_, .succ .zero⟩ => .var (.succ .zero)
  | .inl ⟨_, .succ (.succ impossible)⟩ => nomatch impossible
  | .inr identity => generator target (.inr identity)

theorem the_first_projection_solves_the_residual : Models projectFirst (mapProblem first problem) := by
  intro equation member
  simp only [mapProblem, problem, List.map_cons, List.map_nil, List.mem_singleton] at member
  subst equation
  with_unfolding_all rfl

theorem the_second_projection_also_solves_the_residual : Models projectSecond (mapProblem first problem) := by
  intro equation member
  simp only [mapProblem, problem, List.map_cons, List.map_nil, List.mem_singleton] at member
  subst equation
  with_unfolding_all rfl

theorem both_original_contextual_answers_are_solutions :
    Models (Assignment.compose projectFirst first) problem ∧
      Models (Assignment.compose projectSecond first) problem :=
  ⟨imitation_accepts_the_repeated_spine_without_claiming_unique_recovery.sound target projectFirst
      the_first_projection_solves_the_residual,
    imitation_accepts_the_repeated_spine_without_claiming_unique_recovery.sound target projectSecond
      the_second_projection_also_solves_the_residual⟩

theorem the_original_images_are_distinct :
    Assignment.compose projectFirst first original ≠ Assignment.compose projectSecond first original := by
  intro same
  have fields := eq_of_heq (Term.op.inj same).2
  have firstFields := (Args.cons.inj fields).1
  have positions := Term.var.inj firstFields
  cases positions

def helperCall : pairSlots → Term (signature base target) [()] ()
  | ⟨_, .zero⟩ =>
      .op (.inr (.mk (.inl firstSlot))) (.cons (.var .zero) (.cons (.var .zero) .nil))
  | ⟨_, .succ .zero⟩ =>
      .op (.inr (.mk (.inl secondSlot))) (.cons (.var .zero) (.cons (.var .zero) .nil))
  | ⟨_, .succ (.succ impossible)⟩ => nomatch impossible

def remaining : Problem target :=
  [(observe (helperCall firstSlot), observe (Term.var (S := signature base target) (Γ := [()]) .zero)),
   (observe (helperCall secondSlot), observe (Term.var (S := signature base target) (Γ := [()]) .zero))]

theorem normalization_retains_both_repeated_spine_obligations :
    ContextualRigidSolver.normalize (mapProblem first problem) = some remaining := by
  with_unfolding_all rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualImitation.RepeatedControls
