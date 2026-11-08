import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnifierProfiles
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopePullbackControls

/-!
# Same-hole equations preserve local binders and the old active frame

Swapping both parameters leaves no old parameter available to a structural
solution. A lambda may still use its own bound variable. A second control
retains precisely the unchanged first parameter. The generated answer is
lifted into the ordinary equation action with the complete old interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ScopePullback.Controls (base)

def identityMap : Ren base [(), ()] [(), ()] := fun _ position => position

def swappedMap : Ren base [(), ()] [(), ()]
  | _, .zero => .succ .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

def collapsedMap : Ren base [(), ()] [(), ()]
  | _, .zero => .zero
  | _, .succ .zero => .zero
  | _, .succ (.succ impossible) => nomatch impossible

abbrev swapped := Mettapedia.OSLF.Binding.ScopeEqualizer.Finite.build identityMap swappedMap
abbrev collapsed := Mettapedia.OSLF.Binding.ScopeEqualizer.Finite.build identityMap collapsedMap

theorem swapped_parameters_have_no_fixed_position : swapped.context = [] := by with_unfolding_all rfl

theorem collapsing_one_parameter_retains_the_other : collapsed.context = [()] := by with_unfolding_all rfl

abbrev others (_ : Nat) : MetaArity base := ([(), ()], ())
abbrev selected (_ : Unit) : MetaArity base := ([(), ()], ())
abbrev fresh (_ : Unit) : MetaArity base := (swapped.context, ())
abbrev old := ContextualFreshFrame.old selected others
abbrev target := ContextualFreshFrame.target fresh others
abbrev active := ContextualFreshFrame.active selected fresh others
abbrev frameAnswer : Assignment old target := answer swapped () others

def problem : EquationStore (Term (signature base old) [(), ()] ()) :=
  [(rename (S := signature base old) identityMap (generator old (.inl ())),
    rename (S := signature base old) swappedMap (generator old (.inl ())))]

theorem generated_frame_answer_is_principal : ContextualFrameUnifier.Principal problem frameAnswer :=
  ContextualUnifierProfiles.same_hole swapped () others

theorem all_old_observations_are_retained
    (observed : List (Term (signature base old) [(), ()] ())) :
    (ContextualFamilies.action active [(), ()] ()).PrincipalOn
      (ContextualFrameUnifier.mapProblem (ContextualFreshFrame.includeOld selected fresh others) problem)
      (ContextualFreshFrame.answer selected fresh others frameAnswer)
      (observed.map (instantiate (ContextualFreshFrame.includeOld selected fresh others))) :=
  ContextualFreshFrame.principal_on selected fresh others problem frameAnswer
    generated_frame_answer_is_principal (fun _ => rfl) observed

def locallyBound : Assignment old others
  | .inl _ => .op (.inl .lam) (.cons (.var .zero) .nil)
  | .inr identity => generator others identity

theorem a_local_binder_remains_available : ContextualFrameUnifier.Models locallyBound problem := by
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

def privateDependency : Assignment old others
  | .inl _ => .var .zero
  | .inr identity => generator others identity

theorem a_swapped_old_dependency_is_refused : ¬ ContextualFrameUnifier.Models privateDependency problem := by
  intro solved
  have impossible := solved _ (List.mem_singleton_self _)
  change (Term.var (S := signature base others) (Γ := [(), ()]) Var.zero) = .var (.succ .zero) at impossible
  cases impossible

abbrev A := ContextualFamilies.action active [(), ()] ()
abbrev σ := ContextualFreshFrame.answer selected fresh others frameAnswer

def input : Term (signature base active) [(), ()] () :=
  instantiate (ContextualFreshFrame.includeOld selected fresh others) problem[0].1

def otherInput : Term (signature base active) [(), ()] () :=
  instantiate (ContextualFreshFrame.includeOld selected fresh others) problem[0].2

def frame : Term (signature base active) [(), ()] () :=
  instantiate (ContextualFreshFrame.includeOld selected fresh others) (generator old (.inr 9))

def label : Nat → Term (signature base active) [(), ()] ()
  | 0 => otherInput
  | 1 => frame
  | _ => input

def initial : Configuration (Term (signature base active) [(), ()] ()) Nat := ⟨[], {0, 1}⟩
def selectedOccurrences : Selection Nat := ⟨[0], [], [2]⟩
def rule : RuleInstance (Term (signature base active) [(), ()] ()) := ⟨[input], [], [], [], [input]⟩

theorem generated_answer_supports_an_ordinary_step : selectedOccurrences.Valid A label rule initial := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨σ, ?_⟩
    change A.Models σ (ContextualFrameUnifier.mapProblem
      (ContextualFreshFrame.includeOld selected fresh others) problem)
    exact (all_old_observations_are_retained
      [problem[0].1, problem[0].2, generator old (.inr 9)]).sound
  · simp [rule]

theorem same_hole_unification_fires_an_ordinary_step :
    Step A label rule initial (selectedOccurrences.result label rule initial) :=
  ⟨selectedOccurrences, generated_answer_supports_an_ordinary_step, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPair.Controls
