import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectResidual

/-!
# Actual subject observations require a live occurrence

Subject counting and guarded-body observations inspect the same authored
active prefixes. An observed subject therefore has a positive occurrence
count. This connects private-key exclusion to occurrence provenance without
coalescing identical messages or identifying copied binder-origin labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectObservations

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveGuardedBodies ActiveSubjectResidual

universe u

local instance {Γ : Ctx sig} : DecidableEq (Var Γ Srt.nm) := decEqVar (S := sig)

theorem observed_positive {Label : Type u} {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ : Ctx sig} (process : Proc Γ) (marked : ActiveMarking.Tree Label)
      (environment : Ren sig Γ Ω) (observation : Observation Label Ω),
      observation ∈ observe (fun _ => fresh) marked process environment →
      observation.header.channel = subject → 0 < count fresh subject environment process
  | _, .var _, _, _, _, member, _ => by simp only [observe, Set.mem_empty_iff_false] at member
  | _, .op .nil .nil, _, _, _, member, _ => by simp only [observe, Set.mem_empty_iff_false] at member
  | _, .op .par (.cons first (.cons second .nil)), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_union] at member
      rename_i left right
      simp only [count]
      rcases member with leftMember | rightMember
      · have positive := observed_positive fresh subject first left environment observation leftMember same
        omega
      · have positive := observed_positive fresh subject second right environment observation rightMember same
        omega
  | _, .op .inp1 (.cons channel (.cons _ .nil)), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      simp only [input1] at same
      simp only [count, onSubject, same, decide_true, ite_true]
      omega
  | _, .op .inp2 (.cons channel (.cons _ .nil)), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      simp only [input2] at same
      simp only [count, onSubject, same, decide_true, ite_true]
      omega
  | _, .op .out1 (.cons channel (.cons _ .nil)), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      simp only [output1] at same
      simp only [count, onSubject, same, decide_true, ite_true]
      omega
  | _, .op .out2 (.cons channel (.cons _ (.cons _ .nil))), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false, Set.mem_singleton_iff] at member
      subst observation
      simp only [output2] at same
      simp only [count, onSubject, same, decide_true, ite_true]
      omega
  | _, .op .nu (.cons body .nil), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false] at member
      rename_i origin inside
      simpa only [count] using
        observed_positive fresh subject body inside (prependRen fresh environment) observation member same
  | _, .op .rep (.cons body .nil), marked, environment, observation, member, same => by
      cases marked <;> simp only [observe, Set.mem_empty_iff_false] at member
      rename_i inside
      simpa only [count] using observed_positive fresh subject body inside environment observation member same
termination_by _ process _ _ _ _ _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem observed_ne_of_count_zero {Label : Type u} {Γ Ω : Ctx sig}
    (fresh subject : Var Ω .nm) (process : Proc Γ) (marked : ActiveMarking.Tree Label)
    (environment : Ren sig Γ Ω) (zero : count fresh subject environment process = 0)
    (observation : Observation Label Ω)
    (member : observation ∈ observe (fun _ => fresh) marked process environment) :
    observation.header.channel ≠ subject := by
  intro same
  have positive := observed_positive fresh subject process marked environment observation member same
  omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectObservations
