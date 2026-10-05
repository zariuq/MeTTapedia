import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginErasure

/-!
# Active observations are witnessed by their counted constructor origins

The count follows prefix origins through parallel components, restrictions and
replicated bodies. It does not count suspended continuations. Thus a frame with
zero selected origins cannot provide a selected active guard or message, even
when its unselected guards use the same physical subject.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginObservations

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies

universe u

theorem count_mono {Label : Type u} (smaller larger : Label → Bool)
    (included : ∀ origin, smaller origin = true → larger origin = true)
    (marked : ActiveMarking.Tree Label) : originCount smaller marked ≤ originCount larger marked := by
  induction marked with
  | var | nil => exact le_rfl
  | par _ _ left right => exact Nat.add_le_add left right
  | inp1 origin _ | inp2 origin _ | out1 origin | out2 origin =>
      by_cases chosen : smaller origin = true
      · have largerChosen := included origin chosen
        simp only [originCount, chosen, largerChosen, ite_true, le_refl]
      · simp only [originCount, chosen]
        exact Nat.zero_le _
  | nu _ _ ih | rep _ ih => exact ih

theorem count_zero_of_subset {Label : Type u} (smaller larger : Label → Bool)
    (included : ∀ origin, smaller origin = true → larger origin = true)
    (marked : ActiveMarking.Tree Label) (zero : originCount larger marked = 0) :
    originCount smaller marked = 0 := by
  have bound := count_mono smaller larger included marked
  omega

theorem communication_count {Label : Type u} (selected : Label → Bool)
    {Γ : Ctx sig} {redex reduct : Proc Γ}
    {chosen : ScopedCommunicationInversion.Communication redex reduct}
    {marked : ActiveMarking.Tree Label} (comm : MarkedCommunication chosen marked) :
    originCount selected marked =
      (if selected comm.inputOrigin then 1 else 0) + (if selected comm.outputOrigin then 1 else 0) := by
  cases comm <;> simp only [originCount, MarkedCommunication.inputOrigin,
    MarkedCommunication.outputOrigin, Nat.add_comm]
  all_goals rfl

/-- Observations of the supplied untouched frame travel back through the
same transport that exposed the chosen communication. -/
theorem traced_frame_observed {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    {Γ : Ctx sig} {original : ActiveMarking.Tree Label} {source target : Proc Γ}
    {exposure : ScopedCommunicationInversion.Exposure source target}
    (traced : TracedExposure original exposure) (environment : Ren sig Γ Ω)
    (observation : Observation Label Ω)
    (member : observation ∈ observe binderName traced.frameMarks exposure.frame
      (scopeEnvironment binderName traced.binders environment)) :
    observation ∈ observe binderName original source environment := by
  apply observations_back binderName traced.transport environment
  rw [observe_scope]
  simp only [par, observe, Set.mem_union]
  exact Or.inr member

theorem positive {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    (selected : Label → Bool) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label}
    {process : Proc Γ} (fitted : Fits marked process) (environment : Ren sig Γ Ω)
    (observation : Observation Label Ω)
    (member : observation ∈ observe binderName marked process environment)
    (chosen : selected observation.header.origin = true) :
    0 < originCount selected marked := by
  induction fitted with
  | var => simp only [observe, Set.mem_empty_iff_false] at member
  | nil => simp only [nil, observe, Set.mem_empty_iff_false] at member
  | par _ _ firstIH secondIH =>
      simp only [par, observe, Set.mem_union] at member
      simp only [originCount]
      rcases member with left | right
      · have bound := firstIH environment left
        omega
      · have bound := secondIH environment right
        omega
  | inp1 =>
      simp only [inp1, observe, Set.mem_singleton_iff] at member
      rw [member] at chosen
      simp only [input1] at chosen
      simpa only [originCount, chosen, ite_true] using Nat.zero_lt_one
  | inp2 =>
      simp only [inp2, observe, Set.mem_singleton_iff] at member
      rw [member] at chosen
      simp only [input2] at chosen
      simpa only [originCount, chosen, ite_true] using Nat.zero_lt_one
  | out1 =>
      simp only [out1, observe, Set.mem_singleton_iff] at member
      rw [member] at chosen
      simp only [output1] at chosen
      simpa only [originCount, chosen, ite_true] using Nat.zero_lt_one
  | out2 =>
      simp only [out2, observe, Set.mem_singleton_iff] at member
      rw [member] at chosen
      simp only [output2] at chosen
      simpa only [originCount, chosen, ite_true] using Nat.zero_lt_one
  | nu origin _ ih =>
      simp only [nu, observe] at member
      simpa only [originCount] using ih (prependRen (binderName origin) environment) member
  | rep _ ih =>
      simp only [rep, observe] at member
      simpa only [originCount] using ih environment member

theorem excluded {Label : Type u} {Ω : Ctx sig} (binderName : Label → Var Ω .nm)
    (selected : Label → Bool) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label}
    {process : Proc Γ} (fitted : Fits marked process) (environment : Ren sig Γ Ω)
    (zero : originCount selected marked = 0) (observation : Observation Label Ω)
    (member : observation ∈ observe binderName marked process environment) :
    selected observation.header.origin = false := by
  cases chosen : selected observation.header.origin with
  | false => rfl
  | true =>
      have bound := positive binderName selected fitted environment observation member chosen
      omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveOriginObservations
