import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministrativeProgress
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceOrigins

/-!
# Original guarded bodies of stable unary runtime sources

Observations of a stable activity retain its actual input body in the authored
equational quotient, or its actual ordered output field. Reading these
observations recovers the original source constructor. A retained server is
distinguished from an ordinary input rather than replaced by a fresh copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceObservations

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryActive RhoUnaryAdministrativeProgress ActiveGuardedBodies

private theorem input_equal {Γ : Ctx sig} {index origin : Nat}
    {channel actualChannel : Var Γ .nm} {body actualBody : Proc (.nm :: Γ)}
    (equal : input1 index (.var channel) body (fun _ name => name) =
      input1 origin (.var actualChannel) actualBody (fun _ name => name)) :
    index = origin ∧ channel = actualChannel ∧ StructuralEq body actualBody := by
  have origins : index = origin := congrArg (fun observation => observation.header.origin) equal
  have channels : channel = actualChannel := congrArg (fun observation => observation.header.channel) equal
  have bodies : bodyQ (fun _ name => name) [.nm] body = bodyQ (fun _ name => name) [.nm] actualBody :=
    Option.some.inj (congrArg Observation.unaryBody equal)
  have identity : liftRen (fun _ name => name : Ren sig Γ Γ) [.nm] = (fun _ name => name) := by
    funext sort name
    cases name <;> rfl
  have quotient : EqClosure equations
      (rename (liftRen (fun _ name => name : Ren sig Γ Γ) [Srt.nm]) body)
      (rename (liftRen (fun _ name => name : Ren sig Γ Γ) [Srt.nm]) actualBody) := Quotient.exact bodies
  rw [identity, rename_id, rename_id] at quotient
  exact ⟨origins, channels, eqClosure_sound quotient⟩

/-- An observed unary receiver is the original indexed input or retained
server. Its supplied suspended body agrees modulo the authored equations. -/
theorem input_activity {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (index origin : Nat) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (activity : Activity Γ) (stable : Stable activity)
    (seen : input1 index (.var channel) body (fun _ name => name) ∈
      observe binderName (ActiveSyntaxMarking.mark origin activity.source) activity.source (fun _ name => name)) :
    index = origin ∧ ∃ (actualBody : Proc (.nm :: Γ))
      (guarded : RhoUnaryCompiler.GuardedUnary actualBody),
      StructuralEq body actualBody ∧
        (activity = .input channel actualBody guarded ∨
          ∃ self, activity = .ready channel actualBody guarded self) := by
  cases activity with
  | output actualChannel datum =>
      simp [Activity.source, ActiveSyntaxMarking.mark, out1, observe, input1, output1,
        Observation.mk.injEq, ActiveMarkedNames.Observation.mk.injEq] at seen
  | input actualChannel actualBody guarded =>
      simp only [Activity.source, inp1, ActiveSyntaxMarking.mark, observe,
        Set.mem_singleton_iff] at seen
      obtain ⟨sameIndex, sameChannel, sameBody⟩ := input_equal seen
      subst actualChannel
      exact ⟨sameIndex, actualBody, guarded, sameBody, Or.inl rfl⟩
  | ready actualChannel actualBody guarded self =>
      simp only [Activity.source, rep, inp1, ActiveSyntaxMarking.mark, observe,
        Set.mem_singleton_iff] at seen
      obtain ⟨sameIndex, sameChannel, sameBody⟩ := input_equal seen
      subst actualChannel
      exact ⟨sameIndex, actualBody, guarded, sameBody, Or.inr ⟨self, rfl⟩⟩
  | allocatorReady => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | token seed => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | _ => cases stable

/-- Every observation belongs to a literal activity at the original list
index. This decomposition also applies before administrative work finishes. -/
theorem observed_index {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activities : List (Activity Γ)) (start : Nat) (observation : Observation Nat Γ)
    (seen : observation ∈ observe binderName (RhoUnarySourceOrigins.mark start activities)
      (source activities) (fun _ name => name)) :
    ∃ (index : Nat) (activity : Activity Γ), activities[index]? = some activity ∧
      observation ∈ observe binderName (ActiveSyntaxMarking.mark (start + index) activity.source)
        activity.source (fun _ name => name) := by
  induction activities generalizing start with
  | nil => simp [RhoUnarySourceOrigins.mark, source, ScopedActiveFrontier.parallel, nil, observe] at seen
  | cons first rest ih =>
      simp only [RhoUnarySourceOrigins.mark, source, List.map_cons, ScopedActiveFrontier.parallel,
        par, observe, Set.mem_union] at seen
      rcases seen with here | later
      · exact ⟨0, first, rfl, by simpa only [Nat.add_zero] using here⟩
      · obtain ⟨index, activity, selected, seen⟩ := ih (start + 1) later
        refine ⟨index + 1, activity, ?_, ?_⟩
        · simpa only [List.getElem?_cons_succ] using selected
        · simpa only [Nat.add_assoc, Nat.add_comm 1 index] using seen

/-- The body of an observed receiver is read from the same retained
activity, with ordinary and persistent reception kept separate. -/
theorem input1_at {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activities : List (Activity Γ)) (stable : ∀ activity ∈ activities, Stable activity)
    (index : Nat) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (seen : input1 index (.var channel) body (fun _ name => name) ∈
      observe binderName (RhoUnarySourceOrigins.mark 0 activities) (source activities) (fun _ name => name)) :
    ∃ (actualBody : Proc (.nm :: Γ)) (guarded : RhoUnaryCompiler.GuardedUnary actualBody),
      StructuralEq body actualBody ∧
        (activities[index]? = some (.input channel actualBody guarded) ∨
          ∃ self, activities[index]? = some (.ready channel actualBody guarded self)) := by
  obtain ⟨selectedIndex, activity, selected, seen⟩ := observed_index binderName activities 0 _ seen
  obtain ⟨sameIndex, actualBody, guarded, equal, kind⟩ :=
    input_activity binderName index (0 + selectedIndex) channel body activity
      (stable activity (List.mem_of_getElem? selected)) seen
  have same : selectedIndex = index := by omega
  subst selectedIndex
  refine ⟨actualBody, guarded, equal, ?_⟩
  rcases kind with ordinary | ⟨self, server⟩
  · exact Or.inl (selected.trans (congrArg some ordinary))
  · exact Or.inr ⟨self, selected.trans (congrArg some server)⟩

/-- The output observation recovers the same source channel and datum;
equal messages at distinct indices remain distinct source occurrences. -/
theorem output_activity {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (index origin : Nat) (channel datum : Var Γ .nm)
    (activity : Activity Γ) (stable : Stable activity)
    (seen : output1 index (.var channel) (.var datum) (fun _ name => name) ∈
      observe binderName (ActiveSyntaxMarking.mark origin activity.source) activity.source (fun _ name => name)) :
    index = origin ∧ activity = .output channel datum := by
  cases activity with
  | output actualChannel actualDatum =>
      simp only [Activity.source, out1, ActiveSyntaxMarking.mark, observe,
        Set.mem_singleton_iff] at seen
      have sameIndex : index = origin := congrArg (fun observation => observation.header.origin) seen
      have sameChannel : channel = actualChannel := congrArg (fun observation => observation.header.channel) seen
      have sameDatum : [datum] = [actualDatum] := congrArg (fun observation => observation.header.fields) seen
      have datumEqual : datum = actualDatum := List.cons.inj sameDatum |>.1
      subst actualChannel
      subst actualDatum
      exact ⟨sameIndex, rfl⟩
  | input actualChannel body guarded | ready actualChannel body guarded self =>
      simp [Activity.source, rep, inp1, ActiveSyntaxMarking.mark, observe, input1, output1,
        Observation.mk.injEq, ActiveMarkedNames.Observation.mk.injEq] at seen
  | allocatorReady => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | token seed => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | _ => cases stable

/-- The selected output keeps its original index, subject and ordered datum. -/
theorem output1_at {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activities : List (Activity Γ)) (stable : ∀ activity ∈ activities, Stable activity)
    (index : Nat) (channel datum : Var Γ .nm)
    (seen : output1 index (.var channel) (.var datum) (fun _ name => name) ∈
      observe binderName (RhoUnarySourceOrigins.mark 0 activities) (source activities) (fun _ name => name)) :
    activities[index]? = some (.output channel datum) := by
  obtain ⟨selectedIndex, activity, selected, seen⟩ := observed_index binderName activities 0 _ seen
  obtain ⟨sameIndex, equal⟩ := output_activity binderName index (0 + selectedIndex) channel datum
    activity (stable activity (List.mem_of_getElem? selected)) seen
  have same : selectedIndex = index := by omega
  subst selectedIndex
  exact selected.trans (congrArg some equal)

theorem stable_observed_origin {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activity : Activity Γ) (stable : Stable activity) (origin : Nat)
    (observation : Observation Nat Γ)
    (seen : observation ∈ observe binderName
      (ActiveSyntaxMarking.mark origin activity.source) activity.source (fun _ name => name)) :
    observation.header.origin = origin := by
  cases activity with
  | output channel datum =>
      simp only [Activity.source, out1, ActiveSyntaxMarking.mark, observe, Set.mem_singleton_iff] at seen
      subst observation
      rfl
  | input channel body guarded | ready channel body guarded self =>
      simp only [Activity.source, rep, inp1, ActiveSyntaxMarking.mark, observe, Set.mem_singleton_iff] at seen
      subst observation
      rfl
  | allocatorReady => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | token seed => simp [Activity.source, nil, ActiveSyntaxMarking.mark, observe] at seen
  | _ => cases stable

/-- A supplied original index determines the activity producing any
observation carrying that index, including copied persistent receivers. -/
theorem activity_observation_at {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activities : List (Activity Γ)) (stable : ∀ activity ∈ activities, Stable activity)
    (index : Nat) (activity : Activity Γ) (selected : activities[index]? = some activity)
    (observation : Observation Nat Γ)
    (seen : observation ∈ observe binderName (RhoUnarySourceOrigins.mark 0 activities)
      (source activities) (fun _ name => name)) (origin : observation.header.origin = index) :
    observation ∈ observe binderName (ActiveSyntaxMarking.mark index activity.source)
      activity.source (fun _ name => name) := by
  obtain ⟨actualIndex, actual, actualSelected, actualSeen⟩ := observed_index binderName activities 0 _ seen
  have actualOrigin := stable_observed_origin binderName actual
    (stable actual (List.mem_of_getElem? actualSelected)) (0 + actualIndex) observation actualSeen
  have sameIndex : actualIndex = index := by omega
  subst actualIndex
  have sameActivity : actual = activity := Option.some.inj (actualSelected.symm.trans selected)
  subst actual
  simpa only [Nat.zero_add] using actualSeen

/-- Every observed copy at a retained server's index has the actual
original subject and suspended body, rather than just the same arity. -/
theorem ready_observation_at {Γ : Ctx sig} (binderName : Nat → Var Γ .nm)
    (activities : List (Activity Γ)) (stable : ∀ activity ∈ activities, Stable activity)
    (index : Nat) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (guarded : RhoUnaryCompiler.GuardedUnary body) (self : Nat)
    (selected : activities[index]? = some (.ready channel body guarded self))
    (observation : Observation Nat Γ)
    (seen : observation ∈ observe binderName (RhoUnarySourceOrigins.mark 0 activities)
      (source activities) (fun _ name => name)) (origin : observation.header.origin = index) :
    observation = input1 index (.var channel) body (fun _ name => name) := by
  have actual := activity_observation_at binderName activities stable index
    (.ready channel body guarded self) selected observation seen origin
  simpa only [Activity.source, rep, inp1, ActiveSyntaxMarking.mark, observe, Set.mem_singleton_iff] using actual


end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceObservations
