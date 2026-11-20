import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketGuardedRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryControls

/-!
# Canonical packet admission with a genuinely varying count region

The store is a bag of physical occurrences, the commit one prepared match,
guards are asked after the match's own tells, the program is fixed, and
knowledge is one store. The native unknown F satisfies F(0,1)=0. Its query
F(1,0) matches exactly one stored literal at every solution, but that literal
can be either occurrence. The positive uses the actual native firing and
the concrete compiled guard list. Changing the requested count to two is
refused, without changing its physical selection or output shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedAdmissionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualNonprincipalCountControls
open NativePacketStep (packetAction)
open PredicateQueryAdmission (RegionValid RegionQuery)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Nat)

abbrev state := NativePacketQueryControls.Nonprincipal.state

def counted (number : Nat) : LiveFiring state :=
  { NativePacketQueryControls.Nonprincipal.firing with
    rule := { rule with checks := [.count (instantiate
      (ContextualSelectionViews.capturedSource locals functions)
      (call (literal 1) (literal 0))) number] } }

def members (number : Nat) : List (LiveFiring state) := [counted number]

def index (number : Nat) : Fin (members number).length := ⟨0,by simp [members]⟩

theorem shapes (number : Nat) : (native (S := base) (O := Nat) (Γ := []) (sort := ())).Shapes (counted number).toNative :=
  ⟨by change ([] : List Nat).Nodup; exact List.nodup_nil,
    by change ([2] : List Nat).Nodup; exact List.nodup_singleton _,rfl,rfl,rfl⟩

theorem keeps_labels (number : Nat) :
    (NativePacketStep.selection (counted number)).made.map (NativePacketRounds.label (members number)) =
      (NativePacketStep.body (counted number) 1).produce := rfl

noncomputable def valid (number : Nat) : Prop :=
  RegionValid (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
    (NativePacketRounds.label (members number))
    (NativePacketGuardedAdmission.body (counted number) 1)
    (NativePacketGuardedAdmission.questions (counted number) 1)
    (NativePacketStep.configuration state 0) (NativePacketStep.selection (counted number))

theorem count_one_native : (counted 1).toNative.Realized :=
  NativePacketQueryControls.Nonprincipal.actual_native_admitted

theorem count_one_clear : NativeIterated.FamilyClear state (members 1) where
  admitted firing inside := by
    obtain rfl := List.mem_singleton.mp inside
    exact count_one_native
  pairwise := List.pairwise_singleton _ _
  jointly := by
    refine ⟨⟨Empty,locals⟩,Assignment.compose (model locals (literal 0))
      (ContextualSelectionViews.capturedTarget locals functions),?_⟩
    intro firing inside
    obtain rfl := List.mem_singleton.mp inside
    exact ⟨model locals (literal 0),constant_model locals,rfl⟩

theorem count_one_packet : valid 1 :=
  (NativePacketGuardedAdmission.regionValid_iff (members 1) (index 1) (shapes 1)).mpr
    ⟨count_one_native,keeps_labels 1⟩

theorem count_two_native_refused : ¬ (counted 2).toNative.Realized := by
  intro realized
  have checks := ((NativePacketGuardedAdmission.native_asks_iff (counted 2)).mp
    ((native_admits_iff (counted 2).toNative).mp realized).2.2.2).1
  have asked := checks (.count pattern 2) (by exact List.mem_singleton_self _)
  have seen := asked ⟨Empty,locals⟩ (model locals (literal 0)) (constant_model locals)
  change (ContextualConditionalGuards.region locals (model locals (literal 0)) rows before.present pattern).card = 2 at seen
  rw [region_at_literal locals (model locals (literal 0)) 0 (.inl rfl) rfl] at seen
  norm_num at seen

theorem count_two_packet_refused : ¬ valid 2 := by
  intro accepted
  exact count_two_native_refused
    ((NativePacketGuardedAdmission.regionValid_iff (members 2) (index 2) (shapes 2)).mp accepted).1

theorem same_physical_selection : (counted 1).selection = (counted 2).selection := rfl

theorem count_does_not_fix_a_collect (seen : Finset Nat) :
    ¬ (RegionQuery.exact
        (NativePacketQueryView.region (NativePacketStep.useObject state 1) pattern)
        (seen.image Sum.inl)).Ask
      (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
      (NativePacketQueryCuts.memberProblem (members 1) (index 1))
      (NativePacketRounds.label (members 1)) (NativePacketStep.present state) := by
  intro asked
  have exactAsk := (NativePacketGuardedAdmission.exact_ask_iff (members 1) (index 1)
    NativePacketQueryControls.Nonprincipal.enabled pattern seen).mp asked
  apply no_fixed_matching_table seen
  intro Future future candidate solved
  exact (ContextualPredicateQueryAdmission.matching_holds_iff locals pattern seen rows before.present
    ⟨Future,future,candidate⟩).mpr (exactAsk ⟨Future,future⟩ candidate solved)

theorem varying_region_witnesses :
    MeTTaCalculus.OccurrenceCommits.regionOf (NativePacketStep.label (counted 1) 0 1) (NativePacketStep.present state)
        ((NativePacketQueryControls.Nonprincipal.counted 1).region
          NativePacketQueryControls.Nonprincipal.constantFit) = {Sum.inl 0} ∧
      MeTTaCalculus.OccurrenceCommits.regionOf (NativePacketStep.label (counted 1) 0 1) (NativePacketStep.present state)
        ((NativePacketQueryControls.Nonprincipal.counted 1).region
          NativePacketQueryControls.Nonprincipal.projectionFit) = {Sum.inl 1} :=
  ⟨NativePacketQueryControls.Nonprincipal.constant_region,NativePacketQueryControls.Nonprincipal.projection_region⟩

def quietCount : LiveFiring state :=
  { counted 1 with
    rule := { (counted 1).rule with produce := [] }
    selection := ⟨[],[],[]⟩ }

theorem quiet_count_native : quietCount.toNative.Realized := by
  apply (native_admits_iff quietCount.toNative).mpr
  refine ⟨⟨by decide,by decide,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,
      fun _ inside => by cases inside⟩
  · exact ⟨⟨Empty,locals⟩,model locals (literal 0),constant_model locals⟩
  · intro target candidate solved
    refine ⟨?_,fun _ inside => by cases inside⟩
    intro check inside
    obtain rfl := List.mem_singleton.mp inside
    exact count_guard target.Names target.arity candidate solved

def quietJoint : NativeResidual.Joint state quietCount.toNative.information
    quietCount.toNative.information ⟨Empty,locals⟩ where
  left := model locals (literal 0)
  right := model locals (literal 0)
  left_models := constant_model locals
  right_models := constant_model locals
  agree := rfl

theorem quiet_clear_itself : Clear quietCount quietCount.selection quietCount.rule quietCount.outputs where
  takes := by decide
  ports := by decide
  keeps := by decide
  consistent := ⟨⟨Empty,locals⟩,⟨quietJoint⟩⟩
  blindTakes _ _ _ inside := by cases inside
  blindOutputs _ _ _ inside := by cases inside

theorem two_count_events_clear : NativeIterated.FamilyClear state [quietCount,quietCount] where
  admitted firing inside := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at inside
    subst firing
    exact quiet_count_native
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro firing inside
    obtain rfl := List.mem_singleton.mp inside
    exact ⟨quiet_clear_itself,quiet_clear_itself⟩
  jointly := by
    refine ⟨⟨Empty,locals⟩,Assignment.compose (model locals (literal 0))
      (ContextualSelectionViews.capturedTarget locals functions),?_⟩
    intro firing inside
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at inside
    subst firing
    exact ⟨model locals (literal 0),constant_model locals,rfl⟩

theorem two_count_events_round :
    AnnotatedRuns.Round (packetAction (S := base) (O := Nat) (Γ := []) (sort := ()))
      (NativePacketRounds.label [quietCount,quietCount]) (NativePacketStep.configuration state 0)
      (NativePacketGuardedRounds.image [quietCount,quietCount]) :=
  NativePacketGuardedRounds.round_of_clear (by simp) two_count_events_clear

theorem two_count_events_every_order {order : List (LiveFiring state)} (permutes : order.Perm [quietCount,quietCount]) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness state order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = 2 ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  NativePacketGuardedRounds.native_every_order [quietCount,quietCount] (by simp)
    (fun index => ((native_admits_iff ([quietCount,quietCount][index]).toNative).mp
      (two_count_events_clear.admitted _ (List.getElem_mem ..))).1) two_count_events_round permutes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketGuardedAdmissionControls
