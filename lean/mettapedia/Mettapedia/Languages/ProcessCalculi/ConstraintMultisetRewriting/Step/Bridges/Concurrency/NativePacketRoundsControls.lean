import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformationControls

/-!
# Two actual generative reads at one symbolic packet state

Two native members read physical row 7. Its schema body opens privately at
each use; its latent equation links the same two captured names. The common
model keeps those captures unresolved and gives the two private bodies
opposite values. Both members belong to one fixed packet program and start
at one packet state.

Changing the latent equation to private-body = captured-X leaves each member
admitted alone but prevents their joint information from having a solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketRoundsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open MeTTaCalculus.OccurrenceCommits (Enabled)
open NativeResidualExample (tiny bit)
open FamilyInformationControls (locals shared privateTerm sharedTerm target valuation captured)

abbrev active := ContextualActivatedStep.target locals shared

def row (tied : Bool) : ContextualConditionalRows.Row locals shared [] () :=
  ⟨.schema privateTerm,if tied then [(observe privateTerm,observe (sharedTerm true))]
    else [(observe (sharedTerm true),observe (sharedTerm false))]⟩

def state (tied : Bool) : NativeState tiny Nat ([] : Ctx tiny) () :=
  { FamilyInformationControls.state with state :=
    { FamilyInformationControls.state.state with present := {7},rows := fun _ => row tied } }

def reader (tied : Bool) (port : Nat) (value : Bool) : LiveFiring (state tied) where
  rule := ⟨[],[bit (ContextualActivatedStep.source locals shared) value],[],[],[bit _ false]⟩
  selection := ⟨[],[7],[port]⟩
  outputs _ := bit active false
  patterns := []
  fuel := 0

abbrev readScope (port : Nat) : Nat :=
  ContextualActivationScopes.scopeAt (∅ : Finset Nat)
    (ContextualActivationScopes.readPort (⟨[],[7],[port]⟩ : Selection Nat) ⟨0,Nat.zero_lt_succ 0⟩)

theorem reader_information (tied : Bool) (port : Nat) (value : Bool) :
    FamilyInformation.memberInformation (reader tied port value) =
      [(observe (bit active value),observe (ContextualFreshening.termAt locals shared (readScope port) privateTerm))] ++
        if tied then
          [(observe (ContextualFreshening.termAt locals shared (readScope port) privateTerm),
            observe (ContextualFreshening.termAt locals shared (readScope port) (sharedTerm true)))]
        else
          [(observe (ContextualFreshening.termAt locals shared (readScope port) (sharedTerm true)),
            observe (ContextualFreshening.termAt locals shared (readScope port) (sharedTerm false)))] := by
  cases tied <;> rfl

theorem open_models (port : Nat) (value : Bool) :
    ContextualResidual.Models (valuation value) (FamilyInformation.memberInformation (reader false port value)) := by
  rw [reader_information]
  intro equation inside
  simp only [Bool.false_eq_true,if_false,List.mem_append,List.mem_singleton] at inside
  rcases inside with rfl | rfl <;> rfl

def tiedValuation (value : Bool) : Assignment active target.arity
  | .inl _ => bit target.arity value
  | .inr _ => bit target.arity value

theorem tied_models (port : Nat) (value : Bool) :
    ContextualResidual.Models (tiedValuation value) (FamilyInformation.memberInformation (reader true port value)) := by
  rw [reader_information]
  intro equation inside
  simp only [if_true,List.mem_append,List.mem_singleton] at inside
  rcases inside with rfl | rfl <;> rfl

private theorem reader_realized (tied : Bool) (port : Nat) (value : Bool) (fresh : port ≠ 7)
    (candidate : Assignment active target.arity)
    (model : ContextualResidual.Models candidate (FamilyInformation.memberInformation (reader tied port value))) :
    (reader tied port value).toNative.Realized := by
  apply (native_admits_iff (S := tiny) (reader tied port value).toNative).mpr
  refine ⟨⟨List.nodup_nil,List.nodup_singleton port,rfl,rfl,rfl⟩,?_,⟨target,candidate,model⟩,?_⟩
  · refine ⟨?_,?_,?_,?_,fun _ inside => by simp [Selection.commit] at inside⟩
    · show ([] : List Nat).toFinset ⊆ ({7} : Finset Nat)
      simp
    · show ([7] : List Nat).toFinset ⊆ ({7} : Finset Nat)
      simp
    · show Disjoint ([] : List Nat).toFinset [7].toFinset
      simp
    · show Disjoint [port].toFinset ({7} : Finset Nat)
      simpa using fresh
  · intro _ _ _
    exact ⟨fun _ inside => absurd inside List.not_mem_nil,fun _ inside => absurd inside List.not_mem_nil⟩

theorem open_realized (port : Nat) (value : Bool) (fresh : port ≠ 7) :
    (reader false port value).toNative.Realized := reader_realized false port value fresh (valuation value) (open_models port value)

theorem tied_realized (port : Nat) (value : Bool) (fresh : port ≠ 7) :
    (reader true port value).toNative.Realized := reader_realized true port value fresh (tiedValuation value) (tied_models port value)

def members (tied : Bool) : List (LiveFiring (state tied)) := [reader tied 0 false,reader tied 1 true]

theorem open_jointly : NativeIterated.Jointly (state false) (members false) := by
  refine ⟨target,captured,?_⟩
  intro firing inside
  simp only [members,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl
  · exact ⟨valuation false,open_models 0 false,FamilyInformationControls.valuation_agrees false⟩
  · exact ⟨valuation true,open_models 1 true,FamilyInformationControls.valuation_agrees true⟩

theorem open_clear : NativeIterated.FamilyClear (state false) (members false) where
  admitted firing inside := by
    simp only [members,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl
    · exact open_realized 0 false (by decide)
    · exact open_realized 1 true (by decide)
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro firing inside
    obtain rfl := List.mem_singleton.mp inside
    apply NativePacketRounds.clears_of_resources
    · simp [NativePacketRounds.ResourcesApart,reader]
    · exact open_jointly.joint List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals rfl
  jointly := open_jointly

abbrev actualNative := native (S := tiny) (O := Nat) (Γ := []) (sort := ())

theorem reader_shapes (tied : Bool) (index : Fin (members tied).length) :
    actualNative.Shapes (members tied)[index].toNative := by
  fin_cases index
  · exact ((native_admits_iff (S := tiny) (reader tied 0 false).toNative).mp
      (reader_realized tied 0 false (by decide) (if tied then tiedValuation false else valuation false)
        (by cases tied <;> first | exact open_models 0 false | exact tied_models 0 false))).1
  · exact ((native_admits_iff (S := tiny) (reader tied 1 true).toNative).mp
      (reader_realized tied 1 true (by decide) (if tied then tiedValuation true else valuation true)
        (by cases tied <;> first | exact open_models 1 true | exact tied_models 1 true))).1

theorem open_round : AnnotatedRuns.Round
    (NativePacketStep.packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ()))
    (NativePacketRounds.label (members false)) (NativePacketStep.configuration (state false) 0)
    (NativePacketRounds.image (members false)) :=
  NativePacketRounds.round_of_clear (by simp [members]) open_clear
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl)

theorem open_native_concurrent : ∃ last, NativeConcurrent.Concurrent (state false)
    ((members false) : Multiset (LiveFiring (state false))) last :=
  (NativePacketRounds.round_iff_concurrent (members false) (by simp [members]) (reader_shapes false)
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl)).mp open_round

theorem same_physical_read :
    (NativePacketRounds.member (members false) ⟨0,by decide⟩).selection.read = [.inl 7,.inr ()] ∧
      (NativePacketRounds.member (members false) ⟨1,by decide⟩).selection.read = [.inl 7,.inr ()] := ⟨rfl,rfl⟩

theorem actual_schema_is_retained : NativePacketRounds.label (members false) (.inl 7) =
    NativePacketStep.oldRow (state false) 0 7 := NativePacketRounds.label_old _ _ (by simp [state])

theorem actual_latent_equation_is_not_empty : (row false).obligations ≠ [] := by intro same; cases same

theorem captures_remain_symbolic : valuation false (.inr true) = generator target.arity () ∧
    valuation true (.inr false) = generator target.arity () := ⟨rfl,rfl⟩

theorem actual_native_every_order {order : List (LiveFiring (state false))} (permutes : order.Perm (members false)) :
    ∃ last, ∃ witness : NativeRoundExecution.Witness (state false) order last,
      witness.toRun.last = last ∧ witness.toRun.word.length = 2 ∧
        witness.toRun.word.map (fun event => event.2.selection) = order.map (fun event => event.selection) :=
  NativePacketRounds.native_every_order (members false) (by simp [members]) (reader_shapes false)
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl) open_round permutes

theorem tied_capture_value {V : Type} {next : V → MetaArity tiny} (candidate : Assignment active next)
    (port : Nat) (value : Bool)
    (model : ContextualResidual.Models candidate (FamilyInformation.memberInformation (reader true port value))) :
    candidate (.inr true) = bit next value := by
  rw [reader_information] at model
  have first := observe_injective (model _ List.mem_cons_self)
  have second := observe_injective (model _ (List.mem_cons_of_mem _ List.mem_cons_self))
  change bit next value = instantiate candidate
    (ContextualFreshening.termAt locals shared (readScope port) privateTerm) at first
  change instantiate candidate (ContextualFreshening.termAt locals shared (readScope port) privateTerm) =
    instantiate candidate (ContextualFreshening.termAt locals shared (readScope port) (sharedTerm true)) at second
  have opened : ContextualFreshening.termAt locals shared (readScope port) (sharedTerm true) =
      generator active (.inr true) :=
    instantiate_generator (ContextualFreshening.assignment locals shared (readScope port)) (.inr true)
  have sharedValue := (congrArg (fun term : Term (signature tiny active) ([] : Ctx tiny) () =>
    instantiate candidate term) opened).trans (instantiate_generator candidate (.inr true))
  exact (first.trans (second.trans sharedValue)).symm

theorem tied_not_jointly : ¬ NativeIterated.Jointly (state true) (members true) := by
  rintro ⟨future,_,each⟩
  obtain ⟨left,leftModel,leftAgrees⟩ := each (reader true 0 false) List.mem_cons_self
  obtain ⟨right,rightModel,rightAgrees⟩ := each (reader true 1 true) (List.mem_cons_of_mem _ List.mem_cons_self)
  have agree : left (.inr true) = right (.inr true) :=
    (instantiate_generator left (.inr true)).symm.trans
      ((congrFun (leftAgrees.trans rightAgrees.symm) true).trans (instantiate_generator right (.inr true)))
  have clash : bit future.arity false = bit future.arity true :=
    (tied_capture_value left 0 false leftModel).symm.trans (agree.trans (tied_capture_value right 1 true rightModel))
  cases clash

theorem tied_members_individually_admitted :
    (reader true 0 false).toNative.Realized ∧ (reader true 1 true).toNative.Realized :=
  ⟨tied_realized 0 false (by decide),tied_realized 1 true (by decide)⟩

theorem tied_no_round : ¬ AnnotatedRuns.Round
    (NativePacketStep.packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ()))
    (NativePacketRounds.label (members true)) (NativePacketStep.configuration (state true) 0)
    (NativePacketRounds.image (members true)) := by
  intro round
  exact tied_not_jointly (NativePacketRounds.clear_of_round (members true) (by simp [members]) (reader_shapes true)
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl) round).jointly

theorem tied_no_native_concurrent : ¬ ∃ last, NativeConcurrent.Concurrent (state true)
    ((members true) : Multiset (LiveFiring (state true))) last := by
  intro concurrent
  exact tied_no_round ((NativePacketRounds.round_iff_concurrent (members true) (by simp [members]) (reader_shapes true)
    (fun index => by fin_cases index <;> rfl) (fun index => by fin_cases index <;> rfl)).mpr concurrent)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.NativePacketRoundsControls
