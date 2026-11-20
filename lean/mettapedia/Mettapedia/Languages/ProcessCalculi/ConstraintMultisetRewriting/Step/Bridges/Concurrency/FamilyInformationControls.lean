import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeRoundExecution

/-!
# Shared names and distinct private copies in actual native information

Two actual native makers tell opposite values of their own activation local
and both tell the shared equation X = Y. Their joint model leaves X and Y as
one symbolic target name. Identifying the two private copies instead makes
the same information inconsistent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.FamilyInformationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidualExample (tiny bit)
open FamilyInformation

def locals : Unit → MetaArity tiny := fun _ => ([], ())
def shared : Bool → MetaArity tiny := fun _ => ([], ())

def state : NativeState tiny Nat ([] : Ctx tiny) () :=
  ⟨Unit,inferInstance,locals,
    { Names := Bool
      equality := inferInstance
      declarations := shared
      occupied := ∅
      equations := []
      present := ∅
      rows := fun _ => ContextualConditionalRows.ofStored locals shared (.shared (generator shared true)) }⟩

def privateTerm : Term (signature tiny (ContextualActivatedStep.source locals shared)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.source locals shared) (.inl ())

def sharedTerm (name : Bool) : Term (signature tiny (ContextualActivatedStep.source locals shared)) ([] : Ctx tiny) () :=
  generator (ContextualActivatedStep.source locals shared) (.inr name)

def maker (port : Nat) (value : Bool) : LiveFiring state where
  rule := ⟨[],[],[(privateTerm,bit _ value),(sharedTerm true,sharedTerm false)],[],[bit _ false]⟩
  selection := ⟨[],[],[port]⟩
  outputs _ := bit (ContextualActivatedStep.target locals shared) false
  patterns := []
  fuel := 0

abbrev scope (port : Nat) : Nat :=
  ContextualActivationScopes.scopeAt (∅ : Finset Nat)
    (ContextualActivationScopes.rulePort (⟨[],[],[port]⟩ : Selection Nat))

theorem maker_information (port : Nat) (value : Bool) :
    memberInformation (maker port value) =
      [(observe (ContextualFreshening.termAt locals shared (scope port) privateTerm),
        observe (bit (ContextualActivatedStep.target locals shared) value)),
       (observe (ContextualFreshening.termAt locals shared (scope port) (sharedTerm true)),
        observe (ContextualFreshening.termAt locals shared (scope port) (sharedTerm false)))] := rfl

theorem opened_private (port : Nat) :
    ContextualFreshening.termAt locals shared (scope port) privateTerm =
      generator (ContextualActivatedStep.target locals shared) (.inl (ScopedVar.at (scope port) ())) :=
  instantiate_generator (ContextualFreshening.assignment locals shared (scope port)) (.inl ())

theorem opened_shared (port : Nat) (name : Bool) :
    ContextualFreshening.termAt locals shared (scope port) (sharedTerm name) =
      generator (ContextualActivatedStep.target locals shared) (.inr name) :=
  instantiate_generator (ContextualFreshening.assignment locals shared (scope port)) (.inr name)

theorem evaluate_private {V : Type} {next : V → MetaArity tiny}
    (candidate : Assignment (ContextualActivatedStep.target locals shared) next) (port : Nat) :
    instantiate candidate (ContextualFreshening.termAt locals shared (scope port) privateTerm) =
      candidate (.inl (ScopedVar.at (scope port) ())) :=
  (congrArg (fun term : Term (signature tiny (ContextualActivatedStep.target locals shared)) ([] : Ctx tiny) () =>
    instantiate candidate term) (opened_private port)).trans
      (instantiate_generator candidate (.inl (ScopedVar.at (scope port) ())))

theorem evaluate_shared {V : Type} {next : V → MetaArity tiny}
    (candidate : Assignment (ContextualActivatedStep.target locals shared) next) (port : Nat) (name : Bool) :
    instantiate candidate (ContextualFreshening.termAt locals shared (scope port) (sharedTerm name)) =
      candidate (.inr name) :=
  (congrArg (fun term : Term (signature tiny (ContextualActivatedStep.target locals shared)) ([] : Ctx tiny) () =>
    instantiate candidate term) (opened_shared port name)).trans (instantiate_generator candidate (.inr name))

theorem models_maker {V : Type} {next : V → MetaArity tiny}
    (candidate : Assignment (ContextualActivatedStep.target locals shared) next) (port : Nat) (value : Bool) :
    ContextualResidual.Models candidate (memberInformation (maker port value)) ↔
      candidate (.inl (ScopedVar.at (scope port) ())) = bit next value ∧
        candidate (.inr true) = candidate (.inr false) := by
  rw [maker_information]
  constructor
  · intro solved
    have first := observe_injective (solved _ List.mem_cons_self)
    have second := observe_injective (solved _ (List.mem_cons_of_mem _ List.mem_cons_self))
    exact ⟨(evaluate_private candidate port).symm.trans first,
      (evaluate_shared candidate port true).symm.trans (second.trans (evaluate_shared candidate port false))⟩
  · rintro ⟨privateValue,sharedValue⟩ equation present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · change observe (instantiate candidate (ContextualFreshening.termAt locals shared (scope port) privateTerm)) =
        observe (bit next value)
      exact congrArg observe ((evaluate_private candidate port).trans privateValue)
    · change observe (instantiate candidate (ContextualFreshening.termAt locals shared (scope port) (sharedTerm true))) =
        observe (instantiate candidate (ContextualFreshening.termAt locals shared (scope port) (sharedTerm false)))
      exact congrArg observe ((evaluate_shared candidate port true).trans
        (sharedValue.trans (evaluate_shared candidate port false).symm))

def target : Frames.Frame tiny := ⟨Unit,fun _ => ([], ())⟩

def valuation (value : Bool) : Assignment (ContextualActivatedStep.target locals shared) target.arity
  | .inl _ => bit target.arity value
  | .inr _ => generator target.arity ()

def captured : Assignment shared target.arity := fun _ => generator target.arity ()

theorem valuation_agrees (value : Bool) :
    Assignment.compose (valuation value) (ContextualSelectionViews.capturedTarget locals shared) = captured := by
  funext name
  exact instantiate_generator (valuation value) (.inr name)

theorem valuation_models (port : Nat) (value : Bool) :
    ContextualResidual.Models (valuation value) (memberInformation (maker port value)) :=
  (models_maker (valuation value) port value).mpr ⟨rfl,rfl⟩

theorem maker_realized (port : Nat) (value : Bool) : (maker port value).toNative.Realized := by
  apply (native_admits_iff (maker port value).toNative).mpr
  refine ⟨⟨List.nodup_nil,List.nodup_singleton port,rfl,rfl,rfl⟩,?_,
    ⟨target,valuation value,valuation_models port value⟩,?_⟩
  · refine ⟨?_,?_,?_,?_,fun _ present => by simp [Selection.commit] at present⟩
    · show ([] : List Nat).toFinset ⊆ (∅ : Finset Nat)
      simp
    · show ([] : List Nat).toFinset ⊆ (∅ : Finset Nat)
      simp
    · show Disjoint ([] : List Nat).toFinset ([] : List Nat).toFinset
      simp
    · show Disjoint [port].toFinset (∅ : Finset Nat)
      simp
  · intro b candidate _
    exact ⟨fun _ present => absurd present List.not_mem_nil,
      fun _ present => absurd present List.not_mem_nil⟩

def first : LiveFiring state := maker 0 false
def second : LiveFiring state := maker 1 true
def members : List (LiveFiring state) := [first,second]

theorem jointly : NativeIterated.Jointly state members := by
  refine ⟨target,captured,fun firing present => ?_⟩
  simp only [members,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  · exact ⟨valuation false,valuation_models 0 false,valuation_agrees false⟩
  · exact ⟨valuation true,valuation_models 1 true,valuation_agrees true⟩

theorem common_problem_solvable :
    (Frames.contextual tiny).Solvable (a := familyFrame state members.length) (information state members) :=
  (jointly_iff_solvable state members).mp jointly

theorem maker_clear (left right : Nat) (leftValue rightValue : Bool) (different : left ≠ right) :
    Clear (maker left leftValue) (maker right rightValue).selection
      (maker right rightValue).rule (maker right rightValue).outputs where
  takes := by simp [maker]
  ports := by simp [maker,different]
  keeps := by simp [maker]
  consistent := ⟨target,⟨⟨valuation leftValue,valuation rightValue,
    valuation_models left leftValue,valuation_models right rightValue,
    (valuation_agrees leftValue).trans (valuation_agrees rightValue).symm⟩⟩⟩
  blindTakes _ _ _ present := absurd present List.not_mem_nil
  blindOutputs _ _ _ _ :=
    ⟨fun _ present => absurd present List.not_mem_nil,
      fun _ present => absurd present List.not_mem_nil⟩

theorem clears : NativeIterated.Clears first second :=
  ⟨maker_clear 0 1 false true (by decide),maker_clear 1 0 true false (by decide)⟩

theorem clear_family : NativeIterated.FamilyClear state members where
  admitted firing present := by
    simp only [members,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    · exact maker_realized 0 false
    · exact maker_realized 1 true
  pairwise := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_singleton _ _⟩
    intro firing present
    rw [List.mem_singleton] at present
    subst firing
    exact clears
  jointly := jointly

theorem actual_every_order {order : List (LiveFiring state)} (permutes : order.Perm members) :
    ∃ last, NativeIterated.Sequential state order last :=
  NativeIterated.every_order_admitted clear_family permutes

theorem same_raw_scope : scope 0 = scope 1 := rfl

theorem conflated_private_information_impossible {b : Frames.Frame tiny}
    (candidate : Assignment (ContextualActivatedStep.target locals shared) b.arity)
    (left : ContextualResidual.Models candidate (memberInformation first))
    (right : ContextualResidual.Models candidate (memberInformation second)) : False := by
  have leftValue := ((models_maker candidate 0 false).mp left).1
  have rightValue := ((models_maker candidate 1 true).mp right).1
  rw [same_raw_scope] at leftValue
  have clash := leftValue.symm.trans rightValue
  unfold bit at clash
  cases clash

theorem pairwise_without_joint_still_refused :
    ¬ (Frames.contextual tiny).Solvable
      (a := familyFrame NativeIteratedControls.pair NativeIteratedControls.tellers.length)
      (information NativeIteratedControls.pair NativeIteratedControls.tellers) := by
  intro solved
  exact NativeIteratedControls.tellers_not_jointly
    ((jointly_iff_solvable NativeIteratedControls.pair NativeIteratedControls.tellers).mpr solved)

def generative : LiveFiring state where
  rule := ⟨[],[],[(sharedTerm true,sharedTerm false)],[],[privateTerm]⟩
  selection := ⟨[],[],[3]⟩
  outputs _ := ContextualFreshening.termAt locals shared (scope 3) privateTerm
  patterns := []
  fuel := 0

theorem generative_models (value : Bool) :
    ContextualResidual.Models (valuation value) (memberInformation generative) := by
  intro equation present
  change equation ∈ [(observe (ContextualFreshening.termAt locals shared (scope 3) (sharedTerm true)),
    observe (ContextualFreshening.termAt locals shared (scope 3) (sharedTerm false)))] at present
  obtain rfl := List.mem_singleton.mp present
  change observe (instantiate (valuation value)
      (ContextualFreshening.termAt locals shared (scope 3) (sharedTerm true))) =
    observe (instantiate (valuation value)
      (ContextualFreshening.termAt locals shared (scope 3) (sharedTerm false)))
  exact congrArg observe ((evaluate_shared (valuation value) 3 true).trans
    (evaluate_shared (valuation value) 3 false).symm)

def duplicateSolutions : SolutionData state [generative,generative] target where
  shared := captured
  member index := valuation (index.val == 1)
  agrees index := valuation_agrees (index.val == 1)
  models index := by
    have member : ([generative,generative] : List (LiveFiring state))[index] = generative := by
      fin_cases index <;> rfl
    rw [member]
    exact generative_models (index.val == 1)

theorem duplicate_information_solved :
    ContextualResidual.Models (assemble duplicateSolutions) (information state [generative,generative]) :=
  assemble_models duplicateSolutions

theorem duplicate_private_values :
    assemble duplicateSolutions (.inl (⟨0,by decide⟩,ScopedVar.at (scope 3) ())) = bit target.arity false ∧
      assemble duplicateSolutions (.inl (⟨1,by decide⟩,ScopedVar.at (scope 3) ())) = bit target.arity true :=
  ⟨rfl,rfl⟩

theorem duplicate_outputs_differ :
    instantiate (duplicateSolutions.member ⟨0,by decide⟩) (generative.outputs 3) ≠
      instantiate (duplicateSolutions.member ⟨1,by decide⟩) (generative.outputs 3) := by
  change instantiate (valuation false) (ContextualFreshening.termAt locals shared (scope 3) privateTerm) ≠
    instantiate (valuation true) (ContextualFreshening.termAt locals shared (scope 3) privateTerm)
  rw [evaluate_private,evaluate_private]
  intro clash
  cases clash

theorem duplicate_not_clear : ¬ NativeIterated.Clears generative generative := by
  intro clear
  have ports : Disjoint ([3] : List Nat).toFinset [3].toFinset := clear.1.ports
  exact Finset.disjoint_left.mp ports (show 3 ∈ ([3] : List Nat).toFinset by simp)
    (show 3 ∈ ([3] : List Nat).toFinset by simp)

def dead : NativeState tiny Nat ([] : Ctx tiny) () :=
  { state with state := { state.state with equations := [(observe (bit shared false),observe (bit shared true))] } }

theorem dead_knowledge_unsolvable :
    ¬ (Frames.contextual tiny).Solvable (a := ⟨dead.state.Names,dead.state.declarations⟩) dead.state.equations := by
  rintro ⟨_,candidate,solved⟩
  have clash := observe_injective (solved _ List.mem_cons_self)
  change bit _ false = bit _ true at clash
  cases clash

theorem empty_family_is_still_jointly : NativeIterated.Jointly dead [] :=
  ⟨target,captured,fun _ present => absurd present List.not_mem_nil⟩

theorem empty_information_is_empty : information dead [] = [] := rfl

theorem empty_information_solvable :
    (Frames.contextual tiny).Solvable (a := familyFrame dead 0) (information dead []) :=
  (jointly_iff_solvable dead []).mp empty_family_is_still_jointly

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.FamilyInformationControls
