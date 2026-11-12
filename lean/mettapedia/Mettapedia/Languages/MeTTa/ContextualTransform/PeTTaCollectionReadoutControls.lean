import Mettapedia.Languages.MeTTa.PeTTa.StreamingCollectionReadout
import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionReachability
import Lean.Elab.Tactic.Cbv

/-!
# Independent source models, isolated answers and capture controls

The source and runtime solve the same scoped equation in opposite directions.
Copying preserves each pair's internal sharing and separates the two answers.
An incorrect whole-bank renaming passes individual observations but fails the
joint one. A caller with an unallocated future key can capture a fresh copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCollectionReadoutControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS
open UnifyingConstraintPresentation
open OutputPlan.ConstraintAdmission

def x : Atom := Unifying.rename 0 (.var "x")
def y : Atom := Unifying.rename 0 (.var "y")
def pair (left right : Atom) : Atom := .expression [.symbol "pair",left,right]
def constraints : Destination.Equations := [(x,y)]
def reversed : Subst := [(Unifying.freshName 0 "y",x)]
def sourceModel : Destination.Environment :=
  Mettapedia.Logic.LP.Subst.single (Unifying.freshName 0 "x") (.var (Unifying.freshName 0 "y"))
def answer : Unifying.Answer := ⟨pair x x,reversed⟩
def bank : List Unifying.Answer := [answer,answer]
def rows : Streaming.CollectionReadout.SourceRows := [(constraints,sourceModel),(constraints,sourceModel)]
def program : SpaceSemantics.Program := {equations := [],declarations := []}

theorem actual_source_model : Destination.resolve constraints = some sourceModel := by
  simp [Destination.resolve,Destination.equations,Destination.encode,constraints,x,y,sourceModel,
    Unifying.rename,Unifying.freshName,Mettapedia.Logic.LP.unifyTotal,Mettapedia.Logic.LP.Subst.applyEqs]
  exact Mettapedia.Logic.LP.Subst.comp_id_left _

theorem runtime_represents_source : Represents constraints reversed := by
  intro model
  change Destination.Solves model [(x,y)] ↔ Destination.Solves model [(y,x)]
  simp only [Destination.Solves,List.mem_singleton,forall_eq]
  exact eq_comm

theorem runtime_binding_valid : Unifying.BindingRefines [] reversed := by
  have computed : Unifying.unify [] y x = .ok reversed := by decide +kernel
  obtain ⟨valid,refined,_⟩ := Unifying.unifyTerms_sound (Unifying.fuelFor [] y x) [] reversed y x
    (by simp [Unifying.Idempotent,Subst.lookup]) computed
  exact ⟨valid,refined⟩

theorem source_bank_models : Streaming.CollectionReadout.Models rows bank :=
  .cons ⟨runtime_represents_source,actual_source_model⟩
    (.cons ⟨runtime_represents_source,actual_source_model⟩ .nil)

theorem raw_representatives_differ :
    Streaming.CollectionReadout.sourceValues rows bank ≠
      bank.map (fun answer => Unifying.resolve answer.bindings answer.value) := by decide +kernel

theorem actual_joint_readout :
    VariantReadout.joint
        ((Collection.copyAnswers ∅ ((Streaming.CollectionReadout.sourceValues rows bank).map fun value => (value,[]))).map Prod.fst) =
      VariantReadout.joint (Unifying.copies 1 bank) := by
  apply Streaming.CollectionReadout.copied_bank_joint _ _ source_bank_models
  · intro packet present
    have same : packet = answer := by simpa only [bank,List.mem_cons,List.not_mem_nil,or_false,or_self] using present
    subst packet
    exact runtime_binding_valid.1
  · simp

def sharedScope : List Atom := bank.map fun answer => Unifying.rename 1 (Unifying.resolve answer.bindings answer.value)

theorem individual_checks_can_miss_cross_answer_aliasing :
    VariantReadout.each sharedScope = VariantReadout.each (Unifying.copies 1 bank) ∧
      VariantReadout.joint sharedScope ≠ VariantReadout.joint (Unifying.copies 1 bank) := by decide +kernel

def futureKey : String := Unifying.freshName 1 (Unifying.freshName 0 "x")
def badCaller : Subst := [(futureKey,.symbol "captured")]

theorem future_caller_key_changes_the_collection :
    Unifying.resolve badCaller (.expression (Unifying.copies 1 bank)) ≠
      .expression (Unifying.copies 1 bank) := by decide +kernel

theorem that_caller_violates_the_preallocation_invariant :
    ¬Unifying.SupportedBindings (Mettapedia.ScopedString.Before 1) badCaller := by
  intro supported
  have allocated := (supported (futureKey,.symbol "captured") (by simp [badCaller])).1
  exact Mettapedia.ScopedString.new_identity_is_fresh allocated (Unifying.freshName 0 "x") rfl

def closing : Streaming.State :=
  {world := {state := Effects.empty,uses := 1},agenda := [.collect 0 [] [] bank],nextBoundary := 1}

theorem bank_state_regions : Streaming.Regions.WellFormed closing :=
  ⟨⟨by decide,True.intro⟩,True.intro,True.intro⟩

theorem bank_state_refines : Streaming.BindingInvariant.stateRefines [] closing := by
  constructor
  · intro job present
    have same := List.mem_singleton.mp present
    subst job
    refine ⟨?_,by simp [Streaming.BindingInvariant.framesRefine],?_⟩
    · simp [Unifying.BindingRefines,Unifying.Idempotent,Unifying.Refines,Unifying.resolve,applySubst_nil,Subst.lookup]
    · intro packet present
      have same : packet = answer := by simpa only [bank,List.mem_cons,List.not_mem_nil,or_false,or_self] using present
      subst packet
      exact runtime_binding_valid
  · simp [closing]

theorem runtime_binding_supported : Unifying.SupportedBindings (Mettapedia.ScopedString.Before 1) reversed := by
  intro binding present
  have same := List.mem_singleton.mp present
  subst binding
  exact ⟨Mettapedia.ScopedString.new_identity_before_next 0 "y",ScopedSource.renamed_allocated 0 (.var "x")⟩

theorem bank_state_wellScoped : Streaming.ScopeInvariant.WellScoped closing := by
  refine ⟨⟨?_,by simp [closing]⟩,?_,by simp [closing]⟩
  · intro name value stored
    cases stored
  · intro job present
    have same := List.mem_singleton.mp present
    subst job
    refine ⟨by simp [Unifying.SupportedBindings],by simp [Streaming.ScopeInvariant.framesSupported],?_⟩
    intro packet present
    have same : packet = answer := by simpa only [bank,List.mem_cons,List.not_mem_nil,or_false,or_self] using present
    subst packet
    refine ⟨?_,runtime_binding_supported⟩
    change Unifying.Supported (Mettapedia.ScopedString.Before 1) (pair x x)
    simpa only [Unifying.Supported,ScopedSource.Allocated,pair,x,Unifying.rename,Unifying.rename.renameList] using
      ScopedSource.renamed_allocated 0 (.expression [.symbol "pair",.var "x",.var "x"])

theorem actual_closure_has_source_observations :
    ∃ reached,
      Streaming.step program closing = some reached ∧
      reached.world.state = closing.world.state ∧
      reached.world.uses = 3 ∧
      reached.agenda = [.execute ⟨.returned [⟨.expression (Unifying.copies 1 bank),[]⟩],[]⟩] ∧
      Unifying.resolve [] (.expression (Unifying.copies 1 bank)) = .expression (Unifying.copies 1 bank) ∧
      VariantReadout.joint
          ((Collection.copyAnswers (Streaming.CollectionReadout.callerNames [])
            ((Streaming.CollectionReadout.sourceValues rows bank).map fun value => (value,[]))).map Prod.fst) =
        VariantReadout.joint (Unifying.copies 1 bank) :=
  Streaming.CollectionReadout.actual_collection_return program closing 0 [] [] bank [] rows rfl
    bank_state_refines bank_state_wellScoped source_bank_models

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCollectionReadoutControls
