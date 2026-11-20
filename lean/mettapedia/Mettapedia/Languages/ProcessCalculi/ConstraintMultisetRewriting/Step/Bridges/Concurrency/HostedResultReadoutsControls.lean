import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedResultReadouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.CanonicalHistories

/-!
# A nonempty actual hosted return reads its actual scoped result

The control uses the existing ret rule and its real canonical firing. Its
matching information has an explicit solution; native admission and shape,
the guarded round and the hosted run are earned from that firing. The
actual returned alternative answers one, and refuses the different value two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedResultReadoutsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open RuleSyntax RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds
open NativeClosedReadings (closedArity)

abbrev N := mettaNodes
abbrev X := Frames.contextual MSig

def value : Term MSig [] () := csym "one"

def input {V : Type} (declaration : V → MetaArity MSig) : Term (signature MSig declaration) [] () :=
  altN N (evalN N (retN N (Rigid.includeTerm declaration value))) (emptyN N)

def output {V : Type} (declaration : V → MetaArity MSig) : Term (signature MSig declaration) [] () :=
  altN N (valueN N (Rigid.includeTerm declaration value)) (emptyN N)

def before : HostState MSig :=
  ⟨⟨Empty,closedArity MSig⟩,[],{0},fun _ => observe (input (closedArity MSig))⟩

def presented : Presented [] () before where
  term _ := input (closedArity MSig)
  label_eq _ := rfl

def program : CProgram MSig := {retRule N}

def member : Member [] () mkeys program :=
  ⟨retRule N,Set.mem_singleton _,placedRet N,⟨[0],[],[1]⟩,0⟩

def firing := member.hosted before
def takePattern : Observation MSig (unknownArity ([] : Ctx MSig) ()) :=
  observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))
def madePattern : Observation MSig (unknownArity ([] : Ctx MSig) ()) :=
  observe (altN N (valueN N (unk .datum)) (unk .stack))

theorem simple : Simple firing 0 1 takePattern madePattern := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def fill {V : Type} (declaration : V → MetaArity MSig) : Assignment (unknownArity [] ()) declaration
  | .stack => emptyN N
  | _ => Rigid.includeTerm declaration value

theorem fill_take {V : Type} (declaration : V → MetaArity MSig) :
    instantiateObservation (fill declaration) takePattern = observe (input declaration) := by
  change observe (instantiate (fill declaration)
    (altN N (evalN N (retN N (unk .datum))) (unk .stack))) = _
  rw [instantiate_altN,instantiate_evalN,instantiate_retN,
    instantiate_unk (B := ⟨V,declaration⟩) (fill declaration) .datum,
    instantiate_unk (B := ⟨V,declaration⟩) (fill declaration) .stack]
  rfl

theorem fill_made {V : Type} (declaration : V → MetaArity MSig) :
    instantiateObservation (fill declaration) madePattern = observe (output declaration) := by
  change observe (instantiate (fill declaration)
    (altN N (valueN N (unk .datum)) (unk .stack))) = _
  rw [instantiate_altN,instantiate_valueN,
    instantiate_unk (B := ⟨V,declaration⟩) (fill declaration) .datum,
    instantiate_unk (B := ⟨V,declaration⟩) (fill declaration) .stack]
  rfl

theorem input_natural {V W : Type} {source : V → MetaArity MSig} {target : W → MetaArity MSig}
    (candidate : Assignment source target) : instantiate candidate (input source) = input target := by
  unfold input
  rw [instantiate_altN,instantiate_evalN,instantiate_retN,Rigid.instantiate_include,
    HostedAnswerReadings.empty_node_natural]

theorem information_solution :
    ∃ candidate : Assignment ((Contextual.declarations MSig).target firing.ext).arity (closedArity MSig),
      X.Models (b := ⟨Empty,closedArity MSig⟩) candidate (firing.information X before) ∧
        instantiateObservation candidate (instantiateObservation firing.opening madePattern) =
          observe (output (closedArity MSig)) := by
  obtain ⟨candidate,model,made,_,_⟩ := simple_amalgamate simple
    (Contextual.canonical_fresh before _ _ _ _) (by decide : (0 : Nat) ∈ before.present)
    (B := ⟨Empty,closedArity MSig⟩)
    (generator (closedArity MSig)) (fill (closedArity MSig))
    (X.models_nil _) (X.models_nil _) (by
      exact (fill_take (closedArity MSig)).trans (instantiateObservation_identity (before.label 0)).symm)
  exact ⟨candidate,model,made.trans (fill_made _)⟩

theorem admitted : firing.Admits X before := by
  refine ⟨⟨Contextual.canonical_fresh before _ _ _ _,List.nodup_singleton _,List.nodup_singleton _,
    rfl,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · exact ⟨by decide,by decide,by decide,by decide,fun _ impossible => by cases impossible⟩
  · obtain ⟨candidate,model,_⟩ := information_solution
    exact ⟨⟨Empty,closedArity MSig⟩,candidate,model⟩
  · intro target candidate model
    exact ⟨(fun _ inside => by cases inside),(fun _ inside => by cases inside)⟩

def after := firing.result X before
def afterPresented : Presented [] () after :=
  resultPresented before presented member.member member.placed member.selection
def ledger := nextLedger ∅ member.selection

theorem after_present : 1 ∈ after.present := by
  rw [show after.present = insert 1 (before.present.erase 0) from simple_present simple]
  exact Finset.mem_insert_self _ _

theorem hosted_run : HostedRun before presented ∅ [member] after afterPresented ledger :=
  .cons member [] admitted (.nil _ _ _)

theorem native_realized : (member.live N before presented ∅).toNative.Realized :=
  (admits_iff N before presented ∅ member.member member.placed member.selection member.fuel).mp admitted

def members : List (Member [] () mkeys program) := [member]
noncomputable def lives := HostedPacketRounds.live N before presented ∅ members

theorem family_clear : NativeIterated.FamilyClear (state mkeys before presented ∅) lives where
  admitted firing inside := by
    obtain rfl := List.mem_singleton.mp inside
    exact native_realized
  pairwise := List.pairwise_singleton _ _
  jointly := by
    obtain ⟨target,candidate,model⟩ := NativeFiring.solvable_of_realized native_realized
    refine ⟨target,Assignment.compose candidate
      (ContextualSelectionViews.capturedTarget (state mkeys before presented ∅).locals before.frame.arity),?_⟩
    intro firing inside
    obtain rfl := List.mem_singleton.mp inside
    exact ⟨candidate,model,rfl⟩

theorem native_shapes (index : Fin lives.length) :
    (native (S := MSig) (O := Nat) (Γ := []) (sort := ())).Shapes lives[index].toNative := by
  have actual := family_clear.admitted lives[index] (List.getElem_mem ..)
  exact ((native_admits_iff lives[index].toNative).mp actual).1

theorem guarded_round :
    AnnotatedRuns.Round (NativePacketStep.packetAction (S := MSig) (O := Nat) (Γ := []) (sort := ()))
      (NativePacketRounds.label lives) (NativePacketStep.configuration (state mkeys before presented ∅) 0)
      (NativePacketGuardedRounds.image lives) :=
  NativePacketGuardedRounds.round_of_clear (by simp [lives,members,HostedPacketRounds.live]) family_clear

theorem source_answer : value ∈ stateAnswer N after 1 := by
  obtain ⟨candidate,model,made⟩ := information_solution
  refine ⟨⟨Empty,closedArity MSig⟩,candidate,model,?_⟩
  have afterLabel : after.label 1 = instantiateObservation firing.opening madePattern :=
    simple_label_made simple admitted.1
  exact (congrArg (instantiateObservation candidate) afterLabel).trans made

theorem answer_exact : stateAnswer N after 1 = {value} := by
  ext result
  constructor
  · rintro ⟨target,candidate,model,answered⟩
    have matched := (simple_restrict simple candidate model).2.2
    have old : instantiateObservation
        (Assignment.compose candidate ((Contextual.declarations MSig).weaken firing.ext)) (before.label 0) =
          observe (input target.arity) := by
      change observe (instantiate _ (input (closedArity MSig))) = _
      exact congrArg observe (input_natural _)
    have patEq := matched.trans (old.trans (fill_take target.arity).symm)
    have datum := CanonicalHistoryControls.retPattern_datum N patEq
    have afterLabel : after.label 1 = instantiateObservation firing.opening madePattern :=
      simple_label_made simple admitted.1
    have normalized := (instantiateObservation_comp firing.opening candidate madePattern).symm.trans
      ((congrArg (instantiateObservation candidate) afterLabel).symm.trans answered)
    change observe (instantiate (Assignment.compose candidate firing.opening)
      (altN N (valueN N (unk .datum)) (unk .stack))) = _ at normalized
    have term := observe_injective normalized
    let opened : Assignment (unknownArity ([] : Ctx MSig) ()) target.arity :=
      Assignment.compose candidate firing.opening
    change instantiate opened (altN N (valueN N (unk .datum)) (unk .stack)) = _ at term
    rw [instantiate_altN,instantiate_valueN,
      instantiate_unk (B := target) opened .datum,
      instantiate_unk (B := target) opened .stack] at term
    have found := vec1_inj (N.args_eq ((vec2_inj (N.args_eq term)).1))
    have same := datum.symm.trans found
    exact Set.mem_singleton_iff.mpr ((Rigid.include_injective target.arity value result same).symm)
  · intro present
    have same := Set.mem_singleton_iff.mp present
    subst result
    exact source_answer

theorem actual_scoped_answer :
    ScopedResultReadouts.StateReads (state mkeys before presented ∅)
      (HostedResultReadouts.scopedResult lives (by simp [lives,members,HostedPacketRounds.live]) guarded_round)
      1 (HostedAnswerReadings.answerPattern N value) :=
  (HostedResultReadouts.scoped_hosted_iff N before presented ∅ members (by simp [members]) native_shapes guarded_round
    (List.Perm.refl members) hosted_run 1 after_present value).mpr source_answer

theorem wrong_value_refused :
    ¬ ScopedResultReadouts.StateReads (state mkeys before presented ∅)
      (HostedResultReadouts.scopedResult lives (by simp [lives,members,HostedPacketRounds.live]) guarded_round)
      1 (HostedAnswerReadings.answerPattern N (csym "two")) := by
  intro read
  have shown := (HostedResultReadouts.scoped_hosted_iff N before presented ∅ members (by simp [members]) native_shapes guarded_round
    (List.Perm.refl members) hosted_run 1 after_present (csym "two")).mp read
  rw [answer_exact] at shown
  have different : (csym "two" : Term MSig [] ()) ≠ value := by decide
  exact different (Set.mem_singleton_iff.mp shown)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedResultReadoutsControls
