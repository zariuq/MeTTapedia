import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicQuery

/-!
# Public source answers reflect actual machine reachability

The invariant follows calls of the existing binder program, its returned
reply, the public pattern bind and the final return. In particular, a
finished public branch must have read a done reply of the machine. Failed
helper residuals cannot be counted as public results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicInvariant

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open PublicQuery (rows keys result site query frame)

local instance msigClosed : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "unused"

variable (helpers authored : List ProgramLayout.Rule) (D : Discipline MSig [] ())

abbrev Reach (call answer : MClosed) : Prop :=
  Relation.ReflTransGen (ProgramBinders.Rewrites (rows helpers authored).get) call answer

def CallReads (call : MClosed) (store : List (Constraint (keys helpers authored) [] ()))
    (term : Data (keys helpers authored) [] ()) : Prop :=
  ∀ value, Reads store term value → Reach helpers authored call value

def OutputReads (call : MClosed) (store : List (Constraint (keys helpers authored) [] ()))
    (term : Data (keys helpers authored) [] ()) : Prop :=
  ∀ value, Reads store term value → Reach helpers authored call (doneC value)

inductive BranchInvariant (call : MClosed) : Branch (keys helpers authored) [] () D.Ty → Prop
  | initial : BranchInvariant call ⟨[], .eval (query helpers authored call), [], []⟩
  | calling (store : List (Constraint (keys helpers authored) [] ())) (term : Data (keys helpers authored) [] ())
      (reads : CallReads helpers authored call store term) :
      BranchInvariant call ⟨store, .eval (.apply term), [frame helpers authored], []⟩
  | replied (store : List (Constraint (keys helpers authored) [] ())) (term : Data (keys helpers authored) [] ())
      (reads : CallReads helpers authored call store term) :
      BranchInvariant call ⟨store, .value term, [frame helpers authored], []⟩
  | returning (store : List (Constraint (keys helpers authored) [] ())) (term : Data (keys helpers authored) [] ())
      (reads : OutputReads helpers authored call store term) :
      BranchInvariant call ⟨store, .eval (.ret term), [], []⟩
  | finished (store : List (Constraint (keys helpers authored) [] ())) (term : Data (keys helpers authored) [] ())
      (reads : OutputReads helpers authored call store term) :
      BranchInvariant call ⟨store, .value term, [], []⟩

variable (supply : Nat → MClosed)

theorem move {call : MClosed} {world nextWorld : World (keys helpers authored) [] ()}
    {before : Branch (keys helpers authored) [] () D.Ty}
    {children : Multiset (Branch (keys helpers authored) [] () D.Ty)}
    (known : BranchInvariant helpers authored D call before)
    (moved : Move D (BinderCore.program (rows helpers authored)) supply world before nextWorld children) :
    ∀ child ∈ children, BranchInvariant helpers authored D call child := by
  cases known with
  | initial =>
      cases moved with
      | letStart =>
          intro child member
          rw [Multiset.mem_singleton.mp member]
          apply BranchInvariant.calling
          intro value read
          obtain ⟨X, family, assignment, _, equal⟩ := read
          rw [Rigid.instantiate_include] at equal
          have same := Rigid.include_injective family call value equal
          subst value
          exact .refl
  | calling store term readings =>
      cases moved with
      | apply =>
          intro child member
          obtain ⟨index, rfl⟩ := (BinderCore.mem_callBranches (rows helpers authored) D).mp
            (Multiset.mem_coe.mp member)
          apply BranchInvariant.calling
          intro value read
          obtain ⟨previous, earlier, rewritten⟩ := BinderCore.reads_backward (rows helpers authored) index read
          exact (readings previous earlier).tail ⟨index, rewritten⟩
      | unmatched =>
          intro child member
          rw [Multiset.mem_singleton.mp member]
          exact .replied store term readings
  | replied store term readings =>
      cases moved with
      | letBind =>
          intro child member
          rw [Multiset.mem_singleton.mp member]
          apply BranchInvariant.returning
          intro value read
          exact readings (doneC value)
            (PublicReadout.bind_reads_original store (result helpers authored) term
              (site helpers authored) world.scope value read)
  | returning store term readings =>
      cases moved with
      | ret =>
          intro child member
          rw [Multiset.mem_singleton.mp member]
          exact .finished store term readings
  | finished => cases moved

def Invariant (call : MClosed) (configuration : Config (keys helpers authored) [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches, BranchInvariant helpers authored D call branch

theorem initial (call : MClosed) :
    Invariant helpers authored D call (Config.initial (fun _ => 0) (query helpers authored call)) := by
  intro branch member
  rw [Multiset.mem_singleton.mp member]
  exact .initial

theorem step {call : MClosed} {before after : Config (keys helpers authored) [] () D.Ty}
    (known : Invariant helpers authored D call before)
    (moved : SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply before after) :
    Invariant helpers authored D call after := by
  cases moved with
  | move world nextWorld before rest children _ moved =>
      intro child member
      rcases Multiset.mem_add.mp member with made | kept
      · exact move helpers authored D supply (known before (Multiset.mem_cons_self _ _)) moved child made
      · exact known child (Multiset.mem_cons_of_mem kept)

theorem runs {call : MClosed} {after : Config (keys helpers authored) [] () D.Ty}
    (executed : Runs D (BinderCore.program (rows helpers authored)) supply
      (Config.initial (fun _ => 0) (query helpers authored call)) after) :
    Invariant helpers authored D call after := by
  induction executed with
  | refl => exact initial helpers authored D call
  | tail _ last ih => exact step helpers authored D supply ih last

theorem finished_read {call value : MClosed} {branch : Branch (keys helpers authored) [] () D.Ty}
    (known : BranchInvariant helpers authored D call branch)
    (finished : branch.Finished (D := D)) (read : value ∈ branch.answer (D := D)) :
    Reach helpers authored call (doneC value) := by
  cases known with
  | initial => obtain ⟨term, impossible, _⟩ := read; cases impossible
  | calling => obtain ⟨term, impossible, _⟩ := read; cases impossible
  | replied => cases finished.1
  | returning => obtain ⟨term, impossible, _⟩ := read; cases impossible
  | finished store term readings =>
      obtain ⟨actual, focus, read⟩ := read
      have same : term = actual := Focus.value.inj focus
      subst actual
      exact readings value read

theorem public_answer_reflected {call value : MClosed}
    {after : Config (keys helpers authored) [] () D.Ty}
    (executed : Runs D (BinderCore.program (rows helpers authored)) supply
      (Config.initial (fun _ => 0) (query helpers authored call)) after)
    (answered : HasAnswer (D := D) (rows helpers authored) after value) :
    Reach helpers authored call (doneC value) := by
  obtain ⟨branch, member, finished, read⟩ := answered
  exact finished_read helpers authored D (runs helpers authored D supply executed branch member) finished read

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicInvariant

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicInvariant.public_answer_reflected
