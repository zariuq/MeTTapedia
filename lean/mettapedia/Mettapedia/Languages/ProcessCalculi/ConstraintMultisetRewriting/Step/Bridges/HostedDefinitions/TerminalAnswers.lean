import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HeadSeparation

/-!
# A literal terminal head turns binder-core reachability into actual answers

Every equation is entered through the active head. Its right side retains
that head or uses the separate done head. A reached done reading therefore
has no matching equation and takes the source language's actual unmatched
move to a final answer. This concerns the selected finite program only.
It neither validates arbitrary done payloads nor proves interpretation of an
object machine; the compiler's operation correspondence supplies those laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open ProgramBinders (Rewrites)

local instance msigClosed : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "unused"

variable (rows : List (ProgramBinders.Equation MSig [] ()))

structure HeadSeparated (active done : String) : Prop where
  distinct : active ≠ done
  lhs : ∀ index : Fin rows.length, literalHead (rows.get index).lhs = some active
  rhs : ∀ index : Fin rows.length,
    literalHead (rows.get index).rhs = some active ∨ literalHead (rows.get index).rhs = some done

variable {D : Discipline MSig [] ()} {active done : String}
  (separated : HeadSeparated rows active done)
  (supply : Nat → MClosed)

def focusHead (focus : Focus (BinderCore.keys rows) [] () D.Ty) : Option String :=
  match focus with
  | .eval (.apply term) | .value term => literalHead term
  | _ => none

def HeadInvariant (configuration : Config (BinderCore.keys rows) [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches,
    focusHead rows branch.focus = some active ∨ focusHead rows branch.focus = some done

omit separated supply in
theorem heads_initial (call : MClosed)
    (head : closedHead call = some active ∨ closedHead call = some done) :
    HeadInvariant (D := D) rows (active := active) (done := done) (BinderCore.start rows call) := by
  intro branch member
  rw [Multiset.mem_singleton.mp member]
  change literalHead (Rigid.includeTerm (fam (BinderCore.keys rows)) call) = some active ∨
    literalHead (Rigid.includeTerm (fam (BinderCore.keys rows)) call) = some done
  simpa only [literalHead_include] using head

include separated

theorem heads_step {call : MClosed} {before after : Config (BinderCore.keys rows) [] () D.Ty}
    (shape : BinderCore.Invariant rows D call before)
    (heads : HeadInvariant (D := D) rows (active := active) (done := done) before)
    (step : SourceLanguage.Step D (BinderCore.program rows) supply before after) :
    HeadInvariant (D := D) rows (active := active) (done := done) after := by
  cases step with
  | move world nextWorld branch rest branches live moved =>
    obtain ⟨K, term, forms, _⟩ := shape branch (Multiset.mem_cons_self _ _)
    have oldHead := heads branch (Multiset.mem_cons_self _ _)
    intro child member
    rcases Multiset.mem_add.mp member with made | kept
    · rcases forms with rfl | rfl
      · cases moved with
        | apply =>
            obtain ⟨index, rfl⟩ := (BinderCore.mem_callBranches rows D).mp (Multiset.mem_coe.mp made)
            rcases separated.rhs index with activeHead | doneHead
            · exact .inl (literalHead_instantiate (BinderCore.stamp rows world.scope index) activeHead)
            · exact .inr (literalHead_instantiate (BinderCore.stamp rows world.scope index) doneHead)
        | unmatched =>
            rw [Multiset.mem_singleton.mp made]
            exact oldHead
      · cases moved
    · exact heads child (Multiset.mem_cons_of_mem kept)

theorem heads_runs {call : MClosed} (head : closedHead call = some active ∨ closedHead call = some done)
    {configuration : Config (BinderCore.keys rows) [] () D.Ty}
    (runs : Runs D (BinderCore.program rows) supply (BinderCore.start rows call) configuration) :
    HeadInvariant (D := D) rows (active := active) (done := done) configuration := by
  induction runs with
  | refl => exact heads_initial rows call head
  | tail previous step ih =>
      exact heads_step rows separated supply (BinderCore.invariant_runs rows D supply previous) ih step

omit supply in
theorem none_at_done {scope : Nat} {store : List (Constraint (BinderCore.keys rows) [] ())}
    {term : Data (BinderCore.keys rows) [] ()} (headed : literalHead term = some done) :
    ∀ equation ∈ (BinderCore.program rows (Ty := D.Ty)).equations,
      ¬ Solvable (store ++ [(instantiate (copyAt (BinderCore.keys rows) scope) equation.lhs, term)]) := by
  intro equation member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  rintro ⟨X, target, assignment, solved⟩
  have same := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
  change instantiate assignment
    (instantiate (copyAt (BinderCore.keys rows) scope) (instantiate (BinderCore.embedAt rows index) (rows.get index).lhs)) =
    instantiate assignment term at same
  rw [BinderCore.copy_embed] at same
  have left := literalHead_instantiate assignment
    (literalHead_instantiate (BinderCore.stamp rows scope index) (separated.lhs index))
  have right := literalHead_instantiate assignment headed
  rw [same, right] at left
  exact separated.distinct (Option.some.inj left).symm

def HasAnswer (configuration : Config (BinderCore.keys rows) [] () D.Ty) (answer : MClosed) : Prop :=
  ∃ branch ∈ configuration.branches, branch.Finished (D := D) ∧ answer ∈ branch.answer (D := D)

/-- The final-answer bridge needs the literal separation invariant, not merely
normality of one closed instance of a symbolic call. -/
theorem answers_iff (call answer : MClosed)
    (initialHead : closedHead call = some active ∨ closedHead call = some done)
    (answerHead : closedHead answer = some done) :
    Relation.ReflTransGen (Rewrites rows.get) call answer ↔
      ∃ configuration, Runs D (BinderCore.program rows) supply (BinderCore.start rows call) configuration ∧
        HasAnswer (D := D) rows configuration answer := by
  constructor
  · intro rewriting
    obtain ⟨configuration, path, branch, member, term, focus, frames, pending, _, read⟩ :=
      BinderCore.runs_forward rows D supply rewriting
    have head := heads_runs rows separated supply initialHead path branch member
    rw [focus] at head
    change literalHead term = some active ∨ literalHead term = some done at head
    have doneHead : literalHead term = some done := by
      rcases head with activeHead | doneHead
      · have wrong := literalHead_of_reads activeHead read
        rw [answerHead] at wrong
        exact (separated.distinct (Option.some.inj wrong).symm).elim
      · exact doneHead
    have live : Solvable branch.store := by
      obtain ⟨X, target, assignment, solved, _⟩ := read
      exact ⟨X, target, assignment, solved⟩
    obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
    rcases configuration with ⟨world, all⟩
    rcases branch with ⟨K, oldFocus, oldFrames, oldPending⟩
    simp only at focus frames pending split read live doneHead
    subst oldFocus oldFrames oldPending
    let result : Branch (BinderCore.keys rows) [] () D.Ty := ⟨K, .value term, [], []⟩
    exact ⟨⟨world, result ::ₘ rest⟩,
      path.tail (SourceLanguage.Step.of_eq split rfl live
        (.unmatched world K term [] [] (none_at_done (D := D) rows separated doneHead))),
      result, Multiset.mem_cons_self _ _, ⟨rfl, term, rfl⟩, term, rfl, read⟩
  · rintro ⟨configuration, runs, branch, member, _, term, focus, read⟩
    exact (BinderCore.execution_iff rows D supply call answer).mpr
      ⟨configuration, runs, branch, member, term, .inr focus, read⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions
