import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNativeRelation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierRuns

/-!
# Native representative frontiers compose with whole source configurations

Every history-class expansion is realized by a coverage-certified family of
actual native firings. Conversely, every supplied native expansion reflects
to the exact all-name expansion of the history controller. The runtime state
stores no history words. History and source representations are proof evidence
at the correspondence boundary.

The composed source theorem preserves partial answer bags. These controller
steps are complete expansions; checking coverage and scheduling their native
firings are separate executable contracts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)

abbrev FrontiersRelated := Frontier.Related (Related N P q)

theorem forward (plainP : PlainProgram P)
    {before after : FrontierConfig.TargetState} {current : State S}
    (paired : FrontiersRelated N P q before current) (moved : (FrontierNames.target P N q).Step before after) :
    ∃ next, (theory N P).Step current next ∧ FrontiersRelated N P q after next := by
  cases moved with
  | expand word rest retired unfinished =>
    obtain ⟨leaf, nativeRest, related, restRelated, shape⟩ := Multiset.rel_cons_left.mp paired.1
    rcases current with ⟨leaves, nativeRetired⟩
    change leaves = leaf ::ₘ nativeRest at shape
    subst leaves
    let chosen := expansion N P leaf
    refine ⟨_, .expand leaf nativeRest nativeRetired (valid_of_related N P q related)
      (fun finished => unfinished ((finished_iff N P q related).mpr finished)) chosen,
      (children_related N P q plainP related chosen).add restRelated,
      retired_related N P q plainP related chosen paired.2⟩

theorem backward (plainP : PlainProgram P)
    {before : FrontierConfig.TargetState} {current next : State S}
    (paired : FrontiersRelated N P q before current) (moved : (theory N P).Step current next) :
    ∃ after, (FrontierNames.target P N q).Step before after ∧ FrontiersRelated N P q after next := by
  cases moved with
  | expand leaf rest retired valid unfinished chosen =>
    obtain ⟨word, historyRest, related, restRelated, shape⟩ := Multiset.rel_cons_right.mp paired.1
    rcases before with ⟨leaves, historyRetired⟩
    change leaves = word ::ₘ historyRest at shape
    subst leaves
    refine ⟨_, Frontier.Unfold.expand word historyRest historyRetired
      (fun finished => unfinished ((finished_iff N P q related).mp finished)),
      (children_related N P q plainP related chosen).add restRelated,
      retired_related N P q plainP related chosen paired.2⟩

def correspondence (plainP : PlainProgram P) :
    OperationalCorrespondence (FrontierNames.target P N q) (theory N P) where
  related := FrontiersRelated N P q
  readStep paired moved := .inr (backward N P q plainP paired moved)
  forward paired moved := by
    obtain ⟨next, step, related⟩ := forward N P q plainP paired moved
    exact ⟨next, ⟨.cons ⟨step⟩ (.refl next)⟩, related⟩

def progress (plainP : PlainProgram P) :
    Progress.Certificate (correspondence N P q plainP).toOperationalReadback :=
  Progress.Certificate.ofReflection (backward N P q plainP)

theorem positive_forward (plainP : PlainProgram P)
    {before after : FrontierConfig.TargetState} {current : State S}
    (paired : FrontiersRelated N P q before current) (moved : (FrontierNames.target P N q).Step before after) :
    ∃ next, ∃ path : ExecutionPath (theory N P) current next,
      0 < path.length ∧ FrontiersRelated N P q after next := by
  obtain ⟨next, step, related⟩ := forward N P q plainP paired moved
  exact ⟨next, .cons ⟨step⟩ (.refl next), by change 0 < 1; decide, related⟩

theorem normalization_iff (plainP : PlainProgram P) {before : FrontierConfig.TargetState} {current : State S}
    (paired : FrontiersRelated N P q before current) :
    Acc (fun after origin => (FrontierNames.target P N q).Step origin after) before ↔
      Acc (fun next state => (theory N P).Step state next) current :=
  Progress.normalization_iff (correspondence N P q plainP) (progress N P q plainP)
    (positive_forward N P q plainP) paired

theorem answers_eq {before : FrontierConfig.TargetState} {current : State S}
    (paired : FrontiersRelated N P q before current) :
    Frontier.answers (FinishedClass N P q) (classAnswer N P q) before = answers N current :=
  Frontier.answers_eq (R := Related N P q)
    (leftFinished := FinishedClass N P q)
    (rightFinished := fun leaf => StateFinished N leaf.state leaf.active)
    (finished_iff N P q) (classAnswer N P q)
    (fun (leaf : Leaf S) => stateAnswer N leaf.state leaf.active) (answer_eq N P q) paired

def initialLeaf : Leaf S := ⟨start N P q, P.equations.length⟩
def initialState : State S := ⟨{initialLeaf N P q}, 0⟩

theorem initial_related (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    FrontiersRelated N P q ⟨{[]}, 0⟩ (initialState N P q) := by
  have leaf : Related N P q [] (initialLeaf N P q) :=
    ⟨⟨_, HostedEvents.initial spaces plainQ unopened⟩, .nil _ _⟩
  exact ⟨Multiset.Rel.cons leaf Multiset.Rel.zero, Multiset.Rel.zero⟩

/-- The two existing correspondence objects compose through the SAME history controller. -/
def sourceCorrespondence (supply : Nat → Term S Γ star) (plainP : PlainProgram P) :
    OperationalCorrespondence (FrontierConfig.source P supply) (theory N P) :=
  (FrontierConfig.correspondence P N q supply plainP).comp (correspondence N P q plainP)

theorem source_initial_related (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (supply : Nat → Term S Γ star) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    (sourceCorrespondence N P q supply plainP).related (Config.initial spaces q) (initialState N P q) :=
  ⟨⟨{[]}, 0⟩, FrontierConfig.initial P N q spaces plainQ unopened, initial_related N P q spaces plainQ unopened⟩

theorem source_answers_eq (supply : Nat → Term S Γ star) (plainP : PlainProgram P)
    {before : Config κ Γ star D.Ty} {current : State S}
    (paired : (sourceCorrespondence N P q supply plainP).related before current) :
    before.answers (D := D) = answers N current := by
  obtain ⟨history, sourceRelated, nativeRelated⟩ := paired
  exact (FrontierConfig.answers_eq P N q sourceRelated).trans (answers_eq N P q nativeRelated)

theorem source_prefixes_iff (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (supply : Nat → Term S Γ star) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (post : Multiset (Set (Term S Γ star)) → Prop) :
    (∃ after, Runs D P supply (Config.initial spaces q) after ∧ post (after.answers (D := D))) ↔
      ∃ next, (theory N P).MultiStep (initialState N P q) next ∧ post (answers N next) := by
  have compared := (sourceCorrespondence N P q supply plainP).reachable_iff
    (fun configuration => post (configuration.answers (D := D)))
    (fun state => post (answers N state))
    (fun related => (source_answers_eq N P q supply plainP related) ▸ Iff.rfl)
    (source_initial_related N P q spaces supply plainP plainQ unopened)
  constructor
  · rintro ⟨after, path, observed⟩
    exact compared.mp ⟨after, (FrontierConfig.source_runs_iff P supply).mpr path, observed⟩
  · rintro ⟨next, path, observed⟩
    obtain ⟨after, sourcePath, sourceObserved⟩ := compared.mpr ⟨next, path, observed⟩
    exact ⟨after, (FrontierConfig.source_runs_iff P supply).mp sourcePath, sourceObserved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.correspondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.sourceCorrespondence
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.source_prefixes_iff
