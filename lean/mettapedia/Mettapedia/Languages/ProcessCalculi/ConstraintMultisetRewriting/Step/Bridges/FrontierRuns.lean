import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierConfig
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Progress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.StepAlone
import Mettapedia.GSLT.Meredith.GSLT

/-!
# Whole-configuration runs, partial answer bags and frontier progress

Every reached source configuration has a reachable native-history frontier
with the same bag of sets of closed answers. Every supplied target controller
prefix reflects to an actual source prefix. Failure retirement is an explicit
controller step, so no source deletion is erased by this correspondence.

The prefix readout also agrees with the independent `StepAlone.partial_bag`
theorem. The two constructions are not claimed to choose literally the same
history words. Their common observation is the actual partial answer bag.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star} (P : SourceLanguage.Program κ Γ star D.Ty)
  (N : Nodes S Γ star) (q : Comp κ Γ star D.Ty)
  (supply : Nat → Term S Γ star)

theorem source_runs_iff {before after : Config κ Γ star D.Ty} :
    (source P supply).MultiStep before after ↔ Runs D P supply before after :=
  Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen (source P supply) before after

theorem runs_forward (plainP : PlainProgram P) {before after : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) (runs : Runs D P supply before after) :
    ∃ next, (target P N q).MultiStep current next ∧ Represents P N q after next :=
  (correspondence P N q supply plainP).liftMultiStep represented ((source_runs_iff P supply).mpr runs)

theorem runs_reflected (plainP : PlainProgram P) {before : Config κ Γ star D.Ty} {current next : TargetState}
    (represented : Represents P N q before current) (runs : (target P N q).MultiStep current next) :
    ∃ after, Runs D P supply before after ∧ Represents P N q after next := by
  obtain ⟨after, path, related⟩ :=
    (correspondence P N q supply plainP).toOperationalReadback.reflectMultiStep represented runs
  exact ⟨after, (source_runs_iff P supply).mp path, related⟩

def progress (plainP : PlainProgram P) :
    Progress.Certificate (correspondence P N q supply plainP).toOperationalReadback :=
  Progress.Certificate.ofReflection (backward P N q supply plainP)

theorem positive_forward (plainP : PlainProgram P)
    {before after : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) (moved : SourceLanguage.Step D P supply before after) :
    ∃ next, ∃ path : ExecutionPath (target P N q) current next,
      0 < path.length ∧ Represents P N q after next := by
  obtain ⟨next, stepped, related⟩ := forward P N q supply plainP represented moved
  exact ⟨next, .cons ⟨stepped⟩ (.refl next), by change 0 < 1; decide, related⟩

theorem normalization_iff (plainP : PlainProgram P) {before : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) :
    Acc (fun after origin => SourceLanguage.Step D P supply origin after) before ↔
      Acc (fun next state => (target P N q).Step state next) current :=
  Progress.normalization_iff (correspondence P N q supply plainP) (progress P N q supply plainP)
    (positive_forward P N q supply plainP) represented

theorem terminal_iff (plainP : PlainProgram P) {before : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) :
    (¬ ∃ after, SourceLanguage.Step D P supply before after) ↔
      ¬ ∃ next, (target P N q).Step current next := by
  constructor
  · rintro stopped ⟨next, moved⟩
    obtain ⟨after, sourceStep, _⟩ := backward P N q supply plainP represented moved
    exact stopped ⟨after, sourceStep⟩
  · rintro stopped ⟨after, moved⟩
    obtain ⟨next, targetStep, _⟩ := forward P N q supply plainP represented moved
    exact stopped ⟨next, targetStep⟩

theorem reachable_answers_iff (plainP : PlainProgram P)
    (post : Multiset (Set (Term S Γ star)) → Prop)
    {before : Config κ Γ star D.Ty} {current : TargetState}
    (represented : Represents P N q before current) :
    (∃ after, Runs D P supply before after ∧ post (after.answers (D := D))) ↔
      ∃ next, (target P N q).MultiStep current next ∧
        post (Frontier.answers (FinishedClass N P q) (classAnswer N P q) next) := by
  constructor
  · rintro ⟨after, runs, observed⟩
    obtain ⟨next, path, paired⟩ := runs_forward P N q supply plainP represented runs
    exact ⟨next, path, (answers_eq P N q paired) ▸ observed⟩
  · rintro ⟨next, path, observed⟩
    obtain ⟨after, runs, paired⟩ := runs_reflected P N q supply plainP represented path
    exact ⟨after, runs, (answers_eq P N q paired).symm ▸ observed⟩

/-- The independent prefix-bag theorem agrees with a frontier that the target controller
actually reaches. No equality of the chosen word representations is assumed. -/
theorem partial_bag_realized (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {configuration : Config κ Γ star D.Ty} (runs : Runs D P supply (Config.initial spaces q) configuration) :
    ∃ frontier : TargetState, (target P N q).MultiStep ⟨{[]}, 0⟩ frontier ∧
      Represents P N q configuration frontier ∧
      ∃ words : Multiset (List RuleName), words.Nodup ∧
        (∀ word ∈ words, ∃ state active, NamedFrom N P q word state active) ∧
        Frontier.answers (FinishedClass N P q) (classAnswer N P q) frontier =
          (words.filter (FinishedClass N P q)).map (classAnswer N P q) := by
  obtain ⟨frontier, reached, paired⟩ :=
    runs_forward P N q supply plainP (initial P N q spaces plainQ unopened) runs
  obtain ⟨words, distinct, histories, observed⟩ :=
    StepAlone.partial_bag N spaces q plainP plainQ unopened runs
  exact ⟨frontier, reached, paired, words, distinct, histories,
    (answers_eq P N q paired).symm.trans observed⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.runs_reflected
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.normalization_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.reachable_answers_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierConfig.partial_bag_realized
