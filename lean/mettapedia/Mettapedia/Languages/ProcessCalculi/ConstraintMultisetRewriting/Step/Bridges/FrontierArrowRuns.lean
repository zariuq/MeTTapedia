import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierArrowConfig
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierRuns

/-!
# Complete arrow frontiers, partial answers and progress

The correspondence preserves the bag of closed-reading sets at every reached
prefix. A completed negative bind is one controller step corresponding to one
source step. Its lack of a live native child is not hidden administrative
divergence. All source hygiene premises are obtained from scoped programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S} {D : Discipline S Γ star}
  (N : Nodes S Γ star) (P : SourceLanguage.Program κ Γ star D.Ty)
  (supply : Nat → Term S Γ star) (spaces : Term S Γ star → Multiset (Row κ Γ star))
  (q : Comp κ Γ star D.Ty)

def initialLeaf : Leaf S := ⟨start N P q, P.equations.length⟩
def initialState : State S := ⟨{initialLeaf N P q}, 0⟩

def answers (state : State S) : Multiset (Set (Term S Γ star)) :=
  Frontier.answers (fun leaf => StateFinished N leaf.state leaf.active)
    (fun leaf => stateAnswer N leaf.state leaf.active) state

theorem initial_related (arrowQ : ArrowComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Representation N P supply spaces q (Config.initial spaces q) (initialState N P q) := by
  refine ⟨.refl, ?_, ?_⟩
  · have live : Solvable (Hosting.initialBranch q).store := initial_live
    change Multiset.Rel (LeafRep N P ⟨0, 0, spaces⟩)
      (({Hosting.initialBranch q} : Multiset (Branch κ Γ star D.Ty)).filter fun branch => Solvable branch.store)
      {initialLeaf N P q}
    simp only [Multiset.filter_singleton, if_pos live]
    apply Multiset.Rel.cons _ Multiset.Rel.zero
    exact ⟨start_represents N P q unopened, trivial, .inl ⟨q, rfl, arrowQ⟩⟩
  · intro leaf absent
    exact (Multiset.notMem_zero _ absent).elim

theorem answers_eq {configuration : Config κ Γ star D.Ty} {frontier : State S}
    (represented : Representation N P supply spaces q configuration frontier) :
    configuration.answers (D := D) = answers N frontier := by
  let R := fun (branch : Branch κ Γ star D.Ty) (leaf : Leaf S) =>
    LeafRep N P configuration.world branch leaf ∧ Solvable branch.store
  have paired : Multiset.Rel R
      (configuration.branches.filter fun branch => Solvable branch.store) frontier.leaves :=
    represented.leaves.mono (fun branch member leaf _ rep => ⟨rep, (Multiset.mem_filter.mp member).2⟩)
  have compared := Frontier.answers_eq (R := R)
    (leftFinished := fun branch => branch.Finished (D := D))
    (rightFinished := fun leaf => StateFinished N leaf.state leaf.active)
    (fun pair => ⟨fun fin => (Hosting.finished_iff N pair.1.1).mp ⟨fin, pair.2⟩,
      fun fin => ((Hosting.finished_iff N pair.1.1).mpr fin).1⟩)
    (fun branch => branch.answer (D := D)) (fun leaf => stateAnswer N leaf.state leaf.active)
    (fun pair finished => (Hosting.answer_eq N pair.1.1 finished).symm)
    (show Frontier.Related R
      ⟨configuration.branches.filter (fun branch => Solvable branch.store), 0⟩
      ⟨frontier.leaves, 0⟩ from ⟨paired, .zero⟩)
  have split : configuration.branches.filter (fun branch => branch.Finished (D := D) ∧ Solvable branch.store) =
      (configuration.branches.filter fun branch => Solvable branch.store).filter
        (fun branch => branch.Finished (D := D)) := by rw [Multiset.filter_filter]
  change Multiset.map _ (configuration.branches.filter _) = _
  rw [split]
  exact compared

variable
  (equations : ∀ e ∈ P.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs)
  {qsite : κ.Site} (qScoped : q.Scoped [qsite]) (qDistinct : (qsite :: q.sites).Nodup)
  (arrowQ : ArrowComp q)

include equations qScoped qDistinct arrowQ

def progress :
    Progress.Certificate (correspondence N P supply spaces q equations qScoped qDistinct arrowQ).toOperationalReadback :=
  Progress.Certificate.ofReflection (backward N P supply spaces q equations qScoped qDistinct arrowQ)

theorem positive_forward {before after : Config κ Γ star D.Ty} {current : State S}
    (paired : Representation N P supply spaces q before current) (moved : (source P supply).Step before after) :
    ∃ next, ∃ path : ExecutionPath (target N P) current next,
      0 < path.length ∧ Representation N P supply spaces q after next := by
  obtain ⟨next, step, related⟩ := forward N P supply spaces q equations qScoped qDistinct arrowQ paired moved
  exact ⟨next, .cons ⟨step⟩ (.refl next), by change 0 < 1; decide, related⟩

theorem normalization_iff {before : Config κ Γ star D.Ty} {current : State S}
    (paired : Representation N P supply spaces q before current) :
    Acc (fun after origin => (source P supply).Step origin after) before ↔
      Acc (fun next state => (target N P).Step state next) current :=
  Progress.normalization_iff (correspondence N P supply spaces q equations qScoped qDistinct arrowQ)
    (progress N P supply spaces q equations qScoped qDistinct arrowQ)
    (positive_forward N P supply spaces q equations qScoped qDistinct arrowQ) paired

theorem source_run {after : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) after) :
    ∃ next, (target N P).MultiStep (initialState N P q) next ∧
      Representation N P supply spaces q after next ∧ after.answers (D := D) = answers N next := by
  have initial := initial_related N P supply spaces q arrowQ (query_unopened qScoped qDistinct arrowQ)
  obtain ⟨next, path, related⟩ :=
    (correspondence N P supply spaces q equations qScoped qDistinct arrowQ).liftMultiStep initial
      ((FrontierConfig.source_runs_iff P supply).mpr runs)
  exact ⟨next, path, related, answers_eq N P supply spaces q related⟩

theorem target_run {next : State S}
    (runs : (target N P).MultiStep (initialState N P q) next) :
    ∃ after, Runs D P supply (Config.initial spaces q) after ∧
      Representation N P supply spaces q after next ∧ after.answers (D := D) = answers N next := by
  have initial := initial_related N P supply spaces q arrowQ (query_unopened qScoped qDistinct arrowQ)
  obtain ⟨after, path, related⟩ :=
    (correspondence N P supply spaces q equations qScoped qDistinct arrowQ).toOperationalReadback.reflectMultiStep
      initial runs
  exact ⟨after, (FrontierConfig.source_runs_iff P supply).mp path, related, answers_eq N P supply spaces q related⟩

theorem prefixes_iff (post : Multiset (Set (Term S Γ star)) → Prop) :
    (∃ after, Runs D P supply (Config.initial spaces q) after ∧ post (after.answers (D := D))) ↔
      ∃ next, (target N P).MultiStep (initialState N P q) next ∧ post (answers N next) := by
  have initial := initial_related N P supply spaces q arrowQ (query_unopened qScoped qDistinct arrowQ)
  have compared := (correspondence N P supply spaces q equations qScoped qDistinct arrowQ).reachable_iff
    (fun configuration => post (configuration.answers (D := D))) (fun state => post (answers N state))
    (fun related => (answers_eq N P supply spaces q related) ▸ Iff.rfl) initial
  constructor
  · rintro ⟨after, path, observed⟩
    exact compared.mp ⟨after, (FrontierConfig.source_runs_iff P supply).mpr path, observed⟩
  · rintro ⟨next, path, observed⟩
    obtain ⟨after, sourcePath, sourceObserved⟩ := compared.mpr ⟨next, path, observed⟩
    exact ⟨after, (FrontierConfig.source_runs_iff P supply).mp sourcePath, sourceObserved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierArrow
