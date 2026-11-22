import Mathlib.Data.List.Permutation
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Sort

/-!
# Finite constrained answer collection

This file separates three operations over the existing source machine:

* a read-only restriction that cannot alter public spaces;
* a collector that retains complete branches, including their equation stores;
* an immutable bag of completed answer snapshots that can be reopened against
  one caller at a time.

Collection never identifies encounter order with semantic order. Serialization
therefore requires an explicit order, while commutative folds act directly on
the answer bag. A live pending branch prevents completion, and reopening checks
the selected answer's constraints together with the caller's constraints rather
than conjoining sibling alternatives.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt} {Ty : Type}

/-! ## Read-only source computations -/

inductive ReadOnlyComp : Comp κ Γ star Ty → Prop where
  | ret (datum) : ReadOnlyComp (.ret datum)
  | apply (call) : ReadOnlyComp (.apply call)
  | run (text) : ReadOnlyComp (.run text)
  | bind {site pattern bound body} : ReadOnlyComp bound → ReadOnlyComp body →
      ReadOnlyComp (.let_ site pattern bound body)
  | choice {left right} : ReadOnlyComp left → ReadOnlyComp right → ReadOnlyComp (.choice left right)
  | fail : ReadOnlyComp .fail
  | query {space pattern body} : ReadOnlyComp body → ReadOnlyComp (.query space pattern body)
  | check {type body} : ReadOnlyComp body → ReadOnlyComp (.check type body)

theorem ReadOnlyComp.mapData {computation : Comp κ Γ star Ty} (readonly : ReadOnlyComp computation)
    (map : Data κ Γ star → Data κ Γ star) : ReadOnlyComp (computation.mapData map) := by
  induction readonly with
  | ret datum => exact .ret _
  | apply call => exact .apply _
  | run text => exact .run _
  | bind _ _ bound body => exact .bind bound body
  | choice _ _ left right => exact .choice left right
  | fail => exact .fail
  | query _ body => exact .query body
  | check _ body => exact .check body

inductive ReadOnlyFrame : Frame κ Γ star Ty → Prop where
  | bind {site pattern body} : ReadOnlyComp body → ReadOnlyFrame (.bindTo site pattern body)
  | check (type) : ReadOnlyFrame (.checkAt type)

inductive ReadOnlyFocus : Focus κ Γ star Ty → Prop where
  | eval {computation} : ReadOnlyComp computation → ReadOnlyFocus (.eval computation)
  | value (datum) : ReadOnlyFocus (.value datum)
  | refused (datum type) : ReadOnlyFocus (.refused datum type)

theorem ReadOnlyFocus.eval_body {computation : Comp κ Γ star Ty}
    (readonly : ReadOnlyFocus (.eval computation)) : ReadOnlyComp computation := by
  cases readonly with
  | eval body => exact body

structure ReadOnlyBranch (branch : Branch κ Γ star Ty) : Prop where
  focus : ReadOnlyFocus branch.focus
  frames : ∀ frame ∈ branch.frames, ReadOnlyFrame frame
  pending : branch.pending = []

structure ReadOnlyProgram (program : Program κ Γ star Ty) : Prop where
  equations : ∀ equation ∈ program.equations, ReadOnlyComp equation.rhs
  activation : ∀ text, ReadOnlyComp (program.reflect text)

def ReadOnlyConfig (config : Config κ Γ star Ty) : Prop :=
  ∀ branch ∈ config.branches, ReadOnlyBranch branch

theorem initial_readonly (spaces : Term S Γ star → Multiset (Row κ Γ star))
    {query : Comp κ Γ star Ty} (readonly : ReadOnlyComp query) :
    ReadOnlyConfig (Config.initial spaces query) := by
  intro branch member
  obtain rfl := Multiset.mem_singleton.mp member
  exact ⟨.eval readonly, fun _ member => False.elim (List.not_mem_nil member), rfl⟩

variable {D : Discipline S Γ star} {P : Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}

theorem move_public_stores {before after : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {outputs : Multiset (Branch κ Γ star D.Ty)} (readonly : ReadOnlyBranch branch)
    (moved : Move D P supply before branch after outputs) :
    after.spaces = before.spaces ∧ after.handles = before.handles := by
  cases moved <;> try exact ⟨rfl, rfl⟩
  all_goals
    have body := readonly.focus.eval_body
    cases body

theorem move_preserves_readonly (program : ReadOnlyProgram P)
    {before after : World κ Γ star} {branch : Branch κ Γ star D.Ty}
    {outputs : Multiset (Branch κ Γ star D.Ty)} (readonly : ReadOnlyBranch branch)
    (moved : Move D P supply before branch after outputs) :
    ∀ output ∈ outputs, ReadOnlyBranch output := by
  cases moved with
  | ret K datum frames pending =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      exact ⟨.value _, readonly.frames, readonly.pending⟩
  | apply K call frames pending matched =>
      intro output member
      change output ∈ P.equations.map (callBranch D before.scope K call frames pending) at member
      obtain ⟨equation, inside, rfl⟩ := List.mem_map.mp member
      exact ⟨.eval ((program.equations equation inside).mapData _), readonly.frames, readonly.pending⟩
  | unmatched K call frames pending missing =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      exact ⟨.value _, readonly.frames, readonly.pending⟩
  | run K text frames pending answer principal =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      exact ⟨.eval (program.activation _), readonly.frames, readonly.pending⟩
  | letStart K site pattern bound body frames pending =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      cases readonly.focus.eval_body with
      | bind boundRO bodyRO =>
          refine ⟨.eval boundRO, ?_, readonly.pending⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | inside
          · exact .bind bodyRO
          · exact readonly.frames frame inside
  | letBind K value site pattern body frames pending =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      have continuation := readonly.frames _ (List.mem_cons_self ..)
      cases continuation with
      | bind bodyRO =>
          refine ⟨.eval (bodyRO.mapData _), ?_, readonly.pending⟩
          intro frame inside
          exact readonly.frames frame (List.mem_cons_of_mem _ inside)
  | choice K left right frames pending =>
      intro output member
      cases readonly.focus.eval_body with
      | choice leftRO rightRO =>
          have cases : output = ⟨K, .eval left, frames, pending⟩ ∨
              output = ⟨K, .eval right, frames, pending⟩ := by simpa using member
          rcases cases with rfl | rfl
          · exact ⟨.eval leftRO, readonly.frames, readonly.pending⟩
          · exact ⟨.eval rightRO, readonly.frames, readonly.pending⟩
  | fail K frames pending =>
      intro output member
      exact False.elim ((Multiset.notMem_zero _) member)
  | query K space pattern body frames pending address addressed =>
      intro output member
      obtain ⟨row, _, rfl⟩ := Multiset.mem_map.mp member
      cases readonly.focus.eval_body with
      | query bodyRO => exact ⟨.eval bodyRO, readonly.frames, readonly.pending⟩
  | checkStart K type body frames pending =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      cases readonly.focus.eval_body with
      | check bodyRO =>
          refine ⟨.eval bodyRO, ?_, readonly.pending⟩
          intro frame member
          rcases List.mem_cons.mp member with rfl | inside
          · exact .check _
          · exact readonly.frames frame inside
  | admitted K value type frames pending allowed =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      exact ⟨.value _, fun frame inside => readonly.frames frame (List.mem_cons_of_mem _ inside),
        readonly.pending⟩
  | refused K value type frames pending refused =>
      intro output member
      obtain rfl := Multiset.mem_singleton.mp member
      exact ⟨.refused _ _, fun _ member => False.elim (List.not_mem_nil member), readonly.pending⟩
  | memo K value cell frames pending =>
      have impossible := readonly.frames _ (List.mem_cons_self ..)
      cases impossible
  | add | remove | removeAbsent | new | delay | forcePending | forceDone =>
      have impossible := readonly.focus.eval_body
      cases impossible

theorem step_preserves_readonly (program : ReadOnlyProgram P) {before after : Config κ Γ star D.Ty}
    (readonly : ReadOnlyConfig before) (step : Step D P supply before after) :
    ReadOnlyConfig after ∧ after.world.spaces = before.world.spaces ∧
      after.world.handles = before.world.handles := by
  cases step with
  | move world world' branch rest outputs live moved =>
      have branchRO := readonly branch (Multiset.mem_cons_self _ _)
      have outputsRO := move_preserves_readonly program branchRO moved
      have stores := move_public_stores branchRO moved
      refine ⟨?_, stores.1, stores.2⟩
      intro output member
      rcases Multiset.mem_add.mp member with produced | retained
      · exact outputsRO output produced
      · exact readonly output (Multiset.mem_cons.mpr (Or.inr retained))

theorem runs_preserve_readonly (program : ReadOnlyProgram P) {before after : Config κ Γ star D.Ty}
    (readonly : ReadOnlyConfig before) (runs : Runs D P supply before after) :
    ReadOnlyConfig after ∧ after.world.spaces = before.world.spaces ∧
      after.world.handles = before.world.handles := by
  induction runs with
  | refl => exact ⟨readonly, rfl, rfl⟩
  | tail previous step ih =>
      obtain ⟨nextRO, spaces, handles⟩ := step_preserves_readonly program ih.1 step
      exact ⟨nextRO, spaces.trans ih.2.1, handles.trans ih.2.2⟩

/-! ## Collector state and completion -/

structure State (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (D : Discipline S Γ star) where
  current : Config κ Γ star D.Ty
  reverseAnswers : List (Branch κ Γ star D.Ty)
  refuted : Multiset (Branch κ Γ star D.Ty)

def State.initial (producer : Config κ Γ star D.Ty) : State κ Γ star D := ⟨producer, [], 0⟩

def State.erase (state : State κ Γ star D) : Config κ Γ star D.Ty :=
  ⟨state.current.world, state.current.branches + (state.reverseAnswers : Multiset _) + state.refuted⟩

structure State.Valid (state : State κ Γ star D) : Prop where
  answers : ∀ branch ∈ state.reverseAnswers, branch.Finished (D := D) ∧ Solvable branch.store
  refuted : ∀ branch ∈ state.refuted, ¬ Solvable branch.store

theorem State.initial_valid (producer : Config κ Γ star D.Ty) : (State.initial producer).Valid := by
  constructor
  · intro branch member
    cases member
  · intro branch member
    exact False.elim ((Multiset.notMem_zero _) member)

@[simp] theorem State.erase_initial (producer : Config κ Γ star D.Ty) :
    (State.initial producer).erase = producer := by
  cases producer
  simp [State.initial, State.erase]

inductive Admin : State κ Γ star D → State κ Γ star D → Prop where
  | capture (world : World κ Γ star) (branch : Branch κ Γ star D.Ty)
      (rest : Multiset (Branch κ Γ star D.Ty)) (answers : List (Branch κ Γ star D.Ty)) (refuted)
      (finished : branch.Finished (D := D)) (live : Solvable branch.store) :
      Admin ⟨⟨world, branch ::ₘ rest⟩, answers, refuted⟩ ⟨⟨world, rest⟩, branch :: answers, refuted⟩
  | discard (world : World κ Γ star) (branch : Branch κ Γ star D.Ty)
      (rest : Multiset (Branch κ Γ star D.Ty)) (answers : List (Branch κ Γ star D.Ty)) (refuted)
      (dead : ¬ Solvable branch.store) :
      Admin ⟨⟨world, branch ::ₘ rest⟩, answers, refuted⟩ ⟨⟨world, rest⟩, answers, branch ::ₘ refuted⟩

theorem Admin.erase_eq {before after : State κ Γ star D} (step : Admin before after) :
    before.erase = after.erase := by
  cases step with
  | capture => simp [State.erase, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]
  | discard => simp [State.erase, Multiset.cons_add, Multiset.add_cons]

theorem Admin.preserves_valid {before after : State κ Γ star D}
    (step : Admin before after) (valid : before.Valid) : after.Valid := by
  cases step with
  | capture world branch rest answers refuted finished live =>
      refine ⟨?_, valid.refuted⟩
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨finished, live⟩
      · exact valid.answers result member
  | discard world branch rest answers refuted dead =>
      refine ⟨valid.answers, ?_⟩
      intro result member
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact dead
      · exact valid.refuted result member

theorem Admin.pending_decreases {before after : State κ Γ star D} (step : Admin before after) :
    after.current.branches.card < before.current.branches.card := by
  cases step <;> simp

theorem admin_wellFounded : WellFounded (fun after before : State κ Γ star D => Admin before after) :=
  (measure (fun state : State κ Γ star D => state.current.branches.card)).wf.mono
    (fun _ _ step => step.pending_decreases)

variable (D) (P : Program κ Γ star D.Ty) (supply : Nat → Term S Γ star)

inductive CollectorStep : State κ Γ star D → State κ Γ star D → Prop where
  | drive {producer producer' : Config κ Γ star D.Ty} (answers refuted)
      (step : SourceLanguage.Step D P supply producer producer') :
      CollectorStep ⟨producer, answers, refuted⟩ ⟨producer', answers, refuted⟩
  | admin {before after} : Admin before after → CollectorStep before after

abbrev CollectorRuns := Relation.ReflTransGen (CollectorStep D P supply)

variable {D P supply}

theorem CollectorStep.preserves_valid {before after : State κ Γ star D}
    (step : CollectorStep D P supply before after) (valid : before.Valid) : after.Valid := by
  cases step with
  | drive => exact ⟨valid.answers, valid.refuted⟩
  | admin step => exact step.preserves_valid valid

theorem CollectorStep.erase {before after : State κ Γ star D}
    (step : CollectorStep D P supply before after) :
    SourceLanguage.Runs D P supply before.erase after.erase := by
  cases step with
  | drive answers refuted source =>
      exact .single (by simpa [State.erase, add_assoc] using
        (source.frame ((answers : Multiset _) + refuted)))
  | admin administrative => rw [administrative.erase_eq]

theorem CollectorRuns.erase {before after : State κ Γ star D}
    (run : CollectorRuns D P supply before after) :
    SourceLanguage.Runs D P supply before.erase after.erase := by
  induction run with
  | refl => exact .refl
  | tail previous step ih => exact ih.trans step.erase

theorem CollectorRuns.preserves_valid {before after : State κ Γ star D}
    (run : CollectorRuns D P supply before after) (valid : before.Valid) : after.Valid := by
  induction run with
  | refl => exact valid
  | tail previous step ih => exact step.preserves_valid ih

def State.finish? (state : State κ Γ star D) : Option (List (Branch κ Γ star D.Ty)) :=
  if state.current.branches.card = 0 then some state.reverseAnswers.reverse else none

theorem State.finish_some_iff (state : State κ Γ star D) (payload : List (Branch κ Γ star D.Ty)) :
    state.finish? = some payload ↔ state.current.branches = 0 ∧ state.reverseAnswers.reverse = payload := by
  by_cases empty : state.current.branches = 0
  · simp [State.finish?, empty]
  · have nonzero : state.current.branches.card ≠ 0 := fun zero => empty (Multiset.card_eq_zero.mp zero)
    simp [State.finish?, nonzero, empty]

theorem State.finish_none_of_pending (state : State κ Γ star D)
    (branch : Branch κ Γ star D.Ty) (pending : branch ∈ state.current.branches) :
    state.finish? = none := by
  have nonempty : state.current.branches ≠ 0 := by
    intro empty
    rw [empty] at pending
    exact (Multiset.notMem_zero _) pending
  have nonzero : state.current.branches.card ≠ 0 := fun zero => nonempty (Multiset.card_eq_zero.mp zero)
  simp [State.finish?, nonzero]

theorem State.erase_answers (state : State κ Γ star D) (valid : state.Valid) :
    state.erase.answers (D := D) = state.current.answers (D := D) +
      (state.reverseAnswers : Multiset (Branch κ Γ star D.Ty)).map (Branch.answer (D := D)) := by
  classical
  have complete : (state.reverseAnswers : Multiset (Branch κ Γ star D.Ty)).filter
      (fun branch => branch.Finished (D := D) ∧ Solvable branch.store) = state.reverseAnswers := by
    apply Multiset.filter_eq_self.mpr
    intro branch member
    exact valid.answers branch (Multiset.mem_coe.mp member)
  have dead : state.refuted.filter (fun branch => branch.Finished (D := D) ∧ Solvable branch.store) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro branch member admitted
    exact valid.refuted branch member admitted.2
  simp only [State.erase, Config.answers, Multiset.filter_add, Multiset.map_add]
  rw [complete, dead, Multiset.map_zero, add_zero]

theorem State.completed_quiescent (state : State κ Γ star D) (valid : state.Valid)
    (payload : List (Branch κ Γ star D.Ty)) (finished : state.finish? = some payload) :
    state.erase.Quiescent P supply := by
  have empty := ((state.finish_some_iff payload).mp finished).1
  apply Config.quiescent_of_finished
  intro branch member live
  change branch ∈ state.current.branches + (state.reverseAnswers : Multiset _) + state.refuted at member
  rw [empty, zero_add] at member
  rcases Multiset.mem_add.mp member with captured | rejected
  · exact (valid.answers branch (Multiset.mem_coe.mp captured)).1
  · exact False.elim (valid.refuted branch rejected live)

theorem collector_preserves_public_stores (program : ReadOnlyProgram P)
    (initial : Config κ Γ star D.Ty) (readonly : ReadOnlyConfig initial)
    (state : State κ Γ star D) (run : CollectorRuns D P supply (State.initial initial) state) :
    state.current.world.spaces = initial.world.spaces ∧ state.current.world.handles = initial.world.handles := by
  have actual := run.erase
  rw [State.erase_initial] at actual
  have result := runs_preserve_readonly program readonly actual
  exact ⟨result.2.1, result.2.2⟩

/-! ## Captured answers and reopening -/

def resume (caller captured : Branch κ Γ star D.Ty) : Branch κ Γ star D.Ty :=
  ⟨caller.store ++ captured.store, captured.focus, caller.frames, caller.pending ++ captured.pending⟩

theorem resume_models {Variables : Type} {declaration : Variables → MetaArity S}
    (point : Assignment (fam κ) declaration) (caller captured : Branch κ Γ star D.Ty) :
    Models point (resume caller captured).store ↔ Models point caller.store ∧ Models point captured.store :=
  models_append point _ _

theorem captured_information_erasure_iff (caller captured : Branch κ Γ star D.Ty) :
    (∀ (Variables : Type) (declaration : Variables → MetaArity S)
      (point : Assignment (fam κ) declaration),
      Models point (resume caller captured).store ↔ Models point caller.store) ↔
    (∀ (Variables : Type) (declaration : Variables → MetaArity S)
      (point : Assignment (fam κ) declaration), Models point caller.store → Models point captured.store) := by
  constructor
  · intro same Variables declaration point callerModel
    exact ((resume_models point caller captured).mp ((same Variables declaration point).mpr callerModel)).2
  · intro entailed Variables declaration point
    rw [resume_models]
    exact ⟨And.left, fun callerModel => ⟨callerModel, entailed Variables declaration point callerModel⟩⟩

structure AnswerSpace (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (D : Discipline S Γ star) where
  rows : Multiset (Branch κ Γ star D.Ty)
  ready : ∀ branch ∈ rows, branch.Finished (D := D) ∧ Solvable branch.store

def reify (state : State κ Γ star D) (valid : state.Valid) : Option (AnswerSpace κ Γ star D) :=
  if state.current.branches.card = 0 then
    some ⟨(state.reverseAnswers : Multiset _), fun branch member => valid.answers branch (Multiset.mem_coe.mp member)⟩
  else none

open Classical in
/-- Drain a finite frontier of finished branches. Inconsistent branches go
to the refuted journal. At closure the answer bag agrees with the logical
filter independently of the order in which these branches were visited. -/
theorem collect_finished (world : World κ Γ star) (work : List (Branch κ Γ star D.Ty))
    (finished : ∀ b ∈ work, b.Finished (D := D)) :
    ∃ final, Relation.ReflTransGen (Admin (D := D)) (State.initial ⟨world, work⟩) final ∧
      ∃ (valid : final.Valid) (bag : AnswerSpace κ Γ star D),
        reify final valid = some bag ∧
        bag.rows = (work : Multiset _).filter (fun b => Solvable b.store) := by
  classical
  have drain (todo kept : List (Branch κ Γ star D.Ty)) (dead : Multiset (Branch κ Γ star D.Ty))
      (done_ : ∀ b ∈ todo, b.Finished (D := D)) :
      ∃ (out : List (Branch κ Γ star D.Ty)) (discarded : Multiset (Branch κ Γ star D.Ty)),
        Relation.ReflTransGen (Admin (D := D)) ⟨⟨world, todo⟩, kept, dead⟩ ⟨⟨world, 0⟩, out, discarded⟩ ∧
        (out : Multiset _) = (todo : Multiset (Branch κ Γ star D.Ty)).filter (fun b => Solvable b.store) + (kept : Multiset (Branch κ Γ star D.Ty)) := by
    induction todo generalizing kept dead with
    | nil => exact ⟨kept, dead, .refl, by simp⟩
    | cons b bs ih =>
      have tail := fun b hb => done_ b (List.mem_cons_of_mem _ hb)
      by_cases live : Solvable b.store
      · obtain ⟨out, rejected, path, rows⟩ := ih (b :: kept) dead tail
        exact ⟨out, rejected, path.head (.capture world b bs kept dead (done_ b List.mem_cons_self) live),
          by rw [rows]; simp only [← Multiset.cons_coe, Multiset.filter_cons, if_pos live,
            Multiset.add_cons, Multiset.singleton_add, Multiset.cons_add]⟩
      · obtain ⟨out, rejected, path, rows⟩ := ih kept (b ::ₘ dead) tail
        exact ⟨out, rejected, path.head (.discard world b bs kept dead live),
          by rw [rows]; simp only [← Multiset.cons_coe, Multiset.filter_cons, if_neg live, zero_add]⟩
  obtain ⟨out, rejected, path, counted⟩ := drain work [] 0 finished
  have preserves {a z : State κ Γ star D} (steps : Relation.ReflTransGen Admin a z) :
      a.Valid → z.Valid := by
    induction steps with
    | refl => exact id
    | tail _ step ih => exact fun h => step.preserves_valid (ih h)
  have valid := preserves path (State.initial_valid _)
  refine ⟨_, path, valid, ⟨out, fun b hb => valid.answers b (Multiset.mem_coe.mp hb)⟩, rfl, ?_⟩
  simpa using counted

structure Status (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (D : Discipline S Γ star) where
  answers : AnswerSpace κ Γ star D
  outstanding : Multiset (Branch κ Γ star D.Ty)

def status (state : State κ Γ star D) (valid : state.Valid) : Status κ Γ star D :=
  ⟨⟨state.reverseAnswers, fun branch member => valid.answers branch (Multiset.mem_coe.mp member)⟩,
    state.current.branches⟩

theorem reify_none_of_pending (state : State κ Γ star D) (valid : state.Valid)
    (branch : Branch κ Γ star D.Ty) (member : branch ∈ state.current.branches) : reify state valid = none := by
  have nonzero : state.current.branches.card ≠ 0 := by
    intro zero
    have empty := Multiset.card_eq_zero.mp zero
    rw [empty] at member
    exact (Multiset.notMem_zero _) member
  simp only [reify, if_neg nonzero]

def AnswerSpace.reflect (space : AnswerSpace κ Γ star D) (world : World κ Γ star)
    (caller : Branch κ Γ star D.Ty) : Config κ Γ star D.Ty :=
  ⟨world, space.rows.map (resume caller)⟩

theorem reflect_models {Variables : Type} {declaration : Variables → MetaArity S}
    (point : Assignment (fam κ) declaration) (caller captured : Branch κ Γ star D.Ty) :
    Models point (resume caller captured).store ↔ Models point caller.store ∧ Models point captured.store :=
  resume_models point caller captured

theorem rejoin_answer (caller captured : Branch κ Γ star D.Ty)
    (containsCaller : ∀ (Variables : Type) (declaration : Variables → MetaArity S)
      (point : Assignment (fam κ) declaration), Models point captured.store → Models point caller.store) :
    (resume caller captured).answer (D := D) = captured.answer (D := D) := by
  ext ground
  change (∃ datum, captured.focus = .value datum ∧ Reads (caller.store ++ captured.store) datum ground) ↔
    (∃ datum, captured.focus = .value datum ∧ Reads captured.store datum ground)
  constructor
  · rintro ⟨datum, focus, Variables, declaration, point, known, reading⟩
    exact ⟨datum, focus, Variables, declaration, point, (resume_models point caller captured).mp known |>.2, reading⟩
  · rintro ⟨datum, focus, Variables, declaration, point, known, reading⟩
    exact ⟨datum, focus, Variables, declaration, point,
      (resume_models point caller captured).mpr ⟨containsCaller Variables declaration point known, known⟩, reading⟩

theorem reflect_answers (space : AnswerSpace κ Γ star D) (world : World κ Γ star)
    (caller : Branch κ Γ star D.Ty) (noFrames : caller.frames = [])
    (containsCaller : ∀ captured ∈ space.rows, ∀ (Variables : Type) (declaration : Variables → MetaArity S)
      (point : Assignment (fam κ) declaration), Models point captured.store → Models point caller.store) :
    (space.reflect world caller).answers (D := D) = space.rows.map (Branch.answer (D := D)) := by
  classical
  have complete : space.rows.filter (fun branch =>
      (resume caller branch).Finished (D := D) ∧ Solvable (resume caller branch).store) = space.rows := by
    apply Multiset.filter_eq_self.mpr
    intro branch member
    obtain ⟨finished, Variables, declaration, point, known⟩ := space.ready branch member
    refine ⟨⟨noFrames, finished.2⟩, Variables, declaration, point, ?_⟩
    exact (resume_models point caller branch).mpr ⟨containsCaller branch member Variables declaration point known, known⟩
  simp only [AnswerSpace.reflect, Config.answers, Multiset.filter_map, Multiset.map_map, Function.comp_def]
  rw [complete]
  apply Multiset.map_congr rfl
  intro branch member
  exact rejoin_answer caller branch (containsCaller branch member)

def AnswerSpace.serialize (space : AnswerSpace κ Γ star D)
    (order : LinearOrder (Branch κ Γ star D.Ty)) : List (Branch κ Γ star D.Ty) :=
  letI := order
  space.rows.sort (· ≤ ·)

theorem serialize_preserves_rows (space : AnswerSpace κ Γ star D)
    (order : LinearOrder (Branch κ Γ star D.Ty)) :
    (space.serialize order : Multiset _) = space.rows := by
  let : LinearOrder (Branch κ Γ star D.Ty) := order
  exact Multiset.sort_eq _ _

/-- Explicit nondeterministic serialization counts permutations of occurrences.
Rows retain their stores. Representatives of the same bag give the same
multiset of sequences, including repeated equal sequences. -/
def AnswerSpace.linearizations (space : AnswerSpace κ Γ star D) :
    Multiset (List (Branch κ Γ star D.Ty)) :=
  Quotient.liftOn space.rows (fun xs => (xs.permutations : Multiset _))
    (fun _ _ h => Multiset.coe_eq_coe.mpr (List.Perm.permutations h))

theorem mem_linearizations (space : AnswerSpace κ Γ star D) (sequence : List (Branch κ Γ star D.Ty)) :
    sequence ∈ space.linearizations ↔ (sequence : Multiset _) = space.rows := by
  cases space with
  | mk rows ready =>
    induction rows using Quotient.inductionOn with
    | _ xs => exact Multiset.mem_coe.trans (List.mem_permutations.trans Multiset.coe_eq_coe.symm)

theorem linearizations_card (space : AnswerSpace κ Γ star D) :
    space.linearizations.card = space.rows.card.factorial := by
  cases space with
  | mk rows ready =>
    induction rows using Quotient.inductionOn with
    | _ xs => exact List.length_permutations xs

/-- Residual equations are symmetric. Solved assignments keep their
direction from a declared slot to its image. -/
def orientEquation {Key : Type} [LinearOrder Key] (e : Key × Key) : Key × Key :=
  (min e.1 e.2, max e.1 e.2)

theorem orientEquation_swap {Key : Type} [LinearOrder Key] (e : Key × Key) :
    orientEquation e.swap = orientEquation e := by
  cases e
  simp [orientEquation, min_comm, max_comm]

/-- The ordering observation of a binding image at fixed slot coordinates.
Both lists keep their multiplicities. Only the residuals are undirected. -/
def knowledgeKey {Key : Type} [LinearOrder Key] (assignments residuals : List (Key × Key)) :
    List (Key ×ₗ Key) × List (Key ×ₗ Key) :=
  let a : Multiset (Key ×ₗ Key) := assignments.map toLex
  let r : Multiset (Key ×ₗ Key) := residuals.map (toLex ∘ orientEquation)
  (a.sort (· ≤ ·), r.sort (· ≤ ·))

theorem knowledgeKey_perm {Key : Type} [LinearOrder Key]
    {assignments otherAssignments residuals otherResiduals : List (Key × Key)}
    (assigned : assignments.Perm otherAssignments)
    (pending : residuals.Perm otherResiduals) :
    knowledgeKey assignments residuals = knowledgeKey otherAssignments otherResiduals := by
  unfold knowledgeKey
  rw [Multiset.coe_eq_coe.mpr (assigned.map toLex),
    Multiset.coe_eq_coe.mpr (pending.map (toLex ∘ orientEquation))]

theorem knowledgeKey_reverse_residual {Key : Type} [LinearOrder Key]
    (assignments before after : List (Key × Key)) (e : Key × Key) :
    knowledgeKey assignments (before ++ e.swap :: after) =
      knowledgeKey assignments (before ++ e :: after) := by
  simp [knowledgeKey, Function.comp_apply, orientEquation_swap]

/-- Sort complete snapshots using a partial structural key. The payload of
the returned sequence is the original row. An opaque row prevents this
observation. Equal keys must identify equivalent public observations. -/
def serializeBy? {Row Key : Type*} [LinearOrder Key] (key : Row → WithBot Key)
    (rows : List Row) : Option (List Row) :=
  if rows.all (fun r => Option.isSome (key r)) then
    some (rows.mergeSort (fun a b => decide (key a ≤ key b)))
  else none

theorem serialized_rows {Row Key : Type*} [LinearOrder Key] (key : Row → WithBot Key)
    (rows out : List Row) (success : serializeBy? key rows = some out) : out.Perm rows := by
  unfold serializeBy? at success
  split at success
  · cases success; exact List.mergeSort_perm _ _
  · contradiction

theorem serialized_keys {Row Key : Type*} [LinearOrder Key] (key : Row → WithBot Key)
    (rows out : List Row) (success : serializeBy? key rows = some out) :
    (out.map key).Pairwise (· ≤ ·) := by
  unfold serializeBy? at success
  split at success
  · cases success
    rw [List.pairwise_map]
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
        (by intro a b c h k; simpa using le_trans (of_decide_eq_true h) (of_decide_eq_true k))
        (by intro a b; simpa using le_total (key a) (key b)) rows)
  · contradiction

/-- Permuting the journal cannot change its serialized key sequence. This
applies to all observers that factor through the full structural key. -/
theorem serialized_keys_perm {Row Key : Type*} [LinearOrder Key] (key : Row → WithBot Key)
    {xs ys first second : List Row} (perm : xs.Perm ys)
    (left : serializeBy? key xs = some first) (right : serializeBy? key ys = some second) :
    first.map key = second.map key := by
  exact (((serialized_rows _ _ _ left).trans (perm.trans (serialized_rows _ _ _ right).symm)).map key).eq_of_pairwise'
    (serialized_keys _ _ _ left) (serialized_keys _ _ _ right)

def AnswerSpace.fold {M : Type} [CommMonoid M] (observe : Branch κ Γ star D.Ty → M)
    (space : AnswerSpace κ Γ star D) : M := (space.rows.map observe).prod

def foldAtClose {M : Type} [CommMonoid M] (observe : Branch κ Γ star D.Ty → M)
    (state : State κ Γ star D) : Option M :=
  if state.current.branches.card = 0 then some ((state.reverseAnswers.map observe).prod) else none

theorem fold_reify_fusion {M : Type} [CommMonoid M] (observe : Branch κ Γ star D.Ty → M)
    (state : State κ Γ star D) (valid : state.Valid) :
    (reify state valid).map (AnswerSpace.fold observe) = foldAtClose observe state := by
  by_cases done : state.current.branches.card = 0 <;>
    simp [reify, foldAtClose, done, AnswerSpace.fold]

/-! ## Enumeration-order boundary -/

theorem collection_descends_iff {Answer Output : Type} (collect : List Answer → Output) :
    (∃ collectBag : Multiset Answer → Output,
      ∀ answers : List Answer, collectBag (answers : Multiset Answer) = collect answers) ↔
      ∀ first second : List Answer, first.Perm second → collect first = collect second := by
  constructor
  · rintro ⟨collectBag, agrees⟩ first second same
    exact (agrees first).symm.trans ((congrArg collectBag (Multiset.coe_eq_coe.mpr same)).trans (agrees second))
  · intro invariant
    refine ⟨Quotient.lift collect ?_, ?_⟩
    · intro first second same
      exact invariant first second same
    · intro answers
      rfl

theorem original_order_does_not_descend {Answer : Type} (left right : Answer) (different : left ≠ right) :
    ¬ ∃ collectBag : Multiset Answer → List Answer,
      ∀ answers : List Answer, collectBag (answers : Multiset Answer) = answers := by
  intro collector
  have invariant := (collection_descends_iff (fun answers : List Answer => answers)).mp collector
  have same := invariant [left, right] [right, left] (List.Perm.swap right left [])
  exact different (List.cons.inj same).1

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection
