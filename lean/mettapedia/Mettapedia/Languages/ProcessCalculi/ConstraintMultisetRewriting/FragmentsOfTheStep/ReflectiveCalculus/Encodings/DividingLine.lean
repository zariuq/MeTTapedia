import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Junk
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Composition

/-!
# What switches a system off when composition asks for solvable joint knowledge

In the calculus of systems composed by the union of their programs and the tensor of their states,
with composition restricted to systems whose joint knowledge is solvable (`stepParallelSolvable`):

* **A system whose rules have only equation checks and `any` queries and no collect pattern is
  switched off by no composable neighbour** (`succeeds_beside`): if it reaches success alone, it
  reaches success beside every system whose knowledge is solvable, **whatever that system's rows and
  whatever its rules**. More generally every reachable may-barb of every pattern survives
  (`reaches_barb_beside`). Such a rule is `MonotoneRule`: a neighbour only adds rows, and added rows
  can only add witnesses to an `any` query. A rule with only equation checks and no collect pattern
  is `RuleSyntax.Scope.Positive`, and is monotone (`positive_monotone`).
* **The dividing line** (`switched_has_guard`): if a composable neighbour switches a system off, the
  system's program has a rule with a none query (`none`) check, a count check or a collect pattern; run
  by run (`switched_every_run_guarded`), every run of the system alone to success fires a rule that
  is not positive.
* The four-rule program of the reflective calculus is positive (`image_positive`), so the translation
  of a process is switched off by no composable neighbour (`image_never_switched`), while with every
  pair composable a neighbour whose knowledge has no solution switches it off
  (`image_switched_off`).
* **The calculus of positive systems** (`positiveParallel`): not switchable
  (`positiveParallel_not_switchable`); success at once persists beside every composable neighbour
  (`success_persists_composable`); and it is not persistent in the sense of
  `ParallelClosed.ParallelCalculus.Persistent` (`positiveParallel_not_persistent`), because that
  notion asks success to persist beside every term, composable or not, and a neighbour whose
  knowledge has no solution is not composable and removes every barb. The reduction is replayed
  beside a neighbour up to the renaming the tensor does (`Beside.runs`); that the reduct of a tensor
  is the tensor of the reduct on the nose is not claimed.

## What the neighbour may contain

The theorem holds for every neighbour with solvable knowledge (the composability), with any rows
and any program: the neighbour's rules join the system's by the union and may fire on the system's
rows, and they may be guarded by none queries; under may-success they only add runs. The hypotheses have
an instance together (`positive_beside_guarded`: the system of the four-rule program with the row
`ω!(0)` beside a system with the row `*@0` and the none-guarded rule). Controls, one per clause:
knowledge without a solution, once every pair is composable, switches a positive system off
(`junk_switches`); a row switches off a system with a none check (`solvable_switchable`); the
controls of the rules clause and of count checks and collect patterns are in `DividingLineControls`.

## The proof: replay up to the renaming the tensor does

The composite of `u` and `t` changes frames as it runs: a firing at `u` extends `u`'s frame by new
names, and replayed beside `t` it extends the composite's frame, so after it the composite's frame is
`(F ⊕ G) ⊕ N` while the tensor of the result with `t` has frame `(F ⊕ N) ⊕ G`. The invariant
(`Beside t u w`) says that `w` is `u` beside `t` up to that renaming: `w`'s frame is a coproduct of the
frames of `u` and `t` along two maps (every pair of instantiations of the two factors is realized by
one instantiation of `w`'s frame), `w`'s knowledge consists of the two knowledges carried along them,
and `w` holds the rows of `u` at even identities and those of `t` at odd ones. The tensor is an
instance (`besideTensor`). A firing of a monotone rule admitted at `u` is replayed at `w`
(`replayFiring`: the same rule and new names, the opening carried along the replay of the frame,
identities doubled); it is admitted there (`replay_admits`: an `any` query keeps its witness, at the
doubled identity), and its result is again beside `t` (`replayResult`). A may-barb of
`u` is a may-barb of `w` when `t`'s knowledge is solvable (`Beside.mayBarb`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation)
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read outputT zeroT
  knowledge groundFrame someGrounding)
open Interface.Frames (Frame)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess)

/-- The programs of the step at the twin-binder frames. -/
abbrev Prog := RuleSyntax.Program (RuleSyntax.Contextual.Terms sig)

/-- The extensions of the step at the twin-binder frames: declarations of new names. -/
abbrev decl := RuleSyntax.Contextual.declarations sig

/-- A step of the program `P`, as a relation on states. -/
abbrev ProgramMoves (P : Prog) : ByInstantiation.State → ByInstantiation.State → Prop :=
  Succ (RuleSyntax.step knowledge ℕ decl P).toStep

/-- **A rule no composable neighbour switches off**: its checks are equations or `any` queries, and
it has no collect pattern. A neighbour only adds rows, and added rows can only add witnesses to an
`any` query; a `none` query, a count and a collect pattern can each be falsified by an added row. -/
def MonotoneRule (r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig)) : Prop :=
  (∀ c ∈ r.body.checks, (∃ l l', c = Check.equal l l') ∨ ∃ p, c = Check.predicate .any p) ∧
    r.collect = []

/-- A positive rule is monotone. -/
theorem positive_monotone {r : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig)}
    (positive : RuleSyntax.Scope.Positive r) : MonotoneRule r :=
  ⟨fun c inside => Or.inl (positive.1 c inside), positive.2⟩

/-- The new names of an extension of one frame, as an extension of another. -/
def moveExt {F F' : Frame sig} (x : decl.Ext F) : decl.Ext F' := x

/-! ## Actions compose -/

theorem act_act {F F' F'' : Frame sig} (f : Assignment F.arity F'.arity) (g : Assignment F'.arity F''.arity)
    (o : Observation sig F.arity) :
    knowledge.act g (knowledge.act f o) = knowledge.act (Assignment.compose g f) o :=
  instantiateObservation_comp f g o

theorem knowledge_refl {F : Frame sig} (o : Observation sig F.arity) : knowledge.E o o :=
  (knowledge.equivalence F).refl o

/-! ## Identities doubled -/

theorem double_mem_map (l : List ℕ) (k : ℕ) : 2 * k ∈ l.map (2 * ·) ↔ k ∈ l := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨j, inside, same⟩
    have : j = k := by omega
    exact this ▸ inside
  · exact fun inside => ⟨k, inside, rfl⟩

theorem odd_not_mem_map_double (l : List ℕ) (k : ℕ) : 2 * k + 1 ∉ l.map (2 * ·) := by
  simp only [List.mem_map, not_exists, not_and]
  intro j _ same
  omega

theorem mem_doubled (l : List ℕ) (k : ℕ) : 2 * k ∈ (l.map (2 * ·)).toFinset ↔ k ∈ l := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨j, inside, same⟩
    have : j = k := by omega
    exact this ▸ inside
  · exact fun inside => ⟨k, inside, rfl⟩

theorem odd_not_mem_doubled (l : List ℕ) (k : ℕ) : 2 * k + 1 ∉ (l.map (2 * ·)).toFinset := by
  simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
  intro j _ same
  omega

theorem mem_doubled_iff (l : List ℕ) (o : ℕ) : o ∈ (l.map (2 * ·)).toFinset ↔ ∃ k ∈ l, 2 * k = o := by
  simp only [List.mem_toFinset, List.mem_map]

theorem even_mem_map (s : Finset ℕ) (k : ℕ) : 2 * k ∈ s.map evenEmbedding ↔ k ∈ s := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, inside, same⟩
    rw [evenEmbedding_apply] at same
    have : j = k := by omega
    exact this ▸ inside
  · exact fun inside => ⟨k, inside, rfl⟩

theorem odd_not_mem_even_map (s : Finset ℕ) (k : ℕ) : 2 * k + 1 ∉ s.map evenEmbedding := by
  rw [Finset.mem_map]
  rintro ⟨j, _, same⟩
  rw [evenEmbedding_apply] at same
  omega

theorem odd_mem_map (s : Finset ℕ) (k : ℕ) : 2 * k + 1 ∈ s.map oddEmbedding ↔ k ∈ s := by
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, inside, same⟩
    rw [oddEmbedding_apply] at same
    have : j = k := by omega
    exact this ▸ inside
  · exact fun inside => ⟨k, inside, rfl⟩

theorem even_not_mem_odd_map (s : Finset ℕ) (k : ℕ) : 2 * k ∉ s.map oddEmbedding := by
  rw [Finset.mem_map]
  rintro ⟨j, _, same⟩
  rw [oddEmbedding_apply] at same
  omega

/-- Relabelling commutes with doubling the identities and mapping the rows. -/
theorem relabel_doubled {F F' : Frame sig} (old : ℕ → Observation sig F.arity)
    (old' : ℕ → Observation sig F'.arity) (φ : Observation sig F.arity → Observation sig F'.arity)
    (rows : ∀ j, old' (2 * j) = φ (old j)) :
    ∀ (made : List ℕ) (produced : List (Observation sig F.arity)) (k : ℕ),
      RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig) old' (made.map (2 * ·))
          (produced.map φ) (2 * k) =
        φ (RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig) old made produced k)
  | [], _, k => rows k
  | _ :: _, [], k => rows k
  | m :: ms, p :: ps, k => by
      simp only [List.map_cons, RuleSyntax.relabel]
      by_cases same : k = m
      · subst same
        simp
      · have apart : 2 * k ≠ 2 * m := by omega
        rw [if_neg apart, if_neg same]
        exact relabel_doubled old old' φ rows ms ps k

/-! ## A state beside a neighbour, up to the renaming the tensor does -/

/-- **`w` is `u` beside `t`, up to the renaming the tensor does.** `w`'s frame is a coproduct of the
frames of `u` and `t` along `left` and `right`; its knowledge consists of their knowledges carried
along them; it holds the rows of `u` at even identities and those of `t` at odd ones. -/
structure Beside (t u w : ByInstantiation.State) where
  left : Assignment u.frame.arity w.frame.arity
  right : Assignment t.frame.arity w.frame.arity
  copair : ∀ {B : Frame sig} (g : Assignment u.frame.arity B.arity)
    (h : Assignment t.frame.arity B.arity),
    ∃ v : Assignment w.frame.arity B.arity, Assignment.compose v left = g ∧ Assignment.compose v right = h
  knowledge_iff : ∀ e, e ∈ w.knowledge ↔
    e ∈ knowledge.applyStore (a := u.frame) (b := w.frame) left u.knowledge ∨
      e ∈ knowledge.applyStore (a := t.frame) (b := w.frame) right t.knowledge
  present : w.present = u.present.map evenEmbedding ∪ t.present.map oddEmbedding
  label_even : ∀ k, w.label (2 * k) = knowledge.act left (u.label k)
  label_odd : ∀ k, w.label (2 * k + 1) = knowledge.act right (t.label k)

/-- **The tensor is beside**: `tensor s t` is `s` beside `t`, along the two weakenings. -/
def besideTensor (s t : ByInstantiation.State) : Beside t s (tensor s t) where
  left := leftIn s.frame t.frame
  right := rightIn s.frame t.frame
  copair g h := ⟨RuleSyntax.Contextual.copair sig g h,
    funext fun x => instantiate_generator (RuleSyntax.Contextual.copair sig g h) (Sum.inl x),
    funext fun y => instantiate_generator (RuleSyntax.Contextual.copair sig g h) (Sum.inr y)⟩
  knowledge_iff _ := List.mem_append
  present := rfl
  label_even k := tensor_label_even s t k
  label_odd k := tensor_label_odd s t k

section Replay

variable {t u w : ByInstantiation.State}

/-- **The replay of an extension**: the old names of `u` go to their images in `w`, each new name to
itself. -/
def Beside.replay (b : Beside t u w) (x : decl.Ext u.frame) :
    Assignment (decl.target x).arity (decl.target (moveExt (F' := w.frame) x)).arity :=
  RuleSyntax.Contextual.copair sig
    (Assignment.compose (decl.weaken (moveExt (F' := w.frame) x)) b.left)
    (RuleSyntax.Contextual.canonicalOpening sig w.frame x)

theorem Beside.replay_weaken (b : Beside t u w) (x : decl.Ext u.frame) :
    Assignment.compose (b.replay x) (decl.weaken x) =
      Assignment.compose (decl.weaken (moveExt (F' := w.frame) x)) b.left :=
  funext fun y => instantiate_generator (b.replay x) (Sum.inl y)

theorem Beside.act_replay_weaken (b : Beside t u w) (x : decl.Ext u.frame) (o : Observation sig u.frame.arity) :
    knowledge.act (b.replay x) (knowledge.act (decl.weaken x) o) =
      knowledge.act (decl.weaken (moveExt (F' := w.frame) x)) (knowledge.act b.left o) := by
  rw [act_act, act_act, b.replay_weaken]

/-- The instantiation of `w`'s extended frame built from one of `w`'s frame and one of `u`'s
extended frame: old names by the first, new names as the second sends them. -/
def extendPair {F F' : Frame sig} (x : decl.Ext F) {B : Frame sig} (v₀ : Assignment F'.arity B.arity)
    (g : Assignment (decl.target x).arity B.arity) :
    Assignment (decl.target (moveExt (F' := F') x)).arity B.arity :=
  RuleSyntax.Contextual.copair sig v₀
    (Assignment.compose g (RuleSyntax.Contextual.canonicalOpening sig F x))

theorem extendPair_weaken {F F' : Frame sig} (x : decl.Ext F) {B : Frame sig}
    (v₀ : Assignment F'.arity B.arity) (g : Assignment (decl.target x).arity B.arity) :
    Assignment.compose (extendPair x v₀ g) (decl.weaken (moveExt (F' := F') x)) = v₀ :=
  funext fun y => instantiate_generator (extendPair x v₀ g) (Sum.inl y)

/-- **The extended frames are again a coproduct**: every instantiation of `u`'s extended frame and
every instantiation of `t`'s frame are realized together by one instantiation of `w`'s extended
frame, along the replay and along `right` followed by the weakening. -/
theorem Beside.extend_copair (b : Beside t u w) (x : decl.Ext u.frame) {B : Frame sig}
    (g : Assignment (decl.target x).arity B.arity) (h : Assignment t.frame.arity B.arity) :
    ∃ v : Assignment (decl.target (moveExt (F' := w.frame) x)).arity B.arity,
      Assignment.compose v (b.replay x) = g ∧
        Assignment.compose v (Assignment.compose (decl.weaken (moveExt (F' := w.frame) x)) b.right) = h := by
  obtain ⟨v₀, onLeft, onRight⟩ := b.copair (Assignment.compose g (decl.weaken x)) h
  refine ⟨extendPair x v₀ g, funext fun y => ?_, ?_⟩
  · rcases y with y | n
    · show instantiate (extendPair x v₀ g)
          (instantiate (decl.weaken (moveExt (F' := w.frame) x)) (b.left y)) = g (Sum.inl y)
      rw [← Assignment.instantiate_compose, extendPair_weaken]
      exact (congrFun onLeft y).trans (instantiate_generator g (Sum.inl y))
    · show instantiate (extendPair x v₀ g)
          (generator (decl.target (moveExt (F' := w.frame) x)).arity (Sum.inr n)) = g (Sum.inr n)
      exact (instantiate_generator (extendPair x v₀ g) (Sum.inr n)).trans
        (instantiate_generator g (Sum.inr n))
  · rw [Assignment.compose_associative, extendPair_weaken, onRight]

/-- Every term `w` mentions comes from a term `u` mentions or from a term of `t`. -/
theorem Beside.mentions (b : Beside t u w) {o : Observation sig w.frame.arity} (mentioned : w.Mentions o) :
    (∃ o₀, u.Mentions o₀ ∧ o = knowledge.act b.left o₀) ∨ ∃ o₁, o = knowledge.act b.right o₁ := by
  rcases mentioned with first | second | ⟨k, present, rfl⟩
  · obtain ⟨e, inW, rfl⟩ := List.mem_map.mp first
    rcases (b.knowledge_iff e).mp inW with inU | inT
    · obtain ⟨e₀, inU', rfl⟩ := List.mem_map.mp inU
      exact Or.inl ⟨e₀.1, Or.inl (List.mem_map_of_mem inU'), rfl⟩
    · obtain ⟨e₁, _, rfl⟩ := List.mem_map.mp inT
      exact Or.inr ⟨e₁.1, rfl⟩
  · obtain ⟨e, inW, rfl⟩ := List.mem_map.mp second
    rcases (b.knowledge_iff e).mp inW with inU | inT
    · obtain ⟨e₀, inU', rfl⟩ := List.mem_map.mp inU
      exact Or.inl ⟨e₀.2, Or.inr (Or.inl (List.mem_map_of_mem inU')), rfl⟩
    · obtain ⟨e₁, _, rfl⟩ := List.mem_map.mp inT
      exact Or.inr ⟨e₁.2, rfl⟩
  · rw [b.present, Finset.mem_union, Finset.mem_map, Finset.mem_map] at present
    rcases present with ⟨j, inU, rfl⟩ | ⟨j, _, rfl⟩
    · exact Or.inl ⟨u.label j, Or.inr (Or.inr ⟨j, inU, rfl⟩), b.label_even j⟩
    · exact Or.inr ⟨t.label j, b.label_odd j⟩

/-! ## Replaying a firing -/

/-- The selection with every identity doubled. -/
def evenSelection (selection : Selection ℕ) : Selection ℕ :=
  ⟨selection.taken.map (2 * ·), selection.read.map (2 * ·), selection.made.map (2 * ·)⟩

/-- **A firing at `u`, replayed at `w`**: the same rule and new names, the opening carried along the
replay of the frame, and the selection with every identity doubled. -/
abbrev Beside.replayFiring (b : Beside t u w) {P : Prog} (Q : Prog)
    (f : RuleSyntax.Firing ℕ decl P u.frame) : RuleSyntax.Firing ℕ decl (P ∪ Q) w.frame :=
  ⟨f.rule, Set.mem_union_left Q f.member, moveExt f.ext, Assignment.compose (b.replay f.ext) f.opening,
    evenSelection f.selection, f.seen⟩

variable (b : Beside t u w) {P : Prog} (Q : Prog) (f : RuleSyntax.Firing ℕ decl P u.frame)

theorem Beside.row_even (k : ℕ) :
    (b.replayFiring Q f).row knowledge w (2 * k) = knowledge.act (b.replay f.ext) (f.row knowledge u k) := by
  show knowledge.act (decl.weaken (moveExt (F' := w.frame) f.ext)) (w.label (2 * k)) =
    knowledge.act (b.replay f.ext) (knowledge.act (decl.weaken f.ext) (u.label k))
  rw [b.label_even, b.act_replay_weaken]

theorem Beside.row_odd (k : ℕ) :
    (b.replayFiring Q f).row knowledge w (2 * k + 1) =
      knowledge.act (Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right)
        (t.label k) := by
  show knowledge.act (decl.weaken (moveExt (F' := w.frame) f.ext)) (w.label (2 * k + 1)) = _
  rw [b.label_odd, act_act]

theorem Beside.opened_take :
    ((b.replayFiring Q f).opened knowledge).take =
      (f.opened knowledge).take.map (knowledge.act (b.replay f.ext)) := by
  show f.rule.body.take.map (knowledge.act (Assignment.compose (b.replay f.ext) f.opening)) =
    (f.rule.body.take.map (knowledge.act f.opening)).map (knowledge.act (b.replay f.ext))
  rw [List.map_map]
  exact List.map_congr_left fun o _ => (act_act _ _ o).symm

theorem Beside.opened_read :
    ((b.replayFiring Q f).opened knowledge).read =
      (f.opened knowledge).read.map (knowledge.act (b.replay f.ext)) := by
  show f.rule.body.read.map (knowledge.act (Assignment.compose (b.replay f.ext) f.opening)) =
    (f.rule.body.read.map (knowledge.act f.opening)).map (knowledge.act (b.replay f.ext))
  rw [List.map_map]
  exact List.map_congr_left fun o _ => (act_act _ _ o).symm

theorem Beside.opened_produce :
    ((b.replayFiring Q f).opened knowledge).produce =
      (f.opened knowledge).produce.map (knowledge.act (b.replay f.ext)) := by
  show f.rule.body.produce.map (knowledge.act (Assignment.compose (b.replay f.ext) f.opening)) =
    (f.rule.body.produce.map (knowledge.act f.opening)).map (knowledge.act (b.replay f.ext))
  rw [List.map_map]
  exact List.map_congr_left fun o _ => (act_act _ _ o).symm

theorem Beside.opened_tell :
    ((b.replayFiring Q f).opened knowledge).tell =
      knowledge.applyStore (b.replay f.ext) (f.opened knowledge).tell := by
  show f.rule.body.tell.map (fun pair =>
      (knowledge.act (Assignment.compose (b.replay f.ext) f.opening) pair.1,
        knowledge.act (Assignment.compose (b.replay f.ext) f.opening) pair.2)) =
    (f.rule.body.tell.map (fun pair => (knowledge.act f.opening pair.1, knowledge.act f.opening pair.2))).map
      (fun e => (knowledge.act (b.replay f.ext) e.1, knowledge.act (b.replay f.ext) e.2))
  rw [List.map_map]
  exact List.map_congr_left fun e _ => by
    simp only [Function.comp_apply, act_act]

theorem Beside.opened_checks :
    ((b.replayFiring Q f).opened knowledge).checks =
      (f.opened knowledge).checks.map (Check.map (knowledge.act (b.replay f.ext))) := by
  show f.rule.body.checks.map (Check.map (knowledge.act (Assignment.compose (b.replay f.ext) f.opening))) =
    (f.rule.body.checks.map (Check.map (knowledge.act f.opening))).map
      (Check.map (knowledge.act (b.replay f.ext)))
  rw [List.map_map]
  refine List.map_congr_left fun c _ => ?_
  cases c <;> simp only [Function.comp_apply, Check.map, act_act]

theorem Beside.matching_take :
    (b.replayFiring Q f).matching knowledge w ((b.replayFiring Q f).opened knowledge).take
        (b.replayFiring Q f).selection.taken =
      knowledge.applyStore (b.replay f.ext)
        (f.matching knowledge u (f.opened knowledge).take f.selection.taken) := by
  rw [b.opened_take]
  show List.zipWith (fun p o => (p, (b.replayFiring Q f).row knowledge w o))
      ((f.opened knowledge).take.map (knowledge.act (b.replay f.ext))) (f.selection.taken.map (2 * ·)) =
    (List.zipWith (fun p o => (p, f.row knowledge u o)) (f.opened knowledge).take f.selection.taken).map
      (fun e => (knowledge.act (b.replay f.ext) e.1, knowledge.act (b.replay f.ext) e.2))
  rw [List.zipWith_map, List.map_zipWith]
  simp only [b.row_even]

theorem Beside.matching_read :
    (b.replayFiring Q f).matching knowledge w ((b.replayFiring Q f).opened knowledge).read
        (b.replayFiring Q f).selection.read =
      knowledge.applyStore (b.replay f.ext)
        (f.matching knowledge u (f.opened knowledge).read f.selection.read) := by
  rw [b.opened_read]
  show List.zipWith (fun p o => (p, (b.replayFiring Q f).row knowledge w o))
      ((f.opened knowledge).read.map (knowledge.act (b.replay f.ext))) (f.selection.read.map (2 * ·)) =
    (List.zipWith (fun p o => (p, f.row knowledge u o)) (f.opened knowledge).read f.selection.read).map
      (fun e => (knowledge.act (b.replay f.ext) e.1, knowledge.act (b.replay f.ext) e.2))
  rw [List.zipWith_map, List.map_zipWith]
  simp only [b.row_even]

/-- The old knowledge, replayed: what `w` knew, read at the extended frame, is what `u` knew read
there and carried along the replay, together with `t`'s knowledge. -/
theorem Beside.weakened_iff (e : Equation (Observation sig (decl.target (moveExt (F' := w.frame) f.ext)).arity)) :
    e ∈ knowledge.applyStore (decl.weaken (moveExt (F' := w.frame) f.ext)) w.knowledge ↔
      e ∈ knowledge.applyStore (b.replay f.ext) (knowledge.applyStore (decl.weaken f.ext) u.knowledge) ∨
        e ∈ knowledge.applyStore
          (Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right) t.knowledge := by
  constructor
  · intro member
    obtain ⟨e₀, inW, rfl⟩ := List.mem_map.mp member
    rcases (b.knowledge_iff e₀).mp inW with inU | inT
    · obtain ⟨e₁, inU', rfl⟩ := List.mem_map.mp inU
      refine Or.inl (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨e₁, inU', rfl⟩, ?_⟩)
      simp only [b.act_replay_weaken]
    · obtain ⟨e₁, inT', rfl⟩ := List.mem_map.mp inT
      refine Or.inr (List.mem_map.mpr ⟨e₁, inT', ?_⟩)
      simp only [act_act]
  · rintro (inU | inT)
    · obtain ⟨e₀, inU', rfl⟩ := List.mem_map.mp inU
      obtain ⟨e₁, inU'', rfl⟩ := List.mem_map.mp inU'
      refine List.mem_map.mpr ⟨_, (b.knowledge_iff _).mpr (Or.inl (List.mem_map.mpr ⟨e₁, inU'', rfl⟩)), ?_⟩
      simp only [b.act_replay_weaken]
    · obtain ⟨e₁, inT', rfl⟩ := List.mem_map.mp inT
      refine List.mem_map.mpr ⟨_, (b.knowledge_iff _).mpr (Or.inr (List.mem_map.mpr ⟨e₁, inT', rfl⟩)), ?_⟩
      simp only [act_act]

/-- **The information of the replayed firing** is the replayed information together with `t`'s
knowledge. -/
theorem Beside.information_iff
    (e : Equation (Observation sig (decl.target (moveExt (F' := w.frame) f.ext)).arity)) :
    e ∈ (b.replayFiring Q f).information knowledge w ↔
      e ∈ knowledge.applyStore (b.replay f.ext) (f.information knowledge u) ∨
        e ∈ knowledge.applyStore
          (Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right) t.knowledge := by
  have weakened := b.weakened_iff f e
  have take := b.matching_take Q f
  have read := b.matching_read Q f
  have tell := b.opened_tell Q f
  change e ∈ knowledge.applyStore (decl.weaken (moveExt (F' := w.frame) f.ext)) w.knowledge ++
      (b.replayFiring Q f).matching knowledge w ((b.replayFiring Q f).opened knowledge).take
        (b.replayFiring Q f).selection.taken ++
      (b.replayFiring Q f).matching knowledge w ((b.replayFiring Q f).opened knowledge).read
        (b.replayFiring Q f).selection.read ++
      ((b.replayFiring Q f).opened knowledge).tell ↔
    e ∈ knowledge.applyStore (b.replay f.ext)
        (knowledge.applyStore (decl.weaken f.ext) u.knowledge ++
          f.matching knowledge u (f.opened knowledge).take f.selection.taken ++
          f.matching knowledge u (f.opened knowledge).read f.selection.read ++
          (f.opened knowledge).tell) ∨
      e ∈ knowledge.applyStore
        (Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right) t.knowledge
  rw [take, read, tell]
  simp only [Interface.Frames.applyStore, List.map_append, List.mem_append] at weakened ⊢
  rw [weakened]
  tauto

/-- **Solutions of the replayed information**: an instantiation solves it exactly when, along the
replay, it solves the firing's information at `u`, and along `right`, `t`'s knowledge. -/
theorem Beside.models_iff {B : Frame sig}
    (σ : Assignment (decl.target (moveExt (F' := w.frame) f.ext)).arity B.arity) :
    knowledge.Models σ ((b.replayFiring Q f).information knowledge w) ↔
      knowledge.Models (Assignment.compose σ (b.replay f.ext)) (f.information knowledge u) ∧
        knowledge.Models (Assignment.compose σ
          (Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right)) t.knowledge := by
  constructor
  · intro solved
    refine ⟨(Frames.models_applyStore (X := knowledge) (b.replay f.ext) σ _).mp ?_,
      (Frames.models_applyStore (X := knowledge) _ σ _).mp ?_⟩
    · exact fun e member => solved e ((b.information_iff Q f e).mpr (Or.inl member))
    · exact fun e member => solved e ((b.information_iff Q f e).mpr (Or.inr member))
  · rintro ⟨one, two⟩ e member
    rcases (b.information_iff Q f e).mp member with inside | inside
    · exact (Frames.models_applyStore (X := knowledge) (b.replay f.ext) σ _).mpr one e inside
    · exact (Frames.models_applyStore (X := knowledge) _ σ _).mpr two e inside

/-- **A firing of a monotone rule admitted at `u` is admitted at `w` when replayed**, provided `t`'s
knowledge is solvable. An `any` query keeps its witness, at the doubled identity. -/
theorem Beside.replay_admits (solvable : knowledge.Solvable t.knowledge) (admitted : f.Admits knowledge u)
    (monotone : MonotoneRule f.rule) : (b.replayFiring Q f).Admits knowledge w := by
  obtain ⟨⟨fresh, takenNodup, madeNodup, takeLength, readLength, produceLength, collectLength⟩,
    enabled, solvableInformation, entails⟩ := admitted
  have doubleInjective : Function.Injective (2 * · : ℕ → ℕ) := fun a a' same => by
    have twice : 2 * a = 2 * a' := same
    omega
  refine ⟨⟨?_, takenNodup.map doubleInjective, madeNodup.map doubleInjective, ?_, ?_, ?_, collectLength⟩,
    ?_, ?_, ?_⟩
  · intro B g' h
    obtain ⟨u', onState, onRule⟩ := fresh B (Assignment.compose g' b.left) h
    obtain ⟨v, onReplay, onRight⟩ := b.extend_copair f.ext u' (Assignment.compose g' b.right)
    refine ⟨v, fun o mentioned => ?_, fun o inside => ?_⟩
    · rcases b.mentions mentioned with ⟨o₀, mentioned₀, rfl⟩ | ⟨o₁, rfl⟩
      · show knowledge.E (knowledge.act v (knowledge.act (decl.weaken (moveExt (F' := w.frame) f.ext))
            (knowledge.act b.left o₀))) (knowledge.act g' (knowledge.act b.left o₀))
        rw [← b.act_replay_weaken, act_act (b.replay f.ext) v, onReplay, act_act b.left g']
        exact onState o₀ mentioned₀
      · show knowledge.E (knowledge.act v (knowledge.act (decl.weaken (moveExt (F' := w.frame) f.ext))
            (knowledge.act b.right o₁))) (knowledge.act g' (knowledge.act b.right o₁))
        rw [act_act b.right (decl.weaken (moveExt (F' := w.frame) f.ext)), act_act _ v, onRight,
          act_act b.right g']
        exact knowledge_refl _
    · show knowledge.E (knowledge.act v (knowledge.act (Assignment.compose (b.replay f.ext) f.opening) o))
        (knowledge.act h o)
      rw [act_act _ v, Assignment.compose_associative, onReplay, ← act_act]
      exact onRule o inside
  · show f.rule.body.take.length = (f.selection.taken.map (2 * ·)).length
    rw [List.length_map]
    exact takeLength
  · show f.rule.body.read.length = (f.selection.read.map (2 * ·)).length
    rw [List.length_map]
    exact readLength
  · show f.rule.body.produce.length = (f.selection.made.map (2 * ·)).length
    rw [List.length_map]
    exact produceLength
  · refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, ?_, fun query inside => ?_⟩
    · change o ∈ (f.selection.taken.map (2 * ·)).toFinset at inside
      obtain ⟨k, inTaken, rfl⟩ := (mem_doubled_iff _ o).mp inside
      rw [b.present]
      exact Finset.mem_union_left _ ((even_mem_map _ k).mpr
        (enabled.taken_subset (List.mem_toFinset.mpr inTaken)))
    · change o ∈ (f.selection.read.map (2 * ·)).toFinset at inside
      obtain ⟨k, inRead, rfl⟩ := (mem_doubled_iff _ o).mp inside
      rw [b.present]
      exact Finset.mem_union_left _ ((even_mem_map _ k).mpr
        (enabled.kept_subset (List.mem_toFinset.mpr inRead)))
    · refine Finset.disjoint_left.mpr fun o inTaken inRead => ?_
      change o ∈ (f.selection.taken.map (2 * ·)).toFinset at inTaken
      change o ∈ (f.selection.read.map (2 * ·)).toFinset at inRead
      obtain ⟨k, takenK, rfl⟩ := (mem_doubled_iff _ o).mp inTaken
      exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr takenK)
        (List.mem_toFinset.mpr ((mem_doubled _ k).mp inRead))
    · refine Finset.disjoint_left.mpr fun o inMade inPresent => ?_
      change o ∈ (f.selection.made.map (2 * ·)).toFinset at inMade
      obtain ⟨k, madeK, rfl⟩ := (mem_doubled_iff _ o).mp inMade
      rw [b.present, Finset.mem_union] at inPresent
      rcases inPresent with inU | inT
      · exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr madeK)
          ((even_mem_map _ k).mp inU)
      · exact even_not_mem_odd_map _ k inT
    · exact absurd inside List.not_mem_nil
  · obtain ⟨σ, solvesσ⟩ := (ByInstantiation.solvable_iff _).mp solvableInformation
    obtain ⟨ρ, solvesρ⟩ := (ByInstantiation.solvable_iff _).mp solvable
    obtain ⟨v, onReplay, onRight⟩ := b.extend_copair (B := groundFrame) f.ext σ ρ
    refine ⟨groundFrame, v, (b.models_iff Q f v).mpr ⟨?_, ?_⟩⟩
    · rw [onReplay]
      exact ByInstantiation.models_of_groundSolves solvesσ
    · rw [onRight]
      exact ByInstantiation.models_of_groundSolves solvesρ
  · intro B σ solved
    have holds := entails B (Assignment.compose σ (b.replay f.ext)) ((b.models_iff Q f σ).mp solved).1
    refine ⟨fun c member => ?_, fun q member => ?_⟩
    · rw [b.opened_checks] at member
      obtain ⟨c₀, inside, rfl⟩ := List.mem_map.mp member
      have atC₀ := holds.1 c₀ inside
      obtain ⟨c₁, inRule, rfl⟩ := List.mem_map.mp inside
      rcases monotone.1 c₁ inRule with ⟨l, l', rfl⟩ | ⟨p, rfl⟩
      · show knowledge.E (knowledge.act σ (knowledge.act (b.replay f.ext) (knowledge.act f.opening l)))
          (knowledge.act σ (knowledge.act (b.replay f.ext) (knowledge.act f.opening l')))
        rw [act_act (b.replay f.ext) σ, act_act (b.replay f.ext) σ]
        exact atC₀
      · obtain ⟨k, present, equal⟩ := atC₀
        refine ⟨2 * k, ?_, ?_⟩
        · rw [b.present]
          exact Finset.mem_union_left _ ((even_mem_map _ k).mpr present)
        · show knowledge.E (knowledge.act σ (knowledge.act (b.replay f.ext) (knowledge.act f.opening p)))
            (knowledge.act σ ((b.replayFiring Q f).row knowledge w (2 * k)))
          rw [b.row_even Q f k, act_act (b.replay f.ext) σ, act_act (b.replay f.ext) σ]
          exact equal
    · have empty : (b.replayFiring Q f).collectOpened knowledge = [] := by
        show f.rule.collect.map (knowledge.act (Assignment.compose (b.replay f.ext) f.opening)) = []
        rw [monotone.2]
        rfl
      rw [empty] at member
      exact absurd member (by simp)

/-- **After the firing, the replayed result is again beside `t`.** -/
def Beside.replayResult : Beside t (f.result knowledge u) ((b.replayFiring Q f).result knowledge w) where
  left := b.replay f.ext
  right := Assignment.compose (decl.weaken (moveExt (F' := w.frame) f.ext)) b.right
  copair g h := b.extend_copair f.ext g h
  knowledge_iff e := b.information_iff Q f e
  present := by
    show fire w.present (evenSelection f.selection).commit =
      (fire u.present f.selection.commit).map evenEmbedding ∪ t.present.map oddEmbedding
    ext o
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' o
    · simp only [Finset.mem_union, mem_fire, b.present, even_mem_map, even_not_mem_odd_map, or_false,
        Selection.commit, evenSelection, List.mem_toFinset, double_mem_map]
    · simp only [Finset.mem_union, mem_fire, b.present, odd_not_mem_even_map, odd_mem_map, false_or,
        Selection.commit, evenSelection, List.mem_toFinset, odd_not_mem_map_double, not_false_eq_true,
        and_true, or_false]
  label_even k := by
    show RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig) ((b.replayFiring Q f).row knowledge w)
        (f.selection.made.map (2 * ·)) ((b.replayFiring Q f).opened knowledge).produce (2 * k) =
      knowledge.act (b.replay f.ext) (RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig)
        (f.row knowledge u) f.selection.made (f.opened knowledge).produce k)
    rw [b.opened_produce]
    exact relabel_doubled _ _ _ (b.row_even Q f) _ _ k
  label_odd k := by
    show RuleSyntax.relabel (Tm := RuleSyntax.Contextual.Terms sig) ((b.replayFiring Q f).row knowledge w)
        (f.selection.made.map (2 * ·)) ((b.replayFiring Q f).opened knowledge).produce (2 * k + 1) = _
    rw [RuleSyntax.Firing.relabel_of_not_mem (Tm := RuleSyntax.Contextual.Terms sig) _ _ _
      (odd_not_mem_map_double f.selection.made k)]
    exact b.row_odd Q f k

end Replay

/-! ## Runs, barbs, and success beside a neighbour -/

/-- **Every run of a monotone program is replayed beside a neighbour with solvable knowledge**, up to
the renaming the tensor does. -/
theorem Beside.runs {t : ByInstantiation.State} (solvable : knowledge.Solvable t.knowledge) {P : Prog}
    (monotone : ∀ r ∈ P, MonotoneRule r) (Q : Prog) {u u' : ByInstantiation.State}
    (run : Relation.ReflTransGen (ProgramMoves P) u u') {w : ByInstantiation.State} (b : Beside t u w) :
    ∃ w', Relation.ReflTransGen (ProgramMoves (P ∪ Q)) w w' ∧ Nonempty (Beside t u' w') := by
  induction run with
  | refl => exact ⟨w, .refl, ⟨b⟩⟩
  | tail _ last ih =>
      obtain ⟨w₁, run₁, ⟨b₁⟩⟩ := ih
      obtain ⟨f, admitted, rfl⟩ := last
      exact ⟨_, run₁.tail ⟨b₁.replayFiring Q f,
        b₁.replay_admits Q f solvable admitted (monotone _ f.member), rfl⟩, ⟨b₁.replayResult Q f⟩⟩

/-- **A step of the program `P` by a firing of a positive rule.** -/
def PositiveMoves (P : Prog) (s s' : ByInstantiation.State) : Prop :=
  ∃ f : RuleSyntax.Firing ℕ decl P s.frame, f.Admits knowledge s ∧ RuleSyntax.Scope.Positive f.rule ∧
    f.result knowledge s = s'

/-- **Every run of positive firings is replayed beside a neighbour with solvable knowledge**, up to the
renaming the tensor does; the program may have other rules. -/
theorem Beside.positiveRuns {t : ByInstantiation.State} (solvable : knowledge.Solvable t.knowledge)
    {P : Prog} (Q : Prog) {u u' : ByInstantiation.State} (run : Relation.ReflTransGen (PositiveMoves P) u u')
    {w : ByInstantiation.State} (b : Beside t u w) :
    ∃ w', Relation.ReflTransGen (ProgramMoves (P ∪ Q)) w w' ∧ Nonempty (Beside t u' w') := by
  induction run with
  | refl => exact ⟨w, .refl, ⟨b⟩⟩
  | tail _ last ih =>
      obtain ⟨w₁, run₁, ⟨b₁⟩⟩ := ih
      obtain ⟨f, admitted, positive, rfl⟩ := last
      exact ⟨_, run₁.tail ⟨b₁.replayFiring Q f,
        b₁.replay_admits Q f solvable admitted (positive_monotone positive), rfl⟩,
        ⟨b₁.replayResult Q f⟩⟩

/-- **A may-barb of `u` is a may-barb of `w`**, when `t`'s knowledge is solvable. -/
theorem Beside.mayBarb {t u w : ByInstantiation.State} (b : Beside t u w)
    (solvable : knowledge.Solvable t.knowledge)
    {p : RuleSyntax.Equivalence.Pattern (RuleSyntax.Contextual.Terms sig)}
    (barb : RuleSyntax.Equivalence.MayBarb knowledge p u) : RuleSyntax.Equivalence.MayBarb knowledge p w := by
  obtain ⟨o, present, B, σ, h, known, equal⟩ := barb
  obtain ⟨ρ, solvesρ⟩ := (ByInstantiation.solvable_iff _).mp solvable
  obtain ⟨v, onLeft, onRight⟩ := b.copair (B := groundFrame) (Assignment.compose (someGrounding B) σ) ρ
  refine ⟨2 * o, ?_, groundFrame, v, Assignment.compose (someGrounding B) h, ?_, ?_⟩
  · rw [b.present]
    exact Finset.mem_union_left _ ((even_mem_map _ o).mpr present)
  · intro e member
    rcases (b.knowledge_iff e).mp member with inU | inT
    · obtain ⟨e₀, inU', rfl⟩ := List.mem_map.mp inU
      show knowledge.E (knowledge.act v (knowledge.act b.left e₀.1))
        (knowledge.act v (knowledge.act b.left e₀.2))
      rw [act_act, act_act, onLeft]
      exact ByInstantiation.models_of_groundSolves
        (ByInstantiation.groundSolves_of_models known (someGrounding B)) e₀ inU'
    · obtain ⟨e₁, inT', rfl⟩ := List.mem_map.mp inT
      show knowledge.E (knowledge.act v (knowledge.act b.right e₁.1))
        (knowledge.act v (knowledge.act b.right e₁.2))
      rw [act_act, act_act, onRight]
      exact ByInstantiation.models_of_groundSolves solvesρ e₁ inT'
  · show knowledge.E (knowledge.act v (w.label (2 * o)))
      (knowledge.act (Assignment.compose (someGrounding B) h) p.term)
    rw [b.label_even, act_act, onLeft, ← act_act, ← act_act]
    exact knowledge.preserves (a := B) (b := groundFrame) (someGrounding B) equal

/-- **Reachable may-barbs of a monotone program survive a neighbour with solvable knowledge**, any
rows and any program, for every pattern. -/
theorem reaches_barb_beside {t : ByInstantiation.State} (solvable : knowledge.Solvable t.knowledge)
    {P : Prog} (monotone : ∀ r ∈ P, MonotoneRule r) (Q : Prog) {s : ByInstantiation.State}
    {p : RuleSyntax.Equivalence.Pattern (RuleSyntax.Contextual.Terms sig)}
    (reaches : ∃ s', Relation.ReflTransGen (ProgramMoves P) s s' ∧
      RuleSyntax.Equivalence.MayBarb knowledge p s') :
    ∃ w', Relation.ReflTransGen (ProgramMoves (P ∪ Q)) (tensor s t) w' ∧
      RuleSyntax.Equivalence.MayBarb knowledge p w' := by
  obtain ⟨s', run, barb⟩ := reaches
  obtain ⟨w', run', ⟨b⟩⟩ := Beside.runs solvable monotone Q run (besideTensor s t)
  exact ⟨w', run', b.mayBarb solvable barb⟩

theorem systemRuns_states {P : Prog} {s : ByInstantiation.State} {T : System}
    (run : Relation.ReflTransGen SystemReduces ⟨P, s⟩ T) :
    T.program = P ∧ Relation.ReflTransGen (ProgramMoves P) s T.state := by
  induction run with
  | refl => exact ⟨rfl, .refl⟩
  | @tail B C _ last ih =>
      obtain ⟨same, run⟩ := ih
      obtain ⟨keeps, moved⟩ := last
      obtain ⟨program, state⟩ := B
      change program = P at same
      subst same
      exact ⟨keeps, run.tail moved⟩

theorem systemRuns_of_states {P : Prog} {s s' : ByInstantiation.State}
    (run : Relation.ReflTransGen (ProgramMoves P) s s') :
    Relation.ReflTransGen SystemReduces ⟨P, s⟩ ⟨P, s'⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ last ih => exact ih.tail ⟨rfl, last⟩

/-- **A monotone system is switched off by no composable neighbour.** If a system whose rules have
only equation checks and `any` queries and no collect pattern reaches success, then beside every
system with which its joint knowledge is solvable, whatever that system's rows and rules, the
composite reaches success. -/
theorem succeeds_beside {ω : G [] .nm} {S T : System}
    (monotone : ∀ r ∈ S.program, MonotoneRule r)
    (composable : (stepParallelSolvable ω).composable S T)
    (succeeds : (stepParallelSolvable ω).Succeeds S) :
    (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par S T) := by
  obtain ⟨P, s⟩ := S
  obtain ⟨S', run, shows⟩ := succeeds
  obtain ⟨_, states⟩ := systemRuns_states run
  obtain ⟨w', run', shows'⟩ := reaches_barb_beside ((tensor_solvable_iff _ _).mp composable).2
    monotone T.program ⟨S'.state, states, shows⟩
  exact ⟨⟨P ∪ T.program, w'⟩, systemRuns_of_states run', shows'⟩

/-- **The dividing line.** If a composable neighbour switches a system off, the system's program has
a rule with a none check, a count check or a collect pattern. -/
theorem switched_has_guard {ω : G [] .nm} {S T : System}
    (composable : (stepParallelSolvable ω).composable S T)
    (succeeds : (stepParallelSolvable ω).Succeeds S)
    (blocked : ¬ (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par S T)) :
    ∃ r ∈ S.program, (∃ c ∈ r.body.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n) ∨
      r.collect ≠ [] := by
  by_contra none
  refine blocked (succeeds_beside (fun r member => ⟨fun c inside => ?_, ?_⟩) composable succeeds)
  · cases c with
    | equal l l' => exact Or.inl ⟨l, l', rfl⟩
    | predicate quantifier p =>
        cases quantifier with
        | any => exact Or.inr ⟨p, rfl⟩
        | none => exact absurd ⟨r, member, Or.inl ⟨_, inside, Or.inl ⟨p, rfl⟩⟩⟩ none
    | count p n => exact absurd ⟨r, member, Or.inl ⟨_, inside, Or.inr ⟨p, n, rfl⟩⟩⟩ none
  · by_contra nonempty
    exact none ⟨r, member, Or.inr nonempty⟩

/-- **The dividing line, run by run.** If a composable neighbour switches a system off, then no run
of the system alone that fires only positive rules reaches success: every run of it to success fires
a rule that is not positive. -/
theorem switched_every_run_guarded {ω : G [] .nm} {S T : System}
    (composable : (stepParallelSolvable ω).composable S T)
    (blocked : ¬ (stepParallelSolvable ω).Succeeds ((stepParallelSolvable ω).par S T)) :
    ¬ ∃ s', Relation.ReflTransGen (PositiveMoves S.program) S.state s' ∧ OutBarb ω s' := by
  rintro ⟨s', run, shows⟩
  obtain ⟨w', run', ⟨b⟩⟩ := Beside.positiveRuns ((tensor_solvable_iff _ _).mp composable).2 T.program run
    (besideTensor S.state T.state)
  exact blocked ⟨⟨S.program ∪ T.program, w'⟩, systemRuns_of_states run',
    b.mayBarb ((tensor_solvable_iff _ _).mp composable).2 shows⟩

/-- The same for the calculus: every switching pair has such a rule in its first system. -/
theorem switchable_has_guard {ω : G [] .nm} (switchable : (stepParallelSolvable ω).Switchable) :
    ∃ S : System, ∃ r ∈ S.program,
      (∃ c ∈ r.body.checks, (∃ p, c = Check.predicate .none p) ∨ ∃ p n, c = Check.count p n) ∨ r.collect ≠ [] := by
  obtain ⟨S, T, composable, succeeds, blocked⟩ := switchable
  exact ⟨S, switched_has_guard composable succeeds blocked⟩

/-! ## The translation of the reflective calculus is never switched off -/

/-- **The four-rule program is positive.** -/
theorem image_positive : ∀ r ∈ ByInstantiation.program, RuleSyntax.Scope.Positive r := by
  intro r member
  obtain ⟨checks, collect, _⟩ := program_positive r member
  exact ⟨fun c inside => by rw [checks] at inside; exact absurd inside List.not_mem_nil, collect⟩

/-- **The translation of a process is switched off by no composable neighbour.** -/
theorem image_never_switched {ω : G [] .nm} (closed : Closed ω) (P : RhoProcess) (T : System)
    (composable : (stepParallelSolvable ω).composable ((rhoIntoStepSolvable closed).map P) T)
    (succeeds : (stepParallelSolvable ω).Succeeds ((rhoIntoStepSolvable closed).map P)) :
    (stepParallelSolvable ω).Succeeds
      ((stepParallelSolvable ω).par ((rhoIntoStepSolvable closed).map P) T) :=
  succeeds_beside (fun r member => positive_monotone (image_positive r member)) composable succeeds

/-- **The hypotheses have an instance together, with a neighbour that has a row and a rule guarded by
none queries**: the system of the four-rule program with the row `ω!(0)` is positive and succeeds; it is
composable with the system holding the row `*@0` and the none-guarded rule, which is not positive;
side by side they succeed. -/
theorem positive_beside_guarded {ω : G [] .nm} (closed : Closed ω) :
    (∀ r ∈ (outputSystem ω).program, RuleSyntax.Scope.Positive r) ∧
      (stepParallelSolvable ω).composable (outputSystem ω) ⟨{guardedSpawn ω}, single blockerRow⟩ ∧
      (stepParallelSolvable ω).Succeeds (outputSystem ω) ∧
      ¬ RuleSyntax.Scope.Positive (guardedSpawn ω) ∧
      (stepParallelSolvable ω).Succeeds
        ((stepParallelSolvable ω).par (outputSystem ω) ⟨{guardedSpawn ω}, single blockerRow⟩) := by
  have positive : ∀ r ∈ (outputSystem ω).program, RuleSyntax.Scope.Positive r := image_positive
  have composable : (stepParallelSolvable ω).composable (outputSystem ω)
      ⟨{guardedSpawn ω}, single blockerRow⟩ := by
    refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
    intro e member
    change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
    simp [Interface.Frames.applyStore] at member
  have succeeds : (stepParallelSolvable ω).Succeeds (outputSystem ω) :=
    ⟨outputSystem ω, .refl, single_output_barb closed⟩
  refine ⟨positive, composable, succeeds, ?_,
    succeeds_beside (fun r member => positive_monotone (positive r member)) composable succeeds⟩
  rintro ⟨checks, _⟩
  obtain ⟨l, l', same⟩ := checks _ (List.mem_singleton_self _)
  cases same

/-! ## The calculus of positive systems -/

/-- **The calculus of positive systems**: systems whose rules have only equation checks and no collect query
pattern, composed and observed as in `stepParallelSolvable`; the union of two positive programs is
positive. -/
def positiveParallel (ω : G [] .nm) : ParallelCalculus.{1} where
  Term := {S : System // ∀ r ∈ S.program, RuleSyntax.Scope.Positive r}
  step S T := SystemReduces S.1 T.1
  par S T := ⟨(stepParallelSolvable ω).par S.1 T.1, fun r member =>
    ((Set.mem_union r S.1.program T.1.program).mp member).elim (S.2 r) (T.2 r)⟩
  composable S T := (stepParallelSolvable ω).composable S.1 T.1
  success S := OutBarb ω S.1.state
  same := Eq

theorem positive_succeeds_iff (ω : G [] .nm) (S : (positiveParallel ω).Term) :
    (positiveParallel ω).Succeeds S ↔ (stepParallelSolvable ω).Succeeds S.1 := by
  constructor
  · rintro ⟨T, run, shows⟩
    have lowered : ∀ T', Relation.ReflTransGen (positiveParallel ω).step S T' →
        Relation.ReflTransGen SystemReduces S.1 T'.1 := by
      intro T' run'
      induction run' with
      | refl => exact .refl
      | tail _ last ih => exact ih.tail last
    exact ⟨T.1, lowered T run, shows⟩
  · rintro ⟨T, run, shows⟩
    have lifted : ∀ T', Relation.ReflTransGen SystemReduces S.1 T' →
        ∃ positive : ∀ r ∈ T'.program, RuleSyntax.Scope.Positive r,
          Relation.ReflTransGen (positiveParallel ω).step S ⟨T', positive⟩ := by
      intro T' run'
      induction run' with
      | refl => exact ⟨S.2, .refl⟩
      | tail _ last ih =>
          obtain ⟨positive, run''⟩ := ih
          exact ⟨fun r member => positive r (last.1 ▸ member), run''.tail last⟩
    obtain ⟨positive, run'⟩ := lifted T run
    exact ⟨⟨T, positive⟩, run', shows⟩

/-- **The calculus of positive systems is not switchable.** -/
theorem positiveParallel_not_switchable (ω : G [] .nm) : ¬ (positiveParallel ω).Switchable := by
  rintro ⟨S, T, composable, succeeds, blocked⟩
  exact blocked ((positive_succeeds_iff ω _).mpr
    (succeeds_beside (fun r member => positive_monotone (S.2 r member)) composable
      ((positive_succeeds_iff ω S).mp succeeds)))

/-- **Success at once persists beside every composable neighbour**, for every system. -/
theorem success_persists_composable (ω : G [] .nm) (S T : System)
    (composable : (stepParallelSolvable ω).composable S T)
    (shows : (stepParallelSolvable ω).success S) :
    (stepParallelSolvable ω).success ((stepParallelSolvable ω).par S T) :=
  (besideTensor S.state T.state).mayBarb ((tensor_solvable_iff _ _).mp composable).2 shows

/-- **The calculus of positive systems is not persistent in the sense of
`ParallelClosed.ParallelCalculus.Persistent`**: that notion asks success to persist beside every term,
composable or not, and beside the system of the junk state (no rule, not composable) the system with
the row `ω!(0)` shows no barb. -/
theorem positiveParallel_not_persistent {ω : G [] .nm} (closed : Closed ω) :
    ¬ (positiveParallel ω).Persistent := by
  intro persistent
  have shows := persistent.persists
    ⟨⟨∅, single (outputT ω zeroT)⟩, fun r member => absurd member (Set.notMem_empty r)⟩
    ⟨⟨∅, junk⟩, fun r member => absurd member (Set.notMem_empty r)⟩ (single_output_barb closed)
  exact RuleSyntax.Equivalence.not_mayBarb_of_unsolvable (X := knowledge) (tensor_junk_unsolvable _) shows

#print axioms besideTensor
#print axioms Beside.extend_copair
#print axioms Beside.mentions
#print axioms Beside.information_iff
#print axioms Beside.models_iff
#print axioms relabel_doubled
#print axioms positive_monotone
#print axioms Beside.replay_admits
#print axioms Beside.replayResult
#print axioms Beside.runs
#print axioms Beside.mayBarb
#print axioms reaches_barb_beside
#print axioms succeeds_beside
#print axioms switched_has_guard
#print axioms Beside.positiveRuns
#print axioms switched_every_run_guarded
#print axioms switchable_has_guard
#print axioms image_positive
#print axioms image_never_switched
#print axioms positive_beside_guarded
#print axioms positive_succeeds_iff
#print axioms positiveParallel_not_switchable
#print axioms success_persists_composable
#print axioms positiveParallel_not_persistent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
