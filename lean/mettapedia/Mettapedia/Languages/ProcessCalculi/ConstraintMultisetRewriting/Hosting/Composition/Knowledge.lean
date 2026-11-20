import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-!
# Knowledge beside a hosted program: of whose unknown it speaks

The clause `Beside.hosted` asks that the knowledge of the state says nothing more of the hosted rows than
the alternative's store. Knowledge that says more is of two kinds, with different effects.

**What the representation depends on.**

* `represents_of_same_readings`: a state that represents an alternative represents every alternative
  with the same readings.
* `represents_of_same_joint_readings`: the representation depends only on the present rows and on the
  **joint readings** of their labels under the solutions of the knowledge. Two states with the same
  present rows whose solutions read them jointly alike, each way, represent the same alternatives. This
  is the condition on knowledge as far as it is exact; the clause `Beside.hosted` is a sufficient form of
  it.

**(a) Knowledge of the alternative's unknown runs the instance of the query.** The state
`Controls.constrained` (the start of the query `ret $x` with `$x ≐ c` in its knowledge) represents the
alternative of the query `ret c` (`constrained_is_instance`), not that of `ret $x`
(`constrained_not_query`), and the answers the step shows from it are, as a set, the source's answers of
`ret c` (`constrained_answers`).

**(b) Knowledge of an equation row's private unknown adds an answer.** The program is `(= (h $y) d)`, the
query is the closed call `(h e)`, and `RowName.rowPinned` is its start with `$y ≐ c` in its knowledge, for
the row's private copy of `$y`. The clause `reads` of `Represents` holds (`RowName.reads_hold`), the
clause `independent` fails (`RowName.not_independent`), so the state represents no alternative of the
query (`RowName.not_represents`). The rule of the unmatched call is admitted there
(`RowName.unmatched_fires`): the row reads as `eqn((h c))` only. So the translated program reaches a
finished row whose answer contains `(h e)` (`RowName.extra_answer`), and every answer of the source is
`{d}` (`RowName.source_only_d`). This is the control of the clause `independent`.

**(c) The clause is sufficient, not necessary.** The same program with the query `(h $x)`, and
`Discard.pinned` its start with `$x ≐ c` in its knowledge: it represents the alternative of `(h c)`
(`Discard.pinned_is_instance`), not that of `(h $x)` (`Discard.pinned_not_query`), and the answers the
step shows from it are, as a set, the source's answers of `(h $x)` (`Discard.discarded_name_same_answers`):
the program discards its argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Classical

/-! ## What the representation depends on -/

section General

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star) {κ : Keys S} {Ty : Type}
  {P : SourceLanguage.Program κ Γ star Ty}

/-- **The representation is a statement about readings**: a state that represents an alternative
represents every alternative with the same readings. -/
theorem represents_of_same_readings {n : ℕ} {b b' : Branch κ Γ star Ty} {s : HostState S} {a : ℕ}
    (rep : Represents N P n b s a)
    (same : ∀ (B : Interface.Frames.Frame S) (r : Observation S B.arity),
      branchReads N b B r ↔ branchReads N b' B r)
    (fresh : BranchBelow n b') (noPending : b'.pending = []) : Represents N P n b' s a :=
  ⟨rep.notRow, rep.present, fun B r => (rep.reads B r).trans (same B r), rep.rows, rep.independent, fresh,
    noPending⟩

/-- **The representation depends only on the joint readings of the present rows**: a state with the same
present rows whose solutions read them jointly as the solutions of a representing state do, each way,
represents the same alternative. -/
theorem represents_of_same_joint_readings {n : ℕ} {b : Branch κ Γ star Ty} {s s' : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (present : s'.present = s.present)
    (fwd : ∀ (B : Interface.Frames.Frame S) (σ : Assignment s.frame.arity B.arity),
      (Interface.Frames.contextual S).Models σ s.knowledge →
        ∃ σ' : Assignment s'.frame.arity B.arity, (Interface.Frames.contextual S).Models σ' s'.knowledge ∧
          ∀ o ∈ s.present, instantiateObservation σ' (s'.label o) = instantiateObservation σ (s.label o))
    (bwd : ∀ (B : Interface.Frames.Frame S) (σ' : Assignment s'.frame.arity B.arity),
      (Interface.Frames.contextual S).Models σ' s'.knowledge →
        ∃ σ : Assignment s.frame.arity B.arity, (Interface.Frames.contextual S).Models σ s.knowledge ∧
          ∀ o ∈ s.present, instantiateObservation σ (s.label o) = instantiateObservation σ' (s'.label o)) :
    Represents N P n b s' a := by
  have aIn : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have rowIn : ∀ i, i < P.equations.length → i ∈ s.present := fun i small => by
    rw [rep.present]; exact Finset.mem_insert_of_mem (Finset.mem_range.mpr small)
  refine ⟨rep.notRow, present.trans rep.present, ?_, ?_, ?_, rep.fresh, rep.noPending⟩
  · intro B r
    refine Iff.trans ?_ (rep.reads B r)
    constructor
    · rintro ⟨σ', known, rfl⟩
      obtain ⟨σ, known', same⟩ := bwd B σ' known
      exact ⟨σ, known', same a aIn⟩
    · rintro ⟨σ, known, rfl⟩
      obtain ⟨σ', known', same⟩ := fwd B σ known
      exact ⟨σ', known', same a aIn⟩
  · intro B σ' known i hi
    obtain ⟨σ, known', same⟩ := bwd B σ' known
    obtain ⟨θ, row⟩ := rep.rows B σ known' i hi
    exact ⟨θ, (same i (rowIn i hi)).symm.trans row⟩
  · intro B σ' known i hi θ
    obtain ⟨σ, known', same⟩ := bwd B σ' known
    obtain ⟨σ₂, known₂, sameAlt, row⟩ := rep.independent B σ known' i hi θ
    obtain ⟨σ₂', known₂', same₂⟩ := fwd B σ₂ known₂
    exact ⟨σ₂', known₂', (same₂ a aIn).trans (sameAlt.trans (same a aIn)),
      (same₂ i (rowIn i hi)).trans row⟩

end General

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-- The frame with no names. -/
abbrev B₀ : Interface.Frames.Frame MSig := ⟨Empty, noNames⟩

/-! ## (a) Knowledge of the alternative's unknown -/

section Instance

/-- The query `c`, returned: the instance of `ret $x` at `$x := c`. -/
def qc : Comp mkeys [] () MTy := .ret cT

theorem qc_unopened : ∀ t ∈ qc.data, ∀ x ∈ support t, x.scopes = [] := by decide

/-- The alternative whose store has `$x ≐ c` and the alternative of the query `ret c` have the same
readings. -/
theorem same_readings (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity) :
    branchReads N Bx B r ↔ branchReads N (initialBranch qc) B r := by
  constructor
  · rintro ⟨σ, solved, rfl⟩
    have pinned : instantiate σ xName = instantiate σ cT := solved _ (List.mem_singleton_self _)
    refine ⟨σ, (fun e member => by cases member), ?_⟩
    show observe (altN N (evalN N (retN N (instantiate σ cT))) (emptyN N)) =
      observe (altN N (evalN N (retN N (instantiate σ xName))) (emptyN N))
    rw [pinned]
  · rintro ⟨σ, _, rfl⟩
    refine ⟨Function.update σ (fo [] [7] 0) (symAt "c"), ?_, ?_⟩
    · intro e member
      rw [List.mem_singleton.mp member]
      show instantiate (Function.update σ (fo [] [7] 0) (symAt "c")) (foD [] [7] 0) = symAt "c"
      rw [instantiate_foD, Function.update_self]
    · show observe (altN N (evalN N (retN N
          (instantiate (Function.update σ (fo [] [7] 0) (symAt "c")) (foD [] [7] 0)))) (emptyN N)) =
        observe (altN N (evalN N (retN N (symAt "c"))) (emptyN N))
      rw [instantiate_foD, Function.update_self]

/-- **The state with `$x ≐ c` in its knowledge represents the alternative of the query `ret c`.** -/
theorem constrained_is_instance : Represents N P0 0 (initialBranch qc) constrained 0 :=
  represents_of_same_readings N constrained_represents same_readings
    (start_represents N P0 qc qc_unopened).fresh (start_represents N P0 qc qc_unopened).noPending

/-- **From that state the step shows, as a set, the source's answers of the query `ret c`**: the run
theorems apply to it, for the instance of the query. -/
theorem constrained_answers :
    stepAnswersFrom N P0 constrained = Answers.sourceAnswers D P0 supply sp qc :=
  answers_beside N (D := D) (supply := supply) sp qc (fun e member => by cases member)
    (qsite := [311]) (by decide) (by decide) trivial ((beside_empty N).mpr constrained_is_instance)
    (fun o inside => absurd inside (Finset.notMem_empty o))
    (fun o inside => absurd inside (Finset.notMem_empty o))

/-- **It does not represent the alternative of the query `ret $x`**: that alternative reads with
`$x := d`, the state does not. -/
theorem constrained_not_query : ¬ Represents N P0 0 (initialBranch qx) constrained 0 := by
  intro rep
  let σ : Assignment (fam mkeys) (noNames) := closeNames [(([], [7], 0), dC)] (csym "a")
  have reads : branchReads N (initialBranch qx) ⟨Empty, noNames⟩
      (observe (encBranch N (instantiate σ) (initialBranch qx))) :=
    ⟨σ, (fun e member => by cases member), rfl⟩
  obtain ⟨σ', solved, same⟩ := (same_readings _ _).mp
    ((constrained_represents.reads ⟨Empty, noNames⟩ _).mp ((rep.reads ⟨Empty, noNames⟩ _).mpr reads))
  have terms := observe_injective same
  have args := vec1_inj (N.args_eq (vec1_inj (N.args_eq (vec2_inj (N.args_eq terms)).1)))
  have clash : (symAt "c" : Term (signature MSig noNames) [] ()) = symAt "d" := args
  simp [symAt] at clash

end Instance

/-! ## The program that discards its argument: `(= (h $y) d)` -/

section Discarding

/-- `(h x)`. -/
def hT (x : MData) : MData := tuple [sym "h", x]

/-- The equation's own variable. -/
def yv : MData := foD [] [301] 0

/-- `(= (h $y) d)`. -/
def eh : SourceLanguage.Equation mkeys [] () MTy := ⟨[301], hT yv, .ret dT⟩

/-- The program of that one equation. -/
def Ph : SourceLanguage.Program mkeys [] () MTy := ⟨[eh], fun t => .apply t⟩

/-- An equation row's private names, read by an instantiation of the start's names. -/
theorem read_rowNames {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity)
    (i : ℕ) (t : MData) :
    instantiate σ (instantiate (rowNames i) t) = instantiate (fun x => σ (.inr (i, x))) t := by
  rw [instantiate_comp]
  apply congrArg (fun ρ => instantiate ρ t)
  funext x
  exact instantiate_generator σ (.inr (i, x))

theorem inst_empty {V W : Type} {A : V → MetaArity MSig} {E : W → MetaArity MSig} (σ : Assignment A E) :
    instantiate σ (emptyN N) = emptyN N := by
  rw [emptyN, N.instantiate_node]
  exact congrArg _ (map_vec0 _)

theorem Ph_scoped : ∀ e ∈ Ph.equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  rw [List.mem_singleton.mp member]
  exact ⟨by decide, by decide, trivial⟩

variable (t : MData)
  (matches' : ∀ n, Solvable ([] ++ [(instantiate (copyAt mkeys n) (hT yv), t)] : List (Constraint mkeys [] ())))

/-- The shapes of the alternatives along a run of the query `(h t)`. -/
def Shape (b : Branch mkeys [] () MTy) : Prop :=
  b = ⟨[], .eval (.apply t), [], []⟩ ∨ (b.frames = [] ∧ (b.focus = .eval (.ret dT) ∨ b.focus = .value dT))

include matches' in
theorem move_call {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} (move : Move D Ph supply w b w' bs)
    (hb : b = ⟨[], .eval (.apply t), [], []⟩) : ∀ b' ∈ bs, b'.frames = [] ∧ b'.focus = .eval (.ret dT) := by
  cases move <;> cases hb
  · intro b' made
    simp only [Ph, List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.mem_singleton] at made
    rw [made]
    exact ⟨rfl, rfl⟩
  · rename_i none
    exact absurd (matches' w.scope) (none eh (List.mem_singleton_self _))

theorem move_ret {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    {bs : Multiset (Branch mkeys [] () D.Ty)} {K : List (Constraint mkeys [] ())}
    {ps : List (MData × Comp mkeys [] () D.Ty)} (move : Move D Ph supply w b w' bs)
    (hb : b = ⟨K, .eval (.ret dT), [], ps⟩) : ∀ b' ∈ bs, b' = ⟨K, .value dT, [], ps⟩ := by
  cases move <;> cases hb
  intro b' made
  exact Multiset.mem_singleton.mp made

include matches' in
theorem shape_runs {C : Config mkeys [] () MTy} (runs : Runs D Ph supply (Config.initial sp (.apply t)) C) :
    ∀ b ∈ C.branches, Shape t b := by
  induction runs with
  | refl =>
      intro b member
      exact .inl (Multiset.mem_singleton.mp member)
  | tail _ step ih =>
      obtain ⟨w, w', b, rest, bs, _, move⟩ := step
      have bShape := ih b (Multiset.mem_cons_self _ _)
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · rcases bShape with hb | ⟨frames, focus | focus⟩
        · obtain ⟨noFrames, isRet⟩ := move_call t matches' move hb b' made
          exact .inr ⟨noFrames, .inl isRet⟩
        · obtain ⟨K, f, fs, ps⟩ := b
          simp only at frames focus
          subst frames focus
          rw [move_ret move rfl b' made]
          exact .inr ⟨rfl, .inr rfl⟩
        · obtain ⟨K, f, fs, ps⟩ := b
          simp only at frames focus
          subst frames focus
          exact absurd move Move.value_still
      · exact ih b' (Multiset.mem_cons_of_mem kept)

include matches' in
/-- Every answer of a configuration a source run of `(h t)` reaches is `{d}`. -/
theorem only_d {C : Config mkeys [] () MTy} (runs : Runs D Ph supply (Config.initial sp (.apply t)) C) :
    ∀ A ∈ Config.answers (D := D) C, A = {dC} := by
  intro A member
  unfold Config.answers at member
  obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨bMember, finished, live⟩ := Multiset.mem_filter.mp inside
  rcases shape_runs t matches' runs b bMember with rfl | ⟨_, focus | focus⟩
  · obtain ⟨_, v, focus⟩ := finished
    cases focus
  · obtain ⟨_, v, focus'⟩ := finished
    rw [focus] at focus'
    cases focus'
  · exact answer_of_determines (g := dC) focus ⟨live, fun _ _ _ => rfl⟩

include matches' in
theorem reaches_d : ∃ C, Runs D Ph supply (Config.initial sp (.apply t)) C ∧
    ({dC} : Set MClosed) ∈ Config.answers (D := D) C := by
  have live1 := matches' 0
  refine ⟨⟨⟨1, 0, sp⟩, {⟨[] ++ [(instantiate (copyAt mkeys 0) (hT yv), t)], .value dT, [], []⟩}⟩, ?_, ?_⟩
  · refine Relation.ReflTransGen.tail
      (b := ⟨⟨1, 0, sp⟩, {⟨[] ++ [(instantiate (copyAt mkeys 0) (hT yv), t)], .eval (.ret dT), [], []⟩}⟩) ?_
      (step_one live1 (.ret _ _ _ _ _))
    exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil
      (.apply ⟨0, 0, sp⟩ [] t [] [] ⟨eh, List.mem_singleton_self _, live1⟩))
  · rw [answers_singleton (D := D) ⟨rfl, _, rfl⟩ live1,
      answer_of_determines (D := D) (g := dC) rfl ⟨live1, fun _ _ _ => rfl⟩]
    exact Multiset.mem_singleton_self _

include matches' in
/-- **The source's answers of `(h t)` are `{{d}}`**, for every `t` the left side unifies with. -/
theorem source_answers : Answers.sourceAnswers D Ph supply sp (.apply t) = {{dC}} := by
  ext A
  constructor
  · rintro ⟨C, runs, member⟩
    exact Set.mem_singleton_iff.mpr (only_d t matches' runs A member)
  · intro isD
    rw [Set.mem_singleton_iff.mp isD]
    obtain ⟨C, runs, member⟩ := reaches_d t matches'
    exact ⟨C, runs, member⟩

end Discarding

/-! ## (b) Knowledge of an equation row's private unknown -/

namespace RowName

def eT : MData := sym "e"
def heC : MClosed := ctuple [csym "h", csym "e"]

/-- The query `(h e)`, called. -/
abbrev qe : Comp mkeys [] () MTy := .apply (hT eT)

/-- The start of the query with `$y ≐ c` added to the knowledge, for the row's private copy of `$y`. -/
def rowPinned : HostState MSig :=
  ⟨startFrame mkeys, [(observe (instantiate (rowNames 0) yv), observe (instantiate (rowNames 0) cT))],
    (Hosting.start N Ph qe).present, (Hosting.start N Ph qe).label⟩

/-- The alternative's row, read by any instantiation of the start's names. -/
theorem reads_call {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation σ (rowPinned.label 1) =
      observe (altN N (evalN N (applyN N (tupleAt [symAt "h", symAt "e"]))) (emptyN N)) := by
  show observe (instantiate σ (altN N (evalN N (applyN N (instantiate queryNames (hT eT)))) (emptyN N))) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN, inst_empty, read_queryNames]
  rfl

/-- The equation row, read by an instantiation of the start's names. -/
theorem reads_row {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation σ (rowPinned.label 0) =
      observe (eqnN N (tupleAt [symAt "h", σ (.inr (0, fo [] [301] 0))])) := by
  show observe (instantiate σ (eqnN N (instantiate (rowNames 0) (hT yv)))) = _
  rw [instantiate_eqnN, read_rowNames]
  have atY : instantiate (fun x => σ (.inr (0, x))) yv = σ (.inr (0, fo [] [301] 0)) :=
    instantiate_foD (fun x => σ (.inr (0, x))) [] [301] 0
  rw [← atY]
  rfl

/-- What the knowledge says: the row's private `$y` reads as `c`. -/
theorem pinned_known {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models σ rowPinned.knowledge ↔
      σ (.inr (0, fo [] [301] 0)) = symAt "c" := by
  have atY : instantiate (fun x => σ (.inr (0, x))) yv = σ (.inr (0, fo [] [301] 0)) :=
    instantiate_foD (fun x => σ (.inr (0, x))) [] [301] 0
  constructor
  · intro solved
    have same : observe (instantiate σ (instantiate (rowNames 0) yv)) =
        observe (instantiate σ (instantiate (rowNames 0) cT)) := solved _ (List.mem_singleton_self _)
    have terms := observe_injective same
    rw [read_rowNames, read_rowNames, atY] at terms
    exact terms
  · intro isC e member
    rw [List.mem_singleton.mp member]
    show observe (instantiate σ (instantiate (rowNames 0) yv)) =
      observe (instantiate σ (instantiate (rowNames 0) cT))
    rw [read_rowNames, read_rowNames, atY, isC]
    rfl

/-- An instantiation of the start's names: the query's names by `ρ`, every private copy by `v`. -/
def pin {B : Interface.Frames.Frame MSig} (ρ : Assignment (fam mkeys) B.arity) (v : String) :
    Assignment (startArity mkeys) B.arity
  | .inl x => ρ x
  | .inr _ => symAt v

theorem pin_known {B : Interface.Frames.Frame MSig} (ρ : Assignment (fam mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models (pin ρ "c") rowPinned.knowledge :=
  (pinned_known (pin ρ "c")).mpr rfl

/-- **The clause `reads` holds**: the alternative's row reads exactly as the query's alternative. -/
theorem reads_hold (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity) :
    rowReads rowPinned 1 B r ↔ branchReads N (initialBranch qe) B r := by
  constructor
  · rintro ⟨σ, _, rfl⟩
    refine ⟨fun x => σ (.inl x), (fun e member => by cases member), ?_⟩
    rw [reads_call]
    rfl
  · rintro ⟨ρ, _, rfl⟩
    refine ⟨pin ρ "c", pin_known ρ, ?_⟩
    rw [reads_call]
    rfl

/-- **The clause `independent` fails**: no solution of the knowledge reads the equation row as
`eqn((h d))`. -/
theorem not_independent :
    ¬ ∀ (B : Interface.Frames.Frame MSig) (σ : Assignment rowPinned.frame.arity B.arity),
      (Interface.Frames.contextual MSig).Models σ rowPinned.knowledge → ∀ θ : Assignment (fam mkeys) B.arity,
        ∃ σ' : Assignment rowPinned.frame.arity B.arity,
          (Interface.Frames.contextual MSig).Models σ' rowPinned.knowledge ∧
          instantiateObservation σ' (rowPinned.label 1) = instantiateObservation σ (rowPinned.label 1) ∧
          instantiateObservation σ' (rowPinned.label 0) = eqnRow N eh θ := by
  intro independent
  obtain ⟨σ', known, _, row⟩ := independent B₀ (pin (closeNames [] (csym "a")) "c") (pin_known _)
    (closeNames [(([], [301], 0), dC)] (csym "a"))
  rw [reads_row, (pinned_known σ').mp known] at row
  have terms : tupleAt [symAt "h", symAt "c"] =
      (tupleAt [symAt "h", symAt "d"] : Term (signature MSig B₀.arity) [] ()) :=
    vec1_inj (N.args_eq (observe_injective row))
  have clash := (tuple2_inj terms).2
  simp [symAt] at clash

/-- So the state does not represent the query's alternative. -/
theorem not_represents : ¬ Represents N Ph 0 (initialBranch qe) rowPinned 1 :=
  fun rep => not_independent fun B σ known θ => rep.independent B σ known 0 (by decide) θ

/-- The canonical firing of the unmatched call's rule on the alternative's row. -/
def unmatchedFiring : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N Ph)
    rowPinned.frame :=
  canonicalAt rowPinned (unmatchedRule N) (unmatchedRule_mem N Ph) 1

theorem unmatchedSimple : Simple unmatchedFiring 1 (freshId rowPinned)
    (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
    (observe (altN N (valueN N (unk .datum)) (unk .stack))) := canonical_simple rfl rfl rfl

theorem unmatchedShapes : unmatchedFiring.Shapes (Interface.Frames.contextual MSig) rowPinned :=
  canonical_shapes rfl rfl rfl rfl

theorem present1 : (1 : ℕ) ∈ rowPinned.present := by decide

/-- The instantiation of the rule's unknowns that reads its pattern as the call `(h e)`. -/
def callFill {B : Interface.Frames.Frame MSig} : Assignment (unknownArity (S := MSig) [] ()) B.arity :=
  fill (tupleAt [symAt "h", symAt "e"]) (emptyN N) (emptyN N) (emptyN N) (emptyN N)

theorem call_matched {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    instantiateObservation (callFill (B := B)) (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) =
      instantiateObservation σ (rowPinned.label 1) := by
  rw [reads_call]
  show observe (instantiate callFill (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk]
  rfl

/-- **The rule of the unmatched call is admitted**: at every solution the equation row reads as
`eqn((h c))`, which is not `eqn` of the call `(h e)`. -/
theorem unmatched_fires : unmatchedFiring.Admits (Interface.Frames.contextual MSig) rowPinned := by
  obtain ⟨u₀, solved₀, _⟩ := simple_amalgamate unmatchedSimple unmatchedShapes.1 present1
    (pin (closeNames [] (csym "a")) "c") (callFill (B := B₀)) (pin_known _)
    (fun _ member => absurd member List.not_mem_nil) (call_matched _)
  refine ⟨unmatchedShapes, enabled_single present1 (freshId_not_mem rowPinned), ⟨_, u₀, solved₀⟩, ?_⟩
  intro B u solved
  obtain ⟨known, _, matched⟩ := simple_restrict unmatchedSimple u solved
  refine ⟨?_, ?_⟩
  · intro c member
    change c ∈ [Check.predicate .none (instantiateObservation unmatchedFiring.opening (unmatchedCheck N))] at member
    rw [List.mem_singleton] at member
    subst member
    intro o present equal
    change instantiateObservation u (instantiateObservation _ (unmatchedCheck N)) =
      instantiateObservation u (instantiateObservation _ (rowPinned.label o)) at equal
    rw [instantiateObservation_comp, instantiateObservation_comp] at equal
    rw [reads_call] at matched
    change observe (instantiate _ (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) = _ at matched
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at matched
    have onCall := vec1_inj (N.args_eq (vec1_inj (N.args_eq (vec2_inj (N.args_eq (observe_injective matched))).1)))
    change observe (instantiate _ (eqnN N (unk .datum))) = _ at equal
    rw [instantiate_eqnN] at equal
    replace equal := (congrArg (fun t => observe (eqnN N t)) onCall).symm.trans equal
    have rows : o = 1 ∨ o = 0 := by
      have inside : o ∈ ({1, 0} : Finset ℕ) := present
      simpa using inside
    rcases rows with rfl | rfl
    · rw [reads_call] at equal
      exact absurd (N.tag_eq (observe_injective equal)) (by decide)
    · rw [reads_row, (pinned_known _).mp known] at equal
      have terms : tupleAt [symAt "h", symAt "e"] =
          (tupleAt [symAt "h", symAt "c"] : Term (signature MSig B.arity) [] ()) :=
        vec1_inj (N.args_eq (observe_injective equal))
      have clash := (tuple2_inj terms).2
      simp [symAt] at clash
  · intro q member
    have empty : unmatchedFiring.collectOpened (Interface.Frames.contextual MSig) = [] := rfl
    rw [empty] at member
    simp at member

/-- **The translated program reaches a finished row whose answer contains `(h e)`.** -/
theorem extra_answer :
    ∃ s a, Fires N Ph rowPinned s ∧ a ∈ s.present ∧ StateFinished N s a ∧ heC ∈ stateAnswer N s a := by
  have made : freshId rowPinned ∈
      (unmatchedFiring.result (Interface.Frames.contextual MSig) rowPinned).present := by
    rw [simple_present unmatchedSimple]
    exact Finset.mem_insert_self _ _
  have reading : ∀ (B : Interface.Frames.Frame MSig) (r : Observation MSig B.arity),
      rowReads (unmatchedFiring.result (Interface.Frames.contextual MSig) rowPinned) (freshId rowPinned) B r ↔
        r = observe (altN N (valueN N (tupleAt [symAt "h", symAt "e"])) (emptyN N)) := by
    intro B r
    rw [rowReads_result unmatchedSimple unmatchedShapes present1]
    constructor
    · rintro ⟨h, ⟨σ, _, same⟩, _, rfl⟩
      rw [reads_call] at same
      change _ = observe (instantiate h (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) at same
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at same
      obtain ⟨onFocus, onStack⟩ := vec2_inj (N.args_eq (observe_injective same))
      have onCall := vec1_inj (N.args_eq (vec1_inj (N.args_eq onFocus)))
      show observe (instantiate h (altN N (valueN N (unk .datum)) (unk .stack))) = _
      rw [instantiate_altN, instantiate_valueN, ← onCall, ← onStack]
    · rintro rfl
      refine ⟨callFill, ⟨pin (fun _ => symAt "c") "c", ?_, (call_matched _).symm⟩,
        (fun _ member => absurd member List.not_mem_nil), ?_⟩
      · exact pin_known _
      · show observe (instantiate callFill (altN N (valueN N (unk .datum)) (unk .stack))) = _
        rw [instantiate_altN, instantiate_valueN, instantiate_unk, instantiate_unk]
        rfl
  refine ⟨_, freshId rowPinned, ⟨unmatchedFiring, unmatched_fires, rfl⟩, made,
    ⟨⟨B₀, _, (reading B₀ _).mpr rfl⟩, ?_⟩, ⟨B₀, (reading B₀ _).mpr rfl⟩⟩
  intro B r reads
  exact ⟨_, (reading B r).mp reads⟩

theorem matches_e (n : ℕ) :
    Solvable ([] ++ [(instantiate (copyAt mkeys n) (hT yv), hT eT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "e"), fun e member => by
    simp only [List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

/-- **Every answer of the source is `{d}`**: none contains `(h e)`. -/
theorem source_only_d {C : Config mkeys [] () MTy} (runs : Runs D Ph supply (Config.initial sp qe) C) :
    ∀ A ∈ Config.answers (D := D) C, A = {dC} ∧ heC ∉ A := by
  intro A member
  have isD := only_d (hT eT) matches_e runs A member
  refine ⟨isD, ?_⟩
  rw [isD]
  intro inside'
  have same : heC = dC := inside'
  simp [heC, dC, ctuple, csym] at same

end RowName

/-! ## (c) Sufficient, not necessary -/

namespace Discard

/-- The query `(h $x)`, with the query's own name. -/
abbrev qhx : Comp mkeys [] () MTy := .apply (hT xName)
/-- The query `(h c)`: its instance at `$x := c`. -/
abbrev qhc : Comp mkeys [] () MTy := .apply (hT cT)

theorem qhc_unopened : ∀ t ∈ qhc.data, ∀ x ∈ support t, x.scopes = [] := by decide

theorem matches_x (n : ℕ) :
    Solvable ([] ++ [(instantiate (copyAt mkeys n) (hT yv), hT xName)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "a"), fun e member => by
    simp only [List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

theorem matches_c (n : ℕ) :
    Solvable ([] ++ [(instantiate (copyAt mkeys n) (hT yv), hT cT)] : List (Constraint mkeys [] ())) :=
  ⟨Empty, noNames, closeNames [] (csym "c"), fun e member => by
    simp only [List.nil_append, List.mem_singleton] at member
    subst member
    rfl⟩

/-- The start of the query `(h $x)` with the equation `$x ≐ c` added to its knowledge. -/
def pinned : HostState MSig :=
  ⟨startFrame mkeys, [(observe (instantiate queryNames xName), observe (instantiate queryNames cT))],
    (Hosting.start N Ph qhx).present, (Hosting.start N Ph qhx).label⟩

/-- The alternative's row of the start of `(h t)`, read by an instantiation of the start's names. -/
theorem reads_call {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) (t : MData) :
    instantiateObservation σ ((Hosting.start N Ph (.apply (hT t))).label 1) =
      observe (altN N (evalN N (applyN N (tupleAt [symAt "h", instantiate (fun x => σ (.inl x)) t])))
        (emptyN N)) := by
  show observe (instantiate σ (altN N (evalN N (applyN N (instantiate queryNames (hT t)))) (emptyN N))) = _
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN, inst_empty, read_queryNames]
  rfl

/-- The equation row, read by an instantiation of the start's names. -/
theorem reads_row {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity)
    (q : Comp mkeys [] () MTy) :
    instantiateObservation σ ((Hosting.start N Ph q).label 0) =
      observe (eqnN N (instantiate (fun x => σ (.inr (0, x))) (hT yv))) := by
  show observe (instantiate σ (eqnN N (instantiate (rowNames 0) (hT yv)))) = _
  rw [instantiate_eqnN, read_rowNames]

/-- What the knowledge of `pinned` says: `$x` reads as `c`. -/
theorem pinned_known {B : Interface.Frames.Frame MSig} (σ : Assignment (startArity mkeys) B.arity) :
    (Interface.Frames.contextual MSig).Models σ pinned.knowledge ↔ σ (.inl (fo [] [7] 0)) = symAt "c" := by
  have left : instantiate (fun x => σ (.inl x)) xName = σ (.inl (fo [] [7] 0)) :=
    instantiate_foD (fun x => σ (.inl x)) [] [7] 0
  constructor
  · intro solved
    have same : observe (instantiate σ (instantiate queryNames xName)) =
        observe (instantiate σ (instantiate queryNames cT)) := solved _ (List.mem_singleton_self _)
    have terms := observe_injective same
    rw [read_queryNames, read_queryNames, left] at terms
    exact terms
  · intro isC e member
    rw [List.mem_singleton.mp member]
    show observe (instantiate σ (instantiate queryNames xName)) =
      observe (instantiate σ (instantiate queryNames cT))
    rw [read_queryNames, read_queryNames, left, isC]
    rfl

theorem present_rows : (Hosting.start N Ph qhc).present = {1, 0} := by decide

/-- **The state represents the alternative of the query `(h c)`.** -/
theorem pinned_is_instance : Represents N Ph 0 (initialBranch qhc) pinned 1 := by
  refine represents_of_same_joint_readings N (start_represents N Ph qhc qhc_unopened) rfl ?_ ?_
  · intro B σ _
    let σ' : Assignment (startArity mkeys) B.arity := fun y => match y with
      | .inl x => Function.update (fun x => σ (.inl x)) (fo [] [7] 0) (symAt "c") x
      | .inr p => σ (.inr p)
    have atX : σ' (.inl (fo [] [7] 0)) = symAt "c" :=
      Function.update_self (f := fun x => σ (.inl x)) (fo [] [7] 0) (symAt "c")
    refine ⟨σ', (pinned_known σ').mpr atX, ?_⟩
    intro o inside
    rw [present_rows] at inside
    simp only [Finset.mem_insert, Finset.mem_singleton] at inside
    rcases inside with rfl | rfl
    · show instantiateObservation σ' ((Hosting.start N Ph (.apply (hT xName))).label 1) =
        instantiateObservation σ ((Hosting.start N Ph (.apply (hT cT))).label 1)
      rw [reads_call, reads_call]
      have left : instantiate (fun x => σ' (.inl x)) xName = σ' (.inl (fo [] [7] 0)) :=
        instantiate_foD (fun x => σ' (.inl x)) [] [7] 0
      rw [left, atX]
      rfl
    · show instantiateObservation σ' ((Hosting.start N Ph qhx).label 0) =
        instantiateObservation σ ((Hosting.start N Ph qhc).label 0)
      rw [reads_row, reads_row]
  · intro B σ' known
    have atX := (pinned_known σ').mp known
    refine ⟨σ', fun e member => absurd member List.not_mem_nil, ?_⟩
    intro o inside
    rw [present_rows] at inside
    simp only [Finset.mem_insert, Finset.mem_singleton] at inside
    rcases inside with rfl | rfl
    · show instantiateObservation σ' ((Hosting.start N Ph (.apply (hT cT))).label 1) =
        instantiateObservation σ' ((Hosting.start N Ph (.apply (hT xName))).label 1)
      rw [reads_call, reads_call]
      have left : instantiate (fun x => σ' (.inl x)) xName = σ' (.inl (fo [] [7] 0)) :=
        instantiate_foD (fun x => σ' (.inl x)) [] [7] 0
      rw [left, atX]
      rfl
    · show instantiateObservation σ' ((Hosting.start N Ph qhc).label 0) =
        instantiateObservation σ' ((Hosting.start N Ph qhx).label 0)
      rw [reads_row, reads_row]

/-- **It does not represent the alternative of the query `(h $x)`**: that alternative reads with
`$x := d`, the state does not. The clause `Beside.hosted` fails for the query. -/
theorem pinned_not_query : ¬ Represents N Ph 0 (initialBranch qhx) pinned 1 := by
  intro rep
  let σd : Assignment (fam mkeys) (noNames) := closeNames [(([], [7], 0), dC)] (csym "a")
  have reads : branchReads N (initialBranch qhx) ⟨Empty, noNames⟩
      (observe (encBranch N (instantiate σd) (initialBranch qhx))) :=
    ⟨σd, (fun e member => by cases member), rfl⟩
  obtain ⟨σ, known, same⟩ := (rep.reads ⟨Empty, noNames⟩ _).mpr reads
  have atX := (pinned_known σ).mp known
  have same' : instantiateObservation σ ((Hosting.start N Ph (.apply (hT xName))).label 1) =
      observe (encBranch N (instantiate σd) (initialBranch qhx)) := same
  rw [reads_call] at same'
  have terms := observe_injective same'
  have call := vec1_inj (N.args_eq (vec1_inj (N.args_eq (vec2_inj (N.args_eq terms)).1)))
  have unfolded : tupleAt [symAt "h", instantiate (fun x => σ (.inl x)) xName] =
      (tupleAt [symAt "h", symAt "d"] : Term (signature MSig noNames) [] ()) := call
  have left : instantiate (fun x => σ (.inl x)) xName = σ (.inl (fo [] [7] 0)) :=
    instantiate_foD (fun x => σ (.inl x)) [] [7] 0
  rw [left, atX] at unfolded
  have clash := (tuple2_inj unfolded).2
  simp [symAt] at clash

/-- From `pinned` the step shows, as a set, the source's answers of the query `(h c)`. -/
theorem pinned_answers : stepAnswersFrom N Ph pinned = Answers.sourceAnswers D Ph supply sp qhc :=
  answers_beside N (D := D) (supply := supply) sp qhc Ph_scoped (qsite := [311]) (by decide) (by decide)
    trivial ((beside_empty N).mpr pinned_is_instance)
    (fun o inside => absurd inside (Finset.notMem_empty o))
    (fun o inside => absurd inside (Finset.notMem_empty o))

/-- **The clause fails and the answers are the query's**: the state does not represent the alternative
of the query `(h $x)`, and the answers the step shows from it are, as a set, the source's answers of that
query. The program discards the name the knowledge speaks of. -/
theorem discarded_name_same_answers :
    ¬ Represents N Ph 0 (initialBranch qhx) pinned 1 ∧
      stepAnswersFrom N Ph pinned = Answers.sourceAnswers D Ph supply sp qhx := by
  refine ⟨pinned_not_query, ?_⟩
  rw [pinned_answers, source_answers (hT cT) matches_c, source_answers (hT xName) matches_x]

end Discard

#print axioms represents_of_same_readings
#print axioms represents_of_same_joint_readings
#print axioms constrained_is_instance
#print axioms constrained_answers
#print axioms constrained_not_query
#print axioms source_answers
#print axioms RowName.reads_hold
#print axioms RowName.not_independent
#print axioms RowName.not_represents
#print axioms RowName.unmatched_fires
#print axioms RowName.extra_answer
#print axioms RowName.source_only_d
#print axioms Discard.pinned_is_instance
#print axioms Discard.pinned_not_query
#print axioms Discard.pinned_answers
#print axioms Discard.discarded_name_same_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Knowledge
