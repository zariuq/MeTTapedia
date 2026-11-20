import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersStep

/-!
# The binder core is a fragment: equations under binders, rewritten at the root of a call

The binder core (`ProgramBinders`) has equations `(= lhs rhs)` over the terms of any binding
signature, with holes of any parameter context, and its reference semantics rewrites a closed call at
its root by one equation (`Rewrites`): some closed solution of the holes makes the left-hand side the
call, and the answer is the right-hand side under it.

**The embedding** (`program`): the key system of a list of equations is the disjoint union of their
holes, one site per equation (`keys`); each equation becomes the core equation with the same two
terms, its holes as the site's names, and right-hand side `apply rhs` (the answer is called again at
its root, as the binder core's runs rewrite again at the root). A call is the query `apply call`.

**The theorems.**
* `branch_reads_iff`: from the query of a call, the alternative that equation `i` makes reads exactly
  the binder core's answers of equation `i` at the call. One step makes one alternative per equation,
  so the bag of one step is the binder core's branches.
* `execution_iff`: the binder core's runs from a call reach exactly the closed terms that some
  alternative of some run of the core shows (as its call, or as its value once no equation matches).
  This is **reachability**: an alternative shows a term at any configuration of any run, intermediate
  ones included. It is not a statement about final answers, and at that level it fails: when a
  right-hand side leaves a hole free, the open call it makes commits to the equations that match some
  instance of it, so a normal form of the core that is another instance is never an answer of the
  language (`BinderCoreAnswers.answers_differ`).

The binder core's programs are any family of equations; the core's programs are finite lists, so
the embedding is for every finite program (a family indexed by a list). The embedding rewrites at the
root of a call only. The binder core's infinite programs (the contextual closure `contextProgram` of a
context grammar, which rewrites under contexts) are not programs of the language, and nothing here
represents them: the language has no evaluation position under a binder, and the elaboration reads
`(lam x. …)` as inert data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ProgramBinders (Matches Answers Rewrites ground decode holeFree ClosedTerms close closedAt
  extendGround extendGround_at)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} (l : List (ProgramBinders.Equation S Γ sort))

/-! ## The embedding -/

/-- The key system of a list of equations: their holes, one site per equation. -/
def keys : Keys S where
  Key := Σ i : Fin l.length, (l.get i).Holes
  Site := Fin l.length
  site := Sigma.fst
  arity := fun key => (l.get key.1).arity key.2
  siteEq := inferInstance

/-- The holes of equation `i` as unopened names of its site. -/
def embedAt (i : Fin l.length) : Assignment (l.get i).arity (fam (keys l)) :=
  fun hole => generator (fam (keys l)) ⟨[], ⟨i, hole⟩⟩

/-- The holes of equation `i` as its copy at scope `m`. -/
def stamp (m : ℕ) (i : Fin l.length) : Assignment (l.get i).arity (fam (keys l)) :=
  fun hole => generator (fam (keys l)) ⟨[m], ⟨i, hole⟩⟩

variable {Ty : Type}

/-- Equation `i` as a core equation: the same two terms; the answer is called again. -/
def embedEquation (i : Fin l.length) : SourceLanguage.Equation (keys l) Γ sort Ty :=
  ⟨i, instantiate (embedAt l i) (l.get i).lhs, .apply (instantiate (embedAt l i) (l.get i).rhs)⟩

/-- **The embedded program.** Text is read as a root call. -/
def program : Program (keys l) Γ sort Ty :=
  ⟨(List.finRange l.length).map (embedEquation l), fun t => .apply t⟩

/-- The query of a closed call, over no spaces. -/
def start (call : Term S Γ sort) : Config (keys l) Γ sort Ty :=
  Config.initial (fun _ => 0) (.apply (Rigid.includeTerm (fam (keys l)) call))

/-- An alternative shows the closed term `g`: its call, or its value, reads as `g`. -/
def Shows (b : Branch (keys l) Γ sort Ty) (g : Term S Γ sort) : Prop :=
  ∃ t, (b.focus = .eval (.apply t) ∨ b.focus = .value t) ∧ Reads b.store t g

/-! ## Copies -/

theorem copy_embed (m : ℕ) (i : Fin l.length) {Δ : Ctx S} {result : S.Srt}
    (x : Term (signature S (l.get i).arity) Δ result) :
    instantiate (copyAt (keys l) m) (instantiate (embedAt l i) x) = instantiate (stamp l m i) x := by
  rw [instantiate_comp]
  congr 1
  funext hole
  exact instantiate_generator _ _

/-- Instantiating a copy reads the copy's holes. -/
theorem instantiate_stamp {X : Type} {target : X → MetaArity S}
    (σ : Assignment (fam (keys l)) target) (m : ℕ) (i : Fin l.length) {Δ : Ctx S} {result : S.Srt}
    (x : Term (signature S (l.get i).arity) Δ result) :
    instantiate σ (instantiate (stamp l m i) x) =
      instantiate (fun hole => σ ⟨[m], ⟨i, hole⟩⟩) x := by
  rw [instantiate_comp]
  congr 1
  funext hole
  exact instantiate_generator _ _

/-- Where the data of an alternative come from: the closed call, or a copy at an earlier scope. -/
def Origin (n : ℕ) (t : Data (keys l) Γ sort) : Prop :=
  (∃ g, t = Rigid.includeTerm (fam (keys l)) g) ∨
    ∃ m < n, ∃ (j : Fin l.length) (x : Term (signature S (l.get j).arity) Γ sort), t = instantiate (stamp l m j) x

theorem Origin.mono {n n' : ℕ} {t : Data (keys l) Γ sort} (origin : Origin l n t) (le : n ≤ n') :
    Origin l n' t := by
  rcases origin with rigid | ⟨m, lt, j, x, rfl⟩
  · exact Or.inl rigid
  · exact Or.inr ⟨m, Nat.lt_of_lt_of_le lt le, j, x, rfl⟩

/-! ## One equation at a call -/

section Extension

variable [ClosedTerms S]

/-- An old solution, with equation `i`'s copy at scope `n` read by the closed solution `θ`. -/
def extend {X : Type} {target : X → MetaArity S} (σ : Assignment (fam (keys l)) target) (n : ℕ)
    (i : Fin l.length) (θ : (l.get i).Ground) : Assignment (fam (keys l)) target :=
  fun name => if name.scopes = [n] then Rigid.includeTerm target (extendGround l.get i θ name.key) else σ name

/-- The extension does not change what the old data read. -/
theorem extend_old {X : Type} {target : X → MetaArity S} (σ : Assignment (fam (keys l)) target)
    (n : ℕ) (i : Fin l.length) (θ : (l.get i).Ground) {t : Data (keys l) Γ sort}
    (origin : Origin l n t) : instantiate (extend l σ n i θ) t = instantiate σ t := by
  rcases origin with ⟨g, rfl⟩ | ⟨m, lt, j, x, rfl⟩
  · rw [Rigid.instantiate_include, Rigid.instantiate_include]
  · rw [instantiate_stamp, instantiate_stamp]
    congr 1
    funext hole
    have other : ([m] : List ℕ) ≠ [n] := by
      intro same
      have := List.head_eq_of_cons_eq same
      omega
    simp [extend, other]

/-- The extension reads the copy of equation `i` through `θ`. -/
theorem extend_new {X : Type} {target : X → MetaArity S} (σ : Assignment (fam (keys l)) target)
    (n : ℕ) (i : Fin l.length) (θ : (l.get i).Ground) {Δ : Ctx S} {result : S.Srt}
    (x : Term (signature S (l.get i).arity) Δ result) :
    instantiate (extend l σ n i θ) (instantiate (stamp l n i) x) =
      instantiate ((l.get i).assign θ target) x := by
  rw [instantiate_stamp]
  congr 1
  funext hole
  have at_i := congrFun (extendGround_at l.get i θ) hole
  simp only [extend, if_true]
  rw [at_i]
  rfl

end Extension

/-- A store whose sides and a datum whose names all come from earlier scopes. -/
def Fresh (n : ℕ) (K : List (Constraint (keys l) Γ sort)) (t : Data (keys l) Γ sort) : Prop :=
  (∀ e ∈ K, Origin l n e.1 ∧ Origin l n e.2) ∧ Origin l n t

/-- **One equation at a call, forwards**: a reading of the call that equation `i` rewrites extends to
a reading of the alternative it makes. -/
theorem reads_forward [ClosedTerms S] {n : ℕ} {K : List (Constraint (keys l) Γ sort)}
    {t : Data (keys l) Γ sort} (fresh : Fresh l n K t) {s answer : Term S Γ sort}
    (reads : Reads K t s) (i : Fin l.length) (answered : Answers (l.get i) s answer) :
    Reads (K ++ [(instantiate (stamp l n i) (l.get i).lhs, t)])
      (instantiate (stamp l n i) (l.get i).rhs) answer := by
  obtain ⟨X, target, σ, solved, read⟩ := reads
  obtain ⟨θ, matched, rhsRead⟩ := answered
  refine ⟨X, target, extend l σ n i θ, ?_, ?_⟩
  · apply (models_append _ _ _).mpr
    constructor
    · intro e member
      rw [extend_old l σ n i θ (fresh.1 e member).1, extend_old l σ n i θ (fresh.1 e member).2]
      exact solved e member
    · apply (models_singleton _ _).mpr
      dsimp only
      rw [extend_new, extend_old l σ n i θ fresh.2, read]
      exact ((l.get i).reads_in_frame θ (l.get i).lhs s target).mp matched
  · rw [extend_new]
    exact ((l.get i).reads_in_frame θ (l.get i).rhs answer target).mp rhsRead

/-- **One equation at a call, backwards**: a reading of the alternative equation `i` makes comes from a
reading of the call and an answer of equation `i` there. -/
theorem reads_backward [ClosedTerms S] {n : ℕ} {K : List (Constraint (keys l) Γ sort)}
    {t : Data (keys l) Γ sort} (i : Fin l.length) {answer : Term S Γ sort}
    (reads : Reads (K ++ [(instantiate (stamp l n i) (l.get i).lhs, t)])
      (instantiate (stamp l n i) (l.get i).rhs) answer) :
    ∃ s, Reads K t s ∧ Answers (l.get i) s answer := by
  obtain ⟨X, target, σ, solved, read⟩ := reads
  obtain ⟨old, new⟩ := (models_append _ _ _).mp solved
  have matchedRaw := (models_singleton _ _).mp new
  dsimp only at matchedRaw
  let ground' : Assignment (fam (keys l)) (ground S) := Assignment.compose (close target) σ
  obtain ⟨s, readS⟩ := holeFree (instantiate ground' t)
  let θ : (l.get i).Ground := fun hole => decode (ground' ⟨[n], ⟨i, hole⟩⟩)
  have restored : (l.get i).assign θ (ground S) = fun hole => ground' ⟨[n], ⟨i, hole⟩⟩ :=
    (l.get i).ground_assignment (fun hole => ground' ⟨[n], ⟨i, hole⟩⟩)
  have composed : ∀ {Δ : Ctx S} {result : S.Srt} (x : Term (signature S (fam (keys l))) Δ result),
      instantiate ground' x = instantiate (close target) (instantiate σ x) :=
    fun x => Assignment.instantiate_compose (close target) σ x
  refine ⟨s, ⟨Empty, ground S, ground', ?_, readS⟩, θ, ?_, ?_⟩
  · intro e member
    rw [composed, composed, old e member]
  · unfold Matches
    rw [restored]
    exact (instantiate_stamp l ground' n i (l.get i).lhs).symm.trans
      ((composed _).trans ((congrArg (instantiate (close target)) matchedRaw).trans
        ((composed t).symm.trans readS)))
  · rw [restored]
    exact (instantiate_stamp l ground' n i (l.get i).rhs).symm.trans
      ((composed _).trans ((congrArg (instantiate (close target)) read).trans
        (Rigid.instantiate_include _ answer)))

/-- **The bag of one step, branch by branch.** From the query of a closed call, the alternative that
equation `i` makes reads exactly the answers of equation `i` at the call. -/
theorem branch_reads_iff [ClosedTerms S] (call answer : Term S Γ sort) (i : Fin l.length) :
    Reads [(instantiate (stamp l 0 i) (l.get i).lhs, Rigid.includeTerm (fam (keys l)) call)]
      (instantiate (stamp l 0 i) (l.get i).rhs) answer ↔ Answers (l.get i) call answer := by
  constructor
  · intro reads
    obtain ⟨s, readsCall, answered⟩ := reads_backward l (K := []) i reads
    obtain ⟨X, target, σ, _, read⟩ := readsCall
    rw [Rigid.instantiate_include] at read
    rw [Rigid.include_injective target call s read]
    exact answered
  · intro answered
    have fresh : Fresh l 0 [] (Rigid.includeTerm (fam (keys l)) call) :=
      ⟨fun e member => (by cases member), Or.inl ⟨call, rfl⟩⟩
    have readsCall : Reads ([] : List (Constraint (keys l) Γ sort)) (Rigid.includeTerm (fam (keys l)) call) call :=
      ⟨Empty, ground S, close (fam (keys l)), fun e member => (by cases member),
        Rigid.instantiate_include _ call⟩
    exact reads_forward l fresh readsCall i answered

/-! ## Runs -/

variable (D : Discipline S Γ sort) (supply : ℕ → Term S Γ sort)

/-- The alternative equation `i` makes, in the copy notation. -/
theorem callBranch_embed (n : ℕ) (K : List (Constraint (keys l) Γ sort)) (t : Data (keys l) Γ sort)
    (fs : List (Frame (keys l) Γ sort D.Ty)) (ps : List (Data (keys l) Γ sort × Comp (keys l) Γ sort D.Ty))
    (i : Fin l.length) :
    callBranch D n K t fs ps (embedEquation l i) =
      ⟨K ++ [(instantiate (stamp l n i) (l.get i).lhs, t)],
        .eval (.apply (instantiate (stamp l n i) (l.get i).rhs)), fs, ps⟩ := by
  simp only [callBranch, embedEquation, Comp.inst, Comp.mapData, copy_embed]

theorem mem_callBranches {n : ℕ} {K : List (Constraint (keys l) Γ sort)} {t : Data (keys l) Γ sort}
    {fs : List (Frame (keys l) Γ sort D.Ty)} {ps : List (Data (keys l) Γ sort × Comp (keys l) Γ sort D.Ty)}
    {b : Branch (keys l) Γ sort D.Ty} :
    b ∈ ((program l (Ty := D.Ty)).equations.map (callBranch D n K t fs ps)) ↔
      ∃ i, b = ⟨K ++ [(instantiate (stamp l n i) (l.get i).lhs, t)],
        .eval (.apply (instantiate (stamp l n i) (l.get i).rhs)), fs, ps⟩ := by
  simp only [program, List.map_map, List.mem_map, List.mem_finRange, true_and, Function.comp_apply,
    callBranch_embed]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- **Runs forwards**: every source run from a call is followed by a run of the embedded program, with
an alternative whose call reads as the run's end. -/
theorem runs_forward [ClosedTerms S] {call s : Term S Γ sort}
    (runs : Relation.ReflTransGen (Rewrites l.get) call s) :
    ∃ C, Runs D (program l) supply (start l call) C ∧ ∃ b ∈ C.branches, ∃ t,
      b.focus = .eval (.apply t) ∧ b.frames = [] ∧ b.pending = [] ∧ Fresh l C.world.scope b.store t ∧
        Reads b.store t s := by
  induction runs with
  | refl =>
      refine ⟨start l call, .refl, ⟨[], .eval (.apply (Rigid.includeTerm (fam (keys l)) call)), [], []⟩,
        Multiset.mem_singleton_self _, _, rfl, rfl, rfl, ⟨fun e member => (by cases member), Or.inl ⟨call, rfl⟩⟩,
        Empty, ground S, close (fam (keys l)), fun e member => (by cases member), Rigid.instantiate_include _ call⟩
  | tail _ rewriting ih =>
      obtain ⟨C, path, b, member, t, focus, frames, pending, fresh, reads⟩ := ih
      obtain ⟨i, answered⟩ := rewriting
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      obtain ⟨w, B⟩ := C
      obtain ⟨K, focus', fs, ps⟩ := b
      simp only at focus frames pending fresh reads split
      subst focus frames pending
      have newReads := reads_forward l fresh reads i answered
      have live : Solvable K := by
        obtain ⟨X, target, σ, solved, _⟩ := reads
        exact ⟨X, target, σ, solved⟩
      have matched : ∃ e ∈ (program l (Ty := D.Ty)).equations,
          Solvable (K ++ [(instantiate (copyAt (keys l) w.scope) e.lhs, t)]) := by
        refine ⟨embedEquation l i, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
        obtain ⟨X, target, σ, solved, _⟩ := newReads
        refine ⟨X, target, σ, ?_⟩
        simpa only [embedEquation, copy_embed] using solved
      refine ⟨⟨w.fresh, ((program l (Ty := D.Ty)).equations.map (callBranch D w.scope K t [] []) :
          Multiset (Branch (keys l) Γ sort D.Ty)) + rest⟩,
        path.tail (Step.of_eq split rfl live (.apply w K t [] [] matched)),
        ⟨K ++ [(instantiate (stamp l w.scope i) (l.get i).lhs, t)],
          .eval (.apply (instantiate (stamp l w.scope i) (l.get i).rhs)), [], []⟩,
        Multiset.mem_add.mpr (Or.inl (Multiset.mem_coe.mpr ((mem_callBranches l D).mpr ⟨i, rfl⟩))),
        _, rfl, rfl, rfl, ⟨?_, ?_⟩, newReads⟩
      · intro e member
        rcases List.mem_append.mp member with old | new
        · exact ⟨(fresh.1 e old).1.mono l (Nat.le_succ _), (fresh.1 e old).2.mono l (Nat.le_succ _)⟩
        · rw [List.mem_singleton.mp new]
          exact ⟨Or.inr ⟨w.scope, Nat.lt_succ_self _, i, _, rfl⟩, fresh.2.mono l (Nat.le_succ _)⟩
      · exact Or.inr ⟨w.scope, Nat.lt_succ_self _, i, _, rfl⟩

/-- What every alternative of a run of the embedded program is, and what its readings are. -/
def Invariant (call : Term S Γ sort) (C : Config (keys l) Γ sort D.Ty) : Prop :=
  ∀ b ∈ C.branches, ∃ (K : List (Constraint (keys l) Γ sort)) (t : Data (keys l) Γ sort),
    (b = ⟨K, .eval (.apply t), [], []⟩ ∨ b = ⟨K, .value t, [], []⟩) ∧
      ∀ g, Reads K t g → Relation.ReflTransGen (Rewrites l.get) call g

theorem invariant_start (call : Term S Γ sort) : Invariant l D call (start l call) := by
  intro b member
  rw [Multiset.mem_singleton.mp member]
  refine ⟨[], _, Or.inl rfl, fun g reads => ?_⟩
  obtain ⟨X, target, σ, _, read⟩ := reads
  rw [Rigid.instantiate_include] at read
  rw [← Rigid.include_injective target call g read]

theorem invariant_step [ClosedTerms S] {call : Term S Γ sort} {C C' : Config (keys l) Γ sort D.Ty}
    (inv : Invariant l D call C) (step : Step D (program l) supply C C') : Invariant l D call C' := by
  cases step with
  | move w w' b rest bs live moved =>
      obtain ⟨K, t, shape, readings⟩ := inv b (Multiset.mem_cons_self _ _)
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · rcases shape with rfl | rfl
        · cases moved with
          | apply =>
              obtain ⟨i, rfl⟩ := (mem_callBranches l D).mp (Multiset.mem_coe.mp made)
              refine ⟨_, _, Or.inl rfl, fun g reads => ?_⟩
              obtain ⟨s, readsCall, answered⟩ := reads_backward l i reads
              exact (readings s readsCall).tail ⟨i, answered⟩
          | unmatched =>
              rw [Multiset.mem_singleton.mp made]
              exact ⟨K, t, Or.inr rfl, readings⟩
        · cases moved
      · exact inv b' (Multiset.mem_cons_of_mem kept)

theorem invariant_runs [ClosedTerms S] {call : Term S Γ sort} {C : Config (keys l) Γ sort D.Ty}
    (runs : Runs D (program l) supply (start l call) C) : Invariant l D call C := by
  induction runs with
  | refl => exact invariant_start l D call
  | tail _ step ih => exact invariant_step l D supply ih step

/-- **The binder core is a fragment, at the level of reachable terms.** The binder core's runs from a
closed call reach exactly the closed terms that some alternative of some configuration of some run of
the embedded program shows (not only final answers). -/
theorem execution_iff [ClosedTerms S] (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites l.get) call answer ↔
      ∃ C, Runs D (program l) supply (start l call) C ∧ ∃ b ∈ C.branches, Shows l b answer := by
  constructor
  · intro runs
    obtain ⟨C, path, b, member, t, focus, _, _, _, reads⟩ := runs_forward l D supply runs
    exact ⟨C, path, b, member, t, Or.inl focus, reads⟩
  · rintro ⟨C, path, b, member, t', shown, reads⟩
    obtain ⟨K, t, shape, readings⟩ := invariant_runs l D supply path b member
    rcases shape with rfl | rfl
    · rcases shown with same | same
      · simp only [Focus.eval.injEq, Comp.apply.injEq] at same
        subst same
        exact readings answer reads
      · cases same
    · rcases shown with same | same
      · cases same
      · simp only [Focus.value.injEq] at same
        subst same
        exact readings answer reads

#print axioms branch_reads_iff
#print axioms runs_forward
#print axioms invariant_runs
#print axioms execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore
