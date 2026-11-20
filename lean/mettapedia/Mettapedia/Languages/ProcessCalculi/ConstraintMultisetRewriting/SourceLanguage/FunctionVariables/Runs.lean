import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Runs of one alternative beside dead ones

A deterministic run keeps one live alternative; every other alternative a call makes has a store with
no solution. `Along C w b` says that from `C`, when `b` is live, a run of `Semantics.Step` reaches the
world `w` with `b` beside dead alternatives. Each move of the fragment with arrows, and `run`, extends
such a run by one step (`Along.ret`, `letStart`, `letBind`, `unmatched`, `call`, `run`); liveness is
asked once, of the last store, because stores only grow. At the end the run is quiescent and its bag of
answers is the last alternative's (`Along.answers`).

A store whose last equation sets two data with different operators at the root, or two tuples with
different operators at the root of their first elements, has no solution (`dead_of_roots`,
`dead_of_heads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

/-! ## Clashes -/

/-- The code of the operator at the root of a datum, when it is one of the signature's. -/
def rootCode {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} {s : Unit} :
    Term (signature MSig target) Δ s → Option (String ⊕ Int ⊕ ℕ ⊕ ℕ)
  | .op (.inl o) _ => some o.code
  | _ => none

/-- The root code of the first of some arguments. -/
def firstCode {X : Type} {target : X → MetaArity MSig} {as : List (List Unit × Unit)} {Δ : Ctx MSig} :
    Args (signature MSig target) as Δ → Option (String ⊕ Int ⊕ ℕ ⊕ ℕ)
  | .nil => none
  | .cons hd _ => rootCode hd

/-- The root code of the first element of a tuple. -/
def headCode {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} {s : Unit} :
    Term (signature MSig target) Δ s → Option (String ⊕ Int ⊕ ℕ ⊕ ℕ)
  | .op (.inl (.tup _)) args => firstCode args
  | _ => none

theorem rootCode_instantiate {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target) :
    ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) {c : String ⊕ Int ⊕ ℕ ⊕ ℕ},
      rootCode t = some c → rootCode (instantiate σ t) = some c
  | _, _, .var _, _, rooted => by simp [rootCode] at rooted
  | _, _, .op (.inl _) _, _, rooted => rooted
  | _, _, .op (.inr (.mk _)) _, _, rooted => by simp [rootCode] at rooted

theorem firstCode_instantiate {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target) :
    ∀ {as : List (List Unit × Unit)} {Δ : Ctx MSig} (args : Args (signature MSig (fam mkeys)) as Δ)
      {c : String ⊕ Int ⊕ ℕ ⊕ ℕ}, firstCode args = some c → firstCode (instantiateArgs σ args) = some c
  | _, _, .nil, _, first => by simp [firstCode] at first
  | _, _, .cons hd _, _, first => rootCode_instantiate σ hd first

theorem headCode_instantiate {X : Type} {target : X → MetaArity MSig} (σ : Assignment (fam mkeys) target) :
    ∀ {Δ : Ctx MSig} {s : Unit} (t : Term (signature MSig (fam mkeys)) Δ s) {c : String ⊕ Int ⊕ ℕ ⊕ ℕ},
      headCode t = some c → headCode (instantiate σ t) = some c
  | _, _, .var _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inl (.tup _)) args, _, headed => firstCode_instantiate σ args headed
  | _, _, .op (.inl (.sym _)) _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inl (.num _)) _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inl .lam) _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inl .hold) _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inl .run) _, _, headed => by simp [headCode] at headed
  | _, _, .op (.inr (.mk _)) _, _, headed => by simp [headCode] at headed

/-- A symbol is never a tuple, in any family. -/
theorem sym_ne_tuple {X : Type} {target : X → MetaArity MSig} {Δ : Ctx MSig} {s : String}
    {ts : List (Term (signature MSig target) Δ ())} : (symAt s : Term (signature MSig target) Δ ()) ≠ tupleAt ts := by
  intro same
  have codes := congrArg rootCode same
  simp [rootCode, symAt, tupleAt, MOp.code] at codes

/-- **Different operators at the root**: a store whose last equation sets two such data equal is dead. -/
theorem dead_of_roots {K : List (Constraint mkeys [] ())} {a b : MData} {c c' : String ⊕ Int ⊕ ℕ ⊕ ℕ}
    (ra : rootCode a = some c) (rb : rootCode b = some c') (different : c ≠ c') :
    ¬ Solvable (K ++ [(a, b)]) := by
  rintro ⟨X, target, σ, solved⟩
  have same : instantiate σ a = instantiate σ b :=
    solved (a, b) (List.mem_append_right _ (List.mem_singleton_self _))
  have codes := congrArg rootCode same
  rw [rootCode_instantiate σ a ra, rootCode_instantiate σ b rb] at codes
  exact different (Option.some.inj codes)

/-- **Different operators at the root of the first elements**: a store whose last equation sets two such
tuples equal is dead. -/
theorem dead_of_heads {K : List (Constraint mkeys [] ())} {a b : MData} {c c' : String ⊕ Int ⊕ ℕ ⊕ ℕ}
    (ha : headCode a = some c) (hb : headCode b = some c') (different : c ≠ c') :
    ¬ Solvable (K ++ [(a, b)]) := by
  rintro ⟨X, target, σ, solved⟩
  have same : instantiate σ a = instantiate σ b :=
    solved (a, b) (List.mem_append_right _ (List.mem_singleton_self _))
  have codes := congrArg headCode same
  rw [headCode_instantiate σ a ha, headCode_instantiate σ b hb] at codes
  exact different (Option.some.inj codes)

/-- Two data have different operators at the root (computed). -/
def rootClash (a b : MData) : Bool :=
  match rootCode a, rootCode b with
  | some c, some c' => decide (c ≠ c')
  | _, _ => false

/-- Two tuples have different operators at the root of their first elements (computed). -/
def headClash (a b : MData) : Bool :=
  match headCode a, headCode b with
  | some c, some c' => decide (c ≠ c')
  | _, _ => false

theorem dead_of_rootClash {K : List (Constraint mkeys [] ())} {a b : MData} (clashes : rootClash a b = true) :
    ¬ Solvable (K ++ [(a, b)]) := by
  unfold rootClash at clashes
  split at clashes
  · rename_i c c' ra rb
    exact dead_of_roots ra rb (of_decide_eq_true clashes)
  · cases clashes

theorem dead_of_headClash {K : List (Constraint mkeys [] ())} {a b : MData} (clashes : headClash a b = true) :
    ¬ Solvable (K ++ [(a, b)]) := by
  unfold headClash at clashes
  split at clashes
  · rename_i c c' ha hb
    exact dead_of_heads ha hb (of_decide_eq_true clashes)
  · cases clashes

/-- Close a goal that a store is dead by a clash at the root or at the head of its last equation. -/
macro "clash" : tactic =>
  `(tactic| first
    | exact dead_of_rootClash (by decide)
    | exact dead_of_headClash (by decide))

/-! ## Runs of one alternative -/

variable {D : Discipline MSig [] ()} {P : Program mkeys [] () D.Ty} {supply : ℕ → MClosed}

/-- **A run of one alternative beside dead ones**: from `C`, when `b` is live, a run reaches the world
`w` with `b` and alternatives whose stores have no solution. -/
def Along (D : Discipline MSig [] ()) (P : Program mkeys [] () D.Ty) (supply : ℕ → MClosed)
    (C : Config mkeys [] () D.Ty) (w : World mkeys [] ()) (b : Branch mkeys [] () D.Ty) : Prop :=
  ∃ dead : Multiset (Branch mkeys [] () D.Ty), (∀ d ∈ dead, ¬ Solvable d.store) ∧
    (Solvable b.store → Runs D P supply C ⟨w, b ::ₘ dead⟩)

/-- The run of no step, from the initial configuration of a query. -/
theorem Along.start (spaces : MClosed → Multiset (Row mkeys [] ())) (q : Comp mkeys [] () D.Ty) :
    Along D P supply (Config.initial spaces q) ⟨0, 0, spaces⟩ ⟨[], .eval q, [], []⟩ :=
  ⟨0, fun _ member => absurd member (Multiset.notMem_zero _), fun _ => .refl⟩

/-- The same run, with the alternative's store written another way. -/
theorem Along.withStore {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {focus : Focus mkeys [] () D.Ty}
    {fs : List (Frame mkeys [] () D.Ty)} {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, focus, fs, ps⟩) (K' : List (Constraint mkeys [] ())) (same : K = K') :
    Along D P supply C w ⟨K', focus, fs, ps⟩ :=
  same ▸ along

/-- One move that makes one alternative whose store extends the mover's. -/
theorem Along.step {C : Config mkeys [] () D.Ty} {w w' : World mkeys [] ()} {b b' : Branch mkeys [] () D.Ty}
    (along : Along D P supply C w b) (moved : Move D P supply w b w' {b'})
    (back : Solvable b'.store → Solvable b.store) : Along D P supply C w' b' := by
  obtain ⟨dead, isDead, runs⟩ := along
  refine ⟨dead, isDead, fun live' => ?_⟩
  exact (runs (back live')).tail
    (Step.of_eq (b := b) (rest := dead) rfl (Multiset.singleton_add _ _) (back live') moved)

theorem Along.ret {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()} {K : List (Constraint mkeys [] ())}
    {t : MData} {fs : List (Frame mkeys [] () D.Ty)} {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .eval (.ret t), fs, ps⟩) :
    Along D P supply C w ⟨K, .value t, fs, ps⟩ :=
  along.step (.ret w K t fs ps) id

theorem Along.letStart {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {s : List ℕ} {p : MData} {c k : Comp mkeys [] () D.Ty}
    {fs : List (Frame mkeys [] () D.Ty)} {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .eval (.let_ s p c k), fs, ps⟩) :
    Along D P supply C w ⟨K, .eval c, .bindTo s p k :: fs, ps⟩ :=
  along.step (.letStart w K s p c k fs ps) id

theorem Along.letBind {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {v : MData} {s : List ℕ} {p : MData} {k : Comp mkeys [] () D.Ty}
    {fs : List (Frame mkeys [] () D.Ty)} {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .value v, .bindTo s p k :: fs, ps⟩) :
    Along D P supply C w.fresh
      ⟨K ++ [(instantiate (openAt mkeys s w.scope) p, v)], .eval (k.inst (openAt mkeys s w.scope)), fs, ps⟩ :=
  along.step (.letBind w K v s p k fs ps) solvable_of_append

/-- A call that no equation answers is returned as data. -/
theorem Along.unmatched {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {t : MData} {fs : List (Frame mkeys [] () D.Ty)}
    {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .eval (.apply t), fs, ps⟩)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt mkeys w.scope) e.lhs, t)])) :
    Along D P supply C w ⟨K, .value t, fs, ps⟩ :=
  along.step (.unmatched w K t fs ps none) id

/-- A call that one equation answers: the alternatives of the others are dead. -/
theorem Along.call {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {t : MData} {fs : List (Frame mkeys [] () D.Ty)}
    {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .eval (.apply t), fs, ps⟩)
    (pre : List (Equation mkeys [] () D.Ty)) (e : Equation mkeys [] () D.Ty)
    (post : List (Equation mkeys [] () D.Ty)) (equations : P.equations = pre ++ e :: post)
    (others : ∀ e' ∈ pre ++ post, ¬ Solvable (K ++ [(instantiate (copyAt mkeys w.scope) e'.lhs, t)])) :
    Along D P supply C w.fresh (callBranch D w.scope K t fs ps e) := by
  obtain ⟨dead, isDead, runs⟩ := along
  refine ⟨(((pre ++ post).map (callBranch D w.scope K t fs ps) : List (Branch mkeys [] () D.Ty)) :
    Multiset (Branch mkeys [] () D.Ty)) + dead, ?_, fun live' => ?_⟩
  · intro d member
    rcases Multiset.mem_add.mp member with new | old
    · obtain ⟨e', inside, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp new)
      exact others e' inside
    · exact isDead d old
  · have live : Solvable K := solvable_of_append live'
    have matched : ∃ e ∈ P.equations, Solvable (K ++ [(instantiate (copyAt mkeys w.scope) e.lhs, t)]) :=
      ⟨e, by rw [equations]; exact List.mem_append_right _ List.mem_cons_self, live'⟩
    refine (runs live).tail (Step.of_eq (b := ⟨K, .eval (.apply t), fs, ps⟩) (rest := dead) rfl ?_ live
      (.apply w K t fs ps matched))
    rw [equations, ← Multiset.cons_add, Multiset.cons_coe]
    congr 1
    refine Multiset.coe_eq_coe.mpr ?_
    rw [List.map_append, List.map_append, List.map_cons]
    exact List.perm_middle.symm

/-- Text run as code: the program's reading of the text dereferenced by a most general solution. -/
theorem Along.run {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()}
    {K : List (Constraint mkeys [] ())} {t : MData} {fs : List (Frame mkeys [] () D.Ty)}
    {ps : List (MData × Comp mkeys [] () D.Ty)}
    (along : Along D P supply C w ⟨K, .eval (.run t), fs, ps⟩)
    (θ : Assignment (fam mkeys) (fam mkeys)) (principal : Principal K θ) :
    Along D P supply C w ⟨K, .eval (P.reflect (instantiate θ t)), fs, ps⟩ :=
  along.step (.run w K t fs ps θ principal) id

theorem answers_of_all_dead {w : World mkeys [] ()} : ∀ dead : Multiset (Branch mkeys [] () D.Ty),
    (∀ d ∈ dead, ¬ Solvable d.store) →
      Config.answers (D := D) (⟨w, dead⟩ : Config mkeys [] () D.Ty) = 0 := by
  intro dead
  refine Multiset.induction_on dead (fun _ => Config.answers_of_zero) ?_
  intro d rest ih isDead
  rw [Config.answers_cons_of_dead (isDead d (Multiset.mem_cons_self _ _))]
  exact ih fun d' member => isDead d' (Multiset.mem_cons_of_mem member)

/-- **The end of such a run**: when the alternative is finished and live, the run reaches a quiescent
configuration whose bag of answers is that alternative's. -/
theorem Along.answers {C : Config mkeys [] () D.Ty} {w : World mkeys [] ()} {b : Branch mkeys [] () D.Ty}
    (along : Along D P supply C w b) (finished : b.Finished) (live : Solvable b.store) :
    ∃ C' : Config mkeys [] () D.Ty, Runs D P supply C C' ∧ Config.Quiescent (D := D) P supply C' ∧
      Config.answers (D := D) C' = {b.answer} := by
  obtain ⟨dead, isDead, runs⟩ := along
  refine ⟨⟨w, b ::ₘ dead⟩, runs live, ?_, ?_⟩
  · exact Config.quiescent_of_finished fun b' member live' => by
      rcases Multiset.mem_cons.mp member with rfl | old
      · exact finished
      · exact absurd live' (isDead b' old)
  · rw [Config.answers_cons_of_finished finished live, answers_of_all_dead dead isDead]
    rfl

#print axioms dead_of_roots
#print axioms dead_of_heads
#print axioms Along.call
#print axioms Along.answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
