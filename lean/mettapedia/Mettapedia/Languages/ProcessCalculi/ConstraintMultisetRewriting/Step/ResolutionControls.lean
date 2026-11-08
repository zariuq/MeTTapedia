import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionModulo

/-!
# Controls for resolution as a step

All controls use one small first-order signature: constants `a`, `b`, `gp`, `alice`, `carol`;
variables `ℕ`; function symbols `p` (unary), `q` (nullary), `r` (binary), `f` (unary) and the
literal wrapper `m` (ternary).

* **Two clauses for one goal** (`two_clauses_admitted`, `two_clauses_dependent`): the goal `p(X)`
  against `p(a).` and `p(b).`: both firings are admitted, and they are not independent.
* **Capture** (`capture_refused`, `apart_admitted`, `capture_not_fresh`, `apart_fresh`,
  `capture_loses_answer`): the goal `p(X)` against `p(f(X)).` not renamed apart tells `X = f(X)` and
  is refused; renamed apart it tells `X = f(Y)` and is admitted. The answer `X = f(a)` holds, so
  the unrenamed reading loses it.
* **Occurs check** (`occurs_fresh`, `occurs_refused`): the goal `r(X, f(X))` against `r(Y, Y).`,
  renamed apart, is refused: `X = f(X)` has no finite solution.
* **Atomicity with several body atoms** (`atomic_refused`, `split_leaves_residue`): against
  `r(Y, Y) :- q, q.` the atomic firing is refused and the goal stays. A split realization that first
  takes the goal and makes one body atom, and only then tells the unification, is admitted halfway
  and stuck there: the goal is consumed and one body goal is made.
* **An infinite branch** (`loop_step`, `loop_never_completes`, `answer_from_every_point`): with
  `q :- q.` before `q.`, the leftmost clause is admitted at every state of an infinite branch, and
  from every point of that branch one more firing completes with an answer.
* **Variant tabling** (`variant_hit`, `variant_hit_answer`, `variants_not_private`,
  `instance_not_variant`, `instance_answers_differ`): `p(X)` and `p(Y)` are variants with the same
  answer instances, though not privately equivalent; `p(a)` is an instance of `p(X)`, not a variant,
  and its answer instances differ.
* **A metarule through the literal wrapper** (`chain_admitted`, `chain_binds_predicate`): the Chain
  metarule `m(P,X,Y) :- m(Q,X,Z), m(R,Z,Y)` resolves the goal `m(gp, alice, carol)`, and every
  solution of the result binds the predicate variable `P` to `gp`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.Controls

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder firstOrderTransport)

inductive Name | a | b | gp | alice | carol
  deriving DecidableEq

inductive Fn | p | q | r | f | m
  deriving DecidableEq

def Fn.arity : Fn → ℕ
  | .p => 1
  | .q => 0
  | .r => 2
  | .f => 1
  | .m => 3

abbrev sig : LPSignature where
  constants := Name
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Fn
  functionArity := Fn.arity

abbrev Tm := Term sig

abbrev X : Tm := .var 0
abbrev Y : Tm := .var 1

def a : Tm := .const .a
def b : Tm := .const .b
def P (t : Tm) : Tm := .app .p fun _ => t
def Q : Tm := .app .q Fin.elim0
def R (s t : Tm) : Tm := .app .r fun i => if i.val = 0 then s else t
def F (t : Tm) : Tm := .app .f fun _ => t
def M (p s t : Tm) : Tm := .app .m fun i => if i.val = 0 then p else if i.val = 1 then s else t

/-! ## Terms -/

theorem apply_Q (θ : Subst sig) : θ.applyTerm Q = Q := by
  show Term.app _ _ = Term.app _ _
  congr 1
  funext i
  exact i.elim0

theorem apply_R (θ : Subst sig) (s t : Tm) : θ.applyTerm (R s t) = R (θ.applyTerm s) (θ.applyTerm t) := by
  show Term.app _ _ = Term.app _ _
  congr 1
  funext i
  show θ.applyTerm (if (i : ℕ) = 0 then s else t) = _
  rw [apply_ite θ.applyTerm]

theorem apply_M (θ : Subst sig) (p s t : Tm) :
    θ.applyTerm (M p s t) = M (θ.applyTerm p) (θ.applyTerm s) (θ.applyTerm t) := by
  show Term.app _ _ = Term.app _ _
  congr 1
  funext i
  show θ.applyTerm (if (i : ℕ) = 0 then p else if (i : ℕ) = 1 then s else t) = _
  rw [apply_ite θ.applyTerm, apply_ite θ.applyTerm]

theorem rename_refl (t : Tm) : rename (Equiv.refl ℕ) t = t := by
  rw [rename, permSubst_refl, Subst.applyTerm_id]

theorem P_inj {s t : Tm} (same : P s = P t) : s = t := by
  simp only [P, Term.app.injEq, heq_eq_eq, true_and] at same
  exact congrFun same ⟨0, Nat.zero_lt_one⟩

theorem R_inj {s t s' t' : Tm} (same : R s t = R s' t') : s = s' ∧ t = t' := by
  simp only [R, Term.app.injEq, heq_eq_eq, true_and] at same
  exact ⟨by simpa using congrFun same ⟨0, by decide⟩, by simpa using congrFun same ⟨1, by decide⟩⟩

theorem M_first {p s t p' s' t' : Tm} (same : M p s t = M p' s' t') : p = p' := by
  simp only [M, Term.app.injEq, heq_eq_eq, true_and] at same
  simpa using congrFun same ⟨0, by decide⟩

theorem F_ne (t : Tm) : F t ≠ t := by
  intro same
  have smaller := Term.size_subterm (σ := sig) (f := Fn.f) (ts := fun _ => t) ⟨0, Nat.zero_lt_one⟩
  change t.size < (F t).size at smaller
  rw [same] at smaller
  exact lt_irrefl _ smaller

theorem a_ne_b : a ≠ b := fun same => by cases same

theorem freeVars_P (t : Tm) : (P t).freeVars = t.freeVars := by
  ext v
  rw [show P t = Term.app Fn.p (fun _ => t) from rfl, Term.mem_freeVars_app (σ := sig)]
  exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨⟨0, Nat.zero_lt_one⟩, member⟩⟩

theorem freeVars_F (t : Tm) : (F t).freeVars = t.freeVars := by
  ext v
  rw [show F t = Term.app Fn.f (fun _ => t) from rfl, Term.mem_freeVars_app (σ := sig)]
  exact ⟨fun ⟨_, member⟩ => member, fun member => ⟨⟨0, Nat.zero_lt_one⟩, member⟩⟩

theorem freeVars_Q : (Q : Tm).freeVars = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v member => ?_
  obtain ⟨i, -, -⟩ := Finset.mem_biUnion.mp member
  exact i.elim0

theorem mem_freeVars_R {s t : Tm} {v : ℕ} :
    v ∈ (R s t).freeVars ↔ v ∈ s.freeVars ∨ v ∈ t.freeVars := by
  rw [show R s t = Term.app Fn.r (fun i => if (i : ℕ) = 0 then s else t) from rfl,
    Term.mem_freeVars_app (σ := sig)]
  constructor
  · rintro ⟨i, member⟩
    have member : v ∈ (if (i : ℕ) = 0 then s else t).freeVars := member
    by_cases zero : (i : ℕ) = 0
    · rw [if_pos zero] at member
      exact .inl member
    · rw [if_neg zero] at member
      exact .inr member
  · rintro (member | member)
    · exact ⟨⟨0, by decide⟩, member⟩
    · exact ⟨⟨1, by decide⟩, member⟩

theorem freeVars_var (w : ℕ) : (Term.var w : Tm).freeVars = {w} := rfl

theorem freeVars_P_X : (P X).freeVars = {0} := by
  rw [freeVars_P]
  rfl

/-! ## Calls -/

/-- Labels of the calls: `1 : p(X)`, `2 : p(Y)`, `3 : p(a)`, every other identity `a`. -/
def callLabel : ℕ → Tm
  | 1 => P X
  | 2 => P Y
  | 3 => P a
  | _ => a

def callX : Configuration Tm ℕ := ⟨[], {1}⟩
def callY : Configuration Tm ℕ := ⟨[], {2}⟩
def callA : Configuration Tm ℕ := ⟨[], {3}⟩

def factA : Clause sig := ⟨P a, []⟩
def factB : Clause sig := ⟨P b, []⟩
def factsAB : Program sig := [factA, factB]

/-- The constant substitution. -/
def everywhere (t : Tm) : Subst sig := fun _ => t

theorem fact_valid (t : Tm) (ground : ∀ θ : Subst sig, θ.applyTerm t = t) :
    (resolve 1 ⟨P t, []⟩ (Equiv.refl ℕ) []).Valid (A sig) callLabel callX := by
  refine (resolve_valid_iff callLabel callX 1 ⟨P t, []⟩ (Equiv.refl ℕ) []).mpr
    ⟨List.nodup_nil, rfl, by simp [callX], fun _ member => absurd member List.not_mem_nil, ?_⟩
  refine ⟨everywhere t, (A sig).models_nil _, ?_⟩
  show P ((everywhere t).applyTerm (rename (Equiv.refl ℕ) t)) = P (everywhere t 0)
  rw [rename_refl, ground]
  rfl

theorem const_ground (n : Name) (θ : Subst sig) : θ.applyTerm (.const n) = .const n := rfl

/-! ### Two clauses for one goal -/

theorem two_clauses_admitted :
    (resolve 1 factA (Equiv.refl ℕ) []).Valid (A sig) callLabel callX ∧
      (resolve 1 factB (Equiv.refl ℕ) []).Valid (A sig) callLabel callX :=
  ⟨fact_valid a (const_ground .a), fact_valid b (const_ground .b)⟩

/-- **Two firings that compete for one goal are dependent.** -/
theorem two_clauses_dependent :
    ¬ (firstOrderTransport (A sig) callLabel).Independent callX
      (resolve 1 factA (Equiv.refl ℕ) []) (resolve 1 factB (Equiv.refl ℕ) []) :=
  resolve_same_goal_dependent two_clauses_admitted.1 two_clauses_admitted.2
    fun _ member => absurd member List.not_mem_nil

/-! ### Capture -/

/-- `p(f(X)).` -/
def selfApplied : Clause sig := ⟨P (F X), []⟩

theorem configVars_callX : configVars callLabel callX = {0} := by
  ext v
  simp only [configVars, callX, eqVars, Finset.empty_union, Finset.singleton_biUnion]
  show v ∈ (P X).freeVars ↔ v ∈ ({0} : Finset ℕ)
  rw [freeVars_P_X]

theorem selfApplied_vars : selfApplied.vars = {0} := by
  show (P (F X)).freeVars ∪ termsVars [] = {0}
  rw [show termsVars ([] : List Tm) = ∅ from rfl, Finset.union_empty, freeVars_P, freeVars_F]
  rfl

/-- **Capture**: without renaming apart, the goal `p(X)` against `p(f(X)).` tells `X = f(X)`, and
the firing is refused. -/
theorem capture_refused :
    ¬ (resolve 1 selfApplied (Equiv.refl ℕ) []).Valid (A sig) callLabel callX := by
  intro valid
  obtain ⟨-, -, -, -, τ, -, same⟩ := (resolve_valid_iff callLabel callX 1 selfApplied _ []).mp valid
  rw [rename_refl] at same
  have inner := P_inj same
  exact F_ne (τ 0) inner

/-- **Renamed apart**, the same clause tells `X = f(Y)`, and the firing is admitted. -/
theorem apart_admitted :
    (resolve 1 selfApplied (Equiv.swap 0 1) []).Valid (A sig) callLabel callX := by
  refine (resolve_valid_iff callLabel callX 1 selfApplied _ []).mpr
    ⟨List.nodup_nil, rfl, by simp [callX], fun _ member => absurd member List.not_mem_nil, ?_⟩
  refine ⟨fun v => if v = 0 then F Y else .var v, (A sig).models_nil _, ?_⟩
  show P (F (if Equiv.swap 0 1 0 = 0 then F Y else .var (Equiv.swap 0 1 0))) = P (if 0 = 0 then F Y else X)
  rw [Equiv.swap_apply_left]
  rfl

theorem capture_not_fresh : ¬ Fresh (configVars callLabel callX) (Equiv.refl ℕ) selfApplied := by
  intro fresh
  apply fresh 0 (by rw [selfApplied_vars]; exact Finset.mem_singleton_self 0)
  rw [configVars_callX]
  exact Finset.mem_singleton_self 0

theorem apart_fresh : Fresh (configVars callLabel callX) (Equiv.swap 0 1) selfApplied := by
  intro v member
  rw [selfApplied_vars, Finset.mem_singleton] at member
  subst member
  rw [configVars_callX, Equiv.swap_apply_left]
  decide

/-- **The unrenamed reading loses an answer**: `p(f(a))` holds, an instance of the call `p(X)`. -/
theorem capture_loses_answer :
    Holds [selfApplied] ((everywhere (F a)).applyTerm (callLabel 1)) :=
  Holds.rule List.mem_cons_self (everywhere a) fun _ member => absurd member List.not_mem_nil

/-! ### Occurs check and atomicity -/

/-- Labels: `0 : r(X, f(X))`, every other identity `q`. -/
def occursLabel : ℕ → Tm
  | 0 => R X (F X)
  | _ => Q

def occursCall : Configuration Tm ℕ := ⟨[], {0}⟩

/-- `r(Y, Y).` -/
def sameArgs : Clause sig := ⟨R Y Y, []⟩

/-- `r(Y, Y) :- q, q.` -/
def sameArgsBody : Clause sig := ⟨R Y Y, [Q, Q]⟩

theorem not_unifiable_occurs :
    ¬ Unifiable occursCall.equations (rename (Equiv.refl ℕ) (R Y Y)) (occursLabel 0) := by
  rintro ⟨τ, -, same⟩
  rw [rename_refl, show occursLabel 0 = R X (F X) from rfl, apply_R, apply_R] at same
  obtain ⟨first, second⟩ := R_inj same
  rw [first] at second
  exact F_ne (τ 0) second.symm

theorem configVars_occursCall : configVars occursLabel occursCall = {0} := by
  ext v
  simp only [configVars, occursCall, eqVars, Finset.empty_union, Finset.singleton_biUnion]
  show v ∈ (R X (F X)).freeVars ↔ v ∈ ({0} : Finset ℕ)
  rw [mem_freeVars_R, freeVars_F, freeVars_var, or_self]

theorem sameArgs_vars_subset (c : Clause sig) (head : c.head = R Y Y) (body : c.body = [] ∨ c.body = [Q, Q]) :
    ∀ v ∈ c.vars, v = 1 := by
  intro v member
  rcases Finset.mem_union.mp member with inHead | inBody
  · rw [head, mem_freeVars_R, freeVars_var, or_self] at inHead
    exact Finset.mem_singleton.mp inHead
  · obtain ⟨t, inList, occurs⟩ := (mem_termsVars (sig := sig)).mp inBody
    rcases body with empty | twoQ
    · rw [empty] at inList
      exact absurd inList List.not_mem_nil
    · rw [twoQ] at inList
      have isQ : t = Q := by simpa using inList
      rw [isQ, freeVars_Q] at occurs
      exact absurd occurs (Finset.notMem_empty v)

/-- The clause `r(Y, Y).` is apart from the call: the occurs failure is not a capture. -/
theorem occurs_fresh : Fresh (configVars occursLabel occursCall) (Equiv.refl ℕ) sameArgs := by
  intro v member
  have one := sameArgs_vars_subset sameArgs rfl (.inl rfl) v member
  subst one
  rw [configVars_occursCall]
  decide

/-- **Occurs check**: `r(X, f(X))` against `r(Y, Y).` is refused. -/
theorem occurs_refused :
    ¬ (resolve 0 sameArgs (Equiv.refl ℕ) []).Valid (A sig) occursLabel occursCall :=
  (resolve_refused_iff occursLabel occursCall 0 sameArgs _ []).mpr (.inr not_unifiable_occurs)

/-- **The atomic firing with two body atoms is refused, and leaves no residue**: no run begins with
it, the goal stays and no body goal is made. -/
theorem atomic_refused :
    ¬ (resolve 0 sameArgsBody (Equiv.refl ℕ) [1, 2]).Valid (A sig) occursLabel occursCall ∧
      (∀ r : (firstOrder (A sig) occursLabel).Run occursCall,
        ∀ x ∈ r.word.head?, x.2 ≠ resolve 0 sameArgsBody (Equiv.refl ℕ) [1, 2]) ∧
      0 ∈ occursCall.present ∧ 1 ∉ occursCall.present ∧ 2 ∉ occursCall.present := by
  have refused : ¬ (resolve 0 sameArgsBody (Equiv.refl ℕ) [1, 2]).Valid (A sig) occursLabel occursCall :=
    (resolve_refused_iff occursLabel occursCall 0 sameArgsBody _ _).mpr (.inr not_unifiable_occurs)
  exact ⟨refused, resolve_no_step occursLabel refused, by decide, by decide, by decide⟩

/-- The first half of a split: take the goal by its own label, make the first body goal. -/
def splitTake : Firing Tm (Subst sig) ℕ :=
  ⟨⟨[R X (F X)], [], [], [], [Q]⟩, [], ⟨[0], [], [1]⟩⟩

/-- The second half: make the second body goal and tell the unification. -/
def splitTell : Firing Tm (Subst sig) ℕ :=
  ⟨⟨[], [], [(R Y Y, R X (F X))], [], [Q]⟩, [], ⟨[], [], [2]⟩⟩

theorem splitTake_result :
    splitTake.result occursLabel occursCall = ⟨[(R X (F X), R X (F X))], {1}⟩ := by
  show Selection.result _ _ _ _ = _
  simp only [Selection.result, Selection.problem, Selection.equations, splitTake, occursCall,
    MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, Configuration.mk.injEq]
  exact ⟨rfl, by decide⟩

/-- **A split realization leaves residue**: its first half is admitted, its second is refused, and
the configuration it is stuck in has consumed the goal and made one body goal. -/
theorem split_leaves_residue :
    splitTake.Valid (A sig) occursLabel occursCall ∧
      ¬ splitTell.Valid (A sig) occursLabel (splitTake.result occursLabel occursCall) ∧
      0 ∉ (splitTake.result occursLabel occursCall).present ∧
      1 ∈ (splitTake.result occursLabel occursCall).present := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro x member
      simpa [splitTake, Selection.commit, occursCall] using member
    · intro x member
      simp [splitTake, Selection.commit] at member
    · simp [splitTake, Selection.commit]
    · simp [splitTake, Selection.commit, occursCall]
    · intro read member
      simp [splitTake, Selection.commit] at member
    · refine ⟨Subst.id sig, ?_⟩
      intro e member
      simp only [Selection.problem, Selection.equations, splitTake, occursCall, List.nil_append,
        List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      rfl
    · intro check member
      simp [splitTake] at member
    · intro query member
      simp [splitTake] at member
  · rintro ⟨⟨-, -, -, -, -, -, ⟨τ, solved⟩, -⟩, -⟩
    rw [splitTake_result] at solved
    have pair : τ.applyTerm (R Y Y) = τ.applyTerm (R X (F X)) :=
      solved (R Y Y, R X (F X)) (by simp [Selection.problem, Selection.equations, splitTell])
    rw [apply_R, apply_R] at pair
    obtain ⟨first, second⟩ := R_inj pair
    rw [first] at second
    exact F_ne (τ 0) second.symm
  · rw [splitTake_result]
    decide
  · rw [splitTake_result]
    decide

/-! ### An infinite branch -/

/-- Every identity is labelled `q`. -/
def loopLabel : ℕ → Tm := fun _ => Q

/-- `q :- q.` -/
def loop : Clause sig := ⟨Q, [Q]⟩

/-- `q.` -/
def stop : Clause sig := ⟨Q, []⟩

/-- The program, with the looping clause first. -/
def loopProgram : Program sig := [loop, stop]

/-- The configuration after `k` firings of the looping clause. -/
def branch (k : ℕ) : Configuration Tm ℕ := ⟨List.replicate k (Q, Q), {k}⟩

theorem branch_consistent (k : ℕ) (τ : Subst sig) : (A sig).Models τ (branch k).equations := by
  intro e member
  rw [List.eq_of_mem_replicate member]
  rfl

theorem unifiable_branch (k : ℕ) : Unifiable (branch k).equations (rename (Equiv.refl ℕ) Q) (loopLabel k) :=
  ⟨Subst.id sig, branch_consistent k _, by rw [rename_refl]; rfl⟩

/-- **The leftmost clause is admitted at every state of the branch**, and leads to the next. -/
theorem loop_step (k : ℕ) :
    (resolve k loop (Equiv.refl ℕ) [k + 1]).Valid (A sig) loopLabel (branch k) ∧
      (resolve k loop (Equiv.refl ℕ) [k + 1]).result loopLabel (branch k) = branch (k + 1) := by
  refine ⟨(resolve_valid_iff loopLabel (branch k) k loop _ _).mpr
    ⟨List.nodup_singleton _, ?_, by simp [branch], ?_, unifiable_branch k⟩, ?_⟩
  · show [Q] = [rename (Equiv.refl ℕ) Q]
    rw [rename_refl]
  · intro r member
    rw [List.mem_singleton] at member
    subst member
    simp [branch]
  · rw [resolve_result, rename_refl]
    simp only [branch, Configuration.mk.injEq]
    refine ⟨List.replicate_succ'.symm, ?_⟩
    simp

/-- **The branch never completes**: every state on it has a goal. -/
theorem loop_never_completes (k : ℕ) : (branch k).present.Nonempty := ⟨k, Finset.mem_singleton_self k⟩

/-- **From every point of the branch, one firing completes with an answer.** A search that tries
every admitted firing of every state it reaches therefore finds an answer however long it followed
the loop. -/
theorem answer_from_every_point (k : ℕ) :
    ∃ r : (firstOrder (A sig) loopLabel).Run (branch k),
      (∀ x ∈ r.word, IsResolution loopProgram x.2) ∧ r.word.length = 1 ∧ r.last.present = ∅ ∧
        (A sig).Models (Subst.id sig) r.last.equations := by
  have valid : (resolve k stop (Equiv.refl ℕ) []).Valid (A sig) loopLabel (branch k) :=
    (resolve_valid_iff loopLabel (branch k) k stop _ _).mpr
      ⟨List.nodup_nil, rfl, by simp [branch], fun _ member => absurd member List.not_mem_nil,
        unifiable_branch k⟩
  refine ⟨.cons _ valid (.nil _), ?_, rfl, ?_, ?_⟩
  · intro x member
    rw [List.mem_singleton.mp member]
    exact ⟨k, stop, Equiv.refl ℕ, [], List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · show ((resolve k stop (Equiv.refl ℕ) []).result loopLabel (branch k)).present = ∅
    rw [resolve_result]
    simp [branch]
  · show (A sig).Models _ ((resolve k stop (Equiv.refl ℕ) []).result loopLabel (branch k)).equations
    rw [resolve_result, rename_refl]
    exact ((A sig).models_append _ _ _).mpr ⟨branch_consistent k _,
      ((A sig).models_cons _ _ _).mpr ⟨rfl, (A sig).models_nil _⟩⟩

/-! ### Variant tabling -/

/-- Swap the variables `X` and `Y`. -/
abbrev swapXY : Equiv.Perm ℕ := Equiv.swap 0 1

/-- Swap the calls `1` and `2`. -/
abbrev swapCalls : ℕ ≃ ℕ := Equiv.swap 1 2

theorem covers_swap : Covers callLabel swapXY swapCalls := by
  intro o
  rcases o with _ | _ | _ | _ | n
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    rfl
  · rw [show (0 + 1 : ℕ) = 1 from rfl, Equiv.swap_apply_left]
    show P Y = P (.var (Equiv.swap 0 1 0))
    rw [Equiv.swap_apply_left]
  · rw [show (0 + 1 + 1 : ℕ) = 2 from rfl, Equiv.swap_apply_right]
    show P X = P (.var (Equiv.swap 0 1 1))
    rw [Equiv.swap_apply_right]
  · rw [show (0 + 1 + 1 + 1 : ℕ) = 3 from rfl, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    rfl
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    rfl

theorem rename_callX : renameVars swapXY swapCalls callX = callY := by
  show (⟨[], ({1} : Finset ℕ).map swapCalls.toEmbedding⟩ : Configuration Tm ℕ) = ⟨[], {2}⟩
  rw [Finset.map_singleton, Equiv.coe_toEmbedding, Equiv.swap_apply_left]

theorem variants : VariantEquivalent callLabel callX callY :=
  ⟨swapXY, swapCalls, covers_swap, by rw [rename_callX]; exact GuardFreeProcessOrders.SameUpTo.refl _ _⟩

/-- **Variant hit**: the call `p(Y)` has the answer instances of the call `p(X)`. -/
theorem variant_hit :
    AnswerInstances callLabel factsAB callY (P Y) = AnswerInstances callLabel factsAB callX (P X) := by
  have moved := answerInstances_rename factsAB covers_swap callX (P X)
  rw [rename_callX] at moved
  have renamed : rename swapXY (P X) = P Y := by
    show P (.var (Equiv.swap 0 1 0)) = P Y
    rw [Equiv.swap_apply_left]
  rw [renamed] at moved
  exact moved

/-- `p(b)` answers the call `p(X)`, hence also the call `p(Y)`. -/
theorem variant_hit_answer :
    P b ∈ AnswerInstances callLabel factsAB callX (P X) ∧
      P b ∈ AnswerInstances callLabel factsAB callY (P Y) := by
  have valid := two_clauses_admitted.2
  have answered : P b ∈ AnswerInstances callLabel factsAB callX (P X) := by
    refine ⟨everywhere b, ⟨.cons _ valid (.nil _), ?_, ?_, ?_⟩, rfl⟩
    · intro x member
      rw [List.mem_singleton.mp member]
      exact ⟨1, factB, Equiv.refl ℕ, [], List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    · show ((resolve 1 factB (Equiv.refl ℕ) []).result callLabel callX).present = ∅
      rw [resolve_result]
      simp [callX]
    · show (A sig).Models _ ((resolve 1 factB (Equiv.refl ℕ) []).result callLabel callX).equations
      rw [resolve_result]
      refine ((A sig).models_append _ _ _).mpr ⟨(A sig).models_nil _,
        ((A sig).models_cons _ _ _).mpr ⟨?_, (A sig).models_nil _⟩⟩
      show P ((everywhere b).applyTerm (rename (Equiv.refl ℕ) b)) = P (everywhere b 0)
      rw [rename_refl]
      rfl
  exact ⟨answered, variant_hit ▸ answered⟩

/-- **Variants are not privately equivalent**: private renamings keep labels, and `p(X)` is not
`p(Y)`. The variant table needs the frame isomorphism. -/
theorem variants_not_private : ¬ Observation.PrivatelyEquivalent (A sig) callLabel ∅ callX callY := by
  rintro ⟨κ, priv, -, present⟩
  have moved : ({κ 1} : Finset ℕ) = {2} := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_singleton]
    exact present
  have one : κ 1 = 2 := Finset.singleton_inj.mp moved
  have keeps := priv.keeps 1
  rw [one] at keeps
  exact absurd (Term.var.inj (P_inj keeps)) (by decide)

/-- **An instance is not a variant**: `p(a)` is no renaming of `p(X)`. -/
theorem instance_not_variant : ¬ VariantEquivalent callLabel callX callA := by
  rintro ⟨π, κ, covers, -, present⟩
  have moved : ({κ 1} : Finset ℕ) = {3} := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_singleton]
    exact present
  have three : κ 1 = 3 := Finset.singleton_inj.mp moved
  have labelled := covers 1
  rw [three] at labelled
  have inner := P_inj labelled
  cases inner

/-- **Reusing the table of `p(X)` for `p(a)` as a variant would be wrong**: `p(b)` answers `p(X)`
and does not answer `p(a)`, whose answer instances are `p(a)`. -/
theorem instance_answers_differ :
    P b ∈ AnswerInstances callLabel factsAB callX (P X) ∧
      P b ∉ AnswerInstances callLabel factsAB callA (P a) ∧
      ∀ u ∈ AnswerInstances callLabel factsAB callA (P a), u = P a := by
  refine ⟨variant_hit_answer.1, ?_, ?_⟩
  · rintro ⟨τ, -, same⟩
    exact a_ne_b (P_inj same).symm
  · rintro u ⟨τ, -, rfl⟩
    rfl

/-! ### A table hit modulo the knowledge that is not a variant hit -/

/-- The knowledge `X = a`. -/
def knowsXa : EquationStore Tm := [(X, a)]

/-- The call `p(X)` under `X = a`. -/
def boundX : Configuration Tm ℕ := ⟨knowsXa, {1}⟩

/-- The call `p(a)` under `X = a`. -/
def boundA : Configuration Tm ℕ := ⟨knowsXa, {3}⟩

/-- The facts have no body goals, so they need no fresh identities. -/
theorem facts_supply : BodySupply callLabel factsAB := by
  intro c member b inBody
  rcases List.mem_cons.mp member with rfl | rest
  · exact absurd inBody List.not_mem_nil
  · rw [List.mem_singleton.mp rest] at inBody
    exact absurd inBody List.not_mem_nil

theorem entailed_refl (t : Tm) : Observation.Entailed (A sig) knowsXa t t := fun _ _ => rfl

theorem entailed_Pa_PX : Observation.Entailed (A sig) knowsXa (P a) (P X) := by
  intro σ solved
  have bound : σ.applyTerm X = σ.applyTerm a := solved (X, a) List.mem_cons_self
  show P (σ.applyTerm a) = P (σ.applyTerm X)
  rw [bound]

/-- **`p(X)` under `X = a` and `p(a)` under `X = a` are equivalent modulo the knowledge.** -/
theorem bound_modulo : Observation.ModuloEquivalent (A sig) callLabel ∅ boundX boundA := by
  refine ⟨Equiv.swap 1 3, ⟨fun o => ?_, fun _ member => absurd member (Finset.notMem_empty _)⟩,
    fun _ => Iff.rfl, ?_⟩
  · show Observation.Entailed (A sig) knowsXa (callLabel (Equiv.swap 1 3 o)) (callLabel o)
    rcases o with _ | _ | _ | _ | n
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact entailed_refl _
    · rw [show (0 + 1 : ℕ) = 1 from rfl, Equiv.swap_apply_left]
      exact entailed_Pa_PX
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact entailed_refl _
    · rw [show (0 + 1 + 1 + 1 : ℕ) = 3 from rfl, Equiv.swap_apply_right]
      exact (Observation.entailedSetoid (A sig) knowsXa).symm entailed_Pa_PX
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      exact entailed_refl _
  · show ({1} : Finset ℕ).map (Equiv.swap 1 3).toEmbedding = {3}
    rw [Finset.map_singleton, Equiv.coe_toEmbedding, Equiv.swap_apply_left]

/-- **The two calls share their table**: they have the same answers. -/
theorem modulo_hit : Answers callLabel factsAB boundX = Answers callLabel factsAB boundA :=
  ModuloEquivalent.answers_eq factsAB facts_supply bound_modulo

/-- **They are not variants**: no renaming of variables makes `p(X)` into `p(a)`. -/
theorem modulo_not_variant : ¬ VariantEquivalent callLabel boundX boundA := by
  rintro ⟨π, κ, covers, -, present⟩
  have moved : ({κ 1} : Finset ℕ) = {3} := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_singleton]
    exact present
  have three : κ 1 = 3 := Finset.singleton_inj.mp moved
  have labelled := covers 1
  rw [three] at labelled
  have inner := P_inj labelled
  cases inner

/-! ### A metarule through the literal wrapper -/

/-- Labels: `0 : m(gp, alice, carol)`, `1 : m(Q, X, Z)`, `2 : m(R, Z, Y)`, every other `a`. -/
def metaLabel : ℕ → Tm
  | 0 => M (.const .gp) (.const .alice) (.const .carol)
  | 1 => M (.var 4) (.var 0) (.var 2)
  | 2 => M (.var 5) (.var 2) (.var 1)
  | _ => a

def metaCall : Configuration Tm ℕ := ⟨[], {0}⟩

/-- Chain: `m(P,X,Y) :- m(Q,X,Z), m(R,Z,Y)`, with `P`, `Q`, `R` the variables `3`, `4`, `5`. -/
def chain : Clause sig :=
  ⟨M (.var 3) (.var 0) (.var 1), [M (.var 4) (.var 0) (.var 2), M (.var 5) (.var 2) (.var 1)]⟩

/-- `P := gp`, `X := alice`, every other variable `carol`. -/
def chainSolution : Subst sig := fun v =>
  if v = 3 then .const .gp else if v = 0 then .const .alice else .const .carol

/-- **The Chain metarule resolves the goal** `m(gp, alice, carol)`. -/
theorem chain_admitted : (resolve 0 chain (Equiv.refl ℕ) [1, 2]).Valid (A sig) metaLabel metaCall := by
  refine (resolve_valid_iff metaLabel metaCall 0 chain _ _).mpr
    ⟨by decide, ?_, by simp [metaCall], ?_, ?_⟩
  · show [metaLabel 1, metaLabel 2] = [rename (Equiv.refl ℕ) _, rename (Equiv.refl ℕ) _]
    rw [rename_refl, rename_refl]
    rfl
  · intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [metaCall]
  · refine ⟨chainSolution, (A sig).models_nil _, ?_⟩
    rw [rename_refl]
    show Subst.applyTerm _ (M _ _ _) = Subst.applyTerm _ (M _ _ _)
    rw [apply_M, apply_M]
    rfl

/-- **The predicate variable is bound by first-order unification**: every solution of the result's
knowledge sends `P` to `gp`, the metasubstitution of this step. -/
theorem chain_binds_predicate (τ : Subst sig)
    (solved : (A sig).Models τ ((resolve 0 chain (Equiv.refl ℕ) [1, 2]).result metaLabel metaCall).equations) :
    τ 3 = .const .gp := by
  rw [resolve_result, rename_refl] at solved
  have pair : τ.applyTerm (M (.var 3) (.var 0) (.var 1)) = τ.applyTerm (metaLabel 0) :=
    (((A sig).models_append _ _ _).mp solved).2 _ List.mem_cons_self
  rw [show metaLabel 0 = M (.const .gp) (.const .alice) (.const .carol) from rfl, apply_M, apply_M] at pair
  exact M_first pair

#print axioms apply_Q
#print axioms apply_R
#print axioms apply_M
#print axioms P_inj
#print axioms R_inj
#print axioms M_first
#print axioms F_ne
#print axioms two_clauses_admitted
#print axioms two_clauses_dependent
#print axioms capture_refused
#print axioms apart_admitted
#print axioms capture_not_fresh
#print axioms apart_fresh
#print axioms capture_loses_answer
#print axioms occurs_fresh
#print axioms occurs_refused
#print axioms atomic_refused
#print axioms splitTake_result
#print axioms split_leaves_residue
#print axioms loop_step
#print axioms loop_never_completes
#print axioms answer_from_every_point
#print axioms covers_swap
#print axioms variants
#print axioms variant_hit
#print axioms variant_hit_answer
#print axioms variants_not_private
#print axioms instance_not_variant
#print axioms instance_answers_differ
#print axioms facts_supply
#print axioms entailed_Pa_PX
#print axioms bound_modulo
#print axioms modulo_hit
#print axioms modulo_not_variant
#print axioms chain_admitted
#print axioms chain_binds_predicate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution.Controls
