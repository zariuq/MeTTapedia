import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.LanguageOnTheStep
import Mettapedia.Languages.Prolog.Eval
import Mettapedia.Logic.LP.SLD

/-!
# ISO Prolog as a core step plus a strategy

**The core.** One SLD resolution step is one firing of the step: it takes the selected goal, reads a
clause renamed apart, tells the unifier, and makes the body goals. That is already proved in the tree
(`Step/ResolutionFiring.lean`: `Resolution.resolve`, `resolve_valid_iff`, `resolve_sld_step`), with
soundness and completeness of resolution runs for every selection rule
(`Step/ResolutionAnswers.lean`). This module adds the strategy.

## Depth-first search over leftmost resolution

`sld prog` is the SLD tree of a ground definite program under the leftmost selection rule, as a
search space: a goal list unfolds into one alternative per clause of its first goal, in program
order. Prolog's strategy is the depth-first policy over it (`Search.Policy.dfs`).

* `sld_sound`, `search_sound`: every answer every policy records is a refutation, and every goal of
  the query is derivable. The strategy is sound by construction.
* Control `Controls.depth_first_incomplete`: for `p :- p.  p.` the query `p` is derivable, the SLD
  tree has an answer, breadth-first records it, and depth-first never does. The selection rule loses
  nothing (resolution is complete for every selection rule); the clause order searched depth-first
  is what loses the answer.

## Control constructs, on the tree's evaluator (`Languages/Prolog/Eval.lean`)

* **The factorization** (`eval_factors`): on the control-free goals (no cut, `once`, if-then-else,
  `\+` or `findall`), `PrologEval` is exactly the depth-first handler (`Handled` with append) over
  its atomic goals (`Atomic`: `true`, `fail`, `var`, `=`, `\=`, `match`, `reduce`), and it never
  signals a cut.
* **Handler independence** (`handler_independence`): on those goals every handler that combines
  the answers of a disjunction as a permutation of append (left first, right first, any) gives the
  same answer bag. Its assumptions: the evaluation terminates (a `Handled` derivation is finite);
  no handler prunes (each keeps every answer of a disjunction, so no first answer, `once` or cut);
  the atomic goals are answered by one oracle, with no effects threaded between branches. A pruning
  handler, or a search that never returns from an infinite branch, can change the answers
  (`Controls.cut_changes_answers`, `Controls.depth_first_incomplete`).
* **Cut is a scoped commit** (`cut_commits`, `cut_commits_iff`): `(!, G ; H)` has exactly the
  answers of `G`, whether `G` ends normally or throws a cut of its own, and `H` is never explored.
  Its scope is the nearest choice point (`Controls.cut_scoped`). Controls:
  `Controls.cut_changes_answers` and `Controls.cut_sees_order`: with the cut `(!, fail ; true)` has
  no answer, without it one, and with its branches swapped one.
* **`\+` is absence of a derivation** (`Controls.negation_not_monotone`): the inner goal gaining an
  answer takes the negation's away. **Operationally `\+` needs no stratification**: a forward firing
  (`Fires`) checks its negated atoms absent in the current store, for every program, and
  `p :- \+ p`, which has no stratification (`Controls.self_negation_unstratified`), fires
  (`Controls.self_negation_fires`). **Stratification** (`Stratified`: positive body atoms at or below
  the head, negated ones strictly below) is an additional declarative adequacy profile.
  `lower_strata_stable`, `absence_stable`: on a stratified program, once the strata below a level
  are saturated (`SaturatedBelow`), every run of the program, firing any of its clauses, leaves the
  atoms below that level as they were, so an absence checked there stays true: the protected region
  that a snapshot alone does not give. These are stated on a ground model of forward chaining over
  atoms, not on the step or the tree's Prolog evaluator. Controls: `Controls.guarded_stratified`,
  `p :- \+ q` is stratified, fires on the empty store and not once `q` is there, and
  `Controls.guarded_absence_protected` keeps `q` absent along its runs;
  `Controls.unstratified_absence_breaks`, `Controls.unsaturated_absence_breaks`: without either
  hypothesis a run makes an atom below the level.

## The logical update view is the pre-state

`DB` keeps every clause with the generation it was asserted in and the one it was retracted in, as
SWI-Prolog does (manual, "Update view"). `view_stable`: for one invocation of a dynamic predicate,
over its whole lifetime, backtracking included, the clauses it iterates are the live clauses of its
own pre-state (`DB.live`), whatever asserts and retracts run after it starts. The view belongs to
the invocation, not to each firing its continuation makes: a call started later has its own
generation and reads another view, so several calls need not share one snapshot. Control
`Controls.update_views_differ`: after a retract and an assert, the running goal still sees the
retracted clause and not the asserted one, while a goal started afterwards sees the reverse.

## `Logic.LP`: factored on ground programs; what blocks the rest

* `lp_factors`: on ground programs a goal list has an `SLDTree` refutation exactly when the leftmost
  SLD space of the program (`lpSld`) has an answer below it, and every search policy records only
  such answers (`answer_sldTree` holds for every program, `sldTree_answer` for ground ones).
  Control: `Controls.lp_loop_refutes`, `p :- p.  p.` in `Logic.LP`.
* Beyond ground programs, `Logic.LP.SLDTree` resolves the leftmost goal against clauses that are
  assumed renamed apart; the renaming is not part of the derivation. The step's resolution firing
  requires a renaming fresh for the configuration (`Resolution.Fresh`), and without it a firing
  captures variables (`ResolutionControls.capture_loses_answer`). So an `SLDTree` derivation is a run
  of the step only after choosing fresh renamings, which `SLDScopedTree` makes explicit with
  activation scopes; mapping scopes to fresh occurrences and renamings is the remaining work.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

namespace ISOProlog

/-! ## Leftmost resolution, searched -/

/-- A ground definite program: clauses as a head and a body, in program order. -/
abbrev Program := List (ℕ × List ℕ)

/-- **The SLD tree under the leftmost rule**, as a search space: the empty goal list is an answer;
otherwise one alternative per clause of the first goal, in program order. -/
def sld (prog : Program) : Search.Space (List ℕ) Unit where
  unfold
    | [] => [.inl ()]
    | a :: rest => (prog.filter fun c => c.1 == a).map fun c => .inr (c.2 ++ rest)

theorem sld_unfold_cons (prog : Program) (a : ℕ) (rest : List ℕ) :
    (sld prog).unfold (a :: rest) = (prog.filter fun c => c.1 == a).map fun c => .inr (c.2 ++ rest) :=
  rfl

/-- **Derivability**: the least set of atoms closed under the clauses. -/
inductive Derivable (prog : Program) : ℕ → Prop
  | rule {head : ℕ} {body : List ℕ} : (head, body) ∈ prog → (∀ b ∈ body, Derivable prog b) →
      Derivable prog head

/-- **Refutations are sound**: an answer of the SLD tree below a goal list derives every goal. -/
theorem sld_sound (prog : Program) : ∀ (w g : List ℕ),
    (sld prog).item (.inr g) w = some (.inl ()) → ∀ a ∈ g, Derivable prog a
  | [], g, h => by simp at h
  | _ :: _, [], _ => fun _ member => absurd member List.not_mem_nil
  | i :: w, a :: rest, h => by
      rw [Search.Space.item_inr_cons, sld_unfold_cons, List.getElem?_map] at h
      cases found : (prog.filter fun c => c.1 == a)[i]? with
      | none =>
          rw [found] at h
          simp at h
      | some c =>
          rw [found] at h
          simp only [Option.map_some, Option.bind_some] at h
          have all := sld_sound prog w (c.2 ++ rest) h
          obtain ⟨inProg, headIs⟩ := List.mem_filter.mp (List.mem_of_getElem? found)
          have headEq : c.1 = a := by simpa using headIs
          intro x member
          rcases List.mem_cons.mp member with rfl | later
          · rw [← headEq]
            exact Derivable.rule (body := c.2) (by simpa using inProg)
              (fun b inBody => all b (List.mem_append_left _ inBody))
          · exact all x (List.mem_append_right _ later)

/-- **Every policy is sound**: what it records derives the query. -/
theorem search_sound (prog : Program) (P : Search.Policy (List ℕ × (Unit ⊕ List ℕ))) {k : ℕ}
    {g : List ℕ} {p : List ℕ × Unit} (found : p ∈ ((sld prog).search P k (.inr g)).found) :
    ∀ a ∈ g, Derivable prog a :=
  sld_sound prog p.1 g ((sld prog).found_sound P found)

/-! ## The tree's evaluator: atomic core, depth-first handler -/

open Mettapedia.Languages.Prolog

/-- **The atomic goals**: the core the handler runs. -/
def Atomic : PrologGoal → Prop
  | .succeed | .fail | .isVar _ | .unify _ _ | .notUnify _ _ | .spaceMatch _ _ | .reduceCall _ => True
  | _ => False

/-- **The control-free goals**: atomic goals under conjunction and disjunction. -/
def ControlFree : PrologGoal → Prop
  | .conj g h => ControlFree g ∧ ControlFree h
  | .disj g h => ControlFree g ∧ ControlFree h
  | .cut | .ite _ _ _ | .once _ | .neg _ | .findall _ _ => False
  | .succeed | .fail | .isVar _ | .unify _ _ | .notUnify _ _ | .spaceMatch _ _ | .reduceCall _ => True

/-- **A handler over the atomic core**: conjunction runs the second goal on each answer of the
first; a disjunction's answers are combined by `combine`. -/
inductive Handled (oracle : EvalOracle) (combine : List PEnv → List PEnv → List PEnv) :
    PrologGoal → PEnv → List PEnv → Prop
  | atom {g : PrologGoal} {env : PEnv} {envs : List PEnv} :
      Atomic g → PrologEval oracle g env (.normal envs) → Handled oracle combine g env envs
  | conj {g h : PrologGoal} {env : PEnv} {pairs : List (PEnv × List PEnv)} :
      Handled oracle combine g env (pairs.map Prod.fst) → (∀ p ∈ pairs, Handled oracle combine h p.1 p.2) →
      Handled oracle combine (.conj g h) env (pairs.flatMap Prod.snd)
  | disj {g h : PrologGoal} {env : PEnv} {first second : List PEnv} :
      Handled oracle combine g env first → Handled oracle combine h env second →
      Handled oracle combine (.disj g h) env (combine first second)

theorem no_cut_signal {envs : List PEnv} {Q : List PEnv → Prop}
    (h : ∃ e, PrologEvalResult.cutThrown envs = .normal e ∧ Q e) : False := by
  obtain ⟨_, bad, _⟩ := h
  cases bad

/-- On control-free goals the evaluator answers normally, as the depth-first handler does. -/
theorem eval_handled {oracle : EvalOracle} {g : PrologGoal} {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle g env r) :
    ControlFree g → ∃ envs, r = .normal envs ∧ Handled oracle (· ++ ·) g env envs := by
  induction h with
  | succeed_eval env => exact fun _ => ⟨_, rfl, .atom trivial (.succeed_eval env)⟩
  | fail_eval env => exact fun _ => ⟨_, rfl, .atom trivial (.fail_eval env)⟩
  | cut_eval => exact fun free => free.elim
  | conj_normal g1 g2 env envs1 pairs h1 h_dom h_each ih1 ih_each =>
      intro free
      obtain ⟨envs1', same, first⟩ := ih1 free.1
      cases same
      refine ⟨_, rfl, .conj (h_dom ▸ first) fun p member => ?_⟩
      obtain ⟨out, same', rest⟩ := ih_each p member free.2
      cases same'
      exact rest
  | conj_g2_cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih_cut =>
      exact fun free => (no_cut_signal (ih_cut free.2)).elim
  | conj_g1_cut _ _ _ _ _ _ _ _ ih1 _ => exact fun free => (no_cut_signal (ih1 free.1)).elim
  | conj_g1_cut_g2_cut _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ _ =>
      exact fun free => (no_cut_signal (ih1 free.1)).elim
  | disj_g1_cut _ _ _ _ _ ih1 => exact fun free => (no_cut_signal (ih1 free.1)).elim
  | disj_normal g1 g2 env envs1 envs2 h1 h2 ih1 ih2 =>
      intro free
      obtain ⟨_, same1, first⟩ := ih1 free.1
      obtain ⟨_, same2, second⟩ := ih2 free.2
      cases same1
      cases same2
      exact ⟨_, rfl, .disj first second⟩
  | disj_g2_cut _ _ _ _ _ _ _ _ ih2 => exact fun free => (no_cut_signal (ih2 free.2)).elim
  | ite_then => exact fun free => free.elim
  | ite_else => exact fun free => free.elim
  | once_some => exact fun free => free.elim
  | once_none => exact fun free => free.elim
  | neg_succ => exact fun free => free.elim
  | neg_fail => exact fun free => free.elim
  | isVar_succ p env v h => exact fun _ => ⟨_, rfl, .atom trivial (.isVar_succ p env v h)⟩
  | isVar_fail p env h => exact fun _ => ⟨_, rfl, .atom trivial (.isVar_fail p env h)⟩
  | unify_succ p q env bs h => exact fun _ => ⟨_, rfl, .atom trivial (.unify_succ p q env bs h)⟩
  | unify_fail p q env h => exact fun _ => ⟨_, rfl, .atom trivial (.unify_fail p q env h)⟩
  | notUnify_succ p q env h => exact fun _ => ⟨_, rfl, .atom trivial (.notUnify_succ p q env h)⟩
  | notUnify_fail p q env bs rest h =>
      exact fun _ => ⟨_, rfl, .atom trivial (.notUnify_fail p q env bs rest h)⟩
  | findall_eval => exact fun free => free.elim
  | spaceMatch_eval pat tmpl env outs h =>
      exact fun _ => ⟨_, rfl, .atom trivial (.spaceMatch_eval pat tmpl env outs h)⟩
  | reduceCall_eval args env outs h =>
      exact fun _ => ⟨_, rfl, .atom trivial (.reduceCall_eval args env outs h)⟩

/-- The depth-first handler's answers are the evaluator's. -/
theorem handled_eval {oracle : EvalOracle} {g : PrologGoal} {env : PEnv} {envs : List PEnv}
    (h : Handled oracle (· ++ ·) g env envs) : PrologEval oracle g env (.normal envs) := by
  induction h with
  | atom _ eval => exact eval
  | @conj g h env pairs _ _ ih ihEach =>
      exact PrologEval.conj_normal g h env (pairs.map Prod.fst) pairs ih rfl ihEach
  | @disj g h env first second _ _ ih1 ih2 => exact PrologEval.disj_normal g h env first second ih1 ih2

/-- **The factorization**: on control-free goals the tree's evaluator is the depth-first handler over
the atomic core, and it never signals a cut. -/
theorem eval_factors (oracle : EvalOracle) {g : PrologGoal} (free : ControlFree g) (env : PEnv) :
    (∀ envs, PrologEval oracle g env (.normal envs) ↔ Handled oracle (· ++ ·) g env envs) ∧
      ∀ envs, ¬ PrologEval oracle g env (.cutThrown envs) := by
  refine ⟨fun envs => ⟨fun h => ?_, handled_eval⟩, fun envs h => ?_⟩
  · obtain ⟨_, same, handled⟩ := eval_handled h free
    cases same
    exact handled
  · obtain ⟨_, bad, _⟩ := eval_handled h free
    cases bad

/-! ## Handler independence for the evaluator -/

/-- Reordering the first components of a list of pairs reorders the pairs. -/
theorem repair {α β : Type*} : ∀ (pairs : List (α × β)) (m : List α),
    (pairs.map Prod.fst).Perm m → ∃ pairs' : List (α × β), pairs'.Perm pairs ∧ pairs'.map Prod.fst = m
  | [], m, perm => ⟨[], .nil, (List.Perm.eq_nil perm.symm).symm⟩
  | (a, b) :: rest, m, perm => by
      have member : a ∈ m := perm.subset List.mem_cons_self
      obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem member
      have restPerm : (rest.map Prod.fst).Perm (m₁ ++ m₂) :=
        (perm.trans List.perm_middle).cons_inv
      obtain ⟨pairs'', perm'', mapped⟩ := repair rest (m₁ ++ m₂) restPerm
      obtain ⟨q₁, q₂, rfl, first, second⟩ := List.map_eq_append_iff.mp mapped
      refine ⟨q₁ ++ (a, b) :: q₂, ?_, by simp [first, second]⟩
      exact List.perm_middle.trans (perm''.cons _)

/-- Choosing a witness for every member of a list of pairs. -/
theorem choose_each {α β : Type*} {R : α × β → β → Prop} :
    ∀ (pairs : List (α × β)), (∀ p ∈ pairs, ∃ b', R p b') →
      ∃ pairs' : List (α × β), pairs'.map Prod.fst = pairs.map Prod.fst ∧
        List.Forall₂ (fun p q => q.1 = p.1 ∧ R p q.2) pairs pairs'
  | [], _ => ⟨[], rfl, .nil⟩
  | p :: rest, each => by
      obtain ⟨b', hb⟩ := each p List.mem_cons_self
      obtain ⟨pairs', mapped, related⟩ := choose_each rest fun q member => each q (List.mem_cons_of_mem p member)
      exact ⟨(p.1, b') :: pairs', by simp [mapped], .cons ⟨rfl, hb⟩ related⟩

theorem flatMap_perm_of_forall₂ {α β : Type*} :
    ∀ {pairs pairs' : List (α × List β)},
      List.Forall₂ (fun p q => q.2.Perm p.2) pairs pairs' → (pairs'.flatMap Prod.snd).Perm (pairs.flatMap Prod.snd)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => by
      simp only [List.flatMap_cons]
      exact head.append (flatMap_perm_of_forall₂ tail)

theorem mem_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ q ∈ l', ∃ p ∈ l, R p q
  | [], [], .nil, _, member => absurd member List.not_mem_nil
  | p :: _, _ :: _, .cons head tail, q, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨p, List.mem_cons_self, head⟩
      · obtain ⟨p', inRest, related⟩ := mem_of_forall₂ tail q later
        exact ⟨p', List.mem_cons_of_mem _ inRest, related⟩

/-- **Handler independence**: two handlers whose disjunctions combine answers as permutations of
append give the same answer bag for every goal with a derivation. Assumptions: the evaluation
terminates (`Handled` is inductive, so a goal that never returns has no derivation); neither handler
prunes (each keeps every answer of a disjunction: no first answer, `once` or cut); the goals are
control-free; the atomic goals are answered by one oracle, with no effects threaded between
branches. -/
theorem handler_independence {oracle : EvalOracle} {combine combine' : List PEnv → List PEnv → List PEnv}
    (shuffles : ∀ A B, (combine A B).Perm (A ++ B)) (shuffles' : ∀ A B, (combine' A B).Perm (A ++ B))
    {g : PrologGoal} {env : PEnv} {envs : List PEnv} (h : Handled oracle combine g env envs) :
    ∃ envs', Handled oracle combine' g env envs' ∧ envs'.Perm envs := by
  induction h with
  | atom atomic eval => exact ⟨_, .atom atomic eval, .refl _⟩
  | @conj g h env pairs _ _ ih ihEach =>
      obtain ⟨m, firstHandled, firstPerm⟩ := ih
      obtain ⟨pairs₁, mapped₁, related⟩ := choose_each pairs ihEach
      obtain ⟨pairs₂, perm₂, mapped₂⟩ :=
        repair pairs₁ m (by rw [mapped₁]; exact firstPerm.symm)
      refine ⟨pairs₂.flatMap Prod.snd, .conj (mapped₂ ▸ firstHandled) fun q member => ?_, ?_⟩
      · obtain ⟨p, _, sameFirst, handled, _⟩ := mem_of_forall₂ related q (perm₂.subset member)
        rw [sameFirst]
        exact handled
      · refine (perm₂.flatMap_right Prod.snd).trans (flatMap_perm_of_forall₂ ?_)
        exact related.imp fun p q r => r.2.2
  | @disj g h env first second _ _ ih1 ih2 =>
      obtain ⟨first', handled1, perm1⟩ := ih1
      obtain ⟨second', handled2, perm2⟩ := ih2
      exact ⟨_, .disj handled1 handled2,
        ((shuffles' first' second').trans (perm1.append perm2)).trans (shuffles first second).symm⟩

/-! ## Cut: a scoped commit -/

/-- **Cut commits**: when `G` has the answers `envs`, so does `(!, G ; H)`, and `H` is never
explored. Both ways: `cut_commits_iff`. -/
theorem cut_commits (oracle : EvalOracle) (g h : PrologGoal) (env : PEnv) (envs : List PEnv)
    (hg : PrologEval oracle g env (.normal envs)) :
    PrologEval oracle (.disj (.conj .cut g) h) env (.normal envs) := by
  have inner := PrologEval.conj_g1_cut (oracle := oracle) .cut g env [env] [(env, envs)]
    (.cut_eval env) rfl (fun p member => by
      rw [List.mem_singleton] at member
      subst member
      exact hg)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at inner
  exact PrologEval.disj_g1_cut _ h env envs inner

/-- **Cut commits, both ways**: `(!, G ; H)` has the answers `envs` exactly when `G` has them,
whether `G` ends normally or throws a cut of its own; `H` is never explored. -/
theorem cut_commits_iff (oracle : EvalOracle) (g h : PrologGoal) (env : PEnv) (envs : List PEnv) :
    PrologEval oracle (.disj (.conj .cut g) h) env (.normal envs) ↔
      ∃ r, PrologEval oracle g env r ∧ r.answers = envs := by
  constructor
  · intro eval
    cases eval with
    | disj_g1_cut _ _ _ _ inner =>
        cases inner with
        | conj_g2_cut _ _ _ _ _ _ _ _ cutEval _ _ _ => cases cutEval
        | conj_g1_cut _ _ _ _ pairs cutEval dom each =>
            cases cutEval
            cases pairs with
            | nil => simp at dom
            | cons p rest =>
                cases rest with
                | nil =>
                    obtain ⟨same, _⟩ := List.cons.inj dom
                    refine ⟨.normal p.2, ?_, by simp [PrologEvalResult.answers]⟩
                    rw [same]
                    exact each p (List.mem_singleton_self p)
                | cons _ _ => simp at dom
        | conj_g1_cut_g2_cut _ _ _ _ pref _ cutOut _ cutEval split _ thrown =>
            cases cutEval
            cases pref with
            | nil =>
                obtain ⟨same, _⟩ := List.cons.inj split
                refine ⟨.cutThrown cutOut, ?_, by simp [PrologEvalResult.answers]⟩
                rw [same]
                exact thrown
            | cons _ _ => simp at split
    | disj_normal _ _ _ _ _ inner _ =>
        cases inner with
        | conj_normal _ _ _ _ _ cutEval _ _ => cases cutEval
  · rintro ⟨r, eval, rfl⟩
    cases r with
    | normal envs' => exact cut_commits oracle g h env envs' eval
    | cutThrown envs' =>
        exact PrologEval.disj_g1_cut _ h env _
          (PrologEval.conj_g1_cut_g2_cut .cut g env [env] [] env envs' [] (.cut_eval env) rfl
            (fun _ member => absurd member List.not_mem_nil) eval)

/-! ## Negation and stratification -/

/-- A ground normal program: a head, a positive body and a negated body. -/
abbrev NormalProgram := List (ℕ × List ℕ × List ℕ)

/-- **A stratification**: positive body atoms at or below the head, negated ones strictly below. -/
def Stratified (level : ℕ → ℕ) (prog : NormalProgram) : Prop :=
  ∀ c ∈ prog, (∀ b ∈ c.2.1, level b ≤ level c.1) ∧ ∀ b ∈ c.2.2, level b < level c.1

/-- **One forward firing** of a clause of the program: its positive body present, its negated body
absent, its head added. -/
def Fires (prog : NormalProgram) (S S' : Finset ℕ) : Prop :=
  ∃ c ∈ prog, (∀ b ∈ c.2.1, b ∈ S) ∧ (∀ b ∈ c.2.2, b ∉ S) ∧ S' = insert c.1 S

/-- **The strata below `k` are saturated** at `S`: every clause whose head sits below `k` and whose
body holds at `S` has its head in `S`. -/
def SaturatedBelow (level : ℕ → ℕ) (k : ℕ) (prog : NormalProgram) (S : Finset ℕ) : Prop :=
  ∀ c ∈ prog, level c.1 < k → (∀ b ∈ c.2.1, b ∈ S) → (∀ b ∈ c.2.2, b ∉ S) → c.1 ∈ S

/-- **The strata below a level are stable.** On a stratified program, once the strata below `k` are
saturated, every run of the program, firing any of its clauses, leaves every atom below `k` as it
was: a clause whose head sits below `k` reads only atoms below `k`, so it fires only where it had
already fired. -/
theorem lower_strata_stable {level : ℕ → ℕ} {k : ℕ} {prog : NormalProgram}
    (stratified : Stratified level prog) {S S' : Finset ℕ} (saturated : SaturatedBelow level k prog S)
    (run : Relation.ReflTransGen (Fires prog) S S') : ∀ a, level a < k → (a ∈ S' ↔ a ∈ S) := by
  induction run with
  | refl => exact fun _ _ => Iff.rfl
  | tail _ step earlier =>
      intro a low
      obtain ⟨c, member, positive, negative, rfl⟩ := step
      rw [Finset.mem_insert]
      by_cases high : k ≤ level c.1
      · have different : a ≠ c.1 := by
          rintro rfl
          omega
        rw [or_iff_right different]
        exact earlier a low
      · have headLow : level c.1 < k := by omega
        have atStart : c.1 ∈ S := saturated c member headLow
          (fun b inBody => (earlier b (lt_of_le_of_lt ((stratified c member).1 b inBody) headLow)).mp
            (positive b inBody))
          (fun b inBody present => negative b inBody
            ((earlier b (lt_trans ((stratified c member).2 b inBody) headLow)).mpr present))
        constructor
        · rintro (same | old)
          · rw [same]
            exact atStart
          · exact (earlier a low).mp old
        · exact fun inS => Or.inr ((earlier a low).mpr inS)

/-- **Absence below a level is stable under stratification**: on a stratified program, once the
strata below `k` are saturated, an atom below `k` absent at the start stays absent along every run of
the program. Both hypotheses are needed (`Controls.unstratified_absence_breaks`,
`Controls.unsaturated_absence_breaks`). -/
theorem absence_stable {level : ℕ → ℕ} {k : ℕ} {prog : NormalProgram}
    (stratified : Stratified level prog) {S S' : Finset ℕ} (saturated : SaturatedBelow level k prog S)
    (run : Relation.ReflTransGen (Fires prog) S S') {b : ℕ} (low : level b < k) (absent : b ∉ S) :
    b ∉ S' :=
  fun present => absent ((lower_strata_stable stratified saturated run b low).mp present)

/-! ## The logical update view -/

/-- A stored clause with the generation it was asserted in and the one it was retracted in. -/
structure Row (α : Type*) where
  clause : α
  born : ℕ
  died : Option ℕ

/-- A row is visible to a goal started at generation `g`. -/
def Row.alive {α : Type*} (r : Row α) (g : ℕ) : Bool :=
  decide (r.born ≤ g) && match r.died with
    | none => true
    | some d => decide (g < d)

/-- **A database with generations.** -/
structure DB (α : Type*) where
  rows : List (Row α)
  gen : ℕ

namespace DB

variable {α : Type*}

/-- The clauses a goal started at generation `g` iterates. -/
def view (D : DB α) (g : ℕ) : List α := (D.rows.filter fun r => r.alive g).map Row.clause

/-- The live clauses now. -/
def live (D : DB α) : List α := D.view D.gen

/-- `assert`: a new row, born in the next generation. -/
def assert (D : DB α) (c : α) : DB α := ⟨D.rows ++ [⟨c, D.gen + 1, none⟩], D.gen + 1⟩

/-- `retract`: every live row whose clause is selected dies in the next generation. -/
def retract (D : DB α) (p : α → Bool) : DB α :=
  ⟨D.rows.map fun r => if p r.clause && r.died.isNone then { r with died := some (D.gen + 1) } else r,
    D.gen + 1⟩

/-- An update. -/
inductive Update (α : Type*)
  | assert (c : α)
  | retract (p : α → Bool)

def apply (D : DB α) : Update α → DB α
  | .assert c => D.assert c
  | .retract p => D.retract p

theorem apply_gen (D : DB α) (u : Update α) : (D.apply u).gen = D.gen + 1 := by
  cases u <;> rfl

theorem view_assert (D : DB α) (c : α) {g : ℕ} (early : g ≤ D.gen) : (D.assert c).view g = D.view g := by
  have unseen : (⟨c, D.gen + 1, none⟩ : Row α).alive g = false := by
    simp only [Row.alive, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left
    omega
  simp [view, assert, List.filter_append, unseen]

theorem view_retract (D : DB α) (p : α → Bool) {g : ℕ} (early : g ≤ D.gen) :
    (D.retract p).view g = D.view g := by
  simp only [view, retract, List.filter_map, List.map_map]
  congr 1
  · funext r
    simp only [Function.comp]
    split_ifs <;> rfl
  · apply List.filter_congr
    intro r _
    simp only [Function.comp]
    split_ifs with chosen
    · obtain ⟨_, alive⟩ := Bool.and_eq_true_iff.mp chosen
      cases died : r.died with
      | none => simp [Row.alive, died]; omega
      | some d => simp [died] at alive
    · rfl

theorem view_apply (D : DB α) (u : Update α) {g : ℕ} (early : g ≤ D.gen) :
    (D.apply u).view g = D.view g := by
  cases u with
  | assert c => exact view_assert D c early
  | retract p => exact view_retract D p early

/-- **The logical update view of one invocation is its pre-state**: an invocation of a dynamic
predicate started at generation `D.gen` iterates, over its whole lifetime and through backtracking,
the clauses live at its start, whatever asserts and retracts run meanwhile. Each invocation has its
own start: a call started after the updates reads another view (`Controls.update_views_differ`),
and nothing makes several calls share one snapshot. -/
theorem view_stable : ∀ (ops : List (Update α)) (D : DB α), (ops.foldl apply D).view D.gen = D.live
  | [], _ => rfl
  | u :: ops, D => by
      have later : ∀ (ops : List (Update α)) (D' : DB α) (g : ℕ), g ≤ D'.gen →
          (ops.foldl apply D').view g = D'.view g := by
        intro ops
        induction ops with
        | nil => intro _ _ _; rfl
        | cons v more ih =>
            intro D' g early
            rw [List.foldl_cons, ih (D'.apply v) g (by rw [apply_gen]; omega), view_apply D' v early]
      exact later (u :: ops) D D.gen le_rfl

end DB

/-! ## `Logic.LP` on its ground fragment -/

section LogicPrograms

open Mettapedia.Logic.LP (Atom Clause Subst Term SLDTree LPSignature)

open Classical in
/-- **The ground SLD space of a `Logic.LP` program** under the leftmost rule, as a search space on
goal lists: one alternative per clause whose head equals the first goal, in program order. Heads are
matched by equality, not unification, so this is the SLD tree only on ground programs
(`sldTree_answer`, `lp_factors`). -/
def lpSld {σ : LPSignature} (prog : Mettapedia.Logic.LP.Program σ) :
    Search.Space (List (Atom σ)) Unit where
  unfold
    | [] => [.inl ()]
    | a :: rest => (prog.filter fun c => decide (c.head = a)).map fun c => .inr (c.body ++ rest)

theorem applyTerm_ground {σ : LPSignature} (θ : Subst σ) :
    ∀ t : Term σ, t.isGround → θ.applyTerm t = t
  | .var _, ground => ground.elim
  | .const _, _ => rfl
  | .app f ts, ground => by
      show Term.app f (fun i => θ.applyTerm (ts i)) = Term.app f ts
      congr 1
      funext i
      exact applyTerm_ground θ (ts i) (ground i)

theorem applyAtom_ground {σ : LPSignature} (θ : Subst σ) (a : Atom σ) (ground : a.isGround) :
    θ.applyAtom a = a := by
  cases a with
  | mk symbol args =>
      show Atom.mk symbol (fun i => θ.applyTerm (args i)) = Atom.mk symbol args
      congr 1
      funext i
      exact applyTerm_ground θ (args i) (ground i)

theorem applyAtoms_ground {σ : LPSignature} (θ : Subst σ) (l : List (Atom σ))
    (ground : ∀ a ∈ l, a.isGround) : θ.applyAtoms l = l :=
  (List.map_congr_left fun a member => applyAtom_ground θ a (ground a member)).trans (List.map_id l)

/-- **Every answer of the leftmost SLD space is an `SLDTree` refutation**, each step unifying by
the identity. -/
theorem answer_sldTree {σ : LPSignature} (prog : Mettapedia.Logic.LP.Program σ) :
    ∀ (w : List ℕ) (goals : List (Atom σ)), (lpSld prog).item (.inr goals) w = some (.inl ()) →
      ∃ θ, SLDTree prog goals θ
  | [], _, h => by simp at h
  | _ :: _, [], _ => ⟨_, .nil⟩
  | i :: w, a :: rest, h => by
      classical
      rw [Search.Space.item_inr_cons] at h
      change ((prog.filter fun c => decide (c.head = a)).map
        fun c => (Sum.inr (c.body ++ rest) : Unit ⊕ List (Atom σ)))[i]?.bind
          (fun y => (lpSld prog).item y w) = _ at h
      rw [List.getElem?_map] at h
      cases found : (prog.filter fun c => decide (c.head = a))[i]? with
      | none =>
          rw [found] at h
          simp at h
      | some c =>
          rw [found] at h
          simp only [Option.map_some, Option.bind_some] at h
          obtain ⟨θ', tree⟩ := answer_sldTree prog w (c.body ++ rest) h
          obtain ⟨member, headIs⟩ := List.mem_filter.mp (List.mem_of_getElem? found)
          have same : c.head = a := by simpa using headIs
          refine ⟨θ' ∘ₛ Subst.id σ, .cons a rest c (Subst.id σ) θ' member (by rw [same]) ?_⟩
          rwa [Mettapedia.Logic.LP.Subst.applyAtoms_id]

/-- **On ground programs, every `SLDTree` refutation is an answer of the leftmost SLD space.** -/
theorem sldTree_answer {σ : LPSignature} {prog : Mettapedia.Logic.LP.Program σ}
    (groundProg : ∀ c ∈ prog, c.head.isGround ∧ ∀ b ∈ c.body, b.isGround)
    {goals : List (Atom σ)} {θ : Subst σ} (tree : SLDTree prog goals θ) :
    (∀ a ∈ goals, a.isGround) → ∃ w, (lpSld prog).item (.inr goals) w = some (.inl ()) := by
  classical
  induction tree with
  | nil => exact fun _ => ⟨[0], rfl⟩
  | cons a goals c θ θ' member unify rest ih =>
      intro groundGoals
      obtain ⟨headGround, bodyGround⟩ := groundProg c member
      have same : a = c.head := by
        rwa [applyAtom_ground θ a (groundGoals a List.mem_cons_self),
          applyAtom_ground θ c.head headGround] at unify
      have restGround : ∀ x ∈ c.body ++ goals, x.isGround := by
        intro x member'
        rcases List.mem_append.mp member' with inBody | inGoals
        · exact bodyGround x inBody
        · exact groundGoals x (List.mem_cons_of_mem a inGoals)
      have substituted : θ.applyAtoms (c.body ++ goals) = c.body ++ goals :=
        applyAtoms_ground θ _ restGround
      obtain ⟨w, found⟩ := ih (by rw [substituted]; exact restGround)
      rw [substituted] at found
      have inFilter : c ∈ prog.filter fun c' => decide (c'.head = a) :=
        List.mem_filter.mpr ⟨member, by simp [same]⟩
      obtain ⟨i, get⟩ := List.mem_iff_getElem?.mp inFilter
      refine ⟨i :: w, ?_⟩
      rw [Search.Space.item_inr_cons]
      change ((prog.filter fun c' => decide (c'.head = a)).map
        fun c' => (Sum.inr (c'.body ++ goals) : Unit ⊕ List (Atom σ)))[i]?.bind
          (fun y => (lpSld prog).item y w) = _
      rw [List.getElem?_map, get]
      exact found

/-- **The factorization of `Logic.LP` on ground programs**: a goal list has an `SLDTree`
refutation exactly when the leftmost SLD space has an answer below it; Prolog's strategy is the
depth-first policy over that space, and every policy records only such answers. -/
theorem lp_factors {σ : LPSignature} {prog : Mettapedia.Logic.LP.Program σ}
    (groundProg : ∀ c ∈ prog, c.head.isGround ∧ ∀ b ∈ c.body, b.isGround)
    {goals : List (Atom σ)} (groundGoals : ∀ a ∈ goals, a.isGround) :
    ((∃ θ, SLDTree prog goals θ) ↔ ∃ w, (lpSld prog).item (.inr goals) w = some (.inl ())) ∧
      ∀ (P : Search.Policy (List ℕ × (Unit ⊕ List (Atom σ)))) (k : ℕ) (p : List ℕ × Unit),
        p ∈ ((lpSld prog).search P k (.inr goals)).found → ∃ θ, SLDTree prog goals θ :=
  ⟨⟨fun ⟨_, tree⟩ => sldTree_answer groundProg tree groundGoals,
      fun ⟨w, found⟩ => answer_sldTree prog w goals found⟩,
    fun P _ p found => answer_sldTree prog p.1 goals ((lpSld prog).found_sound P found)⟩

end LogicPrograms

/-! ## Controls -/

namespace Controls

/-- `p :- p.  p.` -/
def leftRecursive : Program := [(0, [0]), (0, [])]

theorem derivable : Derivable leftRecursive 0 :=
  .rule (body := []) (by decide) fun _ member => absurd member List.not_mem_nil

theorem children_loop (w : List ℕ) :
    (sld leftRecursive).children w [0] = [(w ++ [0], .inr [0]), (w ++ [1], .inr [])] := rfl

theorem dfs_shape : ∀ k : ℕ, ∃ w rest,
    (sld leftRecursive).search .dfs k (.inr [0]) = ⟨[], (w, .inr [0]) :: rest⟩
  | 0 => ⟨[], [], rfl⟩
  | k + 1 => by
      obtain ⟨w, rest, same⟩ := dfs_shape k
      refine ⟨w ++ [0], (w ++ [1], .inr []) :: rest, ?_⟩
      rw [Search.Space.search_succ, same]
      show (⟨[], Search.Policy.dfs.insert ((sld leftRecursive).children w [0]) rest⟩ :
        Search.Config (List ℕ) Unit) = _
      rw [children_loop]
      rfl

/-- **Negative control: depth-first is incomplete.** The query is derivable and the SLD tree has an
answer, which breadth-first records at budget six; depth-first records nothing at any budget. -/
theorem depth_first_incomplete :
    Derivable leftRecursive 0 ∧ (([1, 0], ()) : List ℕ × Unit) ∈ (sld leftRecursive).Answers (.inr [0]) ∧
      ((sld leftRecursive).search .bfs 6 (.inr [0])).found = [([1, 0], ())] ∧
      ∀ k, ((sld leftRecursive).search .dfs k (.inr [0])).found = [] := by
  refine ⟨derivable, rfl, rfl, fun k => ?_⟩
  obtain ⟨w, rest, same⟩ := dfs_shape k
  rw [same]

open Mettapedia.Languages.Prolog

theorem fail_result {oracle : EvalOracle} {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle .fail env r) : r = .normal [] := by
  cases h
  rfl

theorem cut_result {oracle : EvalOracle} {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle .cut env r) : r = .cutThrown [env] := by
  cases h
  rfl

theorem cut_fail_result {oracle : EvalOracle} {env : PEnv} {r : PrologEvalResult}
    (h : PrologEval oracle (.conj .cut .fail) env r) : r = .cutThrown [] := by
  cases h with
  | conj_normal _ _ _ _ _ h1 _ _ => cases cut_result h1
  | conj_g2_cut _ _ _ _ _ _ _ _ h1 _ _ _ => cases cut_result h1
  | conj_g1_cut _ _ _ _ pairs _ _ h_each =>
      have empty : ∀ p ∈ pairs, p.2 = [] := fun p member =>
        PrologEvalResult.normal.inj (fail_result (h_each p member))
      rw [List.flatMap_eq_nil_iff.mpr empty]
  | conj_g1_cut_g2_cut _ _ _ _ _ _ _ _ _ _ _ h_cut => cases fail_result h_cut

/-- **Control: cut changes answers.** With the cut, `(!, fail ; true)` has no answer at all; without
it, `(true, fail ; true)` has one. -/
theorem cut_changes_answers (oracle : EvalOracle) (env : PEnv) :
    (∀ r, PrologEval oracle (.disj (.conj .cut .fail) .succeed) env r → r.answers = []) ∧
      PrologEval oracle (.disj (.conj .succeed .fail) .succeed) env (.normal [env]) := by
  refine ⟨fun r h => ?_, ?_⟩
  · cases h with
    | disj_g1_cut _ _ _ envs1 h1 =>
        cases cut_fail_result h1
        rfl
    | disj_normal _ _ _ _ _ h1 _ => cases cut_fail_result h1
    | disj_g2_cut _ _ _ _ _ h1 _ => cases cut_fail_result h1
  · have inner : PrologEval oracle (.conj .succeed .fail) env (.normal []) :=
      PrologEval.conj_normal .succeed .fail env [env] [(env, [])] (.succeed_eval env) rfl
        fun p member => by
          rw [List.mem_singleton] at member
          subst member
          exact .fail_eval env
    exact PrologEval.disj_normal _ _ env [] [env] inner (.succeed_eval env)

/-- **Control: cut sees order.** Swapping the branches of `(!, fail ; true)` gives an answer. -/
theorem cut_sees_order (oracle : EvalOracle) (env : PEnv) :
    PrologEval oracle (.disj .succeed (.conj .cut .fail)) env (.cutThrown [env]) := by
  have inner : PrologEval oracle (.conj .cut .fail) env (.cutThrown []) :=
    PrologEval.conj_g1_cut .cut .fail env [env] [(env, [])] (.cut_eval env) rfl fun p member => by
      rw [List.mem_singleton] at member
      subst member
      exact .fail_eval env
  exact PrologEval.disj_g2_cut _ _ env [env] [] (.succeed_eval env) inner

/-- **Control: the scope of a cut is its choice point.** In `((!, fail ; true) ; true)` the inner
choice point absorbs the cut and the outer alternative still answers. -/
theorem cut_scoped (oracle : EvalOracle) (env : PEnv) :
    PrologEval oracle (.disj (.disj (.conj .cut .fail) .succeed) .succeed) env (.normal [env]) := by
  have inner : PrologEval oracle (.conj .cut .fail) env (.cutThrown []) :=
    PrologEval.conj_g1_cut .cut .fail env [env] [(env, [])] (.cut_eval env) rfl fun p member => by
      rw [List.mem_singleton] at member
      subst member
      exact .fail_eval env
  exact PrologEval.disj_normal _ _ env [] [env] (PrologEval.disj_g1_cut _ _ env [] inner)
    (.succeed_eval env)

/-- **Control: negation is not monotone.** `\+ q` answers while `q` has no clause; once `q` gains an
answer, `\+ q` has none. -/
theorem negation_not_monotone (oracle : EvalOracle) (env : PEnv) :
    PrologEval oracle (.neg .fail) env (.normal [env]) ∧
      PrologEval oracle (.disj .fail .succeed) env (.normal [env]) ∧
      PrologEval oracle (.neg (.disj .fail .succeed)) env (.normal []) :=
  ⟨.neg_succ _ env _ (.fail_eval env) rfl,
    .disj_normal _ _ env [] [env] (.fail_eval env) (.succeed_eval env),
    .neg_fail _ env _ env [] (.disj_normal _ _ env [] [env] (.fail_eval env) (.succeed_eval env)) rfl⟩

/-- `p :- \+ q.` with `p = 1`, `q = 0`. -/
def guarded : NormalProgram := [(1, [], [0])]

/-- **Control: stratified, and the absence is read below.** `p :- \+ q` fires on the empty store
and not once `q` is there. -/
theorem guarded_stratified :
    Stratified (fun a => a) guarded ∧ Fires guarded ∅ {1} ∧ ∀ S', ¬ Fires guarded {0} S' := by
  refine ⟨?_, ⟨(1, [], [0]), by decide, by simp, by simp, rfl⟩, ?_⟩
  · intro c member
    simp only [guarded, List.mem_singleton] at member
    subst member
    exact ⟨by simp, by simp⟩
  · rintro S' ⟨c, member, _, absent, _⟩
    simp only [guarded, List.mem_singleton] at member
    subst member
    exact absent 0 (by simp) (by simp)

/-- **Positive control: the protected region.** Along every run of `p :- \+ q` from the empty store,
`q` stays absent: the strata below `1` are saturated there (`absence_stable`). -/
theorem guarded_absence_protected {S' : Finset ℕ} (run : Relation.ReflTransGen (Fires guarded) ∅ S') :
    0 ∉ S' :=
  absence_stable (k := 1) guarded_stratified.1 (fun c member low _ _ => by
    simp only [guarded, List.mem_singleton] at member
    subst member
    exact absurd low (by decide)) run (by decide) (Finset.notMem_empty 0)

/-- `p :- q.  q.` with `p = 0` and `q = 1`: the positive body sits above the head. -/
def upward : NormalProgram := [(1, [], []), (0, [1], [])]

/-- **Control: without stratification, absence below a level is not stable.** With the atoms as
their own levels, `upward` is not stratified, the empty store is saturated below `1`, and a run from
it makes `0`, absent at the start. -/
theorem unstratified_absence_breaks :
    ¬ Stratified (fun a => a) upward ∧ SaturatedBelow (fun a => a) 1 upward ∅ ∧
      Relation.ReflTransGen (Fires upward) ∅ {0, 1} := by
  refine ⟨fun stratified => ?_, ?_, ?_⟩
  · exact absurd ((stratified (0, [1], []) (by decide)).1 1 (by decide)) (by decide)
  · intro c member low positive _
    simp only [upward, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact absurd low (by decide)
    · exact absurd (positive 1 (by decide)) (Finset.notMem_empty 1)
  · have first : Fires upward ∅ {1} := ⟨(1, [], []), by decide, by decide, by decide, rfl⟩
    have second : Fires upward {1} {0, 1} := ⟨(0, [1], []), by decide, by decide, by decide, rfl⟩
    exact .tail (.single first) second

/-- `p.` with `p = 0`. -/
def fact0 : NormalProgram := [(0, [], [])]

/-- **Control: without saturation, absence below a level is not stable.** `p.` is stratified, the
empty store is not saturated below `1`, and a run from it makes `0`. -/
theorem unsaturated_absence_breaks :
    Stratified (fun a => a) fact0 ∧ ¬ SaturatedBelow (fun a => a) 1 fact0 ∅ ∧
      Relation.ReflTransGen (Fires fact0) ∅ {0} := by
  refine ⟨?_, fun saturated => ?_, .single ⟨(0, [], []), by decide, by decide, by decide, rfl⟩⟩
  · intro c member
    simp only [fact0, List.mem_singleton] at member
    subst member
    exact ⟨by decide, by decide⟩
  · exact Finset.notMem_empty 0
      (saturated (0, [], []) (by decide) (by decide) (by decide) (by decide))

/-- **Control: `p :- \+ p` has no stratification.** -/
theorem self_negation_unstratified (level : ℕ → ℕ) : ¬ Stratified level [(1, [], [1])] := by
  intro stratified
  have := (stratified (1, [], [1]) (by simp)).2 1 (by simp)
  exact lt_irrefl _ this

/-- **Control: operationally `\+` needs no stratification.** `p :- \+ p` has none
(`self_negation_unstratified`), yet it fires on the empty store, where `p` is absent. -/
theorem self_negation_fires : Fires [(1, [], [1])] ∅ {1} :=
  ⟨(1, [], [1]), by decide, by decide, by decide, rfl⟩

/-- One predicate `p` without arguments. -/
abbrev propSig : Mettapedia.Logic.LP.LPSignature where
  constants := Unit
  vars := ℕ
  relationSymbols := Unit
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := fun e => e.elim

def pAtom : Mettapedia.Logic.LP.Atom propSig := ⟨(), Fin.elim0⟩

/-- `p :- p.  p.` in `Logic.LP`. -/
def loopLP : Mettapedia.Logic.LP.Program propSig := [⟨pAtom, [pAtom]⟩, ⟨pAtom, []⟩]

theorem pAtom_ground : pAtom.isGround := fun i => i.elim0

/-- **Positive control for the `Logic.LP` factorization.** The query `p` has an `SLDTree` refutation
through the second clause, hence an answer of the leftmost SLD space. -/
theorem lp_loop_refutes :
    (∃ θ, Mettapedia.Logic.LP.SLDTree loopLP [pAtom] θ) ∧
      ∃ w, (lpSld loopLP).item (.inr [pAtom]) w = some (.inl ()) := by
  have tree : Mettapedia.Logic.LP.SLDTree loopLP [pAtom] _ :=
    .cons pAtom [] ⟨pAtom, []⟩ (Mettapedia.Logic.LP.Subst.id propSig) (Mettapedia.Logic.LP.Subst.id propSig)
      (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) rfl .nil
  have groundProg : ∀ c ∈ loopLP, c.head.isGround ∧ ∀ b ∈ c.body, b.isGround := by
    intro c member
    simp only [loopLP, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨pAtom_ground, fun b inBody => by
        rw [List.mem_singleton] at inBody
        rw [inBody]
        exact pAtom_ground⟩
    · exact ⟨pAtom_ground, fun b inBody => absurd inBody List.not_mem_nil⟩
  exact ⟨⟨_, tree⟩, ((lp_factors groundProg fun a member => by
    rw [List.mem_singleton] at member
    rw [member]
    exact pAtom_ground).1.mp ⟨_, tree⟩)⟩

/-- **Control: the two update views differ.** A goal started on clauses `10`, `11` keeps seeing both
after `11` is retracted and `12` asserted; a goal started afterwards sees `10` and `12`. -/
theorem update_views_differ :
    let D : DB ℕ := ⟨[⟨10, 0, none⟩, ⟨11, 0, none⟩], 0⟩
    let D' := (D.retract (· == 11)).assert 12
    D'.view D.gen = [10, 11] ∧ D'.live = [10, 12] := by
  constructor <;> rfl

end Controls

#print axioms sld_sound
#print axioms search_sound
#print axioms eval_factors
#print axioms handler_independence
#print axioms cut_commits
#print axioms cut_commits_iff
#print axioms lower_strata_stable
#print axioms absence_stable
#print axioms DB.view_stable
#print axioms answer_sldTree
#print axioms sldTree_answer
#print axioms lp_factors
#print axioms Controls.depth_first_incomplete
#print axioms Controls.cut_changes_answers
#print axioms Controls.cut_sees_order
#print axioms Controls.cut_scoped
#print axioms Controls.negation_not_monotone
#print axioms Controls.guarded_stratified
#print axioms Controls.guarded_absence_protected
#print axioms Controls.unstratified_absence_breaks
#print axioms Controls.unsaturated_absence_breaks
#print axioms Controls.self_negation_unstratified
#print axioms Controls.self_negation_fires
#print axioms Controls.update_views_differ
#print axioms Controls.lp_loop_refutes

end ISOProlog

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
