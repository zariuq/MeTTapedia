import Mettapedia.Logic.ASP.Certificate

/-!
# The certificate checker and the action-by-action LRAT checker agree

The certificate checker (`Program.checkCert`) checks RUP additions as they come,
against its live clauses. The action-by-action LRAT checker
(`PropositionalLRATActions.check`) first compiles the whole action stream to a
derivation graph, resolving identifiers, and then replays the graph. This module
proves that on certificates of LRAT actions only, without loop or Hall steps,
they run in lockstep.

## The simulation

* `actStep` runs the action checker one action at a time: compile the action,
  then replay the nodes it added. Running it over a stream is compiling and then
  replaying the whole graph (`foldlM_actStep_iff`).
* `Agree` relates the two states: the action checker's graph replays to its cache,
  and the certificate checker's live clauses are, in order, the action checker's
  live identifiers with the clauses they name in the cache.
* **Lockstep** (`certStep_actStep`, `foldlM_agree`): on every LRAT action both
  checkers fail, or both succeed and still agree. The starting states agree
  (`agree_start`): the inputs are numbered `1, 2, …` on both sides.

## Agreement

* **The certificate checker accepts exactly when the action checker compiles
  and replays the stream and some live identifier names the empty clause**
  (`Program.checkCert_lrat_iff`).
* So acceptance by the certificate checker implies acceptance by the action
  checker (`Program.check_of_checkCert_lrat`).
* **Without deletions the two checkers accept the same certificates**
  (`Program.checkCert_lrat_iff_check`): every replayed clause stays live.
* With deletions they can differ, and only one way: the action checker accepts
  an empty clause that was derived and then deleted, the certificate checker
  does not. A control in `DriverControls` shows it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic PropositionalFormula PropositionalLRATActions Mettapedia.Logic.DerivationGraph

universe u

/-! ## Live clauses on both sides -/

/-- A live clause of the certificate checker and a live identifier of the action checker agree:
the same identifier, naming the same clause. -/
def LiveAgree (cache : Array Clause) (e : ℕ × Clause) (p : ℕ × ℕ) : Prop := e.1 = p.1 ∧ cache[p.2]? = some e.2

theorem lookupClause_cons (e : ℕ × Clause) (live : List (ℕ × Clause)) (id : ℕ) :
    lookupClause (e :: live) id = if e.1 = id then some e.2 else lookupClause live id := by
  unfold lookupClause
  rw [List.find?_cons]
  by_cases h : e.1 = id
  · simp [h]
  · have : (e.1 == id) = false := by simpa using h
    simp [h, this]

theorem lookupId_cons (p : ℕ × ℕ) (live : List (ℕ × ℕ)) (id : ℕ) :
    lookupId (p :: live) id = if p.1 = id then some p.2 else lookupId live id := by
  unfold lookupId
  rw [List.find?_cons]
  by_cases h : p.1 = id
  · simp [h]
  · have : (p.1 == id) = false := by simpa using h
    simp [h, this]

theorem lookupClause_agree {cache : Array Clause} :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      ∀ id, lookupClause live id = (lookupId ids id).bind fun p => cache[p]?
  | [], [], .nil, _ => rfl
  | e :: _, q :: _, .cons ⟨same, hc⟩ rest, id => by
    rw [lookupClause_cons, lookupId_cons, ← same]
    by_cases h : e.1 = id
    · simp [h, hc]
    · simp only [h, if_false]
      exact lookupClause_agree rest id

theorem isSome_lookupClause_agree {cache : Array Clause} :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      ∀ id, (lookupClause live id).isSome = (lookupId ids id).isSome
  | [], [], .nil, _ => rfl
  | e :: _, q :: _, .cons ⟨same, _⟩ rest, id => by
    rw [lookupClause_cons, lookupId_cons, ← same]
    by_cases h : e.1 = id
    · simp [h]
    · simp only [h, if_false]
      exact isSome_lookupClause_agree rest id

theorem mapM_lookupClause_agree {cache : Array Clause} {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}
    (h : List.Forall₂ (LiveAgree cache) live ids) :
    ∀ hints : List ℕ, hints.mapM (lookupClause live) = (hints.mapM (lookupId ids)).bind (lookupPremises cache)
  | [] => rfl
  | i :: hints => by
    have ih := mapM_lookupClause_agree h hints
    simp only [List.mapM_cons, lookupClause_agree h i]
    cases hi : lookupId ids i with
    | none => rfl
    | some p =>
      cases hc : cache[p]? with
      | none =>
        cases hints.mapM (lookupId ids) <;> simp [lookupPremises, hc]
      | some c =>
        rw [ih]
        cases hints.mapM (lookupId ids) <;> simp [lookupPremises, hc]

theorem forall₂_filter {cache : Array Clause} (keep : ℕ → Bool) :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      List.Forall₂ (LiveAgree cache) (live.filter fun e => keep e.1) (ids.filter fun p => keep p.1)
  | [], [], .nil => .nil
  | e :: _, q :: _, .cons ⟨same, hc⟩ rest => by
    simp only [List.filter_cons, ← same]
    split
    · exact .cons ⟨same, hc⟩ (forall₂_filter keep rest)
    · exact forall₂_filter keep rest

theorem forall₂_push {cache : Array Clause} (c : Clause) :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      List.Forall₂ (LiveAgree (cache.push c)) live ids
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons ⟨same, hc⟩ rest => by
    refine .cons ⟨same, ?_⟩ (forall₂_push c rest)
    have inside := (Array.getElem?_eq_some_iff.mp hc).1
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]
    exact hc

theorem exists_agree_of_mem_live {cache : Array Clause} :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      ∀ {e}, e ∈ live → ∃ p ∈ ids, LiveAgree cache e p
  | [], [], .nil, _, he => absurd he List.not_mem_nil
  | _ :: _, q :: _, .cons hrel rest, _, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨q, List.mem_cons_self, hrel⟩
    · obtain ⟨p, hp, hrel'⟩ := exists_agree_of_mem_live rest he
      exact ⟨p, List.mem_cons_of_mem _ hp, hrel'⟩

theorem exists_agree_of_mem_ids {cache : Array Clause} :
    ∀ {live : List (ℕ × Clause)} {ids : List (ℕ × ℕ)}, List.Forall₂ (LiveAgree cache) live ids →
      ∀ {p}, p ∈ ids → ∃ e ∈ live, LiveAgree cache e p
  | [], [], .nil, _, hp => absurd hp List.not_mem_nil
  | e :: _, _ :: _, .cons hrel rest, _, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨e, List.mem_cons_self, hrel⟩
    · obtain ⟨e', he', hrel'⟩ := exists_agree_of_mem_ids rest hp
      exact ⟨e', List.mem_cons_of_mem _ he', hrel'⟩

/-! ## The action checker, one action at a time -/

/-- Replay nodes of the action checker's graph from a cache. -/
def replayActions (F : CNF) (cache : Array Clause) (nodes : List (Node Clause ActionCode ℕ)) : Option (Array Clause) :=
  replayFrom (interface F) cache nodes

theorem replayActions_append (F : CNF) (cache : Array Clause) (xs ys : List (Node Clause ActionCode ℕ)) :
    replayActions F cache (xs ++ ys) = (replayActions F cache xs).bind fun middle => replayActions F middle ys :=
  replayFrom_append_eq (interface F) cache xs ys

/-- **One action of the action checker**: compile it, then replay the nodes it added. -/
def actStep (F : CNF) (s : Retained × Array Clause) (a : Action) : Option (Retained × Array Clause) :=
  (compileStep s.1 a).bind fun R => (replayActions F s.2 (R.nodes.drop s.1.nodes.length)).map fun cache => (R, cache)

theorem compileStep_nodes {R R' : Retained} {a : Action} (h : compileStep R a = some R') :
    ∃ new, R'.nodes = R.nodes ++ new := by
  cases a with
  | rup id clause hints =>
    simp only [compileStep] at h
    split at h
    · cases h
    · cases hm : hints.mapM (lookupId R.live) with
      | none => simp [hm] at h
      | some parents =>
        simp only [hm, Option.some.injEq] at h
        exact ⟨_, by rw [← h]⟩
  | rat _ _ => simp [compileStep] at h
  | delete ids =>
    simp only [compileStep, Option.some.injEq] at h
    exact ⟨[], by rw [← h, List.append_nil]⟩

theorem foldlM_compileStep_nodes : ∀ {actions : List Action} {R R' : Retained},
    actions.foldlM compileStep R = some R' → ∃ new, R'.nodes = R.nodes ++ new
  | [], R, R', h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact ⟨[], by rw [h, List.append_nil]⟩
  | a :: actions, R, R', h => by
    simp only [List.foldlM_cons] at h
    cases hc : compileStep R a with
    | none => simp [hc] at h
    | some R₁ =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨new₁, h₁⟩ := compileStep_nodes hc
      obtain ⟨new₂, h₂⟩ := foldlM_compileStep_nodes h
      exact ⟨new₁ ++ new₂, by rw [h₂, h₁, List.append_assoc]⟩

/-- **Running the action checker one action at a time is compiling and then replaying.** -/
theorem foldlM_actStep_iff (F : CNF) : ∀ (actions : List Action) (R₀ : Retained) (cache₀ : Array Clause),
    replay (interface F) R₀.nodes = some cache₀ → ∀ R cache,
      (actions.foldlM (actStep F) (R₀, cache₀) = some (R, cache) ↔
        actions.foldlM compileStep R₀ = some R ∧ replay (interface F) R.nodes = some cache)
  | [], R₀, cache₀, h₀, R, cache => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, h₀⟩
    · rintro ⟨rfl, h⟩
      rw [h₀] at h
      exact ⟨rfl, Option.some.inj h⟩
  | a :: actions, R₀, cache₀, h₀, R, cache => by
    simp only [List.foldlM_cons, Option.bind_eq_bind]
    unfold actStep
    cases hc : compileStep R₀ a with
    | none => simp
    | some R₁ =>
      obtain ⟨new, hnew⟩ := compileStep_nodes hc
      have hd : R₁.nodes.drop R₀.nodes.length = new := by rw [hnew, List.drop_left]
      have h₀' : replayActions F #[] R₀.nodes = some cache₀ := h₀
      simp only [Option.bind_some]
      rw [hd]
      cases hr : replayActions F cache₀ new with
      | none =>
        simp only [Option.map_none, Option.bind_none, reduceCtorEq, false_iff, not_and]
        intro hfold hreplay
        obtain ⟨more, hmore⟩ := foldlM_compileStep_nodes hfold
        have hreplay' : replayActions F #[] R.nodes = some cache := hreplay
        rw [hmore, hnew, List.append_assoc, replayActions_append, h₀', Option.bind_some, replayActions_append,
          hr] at hreplay'
        cases hreplay'
      | some cache₁ =>
        simp only [Option.map_some, Option.bind_some]
        have h₁ : replay (interface F) R₁.nodes = some cache₁ := by
          show replayActions F #[] R₁.nodes = some cache₁
          rw [hnew, replayActions_append, h₀', Option.bind_some]
          exact hr
        exact foldlM_actStep_iff F actions R₁ cache₁ h₁ R cache

/-! ## Lockstep -/

/-- **The two checkers agree**: the graph replays to the cache, and the live clauses are the live
identifiers with the clauses they name. -/
structure Agree (F : CNF) (live : List (ℕ × Clause)) (R : Retained) (cache : Array Clause) : Prop where
  replayed : replay (interface F) R.nodes = some cache
  agree : List.Forall₂ (LiveAgree cache) live R.live

theorem Agree.size {F : CNF} {live : List (ℕ × Clause)} {R : Retained} {cache : Array Clause}
    (h : Agree F live R cache) : cache.size = R.nodes.length := by
  have := replayFrom_size (interface F) h.replayed
  rw [Array.size_empty, Nat.zero_add] at this
  exact this

variable {A : Type u} [DecidableEq A]

/-- **One LRAT action in lockstep**: both checkers fail, or both succeed and still agree. -/
theorem certStep_actStep (P : Program A) {F : CNF} {live : List (ℕ × Clause)} {R : Retained}
    {cache : Array Clause} (h : Agree F live R cache) (a : Action) :
    (P.certStep live (.lrat a) = none ∧ actStep F (R, cache) a = none) ∨
      ∃ live' R' cache', P.certStep live (.lrat a) = some live' ∧ actStep F (R, cache) a = some (R', cache') ∧
        Agree F live' R' cache' := by
  cases a with
  | rup id clause hints =>
    have hid := isSome_lookupClause_agree h.agree id
    have hm := mapM_lookupClause_agree h.agree hints
    simp only [Program.certStep, actStep, compileStep, hid]
    by_cases taken : (lookupId R.live id).isSome = true
    · simp [taken]
    · simp only [taken, if_false, Bool.false_eq_true]
      rw [hm]
      cases hp : hints.mapM (lookupId R.live) with
      | none => simp
      | some parents =>
        simp only [Option.bind_some, List.drop_left']
        cases hpr : lookupPremises cache parents with
        | none =>
          left
          simp [replayActions, replayFrom, Node.replay, hpr]
        | some premises =>
          by_cases rup : rupCheck premises clause = true
          · right
            refine ⟨(id, clause) :: live, ⟨(id, R.nodes.length) :: R.live, R.nodes ++ [⟨clause, .rup, parents, id⟩]⟩,
              cache.push clause, by simp [rup], ?_, ?_⟩
            · simp [replayActions, replayFrom, Node.replay, hpr, interface, checkAction, rup]
            · refine ⟨?_, ?_⟩
              · show replayActions F #[] (R.nodes ++ [⟨clause, .rup, parents, id⟩]) = some (cache.push clause)
                have hr : replayActions F #[] R.nodes = some cache := h.replayed
                rw [replayActions_append, hr, Option.bind_some]
                simp [replayActions, replayFrom, Node.replay, hpr, interface, checkAction, rup]
              · refine .cons ⟨rfl, ?_⟩ (forall₂_push clause h.agree)
                simp [← h.size]
          · left
            simp [rup, replayActions, replayFrom, Node.replay, hpr, interface, checkAction]
  | rat _ _ => left; simp [Program.certStep, actStep, compileStep]
  | delete ids =>
    right
    refine ⟨live.filter fun e => !ids.contains e.1, ⟨R.live.filter fun entry => !ids.contains entry.1, R.nodes⟩,
      cache, rfl, by simp [actStep, compileStep, replayActions, replayFrom], h.replayed, ?_⟩
    exact forall₂_filter (fun i => !ids.contains i) h.agree

/-- **Streams of LRAT actions in lockstep.** -/
theorem foldlM_agree (P : Program A) {F : CNF} : ∀ (actions : List Action) {live : List (ℕ × Clause)}
    {R : Retained} {cache : Array Clause}, Agree F live R cache →
      ((actions.map CertStep.lrat).foldlM P.certStep live = none ∧ actions.foldlM (actStep F) (R, cache) = none) ∨
        ∃ live' R' cache', (actions.map CertStep.lrat).foldlM P.certStep live = some live' ∧
          actions.foldlM (actStep F) (R, cache) = some (R', cache') ∧ Agree F live' R' cache'
  | [], live, R, cache, h => Or.inr ⟨live, R, cache, rfl, rfl, h⟩
  | a :: actions, live, R, cache, h => by
    simp only [List.map_cons, List.foldlM_cons, Option.bind_eq_bind]
    rcases certStep_actStep P h a with ⟨h₁, h₂⟩ | ⟨live₁, R₁, cache₁, h₁, h₂, agree₁⟩
    · left
      simp [h₁, h₂]
    · simp only [h₁, h₂, Option.bind_some]
      exact foldlM_agree P actions agree₁

/-! ## The starting states -/

theorem replay_start (F : CNF) : replay (interface F) (start F).nodes = some F.toArray := by
  have prefixes : ∀ n, n ≤ F.length → replayFrom (interface F) #[]
      ((F.take n).mapIdx fun index clause => (⟨clause, .input index, [], index + 1⟩ : Node Clause (interface F).W ℕ)) =
        some (F.take n).toArray := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      have lt : n < F.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem lt, Option.toList_some, List.mapIdx_append,
        List.mapIdx_singleton, List.length_take, Nat.min_eq_left lt.le, Nat.zero_add]
      refine replayFrom_append (interface F) (ih (by omega)) ?_
      have node : (⟨F[n], .input n, [], n + 1⟩ : Node Clause (interface F).W ℕ).replay (interface F) (F.take n).toArray =
          some ((F.take n).toArray.push F[n]) :=
        (Node.replay_eq_some_iff _ _ _ _).mpr ⟨[], rfl, by simp [interface, checkAction], rfl⟩
      simp only [replayFrom, node]
      simp
  have := prefixes F.length le_rfl
  rw [List.take_length] at this
  exact this

theorem agree_numberFrom (F : CNF) : ∀ (G : List Clause) (k : ℕ), (∀ j c, G[j]? = some c → F.toArray[k + j]? = some c) →
    List.Forall₂ (LiveAgree F.toArray) (numberFrom (k + 1) G) ((List.range' k G.length).map fun i => (i + 1, i))
  | [], _, _ => .nil
  | c :: G, k, h => by
    refine .cons ⟨rfl, by simpa using h 0 c rfl⟩ ?_
    have := agree_numberFrom F G (k + 1) fun j c' hj => by
      have := h (j + 1) c' (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    exact this

/-- **The starting states agree**: the inputs are numbered `1, 2, …` on both sides. -/
theorem agree_start (F : CNF) : Agree F (numberFrom 1 F) (start F) F.toArray where
  replayed := replay_start F
  agree := by
    have := agree_numberFrom F F 0 fun j c hj => by simpa using hj
    simpa [start, List.range_eq_range'] using this

/-! ## Agreement -/

namespace Program

variable (P : Program A)

/-- **The certificate checker on a certificate of LRAT actions only** accepts exactly when the action
checker compiles and replays the stream and some live identifier names the empty clause. -/
theorem checkCert_lrat_iff (actions : List Action) :
    P.checkCert (actions.map CertStep.lrat) = true ↔
      ∃ R cache, compile P.completionLRAT actions = some R ∧ replay (interface P.completionLRAT) R.nodes = some cache ∧
        ∃ e ∈ R.live, cache[e.2]? = some [] := by
  have lockstep := foldlM_agree P actions (agree_start P.completionLRAT)
  unfold checkCert certRun inputs
  rcases lockstep with ⟨h₁, h₂⟩ | ⟨live, R, cache, h₁, h₂, agree⟩
  · rw [h₁]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro R cache compiled replayed _
    have := (foldlM_actStep_iff _ actions _ _ (replay_start _) R cache).mpr ⟨compiled, replayed⟩
    rw [h₂] at this
    cases this
  · rw [h₁]
    have both := (foldlM_actStep_iff _ actions _ _ (replay_start _) R cache).mp h₂
    simp only [List.any_eq_true, List.isEmpty_iff]
    constructor
    · rintro ⟨e, he, empty⟩
      obtain ⟨p, hp, -, hc⟩ := exists_agree_of_mem_live agree.agree he
      exact ⟨R, cache, both.1, both.2, p, hp, by rw [hc, empty]⟩
    · rintro ⟨R', cache', compiled, replayed, p, hp, hc⟩
      have compiled' : compile P.completionLRAT actions = some R := both.1
      rw [compiled'] at compiled
      cases Option.some.inj compiled
      rw [both.2] at replayed
      cases Option.some.inj replayed
      obtain ⟨e, he, -, he'⟩ := exists_agree_of_mem_ids agree.agree hp
      rw [he'] at hc
      exact ⟨e, he, Option.some.inj hc⟩

/-- **Acceptance by the certificate checker implies acceptance by the action checker.** -/
theorem check_of_checkCert_lrat {actions : List Action} (h : P.checkCert (actions.map CertStep.lrat) = true) :
    check P.completionLRAT actions = true := by
  obtain ⟨R, cache, compiled, replayed, p, -, hc⟩ := (P.checkCert_lrat_iff actions).mp h
  unfold check
  rw [compiled]
  simp only [replayed]
  exact decide_eq_true (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hc))

/-- An action stream without deletions. -/
def NoDelete (actions : List Action) : Prop := ∀ a ∈ actions, ∀ ids, a ≠ .delete ids

theorem compile_live_of_noDelete (F : CNF) : ∀ (actions : List Action) {R R' : Retained},
    (∀ a ∈ actions, ∀ ids, a ≠ .delete ids) → (∀ i < R.nodes.length, ∃ e ∈ R.live, e.2 = i) →
      actions.foldlM compileStep R = some R' → ∀ i < R'.nodes.length, ∃ e ∈ R'.live, e.2 = i
  | [], R, R', _, live, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    exact h ▸ live
  | a :: actions, R, R', noDelete, live, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases hc : compileStep R a with
    | none => simp [hc] at h
    | some R₁ =>
      simp only [hc, Option.bind_some] at h
      refine compile_live_of_noDelete F actions (fun b hb => noDelete b (List.mem_cons_of_mem _ hb)) ?_ h
      cases a with
      | rup id clause hints =>
        simp only [compileStep] at hc
        split at hc
        · cases hc
        · cases hm : hints.mapM (lookupId R.live) with
          | none => simp [hm] at hc
          | some parents =>
            simp only [hm, Option.some.injEq] at hc
            subst hc
            intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            by_cases last : i = R.nodes.length
            · exact ⟨_, List.mem_cons_self, last.symm⟩
            · obtain ⟨e, he, same⟩ := live i (by omega)
              exact ⟨e, List.mem_cons_of_mem _ he, same⟩
      | rat _ _ => simp [compileStep] at hc
      | delete ids => exact absurd rfl (noDelete _ List.mem_cons_self ids)

/-- **Without deletions the two checkers accept the same certificates of LRAT actions only.** -/
theorem checkCert_lrat_iff_check {actions : List Action} (noDelete : NoDelete actions) :
    P.checkCert (actions.map CertStep.lrat) = true ↔ check P.completionLRAT actions = true := by
  refine ⟨P.check_of_checkCert_lrat, fun h => ?_⟩
  obtain ⟨R, cache, compiled, replayed, member⟩ := check_graph h
  rw [P.checkCert_lrat_iff]
  refine ⟨R, cache, compiled, replayed, ?_⟩
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem member
  have size₀ := replayFrom_size (interface P.completionLRAT) replayed
  simp only [Array.size_empty, Nat.zero_add] at size₀
  have size : cache.size = R.nodes.length := size₀
  have startLive : ∀ i < (start P.completionLRAT).nodes.length, ∃ e ∈ (start P.completionLRAT).live, e.2 = i := by
    intro i hi
    simp only [start, List.length_mapIdx] at hi
    exact ⟨(i + 1, i), by simp [start, hi], rfl⟩
  obtain ⟨e, he, same⟩ := compile_live_of_noDelete P.completionLRAT actions noDelete startLive compiled i
    (by rw [← size]; simpa using hi)
  refine ⟨e, he, ?_⟩
  rw [same, Array.getElem?_eq_getElem (by simpa using hi)]
  simp only [Array.getElem_toList] at hget
  rw [← hget]

end Program

end Mettapedia.Logic.ASP
