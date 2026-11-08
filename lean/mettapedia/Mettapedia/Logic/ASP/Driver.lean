import Mettapedia.Logic.ASP.Propagation

/-!
# The reference driver

A deterministic, total answer set solver over the verified transition system,
runnable with `#eval`, against which a C solver can be tested answer by answer
and certificate by certificate.

## The driver

* **State** (`DState`): the trail, the watched nogoods with their watch lists and
  pending literals, the learned nogoods, the short nogoods, the source pointers,
  and the certificate emitted so far (`Book`). The solver state it stands for is
  `DState.spec`.
* **One iteration** (`Program.iterate`): propagate with `Program.propagateAll`;
  then
  - at a closed state with every variable assigned, report the true atoms;
  - at a closed state with an unassigned variable, decide the unassigned variable
    with the lowest number false (atoms come before bodies in the numbering);
  - at a conflict, `Program.resolveConflict`: at level 0, emit the empty clause and
    report `unsat`; if the conflict has a literal at the current level, run
    first-UIP analysis, backjump to the assertion level emitting the learned
    nogood by a RUP step, then learn it and watch it; otherwise (a stale conflict)
    backjump below the newest decision with the nogood of the decisions as
    reason, also emitted by a RUP step.
  After a backjump the kept trail is re-queued for the watches.
* **The run** repeats iterations. Every iteration raises the solver's termination
  measure (`Program.measure`), which is bounded (`Program.measureBound`).
  - `Program.solveWF` terminates by well-founded recursion on that measure, with
    no fuel.
  - `Program.solve` runs on fuel one more than the bound, never runs out
    (`Program.solve_ne_outOfFuel`), and is the same function
    (`Program.solve_eq_solveWF`). It is kept because the kernel can evaluate it,
    so controls can be decided.

## Results

* `Program.iterate_spec`: an iteration from a ready state is a run of the solver
  with emission (`Program.Emit`) and of the discipline (`Program.CDNL`), and
  either reaches a ready state with a larger measure or finishes.
* **Soundness** (`Program.solve_sat_stable`, `Program.solve_sat_isStable`): a
  returned model is stable, and the reduct checker accepts it.
* **Refutation** (`Program.solve_unsat_accepted`): `unsat` comes with a
  certificate the certificate checker accepts, so the program has no stable
  model (`Program.solve_unsat_no_stable`).
* **The run is an emitting run** (`Program.solve_emits`): the final configuration
  and book are reached by `Program.Emit`, and the configuration by
  `Program.CDNL`; every state the driver passes through satisfies `Program.Good`,
  whose first two fields say the same of it.
* **Completeness** (`Program.solve_sat_iff`): the driver returns a model exactly
  when the program has a stable model.

## Emission progress

* `Program.stale_emit`: at any conflict above level 0, including one with no
  literal at the current level, backjumping below the newest decision with the
  nogood of the decisions as reason is an emitting step and a step of the
  discipline.
* `Program.conflict_emit`: every reachable emitting state with a falsified named
  database nogood has an emitting solver step.
* `Program.emit_progress`: every reachable emitting running state has an
  emitting solver step, after at most one loop step that names a falsified loop
  nogood.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Relation

universe u

variable {A : Type u}

section Driver

variable [DecidableEq A]

/-! ## Operations on driver states -/

/-- Learn a nogood: watch it on its first two distinct literals, or scan it if it has none. -/
def DState.learn (st : DState A) (ε : Nogood A) : DState A :=
  match twoWatches ε.lits with
  | some p => { st with ws := st.ws.addWatched ⟨ε, p.1, p.2⟩, learned := ε :: st.learned }
  | none => { st with learned := ε :: st.learned, short := st.short ++ [ε] }

/-- Replace the trail by `t`, re-queue all of it for the watches, and take the book `b`. -/
def DState.requeue (st : DState A) (t : List (Entry A)) (b : Book A) : DState A :=
  { st with ws := { st.ws with trail := t, pending := t.map Entry.lit }, book := b }

/-- The outcome of one driver iteration. -/
inductive Iter (A : Type u)
  | next (st : DState A)
  | sat (model : List A)
  | unsat (book : Book A)
  | stuck

/-- What the driver answers. -/
inductive Answer (A : Type u)
  | sat (model : List A)
  | unsat (certificate : List CertStep)
  | outOfFuel

/-- The model of an answer, if it is one. -/
def Answer.model? {A : Type u} : Answer A → Option (List A)
  | .sat M => some M
  | _ => none

/-- The certificate of an answer, if it refutes. -/
def Answer.certificate? {A : Type u} : Answer A → Option (List CertStep)
  | .unsat cert => some cert
  | _ => none

namespace Program

variable (P : Program A)

/-- **Resolve a conflict** on the falsified nogood `δ`. -/
def resolveConflict (st : DState A) (δ : Nogood A) : Iter A :=
  if levelOf st.ws.trail = 0 then .unsat (P.emitRup st.book [] (refutationHints st.spec δ))
  else if δ.lits.any (fun m => decide (m ∈ (currentLevel st.ws.trail).map Entry.lit)) then
    match (firstUIP st.spec δ).find? (fun m => decide (m ∈ (currentLevel st.ws.trail).map Entry.lit)) with
    | none => .stuck
    | some u =>
      .next ((st.learn ⟨firstUIP st.spec δ, .learned st.book.next⟩).requeue
        (⟨u.compl, assertionLevel st.ws.trail (firstUIP st.spec δ) u,
            some ⟨firstUIP st.spec δ, .learned st.book.next⟩⟩ ::
          cutTo (assertionLevel st.ws.trail (firstUIP st.spec δ) u) st.ws.trail)
        (P.emitRup st.book (firstUIP st.spec δ) (firstUIPHints st.spec δ)))
  else
    match (currentLevel st.ws.trail).getLast? with
    | none => .stuck
    | some d =>
      .next (st.requeue
        (⟨d.lit.compl, levelOf (belowLevel st.ws.trail), some ⟨decisionLits st.ws.trail, .learned st.book.next⟩⟩ ::
          belowLevel st.ws.trail)
        (P.emitRup st.book (decisionLits st.ws.trail) (refutationHints st.spec δ)))

/-- **One driver iteration.** -/
def iterate (st : DState A) : Iter A :=
  match P.propagateAll (P.varList.length + 1) st with
  | .outOfFuel => .stuck
  | .conflict δ st' => P.resolveConflict st' δ
  | .closed st' =>
    match P.varList.find? (fun x => !st'.ws.trail.any fun e => e.lit.var == x) with
    | none => .sat (P.allAtoms.filter fun a => decide (tAtom a ∈ st'.ws.lits))
    | some x => .next { st' with ws := st'.ws.decide ⟨x, false⟩ }

/-- **The driver run**, at most `n` iterations. -/
def runFuel : ℕ → DState A → Answer A
  | 0, _ => .outOfFuel
  | n + 1, st =>
    match P.iterate st with
    | .next st' => runFuel n st'
    | .sat M => .sat M
    | .unsat b => .unsat b.steps
    | .stuck => .outOfFuel

/-- The starting state: nothing assigned, the completion watched or scanned, its nogoods named
`1, 2, …`. -/
def initState : DState A :=
  ⟨WState.init P.completionNogoods [], [], P.completionNogoods.filter (fun δ => (twoWatches δ.lits).isNone), [],
    P.initialBook⟩

/-- One more than the bound of the solver's termination measure. -/
def fuelBound : ℕ := P.measureBound + 1

/-- **The reference driver.** -/
def solve : Answer A := P.runFuel P.fuelBound P.initState

/-! ## Emission progress -/

omit [DecidableEq A] in
theorem decisionLits_split {t newer older : List (Entry A)} {d : Entry A}
    (split : t = newer ++ d :: older) (propagated : ∀ e ∈ newer, e.reason ≠ none) (decision : d.reason = none) :
    decisionLits t = d.lit :: decisionLits older := by
  have newerFree : newer.filter (fun e => e.reason.isNone) = [] :=
    List.filter_eq_nil_iff.mpr fun e he => by simpa using propagated e he
  rw [decisionLits, split, List.filter_append, newerFree, List.nil_append, List.filter_cons_of_pos
    (by simp [decision]), List.map_cons]
  rfl

omit [DecidableEq A] in
/-- Above level 0 the trail splits at its newest decision. -/
theorem newest_split {t : List (Entry A)} {newer : List (Entry A)} {d : Entry A}
    (h : currentLevel t = newer ++ [d]) : t = newer ++ d :: belowLevel t ∧ ∀ e ∈ newer, e.reason ≠ none := by
  constructor
  · have whole := currentLevel_append_belowLevel t
    rw [h, List.append_assoc, List.singleton_append] at whole
    exact whole.symm
  · intro e he
    apply currentLevel_dropLast t e
    rw [h, List.dropLast_concat]
    exact he

/-- **Emission at stale conflicts.** At any conflict above level 0, including one with no literal at
the current level, backjumping below the newest decision with the nogood of the decisions as
reason is a solver step, a step of the discipline, and an emitting step that adds that nogood by a
RUP step whose hints are the trail's reasons, oldest first, and the conflict. -/
theorem stale_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {δ : Nogood A}
    (database : P.InDatabase s δ) (named : Named b δ.lits) (falsified : s.Falsifies δ)
    {newer : List (Entry A)} {d : Entry A} (hcur : currentLevel s.trail = newer ++ [d]) (decision : d.reason = none) :
    P.Step (.running s) (.running ⟨⟨d.lit.compl, levelOf (belowLevel s.trail),
        some ⟨decisionLits s.trail, .learned b.next⟩⟩ :: belowLevel s.trail, s.learned, s.restartMark⟩) ∧
      P.CDNL (.running s) (.running ⟨⟨d.lit.compl, levelOf (belowLevel s.trail),
        some ⟨decisionLits s.trail, .learned b.next⟩⟩ :: belowLevel s.trail, s.learned, s.restartMark⟩) ∧
      P.Emit (.running s, b) (.running ⟨⟨d.lit.compl, levelOf (belowLevel s.trail),
        some ⟨decisionLits s.trail, .learned b.next⟩⟩ :: belowLevel s.trail, s.learned, s.restartMark⟩,
          P.emitRup b (decisionLits s.trail) (refutationHints s δ)) := by
  have reachable := P.emitReachable_reachable reach
  have inv := P.reachable_inv reachable
  have just := P.reachable_justified reachable
  have covered := (P.emitReachable_inv reach).2 s rfl
  obtain ⟨split, propagated⟩ := newest_split hcur
  have lits := decisionLits_split split propagated decision
  have entailed := P.decisions_entailed inv database falsified
  have member : d.lit ∈ decisionLits s.trail := by rw [lits]; exact List.mem_cons_self
  have rest : ∀ m ∈ decisionLits s.trail, m ≠ d.lit → m ∈ (belowLevel s.trail).map Entry.lit := by
    intro m hm ne
    rw [lits] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact absurd rfl ne
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      exact List.mem_map_of_mem (List.mem_filter.mp he).1
  have outside : ∀ e ∈ belowLevel s.trail, e.lit.var ≠ d.lit.var := (nodup_split inv.nodup split).2
  have isVar : P.IsVar d.lit.var := inv.vars d (by rw [split]; exact List.mem_append_right _ List.mem_cons_self)
  have step := Step.backjump (P := P) (ε := ⟨decisionLits s.trail, .learned b.next⟩) (l := d.lit) database falsified
    split decision entailed member rest outside isVar
  refine ⟨step, CDNL.backjump database falsified split decision entailed member rest outside isVar, ?_⟩
  refine Emit.backjump step (newer := newer ++ [d]) (by rw [List.append_assoc, List.singleton_append]; exact split) ?_
    (P.decisions_rupCheck inv just falsified)
  intro ρ hρ
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨e, he, hreason⟩ := trailReasons_mem (List.mem_reverse.mp hρ)
    exact covered.1 e he ρ hreason
  · rw [List.mem_singleton] at hρ
    exact hρ ▸ named

/-- **Every reachable emitting state with a falsified, named database nogood has an emitting solver
step**: the refutation at level 0, and a backjump above it. -/
theorem conflict_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {δ : Nogood A}
    (database : P.InDatabase s δ) (named : Named b δ.lits) (falsified : s.Falsifies δ) :
    ∃ c' b', P.Emit (.running s, b) (c', b') ∧ P.Step (.running s) c' := by
  by_cases ground : levelOf s.trail = 0
  · exact ⟨_, _, P.refutation_emit reach database named falsified ground, .fail database falsified ground⟩
  · obtain ⟨newer, d, hcur, decision⟩ := currentLevel_split ground
    obtain ⟨step, -, emit⟩ := P.stale_emit reach database named falsified hcur decision
    exact ⟨_, _, emit, step⟩

/-- A loop nogood has the literals of the loop nogood of its set's program atoms. -/
theorem loopNogood_lits_filter (U : Finset A) (a : A) :
    (P.loopNogood (U.filter fun x => x ∈ P.allAtoms) a).lits = (P.loopNogood U a).lits := by
  suffices same : P.filter (fun r => decide (ExternalFor (U.filter fun x => x ∈ P.allAtoms) r)) =
      P.filter (fun r => decide (ExternalFor U r)) by
    simp only [loopNogood, externalBodies, same]
  apply List.filter_congr
  intro r hr
  have head : r.head ∈ P.allAtoms := (P.mem_allAtoms).mpr ⟨r, hr, Or.inl rfl⟩
  have pos : ∀ b ∈ r.pos, b ∈ P.allAtoms := fun b hb => (P.mem_allAtoms).mpr ⟨r, hr, Or.inr (Or.inl hb)⟩
  rw [decide_eq_decide]
  unfold ExternalFor
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hU, -⟩, out⟩
    exact ⟨hU, fun b hb inU => out b hb ⟨inU, pos b hb⟩⟩
  · rintro ⟨hU, out⟩
    exact ⟨⟨hU, head⟩, fun b hb inU => out b hb inU.1⟩

/-- A falsified loop nogood can be named by one loop step. -/
theorem loop_nameable {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {U : Finset A} {a : A}
    (noFalsum : ∀ x ∈ U, ¬ P.Falsum x) (ha : a ∈ U) (falsified : s.Falsifies (P.loopNogood U a)) :
    ∃ b₁, P.Emit (.running s, b) (.running s, b₁) ∧ Named b₁ (P.loopNogood U a).lits := by
  classical
  have inv := P.reachable_inv (P.emitReachable_reachable reach)
  have aProgram : a ∈ P.allAtoms := by
    have := P.mem_lits_isVar inv (falsified _ List.mem_cons_self)
    exact (P.mem_allAtoms).mpr this
  set U' := U.filter fun x => x ∈ P.allAtoms with hU'
  have member : a ∈ U'.toList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨ha, aProgram⟩)
  have vars : ∀ x ∈ U'.toList, P.IsVar (.atom x) := fun x hx =>
    (P.mem_allAtoms).mp (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).2
  have noFalsum' : ∀ x ∈ U'.toList, ¬ P.Falsum x := fun x hx =>
    noFalsum x (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).1
  refine ⟨P.emitLoop b U'.toList a, Emit.loop member vars noFalsum', ?_⟩
  have named := named_self b (P.loopNogood U'.toList.toFinset a).lits b.next
    (b.steps ++ [.loop b.next (P.lratClause (P.loopNogood U'.toList.toFinset a).lits) (P.atomNumbers U'.toList)
      (P.index (.atom a))])
    ((b.next, P.lratClause (P.loopNogood U'.toList.toFinset a).lits) :: b.live) (b.next + 1)
  rw [Finset.toList_toFinset, hU', P.loopNogood_lits_filter] at named
  unfold emitLoop
  rw [Finset.toList_toFinset, hU', P.loopNogood_lits_filter]
  exact named

/-- **Progress of emission.** Every reachable emitting running state has an emitting solver step,
after at most one loop step that names a falsified loop nogood. -/
theorem emit_progress {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) :
    ∃ b₁ c' b', ReflTransGen P.Emit (.running s, b) (.running s, b₁) ∧ P.Emit (.running s, b₁) (c', b') ∧
      P.Step (.running s) c' := by
  classical
  have inv := P.reachable_inv (P.emitReachable_reachable reach)
  have covered := (P.emitReachable_inv reach).2 s rfl
  by_cases conflict : ∃ δ, P.InDatabase s δ ∧ s.Falsifies δ
  · obtain ⟨δ, database, falsified⟩ := conflict
    have nameable : ∃ b₁, ReflTransGen P.Emit (.running s, b) (.running s, b₁) ∧ Named b₁ δ.lits := by
      rcases database with completion | learned | ⟨U, noFalsum, a, ha, rfl⟩
      · exact ⟨b, .refl, (P.emitReachable_inv reach).1.completion δ completion⟩
      · exact ⟨b, .refl, covered.2 δ learned⟩
      · obtain ⟨b₁, step, named⟩ := P.loop_nameable reach noFalsum ha falsified
        exact ⟨b₁, .single step, named⟩
    obtain ⟨b₁, run, named⟩ := nameable
    obtain ⟨c', b', emit, step⟩ := P.conflict_emit (reach.trans run) database named falsified
    exact ⟨b₁, c', b', run, emit, step⟩
  · push Not at conflict
    by_cases total : ∀ x, P.IsVar x → s.Assigned x
    · have step : P.Step (.running s) (.done (.sat (P.trailModel s))) :=
        .succeed total (fun δ h => conflict δ (Or.inl h)) fun U noFalsum a ha =>
          conflict _ (Or.inr (Or.inr ⟨U, noFalsum, a, ha, rfl⟩))
      exact ⟨b, _, b, .refl, .quiet step (by simp) (fun s' h => by cases h), step⟩
    · push Not at total
      obtain ⟨x, isVar, unassigned⟩ := total
      exact ⟨b, _, b, .refl, P.decide_emit reach (l := ⟨x, true⟩) isVar unassigned, .decide isVar unassigned⟩

/-! ## The driver is correct -/

/-- A driver state ready for an iteration. -/
structure Ready (st : DState A) : Prop where
  good : P.Good st
  winv : WInv (st.ws.db.map Watched.nogood) st.ws
  nodup : st.ws.pending.Nodup

/-- What an iteration establishes, relative to the state it started from. -/
def IterOK (st₀ : DState A) : Iter A → Prop
  | .next st => P.Ready st ∧ P.measure st₀.spec < P.measure st.spec
  | .sat M => (∃ b, P.EmitReachable (.done (.sat M.toFinset)) b) ∧ P.CDNLReachable (.done (.sat M.toFinset))
  | .unsat b => P.EmitReachable (.done .unsat) b ∧ P.CDNLReachable (.done .unsat)
  | .stuck => False

variable {P}

theorem IterOK.mono {st₀ st : DState A} {r : Iter A} (h : P.IterOK st r)
    (le : P.measure st₀.spec ≤ P.measure st.spec) : P.IterOK st₀ r := by
  cases r with
  | next st' => exact ⟨h.1, lt_of_le_of_lt le h.2⟩
  | sat M => exact h
  | unsat b => exact h
  | stuck => exact h

variable (P)

omit [DecidableEq A] in
theorem trailValue_append_ge (n : ℕ) (t : List (Entry A)) :
    ∀ new : List (Entry A), trailValue n t ≤ trailValue n (new ++ t)
  | [] => le_rfl
  | e :: new => (trailValue_append_ge n t new).trans (trailValue_cons_lt n e (new ++ t)).le

/-- Extending the trail does not lower the measure. -/
theorem measure_extend {t : List (Entry A)} {L : List (Nogood A)} (new : List (Entry A)) :
    P.measure ⟨t, L, 0⟩ ≤ P.measure ⟨new ++ t, L, 0⟩ := by
  unfold measure
  have := trailValue_append_ge P.varFinset.card t new
  simp only
  omega

omit [DecidableEq A] in
theorem nodup_lits {t : List (Entry A)} (h : (t.map fun e => e.lit.var).Nodup) : (t.map Entry.lit).Nodup :=
  nodup_lits_of_prefix (t := []) (by simpa using h)

/-- **The unique implication point is unique**: a literal of the analysed nogood at the current
level is the one first-UIP found. -/
theorem uip_unique {s : State A} (inv : P.Inv s) {r : List (Lit A)} {u₀ : Lit A}
    (others : ∀ m ∈ r, m ≠ u₀ → m ∈ (belowLevel s.trail).map Entry.lit) {u : Lit A} (hu : u ∈ r)
    (cur : u ∈ (currentLevel s.trail).map Entry.lit) : u = u₀ := by
  by_contra ne
  have below := others u hu ne
  have nodup := inv.nodup
  rw [← currentLevel_append_belowLevel s.trail, List.map_append] at nodup
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp cur
  obtain ⟨f, hf, same⟩ := List.mem_map.mp below
  exact (List.nodup_append.mp nodup).2.2 _ (List.mem_map_of_mem he) _ (List.mem_map_of_mem hf) (by rw [same])

theorem learn_spec (st : DState A) (ε : Nogood A) (t : List (Entry A)) (b : Book A) :
    ((st.learn ε).requeue t b).spec = ⟨t, ε :: st.learned, 0⟩ := by
  unfold DState.learn
  split <;> rfl

/-- **Learning and re-queueing keep the driver ready.** -/
theorem ready_learn {st : DState A} (good : P.Good st) (shape : WShape (st.ws.db.map Watched.nogood) st.ws)
    {ε : Nogood A} {t : List (Entry A)} {b : Book A}
    (emit : P.EmitReachable (.running ⟨t, ε :: st.learned, 0⟩) b)
    (cdnl : P.CDNLReachable (.running ⟨t, ε :: st.learned, 0⟩)) : P.Ready ((st.learn ε).requeue t b) := by
  have inv := P.reachable_inv (P.emitReachable_reachable emit)
  have widen : ∀ δ, δ ∈ P.completionNogoods ∨ δ ∈ st.learned → δ ∈ P.completionNogoods ∨ δ ∈ ε :: st.learned :=
    fun δ h => h.imp id (List.mem_cons_of_mem _)
  unfold DState.learn
  cases hw : twoWatches ε.lits with
  | some p =>
    have shape' := shape.addWatched ⟨ε, p.1, p.2⟩ (twoWatches_spec hw)
    refine ⟨⟨emit, cdnl, ?_, fun δ h => widen δ (good.shortIn δ h), good.shortSame, ?_⟩,
      (shape'.requeue t inv.nodup).self, nodup_lits inv.nodup⟩
    · intro δ h
      simp only [DState.requeue, WState.addWatched, List.map_append, List.map_singleton, List.mem_append,
        List.mem_singleton] at h
      rcases h with h | rfl
      · exact widen δ (good.dbIn δ h)
      · exact Or.inr List.mem_cons_self
    · intro δ h
      have old : δ ∈ P.completionNogoods ∨ δ ∈ st.learned → δ ∈ ((st.learn ε).requeue t b).ws.db.map
          Watched.nogood ∨ δ ∈ ((st.learn ε).requeue t b).short := by
        intro h'
        unfold DState.learn
        rw [hw]
        rcases good.cover δ h' with h' | h'
        · left
          simp only [DState.requeue, WState.addWatched, List.map_append, List.mem_append]
          exact Or.inl h'
        · exact Or.inr h'
      unfold DState.learn at old
      rw [hw] at old
      rcases h with h | h
      · exact old (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · left
          simp [DState.requeue, WState.addWatched]
        · exact old (Or.inr h)
  | none =>
    refine ⟨⟨emit, cdnl, fun δ h => widen δ (good.dbIn δ h), ?_, ?_, ?_⟩, (shape.requeue t inv.nodup).self,
      nodup_lits inv.nodup⟩
    · intro δ h
      simp only [DState.requeue, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact widen δ (good.shortIn δ h)
      · exact Or.inr List.mem_cons_self
    · intro δ h
      simp only [DState.requeue, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact good.shortSame δ h
      · exact twoWatches_none hw
    · intro δ h
      have old : δ ∈ P.completionNogoods ∨ δ ∈ st.learned → δ ∈ st.ws.db.map Watched.nogood ∨
          δ ∈ st.short ++ [ε] := by
        intro h'
        rcases good.cover δ h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (List.mem_append_left _ h')
      rcases h with h | h
      · exact old (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        · exact old (Or.inr h)

/-- **Re-queueing keeps the driver ready.** -/
theorem ready_requeue {st : DState A} (good : P.Good st) (shape : WShape (st.ws.db.map Watched.nogood) st.ws)
    {t : List (Entry A)} {b : Book A} (emit : P.EmitReachable (.running ⟨t, st.learned, 0⟩) b)
    (cdnl : P.CDNLReachable (.running ⟨t, st.learned, 0⟩)) : P.Ready (st.requeue t b) := by
  have inv := P.reachable_inv (P.emitReachable_reachable emit)
  exact ⟨⟨emit, cdnl, good.dbIn, good.shortIn, good.shortSame, good.cover⟩, (shape.requeue t inv.nodup).self,
    nodup_lits inv.nodup⟩

/-- **Conflict resolution is correct**: from a good state with a falsified, named database nogood,
it emits the refutation at level 0, and otherwise backjumps (and learns, after first-UIP) by
emitting steps of the discipline to a ready state with a larger measure. -/
theorem resolveConflict_spec {st : DState A} (good : P.Good st) (shape : WShape (st.ws.db.map Watched.nogood) st.ws)
    {δ : Nogood A} (database : P.InDatabase st.spec δ) (named : Named st.book δ.lits)
    (falsified : st.spec.Falsifies δ) : P.IterOK st (P.resolveConflict st δ) := by
  have inv := good.inv
  have just := P.reachable_justified (P.emitReachable_reachable good.emit)
  have covered := (P.emitReachable_inv good.emit).2 _ rfl
  unfold resolveConflict
  by_cases ground : levelOf st.ws.trail = 0
  · rw [if_pos ground]
    exact ⟨good.emit.tail (P.refutation_emit good.emit database named falsified ground),
      good.cdnl.tail (CDNL.fail database falsified ground)⟩
  · rw [if_neg ground]
    by_cases current : ∃ m ∈ δ.lits, m ∈ (currentLevel st.ws.trail).map Entry.lit
    · have anyTrue : δ.lits.any (fun m => decide (m ∈ (currentLevel st.ws.trail).map Entry.lit)) = true := by
        simpa using current
      rw [if_pos anyTrue]
      obtain ⟨-, u₀, hu₀, cur₀, others⟩ := firstUIP_uip just falsified current
      cases hfind : (firstUIP st.spec δ).find? (fun m => decide (m ∈ (currentLevel st.ws.trail).map Entry.lit)) with
      | none =>
        have := List.find?_eq_none.mp hfind u₀ hu₀
        simp only [decide_eq_true_eq] at this
        exact absurd cur₀ this
      | some u =>
        dsimp only
        have hu : u ∈ firstUIP st.spec δ := List.mem_of_find?_eq_some hfind
        have cur : u ∈ (currentLevel st.ws.trail).map Entry.lit := by simpa using List.find?_some hfind
        have same := P.uip_unique inv others hu cur
        obtain ⟨u', hu', cur', below, cutLevel, unit, step⟩ :=
          P.firstUIP_backjump inv just database falsified ground current (.learned st.book.next)
        have same' := P.uip_unique inv others hu' cur'
        have uu : u' = u := same'.trans same.symm
        subst uu
        have ht : st.spec.trail = st.ws.trail := rfl
        rw [ht] at below cutLevel unit step
        set r := firstUIP st.spec δ with hr
        set j := assertionLevel st.ws.trail r u' with hj
        set ε : Nogood A := ⟨r, .learned st.book.next⟩ with hε
        obtain ⟨pre, split⟩ := cutTo_suffix j st.ws.trail
        have emitStep := Emit.backjump (P := P) (s := st.spec) (b := st.book) (ε := ε) (hints := firstUIPHints st.spec δ)
          (l := u') (newer := pre) (older := cutTo j st.ws.trail)
          (by rw [cutLevel]; exact step) split (firstUIPHints_named covered named) (P.firstUIP_rupCheck inv just falsified)
        rw [cutLevel] at emitStep
        have emit₁ := good.emit.tail emitStep
        have isVar : P.IsVar u'.var := by
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp cur
          exact inv.vars g (by
            show g ∈ st.ws.trail
            rw [← currentLevel_append_belowLevel st.ws.trail]
            exact List.mem_append_left _ hg)
        obtain ⟨preCut, d, cutSplit, decision⟩ := cutTo_split below
        have cdnlBack := CDNL.backjump (P := P) (s := st.spec) (ε := ε) (l := u') database falsified cutSplit decision
          (P.firstUIP_entailed inv database) unit.1 unit.2.1 (fun e he same => unit.2.2 ⟨e, he, same⟩) isVar
        rw [cutLevel] at cdnlBack
        have exhaustive := P.cdnlReachable_exhaustive good.cdnl
        have cdnlLearn := CDNL.learn (P := P) (s := ⟨⟨u'.compl, j, some ε⟩ :: cutTo j st.ws.trail, st.learned, 0⟩)
          (P.firstUIP_entailed inv database) (P.firstUIP_vars inv just falsified)
          (P.firstUIP_fresh inv just exhaustive falsified ground current)
          (firstUIP_learnable P inv hu' (.learned st.book.next) unit)
        have covered₁ := (P.emitReachable_inv emit₁).2 _ rfl
        have emit₂ := emit₁.tail (Emit.quiet (CDNL.step P cdnlLearn) (by simp) (by
          rintro s' ⟨⟩
          refine ⟨covered₁.1, ?_⟩
          rintro η (_ | ⟨_, hη⟩)
          · exact covered₁.1 _ List.mem_cons_self _ rfl
          · exact covered₁.2 η hη))
        have cdnl₂ := (good.cdnl.tail cdnlBack).tail cdnlLearn
        have inv₁ := P.reachable_inv (P.emitReachable_reachable emit₁)
        have lt₁ := P.measure_lt (CDNL.step P cdnlBack) inv
        have lt₂ := P.measure_lt (CDNL.step P cdnlLearn) inv₁
        refine ⟨P.ready_learn good shape emit₂ cdnl₂, ?_⟩
        rw [learn_spec]
        exact lt_trans lt₁ lt₂
    · have anyFalse : ¬ δ.lits.any (fun m => decide (m ∈ (currentLevel st.ws.trail).map Entry.lit)) = true := by
        simpa using current
      rw [if_neg anyFalse]
      obtain ⟨newer, d, hcur, decision⟩ := currentLevel_split ground
      have last : (currentLevel st.ws.trail).getLast? = some d := by
        rw [hcur, List.getLast?_concat]
      rw [last]
      dsimp only
      obtain ⟨step, cdnlStep, emitStep⟩ := P.stale_emit good.emit database named falsified hcur decision
      refine ⟨P.ready_requeue good shape (good.emit.tail emitStep) (good.cdnl.tail cdnlStep), ?_⟩
      exact P.measure_lt step inv

/-- **One iteration is correct.** -/
theorem iterate_spec {st : DState A} (ready : P.Ready st) : P.IterOK st (P.iterate st) := by
  have prop := P.propagateAll_spec (P.varList.length + 1) st ready.good ready.winv ready.nodup (by omega)
  unfold iterate
  cases hp : P.propagateAll (P.varList.length + 1) st with
  | outOfFuel =>
    rw [hp] at prop
    exact prop
  | conflict δ st' =>
    rw [hp] at prop
    obtain ⟨good', shape', learned, ⟨new, htrail⟩, database, named, falsified⟩ := prop
    dsimp only
    refine (P.resolveConflict_spec good' shape' database named falsified).mono ?_
    show P.measure ⟨st.ws.trail, st.learned, 0⟩ ≤ P.measure ⟨st'.ws.trail, st'.learned, 0⟩
    rw [htrail, learned]
    exact P.measure_extend new
  | closed st' =>
    rw [hp] at prop
    obtain ⟨good', winv', empty, learned, ⟨new, htrail⟩, propagated⟩ := prop
    have mono : P.measure st.spec ≤ P.measure st'.spec := by
      show P.measure ⟨st.ws.trail, st.learned, 0⟩ ≤ P.measure ⟨st'.ws.trail, st'.learned, 0⟩
      rw [htrail, learned]
      exact P.measure_extend new
    have inv := good'.inv
    dsimp only
    cases hf : P.varList.find? (fun x => !st'.ws.trail.any fun e => e.lit.var == x) with
    | none =>
      have total : ∀ x, P.IsVar x → st'.spec.Assigned x := by
        intro x hx
        have := List.find?_eq_none.mp hf x ((P.mem_varList).mpr hx)
        simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true, beq_iff_eq] at this
        obtain ⟨e, he, hvar⟩ := this
        exact ⟨e, he, hvar⟩
      have completion : ∀ δ ∈ P.completionNogoods, ¬ st'.spec.Falsifies δ :=
        fun δ h => (propagated.1 δ (Or.inl h)).1
      have loops : ∀ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ st'.spec.Falsifies (P.loopNogood U a) :=
        fun U _ a ha => propagated.loops P inv.nodup inv.vars U ha
      have step : P.Step (.running st'.spec) (.done (.sat (P.trailModel st'.spec))) := .succeed total completion loops
      exact ⟨⟨st'.book, good'.emit.tail (.quiet step (by simp) fun s' h => by cases h)⟩,
        good'.cdnl.tail (CDNL.succeed total completion loops)⟩
    | some x =>
      dsimp only
      have hx : x ∈ P.varList := List.mem_of_find?_eq_some hf
      have unassignedB := List.find?_some hf
      have unassigned : ¬ st'.spec.Assigned x := by
        rintro ⟨e, he, hvar⟩
        simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at unassignedB
        exact unassignedB e he hvar
      have isVar : P.IsVar x := (P.mem_varList).mp hx
      have emitStep := P.decide_emit good'.emit (l := ⟨x, false⟩) isVar unassigned
      have cdnlStep : P.CDNL (.running st'.spec)
          (.running (st'.spec.push ⟨⟨x, false⟩, levelOf st'.spec.trail + 1, none⟩)) :=
        CDNL.decide (fun δ h => propagated.1 δ (Or.inr h)) isVar unassigned
      refine ⟨⟨⟨good'.emit.tail emitStep, good'.cdnl.tail cdnlStep, good'.dbIn, good'.shortIn, good'.shortSame,
        good'.cover⟩, winv'.decide empty unassigned, List.nodup_singleton _⟩, ?_⟩
      exact lt_of_le_of_lt mono (P.measure_lt (CDNL.step P cdnlStep) inv)

/-- What the driver answers, read as runs. -/
def AnswerOK : Answer A → Prop
  | .sat M => (∃ b, P.EmitReachable (.done (.sat M.toFinset)) b) ∧ P.CDNLReachable (.done (.sat M.toFinset))
  | .unsat cert => (∃ b : Book A, b.steps = cert ∧ P.EmitReachable (.done .unsat) b) ∧ P.CDNLReachable (.done .unsat)
  | .outOfFuel => False

/-- **The run is correct** while the fuel exceeds what the measure can still rise. -/
theorem runFuel_spec : ∀ (n : ℕ) (st : DState A), P.Ready st → P.measureBound - P.measure st.spec < n →
    P.AnswerOK (P.runFuel n st)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, st, ready, fuel => by
    have it := P.iterate_spec ready
    unfold runFuel
    cases hi : P.iterate st with
    | next st' =>
      rw [hi] at it
      obtain ⟨ready', lt⟩ := it
      have le := P.measure_le ready'.good.inv
      exact runFuel_spec n st' ready' (by omega)
    | sat M =>
      rw [hi] at it
      exact it
    | unsat b =>
      rw [hi] at it
      exact ⟨⟨b, rfl, it.1⟩, it.2⟩
    | stuck =>
      rw [hi] at it
      exact it.elim

/-- The starting state is ready. -/
theorem initState_ready : P.Ready P.initState := by
  have dbIn : ∀ δ ∈ (watchedOf P.completionNogoods).map Watched.nogood, δ ∈ P.completionNogoods := by
    intro δ h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    obtain ⟨δ', hδ', hmap⟩ := List.mem_filterMap.mp hw
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp hmap
    exact hδ'
  refine ⟨⟨.refl, .refl, fun δ h => Or.inl (dbIn δ h), ?_, ?_, ?_⟩, ?_, List.nodup_nil⟩
  · intro δ h
    exact Or.inl (List.mem_filter.mp h).1
  · intro δ h
    exact twoWatches_none (by simpa using (List.mem_filter.mp h).2)
  · rintro δ (h | h)
    · cases hw : twoWatches δ.lits with
      | some p =>
        left
        refine List.mem_map.mpr ⟨⟨δ, p.1, p.2⟩, List.mem_filterMap.mpr ⟨δ, h, by simp [hw]⟩, rfl⟩
      | none =>
        right
        exact List.mem_filter.mpr ⟨h, by simp [hw]⟩
    · cases h
  · exact (WInv.init P.completionNogoods (t := []) List.nodup_nil fun _ _ => ⟨List.not_mem_nil, List.not_mem_nil⟩).self

theorem measure_initState : P.measure P.initState.spec = 0 := by
  simp [measure, initState, DState.spec, WState.init, trailValue]

/-- **The driver's answer, read as runs**: a model is reached by an emitting run and a run of the
discipline, and `unsat` by an emitting run whose book holds the returned certificate. -/
theorem solve_ok : P.AnswerOK P.solve :=
  P.runFuel_spec _ _ P.initState_ready (by rw [measure_initState, fuelBound]; omega)

/-- **The fuel never runs out.** -/
theorem solve_ne_outOfFuel : P.solve ≠ .outOfFuel := by
  intro h
  have := P.solve_ok
  rw [h] at this
  exact this

/-- **The driver's run is a run of the solver with emission and of the discipline.** -/
theorem solve_emits :
    (∀ M, P.solve = .sat M → (∃ b, P.EmitReachable (.done (.sat M.toFinset)) b) ∧
        P.CDNLReachable (.done (.sat M.toFinset))) ∧
      ∀ cert, P.solve = .unsat cert → (∃ b : Book A, b.steps = cert ∧ P.EmitReachable (.done .unsat) b) ∧
        P.CDNLReachable (.done .unsat) := by
  constructor
  · intro M h
    have := P.solve_ok
    rw [h] at this
    exact this
  · intro cert h
    have := P.solve_ok
    rw [h] at this
    exact this

/-- **Soundness**: a returned model is a stable model. -/
theorem solve_sat_stable {M : List A} (h : P.solve = .sat M) : P.Stable ↑M.toFinset := by
  obtain ⟨⟨b, emit⟩, -⟩ := P.solve_emits.1 M h
  exact P.sat_sound (P.emitReachable_reachable emit)

/-- A returned model passes the reduct checker. -/
theorem solve_sat_isStable {M : List A} (h : P.solve = .sat M) : P.isStable M.toFinset = true :=
  (P.isStable_iff _).mpr (P.solve_sat_stable h)

/-- **Refutation**: `unsat` comes with a certificate the certificate checker accepts. -/
theorem solve_unsat_accepted {cert : List CertStep} (h : P.solve = .unsat cert) : P.checkCert cert = true := by
  obtain ⟨⟨b, rfl, emit⟩, -⟩ := P.solve_emits.2 cert h
  exact P.emitted_accepted emit

/-- After `unsat` there is no stable model, by the certificate alone. -/
theorem solve_unsat_no_stable {cert : List CertStep} (h : P.solve = .unsat cert) (S : Set A) : ¬ P.Stable S :=
  P.checkCert_sound (P.solve_unsat_accepted h) S

/-- **Completeness**: the driver returns a model exactly when the program has a stable model. -/
theorem solve_sat_iff : (∃ M, P.solve = .sat M) ↔ ∃ S, P.Stable S := by
  constructor
  · rintro ⟨M, h⟩
    exact ⟨_, P.solve_sat_stable h⟩
  · rintro ⟨S, stable⟩
    cases h : P.solve with
    | sat M => exact ⟨M, rfl⟩
    | unsat cert => exact absurd stable (P.solve_unsat_no_stable h S)
    | outOfFuel => exact absurd h P.solve_ne_outOfFuel

/-! ## Termination by the measure -/

theorem iterate_next {st st' : DState A} (ready : P.Ready st) (h : P.iterate st = .next st') :
    P.Ready st' ∧ P.measure st.spec < P.measure st'.spec := by
  have := P.iterate_spec ready
  rw [h] at this
  exact this

theorem iterate_not_stuck {st : DState A} (ready : P.Ready st) (h : P.iterate st = .stuck) : False := by
  have := P.iterate_spec ready
  rw [h] at this
  exact this

/-- **The driver run by well-founded recursion**: every iteration raises the solver's termination
measure, which is bounded, so no fuel is needed. -/
def runWF (st : DState A) (ready : P.Ready st) : Answer A :=
  match h : P.iterate st with
  | .next st' => runWF st' (P.iterate_next ready h).1
  | .sat M => .sat M
  | .unsat b => .unsat b.steps
  | .stuck => (P.iterate_not_stuck ready h).elim
termination_by P.measureBound - P.measure st.spec
decreasing_by
  have next := P.iterate_next ready h
  have := P.measure_le next.1.good.inv
  omega

/-- The driver, terminating by the measure. -/
def solveWF : Answer A := P.runWF P.initState P.initState_ready

theorem runFuel_eq_runWF : ∀ (n : ℕ) (st : DState A) (ready : P.Ready st),
    P.measureBound - P.measure st.spec < n → P.runFuel n st = P.runWF st ready
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, st, ready, fuel => by
    rw [runFuel, runWF]
    split
    · next st' h =>
      split
      · next _ st'' h' =>
        rw [h] at h'
        cases h'
        have next := P.iterate_next ready h
        have := P.measure_le next.1.good.inv
        exact runFuel_eq_runWF n st' next.1 (by omega)
      all_goals (rename_i h'; rw [h] at h'; cases h')
    · next M h =>
      split
      all_goals (rename_i h'; rw [h] at h'; cases h')
      rfl
    · next b h =>
      split
      all_goals (rename_i h'; rw [h] at h'; cases h')
      rfl
    · next h => exact (P.iterate_not_stuck ready h).elim

/-- **The fuel version and the measure version are the same function**, so every theorem about
`solve` holds of `solveWF`. -/
theorem solve_eq_solveWF : P.solve = P.solveWF :=
  P.runFuel_eq_runWF _ _ P.initState_ready (by rw [measure_initState, fuelBound]; omega)

end Program

end Driver

end Mettapedia.Logic.ASP
