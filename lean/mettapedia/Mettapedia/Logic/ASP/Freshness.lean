import Mettapedia.Logic.ASP.FirstUIP

/-!
# Freshness of first-UIP nogoods under exhaustive propagation

The solver's `learn` rule needs a nogood whose set of literals was not learned
before. A first-UIP nogood is new when propagation was exhaustive before every
decision: had it been in the database, it would have been unit on its unique
implication point just before the decision of the current level was made.

* `Quiescent learned t`: no learned nogood is falsified or unit on the
  trail `t`.
* `Exhaustive s`: the trail below every decision is quiescent, with the
  current learned nogoods. Only learned nogoods matter: completion and loop
  nogoods need not have been propagated exhaustively.

## Results

* **Freshness** (`Program.firstUIP_fresh`): in a state with the invariant and a
  justified, exhaustive trail, at a falsified nogood with a literal at the current
  level above level 0, the first-UIP nogood's set of literals is not the set of
  any learned nogood, which is exactly the side condition of `learn`.
* **The discipline that keeps the invariant** (`Program.CDNL`): the solver's
  rules, with decisions only when no learned nogood is unit or falsified, and
  learning only of nogoods that are neither unit nor falsified below any
  decision. Every `CDNL` step is a
  solver step (`Program.CDNL.step`), and every `CDNL`-reachable state is
  exhaustive (`Program.cdnlReachable_exhaustive`).
* **First-UIP learning fits the discipline** (`Program.firstUIP_learnable`): after
  the backjump to the assertion level, the first-UIP nogood is neither unit nor
  falsified below any decision of the new trail; so the backjump followed by
  learning the nogood are two `CDNL` steps (`Program.firstUIP_cdnl`), and the
  learned nogood is fresh.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Relation

universe u

variable {A : Type u}

section Freshness

variable [DecidableEq A]

omit [DecidableEq A] in
/-- Above level 0 the current level ends with its decision. -/
theorem currentLevel_split : ∀ {t : List (Entry A)}, levelOf t ≠ 0 →
    ∃ newer d, currentLevel t = newer ++ [d] ∧ d.reason = none
  | [], h => absurd rfl h
  | e :: t, h => by
    by_cases decision : e.reason = none
    · exact ⟨[], e, by simp [currentLevel, decision], decision⟩
    · rw [levelOf_cons, if_neg decision] at h
      obtain ⟨newer, d, split, isDecision⟩ := currentLevel_split h
      refine ⟨e :: newer, d, ?_, isDecision⟩
      have : e.reason.isNone = false := by
        rcases h : e.reason with _ | ρ
        · exact absurd h decision
        · rfl
      simp [currentLevel, this, split]

omit [DecidableEq A] in
theorem cutTo_self {j : ℕ} : ∀ {t : List (Entry A)}, levelOf t ≤ j → cutTo j t = t
  | [], _ => rfl
  | _ :: _, h => by rw [cutTo, if_pos h]

omit [DecidableEq A] in
theorem levelOf_le_append (x y : List (Entry A)) : levelOf y ≤ levelOf (x ++ y) := by
  rw [levelOf_append]
  omega

omit [DecidableEq A] in
theorem foldr_max_mem : ∀ (l : List ℕ), l.foldr max 0 ∈ l ∨ l.foldr max 0 = 0
  | [] => Or.inr rfl
  | x :: l => by
    rcases foldr_max_mem l with h | h
    · rw [List.foldr_cons]
      rcases le_total x (l.foldr max 0) with le | le
      · rw [max_eq_right le]
        exact Or.inl (List.mem_cons_of_mem _ h)
      · rw [max_eq_left le]
        exact Or.inl List.mem_cons_self
    · rw [List.foldr_cons, h]
      exact Or.inl (by rw [Nat.max_zero]; exact List.mem_cons_self)

/-- No learned nogood is falsified or unit on the trail `t`. -/
def Quiescent (learned : List (Nogood A)) (t : List (Entry A)) : Prop :=
  ∀ δ ∈ learned, ¬ (⟨t, learned, 0⟩ : State A).Falsifies δ ∧ ∀ l, ¬ (⟨t, learned, 0⟩ : State A).UnitOn δ l

/-- **Exhaustive propagation of the learned nogoods below every decision.** -/
def Exhaustive (s : State A) : Prop :=
  ∀ newer d older, s.trail = newer ++ d :: older → d.reason = none → Quiescent s.learned older

namespace Program

variable (P : Program A)

/-- **The first-UIP nogood is fresh** under exhaustive propagation. -/
theorem firstUIP_fresh {s : State A} (inv : P.Inv s) (just : Justified s.trail) (exhaustive : Exhaustive s)
    {δ : Nogood A} (falsified : s.Falsifies δ) (level : levelOf s.trail ≠ 0)
    (current : ∃ m ∈ δ.lits, m ∈ (currentLevel s.trail).map Entry.lit) :
    (firstUIP s δ).toFinset ∉ s.learned.map fun η => η.lits.toFinset := by
  intro learned
  obtain ⟨η, hη, same⟩ := List.mem_map.mp learned
  obtain ⟨-, u, hu, uCurrent, others⟩ := firstUIP_uip just falsified current
  obtain ⟨newer, d, levelSplit, decision⟩ := currentLevel_split level
  have whole := currentLevel_append_belowLevel s.trail
  rw [levelSplit, List.append_assoc, List.singleton_append] at whole
  have quiet := exhaustive newer d (belowLevel s.trail) whole.symm decision η hη
  apply quiet.2 u
  have sameMem : ∀ m, m ∈ η.lits ↔ m ∈ firstUIP s δ := by
    intro m
    rw [← List.mem_toFinset, same, List.mem_toFinset]
  refine ⟨(sameMem u).mpr hu, fun m hm ne => others m ((sameMem m).mp hm) ne, ?_⟩
  rintro ⟨f, hf, sameVar⟩
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp uCurrent
  have nodup := inv.nodup
  rw [← currentLevel_append_belowLevel s.trail, List.map_append] at nodup
  exact (List.nodup_append.mp nodup).2.2 _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hf) sameVar.symm

/-! ## The discipline -/

/-- **The solver with exhaustive propagation of learned nogoods**: decisions only when no learned
nogood is unit or falsified, learning only of nogoods neither unit nor falsified below any
decision. -/
inductive CDNL : Config A → Config A → Prop
  | propagate {s : State A} {δ : Nogood A} {l : Lit A} :
      P.InDatabase s δ → s.UnitOn δ l → P.IsVar l.var →
      CDNL (.running s) (.running (s.push ⟨l.compl, levelOf s.trail, some δ⟩))
  | decide {s : State A} {l : Lit A} :
      Quiescent s.learned s.trail → P.IsVar l.var → ¬ s.Assigned l.var →
      CDNL (.running s) (.running (s.push ⟨l, levelOf s.trail + 1, none⟩))
  | fail {s : State A} {δ : Nogood A} :
      P.InDatabase s δ → s.Falsifies δ → levelOf s.trail = 0 → CDNL (.running s) (.done .unsat)
  | backjump {s : State A} {δ ε : Nogood A} {l : Lit A} {newer older : List (Entry A)} {d : Entry A} :
      P.InDatabase s δ → s.Falsifies δ → s.trail = newer ++ d :: older → d.reason = none →
      P.Entailed ε.lits → l ∈ ε.lits → (∀ m ∈ ε.lits, m ≠ l → m ∈ older.map Entry.lit) →
      (∀ e ∈ older, e.lit.var ≠ l.var) → P.IsVar l.var →
      CDNL (.running s) (.running ⟨⟨l.compl, levelOf older, some ε⟩ :: older, s.learned, s.restartMark⟩)
  | learn {s : State A} {ε : Nogood A} :
      P.Entailed ε.lits → (∀ m ∈ ε.lits, P.IsVar m.var) →
      ε.lits.toFinset ∉ s.learned.map (fun η => η.lits.toFinset) →
      (∀ newer d older, s.trail = newer ++ d :: older → d.reason = none →
        ¬ (⟨older, s.learned, 0⟩ : State A).Falsifies ε ∧ ∀ l, ¬ (⟨older, s.learned, 0⟩ : State A).UnitOn ε l) →
      CDNL (.running s) (.running { s with learned := ε :: s.learned })
  | restart {s : State A} {newer older : List (Entry A)} :
      s.trail = newer ++ older → (∀ e ∈ older, e.reason ≠ none) → s.restartMark < s.learned.length →
      CDNL (.running s) (.running ⟨older, s.learned, s.learned.length⟩)
  | succeed {s : State A} :
      (∀ x, P.IsVar x → s.Assigned x) → (∀ δ ∈ P.completionNogoods, ¬ s.Falsifies δ) →
      (∀ (U : Finset A), (∀ b ∈ U, ¬ P.Falsum b) → ∀ a ∈ U, ¬ s.Falsifies (P.loopNogood U a)) →
      CDNL (.running s) (.done (.sat (P.trailModel s)))

/-- **The discipline refines the solver.** -/
theorem CDNL.step {c c' : Config A} (h : P.CDNL c c') : P.Step c c' := by
  cases h with
  | propagate database unit isVar => exact .propagate database unit isVar
  | decide _ isVar unassigned => exact .decide isVar unassigned
  | fail database falsified ground => exact .fail database falsified ground
  | backjump database falsified split decision entailed member rest outside isVar =>
    exact .backjump database falsified split decision entailed member rest outside isVar
  | learn entailed vars fresh _ => exact .learn entailed vars fresh
  | restart split propagated fair => exact .restart split propagated fair
  | succeed total completion loops => exact .succeed total completion loops

omit [DecidableEq A] in
/-- A decision of `e :: t` other than a propagated `e` is a decision of `t`. -/
theorem split_cons_of_reason {e d : Entry A} {t newer older : List (Entry A)} (implied : e.reason ≠ none)
    (decision : d.reason = none) (split : e :: t = newer ++ d :: older) :
    ∃ newer', t = newer' ++ d :: older := by
  rcases newer with _ | ⟨f, newer'⟩
  · simp only [List.nil_append, List.cons.injEq] at split
    obtain ⟨rfl, -⟩ := split
    exact absurd decision implied
  · simp only [List.cons_append, List.cons.injEq] at split
    exact ⟨newer', split.2⟩

/-- **The discipline keeps propagation exhaustive.** -/
theorem CDNL.exhaustive {s s' : State A} (h : P.CDNL (.running s) (.running s')) (ex : Exhaustive s) :
    Exhaustive s' := by
  cases h with
  | propagate _ _ _ =>
    intro newer d older split decision
    obtain ⟨newer', split'⟩ := split_cons_of_reason (by simp) decision split
    exact ex newer' d older split' decision
  | decide quiet _ _ =>
    intro newer d older split decision
    rcases newer with _ | ⟨f, newer'⟩
    · simp only [State.push, List.nil_append, List.cons.injEq] at split
      obtain ⟨-, rfl⟩ := split
      exact quiet
    · simp only [State.push, List.cons_append, List.cons.injEq] at split
      exact ex newer' d older split.2 decision
  | @backjump _ δ ε l newer₀ older₀ d₀ _ _ split₀ decision₀ =>
    intro newer d older split decision
    obtain ⟨newer', split'⟩ := split_cons_of_reason (by simp) decision split
    exact ex (newer₀ ++ d₀ :: newer') d older (by rw [split₀, split']; simp) decision
  | @learn _ ε _ _ _ below =>
    intro newer d older split decision δ learned
    rcases List.mem_cons.mp learned with rfl | learned
    · exact below newer d older split decision
    · exact ex newer d older split decision δ learned
  | @restart _ newer₀ older₀ split₀ propagated _ =>
    intro newer d older split decision
    simp only at split
    exact absurd decision (propagated d (by rw [split]; exact List.mem_append_right _ List.mem_cons_self))

/-- States reachable under the discipline. -/
def CDNLReachable (c : Config A) : Prop := ReflTransGen P.CDNL (.running State.initial) c

theorem cdnlReachable_reachable {c : Config A} (h : P.CDNLReachable c) : P.Reachable c := by
  unfold CDNLReachable at h
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ step ih => exact ih.tail (CDNL.step P step)

/-- **Every state reachable under the discipline is exhaustive.** -/
theorem cdnlReachable_exhaustive {s : State A} (h : P.CDNLReachable (.running s)) : Exhaustive s := by
  suffices ∀ c, P.CDNLReachable c → ∀ s, c = .running s → Exhaustive s from this _ h s rfl
  intro c reach
  induction reach with
  | refl =>
    rintro s ⟨⟩ newer d older split
    exact absurd split.symm (by simp [State.initial])
  | @tail b c _ step ih =>
    rintro s rfl
    cases b with
    | done r => cases step
    | running s₀ => exact CDNL.exhaustive P step (ih s₀ rfl)

/-! ## First-UIP learning fits the discipline -/

/-- **After the backjump, the first-UIP nogood is neither unit nor falsified below any
decision.** -/
theorem firstUIP_learnable {s : State A} (inv : P.Inv s) {δ : Nogood A} {u : Lit A} (hu : u ∈ firstUIP s δ) (origin : Origin A)
    (unit : (⟨cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail, s.learned, s.restartMark⟩ : State A).UnitOn
      ⟨firstUIP s δ, origin⟩ u) :
    ∀ newer d older,
      (⟨u.compl, assertionLevel s.trail (firstUIP s δ) u, some ⟨firstUIP s δ, origin⟩⟩ ::
        cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail) = newer ++ d :: older → d.reason = none →
      ¬ (⟨older, s.learned, 0⟩ : State A).Falsifies ⟨firstUIP s δ, origin⟩ ∧
        ∀ l, ¬ (⟨older, s.learned, 0⟩ : State A).UnitOn ⟨firstUIP s δ, origin⟩ l := by
  intro newer d older split decision
  set t := s.trail with ht
  set r := firstUIP s δ with hr
  set j := assertionLevel t r u with hj
  obtain ⟨newer', cutSplit⟩ := split_cons_of_reason (by simp) decision split
  -- the decision lies in the backjumped trail, whose level is `j`
  have cutLevel : levelOf (cutTo j t) ≤ j := by
    by_cases le : j ≤ levelOf t
    · rw [levelOf_cutTo le]
    · rw [cutTo_self (by omega)]
      omega
  have olderLevel : levelOf older < j := by
    have := levelOf_le_append newer' (d :: older)
    rw [← cutSplit, levelOf_cons, if_pos decision] at this
    omega
  -- `u` is unassigned below the decision
  obtain ⟨preCut, cutWhole⟩ := cutTo_suffix j t
  have olderIn : ∀ f ∈ older, f ∈ cutTo j t := fun f hf => by
    rw [cutSplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
  have uOff : u ∉ older.map Entry.lit := by
    intro h
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp h
    exact unit.2.2 ⟨f, olderIn f hf, rfl⟩
  -- some other literal of the nogood lies at level `j`, which is above `older`
  have otherOff : ∃ m ∈ r, m ≠ u ∧ m ∉ older.map Entry.lit := by
    have positive : 0 < j := by omega
    rcases foldr_max_mem ((r.filter (· ≠ u)).map fun m => litLevel m t) with h | h
    · obtain ⟨m, hm, hlevel⟩ := List.mem_map.mp h
      obtain ⟨hm, ne⟩ := List.mem_filter.mp hm
      have ne : m ≠ u := by simpa using ne
      refine ⟨m, hm, ne, fun onOlder => ?_⟩
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp onOlder
      obtain ⟨pre, post, olderSplit⟩ := List.append_of_mem hf
      have full : t = (preCut ++ newer' ++ d :: pre) ++ f :: post := by
        rw [cutWhole, cutSplit, olderSplit]
        simp
      have atF : litLevel f.lit t = levelOf (f :: post) := by
        rw [full]
        exact litLevel_append_cons rfl (not_mem_map_lit (nodup_split inv.nodup full).1)
      have : levelOf (f :: post) ≤ levelOf older := by
        rw [olderSplit]
        exact levelOf_le_append _ _
      change litLevel f.lit t = j at hlevel
      omega
    · change j = 0 at h
      omega
  obtain ⟨m, hm, ne, mOff⟩ := otherOff
  refine ⟨fun falsifies => uOff (falsifies u hu), fun l unitOn => ?_⟩
  by_cases same : l = u
  · subst same
    exact mOff (unitOn.2.1 m hm ne)
  · exact uOff (unitOn.2.1 u hu (Ne.symm same))

/-- **First-UIP learning under the discipline**: at a conflict above level 0 with a literal at the
current level, in an exhaustive state, the backjump to the assertion level and then learning the
first-UIP nogood are two steps of `CDNL`. -/
theorem firstUIP_cdnl {s : State A} (inv : P.Inv s) (just : Justified s.trail) (exhaustive : Exhaustive s)
    {δ : Nogood A} (database : P.InDatabase s δ) (falsified : s.Falsifies δ) (level : levelOf s.trail ≠ 0)
    (current : ∃ m ∈ δ.lits, m ∈ (currentLevel s.trail).map Entry.lit) (origin : Origin A) :
    ∃ u s', P.CDNL (.running s) (.running s') ∧
      s' = ⟨⟨u.compl, assertionLevel s.trail (firstUIP s δ) u, some ⟨firstUIP s δ, origin⟩⟩ ::
        cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail, s.learned, s.restartMark⟩ ∧
      P.CDNL (.running s') (.running { s' with learned := ⟨firstUIP s δ, origin⟩ :: s'.learned }) := by
  obtain ⟨u, hu, uCurrent, below, cutLevel, unit, -⟩ :=
    P.firstUIP_backjump inv just database falsified level current origin
  obtain ⟨pre, d, cutSplit, decision⟩ := cutTo_split below
  have isVar : P.IsVar u.var := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp uCurrent
    exact inv.vars g (by rw [← currentLevel_append_belowLevel s.trail]; exact List.mem_append_left _ hg)
  have backjump := CDNL.backjump (P := P) (ε := ⟨firstUIP s δ, origin⟩) (l := u) database falsified cutSplit
    decision (P.firstUIP_entailed inv database) unit.1 unit.2.1 (fun e he same => unit.2.2 ⟨e, he, same⟩) isVar
  rw [cutLevel] at backjump
  refine ⟨u, _, backjump, rfl, ?_⟩
  refine .learn (P.firstUIP_entailed inv database) ?_ (P.firstUIP_fresh inv just exhaustive falsified level current)
    (firstUIP_learnable P inv hu origin unit)
  intro m hm
  by_cases mu : m = u
  · exact mu ▸ isVar
  · have := unit.2.1 m hm mu
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp this
    obtain ⟨preCut, cutWhole⟩ := cutTo_suffix (assertionLevel s.trail (firstUIP s δ) u) s.trail
    exact inv.vars g (by rw [cutWhole]; exact List.mem_append_right _ hg)

end Program

end Freshness

end Mettapedia.Logic.ASP
