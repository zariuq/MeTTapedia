import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.MatchBuild

/-!
# The phases of a compiled program

Each phase of `compile` decides one conjunct of admission:

* `run_loadParams`: the parameters go to their registers;
* `shapeChecks_iff` with `run_tests`: the shape tests pass exactly at `Shapes`;
* `run_lookups`, `fitDistinct_iff`: the lookups and the read/take tests pass exactly at `Fits`;
* `run_mtests`, `tells_phase`: the match code of the uses and the tells passes exactly when the
  information is solvable, and then the solutions are the assignments that agree with the
  registers;
* `guards_phase`: the guards refuse at the first guard that fails at some solution;
* `commit_phase`: the commit makes the result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

theorem run_seq {c : Ctx} {A B : List Instr} {m m' : Mach} (h : run c A m = (none, m')) :
    run c (A ++ B) m = run c B m' := by
  simp only [run_append, h]

theorem run_seq_stop {c : Ctx} {A B : List Instr} {m m' : Mach} {r : Reason}
    (h : run c A m = (some r, m')) : run c (A ++ B) m = (some r, m') := by
  simp only [run_append, h]

theorem forall_mem_flatMap_iff {α β : Type} {l : List α} {f : α → List β} {P : β → Prop} :
    (∀ b ∈ l.flatMap f, P b) ↔ ∀ a ∈ l, ∀ b ∈ f a, P b := by
  simp only [List.mem_flatMap]
  constructor
  · intro h a ha b hb
    exact h b ⟨a, ha, hb⟩
  · rintro h b ⟨a, ha, hb⟩
    exact h a ha b hb

/-! ## Tests that keep the machine -/

theorem run_tests (c : Ctx) (m : Mach) (r : Reason) (P : Instr → Prop) : ∀ is : List Instr,
    (∀ i ∈ is, (P i → i.exec c m = .ok m) ∧ (¬ P i → i.exec c m = .error r)) →
    ((∀ i ∈ is, P i) → run c is m = (none, m)) ∧ ((¬ ∀ i ∈ is, P i) → run c is m = (some r, m))
  | [], _ => ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | i :: is, h => by
      have hi := h i (List.mem_cons_self ..)
      have ih := run_tests c m r P is (fun j hj => h j (List.mem_cons_of_mem _ hj))
      by_cases hp : P i
      · have e := hi.1 hp
        refine ⟨fun hall => ?_, fun hnot => ?_⟩
        · simp only [run, e]
          exact ih.1 (fun j hj => hall j (List.mem_cons_of_mem _ hj))
        · simp only [run, e]
          refine ih.2 (fun hall => hnot (fun j hj => ?_))
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hp
          · exact hall j hj
      · have e := hi.2 hp
        refine ⟨fun hall => absurd (hall i (List.mem_cons_self ..)) hp, fun _ => ?_⟩
        simp only [run, e]

/-- What a test instruction asks. -/
def testCond (c : Ctx) (m : Mach) : Instr → Prop
  | .fail _ => False
  | .needName k => k < m.st.names
  | .paramMinted k => (c.param k).minted m.st.names = true
  | .occNonzero u => c.occ u ≠ 0
  | .occDistinct u v _ => c.occ u ≠ c.occ v
  | _ => True

theorem ite_ok_err {P : Prop} [Decidable P] {m : Mach} {r : Reason} {x : Except Reason Mach}
    (hx : x = if P then .ok m else .error r) : (P → x = .ok m) ∧ (¬ P → x = .error r) :=
  ⟨fun h => hx.trans (if_pos h), fun h => hx.trans (if_neg h)⟩

/-! ## Shapes -/

theorem shapeChecks_exec (R : Rule) (c : Ctx) (m : Mach) : ∀ i ∈ shapeChecks R,
    (testCond c m i → i.exec c m = .ok m) ∧ (¬ testCond c m i → i.exec c m = .error .shapes) := by
  intro i hi
  simp only [shapeChecks, List.mem_append, List.mem_map, List.mem_flatMap] at hi
  rcases hi with ((((⟨j, _, rfl⟩ | ⟨k, _, rfl⟩) | ⟨k, _, rfl⟩) | ⟨u, _, rfl⟩) | ⟨u, _, v, _, rfl⟩)
  · exact ⟨fun h => h.elim, fun _ => rfl⟩
  · exact ite_ok_err (P := k < m.st.names) rfl
  · exact ite_ok_err (P := (c.param k).minted m.st.names = true) rfl
  · exact ite_ok_err (P := c.occ u ≠ 0) rfl
  · exact ite_ok_err (P := c.occ u ≠ c.occ v) rfl

theorem mem_nameList {R : Rule} {k : Nat} : k ∈ R.nameList ↔ Tm.name k ∈ R.atomsAll := by
  simp only [Rule.nameList, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a with
    | name k' =>
        simp only [Option.some.injEq] at h
        subst h
        exact ha
    | _ => cases h
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_freshList {R : Rule} {j : Nat} : j ∈ R.freshList ↔ Tm.fresh j ∈ R.atomsAll := by
  simp only [Rule.freshList, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a with
    | fresh j' =>
        simp only [Option.some.injEq] at h
        subst h
        exact ha
    | _ => cases h
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_paramsUsed {R : Rule} {k : Nat} :
    k ∈ R.paramsUsed ↔ k < R.nparams ∧ Tm.loc k ∈ R.atomsAll := by
  simp only [Rule.paramsUsed, List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem atoms_ok_iff (R : Rule) (hR : InClass R) (s : St) (p : List Tm) :
    (∀ t ∈ R.opened, ∀ a ∈ t.atoms, AtomAtFrame R s p a) ↔
      (∀ j ∈ R.freshList, ¬ R.fresh ≤ j) ∧ (∀ k ∈ R.nameList, k < s.names) ∧
      (∀ k ∈ R.paramsUsed, (p.getD k default).minted s.names = true) := by
  have hmem : ∀ a, a ∈ R.atomsAll ↔ ∃ t ∈ R.opened, a ∈ t.atoms := fun a => List.mem_flatMap
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · obtain ⟨t, ht, ha⟩ := (hmem _).mp (mem_freshList.mp hj)
      exact Nat.not_le.mpr (h t ht _ ha)
    · obtain ⟨t, ht, ha⟩ := (hmem _).mp (mem_nameList.mp hk)
      exact h t ht _ ha
    · obtain ⟨hk1, hk2⟩ := mem_paramsUsed.mp hk
      obtain ⟨t, ht, ha⟩ := (hmem _).mp hk2
      exact h t ht _ ha hk1
  · rintro ⟨h1, h2, h3⟩ t ht a ha
    have haa : a ∈ R.atomsAll := (hmem a).mpr ⟨t, ht, ha⟩
    cases a with
    | name k => exact h2 k (mem_nameList.mpr haa)
    | fresh j => exact Nat.not_le.mp (h1 j (mem_freshList.mpr haa))
    | var i => exact absurd ha (hR.noFrameVariables t ht i)
    | loc k => exact fun hk => h3 k (mem_paramsUsed.mpr ⟨hk, haa⟩)
    | code _ => trivial
    | app _ _ => trivial

theorem shapeChecks_iff (R : Rule) (hR : InClass R) (p : List Tm) (o : List Nat) (m : Mach) :
    (∀ i ∈ shapeChecks R, testCond ⟨p, o⟩ m i) ↔ Shapes R m.st p o := by
  have e1 : (∀ i ∈ shapeChecks R, testCond ⟨p, o⟩ m i) ↔
      ((∀ j ∈ R.freshList, ¬ R.fresh ≤ j) ∧ (∀ k ∈ R.nameList, k < m.st.names) ∧
        (∀ k ∈ R.paramsUsed, (p.getD k default).minted m.st.names = true)) ∧
      (∀ u < R.takes.length, o.getD u 0 ≠ 0) ∧
      (∀ u < R.takes.length, ∀ v < u, o.getD u 0 ≠ o.getD v 0) := by
    simp only [shapeChecks, List.forall_mem_append, List.forall_mem_map, forall_mem_flatMap_iff,
      List.mem_filter, List.mem_range, testCond, Ctx.occ, Ctx.param, decide_eq_true_eq,
      imp_false, not_and, and_assoc]
  rw [e1, Shapes, atoms_ok_iff R hR]

/-! ## Fits -/

theorem fitDistinct_exec (R : Rule) (c : Ctx) (m : Mach) : ∀ i ∈ fitDistinct R,
    (testCond c m i → i.exec c m = .ok m) ∧ (¬ testCond c m i → i.exec c m = .error .fits) := by
  intro i hi
  simp only [fitDistinct, List.mem_flatMap, List.mem_map] at hi
  obtain ⟨u, _, v, _, rfl⟩ := hi
  exact ite_ok_err (P := c.occ u ≠ c.occ v) rfl

theorem fitDistinct_iff (R : Rule) (p : List Tm) (o : List Nat) (m : Mach) :
    (∀ i ∈ fitDistinct R, testCond ⟨p, o⟩ m i) ↔
      ∀ u < R.uses.length, R.takes.length ≤ u → ∀ v < R.takes.length, o.getD u 0 ≠ o.getD v 0 := by
  simp only [fitDistinct, forall_mem_flatMap_iff, List.mem_filter, List.mem_range, decide_eq_true_eq,
    List.forall_mem_map, testCond, Ctx.occ, and_imp]

theorem run_lookups (c : Ctx) (base : Nat) : ∀ (nu : Nat) (m : Mach),
    ((∀ u < nu, (labelOf m.st (c.occ u)).isSome = true) →
      ∃ rs', run c ((List.range nu).map fun u => Instr.lookup u (base + u)) m =
          (none, { m with rs := rs' }) ∧
        SameBelow m.rs rs' base ∧ ∀ u < nu, labelOf m.st (c.occ u) = some (rs' (base + u))) ∧
    ((¬ ∀ u < nu, (labelOf m.st (c.occ u)).isSome = true) →
      ∃ rs', run c ((List.range nu).map fun u => Instr.lookup u (base + u)) m =
        (some .fits, { m with rs := rs' }))
  | 0, m => ⟨fun _ => ⟨m.rs, rfl, SameBelow.refl _ _, fun u hu => absurd hu (Nat.not_lt_zero u)⟩,
      fun h => absurd (fun u hu => absurd hu (Nat.not_lt_zero u)) h⟩
  | nu + 1, m => by
      obtain ⟨ih1, ih2⟩ := run_lookups c base nu m
      rw [List.range_succ, List.map_append]
      constructor
      · intro hall
        obtain ⟨rs₁, r1, s1, v1⟩ := ih1 (fun u hu => hall u (by omega))
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hall nu (by omega))
        refine ⟨rs₁.write (base + nu) l, ?_, ?_, fun u hu => ?_⟩
        · rw [run_seq r1]
          simp [run, Instr.exec, hl]
        · exact SameBelow.trans s1 (write_sameBelow rs₁ l (by omega)) (Nat.le_refl _)
        · by_cases hun : u = nu
          · subst hun
            rw [Regs.write_same]
            exact hl
          · rw [Regs.write_other _ _ (by omega)]
            exact v1 u (by omega)
      · intro hnot
        by_cases hpre : ∀ u < nu, (labelOf m.st (c.occ u)).isSome = true
        · obtain ⟨rs₁, r1, -, -⟩ := ih1 hpre
          cases hx : labelOf m.st (c.occ nu) with
          | some l =>
              exfalso
              apply hnot
              intro u hu
              by_cases hun : u = nu
              · subst hun
                simp [hx]
              · exact hpre u (by omega)
          | none =>
              refine ⟨rs₁, ?_⟩
              rw [run_seq r1]
              simp [run, Instr.exec, hx]
        · obtain ⟨rs₁, r1⟩ := ih2 hpre
          exact ⟨rs₁, run_seq_stop r1⟩

/-! ## Parameters -/

theorem run_loadParams (c : Ctx) : ∀ (np : Nat) (m : Mach),
    ∃ rs', run c ((List.range np).map fun k => Instr.loadParam k k) m = (none, { m with rs := rs' }) ∧
      (∀ k < np, rs' k = c.param k)
  | 0, m => ⟨m.rs, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | np + 1, m => by
      obtain ⟨rs₁, h1, h2⟩ := run_loadParams c np m
      refine ⟨rs₁.write np (c.param np), ?_, fun k hk => ?_⟩
      · rw [List.range_succ, List.map_append, run_seq h1]
        simp [run, Instr.exec]
      · by_cases hkn : k = np
        · subst hkn
          exact Regs.write_same _ _ _
        · rw [Regs.write_other _ _ hkn]
          exact h2 k (by omega)

/-! ## Match code as tests -/

theorem run_mtests (c : Ctx) (why : Reason) : ∀ (is : List MInstr) (m : Mach),
    (∀ rs', MInstr.run m.st.names is m.rs = some rs' →
      run c (is.map fun i => Instr.test i why) m = (none, { m with rs := rs' })) ∧
    (MInstr.run m.st.names is m.rs = none →
      ∃ rs', run c (is.map fun i => Instr.test i why) m = (some why, { m with rs := rs' }))
  | [], m => ⟨fun rs' h => by
        simp only [MInstr.run, Option.some.injEq] at h
        subst h
        rfl,
      fun h => by simp [MInstr.run] at h⟩
  | i :: is, m => by
      rcases hi : MInstr.exec m.st.names m.rs i with _ | rs₁
      · refine ⟨fun rs' h => ?_, fun _ => ⟨m.rs, ?_⟩⟩
        · simp [MInstr.run, hi] at h
        · simp [run, Instr.exec, hi]
      · have ih := run_mtests c why is { m with rs := rs₁ }
        refine ⟨fun rs' h => ?_, fun h => ?_⟩
        · simp only [MInstr.run, hi] at h
          have := ih.1 rs' h
          simp only [List.map_cons, run, Instr.exec, hi]
          exact this
        · simp only [MInstr.run, hi] at h
          obtain ⟨rs', h'⟩ := ih.2 h
          refine ⟨rs', ?_⟩
          simp only [List.map_cons, run, Instr.exec, hi]
          exact h'

/-! ## Tells -/

theorem Tm.mem_locals {t : Tm} {k : Nat} : k ∈ t.locals ↔ Tm.loc k ∈ t.atoms := by
  simp only [Tm.locals, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    cases a with
    | loc k' =>
        simp only [Option.some.injEq] at h
        subst h
        exact ha
    | _ => cases h
  · intro h
    exact ⟨_, h, rfl⟩

theorem determinedB_iff {E : Env} {t : Tm} :
    determinedB E t = true ↔ ∀ x, Tm.loc x ∈ t.atoms → (E x).isSome = true := by
  simp only [determinedB, List.all_eq_true]
  constructor
  · intro h x hx
    exact h x (Tm.mem_locals.mpr hx)
  · intro h x hx
    exact h x (Tm.mem_locals.mp hx)

theorem orient_spec (E : Env) (b : List Nat) (hb : ∀ x, (E x).isSome = true ↔ x ∈ b) (e : Tm × Tm)
    (h : (∀ k ∈ e.1.locals, k ∈ b) ∨ (∀ k ∈ e.2.locals, k ∈ b)) :
    (∀ x, Tm.loc x ∈ (orient E e).2.atoms → (E x).isSome = true) ∧
    (∀ σ φ, (orient E e).1.inst σ φ = (orient E e).2.inst σ φ ↔ e.1.inst σ φ = e.2.inst σ φ) ∧
    (∀ x, (x ∈ b ∨ Tm.loc x ∈ (orient E e).1.atoms) ↔ x ∈ b ++ e.1.locals ++ e.2.locals) := by
  unfold orient
  by_cases hd : determinedB E e.2 = true
  · rw [if_pos hd]
    have hd' := determinedB_iff.mp hd
    refine ⟨hd', fun _ _ => Iff.rfl, fun x => ?_⟩
    simp only [List.mem_append, Tm.mem_locals]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
    · rintro ((h1 | h1) | h1)
      · exact Or.inl h1
      · exact Or.inr h1
      · exact Or.inl ((hb x).mp (hd' x h1))
  · rw [if_neg hd]
    have h1 : ∀ k ∈ e.1.locals, k ∈ b := by
      rcases h with h | h
      · exact h
      · exfalso
        apply hd
        apply determinedB_iff.mpr
        intro x hx
        exact (hb x).mpr (h x (Tm.mem_locals.mpr hx))
    refine ⟨fun x hx => (hb x).mpr (h1 x (Tm.mem_locals.mpr hx)), fun _ _ => eq_comm, fun x => ?_⟩
    simp only [List.mem_append, Tm.mem_locals]
    constructor
    · rintro (h2 | h2)
      · exact Or.inl (Or.inl h2)
      · exact Or.inr h2
    · rintro ((h2 | h2) | h2)
      · exact Or.inl h2
      · exact Or.inl (h1 x (Tm.mem_locals.mpr h2))
      · exact Or.inr h2

theorem tell_spec (c : Ctx) (lr : Tm × Tm) (E : Env) (n : Nat) (m : Mach)
    (P : (Nat → Tm) → Prop) (hE : EnvBelow E n)
    (hr : ∀ x, Tm.loc x ∈ lr.2.atoms → (E x).isSome = true) (hP : ∀ σ, P σ ↔ Agrees σ E m.rs) :
    (∀ i ∈ (compileTell E n lr).1, i.pure = true) ∧ n ≤ (compileTell E n lr).2.2 ∧
    EnvBelow (compileTell E n lr).2.1 (compileTell E n lr).2.2 ∧
    (∀ x, ((compileTell E n lr).2.1 x).isSome = true ↔ (E x).isSome = true ∨ Tm.loc x ∈ lr.1.atoms) ∧
    ((∃ rs', run c (compileTell E n lr).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
        ∀ σ, (P σ ∧ lr.1.inst σ (openFresh m.st.names) = lr.2.inst σ (openFresh m.st.names)) ↔
          Agrees σ (compileTell E n lr).2.1 rs') ∨
     (∃ rs', run c (compileTell E n lr).1 m = (some .unsolvable, { m with rs := rs' }) ∧
        ¬ ∃ σ, P σ ∧ lr.1.inst σ (openFresh m.st.names) = lr.2.inst σ (openFresh m.st.names))) := by
  obtain ⟨b1, b2, b3, b4⟩ := cb_spec c lr.2 E n hE hr
  obtain ⟨s1, s2, s3, s4⟩ := cm_static lr.1 E (cb E n lr.2).2.1 (cb E n lr.2).2.2 b1 (hE.mono b2)
  have hd := cm_dyn m.st.names lr.1 E (cb E n lr.2).2.1 (cb E n lr.2).2.2 b1 (hE.mono b2)
  dsimp only [compileTell]
  refine ⟨fun i hi => ?_, by omega, s2, s4, ?_⟩
  · rcases List.mem_append.mp hi with hi | hi
    · exact b3 i hi
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      rfl
  · obtain ⟨rs₁, r1, sm1, v1⟩ := b4 m
    rcases hrun : MInstr.run m.st.names (cm E (cb E n lr.2).2.1 (cb E n lr.2).2.2 lr.1).1 rs₁
      with _ | rs₂
    · right
      obtain ⟨rs', hr'⟩ := (run_mtests c .unsolvable
        (cm E (cb E n lr.2).2.1 (cb E n lr.2).2.2 lr.1).1 { m with rs := rs₁ }).2 hrun
      refine ⟨rs', ?_, ?_⟩
      · rw [run_seq r1]
        exact hr'
      · rintro ⟨σ, hPσ, heq⟩
        have a := (hP σ).mp hPσ
        have a₁ : Agrees σ E rs₁ := (agrees_iff_of_sameBelow hE sm1).mp a
        exact hd.2 rs₁ hrun σ a₁ (heq.trans (v1 σ a).symm)
    · left
      have hr' := (run_mtests c .unsolvable
        (cm E (cb E n lr.2).2.1 (cb E n lr.2).2.2 lr.1).1 { m with rs := rs₁ }).1 rs₂ hrun
      obtain ⟨sm2, i2⟩ := hd.1 rs₁ rs₂ hrun
      refine ⟨rs₂, ?_, SameBelow.trans sm1 sm2 b2, fun σ => ?_⟩
      · rw [run_seq r1]
        exact hr'
      · constructor
        · rintro ⟨hPσ, heq⟩
          have a := (hP σ).mp hPσ
          have a₁ : Agrees σ E rs₁ := (agrees_iff_of_sameBelow hE sm1).mp a
          exact (i2 σ a₁).mp (heq.trans (v1 σ a).symm)
        · intro A
          have a₁ : Agrees σ E rs₁ := agrees_mono s3 (hE.mono b2) sm2 A
          have a : Agrees σ E m.rs := (agrees_iff_of_sameBelow hE sm1).mpr a₁
          exact ⟨(hP σ).mpr a, ((i2 σ a₁).mpr A).trans (v1 σ a)⟩

theorem tells_phase (c : Ctx) : ∀ (es : List (Tm × Tm)) (E : Env) (n : Nat) (b : List Nat)
    (m : Mach) (P : (Nat → Tm) → Prop), EnvBelow E n → (∀ x, (E x).isSome = true ↔ x ∈ b) →
    TellsInOrder b es → (∀ σ, P σ ↔ Agrees σ E m.rs) →
    (∀ i ∈ (compileTells E n es).1, i.pure = true) ∧ n ≤ (compileTells E n es).2.2 ∧
    EnvBelow (compileTells E n es).2.1 (compileTells E n es).2.2 ∧
    (∀ x, ((compileTells E n es).2.1 x).isSome = true ↔ x ∈ boundAfter b es) ∧
    ((∃ rs', run c (compileTells E n es).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
        ∀ σ, (P σ ∧ ∀ e ∈ es, e.1.inst σ (openFresh m.st.names) = e.2.inst σ (openFresh m.st.names)) ↔
          Agrees σ (compileTells E n es).2.1 rs') ∨
     (∃ rs', run c (compileTells E n es).1 m = (some .unsolvable, { m with rs := rs' }) ∧
        ¬ ∃ σ, P σ ∧ ∀ e ∈ es, e.1.inst σ (openFresh m.st.names) = e.2.inst σ (openFresh m.st.names)))
  | [], E, n, b, m, P, hE, hb, _, hP => by
      dsimp only [compileTells]
      exact ⟨fun i hi => (by cases hi), Nat.le_refl _, hE, hb, Or.inl ⟨m.rs, rfl, SameBelow.refl _ _,
        fun σ => ⟨fun h => (hP σ).mp h.1, fun h => ⟨(hP σ).mpr h, fun e he => (by cases he)⟩⟩⟩⟩
  | e :: es, E, n, b, m, P, hE, hb, htells, hP => by
      obtain ⟨hdet, hrest⟩ := htells
      obtain ⟨o1, o2, o3⟩ := orient_spec E b hb e hdet
      obtain ⟨t1, t2, t3, t4, t5⟩ := tell_spec c (orient E e) E n m P hE o1 hP
      have hb' : ∀ x, ((compileTell E n (orient E e)).2.1 x).isSome = true ↔
          x ∈ b ++ e.1.locals ++ e.2.locals := by
        intro x
        rw [t4 x, hb x]
        exact o3 x
      obtain ⟨u1, u2, u3, u4, -⟩ := tells_phase c es (compileTell E n (orient E e)).2.1
        (compileTell E n (orient E e)).2.2 (b ++ e.1.locals ++ e.2.locals) m
        (fun σ => Agrees σ (compileTell E n (orient E e)).2.1 m.rs) t3 hb' hrest (fun _ => Iff.rfl)
      dsimp only [compileTells]
      refine ⟨fun i hi => ?_, by omega, u3, u4, ?_⟩
      · rcases List.mem_append.mp hi with hi | hi
        · exact t1 i hi
        · exact u1 i hi
      · rcases t5 with ⟨rs₁, r1, sm1, i1⟩ | ⟨rs₁, r1, hno⟩
        · have hP' : ∀ σ, (P σ ∧ e.1.inst σ (openFresh m.st.names) = e.2.inst σ (openFresh m.st.names)) ↔
              Agrees σ (compileTell E n (orient E e)).2.1 rs₁ := fun σ =>
            ⟨fun h => (i1 σ).mp ⟨h.1, (o2 σ _).mpr h.2⟩,
             fun h => ⟨((i1 σ).mpr h).1, (o2 σ _).mp ((i1 σ).mpr h).2⟩⟩
          obtain ⟨-, -, -, -, v5⟩ := tells_phase c es (compileTell E n (orient E e)).2.1
            (compileTell E n (orient E e)).2.2 (b ++ e.1.locals ++ e.2.locals) { m with rs := rs₁ }
            (fun σ => P σ ∧ e.1.inst σ (openFresh m.st.names) = e.2.inst σ (openFresh m.st.names))
            t3 hb' hrest hP'
          rcases v5 with ⟨rs₂, r2, sm2, i2⟩ | ⟨rs₂, r2, hno2⟩
          · left
            refine ⟨rs₂, ?_, SameBelow.trans sm1 sm2 t2, fun σ => ⟨?_, ?_⟩⟩
            · rw [run_seq r1]
              exact r2
            · rintro ⟨hPσ, hall⟩
              exact (i2 σ).mp ⟨⟨hPσ, hall e (List.mem_cons_self ..)⟩,
                fun e' he' => hall e' (List.mem_cons_of_mem _ he')⟩
            · intro A
              obtain ⟨⟨hPσ, h1⟩, h2⟩ := (i2 σ).mpr A
              refine ⟨hPσ, fun e' he' => ?_⟩
              rcases List.mem_cons.mp he' with rfl | he'
              · exact h1
              · exact h2 e' he'
          · right
            refine ⟨rs₂, ?_, ?_⟩
            · rw [run_seq r1]
              exact r2
            · rintro ⟨σ, hPσ, hall⟩
              exact hno2 ⟨σ, ⟨hPσ, hall e (List.mem_cons_self ..)⟩,
                fun e' he' => hall e' (List.mem_cons_of_mem _ he')⟩
        · right
          refine ⟨rs₁, run_seq_stop r1, ?_⟩
          rintro ⟨σ, hPσ, hall⟩
          exact hno ⟨σ, hPσ, (o2 σ _).mpr (hall e (List.mem_cons_self ..))⟩

/-! ## Guards -/

mutual
/-- The size of a term. -/
def Tm.size : Tm → Nat
  | .app _ args => Tm.sizeList args + 1
  | .code _ => 1
  | .name _ => 1
  | .var _ => 1
  | .loc _ => 1
  | .fresh _ => 1
def Tm.sizeList : List Tm → Nat
  | [] => 0
  | t :: ts => Tm.size t + Tm.sizeList ts
end

mutual
/-- A local's value lies inside every instance of a term that mentions it. -/
theorem Tm.size_le_inst (σ φ : Nat → Tm) (x : Nat) : ∀ t : Tm,
    Tm.loc x ∈ t.atoms → (σ x).size ≤ (t.inst σ φ).size
  | .app f args, h => by
      have := Tm.sizeList_le_inst σ φ x args (by simpa only [Tm.atoms] using h)
      simp only [Tm.inst, Tm.size]
      omega
  | .loc y, h => by
      simp only [Tm.atoms, List.mem_singleton, Tm.loc.injEq] at h
      subst h
      simp only [Tm.inst]
      exact Nat.le_refl _
  | .code _, h => by simp [Tm.atoms] at h
  | .name _, h => by simp [Tm.atoms] at h
  | .var _, h => by simp [Tm.atoms] at h
  | .fresh _, h => by simp [Tm.atoms] at h
theorem Tm.sizeList_le_inst (σ φ : Nat → Tm) (x : Nat) : ∀ ts : List Tm,
    Tm.loc x ∈ Tm.atomsList ts → (σ x).size ≤ Tm.sizeList (Tm.instList σ φ ts)
  | [], h => by simp [Tm.atomsList] at h
  | t :: ts, h => by
      simp only [Tm.atomsList, List.mem_append] at h
      simp only [Tm.instList, Tm.sizeList]
      rcases h with h | h
      · have := Tm.size_le_inst σ φ x t h
        omega
      · have := Tm.sizeList_le_inst σ φ x ts h
        omega
end

/-- A term larger than `n`. -/
def Tm.big (n : Nat) : Tm := .app 0 (List.replicate n (.code 0))

theorem Tm.size_big (n : Nat) : (Tm.big n).size = n + 1 := by
  have h : ∀ k : Nat, Tm.sizeList (List.replicate k (Tm.code 0)) = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ, Tm.sizeList, Tm.size, ih]; omega
  simp only [Tm.big, Tm.size, h]

/-- A bound on the sizes of the present labels. -/
def labelBound (l : List Row) : Nat := l.foldr (fun r acc => r.label.size + acc) 0

theorem size_le_labelBound : ∀ (l : List Row), ∀ row ∈ l, row.label.size ≤ labelBound l
  | [], _, h => by cases h
  | r :: l, row, h => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [labelBound, List.foldr_cons]
        omega
      · have := size_le_labelBound l row h
        simp only [labelBound, List.foldr_cons] at this ⊢
        omega

theorem absent_iff_count (s : St) (v : Tm) :
    (∀ row ∈ s.present, row.label ≠ v) ↔
      (s.present.filter fun row => decide (row.label = v)).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp only [decide_eq_true_eq, ne_eq]

theorem countGuard_phase (c : Ctx) (q : Tm) (k : Nat) (E : Env) (n i : Nat) (m : Mach)
    (S : (Nat → Tm) → Prop) (hE : EnvBelow E n)
    (hS : ∀ σ, S σ ↔ Agrees σ E m.rs) (hne : ∃ σ, S σ) :
    (∀ j ∈ (countGuard E n i q k).1, j.pure = true) ∧ n ≤ (countGuard E n i q k).2 ∧
    ((∃ rs', run c (countGuard E n i q k).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
        ∀ σ, S σ → (m.st.present.filter fun row =>
          decide (row.label = q.inst σ (openFresh m.st.names))).length = k) ∨
     (∃ rs', run c (countGuard E n i q k).1 m = (some (.guard i), { m with rs := rs' }) ∧
        ¬ ∀ σ, S σ → (m.st.present.filter fun row =>
          decide (row.label = q.inst σ (openFresh m.st.names))).length = k)) := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  by_cases hd : determinedB E q = true
  · have hq := determinedB_iff.mp hd
    obtain ⟨b1, b2, b3, b4⟩ := cb_spec c q E n hE hq
    obtain ⟨rs₁, r1, sm1, v1⟩ := b4 m
    simp only [countGuard, hd, ↓reduceIte]
    refine ⟨fun j hj => ?_, by omega, ?_⟩
    · rcases List.mem_append.mp hj with hj | hj
      · exact b3 j hj
      · simp only [List.mem_singleton] at hj
        subst hj
        rfl
    · have hval : ∀ σ, S σ → q.inst σ (openFresh m.st.names) = rs₁ (cb E n q).2.2 :=
        fun σ hσ => (v1 σ ((hS σ).mp hσ)).symm
      by_cases hc : (m.st.present.filter fun row => decide (row.label = rs₁ (cb E n q).2.2)).length = k
      · left
        refine ⟨rs₁, ?_, sm1, fun σ hσ => ?_⟩
        · rw [run_seq r1]
          simp [run, Instr.exec, hc]
        · rw [hval σ hσ]
          exact hc
      · right
        refine ⟨rs₁, ?_, fun hall => hc ?_⟩
        · rw [run_seq r1]
          simp [run, Instr.exec, hc]
        · have h := hall σ₀ hσ₀
          rw [hval σ₀ hσ₀] at h
          exact h
  by_cases hk0 : k ≠ 0
  · -- a count of a nonzero number with guard-only locals fails at every state
    have hcode : (countGuard E n i q k).1 =
        [Instr.scanNone n (cm E (n + 1) n q).1 (.guard i), Instr.fail (.guard i)] := by
      simp only [countGuard, hd, Bool.false_eq_true, ↓reduceIte, hk0]
    have hnext : (countGuard E n i q k).2 = n + 1 := by
      simp only [countGuard, hd, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun j hj => ?_, by omega, Or.inr ⟨m.rs, ?_, fun hall => ?_⟩⟩
    · rw [hcode] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
    · show run c (countGuard E n i q k).1 m = (some (.guard i), m)
      rw [hcode]
      have e2 : Instr.exec c m (.fail (.guard i)) = .error (.guard i) := rfl
      by_cases hany : m.st.present.any (fun row =>
          (MInstr.run m.st.names (cm E (n + 1) n q).1 (m.rs.write n row.label)).isSome) = true
      · have e : Instr.exec c m (.scanNone n (cm E (n + 1) n q).1 (.guard i)) = .error (.guard i) := by
          simp only [Instr.exec, hany, ↓reduceIte]
        simp only [run, e]
      · have e : Instr.exec c m (.scanNone n (cm E (n + 1) n q).1 (.guard i)) = .ok m := by
          simp only [Instr.exec, hany, Bool.false_eq_true, ↓reduceIte]
        simp only [run, e, e2]
    · have hfree : ∃ x, Tm.loc x ∈ q.atoms ∧ E x = none := by
        have hnot : ¬ ∀ x, Tm.loc x ∈ q.atoms → (E x).isSome = true :=
          fun h => hd (determinedB_iff.mpr h)
        simp only [not_forall] at hnot
        obtain ⟨x, hx, hns⟩ := hnot
        refine ⟨x, hx, ?_⟩
        cases hEx : E x with
        | none => rfl
        | some _ =>
            rw [hEx] at hns
            exact absurd rfl hns
      obtain ⟨x, hx, hEx⟩ := hfree
      have hS' : S (agreeing E m.rs (fun _ => Tm.big (labelBound m.st.present + 1))) :=
        (hS _).mpr (agreeing_agrees _ _ _)
      have hval : agreeing E m.rs (fun _ => Tm.big (labelBound m.st.present + 1)) x =
          Tm.big (labelBound m.st.present + 1) := by
        simp [agreeing, hEx]
      have hlarge : ∀ row ∈ m.st.present,
          ¬ row.label = q.inst (agreeing E m.rs (fun _ => Tm.big (labelBound m.st.present + 1)))
            (openFresh m.st.names) := by
        intro row hrow heq
        have h1 := Tm.size_le_inst (agreeing E m.rs (fun _ => Tm.big (labelBound m.st.present + 1)))
          (openFresh m.st.names) x q hx
        rw [hval, Tm.size_big, ← heq] at h1
        have h3 := size_le_labelBound m.st.present row hrow
        omega
      have h0 := hall _ hS'
      have hnil : (m.st.present.filter fun row => decide (row.label =
          q.inst (agreeing E m.rs (fun _ => Tm.big (labelBound m.st.present + 1)))
            (openFresh m.st.names))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro row hrow h
        exact hlarge row hrow (of_decide_eq_true h)
      rw [hnil] at h0
      exact hk0 h0.symm
  have hk00 : k = 0 := Classical.byContradiction hk0
  · subst hk00
    have hcs := cm_static q E (n + 1) n (Nat.lt_succ_self n) (hE.mono (Nat.le_succ n))
    have hcd := cm_dyn m.st.names q E (n + 1) n (Nat.lt_succ_self n) (hE.mono (Nat.le_succ n))
    simp only [countGuard, hd, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun j hj => ?_, Nat.le_succ n, ?_⟩
    · simp only [List.mem_singleton] at hj
      subst hj
      rfl
    · by_cases hany : m.st.present.any (fun row =>
          (MInstr.run m.st.names (cm E (n + 1) n q).1 (m.rs.write n row.label)).isSome) = true
      · right
        have e : Instr.exec c m (.scanNone n (cm E (n + 1) n q).1 (.guard i)) = .error (.guard i) := by
          simp only [Instr.exec, hany, ↓reduceIte]
        refine ⟨m.rs, ?_, fun hall => ?_⟩
        · rw [show run c [Instr.scanNone n (cm E (n + 1) n q).1 (.guard i)] m = (some (.guard i), m) by
            simp only [run, e]]
        · obtain ⟨row, hrow, hsome⟩ := List.any_eq_true.mp hany
          obtain ⟨rs'', hrun⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨sm, hiff⟩ := hcd.1 _ _ hrun
          have a' : Agrees (agreeing (cm E (n + 1) n q).2.1 rs'' σ₀) (cm E (n + 1) n q).2.1 rs'' :=
            agreeing_agrees _ _ _
          have a0 : Agrees (agreeing (cm E (n + 1) n q).2.1 rs'' σ₀) E (m.rs.write n row.label) :=
            agrees_mono hcs.2.2.1 (hE.mono (Nat.le_succ n)) sm a'
          have hm : Agrees (agreeing (cm E (n + 1) n q).2.1 rs'' σ₀) E m.rs :=
            (agrees_iff_of_sameBelow hE (write_sameBelow m.rs row.label (Nat.le_refl n))).mpr a0
          have heq : q.inst (agreeing (cm E (n + 1) n q).2.1 rs'' σ₀) (openFresh m.st.names) =
              row.label := by
            have h := (hiff _ a0).mpr a'
            rw [Regs.write_same] at h
            exact h
          have h0 := hall _ ((hS _).mpr hm)
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
          exact h0 row hrow (by simp [heq])
      · left
        have e : Instr.exec c m (.scanNone n (cm E (n + 1) n q).1 (.guard i)) = .ok m := by
          simp only [Instr.exec, hany, Bool.false_eq_true, ↓reduceIte]
        refine ⟨m.rs, ?_, SameBelow.refl _ _, fun σ hσ => ?_⟩
        · rw [show run c [Instr.scanNone n (cm E (n + 1) n q).1 (.guard i)] m = (none, m) by
            simp only [run, e]]
        · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro row hrow hlab
          simp only [decide_eq_true_eq] at hlab
          apply hany
          apply List.any_eq_true.mpr
          refine ⟨row, hrow, ?_⟩
          cases hrun : MInstr.run m.st.names (cm E (n + 1) n q).1 (m.rs.write n row.label) with
          | some _ => rfl
          | none =>
              exfalso
              have a0 : Agrees σ E (m.rs.write n row.label) :=
                (agrees_iff_of_sameBelow hE (write_sameBelow m.rs row.label (Nat.le_refl n))).mp
                  ((hS σ).mp hσ)
              apply hcd.2 _ hrun σ a0
              rw [Regs.write_same]
              exact hlab.symm

theorem guard_phase (c : Ctx) (host : String → List Tm → Prop) (E : Env) (b : List Nat)
    (hb : ∀ x, (E x).isSome = true ↔ x ∈ b) (n i : Nat) (m : Mach) (S : (Nat → Tm) → Prop)
    (hE : EnvBelow E n) (hS : ∀ σ, S σ ↔ Agrees σ E m.rs) (hne : ∃ σ, S σ) :
    ∀ g : Guard, g.inClassB b = true →
    (∀ j ∈ (compileGuard E n i g).1, j.pure = true) ∧ n ≤ (compileGuard E n i g).2 ∧
    ((∃ rs', run c (compileGuard E n i g).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
        ∀ σ, S σ → g.Holds host m.st σ) ∨
     (∃ rs', run c (compileGuard E n i g).1 m = (some (.guard i), { m with rs := rs' }) ∧
        ¬ ∀ σ, S σ → g.Holds host m.st σ))
  | .host _ _, hg => by simp [Guard.inClassB] at hg
  | .absent q, _ => by
      obtain ⟨g1, g2, g3⟩ := countGuard_phase c q 0 E n i m S hE hS hne
      refine ⟨g1, g2, ?_⟩
      rcases g3 with ⟨rs', r, sm, h⟩ | ⟨rs', r, h⟩
      · exact Or.inl ⟨rs', r, sm, fun σ hσ => (absent_iff_count m.st _).mpr (h σ hσ)⟩
      · exact Or.inr ⟨rs', r, fun hall => h (fun σ hσ => (absent_iff_count m.st _).mp (hall σ hσ))⟩
  | .count q k, _ => countGuard_phase c q k E n i m S hE hS hne
  | .ask a a', hg => by
      have hall := List.all_eq_true.mp hg
      have ha : ∀ x, Tm.loc x ∈ a.atoms → (E x).isSome = true := fun x hx =>
        (hb x).mpr (by simpa using hall x (List.mem_append_left _ (Tm.mem_locals.mpr hx)))
      have ha' : ∀ x, Tm.loc x ∈ a'.atoms → (E x).isSome = true := fun x hx =>
        (hb x).mpr (by simpa using hall x (List.mem_append_right _ (Tm.mem_locals.mpr hx)))
      obtain ⟨x1, x2, x3, x4⟩ := cb_spec c a E n hE ha
      obtain ⟨y1, y2, y3, y4⟩ := cb_spec c a' E (cb E n a).2.1 (hE.mono x2) ha'
      obtain ⟨σ₀, hσ₀⟩ := hne
      obtain ⟨rs₁, r1, sm1, v1⟩ := x4 m
      obtain ⟨rs₂, r2, sm2, v2⟩ := y4 { m with rs := rs₁ }
      have va : ∀ σ, S σ → a.inst σ (openFresh m.st.names) = rs₂ (cb E n a).2.2 := fun σ hσ =>
        (v1 σ ((hS σ).mp hσ)).symm.trans (sm2 _ x1).symm
      have vb : ∀ σ, S σ → a'.inst σ (openFresh m.st.names) = rs₂ (cb E (cb E n a).2.1 a').2.2 :=
        fun σ hσ => (v2 σ ((agrees_iff_of_sameBelow hE sm1).mp ((hS σ).mp hσ))).symm
      have hrun : run c (compileGuard E n i (.ask a a')).1 m =
          run c [Instr.test (.eqReg (cb E n a).2.2 (cb E (cb E n a).2.1 a').2.2) (.guard i)]
            { m with rs := rs₂ } := by
        show run c ((cb E n a).1 ++ (cb E (cb E n a).2.1 a').1 ++ [_]) m = _
        rw [List.append_assoc, run_seq r1, run_seq r2]
      refine ⟨fun j hj => ?_, ?_, ?_⟩
      · simp only [compileGuard, List.mem_append, List.mem_singleton] at hj
        rcases hj with (hj | hj) | rfl
        · exact x3 j hj
        · exact y3 j hj
        · rfl
      · show n ≤ (cb E (cb E n a).2.1 a').2.1
        omega
      · by_cases heq : rs₂ (cb E n a).2.2 = rs₂ (cb E (cb E n a).2.1 a').2.2
        · left
          refine ⟨rs₂, ?_, SameBelow.trans sm1 sm2 x2, fun σ hσ => ?_⟩
          · rw [hrun]
            simp [run, Instr.exec, MInstr.exec, heq]
          · show a.inst σ _ = a'.inst σ _
            rw [va σ hσ, vb σ hσ, heq]
        · right
          refine ⟨rs₂, ?_, fun hall => heq ?_⟩
          · rw [hrun]
            simp [run, Instr.exec, MInstr.exec, heq]
          · have h : a.inst σ₀ (openFresh m.st.names) = a'.inst σ₀ (openFresh m.st.names) := hall σ₀ hσ₀
            rw [← va σ₀ hσ₀, ← vb σ₀ hσ₀]
            exact h

theorem guards_phase (c : Ctx) (host : String → List Tm → Prop) (E : Env) (b : List Nat)
    (hb : ∀ x, (E x).isSome = true ↔ x ∈ b) (S : (Nat → Tm) → Prop) (hne : ∃ σ, S σ) :
    ∀ (gs : List Guard) (n i0 : Nat) (m : Mach), EnvBelow E n → (∀ g ∈ gs, g.inClassB b = true) →
    (∀ σ, S σ ↔ Agrees σ E m.rs) →
    (∀ j ∈ (compileGuards E n i0 gs).1, j.pure = true) ∧ n ≤ (compileGuards E n i0 gs).2 ∧
    ((∃ rs', run c (compileGuards E n i0 gs).1 m = (none, { m with rs := rs' }) ∧
        SameBelow m.rs rs' n ∧ ∀ g ∈ gs, ∀ σ, S σ → g.Holds host m.st σ) ∨
     (∃ j rs', run c (compileGuards E n i0 gs).1 m = (some (.guard (i0 + j)), { m with rs := rs' }) ∧
        ∃ g, gs[j]? = some g ∧ ¬ (∀ σ, S σ → g.Holds host m.st σ) ∧
          ∀ j' < j, ∀ g', gs[j']? = some g' → ∀ σ, S σ → g'.Holds host m.st σ))
  | [], n, _, m, _, _, _ => by
      dsimp only [compileGuards]
      exact ⟨fun j hj => (by cases hj), Nat.le_refl _,
        Or.inl ⟨m.rs, rfl, SameBelow.refl _ _, fun g hg => (by cases hg)⟩⟩
  | g :: gs, n, i0, m, hE, hcl, hS => by
      obtain ⟨g1, g2, g3⟩ :=
        guard_phase c host E b hb n i0 m S hE hS hne g (hcl g (List.mem_cons_self ..))
      obtain ⟨h1, h2, -⟩ := guards_phase c host E b hb S hne gs (compileGuard E n i0 g).2 (i0 + 1) m
        (hE.mono g2) (fun g' hg' => hcl g' (List.mem_cons_of_mem _ hg')) hS
      dsimp only [compileGuards]
      refine ⟨fun j hj => ?_, by omega, ?_⟩
      · rcases List.mem_append.mp hj with hj | hj
        · exact g1 j hj
        · exact h1 j hj
      · rcases g3 with ⟨rs₁, r1, sm1, hok⟩ | ⟨rs₁, r1, hbad⟩
        · have hS₁ : ∀ σ, S σ ↔ Agrees σ E rs₁ := fun σ =>
            (hS σ).trans (agrees_iff_of_sameBelow hE sm1)
          obtain ⟨-, -, h3⟩ := guards_phase c host E b hb S hne gs (compileGuard E n i0 g).2 (i0 + 1)
            { m with rs := rs₁ } (hE.mono g2) (fun g' hg' => hcl g' (List.mem_cons_of_mem _ hg')) hS₁
          rcases h3 with ⟨rs₂, r2, sm2, hall⟩ | ⟨j, rs₂, r2, g', hg', hno, hbefore⟩
          · left
            refine ⟨rs₂, ?_, SameBelow.trans sm1 sm2 g2, fun g'' hg'' => ?_⟩
            · rw [run_seq r1]
              exact r2
            · rcases List.mem_cons.mp hg'' with rfl | hg''
              · exact hok
              · exact hall g'' hg''
          · right
            have hidx : i0 + (j + 1) = i0 + 1 + j := by omega
            refine ⟨j + 1, rs₂, ?_, g', by simpa using hg', hno, fun j' hj' g'' hg'' => ?_⟩
            · rw [hidx, run_seq r1]
              exact r2
            · cases j' with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hg''
                  subst hg''
                  exact hok
              | succ j'' =>
                  exact hbefore j'' (by omega) g'' (by simpa using hg'')
        · right
          refine ⟨0, rs₁, ?_, g, rfl, hbad, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
          rw [Nat.add_zero]
          exact run_seq_stop r1

/-! ## Commit -/

theorem run_removes (c : Ctx) : ∀ (k : Nat) (m : Mach),
    ∃ m', run c ((List.range k).map Instr.remove) m = (none, m') ∧ m'.rs = m.rs ∧ m'.made = m.made ∧
      m'.st.names = m.st.names ∧ m'.st.nextId = m.st.nextId ∧ m'.st.vars = m.st.vars ∧
      m'.st.diseqs = m.st.diseqs ∧
      m'.st.present = m.st.present.filter fun row => ((List.range k).map c.occ).all fun id => row.id != id
  | 0, m => ⟨m, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩
  | k + 1, m => by
      obtain ⟨m', h1, h2, h3, h4, h5, h6, h7, h8⟩ := run_removes c k m
      refine ⟨{ m' with st := { m'.st with present := m'.st.present.filter fun row => row.id != c.occ k } },
        ?_, h2, h3, h4, h5, h6, h7, ?_⟩
      · rw [List.range_succ, List.map_append, run_seq h1]
        rfl
      · show (m'.st.present.filter fun row => row.id != c.occ k) = _
        rw [h8, List.filter_filter, List.range_succ, List.map_append]
        congr 1
        funext row
        simp only [List.all_append, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true]
        exact Bool.and_comm _ _

theorem run_adds (c : Ctx) : ∀ (regs : List Nat) (m : Mach),
    ∃ m', run c (regs.map Instr.add) m = (none, m') ∧
      m'.made = m.made ++ List.range' m.st.nextId regs.length ∧
      m'.st.present = m.st.present ++ madeRows m.st.nextId (regs.map m.rs) ∧
      m'.st.nextId = m.st.nextId + regs.length ∧ m'.st.names = m.st.names ∧
      m'.st.vars = m.st.vars ∧ m'.st.diseqs = m.st.diseqs
  | [], m => ⟨m, rfl, by simp, by simp [madeRows], by simp, rfl, rfl, rfl⟩
  | r :: rest, m => by
      obtain ⟨m', h1, h2, h3, h4, h5, h6, h7⟩ := run_adds c rest
        { m with st := { m.st with present := m.st.present ++ [⟨m.st.nextId, m.rs r⟩],
                                   nextId := m.st.nextId + 1 },
                 made := m.made ++ [m.st.nextId] }
      refine ⟨m', ?_, ?_, ?_, ?_, h5, h6, h7⟩
      · simp only [List.map_cons, run, Instr.exec]
        exact h1
      · rw [h2]
        simp [List.range'_succ]
      · rw [h3]
        simp [madeRows]
      · rw [h4]
        simp only [List.length_cons]
        omega

theorem St.ext_fields {a b : St} (h1 : a.vars = b.vars) (h2 : a.diseqs = b.diseqs)
    (h3 : a.names = b.names) (h4 : a.nextId = b.nextId) (h5 : a.present = b.present) : a = b := by
  cases a
  cases b
  simp only [St.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem commit_phase (c : Ctx) (R : Rule) (E : Env) (n : Nat) (m : Mach) (σ : Nat → Tm)
    (hE : EnvBelow E n) (hloc : ∀ t ∈ R.makes, ∀ x, Tm.loc x ∈ t.atoms → (E x).isSome = true)
    (ha : Agrees σ E m.rs) :
    ∃ m', run c ((cbList E n R.makes).1 ++ [Instr.mint R.fresh] ++
        (List.range R.takes.length).map Instr.remove ++ (cbList E n R.makes).2.2.map Instr.add) m =
        (none, m') ∧
      m'.made = m.made ++ List.range' m.st.nextId R.makes.length ∧
      m'.st = { m.st with
        names := m.st.names + R.fresh
        nextId := m.st.nextId + R.makes.length
        present := m.st.present.filter (fun row =>
            ((List.range R.takes.length).map c.occ).all fun id => row.id != id) ++
          madeRows m.st.nextId (R.makes.map (Tm.inst σ (openFresh m.st.names))) } := by
  have hloc' : ∀ x, Tm.loc x ∈ Tm.atomsList R.makes → (E x).isSome = true := by
    intro x hx
    rw [Tm.atomsList_eq_flatMap, List.mem_flatMap] at hx
    obtain ⟨t, ht, hx⟩ := hx
    exact hloc t ht x hx
  obtain ⟨l1, -, -, -, l5⟩ := cbList_spec c R.makes E n hE hloc'
  obtain ⟨rs₁, r1, -, v1⟩ := l5 m
  obtain ⟨m₂, r2, q1, q2, q3, q4, q5, q6, q7⟩ := run_removes c R.takes.length
    { m with rs := rs₁, st := { m.st with names := m.st.names + R.fresh } }
  obtain ⟨m₃, r3, p1, p2, p3, p4, p5, p6⟩ := run_adds c (cbList E n R.makes).2.2 m₂
  have hB : run c ((cbList E n R.makes).1 ++ [Instr.mint R.fresh]) m =
      (none, { m with rs := rs₁, st := { m.st with names := m.st.names + R.fresh } }) := by
    rw [run_seq r1]
    rfl
  have hBR : run c ((cbList E n R.makes).1 ++ [Instr.mint R.fresh] ++
      (List.range R.takes.length).map Instr.remove) m = (none, m₂) := by
    rw [run_seq hB]
    exact r2
  refine ⟨m₃, ?_, ?_, ?_⟩
  · rw [run_seq hBR]
    exact r3
  · rw [p1, q2, q4, l1]
  · apply St.ext_fields
    · rw [p5, q5]
    · rw [p6, q6]
    · rw [p4, q3]
    · rw [p3, q4, l1]
    · rw [p2, q7, q4, q1]
      dsimp only
      rw [v1 σ ha]

#print axioms tells_phase
#print axioms guards_phase
#print axioms commit_phase

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
