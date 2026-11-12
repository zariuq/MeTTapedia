import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Phases

/-!
# The specializer is correct

For every rule of the specialized class, every state, every parameters and identities, and every
meaning of host predicates:

* `specialized_admission`: admission alone gives the step's verdict (`RefVerdict`: admitted, or
  the first conjunct that fails: shapes, fits, unsolvable, or which guard), leaves the state as it
  was, and reports the frame's next name as the first name a firing mints;
* `specialized_firing`: the firing gives the same verdict; a refusal changes nothing and makes no
  identity; an admission leaves `Result` at every solution, with the made identities
  `nextId, nextId + 1, ...`;
* `inClassB_iff`, `specialize_isSome_iff`: the specializer returns a program exactly for the rules
  of the class;
* `dispatch_generic_iff`: a decision goes to the generic route exactly outside the specialized
  fragment (a rule outside the class, a frame with variables or live disequations, or a parameter
  that is not closed).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-! ## The pieces of a compiled program -/

/-- The match code of the uses. -/
def usesM (R : Rule) : List MInstr × Env × Nat :=
  cmList (paramEnv R.nparams) (R.nparams + R.uses.length) R.nparams R.uses
/-- The code of the tells. -/
def tellsT (R : Rule) : List Instr × Env × Nat := compileTells (usesM R).2.1 (usesM R).2.2 R.tells
/-- The code of the guards. -/
def guardsG (R : Rule) : List Instr × Nat := compileGuards (tellsT R).2.1 (tellsT R).2.2 0 R.guards
/-- The build code of the makes. -/
def makesB (R : Rule) : List Instr × Nat × List Nat := cbList (tellsT R).2.1 (guardsG R).2 R.makes

theorem compile_eq (R : Rule) : compile R =
    { checks := (List.range R.nparams).map (fun k => Instr.loadParam k k) ++ shapeChecks R ++
        fitChecks R ++ (usesM R).1.map (fun i => Instr.test i .unsolvable) ++ (tellsT R).1 ++
        (guardsG R).1
      commit := (makesB R).1 ++ [Instr.mint R.fresh] ++ (List.range R.takes.length).map Instr.remove ++
        (makesB R).2.2.map Instr.add } := rfl

/-! ## Facts about the class -/

theorem paramEnv_below (np n : Nat) (h : np ≤ n) : EnvBelow (paramEnv np) n := by
  intro x r hx
  simp only [paramEnv] at hx
  split at hx
  · cases hx
    omega
  · cases hx

theorem paramEnv_isSome (np x : Nat) : ((paramEnv np) x).isSome = true ↔ x < np := by
  simp only [paramEnv]
  split <;> simp_all

theorem agrees_paramEnv (σ : Nat → Tm) (np : Nat) (rs : Regs) :
    Agrees σ (paramEnv np) rs ↔ ∀ k < np, σ k = rs k := by
  constructor
  · intro a k hk
    exact a k k (by simp [paramEnv, hk])
  · intro h x r hx
    simp only [paramEnv] at hx
    split at hx
    · cases hx
      exact h x (by assumption)
    · cases hx

theorem uses_binds (R : Rule) : ∀ x, ((usesM R).2.1 x).isSome = true ↔ x ∈ R.boundUses := by
  intro x
  have h := (cmList_static R.uses (paramEnv R.nparams) (R.nparams + R.uses.length) R.nparams
    (Nat.le_refl _) (paramEnv_below _ _ (Nat.le_add_right _ _))).2.2.2 x
  rw [usesM, h, paramEnv_isSome, Rule.boundUses, List.mem_append, List.mem_range,
    Tm.atomsList_eq_flatMap, List.mem_flatMap, List.mem_flatMap]
  simp only [Tm.mem_locals]

theorem inClass_guards {R : Rule} (hR : InClass R) :
    ∀ g ∈ R.guards, g.inClassB (boundAfter R.boundUses R.tells) = true := by
  intro g hg
  cases g with
  | ask a b =>
      simp only [Guard.inClassB, List.all_eq_true, decide_eq_true_eq]
      exact hR.asks a b hg
  | absent q => rfl
  | count q n => rfl
  | host h args => exact absurd (hR.noHostGuards _ hg) (by simp [Guard.isHost])

theorem matchL_iff (σ φ : Nat → Tm) (rs : Regs) : ∀ (ts : List Tm) (src : Nat),
    MatchL σ φ rs src ts ↔ ∀ u < ts.length, (ts.getD u default).inst σ φ = rs (src + u)
  | [], src => by simp [MatchL]
  | t :: ts, src => by
      rw [MatchL, matchL_iff σ φ rs ts (src + 1)]
      constructor
      · rintro ⟨h0, h1⟩ u hu
        cases u with
        | zero => simpa using h0
        | succ u =>
            have e : src + (u + 1) = src + 1 + u := by omega
            rw [e]
            simpa using h1 u (by simp at hu; omega)
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun u hu => ?_⟩
        have e : src + 1 + u = src + (u + 1) := by omega
        rw [e]
        simpa using h (u + 1) (by simp; omega)

/-! ## The checks -/

theorem checks_spec (R : Rule) (hR : InClass R) (s : St) (p : List Tm) (o : List Nat)
    (host : String → List Tm → Prop) :
    (run ⟨p, o⟩ (compile R).checks (Prog.start s)).2.st = s ∧
    (run ⟨p, o⟩ (compile R).checks (Prog.start s)).2.made = [] ∧
    (∀ r, (run ⟨p, o⟩ (compile R).checks (Prog.start s)).1 = some r →
      RefVerdict R s p o host (.refused r)) ∧
    ((run ⟨p, o⟩ (compile R).checks (Prog.start s)).1 = none → Admits R s p o host ∧
      EnvBelow (tellsT R).2.1 (guardsG R).2 ∧
      ∀ σ, Sol R s p o σ ↔ Agrees σ (tellsT R).2.1 (run ⟨p, o⟩ (compile R).checks (Prog.start s)).2.rs) := by
  -- the statics of the uses and the tells
  have hE0 : EnvBelow (paramEnv R.nparams) (R.nparams + R.uses.length) :=
    paramEnv_below _ _ (Nat.le_add_right _ _)
  obtain ⟨-, u2, u3, -⟩ := cmList_static R.uses (paramEnv R.nparams) (R.nparams + R.uses.length)
    R.nparams (Nat.le_refl _) hE0
  -- the run, re-associated
  have hchecks : (compile R).checks = (List.range R.nparams).map (fun k => Instr.loadParam k k) ++
      (shapeChecks R ++ (lookups R ++ (fitDistinct R ++ ((usesM R).1.map (fun i => Instr.test i .unsolvable) ++
        ((tellsT R).1 ++ (guardsG R).1))))) := by
    simp only [compile_eq, fitChecks, List.append_assoc]
  set c : Ctx := ⟨p, o⟩
  -- the parameters
  obtain ⟨rs₀, h0, hp0⟩ := run_loadParams c R.nparams (Prog.start s)
  have hrun0 : run c (compile R).checks (Prog.start s) =
      run c (shapeChecks R ++ (lookups R ++ (fitDistinct R ++ ((usesM R).1.map (fun i => Instr.test i .unsolvable) ++
        ((tellsT R).1 ++ (guardsG R).1))))) { Prog.start s with rs := rs₀ } := by
    rw [hchecks]
    exact run_seq h0
  -- shapes
  have hsh := run_tests c { Prog.start s with rs := rs₀ } .shapes (testCond c { Prog.start s with rs := rs₀ })
    (shapeChecks R) (shapeChecks_exec R c _)
  have hshiff := shapeChecks_iff R hR p o { Prog.start s with rs := rs₀ }
  by_cases hS : Shapes R s p o
  swap
  · have hfin : run c (compile R).checks (Prog.start s) = (some .shapes, { Prog.start s with rs := rs₀ }) :=
      hrun0.trans (run_seq_stop (hsh.2 (fun h => hS (hshiff.mp h))))
    rw [hfin]
    exact ⟨rfl, rfl, fun r hr => by cases hr; exact hS, fun h => by cases h⟩
  have hrun1 : run c (compile R).checks (Prog.start s) =
      run c (lookups R ++ (fitDistinct R ++ ((usesM R).1.map (fun i => Instr.test i .unsolvable) ++
        ((tellsT R).1 ++ (guardsG R).1)))) { Prog.start s with rs := rs₀ } :=
    hrun0.trans (run_seq (hsh.1 (hshiff.mpr hS)))
  -- fits: the lookups
  obtain ⟨hl1, hl2⟩ := run_lookups c R.nparams R.uses.length { Prog.start s with rs := rs₀ }
  by_cases hF1 : ∀ u < R.uses.length, (labelOf s (c.occ u)).isSome = true
  swap
  · obtain ⟨rsL, hL⟩ := hl2 hF1
    have hfin : run c (compile R).checks (Prog.start s) = (some .fits, { Prog.start s with rs := rsL }) :=
      hrun1.trans (run_seq_stop (A := lookups R) hL)
    rw [hfin]
    exact ⟨rfl, rfl, fun r hr => by cases hr; exact ⟨hS, fun hF => hF1 hF.1⟩, fun h => by cases h⟩
  obtain ⟨rsL, hL, sL, vL⟩ := hl1 hF1
  have hrun2 : run c (compile R).checks (Prog.start s) =
      run c (fitDistinct R ++ ((usesM R).1.map (fun i => Instr.test i .unsolvable) ++
        ((tellsT R).1 ++ (guardsG R).1))) { Prog.start s with rs := rsL } :=
    hrun1.trans (run_seq (A := lookups R) hL)
  -- fits: nothing both read and taken
  have hfd := run_tests c { Prog.start s with rs := rsL } .fits (testCond c { Prog.start s with rs := rsL })
    (fitDistinct R) (fitDistinct_exec R c _)
  have hfdiff := fitDistinct_iff R p o { Prog.start s with rs := rsL }
  by_cases hF2 : ∀ u < R.uses.length, R.takes.length ≤ u → ∀ v < R.takes.length, o.getD u 0 ≠ o.getD v 0
  swap
  · have hfin : run c (compile R).checks (Prog.start s) = (some .fits, { Prog.start s with rs := rsL }) :=
      hrun2.trans (run_seq_stop (hfd.2 (fun h => hF2 (hfdiff.mp h))))
    rw [hfin]
    exact ⟨rfl, rfl, fun r hr => by cases hr; exact ⟨hS, fun hF => hF2 hF.2⟩, fun h => by cases h⟩
  have hF : Fits R s o := ⟨hF1, hF2⟩
  have hrun3 : run c (compile R).checks (Prog.start s) =
      run c ((usesM R).1.map (fun i => Instr.test i .unsolvable) ++ ((tellsT R).1 ++ (guardsG R).1))
        { Prog.start s with rs := rsL } :=
    hrun2.trans (run_seq (hfd.1 (hfdiff.mpr hF2)))
  -- the information: the uses
  have hparams : ∀ σ, Agrees σ (paramEnv R.nparams) rsL ↔ ∀ k < R.nparams, σ k = p.getD k default := by
    intro σ
    rw [agrees_paramEnv]
    constructor
    · intro h k hk
      exact (h k hk).trans ((sL k hk).trans (hp0 k hk))
    · intro h k hk
      exact (h k hk).trans ((sL k hk).trans (hp0 k hk)).symm
  have huses : ∀ σ, MatchL σ (openFresh s.names) rsL R.nparams R.uses ↔
      ∀ u < R.uses.length, labelOf s (o.getD u 0) =
        some ((R.uses.getD u default).inst σ (openFresh s.names)) := by
    intro σ
    rw [matchL_iff]
    constructor
    · intro h u hu
      exact (vL u hu).trans (congrArg some (h u hu).symm)
    · intro h u hu
      have e := (vL u hu).symm.trans (h u hu)
      exact (Option.some.inj e).symm
  have hdU := cmList_dyn s.names R.uses (paramEnv R.nparams) (R.nparams + R.uses.length) R.nparams
    (Nat.le_refl _) hE0
  rcases hU : MInstr.run s.names (usesM R).1 rsL with _ | rs₁
  · -- the uses have no solution
    obtain ⟨rs', hstop⟩ := (run_mtests c .unsolvable (usesM R).1 { Prog.start s with rs := rsL }).2 hU
    have hfin : run c (compile R).checks (Prog.start s) = (some .unsolvable, { Prog.start s with rs := rs' }) :=
      hrun3.trans (run_seq_stop hstop)
    rw [hfin]
    refine ⟨rfl, rfl, fun r hr => ?_, fun h => by cases h⟩
    cases hr
    refine ⟨hS, hF, ?_⟩
    rintro ⟨σ, hσp, hσu, -⟩
    exact hdU.2 rsL hU σ ((hparams σ).mpr hσp) ((huses σ).mpr hσu)
  have hr1 := (run_mtests c .unsolvable (usesM R).1 { Prog.start s with rs := rsL }).1 rs₁ hU
  obtain ⟨sU, iU⟩ := hdU.1 rsL rs₁ hU
  have hrun4 : run c (compile R).checks (Prog.start s) =
      run c ((tellsT R).1 ++ (guardsG R).1) { Prog.start s with rs := rs₁ } :=
    hrun3.trans (run_seq hr1)
  have hSolU : ∀ σ, ((∀ k < R.nparams, σ k = p.getD k default) ∧
      ∀ u < R.uses.length, labelOf s (o.getD u 0) =
        some ((R.uses.getD u default).inst σ (openFresh s.names))) ↔
      Agrees σ (usesM R).2.1 ({ Prog.start s with rs := rs₁ } : Mach).rs := by
    intro σ
    constructor
    · rintro ⟨hp, hu⟩
      exact (iU σ ((hparams σ).mpr hp)).mp ((huses σ).mpr hu)
    · intro A
      have a0 : Agrees σ (paramEnv R.nparams) rsL := agrees_mono u3 hE0 sU A
      exact ⟨(hparams σ).mp a0, (huses σ).mp ((iU σ a0).mpr A)⟩
  -- the information: the tells
  obtain ⟨-, -, t3, t4, t5⟩ := tells_phase c R.tells (usesM R).2.1 (usesM R).2.2 R.boundUses
    { Prog.start s with rs := rs₁ } _ u2 (uses_binds R) hR.tells hSolU
  rcases t5 with ⟨rs₂, hT, -, iT⟩ | ⟨rs₂, hT, hnoT⟩
  swap
  · have hfin : run c (compile R).checks (Prog.start s) = (some .unsolvable, { Prog.start s with rs := rs₂ }) :=
      hrun4.trans (run_seq_stop (A := (tellsT R).1) hT)
    rw [hfin]
    refine ⟨rfl, rfl, fun r hr => ?_, fun h => by cases h⟩
    cases hr
    refine ⟨hS, hF, ?_⟩
    rintro ⟨σ, hσp, hσu, hσt⟩
    exact hnoT ⟨σ, ⟨hσp, hσu⟩, hσt⟩
  have hSol : ∀ σ, Sol R s p o σ ↔ Agrees σ (tellsT R).2.1 rs₂ := fun σ =>
    ⟨fun h => (iT σ).mp ⟨⟨h.1, h.2.1⟩, h.2.2⟩,
     fun h => ⟨((iT σ).mpr h).1.1, ((iT σ).mpr h).1.2, ((iT σ).mpr h).2⟩⟩
  have hsolv : Solvable R s p o := ⟨agreeing (tellsT R).2.1 rs₂ default,
    (hSol _).mpr (agreeing_agrees _ _ _)⟩
  have hrun5 : run c (compile R).checks (Prog.start s) =
      run c (guardsG R).1 { Prog.start s with rs := rs₂ } :=
    hrun4.trans (run_seq (A := (tellsT R).1) hT)
  -- the guards
  obtain ⟨-, g2, g3⟩ := guards_phase c host (tellsT R).2.1 (boundAfter R.boundUses R.tells) t4
    (Sol R s p o) hsolv R.guards (tellsT R).2.2 0 { Prog.start s with rs := rs₂ } t3
    (inClass_guards hR) hSol
  rcases g3 with ⟨rs₃, hG, sG, hall⟩ | ⟨j, rs₃, hG, g, hgj, hno, hbefore⟩
  · have hfin : run c (compile R).checks (Prog.start s) = (none, { Prog.start s with rs := rs₃ }) :=
      hrun5.trans hG
    rw [hfin]
    refine ⟨rfl, rfl, fun r hr => (by cases hr), fun _ => ⟨⟨hS, hF, hsolv, fun g hg => hall g hg⟩,
      t3.mono g2, fun σ => (hSol σ).trans (agrees_iff_of_sameBelow t3 sG)⟩⟩
  · have hfin : run c (compile R).checks (Prog.start s) =
        (some (.guard (0 + j)), { Prog.start s with rs := rs₃ }) := hrun5.trans hG
    rw [hfin]
    refine ⟨rfl, rfl, fun r hr => ?_, fun h => by cases h⟩
    cases hr
    rw [Nat.zero_add]
    exact ⟨hS, hF, hsolv, g, hgj, hno, hbefore⟩

/-! ## The headline theorems -/

/-- **Specialized admission decides the step's admission.** Admission alone: the verdict of the
step, the state unchanged, and the first name a firing would mint. -/
theorem specialized_admission (R : Rule) (hR : InClass R) (s : St) (p : List Tm) (o : List Nat)
    (host : String → List Tm → Prop) :
    RefVerdict R s p o host ((compile R).admits ⟨p, o⟩ s).1 ∧
    ((compile R).admits ⟨p, o⟩ s).2.1 = s ∧ ((compile R).admits ⟨p, o⟩ s).2.2 = s.names := by
  obtain ⟨c1, -, c3, c4⟩ := checks_spec R hR s p o host
  rcases h : run ⟨p, o⟩ (compile R).checks (Prog.start s) with ⟨r, m⟩
  rw [h] at c1 c3 c4
  dsimp only at c1 c3 c4
  cases r with
  | none =>
      have hadm : (compile R).admits ⟨p, o⟩ s = (.admitted, m.st, m.st.names) := by
        simp only [Prog.admits, h]
      rw [hadm]
      exact ⟨(c4 rfl).1, c1, congrArg St.names c1⟩
  | some r =>
      have hadm : (compile R).admits ⟨p, o⟩ s = (.refused r, m.st, m.st.names) := by
        simp only [Prog.admits, h]
      rw [hadm]
      exact ⟨c3 r rfl, c1, congrArg St.names c1⟩

/-- **Specialized firing.** The verdict of the step; a refusal changes nothing and makes nothing;
an admission leaves the step's result, at every solution, with the next identities made. -/
theorem specialized_firing (R : Rule) (hR : InClass R) (s : St) (p : List Tm) (o : List Nat)
    (host : String → List Tm → Prop) :
    RefVerdict R s p o host ((compile R).fire ⟨p, o⟩ s).1 ∧
    (((compile R).fire ⟨p, o⟩ s).1 ≠ .admitted →
      ((compile R).fire ⟨p, o⟩ s).2.1 = s ∧ ((compile R).fire ⟨p, o⟩ s).2.2 = []) ∧
    (((compile R).fire ⟨p, o⟩ s).1 = .admitted →
      (∀ σ, Sol R s p o σ → ((compile R).fire ⟨p, o⟩ s).2.1 = Result R s o σ) ∧
      ((compile R).fire ⟨p, o⟩ s).2.2 = List.range' s.nextId R.makes.length) := by
  obtain ⟨c1, c2, c3, c4⟩ := checks_spec R hR s p o host
  rcases h : run ⟨p, o⟩ (compile R).checks (Prog.start s) with ⟨r, m⟩
  rw [h] at c1 c2 c3 c4
  dsimp only at c1 c2 c3 c4
  cases r with
  | some r =>
      have hfire : (compile R).fire ⟨p, o⟩ s = (.refused r, m.st, m.made) := by
        simp only [Prog.fire, h]
      rw [hfire]
      exact ⟨c3 r rfl, fun _ => ⟨c1, c2⟩, fun h' => by cases h'⟩
  | none =>
      obtain ⟨hadm, hbelow, hsol⟩ := c4 rfl
      obtain ⟨σ₀, hσ₀⟩ := hadm.2.2.1
      have hloc : ∀ t ∈ R.makes, ∀ x, Tm.loc x ∈ t.atoms → ((tellsT R).2.1 x).isSome = true := by
        intro t ht x hx
        have hb := (tells_phase ⟨p, o⟩ R.tells (usesM R).2.1 (usesM R).2.2 R.boundUses
          (Prog.start s) (fun σ => Agrees σ (usesM R).2.1 (Prog.start s).rs)
          (cmList_static R.uses (paramEnv R.nparams) (R.nparams + R.uses.length) R.nparams
            (Nat.le_refl _) (paramEnv_below _ _ (Nat.le_add_right _ _))).2.1
          (uses_binds R) hR.tells (fun _ => Iff.rfl)).2.2.2.1 x
        exact hb.mpr (hR.makes t ht x (Tm.mem_locals.mpr hx))
      obtain ⟨m', hrun, hmade, -⟩ :=
        commit_phase ⟨p, o⟩ R (tellsT R).2.1 (guardsG R).2 m σ₀ hbelow hloc ((hsol σ₀).mp hσ₀)
      have hc : run ⟨p, o⟩ (compile R).commit m = (none, m') := hrun
      have hfire : (compile R).fire ⟨p, o⟩ s = (.admitted, m'.st, m'.made) := by
        simp only [Prog.fire, h, hc]
      rw [hfire]
      refine ⟨hadm, fun h' => absurd rfl h', fun _ => ⟨fun σ hσ => ?_, ?_⟩⟩
      · obtain ⟨m'', hrun', -, hst⟩ :=
          commit_phase ⟨p, o⟩ R (tellsT R).2.1 (guardsG R).2 m σ hbelow hloc ((hsol σ).mp hσ)
        rw [hrun] at hrun'
        cases hrun'
        rw [hst, c1]
        rfl
      · simp only [hmade, c2, c1, List.nil_append]

/-! ## The class and the hand-off -/

theorem tellsInOrderB_iff : ∀ (b : List Nat) (es : List (Tm × Tm)),
    tellsInOrderB b es = true ↔ TellsInOrder b es
  | _, [] => by simp [tellsInOrderB, TellsInOrder]
  | b, e :: es => by
      simp only [tellsInOrderB, TellsInOrder, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
        decide_eq_true_eq, tellsInOrderB_iff (b ++ e.1.locals ++ e.2.locals) es]

/-- **The decided class is the class.** -/
theorem inClassB_iff (R : Rule) : R.inClassB = true ↔ InClass R := by
  simp only [Rule.inClassB, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, tellsInOrderB_iff,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨hv, ha⟩, ht⟩, hm⟩, hg⟩
    refine ⟨fun t ht' i hi => ?_, ha, fun g hg' => ?_, ht, hm, fun a b hab => ?_⟩
    · have := hv t ht' _ hi
      simp at this
    · have := hg g hg'
      cases g <;> simp_all [Guard.inClassB, Guard.isHost]
    · have := hg _ hab
      simp only [Guard.inClassB, List.all_eq_true, decide_eq_true_eq] at this
      exact this
  · rintro ⟨hv, ha, hh, ht, hm, has⟩
    refine ⟨⟨⟨⟨fun t ht' a ha' => ?_, ha⟩, ht⟩, hm⟩, fun g hg => ?_⟩
    · cases a with
      | var i => exact absurd ha' (hv t ht' i)
      | _ => rfl
    · cases g with
      | ask a b =>
          simp only [Guard.inClassB, List.all_eq_true, decide_eq_true_eq]
          exact has a b hg
      | absent q => rfl
      | count q n => rfl
      | host h args => exact absurd (hh _ hg) (by simp [Guard.isHost])

/-- **The specializer returns a program exactly for the rules of the class.** -/
theorem specialize_isSome_iff (R : Rule) : (specialize R).isSome = true ↔ InClass R := by
  unfold specialize
  rw [← inClassB_iff]
  cases R.inClassB <;> simp

theorem specialize_eq_some {R : Rule} {P : Prog} (h : specialize R = some P) :
    P = compile R ∧ InClass R := by
  unfold specialize at h
  by_cases hc : R.inClassB = true
  · rw [if_pos hc] at h
    exact ⟨(Option.some.inj h).symm, (inClassB_iff R).mp hc⟩
  · rw [if_neg hc] at h
    cases h

/-- The specialized fragment: a rule of the class, a frame with no variables and no live
disequations, closed parameters. -/
def InFragment (R : Rule) (s : St) (p : List Tm) : Prop :=
  InClass R ∧ s.vars = 0 ∧ s.diseqs = 0 ∧ ∀ q ∈ p, q.closed = true

theorem dispatch_specialized_iff (R : Rule) (s : St) (p : List Tm) (P : Prog) :
    dispatch R s p = .specialized P ↔ InFragment R s p ∧ P = compile R := by
  unfold dispatch specialize InFragment
  by_cases hc : R.inClassB = true
  · have hi := (inClassB_iff R).mp hc
    rw [if_pos hc]
    by_cases hs : s.vars = 0 ∧ s.diseqs = 0 ∧ p.all Tm.closed = true
    · simp only [if_pos hs]
      have hs' := hs
      simp only [List.all_eq_true] at hs'
      constructor
      · intro h
        cases h
        exact ⟨⟨hi, hs'.1, hs'.2.1, hs'.2.2⟩, rfl⟩
      · rintro ⟨-, rfl⟩
        rfl
    · simp only [if_neg hs]
      constructor
      · intro h
        cases h
      · rintro ⟨⟨-, h1, h2, h3⟩, -⟩
        exact absurd ⟨h1, h2, List.all_eq_true.mpr h3⟩ hs
  · have hi : ¬ InClass R := fun h => hc ((inClassB_iff R).mpr h)
    rw [if_neg hc]
    constructor
    · intro h
      cases h
    · rintro ⟨⟨h, -⟩, -⟩
      exact absurd h hi

/-- **The hand-off is exactly the complement of the fragment.** -/
theorem dispatch_generic_iff (R : Rule) (s : St) (p : List Tm) :
    dispatch R s p = .generic ↔ ¬ InFragment R s p := by
  constructor
  · intro h hf
    have := (dispatch_specialized_iff R s p (compile R)).mpr ⟨hf, rfl⟩
    rw [h] at this
    cases this
  · intro hf
    cases hd : dispatch R s p with
    | generic => rfl
    | specialized P => exact absurd ((dispatch_specialized_iff R s p P).mp hd).1 hf

/-- **What the dispatcher runs is correct.** -/
theorem dispatch_correct {R : Rule} {s : St} {p : List Tm} {P : Prog}
    (h : dispatch R s p = .specialized P) (o : List Nat) (host : String → List Tm → Prop) :
    RefVerdict R s p o host (P.fire ⟨p, o⟩ s).1 ∧
    ((P.fire ⟨p, o⟩ s).1 ≠ .admitted → (P.fire ⟨p, o⟩ s).2.1 = s ∧ (P.fire ⟨p, o⟩ s).2.2 = []) ∧
    ((P.fire ⟨p, o⟩ s).1 = .admitted →
      (∀ σ, Sol R s p o σ → (P.fire ⟨p, o⟩ s).2.1 = Result R s o σ) ∧
      (P.fire ⟨p, o⟩ s).2.2 = List.range' s.nextId R.makes.length) := by
  obtain ⟨⟨hR, -⟩, rfl⟩ := (dispatch_specialized_iff R s p P).mp h
  exact specialized_firing R hR s p o host

#print axioms specialized_admission
#print axioms specialized_firing
#print axioms specialize_isSome_iff
#print axioms dispatch_generic_iff
#print axioms dispatch_correct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
