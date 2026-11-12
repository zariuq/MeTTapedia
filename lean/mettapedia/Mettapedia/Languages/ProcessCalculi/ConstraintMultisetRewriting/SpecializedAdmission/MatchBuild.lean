import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Specializer

/-!
# Matching and building are correct

* `cm_dyn`: the match code of a pattern, run against a register, succeeds exactly when the pattern
  has an instance equal to the register's term at an assignment that agrees with what is bound so
  far; on success the new bindings are forced: an assignment that agrees with the old bindings
  solves the pattern exactly when it agrees with the new ones. `cm_static` gives the shape of the
  environment after it: what is bound is what was bound and the locals of the pattern.
* `cb_spec`: the build code of a term whose locals are bound leaves, in its register, the term's
  value at every agreeing assignment.

Registers are written above the compiler's high-water mark only (`SameBelow`), so a binding, once
made, keeps its register.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission

/-! ## Registers and environments -/

/-- `σ` gives each bound local the term its register holds. -/
def Agrees (σ : Nat → Tm) (E : Env) (rs : Regs) : Prop := ∀ x r, E x = some r → σ x = rs r

/-- Every bound local is held below `n`. -/
def EnvBelow (E : Env) (n : Nat) : Prop := ∀ x r, E x = some r → r < n

/-- `E'` keeps every binding of `E`. -/
def EnvLe (E E' : Env) : Prop := ∀ x r, E x = some r → E' x = some r

/-- The registers below `n` are unchanged. -/
def SameBelow (rs rs' : Regs) (n : Nat) : Prop := ∀ i < n, rs' i = rs i

theorem EnvLe.refl (E : Env) : EnvLe E E := fun _ _ h => h

theorem EnvLe.trans {E₁ E₂ E₃ : Env} (h₁ : EnvLe E₁ E₂) (h₂ : EnvLe E₂ E₃) : EnvLe E₁ E₃ :=
  fun x r h => h₂ x r (h₁ x r h)

theorem EnvBelow.mono {E : Env} {n m : Nat} (h : EnvBelow E n) (hnm : n ≤ m) : EnvBelow E m :=
  fun x r hx => Nat.lt_of_lt_of_le (h x r hx) hnm

theorem SameBelow.refl (rs : Regs) (n : Nat) : SameBelow rs rs n := fun _ _ => rfl

theorem SameBelow.trans {rs₁ rs₂ rs₃ : Regs} {n m : Nat} (h₁ : SameBelow rs₁ rs₂ n)
    (h₂ : SameBelow rs₂ rs₃ m) (hnm : n ≤ m) : SameBelow rs₁ rs₃ n :=
  fun i hi => (h₂ i (Nat.lt_of_lt_of_le hi hnm)).trans (h₁ i hi)

theorem SameBelow.mono {rs rs' : Regs} {n m : Nat} (h : SameBelow rs rs' m) (hnm : n ≤ m) :
    SameBelow rs rs' n :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hnm)

theorem agrees_iff_of_sameBelow {σ : Nat → Tm} {E : Env} {rs rs' : Regs} {n : Nat}
    (hE : EnvBelow E n) (h : SameBelow rs rs' n) : Agrees σ E rs ↔ Agrees σ E rs' :=
  ⟨fun a x r hx => (a x r hx).trans (h r (hE x r hx)).symm,
   fun a x r hx => (a x r hx).trans (h r (hE x r hx))⟩

theorem agrees_mono {σ : Nat → Tm} {E E' : Env} {rs rs' : Regs} {n : Nat} (hle : EnvLe E E')
    (hE : EnvBelow E n) (h : SameBelow rs rs' n) (a : Agrees σ E' rs') : Agrees σ E rs :=
  fun x r hx => (a x r (hle x r hx)).trans (h r (hE x r hx))

/-- The assignment that reads the bound locals from the registers, and the others from `σ₀`. -/
def agreeing (E : Env) (rs : Regs) (σ₀ : Nat → Tm) : Nat → Tm := fun x =>
  match E x with
  | some r => rs r
  | none => σ₀ x

theorem agreeing_agrees (E : Env) (rs : Regs) (σ₀ : Nat → Tm) : Agrees (agreeing E rs σ₀) E rs := by
  intro x r hx
  simp [agreeing, hx]

theorem Regs.write_same (rs : Regs) (d : Nat) (v : Tm) : rs.write d v d = v := by
  simp [Regs.write]

theorem Regs.write_other (rs : Regs) {d i : Nat} (v : Tm) (h : i ≠ d) : rs.write d v i = rs i := by
  simp [Regs.write, h]

theorem write_sameBelow (rs : Regs) {d n : Nat} (v : Tm) (h : n ≤ d) :
    SameBelow rs (rs.write d v) n :=
  fun _ hi => Regs.write_other rs v (by omega)

theorem writeList_sameBelow : ∀ (rs : Regs) (d : Nat) (vs : List Tm) {n : Nat}, n ≤ d →
    SameBelow rs (rs.writeList d vs) n
  | rs, _, [], n, _ => SameBelow.refl rs n
  | rs, d, v :: vs, n, h =>
      SameBelow.trans (write_sameBelow rs v h)
        (writeList_sameBelow (rs.write d v) (d + 1) vs (n := n) (by omega)) (Nat.le_refl _)

/-- The patterns `ts`, at `σ`, are the terms in registers `src`, `src + 1`, .... -/
def MatchL (σ φ : Nat → Tm) (rs : Regs) : Nat → List Tm → Prop
  | _, [] => True
  | src, t :: ts => t.inst σ φ = rs src ∧ MatchL σ φ rs (src + 1) ts

theorem matchL_sameBelow {σ φ : Nat → Tm} : ∀ (ts : List Tm) (rs rs' : Regs) (src n : Nat),
    src + ts.length ≤ n → SameBelow rs rs' n → (MatchL σ φ rs src ts ↔ MatchL σ φ rs' src ts)
  | [], _, _, _, _, _, _ => Iff.rfl
  | t :: ts, rs, rs', src, n, hlen, h => by
      have hl : src + 1 + ts.length ≤ n := by simp only [List.length_cons] at hlen; omega
      simp only [MatchL]
      rw [h src (by omega), matchL_sameBelow ts rs rs' (src + 1) n hl h]

theorem matchL_writeList {σ φ : Nat → Tm} : ∀ (ts vs : List Tm) (rs : Regs) (d : Nat),
    ts.length = vs.length → (MatchL σ φ (rs.writeList d vs) d ts ↔ ts.map (Tm.inst σ φ) = vs)
  | [], [], _, _, _ => by simp [MatchL]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | t :: ts, v :: vs, rs, d, h => by
      have hl : ts.length = vs.length := by simpa using h
      have ih := matchL_writeList (σ := σ) (φ := φ) ts vs (rs.write d v) (d + 1) hl
      have hd : (rs.writeList d (v :: vs)) d = v := by
        show ((rs.write d v).writeList (d + 1) vs) d = v
        rw [writeList_sameBelow (rs.write d v) (d + 1) vs (n := d + 1) (Nat.le_refl _) d (Nat.lt_succ_self d)]
        exact Regs.write_same rs d v
      show (t.inst σ φ = (rs.writeList d (v :: vs)) d ∧
          MatchL σ φ ((rs.write d v).writeList (d + 1) vs) (d + 1) ts) ↔ _
      rw [hd, ih, List.map_cons, List.cons.injEq]

/-! ## Runs of match code -/

theorem MInstr.run_append (names : Nat) : ∀ (A B : List MInstr) (rs : Regs),
    MInstr.run names (A ++ B) rs = (MInstr.run names A rs).bind (MInstr.run names B)
  | [], _, _ => rfl
  | i :: is, B, rs => by
      rcases h : MInstr.exec names rs i with _ | rs'
      · simp only [List.cons_append, MInstr.run, h, Option.bind_none]
      · simp only [List.cons_append, MInstr.run, h]
        exact MInstr.run_append names is B rs'

theorem MInstr.run_single (names : Nat) (i : MInstr) (rs : Regs) :
    MInstr.run names [i] rs = MInstr.exec names rs i := by
  rcases h : MInstr.exec names rs i with _ | r <;> simp [MInstr.run, h]

theorem MInstr.run_cons_some {names : Nat} {i : MInstr} {is : List MInstr} {rs rs' : Regs}
    (h : MInstr.run names (i :: is) rs = some rs') :
    ∃ rs₁, MInstr.exec names rs i = some rs₁ ∧ MInstr.run names is rs₁ = some rs' := by
  rcases h1 : MInstr.exec names rs i with _ | rs₁
  · simp [MInstr.run, h1] at h
  · simp only [MInstr.run, h1] at h
    exact ⟨rs₁, rfl, h⟩

theorem MInstr.run_cons_none {names : Nat} {i : MInstr} {is : List MInstr} {rs : Regs}
    (h : MInstr.run names (i :: is) rs = none) :
    MInstr.exec names rs i = none ∨
      ∃ rs₁, MInstr.exec names rs i = some rs₁ ∧ MInstr.run names is rs₁ = none := by
  rcases h1 : MInstr.exec names rs i with _ | rs₁
  · exact Or.inl rfl
  · simp only [MInstr.run, h1] at h
    exact Or.inr ⟨rs₁, rfl, h⟩

theorem getApp_some {names : Nat} {rs rs₁ : Regs} {src f len dst : Nat}
    (h : MInstr.exec names rs (.getApp src f len dst) = some rs₁) :
    ∃ vs, rs src = .app f vs ∧ vs.length = len ∧ rs₁ = rs.writeList dst vs := by
  cases hv : rs src with
  | app g vs =>
      simp only [MInstr.exec, hv] at h
      split at h
      · rename_i hg
        obtain ⟨rfl, hl⟩ := hg
        exact ⟨vs, rfl, hl, (Option.some.inj h).symm⟩
      · cases h
  | code _ => simp [MInstr.exec, hv] at h
  | name _ => simp [MInstr.exec, hv] at h
  | var _ => simp [MInstr.exec, hv] at h
  | loc _ => simp [MInstr.exec, hv] at h
  | fresh _ => simp [MInstr.exec, hv] at h

theorem getApp_none {names : Nat} {rs : Regs} {src f len dst : Nat}
    (h : MInstr.exec names rs (.getApp src f len dst) = none) (vs : List Tm)
    (hv : rs src = .app f vs) : vs.length ≠ len := by
  intro hl
  simp [MInstr.exec, hv, hl] at h

/-- A single test: on success the registers are unchanged and `P` holds at every agreeing
assignment; on failure it holds at none. -/
theorem leaf_dyn {names : Nat} {E : Env} {n : Nat} (i : MInstr) (Q : Regs → Prop)
    [DecidablePred Q] (P : (Nat → Tm) → Regs → Prop)
    (hexec : ∀ rs, MInstr.exec names rs i = if Q rs then some rs else none)
    (hP : ∀ σ rs, Agrees σ E rs → (P σ rs ↔ Q rs)) :
    (∀ rs rs', MInstr.run names [i] rs = some rs' → SameBelow rs rs' n ∧
        ∀ σ, Agrees σ E rs → (P σ rs ↔ Agrees σ E rs')) ∧
    (∀ rs, MInstr.run names [i] rs = none → ∀ σ, Agrees σ E rs → ¬ P σ rs) := by
  constructor
  · intro rs rs' h
    rw [MInstr.run_single, hexec] at h
    split at h
    · rename_i hq
      cases h
      exact ⟨SameBelow.refl _ _, fun σ a => ⟨fun _ => a, fun _ => (hP σ rs a).mpr hq⟩⟩
    · cases h
  · intro rs h σ a hp
    rw [MInstr.run_single, hexec] at h
    split at h
    · cases h
    · rename_i hq
      exact hq ((hP σ rs a).mp hp)

/-! ## The compiler's equations -/

theorem cm_app (E : Env) (n src f : Nat) (args : List Tm) : cm E n src (.app f args) =
    if (Tm.app f args).closed then ([.eqConst src (.app f args)], E, n)
    else (.getApp src f args.length n :: (cmList E (n + args.length) n args).1,
      (cmList E (n + args.length) n args).2.1, (cmList E (n + args.length) n args).2.2) := rfl
theorem cm_code (E : Env) (n src : Nat) (c : Int) :
    cm E n src (.code c) = ([.eqConst src (.code c)], E, n) := rfl
theorem cm_name (E : Env) (n src m : Nat) :
    cm E n src (.name m) = ([.eqConst src (.name m)], E, n) := rfl
theorem cm_var (E : Env) (n src i : Nat) :
    cm E n src (.var i) = ([.eqConst src (.var i)], E, n) := rfl
theorem cm_fresh (E : Env) (n src j : Nat) :
    cm E n src (.fresh j) = ([.eqFresh src j], E, n) := rfl
theorem cm_loc (E : Env) (n src x : Nat) : cm E n src (.loc x) =
    match E x with
    | some r => ([.eqReg src r], E, n)
    | none => ([], E.bind x src, n) := rfl
theorem cmList_nil (E : Env) (n src : Nat) : cmList E n src [] = ([], E, n) := rfl
theorem cmList_cons (E : Env) (n src : Nat) (t : Tm) (ts : List Tm) : cmList E n src (t :: ts) =
    ((cm E n src t).1 ++ (cmList (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) ts).1,
      (cmList (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) ts).2.1,
      (cmList (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) ts).2.2) := rfl

theorem not_loc_of_closed {t : Tm} (h : t.closed = true) (x : Nat) : Tm.loc x ∉ t.atoms := by
  intro hx
  have := List.all_eq_true.mp h _ hx
  simp [Tm.rigidAtom] at this

/-! ## Matching: the environment -/

mutual
theorem cm_static : ∀ (t : Tm) (E : Env) (n src : Nat), src < n → EnvBelow E n →
    n ≤ (cm E n src t).2.2 ∧ EnvBelow (cm E n src t).2.1 (cm E n src t).2.2 ∧
      EnvLe E (cm E n src t).2.1 ∧
      ∀ x, ((cm E n src t).2.1 x).isSome = true ↔ (E x).isSome = true ∨ Tm.loc x ∈ t.atoms
  | .app f args, E, n, src, _, hE => by
      rw [cm_app]
      cases hc : (Tm.app f args).closed
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨h1, h2, h3, h4⟩ :=
          cmList_static args E (n + args.length) n (by omega) (hE.mono (by omega))
        refine ⟨by omega, h2, h3, fun x => ?_⟩
        rw [h4 x]
        simp only [Tm.atoms]
      · simp only [↓reduceIte]
        refine ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => ?_⟩
        simp only [not_loc_of_closed hc x, or_false]
  | .code c, E, n, _, _, hE => by
      dsimp only [cm_code]
      exact ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => by simp⟩
  | .name m, E, n, _, _, hE => by
      dsimp only [cm_name]
      exact ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => by simp⟩
  | .var i, E, n, _, _, hE => by
      dsimp only [cm_var]
      exact ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => by simp⟩
  | .fresh j, E, n, _, _, hE => by
      dsimp only [cm_fresh]
      exact ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => by simp⟩
  | .loc y, E, n, src, hsrc, hE => by
      rw [cm_loc]
      cases hy : E y with
      | some r =>
          refine ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => ?_⟩
          simp only [Tm.atoms_loc, List.mem_singleton, Tm.loc.injEq]
          constructor
          · exact Or.inl
          · rintro (h | rfl)
            · exact h
            · simp [hy]
      | none =>
          refine ⟨(Nat.le_refl _), ?_, ?_, fun x => ?_⟩
          · intro x r hx
            simp only [Env.bind] at hx
            split at hx
            · cases hx
              exact hsrc
            · exact hE x r hx
          · intro x r hx
            simp only [Env.bind]
            split
            · rename_i hxy
              subst hxy
              rw [hy] at hx
              cases hx
            · exact hx
          · simp only [Env.bind, Tm.atoms_loc, List.mem_singleton, Tm.loc.injEq]
            split
            · rename_i hxy
              simp [hxy]
            · rename_i hxy
              simp [hxy]
theorem cmList_static : ∀ (ts : List Tm) (E : Env) (n src : Nat), src + ts.length ≤ n →
    EnvBelow E n →
    n ≤ (cmList E n src ts).2.2 ∧ EnvBelow (cmList E n src ts).2.1 (cmList E n src ts).2.2 ∧
      EnvLe E (cmList E n src ts).2.1 ∧
      ∀ x, ((cmList E n src ts).2.1 x).isSome = true ↔
        (E x).isSome = true ∨ Tm.loc x ∈ Tm.atomsList ts
  | [], E, n, _, _, hE => by
      dsimp only [cmList_nil]
      exact ⟨(Nat.le_refl _), hE, EnvLe.refl E, fun x => by simp [Tm.atomsList]⟩
  | t :: ts, E, n, src, hlen, hE => by
      dsimp only [cmList_cons]
      have hl : src + 1 + ts.length ≤ n := by simp only [List.length_cons] at hlen; omega
      obtain ⟨a1, a2, a3, a4⟩ := cm_static t E n src (by omega) hE
      obtain ⟨b1, b2, b3, b4⟩ :=
        cmList_static ts (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) (by omega) a2
      refine ⟨by omega, b2, a3.trans b3, fun x => ?_⟩
      rw [b4 x, a4 x]
      simp only [Tm.atomsList, List.mem_append, or_assoc]
end

/-! ## Matching: the runs -/

mutual
theorem cm_dyn (names : Nat) : ∀ (t : Tm) (E : Env) (n src : Nat), src < n → EnvBelow E n →
    (∀ rs rs', MInstr.run names (cm E n src t).1 rs = some rs' → SameBelow rs rs' n ∧
        ∀ σ, Agrees σ E rs →
          (t.inst σ (openFresh names) = rs src ↔ Agrees σ (cm E n src t).2.1 rs')) ∧
    (∀ rs, MInstr.run names (cm E n src t).1 rs = none →
        ∀ σ, Agrees σ E rs → t.inst σ (openFresh names) ≠ rs src)
  | .app f args, E, n, src, _, hE => by
      rw [cm_app]
      cases hc : (Tm.app f args).closed
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have ih := cmList_dyn names args E (n + args.length) n (by omega) (hE.mono (by omega))
        constructor
        · intro rs rs' h
          obtain ⟨rs₁, h1, h2⟩ := MInstr.run_cons_some h
          obtain ⟨vs, hv, hl, rfl⟩ := getApp_some h1
          obtain ⟨hsame, hiff⟩ := ih.1 _ _ h2
          refine ⟨SameBelow.trans (writeList_sameBelow rs n vs (Nat.le_refl _)) hsame (by omega), fun σ a => ?_⟩
          have a₁ : Agrees σ E (rs.writeList n vs) :=
            (agrees_iff_of_sameBelow hE (writeList_sameBelow rs n vs (Nat.le_refl _))).mp a
          rw [← hiff σ a₁, matchL_writeList args vs rs n hl.symm, Tm.inst_app, hv, Tm.app.injEq]
          simp
        · intro rs h σ a heq
          rcases MInstr.run_cons_none h with h1 | ⟨rs₁, h1, h2⟩
          · rw [Tm.inst_app] at heq
            exact getApp_none h1 _ heq.symm (by simp)
          · obtain ⟨vs, hv, hl, rfl⟩ := getApp_some h1
            have a₁ : Agrees σ E (rs.writeList n vs) :=
              (agrees_iff_of_sameBelow hE (writeList_sameBelow rs n vs (Nat.le_refl _))).mp a
            apply ih.2 _ h2 σ a₁
            rw [matchL_writeList args vs rs n hl.symm]
            rw [Tm.inst_app, hv, Tm.app.injEq] at heq
            exact heq.2
      · simp only [↓reduceIte]
        exact leaf_dyn (.eqConst src (.app f args)) (fun rs => rs src = .app f args)
          (fun σ rs => (Tm.app f args).inst σ (openFresh names) = rs src) (fun _ => rfl)
          (fun σ rs _ => by rw [Tm.inst_closed hc]; exact eq_comm)
  | .code c, E, n, src, _, _ => by
      dsimp only [cm_code]
      exact leaf_dyn (.eqConst src (.code c)) (fun rs => rs src = .code c)
        (fun σ rs => (Tm.code c).inst σ (openFresh names) = rs src) (fun _ => rfl)
        (fun σ rs _ => eq_comm)
  | .name m, E, n, src, _, _ => by
      dsimp only [cm_name]
      exact leaf_dyn (.eqConst src (.name m)) (fun rs => rs src = .name m)
        (fun σ rs => (Tm.name m).inst σ (openFresh names) = rs src) (fun _ => rfl)
        (fun σ rs _ => eq_comm)
  | .var i, E, n, src, _, _ => by
      dsimp only [cm_var]
      exact leaf_dyn (.eqConst src (.var i)) (fun rs => rs src = .var i)
        (fun σ rs => (Tm.var i).inst σ (openFresh names) = rs src) (fun _ => rfl)
        (fun σ rs _ => eq_comm)
  | .fresh j, E, n, src, _, _ => by
      dsimp only [cm_fresh]
      exact leaf_dyn (.eqFresh src j) (fun rs => rs src = .name (names + j))
        (fun σ rs => (Tm.fresh j).inst σ (openFresh names) = rs src) (fun _ => rfl)
        (fun σ rs _ => eq_comm)
  | .loc y, E, n, src, hsrc, hE => by
      rw [cm_loc]
      cases hy : E y with
      | some r =>
          exact leaf_dyn (.eqReg src r) (fun rs => rs src = rs r)
            (fun σ rs => (Tm.loc y).inst σ (openFresh names) = rs src) (fun _ => rfl)
            (fun σ rs a => by
              show σ y = rs src ↔ rs src = rs r
              rw [a y r hy]
              exact eq_comm)
      | none =>
          constructor
          · intro rs rs' h
            simp only [MInstr.run, Option.some.injEq] at h
            subst h
            refine ⟨SameBelow.refl _ _, fun σ a => ?_⟩
            show σ y = rs src ↔ Agrees σ (E.bind y src) rs
            constructor
            · intro hσ x r hx
              simp only [Env.bind] at hx
              split at hx
              · rename_i hxy
                cases hx
                rw [hxy]
                exact hσ
              · exact a x r hx
            · intro A
              exact A y src (by simp [Env.bind])
          · intro rs h
            simp [MInstr.run] at h
theorem cmList_dyn (names : Nat) : ∀ (ts : List Tm) (E : Env) (n src : Nat),
    src + ts.length ≤ n → EnvBelow E n →
    (∀ rs rs', MInstr.run names (cmList E n src ts).1 rs = some rs' → SameBelow rs rs' n ∧
        ∀ σ, Agrees σ E rs →
          (MatchL σ (openFresh names) rs src ts ↔ Agrees σ (cmList E n src ts).2.1 rs')) ∧
    (∀ rs, MInstr.run names (cmList E n src ts).1 rs = none →
        ∀ σ, Agrees σ E rs → ¬ MatchL σ (openFresh names) rs src ts)
  | [], E, n, src, _, _ => by
      dsimp only [cmList_nil]
      constructor
      · intro rs rs' h
        simp only [MInstr.run, Option.some.injEq] at h
        subst h
        exact ⟨SameBelow.refl _ _, fun σ a => ⟨fun _ => a, fun _ => trivial⟩⟩
      · intro rs h
        simp [MInstr.run] at h
  | t :: ts, E, n, src, hlen, hE => by
      dsimp only [cmList_cons]
      have hl : src + 1 + ts.length ≤ n := by simp only [List.length_cons] at hlen; omega
      obtain ⟨a1, a2, a3, -⟩ := cm_static t E n src (by omega) hE
      obtain ⟨-, -, b3, -⟩ :=
        cmList_static ts (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) (by omega) a2
      have iha := cm_dyn names t E n src (by omega) hE
      have ihb := cmList_dyn names ts (cm E n src t).2.1 (cm E n src t).2.2 (src + 1) (by omega) a2
      constructor
      · intro rs rs' h
        rw [MInstr.run_append] at h
        rcases ha : MInstr.run names (cm E n src t).1 rs with _ | rsa
        · simp [ha] at h
        · simp only [ha, Option.bind_some] at h
          obtain ⟨sa, ia⟩ := iha.1 rs rsa ha
          obtain ⟨sb, ib⟩ := ihb.1 rsa rs' h
          refine ⟨SameBelow.trans sa sb a1, fun σ a => ?_⟩
          have hm : MatchL σ (openFresh names) rs (src + 1) ts ↔
              MatchL σ (openFresh names) rsa (src + 1) ts := matchL_sameBelow ts rs rsa (src + 1) n hl sa
          show (t.inst σ (openFresh names) = rs src ∧ MatchL σ (openFresh names) rs (src + 1) ts) ↔ _
          constructor
          · rintro ⟨h1, h2⟩
            have aa := (ia σ a).mp h1
            exact (ib σ aa).mp (hm.mp h2)
          · intro A
            have aa : Agrees σ (cm E n src t).2.1 rsa := agrees_mono b3 a2 sb A
            exact ⟨(ia σ a).mpr aa, hm.mpr ((ib σ aa).mpr A)⟩
      · intro rs h σ a
        rw [MInstr.run_append] at h
        rcases ha : MInstr.run names (cm E n src t).1 rs with _ | rsa
        · rintro ⟨h1, -⟩
          exact iha.2 rs ha σ a h1
        · simp only [ha, Option.bind_some] at h
          obtain ⟨sa, ia⟩ := iha.1 rs rsa ha
          rintro ⟨h1, h2⟩
          have aa := (ia σ a).mp h1
          exact ihb.2 rsa h σ aa ((matchL_sameBelow ts rs rsa (src + 1) n hl sa).mp h2)
end

/-! ## Building -/

theorem cb_app (E : Env) (n f : Nat) (args : List Tm) : cb E n (.app f args) =
    if (Tm.app f args).closed then ([.loadConst n (.app f args)], n + 1, n)
    else ((cbList E n args).1 ++ [.mkApp (cbList E n args).2.1 f (cbList E n args).2.2],
      (cbList E n args).2.1 + 1, (cbList E n args).2.1) := rfl
theorem cb_code (E : Env) (n : Nat) (c : Int) : cb E n (.code c) = ([.loadConst n (.code c)], n + 1, n) := rfl
theorem cb_name (E : Env) (n m : Nat) : cb E n (.name m) = ([.loadConst n (.name m)], n + 1, n) := rfl
theorem cb_var (E : Env) (n i : Nat) : cb E n (.var i) = ([.loadConst n (.var i)], n + 1, n) := rfl
theorem cb_fresh (E : Env) (n j : Nat) : cb E n (.fresh j) = ([.loadFresh n j], n + 1, n) := rfl
theorem cb_loc (E : Env) (n x : Nat) : cb E n (.loc x) =
    match E x with
    | some r => ([], n, r)
    | none => ([.loadConst n default], n + 1, n) := rfl
theorem cbList_nil (E : Env) (n : Nat) : cbList E n [] = ([], n, []) := rfl
theorem cbList_cons (E : Env) (n : Nat) (t : Tm) (ts : List Tm) : cbList E n (t :: ts) =
    ((cb E n t).1 ++ (cbList E (cb E n t).2.1 ts).1, (cbList E (cb E n t).2.1 ts).2.1,
      (cb E n t).2.2 :: (cbList E (cb E n t).2.1 ts).2.2) := rfl

/-- One load. -/
theorem run_load (c : Ctx) (m : Mach) (i : Instr) (rs' : Regs) (h : i.exec c m = .ok { m with rs := rs' }) :
    run c [i] m = (none, { m with rs := rs' }) := by
  simp only [run, h]

mutual
theorem cb_spec (c : Ctx) : ∀ (t : Tm) (E : Env) (n : Nat), EnvBelow E n →
    (∀ x, Tm.loc x ∈ t.atoms → (E x).isSome = true) →
    (cb E n t).2.2 < (cb E n t).2.1 ∧ n ≤ (cb E n t).2.1 ∧ (∀ i ∈ (cb E n t).1, i.pure = true) ∧
    ∀ m : Mach, ∃ rs', run c (cb E n t).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
      ∀ σ, Agrees σ E m.rs → rs' (cb E n t).2.2 = t.inst σ (openFresh m.st.names)
  | .app f args, E, n, hE, hloc => by
      rw [cb_app]
      cases hc : (Tm.app f args).closed
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨l1, l2, l3, l4, l5⟩ :=
          cbList_spec c args E n hE (fun x hx => hloc x (by simpa only [Tm.atoms] using hx))
        refine ⟨by omega, by omega, ?_, fun m => ?_⟩
        · intro i hi
          rcases List.mem_append.mp hi with hi | hi
          · exact l4 i hi
          · simp only [List.mem_singleton] at hi
            subst hi
            rfl
        · obtain ⟨rs₁, r1, s1, v1⟩ := l5 m
          refine ⟨rs₁.write (cbList E n args).2.1 (.app f ((cbList E n args).2.2.map rs₁)), ?_, ?_, ?_⟩
          · rw [run_append, r1]
            exact run_load c _ _ _ rfl
          · exact SameBelow.trans s1 (write_sameBelow rs₁ _ l3) (Nat.le_refl _)
          · intro σ a
            rw [Regs.write_same, v1 σ a, Tm.inst_app]
      · simp only [↓reduceIte]
        refine ⟨by omega, by omega, fun i hi => ?_, fun m => ⟨m.rs.write n (.app f args), ?_, ?_, ?_⟩⟩
        · simp only [List.mem_singleton] at hi
          subst hi
          rfl
        · exact run_load c _ _ _ rfl
        · exact write_sameBelow m.rs _ (Nat.le_refl _)
        · intro σ _
          rw [Regs.write_same, Tm.inst_closed hc]
  | .code k, E, n, _, _ => by
      dsimp only [cb_code]
      refine ⟨by omega, by omega, fun i hi => ?_, fun m => ⟨m.rs.write n (.code k), run_load c _ _ _ rfl,
        write_sameBelow m.rs _ (Nat.le_refl _), fun σ _ => by rw [Regs.write_same]; rfl⟩⟩
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  | .name k, E, n, _, _ => by
      dsimp only [cb_name]
      refine ⟨by omega, by omega, fun i hi => ?_, fun m => ⟨m.rs.write n (.name k), run_load c _ _ _ rfl,
        write_sameBelow m.rs _ (Nat.le_refl _), fun σ _ => by rw [Regs.write_same]; rfl⟩⟩
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  | .var k, E, n, _, _ => by
      dsimp only [cb_var]
      refine ⟨by omega, by omega, fun i hi => ?_, fun m => ⟨m.rs.write n (.var k), run_load c _ _ _ rfl,
        write_sameBelow m.rs _ (Nat.le_refl _), fun σ _ => by rw [Regs.write_same]; rfl⟩⟩
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  | .fresh j, E, n, _, _ => by
      dsimp only [cb_fresh]
      refine ⟨by omega, by omega, fun i hi => ?_, fun m =>
        ⟨m.rs.write n (.name (m.st.names + j)), run_load c _ _ _ rfl,
        write_sameBelow m.rs _ (Nat.le_refl _), fun σ _ => by rw [Regs.write_same]; rfl⟩⟩
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  | .loc x, E, n, hE, hloc => by
      rw [cb_loc]
      have hx := hloc x (by simp)
      cases hEx : E x with
      | none => rw [hEx] at hx; cases hx
      | some r =>
          refine ⟨Nat.lt_of_lt_of_le (hE x r hEx) (Nat.le_refl _), (Nat.le_refl _),
            fun i hi => (by cases hi), fun m =>
            ⟨m.rs, rfl, SameBelow.refl _ _, fun σ a => (a x r hEx).symm⟩⟩
theorem cbList_spec (c : Ctx) : ∀ (ts : List Tm) (E : Env) (n : Nat), EnvBelow E n →
    (∀ x, Tm.loc x ∈ Tm.atomsList ts → (E x).isSome = true) →
    (cbList E n ts).2.2.length = ts.length ∧ (∀ r ∈ (cbList E n ts).2.2, r < (cbList E n ts).2.1) ∧
    n ≤ (cbList E n ts).2.1 ∧ (∀ i ∈ (cbList E n ts).1, i.pure = true) ∧
    ∀ m : Mach, ∃ rs', run c (cbList E n ts).1 m = (none, { m with rs := rs' }) ∧ SameBelow m.rs rs' n ∧
      ∀ σ, Agrees σ E m.rs → (cbList E n ts).2.2.map rs' = ts.map (Tm.inst σ (openFresh m.st.names))
  | [], E, n, _, _ => by
      dsimp only [cbList_nil]
      exact ⟨rfl, fun r hr => (by cases hr), (Nat.le_refl _), fun i hi => (by cases hi),
        fun m => ⟨m.rs, rfl, SameBelow.refl _ _, fun σ _ => rfl⟩⟩
  | t :: ts, E, n, hE, hloc => by
      dsimp only [cbList_cons]
      simp only [Tm.atomsList, List.mem_append] at hloc
      obtain ⟨a1, a2, a3, a4⟩ := cb_spec c t E n hE (fun x hx => hloc x (Or.inl hx))
      obtain ⟨b1, b2, b3, b4, b5⟩ :=
        cbList_spec c ts E (cb E n t).2.1 (hE.mono a2) (fun x hx => hloc x (Or.inr hx))
      refine ⟨by simp [b1], fun r hr => ?_, by omega, fun i hi => ?_, fun m => ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · omega
        · exact b2 r hr
      · rcases List.mem_append.mp hi with hi | hi
        · exact a3 i hi
        · exact b4 i hi
      · obtain ⟨rs₁, r1, s1, v1⟩ := a4 m
        obtain ⟨rs₂, r2, s2, v2⟩ := b5 { m with rs := rs₁ }
        refine ⟨rs₂, ?_, SameBelow.trans s1 s2 a2, fun σ a => ?_⟩
        · rw [run_append, r1]
          exact r2
        · have a' : Agrees σ E rs₁ := (agrees_iff_of_sameBelow hE s1).mp a
          have e1 : rs₂ (cb E n t).2.2 = t.inst σ (openFresh m.st.names) := (s2 _ a1).trans (v1 σ a)
          have e2 : (cbList E (cb E n t).2.1 ts).2.2.map rs₂ =
              ts.map (Tm.inst σ (openFresh m.st.names)) := v2 σ a'
          rw [List.map_cons, List.map_cons, e1, e2]
end

#print axioms cm_dyn
#print axioms cb_spec

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission
