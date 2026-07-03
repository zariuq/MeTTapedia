/-
# E2b-universal — `eval pLF` simulates de Bruijn `shift`  (2026-07-03)

Mirrors `LFEngineSim.lt_sim`: the certified normalizer `MeTTaIL.eval` computes the recognizer's
`shift` exactly as Lean's `LF.shift`, on *every* term.  Unlike `lt` (root reductions only), `shift`
reduces inside `Pi`/`Lam`/`App`/`shiftVar` contexts, so the proof adds a context-congruence brick
(`cong_eval`) lifting an `eval`-reduction of a subterm through a one-hole context.

Integrity: 0 sorry / 0 native_decide; `#print axioms` clean.
-/
import Mettapedia.GSLT.LanguageDef.LFEngineSim
import Mettapedia.GSLT.LanguageDef.LFEngineCorrespondence

namespace Mettapedia.GSLT.LanguageDef.LFShiftSim

open MeTTaIL Mettapedia.GSLT.LanguageDef.LFEnc Mettapedia.GSLT.LanguageDef.LFUniv
open Mettapedia.GSLT.LanguageDef.LFSim (lt_sim os_lt_ss os_lt_zs os_lt_zz os_lt_sz)
open Mettapedia.GSLT.LanguageDef.LFEngineCorr (encSrt encTerm)

set_option maxRecDepth 8000

/-! ## One-step dispatch facts (each `rfl`, arbitrary AST operands). -/

theorem os_sh_var (c k : AST) :
    oneStep pLF (shift c (Var k)) = some (shiftVar c k (ltT k c)) := by rfl
theorem os_sh_con (c x : AST) :
    oneStep pLF (shift c (Con x)) = some (Con x) := by rfl
theorem os_sh_srt (c s : AST) :
    oneStep pLF (shift c (Srt s)) = some (Srt s) := by rfl
theorem os_sh_pi (c A B : AST) :
    oneStep pLF (shift c (Pi A B)) = some (Pi (shift c A) (shift (S c) B)) := by rfl
theorem os_sh_lam (c A b : AST) :
    oneStep pLF (shift c (Lam A b)) = some (Lam (shift c A) (shift (S c) b)) := by rfl
theorem os_sh_app (c f a : AST) :
    oneStep pLF (shift c (App f a)) = some (App (shift c f) (shift c a)) := by rfl
theorem os_shv_tt (c k : AST) :
    oneStep pLF (shiftVar c k (con0 "tt")) = some (Var k) := by rfl
theorem os_shv_ff (c k : AST) :
    oneStep pLF (shiftVar c k (con0 "ff")) = some (Var (S k)) := by rfl

/-- A positive-arity constructor pattern never matches a nullary constructor term. -/
theorem matchPat_pos_nil (l m : Label) (p : AST) (ps : List AST) (bnds : List (String × AST)) :
    AST.matchPat (.sexp l (p :: ps)) (.sexp m []) bnds = none := by
  simp only [AST.matchPat]
  split <;> rfl

/-- No rule of `pLF` has a nullary left-hand side, so a bare constructor `con0 x` is irreducible. -/
theorem baseReducts_con0 (x : String) : baseReducts pLF (con0 x) = [] := by
  simp only [baseReducts, pLF, Presentation.rewrites, shiftRules, ltRules, resolveRules,
    ctxidxRules, parserRules, applyBaseRewrite, Mettapedia.GSLT.LanguageDef.LFEnc.rw,
    con0, ltT, shift, shiftVar, Var, Con, Srt, Pi, Lam, App, S, Z,
    Nil, Cons, NF, Idx, ctxidx, ctxK, resolve, resolveK, tm, ar, ap, apm, at', tmPi1, tmPi2,
    tmLam1, tmLam2, arK, arK2, apK, apmK, atLPk, recK, lfrec, Pp, PErr, Ok, Err, tId, tPI, tLAM,
    tARR, tCOLON, tDOT, tLP, tRP, tTYPE, extraToks, pv, peano, List.filterMap_cons,
    List.filterMap_nil, List.cons_append, List.nil_append, matchPat_pos_nil,
    Option.map_none]

theorem isnormal_con0 (x : String) : IsNormal pLF (con0 x) := by
  have h : baseReducts pLF (con0 x) = [] := baseReducts_con0 x
  simp only [IsNormal, con0] at *
  simp only [oneStep, h, oneStepList, Option.map_none]

/-! ## General normality by structural descent (heads with no matching rule). -/

/-- If every element of a list is normal, no list step applies. -/
theorem oneStepList_none_of_forall_normal :
    ∀ (args : List AST), (∀ a ∈ args, IsNormal pLF a) → oneStepList pLF args = none
  | [], _ => rfl
  | a :: as, h => by
      have ha : oneStep pLF a = none := h a (List.mem_cons.mpr (Or.inl rfl))
      have has : oneStepList pLF as = none :=
        oneStepList_none_of_forall_normal as (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
      simp only [oneStepList, ha, has, Option.map_none]

/-- A constructor with no root reduct and all-normal arguments is normal. -/
theorem isnormal_sexp (l : Label) (args : List AST)
    (hb : baseReducts pLF (.sexp l args) = [])
    (hargs : ∀ a ∈ args, IsNormal pLF a) : IsNormal pLF (.sexp l args) := by
  have hl := oneStepList_none_of_forall_normal args hargs
  show oneStep pLF (.sexp l args) = none
  simp only [oneStep, hb, hl, Option.map_none]

theorem isnormal_sexp1 (l : Label) (a : AST)
    (hb : baseReducts pLF (.sexp l [a]) = []) (ha : IsNormal pLF a) :
    IsNormal pLF (.sexp l [a]) :=
  isnormal_sexp l [a] hb (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ha)

theorem isnormal_sexp2 (l : Label) (a b : AST)
    (hb : baseReducts pLF (.sexp l [a, b]) = [])
    (ha : IsNormal pLF a) (hb2 : IsNormal pLF b) : IsNormal pLF (.sexp l [a, b]) :=
  isnormal_sexp l [a, b] hb
    (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · rw [List.mem_singleton] at hx; subst hx; exact hb2)

/-- Peano numerals are normal. -/
theorem isnormal_peano : ∀ n, IsNormal pLF (peano n)
  | 0 => rfl
  | n + 1 => isnormal_sexp1 (.id "S") (peano n) rfl (isnormal_peano n)

/-- Every encoded term is a normal form of `pLF` (no rule matches a pure de Bruijn term). -/
theorem isnormal_encTerm : ∀ t : LF.Term, IsNormal pLF (encTerm t)
  | .srt s   => isnormal_sexp1 (.id "Srt") (encSrt s) rfl (by cases s <;> exact isnormal_con0 _)
  | .con x   => isnormal_sexp1 (.id "Con") (con0 x) rfl (isnormal_con0 x)
  | .var k   => isnormal_sexp1 (.id "Var") (peano k) rfl (isnormal_peano k)
  | .pi A B  => isnormal_sexp2 (.id "Pi") (encTerm A) (encTerm B) rfl
                  (isnormal_encTerm A) (isnormal_encTerm B)
  | .lam A b => isnormal_sexp2 (.id "Lam") (encTerm A) (encTerm b) rfl
                  (isnormal_encTerm A) (isnormal_encTerm b)
  | .app f a => isnormal_sexp2 (.id "App") (encTerm f) (encTerm a) rfl
                  (isnormal_encTerm f) (isnormal_encTerm a)

/-! ## Fuel composition and context congruence over `eval`. -/

/-- Reductions compose: `N` steps to `u` then `k` steps to `w` is `N + k` steps to `w`. -/
theorem eval_trans (p : Presentation) : ∀ (a b : Nat) (t u w : AST),
    eval p a t = u → eval p b u = w → eval p (a + b) t = w := by
  intro a
  induction a with
  | zero =>
    intro b t u w h1 h2
    simp only [eval] at h1; subst h1; simp only [Nat.zero_add]; exact h2
  | succ n ih =>
    intro b t u w h1 h2
    simp only [eval] at h1
    cases hstep : oneStep p t with
    | none =>
      rw [hstep] at h1; subst h1
      have hb := eval_of_normal p t hstep b
      rw [hb] at h2
      rw [← h2]
      exact eval_of_normal p t hstep (n + 1 + b)
    | some t' =>
      rw [hstep] at h1
      have hcomp := ih b t' u w h1 h2
      have hab : n + 1 + b = (n + b) + 1 := by omega
      rw [hab]
      simp only [eval, hstep]
      exact hcomp

/-- **Context congruence over `eval`.** If a one-hole context `F` lifts every one-step reduction of
    its hole, then reducing the hole to a value lifts to reducing `F` of the hole to `F` of the value.
    The value need not be normal (`F v` may still reduce at its root), so the returned fuel is exactly
    the hole's reduction length. -/
theorem cong_eval (F : AST → AST)
    (hcong : ∀ s s', oneStep pLF s = some s' → oneStep pLF (F s) = some (F s')) :
    ∀ (N : Nat) {s v : AST}, eval pLF N s = v → IsNormal pLF v → ∃ M, eval pLF M (F s) = F v := by
  intro N
  induction N with
  | zero =>
    intro s v hs _
    simp only [eval] at hs; subst hs
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro s v hs hv
    simp only [eval] at hs
    cases hstep : oneStep pLF s with
    | none =>
      rw [hstep] at hs; subst hs
      exact ⟨0, rfl⟩
    | some s' =>
      rw [hstep] at hs
      obtain ⟨M, hM⟩ := ih hs hv
      refine ⟨M + 1, ?_⟩
      simp only [eval, hcong s s' hstep]
      exact hM

/-! ## One-step congruences for the de Bruijn constructor contexts (each `baseReducts = []` by `rfl`). -/

theorem hcong_pi1 (Y : AST) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Pi s Y) = some (Pi s' Y) := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Pi") [s, Y]) = [] := rfl
  show oneStep pLF (.sexp (.id "Pi") [s, Y]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, Pi]

theorem hcong_pi2 (X : AST) (hX : oneStep pLF X = none) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Pi X s) = some (Pi X s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Pi") [X, s]) = [] := rfl
  show oneStep pLF (.sexp (.id "Pi") [X, s]) = _
  simp only [oneStep, hb, oneStepList, hX, h, Option.map_some, Pi]

theorem hcong_lam1 (Y : AST) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Lam s Y) = some (Lam s' Y) := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Lam") [s, Y]) = [] := rfl
  show oneStep pLF (.sexp (.id "Lam") [s, Y]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, Lam]

theorem hcong_lam2 (X : AST) (hX : oneStep pLF X = none) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (Lam X s) = some (Lam X s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "Lam") [X, s]) = [] := rfl
  show oneStep pLF (.sexp (.id "Lam") [X, s]) = _
  simp only [oneStep, hb, oneStepList, hX, h, Option.map_some, Lam]

theorem hcong_app1 (Y : AST) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (App s Y) = some (App s' Y) := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "App") [s, Y]) = [] := rfl
  show oneStep pLF (.sexp (.id "App") [s, Y]) = _
  simp only [oneStep, hb, oneStepList, h, Option.map_some, App]

theorem hcong_app2 (X : AST) (hX : oneStep pLF X = none) : ∀ s s', oneStep pLF s = some s' →
    oneStep pLF (App X s) = some (App X s') := by
  intro s s' h
  have hb : baseReducts pLF (AST.sexp (Label.id "App") [X, s]) = [] := rfl
  show oneStep pLF (.sexp (.id "App") [X, s]) = _
  simp only [oneStep, hb, oneStepList, hX, h, Option.map_some, App]

/-! ## `shiftVar` over the `lt`-guard: descend into the `lt`-headed 3rd argument.

While the guard is still `(lt _ _)` (not yet `tt`/`ff`), no root `shiftVar` rule fires, so `oneStep`
descends into the 3rd argument once the cutoff/index are normal.  Each `baseReducts = []` is `rfl`
(the guard head `lt` is neither `tt` nor `ff`). -/

theorem os_shv_lt_ss (c k x y : AST) (hc : oneStep pLF c = none) (hk : oneStep pLF k = none) :
    oneStep pLF (shiftVar c k (ltT (S x) (S y))) = some (shiftVar c k (ltT x y)) := by
  have hb : baseReducts pLF (AST.sexp (Label.id "shiftVar") [c, k, ltT (S x) (S y)]) = [] := rfl
  show oneStep pLF (.sexp (.id "shiftVar") [c, k, ltT (S x) (S y)]) = _
  simp only [oneStep, hb, oneStepList, hc, hk, os_lt_ss, Option.map_some, shiftVar]

theorem os_shv_lt_zs (c k y : AST) (hc : oneStep pLF c = none) (hk : oneStep pLF k = none) :
    oneStep pLF (shiftVar c k (ltT Z (S y))) = some (shiftVar c k (con0 "tt")) := by
  have hb : baseReducts pLF (AST.sexp (Label.id "shiftVar") [c, k, ltT Z (S y)]) = [] := rfl
  show oneStep pLF (.sexp (.id "shiftVar") [c, k, ltT Z (S y)]) = _
  simp only [oneStep, hb, oneStepList, hc, hk, os_lt_zs, Option.map_some, shiftVar]

theorem os_shv_lt_zz (c k : AST) (hc : oneStep pLF c = none) (hk : oneStep pLF k = none) :
    oneStep pLF (shiftVar c k (ltT Z Z)) = some (shiftVar c k (con0 "ff")) := by
  have hb : baseReducts pLF (AST.sexp (Label.id "shiftVar") [c, k, ltT Z Z]) = [] := rfl
  show oneStep pLF (.sexp (.id "shiftVar") [c, k, ltT Z Z]) = _
  simp only [oneStep, hb, oneStepList, hc, hk, os_lt_zz, Option.map_some, shiftVar]

theorem os_shv_lt_sz (c k x : AST) (hc : oneStep pLF c = none) (hk : oneStep pLF k = none) :
    oneStep pLF (shiftVar c k (ltT (S x) Z)) = some (shiftVar c k (con0 "ff")) := by
  have hb : baseReducts pLF (AST.sexp (Label.id "shiftVar") [c, k, ltT (S x) Z]) = [] := rfl
  show oneStep pLF (.sexp (.id "shiftVar") [c, k, ltT (S x) Z]) = _
  simp only [oneStep, hb, oneStepList, hc, hk, os_lt_sz, Option.map_some, shiftVar]

/-- **`shiftVar` over the guard.** With normal cutoff `c` and index `k`, the engine reduces
    `shiftVar c k (lt (peano a) (peano b))` all the way to `Var k` (if `a < b`) or `Var (S k)`
    (otherwise) — the guard is computed by `lt`, then `sh-var-lt`/`sh-var-ge` fires.  Mirrors
    `lt_sim`'s induction, one `shiftVar`-context step per `lt` step plus the final root step. -/
theorem shv_lt_final : ∀ (a b : Nat) (c k : AST),
    oneStep pLF c = none → oneStep pLF k = none →
    ∃ N, eval pLF N (shiftVar c k (ltT (peano a) (peano b)))
      = (if a < b then Var k else Var (S k)) := by
  intro a
  induction a with
  | zero =>
    intro b c k hc hk
    cases b with
    | zero =>
      refine ⟨2, ?_⟩
      simp only [peano, eval, os_shv_lt_zz c k hc hk, os_shv_ff]
      simp
    | succ b' =>
      refine ⟨2, ?_⟩
      simp only [peano, eval, os_shv_lt_zs c k (peano b') hc hk, os_shv_tt]
      simp [Nat.zero_lt_succ]
  | succ a' ih =>
    intro b c k hc hk
    cases b with
    | zero =>
      refine ⟨2, ?_⟩
      simp only [peano, eval, os_shv_lt_sz c k (peano a') hc hk, os_shv_ff]
      simp
    | succ b' =>
      obtain ⟨N, hN⟩ := ih b' c k hc hk
      refine ⟨N + 1, ?_⟩
      simp only [peano, eval, os_shv_lt_ss c k (peano a') (peano b') hc hk]
      rw [hN]
      simp [Nat.succ_lt_succ_iff]

/-! ## The simulation: `eval pLF` computes `shift` exactly as `LF.shift`, on every term. -/

/-- Auxiliary form, by structural induction on the term (cutoff generalized). -/
theorem shift_sim_aux : ∀ (t : LF.Term) (c : Nat),
    ∃ N, eval pLF N (shift (peano c) (encTerm t)) = encTerm (LF.shift c t) := by
  intro t
  induction t with
  | srt s =>
    intro c
    exact ⟨1, by simp only [encTerm, LF.shift, eval, os_sh_srt]⟩
  | con x =>
    intro c
    exact ⟨1, by simp only [encTerm, LF.shift, eval, os_sh_con]⟩
  | var k =>
    intro c
    obtain ⟨N, hN⟩ := shv_lt_final k c (peano c) (peano k) (isnormal_peano c) (isnormal_peano k)
    refine ⟨N + 1, ?_⟩
    simp only [encTerm, LF.shift, eval, os_sh_var]
    rw [hN]
    by_cases hkc : k < c
    · simp only [if_pos hkc]
    · simp only [if_neg hkc, peano]
  | pi A B ihA ihB =>
    intro c
    obtain ⟨N1, hN1⟩ := ihA c
    obtain ⟨N2, hN2⟩ := ihB (c + 1)
    obtain ⟨M1, hM1⟩ := cong_eval (fun s => Pi s (shift (S (peano c)) (encTerm B)))
        (hcong_pi1 _) N1 hN1 (isnormal_encTerm _)
    obtain ⟨M2, hM2⟩ := cong_eval (fun s => Pi (encTerm (LF.shift c A)) s)
        (hcong_pi2 _ (isnormal_encTerm _)) N2 hN2 (isnormal_encTerm _)
    refine ⟨1 + (M1 + M2), ?_⟩
    have hstep1 : eval pLF 1 (shift (peano c) (encTerm (.pi A B)))
        = Pi (shift (peano c) (encTerm A)) (shift (S (peano c)) (encTerm B)) := by
      simp only [encTerm, eval, os_sh_pi]
    refine eval_trans pLF 1 (M1 + M2) _ _ _ hstep1 ?_
    refine eval_trans pLF M1 M2 _ _ _ hM1 ?_
    exact hM2
  | lam A b ihA ihb =>
    intro c
    obtain ⟨N1, hN1⟩ := ihA c
    obtain ⟨N2, hN2⟩ := ihb (c + 1)
    obtain ⟨M1, hM1⟩ := cong_eval (fun s => Lam s (shift (S (peano c)) (encTerm b)))
        (hcong_lam1 _) N1 hN1 (isnormal_encTerm _)
    obtain ⟨M2, hM2⟩ := cong_eval (fun s => Lam (encTerm (LF.shift c A)) s)
        (hcong_lam2 _ (isnormal_encTerm _)) N2 hN2 (isnormal_encTerm _)
    refine ⟨1 + (M1 + M2), ?_⟩
    have hstep1 : eval pLF 1 (shift (peano c) (encTerm (.lam A b)))
        = Lam (shift (peano c) (encTerm A)) (shift (S (peano c)) (encTerm b)) := by
      simp only [encTerm, eval, os_sh_lam]
    refine eval_trans pLF 1 (M1 + M2) _ _ _ hstep1 ?_
    refine eval_trans pLF M1 M2 _ _ _ hM1 ?_
    exact hM2
  | app f a ihf iha =>
    intro c
    obtain ⟨N1, hN1⟩ := ihf c
    obtain ⟨N2, hN2⟩ := iha c
    obtain ⟨M1, hM1⟩ := cong_eval (fun s => App s (shift (peano c) (encTerm a)))
        (hcong_app1 _) N1 hN1 (isnormal_encTerm _)
    obtain ⟨M2, hM2⟩ := cong_eval (fun s => App (encTerm (LF.shift c f)) s)
        (hcong_app2 _ (isnormal_encTerm _)) N2 hN2 (isnormal_encTerm _)
    refine ⟨1 + (M1 + M2), ?_⟩
    have hstep1 : eval pLF 1 (shift (peano c) (encTerm (.app f a)))
        = App (shift (peano c) (encTerm f)) (shift (peano c) (encTerm a)) := by
      simp only [encTerm, eval, os_sh_app]
    refine eval_trans pLF 1 (M1 + M2) _ _ _ hstep1 ?_
    refine eval_trans pLF M1 M2 _ _ _ hM1 ?_
    exact hM2

/-- **`shift`-correctness (simulation).** For every cutoff `c` and term `t`, the certified normalizer
    reduces the encoded `shift (peano c) ⟦t⟧` to the encoding of Lean's `LF.shift c t`. -/
theorem shift_sim : ∀ (c : Nat) (t : LF.Term),
    ∃ N, eval pLF N (LFEnc.shift (peano c) (LFEngineCorr.encTerm t))
      = LFEngineCorr.encTerm (LF.shift c t) := by
  intro c t
  exact shift_sim_aux t c

end Mettapedia.GSLT.LanguageDef.LFShiftSim
