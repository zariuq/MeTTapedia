import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotedBinders

/-!
# Pattern quotations

A pattern quotation is code with holes. A hole is a store name of the
surrounding scope. A binder of the code, and a parameter of the code, is a
name of the code: the two models store it by the same quotation-relative
position, and one map sends the slot model's name to the identity model's
name. Sealing binds every parameter, so the free names of a sealed pattern
quotation are its holes.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- The slot model's name of code, sent to the identity model's name.
A binder and a free parameter keep their position. A hole whose owner is
the surrounding scope's slot of its spelling becomes that scope's slot. -/
def codeMapHoles (env : REnv X) (envI : IEnv X) : Nm (Slot X) → Nm (BId X)
  | .src (o, y) =>
      if codeBound o = true ∨ o = codeFreeParam then .src (.code y o)
      else if o = env y then .src (.slot (envI y))
      else .src (.code y o)
  | .inst ρ n => .inst ρ (codeMapHoles env envI n)

/-- Two pieces of sealed code are the same quotation. -/
def codeQ (c₁ : Tm S (Slot X)) (c₂ : Tm S (BId X)) : Prop :=
  ∃ s : Src S X, c₁ = codeOf s ∧ c₂ = codeI s

/-- A name that belongs to the code: a binder, or a free parameter. -/
def codeOwned (n : Nm (Slot X)) : Prop :=
  match n with
  | .src (o, _) => codeBound o = true ∨ o = codeFreeParam
  | .inst _ _ => False

theorem codeBound_binder (pos : Owner) : codeBound (codeBinder pos) = true := rfl

omit [DecidableEq X] in
theorem codeMapHoles_owned {env : REnv X} {envI : IEnv X} {o : Owner} {y : X}
    (h : codeBound o = true ∨ o = codeFreeParam) :
    codeMapHoles env envI (.src (o, y)) = .src (.code y o) := by
  simp only [codeMapHoles, if_pos h]

omit [DecidableEq X] in
theorem codeMapHoles_hole {env : REnv X} {envI : IEnv X} {y : X}
    (hB : codeBound (env y) = false) (hF : env y ≠ codeFreeParam) :
    codeMapHoles env envI (.src (env y, y)) = .src (.slot (envI y)) := by
  have hnot : ¬ (codeBound (env y) = true ∨ env y = codeFreeParam) := by
    rintro (h | h)
    · exact Bool.false_ne_true (hB.symm.trans h)
    · exact hF h
  simp only [codeMapHoles, if_neg hnot, if_true]

omit [DecidableEq X] in
theorem codeMapHoles_ne_owned {env : REnv X} {envI : IEnv X} {x a : Nm (Slot X)}
    (hx : codeOwned x) (ha : a ≠ x) :
    codeMapHoles env envI a ≠ codeMapHoles env envI x := by
  cases x with
  | inst _ _ =>
      simp only [codeOwned] at hx
  | src sx =>
      obtain ⟨ox, yx⟩ := sx
      have hxmap : codeMapHoles env envI (.src (ox, yx)) = .src (.code yx ox) :=
        codeMapHoles_owned (by
          simp only [codeOwned] at hx
          exact hx)
      cases a with
      | inst _ _ =>
          rw [hxmap]
          simp only [codeMapHoles]
          intro h
          injection h
      | src sa =>
          obtain ⟨oa, ya⟩ := sa
          by_cases hao : codeBound oa = true ∨ oa = codeFreeParam
          · rw [codeMapHoles_owned hao, hxmap]
            intro h
            injection h with h
            injection h with hy ho
            exact ha (by rw [hy, ho])
          · by_cases he : oa = env ya
            · rw [hxmap]
              simp only [codeMapHoles, if_neg hao, if_pos he]
              intro h
              injection h with h
              cases h
            · rw [hxmap]
              simp only [codeMapHoles, if_neg hao, if_neg he]
              intro h
              injection h with h
              injection h with hy ho
              exact ha (by rw [hy, ho])

private theorem map_filter_owned {α β : Type v} [DecidableEq α] [DecidableEq β]
    {f : α → β} {x : α} (hne : ∀ a, a ≠ x → f a ≠ f x) (l : List α) :
    ((l.filter fun y => decide (y ≠ x)).map f) =
      ((l.map f).filter fun z => decide (z ≠ f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : a = x
      · have hd : decide (a ≠ x) = false := decide_eq_false (fun h => h ha)
        have hdf : decide (f a ≠ f x) = false :=
          decide_eq_false (fun h => h (congrArg f ha))
        rw [List.filter_cons_of_neg (p := fun y => decide (y ≠ x))
            (by rw [hd]; exact Bool.false_ne_true),
          List.map_cons,
          List.filter_cons_of_neg (p := fun z => decide (z ≠ f x))
            (by rw [hdf]; exact Bool.false_ne_true),
          ih]
      · have hk : decide (a ≠ x) = true := decide_eq_true ha
        have hkf : decide (f a ≠ f x) = true := decide_eq_true (hne a ha)
        rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ x)) hk,
          List.map_cons, List.map_cons,
          List.filter_cons_of_pos (p := fun z => decide (z ≠ f x)) hkf, ih]

private theorem filter_drop_nil {Y : Type v} [DecidableEq Y] (l : List (Nm Y)) :
    l.filter (fun n => !ownKey ([] : List Y) n) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have h : (!ownKey ([] : List Y) a) = true := by rw [ownKey_nil]; rfl
      rw [List.filter_cons_of_pos (p := fun n => !ownKey ([] : List Y) n) h, ih]

private theorem freeNames_lam_nil {Y : Type v} [DecidableEq Y] (x : Nm Y) (b : Tm S Y) :
    freeNames (.lam x [] b) = freeNames b := by
  simp only [freeNames, filter_drop_nil]

/-- Binding parameters does not change the free store names. -/
theorem freeNames_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) :
    freeNames (sealParams t) = freeNames t := by
  unfold sealParams
  induction paramOcc t with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.foldr, freeNames_lam_nil, ih]

private theorem paramOcc_eq_freeParams {Y : Type v} [DecidableEq Y] :
    ∀ t : Tm S Y, paramOcc t = freeParams t
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam _ _ b => by
      simp only [paramOcc, freeParams, paramOcc_eq_freeParams b]
  | .app a b => by
      simp only [paramOcc, freeParams, paramOcc_eq_freeParams a, paramOcc_eq_freeParams b]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by
      simp only [paramOcc, freeParams, paramOcc_eq_freeParams c]
  | .letP p w b => by
      simp only [paramOcc, freeParams, paramOcc_eq_freeParams p, paramOcc_eq_freeParams w,
        paramOcc_eq_freeParams b]
  | .alt t₁ t₂ => by
      simp only [paramOcc, freeParams, paramOcc_eq_freeParams t₁, paramOcc_eq_freeParams t₂]

private theorem freeParams_fold_sub {Y : Type v} [DecidableEq Y]
    (ps : List (Nm Y)) (t : Tm S Y) :
    ∀ p ∈ freeParams (ps.foldr (fun q acc => .lam q [] acc) t), p ∈ freeParams t := by
  induction ps with
  | nil => intro _ hp; exact hp
  | cons q ps ih =>
      intro p hp
      simp only [List.foldr, freeParams, List.mem_filter, decide_eq_true_eq] at hp
      exact ih p hp.1

private theorem freeParams_fold_out {Y : Type v} [DecidableEq Y]
    (ps : List (Nm Y)) (t : Tm S Y) :
    ∀ p ∈ freeParams (ps.foldr (fun q acc => .lam q [] acc) t), p ∉ ps := by
  induction ps with
  | nil => intro _ _; simp
  | cons q ps ih =>
      intro p hp
      simp only [List.foldr, freeParams, List.mem_filter, decide_eq_true_eq] at hp
      have htail : p ∉ ps := ih p hp.1
      simp only [List.mem_cons, not_or]
      exact ⟨hp.2, htail⟩

/-- Sealing binds every free parameter. -/
theorem freeParams_sealParams {Y : Type v} [DecidableEq Y] (t : Tm S Y) :
    freeParams (sealParams t) = [] := by
  unfold sealParams
  rw [paramOcc_eq_freeParams]
  refine (List.eq_nil_iff_forall_not_mem).2 fun p hp => ?_
  exact freeParams_fold_out (freeParams t) t p hp (freeParams_fold_sub (freeParams t) t p hp)

private theorem codeLookup_bound :
    ∀ (env : List (X × Owner)), (∀ p ∈ env, codeBound p.2 = true) →
      ∀ y o, codeLookup env y = some o → codeBound o = true
  | [], _, _, _, h => by simp [codeLookup] at h
  | (y, o) :: env, hb, z, o', h => by
      simp only [codeLookup] at h
      by_cases hy : y = z
      · rw [if_pos hy] at h
        cases h
        exact hb (y, o) List.mem_cons_self
      · rw [if_neg hy] at h
        exact codeLookup_bound env (fun p hp => hb p (List.mem_cons_of_mem _ hp)) z o' h

omit [DecidableEq X] in
private theorem svBinds_bound (pos : Owner) :
    ∀ s : Src S X, ∀ p ∈ svBinds pos s, codeBound p.2 = true
  | .sv _, p, h => by
      simp only [svBinds, List.mem_singleton] at h
      cases h
      exact codeBound_binder pos
  | .app f a, p, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact svBinds_bound (pos ++ [0]) f p h
      · exact svBinds_bound (pos ++ [1]) a p h
  | .alt t₁ t₂, p, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact svBinds_bound (pos ++ [0]) t₁ p h
      · exact svBinds_bound (pos ++ [1]) t₂ p h
  | .sym _, _, h | .fn _, _, h | .par _, _, h | .lam _ _ _, _, h | .quote _, _, h
    | .pquote _, _, h | .letS _ _ _ _, _, h | .unify _ _ _, _, h | .new _ _, _, h
    | .form _ _, _, h => by
      simp [svBinds] at h

omit [DecidableEq X] in
private theorem append_bound {a b : List (X × Owner)}
    (ha : ∀ p ∈ a, codeBound p.2 = true) (hb : ∀ p ∈ b, codeBound p.2 = true) :
    ∀ p ∈ a ++ b, codeBound p.2 = true := by
  intro p hp
  simp only [List.mem_append] at hp
  rcases hp with hp | hp
  · exact ha p hp
  · exact hb p hp

/-- A free parameter of elaborated code is a binder or a free parameter of
that code, never a hole. -/
theorem mem_freeParams_codeAt (holes : Option (X → Owner)) (penv senv : List (X × Owner))
    (pos : Owner) (hpenv : ∀ p ∈ penv, codeBound p.2 = true)
    (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ (s : Src S X) (n : Nm (Slot X)), n ∈ freeParams (codeAt holes penv senv pos s) →
      codeOwned n
  | .sym _, _, h => by simp [codeAt, freeParams] at h
  | .fn _, _, h => by simp [codeAt, freeParams] at h
  | .sv y, n, h => by
      simp only [codeAt] at h
      cases hlu : codeLookup senv y with
      | some o =>
          rw [hlu] at h
          simp only [freeParams, List.mem_singleton] at h
          rw [h]
          exact Or.inl (codeLookup_bound senv hsenv y o hlu)
      | none =>
          rw [hlu] at h
          cases holes <;> simp [freeParams] at h
  | .par z, n, h => by
      simp only [codeAt] at h
      cases hlu : codeLookup penv z with
      | some o =>
          rw [hlu] at h
          simp only [freeParams, List.mem_singleton] at h
          rw [h]
          exact Or.inl (codeLookup_bound penv hpenv z o hlu)
      | none =>
          rw [hlu] at h
          simp only [freeParams, List.mem_singleton] at h
          rw [h]
          exact Or.inr rfl
  | .lam z _ b, n, h => by
      simp only [codeAt, freeParams, List.mem_filter, decide_eq_true_eq] at h
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      exact mem_freeParams_codeAt holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        hpenv' hsenv b n h.1
  | .form z b, n, h => by
      simp only [codeAt, freeParams, List.mem_filter, decide_eq_true_eq] at h
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      exact mem_freeParams_codeAt holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        hpenv' hsenv b n h.1
  | .app f a, n, h => by
      simp only [codeAt, freeParams, List.mem_append] at h
      rcases h with h | h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [0]) hpenv hsenv f n h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [1]) hpenv hsenv a n h
  | .quote _, _, h => by simp [codeAt, freeParams] at h
  | .pquote c, n, h => by
      simp only [codeAt, freeParams] at h
      exact mem_freeParams_codeAt holes [] [] [] (by intro _ h; cases h) (by intro _ h; cases h) c n h
  | .letS p w b _, n, h => by
      simp only [codeAt, freeParams, List.mem_append] at h
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      rcases h with (h | h) | h
      · exact mem_freeParams_codeAt holes penv _ (pos ++ [0]) hpenv hsenv' p n h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [1]) hpenv hsenv w n h
      · exact mem_freeParams_codeAt holes penv _ (pos ++ [2]) hpenv hsenv' b n h
  | .unify p w b, n, h => by
      simp only [codeAt, freeParams, List.mem_append] at h
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      rcases h with (h | h) | h
      · exact mem_freeParams_codeAt holes penv _ (pos ++ [0]) hpenv hsenv' p n h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [1]) hpenv hsenv w n h
      · exact mem_freeParams_codeAt holes penv _ (pos ++ [2]) hpenv hsenv' b n h
  | .alt t₁ t₂, n, h => by
      simp only [codeAt, freeParams, List.mem_append] at h
      rcases h with h | h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [0]) hpenv hsenv t₁ n h
      · exact mem_freeParams_codeAt holes penv senv (pos ++ [1]) hpenv hsenv t₂ n h
  | .new _ b, n, h => by
      simp only [codeAt] at h
      exact mem_freeParams_codeAt holes penv senv (pos ++ [0]) hpenv hsenv b n h

/-- A free store name of code elaborated as a pattern is a hole: the
surrounding scope's slot of a spelling written in the code. -/
theorem mem_freeNames_codeAt (env : REnv X) (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ (s : Src S X) (n : Nm (Slot X)), n ∈ freeNames (codeAt (some env) penv senv pos s) →
      ∃ y, y ∈ Src.names s ∧ n = .src (env y, y)
  | .sym _, _, h => by simp [codeAt, freeNames] at h
  | .fn _, _, h => by simp [codeAt, freeNames] at h
  | .sv y, n, h => by
      simp only [codeAt] at h
      cases hlu : codeLookup senv y with
      | some _ =>
          rw [hlu] at h
          simp [freeNames] at h
      | none =>
          rw [hlu] at h
          simp only [freeNames, List.mem_singleton] at h
          exact ⟨y, by simp [Src.names], h⟩
  | .par z, _, h => by
      simp only [codeAt] at h
      cases hlu : codeLookup penv z with
      | some _ =>
          rw [hlu] at h
          simp [freeNames] at h
      | none =>
          rw [hlu] at h
          simp [freeNames] at h
  | .lam z _ b, n, h => by
      simp only [codeAt] at h
      rw [freeNames_lam_nil] at h
      obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env ((z, codeBinder pos) :: penv) senv
        (pos ++ [0]) b n h
      exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .form z b, n, h => by
      simp only [codeAt] at h
      rw [freeNames_lam_nil] at h
      obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env ((z, codeBinder pos) :: penv) senv
        (pos ++ [0]) b n h
      exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .app f a, n, h => by
      simp only [codeAt, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [0]) f n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [1]) a n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .quote _, _, h => by simp [codeAt, freeNames] at h
  | .pquote c, n, h => by
      simp only [codeAt, freeNames] at h
      obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env [] [] [] c n h
      exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .letS p w b _, n, h => by
      simp only [codeAt, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv (svBinds (pos ++ [0]) p ++ senv)
          (pos ++ [0]) p n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [1]) w n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv (svBinds (pos ++ [0]) p ++ senv)
          (pos ++ [2]) b n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .unify p w b, n, h => by
      simp only [codeAt, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv (svBinds (pos ++ [0]) p ++ senv)
          (pos ++ [0]) p n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [1]) w n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv (svBinds (pos ++ [0]) p ++ senv)
          (pos ++ [2]) b n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .alt t₁ t₂, n, h => by
      simp only [codeAt, freeNames, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [0]) t₁ n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
      · obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [1]) t₂ n h
        exact ⟨y, by simp [Src.names, hy], rfl⟩
  | .new _ b, n, h => by
      simp only [codeAt] at h
      obtain ⟨y, hy, rfl⟩ := mem_freeNames_codeAt env penv senv (pos ++ [0]) b n h
      exact ⟨y, by simp [Src.names, hy], rfl⟩

private theorem paramOcc_codeIAt (env : REnv X) (envI : IEnv X)
    (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true)
    (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ s : Src S X,
      paramOcc (codeIAt (some envI) penv senv pos s) =
        (paramOcc (codeAt (some env) penv senv pos s)).map (codeMapHoles env envI)
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases hlu : codeLookup senv y with
      | some o =>
          simp only [paramOcc, List.map_cons, List.map_nil,
            codeMapHoles_owned (Or.inl (codeLookup_bound senv hsenv y o hlu))]
      | none =>
          simp only [iVar, paramOcc, List.map_nil]
  | .par z => by
      simp only [codeAt, codeIAt]
      cases hlu : codeLookup penv z with
      | some o =>
          simp only [paramOcc, List.map_cons, List.map_nil,
            codeMapHoles_owned (Or.inl (codeLookup_bound penv hpenv z o hlu))]
      | none =>
          simp only [paramOcc, List.map_cons, List.map_nil, codeMapHoles_owned (Or.inr rfl)]
  | .lam z _ b => by
      simp only [codeAt, codeIAt, paramOcc]
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      rw [paramOcc_codeIAt env envI ((z, codeBinder pos) :: penv) senv (pos ++ [0]) hpenv' hsenv b]
      have hx : codeMapHoles env envI (.src (codeBinder pos, z)) =
          .src (.code z (codeBinder pos)) :=
        codeMapHoles_owned (Or.inl (codeBound_binder pos))
      rw [← hx]
      exact (map_filter_owned
        (f := codeMapHoles env envI)
        (x := .src (codeBinder pos, z))
        (fun a (ha : a ≠ .src (codeBinder pos, z)) =>
          codeMapHoles_ne_owned
            (show codeOwned (.src (codeBinder pos, z)) from Or.inl (codeBound_binder pos)) ha)
        (paramOcc (codeAt (some env) ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b))).symm
  | .form z b => by
      simp only [codeAt, codeIAt, paramOcc]
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      rw [paramOcc_codeIAt env envI ((z, codeBinder pos) :: penv) senv (pos ++ [0]) hpenv' hsenv b]
      have hx : codeMapHoles env envI (.src (codeBinder pos, z)) =
          .src (.code z (codeBinder pos)) :=
        codeMapHoles_owned (Or.inl (codeBound_binder pos))
      rw [← hx]
      exact (map_filter_owned
        (f := codeMapHoles env envI)
        (x := .src (codeBinder pos, z))
        (fun a (ha : a ≠ .src (codeBinder pos, z)) =>
          codeMapHoles_ne_owned
            (show codeOwned (.src (codeBinder pos, z)) from Or.inl (codeBound_binder pos)) ha)
        (paramOcc (codeAt (some env) ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b))).symm
  | .app f a => by
      simp only [codeAt, codeIAt, paramOcc, paramOcc_codeIAt env envI penv senv (pos ++ [0])
        hpenv hsenv f, paramOcc_codeIAt env envI penv senv (pos ++ [1]) hpenv hsenv a,
        List.map_append]
  | .quote _ => rfl
  | .pquote c => by
      simp only [codeAt, codeIAt, paramOcc,
        paramOcc_codeIAt env envI [] [] [] (by intro _ h; cases h) (by intro _ h; cases h) c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, paramOcc]
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      simp only [paramOcc_codeIAt env envI penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0])
        hpenv hsenv' p, paramOcc_codeIAt env envI penv senv (pos ++ [1]) hpenv hsenv w,
        paramOcc_codeIAt env envI penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2])
        hpenv hsenv' b, List.map_append]
  | .unify p w b => by
      simp only [codeAt, codeIAt, paramOcc]
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      simp only [paramOcc_codeIAt env envI penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0])
        hpenv hsenv' p, paramOcc_codeIAt env envI penv senv (pos ++ [1]) hpenv hsenv w,
        paramOcc_codeIAt env envI penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2])
        hpenv hsenv' b, List.map_append]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, paramOcc, paramOcc_codeIAt env envI penv senv (pos ++ [0])
        hpenv hsenv t₁, paramOcc_codeIAt env envI penv senv (pos ++ [1]) hpenv hsenv t₂,
        List.map_append]
  | .new _ b =>
      paramOcc_codeIAt env envI penv senv (pos ++ [0]) hpenv hsenv b

private theorem codeRel_foldBind {f : Nm (Slot X) → Nm (BId X)}
    {L : Nm (Slot X) → Prop} {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)}
    (ps : List (Nm (Slot X)))
    (hsep : ∀ p ∈ ps, ∀ y ∈ freeParams t₁, y ≠ p → f y ≠ f p)
    (hL : ∀ p ∈ ps, L p)
    (h : CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
      codeQ L f t₁ t₂) :
    CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
      codeQ L f
      (ps.foldr (fun p acc => .lam p [] acc) t₁)
      ((ps.map f).foldr (fun p acc => .lam p [] acc) t₂) := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
      simp only [List.foldr, List.map]
      refine .lam rfl (hL p List.mem_cons_self) ?hr₁ ?hr₂ ?hown ?hpar ?hb
      · intro s hs; cases hs
      · intro s hs; cases hs
      · intro n hn
        rw [ownKey_nil, ownKey_nil]
      · intro y hy hne
        have hy' : y ∈ freeParams t₁ := freeParams_fold_sub ps t₁ y hy
        exact hsep p List.mem_cons_self y hy' hne
      · exact ih (fun q hq => hsep q (List.mem_cons_of_mem _ hq))
          (fun q hq => hL q (List.mem_cons_of_mem _ hq))

private theorem codeRel_codeAt (env : REnv X) (envI : IEnv X)
    (hB : ∀ y, codeBound (env y) = false) (hF : ∀ y, env y ≠ codeFreeParam)
    (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true)
    (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ s : Src S X,
      CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
        codeQ (fun _ => True) (codeMapHoles env envI)
        (codeAt (some env) penv senv pos s)
        (codeIAt (some envI) penv senv pos s)
  | .sym s => by
      simp [codeAt, codeIAt]
      exact .sym s
  | .fn F => by
      simp [codeAt, codeIAt]
      exact .fn F
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases hlu : codeLookup senv y with
      | some o =>
          dsimp
          rw [← codeMapHoles_owned (Or.inl (codeLookup_bound senv hsenv y o hlu))]
          exact .pvar trivial
      | none =>
          simp only [iVar]
          rw [← codeMapHoles_hole (hB y) (hF y)]
          exact .var _
  | .par z => by
      simp only [codeAt, codeIAt]
      cases hlu : codeLookup penv z with
      | some o =>
          dsimp
          rw [← codeMapHoles_owned (Or.inl (codeLookup_bound penv hpenv z o hlu))]
          exact .pvar trivial
      | none =>
          dsimp
          rw [← codeMapHoles_owned (Or.inr rfl)]
          exact .pvar trivial
  | .lam z _ b => by
      simp only [codeAt, codeIAt]
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      refine .lam ?hx trivial ?hr₁ ?hr₂ ?hown ?hpar
        (codeRel_codeAt env envI hB hF ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          hpenv' hsenv b)
      · exact codeMapHoles_owned (Or.inl (codeBound_binder pos))
      · intro s hs; cases hs
      · intro s hs; cases hs
      · intro n hn
        rw [ownKey_nil, ownKey_nil]
      · intro _ _ hne
        exact codeMapHoles_ne_owned
          (show codeOwned (.src (codeBinder pos, z)) from Or.inl (codeBound_binder pos)) hne
  | .form z b => by
      simp only [codeAt, codeIAt]
      have hpenv' : ∀ p ∈ (z, codeBinder pos) :: penv, codeBound p.2 = true := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact codeBound_binder pos
        · exact hpenv p hp
      refine .lam ?_ trivial ?_ ?_ ?_ ?_
        (codeRel_codeAt env envI hB hF ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          hpenv' hsenv b)
      · exact codeMapHoles_owned (Or.inl (codeBound_binder pos))
      · intro s hs; cases hs
      · intro s hs; cases hs
      · intro n hn
        rw [ownKey_nil, ownKey_nil]
      · intro _ _ hne
        exact codeMapHoles_ne_owned
          (show codeOwned (.src (codeBinder pos, z)) from Or.inl (codeBound_binder pos)) hne
  | .app f a => by
      simp only [codeAt, codeIAt]
      exact .app
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [0]) hpenv hsenv f)
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [1]) hpenv hsenv a)
  | .quote c => by
      simp only [codeAt, codeIAt]
      exact .quote ⟨c, rfl, rfl⟩
  | .pquote c => by
      simp only [codeAt, codeIAt]
      exact .pquote (codeRel_codeAt env envI hB hF [] [] []
        (by intro _ h; cases h) (by intro _ h; cases h) c)
  | .letS p w b _ => by
      simp only [codeAt, codeIAt]
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      exact .letP
        (codeRel_codeAt env envI hB hF penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0])
          hpenv hsenv' p)
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [1]) hpenv hsenv w)
        (codeRel_codeAt env envI hB hF penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2])
          hpenv hsenv' b)
  | .unify p w b => by
      simp only [codeAt, codeIAt]
      have hsenv' := append_bound (svBinds_bound (pos ++ [0]) p) hsenv
      exact .letP
        (codeRel_codeAt env envI hB hF penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0])
          hpenv hsenv' p)
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [1]) hpenv hsenv w)
        (codeRel_codeAt env envI hB hF penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2])
          hpenv hsenv' b)
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt]
      exact .alt
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [0]) hpenv hsenv t₁)
        (codeRel_codeAt env envI hB hF penv senv (pos ++ [1]) hpenv hsenv t₂)
  | .new _ b => by
      simp only [codeAt, codeIAt]
      exact codeRel_codeAt env envI hB hF penv senv (pos ++ [0]) hpenv hsenv b

/-- The two elaborations of a pattern quotation are the same code. Holes are
the surrounding scope's slots. Every other name is a binder or a parameter
of the code, sent across by one map, and sealing binds the parameters. -/
theorem codeRel_pattern (env : REnv X) (envI : IEnv X)
    (hB : ∀ y, codeBound (env y) = false) (hF : ∀ y, env y ≠ codeFreeParam)
    (c : Src S X) :
    CodeRel (R₁ := fun (_ : Slot X) => True) (R₂ := fun (_ : BId X) => True)
      codeQ (fun _ => True) (codeMapHoles env envI)
      (sealParams (codeAt (some env) [] [] [] c))
      (sealParams (codeIAt (some envI) [] [] [] c)) := by
  have hrel := codeRel_codeAt env envI hB hF [] [] [] (by intro _ h; cases h)
    (by intro _ h; cases h) c
  have hocc := paramOcc_codeIAt env envI [] [] [] (by intro _ h; cases h)
    (by intro _ h; cases h) c
  unfold sealParams
  rw [hocc]
  refine codeRel_foldBind (paramOcc (codeAt (some env) [] [] [] c)) ?hsep ?hL hrel
  · intro p hp _ _ hne
    rw [paramOcc_eq_freeParams] at hp
    exact codeMapHoles_ne_owned
      (mem_freeParams_codeAt (some env) [] [] [] (by intro _ h; cases h)
        (by intro _ h; cases h) c p hp) hne
  · intro _ _; trivial

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
