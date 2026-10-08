import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh

/-!
# Code equality agrees for the two name disciplines

A binder inside quoted code is compared by its quotation-relative position, and
a free parameter by its spelling. The slot model stores that position as the
owner of a slot; the identity model stores it on a code name. `codeEq` gives
the same answer either way.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v} [DecidableEq S] [DecidableEq X]

omit [DecidableEq S] [DecidableEq X] in
private theorem decide_eq_of_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : decide p = decide q := by
  by_cases hp : p
  · rw [decide_eq_true hp, decide_eq_true (h.mp hp)]
  · rw [decide_eq_false hp, decide_eq_false (fun hq => hp (h.mpr hq))]

omit [DecidableEq S] in
/-- A slot `(owner, spelling)` and the code name of that spelling at that
owner are the same name to `CodeId`. -/
private theorem same_slot_code (o₁ o₂ : Owner) (y₁ y₂ : X) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      CodeId.same (.src (.code y₁ o₁) : Nm (BId X)) (.src (.code y₂ o₂)) := by
  have hiff :
      ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) ↔
        ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) := by
    simp only [Nm.src.injEq, Prod.mk.injEq, BId.code.injEq]
    exact and_comm
  simp only [CodeId.same]
  by_cases hb : (codeBound o₁ && codeBound o₂) = true
  · simp_rw [hb]; rfl
  · have hb' : (codeBound o₁ && codeBound o₂) = false := Bool.eq_false_iff.mpr hb
    simp_rw [hb']
    by_cases hf : (decide (o₁ = codeFreeParam) && decide (o₂ = codeFreeParam)) = true
    · simp_rw [hf]; rfl
    · have hf' : (decide (o₁ = codeFreeParam) && decide (o₂ = codeFreeParam)) = false :=
        Bool.eq_false_iff.mpr hf
      simp_rw [hf']
      exact decide_eq_of_iff hiff

omit [DecidableEq S] [DecidableEq X] in
private def codeFwd : Nm (Slot X) → Nm (BId X)
  | .src ([], y) => .src (.slot ⟨y, [], [], .head⟩)
  | .src ((n :: o), y) => .src (.code y (n :: o))
  | .inst ρ n => .inst ρ (codeFwd n)

omit [DecidableEq S] [DecidableEq X] in
private def codeBack : Nm (BId X) → Nm (Slot X)
  | .src (.slot k) => .src ([], k.spell)
  | .src (.code y o) => .src (o, y)
  | .src (.par z _) => .src ([], z)
  | .inst ρ n => .inst ρ (codeBack n)

omit [DecidableEq S] [DecidableEq X] in
private theorem codeBack_codeFwd : ∀ n : Nm (Slot X), codeBack (codeFwd n) = n
  | .src ([], _) => rfl
  | .src ((_ :: _), _) => rfl
  | .inst _ n => by simp only [codeFwd, codeBack, codeBack_codeFwd n]

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_eq_iff (n₁ n₂ : Nm (Slot X)) :
    codeFwd n₁ = codeFwd n₂ ↔ n₁ = n₂ := by
  constructor
  · intro h
    rw [← codeBack_codeFwd n₁, h, codeBack_codeFwd]
  · exact fun h => congrArg codeFwd h

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_binder (pos : Owner) (z : X) :
    codeFwd (.src (codeBinder pos, z)) = .src (.code z (codeBinder pos)) := by
  simp only [codeBinder]
  rfl

omit [DecidableEq S] in
private theorem bound_nil_and (o : Owner) :
    (codeBound ([] : Owner) && codeBound o) = false := by
  simp [codeBound]

omit [DecidableEq S] in
private theorem and_bound_nil (o : Owner) :
    (codeBound o && codeBound ([] : Owner)) = false := by
  simp [codeBound]

omit [DecidableEq S] in
private theorem free_nil_and (o : Owner) :
    (decide (([] : Owner) = codeFreeParam) && decide (o = codeFreeParam)) = false := by
  simp [codeFreeParam]

omit [DecidableEq S] in
private theorem and_free_nil (o : Owner) :
    (decide (o = codeFreeParam) && decide (([] : Owner) = codeFreeParam)) = false := by
  simp [codeFreeParam]

omit [DecidableEq S] in
private theorem bslot_ne_code (k : SlotId X) (y : X) (o : Owner) :
    CodeId.same (.src (.slot k) : Nm (BId X)) (.src (.code y o)) = false :=
  decide_eq_false fun h => by cases h

omit [DecidableEq S] in
private theorem same_root_slots (y₁ y₂ : X) :
    CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src ([], y₂)) =
      CodeId.same (.src (.slot ⟨y₁, [], [], .head⟩) : Nm (BId X))
        (.src (.slot ⟨y₂, [], [], .head⟩)) := by
  simp only [CodeId.same]
  simp_rw [bound_nil_and, free_nil_and]
  exact decide_eq_of_iff <| by
    simp only [Nm.src.injEq, Prod.mk.injEq, BId.slot.injEq, SlotId.mk.injEq,
      and_true, true_and]

omit [DecidableEq S] in
private theorem same_root_cons (y₁ y₂ : X) (n : ℕ) (o : List ℕ) :
    CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src (n :: o, y₂)) =
      CodeId.same (.src (.slot ⟨y₁, [], [], .head⟩) : Nm (BId X))
        (.src (.code y₂ (n :: o))) := by
  have hL : CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src (n :: o, y₂)) = false := by
    simp only [CodeId.same]
    simp_rw [bound_nil_and (n :: o), free_nil_and (n :: o)]
    rfl
  rw [hL, bslot_ne_code]

omit [DecidableEq S] in
private theorem same_cons_root (y₁ y₂ : X) (n : ℕ) (o : List ℕ) :
    CodeId.same (.src (n :: o, y₁) : Nm (Slot X)) (.src ([], y₂)) =
      CodeId.same (.src (.code y₁ (n :: o)) : Nm (BId X))
        (.src (.slot ⟨y₂, [], [], .head⟩)) := by
  have hL : CodeId.same (.src (n :: o, y₁) : Nm (Slot X)) (.src ([], y₂)) = false := by
    simp only [CodeId.same]
    simp_rw [and_bound_nil (n :: o), and_free_nil (n :: o)]
    rfl
  have hR : CodeId.same (.src (.code y₁ (n :: o)) : Nm (BId X))
      (.src (.slot ⟨y₂, [], [], .head⟩)) = false :=
    decide_eq_false fun h => by cases h
  rw [hL, hR]

omit [DecidableEq S] in
private theorem same_fwd (n₁ n₂ : Nm (Slot X)) :
    CodeId.same n₁ n₂ = CodeId.same (codeFwd n₁) (codeFwd n₂) := by
  cases n₁ with
  | src p =>
      cases n₂ with
      | src q =>
          cases p with
          | mk o₁ y₁ =>
              cases q with
              | mk o₂ y₂ =>
                  cases o₁ with
                  | nil =>
                      cases o₂ with
                      | nil =>
                          simp only [codeFwd]
                          exact same_root_slots y₁ y₂
                      | cons n o =>
                          simp only [codeFwd]
                          exact same_root_cons y₁ y₂ n o
                  | cons n o =>
                      cases o₂ with
                      | nil =>
                          simp only [codeFwd]
                          exact same_cons_root y₁ y₂ n o
                      | cons m t =>
                          simp only [codeFwd]
                          exact same_slot_code (n :: o) (m :: t) y₁ y₂
      | inst _ _ =>
          cases p with
          | mk o _ =>
              cases o with
              | nil =>
                  simp only [CodeId.same, codeFwd]
                  exact decide_eq_of_iff (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
              | cons _ _ =>
                  simp only [CodeId.same, codeFwd]
                  exact decide_eq_of_iff (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
  | inst _ _ =>
      cases n₂ with
      | src q =>
          cases q with
          | mk o _ =>
              cases o with
              | nil =>
                  simp only [CodeId.same, codeFwd]
                  exact decide_eq_of_iff (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
              | cons _ _ =>
                  simp only [CodeId.same, codeFwd]
                  exact decide_eq_of_iff (Iff.intro (fun h => nomatch h) (fun h => nomatch h))
      | inst _ _ =>
          simp only [CodeId.same, codeFwd]
          exact decide_eq_of_iff (codeFwd_eq_iff _ _).symm

omit [DecidableEq S] [DecidableEq X] in
private def mapC {Y Z : Type v} (f : Nm Y → Nm Z) : Tm S Y → Tm S Z
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (f n)
  | .pvar n => .pvar (f n)
  | .lam x _ b => .lam (f x) [] (mapC f b)
  | .app a b => .app (mapC f a) (mapC f b)
  | .quote c => .quote (mapC f c)
  | .ctx ks c => .ctx (ks.map f) (mapC f c)
  | .pquote c => .pquote (mapC f c)
  | .letP p w b => .letP (mapC f p) (mapC f w) (mapC f b)
  | .alt t₁ t₂ => .alt (mapC f t₁) (mapC f t₂)

omit [DecidableEq S] [DecidableEq X] in
/-- Every lambda produced as code has an empty own list, including under a
quotation. -/
private def ownEmpty : Tm S X → Prop
  | .lam _ own b => own = [] ∧ ownEmpty b
  | .app f a => ownEmpty f ∧ ownEmpty a
  | .quote c => ownEmpty c
  | .pquote c => ownEmpty c
  | .letP p w b => ownEmpty p ∧ ownEmpty w ∧ ownEmpty b
  | .alt t₁ t₂ => ownEmpty t₁ ∧ ownEmpty t₂
  | _ => True

omit [DecidableEq S] [DecidableEq X] in
private theorem codeFwd_injective :
    Function.Injective (codeFwd : Nm (Slot X) → Nm (BId X)) :=
  fun a b h => (codeFwd_eq_iff a b).1 h

omit [DecidableEq S] [DecidableEq X] in
private theorem ownEmpty_fold {Y : Type v} (ps : List (Nm Y)) {t : Tm S Y}
    (h : ownEmpty t) : ownEmpty (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact h
  | cons _ _ ih => exact ⟨rfl, ih⟩

omit [DecidableEq S] in
private theorem ownEmpty_seal {Y : Type v} [DecidableEq Y] {t : Tm S Y}
    (h : ownEmpty t) : ownEmpty (sealParams t) := by
  unfold sealParams
  exact ownEmpty_fold _ h

omit [DecidableEq S] [DecidableEq X] in
private theorem map_filter_binder {α β : Type v} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (x : α) (l : List α) :
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
        have hkf : decide (f a ≠ f x) = true := decide_eq_true (hf.ne ha)
        rw [List.filter_cons_of_pos (p := fun y => decide (y ≠ x)) hk,
          List.map_cons, List.map_cons,
          List.filter_cons_of_pos (p := fun z => decide (z ≠ f x)) hkf, ih]

omit [DecidableEq S] in
private theorem paramOcc_mapC {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) :
    ∀ t : Tm S Y, paramOcc (mapC f t) = (paramOcc t).map f
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x _ b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf b, map_filter_binder hf x]
  | .app a b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf a, paramOcc_mapC hf b, List.map_append]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by
      simp only [mapC, paramOcc, paramOcc_mapC hf c]
  | .letP p w b => by
      simp only [mapC, paramOcc, paramOcc_mapC hf p, paramOcc_mapC hf w, paramOcc_mapC hf b,
        List.map_append]
  | .alt t₁ t₂ => by
      simp only [mapC, paramOcc, paramOcc_mapC hf t₁, paramOcc_mapC hf t₂, List.map_append]

omit [DecidableEq S] in
private theorem mapC_fold {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    (f : Nm Y → Nm Z) (ps : List (Nm Y)) (t : Tm S Y) :
    mapC f (ps.foldr (fun p acc => .lam p [] acc) t) =
      (ps.map f).foldr (fun p acc => .lam p [] acc) (mapC f t) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr, List.map, mapC, ih]

omit [DecidableEq S] in
private theorem mapC_seal {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) (t : Tm S Y) :
    mapC f (sealParams t) = sealParams (mapC f t) := by
  unfold sealParams
  rw [mapC_fold, paramOcc_mapC hf]

omit [DecidableEq S] in
private theorem codeAt_ownEmpty (holes : Option (X → Owner))
    (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X) :
    ownEmpty (codeAt holes penv senv pos s) := by
  induction s generalizing holes penv senv pos with
  | sym _ => simp [codeAt, ownEmpty]
  | fn _ => simp [codeAt, ownEmpty]
  | sv y =>
      simp only [codeAt]
      cases codeLookup senv y with
      | some _ => simp [ownEmpty]
      | none => cases holes <;> simp [ownEmpty]
  | par _ =>
      simp only [codeAt]
      split <;> simp [ownEmpty]
  | lam z _ _ ih =>
      unfold codeAt
      exact ⟨rfl, ih holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])⟩
  | form z _ ih =>
      unfold codeAt
      exact ⟨rfl, ih holes ((z, codeBinder pos) :: penv) senv (pos ++ [0])⟩
  | app _ _ ihf iha =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihf _ _ _ _, iha _ _ _ _⟩
  | quote _ ih =>
      simp only [codeAt, ownEmpty]
      exact ownEmpty_seal (ih none [] [] [])
  | pquote _ ih =>
      simp only [codeAt, ownEmpty]
      exact ih _ _ _ _
  | letS _ _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | unify _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownEmpty]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, ownEmpty]
      exact ⟨iht _ _ _ _, ihu _ _ _ _⟩
  | new _ _ ih =>
      simpa [codeAt] using ih holes penv senv (pos ++ [0])

omit [DecidableEq S] in
private theorem codeBinder_ne_nil (pos : Owner) : codeBinder pos ≠ [] :=
  List.cons_ne_nil 9 (1 :: pos)

omit [DecidableEq S] [DecidableEq X] in
private theorem nil_owners : ∀ p ∈ ([] : List (X × Owner)), p.2 ≠ [] := by
  intro _ h
  simp at h

omit [DecidableEq S] [DecidableEq X] in
private theorem cons_owners {z : X} {o : Owner} {l : List (X × Owner)}
    (ho : o ≠ []) (hl : ∀ p ∈ l, p.2 ≠ []) :
    ∀ p ∈ (z, o) :: l, p.2 ≠ [] := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hl p hp

omit [DecidableEq S] [DecidableEq X] in
private theorem append_owners {l₁ l₂ : List (X × Owner)}
    (h₁ : ∀ p ∈ l₁, p.2 ≠ []) (h₂ : ∀ p ∈ l₂, p.2 ≠ []) :
    ∀ p ∈ l₁ ++ l₂, p.2 ≠ [] := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

omit [DecidableEq S] in
private theorem codeLookup_ne {l : List (X × Owner)} (hl : ∀ p ∈ l, p.2 ≠ [])
    {y : X} {o : Owner} (h : codeLookup l y = some o) : o ≠ [] := by
  induction l with
  | nil => simp [codeLookup] at h
  | cons p rest ih =>
      obtain ⟨z, oz⟩ := p
      have hoz : oz ≠ [] := hl (z, oz) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 ≠ [] := fun q hq => hl q (List.mem_cons_of_mem _ hq)
      simp only [codeLookup] at h
      by_cases hz : z = y
      · simp only [hz, if_true, Option.some.injEq] at h
        exact h ▸ hoz
      · simp only [hz, if_false] at h
        exact ih hrest h

omit [DecidableEq S] [DecidableEq X] in
private theorem svBinds_ne (pos : Owner) :
    ∀ (s : Src S X), ∀ p ∈ svBinds pos s, p.2 ≠ []
  | .sv _, _, h => by
      simp only [svBinds, List.mem_singleton] at h
      subst h
      exact codeBinder_ne_nil pos
  | .app f a, _, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact svBinds_ne (pos ++ [0]) f _ h
      · exact svBinds_ne (pos ++ [1]) a _ h
  | .alt t₁ t₂, _, h => by
      simp only [svBinds, List.mem_append] at h
      rcases h with h | h
      · exact svBinds_ne (pos ++ [0]) t₁ _ h
      · exact svBinds_ne (pos ++ [1]) t₂ _ h
  | .sym _, _, h | .fn _, _, h | .par _, _, h | .lam _ _ _, _, h | .quote _, _, h
    | .pquote _, _, h | .letS _ _ _ _, _, h | .unify _ _ _, _, h | .new _ _, _, h
    | .form _ _, _, h => by
      simp [svBinds] at h

omit [DecidableEq S] in
private theorem codeIAt_eq_map (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, p.2 ≠ []) (hsenv : ∀ p ∈ senv, p.2 ≠ []) :
    ∀ s : Src S X,
      mapC codeFwd (codeAt none penv senv pos s) = codeIAt none penv senv pos s
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup senv y with
      | none => rfl
      | some p =>
          have hp : p ≠ [] := codeLookup_ne hsenv h
          cases p with
          | nil => exact absurd rfl hp
          | cons _ _ => rfl
  | .par z => by
      simp only [codeAt, codeIAt]
      cases h : codeLookup penv z with
      | none => rfl
      | some p =>
          have hp : p ≠ [] := codeLookup_ne hpenv h
          cases p with
          | nil => exact absurd rfl hp
          | cons _ _ => rfl
  | .lam z _ b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_owners (codeBinder_ne_nil pos) hpenv) hsenv b]
      rw [codeFwd_binder]
  | .form z b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_owners (codeBinder_ne_nil pos) hpenv) hsenv b]
      rw [codeFwd_binder]
  | .app f a => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map penv senv (pos ++ [0]) hpenv hsenv f,
        codeIAt_eq_map penv senv (pos ++ [1]) hpenv hsenv a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapC]
      rw [mapC_seal codeFwd_injective]
      exact congrArg Tm.quote (congrArg sealParams
        (codeIAt_eq_map [] [] [] nil_owners nil_owners c))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapC, codeIAt_eq_map [] [] [] nil_owners nil_owners c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) p,
        codeIAt_eq_map penv senv (pos ++ [1]) hpenv hsenv w,
        codeIAt_eq_map penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) p,
        codeIAt_eq_map penv senv (pos ++ [1]) hpenv hsenv w,
        codeIAt_eq_map penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapC,
        codeIAt_eq_map penv senv (pos ++ [0]) hpenv hsenv t₁,
        codeIAt_eq_map penv senv (pos ++ [1]) hpenv hsenv t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt, codeIAt_eq_map penv senv (pos ++ [0]) hpenv hsenv b]

private theorem codeEq_map (t₁ t₂ : Tm S (Slot X)) (h₁ : ownEmpty t₁) (h₂ : ownEmpty t₂) :
    codeEq t₁ t₂ = codeEq (mapC codeFwd t₁) (mapC codeFwd t₂) := by
  induction t₁ generalizing t₂ with
  | sym _ =>
      cases h₁
      cases t₂ with
      | sym _ =>
          cases h₂
          simp [codeEq, mapC]
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | fn _ =>
      cases h₁
      cases t₂ with
      | fn _ =>
          cases h₂
          simp [codeEq, mapC]
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | var _ =>
      cases h₁
      cases t₂ with
      | var _ =>
          cases h₂
          simp [codeEq, mapC, same_fwd]
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | pvar _ =>
      cases h₁
      cases t₂ with
      | pvar _ =>
          cases h₂
          simp [codeEq, mapC, same_fwd]
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | lam _ _ _ ih =>
      cases t₂ with
      | lam _ _ b' =>
          rcases h₁ with ⟨rfl, hb⟩
          rcases h₂ with ⟨rfl, hb'⟩
          simp only [codeEq, mapC]
          rw [same_fwd, ih b' hb hb']
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | app _ _ ihf iha =>
      cases t₂ with
      | app f' a' =>
          rcases h₁ with ⟨hf, ha⟩
          rcases h₂ with ⟨hf', ha'⟩
          simp only [codeEq, mapC]
          rw [ihf f' hf hf', iha a' ha ha']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | quote _ ih =>
      cases t₂ with
      | quote c' =>
          simp only [codeEq, mapC]
          rw [ih c' h₁ h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | pquote _ ih =>
      cases t₂ with
      | pquote c' =>
          simp only [codeEq, mapC]
          rw [ih c' h₁ h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [codeEq, mapC]
  | letP _ _ _ ihp ihw ihb =>
      cases t₂ with
      | letP p' w' b' =>
          rcases h₁ with ⟨hp, hw, hb⟩
          rcases h₂ with ⟨hp', hw', hb'⟩
          simp only [codeEq, mapC]
          rw [ihp p' hp hp', ihw w' hw hw', ihb b' hb hb']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | alt _ _ =>
          simp [codeEq, mapC]
  | alt _ _ iht ihu =>
      cases t₂ with
      | alt t' u' =>
          rcases h₁ with ⟨ht, hu⟩
          rcases h₂ with ⟨ht', hu'⟩
          simp only [codeEq, mapC]
          rw [iht t' ht ht', ihu u' hu hu']
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ =>
          simp [codeEq, mapC]
  | ctx _ _ _ => cases t₂ <;> simp [codeEq, mapC]

/-- `codeEq` gives the same answer for the slot elaboration and the identity
elaboration of two pieces of code, at any quotation-relative positions.
A `new` block contributes the code of its body. -/
theorem codeEq_at (penv₁ penv₂ senv₁ senv₂ : List (X × Owner)) (pos₁ pos₂ : Owner)
    (hp₁ : ∀ p ∈ penv₁, p.2 ≠ []) (hp₂ : ∀ p ∈ penv₂, p.2 ≠ [])
    (hs₁ : ∀ p ∈ senv₁, p.2 ≠ []) (hs₂ : ∀ p ∈ senv₂, p.2 ≠ [])
    (s s' : Src S X) :
    codeEq (codeAt none penv₁ senv₁ pos₁ s) (codeAt none penv₂ senv₂ pos₂ s') =
      codeEq (codeIAt none penv₁ senv₁ pos₁ s) (codeIAt none penv₂ senv₂ pos₂ s') := by
  rw [← codeIAt_eq_map penv₁ senv₁ pos₁ hp₁ hs₁ s,
    ← codeIAt_eq_map penv₂ senv₂ pos₂ hp₂ hs₂ s']
  exact codeEq_map (codeAt none penv₁ senv₁ pos₁ s) (codeAt none penv₂ senv₂ pos₂ s')
    (codeAt_ownEmpty none penv₁ senv₁ pos₁ s) (codeAt_ownEmpty none penv₂ senv₂ pos₂ s')

/-- Sealed code agrees: `(lam w w)` and `(lam z z)` compare alike in both models. -/
theorem codeEq_codeOf_codeI (s s' : Src S X) :
    codeEq (codeOf s) (codeOf s') = codeEq (codeI s) (codeI s') := by
  simp only [codeOf, codeI]
  have hs : mapC codeFwd (sealParams (codeAt none [] [] [] s)) =
      sealParams (codeIAt none [] [] [] s) := by
    rw [mapC_seal codeFwd_injective]
    exact congrArg sealParams (codeIAt_eq_map [] [] [] nil_owners nil_owners s)
  have hs' : mapC codeFwd (sealParams (codeAt none [] [] [] s')) =
      sealParams (codeIAt none [] [] [] s') := by
    rw [mapC_seal codeFwd_injective]
    exact congrArg sealParams (codeIAt_eq_map [] [] [] nil_owners nil_owners s')
  rw [← hs, ← hs']
  exact codeEq_map _ _
    (ownEmpty_seal (codeAt_ownEmpty none [] [] [] s))
    (ownEmpty_seal (codeAt_ownEmpty none [] [] [] s'))

end Mettapedia.GSLT.LanguageDef.TemplateScope
