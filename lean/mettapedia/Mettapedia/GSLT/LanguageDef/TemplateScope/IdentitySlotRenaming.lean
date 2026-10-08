import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotConverse
import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotProfiles
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshConnections
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotedCodeEq

/-!
# Template scope: the identity model is the slot model, up to renaming

The slot model (`TemplateScope.Spectrum`: names are slots `(owner, spelling)`,
a `let` that introduces names and a `new` block are activations) and the
identity model (`TemplateScope.LexicalFresh`: names are binder identities,
every binder is allocated in its frame) run the same programs to the same
observations, up to a renaming of names, under rule M and under lexical fresh.

## Main results

* `renaming_M`, `renaming_LF` — **the renaming theorem**: on admissible
  programs, the slot model's run and the identity model's run are defined
  together, and when both are defined their bags of results correspond in
  order, each pair of results related by its own injective renaming of the
  names in play: the answers are related values and the final stores are
  related (`Renamed`).
* `transfer` — **the translator's correctness in the slot model**: the slot
  model's lexical fresh on the translated program is defined exactly when the
  slot model's rule M on the source is, and both bags are renamings, result by
  result, of the identity model's bag of rule M on the source (which is the
  identity model's bag of lexical fresh on the translation, `run_toLexical`).

## Admissible text

No `new` block with names on the spine of a pattern, every parameter bound
(`Src.Admissible`). A quotation may stand in pattern position. Each condition
is needed: `newPat_needed` and `freePar_needed` name a program violating it
on which the two models differ.

## What the renaming is not

The renaming is per result: the two models may share a name across two results
of one bag in different ways (the identity model allocates in the frame, the
slot model at each activation), so the printed bag, which numbers names across
the whole bag, can differ.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace Src

variable {S : Type u} {X : Type v} [DecidableEq X]

/-- **Admissible authored text**: no `new` block with names on the spine of a
pattern, every parameter bound. A quotation may stand in pattern position. -/
def Admissible (t : Src S X) : Prop :=
  t.patsNewFree = true ∧ t.freePars = []

instance (t : Src S X) : Decidable t.Admissible :=
  inferInstanceAs (Decidable (_ ∧ _))

end Src

namespace IdSlot

variable {S : Type u} {X : Type v} [DecidableEq X]

/-! ## Sealed code -/

theorem ownNil_fold {Y : Type v} (ps : List (Nm Y)) {t : Tm S Y} (h : ownNil t) :
    ownNil (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact h
  | cons _ _ ih => exact ⟨rfl, ih⟩

theorem ownNil_seal {Y : Type v} [DecidableEq Y] {t : Tm S Y} (h : ownNil t) :
    ownNil (sealParams t) := by
  unfold sealParams
  exact ownNil_fold _ h

theorem ownNil_codeAt (holes : Option (X → Owner)) (penv senv : List (X × Owner)) (pos : Owner)
    (s : Src S X) : ownNil (codeAt holes penv senv pos s) := by
  induction s generalizing holes penv senv pos with
  | sym _ => simp [codeAt, ownNil]
  | fn _ => simp [codeAt, ownNil]
  | sv y =>
      simp only [codeAt]
      cases codeLookup senv y with
      | some _ => simp [ownNil]
      | none => cases holes <;> simp [ownNil]
  | par _ =>
      simp only [codeAt]
      split <;> simp [ownNil]
  | lam z _ _ ih =>
      unfold codeAt
      exact ⟨rfl, ih _ _ _ _⟩
  | form z _ ih =>
      unfold codeAt
      exact ⟨rfl, ih _ _ _ _⟩
  | app _ _ ihf iha =>
      simp only [codeAt, ownNil]
      exact ⟨ihf _ _ _ _, iha _ _ _ _⟩
  | quote _ ih =>
      simp only [codeAt, ownNil]
      exact ownNil_seal (ih none [] [] [])
  | pquote _ ih =>
      simp only [codeAt, ownNil]
      exact ih _ _ _ _
  | letS _ _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownNil]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | unify _ _ _ ihp ihw ihb =>
      simp only [codeAt, ownNil]
      exact ⟨ihp _ _ _ _, ihw _ _ _ _, ihb _ _ _ _⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, ownNil]
      exact ⟨iht _ _ _ _, ihu _ _ _ _⟩
  | new _ _ ih =>
      simpa [codeAt] using ih holes penv senv (pos ++ [0])

omit [DecidableEq X] in
theorem mapCode_back_fwd {t : Tm S (Slot X)} (h : ownNil t) :
    mapCode codeBack (mapCode codeFwd t) = t := by
  induction t with
  | sym _ => rfl
  | fn _ => rfl
  | var n => simp [mapCode, codeBack_codeFwd]
  | pvar n => simp [mapCode, codeBack_codeFwd]
  | lam x own b ih =>
      simp only [ownNil] at h
      rcases h with ⟨rfl, hb⟩
      simp only [mapCode, codeBack_codeFwd, ih hb]
  | app _ _ ihf iha =>
      simp only [ownNil] at h
      simp only [mapCode, ihf h.1, iha h.2]
  | quote _ ih =>
      simp only [ownNil] at h
      simp only [mapCode, ih h]
  | ctx ks c ih =>
      simp only [ownNil] at h
      have hb := ih h
      simp only [mapCode, hb, List.map_map]
      congr
      induction ks with
      | nil => rfl
      | cons n ns ihk => simp [List.map_cons, codeBack_codeFwd, ihk]
  | pquote _ ih =>
      simp only [ownNil] at h
      simp only [mapCode, ih h]
  | letP _ _ _ ihp ihw ihb =>
      simp only [ownNil] at h
      simp only [mapCode, ihp h.1, ihw h.2.1, ihb h.2.2]
  | alt _ _ ih₁ ih₂ =>
      simp only [ownNil] at h
      simp only [mapCode, ih₁ h.1, ih₂ h.2]

omit [DecidableEq X] in
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

private theorem paramOcc_mapCode {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) :
    ∀ t : Tm S Y, paramOcc (mapCode f t) = (paramOcc t).map f
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x _ b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf b, map_filter_binder hf x]
  | .app a b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf a, paramOcc_mapCode hf b, List.map_append]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf c]
  | .letP p w b => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf p, paramOcc_mapCode hf w,
        paramOcc_mapCode hf b, List.map_append]
  | .alt t₁ t₂ => by
      simp only [mapCode, paramOcc, paramOcc_mapCode hf t₁, paramOcc_mapCode hf t₂, List.map_append]

private theorem mapCode_fold {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    (f : Nm Y → Nm Z) (ps : List (Nm Y)) (t : Tm S Y) :
    mapCode f (ps.foldr (fun p acc => .lam p [] acc) t) =
      (ps.map f).foldr (fun p acc => .lam p [] acc) (mapCode f t) := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldr, List.map, mapCode, ih]

theorem mapCode_seal {Y Z : Type v} [DecidableEq Y] [DecidableEq Z]
    {f : Nm Y → Nm Z} (hf : Function.Injective f) (t : Tm S Y) :
    mapCode f (sealParams t) = sealParams (mapCode f t) := by
  unfold sealParams
  rw [mapCode_fold, paramOcc_mapCode hf]

omit [DecidableEq X] in
private theorem nil_owners : ∀ p ∈ ([] : List (X × Owner)), p.2 ≠ [] := by
  intro _ h
  simp at h

omit [DecidableEq X] in
private theorem cons_owners {z : X} {o : Owner} {l : List (X × Owner)}
    (ho : o ≠ []) (hl : ∀ p ∈ l, p.2 ≠ []) :
    ∀ p ∈ (z, o) :: l, p.2 ≠ [] := by
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hl p hp

omit [DecidableEq X] in
private theorem append_owners {l₁ l₂ : List (X × Owner)}
    (h₁ : ∀ p ∈ l₁, p.2 ≠ []) (h₂ : ∀ p ∈ l₂, p.2 ≠ []) :
    ∀ p ∈ l₁ ++ l₂, p.2 ≠ [] := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

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

omit [DecidableEq X] in
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

/-- Sealed code in the slot model is sealed code in the identity model.  The
environments are the binders of this quotation, most recent first.  Every
binder owner is nonempty: owner `[]` is the query's head slot, not a binder. -/
theorem mapCode_codeAt (penv senv : List (X × Owner)) (pos : Owner)
    (hpenv : ∀ p ∈ penv, p.2 ≠ []) (hsenv : ∀ p ∈ senv, p.2 ≠ []) :
    ∀ s : Src S X,
      mapCode codeFwd (codeAt none penv senv pos s) = codeIAt none penv senv pos s
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
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_owners (codeBinder_ne_nil pos) hpenv) hsenv b]
      rw [show codeFwd (.src (codeBinder pos, z)) =
          .src (.code z (codeBinder pos)) by simp only [codeBinder]; rfl]
  | .form z b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (cons_owners (codeBinder_ne_nil pos) hpenv) hsenv b]
      rw [show codeFwd (.src (codeBinder pos, z)) =
          .src (.code z (codeBinder pos)) by simp only [codeBinder]; rfl]
  | .app f a => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt penv senv (pos ++ [0]) hpenv hsenv f,
        mapCode_codeAt penv senv (pos ++ [1]) hpenv hsenv a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapCode]
      rw [mapCode_seal codeFwd_injective]
      exact congrArg Tm.quote (congrArg sealParams
        (mapCode_codeAt [] [] [] nil_owners nil_owners c))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt [] [] [] nil_owners nil_owners c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) p,
        mapCode_codeAt penv senv (pos ++ [1]) hpenv hsenv w,
        mapCode_codeAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) p,
        mapCode_codeAt penv senv (pos ++ [1]) hpenv hsenv w,
        mapCode_codeAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv
          (append_owners (svBinds_ne (pos ++ [0]) p) hsenv) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeAt penv senv (pos ++ [0]) hpenv hsenv t₁,
        mapCode_codeAt penv senv (pos ++ [1]) hpenv hsenv t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt,
        mapCode_codeAt penv senv (pos ++ [0]) hpenv hsenv b]

/-- Sealed code in the identity model is sealed code in the slot model. -/
theorem mapCode_codeIAt (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ s : Src S X,
      mapCode codeBack (codeIAt none penv senv pos s) = codeAt none penv senv pos s
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv y => by
      simp only [codeAt, codeIAt]
      cases codeLookup senv y <;> rfl
  | .par z => by
      simp only [codeAt, codeIAt]
      cases codeLookup penv z <;> rfl
  | .lam z _ b => by
      simp only [codeAt, codeIAt, mapCode, codeBack,
        mapCode_codeIAt ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b]
  | .form z b => by
      simp only [codeAt, codeIAt, mapCode, codeBack,
        mapCode_codeIAt ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b]
  | .app f a => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt penv senv (pos ++ [0]) f, mapCode_codeIAt penv senv (pos ++ [1]) a]
  | .quote c => by
      simp only [codeAt, codeIAt, mapCode]
      have hfwd : mapCode codeFwd (codeAt none [] [] [] c) = codeIAt none [] [] [] c :=
        mapCode_codeAt [] [] [] nil_owners nil_owners c
      rw [← hfwd, ← mapCode_seal codeFwd_injective]
      exact congrArg Tm.quote
        (mapCode_back_fwd (ownNil_seal (ownNil_codeAt none [] [] [] c)))
  | .pquote c => by
      simp only [codeAt, codeIAt, mapCode, mapCode_codeIAt [] [] [] c]
  | .letS p w b _ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p,
        mapCode_codeIAt penv senv (pos ++ [1]) w,
        mapCode_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b]
  | .unify p w b => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p,
        mapCode_codeIAt penv senv (pos ++ [1]) w,
        mapCode_codeIAt penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b]
  | .alt t₁ t₂ => by
      simp only [codeAt, codeIAt, mapCode,
        mapCode_codeIAt penv senv (pos ++ [0]) t₁, mapCode_codeIAt penv senv (pos ++ [1]) t₂]
  | .new _ b => by
      simp only [codeAt, codeIAt, mapCode_codeIAt penv senv (pos ++ [0]) b]

theorem mapCode_codeOf (s : Src S X) : mapCode codeFwd (codeOf s) = codeI s := by
  simp only [codeOf, codeI]
  rw [mapCode_seal codeFwd_injective]
  exact congrArg sealParams (mapCode_codeAt [] [] [] nil_owners nil_owners s)

theorem mapCode_codeI (s : Src S X) : mapCode codeBack (codeI s) = codeOf s := by
  rw [← mapCode_codeOf]
  exact mapCode_back_fwd (ownNil_seal (ownNil_codeAt none [] [] [] s))

/-- **Sealed code is related bi-uniquely**: the two code maps forget the same
information (crossing sets, `new` declarations, `let` versus `unify`). -/
theorem SC_biUnique : (SC : Setting S (Slot X) (BId X)).BiUnique := by
  rintro _ _ _ _ ⟨s, rfl, rfl⟩ ⟨s', rfl, rfl⟩
  constructor
  · intro h
    rw [← mapCode_codeOf s, h, mapCode_codeOf]
  · intro h
    rw [← mapCode_codeI s, h, mapCode_codeI]

/-- Sealed code compares alike: binders by position, free parameters by spelling. -/
theorem SC_codeAgree [DecidableEq S] : (SC : Setting S (Slot X) (BId X)).CodeAgree := by
  rintro _ _ _ _ ⟨s, rfl, rfl⟩ ⟨s', rfl, rfl⟩
  rw [codeEq_codeOf_codeI]

/-! ## Pattern code matches sealed code -/

theorem codeBound_ne_free {o : Owner} (h : codeBound o = true) : o ≠ codeFreeParam := by
  intro e
  subst e
  exact Bool.false_ne_true h

theorem codeBound_nil : codeBound [] = false := rfl

omit [DecidableEq X] in
theorem codeFreeS_param (y : X) : codeFreeS (.src (codeFreeParam, y)) = true := rfl

omit [DecidableEq X] in
theorem codeFreeI_param (y : X) : codeFreeI (.src (.code y codeFreeParam)) = true := rfl

omit [DecidableEq X] in
theorem codeFreeS_bound {o : Owner} {y : X} (h : codeBound o = true) :
    codeFreeS (.src (o, y)) = false := by
  simp only [codeFreeS]
  exact decide_eq_false (codeBound_ne_free h)

omit [DecidableEq X] in
theorem codeFreeI_bound {o : Owner} {y : X} (h : codeBound o = true) :
    codeFreeI (.src (.code y o)) = false := by
  simp only [codeFreeI]
  exact decide_eq_false (codeBound_ne_free h)

omit [DecidableEq X] in
theorem ne_of_codeFree {a b : Nm (Slot X)} (ha : codeFreeS a = false)
    (hb : codeFreeS b = true) : a ≠ b := by
  intro h
  rw [h] at ha
  exact Bool.false_ne_true (ha.symm.trans hb)

/-- `if` on a `Bool` is `ite (c = true)`, so `cond` does not rewrite it. -/
theorem ite_bool_false {α : Sort u} {a b : α} : (if false then a else b) = b :=
  if_neg Bool.false_ne_true

theorem ite_bool_true {α : Sort u} {a b : α} : (if true then a else b) = a :=
  if_pos rfl

/-- The spelling test in `CodeId.same` is a `Bool` conjunction. -/
theorem ite_bool_and_left {α : Sort u} {p q : Prop} [Decidable p] [Decidable q]
    {a b : α} (h : ¬ p) : (if decide p && decide q then a else b) = b := by
  simp only [decide_eq_false h, Bool.false_and, ite_bool_false]

theorem ite_bool_and_right {α : Sort u} {p q : Prop} [Decidable p] [Decidable q]
    {a b : α} (h : ¬ q) : (if decide p && decide q then a else b) = b := by
  simp only [decide_eq_false h, Bool.and_false, ite_bool_false]

theorem freeNames_lam_nil {Y : Type v} [DecidableEq Y] (x : Nm Y) (b : Tm S Y) :
    freeNames (.lam x [] b) = freeNames b := by
  simp only [freeNames]
  induction freeNames b with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.filter, ownKey_nil n, Bool.not_false, ih]

/-- `CodeId.same` on two slot names, as the instance writes it. -/
theorem same_src_eq (o₁ o₂ : Owner) (y₁ y₂ : X) :
    CodeId.same (.src (o₁, y₁) : Nm (Slot X)) (.src (o₂, y₂)) =
      if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
      else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
      else decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) := rfl

/-- `CodeId.same` on two code names, as the instance writes it. -/
theorem same_code_eq (y₁ y₂ : X) (o₁ o₂ : Owner) :
    CodeId.same (.src (.code y₁ o₁) : Nm (BId X)) (.src (.code y₂ o₂)) =
      if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
      else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
      else decide ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) := rfl

theorem same_instL_src {ρ : Path} {n : Nm (Slot X)} {o : Owner} {y : X} :
    CodeId.same (.inst ρ n) (.src (o, y)) = false :=
  decide_eq_false fun h => by cases h

theorem same_instI_src {ρ : Path} {n : Nm (BId X)} {b : BId X} :
    CodeId.same (.inst ρ n) (.src b) = false :=
  decide_eq_false fun h => by cases h

theorem same_slot_code {k : SlotId X} {y : X} {o : Owner} :
    CodeId.same (.src (.slot k) : Nm (BId X)) (.src (.code y o)) = false :=
  decide_eq_false fun h => by cases h

theorem same_par_code {z : X} {pos o : Owner} {y : X} :
    CodeId.same (.src (.par z pos) : Nm (BId X)) (.src (.code y o)) = false :=
  decide_eq_false fun h => by cases h

theorem decide_src_owner_ne {o₁ o₂ : Owner} {y₁ y₂ : X} (h : o₁ ≠ o₂) :
    decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂)) = false :=
  decide_eq_false fun he => by
    simp only [Nm.src.injEq, Prod.mk.injEq] at he
    exact h he.1

theorem decide_code_owner_ne {y₁ y₂ : X} {o₁ o₂ : Owner} (h : o₁ ≠ o₂) :
    decide ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂)) = false :=
  decide_eq_false fun he => by
    simp only [Nm.src.injEq, BId.code.injEq] at he
    exact h he.2

/-- A binder of code is not `CodeId.same` a query hole. -/
theorem same_bound_query {n : Nm (Slot X)} (hn : holeRecS n = false) (y : X) :
    CodeId.same n (.src ([], y)) = false := by
  cases n with
  | inst _ _ => exact same_instL_src
  | src p =>
      obtain ⟨o, z⟩ := p
      have hb : codeBound o = true := by
        simp only [holeRecS] at hn
        cases hc : codeBound o with
        | true => rfl
        | false =>
            simp only [hc, Bool.not_false] at hn
            exact absurd hn Bool.false_ne_true.symm
      have hne : o ≠ [] := fun h => by
        rw [h, codeBound_nil] at hb
        exact Bool.false_ne_true hb
      have hnf : o ≠ codeFreeParam := codeBound_ne_free hb
      rw [same_src_eq]
      simp only [hb, codeBound_nil, Bool.and_false, ite_bool_false,
        decide_eq_false hnf, Bool.false_and, ite_bool_false, decide_src_owner_ne hne]

/-- A binder of code is not `CodeId.same` a query hole, on the identity side. -/
theorem same_bound_queryI {n : Nm (BId X)} (hn : holeRecI n = false) (y : X) :
    CodeId.same n (.src (.code y [])) = false := by
  cases n with
  | inst _ _ => exact same_instI_src
  | src b =>
      cases b with
      | slot _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | par _ _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | code z o =>
          have hb : codeBound o = true := by
            simp only [holeRecI] at hn
            cases hc : codeBound o with
            | true => rfl
            | false =>
                simp only [hc, Bool.not_false] at hn
                exact absurd hn Bool.false_ne_true.symm
          have hne : o ≠ [] := fun h => by
            rw [h, codeBound_nil] at hb
            exact Bool.false_ne_true hb
          have hnf : o ≠ codeFreeParam := codeBound_ne_free hb
          rw [same_code_eq]
          simp only [hb, codeBound_nil, Bool.and_false, ite_bool_false,
            decide_eq_false hnf, Bool.false_and, ite_bool_false, decide_code_owner_ne hne]

/-- A binder of code is not `CodeId.same` a head slot. A root hole reads as
that slot, and a non-hole is a code binder. -/
theorem same_bound_head {n : Nm (BId X)} (hn : holeRecI n = false) (k : SlotId X) :
    CodeId.same n (.src (.slot k)) = false := by
  cases n with
  | inst _ _ => exact same_instI_src
  | src b =>
      cases b with
      | slot _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | par _ _ =>
          simp only [holeRecI] at hn
          exact absurd hn Bool.false_ne_true.symm
      | code _ _ => exact decide_eq_false fun h => by cases h

/-- Free parameters of code still free in a term: a parameter `matchCode` compares
by spelling, not under a lambda of this term and not inside a sealed quotation. -/
def codeFreePvars : Tm S (Slot X) → List (Nm (Slot X))
  | .sym _ => []
  | .fn _ => []
  | .var _ => []
  | .pvar n => if codeFreeS n then [n] else []
  | .lam x _ b => (codeFreePvars b).filter fun p => decide (p ≠ x)
  | .app f a => codeFreePvars f ++ codeFreePvars a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => codeFreePvars c
  | .letP p w b => codeFreePvars p ++ codeFreePvars w ++ codeFreePvars b
  | .alt t₁ t₂ => codeFreePvars t₁ ++ codeFreePvars t₂

theorem codeFreePvars_free {t : Tm S (Slot X)} {n : Nm (Slot X)}
    (h : n ∈ codeFreePvars t) : codeFreeS n = true := by
  induction t with
  | pvar x =>
      cases hc : codeFreeS x with
      | true =>
          simp only [codeFreePvars, hc, ite_true, List.mem_singleton] at h
          exact h ▸ hc
      | false =>
          simp only [codeFreePvars, hc, ite_bool_false, List.mem_nil_iff] at h
  | lam _ _ _ ih =>
      simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq] at h
      exact ih h.1
  | app _ _ ihf iha =>
      simp only [codeFreePvars, List.mem_append] at h
      rcases h with h | h
      · exact ihf h
      · exact iha h
  | pquote _ ih =>
      simp only [codeFreePvars] at h
      exact ih h
  | letP _ _ _ ihp ihw ihb =>
      simp only [codeFreePvars] at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact ihp h
        · exact ihw h
      · exact ihb h
  | alt _ _ iht ihu =>
      simp only [codeFreePvars, List.mem_append] at h
      rcases h with h | h
      · exact iht h
      · exact ihu h
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      simp only [codeFreePvars, List.mem_nil_iff] at h

theorem codeFreePvars_sub {t : Tm S (Slot X)} {n : Nm (Slot X)}
    (h : n ∈ codeFreePvars t) : n ∈ paramOcc t := by
  induction t with
  | pvar x =>
      cases hc : codeFreeS x with
      | true =>
          simp only [codeFreePvars, hc, ite_true, List.mem_singleton] at h
          simp [paramOcc, h]
      | false =>
          simp only [codeFreePvars, hc, ite_bool_false, List.mem_nil_iff] at h
  | lam x _ b ih =>
      simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq] at h
      simp only [paramOcc, List.mem_filter, decide_eq_true_eq]
      exact ⟨ih h.1, h.2⟩
  | app _ _ ihf iha =>
      simp only [codeFreePvars, List.mem_append] at h
      simp only [paramOcc, List.mem_append]
      rcases h with h | h
      · exact Or.inl (ihf h)
      · exact Or.inr (iha h)
  | pquote _ ih =>
      simp only [codeFreePvars] at h
      simpa [paramOcc] using ih h
  | letP _ _ _ ihp ihw ihb =>
      simp only [codeFreePvars] at h
      simp only [paramOcc, List.mem_append]
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl (Or.inl (ihp h))
        · exact Or.inl (Or.inr (ihw h))
      · exact Or.inr (ihb h)
  | alt _ _ iht ihu =>
      simp only [codeFreePvars, List.mem_append] at h
      simp only [paramOcc, List.mem_append]
      rcases h with h | h
      · exact Or.inl (iht h)
      · exact Or.inr (ihu h)
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      simp only [codeFreePvars, List.mem_nil_iff] at h

theorem codeFreePvars_fold (ps : List (Nm (Slot X))) (t : Tm S (Slot X)) :
    ∀ n ∈ codeFreePvars (ps.foldr (fun p acc => .lam p [] acc) t),
      n ∈ codeFreePvars t ∧ n ∉ ps := by
  induction ps with
  | nil =>
      intro n hn
      exact ⟨hn, fun h => by cases h⟩
  | cons p ps ih =>
      intro n hn
      simp only [List.foldr] at hn
      have hmem : n ∈ codeFreePvars (ps.foldr (fun q acc => .lam q [] acc) t) ∧ n ≠ p := by
        simpa [codeFreePvars, List.mem_filter, decide_eq_true_eq] using hn
      obtain ⟨ht, hps⟩ := ih n hmem.1
      refine ⟨ht, ?_⟩
      intro hmem'
      rcases List.mem_cons.1 hmem' with rfl | hmem'
      · exact hmem.2 rfl
      · exact hps hmem'

theorem codeFreePvars_seal (t : Tm S (Slot X)) : codeFreePvars (sealParams t) = [] := by
  unfold sealParams
  apply List.eq_nil_iff_forall_not_mem.2
  intro n hn
  obtain ⟨ht, hnot⟩ := codeFreePvars_fold (paramOcc t) t n hn
  exact hnot (codeFreePvars_sub ht)

theorem codeFreePvars_codeOf (s : Src S X) : codeFreePvars (codeOf s) = [] := by
  simp only [codeOf]
  exact codeFreePvars_seal _

/-- A slot name written for a binder or a free parameter of code. -/
def codeNamed (n : Nm (Slot X)) : Prop :=
  ∃ o y, n = .src (o, y) ∧ (codeBound o = true ∨ o = codeFreeParam)

/-- A fragment of sealed code. Variables are query holes, parameters and binders
are code names, own lists are empty, and a quotation holds sealed code. -/
def frag : Tm S (Slot X) → Prop
  | .sym _ => True
  | .fn _ => True
  | .var n => ∃ y, n = .src ([], y)
  | .pvar n => codeNamed n
  | .lam n own b => own = [] ∧ codeNamed n ∧ frag b
  | .app f a => frag f ∧ frag a
  | .quote c => ∃ s : Src S X, c = codeOf s
  | .ctx _ _ => False
  | .pquote c => frag c
  | .letP p w b => frag p ∧ frag w ∧ frag b
  | .alt t₁ t₂ => frag t₁ ∧ frag t₂

/-- `μ` sends each free parameter of the subject to its code image, and no other
free parameter of the pattern is sent there. -/
def Align (μ : Nm (Slot X) → Nm (BId X)) (c q : Tm S (Slot X)) : Prop :=
  (∀ m ∈ codeFreePvars q, μ m = codeFwd m) ∧
  (∀ x ∈ freeParams c, ∀ m ∈ codeFreePvars q, μ x = codeFwd m → x = m)

theorem codeLookup_bound (l : List (X × Owner)) {z : X} {o : Owner}
    (hb : ∀ p ∈ l, codeBound p.2 = true) (hl : codeLookup l z = some o) :
    codeBound o = true := by
  induction l generalizing z o with
  | nil => simp [codeLookup] at hl
  | cons p rest ih =>
      obtain ⟨y, o'⟩ := p
      simp only [codeLookup] at hl
      by_cases hy : y = z
      · simp only [hy] at hl
        cases hl
        exact hb (y, o) List.mem_cons_self
      · simp only [hy] at hl
        exact ih (fun q hq => hb q (List.mem_cons_of_mem _ hq)) hl

omit [DecidableEq X] in
theorem svBinds_bound (pos : Owner) (s : Src S X) :
    ∀ p ∈ svBinds pos s, codeBound p.2 = true := by
  induction s generalizing pos with
  | sv _ =>
      intro p hp
      simp only [svBinds, List.mem_singleton] at hp
      subst hp
      exact codeBound_binder _
  | app _ _ ihf iha =>
      intro p hp
      simp only [svBinds, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ihf _ p hp
      · exact iha _ p hp
  | alt _ _ iht ihu =>
      intro p hp
      simp only [svBinds, List.mem_append] at hp
      rcases hp with hp | hp
      · exact iht _ p hp
      · exact ihu _ p hp
  | sym _ | fn _ | par _ | lam _ _ _ | quote _ | pquote _ | letS _ _ _ _ | unify _ _ _ | new _ _ | form _ _ =>
      intro p hp
      simp [svBinds] at hp

theorem frag_fold {ps : List (Nm (Slot X))} {t : Tm S (Slot X)} (ht : frag t)
    (hps : ∀ p ∈ ps, codeNamed p) :
    frag (ps.foldr (fun p acc => .lam p [] acc) t) := by
  induction ps with
  | nil => exact ht
  | cons p ps ih =>
      exact ⟨rfl, hps p List.mem_cons_self,
        ih fun q hq => hps q (List.mem_cons_of_mem _ hq)⟩

theorem frag_codeAt (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    frag (codeAt none penv senv pos s) := by
  induction s generalizing penv senv pos with
  | sym _ => simp [codeAt, frag]
  | fn _ => simp [codeAt, frag]
  | sv y =>
      simp only [codeAt]
      cases hl : codeLookup senv y with
      | some o =>
          have hb := codeLookup_bound senv hsenv hl
          simp only [frag, codeNamed]
          exact ⟨o, y, rfl, Or.inl hb⟩
      | none =>
          simp only [frag]
          exact ⟨y, rfl⟩
  | par z =>
      simp only [codeAt]
      cases hl : codeLookup penv z with
      | some o =>
          have hb := codeLookup_bound penv hpenv hl
          simp only [frag, codeNamed]
          exact ⟨o, z, rfl, Or.inl hb⟩
      | none =>
          simp only [frag, codeNamed, codeFreeParam]
          exact ⟨codeFreeParam, z, rfl, Or.inr rfl⟩
  | lam z _ _ ih =>
      simp only [codeAt, frag, codeNamed]
      exact ⟨trivial, ⟨codeBinder pos, z, rfl, Or.inl (codeBound_binder _)⟩,
        ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp
            · exact codeBound_binder _
            · exact hpenv p hp) hsenv⟩
  | form z _ ih =>
      simp only [codeAt, frag, codeNamed]
      exact ⟨trivial, ⟨codeBinder pos, z, rfl, Or.inl (codeBound_binder _)⟩,
        ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
          (fun p hp => by
            rcases List.mem_cons.1 hp with rfl | hp
            · exact codeBound_binder _
            · exact hpenv p hp) hsenv⟩
  | app _ _ ihf iha =>
      simp only [codeAt, frag]
      exact ⟨ihf penv senv (pos ++ [0]) hpenv hsenv, iha penv senv (pos ++ [1]) hpenv hsenv⟩
  | quote _ _ =>
      simp only [codeAt, frag, codeOf]
      exact ⟨_, rfl⟩
  | pquote _ ih =>
      simp only [codeAt, frag]
      exact ih [] [] [] (fun _ h => by cases h) (fun _ h => by cases h)
  | letS p _ _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      simp only [codeAt, frag]
      exact ⟨ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs,
        ihw penv senv (pos ++ [1]) hpenv hsenv,
        ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs⟩
  | unify p _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      simp only [codeAt, frag]
      exact ⟨ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs,
        ihw penv senv (pos ++ [1]) hpenv hsenv,
        ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs⟩
  | alt _ _ iht ihu =>
      simp only [codeAt, frag]
      exact ⟨iht penv senv (pos ++ [0]) hpenv hsenv, ihu penv senv (pos ++ [1]) hpenv hsenv⟩
  | new _ _ ih =>
      simpa [codeAt] using ih penv senv (pos ++ [0]) hpenv hsenv

theorem paramOcc_codeAt (penv senv : List (X × Owner)) (pos : Owner) (s : Src S X)
    (hpenv : ∀ p ∈ penv, codeBound p.2 = true) (hsenv : ∀ p ∈ senv, codeBound p.2 = true) :
    ∀ n ∈ paramOcc (codeAt none penv senv pos s), codeNamed n := by
  induction s generalizing penv senv pos with
  | sym _ => simp [codeAt, paramOcc]
  | fn _ => simp [codeAt, paramOcc]
  | sv y =>
      simp only [codeAt]
      cases hl : codeLookup senv y with
      | some o =>
          have hb := codeLookup_bound senv hsenv hl
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨o, y, hn, Or.inl hb⟩
      | none =>
          simp [paramOcc]
  | par z =>
      simp only [codeAt]
      cases hl : codeLookup penv z with
      | some o =>
          have hb := codeLookup_bound penv hpenv hl
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨o, z, hn, Or.inl hb⟩
      | none =>
          simp only [paramOcc, List.mem_singleton]
          intro n hn
          exact ⟨codeFreeParam, z, hn, Or.inr rfl⟩
  | lam z _ _ ih =>
      simp only [codeAt, paramOcc, List.mem_filter, decide_eq_true_eq]
      intro n hn
      exact ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact codeBound_binder _
          · exact hpenv p hp) hsenv n hn.1
  | form z _ ih =>
      simp only [codeAt, paramOcc, List.mem_filter, decide_eq_true_eq]
      intro n hn
      exact ih ((z, codeBinder pos) :: penv) senv (pos ++ [0])
        (fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp
          · exact codeBound_binder _
          · exact hpenv p hp) hsenv n hn.1
  | app _ _ ihf iha =>
      simp only [codeAt, paramOcc, List.mem_append]
      intro n hn
      rcases hn with hn | hn
      · exact ihf penv senv (pos ++ [0]) hpenv hsenv n hn
      · exact iha penv senv (pos ++ [1]) hpenv hsenv n hn
  | quote _ _ => simp [codeAt, paramOcc]
  | pquote _ ih =>
      simp only [codeAt, paramOcc]
      exact ih [] [] [] (fun _ h => by cases h) (fun _ h => by cases h)
  | letS p _ _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      intro n hn
      simp only [codeAt, paramOcc, List.mem_append] at hn
      rcases hn with hn | hn
      · rcases hn with hn | hn
        · exact ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs n hn
        · exact ihw penv senv (pos ++ [1]) hpenv hsenv n hn
      · exact ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs n hn
  | unify p _ _ ihp ihw ihb =>
      have hs : ∀ q ∈ svBinds (pos ++ [0]) p ++ senv, codeBound q.2 = true := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact svBinds_bound _ _ _ hq
        · exact hsenv _ hq
      intro n hn
      simp only [codeAt, paramOcc, List.mem_append] at hn
      rcases hn with hn | hn
      · rcases hn with hn | hn
        · exact ihp penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) hpenv hs n hn
        · exact ihw penv senv (pos ++ [1]) hpenv hsenv n hn
      · exact ihb penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) hpenv hs n hn
  | alt _ _ iht ihu =>
      simp only [codeAt, paramOcc, List.mem_append]
      intro n hn
      rcases hn with hn | hn
      · exact iht penv senv (pos ++ [0]) hpenv hsenv n hn
      · exact ihu penv senv (pos ++ [1]) hpenv hsenv n hn
  | new _ _ ih =>
      simpa [codeAt] using ih penv senv (pos ++ [0]) hpenv hsenv

theorem frag_codeOf (s : Src S X) : frag (codeOf s) := by
  simp only [codeOf]
  exact frag_fold (frag_codeAt [] [] [] s (fun _ h => by cases h) (fun _ h => by cases h))
    (paramOcc_codeAt [] [] [] s (fun _ h => by cases h) (fun _ h => by cases h))

/-- Ground readings of a code fragment agree, and a quotation is a code twin. -/
theorem grel_toGVal? :
    ∀ q : Tm S (Slot X), frag q →
      OptRel (GRel (SC : Setting S (Slot X) (BId X))) q.toGVal?
        (mapCode codeFwd q).toGVal? := by
  intro q
  induction q with
  | sym s =>
      intro _
      simp only [Tm.toGVal?, mapCode]
      exact GRel.sym s
  | fn _ | var _ | pvar _ | lam _ _ _ | letP _ _ _ | alt _ _ | pquote _ =>
      intro _
      simp only [Tm.toGVal?, mapCode]
      trivial
  | quote _ =>
      intro hf
      obtain ⟨s, rfl⟩ := hf
      simp only [Tm.toGVal?, mapCode, mapCode_codeOf]
      exact GRel.quote ⟨s, rfl, rfl⟩
  | ctx _ _ =>
      intro h
      cases h
  | app _ _ ihf iha =>
      intro hf
      obtain ⟨hff, hfa⟩ := hf
      have hf' := ihf hff
      have ha' := iha hfa
      simp only [Tm.toGVal?, mapCode]
      rcases OptRel.cases hf' with ⟨e1, e2⟩ | ⟨_, _, e1, e2, hfg⟩
      · simp [e1, e2]
        exact trivial
      · rcases OptRel.cases ha' with ⟨e3, e4⟩ | ⟨_, _, e3, e4, hag⟩
        · simp [e1, e2, e3, e4]
          exact trivial
        · simp [e1, e2, e3, e4]
          exact GRel.app hfg hag

theorem var_binder_none [DecidableEq S] {n : Nm (Slot X)} {m : Nm (BId X)}
    (hn : CodeId.hole n = false) (hm : CodeId.hole m = false) {q : Tm S (Slot X)}
    (hf : frag q) (bound₁ : List (Nm (Slot X))) (bound₂ : List (Nm (BId X)))
    (σ₁ : GStore S (Slot X)) (σ₂ : GStore S (BId X)) :
    matchCodeIn σ₁ bound₁ (.var n) q = none ∧
      matchCodeIn σ₂ bound₂ (.var m) (mapCode codeFwd q) = none := by
  have hn' : holeRecS n = false := by rw [← hole_eq_holeRecS]; exact hn
  have hm' : holeRecI m = false := by rw [← hole_eq_holeRecI]; exact hm
  cases q with
  | var k =>
      obtain ⟨y, rfl⟩ := hf
      refine ⟨?_, ?_⟩
      · have hs := same_bound_query hn' y
        simp only [matchCodeIn, hn, hs]
        rfl
      · have hs := same_bound_head hm' ⟨y, [], [], .head⟩
        simp only [matchCodeIn, mapCode, codeFwd, hm, hs, ite_bool_false]
  | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
      simp only [matchCodeIn, mapCode, hn, hm]
      exact ⟨rfl, rfl⟩

theorem opt_seq {D : Set (Nm (Slot X))} {ν : Nm (Slot X) → Nm (BId X)}
    {a₁ : Option (GStore S (Slot X))} {a₂ : Option (GStore S (BId X))}
    {f₁ : GStore S (Slot X) → Option (GStore S (Slot X))}
    {f₂ : GStore S (BId X) → Option (GStore S (BId X))}
    (h1 : OptRel (StoreRel SC ν D) a₁ a₂)
    (h2 : ∀ σ₁ σ₂, StoreRel SC ν D σ₁ σ₂ → OptRel (StoreRel SC ν D) (f₁ σ₁) (f₂ σ₂)) :
    OptRel (StoreRel SC ν D) (a₁.bind f₁) (a₂.bind f₂) := by
  rcases OptRel.cases h1 with ⟨e1, e2⟩ | ⟨τ₁, τ₂, e1, e2, hτ⟩
  · simp [e1, e2]
    exact trivial
  · simp [e1, e2]
    exact h2 τ₁ τ₂ hτ

/-- `matchCode` on an application is `Option.bind`, up to the equation. -/
theorem matchCode_app_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCode σ (.app p₁ p₂) (.app t₁ t₂) =
      (matchCode σ p₁ t₁).bind fun σ' => matchCode σ' p₂ t₂ := by
  simp only [matchCode, matchCodeIn]
  cases matchCodeIn σ [] p₁ t₁ <;> rfl

theorem matchCode_alt_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCode σ (.alt p₁ p₂) (.alt t₁ t₂) =
      (matchCode σ p₁ t₁).bind fun σ' => matchCode σ' p₂ t₂ := by
  simp only [matchCode, matchCodeIn]
  cases matchCodeIn σ [] p₁ t₁ <;> rfl

theorem matchCode_letP_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (σ : GStore S Y) (p w b p' w' b' : Tm S Y) :
    matchCode σ (.letP p w b) (.letP p' w' b') =
      ((matchCode σ p p').bind fun σ₁ =>
        (matchCode σ₁ w w').bind fun σ₂ => matchCode σ₂ b b') := by
  simp only [matchCode, matchCodeIn]
  cases h1 : matchCodeIn σ [] p p' with
  | none => simp only [Option.bind]
  | some σ₁ =>
      simp only [Option.bind]
      cases h2 : matchCodeIn σ₁ [] w w' with
      | none => rfl
      | some σ₂ => rfl

theorem nil_ne_free : ([] : Owner) ≠ codeFreeParam := by
  intro h
  simp [codeFreeParam] at h

theorem same_root_head (y₁ y₂ : X) :
    CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src ([], y₂)) =
      CodeId.same (.src (.slot ⟨y₁, [], [], .head⟩) : Nm (BId X))
        (.src (.slot ⟨y₂, [], [], .head⟩)) := by
  by_cases hy : y₁ = y₂
  · subst hy
    rw [same_src_eq]
    simp only [codeBound_nil, Bool.false_and, ite_bool_false, CodeId.same]
    simp only [decide_eq_false nil_ne_free, Bool.false_and, ite_bool_false]
  · have hL : CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src ([], y₂)) = false := by
      rw [same_src_eq]
      simp only [codeBound_nil, Bool.false_and, ite_bool_false]
      simp only [decide_eq_false nil_ne_free, Bool.false_and, ite_bool_false]
      exact decide_eq_false fun h => by
        simp only [Nm.src.injEq, Prod.mk.injEq] at h
        exact hy h.2
    have hR : CodeId.same (.src (.slot ⟨y₁, [], [], .head⟩) : Nm (BId X))
        (.src (.slot ⟨y₂, [], [], .head⟩)) = false :=
      decide_eq_false fun h => by
        simp only [Nm.src.injEq, BId.slot.injEq, SlotId.mk.injEq] at h
        exact hy h.1
    rw [hL, hR]

theorem same_root_ne_cons (y₁ y₂ : X) (n : ℕ) (o : List ℕ) :
    CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src (n :: o, y₂)) =
      CodeId.same (.src (.slot ⟨y₁, [], [], .head⟩) : Nm (BId X))
        (.src (.code y₂ (n :: o))) := by
  have hL : CodeId.same (.src ([], y₁) : Nm (Slot X)) (.src (n :: o, y₂)) = false := by
    rw [same_src_eq]
    simp only [codeBound_nil, Bool.false_and, ite_bool_false]
    simp only [decide_eq_false nil_ne_free, Bool.false_and, ite_bool_false]
    exact decide_src_owner_ne (List.cons_ne_nil n o).symm
  rw [hL, same_slot_code]

theorem same_cons_ne_root (y₁ y₂ : X) (n : ℕ) (o : List ℕ) :
    CodeId.same (.src (n :: o, y₁) : Nm (Slot X)) (.src ([], y₂)) =
      CodeId.same (.src (.code y₁ (n :: o)) : Nm (BId X))
        (.src (.slot ⟨y₂, [], [], .head⟩)) := by
  have hL : CodeId.same (.src (n :: o, y₁) : Nm (Slot X)) (.src ([], y₂)) = false := by
    rw [same_src_eq]
    simp only [codeBound_nil, Bool.and_false, ite_bool_false]
    simp only [decide_eq_false nil_ne_free, Bool.and_false, ite_bool_false]
    exact decide_src_owner_ne (List.cons_ne_nil n o)
  have hR : CodeId.same (.src (.code y₁ (n :: o)) : Nm (BId X))
      (.src (.slot ⟨y₂, [], [], .head⟩)) = false :=
    decide_eq_false fun h => by cases h
  rw [hL, hR]

/-- `CodeId.same` is unchanged by reading a slot name as a code name. -/
theorem same_codeFwd (a b : Nm (Slot X)) :
    CodeId.same (codeFwd a) (codeFwd b) = CodeId.same a b := by
  cases a with
  | src pa =>
      cases b with
      | src pb =>
          obtain ⟨o₁, y₁⟩ := pa
          obtain ⟨o₂, y₂⟩ := pb
          cases o₁ with
          | nil =>
              cases o₂ with
              | nil =>
                  simp only [codeFwd]
                  exact (same_root_head y₁ y₂).symm
              | cons n o =>
                  simp only [codeFwd]
                  exact (same_root_ne_cons y₁ y₂ n o).symm
          | cons n o =>
              cases o₂ with
              | nil =>
                  simp only [codeFwd]
                  exact (same_cons_ne_root y₁ y₂ n o).symm
              | cons m t =>
                  simp only [codeFwd, same_src_eq, same_code_eq]
                  by_cases hb : codeBound (n :: o) && codeBound (m :: t)
                  · simp only [hb, ite_true]
                  · simp only [hb]
                    by_cases hf : (n :: o) = codeFreeParam && (m :: t) = codeFreeParam
                    · simp only [hf, ite_true]
                    · simp only [hf]
                      by_cases he : (n :: o) = (m :: t) ∧ y₁ = y₂
                      · rcases he with ⟨ho, rfl⟩
                        simp only [ho, ite_bool_false]
                      · have hs :
                            ¬ ((.src (n :: o, y₁) : Nm (Slot X)) = .src (m :: t, y₂)) := by
                          intro h; cases h; exact he ⟨rfl, rfl⟩
                        have hc : ¬ ((.src (.code y₁ (n :: o)) : Nm (BId X)) =
                            .src (.code y₂ (m :: t))) := by
                          intro h; cases h; exact he ⟨rfl, rfl⟩
                        rw [decide_eq_false hs, decide_eq_false hc]
      | inst _ _ =>
          obtain ⟨o, _⟩ := pa
          cases o with
          | nil =>
              simp only [codeFwd, CodeId.same]
              rfl
          | cons _ _ =>
              simp only [codeFwd, CodeId.same]
              rfl
  | inst ρ n =>
      cases b with
      | src pb =>
          obtain ⟨o, _⟩ := pb
          cases o with
          | nil =>
              simp only [codeFwd, CodeId.same]
              rfl
          | cons _ _ =>
              simp only [codeFwd, CodeId.same]
              rfl
      | inst ρ' m =>
          simp only [codeFwd, CodeId.same]
          by_cases he : ρ = ρ' ∧ n = m
          · rcases he with ⟨rfl, rfl⟩
            simp
          · have h1 : ¬ (Nm.inst ρ n = Nm.inst ρ' m) := by
              intro h; cases h; exact he ⟨rfl, rfl⟩
            have h2 : ¬ (Nm.inst ρ (codeFwd n) = Nm.inst ρ' (codeFwd m)) := by
              intro h
              simp only [Nm.inst.injEq] at h
              exact he ⟨h.1, codeFwd_injective h.2⟩
            rw [decide_eq_false h1, decide_eq_false h2]

/-- Mentioning a binder survives the code-name reading. -/
theorem mentionsBinder_map (k : Nm (Slot X)) (q : Tm S (Slot X)) :
    mentionsBinder (codeFwd k) (mapCode codeFwd q) = mentionsBinder k q := by
  induction q with
  | pvar y =>
      simp only [mentionsBinder, mapCode]
      exact same_codeFwd k y
  | lam x _ b ih =>
      simp only [mentionsBinder, mapCode, same_codeFwd, ih]
  | app _ _ ihf iha =>
      simp only [mentionsBinder, mapCode, ihf, iha]
  | letP _ _ _ ihp ihw ihb =>
      simp only [mentionsBinder, mapCode, ihp, ihw, ihb]
  | alt _ _ iha ihb =>
      simp only [mentionsBinder, mapCode, iha, ihb]
  | pquote _ ih =>
      simp only [mentionsBinder, mapCode, ih]
  | sym _ | fn _ | var _ | quote _ | ctx _ _ =>
      simp only [mentionsBinder, mapCode]

/-- The binders a fragment mentions, read as code names. -/
theorem mentioned_codeFwd (bound : List (Nm (Slot X))) (q : Tm S (Slot X)) :
    mentioned (bound.map codeFwd) (mapCode codeFwd q) =
      (mentioned bound q).map codeFwd := by
  induction bound with
  | nil => simp [mentioned]
  | cons k ks ih =>
      have hk : mentionsBinder (codeFwd k) (mapCode codeFwd q) = mentionsBinder k q :=
        mentionsBinder_map k q
      cases h : mentionsBinder k q with
      | true =>
          simp only [mentioned, List.map_cons, List.filter, h, hk]
          simp only [mentioned] at ih
          rw [ih]
      | false =>
          simp only [mentioned, List.map_cons, List.filter, h, hk]
          simp only [mentioned] at ih
          exact ih

/-- A fragment's lambdas own nothing. -/
theorem frag_ownNil {q : Tm S (Slot X)} (h : frag q) : ownNil q := by
  induction q with
  | lam _ _ _ ih =>
      rcases h with ⟨rfl, _, hb⟩
      exact ⟨rfl, ih hb⟩
  | app _ _ ihf iha =>
      exact ⟨ihf h.1, iha h.2⟩
  | quote _ =>
      obtain ⟨s, rfl⟩ := h
      rw [codeOf]
      exact ownNil_seal (ownNil_codeAt none [] [] [] s)
  | pquote _ ih => exact ih h
  | letP _ _ _ ihp ihw ihb =>
      exact ⟨ihp h.1, ihw h.2.1, ihb h.2.2⟩
  | alt _ _ iha ihb =>
      exact ⟨iha h.1, ihb h.2⟩
  | ctx _ _ => cases h
  | sym _ | fn _ | var _ | pvar _ => exact trivial

theorem matchCodeIn_app_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCodeIn σ bound (.app p₁ p₂) (.app t₁ t₂) =
      (matchCodeIn σ bound p₁ t₁).bind fun σ' => matchCodeIn σ' bound p₂ t₂ := by
  simp only [matchCodeIn]
  cases matchCodeIn σ bound p₁ t₁ <;> rfl

theorem matchCodeIn_alt_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p₁ p₂ t₁ t₂ : Tm S Y) :
    matchCodeIn σ bound (.alt p₁ p₂) (.alt t₁ t₂) =
      (matchCodeIn σ bound p₁ t₁).bind fun σ' => matchCodeIn σ' bound p₂ t₂ := by
  simp only [matchCodeIn]
  cases matchCodeIn σ bound p₁ t₁ <;> rfl

theorem matchCodeIn_letP_bind {Y : Type v} [DecidableEq S] [DecidableEq Y] [CodeId Y]
    (bound : List (Nm Y)) (σ : GStore S Y) (p w b p' w' b' : Tm S Y) :
    matchCodeIn σ bound (.letP p w b) (.letP p' w' b') =
      ((matchCodeIn σ bound p p').bind fun σ₁ =>
        (matchCodeIn σ₁ bound w w').bind fun σ₂ => matchCodeIn σ₂ bound b b') := by
  simp only [matchCodeIn]
  cases h1 : matchCodeIn σ bound p p' with
  | none => simp only [Option.bind]
  | some σ₁ =>
      simp only [Option.bind]
      cases h2 : matchCodeIn σ₁ bound w w' with
      | none => rfl
      | some σ₂ => rfl

/-- A hole under code binders binds related values: a ground value when the
fragment mentions none of them, and contextual code along `codeFwd` otherwise. -/
theorem hole_refine [DecidableEq S] {ν : Nm (Slot X) → Nm (BId X)}
    {D : Set (Nm (Slot X))} {σ₁ : GStore S (Slot X)} {σ₂ : GStore S (BId X)}
    (hσ : StoreRel SC ν D σ₁ σ₂) (hinj : Set.InjOn ν D) {n : Nm (Slot X)}
    (hn : n ∈ D) (hb : CodeId.hole n = true) (hb2 : CodeId.hole (ν n) = true)
    {q : Tm S (Slot X)} (hq : frag q) (bound : List (Nm (Slot X))) :
    OptRel (StoreRel SC ν D) (matchCodeIn σ₁ bound (.var n) q)
      (matchCodeIn σ₂ (bound.map codeFwd) (.var (ν n)) (mapCode codeFwd q)) := by
  have hment := mentioned_codeFwd bound q
  have ho := frag_ownNil hq
  cases hks : mentioned bound q with
  | nil =>
      have hg := grel_toGVal? q hq
      have hment0 : mentioned (bound.map codeFwd) (mapCode codeFwd q) = [] := by
        rw [hment, hks]
        rfl
      simp only [matchCodeIn, hb, hb2, contextualVal, hks, hment0]
      rcases OptRel.cases hg with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hgg⟩
      · simp [e1, e2]
        exact trivial
      · rw [e1, e2]
        exact hσ.refine SC_biUnique hinj hn hgg
  | cons k ks =>
      simp only [matchCodeIn, hb, hb2, contextualVal, hks, hment, List.map_cons]
      exact hσ.refine SC_biUnique hinj hn (.ctx ho rfl rfl)

/-- Entering a lambda of sealed code agrees on the two sides, or neither side
enters. A free parameter that does enter is the subject's binder. -/
theorem gate_split {x₁ : Nm (Slot X)} {own₁ : List (Slot X)} {x₂ : Nm (BId X)}
    {own₂ : List (BId X)} {o : Owner} {y : X} (hb : scBare x₁ own₁ x₂ own₂)
    (hbo : codeBound o = true ∨ o = codeFreeParam) :
    ((CodeId.same x₁ (.src (o, y)) && decide (own₁ = [])) = false ∧
        (CodeId.same x₂ (codeFwd (.src (o, y))) && decide (own₂ = [])) = false) ∨
    ((CodeId.same x₁ (.src (o, y)) && decide (own₁ = [])) = true ∧
        (CodeId.same x₂ (codeFwd (.src (o, y))) && decide (own₂ = [])) = true ∧
        own₁ = [] ∧ own₂ = [] ∧ scEnter x₁ x₂ ∧
        (codeFreeS x₁ = true → x₁ = .src (o, y) ∧ x₂ = codeFwd (.src (o, y))) ∧
        (codeFreeS x₁ = true ∨ codeFreeS (.src (o, y)) = false) ∧
        (codeFreeS x₁ = false → ∀ m : Nm (Slot X), codeFreeS m = true →
          x₂ ≠ codeFwd m)) := by
  have hone : o ≠ [] := owner_code_ne_nil hbo
  have hact : actSrcS x₁ = actSrcI x₂ := by
    rcases hb with ⟨_, _, _, _, hact⟩ | ⟨_, _, _, _, _, hact⟩
    · exact hact
    · exact hact
  cases hsrc : actSrcS x₁ with
  | false =>
      have hsrcI : actSrcI x₂ = false := by rw [← hact, hsrc]
      have hL : CodeId.same x₁ (.src (o, y)) = false := by
        cases x₁ with
        | src _ => simp [actSrcS] at hsrc
        | inst _ _ => exact same_instL_src
      have hR : CodeId.same x₂ (codeFwd (.src (o, y))) = false := by
        cases x₂ with
        | src _ => simp [actSrcI] at hsrcI
        | inst _ _ =>
            rw [codeFwd_ne_nil hone]
            exact same_instI_src
      refine Or.inl ⟨?_, ?_⟩
      · rw [hL, Bool.false_and]
      · rw [hR, Bool.false_and]
  | true =>
      have hsrcI : actSrcI x₂ = true := by rw [← hact, hsrc]
      rcases hb with ⟨hS, hI, hm, hown, _⟩ | ⟨hS, hI, e₁, e₂, ho, _⟩
      · rcases hm with ⟨hf₁, hf₂, hs⟩ | ⟨hcS, hcI⟩
        · obtain ⟨y₁, hy₁⟩ : ∃ y₁, x₁ = .src (codeFreeParam, y₁) := by
            cases x₁ with
            | inst _ _ => simp [actSrcS] at hsrc
            | src p =>
                obtain ⟨o₁, y₁⟩ := p
                have ho1 : o₁ = codeFreeParam := of_decide_eq_true (by simpa [codeFreeS] using hf₁)
                exact ⟨y₁, by simp [ho1]⟩
          subst hy₁
          obtain ⟨y₂, hy₂⟩ : ∃ y₂, x₂ = .src (.code y₂ codeFreeParam) := by
            cases x₂ with
            | inst _ _ => simp [actSrcI] at hsrcI
            | src b =>
                cases b with
                | slot _ => simp [codeFreeI] at hf₂
                | par _ _ => simp [codeFreeI] at hf₂
                | code y₂ o₂ =>
                    have ho2 : o₂ = codeFreeParam :=
                      of_decide_eq_true (by simpa [codeFreeI] using hf₂)
                    exact ⟨y₂, by simp [ho2]⟩
          subst hy₂
          have hy : y₁ = y₂ := by simpa [spellS, spellI] using hs
          subst hy
          obtain ⟨eown₁, eown₂⟩ := hown ⟨hf₁, hf₂⟩
          rcases hbo with hbb | rfl
          · have hne : o ≠ codeFreeParam := codeBound_ne_free hbb
            have hLs : CodeId.same (.src (codeFreeParam, y₁)) (.src (o, y)) = false := by
              rw [same_src_eq]
              unfold codeFreeParam at hne ⊢
              simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                Bool.and_false, ite_bool_false, decide_src_owner_ne hne.symm]
            have hRs : CodeId.same (.src (.code y₁ codeFreeParam)) (codeFwd (.src (o, y))) = false := by
              rw [codeFwd_ne_nil hone]
              simp only [same_code_eq]
              unfold codeFreeParam at hne ⊢
              simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                Bool.and_false, ite_bool_false, decide_code_owner_ne hne.symm]
            refine Or.inl ⟨?_, ?_⟩
            · rw [hLs, Bool.false_and]
            · rw [hRs, Bool.false_and]
          · by_cases hey : y₁ = y
            · refine Or.inr ⟨?_, ?_, eown₁, eown₂, Or.inr ⟨hf₁, hf₂, hs⟩, ?_, Or.inl hf₁, ?_⟩
              · rw [hey, eown₁, same_src_eq]
                simp only [codeBound, codeFreeParam, Bool.false_and, ite_bool_false]
                decide
              · rw [hey, eown₂]
                simp only [codeFwd, same_code_eq, codeBound, codeFreeParam, Bool.false_and,
                  ite_bool_false]
                decide
              · intro _
                exact ⟨by simp [hey], by
                  rw [hey]
                  simp only [codeFreeParam]
                  exact codeFwd_cons 9 [] y⟩
              · intro hf
                rw [codeFreeS_param] at hf
                exact absurd hf Bool.false_ne_true.symm
            · have hLs : CodeId.same (.src (codeFreeParam, y₁)) (.src (codeFreeParam, y)) = false := by
                rw [same_src_eq]
                simp only [codeFreeParam, codeBound, Bool.false_and, ite_bool_false]
                exact decide_eq_false hey
              have hRs :
                  CodeId.same (.src (.code y₁ codeFreeParam))
                    (codeFwd (.src (codeFreeParam, y))) = false := by
                simp only [codeFwd, same_code_eq, codeFreeParam, codeBound, Bool.false_and,
                  ite_bool_false]
                exact decide_eq_false hey
              refine Or.inl ⟨?_, ?_⟩
              · rw [hLs, Bool.false_and]
              · rw [hRs, Bool.false_and]
        · have hLs : CodeId.same x₁ (.src (o, y)) = false := by
            cases x₁ with
            | inst _ _ => simp [actSrcS] at hsrc
            | src p =>
                obtain ⟨o₁, y₁⟩ := p
                have hb1 : codeBound o₁ = false := by
                  simp only [holeRecS] at hS
                  cases hc : codeBound o₁ with
                  | false => rfl
                  | true =>
                      simp only [hc, Bool.not_true] at hS
                      exact absurd hS Bool.false_ne_true
                have hf1 : o₁ ≠ codeFreeParam := by
                  intro e
                  rw [e, codeFreeS_param] at hcS
                  exact Bool.false_ne_true hcS.symm
                rw [same_src_eq, hb1, Bool.false_and, ite_bool_false]
                rw [ite_bool_and_left hf1]
                exact decide_src_owner_ne fun he => by
                  rcases hbo with hbo | rfl
                  · rw [he] at hb1
                    exact Bool.false_ne_true (hb1.symm.trans hbo)
                  · exact hf1 he
          have hRs : CodeId.same x₂ (codeFwd (.src (o, y))) = false := by
            rw [codeFwd_ne_nil hone]
            cases x₂ with
            | inst _ _ => simp [actSrcI] at hsrcI
            | src b =>
                cases b with
                | slot k =>
                    exact same_slot_code
                | par z pos =>
                    exact same_par_code
                | code y₂ o₂ =>
                    have hb2 : codeBound o₂ = false := by
                      simp only [holeRecI] at hI
                      cases hc : codeBound o₂ with
                      | false => rfl
                      | true =>
                          simp only [hc, Bool.not_true] at hI
                          exact absurd hI Bool.false_ne_true
                    have hf2 : o₂ ≠ codeFreeParam := by
                      intro e
                      rw [e, codeFreeI_param] at hcI
                      exact Bool.false_ne_true hcI.symm
                    rw [same_code_eq, hb2, Bool.false_and, ite_bool_false]
                    rw [ite_bool_and_left hf2]
                    exact decide_code_owner_ne fun he => by
                      rcases hbo with hbo | rfl
                      · rw [he] at hb2
                        exact Bool.false_ne_true (hb2.symm.trans hbo)
                      · exact hf2 he
          refine Or.inl ⟨?_, ?_⟩
          · rw [hLs, Bool.false_and]
          · rw [hRs, Bool.false_and]
      · obtain ⟨o₁, y₁, hx₁, hb1⟩ :
            ∃ o₁ y₁, x₁ = .src (o₁, y₁) ∧ codeBound o₁ = true := by
          cases x₁ with
          | inst _ _ => simp [actSrcS] at hsrc
          | src p =>
              obtain ⟨o₁, y₁⟩ := p
              refine ⟨o₁, y₁, rfl, ?_⟩
              simp only [holeRecS] at hS
              cases hc : codeBound o₁ with
              | true => rfl
              | false =>
                  simp only [hc, Bool.not_false] at hS
                  exact absurd hS Bool.false_ne_true.symm
        subst hx₁
        obtain ⟨y₂, o₂, hx₂, hb2⟩ :
            ∃ y₂ o₂, x₂ = .src (.code y₂ o₂) ∧ codeBound o₂ = true := by
          cases x₂ with
          | inst _ _ => simp [actSrcI] at hsrcI
          | src b =>
              cases b with
              | slot _ => simp [holeRecI] at hI
              | par _ _ => simp [holeRecI] at hI
              | code y₂ o₂ =>
                  refine ⟨y₂, o₂, rfl, ?_⟩
                  simp only [holeRecI] at hI
                  cases hc : codeBound o₂ with
                  | true => rfl
                  | false =>
                      simp only [hc, Bool.not_false] at hI
                      exact absurd hI Bool.false_ne_true.symm
        subst hx₂
        have ho12 : o₁ = o₂ := by simpa [ownerS, ownerI] using ho
        subst ho12
        rcases hbo with hbb | rfl
        · by_cases heo : o₁ = o
          · refine Or.inr ⟨?_, ?_, e₁, e₂, Or.inl ⟨hS, hI⟩, ?_, Or.inr (codeFreeS_bound hbb), ?_⟩
            · rw [heo, e₁, same_src_eq, hbb]
              simp only [eq_self, Bool.and_self, decide_eq_true trivial, if_pos trivial]
            · rw [heo, e₂, codeFwd_ne_nil hone]
              simp only [same_code_eq, hbb, eq_self, Bool.and_self,
                decide_eq_true trivial, if_pos trivial]
            · intro hf
              rw [codeFreeS_bound hb1] at hf
              exact absurd hf Bool.false_ne_true
            · intro _ m hm heq
              cases m with
              | inst _ _ =>
                  simp only [codeFwd] at heq
                  cases heq
              | src p =>
                  obtain ⟨om, ym⟩ := p
                  have hom : om = codeFreeParam :=
                    of_decide_eq_true (by simpa [codeFreeS] using hm)
                  subst hom
                  rw [show codeFwd (.src (codeFreeParam, ym)) =
                      .src (.code ym codeFreeParam) by simp only [codeFreeParam]; rfl] at heq
                  cases heq
                  simp only [codeFreeParam, codeBound] at hb1
                  exact Bool.false_ne_true hb1
          · have hLs : CodeId.same (.src (o₁, y₁)) (.src (o, y)) = false := by
              rw [same_src_eq, hb1, hbb]
              simp only [Bool.and_self]
              exact decide_eq_false heo
            have hRs : CodeId.same (.src (.code y₂ o₁)) (codeFwd (.src (o, y))) = false := by
              rw [codeFwd_ne_nil hone]
              simp only [same_code_eq, hb1, hbb, Bool.and_self]
              exact decide_eq_false heo
            refine Or.inl ⟨?_, ?_⟩
            · rw [hLs, Bool.false_and]
            · rw [hRs, Bool.false_and]
        · have hne : o₁ ≠ codeFreeParam := codeBound_ne_free hb1
          have hLs : CodeId.same (.src (o₁, y₁)) (.src (codeFreeParam, y)) = false := by
            rw [same_src_eq, hb1]
            unfold codeFreeParam at hne ⊢
            simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
              Bool.false_and, ite_bool_false, decide_src_owner_ne hne]
          have hRs :
              CodeId.same (.src (.code y₂ o₁)) (codeFwd (.src (codeFreeParam, y))) = false := by
            rw [show codeFwd (.src (codeFreeParam, y)) = .src (.code y codeFreeParam) by
              simp only [codeFreeParam]; rfl]
            simp only [same_code_eq, hb1]
            unfold codeFreeParam at hne ⊢
            simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
              Bool.false_and, ite_bool_false, decide_code_owner_ne hne]
          refine Or.inl ⟨?_, ?_⟩
          · rw [hLs, Bool.false_and]
          · rw [hRs, Bool.false_and]

theorem align_lam {μ μb : Nm (Slot X) → Nm (BId X)} {x₁ sb : Nm (Slot X)}
    {x₂ : Nm (BId X)} {b qb : Tm S (Slot X)}
    (hμb : ∀ x, x ≠ x₁ → μb x = μ x) (hμx : μb x₁ = x₂)
    (hpar : ∀ x ∈ freeParams b, x ≠ x₁ → μ x ≠ x₂)
    (hxe : codeFreeS x₁ = true → x₁ = sb ∧ x₂ = codeFwd x₁)
    (hcov : codeFreeS x₁ = true ∨ codeFreeS sb = false)
    (hsep : codeFreeS x₁ = false → ∀ m, codeFreeS m = true → x₂ ≠ codeFwd m)
    (ha : Align μ (.lam x₁ [] b) (.lam sb [] qb)) : Align μb b qb := by
  obtain ⟨hpins, hexact⟩ := ha
  refine ⟨?_, ?_⟩
  · intro m hm
    have hmf := codeFreePvars_free hm
    cases hf : codeFreeS x₁ with
    | true =>
        obtain ⟨rfl, hx2⟩ := hxe hf
        by_cases hm1 : m = x₁
        · rw [hm1, hμx, hx2]
        · rw [hμb m hm1]
          apply hpins
          simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
          exact ⟨hm, hm1⟩
    | false =>
        have hm1 := ne_of_codeFree hf hmf
        have hsb : codeFreeS sb = false := by
          rcases hcov with h | h
          · rw [hf] at h
            exact absurd h Bool.false_ne_true
          · exact h
        have hmsb := ne_of_codeFree hsb hmf
        rw [hμb m hm1.symm]
        apply hpins
        simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
        exact ⟨hm, hmsb.symm⟩
  · intro x hx m hm hμeq
    have hmf := codeFreePvars_free hm
    cases hf : codeFreeS x₁ with
    | true =>
        obtain ⟨rfl, hx2⟩ := hxe hf
        by_cases hx1 : x = x₁
        · rw [hx1, hμx, hx2] at hμeq
          exact hx1.trans (codeFwd_injective hμeq)
        · rw [hμb x hx1] at hμeq
          by_cases hm1 : m = x₁
          · rw [hm1, ← hx2] at hμeq
            exact absurd hμeq (hpar x hx hx1)
          · apply hexact x ?_ m ?_ hμeq
            · simp only [freeParams, List.mem_filter, decide_eq_true_eq]
              exact ⟨hx, hx1⟩
            · simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
              exact ⟨hm, hm1⟩
    | false =>
        have hm1 := ne_of_codeFree hf hmf
        have hsb : codeFreeS sb = false := by
          rcases hcov with h | h
          · rw [hf] at h
            exact absurd h Bool.false_ne_true
          · exact h
        have hmsb := ne_of_codeFree hsb hmf
        by_cases hx1 : x = x₁
        · rw [hx1, hμx] at hμeq
          exact absurd hμeq (hsep hf m hmf)
        · rw [hμb x hx1] at hμeq
          apply hexact x ?_ m ?_ hμeq
          · simp only [freeParams, List.mem_filter, decide_eq_true_eq]
            exact ⟨hx, hx1⟩
          · simp only [codeFreePvars, List.mem_filter, decide_eq_true_eq]
            exact ⟨hm, hmsb.symm⟩

/-- Related code matches a fragment of sealed code on both sides together.
Free parameters of the subject are pinned by `Align`: a sealed `codeOf` has
none until a lambda is entered. -/
theorem match_frag [DecidableEq S] {ν μ : Nm (Slot X) → Nm (BId X)} {k : Kd}
    {Res : List (Nm (BId X))} {ok : Bool} {c₁ : Tm S (Slot X)} {c₂ : Tm S (BId X)}
    (h : Rel SC ν μ k Res ok c₁ c₂) (bound : List (Nm (Slot X)) := []) :
    ok = true →
    ∀ (q : Tm S (Slot X)), frag q → Align μ c₁ q →
    ∀ (D : Set (Nm (Slot X))) (σ₁ : GStore S (Slot X)) (σ₂ : GStore S (BId X)),
      (∀ n ∈ freeNames c₁, n ∈ D) → Set.InjOn ν D → StoreRel SC ν D σ₁ σ₂ →
      OptRel (StoreRel SC ν D) (matchCodeIn σ₁ bound c₁ q)
        (matchCodeIn σ₂ (bound.map codeFwd) c₂ (mapCode codeFwd q)) := by
  induction h generalizing bound with
  | sym s =>
      intro _ q _ _ _ σ₁ σ₂ _ _ hσ
      cases q with
      | sym s' =>
          simp only [matchCodeIn, mapCode]
          by_cases hs : s = s'
          · simp only [if_pos hs]
            exact hσ
          · simp only [if_neg hs]
            trivial
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | fn F =>
      intro _ q _ _ _ σ₁ σ₂ _ _ hσ
      cases q with
      | fn F' =>
          simp only [matchCodeIn, mapCode]
          by_cases hs : F = F'
          · simp only [if_pos hs]
            exact hσ
          · simp only [if_neg hs]
            trivial
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @var ν _ _ n hv =>
      intro _ q hq _ D σ₁ σ₂ hD hinj hσ
      simp only [SC, scVarHole] at hv
      have hbit : CodeId.hole n = CodeId.hole (ν n) := by
        rw [hole_eq_holeRecS, hv, ← hole_eq_holeRecI]
      cases hb : CodeId.hole n with
      | false =>
          have hb2 : CodeId.hole (ν n) = false := by rw [← hbit, hb]
          obtain ⟨e1, e2⟩ :=
            var_binder_none hb hb2 hq bound (bound.map codeFwd) σ₁ σ₂
          rw [e1, e2]
          trivial
      | true =>
          have hb2 : CodeId.hole (ν n) = true := by rw [← hbit, hb]
          exact hole_refine hσ hinj (hD n (by simp [freeNames])) hb hb2 hq bound
  | @pvar _ μ _ x hp =>
      intro _ q hq ha _ σ₁ σ₂ _ _ hσ
      simp only [SC] at hp
      cases q with
      | pvar m =>
          obtain ⟨om, ym, rfl, hbm⟩ := hq
          have homnil : om ≠ [] := owner_code_ne_nil hbm
          rcases hp with ⟨hc1, hc2, ho⟩ | ⟨hn1, hn2⟩
          · obtain ⟨ox, yx, hx, hbx⟩ :
                ∃ ox yx, x = .src (ox, yx) ∧ (codeBound ox = true ∨ ox = codeFreeParam) := by
              cases x with
              | inst _ _ => simp [codeParamS] at hc1
              | src p =>
                  obtain ⟨ox, yx⟩ := p
                  exact ⟨ox, yx, rfl, by simpa [codeParamS] using hc1⟩
            subst hx
            obtain ⟨yμ, oμ, hμx, hbμ⟩ :
                ∃ yμ oμ, μ (.src (ox, yx)) = .src (.code yμ oμ) ∧
                  (codeBound oμ = true ∨ oμ = codeFreeParam) := by
              cases hμ : μ (.src (ox, yx)) with
              | inst _ _ => simp [codeParamI, hμ] at hc2
              | src b =>
                  cases b with
                  | slot _ => simp [codeParamI, hμ] at hc2
                  | par _ _ => simp [codeParamI, hμ] at hc2
                  | code yμ oμ =>
                      exact ⟨yμ, oμ, rfl, by simpa [codeParamI, hμ] using hc2⟩
            rw [hμx] at ho ⊢
            have hox : ox = oμ := by simpa [ownerS, ownerI] using ho
            subst hox
            simp only [matchCodeIn, mapCode]
            rw [codeFwd_ne_nil homnil]
            rcases hbx with hbx | rfl
            · rcases hbm with hbm | rfl
              · rw [same_src_eq, same_code_eq, hbx, hbm]
                simp only [Bool.and_self]
                by_cases heo : ox = om
                · simp only [heo]
                  exact hσ
                · simp only [decide_eq_false heo]
                  trivial
              · have hne : ox ≠ codeFreeParam := codeBound_ne_free hbx
                rw [same_src_eq, same_code_eq, hbx]
                unfold codeFreeParam at hne ⊢
                simp only [codeBound, Bool.and_false, ite_bool_false, decide_eq_false hne,
                  Bool.false_and, ite_bool_false, decide_src_owner_ne hne,
                  decide_code_owner_ne hne]
                trivial
            · rcases hbm with hbm | rfl
              · have hne : om ≠ codeFreeParam := codeBound_ne_free hbm
                rw [same_src_eq, same_code_eq, hbm]
                unfold codeFreeParam at hne ⊢
                simp only [codeBound, Bool.false_and, ite_bool_false, decide_eq_false hne,
                  Bool.and_false, ite_bool_false, decide_src_owner_ne hne.symm,
                  decide_code_owner_ne hne.symm]
                trivial
              · rw [same_src_eq, same_code_eq]
                by_cases hey : yx = ym
                · rw [hey] at hμx ⊢
                  have hpin : μ (.src (codeFreeParam, ym)) =
                      codeFwd (.src (codeFreeParam, ym)) := by
                    refine ha.1 _ ?_
                    simp [codeFreePvars, codeFreeS_param]
                  have hym : yμ = ym := by
                    have hfwd : codeFwd (.src (codeFreeParam, ym)) =
                        .src (.code ym codeFreeParam) := by
                      simp only [codeFreeParam]; rfl
                    have h := hμx.symm.trans (hpin.trans hfwd)
                    simp only [Nm.src.injEq, BId.code.injEq] at h
                    exact h.1
                  rw [hym]
                  simp only [codeFreeParam, codeBound, eq_self, decide_eq_true trivial]
                  exact hσ
                · by_cases hyμ : yμ = ym
                  · exfalso
                    rw [hyμ] at hμx
                    have hxeq : (Nm.src (codeFreeParam, yx) : Nm (Slot X)) =
                        Nm.src (codeFreeParam, ym) := by
                      refine ha.2 _ ?_ _ ?_ ?_
                      · simp [freeParams]
                      · simp [codeFreePvars, codeFreeS_param]
                      · simpa [codeFwd, codeFreeParam] using hμx
                    simp only [Nm.src.injEq, Prod.mk.injEq] at hxeq
                    exact hey hxeq.2
                  · simp only [codeFreeParam, codeBound, decide_eq_false hey, decide_eq_false hyμ]
                    trivial
          · have hLs : CodeId.same x (.src (om, ym)) = false := by
              cases x with
              | inst _ _ => exact same_instL_src
              | src p =>
                  obtain ⟨ox, yx⟩ := p
                  have hb1 : codeBound ox = false := by
                    by_cases hc : codeBound ox = true
                    · exact absurd (Or.inl hc) hn1
                    · exact Bool.eq_false_iff.mpr hc
                  have hf1 : ox ≠ codeFreeParam := fun h => hn1 (Or.inr h)
                  rw [same_src_eq, hb1, Bool.false_and, ite_bool_false]
                  rw [ite_bool_and_left hf1]
                  exact decide_src_owner_ne fun he => by
                    rcases hbm with hbm | rfl
                    · rw [he] at hb1
                      exact Bool.false_ne_true (hb1.symm.trans hbm)
                    · exact hf1 he
            have hRs : CodeId.same (μ x) (codeFwd (.src (om, ym))) = false := by
              rw [codeFwd_ne_nil homnil]
              cases hx : μ x with
              | inst _ _ =>
                  exact same_instI_src
              | src b =>
                  cases b with
                  | slot _ =>
                      exact same_slot_code
                  | par _ _ =>
                      exact same_par_code
                  | code yμ oμ =>
                      have hnot : ¬ (codeBound oμ = true ∨ oμ = codeFreeParam) := by
                        intro h
                        exact hn2 (by simp [codeParamI, hx, h])
                      have hb2 : codeBound oμ = false := Bool.eq_false_iff.mpr fun h => hnot (Or.inl h)
                      have hf2 : oμ ≠ codeFreeParam := fun h => hnot (Or.inr h)
                      rw [same_code_eq, hb2, Bool.false_and, ite_bool_false]
                      rw [ite_bool_and_left hf2]
                      exact decide_code_owner_ne fun he => by
                        rcases hbm with hbm | rfl
                        · rw [he] at hb2
                          exact Bool.false_ne_true (hb2.symm.trans hbm)
                        · exact hf2 he
            simp only [matchCodeIn, mapCode, hLs, hRs, ite_bool_false]
            trivial
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | quote hq =>
      intro _ q hqf _ _ σ₁ σ₂ _ _ hσ
      simp only [SC] at hq
      cases q with
      | quote cq =>
          obtain ⟨sq, rfl⟩ := hqf
          obtain ⟨sp, rfl, rfl⟩ := hq
          simp only [matchCodeIn, mapCode, mapCode_codeOf, codeEq_codeOf_codeI]
          cases hce : codeEq (codeI sp) (codeI sq) with
          | false =>
              simp only [ite_bool_false]
              trivial
          | true => exact hσ
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @pquote _ μ _ pc₁ _ _ hbody _ hokb ih =>
      intro _ q hq ha D σ₁ σ₂ hD hinj hσ
      cases q with
      | quote cq =>
          obtain ⟨s, rfl⟩ := hq
          have hAl : Align μ pc₁ (codeOf s) :=
            ⟨fun m hm => by simp [codeFreePvars_codeOf] at hm,
             fun _ _ m hm => by simp [codeFreePvars_codeOf] at hm⟩
          simp only [matchCodeIn, mapCode]
          simpa [mapCode_codeOf] using
            ih bound hokb (codeOf s) (frag_codeOf s) hAl D σ₁ σ₂
              (fun n hn => hD n (by simpa [freeNames] using hn)) hinj hσ
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | app _ _ ihf iha =>
      intro hok q hq ha D σ₁ σ₂ hD hinj hσ
      have ho := Bool.and_eq_true_iff.mp hok
      cases q with
      | app qf qa =>
          obtain ⟨hqf, hqa⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          have hAf : Align _ _ qf :=
            ⟨fun m hm => hpins m (List.mem_append_left _ hm),
             fun x hx m hm hμ => hexact x (List.mem_append_left _ hx) m
               (List.mem_append_left _ hm) hμ⟩
          have hAa : Align _ _ qa :=
            ⟨fun m hm => hpins m (List.mem_append_right _ hm),
             fun x hx m hm hμ => hexact x (List.mem_append_right _ hx) m
               (List.mem_append_right _ hm) hμ⟩
          simp only [mapCode]
          rw [matchCodeIn_app_bind (bound := bound) (σ := σ₁),
            matchCodeIn_app_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ihf bound ho.1 qf hqf hAf D σ₁ σ₂
              (fun n hn => hD n (List.mem_append_left _ hn)) hinj hσ)
            (fun σ₁' σ₂' hσ' => iha bound ho.2 qa hqa hAa D σ₁' σ₂'
              (fun n hn => hD n (List.mem_append_right _ hn)) hinj hσ')
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | letP _ hp hw hb ihp ihw ihb =>
      intro hok q hq ha D σ₁ σ₂ hD hinj hσ
      have h3 := Bool.and_eq_true_iff.mp hok
      have h12 := Bool.and_eq_true_iff.mp h3.1
      cases q with
      | letP qp qw qb =>
          obtain ⟨hqp, hqw, hqb⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          have memL {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ a) : n ∈ a ++ b ++ c :=
            List.mem_append_left _ (List.mem_append_left _ h)
          have memM {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ b) : n ∈ a ++ b ++ c :=
            List.mem_append_left _ (List.mem_append_right _ h)
          have memR {n : Nm (Slot X)} {a b c : List (Nm (Slot X))}
              (h : n ∈ c) : n ∈ a ++ b ++ c :=
            List.mem_append_right _ h
          simp only [mapCode]
          rw [matchCodeIn_letP_bind (bound := bound) (σ := σ₁),
            matchCodeIn_letP_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ihp bound h12.1 qp hqp
              ⟨fun m hm => hpins m (memL hm),
               fun x hx m hm hμ => hexact x (memL hx) m (memL hm) hμ⟩
              D σ₁ σ₂ (fun n hn => hD n (memL hn)) hinj hσ)
            (fun σa σb hσab =>
              opt_seq (ihw bound h12.2 qw hqw
                  ⟨fun m hm => hpins m (memM hm),
                   fun x hx m hm hμ => hexact x (memM hx) m (memM hm) hμ⟩
                  D σa σb (fun n hn => hD n (memM hn)) hinj hσab)
                (fun σc σd hσcd => ihb bound h3.2 qb hqb
                  ⟨fun m hm => hpins m (memR hm),
                   fun x hx m hm hμ => hexact x (memR hx) m (memR hm) hμ⟩
                  D σc σd (fun n hn => hD n (memR hn)) hinj hσcd))
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | alt _ _ _ ih1 ih2 =>
      intro hok q hq ha D σ₁ σ₂ hD hinj hσ
      have ho := Bool.and_eq_true_iff.mp hok
      cases q with
      | alt q1 q2 =>
          obtain ⟨hq1, hq2⟩ := hq
          obtain ⟨hpins, hexact⟩ := ha
          simp only [mapCode]
          rw [matchCodeIn_alt_bind (bound := bound) (σ := σ₁),
            matchCodeIn_alt_bind (bound := bound.map codeFwd) (σ := σ₂)]
          exact opt_seq (ih1 bound ho.1 q1 hq1
              ⟨fun m hm => hpins m (List.mem_append_left _ hm),
               fun x hx m hm hμ => hexact x (List.mem_append_left _ hx) m
                 (List.mem_append_left _ hm) hμ⟩
              D σ₁ σ₂ (fun n hn => hD n (List.mem_append_left _ hn)) hinj hσ)
            (fun σa σb hσab => ih2 bound ho.2 q2 hq2
              ⟨fun m hm => hpins m (List.mem_append_right _ hm),
               fun x hx m hm hμ => hexact x (List.mem_append_right _ hx) m
                 (List.mem_append_right _ hm) hμ⟩
              D σa σb (fun n hn => hD n (List.mem_append_right _ hn)) hinj hσab)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | @lam ν _ _ x₁ own₁ b₁ x₂ own₂ _ νb μb _ _ hνb hμb hμx _ _ hb _ _ _ _ _ hpar hbare hseen ih =>
      intro _ q hq ha D σ₁ σ₂ hD hinj hσ
      simp only [SC] at hbare
      cases q with
      | lam sb _ qb =>
          obtain ⟨rfl, hnamed, hqb⟩ := hq
          obtain ⟨o, y, rfl, hbo⟩ := hnamed
          simp only [matchCodeIn, mapCode]
          rcases gate_split hbare hbo with ⟨hL, hR⟩ | ⟨hL, hR, hown1, _, hent, hxe, hcov, hsep⟩
          · rw [hL, hR]
            simp only [ite_bool_false]
            trivial
          · rw [hL, hR]
            have hob : _ = true := hseen hent
            have hν : νb = ν := by
              funext n
              exact hνb n (by rw [hown1]; exact ownKey_nil n)
            have hxe' : codeFreeS x₁ = true → x₁ = .src (o, y) ∧ x₂ = codeFwd x₁ := by
              intro hf
              obtain ⟨rfl, hx2⟩ := hxe hf
              exact ⟨rfl, hx2⟩
            have hAl := align_lam hμb hμx hpar hxe' hcov hsep (by
              simpa [hown1] using ha)
            have hih := ih (bound ++ [.src (o, y)]) hob qb hqb hAl D σ₁ σ₂
              (by simpa [hown1, freeNames_lam_nil] using hD)
              (by simpa [hν] using hinj) (by simpa [hν] using hσ)
            rw [List.map_append, List.map_singleton] at hih
            simpa [hν, hown1, freeNames_lam_nil] using hih
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchCodeIn, mapCode]
          trivial
  | ctx _ _ _ =>
      intro _ _ _ _ _ _ _ _ _ _
      simp only [matchCodeIn]
      trivial
  | letAct _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro hok
      exact absurd hok Bool.false_ne_true
  | newAct _ _ _ _ _ _ _ =>
      intro hok
      exact absurd hok Bool.false_ne_true

/-- **Related pattern code matches related sealed code.** A hole binds a ground
value on both sides together. A binder of code is entered only when both sides
name that binder, and then the body matches. -/
theorem SC_patAgree [DecidableEq S] : (SC : Setting S (Slot X) (BId X)).PatAgree := by
  intro ν μ _ c₁ c₂ q₁ q₂ D σ₁ σ₂ hR hok _ hQ hD hinj hσ
  obtain ⟨s, rfl, rfl⟩ := by simpa [SC] using hQ
  have hAl : Align μ c₁ (codeOf s) :=
    ⟨fun m hm => by simp [codeFreePvars_codeOf] at hm,
     fun _ _ m hm => by simp [codeFreePvars_codeOf] at hm⟩
  simpa [matchCode, mapCode_codeOf] using
    match_frag (bound := []) hR hok (codeOf s) (frag_codeOf s) hAl D σ₁ σ₂ hD hinj hσ

/-! ## The root of a form -/

/-- An admissible identity is apart from every reserved name, when a free
name of its spelling is live. -/
theorem ResOK.key_not_mem {F : Owner} {A : Ann S X} {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)}
    {Res : List (Nm (BId X))} (hres : ResOK F F A t₁ t₂ Res) {k : SlotId X} (hk : KeyOK F A k)
    {n : Nm (Slot X)} (hn : n ∈ freeNames t₁) (hsp : spellS n = k.spell) :
    (.src (.slot k) : Nm (BId X)) ∉ Res := by
  intro hm
  obtain ⟨k', hk', -, hkh, q, hq, hpat⟩ := hres.shape _ hm
  injection hk' with hk'
  injection hk' with hk'
  subst hk'
  rcases hk with hh | ⟨hn', hs⟩ | ⟨hp, P, hP, hnot⟩
  · exact hkh hh
  · exact hres.news k hm hn' hs n hn hsp
  · rw [hP] at hq
    have hPq : P = q := List.append_cancel_left hq
    subst hPq
    exact hnot (hpat hp)

/-- **The query's configuration**: at the root `[]`, with the root's
identities, the two elaborations of well-formed annotated text start related,
with empty stores. -/
theorem root_config {A : Ann S X} {rk : X → SlotId X} (hwf : A.WF []) (hpars : A.freePars = [])
    (hrk : ∀ y, (rk y).spell = y ∧ (rk y).frame = [] ∧ KeyOK [] A (rk y)) :
    ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (Res : List (Nm (BId X))) (D : Set (Nm (Slot X)))
      (ok : Bool),
      Rel SC ν μ .code Res ok (A.slotOf (fun _ => []) []) (A.idOf rk (fun _ => []) [] []) ∧
      freeParams (A.slotOf (fun _ => []) []) = [] ∧
      (∀ x ∈ freeNames (A.slotOf (fun _ => []) []), x ∈ D) ∧
      CI (SC : Setting S (Slot X) (BId X)) ν D (Res ++ []) Store.empty Store.empty ∧ Fresh [] [] ν D (Res ++ []) := by
  obtain ⟨Res, hrel, hres⟩ := rel_ann A (k := .code) (env := fun _ => []) (posS := []) (envI := rk)
    (pv := fun _ => []) (fr := []) (posI := []) (ν := fun n => .src (.slot (rk (spellS n))))
    (μ := fun n => .src (.par (spellS n) [])) hwf (by decide) (fun h => by cases h)
    (fun _ _ => rfl) (fun y _ => ⟨(hrk y).1, by rw [(hrk y).2.1]; exact List.prefix_refl _⟩)
    (List.prefix_refl _)
    (by intro z hz; rw [hpars] at hz; cases hz) scopeOwners_nil PosSafe.root
  have hfree : ∀ n ∈ freeNames (A.slotOf (fun _ => []) []), ∃ y, n = .src ([], y) := by
    intro n hn
    obtain ⟨y, _, rfl⟩ := Ann.freeNames_slotOf A _ _ n (Ann.Open.of_WF hwf) hn
    exact ⟨y, rfl⟩
  refine ⟨_, _, Res, {n | n ∈ freeNames (A.slotOf (fun _ => []) [])}, annOK A, hrel, ?_,
    fun x hx => hx, ?_, ?_⟩
  · apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    obtain ⟨z, hz, _⟩ := Ann.freeParams_slotOf A _ _ x (Ann.Open.of_WF hwf) hx
    rw [hpars] at hz
    cases hz
  · rw [List.append_nil]
    refine ⟨?_, hres.nodup, ?_, StoreRel.empty _ _, ?_, ?_, ?_⟩
    · intro n hn n' hn' he
      obtain ⟨y, rfl⟩ := hfree n hn
      obtain ⟨y', rfl⟩ := hfree n' hn'
      simp only [spellS] at he
      injection he with he
      injection he with he
      have hyy : y = y' := by rw [← (hrk y).1, ← (hrk y').1, he]
      rw [hyy]
    · intro n hn hm
      obtain ⟨y, rfl⟩ := hfree n hn
      exact hres.key_not_mem (hrk y).2.2 hn (by simp [spellS, (hrk y).1]) hm
    · intro n hn
      obtain ⟨y, rfl⟩ := hfree n hn
      rfl
    · intro n _
      exact ⟨rk (spellS n), rfl, (hrk _).2.1⟩
    · intro m hm
      obtain ⟨k, rfl, hk, -⟩ := hres.shape m hm
      exact ⟨k, rfl, hk⟩
  · rw [List.append_nil]
    refine ⟨fun n hn => ?_, fun _ _ => oldAt_src _ _, fun m hm => ?_⟩
    · obtain ⟨y, rfl⟩ := hfree n hn
      exact oldAt_src _ _
    · obtain ⟨k, rfl, -⟩ := hres.shape m hm
      exact oldAt_src _ _

/-- **A clause**: rooted at `[5]`, its wrapper activation owns the root's
names on both sides; the two clause terms are closed and related under every
name map. -/
theorem clause_rel {A : Ann S X} {rk : X → SlotId X} {own : List X} (u : X) (unit : S)
    (hwf : A.WF [5]) (hpars : A.freePars = []) (hown : ∀ y ∈ A.names, y ∈ own)
    (hrk : ∀ y, (rk y).spell = y ∧ (rk y).frame = [5] ∧ KeyOK [5] A (rk y)) :
    freeNames (.app (.lam (.src ([5] ++ [9], u)) (own.map fun y => ([5], y))
      (A.slotOf (fun _ => [5]) [5])) (.sym unit) : Tm S (Slot X)) = [] ∧
    freeParams (.app (.lam (.src ([5] ++ [9], u)) (own.map fun y => ([5], y))
      (A.slotOf (fun _ => [5]) [5])) (.sym unit) : Tm S (Slot X)) = [] ∧
    ∀ ν μ, Rel SC ν μ .code [] true
      (.app (.lam (.src ([5] ++ [9], u)) (own.map fun y => ([5], y))
        (A.slotOf (fun _ => [5]) [5])) (.sym unit))
      (.app (.lam (.src (.par u ([5] ++ [9]))) (frameSlots [5] (A.idOf rk (fun _ => [5]) [5] [5]))
        (A.idOf rk (fun _ => [5]) [5] [5])) (.sym unit)) := by
  have hfp : freeParams (A.slotOf (fun _ => [5]) [5]) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro x hx
    obtain ⟨z, hz, _⟩ := Ann.freeParams_slotOf A _ _ x (Ann.Open.of_WF hwf) hx
    rw [hpars] at hz
    cases hz
  refine ⟨?_, ?_, ?_⟩
  · simp only [freeNames, List.append_nil]
    apply List.eq_nil_iff_forall_not_mem.2
    intro n hn
    obtain ⟨hn, ho⟩ := List.mem_filter.1 hn
    obtain ⟨y, hy, rfl⟩ := Ann.freeNames_slotOf A _ _ n (Ann.Open.of_WF hwf) hn
    rw [ownKey_map_src] at ho
    simp [hown y hy] at ho
  · simp [freeParams, hfp]
  · intro ν μ
    obtain ⟨Rb, hrel, hres⟩ := rel_ann A (k := .code) (env := fun _ => [5]) (posS := [5])
      (envI := rk) (pv := fun _ => [5]) (fr := [5]) (posI := [5]) (ν := bindν ν [5] own rk)
      (μ := Function.update μ (.src ([5] ++ [9], u)) (.src (.par u ([5] ++ [9])))) hwf (by decide)
      (fun h => by cases h) (fun y hy => bindν_on (hown y hy))
      (fun y _ => ⟨(hrk y).1, by rw [(hrk y).2.1]; exact List.prefix_refl _⟩) (List.prefix_refl _)
      (by intro z hz; rw [hpars] at hz; cases hz) scopeOwners_five PosSafe.clause
    obtain ⟨hownk, hresb, hinj, hdisj⟩ := frame_conds (key := rk) hrel hres (fun _ _ _ => rfl)
      (fun y hy => bindν_on hy) (fun y hy hyo => absurd (hown y hy) hyo) (fun y _ => hrk y)
      (Ann.Open.of_WF hwf)
    refine .app (.lam (fun n hn => bindν_off hn) (fun x hx => Function.update_of_ne hx _ _)
      (Function.update_self _ _ _) ?_ ?_ hrel hownk hresb hinj hdisj hres.nodup ?_
      (by
        refine Or.inl ⟨?_, rfl, Or.inr ⟨?_, rfl⟩, fun hcf => ?_, rfl⟩
        · simp only [holeRecS, codeBound]
          rfl
        · simp only [codeFreeS, codeFreeParam]
          rfl
        · have hc : codeFreeS (.src ([5] ++ [9], u)) = false := by
            simp only [codeFreeS, codeFreeParam]
            rfl
          exact absurd (hc.symm.trans hcf.1) Bool.false_ne_true)
      (by
        intro hent
        simp only [SC, scEnter, holeRecS, holeRecI, codeFreeS, codeFreeI, codeBound,
          codeFreeParam] at hent
        rcases hent with hent | hent
        · exact absurd hent.1 Bool.false_ne_true.symm
        · exact absurd hent.1 Bool.false_ne_true)) (.sym unit)
    · intro s hs h
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hs
      exact (by simp : ([5] : Owner) ≠ []) h
    · intro s hs h
      obtain ⟨k', rfl, hkF⟩ := frame_of_mem_frameSlots hs
      obtain ⟨k'', hk'', hk0⟩ := h
      injection hk'' with hk''
      subst hk''
      rw [hkF] at hk0
      simp at hk0
    · intro x hx
      rw [hfp] at hx
      cases hx

/-! ## Rule M's and lexical fresh's roots -/

theorem mRootEnv_ok (R : Owner) (t : Src S X) (E cr : List X) (env : IEnv X) (y : X) :
    (mRootEnv R t y).spell = y ∧ (mRootEnv R t y).frame = R ∧
      KeyOK R (annM E cr env R R t) (mRootEnv R t y) := by
  unfold mRootEnv
  cases h : findCover (Src.direct t) y false t with
  | none => exact ⟨rfl, rfl, Or.inl rfl⟩
  | some P =>
      exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, P, rfl, findCover_not_letA t _ y _ P h _ _ _ _ _⟩)⟩

omit [DecidableEq X] in
theorem lfRootEnv_ok (R : Owner) (A : Ann S X) (y : X) :
    (lfRootEnv R y).spell = y ∧ (lfRootEnv R y).frame = R ∧ KeyOK R A (lfRootEnv R y) :=
  ⟨rfl, rfl, Or.inl rfl⟩

/-! ## Programs -/

/-- The equations of a program in the slot model, each clause elaborated as its
own form at the root `[5]` (as `SpectrumCorpus.progOf` does). -/
def progSlot (c : Config) (u : X) (unit : S) (cl : S → Option (Src S X)) :
    S → Option (Tm S (Slot X)) :=
  fun F => (cl F).map (clauseOf c [5] u unit)

/-- **Rule M's programs are related.** -/
theorem progRel_M (u : X) (unit : S) (cl : S → Option (Src S X))
    (hcl : ∀ F body, cl F = some body → body.Admissible) :
    ProgRel SC (progSlot cfgM u unit cl) (progM u unit cl) := by
  intro F
  simp only [progSlot, progM]
  cases h : cl F with
  | none => trivial
  | some body =>
      obtain ⟨h₂, h₃⟩ := hcl F body h
      have e₁ : clauseOf cfgM [5] u unit body =
          .app (.lam (.src ([5] ++ [9], u)) ((Src.names body).dedup.map fun y => ([5], y))
            ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).slotOf (fun _ => [5]) [5]))
            (.sym unit) := by
        simp only [clauseOf, rootSpellings, elabCfgX, elabCfg, cfgM, elabForm, List.append_nil]
        rw [elabMS_eq_slotOf body _ [] (mRootEnv [5] body) [5] [5]]
      have e₂ : clauseId [5] u unit (elabMFormAt [5] body) =
          .app (.lam (.src (.par u ([5] ++ [9])))
            (frameSlots [5] ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).idOf
              (mRootEnv [5] body) (fun _ => [5]) [5] [5]))
            ((annM (Src.direct body) [] (mRootEnv [5] body) [5] [5] body).idOf
              (mRootEnv [5] body) (fun _ => [5]) [5] [5])) (.sym unit) := by
        simp only [clauseId, elabMFormAt]
        rw [elabMId_eq_idOf]
        rfl
      simp only [Option.map_some]
      rw [e₁, e₂]
      exact clause_rel u unit (annM_WF body _ _ _ _ _ h₂) (by rw [freePars_annM]; exact h₃)
        (fun y hy => List.mem_dedup.2 (by rwa [names_annM] at hy))
        (fun y => mRootEnv_ok [5] body _ _ _ y)

/-- **Lexical fresh's programs are related.** -/
theorem progRel_LF (u : X) (unit : S) (cl : S → Option (Src S X))
    (hcl : ∀ F body, cl F = some body → body.Admissible) :
    ProgRel SC (progSlot cfgLF u unit cl) (progLF u unit cl) := by
  intro F
  simp only [progSlot, progLF]
  cases h : cl F with
  | none => trivial
  | some body =>
      obtain ⟨h₂, h₃⟩ := hcl F body h
      have e₁ : clauseOf cfgLF [5] u unit body =
          .app (.lam (.src ([5] ++ [9], u)) ((Src.names body).dedup.map fun y => ([5], y))
            ((annLF [] [5] [5] body).slotOf (fun _ => [5]) [5])) (.sym unit) := by
        simp only [clauseOf, rootSpellings, elabCfgX, elabCfg, cfgLF, elabForm, List.append_nil]
        rw [elabLF_eq_slotOf body [] [5] [5]]
      have e₂ : clauseId [5] u unit (elabLFFormAt [5] body) =
          .app (.lam (.src (.par u ([5] ++ [9])))
            (frameSlots [5] ((annLF [] [5] [5] body).idOf (lfRootEnv [5]) (fun _ => [5]) [5] [5]))
            ((annLF [] [5] [5] body).idOf (lfRootEnv [5]) (fun _ => [5]) [5] [5])) (.sym unit) := by
        simp only [clauseId, elabLFFormAt]
        rw [elabLFId_eq_idOf]
        rfl
      simp only [Option.map_some]
      rw [e₁, e₂]
      exact clause_rel u unit (annLF_WF body _ _ _ h₂) (by rw [freePars_annLF]; exact h₃)
        (fun y hy => List.mem_dedup.2 (by rwa [names_annLF] at hy))
        (fun y => lfRootEnv_ok [5] _ y)

/-! ## The renaming theorem -/

/-- **One result of each model, related by a renaming**: an injective map on
the names in play (the answer's free names and every name either store binds)
under which the answers are related values and the final stores are related
(each binding of one store is a binding of the other at the renamed name,
with related ground values, and nothing else is bound). -/
def Renamed (r₁ : Tm S (Slot X) × GStore S (Slot X)) (r₂ : Tm S (BId X) × GStore S (BId X)) :
    Prop :=
  ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (D : Set (Nm (Slot X))), (∀ n ∈ freeNames r₁.1, n ∈ D) ∧
    Set.InjOn ν D ∧ Rel SC ν μ .val [] true r₁.1 r₂.1 ∧ StoreRel SC ν D r₁.2 r₂.2

omit [DecidableEq X] in
theorem Out.renamed [DecidableEq X] {π π' : Path} {ν μ : Nm (Slot X) → Nm (BId X)}
    {D : Set (Nm (Slot X))} {Res Rc : List (Nm (BId X))} {r₁ : Tm S (Slot X) × GStore S (Slot X)}
    {r₂ : Tm S (BId X) × GStore S (BId X)} (h : Out SC π π' ν μ D Res Rc r₁ r₂) : Renamed r₁ r₂ := by
  obtain ⟨ν', D', hfv, -, hrel, -, hci⟩ := h
  exact ⟨ν', μ, D', hfv, hci.inj, hrel, hci.store⟩

variable [DecidableEq S]

/-- The renaming theorem from a related start. -/
theorem renaming_of {P₁ : S → Option (Tm S (Slot X))} {P₂ : S → Option (Tm S (BId X))}
    {t₁ : Tm S (Slot X)} {t₂ : Tm S (BId X)} (hP : ProgRel SC P₁ P₂)
    (hroot : ∃ (ν μ : Nm (Slot X) → Nm (BId X)) (Res : List (Nm (BId X))) (D : Set (Nm (Slot X)))
      (ok : Bool),
      Rel SC ν μ .code Res ok t₁ t₂ ∧ freeParams t₁ = [] ∧ (∀ x ∈ freeNames t₁, x ∈ D) ∧
      CI (SC : Setting S (Slot X) (BId X)) ν D (Res ++ []) Store.empty Store.empty ∧ Fresh [] [] ν D (Res ++ [])) :
    ((∃ n L₁, run .static P₁ n [] Store.empty t₁ = some L₁) ↔
        ∃ m L₂, run .static P₂ m [] Store.empty t₂ = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static P₁ n [] Store.empty t₁ = some L₁ → run .static P₂ m [] Store.empty t₂ = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨ν, μ, Res, D, _, hR, hfp, hfv, hci, hF⟩ := hroot
  exact ⟨defined_iff SC_biUnique SC_codeAgree SC_patAgree hP hR hfp hfv hci hF,
    fun h₁ h₂ => (bags_rel SC_biUnique SC_codeAgree SC_patAgree hP hR hfp hfv hci hF h₁ h₂).imp
      fun _ _ h => h.renamed⟩

/-- **The renaming theorem, rule M.**  On an admissible program and query, the
slot model's run (`cfgM`) and the identity model's run (`elabMFormAt`,
`progM`) are defined together, and their bags correspond result by result,
each pair related by an injective renaming of its names, answers and final
stores together. -/
theorem renaming_M (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L₁, run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L₁) ↔
        ∃ m L₂, run .static (progM u unit cl) m [] Store.empty (elabMFormAt [] t) = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L₁ →
        run .static (progM u unit cl) m [] Store.empty (elabMFormAt [] t) = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨h₂, h₃⟩ := ht
  have e₁ : elabCfg cfgM [] t =
      (annM (Src.direct t) [] (mRootEnv [] t) [] [] t).slotOf (fun _ => []) [] :=
    elabMS_eq_slotOf t _ _ _ _ _ _ _
  have e₂ : elabMFormAt [] t =
      (annM (Src.direct t) [] (mRootEnv [] t) [] [] t).idOf (mRootEnv [] t) (fun _ => []) [] [] :=
    elabMId_eq_idOf t _ _ _ _ _ _
  rw [e₁, e₂]
  exact renaming_of (progRel_M u unit cl hcl)
    (root_config (annM_WF t _ _ _ _ _ h₂) (by rw [freePars_annM]; exact h₃)
      (fun y => mRootEnv_ok [] t _ _ _ y))

/-- **The renaming theorem, lexical fresh.** -/
theorem renaming_LF (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L₁, run .static (progSlot cfgLF u unit cl) n [] Store.empty (elabCfg cfgLF [] t) = some L₁) ↔
        ∃ m L₂, run .static (progLF u unit cl) m [] Store.empty (elabLFFormAt [] t) = some L₂) ∧
      ∀ {n m : ℕ} {L₁ : Result S (Slot X)} {L₂ : Result S (BId X)},
        run .static (progSlot cfgLF u unit cl) n [] Store.empty (elabCfg cfgLF [] t) = some L₁ →
        run .static (progLF u unit cl) m [] Store.empty (elabLFFormAt [] t) = some L₂ →
          List.Forall₂ Renamed L₁ L₂ := by
  obtain ⟨h₂, h₃⟩ := ht
  have e₁ : elabCfg cfgLF [] t = (annLF [] [] [] t).slotOf (fun _ => []) [] :=
    elabLF_eq_slotOf t _ _ _ _ _
  have e₂ : elabLFFormAt [] t = (annLF [] [] [] t).idOf (lfRootEnv []) (fun _ => []) [] [] :=
    elabLFId_eq_idOf t _ _ _ _ _
  rw [e₁, e₂]
  exact renaming_of (progRel_LF u unit cl hcl)
    (root_config (annLF_WF t _ _ _ h₂) (by rw [freePars_annLF]; exact h₃)
      (fun y => lfRootEnv_ok [] _ y))

/-! ## The translator, in the slot model -/

omit [DecidableEq S] [DecidableEq X] in
theorem patsNewFree_wrapNew (ys : List X) (b : Src S X) :
    (wrapNew ys b).patsNewFree = b.patsNewFree := by
  cases ys <;> rfl

omit [DecidableEq S] in
theorem freePars_wrapNew (ys : List X) (b : Src S X) :
    (wrapNew ys b).freePars = b.freePars := by
  cases ys <;> rfl

omit [DecidableEq S] in
/-- The translation keeps the spine of a pattern. -/
theorem spineNewFree_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).spineNewFree = t.spineNewFree
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _ => rfl
  | .lam _ (some _) _, _, _, _, _, _ => rfl
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt f, spineNewFree_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree]
  | .letS p _ _ none, _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .letS p _ _ (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .unify p _ _, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt p]
  | .alt _ _, _, _, _, _, _ => rfl
  | .form _ _, _, _, _, _, _ => rfl
  | .new [] b, _, _, _, _, _ => by simp only [toLexAt, Src.spineNewFree, spineNewFree_toLexAt b]
  | .new (_ :: _) _, _, _, _, _, _ => rfl

omit [DecidableEq S] in
/-- The translation puts `new` blocks only around lambda bodies, off every
pattern's spine. -/
theorem patsNewFree_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).patsNewFree = t.patsNewFree
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_wrapNew, patsNewFree_toLexAt b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt f, patsNewFree_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.patsNewFree]
  | .letS p w b none, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, spineNewFree_toLexAt p, patsNewFree_toLexAt p,
        patsNewFree_toLexAt w, patsNewFree_toLexAt b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt t₁, patsNewFree_toLexAt t₂]
  | .new _ b, _, _, _, _, _ => by simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]
  | .form _ b, _, _, _, _, _ => by
      simp only [toLexAt, Src.patsNewFree, patsNewFree_toLexAt b]

omit [DecidableEq S] in
/-- The translation binds no parameter and frees none. -/
theorem freePars_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    (toLexAt E cr env fr pos t).freePars = t.freePars
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _ => rfl
  | .lam _ none b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_wrapNew, freePars_toLexAt b]
  | .lam _ (some _) b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt b]
  | .app f a, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt f, freePars_toLexAt a]
  | .pquote _, _, _, _, _, _ => by simp only [toLexAt, Src.freePars]
  | .letS p w b none, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .letS p w b (some _), _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .unify p w b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt p, freePars_toLexAt w, freePars_toLexAt b]
  | .alt t₁ t₂, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt t₁, freePars_toLexAt t₂]
  | .new _ b, _, _, _, _, _ => by simp only [toLexAt, Src.freePars, freePars_toLexAt b]
  | .form _ b, _, _, _, _, _ => by
      simp only [toLexAt, Src.freePars, freePars_toLexAt b]

omit [DecidableEq S] in
/-- **The translation of admissible text is admissible.** -/
theorem admissible_toLexAt {t : Src S X} (h : t.Admissible) (E cr : List X) (env : IEnv X)
    (fr pos : Owner) : (toLexAt E cr env fr pos t).Admissible :=
  ⟨by rw [patsNewFree_toLexAt]; exact h.1, by rw [freePars_toLexAt]; exact h.2⟩

/-- **The translator's correctness, in the slot model.**  On an admissible
program and query, the slot model's lexical fresh on the translated program and
query is defined exactly when the slot model's rule M on the source is; and
both bags are renamings, result by result, of one bag: the identity model's
bag of rule M on the source (which is, exactly, the identity model's bag of
lexical fresh on the translation, `run_toLexical`). -/
theorem transfer (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) :
    ((∃ n L, run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
        (elabCfg cfgLF [] (toLexical t)) = some L) ↔
      ∃ n L, run .static (progSlot cfgM u unit cl) n [] Store.empty (elabCfg cfgM [] t) = some L) ∧
    ∀ {n n' : ℕ} {L L' : Result S (Slot X)},
      run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
        (elabCfg cfgLF [] (toLexical t)) = some L →
      run .static (progSlot cfgM u unit cl) n' [] Store.empty (elabCfg cfgM [] t) = some L' →
      ∃ (k : ℕ) (L₂ : Result S (BId X)),
        run .static (progM u unit cl) k [] Store.empty (elabMFormAt [] t) = some L₂ ∧
        List.Forall₂ Renamed L L₂ ∧ List.Forall₂ Renamed L' L₂ := by
  have hclT : ∀ F body, toLexicalProg cl F = some body → body.Admissible := by
    intro F body h
    simp only [toLexicalProg, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact admissible_toLexAt (hcl F b hb) _ _ _ _ _
  have htT : (toLexical t).Admissible := admissible_toLexAt ht _ _ _ _ _
  obtain ⟨hLF₁, hLF₂⟩ := renaming_LF u unit (toLexicalProg cl) (toLexical t) hclT htT
  obtain ⟨hM₁, hM₂⟩ := renaming_M u unit cl t hcl ht
  have heq : ∀ n, run .static (progLF u unit (toLexicalProg cl)) n [] Store.empty
      (elabLFFormAt [] (toLexical t)) = run .static (progM u unit cl) n [] Store.empty
        (elabMFormAt [] t) :=
    fun n => run_toLexical u unit cl t .static n [] Store.empty
  refine ⟨?_, ?_⟩
  · rw [hLF₁, hM₁]
    simp only [heq]
  · intro n n' L L' h₁ h₂
    obtain ⟨m, L₂, hm⟩ := hLF₁.1 ⟨n, L, h₁⟩
    exact ⟨m, L₂, by rw [← heq]; exact hm, hLF₂ h₁ hm, hM₂ h₂ (by rw [← heq]; exact hm)⟩

/-! ## First-order answers: the slot model's two profiles, directly -/

/-- First-order terms of the same shape, their store names corresponding by
`R`. -/
def FOCorr {Y₁ Y₂ : Type v} (R : Nm Y₁ → Nm Y₂ → Prop) : Tm S Y₁ → Tm S Y₂ → Prop
  | .sym s, .sym s' => s = s'
  | .var n, .var m => R n m
  | .app f a, .app f' a' => FOCorr R f f' ∧ FOCorr R a a'
  | _, _ => False

/-- **Two results of the slot model, equal up to a one-to-one correspondence of
their names**: the answers have the same shape with corresponding names,
corresponding names hold the same value, and every name either store binds
has a partner. -/
def FOMatch (r₁ r₃ : Tm S (Slot X) × GStore S (Slot X)) : Prop :=
  ∃ R : Nm (Slot X) → Nm (Slot X) → Prop,
    (∀ n m m', R n m → R n m' → m = m') ∧ (∀ n n' m, R n m → R n' m → n = n') ∧
    FOCorr R r₁.1 r₃.1 ∧ (∀ n m, R n m → r₁.2 n = r₃.2 m) ∧
    (∀ n, r₁.2 n ≠ none → ∃ m, R n m) ∧ (∀ m, r₃.2 m ≠ none → ∃ n, R n m)

omit [DecidableEq S] in
/-- A value related to a first-order value is its renaming. -/
theorem Rel.val_firstOrder {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]
    {C : Setting S X₁ X₂} {ν μ : Nm X₁ → Nm X₂} :
    ∀ {t₁ : Tm S X₁} {R : List (Nm X₂)} {ok : Bool} {t₂ : Tm S X₂}, Rel C ν μ .val R ok t₁ t₂ →
      t₁.FirstOrder = true → t₂ = mapCode ν t₁
  | .sym _, _, _, _, h, _ => by cases h; rfl
  | .var _, _, _, _, h, _ => by cases h; rfl
  | .app f a, _, _, _, h, hfo => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo
      cases h with
      | app hf ha => rw [Rel.val_firstOrder hf hfo.1, Rel.val_firstOrder ha hfo.2]; rfl
      | letAct hk => exact absurd rfl hk
  | .fn _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .pvar _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .lam _ _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .quote _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .ctx _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .pquote _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .letP _ _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo
  | .alt _ _, _, _, _, _, hfo => by simp [Tm.FirstOrder] at hfo

omit [DecidableEq S] in
/-- A value related to a first-order value is first-order. -/
theorem Rel.val_firstOrder_left {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]
    {C : Setting S X₁ X₂} {ν μ : Nm X₁ → Nm X₂} :
    ∀ {t₁ : Tm S X₁} {R : List (Nm X₂)} {ok : Bool} {t₂ : Tm S X₂}, Rel C ν μ .val R ok t₁ t₂ →
      t₂.FirstOrder = true → t₁.FirstOrder = true
  | .sym _, _, _, _, _, _ => rfl
  | .var _, _, _, _, _, _ => rfl
  | .app f a, _, _, _, h, hfo => by
      cases h with
      | app hf ha =>
          simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo ⊢
          exact ⟨Rel.val_firstOrder_left hf hfo.1, Rel.val_firstOrder_left ha hfo.2⟩
      | letAct hk => exact absurd rfl hk
  | .fn _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .pvar _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .lam _ _ _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .quote _, _, _, _, h, hfo => by cases h; simp [Tm.FirstOrder] at hfo
  | .ctx _ _, _, _, _, h, hfo => by
      cases h
      simp [Tm.FirstOrder] at hfo
  | .pquote _, _, _, _, h, hfo => by
      cases h
      simp [Tm.FirstOrder] at hfo
  | .letP _ _ _, _, _, _, h, _ => by
      cases h with
      | letP hk => exact absurd rfl hk
  | .alt _ _, _, _, _, h, _ => by
      cases h with
      | alt hk => exact absurd rfl hk

omit [DecidableEq S] in
/-- Two first-order terms with the same image correspond, name by name. -/
theorem focorr_of_mapCode {ν₁ ν₃ : Nm (Slot X) → Nm (BId X)} {D₁ D₃ : Set (Nm (Slot X))} :
    ∀ {t₁ t₃ : Tm S (Slot X)}, t₁.FirstOrder = true → t₃.FirstOrder = true →
      mapCode ν₁ t₁ = mapCode ν₃ t₃ → (∀ n ∈ freeNames t₁, n ∈ D₁) → (∀ m ∈ freeNames t₃, m ∈ D₃) →
      FOCorr (fun n m => n ∈ D₁ ∧ m ∈ D₃ ∧ ν₁ n = ν₃ m) t₁ t₃
  | .sym s, .sym s', _, _, he, _, _ => by
      simp only [mapCode, Tm.sym.injEq] at he
      exact he
  | .var n, .var m, _, _, he, h₁, h₃ => by
      simp only [mapCode, Tm.var.injEq] at he
      exact ⟨h₁ n (by simp [freeNames]), h₃ m (by simp [freeNames]), he⟩
  | .app f a, .app f' a', hfo₁, hfo₃, he, h₁, h₃ => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at hfo₁ hfo₃
      simp only [mapCode, Tm.app.injEq] at he
      exact ⟨focorr_of_mapCode hfo₁.1 hfo₃.1 he.1 (fun n hn => h₁ n (by simp [freeNames, hn]))
          (fun m hm => h₃ m (by simp [freeNames, hm])),
        focorr_of_mapCode hfo₁.2 hfo₃.2 he.2 (fun n hn => h₁ n (by simp [freeNames, hn]))
          (fun m hm => h₃ m (by simp [freeNames, hm]))⟩
  | .sym _, .var _, _, _, he, _, _ => by simp [mapCode] at he
  | .sym _, .app _ _, _, _, he, _, _ => by simp [mapCode] at he
  | .var _, .sym _, _, _, he, _, _ => by simp [mapCode] at he
  | .var _, .app _ _, _, _, he, _, _ => by simp [mapCode] at he
  | .app _ _, .sym _, _, _, he, _, _ => by simp [mapCode] at he
  | .app _ _, .var _, _, _, he, _, _ => by simp [mapCode] at he
  | .fn _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .pvar _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .lam _ _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .quote _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .pquote _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .letP _ _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .alt _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .ctx _ _, _, h, _, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .sym _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .var _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .fn _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .pvar _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .lam _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .quote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .pquote _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .ctx _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .letP _ _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h
  | .app _ _, .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h

omit [DecidableEq S] [DecidableEq X] in
theorem firstOrder_mapCode {Y Z : Type v} {f : Nm Y → Nm Z} :
    ∀ {t : Tm S Y}, t.FirstOrder = true → (mapCode f t).FirstOrder = true
  | .sym _, _ => rfl
  | .var _, _ => rfl
  | .app a b, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at h
      simp only [mapCode, Tm.FirstOrder, Bool.and_eq_true]
      exact ⟨firstOrder_mapCode h.1, firstOrder_mapCode h.2⟩
  | .fn _, h => by simp [Tm.FirstOrder] at h
  | .pvar _, h => by simp [Tm.FirstOrder] at h
  | .lam _ _ _, h => by simp [Tm.FirstOrder] at h
  | .quote _, h => by simp [Tm.FirstOrder] at h
  | .pquote _, h => by simp [Tm.FirstOrder] at h
  | .ctx _ _, h => by simp [Tm.FirstOrder] at h
  | .letP _ _ _, h => by simp [Tm.FirstOrder] at h
  | .alt _ _, h => by simp [Tm.FirstOrder] at h

omit [DecidableEq S] in
/-- **Two slot results renamed into one identity result, with a first-order
answer, are equal up to a one-to-one correspondence of names**, stores
included. -/
theorem fomatch_of_renamed {r₁ r₃ : Tm S (Slot X) × GStore S (Slot X)}
    {r₂ : Tm S (BId X) × GStore S (BId X)} (h₁ : Renamed r₁ r₂) (h₃ : Renamed r₃ r₂)
    (hfo : r₁.1.FirstOrder = true) : FOMatch r₁ r₃ := by
  obtain ⟨ν₁, μ₁, D₁, hfv₁, hinj₁, hrel₁, hst₁⟩ := h₁
  obtain ⟨ν₃, μ₃, D₃, hfv₃, hinj₃, hrel₃, hst₃⟩ := h₃
  have e₁ := hrel₁.val_firstOrder hfo
  have hfo₂ : r₂.1.FirstOrder = true := by
    rw [e₁]
    exact firstOrder_mapCode hfo
  have hfo₃ := hrel₃.val_firstOrder_left hfo₂
  have e₃ := hrel₃.val_firstOrder hfo₃
  refine ⟨fun n m => n ∈ D₁ ∧ m ∈ D₃ ∧ ν₁ n = ν₃ m, ?_, ?_,
    focorr_of_mapCode hfo hfo₃ (e₁.symm.trans e₃) hfv₁ hfv₃, ?_, ?_, ?_⟩
  · rintro n m m' ⟨-, hm, he⟩ ⟨-, hm', he'⟩
    exact hinj₃ hm hm' (he.symm.trans he')
  · rintro n n' m ⟨hn, -, he⟩ ⟨hn', -, he'⟩
    exact hinj₁ hn hn' (he.trans he'.symm)
  · rintro n m ⟨hn, hm, he⟩
    have o₁ := hst₁.rel n hn
    have o₃ := hst₃.rel m hm
    rw [he] at o₁
    rcases OptRel.cases o₁ with ⟨a₁, b₁⟩ | ⟨g₁, g₂, a₁, b₁, hg₁⟩ <;>
      rcases OptRel.cases o₃ with ⟨a₃, b₃⟩ | ⟨g₃, g₂', a₃, b₃, hg₃⟩
    · rw [a₁, a₃]
    · rw [b₁] at b₃; cases b₃
    · rw [b₁] at b₃; cases b₃
    · rw [b₁] at b₃
      injection b₃ with b₃
      subst b₃
      rw [a₁, a₃, ((GRel.eq_iff SC_biUnique hg₁ hg₃).2 rfl)]
  · intro n hn
    have hnD := hst₁.dom n hn
    have o₁ := hst₁.rel n hnD
    rcases OptRel.cases o₁ with ⟨a₁, -⟩ | ⟨g₁, g₂, -, b₁, -⟩
    · exact absurd a₁ hn
    · obtain ⟨m, hm, he⟩ := hst₃.only (ν₁ n) (by rw [b₁]; simp)
      exact ⟨m, hnD, hm, he.symm⟩
  · intro m hm
    have hmD := hst₃.dom m hm
    have o₃ := hst₃.rel m hmD
    rcases OptRel.cases o₃ with ⟨a₃, -⟩ | ⟨g₃, g₂, -, b₃, -⟩
    · exact absurd a₃ hm
    · obtain ⟨n, hn, he⟩ := hst₁.only (ν₃ m) (by rw [b₃]; simp)
      exact ⟨n, hn, hmD, he⟩

omit [DecidableEq S] [DecidableEq X] in
theorem forall₂_through {α β γ : Type*} {R₁ : α → β → Prop} {R₃ : γ → β → Prop} :
    ∀ {L : List α} {L' : List γ} {L₂ : List β}, List.Forall₂ R₁ L L₂ → List.Forall₂ R₃ L' L₂ →
      List.Forall₂ (fun a c => ∃ b, R₁ a b ∧ R₃ c b) L L'
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ hs₁, .cons h₃ hs₃ => .cons ⟨_, h₁, h₃⟩ (forall₂_through hs₁ hs₃)

/-- **The translator's correctness on first-order answers, in the slot model,
directly**: result by result, when the answer is first-order, the slot model's
lexical fresh on the translation and its rule M on the source are equal up to a
one-to-one correspondence of names, answers and final stores together. -/
theorem transfer_firstOrder (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hcl : ∀ F body, cl F = some body → body.Admissible) (ht : t.Admissible) {n n' : ℕ}
    {L L' : Result S (Slot X)}
    (h₁ : run .static (progSlot cfgLF u unit (toLexicalProg cl)) n [] Store.empty
      (elabCfg cfgLF [] (toLexical t)) = some L)
    (h₂ : run .static (progSlot cfgM u unit cl) n' [] Store.empty (elabCfg cfgM [] t) = some L') :
    List.Forall₂ (fun r r' => r.1.FirstOrder = true → FOMatch r r') L L' := by
  obtain ⟨_, _, _, hA, hB⟩ := (transfer u unit cl t hcl ht).2 h₁ h₂
  exact (forall₂_through hA hB).imp fun _ _ ⟨_, ha, hb⟩ hfo => fomatch_of_renamed ha hb hfo

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
