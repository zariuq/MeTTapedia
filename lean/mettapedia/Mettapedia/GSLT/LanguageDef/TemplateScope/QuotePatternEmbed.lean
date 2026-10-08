import Mettapedia.GSLT.LanguageDef.TemplateScope.IdentitySlotRelation
import Mettapedia.GSLT.LanguageDef.TemplateScope.QuotePatternRel

/-!
# Pattern quotations as related code

A pattern quotation is code. `CodeRel` compares its binders by one map, with
empty own lists. That comparison is a `Rel` at kind `code`: a hole is a free
store name, and a binder of the code is a name inside the body.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]

variable {C : Setting S X₁ X₂}

/-- Own lists excluded by `True` bind nothing. -/
private theorem ownKey_of_not_true {Y : Type v} [DecidableEq Y] {own : List Y}
    (hr : ∀ s ∈ own, ¬ True) (n : Nm Y) : ownKey own n = false := by
  cases n with
  | inst _ _ => rfl
  | src s =>
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      intro hs
      exact hr s hs trivial

/-- Code related by one map, with no root kept on an own list, is related term
code, and the pair is stable. The same map sends store names and parameters.
A hole compares as the setting's hole, a parameter as the setting's parameter,
and a lambda's binders as the setting allows for own lists that `True`
excludes. The kind is not a value, so a `let` inside the code may sit in a
pattern. The body's stability bit is `true`: this relation builds no pending
activation. -/
theorem Rel.of_codeRel {Q : Tm S X₁ → Tm S X₂ → Prop} {f : Nm X₁ → Nm X₂}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (hQ : ∀ {c₁ c₂}, Q c₁ c₂ → C.Q c₁ c₂)
    (hv : ∀ n, C.varHole n (f n)) (hp : ∀ x, C.parOK x (f x))
    (hbare : ∀ {x : Nm X₁} {own₁ : List X₁} {own₂ : List X₂},
      (∀ s ∈ own₁, ¬ True) → (∀ s ∈ own₂, ¬ True) → C.bareLam x own₁ (f x) own₂)
    (h : CodeRel (R₁ := fun (_ : X₁) => True) (R₂ := fun (_ : X₂) => True)
      Q (fun _ => True) f t₁ t₂) (k : Kd) (hk : k ≠ .val) :
    Rel C f f k [] true t₁ t₂ := by
  induction h generalizing k with
  | sym s => exact .sym s
  | fn F => exact .fn F
  | var n => exact .var n (hv n)
  | @pvar x _ => exact .pvar x (hp x)
  | quote hq => exact .quote (hQ hq)
  | pquote _ ih =>
      have hb := ih .code (by decide)
      exact .pquote hb (hb.shape_of rfl) rfl
  | app _ _ ihf iha =>
      exact .app (ihf k hk) (iha k hk)
  | alt _ _ ih₁ ih₂ =>
      exact .alt hk (ih₁ .code (by decide)) (ih₂ .code (by decide))
  | letP _ _ _ ihp ihw ihb =>
      exact .letP hk (ihp .pat (by decide)) (ihw .code (by decide)) (ihb .code (by decide))
  | lam hx _ hr₁ hr₂ _ hpar _ ihb =>
      have hnil₁ := ownKey_of_not_true hr₁
      have hnil₂ := ownKey_of_not_true hr₂
      refine .lam (νb := f) (μb := f) (fun _ _ => rfl) (fun _ _ => rfl) hx ?_ ?_
        (ihb .code (by decide)) ?_ ?_ ?_ ?_ List.nodup_nil hpar
        (hx ▸ hbare hr₁ hr₂) (fun _ => rfl)
      · intro s hs _
        exact hr₁ s hs trivial
      · intro s hs _
        exact hr₂ s hs trivial
      · intro n _
        rw [hnil₂ (f n), hnil₁ n]
      · intro _ hm
        cases hm
      · intro n _ n' _ ho _ _
        rw [hnil₁ n] at ho
        cases ho
      · intro n _ ho
        rw [hnil₁ n] at ho
        cases ho

/-- The two elaborations of one pattern quotation are related stable code.
Holes are the outer slots; code binders travel by `codeMapHoles`. `C.Q`
accepts every pair of sealed quotations. The three readings are the setting's
hole comparison, parameter comparison, and lambda binders. -/
theorem Rel.code_pattern {X : Type v} [DecidableEq X] {C : Setting S (Slot X) (BId X)}
    (hQ : ∀ {c₁ c₂}, codeQ c₁ c₂ → C.Q c₁ c₂)
    (env : REnv X) (envI : IEnv X)
    (hv : ∀ n, C.varHole n (codeMapHoles env envI n))
    (hp : ∀ x, C.parOK x (codeMapHoles env envI x))
    (hbare : ∀ {x : Nm (Slot X)} {own₁ : List (Slot X)} {own₂ : List (BId X)},
      (∀ s ∈ own₁, ¬ True) → (∀ s ∈ own₂, ¬ True) →
        C.bareLam x own₁ (codeMapHoles env envI x) own₂)
    (hB : ∀ y, codeBound (env y) = false) (hF : ∀ y, env y ≠ codeFreeParam)
    (c : Src S X) (k : Kd) (hk : k ≠ .val) :
    Rel C (codeMapHoles env envI) (codeMapHoles env envI)
      k [] true (sealParams (codeAt (some env) [] [] [] c))
      (sealParams (codeIAt (some envI) [] [] [] c)) :=
  Rel.of_codeRel (C := C) (f := codeMapHoles env envI) hQ hv hp hbare
    (codeRel_pattern env envI hB hF c) k hk

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
