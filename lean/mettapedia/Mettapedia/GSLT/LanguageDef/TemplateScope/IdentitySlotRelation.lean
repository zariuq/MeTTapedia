import Mettapedia.GSLT.LanguageDef.TemplateScope.Defunctionalization

/-!
# Template scope: relating two name disciplines of one evaluator

Two elaborations of one program into the evaluator's terms (`Tm S X₁` and
`Tm S X₂`) can differ in three ways that a plain renaming does not cover:

* **store names**: an injective map `ν` from the first side's names to the
  second side's;
* **parameters**: a binder-respecting map `μ`, so that parameters may be named
  by spelling on one side (shadowing) and by binder position on the other;
* **allocation**: a `let` or a `new` block may be an *activation* on the first
  side, `((lam ℓ own (let p ℓ b)) w)` or `((lam ℓ own b) (lam ℓ [] ℓ))`, which
  renames its own slots when it runs, and a plain `let` (or nothing) on the
  second side, whose slots belong to the enclosing frame and were renamed when
  that frame was activated.  Until the first side's activation runs, the
  second side's slots are **reserved**: free, unbound, and used only inside the
  construct.  `Rel` carries them as a list, split among subterms, so that each
  reserved name belongs to exactly one pending construct.

`Rel C ν μ k Res ok t₁ t₂` is that relation.  The kind `k` says where the pair
sits: a value (`val`: no pending construct outside lambdas), a pattern (`pat`:
no `new` block along the matched spine), or code.  `ok = true` when no pending
activation sits where matching of code can enter.

## Main results

* `Rel.congr` — the relation reads `ν` and `μ` only on free names and
  parameters.
* `Rel.substitute` — **substitution preserves the relation**: renaming slots on
  one side or both, instantiating parameters, substituting values for store
  names, and applying a store are all instances.
* `Rel.mem_freeNames`, `Rel.mem_freeParams` — free names and parameters
  correspond.
* `Rel.toGVal?` — related values read back as related ground values.
* `Rel.matchT` — matching related patterns against related ground values
  succeeds together, with related stores.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v}

/-- Where a related pair of terms sits. -/
inductive Kd where
  /-- A value: no pending construct outside lambdas. -/
  | val
  /-- A pattern: no `new` block along the matched spine. -/
  | pat
  /-- Code. -/
  | code
  deriving DecidableEq, Repr

/-- The order of kinds: `val ≤ pat ≤ code`. -/
def Kd.le : Kd → Kd → Prop
  | .val, _ => True
  | .pat, .pat => True
  | .pat, .code => True
  | .code, .code => True
  | _, _ => False

/-- The parameters of the relation. -/
structure Setting (S : Type u) (X₁ X₂ : Type v) where
  /-- Related sealed code. -/
  Q : Tm S X₁ → Tm S X₂ → Prop
  /-- Base names of the first side that may occur free outside activations: no
  binder owns them. -/
  root₁ : X₁ → Prop
  /-- The same on the second side. -/
  root₂ : X₂ → Prop
  /-- A store name and its image are holes together, or binders of code together. -/
  varHole : Nm X₁ → Nm X₂ → Prop
  /-- A parameter and its image are parameters of code together, or of the
  surrounding scope together. -/
  parOK : Nm X₁ → Nm X₂ → Prop
  /-- Binders a related lambda may carry. Scope binders are holes, at any own
  lists. Binders of code are not holes, own nothing, and share an owner. -/
  bareLam : Nm X₁ → List X₁ → Nm X₂ → List X₂ → Prop
  /-- Binders `matchCode` may enter against code: not holes. -/
  enterLam : Nm X₁ → Nm X₂ → Prop
  /-- Entered binders own nothing. -/
  enter_nil : ∀ {x₁ own₁ x₂ own₂}, bareLam x₁ own₁ x₂ own₂ → enterLam x₁ x₂ →
    own₁ = [] ∧ own₂ = []
  /-- Second-side names that compare alike after a renaming. -/
  preserve : Nm X₂ → Nm X₂ → Prop
  /-- A name compares as itself. -/
  preserve_refl : ∀ m, preserve m m
  /-- An activation copy compares as the name it copies. -/
  preserve_inst : ∀ (ρ : Path) (m : Nm X₂), preserve m (.inst ρ m)
  /-- Copying the first side's name keeps a hole comparison. -/
  varHole_instL : ∀ {n m} (ρ : Path), varHole n m → varHole (.inst ρ n) m
  /-- Renaming the second side's name keeps a hole comparison. -/
  varHole_rename : ∀ {n m m'}, varHole n m → preserve m m' → varHole n m'
  /-- Reading of code names. Contextual code is related only along this map. -/
  codeMap : Nm X₁ → Nm X₂
  /-- `codeMap` does not identify distinct names. -/
  codeMap_inj : Function.Injective codeMap

/-- Rename every name. Own lists are dropped: a term with `ownNil` keeps them empty. -/
def mapCode {Y Z : Type v} (f : Nm Y → Nm Z) : Tm S Y → Tm S Z
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var (f n)
  | .pvar n => .pvar (f n)
  | .lam x _ b => .lam (f x) [] (mapCode f b)
  | .app a b => .app (mapCode f a) (mapCode f b)
  | .quote c => .quote (mapCode f c)
  | .ctx ks c => .ctx (ks.map f) (mapCode f c)
  | .pquote c => .pquote (mapCode f c)
  | .letP p w b => .letP (mapCode f p) (mapCode f w) (mapCode f b)
  | .alt t₁ t₂ => .alt (mapCode f t₁) (mapCode f t₂)

/-- Every lambda in the term has an empty own list. -/
def ownNil {Y : Type v} : Tm S Y → Prop
  | .lam _ own b => own = [] ∧ ownNil b
  | .app f a => ownNil f ∧ ownNil a
  | .quote c => ownNil c
  | .ctx _ c => ownNil c
  | .pquote c => ownNil c
  | .letP p w b => ownNil p ∧ ownNil w ∧ ownNil b
  | .alt t₁ t₂ => ownNil t₁ ∧ ownNil t₂
  | _ => True

theorem list_map_injective {α β : Type v} {f : α → β} (hf : Function.Injective f) :
    ∀ {l₁ l₂ : List α}, List.map f l₁ = List.map f l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by
      simp only [List.map] at h
      cases h
  | _ :: _, [], h => by
      simp only [List.map] at h
      cases h
  | _ :: l₁, _ :: l₂, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, list_map_injective hf h.2]

/-- On terms whose lambdas own nothing, renaming along an injective map is injective. -/
theorem mapCode_injective_ownNil {Y Z : Type v} {f : Nm Y → Nm Z}
    (hf : Function.Injective f) {t₁ : Tm S Y} :
    ∀ {t₂ : Tm S Y}, ownNil t₁ → ownNil t₂ → mapCode f t₁ = mapCode f t₂ → t₁ = t₂ := by
  induction t₁ with
  | sym s =>
      intro t₂ _ _ h
      cases t₂ with
      | sym _ =>
          simp only [mapCode, Tm.sym.injEq] at h
          rw [h]
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | fn F =>
      intro t₂ _ _ h
      cases t₂ with
      | fn _ =>
          simp only [mapCode, Tm.fn.injEq] at h
          rw [h]
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | var n =>
      intro t₂ _ _ h
      cases t₂ with
      | var _ =>
          simp only [mapCode, Tm.var.injEq] at h
          rw [hf h]
      | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | pvar n =>
      intro t₂ _ _ h
      cases t₂ with
      | pvar _ =>
          simp only [mapCode, Tm.pvar.injEq] at h
          rw [hf h]
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | lam x own b ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | lam x' own' b' =>
          simp only [ownNil] at h₁ h₂
          rcases h₁ with ⟨rfl, hb⟩
          rcases h₂ with ⟨rfl, hb'⟩
          simp only [mapCode, Tm.lam.injEq] at h
          rcases h with ⟨hx, _, hbdy⟩
          rw [hf hx, ih hb hb' hbdy]
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | app f₁ a₁ ihf iha =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | app f₂ a₂ =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.app.injEq] at h
          rw [ihf h₁.1 h₂.1 h.1, iha h₁.2 h₂.2 h.2]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | quote c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | quote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.quote.injEq] at h
          rw [ih h₁ h₂ h]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | ctx _ _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | ctx ks c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | ctx ks' c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.ctx.injEq] at h
          rcases h with ⟨hks, hc⟩
          rw [list_map_injective hf hks, ih h₁ h₂ hc]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | pquote c ih =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | pquote c' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.pquote.injEq] at h
          rw [ih h₁ h₂ h]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | letP p w b ihp ihw ihb =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | letP p' w' b' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.letP.injEq] at h
          rcases h with ⟨hp, hw, hb⟩
          rw [ihp h₁.1 h₂.1 hp, ihw h₁.2.1 h₂.2.1 hw, ihb h₁.2.2 h₂.2.2 hb]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | alt _ _ =>
          simp only [mapCode] at h
          cases h
  | alt a b iha ihb =>
      intro t₂ h₁ h₂ h
      cases t₂ with
      | alt a' b' =>
          simp only [ownNil] at h₁ h₂
          simp only [mapCode, Tm.alt.injEq] at h
          rw [iha h₁.1 h₂.1 h.1, ihb h₁.2 h₂.2 h.2]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | ctx _ _ | pquote _ | letP _ _ _ =>
          simp only [mapCode] at h
          cases h

/-- Related ground values: the same data, with related code in quotations.
Contextual code is the same open code read along `codeMap`. -/
inductive GRel (C : Setting S X₁ X₂) : GVal S X₁ → GVal S X₂ → Prop
  | sym (s : S) : GRel C (.sym s) (.sym s)
  | app {f₁ a₁ f₂ a₂} : GRel C f₁ f₂ → GRel C a₁ a₂ → GRel C (.app f₁ a₁) (.app f₂ a₂)
  | quote {c₁ c₂} : C.Q c₁ c₂ → GRel C (.quote c₁) (.quote c₂)
  /-- Open code under the binders it mentions, read along `codeMap`. -/
  | ctx {ks₁ : List (Nm X₁)} {c₁ : Tm S X₁} {ks₂ : List (Nm X₂)} {c₂ : Tm S X₂}
      (ho : ownNil c₁) (hks : ks₂ = ks₁.map C.codeMap) (hc : c₂ = mapCode C.codeMap c₁) :
      GRel C (.ctx ks₁ c₁) (.ctx ks₂ c₂)

/-- Names that may occur free: activation copies, and root names. -/
def OK₁ (C : Setting S X₁ X₂) : Nm X₁ → Prop
  | .src s => C.root₁ s
  | .inst _ _ => True

/-- The same on the second side. -/
def OK₂ (C : Setting S X₁ X₂) : Nm X₂ → Prop
  | .src s => C.root₂ s
  | .inst _ _ => True

/-- Same outer shape, with the setting's reading of names. A lambda contributes
its binders only: a body is read by `matchCode` only after `enterLam`, and that
permission is recorded on the relation, not here. -/
def ShapeParallel (C : Setting S X₁ X₂) : Tm S X₁ → Tm S X₂ → Prop
  | .sym s₁, .sym s₂ => s₁ = s₂
  | .fn f₁, .fn f₂ => f₁ = f₂
  | .var n₁, .var n₂ => C.varHole n₁ n₂
  | .pvar x₁, .pvar x₂ => C.parOK x₁ x₂
  | .lam x₁ o₁ _, .lam x₂ o₂ _ => C.bareLam x₁ o₁ x₂ o₂
  | .app f₁ a₁, .app f₂ a₂ => ShapeParallel C f₁ f₂ ∧ ShapeParallel C a₁ a₂
  | .quote c₁, .quote c₂ => C.Q c₁ c₂
  | .pquote c₁, .pquote c₂ => ShapeParallel C c₁ c₂
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      ShapeParallel C p₁ p₂ ∧ ShapeParallel C w₁ w₂ ∧ ShapeParallel C b₁ b₂
  | .alt t₁ u₁, .alt t₂ u₂ => ShapeParallel C t₁ t₂ ∧ ShapeParallel C u₁ u₂
  | .ctx ks₁ c₁, .ctx ks₂ c₂ =>
      ks₂ = ks₁.map C.codeMap ∧ c₂ = mapCode C.codeMap c₁
  | _, _ => False

variable [DecidableEq X₁] [DecidableEq X₂]

/-- **The relation.**  `ν` maps store names, `μ` parameters; `Res` lists the
reserved names of the second side that the pair's pending constructs own.
`ok = true` when no pending activation sits where matching of code can enter.
A lambda's own result is stable even when its body is not: matching enters
that body only when `enterLam` holds, and then the body is stable too. -/
inductive Rel (C : Setting S X₁ X₂) :
    (Nm X₁ → Nm X₂) → (Nm X₁ → Nm X₂) → Kd → List (Nm X₂) → Bool →
      Tm S X₁ → Tm S X₂ → Prop
  | sym {ν μ k} (s : S) : Rel C ν μ k [] true (.sym s) (.sym s)
  | fn {ν μ k} (F : S) : Rel C ν μ k [] true (.fn F) (.fn F)
  | var {ν μ k} (n : Nm X₁) (hv : C.varHole n (ν n)) :
      Rel C ν μ k [] true (.var n) (.var (ν n))
  | pvar {ν μ k} (x : Nm X₁) (hp : C.parOK x (μ x)) :
      Rel C ν μ k [] true (.pvar x) (.pvar (μ x))
  | quote {ν μ k c₁ c₂} (h : C.Q c₁ c₂) : Rel C ν μ k [] true (.quote c₁) (.quote c₂)
  /-- A pattern quotation. The body is stable code of one shape: a hole is a
  free name of that code, and a binder of the code is named inside the body. -/
  | pquote {ν μ k c₁ c₂ ob}
      (h : Rel C ν μ .code [] ob c₁ c₂) (hp : ShapeParallel C c₁ c₂) (hok : ob = true) :
      Rel C ν μ k [] true (.pquote c₁) (.pquote c₂)
  | app {ν μ k R₁ R₂ o₁ o₂ f₁ a₁ f₂ a₂}
      (hf : Rel C ν μ k R₁ o₁ f₁ f₂) (ha : Rel C ν μ k R₂ o₂ a₁ a₂) :
      Rel C ν μ k (R₁ ++ R₂) (o₁ && o₂) (.app f₁ a₁) (.app f₂ a₂)
  | letP {ν μ k Rp Rw Rb op ow ob p₁ w₁ b₁ p₂ w₂ b₂} (hk : k ≠ .val)
      (hp : Rel C ν μ .pat Rp op p₁ p₂) (hw : Rel C ν μ .code Rw ow w₁ w₂)
      (hb : Rel C ν μ .code Rb ob b₁ b₂) :
      Rel C ν μ k (Rp ++ Rw ++ Rb) (op && ow && ob) (.letP p₁ w₁ b₁) (.letP p₂ w₂ b₂)
  | alt {ν μ k R₁ R₂ o₁ o₂ t₁ u₁ t₂ u₂} (hk : k ≠ .val)
      (h₁ : Rel C ν μ .code R₁ o₁ t₁ t₂) (h₂ : Rel C ν μ .code R₂ o₂ u₁ u₂) :
      Rel C ν μ k (R₁ ++ R₂) (o₁ && o₂) (.alt t₁ u₁) (.alt t₂ u₂)
  | lam {ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb ob}
      (hνb : ∀ n, ownKey own₁ n = false → νb n = ν n)
      (hμb : ∀ x, x ≠ x₁ → μb x = μ x) (hμx : μb x₁ = x₂)
      (hr₁ : ∀ s ∈ own₁, ¬ C.root₁ s) (hr₂ : ∀ s ∈ own₂, ¬ C.root₂ s)
      (hb : Rel C νb μb .code Rb ob b₁ b₂)
      (hown : ∀ n ∈ freeNames b₁, ownKey own₂ (νb n) = ownKey own₁ n)
      (hres : ∀ m ∈ Rb, ownKey own₂ m = true)
      (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁, ownKey own₁ n = true →
        ownKey own₁ n' = true → νb n = νb n' → n = n')
      (hdisj : ∀ n ∈ freeNames b₁, ownKey own₁ n = true → νb n ∉ Rb)
      (hnd : Rb.Nodup)
      (hpar : ∀ x ∈ freeParams b₁, x ≠ x₁ → μ x ≠ x₂)
      (hbare : C.bareLam x₁ own₁ x₂ own₂)
      (hseen : C.enterLam x₁ x₂ → ob = true) :
      Rel C ν μ k [] true (.lam x₁ own₁ b₁) (.lam x₂ own₂ b₂)
  | letAct {ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb ow op ob} (hk : k ≠ .val)
      (hνi : ∀ n, ownKey own n = false → νi n = ν n)
      (hr : ∀ s ∈ own, ¬ C.root₁ s)
      (hℓp : ℓ ∉ freeParams p₁) (hℓb : ℓ ∉ freeParams b₁)
      (hw : Rel C ν μ .code Rw ow w₁ w₂) (hp : Rel C νi μ .pat Rp op p₁ p₂)
      (hb : Rel C νi μ .code Rb ob b₁ b₂)
      (hlive : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
      (hinj : ∀ n ∈ freeNames p₁ ++ freeNames b₁, ∀ n' ∈ freeNames p₁ ++ freeNames b₁,
        ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n') :
      Rel C ν μ k (Rh ++ Rw ++ Rp ++ Rb) false
        (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) (.letP p₂ w₂ b₂)
  | newAct {ν μ ℓ own b₁ b₂ νi Rh Rb ob}
      (hνi : ∀ n, ownKey own n = false → νi n = ν n)
      (hr : ∀ s ∈ own, ¬ C.root₁ s)
      (hℓ : ℓ ∉ freeParams b₁)
      (hb : Rel C νi μ .code Rb ob b₁ b₂)
      (hlive : ∀ n ∈ freeNames b₁, ownKey own n = true → νi n ∈ Rh)
      (hinj : ∀ n ∈ freeNames b₁, ∀ n' ∈ freeNames b₁,
        ownKey own n = true → ownKey own n' = true → νi n = νi n' → n = n') :
      Rel C ν μ .code (Rh ++ Rb) false (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) b₂
  /-- Contextual code, a value. The body is read along `codeMap`. -/
  | ctx {ν μ k ks₁ c₁ ks₂ c₂}
      (ho : ownNil c₁) (hks : ks₂ = ks₁.map C.codeMap) (hc : c₂ = mapCode C.codeMap c₁) :
      Rel C ν μ k [] true (.ctx ks₁ c₁) (.ctx ks₂ c₂)

variable {C : Setting S X₁ X₂}

/-! ## Basic facts -/

theorem Kd.le_refl : ∀ k : Kd, k.le k
  | .val => trivial
  | .pat => trivial
  | .code => trivial

theorem Kd.le_code : ∀ k : Kd, k.le .code
  | .val => trivial
  | .pat => trivial
  | .code => trivial

theorem Kd.ne_val_of_le {k k' : Kd} (h : k.le k') (hk : k ≠ .val) : k' ≠ .val := by
  cases k <;> cases k' <;> simp_all [Kd.le]

theorem Kd.eq_code_of_le {k : Kd} (h : Kd.code.le k) : k = .code := by
  cases k <;> simp_all [Kd.le]

/-- Only a value sits at or below a value. -/
theorem Kd.eq_val_of_le {k : Kd} (h : k.le .val) : k = .val := by
  cases k <;> simp_all [Kd.le]

/-- A larger kind admits more. The stability bit is unchanged. -/
theorem Rel.mono {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {k'}, k.le k' → Rel C ν μ k' Res ok t₁ t₂ := by
  induction h with
  | sym s => intro _ _; exact .sym s
  | fn F => intro _ _; exact .fn F
  | var n hv => intro _ _; exact .var n hv
  | pvar x hp => intro _ _; exact .pvar x hp
  | quote hq => intro _ _; exact .quote hq
  | ctx ho hks hc => intro _ _; exact .ctx ho hks hc
  | pquote h hp hok => intro _ _; exact .pquote h hp hok
  | app _ _ ihf iha => intro _ hk; exact .app (ihf hk) (iha hk)
  | letP hk' hp hw hb => intro _ hk; exact .letP (Kd.ne_val_of_le hk hk') hp hw hb
  | alt hk' h₁ h₂ => intro _ hk; exact .alt (Kd.ne_val_of_le hk hk') h₁ h₂
  | lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen =>
      intro _ _
      exact .lam hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar hbare hseen
  | letAct hk' hνi hr hℓp hℓb hw hp hb hlive hinj =>
      intro _ hk; exact .letAct (Kd.ne_val_of_le hk hk') hνi hr hℓp hℓb hw hp hb hlive hinj
  | newAct hνi hr hℓ hb hlive hinj =>
      intro _ hk
      rw [Kd.eq_code_of_le hk]
      exact .newAct hνi hr hℓ hb hlive hinj

/-- A value is related as anything. Its stability bit is `true`. -/
theorem Rel.of_val {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ .val Res true t₁ t₂) (k : Kd) : Rel C ν μ k Res true t₁ t₂ :=
  h.mono trivial

omit [DecidableEq X₂] in
/-- A name that may occur free is owned by no binder of the first side. -/
theorem ownKey_of_OK₁ {own : List X₁} (hr : ∀ s ∈ own, ¬ C.root₁ s) :
    ∀ {n : Nm X₁}, OK₁ C n → ownKey own n = false
  | .src s, h => by
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | .inst _ _, _ => rfl

omit [DecidableEq X₁] in
/-- The same on the second side. -/
theorem ownKey_of_OK₂ {own : List X₂} (hr : ∀ s ∈ own, ¬ C.root₂ s) :
    ∀ {n : Nm X₂}, OK₂ C n → ownKey own n = false
  | .src s, h => by
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | .inst _ _, _ => rfl

theorem mem_freeNames_lam {x : Nm X₁} {own : List X₁} {b : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.lam x own b : Tm S X₁) ↔ n ∈ freeNames b ∧ ownKey own n = false := by
  simp [freeNames]

theorem mem_freeParams_lam {x : Nm X₁} {own : List X₁} {b : Tm S X₁} {y : Nm X₁} :
    y ∈ freeParams (.lam x own b : Tm S X₁) ↔ y ∈ freeParams b ∧ y ≠ x := by
  simp [freeParams]

/-! ## Free names and parameters correspond -/

/-- Every free name of the first side is sent to a free name of the second. -/
theorem Rel.mem_freeNames {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {n}, n ∈ freeNames t₁ → ν n ∈ freeNames t₂ := by
  induction h with
  | sym s => intro n hn; simp [freeNames] at hn
  | fn F => intro n hn; simp [freeNames] at hn
  | var m _ => intro n hn; simp only [freeNames, List.mem_singleton] at hn ⊢; rw [hn]
  | pvar x _ => intro n hn; simp [freeNames] at hn
  | quote _ => intro n hn; simp [freeNames] at hn
  | ctx _ _ _ => intro n hn; simp [freeNames] at hn
  | pquote _ _ _ ih =>
      intro n hn
      simp only [freeNames] at hn ⊢
      exact ih hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      rcases hn with (hn | hn) | hn
      · exact Or.inl (Or.inl (ihp hn))
      · exact Or.inl (Or.inr (ihw hn))
      · exact Or.inr (ihb hn)
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ih₁ ih₂
  | lam hνb _ _ _ _ _ hown _ _ _ _ _ _ _ ihb =>
      intro n hn
      rw [mem_freeNames_lam] at hn ⊢
      obtain ⟨hn, hk⟩ := hn
      have e := hνb n hk
      refine ⟨e ▸ ihb hn, ?_⟩
      rw [← e, hown n hn, hk]
  | letAct _ hνi _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.not_mem_nil, or_false] at hn ⊢
      rcases hn with ⟨hn | hn, hk⟩ | hn
      · rw [← hνi n hk]; exact Or.inl (Or.inl (ihp hn))
      · rw [← hνi n hk]; exact Or.inr (ihb hn)
      · exact Or.inl (Or.inr (ihw hn))
  | newAct hνi _ _ _ _ _ ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      rcases hn with ⟨hn, hk⟩ | ⟨hf, _⟩
      · rw [← hνi n hk]
        exact ihb hn
      · exact hf.elim

/-- Every free parameter of the first side is sent to a free parameter of the
second. -/
theorem Rel.mem_freeParams {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → μ x ∈ freeParams t₂ := by
  induction h with
  | sym s => intro x hx; simp [freeParams] at hx
  | fn F => intro x hx; simp [freeParams] at hx
  | var m _ => intro x hx; simp [freeParams] at hx
  | pvar y _ => intro x hx; simp only [freeParams, List.mem_singleton] at hx ⊢; rw [hx]
  | quote _ => intro x hx; simp [freeParams] at hx
  | ctx _ _ _ => intro x hx; simp [freeParams] at hx
  | pquote _ _ _ ih =>
      intro x hx
      simp only [freeParams] at hx ⊢
      exact ih hx
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (ihp hx))
      · exact Or.inl (Or.inr (ihw hx))
      · exact Or.inr (ihb hx)
  | alt _ _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ih₁ ih₂
  | lam _ hμb hμx _ _ _ _ _ _ _ _ hpar _ _ ihb =>
      intro x hx
      rw [mem_freeParams_lam] at hx ⊢
      obtain ⟨hx, hne⟩ := hx
      have e := hμb x hne
      exact ⟨e ▸ ihb hx, hpar x hx hne⟩
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx ⊢
      rcases hx with ⟨(hx | hx) | hx, hne⟩ | hx
      · exact Or.inl (Or.inl (ihp hx))
      · exact absurd hx hne
      · exact Or.inr (ihb hx)
      · exact Or.inl (Or.inr (ihw hx))
  | newAct _ _ _ _ _ _ ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, hne⟩
      · exact ihb hx
      · exact absurd hx hne


/-! ## Free names and parameters of the two pending constructs -/

theorem mem_freeNames_letAct {ℓ : Nm X₁} {own : List X₁} {p b w : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.app (.lam ℓ own (.letP p (.pvar ℓ) b)) w : Tm S X₁) ↔
      ((n ∈ freeNames p ∨ n ∈ freeNames b) ∧ ownKey own n = false) ∨ n ∈ freeNames w := by
  simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.not_mem_nil, or_false]

theorem mem_freeParams_letAct {ℓ : Nm X₁} {own : List X₁} {p b w : Tm S X₁} {x : Nm X₁} :
    x ∈ freeParams (.app (.lam ℓ own (.letP p (.pvar ℓ) b)) w : Tm S X₁) ↔
      ((x ∈ freeParams p ∨ x ∈ freeParams b) ∧ x ≠ ℓ) ∨ x ∈ freeParams w := by
  simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro (⟨(h | h) | h, hne⟩ | h)
    · exact Or.inl ⟨Or.inl h, hne⟩
    · exact absurd h hne
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr h
  · rintro (⟨h | h, hne⟩ | h)
    · exact Or.inl ⟨Or.inl (Or.inl h), hne⟩
    · exact Or.inl ⟨Or.inr h, hne⟩
    · exact Or.inr h

theorem mem_freeNames_newAct {ℓ : Nm X₁} {own : List X₁} {b : Tm S X₁} {n : Nm X₁} :
    n ∈ freeNames (.app (.lam ℓ own b) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) ↔
      n ∈ freeNames b ∧ ownKey own n = false := by
  simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.not_mem_nil, false_and, or_false]

theorem mem_freeParams_newAct {ℓ : Nm X₁} {own : List X₁} {b : Tm S X₁} {x : Nm X₁} :
    x ∈ freeParams (.app (.lam ℓ own b) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) ↔
      x ∈ freeParams b ∧ x ≠ ℓ := by
  simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro (h | ⟨h, hne⟩)
    · exact h
    · exact absurd h hne
  · intro h
    exact Or.inl h

/-! ## Congruence -/

/-- **The relation reads `ν` and `μ` only on free names and parameters.** -/
theorem Rel.congr {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {ν' μ' : Nm X₁ → Nm X₂}, (∀ n ∈ freeNames t₁, ν n = ν' n) →
      (∀ x ∈ freeParams t₁, μ x = μ' x) → Rel C ν' μ' k Res ok t₁ t₂ := by
  induction h with
  | sym s => intro _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _; exact .fn F
  | var n hv =>
      intro ν' μ' hν _
      have hv' : C.varHole n (ν' n) := by
        rw [← hν n (by simp [freeNames])]
        exact hv
      rw [hν n (by simp [freeNames])]
      exact .var n hv'
  | pvar x hp =>
      intro ν' μ' _ hμ
      have hp' : C.parOK x (μ' x) := by
        rw [← hμ x (by simp [freeParams])]
        exact hp
      rw [hμ x (by simp [freeParams])]
      exact .pvar x hp'
  | quote hq => intro _ _ _ _; exact .quote hq
  | ctx ho hks hc => intro _ _ _ _; exact .ctx ho hks hc
  | pquote _ hp hok ih =>
      intro ν' μ' hν hμ
      simp only [freeNames, freeParams] at hν hμ
      exact .pquote (ih hν hμ) hp hok
  | app _ _ ihf iha =>
      intro ν' μ' hν hμ
      simp only [freeNames, freeParams, List.mem_append] at hν hμ
      exact .app (ihf (fun n h => hν n (Or.inl h)) (fun x h => hμ x (Or.inl h)))
        (iha (fun n h => hν n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | letP hk _ _ _ ihp ihw ihb =>
      intro ν' μ' hν hμ
      simp only [freeNames, freeParams, List.mem_append] at hν hμ
      exact .letP hk (ihp (fun n h => hν n (Or.inl (Or.inl h))) (fun x h => hμ x (Or.inl (Or.inl h))))
        (ihw (fun n h => hν n (Or.inl (Or.inr h))) (fun x h => hμ x (Or.inl (Or.inr h))))
        (ihb (fun n h => hν n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | alt hk _ _ ih₁ ih₂ =>
      intro ν' μ' hν hμ
      simp only [freeNames, freeParams, List.mem_append] at hν hμ
      exact .alt hk (ih₁ (fun n h => hν n (Or.inl h)) (fun x h => hμ x (Or.inl h)))
        (ih₂ (fun n h => hν n (Or.inr h)) (fun x h => hμ x (Or.inr h)))
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ _ hown hres hinj hdisj hnd hpar
      hbare hseen ihb =>
      intro ν' μ' hν hμ
      have hνbb : ∀ n ∈ freeNames b₁,
          νb n = if ownKey own₁ n = true then νb n else ν' n := by
        intro n hn
        by_cases ho : ownKey own₁ n = true
        · simp [ho]
        · have ho' : ownKey own₁ n = false := by simpa using ho
          simp only [ho]
          rw [hνb n ho']
          exact hν n (mem_freeNames_lam.2 ⟨hn, ho'⟩)
      have hμbb : ∀ x ∈ freeParams b₁,
          μb x = if x = x₁ then x₂ else μ' x := by
        intro x hx
        by_cases hxx : x = x₁
        · simp [hxx, hμx]
        · simp only [hxx, if_false]
          rw [hμb x hxx]
          exact hμ x (mem_freeParams_lam.2 ⟨hx, hxx⟩)
      refine .lam (νb := fun m => if ownKey own₁ m = true then νb m else ν' m)
        (μb := fun y => if y = x₁ then x₂ else μ' y) ?_ ?_ (by simp) hr₁ hr₂
        (ihb hνbb hμbb) ?_ hres ?_ ?_ hnd ?_ hbare hseen
      · intro n hn
        simp [hn]
      · intro x hx
        simp [hx]
      · intro n hn
        rw [← hνbb n hn]
        exact hown n hn
      · intro n hn n' hn' ho ho' he
        rw [← hνbb n hn, ← hνbb n' hn'] at he
        exact hinj n hn n' hn' ho ho' he
      · intro n hn ho
        rw [← hνbb n hn]
        exact hdisj n hn ho
      · intro x hx hne
        rw [← hμ x (mem_freeParams_lam.2 ⟨hx, hne⟩)]
        exact hpar x hx hne
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb _ _ _ hk hνi hr hℓp hℓb _ _ _ hlive hinj
      ihw ihp ihb =>
      intro ν' μ' hν hμ
      have hνii : ∀ n ∈ freeNames p₁ ++ freeNames b₁,
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          exact hν n (mem_freeNames_letAct.2 (Or.inl ⟨List.mem_append.1 hn, ho'⟩))
      have hμp : ∀ x ∈ freeParams p₁, μ x = μ' x := fun x hx =>
        hμ x (mem_freeParams_letAct.2 (Or.inl ⟨Or.inl hx, fun e => hℓp (e ▸ hx)⟩))
      have hμb' : ∀ x ∈ freeParams b₁, μ x = μ' x := fun x hx =>
        hμ x (mem_freeParams_letAct.2 (Or.inl ⟨Or.inr hx, fun e => hℓb (e ▸ hx)⟩))
      refine .letAct (νi := fun m => if ownKey own m = true then νi m else ν' m) hk ?_ hr hℓp hℓb
        (ihw (fun n h => hν n (mem_freeNames_letAct.2 (Or.inr h)))
          (fun x h => hμ x (mem_freeParams_letAct.2 (Or.inr h))))
        (ihp (fun n h => hνii n (List.mem_append_left _ h)) hμp)
        (ihb (fun n h => hνii n (List.mem_append_right _ h)) hμb') ?_ ?_
      · intro n hn
        simp [hn]
      · intro n hn ho
        rw [← hνii n hn]
        exact hlive n hn ho
      · intro n hn n' hn' ho ho' he
        rw [← hνii n hn, ← hνii n' hn'] at he
        exact hinj n hn n' hn' ho ho' he
  | @newAct ν μ ℓ own b₁ b₂ νi Rh Rb _ hνi hr hℓ _ hlive hinj ihb =>
      intro ν' μ' hν hμ
      have hνii : ∀ n ∈ freeNames b₁,
          νi n = if ownKey own n = true then νi n else ν' n := by
        intro n hn
        by_cases ho : ownKey own n = true
        · simp [ho]
        · have ho' : ownKey own n = false := by simpa using ho
          simp only [ho]
          rw [hνi n ho']
          exact hν n (mem_freeNames_newAct.2 ⟨hn, ho'⟩)
      refine .newAct (νi := fun m => if ownKey own m = true then νi m else ν' m) ?_ hr hℓ
        (ihb hνii (fun x hx => hμ x (mem_freeParams_newAct.2 ⟨hx, fun e => hℓ (e ▸ hx)⟩))) ?_ ?_
      · intro n hn
        simp [hn]
      · intro n hn ho
        rw [← hνii n hn]
        exact hlive n hn ho
      · intro n hn n' hn' ho ho' he
        rw [← hνii n hn, ← hνii n' hn'] at he
        exact hinj n hn n' hn' ho ho' he


/-! ## Where free names of a substituted term come from -/

section Track

variable {Y : Type v} [DecidableEq Y]

/-- A free name of a substituted term is a kept free name, or a free name of
what replaced a free name or a free parameter. -/
theorem mem_freeNames_subst' (t : Tm S Y) (θ φ : Sub S Y) (m : Nm Y)
    (hm : m ∈ freeNames (subst θ φ t)) :
    (m ∈ freeNames t ∧ θ m = none) ∨ (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ m ∈ freeNames w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ m ∈ freeNames w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ' (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hm
  rcases mem_freeNames_subst t θ' φ' m hm with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [θ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

/-- The same for free parameters. -/
theorem mem_freeParams_subst' (t : Tm S Y) (θ φ : Sub S Y) (q : Nm Y)
    (hq : q ∈ freeParams (subst θ φ t)) :
    (q ∈ freeParams t ∧ φ q = none) ∨ (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ q ∈ freeParams w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ q ∈ freeParams w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ' (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hq
  rcases mem_freeParams_subst t θ' φ' q hq with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [φ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

end Track

/-! ## Inversion -/

theorem Rel.var_left {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {n : Nm X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok (.var n) t₂) : t₂ = .var (ν n) := by
  cases h
  rfl

theorem Rel.pvar_left {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {x : Nm X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok (.pvar x) t₂) : t₂ = .pvar (μ x) := by
  cases h
  rfl

/-! ## Substitution -/

/-- **Related substitutions** on a term: each free name or parameter is kept,
or replaced, by related values; reserved names are renamed along `rn`,
injectively; whatever is inserted has free names that may occur free and no
free parameter. -/
structure SubOK (C : Setting S X₁ X₂) (ν μ : Nm X₁ → Nm X₂) (Res : List (Nm X₂))
    (t₁ : Tm S X₁) (θ₁ φ₁ : Sub S X₁) (θ₂ φ₂ : Sub S X₂) (ν' μ' : Nm X₁ → Nm X₂)
    (rn : Nm X₂ → Nm X₂) : Prop where
  names : ∀ n ∈ freeNames t₁,
    Rel C ν' μ' .val [] true ((θ₁ n).getD (.var n)) ((θ₂ (ν n)).getD (.var (ν n)))
  params : ∀ x ∈ freeParams t₁,
    Rel C ν' μ' .val [] true ((φ₁ x).getD (.pvar x)) ((φ₂ (μ x)).getD (.pvar (μ x)))
  res : ∀ m ∈ Res, (θ₂ m).getD (.var m) = .var (rn m)
  resInj : ∀ m ∈ Res, ∀ m' ∈ Res, rn m = rn m' → m = m'
  /-- `rn` keeps hole comparisons. -/
  rnPres : ∀ m, C.preserve m (rn m)
  cap₁ : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w →
    (∀ m ∈ freeNames w, OK₁ C m) ∧ freeParams w = []
  capφ₁ : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w →
    (∀ m ∈ freeNames w, OK₁ C m) ∧ freeParams w = []
  cap₂ : ∀ n ∈ freeNames t₁, ∀ w, θ₂ (ν n) = some w →
    (∀ m ∈ freeNames w, OK₂ C m) ∧ freeParams w = []
  capφ₂ : ∀ x ∈ freeParams t₁, ∀ w, φ₂ (μ x) = some w →
    (∀ m ∈ freeNames w, OK₂ C m) ∧ freeParams w = []
  capR : ∀ m ∈ Res, ∀ w, θ₂ m = some w → (∀ m' ∈ freeNames w, OK₂ C m') ∧ freeParams w = []

theorem SubOK.restrict {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {Res' : List (Nm X₂)} {u : Tm S X₁}
    (hn : ∀ n ∈ freeNames u, n ∈ freeNames t₁) (hx : ∀ x ∈ freeParams u, x ∈ freeParams t₁)
    (hR : ∀ m ∈ Res', m ∈ Res) : SubOK C ν μ Res' u θ₁ φ₁ θ₂ φ₂ ν' μ' rn where
  names n h' := h.names n (hn n h')
  params x h' := h.params x (hx x h')
  res m h' := h.res m (hR m h')
  resInj m h' m' h'' := h.resInj m (hR m h') m' (hR m' h'')
  rnPres := h.rnPres
  cap₁ n h' := h.cap₁ n (hn n h')
  capφ₁ x h' := h.capφ₁ x (hx x h')
  cap₂ n h' := h.cap₂ n (hn n h')
  capφ₂ x h' := h.capφ₂ x (hx x h')
  capR m h' := h.capR m (hR m h')

/-- The replacement of a free name, if any, carries only names that may occur
free; the name itself is kept otherwise. -/
theorem SubOK.replacement_names {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    {m : Nm X₁} (hm : m ∈ freeNames ((θ₁ n).getD (.var n))) :
    (θ₁ n = none ∧ m = n) ∨ OK₁ C m := by
  cases hθ : θ₁ n with
  | none =>
      rw [hθ] at hm
      simp only [Option.getD_none, freeNames, List.mem_singleton] at hm
      exact Or.inl ⟨rfl, hm⟩
  | some w =>
      rw [hθ] at hm
      exact Or.inr ((h.cap₁ n hn w hθ).1 m hm)

theorem SubOK.replacement_params {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁) :
    freeParams ((θ₁ n).getD (.var n)) = [] := by
  cases hθ : θ₁ n with
  | none => rfl
  | some w => exact (h.cap₁ n hn w hθ).2

theorem SubOK.param_names {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {m : Nm X₁} (hm : m ∈ freeNames ((φ₁ x).getD (.pvar x))) : OK₁ C m := by
  cases hφ : φ₁ x with
  | none =>
      rw [hφ] at hm
      simp [freeNames] at hm
  | some w =>
      rw [hφ] at hm
      exact (h.capφ₁ x hx w hφ).1 m hm

theorem SubOK.param_params {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {y : Nm X₁} (hy : y ∈ freeParams ((φ₁ x).getD (.pvar x))) : φ₁ x = none ∧ y = x := by
  cases hφ : φ₁ x with
  | none =>
      rw [hφ] at hy
      simp only [Option.getD_none, freeParams, List.mem_singleton] at hy
      exact ⟨rfl, hy⟩
  | some w =>
      rw [hφ, Option.getD_some, (h.capφ₁ x hx w hφ).2] at hy
      cases hy

/-- The identity image of a name the first side keeps is one the second side
may not capture, unless it is the kept image itself. -/
theorem SubOK.kept_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    (hθ : θ₁ n = none) : (θ₂ (ν n) = none ∧ ν' n = ν n) ∨ OK₂ C (ν' n) := by
  have hr := h.names n hn
  rw [hθ, Option.getD_none] at hr
  have e := hr.var_left
  cases h2 : θ₂ (ν n) with
  | none =>
      rw [h2, Option.getD_none] at e
      exact Or.inl ⟨rfl, (Tm.var.inj e).symm⟩
  | some w =>
      rw [h2, Option.getD_some] at e
      subst e
      exact Or.inr ((h.cap₂ n hn _ h2).1 (ν' n) (by simp [freeNames]))

/-- A free name inserted by the first side has an image the second side may
not capture: it comes from the second side's replacement, or is the kept
image of the replaced name. -/
theorem SubOK.inserted_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {n : Nm X₁} (hn : n ∈ freeNames t₁)
    {w : Tm S X₁} (hθ : θ₁ n = some w) {m : Nm X₁} (hm : m ∈ freeNames w) :
    OK₂ C (ν' m) ∨ (θ₂ (ν n) = none ∧ ν' m = ν n) := by
  have hr := h.names n hn
  rw [hθ, Option.getD_some] at hr
  have hm' := hr.mem_freeNames hm
  cases h2 : θ₂ (ν n) with
  | none =>
      rw [h2, Option.getD_none] at hm'
      simp only [freeNames, List.mem_singleton] at hm'
      exact Or.inr ⟨rfl, hm'⟩
  | some w₂ =>
      rw [h2, Option.getD_some] at hm'
      exact Or.inl ((h.cap₂ n hn w₂ h2).1 _ hm')

/-- The same for a free name inserted for a parameter. -/
theorem SubOK.inserted_param_image {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {t₁ : Tm S X₁}
    {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂}
    (h : SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn) {x : Nm X₁} (hx : x ∈ freeParams t₁)
    {w : Tm S X₁} (hφ : φ₁ x = some w) {m : Nm X₁} (hm : m ∈ freeNames w) : OK₂ C (ν' m) := by
  have hr := h.params x hx
  rw [hφ, Option.getD_some] at hr
  have hm' := hr.mem_freeNames hm
  cases h2 : φ₂ (μ x) with
  | none =>
      rw [h2, Option.getD_none] at hm'
      simp [freeNames] at hm'
  | some w₂ =>
      rw [h2, Option.getD_some] at hm'
      exact (h.capφ₂ x hx w₂ h2).1 _ hm'


/-! ## Holes, parameters, and weak shape -/

/-- A free store name and its image are related by `varHole`. -/
theorem Rel.varHole_free {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {n}, n ∈ freeNames t₁ → C.varHole n (ν n) := by
  induction h with
  | sym _ => intro n hn; simp [freeNames] at hn
  | fn _ => intro n hn; simp [freeNames] at hn
  | var m hv =>
      intro n hn
      simp only [freeNames, List.mem_singleton] at hn
      subst hn
      exact hv
  | pvar _ _ => intro n hn; simp [freeNames] at hn
  | quote _ => intro n hn; simp [freeNames] at hn
  | ctx _ _ _ => intro n hn; simp [freeNames] at hn
  | pquote _ _ _ ih =>
      intro n hn
      simp only [freeNames] at hn
      exact ih hn
  | app _ _ ihf iha =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      exact hn.elim ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact ihp hn
      · exact ihw hn
      · exact ihb hn
  | alt _ _ _ ih₁ ih₂ =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn
      exact hn.elim ih₁ ih₂
  | lam hνb _ _ _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro n hn
      rw [mem_freeNames_lam] at hn
      obtain ⟨hn, hk⟩ := hn
      exact hνb n hk ▸ ihb hn
  | letAct _ hνi _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.not_mem_nil, or_false] at hn
      rcases hn with ⟨hn | hn, hk⟩ | hn
      · exact hνi n hk ▸ ihp hn
      · exact hνi n hk ▸ ihb hn
      · exact ihw hn
  | newAct hνi _ _ _ _ _ ihb =>
      intro n hn
      simp only [freeNames, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.not_mem_nil] at hn
      rcases hn with ⟨hn, hk⟩ | ⟨hf, _⟩
      · exact hνi n hk ▸ ihb hn
      · exact hf.elim

/-- A free parameter and its image are related by `parOK`. -/
theorem Rel.parOK_free {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → C.parOK x (μ x) := by
  induction h with
  | sym _ => intro x hx; simp [freeParams] at hx
  | fn _ => intro x hx; simp [freeParams] at hx
  | var _ _ => intro x hx; simp [freeParams] at hx
  | pvar y hp =>
      intro x hx
      simp only [freeParams, List.mem_singleton] at hx
      subst hx
      exact hp
  | quote _ => intro x hx; simp [freeParams] at hx
  | ctx _ _ _ => intro x hx; simp [freeParams] at hx
  | pquote _ _ _ ih =>
      intro x hx
      simp only [freeParams] at hx
      exact ih hx
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ihf iha
  | letP _ _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact ihp hx
      · exact ihw hx
      · exact ihb hx
  | alt _ _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ih₁ ih₂
  | lam _ hμb _ _ _ _ _ _ _ _ _ _ _ _ ihb =>
      intro x hx
      rw [mem_freeParams_lam] at hx
      obtain ⟨hx, hne⟩ := hx
      exact hμb x hne ▸ ihb hx
  | letAct _ _ _ _ _ _ _ _ _ _ ihw ihp ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨(hx | hx) | hx, hne⟩ | hx
      · exact ihp hx
      · exact absurd hx hne
      · exact ihb hx
      · exact ihw hx
  | newAct _ _ _ _ _ _ ihb =>
      intro x hx
      simp only [freeParams, List.mem_append, List.mem_filter, decide_eq_true_eq,
        List.mem_singleton] at hx
      rcases hx with ⟨hx, _⟩ | ⟨hx, hne⟩
      · exact ihb hx
      · exact absurd hx hne

/-- A value carries no pending activation. -/
theorem Rel.val_ok {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ .val Res ok t₁ t₂) : ok = true := by
  generalize hk : Kd.val = k at h
  induction h with
  | sym _ => rfl
  | fn _ => rfl
  | var _ _ => rfl
  | pvar _ _ => rfl
  | quote _ => rfl
  | ctx _ _ _ => rfl
  | pquote _ _ _ => rfl
  | app _ _ ihf iha =>
      rw [ihf hk, iha hk]
      rfl
  | letP hk' => exact absurd hk.symm hk'
  | alt hk' => exact absurd hk.symm hk'
  | lam => rfl
  | letAct hk' => exact absurd hk.symm hk'
  | newAct => cases hk

/-- Stable related terms have the same weak shape. -/
theorem Rel.shape_of {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ok = true → ShapeParallel C t₁ t₂ := by
  induction h with
  | sym _ => intro _; rfl
  | fn _ => intro _; rfl
  | var _ hv => intro _; exact hv
  | pvar _ hp => intro _; exact hp
  | quote hq => intro _; exact hq
  | ctx _ hks hc => intro _; exact ⟨hks, hc⟩
  | pquote _ hp _ => intro _; exact hp
  | app _ _ ihf iha =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      exact ⟨ihf hok.1, iha hok.2⟩
  | letP _ _ _ _ ihp ihw ihb =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨hop, how⟩, hob⟩ := hok
      exact ⟨ihp hop, ihw how, ihb hob⟩
  | alt _ _ _ ih₁ ih₂ =>
      intro hok
      simp only [Bool.and_eq_true] at hok
      exact ⟨ih₁ hok.1, ih₂ hok.2⟩
  | lam _ _ _ _ _ _ _ _ _ _ _ _ hbare _ =>
      intro _
      exact hbare
  | letAct =>
      intro hok
      cases hok
  | newAct =>
      intro hok
      cases hok

/-- A related value has the weak shape of its two terms. -/
theorem Rel.shape_of_val {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ .val Res true t₁ t₂) :
    ShapeParallel C t₁ t₂ :=
  h.shape_of rfl

/-- Weak shape survives substitution. A pending activation is not stable, so it
is excluded; a lambda contributes its binders only. -/
theorem Rel.shape_preserved {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂},
      SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn → ok = true →
        ShapeParallel C (subst θ₁ φ₁ t₁) (subst θ₂ φ₂ t₂) := by
  induction h with
  | sym _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
  | fn _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
  | var n _ =>
      intro _ _ _ _ _ _ _ hS _
      simpa [subst] using (hS.names n (by simp [freeNames])).shape_of_val
  | pvar x _ =>
      intro _ _ _ _ _ _ _ hS _
      simpa [subst] using (hS.params x (by simp [freeParams])).shape_of_val
  | quote hq =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
      exact hq
  | ctx _ hks hc =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
      exact ⟨hks, hc⟩
  | pquote _ _ hbok ih =>
      intro _ _ _ _ _ _ _ hS _
      simp only [subst, ShapeParallel]
      exact ih (hS.restrict (fun n h => by simp [freeNames, h])
        (fun x h => by simp [freeParams, h]) (fun _ h => by cases h)) hbok
  | app _ _ ihf iha =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      simp only [subst, ShapeParallel]
      exact ⟨ihf (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_left _ h)) hok.1,
          iha (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_right _ h)) hok.2⟩
  | letP _ _ _ _ ihp ihw ihb =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨hop, how⟩, hob⟩ := hok
      simp only [subst, ShapeParallel]
      exact ⟨ihp (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h])) hop,
          ihw (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h])) how,
          ihb (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h]) (fun m h => by simp [h])) hob⟩
  | alt _ _ _ ih₁ ih₂ =>
      intro _ _ _ _ _ _ _ hS hok
      simp only [Bool.and_eq_true] at hok
      simp only [subst, ShapeParallel]
      exact ⟨ih₁ (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_left _ h)) hok.1,
          ih₂ (hS.restrict (fun n h => by simp [freeNames, h])
            (fun x h => by simp [freeParams, h])
            (fun m h => List.mem_append_right _ h)) hok.2⟩
  | lam _ _ _ _ _ _ _ _ _ _ _ _ hbare _ =>
      intro _ _ _ _ _ _ _ _ _
      simp only [subst, ShapeParallel]
      exact hbare
  | letAct =>
      intro _ _ _ _ _ _ _ _ hok
      cases hok
  | newAct =>
      intro _ _ _ _ _ _ _ _ hok
      cases hok

/-- **Substitution preserves the relation.**  Renaming slots on one side or on
both, instantiating parameters, substituting values for store names and
applying a store are instances. The stability bit is unchanged: a replacement
is a value, and a value is stable. -/
theorem Rel.substitute {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : Rel C ν μ k Res ok t₁ t₂) :
    ∀ {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {ν' μ' : Nm X₁ → Nm X₂} {rn : Nm X₂ → Nm X₂},
      SubOK C ν μ Res t₁ θ₁ φ₁ θ₂ φ₂ ν' μ' rn →
      Rel C ν' μ' k (Res.map rn) ok (subst θ₁ φ₁ t₁) (subst θ₂ φ₂ t₂) := by
  induction h with
  | sym s => intro _ _ _ _ _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _ _ _ _ _; exact .fn F
  | var n _ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      exact (hS.names n (by simp [freeNames])).of_val _
  | pvar x _ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      exact (hS.params x (by simp [freeParams])).of_val _
  | quote hq => intro _ _ _ _ _ _ _ _; exact .quote hq
  | ctx ho hks hc => intro _ _ _ _ _ _ _ _; exact .ctx ho hks hc
  | pquote hb _ hok ih =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      simp only [subst, List.map_nil]
      exact .pquote
        (ih (hS.restrict (fun n h => by simp [freeNames, h])
          (fun x h => by simp [freeParams, h]) (fun _ hm => hm)))
        (hb.shape_preserved (hS.restrict (fun n h => by simp [freeNames, h])
          (fun x h => by simp [freeParams, h]) (fun _ hm => hm)) hok)
        hok
  | app _ _ ihf iha =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append]
      exact .app
        (ihf (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_left _ h)))
        (iha (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_right _ h)))
  | letP hk _ _ _ ihp ihw ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append, List.map_append]
      exact .letP hk
        (ihp (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h])))
        (ihw (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h])))
        (ihb (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => by simp [h])))
  | alt hk _ _ ih₁ ih₂ =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      rw [List.map_append]
      exact .alt hk
        (ih₁ (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_left _ h)))
        (ih₂ (hS.restrict (fun n h => by simp [freeNames, h]) (fun x h => by simp [freeParams, h])
          (fun m h => List.mem_append_right _ h)))
  | @lam ν μ k x₁ own₁ b₁ x₂ own₂ b₂ νb μb Rb _ hνb hμb hμx hr₁ hr₂ hb hown hres hinj hdisj hnd hpar
      hbare hseen ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      simp only [subst, List.map_nil]
      let νb' : Nm X₁ → Nm X₂ := fun m => if ownKey own₁ m = true then νb m else ν' m
      let μb' : Nm X₁ → Nm X₂ := fun y => if y = x₁ then x₂ else μ' y
      have hνb'o : ∀ m, ownKey own₁ m = true → νb' m = νb m := fun m h => by simp [νb', h]
      have hνb'n : ∀ m, ownKey own₁ m = false → νb' m = ν' m := fun m h => by simp [νb', h]
      have hμb'x : μb' x₁ = x₂ := by simp [μb']
      have hμb'n : ∀ y, y ≠ x₁ → μb' y = μ' y := fun y h => by simp [μb', h]
      have hfv : ∀ n, n ∈ freeNames b₁ → ownKey own₁ n = false →
          n ∈ freeNames (.lam x₁ own₁ b₁ : Tm S X₁) := fun n hn ho => mem_freeNames_lam.2 ⟨hn, ho⟩
      have hfp : ∀ x, x ∈ freeParams b₁ → x ≠ x₁ →
          x ∈ freeParams (.lam x₁ own₁ b₁ : Tm S X₁) := fun x hx hne => mem_freeParams_lam.2 ⟨hx, hne⟩
      have hcongN : ∀ n ∈ freeNames b₁, ∀ (ho : ownKey own₁ n = false),
          Rel C νb' μb' .val [] true ((θ₁ n).getD (.var n)) ((θ₂ (ν n)).getD (.var (ν n))) := by
        intro n hn ho
        refine (hS.names n (hfv n hn ho)).congr ?_ ?_
        · intro m hm
          rcases hS.replacement_names (hfv n hn ho) hm with ⟨_, rfl⟩ | hok
          · exact (hνb'n m ho).symm
          · exact (hνb'n m (ownKey_of_OK₁ hr₁ hok)).symm
        · intro y hy
          rw [hS.replacement_params (hfv n hn ho)] at hy
          cases hy
      have hcongP : ∀ x ∈ freeParams b₁, ∀ (hne : x ≠ x₁),
          Rel C νb' μb' .val [] true ((φ₁ x).getD (.pvar x)) ((φ₂ (μ x)).getD (.pvar (μ x))) := by
        intro x hx hne
        refine (hS.params x (hfp x hx hne)).congr ?_ ?_
        · intro m hm
          exact (hνb'n m (ownKey_of_OK₁ hr₁ (hS.param_names (hfp x hx hne) hm))).symm
        · intro y hy
          obtain ⟨-, rfl⟩ := hS.param_params (hfp x hx hne) hy
          exact (hμb'n y hne).symm
      have hSb : SubOK C νb μb Rb b₁ (θ₁.hideOwn own₁) (φ₁.hideParam x₁) (θ₂.hideOwn own₂)
          (φ₂.hideParam x₂) νb' μb' id := {
        names := by
          intro n hn
          by_cases ho : ownKey own₁ n = true
          · have h2 : ownKey own₂ (νb n) = true := by rw [hown n hn]; exact ho
            simp only [Sub.hideOwn, ho, h2, if_true, Option.getD_none]
            rw [← hνb'o n ho]
            exact .var n ((hνb'o n ho).symm ▸ hb.varHole_free hn)
          · have ho' : ownKey own₁ n = false := by simpa using ho
            have h2 : ownKey own₂ (νb n) = false := by rw [hown n hn]; exact ho'
            simp only [Sub.hideOwn, ho', h2, Bool.false_eq_true, if_false]
            rw [hνb n ho']
            exact hcongN n hn ho'
        params := by
          intro x hx
          by_cases hxx : x = x₁
          · have hp₁ : C.parOK x (μb x) := hb.parOK_free hx
            rw [hxx, hμx]
            simp only [Sub.hideParam, if_true, Option.getD_none]
            rw [← hμb'x]
            exact .pvar x₁ ((hμb'x).symm ▸ (hμx.symm ▸ (hxx ▸ hp₁)))
          · have hne2 : μ x ≠ x₂ := hpar x hx hxx
            simp only [Sub.hideParam, hxx, if_false, hμb x hxx, hne2]
            exact hcongP x hx hxx
        res := by
          intro m hm
          simp [Sub.hideOwn, hres m hm]
        resInj := fun _ _ _ _ h => h
        rnPres := C.preserve_refl
        cap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own₁ n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own₁ n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.cap₁ n (hfv n hn ho') w hw
        capφ₁ := by
          intro x hx w hw
          by_cases hxx : x = x₁
          · rw [hxx] at hw
            simp [Sub.hideParam] at hw
          · simp only [Sub.hideParam, hxx, if_false] at hw
            exact hS.capφ₁ x (hfp x hx hxx) w hw
        cap₂ := by
          intro n hn w hw
          by_cases ho : ownKey own₁ n = true
          · have h2 : ownKey own₂ (νb n) = true := by rw [hown n hn]; exact ho
            simp [Sub.hideOwn, h2] at hw
          · have ho' : ownKey own₁ n = false := by simpa using ho
            have h2 : ownKey own₂ (νb n) = false := by rw [hown n hn]; exact ho'
            simp only [Sub.hideOwn, h2, Bool.false_eq_true, if_false] at hw
            rw [hνb n ho'] at hw
            exact hS.cap₂ n (hfv n hn ho') w hw
        capφ₂ := by
          intro x hx w hw
          by_cases hxx : x = x₁
          · rw [hxx, hμx] at hw
            simp [Sub.hideParam] at hw
          · have hne2 : μ x ≠ x₂ := hpar x hx hxx
            simp only [Sub.hideParam, hμb x hxx, hne2, if_false] at hw
            exact hS.capφ₂ x (hfp x hx hxx) w hw
        capR := by
          intro m hm w hw
          simp [Sub.hideOwn, hres m hm] at hw }
      have IH := ihb hSb
      rw [List.map_id] at IH
      have hownFV : ∀ n ∈ freeNames (subst (θ₁.hideOwn own₁) (φ₁.hideParam x₁) b₁),
          ownKey own₁ n = true → n ∈ freeNames b₁ := by
        intro n hn ho
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr₁ ((hSb.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr₁ ((hSb.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      refine .lam (νb := νb') (μb := μb') hνb'n hμb'n hμb'x hr₁ hr₂ IH ?_ hres ?_ ?_ hnd ?_
        hbare hseen
      · intro n hn
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, h2⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · by_cases ho : ownKey own₁ n = true
          · rw [hνb'o n ho, hown n h1]
          · have ho' : ownKey own₁ n = false := by simpa using ho
            rw [hνb'n n ho', ho']
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at h2
            rcases hS.kept_image (hfv n h1 ho') h2 with ⟨_, e⟩ | hok
            · rw [e, ← hνb n ho', hown n h1, ho']
            · exact ownKey_of_OK₂ hr₂ hok
        · have ho₀ : ownKey own₁ n₀ = false := by
            cases hk₀ : ownKey own₁ n₀
            · rfl
            · simp [Sub.hideOwn, hk₀] at hw
          simp only [Sub.hideOwn, ho₀, Bool.false_eq_true, if_false] at hw
          have ho : ownKey own₁ n = false :=
            ownKey_of_OK₁ hr₁ ((hS.cap₁ n₀ (hfv n₀ hn₀ ho₀) w hw).1 n hm)
          rw [hνb'n n ho, ho]
          rcases hS.inserted_image (hfv n₀ hn₀ ho₀) hw hm with hok | ⟨_, e⟩
          · exact ownKey_of_OK₂ hr₂ hok
          · rw [e, ← hνb n₀ ho₀, hown n₀ hn₀, ho₀]
        · have hyx : y ≠ x₁ := by
            rintro rfl
            simp [Sub.hideParam] at hw
          simp only [Sub.hideParam, hyx, if_false] at hw
          have ho : ownKey own₁ n = false :=
            ownKey_of_OK₁ hr₁ ((hS.capφ₁ y (hfp y hy hyx) w hw).1 n hm)
          rw [hνb'n n ho, ho]
          exact ownKey_of_OK₂ hr₂ (hS.inserted_param_image (hfp y hy hyx) hw hm)
      · intro n hn n' hn' ho ho' he
        rw [hνb'o n ho, hνb'o n' ho'] at he
        exact hinj n (hownFV n hn ho) n' (hownFV n' hn' ho') ho ho' he
      · intro n hn ho
        rw [hνb'o n ho]
        exact hdisj n (hownFV n hn ho) ho
      · intro x hx hne
        rcases mem_freeParams_subst' b₁ _ _ x hx with ⟨h1, h2⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · simp only [Sub.hideParam, hne, if_false] at h2
          have hr := hS.params x (hfp x h1 hne)
          rw [h2, Option.getD_none] at hr
          have e := hr.pvar_left
          cases h3 : φ₂ (μ x) with
          | none =>
              rw [h3, Option.getD_none] at e
              rw [← Tm.pvar.inj e]
              exact hpar x h1 hne
          | some w₂ =>
              rw [h3, Option.getD_some] at e
              have hc := (hS.capφ₂ x (hfp x h1 hne) w₂ h3).2
              rw [e] at hc
              simp [freeParams] at hc
        · rw [(hSb.cap₁ n₀ hn₀ w hw).2] at hm
          cases hm
        · rw [(hSb.capφ₁ y hy w hw).2] at hm
          cases hm
  | @letAct ν μ k ℓ own p₁ w₁ b₁ p₂ w₂ b₂ νi Rh Rw Rp Rb _ _ _ hk hνi hr hℓp hℓb _ hp hb hlive hinj
      ihw ihp ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      have e₁ : (subst θ₁ φ₁ (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁) : Tm S X₁) =
          .app (.lam ℓ own (.letP (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) p₁) (.pvar ℓ)
            (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁))) (subst θ₁ φ₁ w₁) := by
        simp [subst, Sub.hideParam]
      rw [e₁]
      simp only [subst]
      rw [List.map_append, List.map_append, List.map_append]
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then rn (νi m) else ν' m
      have hνi'o : ∀ m, ownKey own m = true → νi' m = rn (νi m) := fun m h => by simp [νi', h]
      have hνi'n : ∀ m, ownKey own m = false → νi' m = ν' m := fun m h => by simp [νi', h]
      have hRes : ∀ m, m ∈ Rh ∨ m ∈ Rp ∨ m ∈ Rb → m ∈ Rh ++ Rw ++ Rp ++ Rb := by
        intro m hm
        simp only [List.mem_append]
        rcases hm with hm | hm | hm
        · exact Or.inl (Or.inl (Or.inl hm))
        · exact Or.inl (Or.inr hm)
        · exact Or.inr hm
      have hfv : ∀ n, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁ → ownKey own n = false →
          n ∈ freeNames (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) :=
        fun n hn ho => mem_freeNames_letAct.2 (Or.inl ⟨hn, ho⟩)
      have hfp : ∀ x, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁ →
          x ∈ freeParams (.app (.lam ℓ own (.letP p₁ (.pvar ℓ) b₁)) w₁ : Tm S X₁) := by
        intro x hx
        refine mem_freeParams_letAct.2 (Or.inl ⟨hx, ?_⟩)
        rintro rfl
        rcases hx with hx | hx
        · exact hℓp hx
        · exact hℓb hx
      have hxℓ : ∀ x, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁ → x ≠ ℓ := by
        rintro x hx rfl
        rcases hx with hx | hx
        · exact hℓp hx
        · exact hℓb hx
      have hSi : ∀ (u : Tm S X₁) (Ru : List (Nm X₂)),
          (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          SubOK C νi μ Ru u (θ₁.hideOwn own) (φ₁.hideParam ℓ) θ₂ φ₂ νi' μ' rn := by
        intro u Ru hun hux huR
        exact {
          names := by
            intro n hn
            have hn' := hun n hn
            by_cases ho : ownKey own n = true
            · have hl : νi n ∈ Rh := hlive n (List.mem_append.2 hn') ho
              have hv : C.varHole n (νi n) := by
                rcases hn' with h | h
                · exact hp.varHole_free h
                · exact hb.varHole_free h
              have hv' : C.varHole n (rn (νi n)) := C.varHole_rename hv (hS.rnPres (νi n))
              simp only [Sub.hideOwn, ho, if_true, Option.getD_none]
              rw [hS.res (νi n) (hRes _ (Or.inl hl)), ← hνi'o n ho]
              exact .var n ((hνi'o n ho).symm ▸ hv')
            · have ho' : ownKey own n = false := by simpa using ho
              simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false]
              rw [hνi n ho']
              refine (hS.names n (hfv n hn' ho')).congr ?_ (fun _ _ => rfl)
              intro m hm
              rcases hS.replacement_names (hfv n hn' ho') hm with ⟨_, rfl⟩ | hok
              · exact (hνi'n m ho').symm
              · exact (hνi'n m (ownKey_of_OK₁ hr hok)).symm
          params := by
            intro x hx
            have hx' := hux x hx
            simp only [Sub.hideParam, hxℓ x hx', if_false]
            refine (hS.params x (hfp x hx')).congr ?_ (fun _ _ => rfl)
            intro m hm
            exact (hνi'n m (ownKey_of_OK₁ hr (hS.param_names (hfp x hx') hm))).symm
          res := fun m hm => hS.res m (hRes m (Or.inr (huR m hm)))
          resInj := fun m hm m' hm' he =>
            hS.resInj m (hRes m (Or.inr (huR m hm))) m' (hRes m' (Or.inr (huR m' hm'))) he
          rnPres := hS.rnPres
          cap₁ := by
            intro n hn w hw
            by_cases ho : ownKey own n = true
            · simp [Sub.hideOwn, ho] at hw
            · have ho' : ownKey own n = false := by simpa using ho
              simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
              exact hS.cap₁ n (hfv n (hun n hn) ho') w hw
          capφ₁ := by
            intro x hx w hw
            simp only [Sub.hideParam, hxℓ x (hux x hx), if_false] at hw
            exact hS.capφ₁ x (hfp x (hux x hx)) w hw
          cap₂ := by
            intro n hn w hw
            by_cases ho : ownKey own n = true
            · exact hS.capR (νi n) (hRes _ (Or.inl (hlive n (List.mem_append.2 (hun n hn)) ho))) w hw
            · have ho' : ownKey own n = false := by simpa using ho
              rw [hνi n ho'] at hw
              exact hS.cap₂ n (hfv n (hun n hn) ho') w hw
          capφ₂ := fun x hx w hw => hS.capφ₂ x (hfp x (hux x hx)) w hw
          capR := fun m hm w hw => hS.capR m (hRes m (Or.inr (huR m hm))) w hw }
      have hSp := hSi p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h)
      have hSb := hSi b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h)
      have hownFV : ∀ u : Tm S X₁, ∀ Ru : List (Nm X₂), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          ∀ n ∈ freeNames (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) u), ownKey own n = true →
            n ∈ freeNames u := by
        intro u Ru hun hux huR n hn ho
        have hSu := hSi u Ru hun hux huR
        rcases mem_freeNames_subst' u _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr ((hSu.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr ((hSu.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      have hpFV := hownFV p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h)
      have hbFV := hownFV b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h)
      have hℓ' : ∀ u : Tm S X₁, ∀ Ru : List (Nm X₂), (∀ n ∈ freeNames u, n ∈ freeNames p₁ ∨ n ∈ freeNames b₁) →
          (∀ x ∈ freeParams u, x ∈ freeParams p₁ ∨ x ∈ freeParams b₁) →
          (∀ m ∈ Ru, m ∈ Rp ∨ m ∈ Rb) →
          ℓ ∉ freeParams (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) u) := by
        intro u Ru hun hux huR hm
        have hSu := hSi u Ru hun hux huR
        rcases mem_freeParams_subst' u _ _ ℓ hm with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm'⟩ |
            ⟨y, hy, w, hw, hm'⟩
        · exact hxℓ ℓ (hux ℓ h1) rfl
        · rw [(hSu.cap₁ n₀ hn₀ w hw).2] at hm'
          cases hm'
        · rw [(hSu.capφ₁ y hy w hw).2] at hm'
          cases hm'
      refine .letAct (νi := νi') (Rh := Rh.map rn) hk hνi'n hr
        (hℓ' p₁ Rp (fun n h => Or.inl h) (fun x h => Or.inl h) (fun m h => Or.inl h))
        (hℓ' b₁ Rb (fun n h => Or.inr h) (fun x h => Or.inr h) (fun m h => Or.inr h))
        (ihw (hS.restrict (fun n h => mem_freeNames_letAct.2 (Or.inr h))
          (fun x h => mem_freeParams_letAct.2 (Or.inr h)) (fun m h => by simp [h])))
        (ihp hSp) (ihb hSb) ?_ ?_
      · intro n hn ho
        have hn' : n ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn with h | h
          · exact List.mem_append_left _ (hpFV n h ho)
          · exact List.mem_append_right _ (hbFV n h ho)
        rw [hνi'o n ho]
        exact List.mem_map_of_mem (hlive n hn' ho)
      · intro n hn n' hn' ho ho' he
        have h1 : n ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn with h | h
          · exact List.mem_append_left _ (hpFV n h ho)
          · exact List.mem_append_right _ (hbFV n h ho)
        have h2 : n' ∈ freeNames p₁ ++ freeNames b₁ := by
          rcases List.mem_append.1 hn' with h | h
          · exact List.mem_append_left _ (hpFV n' h ho')
          · exact List.mem_append_right _ (hbFV n' h ho')
        rw [hνi'o n ho, hνi'o n' ho'] at he
        have l1 := hlive n h1 ho
        have l2 := hlive n' h2 ho'
        exact hinj n h1 n' h2 ho ho'
          (hS.resInj _ (hRes _ (Or.inl l1)) _ (hRes _ (Or.inl l2)) he)
  | @newAct ν μ ℓ own b₁ b₂ νi Rh Rb _ hνi hr hℓ hb hlive hinj ihb =>
      intro θ₁ φ₁ θ₂ φ₂ ν' μ' rn hS
      have e₁ : (subst θ₁ φ₁ (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ))) : Tm S X₁) =
          .app (.lam ℓ own (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁)) (.lam ℓ [] (.pvar ℓ)) := by
        simp [subst, Sub.hideParam]
      rw [e₁, List.map_append]
      let νi' : Nm X₁ → Nm X₂ := fun m => if ownKey own m = true then rn (νi m) else ν' m
      have hνi'o : ∀ m, ownKey own m = true → νi' m = rn (νi m) := fun m h => by simp [νi', h]
      have hνi'n : ∀ m, ownKey own m = false → νi' m = ν' m := fun m h => by simp [νi', h]
      have hfv : ∀ n, n ∈ freeNames b₁ → ownKey own n = false →
          n ∈ freeNames (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) :=
        fun n hn ho => mem_freeNames_newAct.2 ⟨hn, ho⟩
      have hxℓ : ∀ x, x ∈ freeParams b₁ → x ≠ ℓ := by
        rintro x hx rfl
        exact hℓ hx
      have hfp : ∀ x, x ∈ freeParams b₁ →
          x ∈ freeParams (.app (.lam ℓ own b₁) (.lam ℓ [] (.pvar ℓ)) : Tm S X₁) :=
        fun x hx => mem_freeParams_newAct.2 ⟨hx, hxℓ x hx⟩
      have hRes : ∀ m, m ∈ Rh ∨ m ∈ Rb → m ∈ Rh ++ Rb := fun m hm => List.mem_append.2 hm
      have hSb : SubOK C νi μ Rb b₁ (θ₁.hideOwn own) (φ₁.hideParam ℓ) θ₂ φ₂ νi' μ' rn := {
        names := by
          intro n hn
          by_cases ho : ownKey own n = true
          · have hl : νi n ∈ Rh := hlive n hn ho
            have hv' : C.varHole n (rn (νi n)) :=
              C.varHole_rename (hb.varHole_free hn) (hS.rnPres (νi n))
            simp only [Sub.hideOwn, ho, if_true, Option.getD_none]
            rw [hS.res (νi n) (hRes _ (Or.inl hl)), ← hνi'o n ho]
            exact .var n ((hνi'o n ho).symm ▸ hv')
          · have ho' : ownKey own n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false]
            rw [hνi n ho']
            refine (hS.names n (hfv n hn ho')).congr ?_ (fun _ _ => rfl)
            intro m hm
            rcases hS.replacement_names (hfv n hn ho') hm with ⟨_, rfl⟩ | hok
            · exact (hνi'n m ho').symm
            · exact (hνi'n m (ownKey_of_OK₁ hr hok)).symm
        params := by
          intro x hx
          simp only [Sub.hideParam, hxℓ x hx, if_false]
          refine (hS.params x (hfp x hx)).congr ?_ (fun _ _ => rfl)
          intro m hm
          exact (hνi'n m (ownKey_of_OK₁ hr (hS.param_names (hfp x hx) hm))).symm
        res := fun m hm => hS.res m (hRes m (Or.inr hm))
        resInj := fun m hm m' hm' he =>
          hS.resInj m (hRes m (Or.inr hm)) m' (hRes m' (Or.inr hm')) he
        rnPres := hS.rnPres
        cap₁ := by
          intro n hn w hw
          by_cases ho : ownKey own n = true
          · simp [Sub.hideOwn, ho] at hw
          · have ho' : ownKey own n = false := by simpa using ho
            simp only [Sub.hideOwn, ho', Bool.false_eq_true, if_false] at hw
            exact hS.cap₁ n (hfv n hn ho') w hw
        capφ₁ := by
          intro x hx w hw
          simp only [Sub.hideParam, hxℓ x hx, if_false] at hw
          exact hS.capφ₁ x (hfp x hx) w hw
        cap₂ := by
          intro n hn w hw
          by_cases ho : ownKey own n = true
          · exact hS.capR (νi n) (hRes _ (Or.inl (hlive n hn ho))) w hw
          · have ho' : ownKey own n = false := by simpa using ho
            rw [hνi n ho'] at hw
            exact hS.cap₂ n (hfv n hn ho') w hw
        capφ₂ := fun x hx w hw => hS.capφ₂ x (hfp x hx) w hw
        capR := fun m hm w hw => hS.capR m (hRes m (Or.inr hm)) w hw }
      have hbFV : ∀ n ∈ freeNames (subst (θ₁.hideOwn own) (φ₁.hideParam ℓ) b₁),
          ownKey own n = true → n ∈ freeNames b₁ := by
        intro n hn ho
        rcases mem_freeNames_subst' b₁ _ _ n hn with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm⟩ |
            ⟨y, hy, w, hw, hm⟩
        · exact h1
        · rw [ownKey_of_OK₁ hr ((hSb.cap₁ n₀ hn₀ w hw).1 n hm)] at ho
          cases ho
        · rw [ownKey_of_OK₁ hr ((hSb.capφ₁ y hy w hw).1 n hm)] at ho
          cases ho
      refine .newAct (νi := νi') (Rh := Rh.map rn) hνi'n hr ?_ (ihb hSb) ?_ ?_
      · intro hm
        rcases mem_freeParams_subst' b₁ _ _ ℓ hm with ⟨h1, _⟩ | ⟨n₀, hn₀, w, hw, hm'⟩ |
            ⟨y, hy, w, hw, hm'⟩
        · exact hℓ h1
        · rw [(hSb.cap₁ n₀ hn₀ w hw).2] at hm'
          cases hm'
        · rw [(hSb.capφ₁ y hy w hw).2] at hm'
          cases hm'
      · intro n hn ho
        rw [hνi'o n ho]
        exact List.mem_map_of_mem (hlive n (hbFV n hn ho) ho)
      · intro n hn n' hn' ho ho' he
        rw [hνi'o n ho, hνi'o n' ho'] at he
        have l1 := hlive n (hbFV n hn ho) ho
        have l2 := hlive n' (hbFV n' hn' ho') ho'
        exact hinj n (hbFV n hn ho) n' (hbFV n' hn' ho') ho ho'
          (hS.resInj _ (hRes _ (Or.inl l1)) _ (hRes _ (Or.inl l2)) he)


/-! ## Ground values -/

/-- The code relation is bi-unique: related pairs agree on equality. -/
def Setting.BiUnique (C : Setting S X₁ X₂) : Prop :=
  ∀ c₁ c₂ c₁' c₂', C.Q c₁ c₂ → C.Q c₁' c₂' → (c₁ = c₁' ↔ c₂ = c₂')

omit [DecidableEq X₁] [DecidableEq X₂] in
/-- Related ground values agree on equality. -/
theorem GRel.eq_iff (hQ : C.BiUnique) {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C g₁ g₂) :
    ∀ {g₁' : GVal S X₁} {g₂' : GVal S X₂}, GRel C g₁' g₂' → (g₁ = g₁' ↔ g₂ = g₂') := by
  induction h with
  | sym s =>
      intro g₁' g₂' h'
      cases h' <;> simp
  | app _ _ ihf iha =>
      intro g₁' g₂' h'
      cases h' with
      | app hf' ha' => simp [ihf hf', iha ha']
      | sym _ => simp
      | quote _ => simp
      | ctx _ _ _ => simp
  | quote hq =>
      intro g₁' g₂' h'
      cases h' with
      | quote hq' => simpa using hQ _ _ _ _ hq hq'
      | sym _ => simp
      | app _ _ => simp
      | ctx _ _ _ => simp
  | ctx ho hks hc =>
      intro g₁' g₂' h'
      cases h' with
      | ctx ho' hks' hc' =>
          subst hks'; subst hc'; subst hks; subst hc
          simp only [GVal.ctx.injEq]
          constructor
          · rintro ⟨hk, hb⟩
            exact ⟨congrArg (List.map C.codeMap) hk, congrArg (mapCode C.codeMap) hb⟩
          · rintro ⟨hk, hb⟩
            exact ⟨list_map_injective C.codeMap_inj hk,
              mapCode_injective_ownNil C.codeMap_inj ho ho' hb⟩
      | sym _ => simp
      | app _ _ => simp
      | quote _ => simp

/-- A ground value is related to a related ground value as a term. -/
theorem GRel.toTm {g₁ : GVal S X₁} {g₂ : GVal S X₂} (h : GRel C g₁ g₂)
    (ν μ : Nm X₁ → Nm X₂) (k : Kd) : Rel C ν μ k [] true g₁.toTm g₂.toTm := by
  induction h with
  | sym s => exact .sym s
  | app _ _ ihf iha => exact .app ihf iha
  | quote hq => exact .quote hq
  | ctx ho hks hc => exact .ctx ho hks hc

/-- **Related values read back as related ground values.** -/
theorem Rel.toGVal? {ν μ : Nm X₁ → Nm X₂} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ .val Res ok t₁ t₂) : OptRel (GRel C) t₁.toGVal? t₂.toGVal? := by
  generalize hk : Kd.val = k at h
  induction h with
  | sym s => exact .sym s
  | fn F => trivial
  | var _ _ => trivial
  | pvar _ _ => trivial
  | quote hq => exact .quote hq
  | ctx ho hks hc => exact .ctx ho hks hc
  | pquote _ _ _ =>
      simp only [Tm.toGVal?]
      trivial
  | app _ _ ihf iha =>
      have hf := ihf hk
      have ha := iha hk
      simp only [Tm.toGVal?]
      rcases OptRel.cases hf with ⟨e1, e2⟩ | ⟨f₁, f₂, e1, e2, hf'⟩
      · rw [e1, e2]; trivial
      · rcases OptRel.cases ha with ⟨e3, e4⟩ | ⟨a₁, a₂, e3, e4, ha'⟩
        · rw [e1, e2, e3, e4]; trivial
        · rw [e1, e2, e3, e4]; exact .app hf' ha'
  | letP hk' => exact absurd hk.symm hk'
  | alt hk' => exact absurd hk.symm hk'
  | lam => trivial
  | letAct hk' => exact absurd hk.symm hk'
  | newAct => cases hk

/-! ## Stores -/

/-- **Stores related along `ν` on the names `D`**: bindings correspond, the
first store binds only names in `D`, and the second binds only their images. -/
structure StoreRel (C : Setting S X₁ X₂) (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁))
    (σ₁ : GStore S X₁) (σ₂ : GStore S X₂) : Prop where
  rel : ∀ n ∈ D, OptRel (GRel C) (σ₁ n) (σ₂ (ν n))
  dom : ∀ n, σ₁ n ≠ none → n ∈ D
  only : ∀ m, σ₂ m ≠ none → ∃ n ∈ D, ν n = m

omit [DecidableEq X₁] [DecidableEq X₂] in
theorem StoreRel.empty (ν : Nm X₁ → Nm X₂) (D : Set (Nm X₁)) :
    StoreRel C ν D (Store.empty : GStore S X₁) (Store.empty : GStore S X₂) where
  rel _ _ := trivial
  dom _ h := absurd rfl h
  only _ h := absurd rfl h

omit [DecidableEq X₁] [DecidableEq X₂] in
theorem StoreRel.mono {ν ν' : Nm X₁ → Nm X₂} {D D' : Set (Nm X₁)} {σ₁ : GStore S X₁}
    {σ₂ : GStore S X₂} (h : StoreRel C ν D σ₁ σ₂) (hD : D ⊆ D') (hν : ∀ n ∈ D, ν' n = ν n)
    (hnew : ∀ n ∈ D', n ∉ D → σ₁ n = none ∧ σ₂ (ν' n) = none) : StoreRel C ν' D' σ₁ σ₂ where
  rel n hn := by
    by_cases hnD : n ∈ D
    · rw [hν n hnD]; exact h.rel n hnD
    · obtain ⟨e1, e2⟩ := hnew n hn hnD
      rw [e1, e2]; trivial
  dom n hn := hD (h.dom n hn)
  only m hm := by
    obtain ⟨n, hnD, rfl⟩ := h.only m hm
    exact ⟨n, hD hnD, hν n hnD⟩

/-! ## Matching -/

theorem freeNames_toTm {Y : Type v} [DecidableEq Y] : ∀ g : GVal S Y, freeNames g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeNames, freeNames_toTm f, freeNames_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

theorem freeParams_toTm {Y : Type v} [DecidableEq Y] : ∀ g : GVal S Y, freeParams g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeParams, freeParams_toTm f, freeParams_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

theorem GVal.toTm_ne_var {Y : Type v} (g : GVal S Y) (n : Nm Y) : g.toTm ≠ .var n := by
  cases g <;> simp [GVal.toTm]

variable [DecidableEq S]

/-- One refinement step, on related stores and related values, at a name in
`D` where `ν` is injective. -/
theorem StoreRel.refine {ν : Nm X₁ → Nm X₂} {D : Set (Nm X₁)} (hQ : C.BiUnique)
    (hinj : Set.InjOn ν D) {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (h : StoreRel C ν D σ₁ σ₂)
    {n : Nm X₁} (hn : n ∈ D) {g₁ : GVal S X₁} {g₂ : GVal S X₂} (hg : GRel C g₁ g₂) :
    OptRel (StoreRel C ν D) (refineStep σ₁ (n, g₁)) (refineStep σ₂ (ν n, g₂)) := by
  have hr := h.rel n hn
  unfold SequentialBindingDiscipline.refineStep
  rcases OptRel.cases hr with ⟨e1, e2⟩ | ⟨w₁, w₂, e1, e2, hw⟩
  · simp only [e1, e2]
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      by_cases hmn : m = n
      · subst hmn
        simp only [if_true]
        exact hg
      · have hνm : ν m ≠ ν n := fun e => hmn (hinj hm hn e)
        simp only [hmn, hνm, if_false]
        exact h.rel m hm
    · intro m hm
      by_cases hmn : m = n
      · subst hmn; exact hn
      · simp only [hmn, if_false] at hm
        exact h.dom m hm
    · intro m hm
      by_cases hmn : m = ν n
      · exact ⟨n, hn, hmn.symm⟩
      · simp only [hmn, if_false] at hm
        exact h.only m hm
  · simp only [e1, e2]
    by_cases heq : w₁ = g₁
    · have heq2 : w₂ = g₂ := (hw.eq_iff hQ hg).1 heq
      simp only [heq, heq2, if_true]
      exact h
    · have heq2 : ¬ w₂ = g₂ := fun e => heq ((hw.eq_iff hQ hg).2 e)
      simp only [heq, heq2, if_false]
      trivial

variable [CodeId X₁] [CodeId X₂]

/-- Related sealed code agrees under `codeEq`. Structural equality of code is
the special case of the default comparison; a model that stores binder
positions compares those positions. -/
def Setting.CodeAgree (C : Setting S X₁ X₂) : Prop :=
  ∀ c₁ c₂ c₁' c₂', C.Q c₁ c₂ → C.Q c₁' c₂' →
    (codeEq c₁ c₁' = true ↔ codeEq c₂ c₂' = true)

/-- Related pattern code matches related quotations on both sides together.
The code is stable and of one weak shape. A hole binds a ground value; a
binder of the code is compared by `CodeId`. -/
def Setting.PatAgree (C : Setting S X₁ X₂) : Prop :=
  ∀ {ν μ : Nm X₁ → Nm X₂} {ok : Bool} {c₁ : Tm S X₁} {c₂ : Tm S X₂}
    {q₁ : Tm S X₁} {q₂ : Tm S X₂}
    {D : Set (Nm X₁)} {σ₁ : GStore S X₁} {σ₂ : GStore S X₂},
    Rel C ν μ .code [] ok c₁ c₂ →
    ok = true →
    ShapeParallel C c₁ c₂ →
    C.Q q₁ q₂ →
    (∀ n ∈ freeNames c₁, n ∈ D) →
    Set.InjOn ν D →
    StoreRel C ν D σ₁ σ₂ →
    OptRel (StoreRel C ν D) (matchCode σ₁ c₁ q₁) (matchCode σ₂ c₂ q₂)

/-- **Related patterns match related ground values alike**, with related
stores. Two quotations match when `codeEq` says they are the same code. A
pattern quotation matches the quoted code by `matchCode`. -/
theorem Rel.matchT (hQ : C.BiUnique) (hC : C.CodeAgree) (hP : C.PatAgree) {ν μ : Nm X₁ → Nm X₂}
    {ok : Bool} {Res : List (Nm X₂)}
    {p₁ : Tm S X₁} {p₂ : Tm S X₂} (h : Rel C ν μ .pat Res ok p₁ p₂) {D : Set (Nm X₁)}
    (hD : ∀ n ∈ freeNames p₁, n ∈ D) (hinj : Set.InjOn ν D) :
    ∀ {g₁ : GVal S X₁} {g₂ : GVal S X₂}, GRel C g₁ g₂ → ∀ {σ₁ : GStore S X₁} {σ₂ : GStore S X₂},
      StoreRel C ν D σ₁ σ₂ →
      OptRel (StoreRel C ν D) (TemplateScope.matchT σ₁ p₁ g₁.toTm)
        (TemplateScope.matchT σ₂ p₂ g₂.toTm) := by
  generalize hk : Kd.pat = k at h
  induction h with
  | sym s =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.sym s) g₁.toTm =
          if Tm.sym s = g₁.toTm then some σ₁ else none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.sym s) g₂.toTm =
          if Tm.sym s = g₂.toTm then some σ₂ else none := by cases g₂ <;> rfl
      rw [e1, e2]
      have hiff : (Tm.sym s : Tm S X₁) = g₁.toTm ↔ (Tm.sym s : Tm S X₂) = g₂.toTm := by
        cases hg <;> simp [GVal.toTm]
      by_cases hs : (Tm.sym s : Tm S X₁) = g₁.toTm
      · rw [if_pos hs, if_pos (hiff.1 hs)]; exact hσ
      · rw [if_neg hs, if_neg (fun e => hs (hiff.2 e))]; trivial
  | fn F =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.fn F) g₁.toTm = none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.fn F) g₂.toTm = none := by cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | var n _ =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      simp only [TemplateScope.matchT, GVal.toTm_toGVal?]
      exact hσ.refine hQ hinj (hD n (by simp [freeNames])) hg
  | @pvar ν' μ' k' x _ =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.pvar x) g₁.toTm = none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.pvar (μ' x)) g₂.toTm = none := by cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | @quote ν μ k c₁ c₂ hq =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      cases g₁ with
      | sym _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | app _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | ctx _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | quote q₁ =>
          cases g₂ with
          | sym _ => cases hg
          | app _ _ => cases hg
          | ctx _ _ => cases hg
          | quote q₂ =>
              cases hg with
              | quote hq' =>
                  simp only [GVal.toTm, TemplateScope.matchT]
                  cases hce : codeEq c₁ q₁ with
                  | true =>
                      rw [if_pos rfl, if_pos ((hC c₁ c₂ q₁ q₂ hq hq').1 hce)]
                      exact hσ
                  | false =>
                      simp only [Bool.false_eq_true, if_false]
                      have hne : ¬ codeEq c₂ q₂ = true :=
                        fun h => Bool.false_ne_true (hce.symm ▸ (hC c₁ c₂ q₁ q₂ hq hq').2 h)
                      rw [if_neg hne]
                      trivial
  | @pquote ν μ k c₁ c₂ _ hbody hp hok =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      cases g₁ with
      | sym _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | app _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | ctx _ _ =>
          cases hg
          simp [GVal.toTm, TemplateScope.matchT]
          trivial
      | quote q₁ =>
          cases g₂ with
          | sym _ => cases hg
          | app _ _ => cases hg
          | ctx _ _ => cases hg
          | quote q₂ =>
              cases hg with
              | quote hq =>
                  simp only [GVal.toTm, TemplateScope.matchT]
                  exact hP hbody hok hp hq (fun n hn => hD n (by simp [freeNames, hn])) hinj hσ
  | app _ _ ihf iha =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      simp only [freeNames, List.mem_append] at hD
      cases hg with
      | app hf ha =>
          simp only [GVal.toTm, TemplateScope.matchT]
          rcases OptRel.cases (ihf (fun n h => hD n (Or.inl h)) hinj hk hf hσ) with
              ⟨e1, e2⟩ | ⟨τ₁, τ₂, e1, e2, hτ⟩
          · rw [e1, e2]; trivial
          · rw [e1, e2]
            exact iha (fun n h => hD n (Or.inr h)) hinj hk ha hτ
      | sym s => simp [GVal.toTm, TemplateScope.matchT]; trivial
      | quote _ => simp [GVal.toTm, TemplateScope.matchT]; trivial
      | ctx _ _ _ => simp [GVal.toTm, TemplateScope.matchT]; trivial
  | letP =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : ∀ (p w b : Tm S X₁), TemplateScope.matchT σ₁ (.letP p w b) g₁.toTm = none := by
        intro p w b; cases g₁ <;> rfl
      have e2 : ∀ (p w b : Tm S X₂), TemplateScope.matchT σ₂ (.letP p w b) g₂.toTm = none := by
        intro p w b; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | alt =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : ∀ (t u : Tm S X₁), TemplateScope.matchT σ₁ (.alt t u) g₁.toTm = none := by
        intro t u; cases g₁ <;> rfl
      have e2 : ∀ (t u : Tm S X₂), TemplateScope.matchT σ₂ (.alt t u) g₂.toTm = none := by
        intro t u; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | lam =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : ∀ x own (b : Tm S X₁), TemplateScope.matchT σ₁ (.lam x own b) g₁.toTm = none := by
        intro x own b; cases g₁ <;> rfl
      have e2 : ∀ x own (b : Tm S X₂), TemplateScope.matchT σ₂ (.lam x own b) g₂.toTm = none := by
        intro x own b; cases g₂ <;> rfl
      rw [e1, e2]; trivial
  | @ctx ν μ k ks₁ c₁ ks₂ c₂ ho hks hc =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e1 : TemplateScope.matchT σ₁ (.ctx ks₁ c₁) g₁.toTm =
          if Tm.ctx ks₁ c₁ = g₁.toTm then some σ₁ else none := by cases g₁ <;> rfl
      have e2 : TemplateScope.matchT σ₂ (.ctx ks₂ c₂) g₂.toTm =
          if Tm.ctx ks₂ c₂ = g₂.toTm then some σ₂ else none := by cases g₂ <;> rfl
      rw [e1, e2]
      have hiff : (Tm.ctx ks₁ c₁ = g₁.toTm) ↔ (Tm.ctx ks₂ c₂ = g₂.toTm) := by
        cases hg with
        | ctx ho' hks' hc' =>
            subst hks'; subst hc'; subst hks; subst hc
            simp only [GVal.toTm, Tm.ctx.injEq]
            constructor
            · rintro ⟨hk, hb⟩
              exact ⟨congrArg (List.map C.codeMap) hk, congrArg (mapCode C.codeMap) hb⟩
            · rintro ⟨hk, hb⟩
              exact ⟨list_map_injective C.codeMap_inj hk,
                mapCode_injective_ownNil C.codeMap_inj ho ho' hb⟩
        | sym _ =>
            constructor <;> intro heq <;> cases heq
        | app _ _ =>
            constructor <;> intro heq <;> cases heq
        | quote _ =>
            constructor <;> intro heq <;> cases heq
      by_cases hs : Tm.ctx ks₁ c₁ = g₁.toTm
      · rw [if_pos hs, if_pos (hiff.1 hs)]; exact hσ
      · rw [if_neg hs, if_neg (fun e => hs (hiff.2 e))]; trivial
  | letAct =>
      intro g₁ g₂ hg σ₁ σ₂ hσ
      have e2 : ∀ (p w b : Tm S X₂), TemplateScope.matchT σ₂ (.letP p w b) g₂.toTm = none := by
        intro p w b; cases g₂ <;> rfl
      rw [e2]
      cases g₁ with
      | app gf ga =>
          have e : ∀ x own (b : Tm S X₁), TemplateScope.matchT σ₁ (.lam x own b) gf.toTm = none := by
            intro x own b; cases gf <;> rfl
          have e' : ∀ x own (b w : Tm S X₁),
              TemplateScope.matchT σ₁ (.app (.lam x own b) w) (GVal.app gf ga).toTm = none := by
            intro x own b w
            show (match TemplateScope.matchT σ₁ (.lam x own b) gf.toTm with
              | some σ' => TemplateScope.matchT σ' w ga.toTm | none => none) = none
            rw [e]
          rw [e']
          trivial
      | sym s => exact trivial
      | quote c => exact trivial
      | ctx _ _ =>
          cases hg
          exact trivial
  | newAct => cases hk

omit [DecidableEq S] [CodeId X₁] [CodeId X₂] in
/-- **Applying related stores to related terms gives related terms.** -/
theorem Rel.applyStore {ν μ : Nm X₁ → Nm X₂} {k : Kd} {Res : List (Nm X₂)} {ok : Bool}
    {t₁ : Tm S X₁} {t₂ : Tm S X₂}
    (h : Rel C ν μ k Res ok t₁ t₂) {D : Set (Nm X₁)} (hD : ∀ n ∈ freeNames t₁, n ∈ D)
    {σ₁ : GStore S X₁} {σ₂ : GStore S X₂} (hσ : StoreRel C ν D σ₁ σ₂)
    (hres : ∀ m ∈ Res, σ₂ m = none) :
    Rel C ν μ k Res ok (TemplateScope.act σ₁ t₁) (TemplateScope.act σ₂ t₂) := by
  have h' := h.substitute (θ₁ := envSub σ₁) (φ₁ := Sub.none) (θ₂ := envSub σ₂) (φ₂ := Sub.none)
    (ν' := ν) (μ' := μ) (rn := id) {
      names := by
        intro n hn
        rcases OptRel.cases (hσ.rel n (hD n hn)) with ⟨e1, e2⟩ | ⟨g₁, g₂, e1, e2, hg⟩
        · simp only [envSub, e1, e2, Option.map_none, Option.getD_none]
          exact .var n (h.varHole_free hn)
        · simp only [envSub, e1, e2, Option.map_some, Option.getD_some]
          exact hg.toTm ν μ .val
      params := by
        intro x hx
        exact .pvar x (h.parOK_free hx)
      res := by
        intro m hm
        simp [envSub, hres m hm]
      resInj := fun _ _ _ _ h => h
      rnPres := C.preserve_refl
      cap₁ := by
        intro n _ w hw
        simp only [envSub, Option.map_eq_some_iff] at hw
        obtain ⟨g, -, rfl⟩ := hw
        exact ⟨by simp [freeNames_toTm], freeParams_toTm g⟩
      capφ₁ := by
        intro x _ w hw
        cases hw
      cap₂ := by
        intro n _ w hw
        simp only [envSub, Option.map_eq_some_iff] at hw
        obtain ⟨g, -, rfl⟩ := hw
        exact ⟨by simp [freeNames_toTm], freeParams_toTm g⟩
      capφ₂ := by
        intro x _ w hw
        cases hw
      capR := by
        intro m hm w hw
        simp [envSub, hres m hm] at hw }
  simpa [TemplateScope.act] using h'

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
