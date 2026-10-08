import Mettapedia.GSLT.LanguageDef.TemplateScope.Defunctionalization

/-!
# Quoted code, related by binder identity

A quotation written in pattern position is code. Its binders are names, and
the relation compares those names by the identity each model stored, not by
the spelling that was written. Substitution may replace a free store name or
a free parameter by a value; the value is then part of the code, and only its
free names are tracked.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

namespace IdSlot

variable {S : Type u} {X₁ X₂ : Type v} [DecidableEq X₁] [DecidableEq X₂]

variable {R₁ : X₁ → Prop} {R₂ : X₂ → Prop}

/-- A name a binder may leave free: a root spelling, or any activation copy.
Activation copies are never on an own list. -/
def rootNm {Y : Type v} (R : Y → Prop) : Nm Y → Prop
  | .src s => R s
  | .inst _ _ => True

/-- An own list that excludes roots binds no name that may occur free. -/
theorem ownKey_of_rootNm {Y : Type v} [DecidableEq Y] {R : Y → Prop} {own : List Y}
    (hr : ∀ s ∈ own, ¬ R s) {n : Nm Y} (h : rootNm R n) : ownKey own n = false := by
  cases n with
  | src s =>
      simp only [rootNm] at h
      simp only [ownKey, List.contains_eq_mem, decide_eq_false_iff_not]
      exact fun hs => hr s hs h
  | inst _ _ => rfl

/-- On an owned name the two maps agree, because an owned name is a root
spelling and the result map does not move root spellings. -/
theorem map_src_of_owned {Y Z : Type v} [DecidableEq Y] {own : List Y} {g g' : Nm Y → Z}
    {n : Nm Y} (ho : ownKey own n = true) (h : ∀ s, g' (.src s) = g (.src s)) : g' n = g n := by
  cases n with
  | src s => exact h s
  | inst _ _ =>
      simp only [ownKey] at ho
      exact absurd ho Bool.false_ne_true

/-- Code related at the same shape. `f` sends a name of the first side to the
name of the second. `L` marks parameter names of this code: a parameter is
not a free store name. A lambda's own list binds on both sides together, and
neither own list contains a root spelling. -/
inductive CodeRel (Q : Tm S X₁ → Tm S X₂ → Prop) (L : Nm X₁ → Prop) (f : Nm X₁ → Nm X₂) :
    Tm S X₁ → Tm S X₂ → Prop where
  | sym (s : S) : CodeRel Q L f (.sym s) (.sym s)
  | fn (F : S) : CodeRel Q L f (.fn F) (.fn F)
  | var (n : Nm X₁) : CodeRel Q L f (.var n) (.var (f n))
  | pvar {x : Nm X₁} (hx : L x) : CodeRel Q L f (.pvar x) (.pvar (f x))
  | lam {x : Nm X₁} {own₁ : List X₁} {b₁ : Tm S X₁} {x' : Nm X₂} {own₂ : List X₂}
      {b₂ : Tm S X₂}
      (hx : f x = x') (hL : L x)
      (hr₁ : ∀ s ∈ own₁, ¬ R₁ s) (hr₂ : ∀ s ∈ own₂, ¬ R₂ s)
      (hown : ∀ n ∈ freeNames b₁, ownKey own₂ (f n) = ownKey own₁ n)
      (hpar : ∀ y ∈ freeParams b₁, y ≠ x → f y ≠ x')
      (hb : CodeRel Q L f b₁ b₂) :
      CodeRel Q L f (.lam x own₁ b₁) (.lam x' own₂ b₂)
  | app {a₁ b₁ : Tm S X₁} {a₂ b₂ : Tm S X₂}
      (ha : CodeRel Q L f a₁ a₂) (hb : CodeRel Q L f b₁ b₂) :
      CodeRel Q L f (.app a₁ b₁) (.app a₂ b₂)
  | quote {c₁ : Tm S X₁} {c₂ : Tm S X₂} (h : Q c₁ c₂) :
      CodeRel Q L f (.quote c₁) (.quote c₂)
  | pquote {c₁ : Tm S X₁} {c₂ : Tm S X₂} (h : CodeRel Q L f c₁ c₂) :
      CodeRel Q L f (.pquote c₁) (.pquote c₂)
  | letP {p₁ w₁ b₁ : Tm S X₁} {p₂ w₂ b₂ : Tm S X₂}
      (hp : CodeRel Q L f p₁ p₂) (hw : CodeRel Q L f w₁ w₂) (hb : CodeRel Q L f b₁ b₂) :
      CodeRel Q L f (.letP p₁ w₁ b₁) (.letP p₂ w₂ b₂)
  | alt {t₁ u₁ : Tm S X₁} {t₂ u₂ : Tm S X₂}
      (h₁ : CodeRel Q L f t₁ t₂) (h₂ : CodeRel Q L f u₁ u₂) :
      CodeRel Q L f (.alt t₁ u₁) (.alt t₂ u₂)

variable {Q : Tm S X₁ → Tm S X₂ → Prop} {L : Nm X₁ → Prop} {f : Nm X₁ → Nm X₂}

/-- An empty own list binds nothing. -/
theorem ownKey_nil {Y : Type v} [DecidableEq Y] (n : Nm Y) : ownKey ([] : List Y) n = false := by
  cases n <;> rfl

/-- A free store name of related code is sent to a free store name. -/
theorem CodeRel.mem_freeNames {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {n}, n ∈ freeNames t₁ → f n ∈ freeNames t₂ := by
  induction h with
  | sym s => intro n hn; simp [freeNames] at hn
  | fn F => intro n hn; simp [freeNames] at hn
  | var m => intro n hn; simp only [freeNames, List.mem_singleton] at hn ⊢; rw [hn]
  | pvar _ => intro n hn; simp [freeNames] at hn
  | lam _ _ _ _ hown _ _ ih =>
      intro n hn
      simp only [freeNames, List.mem_filter, Bool.not_eq_true'] at hn ⊢
      obtain ⟨hn, ho⟩ := hn
      refine ⟨ih hn, ?_⟩
      rw [hown n hn]
      exact ho
  | app _ _ ihf iha =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ihf iha
  | quote _ => intro n hn; simp [freeNames] at hn
  | pquote _ ih =>
      intro n hn
      simp only [freeNames] at hn
      exact ih hn
  | letP _ _ _ ihp ihw ihb =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      rcases hn with (hn | hn) | hn
      · exact Or.inl (Or.inl (ihp hn))
      · exact Or.inl (Or.inr (ihw hn))
      · exact Or.inr (ihb hn)
  | alt _ _ ih₁ ih₂ =>
      intro n hn
      simp only [freeNames, List.mem_append] at hn ⊢
      exact hn.imp ih₁ ih₂

/-- A free name of the second side is the image of one of the first. -/
theorem CodeRel.mem_freeNames_rev {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {m}, m ∈ freeNames t₂ → ∃ n ∈ freeNames t₁, f n = m := by
  induction h with
  | sym s => intro m hm; simp [freeNames] at hm
  | fn F => intro m hm; simp [freeNames] at hm
  | var n =>
      intro m hm
      simp only [freeNames, List.mem_singleton] at hm
      exact ⟨n, by simp [freeNames], hm.symm⟩
  | pvar _ => intro m hm; simp [freeNames] at hm
  | lam _ _ _ _ hown _ _ ih =>
      intro m hm
      simp only [freeNames, List.mem_filter, Bool.not_eq_true'] at hm
      obtain ⟨hm, ho⟩ := hm
      obtain ⟨n, hn, rfl⟩ := ih hm
      refine ⟨n, ?_, rfl⟩
      simp only [freeNames, List.mem_filter, Bool.not_eq_true']
      exact ⟨hn, by rw [← hown n hn]; exact ho⟩
  | app _ _ ihf iha =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨n, hn, e⟩ := ihf hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inl hn, e⟩
      · obtain ⟨n, hn, e⟩ := iha hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inr hn, e⟩
  | quote _ => intro m hm; simp [freeNames] at hm
  | pquote _ ih =>
      intro m hm
      simp only [freeNames] at hm
      exact ih hm
  | letP _ _ _ ihp ihw ihb =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with (hm | hm) | hm
      · obtain ⟨n, hn, e⟩ := ihp hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inl (Or.inl hn), e⟩
      · obtain ⟨n, hn, e⟩ := ihw hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inl (Or.inr hn), e⟩
      · obtain ⟨n, hn, e⟩ := ihb hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inr hn, e⟩
  | alt _ _ ih₁ ih₂ =>
      intro m hm
      simp only [freeNames, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨n, hn, e⟩ := ih₁ hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inl hn, e⟩
      · obtain ⟨n, hn, e⟩ := ih₂ hm
        exact ⟨n, by simp only [freeNames, List.mem_append]; exact Or.inr hn, e⟩

/-- A free parameter of related code is sent to a free parameter. -/
theorem CodeRel.mem_freeParams {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → f x ∈ freeParams t₂ := by
  induction h with
  | sym s => intro x hx; simp [freeParams] at hx
  | fn F => intro x hx; simp [freeParams] at hx
  | var _ => intro x hx; simp [freeParams] at hx
  | pvar _ => intro x hx; simp only [freeParams, List.mem_singleton] at hx ⊢; rw [hx]
  | lam _ _ _ _ _ hpar _ ih =>
      intro y hy
      simp only [freeParams, List.mem_filter, decide_eq_true_eq] at hy ⊢
      obtain ⟨hy, hne⟩ := hy
      exact ⟨ih hy, hpar y hy hne⟩
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ihf iha
  | quote _ => intro x hx; simp [freeParams] at hx
  | pquote _ ih =>
      intro x hx
      simp only [freeParams] at hx
      exact ih hx
  | letP _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (ihp hx))
      · exact Or.inl (Or.inr (ihw hx))
      · exact Or.inr (ihb hx)
  | alt _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx ⊢
      exact hx.imp ih₁ ih₂

/-- A free parameter of the second side is the image of one of the first. -/
theorem CodeRel.freeParams_rev {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {y}, y ∈ freeParams t₂ → ∃ x ∈ freeParams t₁, f x = y := by
  induction h with
  | sym s => intro y hy; simp [freeParams] at hy
  | fn F => intro y hy; simp [freeParams] at hy
  | var _ => intro y hy; simp [freeParams] at hy
  | @pvar x _ =>
      intro y hy
      simp only [freeParams, List.mem_singleton] at hy
      exact ⟨x, by simp [freeParams], hy.symm⟩
  | @lam x _ _ _ _ _ hfx _ _ _ _ _ _ ih =>
      intro y hy
      simp only [freeParams, List.mem_filter, decide_eq_true_eq] at hy
      obtain ⟨hy, hne⟩ := hy
      obtain ⟨z, hz, he⟩ := ih hy
      have hzx : z ≠ x := by
        intro hze
        apply hne
        rw [← he, hze, hfx]
      refine ⟨z, ?_, he⟩
      simp only [freeParams, List.mem_filter, decide_eq_true_eq]
      exact ⟨hz, hzx⟩
  | app _ _ ihf iha =>
      intro y hy
      simp only [freeParams, List.mem_append] at hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, e⟩ := ihf hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inl hx, e⟩
      · obtain ⟨x, hx, e⟩ := iha hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inr hx, e⟩
  | quote _ => intro y hy; simp [freeParams] at hy
  | pquote _ ih =>
      intro y hy
      simp only [freeParams] at hy
      exact ih hy
  | letP _ _ _ ihp ihw ihb =>
      intro y hy
      simp only [freeParams, List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · obtain ⟨x, hx, e⟩ := ihp hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inl (Or.inl hx), e⟩
      · obtain ⟨x, hx, e⟩ := ihw hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inl (Or.inr hx), e⟩
      · obtain ⟨x, hx, e⟩ := ihb hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inr hx, e⟩
  | alt _ _ ih₁ ih₂ =>
      intro y hy
      simp only [freeParams, List.mem_append] at hy
      rcases hy with hy | hy
      · obtain ⟨x, hx, e⟩ := ih₁ hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inl hx, e⟩
      · obtain ⟨x, hx, e⟩ := ih₂ hy
        exact ⟨x, by simp only [freeParams, List.mem_append]; exact Or.inr hx, e⟩

/-- Every parameter name the code relation uses satisfies `L`. -/
theorem CodeRel.param_local {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {x}, x ∈ freeParams t₁ → L x := by
  induction h with
  | sym s => intro x hx; simp [freeParams] at hx
  | fn F => intro x hx; simp [freeParams] at hx
  | var _ => intro x hx; simp [freeParams] at hx
  | pvar hx => intro y hy; simp only [freeParams, List.mem_singleton] at hy; exact hy.symm ▸ hx
  | lam _ _ _ _ _ _ _ ih =>
      intro y hy
      simp only [freeParams, List.mem_filter, decide_eq_true_eq] at hy
      exact ih hy.1
  | app _ _ ihf iha =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ihf iha
  | quote _ => intro x hx; simp [freeParams] at hx
  | pquote _ ih => intro x hx; simp only [freeParams] at hx; exact ih hx
  | letP _ _ _ ihp ihw ihb =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact ihp hx
      · exact ihw hx
      · exact ihb hx
  | alt _ _ ih₁ ih₂ =>
      intro x hx
      simp only [freeParams, List.mem_append] at hx
      exact hx.elim ih₁ ih₂

/-- What substitution does to the free names and parameters of one piece of
code. Each leaf is already related under the result map `f'`, at the widened
parameter predicate `L'`. `f'` agrees with `f` on the original parameter
binders `L`, and it does not move a root spelling. A value put in place of a
name or a parameter has no free parameter, and every name it inserts may
occur free. -/
structure CodeSub (Q : Tm S X₁ → Tm S X₂ → Prop) (L L' : Nm X₁ → Prop)
    (f f' : Nm X₁ → Nm X₂) (t₁ : Tm S X₁) (θ₁ φ₁ : Sub S X₁) (θ₂ φ₂ : Sub S X₂) : Prop where
  onVar : ∀ n ∈ freeNames t₁,
    CodeRel (R₁ := R₁) (R₂ := R₂) Q L' f' ((θ₁ n).getD (.var n)) ((θ₂ (f n)).getD (.var (f n)))
  onPVar : ∀ x ∈ freeParams t₁,
    CodeRel (R₁ := R₁) (R₂ := R₂) Q L' f' ((φ₁ x).getD (.pvar x)) ((φ₂ (f x)).getD (.pvar (f x)))
  widen : ∀ x, L x → L' x
  bind : ∀ x, L x → f' x = f x
  closedVar : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w → freeParams w = []
  closedPVar : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w → freeParams w = []
  srcFixed : ∀ s, f' (.src s) = f (.src s)
  kept : ∀ n ∈ freeNames t₁, θ₁ n = none →
    (f' n = f n ∧ θ₂ (f n) = none) ∨ rootNm R₂ (f' n)
  ins₁ : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w → ∀ m ∈ freeNames w, rootNm R₁ m
  insCase : ∀ n ∈ freeNames t₁, ∀ w, θ₁ n = some w → ∀ m ∈ freeNames w,
    rootNm R₂ (f' m) ∨ f' m = f n
  par₁ : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w → ∀ m ∈ freeNames w, rootNm R₁ m
  parImg : ∀ x ∈ freeParams t₁, ∀ w, φ₁ x = some w → ∀ m ∈ freeNames w, rootNm R₂ (f' m)

/-- The same substitution, read on a subterm whose free names and parameters
are among those of the whole term. -/
theorem CodeSub.sub {u : Tm S X₁} (hS : CodeSub (R₁ := R₁) (R₂ := R₂) Q L L' f f' t₁ θ₁ φ₁ θ₂ φ₂)
    (hn : ∀ n ∈ freeNames u, n ∈ freeNames t₁) (hx : ∀ x ∈ freeParams u, x ∈ freeParams t₁) :
    CodeSub (R₁ := R₁) (R₂ := R₂) Q L L' f f' u θ₁ φ₁ θ₂ φ₂ where
  onVar n h := hS.onVar n (hn n h)
  onPVar x h := hS.onPVar x (hx x h)
  widen := hS.widen
  bind := hS.bind
  closedVar n h := hS.closedVar n (hn n h)
  closedPVar x h := hS.closedPVar x (hx x h)
  srcFixed := hS.srcFixed
  kept n h := hS.kept n (hn n h)
  ins₁ n h := hS.ins₁ n (hn n h)
  insCase n h := hS.insCase n (hn n h)
  par₁ x h := hS.par₁ x (hx x h)
  parImg x h := hS.parImg x (hx x h)

/-- Hiding the binders of an empty own list leaves the substitution as it is. -/
theorem hideOwn_nil {Y : Type v} [DecidableEq Y] (θ : Sub S Y) : θ.hideOwn [] = θ := by
  funext n
  simp only [Sub.hideOwn, ownKey_nil, Bool.false_eq_true, if_false]

/-- A free name of a substituted term is a kept free name, or a free name of
what replaced a free name or a free parameter. -/
theorem mem_freeNames_of_subst {Y : Type v} [DecidableEq Y] (t : Tm S Y)
    (θ φ : Sub S Y) (m : Nm Y) (hm : m ∈ freeNames (subst θ φ t)) :
    (m ∈ freeNames t ∧ θ m = none) ∨
      (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ m ∈ freeNames w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ m ∈ freeNames w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ'
      (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hm
  rcases mem_freeNames_subst t θ' φ' m hm with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [θ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

/-- A free parameter of a substituted term is a kept parameter, or a parameter
of what replaced a free name or a free parameter. -/
theorem mem_freeParams_of_subst {Y : Type v} [DecidableEq Y] (t : Tm S Y)
    (θ φ : Sub S Y) (q : Nm Y) (hq : q ∈ freeParams (subst θ φ t)) :
    (q ∈ freeParams t ∧ φ q = none) ∨
      (∃ n ∈ freeNames t, ∃ w, θ n = some w ∧ q ∈ freeParams w) ∨
      ∃ x ∈ freeParams t, ∃ w, φ x = some w ∧ q ∈ freeParams w := by
  let θ' : Sub S Y := fun n => if n ∈ freeNames t then θ n else none
  let φ' : Sub S Y := fun x => if x ∈ freeParams t then φ x else none
  have e : subst θ φ t = subst θ' φ' t :=
    subst_eq_of_agree t θ θ' φ φ'
      (fun n hn => by simp [θ', hn]) (fun x hx => by simp [φ', hx])
  rw [e] at hq
  rcases mem_freeParams_subst t θ' φ' q hq with ⟨h1, h2⟩ | ⟨n, w, hn, hw⟩ | ⟨x, w, hx, hw⟩
  · exact Or.inl ⟨h1, by simpa [φ', h1] using h2⟩
  · by_cases hnt : n ∈ freeNames t
    · exact Or.inr (Or.inl ⟨n, hnt, w, by simpa [θ', hnt] using hn, hw⟩)
    · simp [θ', hnt] at hn
  · by_cases hxt : x ∈ freeParams t
    · exact Or.inr (Or.inr ⟨x, hxt, w, by simpa [φ', hxt] using hx, hw⟩)
    · simp [φ', hxt] at hx

/-- Substitution preserves related code. A replaced name is already related at
the widened parameter predicate, under the map of the result. The result map
agrees with the original on parameter binders and on root spellings, so an
own list still binds the same names. -/
theorem CodeRel.subst {t₁ : Tm S X₁} {t₂ : Tm S X₂} (h : CodeRel (R₁ := R₁) (R₂ := R₂) Q L f t₁ t₂) :
    ∀ {L' : Nm X₁ → Prop} {θ₁ φ₁ : Sub S X₁} {θ₂ φ₂ : Sub S X₂} {f' : Nm X₁ → Nm X₂},
      CodeSub (R₁ := R₁) (R₂ := R₂) Q L L' f f' t₁ θ₁ φ₁ θ₂ φ₂ →
      CodeRel (R₁ := R₁) (R₂ := R₂) Q L' f' (subst θ₁ φ₁ t₁) (subst θ₂ φ₂ t₂) := by
  induction h with
  | sym s => intro _ _ _ _ _ _ _; exact .sym s
  | fn F => intro _ _ _ _ _ _ _; exact .fn F
  | var n =>
      intro _ _ _ _ _ _ hS
      exact hS.onVar n (by simp [freeNames])
  | @pvar x _ =>
      intro _ _ _ _ _ _ hS
      exact hS.onPVar x (by simp [freeParams])
  | quote hq => intro _ _ _ _ _ _ _; exact .quote hq
  | pquote _ ih =>
      intro _ _ _ _ _ _ hS
      exact .pquote (ih (hS.sub (fun n hn => by simp [freeNames, hn])
        (fun x hx => by simp [freeParams, hx])))
  | app _ _ ihf iha =>
      intro _ _ _ _ _ _ hS
      exact .app
        (ihf (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
        (iha (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
  | alt _ _ ih₁ ih₂ =>
      intro _ _ _ _ _ _ hS
      exact .alt
        (ih₁ (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
        (ih₂ (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
  | letP _ _ _ ihp ihw ihb =>
      intro _ _ _ _ _ _ hS
      exact .letP
        (ihp (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
        (ihw (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
        (ihb (hS.sub (fun n hn => by simp [freeNames, hn])
          (fun x hx => by simp [freeParams, hx])))
  | @lam x own₁ b₁ x' own₂ b₂ hx hL hr₁ hr₂ hown hpar hb ih =>
      intro _ θ₁ φ₁ θ₂ φ₂ f' hS
      rw [subst.eq_5, subst.eq_5]
      refine .lam (by rw [hS.bind x hL, hx]) (hS.widen x hL) hr₁ hr₂ ?_ ?_ ?_
      · intro n hn
        rcases mem_freeNames_of_subst b₁ (θ₁.hideOwn own₁) (φ₁.hideParam x) n hn with
          ⟨hnb, hθ⟩ | ⟨n₀, hn₀, w, hw, hm⟩ | ⟨y, hy, w, hw, hm⟩
        · cases ho : ownKey own₁ n with
          | true =>
              rw [map_src_of_owned ho hS.srcFixed]
              exact (hown n hnb).trans ho
          | false =>
              have hθ₁ : θ₁ n = none := by
                simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hθ
                exact hθ
              have hnL : n ∈ freeNames (.lam x own₁ b₁) := by
                simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                exact ⟨hnb, ho⟩
              rcases hS.kept n hnL hθ₁ with ⟨heq, _⟩ | hok
              · rw [heq]
                exact (hown n hnb).trans ho
              · exact ownKey_of_rootNm hr₂ hok
        · have ho₀ : ownKey own₁ n₀ = false := by
            cases hk₀ : ownKey own₁ n₀ with
            | false => rfl
            | true => simp [Sub.hideOwn, hk₀] at hw
          have hn₀L : n₀ ∈ freeNames (.lam x own₁ b₁) := by
            simp only [freeNames, List.mem_filter, Bool.not_eq_true']
            exact ⟨hn₀, ho₀⟩
          have hw₁ : θ₁ n₀ = some w := by
            simp only [Sub.hideOwn, ho₀, Bool.false_eq_true, if_false] at hw
            exact hw
          have ho_m : ownKey own₁ n = false :=
            ownKey_of_rootNm hr₁ (hS.ins₁ n₀ hn₀L w hw₁ n hm)
          rcases hS.insCase n₀ hn₀L w hw₁ n hm with hok | heq
          · rw [ho_m]
            exact ownKey_of_rootNm hr₂ hok
          · rw [ho_m]
            exact (heq ▸ hown n₀ hn₀).trans ho₀
        · have hyx : y ≠ x := by
            intro hyx
            simp [Sub.hideParam, hyx] at hw
          have hyL : y ∈ freeParams (.lam x own₁ b₁) := by
            simp only [freeParams, List.mem_filter, decide_eq_true_eq]
            exact ⟨hy, hyx⟩
          have hw₁ : φ₁ y = some w := by
            simp only [Sub.hideParam, hyx, if_false] at hw
            exact hw
          have ho_m : ownKey own₁ n = false :=
            ownKey_of_rootNm hr₁ (hS.par₁ y hyL w hw₁ n hm)
          rw [ho_m]
          exact ownKey_of_rootNm hr₂ (hS.parImg y hyL w hw₁ n hm)
      · intro y hy hne
        rcases mem_freeParams_of_subst b₁ (θ₁.hideOwn own₁) (φ₁.hideParam x) y hy with
          ⟨hyb, _⟩ | ⟨n, hn, w, hw, hp⟩ | ⟨z, hz, w, hw, hp⟩
        · rw [hS.bind y (hb.param_local hyb)]
          exact hpar y hyb hne
        · have ho : ownKey own₁ n = false := by
            cases hk : ownKey own₁ n with
            | false => rfl
            | true => simp [Sub.hideOwn, hk] at hw
          have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
            simp only [freeNames, List.mem_filter, Bool.not_eq_true']
            exact ⟨hn, ho⟩
          have hw' : θ₁ n = some w := by
            simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hw
            exact hw
          rw [hS.closedVar n hn' w hw'] at hp
          cases hp
        · have hzx : z ≠ x := by
            intro hzx
            simp [Sub.hideParam, hzx] at hw
          have hz' : z ∈ freeParams (.lam x own₁ b₁) := by
            simp only [freeParams, List.mem_filter, decide_eq_true_eq]
            exact ⟨hz, hzx⟩
          have hw' : φ₁ z = some w := by simp [Sub.hideParam, hzx] at hw; exact hw
          rw [hS.closedPVar z hz' w hw'] at hp
          cases hp
      · exact ih {
          onVar := by
            intro n hn
            cases ho : ownKey own₁ n with
            | true =>
                have h2 : ownKey own₂ (f n) = true := by rw [hown n hn]; exact ho
                simp only [Sub.hideOwn, ho, h2, if_true, Option.getD_none]
                rw [← map_src_of_owned ho hS.srcFixed]
                exact .var n
            | false =>
                have h2 : ownKey own₂ (f n) = false := by rw [hown n hn]; exact ho
                simp only [Sub.hideOwn, ho, h2, Bool.false_eq_true, if_false]
                have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
                  simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                  exact ⟨hn, ho⟩
                exact hS.onVar n hn'
          onPVar := by
            intro y hy
            by_cases hxy : y = x
            · have hφ : (φ₁.hideParam x) y = none := by simp [Sub.hideParam, hxy]
              have hφ2 : (φ₂.hideParam x') (f y) = none := by
                have hfxy : f y = x' := by rw [hxy, hx]
                simp [Sub.hideParam, hfxy]
              have hLy : L y := hxy.symm ▸ hL
              have hfx : f' y = f y := by rw [hxy]; exact hS.bind x hL
              simp only [hφ, hφ2, Option.getD_none]
              rw [← hfx]
              exact CodeRel.pvar (hS.widen y hLy)
            · have hy' : y ∈ freeParams (.lam x own₁ b₁) := by
                simp only [freeParams, List.mem_filter, decide_eq_true_eq]
                exact ⟨hy, hxy⟩
              have hfy : f y ≠ x' := hpar y hy hxy
              have hφ : (φ₁.hideParam x) y = φ₁ y := by simp [Sub.hideParam, hxy]
              have hφ2 : (φ₂.hideParam x') (f y) = φ₂ (f y) := by simp [Sub.hideParam, hfy]
              simp only [hφ, hφ2]
              exact hS.onPVar y hy'
          widen := hS.widen
          bind := hS.bind
          closedVar := by
            intro n hn w hw
            cases ho : ownKey own₁ n with
            | true => simp [Sub.hideOwn, ho] at hw
            | false =>
                have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
                  simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                  exact ⟨hn, ho⟩
                have hw' : θ₁ n = some w := by
                  simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hw
                  exact hw
                exact hS.closedVar n hn' w hw'
          closedPVar := by
            intro y hy w hw
            have hxy : y ≠ x := by
              intro hxy
              simp [Sub.hideParam, hxy] at hw
            have hy' : y ∈ freeParams (.lam x own₁ b₁) := by
              simp only [freeParams, List.mem_filter, decide_eq_true_eq]
              exact ⟨hy, hxy⟩
            have hw' : φ₁ y = some w := by simp [Sub.hideParam, hxy] at hw; exact hw
            exact hS.closedPVar y hy' w hw'
          srcFixed := hS.srcFixed
          kept := by
            intro n hn hθ
            cases ho : ownKey own₁ n with
            | true =>
                have h2 : ownKey own₂ (f n) = true := by rw [hown n hn]; exact ho
                refine Or.inl ⟨map_src_of_owned ho hS.srcFixed, ?_⟩
                simp [Sub.hideOwn, h2]
            | false =>
                have hθ₁ : θ₁ n = none := by
                  simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hθ
                  exact hθ
                have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
                  simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                  exact ⟨hn, ho⟩
                have h2 : ownKey own₂ (f n) = false := by rw [hown n hn]; exact ho
                rcases hS.kept n hn' hθ₁ with ⟨heq, hθ₂⟩ | hok
                · refine Or.inl ⟨heq, ?_⟩
                  simp only [Sub.hideOwn, h2, Bool.false_eq_true, if_false]
                  exact hθ₂
                · exact Or.inr hok
          ins₁ := by
            intro n hn w hw m hm
            cases ho : ownKey own₁ n with
            | true => simp [Sub.hideOwn, ho] at hw
            | false =>
                have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
                  simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                  exact ⟨hn, ho⟩
                have hw' : θ₁ n = some w := by
                  simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hw
                  exact hw
                exact hS.ins₁ n hn' w hw' m hm
          insCase := by
            intro n hn w hw m hm
            cases ho : ownKey own₁ n with
            | true => simp [Sub.hideOwn, ho] at hw
            | false =>
                have hn' : n ∈ freeNames (.lam x own₁ b₁) := by
                  simp only [freeNames, List.mem_filter, Bool.not_eq_true']
                  exact ⟨hn, ho⟩
                have hw' : θ₁ n = some w := by
                  simp only [Sub.hideOwn, ho, Bool.false_eq_true, if_false] at hw
                  exact hw
                exact hS.insCase n hn' w hw' m hm
          par₁ := by
            intro y hy w hw m hm
            have hyx : y ≠ x := by
              intro hyx
              simp [Sub.hideParam, hyx] at hw
            have hy' : y ∈ freeParams (.lam x own₁ b₁) := by
              simp only [freeParams, List.mem_filter, decide_eq_true_eq]
              exact ⟨hy, hyx⟩
            have hw' : φ₁ y = some w := by simp [Sub.hideParam, hyx] at hw; exact hw
            exact hS.par₁ y hy' w hw' m hm
          parImg := by
            intro y hy w hw m hm
            have hyx : y ≠ x := by
              intro hyx
              simp [Sub.hideParam, hyx] at hw
            have hy' : y ∈ freeParams (.lam x own₁ b₁) := by
              simp only [freeParams, List.mem_filter, decide_eq_true_eq]
              exact ⟨hy, hyx⟩
            have hw' : φ₁ y = some w := by simp [Sub.hideParam, hyx] at hw; exact hw
            exact hS.parImg y hy' w hw' m hm }

end IdSlot

end Mettapedia.GSLT.LanguageDef.TemplateScope
