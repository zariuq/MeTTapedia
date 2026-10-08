import Mathlib.Data.List.Dedup
import Mettapedia.GSLT.LanguageDef.TemplateScope.Term

/-!
# Template scope, part 2: elaboration (who owns a `$` name)

Elaboration computes, once and before evaluation, which store names each
lambda owns, and records them in the term as the lambda's own binders.

* **Rule M** (Mercury's implicit quantification): a store name is quantified
  at the innermost scope containing all of its occurrences, where
  occurrences inside disjoint lambda bodies do not count against each other.
  Read top-down this is: an occurrence is quantified at the *outermost* scope
  on its path whose own level (outside nested lambdas) writes the name.
  `elabM E` implements it; `E` lists the names already quantified at
  enclosing scopes, so a lambda owns `direct body \ E`.
* **Rule A**: the innermost scope containing *all* occurrences, ignoring the
  disjointness clause.  `elabA O` implements it; `O` lists the names written
  outside the current subterm.

The query scope quantifies the names it writes directly (`elabTopM`): they
stay free in the elaborated term.

## Main results

* `elabM_congr` — elaboration reads the enclosing scopes only through the
  names the term writes.
* `elabM_inline` / `elabTopM_inline` — **text inlining is safe under
  hygiene**: re-elaborating the text `C[f := L]` gives the capture-avoiding
  substitution of the elaborated `L` into the elaborated `C`, provided no
  lambda of `C` that encloses a use of `f` owns a name that `L` writes.
  The hypothesis is necessary: `TemplateScope.Corpus` exhibits the negative
  control (the `lam w` program), where re-elaborating the inlined text changes
  ownership and the answers.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v}

/-! ## Names written in a term -/

/-- Spellings of the store names written at the current scope level: outside
nested lambdas and sealed quotations, and inside pattern quotations. -/
def direct : Tm S X → List X
  | .sym _ => []
  | .fn _ => []
  | .var (.src y) => [y]
  | .var (.inst _ _) => []
  | .pvar _ => []
  | .lam _ _ _ => []
  | .app f a => direct f ++ direct a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => direct c
  | .letP p w b => direct p ++ direct w ++ direct b
  | .alt t₁ t₂ => direct t₁ ++ direct t₂

/-- Spellings of all store names written in a term, at any depth, outside
sealed quotations. -/
def names : Tm S X → List X
  | .sym _ => []
  | .fn _ => []
  | .var (.src y) => [y]
  | .var (.inst _ _) => []
  | .pvar _ => []
  | .lam _ _ b => names b
  | .app f a => names f ++ names a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => names c
  | .letP p w b => names p ++ names w ++ names b
  | .alt t₁ t₂ => names t₁ ++ names t₂

theorem mem_names_of_mem_direct {y : X} :
    ∀ {t : Tm S X}, y ∈ direct t → y ∈ names t
  | .sym _, h => by simp [direct] at h
  | .fn _, h => by simp [direct] at h
  | .var (.src z), h => by simpa [direct, names] using h
  | .var (.inst _ _), h => by simp [direct] at h
  | .pvar _, h => by simp [direct] at h
  | .lam _ _ _, h => by simp [direct] at h
  | .app f a, h => by
      simp only [direct, List.mem_append] at h
      simp only [names, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_names_of_mem_direct h)
      · exact Or.inr (mem_names_of_mem_direct h)
  | .quote _, h => by simp [direct] at h
  | .ctx _ _, h => by simp [direct] at h
  | .pquote c, h => by
      simp only [direct] at h
      simp only [names]
      exact mem_names_of_mem_direct h
  | .letP p w b, h => by
      simp only [direct, List.mem_append] at h
      simp only [names, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mem_names_of_mem_direct h))
      · exact Or.inl (Or.inr (mem_names_of_mem_direct h))
      · exact Or.inr (mem_names_of_mem_direct h)
  | .alt t₁ t₂, h => by
      simp only [direct, List.mem_append] at h
      simp only [names, List.mem_append]
      rcases h with h | h
      · exact Or.inl (mem_names_of_mem_direct h)
      · exact Or.inr (mem_names_of_mem_direct h)

variable [DecidableEq X]

/-- Store names occurring free: not bound by an own binder, outside sealed
quotations. -/
def freeNames : Tm S X → List (Nm X)
  | .sym _ => []
  | .fn _ => []
  | .var n => [n]
  | .pvar _ => []
  | .lam _ own b => (freeNames b).filter (fun n => !ownKey own n)
  | .app f a => freeNames f ++ freeNames a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => freeNames c
  | .letP p w b => freeNames p ++ freeNames w ++ freeNames b
  | .alt t₁ t₂ => freeNames t₁ ++ freeNames t₂

/-- Text: no lambda carries own binders yet. -/
def bare : Tm S X → Bool
  | .lam _ own b => own.isEmpty && bare b
  | .app f a => bare f && bare a
  | .pquote c => bare c
  | .letP p w b => bare p && bare w && bare b
  | .alt t₁ t₂ => bare t₁ && bare t₂
  | _ => true

/-! ## Rule M -/

/-- The names a lambda body owns under rule M, given the names `E` already
quantified at enclosing scopes. -/
def ownM (E : List X) (b : Tm S X) : List X :=
  ((direct b).filter (fun y => decide (y ∉ E))).dedup

/-- Rule M elaboration.  Sealed quotations are code and are not elaborated. -/
def elabM (E : List X) : Tm S X → Tm S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var n
  | .pvar x => .pvar x
  | .lam x _ b => .lam x (ownM E b) (elabM (ownM E b ++ E) b)
  | .app f a => .app (elabM E f) (elabM E a)
  | .quote c => .quote c
  | .ctx ks c => .ctx ks c
  | .pquote c => .pquote (elabM E c)
  | .letP p w b => .letP (elabM E p) (elabM E w) (elabM E b)
  | .alt t₁ t₂ => .alt (elabM E t₁) (elabM E t₂)

/-- Rule M at the query: the query quantifies what it writes directly. -/
def elabTopM (t : Tm S X) : Tm S X := elabM (direct t) t

/-- The names an elaborated lambda owns. -/
def ownNames : Tm S X → List X
  | .lam _ own _ => own
  | _ => []

/-- The rest of a lambda's store names: those it captures. -/
def captured (t : Tm S X) : List (Nm X) := (freeNames t).dedup

/-! ## Rule A -/

/-- The number of maximal lambdas in a term whose body writes `y`. -/
def lamHits (y : X) : Tm S X → ℕ
  | .lam _ _ b => if y ∈ names b then 1 else 0
  | .app f a => lamHits y f + lamHits y a
  | .pquote c => lamHits y c
  | .letP p w b => lamHits y p + lamHits y w + lamHits y b
  | .alt t₁ t₂ => lamHits y t₁ + lamHits y t₂
  | _ => 0

/-- The names a lambda body owns under rule A, given the names `O` written
outside the lambda: those not written outside whose occurrences are not all
inside a single nested lambda. -/
def ownA (O : List X) (b : Tm S X) : List X :=
  ((names b).filter (fun y => decide (y ∉ O ∧ (y ∈ direct b ∨ 2 ≤ lamHits y b)))).dedup

/-- Rule A elaboration; `O` lists the names written outside the subterm. -/
def elabA (O : List X) : Tm S X → Tm S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .var n => .var n
  | .pvar x => .pvar x
  | .lam x _ b => .lam x (ownA O b) (elabA O b)
  | .app f a => .app (elabA (O ++ names a) f) (elabA (O ++ names f) a)
  | .quote c => .quote c
  | .ctx ks c => .ctx ks c
  | .pquote c => .pquote (elabA O c)
  | .letP p w b =>
      .letP (elabA (O ++ names w ++ names b) p) (elabA (O ++ names p ++ names b) w)
        (elabA (O ++ names p ++ names w) b)
  | .alt t₁ t₂ => .alt (elabA (O ++ names t₂) t₁) (elabA (O ++ names t₁) t₂)

/-- Rule A at the query. -/
def elabTopA (t : Tm S X) : Tm S X := elabA [] t

/-! ## Elaboration reads its context only through the names written -/

theorem ownM_congr {E E' : List X} {b : Tm S X}
    (h : ∀ y ∈ names b, (y ∈ E ↔ y ∈ E')) : ownM E b = ownM E' b := by
  unfold ownM
  congr 1
  apply List.filter_congr
  intro y hy
  have := h y (mem_names_of_mem_direct hy)
  simp [this]

theorem elabM_congr : ∀ (t : Tm S X) {E E' : List X},
    (∀ y ∈ names t, (y ∈ E ↔ y ∈ E')) → elabM E t = elabM E' t
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .var _, _, _, _ => rfl
  | .pvar _, _, _, _ => rfl
  | .lam x own b, E, E', h => by
      have hb : ∀ y ∈ names b, (y ∈ E ↔ y ∈ E') := h
      have hown : ownM E b = ownM E' b := ownM_congr hb
      simp only [elabM, hown]
      congr 1
      apply elabM_congr b
      intro y hy
      simp only [List.mem_append]
      exact or_congr_right (hb y hy)
  | .app f a, E, E', h => by
      simp only [names, List.mem_append] at h
      simp only [elabM]
      rw [elabM_congr f (fun y hy => h y (Or.inl hy)),
        elabM_congr a (fun y hy => h y (Or.inr hy))]
  | .quote _, _, _, _ => rfl
  | .ctx _ _, _, _, _ => rfl
  | .pquote c, E, E', h => by
      simp only [elabM]
      rw [elabM_congr c h]
  | .letP p w b, E, E', h => by
      simp only [names, List.mem_append] at h
      simp only [elabM]
      rw [elabM_congr p (fun y hy => h y (Or.inl (Or.inl hy))),
        elabM_congr w (fun y hy => h y (Or.inl (Or.inr hy))),
        elabM_congr b (fun y hy => h y (Or.inr hy))]
  | .alt t₁ t₂, E, E', h => by
      simp only [names, List.mem_append] at h
      simp only [elabM]
      rw [elabM_congr t₁ (fun y hy => h y (Or.inl hy)),
        elabM_congr t₂ (fun y hy => h y (Or.inr hy))]

/-! ## Text inlining and hygiene -/

/-- Hygiene of an inlining site: every lambda of the elaborated context that
encloses a use of `f` owns no name that the inlined lambda writes (`NL`). -/
def hygM (fx : X) (NL : List X) : Tm S X → Bool
  | .lam _ own b =>
      (decide (fx ∉ names b) || decide (∀ y ∈ own, y ∉ NL)) && hygM fx NL b
  | .app f a => hygM fx NL f && hygM fx NL a
  | .pquote c => hygM fx NL c
  | .letP p w b => hygM fx NL p && hygM fx NL w && hygM fx NL b
  | .alt t₁ t₂ => hygM fx NL t₁ && hygM fx NL t₂
  | _ => true

theorem ownKey_src (own : List X) (y : X) : ownKey own (.src y) = decide (y ∈ own) := by
  simp [ownKey]

theorem Sub.hideOwn_nil (θ : Sub S X) : θ.hideOwn [] = θ := by
  funext n
  cases n <;> simp [Sub.hideOwn, ownKey]

theorem Sub.single_src_hideOwn {fx : X} {own : List X} (h : fx ∉ own) (t : Tm S X) :
    (Sub.single (.src fx) t).hideOwn own = Sub.single (.src fx) t := by
  funext n
  unfold Sub.hideOwn
  cases n with
  | src y =>
      by_cases hy : y ∈ own
      · have hne : y ≠ fx := fun e => h (e ▸ hy)
        simp [ownKey_src, hy, Sub.single, hne]
      · simp [ownKey_src, hy]
  | inst ρ m => simp [ownKey]

theorem names_elabM : ∀ (E : List X) (t : Tm S X), names (elabM E t) = names t
  | _, .sym _ => rfl
  | _, .fn _ => rfl
  | _, .var _ => rfl
  | _, .pvar _ => rfl
  | E, .lam x own b => by simp only [elabM, names]; exact names_elabM _ b
  | E, .app f a => by simp only [elabM, names, names_elabM E f, names_elabM E a]
  | _, .quote _ => rfl
  | _, .ctx _ _ => rfl
  | E, .pquote c => by simp only [elabM, names, names_elabM E c]
  | E, .letP p w b => by simp only [elabM, names, names_elabM E p, names_elabM E w,
      names_elabM E b]
  | E, .alt t₁ t₂ => by simp only [elabM, names, names_elabM E t₁, names_elabM E t₂]

/-- A substitution that can only replace `src fx` does nothing to a term that
does not write `fx`. -/
theorem subst_eq_self_of_not_mem_names {fx : X} : ∀ (t : Tm S X) (θ : Sub S X),
    (∀ n, n ≠ .src fx → θ n = Option.none) → fx ∉ names t → subst θ Sub.none t = t
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .var (.src y), θ, hθ, h => by
      have hy : (Nm.src y : Nm X) ≠ .src fx := by
        intro e
        apply h
        simp only [names, List.mem_singleton]
        cases e
        rfl
      simp [subst, hθ _ hy]
  | .var (.inst ρ m), θ, hθ, _ => by simp [subst, hθ (.inst ρ m) (by simp)]
  | .pvar _, _, _, _ => rfl
  | .lam x own b, θ, hθ, h => by
      simp only [subst, none_hideParam]
      congr 1
      apply subst_eq_self_of_not_mem_names b
      · intro n hn
        unfold Sub.hideOwn
        split
        · rfl
        · exact hθ n hn
      · exact h
  | .app f a, θ, hθ, h => by
      simp only [names, List.mem_append, not_or] at h
      simp only [subst]
      rw [subst_eq_self_of_not_mem_names f θ hθ h.1, subst_eq_self_of_not_mem_names a θ hθ h.2]
  | .quote _, _, _, _ => rfl
  | .ctx _ _, _, _, _ => rfl
  | .pquote c, θ, hθ, h => by
      simp only [subst]
      rw [subst_eq_self_of_not_mem_names c θ hθ h]
  | .letP p w b, θ, hθ, h => by
      simp only [names, List.mem_append, not_or] at h
      simp only [subst]
      rw [subst_eq_self_of_not_mem_names p θ hθ h.1.1,
        subst_eq_self_of_not_mem_names w θ hθ h.1.2,
        subst_eq_self_of_not_mem_names b θ hθ h.2]
  | .alt t₁ t₂, θ, hθ, h => by
      simp only [names, List.mem_append, not_or] at h
      simp only [subst]
      rw [subst_eq_self_of_not_mem_names t₁ θ hθ h.1,
        subst_eq_self_of_not_mem_names t₂ θ hθ h.2]

theorem single_src_ne {fx : X} (t : Tm S X) :
    ∀ n, n ≠ .src fx → (Sub.single (.src fx) t : Sub S X) n = Option.none := by
  intro n hn
  simp [Sub.single, hn]

/-- Inlining a term with no direct names removes `fx` from the direct names
and changes nothing else at that level. -/
theorem direct_subst_single {fx : X} {L : Tm S X} (hL : direct L = []) :
    ∀ t : Tm S X, direct (subst (Sub.single (.src fx) L) Sub.none t) =
      (direct t).filter (fun y => decide (y ≠ fx))
  | .sym _ => rfl
  | .fn _ => rfl
  | .var (.src y) => by
      by_cases hy : y = fx
      · subst hy
        simp [subst, Sub.single, hL, direct]
      · have hne : (Nm.src y : Nm X) ≠ .src fx := by
          intro e
          cases e
          exact hy rfl
        simp [subst, Sub.single, hne, direct, hy]
  | .var (.inst ρ m) => by simp [subst, Sub.single, direct]
  | .pvar _ => rfl
  | .lam _ _ _ => rfl
  | .app f a => by
      simp only [subst, direct, List.filter_append, direct_subst_single hL f,
        direct_subst_single hL a]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by simp only [subst, direct, direct_subst_single hL c]
  | .letP p w b => by
      simp only [subst, direct, List.filter_append, direct_subst_single hL p,
        direct_subst_single hL w, direct_subst_single hL b]
  | .alt t₁ t₂ => by
      simp only [subst, direct, List.filter_append, direct_subst_single hL t₁,
        direct_subst_single hL t₂]

/-- **Text inlining is safe under hygiene (rule M).**  Re-elaborating the
inlined text gives the capture-avoiding substitution of the elaborated
lambda into the elaborated context.  `E` is the context's scope in the `let`
form (where `fx` is quantified), `E'` the same scope after inlining (where
`fx` no longer occurs), and `E₀` the scope at which `L` was elaborated. -/
theorem elabM_inline {fx : X} {L : Tm S X} (hL : direct L = []) (hfL : fx ∉ names L)
    (E₀ : List X) :
    ∀ (C : Tm S X) (E E' : List X), bare C = true → fx ∈ E →
      (∀ y, y ≠ fx → (y ∈ E ↔ y ∈ E')) →
      (∀ y ∈ names L, (y ∈ E ↔ y ∈ E₀)) →
      hygM fx (names L) (elabM E C) = true →
      elabM E' (subst (Sub.single (.src fx) L) Sub.none C) =
        subst (Sub.single (.src fx) (elabM E₀ L)) Sub.none (elabM E C)
  | .sym _, _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _, _ => rfl
  | .var (.src y), E, E', _, _, hEE', hL0, _ => by
      by_cases hy : y = fx
      · subst hy
        simp only [subst, Sub.single, if_true, Option.getD_some, elabM]
        apply elabM_congr
        intro z hz
        have hz' : z ≠ y := fun e => hfL (e ▸ hz)
        exact (hEE' z hz').symm.trans (hL0 z hz)
      · have hne : (Nm.src y : Nm X) ≠ .src fx := by
          intro e
          cases e
          exact hy rfl
        simp [subst, Sub.single, hne, elabM]
  | .var (.inst ρ m), _, _, _, _, _, _, _ => by simp [subst, Sub.single, elabM]
  | .pvar _, _, _, _, _, _, _, _ => rfl
  | .lam x own b, E, E', hbare, hfE, hEE', hL0, hhyg => by
      simp only [bare, Bool.and_eq_true, List.isEmpty_iff] at hbare
      obtain ⟨hown, hbare⟩ := hbare
      subst hown
      have hfown : fx ∉ ownM E b := by
        simp [ownM, List.mem_dedup, hfE]
      have hownEq : ownM E' (subst (Sub.single (.src fx) L) Sub.none b) = ownM E b := by
        unfold ownM
        rw [direct_subst_single hL b, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro y _
        by_cases hy : y = fx
        · subst hy
          simp [hfE]
        · simp [hy, hEE' y hy]
      simp only [elabM, hygM, names_elabM, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq] at hhyg
      obtain ⟨hsite, hhyg⟩ := hhyg
      simp only [subst, Sub.hideOwn_nil, none_hideParam, elabM, hownEq,
        Sub.single_src_hideOwn hfown]
      congr 1
      by_cases hfb : fx ∈ names b
      · have hdisj : ∀ y ∈ ownM E b, y ∉ names L := by
          rcases hsite with h | h
          · exact absurd hfb h
          · exact h
        apply elabM_inline hL hfL E₀ b (ownM E b ++ E) (ownM E b ++ E') hbare
        · exact List.mem_append_right _ hfE
        · intro y hy
          simp only [List.mem_append]
          exact or_congr_right (hEE' y hy)
        · intro y hy
          simp only [List.mem_append]
          have hyo : y ∉ ownM E b := fun h => hdisj y h hy
          simp only [hyo, false_or]
          exact hL0 y hy
        · exact hhyg
      · rw [subst_eq_self_of_not_mem_names b _ (single_src_ne L) hfb,
          subst_eq_self_of_not_mem_names _ _ (single_src_ne _)
            (by rw [names_elabM]; exact hfb)]
        apply elabM_congr
        intro y hy
        have hyf : y ≠ fx := fun e => hfb (e ▸ hy)
        simp only [List.mem_append]
        exact or_congr_right (hEE' y hyf).symm
  | .app f a, E, E', hbare, hfE, hEE', hL0, hhyg => by
      simp only [bare, Bool.and_eq_true] at hbare
      simp only [elabM, hygM, Bool.and_eq_true] at hhyg
      simp only [subst, elabM]
      rw [elabM_inline hL hfL E₀ f E E' hbare.1 hfE hEE' hL0 hhyg.1,
        elabM_inline hL hfL E₀ a E E' hbare.2 hfE hEE' hL0 hhyg.2]
  | .quote _, _, _, _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _, _, _, _ => rfl
  | .pquote c, E, E', hbare, hfE, hEE', hL0, hhyg => by
      simp only [bare] at hbare
      simp only [elabM, hygM] at hhyg
      simp only [subst, elabM]
      rw [elabM_inline hL hfL E₀ c E E' hbare hfE hEE' hL0 hhyg]
  | .letP p w b, E, E', hbare, hfE, hEE', hL0, hhyg => by
      simp only [bare, Bool.and_eq_true] at hbare
      simp only [elabM, hygM, Bool.and_eq_true] at hhyg
      simp only [subst, elabM]
      rw [elabM_inline hL hfL E₀ p E E' hbare.1.1 hfE hEE' hL0 hhyg.1.1,
        elabM_inline hL hfL E₀ w E E' hbare.1.2 hfE hEE' hL0 hhyg.1.2,
        elabM_inline hL hfL E₀ b E E' hbare.2 hfE hEE' hL0 hhyg.2]
  | .alt t₁ t₂, E, E', hbare, hfE, hEE', hL0, hhyg => by
      simp only [bare, Bool.and_eq_true] at hbare
      simp only [elabM, hygM, Bool.and_eq_true] at hhyg
      simp only [subst, elabM]
      rw [elabM_inline hL hfL E₀ t₁ E E' hbare.1 hfE hEE' hL0 hhyg.1,
        elabM_inline hL hfL E₀ t₂ E E' hbare.2 hfE hEE' hL0 hhyg.2]

omit [DecidableEq X] in
/-- The query scope of a `let` that binds `f` to a lambda. -/
theorem direct_letP_lam (fx : X) (x : Nm X) (own : List X) (body C : Tm S X) :
    direct (.letP (.var (.src fx)) (.lam x own body) C) = fx :: direct C := rfl

/-- **Text inlining at the query (rule M).**  For a `let` that binds `f` to a
lambda written in the text, re-elaborating the inlined text equals
substituting the elaborated lambda into the elaborated body, under hygiene. -/
theorem elabTopM_inline (fx : X) (x : Nm X) (body C : Tm S X)
    (hC : bare C = true) (hfL : fx ∉ names body)
    (hhyg : hygM fx (names body)
      (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) = true) :
    elabTopM (subst (Sub.single (.src fx) (.lam x [] body)) Sub.none C) =
      subst (Sub.single (.src fx)
          (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) (.lam x [] body)))
        Sub.none (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) := by
  unfold elabTopM
  rw [direct_letP_lam] at hhyg ⊢
  apply elabM_inline (L := .lam x [] body) rfl hfL _ C (fx :: direct C) _ hC
    List.mem_cons_self
  · intro y hy
    rw [direct_subst_single rfl C]
    simp [hy]
  · intro y _
    exact Iff.rfl
  · exact hhyg

/-- The `let` form elaborates to a `let` of the elaborated lambda. -/
theorem elabTopM_letP_lam (fx : X) (x : Nm X) (body C : Tm S X) :
    elabTopM (.letP (.var (.src fx)) (.lam x [] body) C) =
      .letP (.var (.src fx))
        (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) (.lam x [] body))
        (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) := rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope
