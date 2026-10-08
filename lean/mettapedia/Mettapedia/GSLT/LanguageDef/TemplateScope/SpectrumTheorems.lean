import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Template scope, part 6: general theorems of the spectrum

* `run_store_mono` — **the cone law for the whole evaluator**: under every
  discipline (reference or snapshot) and every elaboration, a run only
  refines the store.  Information grows monotonically (criterion 8).
* `ownRule_tension` — **the 4-versus-5 tension** at the level of ownership.
  The class quantified over is every *annotation-free inferred ownership
  rule*: any function deciding a lambda's own names from its body text and
  the spellings its enclosing scopes write.  No rule of the class has both
  modularity (property 4: what a lambda writes privately it owns, whatever
  same-spelled outsiders the context writes) and annotation-free relational
  closures (property 5: some lambda captures a name it writes).  The class
  is not vacuous: rule M has 5 (`ownRuleM_relational`), the crossing-set-free
  explicit rule has 4 (`ownRuleEC_modular`), and each property alone is
  satisfiable.
* `ownRuleEC_both` — the explicit rule has both, given its list: its ownership
  never depends on the context, and listing a name captures it.
* `elabEC_congr`, `elabLF_congr` — explicit-capture and lexical-fresh
  elaboration read the context only through the names the text itself
  shares (the crossing sets; the names not bound by an enclosing `let` or a
  crossing set).  A closure without a crossing set elaborates identically in
  every context.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## The 4-versus-5 tension, at the level of ownership -/

/-- An annotation-free inferred ownership rule: the own names of a lambda,
from its body text and the spellings written at its enclosing scope levels. -/
abbrev OwnRule (S : Type u) (X : Type v) := Src S X → List X → List X

namespace OwnRule

/-- Property 4 (modularity), ownership form: a name the body writes is owned
exactly when it is owned in the empty context, and with no context every
name the body writes is owned.  Same-spelled outsiders change nothing. -/
def Modular (R : OwnRule S X) : Prop :=
  (∀ body y, y ∈ Src.direct body → y ∈ R body []) ∧
  (∀ body E y, y ∈ Src.direct body → (y ∈ R body E ↔ y ∈ R body []))

/-- Property 5 without annotation: some lambda captures a name it writes. -/
def RelationalClosure (R : OwnRule S X) : Prop :=
  ∃ body E y, y ∈ Src.direct body ∧ y ∉ R body E

end OwnRule

/-- **The tension.**  No annotation-free inferred ownership rule is both
modular and relational. -/
theorem ownRule_tension (R : OwnRule S X) (hmod : R.Modular) : ¬ R.RelationalClosure := by
  rintro ⟨body, E, y, hy, hnot⟩
  exact hnot ((hmod.2 body E y hy).2 (hmod.1 body y hy))

variable [DecidableEq X]

/-- Rule M's ownership. -/
def ownRuleM : OwnRule S X := fun body E => ((Src.direct body).filter fun y => decide (y ∉ E)).dedup

/-- The explicit rule's ownership, given a crossing set. -/
def ownRuleEC (sh : List X) : OwnRule S X :=
  fun body _ => ((Src.direct body ++ Src.sharedUp body).filter fun y => decide (y ∉ sh)).dedup

/-- `elabMS` records `ownRuleM` at each lambda without a crossing set, and the
explicit rule of its crossing set where there is one. -/
theorem elabMS_lam_own (E : List X) (env : REnv X) (pos : Owner) (z : X) (xs : Option (List X))
    (b : Src S X) :
    elabMS E env pos (.lam z xs b) =
      .lam (parName z) ((crossOwn xs (Src.uses b) (ownRuleM b E)).map fun y => (pos ++ [0], y))
        (elabMS (crossOwn xs (Src.uses b) (ownRuleM b E) ++ Src.direct b ++ E)
          (env.update (crossOwn xs (Src.uses b) (ownRuleM b E)) (pos ++ [0])) (pos ++ [0]) b) :=
  rfl

/-- A crossing set gives exactly the explicit rule's ownership, whatever the
profile's default. -/
theorem crossOwn_lam (sh : List X) (b : Src S X) (E dflt : List X) :
    crossOwn (some sh) (Src.uses b) dflt = ownRuleEC sh b E := rfl

/-- `elabEC` records the explicit rule at each lambda: everything its region
uses without a crossing set, `ownRuleEC` of its crossing set otherwise. -/
theorem elabEC_lam_own (env : REnv X) (pos : Owner) (z : X) (xs : Option (List X))
    (b : Src S X) :
    elabEC env pos (.lam z xs b) =
      .lam (parName z) ((crossOwn xs (Src.uses b) (Src.uses b).dedup).map fun y => (pos ++ [0], y))
        (elabEC (env.update (crossOwn xs (Src.uses b) (Src.uses b).dedup) (pos ++ [0]))
          (pos ++ [0]) b) := rfl

/-- Rule M is relational without annotation: an outsider writing the same
spelling turns the lambda's name into a captured one. -/
theorem ownRuleM_relational (y : X) :
    (ownRuleM : OwnRule S X).RelationalClosure :=
  ⟨.sv y, [y], y, by simp [Src.direct], by simp [ownRuleM, List.mem_dedup]⟩

/-- Rule M is not modular. -/
theorem ownRuleM_not_modular (y : X) : ¬ (ownRuleM : OwnRule S X).Modular :=
  fun h => ownRule_tension _ h (ownRuleM_relational y)

/-- The explicit rule without a crossing set is modular. -/
theorem ownRuleEC_modular : (ownRuleEC [] : OwnRule S X).Modular := by
  constructor
  · intro body y hy
    simp [ownRuleEC, List.mem_dedup, hy]
  · intro body E y _
    rfl

/-- The explicit rule, given its list, has both properties: its ownership
does not depend on the context, and a listed name is captured. -/
theorem ownRuleEC_both (sh : List X) :
    (∀ body E E', (ownRuleEC sh : OwnRule S X) body E = ownRuleEC sh body E') ∧
    (∀ (body : Src S X) E y, y ∈ sh → y ∉ ownRuleEC sh body E) := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro body E y hy
  simp [ownRuleEC, List.mem_dedup, hy]

/-! ## Context independence of explicit capture and lexical fresh -/

/-- A used name that a lambda does not own under the explicit default is in
its crossing set. -/
theorem mem_crossing_of_not_mem_crossOwn {xs : Option (List X)} {U : List X} {y : X}
    (hy : y ∈ U) (hown : y ∉ crossOwn xs U U.dedup) : y ∈ xs.getD [] := by
  cases xs with
  | some sh =>
      simp only [crossOwn, List.mem_dedup, List.mem_filter, decide_eq_true_eq, not_and,
        not_not] at hown
      simpa using hown hy
  | none =>
      simp only [crossOwn, List.mem_dedup] at hown
      exact absurd hy hown

/-- The spellings an explicit-capture term resolves in its context: what its
own level writes, what its nested lambdas share, except the fresh names of a
`let` that introduces by its crossing set. -/
def freeEC : Src S X → List X
  | .sv y => [y]
  | .lam _ xs _ => xs.getD []
  | .app f a => freeEC f ++ freeEC a
  | .pquote c => Src.codeSvs c
  | .letS p w b xs =>
      freeEC w ++ (freeEC p ++ freeEC b).filter fun y => decide (y ∉ crossOwn xs (Src.patNames p) [])
  | .unify p w b => freeEC p ++ freeEC w ++ freeEC b
  | .alt t₁ t₂ => freeEC t₁ ++ freeEC t₂
  | .new ys b => (freeEC b).filter fun y => decide (y ∉ ys)
  | .form _ b => freeEC b
  | _ => []

theorem mem_freeEC {y : X} : ∀ {t : Src S X},
    y ∈ freeEC t → y ∈ Src.direct t ∨ y ∈ Src.sharedUp t
  | .sv z, h => by simp [freeEC] at h; simp [Src.direct, h]
  | .lam _ xs _, h => by
      simp only [freeEC] at h
      exact Or.inr (by simpa [Src.sharedUp] using h)
  | .app f a, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [Src.direct, Src.sharedUp, List.mem_append]
      rcases h with h | h
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .pquote _, h => by
      simp only [freeEC] at h
      simp only [Src.direct]
      exact Or.inl h
  | .letS p w b xs, h => by
      simp only [freeEC, List.mem_append, List.mem_filter] at h
      simp only [Src.direct, Src.sharedUp, List.mem_append]
      rcases h with h | ⟨h | h, -⟩
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr (Or.inl (Or.inr h'))
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr (Or.inl (Or.inl h'))
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .unify p w b, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [Src.direct, Src.sharedUp, List.mem_append]
      rcases h with (h | h) | h
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr (Or.inl (Or.inl h'))
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr (Or.inl (Or.inr h'))
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .alt t₁ t₂, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [Src.direct, Src.sharedUp, List.mem_append]
      rcases h with h | h
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr (Or.inl h')
      · rcases mem_freeEC h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inr h')
  | .new ys b, h => by
      simp only [freeEC, List.mem_filter] at h
      simpa [Src.direct, Src.sharedUp] using mem_freeEC h.1
  | .form _ b, h => by
      simp only [freeEC] at h
      rcases mem_freeEC h with h' | h'
      · exact Or.inl (by simp [Src.direct, h'])
      · exact Or.inr (by simp [Src.sharedUp, h'])
  | .sym _, h => by simp [freeEC] at h
  | .fn _, h => by simp [freeEC] at h
  | .par _, h => by simp [freeEC] at h
  | .quote _, h => by simp [freeEC] at h

/-- Code reads a scope environment only at store names the lookup leaves free.
Agreement on every store name of the code is more than that, and it is enough. -/
theorem codeAt_env (env₁ env₂ : REnv X) (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ s : Src S X, (∀ y ∈ Src.codeSvs s, env₁ y = env₂ y) →
      codeAt (some env₁) penv senv pos s = codeAt (some env₂) penv senv pos s
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .sv y, h => by
      simp only [codeAt]
      cases codeLookup senv y with
      | some _ => rfl
      | none => simp [h y (by simp [Src.codeSvs])]
  | .lam z _ b, h => by
      have hb := codeAt_env env₁ env₂ ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b
        (fun y hy => h y (by simpa [Src.codeSvs] using hy))
      simp only [codeAt, hb]
  | .form z b, h => by
      have hb := codeAt_env env₁ env₂ ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b
        (fun y hy => h y hy)
      simp only [codeAt, hb]
  | .app f a, h => by
      have hf := codeAt_env env₁ env₂ penv senv (pos ++ [0]) f
        (fun y hy => h y (List.mem_append_left _ hy))
      have ha := codeAt_env env₁ env₂ penv senv (pos ++ [1]) a
        (fun y hy => h y (List.mem_append_right _ hy))
      simp only [codeAt, hf, ha]
  | .pquote c, h => by
      have hc := codeAt_env env₁ env₂ [] [] [] c (fun y hy => h y (by simpa [Src.codeSvs] using hy))
      simp only [codeAt, hc]
  | .letS p w b _, h => by
      have hp := codeAt_env env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p
        (fun y hy => h y (List.mem_append_left _ (List.mem_append_left _ hy)))
      have hw := codeAt_env env₁ env₂ penv senv (pos ++ [1]) w
        (fun y hy => h y (List.mem_append_left _ (List.mem_append_right _ hy)))
      have hb := codeAt_env env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b
        (fun y hy => h y (List.mem_append_right _ hy))
      simp only [codeAt, hp, hw, hb]
  | .unify p w b, h => by
      have hp := codeAt_env env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p
        (fun y hy => h y (List.mem_append_left _ (List.mem_append_left _ hy)))
      have hw := codeAt_env env₁ env₂ penv senv (pos ++ [1]) w
        (fun y hy => h y (List.mem_append_left _ (List.mem_append_right _ hy)))
      have hb := codeAt_env env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b
        (fun y hy => h y (List.mem_append_right _ hy))
      simp only [codeAt, hp, hw, hb]
  | .alt t₁ t₂, h => by
      have h₁ := codeAt_env env₁ env₂ penv senv (pos ++ [0]) t₁
        (fun y hy => h y (List.mem_append_left _ hy))
      have h₂ := codeAt_env env₁ env₂ penv senv (pos ++ [1]) t₂
        (fun y hy => h y (List.mem_append_right _ hy))
      simp only [codeAt, h₁, h₂]
  | .new _ b, h => by
      have hb := codeAt_env env₁ env₂ penv senv (pos ++ [0]) b
        (fun y hy => h y (by simpa [Src.codeSvs] using hy))
      simp only [codeAt, hb]

/-- **Explicit capture is modular.**  Elaboration reads the environment only
at the names the text shares with its context. -/
theorem elabEC_congr : ∀ (t : Src S X) (env env' : REnv X) (pos : Owner),
    (∀ y ∈ freeEC t, env y = env' y) → elabEC env pos t = elabEC env' pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv y, env, env', _, h => by
      simp only [elabEC, slotVar]
      rw [h y (by simp [freeEC])]
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, env, env', pos, h => by
      simp only [elabEC]
      congr 1
      apply elabEC_congr b
      intro y hy
      unfold REnv.update
      by_cases hown : y ∈ crossOwn xs (Src.uses b) (Src.uses b).dedup
      · simp only [hown, if_true]
      · simp only [hown, if_false]
        apply h
        simp only [freeEC]
        refine mem_crossing_of_not_mem_crossOwn ?_ hown
        rcases mem_freeEC hy with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ h'
  | .app f a, env, env', pos, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [elabEC]
      rw [elabEC_congr f env env' _ (fun y hy => h y (Or.inl hy)),
        elabEC_congr a env env' _ (fun y hy => h y (Or.inr hy))]
  | .quote _, _, _, _, _ => rfl
  | .pquote c, env, env', _, h => by
      simp only [freeEC] at h
      have hc := codeAt_env env env' [] [] [] c h
      simp only [elabEC, hc]
  | .letS p w b xs, env, env', pos, h => by
      simp only [freeEC, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
      have hw := elabEC_congr w env env' (pos ++ [1]) (fun y hy => h y (Or.inl hy))
      simp only [elabEC]
      split
      · next hnil =>
          have hnone : ∀ y, y ∉ crossOwn xs (Src.patNames p) [] := by
            intro y hy
            rw [hnil] at hy
            cases hy
          rw [elabEC_congr p env env' _ (fun y hy => h y (Or.inr ⟨Or.inl hy, hnone y⟩)),
            hw, elabEC_congr b env env' _ (fun y hy => h y (Or.inr ⟨Or.inr hy, hnone y⟩))]
      · next y₀ ys hcons =>
          have hupd : ∀ (o : Owner) y, (y ∈ freeEC p ∨ y ∈ freeEC b) →
              env.update (y₀ :: ys) o y = env'.update (y₀ :: ys) o y := by
            intro o y hy
            unfold REnv.update
            by_cases hmem : y ∈ y₀ :: ys
            · simp [hmem]
            · simp only [hmem, if_false]
              exact h y (Or.inr ⟨hy, by rw [hcons]; exact hmem⟩)
          rw [elabEC_congr p _ _ _ (fun y hy => hupd _ y (Or.inl hy)),
            elabEC_congr b _ _ _ (fun y hy => hupd _ y (Or.inr hy)), hw]
  | .unify p w b, env, env', pos, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [elabEC]
      rw [elabEC_congr p env env' _ (fun y hy => h y (Or.inl (Or.inl hy))),
        elabEC_congr w env env' _ (fun y hy => h y (Or.inl (Or.inr hy))),
        elabEC_congr b env env' _ (fun y hy => h y (Or.inr hy))]
  | .alt t₁ t₂, env, env', pos, h => by
      simp only [freeEC, List.mem_append] at h
      simp only [elabEC]
      rw [elabEC_congr t₁ env env' _ (fun y hy => h y (Or.inl hy)),
        elabEC_congr t₂ env env' _ (fun y hy => h y (Or.inr hy))]
  | .new [] b, env, env', pos, h => by
      simp only [elabEC]
      exact elabEC_congr b env env' _ (fun y hy => h y (by simp [freeEC, hy]))
  | .new (y₀ :: ys) b, env, env', pos, h => by
      simp only [freeEC, List.mem_filter, decide_eq_true_eq] at h
      simp only [elabEC]
      rw [elabEC_congr b (env.update (y₀ :: ys) (pos ++ [0])) (env'.update (y₀ :: ys) (pos ++ [0]))
        _ ?_]
      intro y hy
      unfold REnv.update
      by_cases hm : y ∈ y₀ :: ys
      · simp only [hm, if_true]
      · simp only [hm, if_false]
        exact h y ⟨hy, hm⟩
  | .form _ b, env, env', pos, h => by
      simp only [elabEC, formedLam]
      congr 1
      apply elabEC_congr b
      intro y hy
      unfold REnv.update
      simp only [List.not_mem_nil, if_false]
      exact h y hy

/-- A closure with no crossing set elaborates identically in every context. -/
theorem elabEC_closed_lam (z : X) (b : Src S X) (env env' : REnv X) (pos : Owner) :
    elabEC env pos (.lam z none b) = elabEC env' pos (.lam z none b) :=
  elabEC_congr _ env env' pos (by simp [freeEC])

/-- The spellings a lexical-fresh term resolves in its context, with the
crossing names `cr` in force: those not bound by one of its own `let`
patterns or by a lambda's crossing set. -/
def freeLF : List X → Src S X → List X
  | _, .sv y => [y]
  | cr, .lam _ xs b =>
      (freeLF (crossIn xs (crossOwn xs (Src.uses b) []) cr) b).filter fun y =>
        decide (y ∉ crossOwn xs (Src.uses b) [])
  | cr, .app f a => freeLF cr f ++ freeLF cr a
  | _, .pquote c => Src.codeSvs c
  | cr, .letS p w b xs =>
      freeLF cr w ++ ((freeLF (crossIn xs (lfIntro xs p cr) cr) p ++
        freeLF (crossIn xs (lfIntro xs p cr) cr) b).filter fun y => decide (y ∉ lfIntro xs p cr))
  | cr, .unify p w b => freeLF cr p ++ freeLF cr w ++ freeLF cr b
  | cr, .alt t₁ t₂ => freeLF cr t₁ ++ freeLF cr t₂
  | cr, .new [] b => freeLF cr b
  | cr, .new (y₀ :: ys) b =>
      (freeLF (cr.filter fun y => decide (y ∉ y₀ :: ys)) b).filter fun y => decide (y ∉ y₀ :: ys)
  | cr, .form _ b => freeLF cr b
  | _, _ => []

/-- **Lexical fresh is modular.**  Elaboration reads the environment only at
the names the text does not bind itself. -/
theorem elabLF_congr : ∀ (t : Src S X) (env env' : REnv X) (cr : List X) (pos : Owner),
    (∀ y ∈ freeLF cr t, env y = env' y) → elabLF env cr pos t = elabLF env' cr pos t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv y, env, env', _, _, h => by
      simp only [elabLF, slotVar]
      rw [h y (by simp [freeLF])]
  | .par _, _, _, _, _, _ => rfl
  | .lam z xs b, env, env', cr, pos, h => by
      simp only [elabLF]
      congr 1
      apply elabLF_congr b
      intro y hy
      unfold REnv.update
      by_cases hown : y ∈ crossOwn xs (Src.uses b) []
      · simp only [hown, if_true]
      · simp only [hown, if_false]
        exact h y (by simp only [freeLF, List.mem_filter, decide_eq_true_eq]; exact ⟨hy, hown⟩)
  | .app f a, env, env', cr, pos, h => by
      simp only [freeLF, List.mem_append] at h
      simp only [elabLF]
      rw [elabLF_congr f env env' cr _ (fun y hy => h y (Or.inl hy)),
        elabLF_congr a env env' cr _ (fun y hy => h y (Or.inr hy))]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote c, env, env', _, _, h => by
      simp only [freeLF] at h
      have hc := codeAt_env env env' [] [] [] c h
      simp only [elabLF, hc]
  | .letS p w b xs, env, env', cr, pos, h => by
      simp only [freeLF, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
      have hw := elabLF_congr w env env' cr (pos ++ [1]) (fun y hy => h y (Or.inl hy))
      simp only [elabLF]
      split
      · next hnil =>
          rw [hnil] at h
          rw [elabLF_congr p env env' _ _ (fun y hy => h y (Or.inr ⟨Or.inl hy, by simp⟩)),
            hw, elabLF_congr b env env' _ _ (fun y hy => h y (Or.inr ⟨Or.inr hy, by simp⟩))]
      · next y₀ ys hcons =>
          rw [hcons] at h
          have hupd : ∀ (o : Owner) y, (y ∈ freeLF (crossIn xs (y₀ :: ys) cr) p ∨
              y ∈ freeLF (crossIn xs (y₀ :: ys) cr) b) →
              env.update (y₀ :: ys) o y = env'.update (y₀ :: ys) o y := by
            intro o y hy
            unfold REnv.update
            by_cases hmem : y ∈ y₀ :: ys
            · simp [hmem]
            · simp only [hmem, if_false]
              exact h y (Or.inr ⟨hy, hmem⟩)
          rw [elabLF_congr p _ _ _ _ (fun y hy => hupd _ y (Or.inl hy)),
            elabLF_congr b _ _ _ _ (fun y hy => hupd _ y (Or.inr hy)), hw]
  | .unify p w b, env, env', cr, pos, h => by
      simp only [freeLF, List.mem_append] at h
      simp only [elabLF]
      rw [elabLF_congr p env env' cr _ (fun y hy => h y (Or.inl (Or.inl hy))),
        elabLF_congr w env env' cr _ (fun y hy => h y (Or.inl (Or.inr hy))),
        elabLF_congr b env env' cr _ (fun y hy => h y (Or.inr hy))]
  | .alt t₁ t₂, env, env', cr, pos, h => by
      simp only [freeLF, List.mem_append] at h
      simp only [elabLF]
      rw [elabLF_congr t₁ env env' cr _ (fun y hy => h y (Or.inl hy)),
        elabLF_congr t₂ env env' cr _ (fun y hy => h y (Or.inr hy))]
  | .new [] b, env, env', cr, pos, h => by
      simp only [freeLF] at h
      simp only [elabLF]
      exact elabLF_congr b env env' cr _ h
  | .new (y₀ :: ys) b, env, env', cr, pos, h => by
      simp only [freeLF, List.mem_filter, decide_eq_true_eq] at h
      simp only [elabLF]
      rw [elabLF_congr b (env.update (y₀ :: ys) (pos ++ [0])) (env'.update (y₀ :: ys) (pos ++ [0]))
        _ _ ?_]
      intro y hy
      unfold REnv.update
      by_cases hm : y ∈ y₀ :: ys
      · simp only [hm, if_true]
      · simp only [hm, if_false]
        exact h y ⟨hy, hm⟩
  | .form _ b, env, env', cr, pos, h => by
      simp only [elabLF, formedLam]
      congr 1
      apply elabLF_congr b
      intro y hy
      unfold REnv.update
      simp only [List.not_mem_nil, if_false]
      exact h y hy

/-! ## The cone law for the evaluator -/

variable [DecidableEq S] [CodeId X]

theorem matchT_mono : ∀ (p t : Tm S X) (σ σ' : GStore S X),
    matchT σ p t = some σ' → σ ⊑ σ'
  | .var n, t, σ, σ', h => by
      simp only [matchT] at h
      cases hg : t.toGVal? with
      | none => rw [hg] at h; cases h
      | some g => rw [hg] at h; exact refineStep_mono h
  | .app p₁ p₂, t, σ, σ', h => by
      cases t with
      | app t₁ t₂ =>
          simp only [matchT] at h
          cases h₁ : matchT σ p₁ t₁ with
          | none => rw [h₁] at h; cases h
          | some σ₁ =>
              rw [h₁] at h
              exact (matchT_mono p₁ t₁ σ σ₁ h₁).trans (matchT_mono p₂ t₂ σ₁ σ' h)
      | _ =>
          simp only [matchT] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
  | .pquote pc, t, σ, σ', h => by
      cases t with
      | quote c =>
          simp only [matchT] at h
          exact matchCode_mono pc c σ σ' h
      | _ =>
          simp only [matchT] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
  | .quote c₁, t, σ, σ', h => by
      cases t with
      | quote c₂ =>
          simp only [matchT] at h
          cases hce : codeEq c₁ c₂ with
          | true =>
              simp only [hce] at h
              injection h with h; subst h; exact Store.LE.refl σ
          | false => simp [hce] at h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchT] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
  | .sym _, t, σ, σ', h | .fn _, t, σ, σ', h | .pvar _, t, σ, σ', h
  | .lam _ _ _, t, σ, σ', h | .letP _ _ _, t, σ, σ', h
  | .ctx _ _, t, σ, σ', h | .alt _ _, t, σ, σ', h => by
      simp only [matchT] at h
      split at h
      · injection h with h; subst h; exact Store.LE.refl σ
      · cases h

omit [CodeId X] in
theorem bindAll_mem {α β : Type*} {g : α → Option (List β)} :
    ∀ (l : List α) (L : List β), bindAll l g = some L →
      ∀ x ∈ L, ∃ a ∈ l, ∃ M, g a = some M ∧ x ∈ M
  | [], L, h, x, hx => by
      simp only [bindAll] at h
      injection h with h
      subst h
      cases hx
  | a :: as, L, h, x, hx => by
      unfold bindAll at h
      cases hga : g a with
      | none => rw [hga] at h; cases h
      | some l =>
          cases hrest : bindAll as g with
          | none => rw [hga, hrest] at h; cases h
          | some r =>
              rw [hga, hrest] at h
              injection h with h
              subst h
              rcases List.mem_append.mp hx with hx | hx
              · exact ⟨a, List.mem_cons_self, l, hga, hx⟩
              · obtain ⟨b, hb, M, hgb, hxM⟩ := bindAll_mem as r hrest x hx
                exact ⟨b, List.mem_cons_of_mem a hb, M, hgb, hxM⟩

omit [CodeId X] in
theorem bindOpt_mem {α β : Type*} {o : Option (List α)} {g : α → Option (List β)}
    {L : List β} (h : bindOpt o g = some L) {x : β} (hx : x ∈ L) :
    ∃ l, o = some l ∧ ∃ a ∈ l, ∃ M, g a = some M ∧ x ∈ M := by
  cases ho : o with
  | none => rw [ho] at h; cases h
  | some l =>
      rw [ho] at h
      exact ⟨l, rfl, bindAll_mem l L h x hx⟩

/-- A runner only refines the store. -/
def Runner.Grows (r : Runner S X) : Prop :=
  ∀ π σ t L, r π σ t = some L → ∀ x ∈ L, σ ⊑ x.2

theorem step_grows (d : Disc) (prog : S → Option (Tm S X)) {r : Runner S X}
    (hr : Runner.Grows r) : Runner.Grows (step d prog r) := by
  intro π σ t L hL x hx
  cases t with
  | fn F =>
      simp only [step] at hL
      cases hp : prog F with
      | none =>
          rw [hp] at hL
          injection hL with hL
          subst hL
          simp only [List.mem_singleton] at hx
          subst hx
          exact Store.LE.refl σ
      | some e => rw [hp] at hL; exact hr _ _ _ _ hL x hx
  | app f a =>
      simp only [step] at hL
      obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem hL hx
      obtain ⟨l₂, hl₂, r₂, hr₂, M₂, hM₂, hx₂⟩ := bindOpt_mem hM₁ hx₁
      have h₁ : σ ⊑ r₁.2 := hr _ _ _ _ hl₁ r₁ hr₁
      have h₂ : r₁.2 ⊑ r₂.2 := hr _ _ _ _ hl₂ r₂ hr₂
      cases r₁ with
      | mk fv σ₁ =>
          cases fv with
          | lam y own body =>
              exact h₁.trans (h₂.trans (hr _ _ _ _ hM₂ x hx₂))
          | _ =>
              simp only at hM₂
              injection hM₂ with hM₂
              subst hM₂
              simp only [List.mem_singleton] at hx₂
              subst hx₂
              exact h₁.trans h₂
  | letP p w b =>
      simp only [step] at hL
      cases hl : letLam? p w with
      | some f => rw [hl] at hL; exact hr _ _ _ _ hL x hx
      | none =>
          rw [hl] at hL
          simp only at hL
          obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem hL hx
          have h₁ : σ ⊑ r₁.2 := hr _ _ _ _ hl₁ r₁ hr₁
          cases hg : (act r₁.2 r₁.1).toGVal? with
          | some g =>
              rw [hg] at hM₁
              simp only at hM₁
              cases hm : matchT r₁.2 p g.toTm with
              | some σ₂ =>
                  rw [hm] at hM₁
                  exact h₁.trans ((matchT_mono _ _ _ _ hm).trans (hr _ _ _ _ hM₁ x hx₁))
              | none =>
                  rw [hm] at hM₁
                  injection hM₁ with hM₁
                  subst hM₁
                  cases hx₁
          | none =>
              rw [hg] at hM₁
              simp only at hM₁
              cases p with
              | var f => exact h₁.trans (hr _ _ _ _ hM₁ x hx₁)
              | _ =>
                  injection hM₁ with hM₁
                  subst hM₁
                  cases hx₁
  | alt t₁ t₂ =>
      simp only [step] at hL
      cases h₁ : r (π ++ [0]) σ t₁ with
      | none => rw [h₁] at hL; cases hL
      | some l =>
          cases h₂ : r (π ++ [1]) σ t₂ with
          | none => rw [h₁, h₂] at hL; cases hL
          | some m =>
              rw [h₁, h₂] at hL
              injection hL with hL
              subst hL
              rcases List.mem_append.mp hx with hx | hx
              · exact hr _ _ _ _ h₁ x hx
              · exact hr _ _ _ _ h₂ x hx
  | sym s | var n | pvar y | lam y own body | quote c | ctx _ _ | pquote c =>
      simp only [step] at hL
      injection hL with hL
      subst hL
      simp only [List.mem_singleton] at hx
      subst hx
      exact Store.LE.refl σ

theorem run_grows (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, Runner.Grows (run d prog n)
  | 0 => fun _ _ _ _ h => by cases h
  | n + 1 => step_grows d prog (run_grows d prog n)

/-- **The cone law for the evaluator.**  Every result store refines the
initial store, under every discipline and every elaboration. -/
theorem run_store_mono (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {σ : GStore S X} {t : Tm S X} {L : Result S X} (h : run d prog n π σ t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) : σ ⊑ x.2 :=
  run_grows d prog n π σ t L h x hx

end Mettapedia.GSLT.LanguageDef.TemplateScope
