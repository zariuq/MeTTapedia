import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumTheorems

/-!
# Template scope: the cone law, as an instance of the sequential binding discipline

`SequentialBindingDiscipline` (8/07) proves its laws for `refineRun`, the
sequential refinement of a ground store by a list of binding steps.  This
module shows that every store the evaluator produces is such a run, so the
8/07 laws apply to every elaborated program, lexical fresh included.

* `matchT_eq_refineRun` — **a pattern match is a refinement run**: matching a
  pattern against a value is `refineRun` of the bindings the match demands
  (`matchSteps`).  This covers `let`, `unify`, and the names a crossing set
  shares: each binds a slot that is unbound or already holds the same value,
  and fails on a conflict.
* `run_refineRun` — **every result store is reached by refinement**: for every
  discipline, program, fuel, path, store and term, each result's store is
  `refineRun` of some list of binding steps from the initial store.
* Instances of the 8/07 laws (`run_forwardCone`, `run_preserves_binding`,
  `run_empty_conjunction`, `run_empty_perm`): every result store lies in the
  forward cone of the initial store; a binding, once made, is never changed;
  from the empty store a result store is the conjunction of its binding steps,
  and permuting the steps changes nothing.

Lexical fresh never overwrites a slot: a pattern that would rebind a name
introduces a new slot (another identity), and a shared or `unify` pattern
refines.  Neither is the 8/07 shadow step (`shadowStep`), which this
evaluator never performs.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v} [DecidableEq S] [DecidableEq X] [CodeId X]

/-- **The binding steps a match demands**: a store-name hole binds the ground
value it meets; data is matched component by component, left to right; a
pattern quotation is matched as code; two quotations are the same code when
`codeEq` holds; anything else must be equal and demands nothing.  `none` when
the shapes do not match. -/
def matchSteps : Tm S X → Tm S X → Option (Steps (Nm X) (GVal S X))
  | .var n, t => t.toGVal?.map fun g => [(n, g)]
  | .app p₁ p₂, .app t₁ t₂ =>
      (matchSteps p₁ t₁).bind fun s₁ => (matchSteps p₂ t₂).map fun s₂ => s₁ ++ s₂
  | .pquote pc, .quote c => matchCodeSteps pc c
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some [] else none
  | p, t => if p = t then some [] else none

omit [CodeId X] in
theorem refineRun_single (σ : GStore S X) (n : Nm X) (g : GVal S X) :
    refineRun σ [(n, g)] = refineStep σ (n, g) := by
  rw [refineRun_cons]
  cases refineStep σ (n, g) <;> rfl

/-- **A pattern match is a refinement run** of the bindings it demands. -/
theorem matchT_eq_refineRun : ∀ (p t : Tm S X) (σ : GStore S X),
    matchT σ p t = (matchSteps p t).bind (refineRun σ)
  | .var n, t, σ => by
      simp only [matchT, matchSteps]
      cases t.toGVal? with
      | none => rfl
      | some g => simp [refineRun_single]
  | .app p₁ p₂, .app t₁ t₂, σ => by
      simp only [matchT, matchSteps]
      rw [matchT_eq_refineRun p₁ t₁ σ]
      cases h₁ : matchSteps p₁ t₁ with
      | none => rfl
      | some s₁ =>
          simp only [Option.bind_some]
          cases h₂ : matchSteps p₂ t₂ with
          | none =>
              simp only [Option.map_none, Option.bind_none]
              cases refineRun σ s₁ with
              | none => rfl
              | some σ' => simp [matchT_eq_refineRun p₂ t₂ σ', h₂]
          | some s₂ =>
              simp only [Option.map_some, Option.bind_some, refineRun_append]
              cases refineRun σ s₁ with
              | none => rfl
              | some σ' => simp [matchT_eq_refineRun p₂ t₂ σ', h₂]
  | .pquote pc, .quote c, σ => by
      simp only [matchT, matchSteps]
      exact matchCode_eq_refineRun pc c σ
  | .quote c₁, .quote c₂, σ => by
      simp only [matchT, matchSteps]
      cases codeEq c₁ c₂ with
      | true =>
          rw [if_pos rfl, if_pos rfl, Option.bind_some, refineRun_nil]
      | false =>
          simp only [Bool.false_eq_true, if_false, Option.bind_none]
  | .app _ _, .sym _, σ | .app _ _, .fn _, σ | .app _ _, .var _, σ | .app _ _, .pvar _, σ
  | .app _ _, .lam _ _ _, σ | .app _ _, .quote _, σ | .app _ _, .pquote _, σ
  | .app _ _, .letP _ _ _, σ | .app _ _, .alt _ _, σ | .app _ _, .ctx _ _, σ
  | .pquote _, .sym _, σ | .pquote _, .fn _, σ | .pquote _, .var _, σ | .pquote _, .pvar _, σ
  | .pquote _, .lam _ _ _, σ | .pquote _, .app _ _, σ | .pquote _, .pquote _, σ
  | .pquote _, .letP _ _ _, σ | .pquote _, .alt _ _, σ | .pquote _, .ctx _ _, σ
  | .quote _, .sym _, σ | .quote _, .fn _, σ | .quote _, .var _, σ | .quote _, .pvar _, σ
  | .quote _, .lam _ _ _, σ | .quote _, .app _ _, σ | .quote _, .pquote _, σ
  | .quote _, .letP _ _ _, σ | .quote _, .alt _ _, σ | .quote _, .ctx _ _, σ
  | .sym _, _, σ | .fn _, _, σ | .pvar _, _, σ | .lam _ _ _, _, σ
  | .letP _ _ _, _, σ | .alt _ _, _, σ | .ctx _ _, _, σ => by
      simp only [matchT, matchSteps]
      split <;> rfl

/-- A runner whose every result store is reached by refinement. -/
def Runner.Refines (r : Runner S X) : Prop :=
  ∀ π σ t L, r π σ t = some L → ∀ x ∈ L, ∃ steps, refineRun σ steps = some x.2

omit [CodeId X] in
theorem refineRun_trans {σ τ υ : GStore S X} {s₁ s₂ : Steps (Nm X) (GVal S X)}
    (h₁ : refineRun σ s₁ = some τ) (h₂ : refineRun τ s₂ = some υ) :
    refineRun σ (s₁ ++ s₂) = some υ := by
  rw [refineRun_append, h₁]
  exact h₂

theorem step_refines (d : Disc) (prog : S → Option (Tm S X)) {r : Runner S X}
    (hr : Runner.Refines r) : Runner.Refines (step d prog r) := by
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
          exact ⟨[], rfl⟩
      | some e => rw [hp] at hL; exact hr _ _ _ _ hL x hx
  | app f a =>
      simp only [step] at hL
      obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem hL hx
      obtain ⟨l₂, hl₂, r₂, hr₂, M₂, hM₂, hx₂⟩ := bindOpt_mem hM₁ hx₁
      obtain ⟨s₁, h₁⟩ := hr _ _ _ _ hl₁ r₁ hr₁
      obtain ⟨s₂, h₂⟩ := hr _ _ _ _ hl₂ r₂ hr₂
      cases r₁ with
      | mk fv σ₁ =>
          cases fv with
          | lam y own body =>
              obtain ⟨s₃, h₃⟩ := hr _ _ _ _ hM₂ x hx₂
              exact ⟨s₁ ++ s₂ ++ s₃, refineRun_trans (refineRun_trans h₁ h₂) h₃⟩
          | _ =>
              simp only at hM₂
              injection hM₂ with hM₂
              subst hM₂
              simp only [List.mem_singleton] at hx₂
              subst hx₂
              exact ⟨s₁ ++ s₂, refineRun_trans h₁ h₂⟩
  | letP p w b =>
      simp only [step] at hL
      cases hl : letLam? p w with
      | some f => rw [hl] at hL; exact hr _ _ _ _ hL x hx
      | none =>
          rw [hl] at hL
          simp only at hL
          obtain ⟨l₁, hl₁, r₁, hr₁, M₁, hM₁, hx₁⟩ := bindOpt_mem hL hx
          obtain ⟨s₁, h₁⟩ := hr _ _ _ _ hl₁ r₁ hr₁
          cases hg : (act r₁.2 r₁.1).toGVal? with
          | some g =>
              rw [hg] at hM₁
              simp only at hM₁
              cases hm : matchT r₁.2 p g.toTm with
              | some σ₂ =>
                  rw [hm] at hM₁
                  rw [matchT_eq_refineRun] at hm
                  cases hs : matchSteps p g.toTm with
                  | none => rw [hs] at hm; cases hm
                  | some sm =>
                      rw [hs] at hm
                      obtain ⟨s₃, h₃⟩ := hr _ _ _ _ hM₁ x hx₁
                      exact ⟨s₁ ++ sm ++ s₃, refineRun_trans (refineRun_trans h₁ hm) h₃⟩
              | none =>
                  rw [hm] at hM₁
                  injection hM₁ with hM₁
                  subst hM₁
                  cases hx₁
          | none =>
              rw [hg] at hM₁
              simp only at hM₁
              cases p with
              | var f =>
                  obtain ⟨s₃, h₃⟩ := hr _ _ _ _ hM₁ x hx₁
                  exact ⟨s₁ ++ s₃, refineRun_trans h₁ h₃⟩
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
      exact ⟨[], rfl⟩

theorem run_refines (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, Runner.Refines (run d prog n)
  | 0 => fun _ _ _ _ h => by cases h
  | n + 1 => step_refines d prog (run_refines d prog n)

/-- **Every result store is reached by refinement**: it is `refineRun` of some
list of binding steps from the initial store, under every discipline and every
elaboration. -/
theorem run_refineRun (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {σ : GStore S X} {t : Tm S X} {L : Result S X} (h : run d prog n π σ t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) : ∃ steps, refineRun σ steps = some x.2 :=
  run_refines d prog n π σ t L h x hx

omit [CodeId X] in
/-- A refinement run is a path of single refinement steps. -/
theorem refineRun_reaches : ∀ {σ τ : GStore S X} (steps : Steps (Nm X) (GVal S X)),
    refineRun σ steps = some τ → Mettapedia.Machines.Reaches RefinesOne σ τ
  | σ, τ, [], h => by
      injection h with h
      subst h
      exact Relation.ReflTransGen.refl
  | σ, τ, p :: rest, h => by
      rw [refineRun_cons] at h
      cases hs : refineStep σ p with
      | none => rw [hs] at h; cases h
      | some σ' =>
          rw [hs] at h
          exact Relation.ReflTransGen.head ⟨p, hs⟩ (refineRun_reaches rest h)

/-- **The cone law, as an instance.**  Every result store lies in the forward
(production) cone of the initial store under single refinement steps. -/
theorem run_forwardCone (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {σ : GStore S X} {t : Tm S X} {L : Result S X} (h : run d prog n π σ t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) :
    x.2 ∈ Mettapedia.Machines.forwardCone RefinesOne ({σ} : Set (GStore S X)) := by
  obtain ⟨steps, hs⟩ := run_refineRun d prog h hx
  exact ⟨σ, rfl, refineRun_reaches steps hs⟩

/-- **No binding is ever changed** (8/07 `futureCone_preserves_binding`): a slot
the initial store binds holds the same value in every result store.  This is
"never overwrite". -/
theorem run_preserves_binding (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {σ : GStore S X} {t : Tm S X} {L : Result S X} (h : run d prog n π σ t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) {k : Nm X} {g : GVal S X} (hk : σ k = some g) :
    x.2 k = some g :=
  futureCone_preserves_binding (run_forwardCone d prog h hx) hk

/-- **Compositionality, as an instance** (8/07 `refineRun_empty_eq_solveConj`):
from the empty store, a result store is the conjunction of its binding steps:
they are consistent, and the store holds exactly their first-asserted values. -/
theorem run_empty_conjunction (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {t : Tm S X} {L : Result S X} (h : run d prog n π Store.empty t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) :
    ∃ steps, solveConj steps = some x.2 := by
  obtain ⟨steps, hs⟩ := run_refineRun d prog h hx
  exact ⟨steps, (refineRun_empty_eq_solveConj steps).symm.trans hs⟩

/-- **Order independence, as an instance** (8/07 `solveConj_perm`): any
reordering of a result's binding steps yields the same store. -/
theorem run_empty_perm (d : Disc) (prog : S → Option (Tm S X)) {n : ℕ} {π : Path}
    {t : Tm S X} {L : Result S X} (h : run d prog n π Store.empty t = some L)
    {x : Tm S X × GStore S X} (hx : x ∈ L) :
    ∃ steps, refineRun Store.empty steps = some x.2 ∧
      ∀ steps', steps'.Perm steps → refineRun Store.empty steps' = some x.2 := by
  obtain ⟨steps, hs⟩ := run_refineRun d prog h hx
  refine ⟨steps, hs, fun steps' hp => ?_⟩
  rw [refineRun_empty_eq_solveConj, solveConj_perm hp, ← refineRun_empty_eq_solveConj]
  exact hs

end Mettapedia.GSLT.LanguageDef.TemplateScope
