import Mathlib.Data.List.Induction
import Mettapedia.GSLT.LanguageDef.TemplateScope.Elaboration

/-!
# Template scope, part 3: activation and the relational answer semantics

The evaluator is a fuel-indexed function returning a bag of results (a list
of result terms with their final ground stores); `none` means the fuel ran
out.  Answers are fuel-independent once defined (`run_mono`), so they form a
relational semantics: `AnswerBag d prog t bag`.

* The environment is applied lazily: a store-name occurrence evaluates to
  itself; the store is consulted when a `let` matches and at the answer,
  where the final store is applied (`act`).
* A `let` whose value is a lambda written in place is performed by
  substitution of that lambda into the body, at the same path: the evaluator
  itself performs `C[f := L]`.  A ground value refines the store (8/07).  A
  non-ground value bound to a single name is substituted into the body: the
  ground model has no aliasing, so a name bound this way is not visible
  outside the `let` body.
* Activation (`activate`) depends on the discipline:
  * `static` renames the lambda's recorded own names to fresh copies tagged
    by the activation path, and instantiates the parameter.  Rules M and A
    are `static` evaluation of `elabTopM` and `elabTopA` elaborations.
  * `copyAtCall` (rule B, HE's `sealed`, yall's `copy_term`) copies every
    store name of the body that is unbound in the store at the call.

## Main results

* `run_mono` — fuel monotonicity; `AnswerBag.unique`.
* `run_letP_lam` — the evaluator's `let` of a lambda is the substitution.
* `run_lifted_call` — **Theorem 1 (lifting)**: calling the lambda-lifted
  equation equals applying the lambda, on the whole observation (bag of
  results with final stores), for any arguments.
* `lifted_closed` — the lifted equation has no free store names.
* `run_elabTopM_inline` — **Theorem 2 (inlining)** at the query, under the
  hygiene hypothesis of `elabTopM_inline`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v} [DecidableEq S] [DecidableEq X]

/-- Activation disciplines. -/
inductive Disc where
  /-- Rename the lambda's recorded own names per activation (rules M, A). -/
  | static
  /-- Rule B: copy every store name unbound at the call. -/
  | copyAtCall
  deriving DecidableEq, Repr

/-- Fresh copies of a lambda's own names, tagged by the activation path. -/
def renameOwn (ρ : Path) (own : List X) : Sub S X :=
  fun n => if ownKey own n then some (.var (.inst ρ n)) else Option.none

/-- Rule B's renaming: every name unbound in the store at the call. -/
def copyUnbound (σ : GStore S X) (ρ : Path) : Sub S X :=
  fun n => match σ n with
    | Option.none => some (.var (.inst ρ n))
    | some _ => Option.none

/-- Activation of `lam x own body` on the argument `arg`, at path `ρ`. -/
def activate (d : Disc) (σ : GStore S X) (ρ : Path) (x : Nm X) (own : List X)
    (body arg : Tm S X) : Tm S X :=
  match d with
  | .static => subst (renameOwn ρ own) (Sub.single x arg) body
  | .copyAtCall => subst (copyUnbound σ ρ) (Sub.single x arg) body

/-- How names are compared inside code.  The default compares them as written.
A model whose quoted binders carry positions supplies its own comparison:
bound names by position, free names by identity, and a store-name hole stays
a hole. -/
class CodeId (X : Type v) where
  same : Nm X → Nm X → Bool
  hole : Nm X → Bool

instance : CodeId X where
  same a b := decide (a = b)
  hole _ := true

variable [CodeId X]

/-- Equality of code: bound names by the model's identity, free names by the
model's identity, structure otherwise.  A hole is not bound here; matching
binds it. -/
def codeEq : Tm S X → Tm S X → Bool
  | .sym s₁, .sym s₂ => decide (s₁ = s₂)
  | .fn F₁, .fn F₂ => decide (F₁ = F₂)
  | .var n₁, .var n₂ => CodeId.same n₁ n₂
  | .pvar x₁, .pvar x₂ => CodeId.same x₁ x₂
  | .lam x₁ own₁ b₁, .lam x₂ own₂ b₂ =>
      CodeId.same x₁ x₂ && decide (own₁ = own₂) && codeEq b₁ b₂
  | .app f₁ a₁, .app f₂ a₂ => codeEq f₁ f₂ && codeEq a₁ a₂
  | .quote c₁, .quote c₂ => codeEq c₁ c₂
  | .pquote c₁, .pquote c₂ => codeEq c₁ c₂
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      codeEq p₁ p₂ && codeEq w₁ w₂ && codeEq b₁ b₂
  | .alt t₁ u₁, .alt t₂ u₂ => codeEq t₁ t₂ && codeEq u₁ u₂
  | _, _ => false

/-- A code binder `k` occurs free in `t`. Quotations are sealed. A lambda
binder that `CodeId` identifies with `k` hides `k` in its body. -/
def mentionsBinder (k : Nm X) : Tm S X → Bool
  | .pvar y => CodeId.same k y
  | .lam x _ b => !CodeId.same k x && mentionsBinder k b
  | .app f a => mentionsBinder k f || mentionsBinder k a
  | .letP p w b => mentionsBinder k p || mentionsBinder k w || mentionsBinder k b
  | .alt a b => mentionsBinder k a || mentionsBinder k b
  | .pquote c => mentionsBinder k c
  | _ => false

/-- Binders of `bound` that `t` mentions, outermost first. -/
def mentioned (bound : List (Nm X)) (t : Tm S X) : List (Nm X) :=
  bound.filter (fun k => mentionsBinder k t)

/-- The value a hole takes under code binders `bound`. No mentioned binder:
the ground value, as before. Otherwise contextual code over those binders. -/
def contextualVal (bound : List (Nm X)) (t : Tm S X) : Option (GVal S X) :=
  match mentioned bound t with
  | [] => t.toGVal?
  | ks => some (.ctx ks t)

/-- Substitute the code binder `k`, compared by `CodeId`. A quotation stays
sealed; a lambda that binds `k` hides it. -/
def substBinder (k : Nm X) (v : Tm S X) : Tm S X → Tm S X
  | .pvar y => if CodeId.same k y then v else .pvar y
  | .lam x own b =>
      if CodeId.same k x then .lam x own b else .lam x own (substBinder k v b)
  | .app f a => .app (substBinder k v f) (substBinder k v a)
  | .letP p w b =>
      .letP (substBinder k v p) (substBinder k v w) (substBinder k v b)
  | .alt a b => .alt (substBinder k v a) (substBinder k v b)
  | .pquote c => .pquote (substBinder k v c)
  | .ctx ks c => .ctx ks (substBinder k v c)
  | t => t

/-- `lift let`: fill binder `k` with a closed term. Contextual code drops `k`
and, once no binder remains, is the body. The filler is also applied under
application, `let` and `alt`, so an answer wrapped around contextual code
fills. -/
def liftLet (k : Nm X) (v : Tm S X) : Tm S X → Tm S X
  | .ctx ks body =>
      let ks' := ks.filter (fun x => !CodeId.same k x)
      let body' :=
        if ks.any (fun x => CodeId.same k x) then substBinder k v body else body
      match ks' with
      | [] => body'
      | ks' => .ctx ks' body'
  | .app f a => .app (liftLet k v f) (liftLet k v a)
  | .letP p w b => .letP (liftLet k v p) (liftLet k v w) (liftLet k v b)
  | .alt a b => .alt (liftLet k v a) (liftLet k v b)
  | t => t

/-- Match inside a quotation, under code binders `bound` (outermost first).
A store-name hole binds `contextualVal`: a ground value when the part mentions
none of `bound`, and contextual code otherwise. A binder of the code is
compared by `CodeId`. Anything bound by the code is not a hole. -/
def matchCodeIn (σ : GStore S X) (bound : List (Nm X)) :
    Tm S X → Tm S X → Option (GStore S X)
  | .var n, t =>
      if CodeId.hole n then
        match contextualVal bound t with
        | some g => refineStep σ (n, g)
        | Option.none => Option.none
      else
        match t with
        | .var m => if CodeId.same n m then some σ else Option.none
        | _ => Option.none
  | .pvar x, .pvar y => if CodeId.same x y then some σ else Option.none
  | .lam x₁ own₁ b₁, .lam x₂ own₂ b₂ =>
      if CodeId.same x₁ x₂ && decide (own₁ = own₂) then
        matchCodeIn σ (bound ++ [x₂]) b₁ b₂
      else Option.none
  | .app p₁ p₂, .app t₁ t₂ =>
      match matchCodeIn σ bound p₁ t₁ with
      | some σ' => matchCodeIn σ' bound p₂ t₂
      | Option.none => Option.none
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      match matchCodeIn σ bound p₁ p₂ with
      | some σ₁ =>
          match matchCodeIn σ₁ bound w₁ w₂ with
          | some σ₂ => matchCodeIn σ₂ bound b₁ b₂
          | Option.none => Option.none
      | Option.none => Option.none
  | .alt p₁ p₂, .alt t₁ t₂ =>
      match matchCodeIn σ bound p₁ t₁ with
      | some σ' => matchCodeIn σ' bound p₂ t₂
      | Option.none => Option.none
  | .sym s₁, .sym s₂ => if s₁ = s₂ then some σ else Option.none
  | .fn F₁, .fn F₂ => if F₁ = F₂ then some σ else Option.none
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some σ else Option.none
  | .pquote pc, .quote c => matchCodeIn σ bound pc c
  | _, _ => Option.none

/-- Match at the quotation's root: no code binder is in scope yet. -/
def matchCode (σ : GStore S X) : Tm S X → Tm S X → Option (GStore S X) :=
  matchCodeIn σ []

/-- The binding steps `matchCodeIn` demands. -/
def matchCodeStepsIn (bound : List (Nm X)) :
    Tm S X → Tm S X → Option (Steps (Nm X) (GVal S X))
  | .var n, t =>
      if CodeId.hole n then (contextualVal bound t).map fun g => [(n, g)] else
        match t with
        | .var m => if CodeId.same n m then some [] else Option.none
        | _ => Option.none
  | .pvar x, .pvar y => if CodeId.same x y then some [] else Option.none
  | .lam x₁ own₁ b₁, .lam x₂ own₂ b₂ =>
      if CodeId.same x₁ x₂ && decide (own₁ = own₂) then
        matchCodeStepsIn (bound ++ [x₂]) b₁ b₂
      else Option.none
  | .app p₁ p₂, .app t₁ t₂ =>
      (matchCodeStepsIn bound p₁ t₁).bind fun s₁ =>
        (matchCodeStepsIn bound p₂ t₂).map fun s₂ => s₁ ++ s₂
  | .letP p₁ w₁ b₁, .letP p₂ w₂ b₂ =>
      (matchCodeStepsIn bound p₁ p₂).bind fun s₁ =>
        (matchCodeStepsIn bound w₁ w₂).bind fun s₂ =>
          (matchCodeStepsIn bound b₁ b₂).map fun s₃ => s₁ ++ s₂ ++ s₃
  | .alt p₁ p₂, .alt t₁ t₂ =>
      (matchCodeStepsIn bound p₁ t₁).bind fun s₁ =>
        (matchCodeStepsIn bound p₂ t₂).map fun s₂ => s₁ ++ s₂
  | .sym s₁, .sym s₂ => if s₁ = s₂ then some [] else Option.none
  | .fn F₁, .fn F₂ => if F₁ = F₂ then some [] else Option.none
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some [] else Option.none
  | .pquote pc, .quote c => matchCodeStepsIn bound pc c
  | _, _ => Option.none

/-- The binding steps `matchCode` demands. -/
def matchCodeSteps : Tm S X → Tm S X → Option (Steps (Nm X) (GVal S X)) :=
  matchCodeStepsIn []

/-- Match a pattern against a term under a ground store.  A store-name hole
binds a ground value; a pattern quotation is matched as code, so binders
inside it are compared by `CodeId`; two quotations of code are the same code
when `codeEq` holds; anything else must be equal. -/
def matchT (σ : GStore S X) : Tm S X → Tm S X → Option (GStore S X)
  | .var n, t =>
      match t.toGVal? with
      | some g => refineStep σ (n, g)
      | Option.none => Option.none
  | .app p₁ p₂, .app t₁ t₂ =>
      match matchT σ p₁ t₁ with
      | some σ' => matchT σ' p₂ t₂
      | Option.none => Option.none
  | .pquote pc, .quote c => matchCode σ pc c
  | .quote c₁, .quote c₂ => if codeEq c₁ c₂ then some σ else Option.none
  | p, t => if p = t then some σ else Option.none

/-- Matching code only refines the store, by the holes it binds. -/
theorem matchCodeIn_mono : ∀ (bound : List (Nm X)) (p t : Tm S X) (σ σ' : GStore S X),
    matchCodeIn σ bound p t = some σ' → σ ⊑ σ'
  | bound, .var n, t, σ, σ', h => by
      simp only [matchCodeIn] at h
      cases hhn : CodeId.hole n with
      | true =>
          simp only [hhn] at h
          cases hg : contextualVal bound t with
          | none => simp [hg] at h
          | some g =>
              simp only [hg] at h
              exact refineStep_mono h
      | false =>
          simp only [hhn] at h
          cases t with
          | var m =>
              cases hsame : CodeId.same n m with
              | true =>
                  simp only [hsame] at h
                  injection h with h; subst h; exact Store.LE.refl σ
              | false => simp [hsame] at h
          | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
              cases h
  | _, .pvar x, t, σ, σ', h => by
      cases t with
      | pvar y =>
          simp only [matchCodeIn] at h
          cases hsame : CodeId.same x y with
          | true =>
              simp only [hsame] at h
              injection h with h; subst h; exact Store.LE.refl σ
          | false => simp [hsame] at h
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | bound, .lam x₁ own₁ b₁, t, σ, σ', h => by
      cases t with
      | lam x₂ own₂ b₂ =>
          simp only [matchCodeIn] at h
          cases hcond : CodeId.same x₁ x₂ && decide (own₁ = own₂) with
          | true =>
              simp only [hcond] at h
              exact matchCodeIn_mono (bound ++ [x₂]) b₁ b₂ σ σ' h
          | false => simp [hcond] at h
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | bound, .app p₁ p₂, t, σ, σ', h => by
      cases t with
      | app t₁ t₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              exact (matchCodeIn_mono bound p₁ t₁ σ σ₁ h₁).trans (matchCodeIn_mono bound p₂ t₂ σ₁ σ' h)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | bound, .letP p₁ w₁ b₁, t, σ, σ', h => by
      cases t with
      | letP p₂ w₂ b₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ p₂ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              cases h₂ : matchCodeIn σ₁ bound w₁ w₂ with
              | none => simp [h₂] at h
              | some σ₂ =>
                  simp only [h₂] at h
                  exact ((matchCodeIn_mono bound p₁ p₂ σ σ₁ h₁).trans
                    (matchCodeIn_mono bound w₁ w₂ σ₁ σ₂ h₂)).trans (matchCodeIn_mono bound b₁ b₂ σ₂ σ' h)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | bound, .alt p₁ p₂, t, σ, σ', h => by
      cases t with
      | alt t₁ t₂ =>
          simp only [matchCodeIn] at h
          cases h₁ : matchCodeIn σ bound p₁ t₁ with
          | none => simp [h₁] at h
          | some σ₁ =>
              simp only [h₁] at h
              exact (matchCodeIn_mono bound p₁ t₁ σ σ₁ h₁).trans (matchCodeIn_mono bound p₂ t₂ σ₁ σ' h)
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ =>
          simp [matchCodeIn] at h
  | _, .sym _, t, σ, σ', h => by
      cases t with
      | sym _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | _, .fn _, t, σ, σ', h => by
      cases t with
      | fn _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | _, .quote _, t, σ, σ', h => by
      cases t with
      | quote _ =>
          simp only [matchCodeIn] at h
          split at h
          · injection h with h; subst h; exact Store.LE.refl σ
          · cases h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | bound, .pquote pc, t, σ, σ', h => by
      cases t with
      | quote c =>
          simp only [matchCodeIn] at h
          exact matchCodeIn_mono bound pc c σ σ' h
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp [matchCodeIn] at h
  | _, .ctx _ _, t, σ, σ', h => by simp [matchCodeIn] at h

theorem matchCode_mono (p t : Tm S X) (σ σ' : GStore S X)
    (h : matchCode σ p t = some σ') : σ ⊑ σ' := by
  unfold matchCode at h
  exact matchCodeIn_mono [] p t σ σ' h

/-- Matching code is the refinement run of the bindings it demands. -/
theorem matchCodeIn_eq_refineRun :
    ∀ (bound : List (Nm X)) (p t : Tm S X) (σ : GStore S X),
    matchCodeIn σ bound p t = (matchCodeStepsIn bound p t).bind (refineRun σ)
  | bound, .var n, t, σ => by
      simp only [matchCodeIn, matchCodeStepsIn]
      cases hhn : CodeId.hole n with
      | true =>
          cases hg : contextualVal bound t with
          | none =>
              simp only [if_true]
              rfl
          | some g =>
              simp only [if_true, Option.map_some, Option.bind_some]
              rw [refineRun_cons]
              cases refineStep σ (n, g) <;> rfl
      | false =>
          simp only [Bool.false_eq_true, if_false]
          cases t with
          | var m =>
              dsimp only
              cases CodeId.same n m with
              | true =>
                  rw [if_pos rfl, if_pos rfl, Option.bind_some, refineRun_nil]
              | false =>
                  simp only [Bool.false_eq_true, if_false, Option.bind_none]
          | sym _ | fn _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
              rfl
  | _, .pvar x, t, σ => by
      cases t with
      | pvar y =>
          simp only [matchCodeIn, matchCodeStepsIn]
          cases CodeId.same x y with
          | true =>
              rw [if_pos rfl, if_pos rfl, Option.bind_some, refineRun_nil]
          | false =>
              simp only [Bool.false_eq_true, if_false, Option.bind_none]
      | sym _ | fn _ | var _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | bound, .lam x₁ own₁ b₁, t, σ => by
      cases t with
      | lam x₂ own₂ b₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          cases CodeId.same x₁ x₂ && decide (own₁ = own₂) with
          | true =>
              rw [if_pos rfl, if_pos rfl]
              exact matchCodeIn_eq_refineRun (bound ++ [x₂]) b₁ b₂ σ
          | false =>
              simp only [Bool.false_eq_true, if_false, Option.bind_none]
      | sym _ | fn _ | var _ | pvar _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | bound, .app p₁ p₂, t, σ => by
      cases t with
      | app t₁ t₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          rw [matchCodeIn_eq_refineRun bound p₁ t₁ σ]
          cases h₁ : matchCodeStepsIn bound p₁ t₁ with
          | none => rfl
          | some s₁ =>
              simp only [Option.bind_some]
              cases h₂ : matchCodeStepsIn bound p₂ t₂ with
              | none =>
                  simp only [Option.map_none, Option.bind_none]
                  cases refineRun σ s₁ with
                  | none => rfl
                  | some σ' => simp [matchCodeIn_eq_refineRun bound p₂ t₂ σ', h₂]
              | some s₂ =>
                  simp only [Option.map_some, Option.bind_some, refineRun_append]
                  cases refineRun σ s₁ with
                  | none => rfl
                  | some σ' => simp [matchCodeIn_eq_refineRun bound p₂ t₂ σ', h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | bound, .letP p₁ w₁ b₁, t, σ => by
      cases t with
      | letP p₂ w₂ b₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          rw [matchCodeIn_eq_refineRun bound p₁ p₂ σ]
          cases h₁ : matchCodeStepsIn bound p₁ p₂ with
          | none => rfl
          | some s₁ =>
              simp only [Option.bind_some]
              cases hr₁ : refineRun σ s₁ with
              | none =>
                  cases h₂ : matchCodeStepsIn bound w₁ w₂ with
                  | none => rfl
                  | some s₂ =>
                      simp only [Option.bind_some]
                      cases h₃ : matchCodeStepsIn bound b₁ b₂ with
                      | none =>
                          simp only [Option.map_none, Option.bind_none]
                      | some s₃ =>
                          simp only [Option.map_some, Option.bind_some, refineRun_append, hr₁]
              | some σ₁ =>
                  dsimp only
                  rw [matchCodeIn_eq_refineRun bound w₁ w₂ σ₁]
                  cases h₂ : matchCodeStepsIn bound w₁ w₂ with
                  | none =>
                      simp only [Option.bind_none]
                  | some s₂ =>
                      simp only [Option.bind_some]
                      cases hr₂ : refineRun σ₁ s₂ with
                      | none =>
                          cases h₃ : matchCodeStepsIn bound b₁ b₂ with
                          | none =>
                              simp only [Option.map_none, Option.bind_none]
                          | some s₃ =>
                              simp only [Option.map_some, Option.bind_some, refineRun_append,
                                hr₁, hr₂]
                      | some σ₂ =>
                          dsimp only
                          rw [matchCodeIn_eq_refineRun bound b₁ b₂ σ₂]
                          cases h₃ : matchCodeStepsIn bound b₁ b₂ with
                          | none =>
                              simp only [Option.map_none, Option.bind_none]
                          | some s₃ =>
                              simp only [Option.map_some, Option.bind_some, refineRun_append,
                                hr₁, hr₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | alt _ _ =>
          rfl
  | bound, .alt p₁ p₂, t, σ => by
      cases t with
      | alt t₁ t₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          rw [matchCodeIn_eq_refineRun bound p₁ t₁ σ]
          cases h₁ : matchCodeStepsIn bound p₁ t₁ with
          | none => rfl
          | some s₁ =>
              simp only [Option.bind_some]
              cases h₂ : matchCodeStepsIn bound p₂ t₂ with
              | none =>
                  simp only [Option.map_none, Option.bind_none]
                  cases refineRun σ s₁ with
                  | none => rfl
                  | some σ' => simp [matchCodeIn_eq_refineRun bound p₂ t₂ σ', h₂]
              | some s₂ =>
                  simp only [Option.map_some, Option.bind_some, refineRun_append]
                  cases refineRun σ s₁ with
                  | none => rfl
                  | some σ' => simp [matchCodeIn_eq_refineRun bound p₂ t₂ σ', h₂]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ =>
          rfl
  | _, .sym s₁, t, σ => by
      cases t with
      | sym s₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          by_cases h : s₁ = s₂
          · rw [if_pos h, if_pos h, Option.bind_some, refineRun_nil]
          · rw [if_neg h, if_neg h]; rfl
      | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | _, .fn F₁, t, σ => by
      cases t with
      | fn F₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          by_cases h : F₁ = F₂
          · rw [if_pos h, if_pos h, Option.bind_some, refineRun_nil]
          · rw [if_neg h, if_neg h]; rfl
      | sym _ | var _ | pvar _ | lam _ _ _ | app _ _ | quote _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | _, .quote c₁, t, σ => by
      cases t with
      | quote c₂ =>
          simp only [matchCodeIn, matchCodeStepsIn]
          cases codeEq c₁ c₂ with
          | true =>
              rw [if_pos rfl, if_pos rfl, Option.bind_some, refineRun_nil]
          | false =>
              simp only [Bool.false_eq_true, if_false, Option.bind_none]
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | bound, .pquote pc, t, σ => by
      cases t with
      | quote c =>
          simp only [matchCodeIn, matchCodeStepsIn]
          exact matchCodeIn_eq_refineRun bound pc c σ
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          rfl
  | _, .ctx _ _, t, σ => by simp [matchCodeIn, matchCodeStepsIn]

theorem matchCode_eq_refineRun (p t : Tm S X) (σ : GStore S X) :
    matchCode σ p t = (matchCodeSteps p t).bind (refineRun σ) := by
  unfold matchCode matchCodeSteps
  exact matchCodeIn_eq_refineRun [] p t σ

/-- `some f` when a `let` binds the name `f` to a lambda written in place. -/
def letLam? : Tm S X → Tm S X → Option (Nm X)
  | .var f, .lam _ _ _ => some f
  | _, _ => Option.none

/-- Results: a bag of result terms with their final stores. -/
abbrev Result (S : Type u) (X : Type v) := List (Tm S X × GStore S X)

/-- Run a continuation on every element of a bag; fail if any run fails. -/
def bindAll {α β : Type*} : List α → (α → Option (List β)) → Option (List β)
  | [], _ => some []
  | a :: as, g =>
      match g a, bindAll as g with
      | some l, some r => some (l ++ r)
      | _, _ => Option.none

/-- Bind a bag that may be undefined. -/
def bindOpt {α β : Type*} (o : Option (List α)) (g : α → Option (List β)) :
    Option (List β) :=
  match o with
  | some l => bindAll l g
  | Option.none => Option.none

/-- Evaluator signature. -/
abbrev Runner (S : Type u) (X : Type v) :=
  Path → GStore S X → Tm S X → Option (Result S X)

/-- One unfolding of the evaluator, with `rec` for the sub-evaluations. -/
def step (d : Disc) (prog : S → Option (Tm S X)) (rec : Runner S X) : Runner S X :=
  fun π σ t =>
    match t with
    | .fn F =>
        match prog F with
        | some e => rec (π ++ [0]) σ e
        | Option.none => some [(.fn F, σ)]
    | .app f a =>
        bindOpt (rec (π ++ [0]) σ f) fun r₁ =>
        bindOpt (rec (π ++ [1]) r₁.2 a) fun r₂ =>
          match r₁.1 with
          | .lam x own body =>
              rec (π ++ [2]) r₂.2 (activate d r₂.2 (π ++ [2]) x own body r₂.1)
          | fv => some [(.app fv r₂.1, r₂.2)]
    | .letP p w b =>
        match letLam? p w with
        | some f => rec π σ (subst (Sub.single f w) Sub.none b)
        | Option.none =>
            bindOpt (rec (π ++ [0]) σ w) fun r₁ =>
              match (act r₁.2 r₁.1).toGVal? with
              | some g =>
                  match matchT r₁.2 p g.toTm with
                  | some σ₂ => rec (π ++ [1]) σ₂ b
                  | Option.none => some []
              | Option.none =>
                  match p with
                  | .var f => rec (π ++ [1]) r₁.2 (subst (Sub.single f r₁.1) Sub.none b)
                  | _ => some []
    | .alt t₁ t₂ =>
        match rec (π ++ [0]) σ t₁, rec (π ++ [1]) σ t₂ with
        | some l, some r => some (l ++ r)
        | _, _ => Option.none
    | v => some [(v, σ)]

/-- The evaluator with `n` units of fuel. -/
def run (d : Disc) (prog : S → Option (Tm S X)) : ℕ → Runner S X
  | 0 => fun _ _ _ => Option.none
  | n + 1 => step d prog (run d prog n)

/-- The answers: each result with its final store applied. -/
def answers (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ) (t : Tm S X) :
    Option (List (Tm S X)) :=
  (run d prog n [] Store.empty t).map (List.map fun r => act r.2 r.1)

/-- The relational answer semantics: `bag` is the answer bag of `t`. -/
def AnswerBag (d : Disc) (prog : S → Option (Tm S X)) (t : Tm S X)
    (bag : List (Tm S X)) : Prop :=
  ∃ n, answers d prog n t = some bag

/-! ## Fuel monotonicity -/

/-- One runner is extended by another: whatever the first defines, the
second defines identically. -/
def Runner.Le (r r' : Runner S X) : Prop :=
  ∀ π σ t L, r π σ t = some L → r' π σ t = some L

theorem bindAll_mono {α β : Type*} {g g' : α → Option (List β)}
    (hg : ∀ a M, g a = some M → g' a = some M) :
    ∀ (l : List α) (L : List β), bindAll l g = some L → bindAll l g' = some L
  | [], _, h => h
  | a :: as, L, h => by
      unfold bindAll at h ⊢
      cases hga : g a with
      | none => rw [hga] at h; cases h
      | some l =>
          cases hrest : bindAll as g with
          | none => rw [hga, hrest] at h; cases h
          | some r =>
              rw [hga, hrest] at h
              rw [hg a l hga, bindAll_mono hg as r hrest]
              exact h

theorem bindOpt_mono {α β : Type*} {o o' : Option (List α)}
    {g g' : α → Option (List β)} (ho : ∀ l, o = some l → o' = some l)
    (hg : ∀ a M, g a = some M → g' a = some M) {L : List β}
    (h : bindOpt o g = some L) : bindOpt o' g' = some L := by
  cases hoo : o with
  | none => rw [hoo] at h; cases h
  | some l =>
      rw [hoo] at h
      rw [ho l hoo]
      exact bindAll_mono hg l L h

theorem step_mono (d : Disc) (prog : S → Option (Tm S X)) {r r' : Runner S X}
    (h : Runner.Le r r') : Runner.Le (step d prog r) (step d prog r') := by
  intro π σ t L hL
  cases t with
  | fn F =>
      simp only [step] at hL ⊢
      cases hp : prog F with
      | none => rw [hp] at hL; exact hL
      | some e => rw [hp] at hL; exact h _ _ _ _ hL
  | app f a =>
      simp only [step] at hL ⊢
      refine bindOpt_mono (fun l hl => h _ _ _ _ hl) ?_ hL
      intro r₁ M hM
      refine bindOpt_mono (fun l hl => h _ _ _ _ hl) ?_ hM
      intro r₂ M' hM'
      cases r₁ with
      | mk fv σ₁ =>
          cases fv with
          | lam x own body => exact h _ _ _ _ hM'
          | _ => exact hM'
  | letP p w b =>
      simp only [step] at hL ⊢
      cases hl : letLam? p w with
      | some f => rw [hl] at hL; exact h _ _ _ _ hL
      | none =>
          rw [hl] at hL
          simp only at hL ⊢
          refine bindOpt_mono (fun l hl => h _ _ _ _ hl) ?_ hL
          intro r₁ M hM
          cases hg : (act r₁.2 r₁.1).toGVal? with
          | some g =>
              rw [hg] at hM
              simp only at hM ⊢
              cases hm : matchT r₁.2 p g.toTm with
              | some σ₂ => rw [hm] at hM; exact h _ _ _ _ hM
              | none => rw [hm] at hM; exact hM
          | none =>
              rw [hg] at hM
              simp only at hM ⊢
              cases p with
              | var f => exact h _ _ _ _ hM
              | _ => exact hM
  | alt t₁ t₂ =>
      simp only [step] at hL ⊢
      cases h₁ : r (π ++ [0]) σ t₁ with
      | none => rw [h₁] at hL; cases hL
      | some l =>
          cases h₂ : r (π ++ [1]) σ t₂ with
          | none => rw [h₁, h₂] at hL; cases hL
          | some m =>
              rw [h₁, h₂] at hL
              rw [h _ _ _ _ h₁, h _ _ _ _ h₂]
              exact hL
  | sym s => exact hL
  | var n => exact hL
  | pvar x => exact hL
  | lam x own body => exact hL
  | quote c => exact hL
  | ctx _ _ => exact hL
  | pquote c => exact hL

theorem run_le_succ (d : Disc) (prog : S → Option (Tm S X)) :
    ∀ n, Runner.Le (run d prog n) (run d prog (n + 1))
  | 0 => fun _ _ _ _ h => by cases h
  | n + 1 => step_mono d prog (run_le_succ d prog n)

/-- **Fuel monotonicity.**  A defined run stays defined, with the same bag. -/
theorem run_mono (d : Disc) (prog : S → Option (Tm S X)) {n m : ℕ} (hnm : n ≤ m)
    {π : Path} {σ : GStore S X} {t : Tm S X} {L : Result S X}
    (h : run d prog n π σ t = some L) : run d prog m π σ t = some L := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact run_le_succ d prog _ _ _ _ _ ih

/-- The answer bag, when defined, does not depend on the fuel. -/
theorem AnswerBag.unique {d : Disc} {prog : S → Option (Tm S X)} {t : Tm S X}
    {b₁ b₂ : List (Tm S X)} (h₁ : AnswerBag d prog t b₁) (h₂ : AnswerBag d prog t b₂) :
    b₁ = b₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  unfold answers at h₁ h₂
  cases hr₁ : run d prog n₁ [] Store.empty t with
  | none => rw [hr₁] at h₁; cases h₁
  | some L₁ =>
      cases hr₂ : run d prog n₂ [] Store.empty t with
      | none => rw [hr₂] at h₂; cases h₂
      | some L₂ =>
          have e₁ := run_mono d prog (le_max_left n₁ n₂) hr₁
          have e₂ := run_mono d prog (le_max_right n₁ n₂) hr₂
          rw [e₁] at e₂
          injection e₂ with e
          subst e
          rw [hr₁] at h₁
          rw [hr₂] at h₂
          injection h₁ with h₁
          injection h₂ with h₂
          rw [← h₁, ← h₂]

/-- Runs that agree from some fuel on have the same answer bags. -/
theorem AnswerBag.congr_of_run {d d' : Disc} {prog prog' : S → Option (Tm S X)}
    {t t' : Tm S X} (k : ℕ)
    (h : ∀ n, k ≤ n → run d prog n [] Store.empty t = run d' prog' n [] Store.empty t')
    (bag : List (Tm S X)) : AnswerBag d prog t bag ↔ AnswerBag d' prog' t' bag := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨max n k, ?_⟩
    unfold answers at hn ⊢
    cases hr : run d prog n [] Store.empty t with
    | none => rw [hr] at hn; cases hn
    | some L =>
        rw [← h _ (le_max_right n k), run_mono d prog (le_max_left n k) hr]
        rw [hr] at hn
        exact hn
  · rintro ⟨n, hn⟩
    refine ⟨max n k, ?_⟩
    unfold answers at hn ⊢
    cases hr : run d' prog' n [] Store.empty t' with
    | none => rw [hr] at hn; cases hn
    | some L =>
        rw [h _ (le_max_right n k), run_mono d' prog' (le_max_left n k) hr]
        rw [hr] at hn
        exact hn

/-! ## The evaluator performs the inlining substitution -/

/-- A `let` of a lambda written in place is the substitution of that lambda
into the body, at the same path. -/
theorem run_letP_lam (d : Disc) (prog : S → Option (Tm S X)) (n : ℕ) (π : Path)
    (σ : GStore S X) (f x : Nm X) (own : List X) (body C : Tm S X) :
    run d prog (n + 1) π σ (.letP (.var f) (.lam x own body) C) =
      run d prog n π σ (subst (Sub.single f (.lam x own body)) Sub.none C) := rfl

/-- Answers agree when one run is the other with one more unit of fuel. -/
theorem AnswerBag.congr_of_run_succ {d d' : Disc} {prog prog' : S → Option (Tm S X)}
    {t t' : Tm S X}
    (h : ∀ n, run d prog (n + 1) [] Store.empty t = run d' prog' n [] Store.empty t')
    (bag : List (Tm S X)) : AnswerBag d prog t bag ↔ AnswerBag d' prog' t' bag := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [answers, run] at hn
    | succ m =>
        refine ⟨m, ?_⟩
        unfold answers at hn ⊢
        rw [← h m]
        exact hn
  · rintro ⟨m, hm⟩
    refine ⟨m + 1, ?_⟩
    unfold answers at hm ⊢
    rw [h m]
    exact hm

theorem bindAll_singleton {α β : Type*} (a : α) (g : α → Option (List β)) :
    bindAll [a] g = g a := by
  unfold bindAll bindAll
  cases g a <;> simp

theorem bindOpt_some_singleton {α β : Type*} (a : α) (g : α → Option (List β)) :
    bindOpt (some [a]) g = g a := bindAll_singleton a g

/-! ## Theorem 1: lambda lifting -/

/-- Parameter names a term binds or uses (outside sealed quotations). -/
def paramNames : Tm S X → List (Nm X)
  | .sym _ => []
  | .fn _ => []
  | .var _ => []
  | .pvar x => [x]
  | .lam x _ b => x :: paramNames b
  | .app f a => paramNames f ++ paramNames a
  | .quote _ => []
  | .ctx _ _ => []
  | .pquote c => paramNames c
  | .letP p w b => paramNames p ++ paramNames w ++ paramNames b
  | .alt t₁ t₂ => paramNames t₁ ++ paramNames t₂

/-- Turn the store names selected by `P` into parameter occurrences. -/
def absP (P : Nm X → Bool) : Sub S X :=
  fun n => if P n then some (.pvar n) else Option.none

/-- **The lambda-lifted equation** of `L`: the names `cs` (its captured names)
become extra leading parameters; its own names stay its own, so the clause's
variables are renamed per call. -/
def lifted (cs : List (Nm X)) (L : Tm S X) : Tm S X :=
  cs.foldr (fun c acc => .lam c [] acc) (subst (absP fun n => decide (n ∈ cs)) Sub.none L)

/-- A curried call `(F a₁ … aₖ)`. -/
def callSpine (h : Tm S X) (args : List (Tm S X)) : Tm S X := args.foldl .app h

omit [CodeId X] [DecidableEq S] in
theorem absP_hideOwn (P : Nm X → Bool) (own : List X) :
    (absP P : Sub S X).hideOwn own = absP fun n => P n && !ownKey own n := by
  funext n
  unfold Sub.hideOwn absP
  by_cases hk : ownKey own n <;> by_cases hp : P n <;> simp [hk, hp]

omit [CodeId X] [DecidableEq S] [DecidableEq X] in
theorem absP_congr {P Q : Nm X → Bool} (h : ∀ n, P n = Q n) :
    (absP P : Sub S X) = absP Q := by
  funext n
  simp [absP, h n]

omit [CodeId X] [DecidableEq S] in
theorem renameOwn_nil (ρ : Path) : (renameOwn ρ [] : Sub S X) = Sub.none := by
  funext n
  cases n <;> simp [renameOwn, ownKey, Sub.none]

omit [CodeId X] [DecidableEq S] in
theorem none_hideOwn (own : List X) : (Sub.none : Sub S X).hideOwn own = Sub.none := by
  funext n
  simp [Sub.hideOwn, Sub.none]

omit [CodeId X] [DecidableEq S] in
theorem single_hideParam_ne {c x : Nm X} (h : x ≠ c) (v : Tm S X) :
    (Sub.single c v).hideParam x = Sub.single c v := by
  funext n
  unfold Sub.hideParam Sub.single
  by_cases hn : n = x
  · subst hn
    simp [h]
  · simp [hn]

omit [CodeId X] [DecidableEq S] in
/-- The empty substitution is the identity. -/
theorem subst_none_none : ∀ t : Tm S X, subst Sub.none Sub.none t = t
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x own b => by
      simp only [subst, none_hideOwn, none_hideParam, subst_none_none b]
  | .app f a => by simp only [subst, subst_none_none f, subst_none_none a]
  | .quote _ => rfl
  | .ctx _ _ => rfl
  | .pquote c => by simp only [subst, subst_none_none c]
  | .letP p w b => by
      simp only [subst, subst_none_none p, subst_none_none w, subst_none_none b]
  | .alt t₁ t₂ => by simp only [subst, subst_none_none t₁, subst_none_none t₂]

omit [CodeId X] [DecidableEq S] in
/-- **Round trip.**  Abstracting the names selected by `P` into parameters and
then instantiating the parameter `c` by the store name `c` undoes the
abstraction of `c`, provided `c` is not a parameter name of the term. -/
theorem subst_single_absP {c : Nm X} : ∀ (t : Tm S X) (P : Nm X → Bool),
    c ∉ paramNames t →
    subst Sub.none (Sub.single c (.var c)) (subst (absP P) Sub.none t) =
      subst (absP fun n => P n && decide (n ≠ c)) Sub.none t
  | .sym _, _, _ => rfl
  | .fn _, _, _ => rfl
  | .var n, P, _ => by
      by_cases hp : P n
      · by_cases hn : n = c
        · subst hn
          simp [subst, absP, hp, Sub.single]
        · simp [subst, absP, hp, Sub.single, hn]
      · simp [subst, absP, hp, Sub.none]
  | .pvar x, P, h => by
      have hx : x ≠ c := by
        intro e
        apply h
        simp [paramNames, e]
      simp [subst, Sub.none, Sub.single, hx]
  | .lam x own b, P, h => by
      have hx : x ≠ c := by
        intro e
        apply h
        simp [paramNames, e]
      have hb : c ∉ paramNames b := by
        intro hb
        apply h
        simp [paramNames, hb]
      simp only [subst, absP_hideOwn, none_hideOwn, none_hideParam,
        single_hideParam_ne hx]
      congr 1
      rw [subst_single_absP b _ hb]
      congr 1
      apply absP_congr
      intro n
      cases P n <;> cases ownKey own n <;> simp
  | .app f a, P, h => by
      simp only [paramNames, List.mem_append, not_or] at h
      simp only [subst, subst_single_absP f P h.1, subst_single_absP a P h.2]
  | .quote _, _, _ => rfl
  | .ctx _ _, _, _ => rfl
  | .pquote c', P, h => by
      simp only [paramNames] at h
      simp only [subst, subst_single_absP c' P h]
  | .letP p w b, P, h => by
      simp only [paramNames, List.mem_append, not_or] at h
      simp only [subst, subst_single_absP p P h.1.1, subst_single_absP w P h.1.2,
        subst_single_absP b P h.2]
  | .alt t₁ t₂, P, h => by
      simp only [paramNames, List.mem_append, not_or] at h
      simp only [subst, subst_single_absP t₁ P h.1, subst_single_absP t₂ P h.2]

omit [CodeId X] [DecidableEq S] in
/-- Instantiating a parameter passes through curried binders of other names. -/
theorem subst_single_foldr_lam {c : Nm X} (v : Tm S X) :
    ∀ (cs : List (Nm X)) (t : Tm S X), c ∉ cs →
      subst Sub.none (Sub.single c v) (cs.foldr (fun c' acc => .lam c' [] acc) t) =
        cs.foldr (fun c' acc => .lam c' [] acc) (subst Sub.none (Sub.single c v) t)
  | [], _, _ => rfl
  | c' :: cs, t, h => by
      have hne : c' ≠ c := fun e => h (e ▸ List.mem_cons_self)
      have hcs : c ∉ cs := fun hc => h (List.mem_cons_of_mem c' hc)
      simp only [List.foldr_cons, subst, none_hideOwn, single_hideParam_ne hne]
      rw [subst_single_foldr_lam v cs t hcs]

/-- A lambda value evaluates to itself. -/
theorem run_lam (d : Disc) (prog : S → Option (Tm S X)) (m : ℕ) (π : Path)
    (σ : GStore S X) (x : Nm X) (own : List X) (b : Tm S X) :
    run d prog (m + 1) π σ (.lam x own b) = some [(.lam x own b, σ)] := rfl

/-- A store-name occurrence evaluates to itself. -/
theorem run_var (d : Disc) (prog : S → Option (Tm S X)) (m : ℕ) (π : Path)
    (σ : GStore S X) (n : Nm X) :
    run d prog (m + 1) π σ (.var n) = some [(.var n, σ)] := rfl

omit [CodeId X] [DecidableEq S] in
/-- A lifted equation (over a lambda) is a lambda. -/
theorem lifted_lam (rest : List (Nm X)) (z : Nm X) (own : List X) (body : Tm S X) :
    ∃ x own' b, lifted rest (.lam z own body) = .lam x own' b := by
  cases rest with
  | nil => exact ⟨z, own, _, rfl⟩
  | cons c rest => exact ⟨c, [], _, rfl⟩

/-- Evaluating the call spine of the lifted equation on a prefix of its
captured names yields the lifted equation of the remaining names. -/
theorem run_spine (prog : S → Option (Tm S X)) (Lf : S) (cs : List (Nm X))
    (z : Nm X) (own : List X) (body : Tm S X)
    (hprog : prog Lf = some (lifted cs (.lam z own body))) (hnd : cs.Nodup)
    (hhyg : ∀ c ∈ cs, c ∉ paramNames (.lam z own body : Tm S X)) (pre : List (Nm X)) :
    ∀ (rest : List (Nm X)), cs = pre ++ rest → ∀ (n : ℕ) (π : Path) (σ : GStore S X),
      pre.length + 2 ≤ n →
      run .static prog n π σ (callSpine (.fn Lf) (pre.map .var)) =
        some [(lifted rest (.lam z own body), σ)] := by
  induction pre using List.reverseRecOn with
  | nil =>
      intro rest hcs n π σ hn
      simp only [List.nil_append] at hcs
      subst hcs
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by simp at hn; omega⟩
      obtain ⟨x, own', b, hlam⟩ := lifted_lam cs z own body
      show step .static prog (run .static prog (m + 1)) π σ (.fn Lf) = _
      simp only [step, hprog, hlam]
      rfl
  | append_singleton pre c ih =>
      intro rest hcs n π σ hn
      have hcs' : cs = pre ++ c :: rest := by simpa using hcs
      have hcrest : c ∉ rest := by
        rw [hcs'] at hnd
        exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
      have hcL : c ∉ paramNames (.lam z own body : Tm S X) :=
        hhyg c (by rw [hcs']; simp)
      simp only [List.length_append, List.length_singleton] at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hspine : callSpine (.fn Lf) ((pre ++ [c]).map Tm.var) =
          .app (callSpine (.fn Lf) (pre.map .var)) (.var c) := by
        simp [callSpine, List.foldl_append]
      rw [hspine]
      show step .static prog (run .static prog m) π σ _ = _
      have hm1 : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      obtain ⟨k, rfl⟩ := hm1
      simp only [step]
      rw [ih (c :: rest) hcs' (k + 1) (π ++ [0]) σ (by omega), bindOpt_some_singleton]
      simp only
      rw [run_var, bindOpt_some_singleton]
      simp only [lifted, List.foldr_cons]
      simp only [activate, renameOwn_nil]
      rw [subst_single_foldr_lam _ rest _ hcrest, subst_single_absP _ _ hcL]
      have habs : (absP fun n => decide (n ∈ c :: rest) && decide (n ≠ c) : Sub S X) =
          absP fun n => decide (n ∈ rest) := by
        apply absP_congr
        intro n
        by_cases hn : n = c
        · subst hn
          simp [hcrest]
        · simp [hn]
      rw [habs]
      obtain ⟨x, own', b, hlam⟩ := lifted_lam rest z own body
      unfold lifted at hlam
      rw [hlam]
      rfl

/-- **Theorem 1 (lifting).**  Under rule M's activation, calling the
lambda-lifted equation `(Lf c₁ … cₖ a)` — the captured names passed as
references, extra leading parameters — equals applying the lambda `(L a)`.
The equality is on the whole observation: the bag of results with their final
stores (multiplicity, aliasing and residual store names included). -/
theorem run_lifted_call (prog : S → Option (Tm S X)) (Lf : S) (cs : List (Nm X))
    (z : Nm X) (own : List X) (body a : Tm S X)
    (hprog : prog Lf = some (lifted cs (.lam z own body))) (hnd : cs.Nodup)
    (hhyg : ∀ c ∈ cs, c ∉ paramNames (.lam z own body : Tm S X))
    (n : ℕ) (hn : cs.length + 3 ≤ n) (π : Path) (σ : GStore S X) :
    run .static prog n π σ (.app (callSpine (.fn Lf) (cs.map .var)) a) =
      run .static prog n π σ (.app (.lam z own body) a) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show step .static prog (run .static prog m) π σ _ =
    step .static prog (run .static prog m) π σ _
  have hspine := run_spine prog Lf cs z own body hprog hnd hhyg cs [] (by simp) m
    (π ++ [0]) σ (by omega)
  have hlift : lifted [] (.lam z own body : Tm S X) = .lam z own body := by
    simp only [lifted, List.foldr_nil, List.not_mem_nil, decide_false]
    have : (absP fun _ => false : Sub S X) = Sub.none := by
      funext n
      simp [absP, Sub.none]
    rw [this, subst_none_none]
  rw [hlift] at hspine
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [step]
  rw [hspine, run_lam]

omit [CodeId X] [DecidableEq S] in
/-- Abstracting the names selected by `P` removes exactly them from the free
names. -/
theorem freeNames_subst_absP : ∀ (t : Tm S X) (P : Nm X → Bool),
    freeNames (subst (absP P) Sub.none t) = (freeNames t).filter (fun n => !P n)
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .var n, P => by
      by_cases hp : P n <;> simp [subst, absP, hp, freeNames]
  | .pvar _, _ => rfl
  | .lam x own b, P => by
      simp only [subst, absP_hideOwn, none_hideParam, freeNames]
      rw [freeNames_subst_absP b, List.filter_filter, List.filter_filter]
      congr 1
      funext n
      cases P n <;> cases ownKey own n <;> rfl
  | .app f a, P => by
      simp only [subst, freeNames, List.filter_append, freeNames_subst_absP f P,
        freeNames_subst_absP a P]
  | .quote _, _ => rfl
  | .ctx _ _, _ => rfl
  | .pquote c, P => by simp only [subst, freeNames, freeNames_subst_absP c P]
  | .letP p w b, P => by
      simp only [subst, freeNames, List.filter_append, freeNames_subst_absP p P,
        freeNames_subst_absP w P, freeNames_subst_absP b P]
  | .alt t₁ t₂, P => by
      simp only [subst, freeNames, List.filter_append, freeNames_subst_absP t₁ P,
        freeNames_subst_absP t₂ P]

omit [CodeId X] [DecidableEq S] in
theorem freeNames_foldr_lam (cs : List (Nm X)) (t : Tm S X) :
    freeNames (cs.foldr (fun c acc => (.lam c [] acc : Tm S X)) t) = freeNames t := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldr_cons, freeNames, ih]
      have : (fun n => !ownKey ([] : List X) n) = fun _ => true := by
        funext n
        cases n <;> rfl
      rw [this, List.filter_true]

omit [CodeId X] [DecidableEq S] in
/-- The lambda-lifted equation over the captured names is closed: it is an
equation of the program, not a closure over the caller's scope. -/
theorem lifted_closed (L : Tm S X) : freeNames (lifted (captured L) L) = [] := by
  unfold lifted
  rw [freeNames_foldr_lam, freeNames_subst_absP, List.filter_eq_nil_iff]
  intro n hn
  simp [captured, List.mem_dedup, hn]

/-! ## Theorem 2: inlining at the query -/

/-- **Theorem 2 (inlining, rule M).**  Under the hygiene hypothesis of
`elabTopM_inline`, the elaborated `let f := L in C` runs exactly as the
elaborated inlined text `C[f := L]`, with one unit of fuel for the `let`. -/
theorem run_elabTopM_inline (prog : S → Option (Tm S X)) (n : ℕ) (π : Path)
    (σ : GStore S X) (fx : X) (x : Nm X) (body C : Tm S X)
    (hC : bare C = true) (hfL : fx ∉ names body)
    (hhyg : hygM fx (names body)
      (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) = true) :
    run .static prog (n + 1) π σ (elabTopM (.letP (.var (.src fx)) (.lam x [] body) C)) =
      run .static prog n π σ
        (elabTopM (subst (Sub.single (.src fx) (.lam x [] body)) Sub.none C)) := by
  rw [elabTopM_letP_lam, elabTopM_inline fx x body C hC hfL hhyg]
  rfl

/-- Theorem 2 on answer bags. -/
theorem answerBag_elabTopM_inline (prog : S → Option (Tm S X)) (fx : X) (x : Nm X)
    (body C : Tm S X) (hC : bare C = true) (hfL : fx ∉ names body)
    (hhyg : hygM fx (names body)
      (elabM (direct (.letP (.var (.src fx)) (.lam x [] body) C)) C) = true)
    (bag : List (Tm S X)) :
    AnswerBag .static prog (elabTopM (.letP (.var (.src fx)) (.lam x [] body) C)) bag ↔
      AnswerBag .static prog
        (elabTopM (subst (Sub.single (.src fx) (.lam x [] body)) Sub.none C)) bag :=
  AnswerBag.congr_of_run_succ
    (fun n => run_elabTopM_inline prog n [] Store.empty fx x body C hC hfL hhyg) bag

end Mettapedia.GSLT.LanguageDef.TemplateScope
