import Mettapedia.GSLT.LanguageDef.TemplateScope.Dropping

/-!
# Template scope, naming part 2: defunctionalization

Reynolds (1972): every lambda of a program becomes a first-order constructor
term `(Clo c₁ … cₖ)` carrying its captured references, and application
dispatches on the constructor to the constructor's apply rule.  The apply rule
of a constructor is the lambda's lifted equation (`TemplateScope.Dropping`):
the captured references are its leading parameters, and dispatching a closure
drops the closure's arguments into the rule.

## The target machine

`stepD` / `runD` / `answersD` are the model's evaluator with closures in place
of lambdas:
* a closure is a value;
* applying a closure activates its apply rule, with the closure's arguments in
  place of the rule's parameters, exactly as activating the lambda does;
* `let` treats a closure as the source treats a lambda: one written in place
  is substituted at the same path, and an evaluated one is a function value,
  substituted for a variable pattern and never stored in the ground store.
Everything else is the model's evaluator.

## Main results

* `rel_subst` — the closure relation `CloTable.rel` (a source lambda against a
  closure that unfolds to the same binders and a related body) is preserved
  by every substitution with related values that carry no rank.
* `run_defun` — **the simulation**: for a source term and a related target
  term, the model's evaluator and the target machine have, at every fuel, the
  same definedness, pointwise related results, and identical final stores.
* `answers_defun`, `answers_defun_lamFree`, `answerBag_defun` — the
  answer bags are related pointwise, and equal when the source's answers
  contain no lambda.
* `defun_B4`, `defun_B1`, `defun_curried` — row B4 (a captured reference that
  the call refines), row B1 (a private local renamed per call) and a curried
  function used partially, defunctionalized and run by the kernel.
* `closures_are_data` — a closure is a first-order term that the matcher
  takes apart, while matching a lambda gives no answer.
* `dropArgs_eqn` — dispatching a closure is dropping its arguments into its
  rule's equation.

## Hygiene

The model's substitution is not capture-avoiding.  The table therefore carries
ranks: a closure's arguments may mention only names and parameters bound by
rules of strictly larger rank, or by no rule.  This keeps a closure's arguments
from being captured by the binders of the rule they are dropped into, and it
holds for nested lambdas whose inner rules get smaller ranks.  The target term
must also be `good`: no free name of the query is a spelling a rule owns.
`defun_needs_good` shows the hypothesis is needed: without it the source
captures and the two programs answer differently.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

variable {S : Type u} {X : Type v}

/-! ## Syntax -/

/-- No lambda outside sealed quotations. -/
def Tm.lamFree : Tm S X → Bool
  | .lam _ _ _ => false
  | .app f a => f.lamFree && a.lamFree
  | .pquote c => c.lamFree
  | .letP p w b => p.lamFree && w.lamFree && b.lamFree
  | .alt t₁ t₂ => t₁.lamFree && t₂.lamFree
  | _ => true

/-- Symbol-headed spines `(s a₁ … aₖ)`: the symbol and the arguments. -/
def symSpine : Tm S X → Option (S × List (Tm S X))
  | .sym s => some (s, [])
  | .app f a => (symSpine f).map fun p => (p.1, p.2 ++ [a])
  | _ => none

/-- Relate two options: both defined and related, or both undefined. -/
def OptRel {α β : Type*} (R : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

/-- The apply rule of a closure constructor: the lambda's lifted equation.
The captured references are the leading `params`; `x`, `own` and `body` are the
lambda's, with nested lambdas already replaced by their closures. -/
structure ApplyRule (S : Type u) (X : Type v) where
  params : List (Nm X)
  x : Nm X
  own : List X
  body : Tm S X

variable [DecidableEq X]

/-- Parameter occurrences not bound in the term, outside sealed quotations. -/
def freeParams : Tm S X → List (Nm X)
  | .pvar x => [x]
  | .lam x _ b => (freeParams b).filter fun p => decide (p ≠ x)
  | .app f a => freeParams f ++ freeParams a
  | .pquote c => freeParams c
  | .letP p w b => freeParams p ++ freeParams w ++ freeParams b
  | .alt t₁ t₂ => freeParams t₁ ++ freeParams t₂
  | _ => []

/-- Simultaneous instantiation of parameters by arguments. -/
def paramSub : List (Nm X) → List (Tm S X) → Sub S X
  | p :: ps, v :: vs => fun n => if n = p then some v else paramSub ps vs n
  | _, _ => Sub.none

/-- A rule instance: the body with the closure's arguments for the parameters. -/
def ApplyRule.inst (r : ApplyRule S X) (vs : List (Tm S X)) : Tm S X :=
  subst Sub.none (paramSub r.params vs) r.body

/-- **A closure table**: the apply rule of each constructor, and the ranks that
keep closure arguments apart from the binders of the rules they enter. -/
structure CloTable (S : Type u) (X : Type v) where
  /-- The apply rule of a constructor, if it is one. -/
  rule : S → Option (ApplyRule S X)
  /-- The nesting rank of a constructor: inner lambdas get smaller ranks. -/
  rank : S → ℕ
  /-- The rank of the rule that owns a spelling, if a rule does. -/
  ownerRank : X → Option ℕ
  /-- The rank of the rule whose lambda parameter a name is, if any. -/
  paramRank : Nm X → Option ℕ

namespace CloTable

variable (T : CloTable S X)

/-- The rank of a store name: that of its owner; activation copies have none. -/
def nameRank : Nm X → Option ℕ
  | .src y => T.ownerRank y
  | .inst _ _ => none

/-- A rank a closure for `κ` may carry: larger than `κ`'s, or none. -/
def rankOK (κ : S) : Option ℕ → Bool
  | some k => decide (T.rank κ < k)
  | none => true

/-- The arguments of a closure for `κ` mention only names and parameters of
larger rank. -/
def argsOK (κ : S) (vs : List (Tm S X)) : Bool :=
  vs.all fun v => (freeNames v).all (fun n => T.rankOK κ (T.nameRank n)) &&
    (freeParams v).all fun p => T.rankOK κ (T.paramRank p)

/-- The closure a term is, if it is one: a symbol-headed spine whose symbol has
an apply rule taking exactly that many arguments. -/
def clo? (t : Tm S X) : Option (S × List (Tm S X) × ApplyRule S X) :=
  (symSpine t).bind fun p =>
    (T.rule p.1).bind fun r => if p.2.length = r.params.length then some (p.1, p.2, r) else none

/-- Whether a closure occurs outside sealed quotations. -/
def hasClo : Tm S X → Bool
  | .sym s => (T.clo? (.sym s)).isSome
  | .app f a => (T.clo? (.app f a)).isSome || hasClo f || hasClo a
  | .lam _ _ b => hasClo b
  | .pquote c => hasClo c
  | .letP p w b => hasClo p || hasClo w || hasClo b
  | .alt t₁ t₂ => hasClo t₁ || hasClo t₂
  | _ => false

/-- The machine's ground test: a closure is a function value, never ground. -/
def ground? (t : Tm S X) : Option (GVal S X) := if T.hasClo t then none else t.toGVal?

/-- `some f` when a `let` binds the name `f` to a closure written in place. -/
def letClo? : Tm S X → Tm S X → Option (Nm X)
  | .var f, w => if (T.clo? w).isSome then some f else none
  | _, _ => none

/-- Terms whose free names and parameters carry no rank: what the machine
evaluates. -/
def good (t : Tm S X) : Bool :=
  (freeNames t).all (fun n => (T.nameRank n).isNone) &&
    (freeParams t).all fun p => (T.paramRank p).isNone

variable [DecidableEq S]

/-- **The closure relation.**  A source term against a target term: equal
leaves (no closure symbol in the source), congruence, and a source lambda
against a closure whose arguments respect the ranks and whose rule instance
has the lambda's binders and a related body. -/
def rel : Tm S X → Tm S X → Bool
  | .sym s, t => decide (t = .sym s) && (T.rule s).isNone
  | .fn F, t => decide (t = .fn F)
  | .var n, t => decide (t = .var n)
  | .pvar x, t => decide (t = .pvar x)
  | .quote c, t => decide (t = .quote c)
  | .ctx ks c, t => decide (t = .ctx ks c)
  | .pquote _, _ => false
  | .lam x own b, t =>
      match T.clo? t with
      | some (κ, vs, r) =>
          T.argsOK κ vs && decide (x = r.x) && decide (own = r.own) && rel b (r.inst vs)
      | none => false
  | .app f a, .app f' a' => rel f f' && rel a a'
  | .letP p w b, .letP p' w' b' => rel p p' && rel w w' && rel b b'
  | .alt t₁ t₂, .alt t₁' t₂' => rel t₁ t₁' && rel t₂ t₂'
  | _, _ => false

/-- A well-formed table: a rule's own names and parameter have its rank, and
its body is first-order and closed except for its own names, parameters and
lambda parameter. -/
structure WF : Prop where
  own_rank : ∀ κ r, T.rule κ = some r → ∀ y ∈ r.own, T.ownerRank y = some (T.rank κ)
  x_rank : ∀ κ r, T.rule κ = some r → T.paramRank r.x = some (T.rank κ)
  body_lamFree : ∀ κ r, T.rule κ = some r → r.body.lamFree = true
  body_names : ∀ κ r, T.rule κ = some r → ∀ n ∈ freeNames r.body, ownKey r.own n = true
  body_params : ∀ κ r, T.rule κ = some r → ∀ p ∈ freeParams r.body, p ∈ r.params ∨ p = r.x

/-- Related substitutions. -/
def SubRel (θ θ' : Sub S X) : Prop := ∀ n, OptRel (fun a b => T.rel a b = true) (θ n) (θ' n)

/-- A substitution whose values carry no rank. -/
def GoodSub (θ : Sub S X) : Prop := ∀ n v, θ n = some v → T.good v = true

/-- Stores whose values relate to themselves (no closure symbol). -/
def StoreOK (σ : GStore S X) : Prop := ∀ n g, σ n = some g → T.rel g.toTm g.toTm = true

/-- Related results: related terms, identical stores, a good target term and
a sound store. -/
def RR (r r' : Tm S X × GStore S X) : Prop :=
  T.rel r.1 r'.1 = true ∧ r.2 = r'.2 ∧ T.good r'.1 = true ∧ T.StoreOK r.2

end CloTable

/-! ## The target machine -/

variable [DecidableEq S]

/-- One unfolding of the target machine. -/
def stepD (T : CloTable S X) (prog : S → Option (Tm S X)) (rec : Runner S X) : Runner S X :=
  fun π σ t =>
    match T.clo? t with
    | some _ => some [(t, σ)]
    | none =>
      match t with
      | .fn F =>
          match prog F with
          | some e => rec (π ++ [0]) σ e
          | none => some [(.fn F, σ)]
      | .app f a =>
          bindOpt (rec (π ++ [0]) σ f) fun r₁ =>
          bindOpt (rec (π ++ [1]) r₁.2 a) fun r₂ =>
            match T.clo? r₁.1 with
            | some (_, vs, r) =>
                rec (π ++ [2]) r₂.2 (activate .static r₂.2 (π ++ [2]) r.x r.own (r.inst vs) r₂.1)
            | none => some [(.app r₁.1 r₂.1, r₂.2)]
      | .letP p w b =>
          match T.letClo? p w with
          | some f => rec π σ (subst (Sub.single f w) Sub.none b)
          | none =>
              bindOpt (rec (π ++ [0]) σ w) fun r₁ =>
                match T.ground? (act r₁.2 r₁.1) with
                | some g =>
                    match matchT r₁.2 p g.toTm with
                    | some σ₂ => rec (π ++ [1]) σ₂ b
                    | none => some []
                | none =>
                    match p with
                    | .var f => rec (π ++ [1]) r₁.2 (subst (Sub.single f r₁.1) Sub.none b)
                    | _ => some []
      | .alt t₁ t₂ =>
          match rec (π ++ [0]) σ t₁, rec (π ++ [1]) σ t₂ with
          | some l, some r => some (l ++ r)
          | _, _ => none
      | v => some [(v, σ)]

/-- The target machine with `n` units of fuel. -/
def runD (T : CloTable S X) (prog : S → Option (Tm S X)) : ℕ → Runner S X
  | 0 => fun _ _ _ => none
  | n + 1 => stepD T prog (runD T prog n)

/-- The target machine's answers. -/
def answersD (T : CloTable S X) (prog : S → Option (Tm S X)) (n : ℕ) (t : Tm S X) :
    Option (List (Tm S X)) :=
  (runD T prog n [] Store.empty t).map (List.map fun r => act r.2 r.1)

/-! ## Generic lemmas -/

theorem OptRel.cases {α β : Type*} {R : α → β → Prop} :
    ∀ {o : Option α} {o' : Option β}, OptRel R o o' →
      (o = none ∧ o' = none) ∨ ∃ a b, o = some a ∧ o' = some b ∧ R a b
  | some a, some b, h => Or.inr ⟨a, b, rfl, rfl, h⟩
  | none, none, _ => Or.inl ⟨rfl, rfl⟩
  | some _, none, h => h.elim
  | none, some _, h => h.elim

theorem forall₂_append {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₁' : List β} {l₂ : List α} {l₂' : List β},
      List.Forall₂ R l₁ l₁' → List.Forall₂ R l₂ l₂' → List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h hs, h' => .cons h (forall₂_append hs h')

theorem bindAll_rel {α α' β β' : Type*} {R : α → α' → Prop} {Q : β → β' → Prop}
    {g : α → Option (List β)} {g' : α' → Option (List β')}
    (hg : ∀ a a', R a a' → OptRel (List.Forall₂ Q) (g a) (g' a')) :
    ∀ {l : List α} {l' : List α'}, List.Forall₂ R l l' →
      OptRel (List.Forall₂ Q) (bindAll l g) (bindAll l' g')
  | [], [], .nil => by simp [bindAll, OptRel]
  | a :: as, a' :: as', .cons h hs => by
      have h1 := hg a a' h
      have h2 := bindAll_rel hg hs
      unfold bindAll
      rcases OptRel.cases h1 with ⟨e1, e1'⟩ | ⟨x, x', e1, e1', hx⟩
      · simp [e1, e1', OptRel]
      · rcases OptRel.cases h2 with ⟨e2, e2'⟩ | ⟨y, y', e2, e2', hy⟩
        · simp [e1, e1', e2, e2', OptRel]
        · simpa [e1, e1', e2, e2', OptRel] using forall₂_append hx hy

theorem bindOpt_rel {α α' β β' : Type*} {R : α → α' → Prop} {Q : β → β' → Prop}
    {o : Option (List α)} {o' : Option (List α')}
    {g : α → Option (List β)} {g' : α' → Option (List β')}
    (ho : OptRel (List.Forall₂ R) o o')
    (hg : ∀ a a', R a a' → OptRel (List.Forall₂ Q) (g a) (g' a')) :
    OptRel (List.Forall₂ Q) (bindOpt o g) (bindOpt o' g') := by
  rcases OptRel.cases ho with ⟨rfl, rfl⟩ | ⟨l, l', rfl, rfl, hl⟩
  · simp [bindOpt, OptRel]
  · exact bindAll_rel hg hl

omit [DecidableEq X] [DecidableEq S] in
theorem symSpine_app {f a : Tm S X} {κ : S} {vs : List (Tm S X)}
    (h : symSpine (.app f a) = some (κ, vs)) :
    ∃ us, symSpine f = some (κ, us) ∧ vs = us ++ [a] := by
  cases hf : symSpine f with
  | none => simp [symSpine, hf] at h
  | some p =>
      obtain ⟨κ', us⟩ := p
      simp only [symSpine, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨us, rfl, rfl⟩

omit [DecidableEq S] in
/-- Substitution maps a symbol spine to the spine of the substituted arguments. -/
theorem symSpine_subst {θ φ : Sub S X} : ∀ {t : Tm S X} {κ : S} {vs : List (Tm S X)},
    symSpine t = some (κ, vs) → symSpine (subst θ φ t) = some (κ, vs.map (subst θ φ))
  | .sym s, κ, vs, h => by
      simp only [symSpine, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | .app f a, κ, vs, h => by
      obtain ⟨us, hf, rfl⟩ := symSpine_app h
      simp [subst, symSpine, symSpine_subst hf]
  | .fn _, _, _, h | .var _, _, _, h | .pvar _, _, _, h | .lam _ _ _, _, _, h
  | .quote _, _, _, h | .pquote _, _, _, h | .letP _ _ _, _, _, h | .alt _ _, _, _, h => by
      simp [symSpine] at h

omit [DecidableEq X] [DecidableEq S] in
/-- The arguments of a spine are among its subterms. -/
theorem symSpine_args_sub : ∀ {t : Tm S X} {κ : S} {vs : List (Tm S X)},
    symSpine t = some (κ, vs) → ∀ v ∈ vs, ∀ (P : Tm S X → Prop),
      (∀ f a, P (.app f a) → P f ∧ P a) → P t → P v
  | .sym s, κ, vs, h, v, hv, _, _, _ => by
      simp only [symSpine, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      cases hv
  | .app f a, κ, vs, h, v, hv, P, hP, ht => by
      obtain ⟨us, hf, rfl⟩ := symSpine_app h
      rcases List.mem_append.mp hv with hv | hv
      · exact symSpine_args_sub hf v hv P hP (hP f a ht).1
      · simp only [List.mem_singleton] at hv
        subst hv
        exact (hP f _ ht).2
  | .fn _, _, _, h, _, _, _, _, _ | .var _, _, _, h, _, _, _, _, _
  | .pvar _, _, _, h, _, _, _, _, _ | .lam _ _ _, _, _, h, _, _, _, _, _
  | .quote _, _, _, h, _, _, _, _, _ | .pquote _, _, _, h, _, _, _, _, _
  | .letP _ _ _, _, _, h, _, _, _, _, _ | .alt _ _, _, _, h, _, _, _, _, _ => by
      simp [symSpine] at h

omit [DecidableEq S] in
theorem paramSub_map (f : Tm S X → Tm S X) :
    ∀ (ps : List (Nm X)) (vs : List (Tm S X)) (p : Nm X),
      paramSub ps (vs.map f) p = (paramSub ps vs p).map f
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | q :: ps, v :: vs, p => by
      simp only [List.map_cons, paramSub]
      by_cases hp : p = q
      · simp [hp]
      · simp [hp, paramSub_map f ps vs p]

omit [DecidableEq S] in
theorem paramSub_eq_none_iff :
    ∀ (ps : List (Nm X)) (vs : List (Tm S X)) (p : Nm X), vs.length = ps.length →
      (paramSub ps vs p = none ↔ p ∉ ps)
  | [], [], _, _ => by simp [paramSub, Sub.none]
  | q :: ps, v :: vs, p, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [paramSub, List.mem_cons, not_or]
      by_cases hp : p = q
      · simp [hp]
      · simp [hp, paramSub_eq_none_iff ps vs p h]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

omit [DecidableEq S] in
theorem paramSub_mem :
    ∀ (ps : List (Nm X)) (vs : List (Tm S X)) (p : Nm X) (v : Tm S X),
      paramSub ps vs p = some v → v ∈ vs
  | [], _, _, _, h => by simp [paramSub, Sub.none] at h
  | _ :: _, [], _, _, h => by simp [paramSub, Sub.none] at h
  | q :: ps, w :: vs, p, v, h => by
      simp only [paramSub] at h
      by_cases hp : p = q
      · simp only [hp, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [hp, if_false] at h
        exact List.mem_cons_of_mem _ (paramSub_mem ps vs p v h)

omit [DecidableEq S] in
/-- Substitutions that agree on the free names and parameters of a term act
alike on it. -/
theorem subst_eq_of_agree : ∀ (t : Tm S X) (θ₁ θ₂ φ₁ φ₂ : Sub S X),
    (∀ n ∈ freeNames t, θ₁ n = θ₂ n) → (∀ p ∈ freeParams t, φ₁ p = φ₂ p) →
    subst θ₁ φ₁ t = subst θ₂ φ₂ t
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .var n, θ₁, θ₂, _, _, hθ, _ => by simp [subst, hθ n (by simp [freeNames])]
  | .pvar x, _, _, φ₁, φ₂, _, hφ => by simp [subst, hφ x (by simp [freeParams])]
  | .lam x own b, θ₁, θ₂, φ₁, φ₂, hθ, hφ => by
      simp only [subst]
      congr 1
      apply subst_eq_of_agree b
      · intro n hn
        unfold Sub.hideOwn
        by_cases ho : ownKey own n
        · simp [ho]
        · simp only [ho]
          exact hθ n (by simp [freeNames, hn, ho])
      · intro p hp
        unfold Sub.hideParam
        by_cases hx : p = x
        · simp [hx]
        · simp only [hx, if_false]
          exact hφ p (by simp [freeParams, hp, hx])
  | .app f a, θ₁, θ₂, φ₁, φ₂, hθ, hφ => by
      simp only [freeNames, freeParams, List.mem_append] at hθ hφ
      simp only [subst]
      rw [subst_eq_of_agree f θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inl h)) (fun p h => hφ p (Or.inl h)),
        subst_eq_of_agree a θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inr h)) (fun p h => hφ p (Or.inr h))]
  | .quote _, _, _, _, _, _, _ => rfl
  | .ctx _ _, _, _, _, _, _, _ => rfl
  | .pquote c, θ₁, θ₂, φ₁, φ₂, hθ, hφ => by
      simp only [freeNames, freeParams] at hθ hφ
      simp only [subst]
      rw [subst_eq_of_agree c θ₁ θ₂ φ₁ φ₂ hθ hφ]
  | .letP p w b, θ₁, θ₂, φ₁, φ₂, hθ, hφ => by
      simp only [freeNames, freeParams, List.mem_append] at hθ hφ
      simp only [subst]
      rw [subst_eq_of_agree p θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inl (Or.inl h)))
          (fun q h => hφ q (Or.inl (Or.inl h))),
        subst_eq_of_agree w θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inl (Or.inr h)))
          (fun q h => hφ q (Or.inl (Or.inr h))),
        subst_eq_of_agree b θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inr h)) (fun q h => hφ q (Or.inr h))]
  | .alt t₁ t₂, θ₁, θ₂, φ₁, φ₂, hθ, hφ => by
      simp only [freeNames, freeParams, List.mem_append] at hθ hφ
      simp only [subst]
      rw [subst_eq_of_agree t₁ θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inl h)) (fun p h => hφ p (Or.inl h)),
        subst_eq_of_agree t₂ θ₁ θ₂ φ₁ φ₂ (fun n h => hθ n (Or.inr h)) (fun p h => hφ p (Or.inr h))]

omit [DecidableEq S] in
/-- Where the free names of a substituted term come from. -/
theorem mem_freeNames_subst : ∀ (t : Tm S X) (θ φ : Sub S X) (m : Nm X),
    m ∈ freeNames (subst θ φ t) →
      (m ∈ freeNames t ∧ θ m = none) ∨ (∃ n w, θ n = some w ∧ m ∈ freeNames w) ∨
        ∃ p w, φ p = some w ∧ m ∈ freeNames w
  | .sym _, _, _, _, h | .fn _, _, _, _, h | .quote _, _, _, _, h => by
      simp [subst, freeNames] at h
  | .var n, θ, _, m, h => by
      cases hn : θ n with
      | none =>
          simp only [subst, hn, Option.getD_none, freeNames, List.mem_singleton] at h
          subst h
          exact Or.inl ⟨by simp [freeNames], hn⟩
      | some w =>
          simp only [subst, hn, Option.getD_some] at h
          exact Or.inr (Or.inl ⟨n, w, hn, h⟩)
  | .pvar x, _, φ, m, h => by
      cases hx : φ x with
      | none => simp [subst, hx, freeNames] at h
      | some w =>
          simp only [subst, hx, Option.getD_some] at h
          exact Or.inr (Or.inr ⟨x, w, hx, h⟩)
  | .lam x own b, θ, φ, m, h => by
      simp only [subst, freeNames, List.mem_filter, Bool.not_eq_true'] at h
      obtain ⟨hm, ho⟩ := h
      rcases mem_freeNames_subst b _ _ m hm with ⟨hb, hθ⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
      · refine Or.inl ⟨by simp [freeNames, hb, ho], ?_⟩
        simpa [Sub.hideOwn, ho] using hθ
      · refine Or.inr (Or.inl ⟨n, w, ?_, hw⟩)
        unfold Sub.hideOwn at hn
        split at hn
        · cases hn
        · exact hn
      · refine Or.inr (Or.inr ⟨p, w, ?_, hw⟩)
        unfold Sub.hideParam at hp
        split at hp
        · cases hp
        · exact hp
  | .app f a, θ, φ, m, h => by
      simp only [subst, freeNames, List.mem_append] at h
      rcases h with h | h
      · rcases mem_freeNames_subst f θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeNames_subst a θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  | .pquote c, θ, φ, m, h => by
      simp only [subst, freeNames] at h
      rcases mem_freeNames_subst c θ φ m h with ⟨h1, h2⟩ | h | h
      · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | .letP p w b, θ, φ, m, h => by
      simp only [subst, freeNames, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases mem_freeNames_subst p θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeNames_subst w θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeNames_subst b θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  | .alt t₁ t₂, θ, φ, m, h => by
      simp only [subst, freeNames, List.mem_append] at h
      rcases h with h | h
      · rcases mem_freeNames_subst t₁ θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeNames_subst t₂ θ φ m h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeNames, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

omit [DecidableEq S] in
/-- Where the free parameters of a substituted term come from. -/
theorem mem_freeParams_subst : ∀ (t : Tm S X) (θ φ : Sub S X) (q : Nm X),
    q ∈ freeParams (subst θ φ t) →
      (q ∈ freeParams t ∧ φ q = none) ∨ (∃ n w, θ n = some w ∧ q ∈ freeParams w) ∨
        ∃ p w, φ p = some w ∧ q ∈ freeParams w
  | .sym _, _, _, _, h | .fn _, _, _, _, h | .quote _, _, _, _, h => by
      simp [subst, freeParams] at h
  | .var n, θ, _, q, h => by
      cases hn : θ n with
      | none => simp [subst, hn, freeParams] at h
      | some w =>
          simp only [subst, hn, Option.getD_some] at h
          exact Or.inr (Or.inl ⟨n, w, hn, h⟩)
  | .pvar x, _, φ, q, h => by
      cases hx : φ x with
      | none =>
          simp only [subst, hx, Option.getD_none, freeParams, List.mem_singleton] at h
          subst h
          exact Or.inl ⟨by simp [freeParams], hx⟩
      | some w =>
          simp only [subst, hx, Option.getD_some] at h
          exact Or.inr (Or.inr ⟨x, w, hx, h⟩)
  | .lam x own b, θ, φ, q, h => by
      simp only [subst, freeParams, List.mem_filter, decide_eq_true_eq] at h
      obtain ⟨hq, hqx⟩ := h
      rcases mem_freeParams_subst b _ _ q hq with ⟨hb, hφ⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
      · refine Or.inl ⟨by simp [freeParams, hb, hqx], ?_⟩
        simpa [Sub.hideParam, hqx] using hφ
      · refine Or.inr (Or.inl ⟨n, w, ?_, hw⟩)
        unfold Sub.hideOwn at hn
        split at hn
        · cases hn
        · exact hn
      · refine Or.inr (Or.inr ⟨p, w, ?_, hw⟩)
        unfold Sub.hideParam at hp
        split at hp
        · cases hp
        · exact hp
  | .app f a, θ, φ, q, h => by
      simp only [subst, freeParams, List.mem_append] at h
      rcases h with h | h
      · rcases mem_freeParams_subst f θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeParams_subst a θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  | .pquote c, θ, φ, q, h => by
      simp only [subst, freeParams] at h
      rcases mem_freeParams_subst c θ φ q h with ⟨h1, h2⟩ | h | h
      · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  | .letP p w b, θ, φ, q, h => by
      simp only [subst, freeParams, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases mem_freeParams_subst p θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeParams_subst w θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeParams_subst b θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  | .alt t₁ t₂, θ, φ, q, h => by
      simp only [subst, freeParams, List.mem_append] at h
      rcases h with h | h
      · rcases mem_freeParams_subst t₁ θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases mem_freeParams_subst t₂ θ φ q h with ⟨h1, h2⟩ | h | h
        · exact Or.inl ⟨by simp [freeParams, h1], h2⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

omit [DecidableEq S] in
/-- **Dropping commutes with substitution** (on a rule instance).  Substituting
under the rule's binders into its instance equals instantiating the rule with
the substituted arguments, provided the rule body is first-order and closed
except for its own names and parameters, and the arguments avoid the rule's
own names and lambda parameter. -/
theorem subst_inst_comm (own : List X) (x : Nm X) (ps : List (Nm X)) (vs : List (Tm S X))
    (θ φ : Sub S X) (hlen : vs.length = ps.length)
    (hargs : ∀ v ∈ vs, (∀ n ∈ freeNames v, ownKey own n = false) ∧ x ∉ freeParams v) :
    ∀ B : Tm S X, B.lamFree = true → (∀ n ∈ freeNames B, ownKey own n = true) →
      (∀ p ∈ freeParams B, p ∈ ps ∨ p = x) →
      subst (θ.hideOwn own) (φ.hideParam x) (subst Sub.none (paramSub ps vs) B) =
        subst Sub.none (paramSub ps (vs.map (subst θ φ))) B
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .quote _, _, _, _ => rfl
  | .ctx _ _, _, _, _ => rfl
  | .var n, _, hB, _ => by
      have hn := hB n (by simp [freeNames])
      simp [subst, Sub.none, Sub.hideOwn, hn]
  | .pvar p, _, _, hP => by
      simp only [subst, paramSub_map]
      cases hps : paramSub ps vs p with
      | some v =>
          simp only [Option.getD_some, Option.map_some]
          obtain ⟨hvn, hvx⟩ := hargs v (paramSub_mem ps vs p v hps)
          apply subst_eq_of_agree
          · intro n hn
            simp [Sub.hideOwn, hvn n hn]
          · intro q hq
            have hqx : q ≠ x := fun e => hvx (e ▸ hq)
            simp [Sub.hideParam, hqx]
      | none =>
          have hpx : p = x := by
            rcases hP p (by simp [freeParams]) with h | h
            · exact absurd h ((paramSub_eq_none_iff ps vs p hlen).1 hps)
            · exact h
          subst hpx
          simp [subst, Sub.hideParam]
  | .lam _ _ _, hlf, _, _ => by simp [Tm.lamFree] at hlf
  | .app f a, hlf, hB, hP => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hlf
      simp only [freeNames, freeParams, List.mem_append] at hB hP
      simp only [subst]
      rw [subst_inst_comm own x ps vs θ φ hlen hargs f hlf.1 (fun n h => hB n (Or.inl h))
          (fun p h => hP p (Or.inl h)),
        subst_inst_comm own x ps vs θ φ hlen hargs a hlf.2 (fun n h => hB n (Or.inr h))
          (fun p h => hP p (Or.inr h))]
  | .pquote c, hlf, hB, hP => by
      simp only [Tm.lamFree] at hlf
      simp only [freeNames, freeParams] at hB hP
      simp only [subst]
      rw [subst_inst_comm own x ps vs θ φ hlen hargs c hlf hB hP]
  | .letP p w b, hlf, hB, hP => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hlf
      simp only [freeNames, freeParams, List.mem_append] at hB hP
      simp only [subst]
      rw [subst_inst_comm own x ps vs θ φ hlen hargs p hlf.1.1
          (fun n h => hB n (Or.inl (Or.inl h))) (fun q h => hP q (Or.inl (Or.inl h))),
        subst_inst_comm own x ps vs θ φ hlen hargs w hlf.1.2
          (fun n h => hB n (Or.inl (Or.inr h))) (fun q h => hP q (Or.inl (Or.inr h))),
        subst_inst_comm own x ps vs θ φ hlen hargs b hlf.2
          (fun n h => hB n (Or.inr h)) (fun q h => hP q (Or.inr h))]
  | .alt t₁ t₂, hlf, hB, hP => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hlf
      simp only [freeNames, freeParams, List.mem_append] at hB hP
      simp only [subst]
      rw [subst_inst_comm own x ps vs θ φ hlen hargs t₁ hlf.1 (fun n h => hB n (Or.inl h))
          (fun p h => hP p (Or.inl h)),
        subst_inst_comm own x ps vs θ φ hlen hargs t₂ hlf.2 (fun n h => hB n (Or.inr h))
          (fun p h => hP p (Or.inr h))]

/-! ## The closure relation -/

namespace CloTable

variable (T : CloTable S X)

omit [DecidableEq X] [DecidableEq S] in
theorem clo?_eq_some {t : Tm S X} {κ : S} {vs : List (Tm S X)} {r : ApplyRule S X} :
    T.clo? t = some (κ, vs, r) ↔
      symSpine t = some (κ, vs) ∧ T.rule κ = some r ∧ vs.length = r.params.length := by
  unfold clo?
  constructor
  · intro h
    obtain ⟨⟨κ', vs'⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hl : vs'.length = r'.params.length
    · simp only [hl, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hs, hr, hl⟩
    · simp [hl] at h
  · rintro ⟨hs, hr, hl⟩
    simp [hs, hr, hl]

omit [DecidableEq S] in
theorem clo?_subst {θ φ : Sub S X} {t : Tm S X} {κ : S} {vs : List (Tm S X)}
    {r : ApplyRule S X} (h : T.clo? t = some (κ, vs, r)) :
    T.clo? (subst θ φ t) = some (κ, vs.map (subst θ φ), r) := by
  obtain ⟨hs, hr, hl⟩ := (T.clo?_eq_some).1 h
  exact (T.clo?_eq_some).2 ⟨symSpine_subst hs, hr, by simpa using hl⟩

omit [DecidableEq X] [DecidableEq S] in
theorem hasClo_of_clo? {t : Tm S X} {c : S × List (Tm S X) × ApplyRule S X}
    (h : T.clo? t = some c) : T.hasClo t = true := by
  cases t with
  | sym s => simp [hasClo, h]
  | app f a => simp [hasClo, h]
  | _ =>
      obtain ⟨κ, vs, r⟩ := c
      have := ((T.clo?_eq_some).1 h).1
      simp [symSpine] at this

omit [DecidableEq S] in
theorem good_iff {t : Tm S X} :
    T.good t = true ↔ (∀ n ∈ freeNames t, T.nameRank n = none) ∧
      ∀ p ∈ freeParams t, T.paramRank p = none := by
  simp [good, List.all_eq_true]

omit [DecidableEq S] in
theorem argsOK_iff {κ : S} {vs : List (Tm S X)} :
    T.argsOK κ vs = true ↔ ∀ v ∈ vs, (∀ n ∈ freeNames v, T.rankOK κ (T.nameRank n) = true) ∧
      ∀ p ∈ freeParams v, T.rankOK κ (T.paramRank p) = true := by
  simp [argsOK, List.all_eq_true]

theorem rel_sym {s₀ : S} {t : Tm S X} :
    T.rel (.sym s₀) t = true ↔ t = .sym s₀ ∧ T.rule s₀ = none := by
  simp [rel]

theorem rel_fn {F : S} {t : Tm S X} : T.rel (.fn F) t = true ↔ t = .fn F := by simp [rel]

theorem rel_var {n : Nm X} {t : Tm S X} : T.rel (.var n) t = true ↔ t = .var n := by simp [rel]

theorem rel_pvar {x : Nm X} {t : Tm S X} : T.rel (.pvar x) t = true ↔ t = .pvar x := by
  simp [rel]

theorem rel_quote {c t : Tm S X} : T.rel (.quote c) t = true ↔ t = .quote c := by simp [rel]

theorem rel_ctx {ks : List (Nm X)} {c t : Tm S X} :
    T.rel (.ctx ks c) t = true ↔ t = .ctx ks c := by simp [rel]

theorem rel_pquote {c t : Tm S X} : T.rel (.pquote c) t = false := by simp [rel]

theorem rel_app {f a t : Tm S X} :
    T.rel (.app f a) t = true ↔
      ∃ f' a', t = .app f' a' ∧ T.rel f f' = true ∧ T.rel a a' = true := by
  cases t <;> simp [rel]

theorem rel_letP {p w b t : Tm S X} :
    T.rel (.letP p w b) t = true ↔ ∃ p' w' b', t = .letP p' w' b' ∧ T.rel p p' = true ∧
      T.rel w w' = true ∧ T.rel b b' = true := by
  cases t <;> simp [rel, and_assoc]

theorem rel_alt {t₁ t₂ t : Tm S X} :
    T.rel (.alt t₁ t₂) t = true ↔
      ∃ t₁' t₂', t = .alt t₁' t₂' ∧ T.rel t₁ t₁' = true ∧ T.rel t₂ t₂' = true := by
  cases t <;> simp [rel]

theorem rel_lam {x : Nm X} {own : List X} {b t : Tm S X} :
    T.rel (.lam x own b) t = true ↔ ∃ κ vs r, T.clo? t = some (κ, vs, r) ∧
      T.argsOK κ vs = true ∧ x = r.x ∧ own = r.own ∧ T.rel b (r.inst vs) = true := by
  simp only [rel]
  cases h : T.clo? t with
  | none => simp
  | some c =>
      obtain ⟨κ, vs, r⟩ := c
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        exact ⟨κ, vs, r, ⟨rfl, rfl, rfl⟩, h1, h2, h3, h4⟩
      · rintro ⟨κ', vs', r', ⟨rfl, rfl, rfl⟩, h1, h2, h3, h4⟩
        exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- A source term that is not a lambda relates only to targets whose symbol
spine is not a closure: its head symbol has no rule, or the spine is a closure
applied to more arguments. -/
theorem rel_spine : ∀ (s t : Tm S X), T.rel s t = true → ∀ κ vs, symSpine t = some (κ, vs) →
    (∃ x own b, s = .lam x own b) ∨ T.rule κ = none ∨
      ∃ r, T.rule κ = some r ∧ r.params.length < vs.length
  | .sym s₀, t, h, κ, vs, hs => by
      obtain ⟨rfl, hr⟩ := (T.rel_sym).1 h
      simp only [symSpine, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      exact Or.inr (Or.inl hr)
  | .app f a, t, h, κ, vs, hs => by
      obtain ⟨f', a', rfl, hf, -⟩ := (T.rel_app).1 h
      obtain ⟨us, hus, rfl⟩ := symSpine_app hs
      rcases rel_spine f f' hf κ us hus with ⟨x, own, b, rfl⟩ | hn | ⟨r, hr, hlt⟩
      · obtain ⟨κ', vs', r', hc, -⟩ := (T.rel_lam).1 hf
        obtain ⟨hs', hr', hl'⟩ := (T.clo?_eq_some).1 hc
        rw [hus] at hs'
        simp only [Option.some.injEq, Prod.mk.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        exact Or.inr (Or.inr ⟨r', hr', by simp [hl']⟩)
      · exact Or.inr (Or.inl hn)
      · exact Or.inr (Or.inr ⟨r, hr, by simp; omega⟩)
  | .lam x own b, _, _, _, _, _ => Or.inl ⟨x, own, b, rfl⟩
  | .fn _, t, h, _, _, hs => by
      rw [(T.rel_fn).1 h] at hs
      simp [symSpine] at hs
  | .var _, t, h, _, _, hs => by
      rw [(T.rel_var).1 h] at hs
      simp [symSpine] at hs
  | .pvar _, t, h, _, _, hs => by
      rw [(T.rel_pvar).1 h] at hs
      simp [symSpine] at hs
  | .quote _, t, h, _, _, hs => by
      rw [(T.rel_quote).1 h] at hs
      simp [symSpine] at hs
  | .ctx _ _, t, h, _, _, hs => by
      rw [(T.rel_ctx).1 h] at hs
      simp [symSpine] at hs
  | .pquote _, t, h, _, _, _ => by simp [T.rel_pquote] at h
  | .letP _ _ _, t, h, _, _, hs => by
      obtain ⟨_, _, _, rfl, -⟩ := (T.rel_letP).1 h
      simp [symSpine] at hs
  | .alt _ _, t, h, _, _, hs => by
      obtain ⟨_, _, rfl, -⟩ := (T.rel_alt).1 h
      simp [symSpine] at hs

/-- A source term that is not a lambda never relates to a closure. -/
theorem clo?_eq_none_of_rel {s t : Tm S X} (h : T.rel s t = true)
    (hs : ∀ x own b, s ≠ .lam x own b) : T.clo? t = none := by
  cases hc : T.clo? t with
  | none => rfl
  | some c =>
      obtain ⟨κ, vs, r⟩ := c
      obtain ⟨hsp, hr, hl⟩ := (T.clo?_eq_some).1 hc
      rcases T.rel_spine s t h κ vs hsp with ⟨x, own, b, rfl⟩ | hn | ⟨r', hr', hlt⟩
      · exact absurd rfl (hs x own b)
      · rw [hr] at hn
        cases hn
      · rw [hr] at hr'
        cases hr'
        omega

/-- Without lambdas, the relation is equality. -/
theorem rel_eq_of_lamFree : ∀ (s t : Tm S X), T.rel s t = true → s.lamFree = true → t = s
  | .sym _, _, h, _ => ((T.rel_sym).1 h).1
  | .fn _, _, h, _ => (T.rel_fn).1 h
  | .var _, _, h, _ => (T.rel_var).1 h
  | .pvar _, _, h, _ => (T.rel_pvar).1 h
  | .quote _, _, h, _ => (T.rel_quote).1 h
  | .ctx _ _, _, h, _ => (T.rel_ctx).1 h
  | .pquote _, _, h, _ => by simp [T.rel_pquote] at h
  | .lam _ _ _, _, _, hl => by simp [Tm.lamFree] at hl
  | .app f a, _, h, hl => by
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      rw [rel_eq_of_lamFree f f' hf hl.1, rel_eq_of_lamFree a a' ha hl.2]
  | .letP p w b, _, h, hl => by
      obtain ⟨p', w', b', rfl, hp, hw, hb⟩ := (T.rel_letP).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      rw [rel_eq_of_lamFree p p' hp hl.1.1, rel_eq_of_lamFree w w' hw hl.1.2,
        rel_eq_of_lamFree b b' hb hl.2]
  | .alt t₁ t₂, _, h, hl => by
      obtain ⟨t₁', t₂', rfl, h₁, h₂⟩ := (T.rel_alt).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      rw [rel_eq_of_lamFree t₁ t₁' h₁ hl.1, rel_eq_of_lamFree t₂ t₂' h₂ hl.2]

/-- A target related to a lambda-free source has no closure. -/
theorem hasClo_eq_false_of_rel : ∀ (s t : Tm S X), T.rel s t = true → s.lamFree = true →
    T.hasClo t = false
  | .sym s₀, t, h, _ => by
      obtain ⟨rfl, hr⟩ := (T.rel_sym).1 h
      simp [hasClo, clo?, symSpine, hr]
  | .fn _, t, h, _ => by rw [(T.rel_fn).1 h]; rfl
  | .var _, t, h, _ => by rw [(T.rel_var).1 h]; rfl
  | .pvar _, t, h, _ => by rw [(T.rel_pvar).1 h]; rfl
  | .quote _, t, h, _ => by rw [(T.rel_quote).1 h]; rfl
  | .ctx _ _, t, h, _ => by rw [(T.rel_ctx).1 h]; rfl
  | .pquote _, _, h, _ => by simp [T.rel_pquote] at h
  | .lam _ _ _, _, _, hl => by simp [Tm.lamFree] at hl
  | .app f a, t, h, hl => by
      have hc := T.clo?_eq_none_of_rel h (fun _ _ _ e => by cases e)
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [hasClo, hc, hasClo_eq_false_of_rel f f' hf hl.1, hasClo_eq_false_of_rel a a' ha hl.2]
  | .letP p w b, t, h, hl => by
      obtain ⟨p', w', b', rfl, hp, hw, hb⟩ := (T.rel_letP).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [hasClo, hasClo_eq_false_of_rel p p' hp hl.1.1, hasClo_eq_false_of_rel w w' hw hl.1.2,
        hasClo_eq_false_of_rel b b' hb hl.2]
  | .alt t₁ t₂, t, h, hl => by
      obtain ⟨t₁', t₂', rfl, h₁, h₂⟩ := (T.rel_alt).1 h
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [hasClo, hasClo_eq_false_of_rel t₁ t₁' h₁ hl.1, hasClo_eq_false_of_rel t₂ t₂' h₂ hl.2]

/-- A target related to a source with a lambda has a closure. -/
theorem hasClo_of_rel_not_lamFree : ∀ (s t : Tm S X), T.rel s t = true → s.lamFree = false →
    T.hasClo t = true
  | .lam _ _ _, t, h, _ => by
      obtain ⟨κ, vs, r, hc, -⟩ := (T.rel_lam).1 h
      exact T.hasClo_of_clo? hc
  | .app f a, t, h, hl => by
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 h
      simp only [Tm.lamFree, Bool.and_eq_false_iff] at hl
      rcases hl with hl | hl
      · simp [hasClo, hasClo_of_rel_not_lamFree f f' hf hl]
      · simp [hasClo, hasClo_of_rel_not_lamFree a a' ha hl]
  | .letP p w b, t, h, hl => by
      obtain ⟨p', w', b', rfl, hp, hw, hb⟩ := (T.rel_letP).1 h
      simp only [Tm.lamFree, Bool.and_eq_false_iff] at hl
      rcases hl with (hl | hl) | hl
      · simp [hasClo, hasClo_of_rel_not_lamFree p p' hp hl]
      · simp [hasClo, hasClo_of_rel_not_lamFree w w' hw hl]
      · simp [hasClo, hasClo_of_rel_not_lamFree b b' hb hl]
  | .alt t₁ t₂, t, h, hl => by
      obtain ⟨t₁', t₂', rfl, h₁, h₂⟩ := (T.rel_alt).1 h
      simp only [Tm.lamFree, Bool.and_eq_false_iff] at hl
      rcases hl with hl | hl
      · simp [hasClo, hasClo_of_rel_not_lamFree t₁ t₁' h₁ hl]
      · simp [hasClo, hasClo_of_rel_not_lamFree t₂ t₂' h₂ hl]
  | .pquote _, _, h, _ => by simp [T.rel_pquote] at h
  | .sym _, _, _, hl | .fn _, _, _, hl | .var _, _, _, hl | .pvar _, _, _, hl
  | .quote _, _, _, hl => by simp [Tm.lamFree] at hl

omit [DecidableEq X] [DecidableEq S] in
theorem toGVal?_eq_none_of_not_lamFree : ∀ (s : Tm S X), s.lamFree = false → s.toGVal? = none
  | .lam _ _ _, _ => rfl
  | .app f a, hl => by
      simp only [Tm.lamFree, Bool.and_eq_false_iff] at hl
      rcases hl with hl | hl
      · simp [Tm.toGVal?, toGVal?_eq_none_of_not_lamFree f hl]
      · simp only [Tm.toGVal?, toGVal?_eq_none_of_not_lamFree a hl]
        cases f.toGVal? <;> rfl
  | .letP _ _ _, _ => rfl
  | .alt _ _, _ => rfl
  | .pquote _, _ => rfl
  | .sym _, hl | .fn _, hl | .var _, hl | .pvar _, hl | .quote _, hl => by
      simp [Tm.lamFree] at hl

/-- The source's ground test and the machine's agree on related terms. -/
theorem toGVal?_eq_ground? {s t : Tm S X} (h : T.rel s t = true) : s.toGVal? = T.ground? t := by
  unfold ground?
  cases hl : s.lamFree
  · rw [if_pos (T.hasClo_of_rel_not_lamFree s t h hl), toGVal?_eq_none_of_not_lamFree s hl]
  · rw [if_neg (by simp [T.hasClo_eq_false_of_rel s t h hl]), T.rel_eq_of_lamFree s t h hl]

/-! ## Substitution preserves the relation -/

omit [DecidableEq S] in
theorem good_app {f a : Tm S X} :
    T.good (.app f a) = true ↔ T.good f = true ∧ T.good a = true := by
  simp only [good_iff, freeNames, freeParams, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun n hn => h1 n (Or.inl hn), fun p hp => h2 p (Or.inl hp)⟩,
      ⟨fun n hn => h1 n (Or.inr hn), fun p hp => h2 p (Or.inr hp)⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun n hn => hn.elim (h1 n) (h3 n), fun p hp => hp.elim (h2 p) (h4 p)⟩

omit [DecidableEq S] in
theorem good_letP {p w b : Tm S X} :
    T.good (.letP p w b) = true ↔ T.good p = true ∧ T.good w = true ∧ T.good b = true := by
  simp only [good_iff, freeNames, freeParams, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun n hn => h1 n (Or.inl (Or.inl hn)), fun q hq => h2 q (Or.inl (Or.inl hq))⟩,
      ⟨fun n hn => h1 n (Or.inl (Or.inr hn)), fun q hq => h2 q (Or.inl (Or.inr hq))⟩,
      ⟨fun n hn => h1 n (Or.inr hn), fun q hq => h2 q (Or.inr hq)⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    exact ⟨fun n hn => hn.elim (fun h => h.elim (h1 n) (h3 n)) (h5 n),
      fun q hq => hq.elim (fun h => h.elim (h2 q) (h4 q)) (h6 q)⟩

omit [DecidableEq S] in
theorem good_alt {t₁ t₂ : Tm S X} :
    T.good (.alt t₁ t₂) = true ↔ T.good t₁ = true ∧ T.good t₂ = true := by
  simp only [good_iff, freeNames, freeParams, List.mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun n hn => h1 n (Or.inl hn), fun p hp => h2 p (Or.inl hp)⟩,
      ⟨fun n hn => h1 n (Or.inr hn), fun p hp => h2 p (Or.inr hp)⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun n hn => hn.elim (h1 n) (h3 n), fun p hp => hp.elim (h2 p) (h4 p)⟩

omit [DecidableEq S] in
theorem goodSub_hideOwn {θ : Sub S X} (h : T.GoodSub θ) (own : List X) :
    T.GoodSub (θ.hideOwn own) := by
  intro n v hv
  unfold Sub.hideOwn at hv
  split at hv
  · cases hv
  · exact h n v hv

omit [DecidableEq S] in
theorem goodSub_hideParam {φ : Sub S X} (h : T.GoodSub φ) (x : Nm X) :
    T.GoodSub (φ.hideParam x) := by
  intro n v hv
  unfold Sub.hideParam at hv
  split at hv
  · cases hv
  · exact h n v hv

theorem subRel_hideOwn {θ θ' : Sub S X} (h : T.SubRel θ θ') (own : List X) :
    T.SubRel (θ.hideOwn own) (θ'.hideOwn own) := by
  intro n
  unfold Sub.hideOwn
  split
  · trivial
  · exact h n

theorem subRel_hideParam {φ φ' : Sub S X} (h : T.SubRel φ φ') (x : Nm X) :
    T.SubRel (φ.hideParam x) (φ'.hideParam x) := by
  intro n
  unfold Sub.hideParam
  split
  · trivial
  · exact h n

omit [DecidableEq S] in
/-- Substituting values without ranks keeps closure arguments within ranks. -/
theorem argsOK_subst {κ : S} {vs : List (Tm S X)} {θ φ : Sub S X} (h : T.argsOK κ vs = true)
    (hθ : T.GoodSub θ) (hφ : T.GoodSub φ) : T.argsOK κ (vs.map (subst θ φ)) = true := by
  rw [argsOK_iff] at h ⊢
  intro v' hv'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hv'
  obtain ⟨hn, hp⟩ := h v hv
  refine ⟨fun m hm => ?_, fun q hq => ?_⟩
  · rcases mem_freeNames_subst v θ φ m hm with ⟨hm', -⟩ | ⟨n, w, hn', hw⟩ | ⟨p, w, hp', hw⟩
    · exact hn m hm'
    · simp [((T.good_iff).1 (hθ n w hn')).1 m hw, rankOK]
    · simp [((T.good_iff).1 (hφ p w hp')).1 m hw, rankOK]
  · rcases mem_freeParams_subst v θ φ q hq with ⟨hq', -⟩ | ⟨n, w, hn', hw⟩ | ⟨p, w, hp', hw⟩
    · exact hp q hq'
    · simp [((T.good_iff).1 (hθ n w hn')).2 q hw, rankOK]
    · simp [((T.good_iff).1 (hφ p w hp')).2 q hw, rankOK]

/-- **Substitution preserves the closure relation.**  For related substitutions
whose target values carry no rank, substituting into related terms gives related
terms.  At a closure, the substitution under the lambda's binders on the source
side meets the substitution of the closure's arguments on the target side:
dropping commutes with substitution (`subst_inst_comm`), because the ranks keep
the arguments away from the rule's own names and parameter. -/
theorem rel_subst (hT : T.WF) : ∀ (s t : Tm S X) (θ θ' φ φ' : Sub S X),
    T.rel s t = true → T.SubRel θ θ' → T.SubRel φ φ' → T.GoodSub θ' → T.GoodSub φ' →
    T.rel (subst θ φ s) (subst θ' φ' t) = true
  | .sym s₀, t, _, _, _, _, h, _, _, _, _ => by
      obtain ⟨rfl, hr⟩ := (T.rel_sym).1 h
      simp [subst, T.rel_sym, hr]
  | .fn F, t, _, _, _, _, h, _, _, _, _ => by
      rw [(T.rel_fn).1 h]
      simp [subst, T.rel_fn]
  | .quote c, t, _, _, _, _, h, _, _, _, _ => by
      rw [(T.rel_quote).1 h]
      simp [subst, T.rel_quote]
  | .ctx _ _, t, _, _, _, _, h, _, _, _, _ => by
      rw [(T.rel_ctx).1 h]
      simp [subst, T.rel_ctx]
  | .pquote _, _, _, _, _, _, h, _, _, _, _ => by simp [T.rel_pquote] at h
  | .var n, t, θ, θ', _, _, h, hθ, _, _, _ => by
      rw [(T.rel_var).1 h]
      rcases OptRel.cases (hθ n) with ⟨e, e'⟩ | ⟨a, b, e, e', hab⟩
      · simp [subst, e, e', T.rel_var]
      · simp [subst, e, e', hab]
  | .pvar x, t, _, _, φ, φ', h, _, hφ, _, _ => by
      rw [(T.rel_pvar).1 h]
      rcases OptRel.cases (hφ x) with ⟨e, e'⟩ | ⟨a, b, e, e', hab⟩
      · simp [subst, e, e', T.rel_pvar]
      · simp [subst, e, e', hab]
  | .app f a, t, θ, θ', φ, φ', h, hθ, hφ, gθ, gφ => by
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 h
      simp only [subst]
      exact (T.rel_app).2 ⟨_, _, rfl, rel_subst hT f f' θ θ' φ φ' hf hθ hφ gθ gφ,
        rel_subst hT a a' θ θ' φ φ' ha hθ hφ gθ gφ⟩
  | .letP p w b, t, θ, θ', φ, φ', h, hθ, hφ, gθ, gφ => by
      obtain ⟨p', w', b', rfl, hp, hw, hb⟩ := (T.rel_letP).1 h
      simp only [subst]
      exact (T.rel_letP).2 ⟨_, _, _, rfl, rel_subst hT p p' θ θ' φ φ' hp hθ hφ gθ gφ,
        rel_subst hT w w' θ θ' φ φ' hw hθ hφ gθ gφ, rel_subst hT b b' θ θ' φ φ' hb hθ hφ gθ gφ⟩
  | .alt t₁ t₂, t, θ, θ', φ, φ', h, hθ, hφ, gθ, gφ => by
      obtain ⟨t₁', t₂', rfl, h₁, h₂⟩ := (T.rel_alt).1 h
      simp only [subst]
      exact (T.rel_alt).2 ⟨_, _, rfl, rel_subst hT t₁ t₁' θ θ' φ φ' h₁ hθ hφ gθ gφ,
        rel_subst hT t₂ t₂' θ θ' φ φ' h₂ hθ hφ gθ gφ⟩
  | .lam x own b, t, θ, θ', φ, φ', h, hθ, hφ, gθ, gφ => by
      obtain ⟨κ, vs, r, hc, hargs, rfl, rfl, hb⟩ := (T.rel_lam).1 h
      obtain ⟨-, hr, hl⟩ := (T.clo?_eq_some).1 hc
      simp only [subst]
      refine (T.rel_lam).2 ⟨κ, vs.map (subst θ' φ'), r, T.clo?_subst hc,
        T.argsOK_subst hargs gθ gφ, rfl, rfl, ?_⟩
      have hav : ∀ v ∈ vs, (∀ n ∈ freeNames v, ownKey r.own n = false) ∧ r.x ∉ freeParams v := by
        intro v hv
        obtain ⟨hn, hp⟩ := (T.argsOK_iff).1 hargs v hv
        refine ⟨fun n hn' => ?_, fun hx => ?_⟩
        · cases n with
          | src y =>
              by_contra hk
              have hy : y ∈ r.own := by simpa [ownKey] using hk
              have := hn (.src y) hn'
              simp [nameRank, hT.own_rank κ r hr y hy, rankOK] at this
          | inst ρ m => simp [ownKey]
        · have := hp r.x hx
          simp [hT.x_rank κ r hr, rankOK] at this
      have hcomm : r.inst (vs.map (subst θ' φ')) =
          subst (θ'.hideOwn r.own) (φ'.hideParam r.x) (r.inst vs) := by
        unfold ApplyRule.inst
        rw [subst_inst_comm r.own r.x r.params vs θ' φ' hl hav r.body (hT.body_lamFree κ r hr)
          (hT.body_names κ r hr) (hT.body_params κ r hr)]
      rw [hcomm]
      exact rel_subst hT b (r.inst vs) _ _ _ _ hb (T.subRel_hideOwn hθ r.own)
        (T.subRel_hideParam hφ r.x) (T.goodSub_hideOwn gθ r.own) (T.goodSub_hideParam gφ r.x)

/-! ## Matching related patterns -/

omit [DecidableEq X] [DecidableEq S] in
theorem toGVal?_toTm : ∀ {t : Tm S X} {g : GVal S X}, t.toGVal? = some g → g.toTm = t
  | .sym _, g, h => by
      simp only [Tm.toGVal?, Option.some.injEq] at h
      subst h
      rfl
  | .app f a, g, h => by
      simp only [Tm.toGVal?] at h
      cases hf : f.toGVal? with
      | none => simp [hf] at h
      | some f' =>
          cases ha : a.toGVal? with
          | none => simp [hf, ha] at h
          | some a' =>
              simp only [hf, ha, Option.some.injEq] at h
              subst h
              simp [GVal.toTm, toGVal?_toTm hf, toGVal?_toTm ha]
  | .quote _, g, h => by
      simp only [Tm.toGVal?, Option.some.injEq] at h
      subst h
      rfl
  | .ctx _ _, g, h => by
      simp only [Tm.toGVal?, Option.some.injEq] at h
      subst h
      rfl
  | .fn _, _, h | .var _, _, h | .pvar _, _, h | .lam _ _ _, _, h | .pquote _, _, h
  | .letP _ _ _, _, h | .alt _ _, _, h => by simp [Tm.toGVal?] at h

omit [DecidableEq X] [DecidableEq S] in
theorem GVal.lamFree_toTm : ∀ g : GVal S X, g.toTm.lamFree = true
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, Tm.lamFree, GVal.lamFree_toTm f, GVal.lamFree_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

omit [DecidableEq S] in
theorem GVal.freeNames_toTm : ∀ g : GVal S X, freeNames g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeNames, GVal.freeNames_toTm f, GVal.freeNames_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

omit [DecidableEq S] in
theorem GVal.freeParams_toTm : ∀ g : GVal S X, freeParams g.toTm = []
  | .sym _ => rfl
  | .app f a => by simp [GVal.toTm, freeParams, GVal.freeParams_toTm f, GVal.freeParams_toTm a]
  | .quote _ => rfl
  | .ctx _ _ => rfl

/-- A closure pattern matches only a closure spine of the same constructor and
length. -/
theorem matchT_symSpine : ∀ (p t : Tm S X) (σ σ' : GStore S X) (κ : S) (us : List (Tm S X)),
    symSpine p = some (κ, us) → matchT σ p t = some σ' →
      ∃ ts, symSpine t = some (κ, ts) ∧ ts.length = us.length
  | .sym s, t, σ, σ', κ, us, hp, hm => by
      simp only [symSpine, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have e : matchT σ (.sym s) t = if Tm.sym s = t then some σ else none := by
        cases t <;> rfl
      rw [e] at hm
      split at hm
      · rename_i ht
        subst ht
        exact ⟨[], rfl, rfl⟩
      · cases hm
  | .app f a, t, σ, σ', κ, us, hp, hm => by
      obtain ⟨us₀, hf, rfl⟩ := symSpine_app hp
      cases t with
      | app t₁ t₂ =>
          simp only [matchT] at hm
          cases h1 : matchT σ f t₁ with
          | none => rw [h1] at hm; cases hm
          | some σ₁ =>
              obtain ⟨ts, hts, hl⟩ := matchT_symSpine f t₁ σ σ₁ κ us₀ hf h1
              exact ⟨ts ++ [t₂], by simp [symSpine, hts], by simp [hl]⟩
      | _ => simp [matchT] at hm
  | .fn _, _, _, _, _, _, hp, _ | .var _, _, _, _, _, _, hp, _
  | .pvar _, _, _, _, _, _, hp, _ | .lam _ _ _, _, _, _, _, _, hp, _
  | .quote _, _, _, _, _, _, hp, _ | .pquote _, _, _, _, _, _, hp, _
  | .letP _ _ _, _, _, _, _, _, hp, _ | .alt _ _, _, _, _, _, _, hp, _ => by
      simp [symSpine] at hp

/-- A closure never matches a term without closures. -/
theorem matchT_clo_eq_none {p t : Tm S X} {c : S × List (Tm S X) × ApplyRule S X}
    (hp : T.clo? p = some c) (ht : T.hasClo t = false) (σ : GStore S X) :
    matchT σ p t = none := by
  obtain ⟨κ, us, r⟩ := c
  obtain ⟨hsp, hr, hl⟩ := (T.clo?_eq_some).1 hp
  cases hm : matchT σ p t with
  | none => rfl
  | some σ' =>
      obtain ⟨ts, hts, htl⟩ := matchT_symSpine p t σ σ' κ us hsp hm
      have hc : T.clo? t = some (κ, ts, r) := (T.clo?_eq_some).2 ⟨hts, hr, by omega⟩
      rw [T.hasClo_of_clo? hc] at ht
      cases ht

theorem rel_eq_iff {p p' t : Tm S X} (h : T.rel p p' = true) (ht : t.lamFree = true)
    (hc : T.hasClo t = false) : p = t ↔ p' = t := by
  cases hl : p.lamFree
  · constructor
    · rintro rfl
      rw [hl] at ht
      cases ht
    · rintro rfl
      rw [T.hasClo_of_rel_not_lamFree p _ h hl] at hc
      cases hc
  · rw [T.rel_eq_of_lamFree p p' h hl]

/-- **Related patterns match alike** against terms without lambdas and
closures: a lambda and its closure both fail, everything else is equal or
matched componentwise. -/
theorem matchT_rel : ∀ (p p' t : Tm S X) (σ : GStore S X), T.rel p p' = true →
    t.lamFree = true → T.hasClo t = false → matchT σ p t = matchT σ p' t
  | .var _, _, _, _, h, _, _ => by rw [(T.rel_var).1 h]
  | .sym _, _, _, _, h, _, _ => by rw [((T.rel_sym).1 h).1]
  | .fn _, _, _, _, h, _, _ => by rw [(T.rel_fn).1 h]
  | .pvar _, _, _, _, h, _, _ => by rw [(T.rel_pvar).1 h]
  | .quote _, _, _, _, h, _, _ => by rw [(T.rel_quote).1 h]
  | .ctx _ _, _, _, _, h, _, _ => by rw [(T.rel_ctx).1 h]
  | .pquote _, _, _, _, h, _, _ => by simp [T.rel_pquote] at h
  | .lam x own b, p', t, σ, h, ht, hc => by
      obtain ⟨κ, vs, r, hcl, -⟩ := (T.rel_lam).1 h
      rw [T.matchT_clo_eq_none hcl hc σ]
      have e : matchT σ (.lam x own b) t = if Tm.lam x own b = t then some σ else none := by
        cases t <;> rfl
      rw [e, if_neg]
      rintro rfl
      simp [Tm.lamFree] at ht
  | .app f a, p', t, σ, h, ht, hc => by
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 h
      cases t with
      | app t₁ t₂ =>
          simp only [Tm.lamFree, Bool.and_eq_true] at ht
          have hc' := hc
          simp only [hasClo, Bool.or_eq_false_iff] at hc'
          obtain ⟨⟨-, hc₁⟩, hc₂⟩ := hc'
          simp only [matchT]
          rw [matchT_rel f f' t₁ σ hf ht.1 hc₁]
          cases matchT σ f' t₁ with
          | none => rfl
          | some σ₁ => exact matchT_rel a a' t₂ σ₁ ha ht.2 hc₂
      | _ => simp [matchT]
  | .letP p₁ w b, p', t, σ, h, ht, hc => by
      obtain ⟨p₁', w', b', rfl, -⟩ := (T.rel_letP).1 h
      have e1 : matchT σ (.letP p₁ w b) t = if Tm.letP p₁ w b = t then some σ else none := by
        cases t <;> rfl
      have e2 : matchT σ (.letP p₁' w' b') t =
          if Tm.letP p₁' w' b' = t then some σ else none := by
        cases t <;> rfl
      rw [e1, e2, if_congr (T.rel_eq_iff h ht hc) rfl rfl]
  | .alt t₁ t₂, p', t, σ, h, ht, hc => by
      obtain ⟨t₁', t₂', rfl, -⟩ := (T.rel_alt).1 h
      have e1 : matchT σ (.alt t₁ t₂) t = if Tm.alt t₁ t₂ = t then some σ else none := by
        cases t <;> rfl
      have e2 : matchT σ (.alt t₁' t₂') t = if Tm.alt t₁' t₂' = t then some σ else none := by
        cases t <;> rfl
      rw [e1, e2, if_congr (T.rel_eq_iff h ht hc) rfl rfl]

/-- Matching a related pattern against a value that relates to itself keeps the
store sound. -/
theorem matchT_storeOK : ∀ (p t : Tm S X) (σ σ' : GStore S X) (p' : Tm S X),
    T.rel p p' = true → T.StoreOK σ → T.rel t t = true → matchT σ p t = some σ' → T.StoreOK σ'
  | .var n, t, σ, σ', _, _, hσ, ht, hm => by
      simp only [matchT] at hm
      cases hg : t.toGVal? with
      | none => rw [hg] at hm; cases hm
      | some g =>
          rw [hg] at hm
          simp only at hm
          intro m g' hm'
          unfold refineStep at hm
          cases hσn : σ n with
          | none =>
              rw [hσn] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              by_cases hmn : m = n
              · subst hmn
                simp only [if_true, Option.some.injEq] at hm'
                subst hm'
                rw [toGVal?_toTm hg]
                exact ht
              · simp only [hmn, if_false] at hm'
                exact hσ m g' hm'
          | some w =>
              rw [hσn] at hm
              simp only at hm
              split at hm
              · simp only [Option.some.injEq] at hm
                subst hm
                exact hσ m g' hm'
              · cases hm
  | .app f a, t, σ, σ', p', hp, hσ, ht, hm => by
      obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 hp
      cases t with
      | app t₁ t₂ =>
          simp only [rel, Bool.and_eq_true] at ht
          simp only [matchT] at hm
          cases h1 : matchT σ f t₁ with
          | none => rw [h1] at hm; cases hm
          | some σ₁ =>
              rw [h1] at hm
              exact matchT_storeOK a t₂ σ₁ σ' a' ha (matchT_storeOK f t₁ σ σ₁ f' hf hσ ht.1 h1)
                ht.2 hm
      | _ => simp [matchT] at hm
  | .pquote _, _, _, _, _, hp, _, _, _ => by simp [T.rel_pquote] at hp
  | .sym s, t, σ, σ', _, _, hσ, _, hm | .fn s, t, σ, σ', _, _, hσ, _, hm
  | .pvar s, t, σ, σ', _, _, hσ, _, hm => by
      have e : ∀ q : Tm S X, (∀ n, q ≠ .var n) → (∀ f a, q ≠ .app f a) →
          (∀ c, q ≠ .pquote c) → (∀ c, q ≠ .quote c) →
          matchT σ q t = if q = t then some σ else none := by
        intro q h1 h2 h3 h4
        cases q <;> first
          | (exfalso; exact h1 _ rfl) | (exfalso; exact h2 _ _ rfl) | (exfalso; exact h3 _ rfl)
          | (exfalso; exact h4 _ rfl)
          | (cases t <;> rfl)
      rw [e _ (by intro n e; cases e) (by intro f a e; cases e) (by intro c e; cases e)
        (by intro c e; cases e)] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact hσ
      · cases hm
  | .quote c, t, σ, σ', _, _, hσ, _, hm => by
      cases t with
      | quote c₂ =>
          simp only [matchT] at hm
          cases hce : codeEq c c₂ with
          | true =>
              rw [if_pos hce] at hm
              simp only [Option.some.injEq] at hm
              subst hm
              exact hσ
          | false =>
              simp only [hce, Bool.false_eq_true, if_false] at hm
              cases hm
      | sym _ | fn _ | var _ | pvar _ | lam _ _ _ | app _ _ | pquote _ | ctx _ _ | letP _ _ _ | alt _ _ =>
          simp only [matchT] at hm
          split at hm
          · simp only [Option.some.injEq] at hm
            subst hm
            exact hσ
          · cases hm
  | .ctx ks c, t, σ, σ', _, _, hσ, _, hm => by
      have e : matchT σ (.ctx ks c) t = if Tm.ctx ks c = t then some σ else none := by
        cases t <;> rfl
      rw [e] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact hσ
      · cases hm
  | .lam x own b, t, σ, σ', _, _, hσ, _, hm => by
      have e : matchT σ (.lam x own b) t = if Tm.lam x own b = t then some σ else none := by
        cases t <;> rfl
      rw [e] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact hσ
      · cases hm
  | .letP p₁ w b, t, σ, σ', _, _, hσ, _, hm => by
      have e : matchT σ (.letP p₁ w b) t = if Tm.letP p₁ w b = t then some σ else none := by
        cases t <;> rfl
      rw [e] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact hσ
      · cases hm
  | .alt t₁ t₂, t, σ, σ', _, _, hσ, _, hm => by
      have e : matchT σ (.alt t₁ t₂) t = if Tm.alt t₁ t₂ = t then some σ else none := by
        cases t <;> rfl
      rw [e] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact hσ
      · cases hm

/-! ## Invariants -/

omit [DecidableEq S] in
theorem good_subst {t : Tm S X} {θ φ : Sub S X} (ht : T.good t = true) (hθ : T.GoodSub θ)
    (hφ : T.GoodSub φ) : T.good (subst θ φ t) = true := by
  rw [good_iff] at ht ⊢
  refine ⟨fun m hm => ?_, fun q hq => ?_⟩
  · rcases mem_freeNames_subst t θ φ m hm with ⟨hm', -⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
    · exact ht.1 m hm'
    · exact ((T.good_iff).1 (hθ n w hn)).1 m hw
    · exact ((T.good_iff).1 (hφ p w hp)).1 m hw
  · rcases mem_freeParams_subst t θ φ q hq with ⟨hq', -⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
    · exact ht.2 q hq'
    · exact ((T.good_iff).1 (hθ n w hn)).2 q hw
    · exact ((T.good_iff).1 (hφ p w hp)).2 q hw

omit [DecidableEq S] in
/-- Activating a closure of a good term on a good argument gives a good body:
the rule's own names become activation copies, its parameters the closure's
arguments, its lambda parameter the argument. -/
theorem good_activate (hT : T.WF) {c : Tm S X} {κ : S} {vs : List (Tm S X)} {r : ApplyRule S X}
    (hc : T.clo? c = some (κ, vs, r)) (hgc : T.good c = true) {a : Tm S X}
    (ha : T.good a = true) (σ : GStore S X) (ρ : Path) :
    T.good (activate .static σ ρ r.x r.own (r.inst vs) a) = true := by
  obtain ⟨hsp, hr, hl⟩ := (T.clo?_eq_some).1 hc
  have hvs : ∀ v ∈ vs, T.good v = true := fun v hv =>
    symSpine_args_sub hsp v hv (fun t => T.good t = true) (fun f a h => (T.good_app).1 h) hgc
  rw [good_iff]
  simp only [activate]
  refine ⟨fun m hm => ?_, fun q hq => ?_⟩
  · rcases mem_freeNames_subst _ _ _ m hm with ⟨hm', hθ⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
    · unfold ApplyRule.inst at hm'
      rcases mem_freeNames_subst _ _ _ m hm' with ⟨hm'', -⟩ | ⟨n, w, hn, -⟩ | ⟨p, w, hp, hw⟩
      · have hk := hT.body_names κ r hr m hm''
        simp [renameOwn, hk] at hθ
      · simp [Sub.none] at hn
      · exact ((T.good_iff).1 (hvs w (paramSub_mem _ _ _ _ hp))).1 m hw
    · simp only [renameOwn] at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        simp only [freeNames, List.mem_singleton] at hw
        subst hw
        rfl
      · cases hn
    · simp only [Sub.single] at hp
      split at hp
      · simp only [Option.some.injEq] at hp
        subst hp
        exact ((T.good_iff).1 ha).1 m hw
      · cases hp
  · rcases mem_freeParams_subst _ _ _ q hq with ⟨hq', hφ⟩ | ⟨n, w, hn, hw⟩ | ⟨p, w, hp, hw⟩
    · unfold ApplyRule.inst at hq'
      rcases mem_freeParams_subst _ _ _ q hq' with ⟨hq'', hps⟩ | ⟨n, w, hn, -⟩ | ⟨p, w, hp, hw⟩
      · rcases hT.body_params κ r hr q hq'' with hin | hx
        · exact absurd hin ((paramSub_eq_none_iff _ _ _ hl).1 hps)
        · subst hx
          simp [Sub.single] at hφ
      · simp [Sub.none] at hn
      · exact ((T.good_iff).1 (hvs w (paramSub_mem _ _ _ _ hp))).2 q hw
    · simp only [renameOwn] at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        simp [freeParams] at hw
      · cases hn
    · simp only [Sub.single] at hp
      split at hp
      · simp only [Option.some.injEq] at hp
        subst hp
        exact ((T.good_iff).1 ha).2 q hw
      · cases hp

theorem subRel_none : T.SubRel Sub.none Sub.none := fun _ => trivial

omit [DecidableEq S] in
theorem goodSub_none : T.GoodSub (Sub.none : Sub S X) := fun _ _ h => by cases h

theorem subRel_single {x : Nm X} {a a' : Tm S X} (h : T.rel a a' = true) :
    T.SubRel (Sub.single x a) (Sub.single x a') := by
  intro n
  by_cases hn : n = x
  · simp [Sub.single, hn, OptRel, h]
  · simp [Sub.single, hn, OptRel]

omit [DecidableEq S] in
theorem goodSub_single {x : Nm X} {a : Tm S X} (h : T.good a = true) :
    T.GoodSub (Sub.single x a) := by
  intro n v hv
  simp only [Sub.single] at hv
  split at hv
  · simp only [Option.some.injEq] at hv
    subst hv
    exact h
  · cases hv

theorem subRel_renameOwn (ρ : Path) (own : List X) :
    T.SubRel (renameOwn ρ own) (renameOwn ρ own) := by
  intro n
  unfold renameOwn
  split
  · simp [OptRel, rel]
  · trivial

omit [DecidableEq S] in
theorem goodSub_renameOwn (ρ : Path) (own : List X) : T.GoodSub (renameOwn ρ own : Sub S X) := by
  intro n v hv
  unfold renameOwn at hv
  split at hv
  · simp only [Option.some.injEq] at hv
    subst hv
    simp [good, freeNames, freeParams, nameRank]
  · cases hv

theorem subRel_envSub {σ : GStore S X} (hσ : T.StoreOK σ) : T.SubRel (envSub σ) (envSub σ) := by
  intro n
  unfold envSub
  cases hn : σ n with
  | none => trivial
  | some g => exact hσ n g hn

omit [DecidableEq S] in
theorem goodSub_envSub (σ : GStore S X) : T.GoodSub (envSub σ) := by
  intro n v hv
  unfold envSub at hv
  cases hn : σ n with
  | none => rw [hn] at hv; cases hv
  | some g =>
      rw [hn] at hv
      simp only [Option.map_some, Option.some.injEq] at hv
      subst hv
      simp [good, GVal.freeNames_toTm, GVal.freeParams_toTm]

theorem storeOK_empty : T.StoreOK (Store.empty : GStore S X) := fun _ _ h => by cases h

/-- The environment action preserves the relation. -/
theorem rel_act (hT : T.WF) {σ : GStore S X} (hσ : T.StoreOK σ) {s t : Tm S X}
    (h : T.rel s t = true) : T.rel (act σ s) (act σ t) = true :=
  T.rel_subst hT s t _ _ _ _ h (T.subRel_envSub hσ) T.subRel_none (T.goodSub_envSub σ)
    T.goodSub_none

theorem rel_var_right {s : Tm S X} {f : Nm X} (h : T.rel s (.var f) = true) : s = .var f := by
  cases s with
  | var n => rw [(T.rel_var).1 h]
  | lam x own b =>
      obtain ⟨κ, vs, r, hc, -⟩ := (T.rel_lam).1 h
      simp [clo?, symSpine] at hc
  | _ => simp [rel] at h

/-- The source's `let`-of-a-lambda test and the machine's `let`-of-a-closure
test agree on related terms. -/
theorem letLam?_eq_letClo? {p w p' w' : Tm S X} (hp : T.rel p p' = true)
    (hw : T.rel w w' = true) : letLam? p w = T.letClo? p' w' := by
  cases p with
  | var f =>
      rw [(T.rel_var).1 hp]
      cases w with
      | lam x own b =>
          obtain ⟨κ, vs, r, hc, -⟩ := (T.rel_lam).1 hw
          simp [letLam?, letClo?, hc]
      | _ =>
          have hc := T.clo?_eq_none_of_rel hw (fun _ _ _ e => by cases e)
          simp [letLam?, letClo?, hc]
  | _ =>
      cases p' with
      | var f => exact absurd (T.rel_var_right hp) (by intro e; cases e)
      | _ => simp [letLam?, letClo?]

/-- Related results give related answers. -/
theorem forall₂_act (hT : T.WF) : ∀ {L L' : List (Tm S X × GStore S X)},
    List.Forall₂ T.RR L L' →
      List.Forall₂ (fun a a' => T.rel a a' = true) (L.map fun r => act r.2 r.1)
        (L'.map fun r => act r.2 r.1)
  | [], [], .nil => List.Forall₂.nil
  | r :: _, r' :: _, .cons hr hs => by
      obtain ⟨h1, h2, -, h4⟩ := hr
      simp only [List.map_cons]
      rw [← h2]
      exact List.Forall₂.cons (T.rel_act hT h4 h1) (forall₂_act hT hs)

/-- Related lambda-free bags are equal. -/
theorem forall₂_rel_eq : ∀ {L L' : List (Tm S X)},
    List.Forall₂ (fun a a' => T.rel a a' = true) L L' → (∀ a ∈ L, a.lamFree = true) → L' = L
  | [], [], .nil, _ => rfl
  | a :: _, a' :: _, .cons h hs, hlf => by
      rw [T.rel_eq_of_lamFree a a' h (hlf a List.mem_cons_self),
        forall₂_rel_eq hs (fun b hb => hlf b (List.mem_cons_of_mem _ hb))]

end CloTable

/-! ## The simulation -/

open CloTable in
/-- **Defunctionalization preserves observations.**  For a well-formed closure
table, programs whose equations are related, a source term and a related good
target term: at every fuel, the model's evaluator and the target machine are
defined together, and their result bags are related pointwise, with identical
final stores. -/
theorem run_defun (T : CloTable S X) (hT : T.WF) (prog prog' : S → Option (Tm S X))
    (hprog : ∀ F, OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (prog F) (prog' F)) :
    ∀ (n : ℕ) (π : Path) (σ : GStore S X) (s t : Tm S X), T.rel s t = true →
      T.good t = true → T.StoreOK σ →
      OptRel (List.Forall₂ T.RR) (run .static prog n π σ s) (runD T prog' n π σ t) := by
  intro n
  induction n with
  | zero => intro π σ s t _ _ _; simp [run, runD, OptRel]
  | succ n ih =>
    intro π σ s t hst hgt hσ
    have single : ∀ u u' : Tm S X, T.rel u u' = true → T.good u' = true →
        OptRel (List.Forall₂ T.RR) (some [(u, σ)]) (some [(u', σ)]) := fun u u' h g =>
      List.Forall₂.cons ⟨h, rfl, g, hσ⟩ List.Forall₂.nil
    show OptRel _ (step .static prog (run .static prog n) π σ s)
      (stepD T prog' (runD T prog' n) π σ t)
    cases s with
    | lam x own b =>
        obtain ⟨κ, vs, r, hc, -⟩ := (T.rel_lam).1 hst
        simp only [step, stepD, hc]
        exact single _ _ hst hgt
    | sym s₀ =>
        obtain ⟨rfl, hr⟩ := (T.rel_sym).1 hst
        have hc : T.clo? (Tm.sym s₀ : Tm S X) = none := by simp [clo?, symSpine, hr]
        simp only [step, stepD, hc]
        exact single _ _ hst hgt
    | var m =>
        rw [(T.rel_var).1 hst] at hgt ⊢
        have hc : T.clo? (Tm.var m : Tm S X) = none := by simp [clo?, symSpine]
        simp only [step, stepD, hc]
        exact single _ _ (by simp [rel]) hgt
    | pvar m =>
        rw [(T.rel_pvar).1 hst] at hgt ⊢
        have hc : T.clo? (Tm.pvar m : Tm S X) = none := by simp [clo?, symSpine]
        simp only [step, stepD, hc]
        exact single _ _ (by simp [rel]) hgt
    | quote c =>
        rw [(T.rel_quote).1 hst] at hgt ⊢
        have hc : T.clo? (Tm.quote c : Tm S X) = none := by simp [clo?, symSpine]
        simp only [step, stepD, hc]
        exact single _ _ (by simp [rel]) hgt
    | pquote c => simp [T.rel_pquote] at hst
    | ctx ks c =>
        rw [(T.rel_ctx).1 hst] at hgt ⊢
        have hc : T.clo? (Tm.ctx ks c : Tm S X) = none := by simp [clo?, symSpine]
        simp only [step, stepD, hc]
        exact single _ _ (by simp [rel]) hgt
    | fn F =>
        rw [(T.rel_fn).1 hst] at hgt ⊢
        have hc : T.clo? (Tm.fn F : Tm S X) = none := by simp [clo?, symSpine]
        simp only [step, stepD, hc]
        rcases OptRel.cases (hprog F) with ⟨e, e'⟩ | ⟨e₀, e₀', e, e', he, hge⟩
        · rw [e, e']
          exact single _ _ (by simp [rel]) hgt
        · rw [e, e']
          exact ih _ σ e₀ e₀' he hge hσ
    | app f a =>
        have hc := T.clo?_eq_none_of_rel hst (fun _ _ _ e => by cases e)
        obtain ⟨f', a', rfl, hf, ha⟩ := (T.rel_app).1 hst
        obtain ⟨hgf, hga⟩ := (T.good_app).1 hgt
        simp only [step, stepD, hc]
        refine bindOpt_rel (ih _ σ f f' hf hgf hσ) ?_
        rintro ⟨u₁, σ₁⟩ ⟨u₁', σ₁'⟩ ⟨h₁, h₁s, hg₁, hσ₁⟩
        simp only at h₁s
        subst h₁s
        refine bindOpt_rel (ih _ σ₁ a a' ha hga hσ₁) ?_
        rintro ⟨u₂, σ₂⟩ ⟨u₂', σ₂'⟩ ⟨h₂, h₂s, hg₂, hσ₂⟩
        simp only at h₂s
        subst h₂s
        dsimp only
        have happ : T.rel (.app u₁ u₂) (.app u₁' u₂') = true := (T.rel_app).2 ⟨_, _, rfl, h₁, h₂⟩
        cases u₁ with
        | lam x own body =>
            obtain ⟨κ, vs, r, hc₁, -, rfl, rfl, hb⟩ := (T.rel_lam).1 h₁
            simp only [hc₁]
            apply ih
            · simp only [activate]
              exact T.rel_subst hT body (r.inst vs) _ _ _ _ hb (T.subRel_renameOwn _ _)
                (T.subRel_single h₂) (T.goodSub_renameOwn _ _) (T.goodSub_single hg₂)
            · exact T.good_activate hT hc₁ hg₁ hg₂ σ₂ _
            · exact hσ₂
        | _ =>
            have hc₁ := T.clo?_eq_none_of_rel h₁ (fun _ _ _ e => by cases e)
            simp only [hc₁]
            exact List.Forall₂.cons ⟨happ, rfl, (T.good_app).2 ⟨hg₁, hg₂⟩, hσ₂⟩ List.Forall₂.nil
    | letP p w b =>
        have hc := T.clo?_eq_none_of_rel hst (fun _ _ _ e => by cases e)
        obtain ⟨p', w', b', rfl, hp, hw, hb⟩ := (T.rel_letP).1 hst
        obtain ⟨hgp, hgw, hgb⟩ := (T.good_letP).1 hgt
        simp only [step, stepD, hc]
        rw [T.letLam?_eq_letClo? hp hw]
        cases hl : T.letClo? p' w' with
        | some f =>
            simp only
            apply ih
            · exact T.rel_subst hT b b' _ _ _ _ hb (T.subRel_single hw) T.subRel_none
                (T.goodSub_single hgw) T.goodSub_none
            · exact T.good_subst hgb (T.goodSub_single hgw) T.goodSub_none
            · exact hσ
        | none =>
            simp only
            refine bindOpt_rel (ih _ σ w w' hw hgw hσ) ?_
            rintro ⟨u₁, σ₁⟩ ⟨u₁', σ₁'⟩ ⟨h₁, h₁s, hg₁, hσ₁⟩
            simp only at h₁s
            subst h₁s
            dsimp only at h₁ hg₁ hσ₁ ⊢
            have hact := T.rel_act hT hσ₁ h₁
            rw [T.toGVal?_eq_ground? hact]
            cases hg : T.ground? (act σ₁ u₁') with
            | some g =>
                simp only
                have hsrc : (act σ₁ u₁).toGVal? = some g := by
                  rw [T.toGVal?_eq_ground? hact]
                  exact hg
                have hgt' : g.toTm = act σ₁ u₁ := toGVal?_toTm hsrc
                have hlf : (act σ₁ u₁).lamFree = true := by
                  rw [← hgt']
                  exact GVal.lamFree_toTm g
                have heq : act σ₁ u₁' = act σ₁ u₁ := T.rel_eq_of_lamFree _ _ hact hlf
                have hrefl : T.rel g.toTm g.toTm = true := by
                  have h' := hact
                  rw [heq] at h'
                  rw [hgt']
                  exact h'
                have hcl : T.hasClo g.toTm = false :=
                  T.hasClo_eq_false_of_rel _ _ hrefl (GVal.lamFree_toTm g)
                rw [T.matchT_rel p p' g.toTm σ₁ hp (GVal.lamFree_toTm g) hcl]
                cases hm : matchT σ₁ p' g.toTm with
                | some σ₂ =>
                    simp only
                    have hm' : matchT σ₁ p g.toTm = some σ₂ := by
                      rw [T.matchT_rel p p' g.toTm σ₁ hp (GVal.lamFree_toTm g) hcl]
                      exact hm
                    exact ih _ σ₂ b b' hb hgb (T.matchT_storeOK p g.toTm σ₁ σ₂ p' hp hσ₁ hrefl hm')
                | none =>
                    simp only
                    exact List.Forall₂.nil
            | none =>
                simp only
                cases p with
                | var f =>
                    rw [(T.rel_var).1 hp]
                    simp only
                    apply ih
                    · exact T.rel_subst hT b b' _ _ _ _ hb (T.subRel_single h₁) T.subRel_none
                        (T.goodSub_single hg₁) T.goodSub_none
                    · exact T.good_subst hgb (T.goodSub_single hg₁) T.goodSub_none
                    · exact hσ₁
                | _ =>
                    simp only
                    split
                    · exact absurd (T.rel_var_right hp) (by intro e; cases e)
                    · exact List.Forall₂.nil
    | alt t₁ t₂ =>
        have hc := T.clo?_eq_none_of_rel hst (fun _ _ _ e => by cases e)
        obtain ⟨t₁', t₂', rfl, h₁, h₂⟩ := (T.rel_alt).1 hst
        obtain ⟨hg₁, hg₂⟩ := (T.good_alt).1 hgt
        simp only [step, stepD, hc]
        have r₁ := ih (π ++ [0]) σ t₁ t₁' h₁ hg₁ hσ
        have r₂ := ih (π ++ [1]) σ t₂ t₂' h₂ hg₂ hσ
        rcases OptRel.cases r₁ with ⟨e, e'⟩ | ⟨l, l', e, e', hl⟩
        · simp [e, e', OptRel]
        · rcases OptRel.cases r₂ with ⟨e₂, e₂'⟩ | ⟨m, m', e₂, e₂', hm⟩
          · simp [e, e', e₂, e₂', OptRel]
          · simpa [e, e', e₂, e₂', OptRel] using forall₂_append hl hm

open CloTable in
/-- **The answer bags are related**, at every fuel. -/
theorem answers_defun (T : CloTable S X) (hT : T.WF) (prog prog' : S → Option (Tm S X))
    (hprog : ∀ F, OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (prog F) (prog' F))
    (n : ℕ) (s t : Tm S X) (hst : T.rel s t = true) (hgt : T.good t = true) :
    OptRel (List.Forall₂ fun a a' => T.rel a a' = true) (answers .static prog n s)
      (answersD T prog' n t) := by
  have h := run_defun T hT prog prog' hprog n [] Store.empty s t hst hgt T.storeOK_empty
  unfold answers answersD
  rcases OptRel.cases h with ⟨e, e'⟩ | ⟨L, L', e, e', hL⟩
  · simp [e, e', OptRel]
  · simp only [e, e', Option.map_some, OptRel]
    exact T.forall₂_act hT hL

open CloTable in
/-- Where the source's answers have no lambda, the machine's answers are the
same bag. -/
theorem answers_defun_lamFree (T : CloTable S X) (hT : T.WF) (prog prog' : S → Option (Tm S X))
    (hprog : ∀ F, OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (prog F) (prog' F))
    (n : ℕ) (s t : Tm S X) (hst : T.rel s t = true) (hgt : T.good t = true)
    (bag : List (Tm S X)) (hs : answers .static prog n s = some bag)
    (hlf : ∀ a ∈ bag, a.lamFree = true) : answersD T prog' n t = some bag := by
  have h := answers_defun T hT prog prog' hprog n s t hst hgt
  rw [hs] at h
  rcases OptRel.cases h with ⟨e, -⟩ | ⟨L, L', e, e', hL⟩
  · cases e
  · simp only [Option.some.injEq] at e
    subst e
    rw [e', T.forall₂_rel_eq hL hlf]

open CloTable in
/-- **Same answer bags.**  A lambda-free answer bag of the source is the
machine's answer bag of the target, and every answer bag of the target comes
from a related answer bag of the source. -/
theorem answerBag_defun (T : CloTable S X) (hT : T.WF) (prog prog' : S → Option (Tm S X))
    (hprog : ∀ F, OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (prog F) (prog' F))
    (s t : Tm S X) (hst : T.rel s t = true) (hgt : T.good t = true) :
    (∀ bag, AnswerBag .static prog s bag → (∀ a ∈ bag, a.lamFree = true) →
      ∃ n, answersD T prog' n t = some bag) ∧
    (∀ n bag', answersD T prog' n t = some bag' →
      ∃ bag, AnswerBag .static prog s bag ∧ List.Forall₂ (fun a a' => T.rel a a' = true) bag bag') := by
  refine ⟨fun bag ⟨n, hn⟩ hlf => ⟨n, answers_defun_lamFree T hT prog prog' hprog n s t hst hgt bag hn hlf⟩,
    fun n bag' hn => ?_⟩
  have h := answers_defun T hT prog prog' hprog n s t hst hgt
  rw [hn] at h
  rcases OptRel.cases h with ⟨-, e'⟩ | ⟨L, L', e, e', hL⟩
  · cases e'
  · simp only [Option.some.injEq] at e'
    subst e'
    exact ⟨L, ⟨n, e⟩, hL⟩

/-! ## The apply rule is the lifted equation, dispatch is dropping -/

/-- The rule as an equation: the lambda with its captured references as
leading parameters, the shape `lifted` produces. -/
def ApplyRule.eqn (r : ApplyRule S X) : Tm S X :=
  r.params.foldr (fun c acc => .lam c [] acc) (.lam r.x r.own r.body)

omit [DecidableEq S] in
theorem lamFree_subst {θ φ : Sub S X} (hθ : ∀ n v, θ n = some v → v.lamFree = true)
    (hφ : ∀ n v, φ n = some v → v.lamFree = true) :
    ∀ B : Tm S X, B.lamFree = true → (subst θ φ B).lamFree = true
  | .sym _, _ | .fn _, _ | .quote _, _ | .ctx _ _, _ => rfl
  | .var n, _ => by
      cases h : θ n with
      | none => simp [subst, h, Tm.lamFree]
      | some v => simpa [subst, h] using hθ n v h
  | .pvar x, _ => by
      cases h : φ x with
      | none => simp [subst, h, Tm.lamFree]
      | some v => simpa [subst, h] using hφ x v h
  | .lam _ _ _, hl => by simp [Tm.lamFree] at hl
  | .app f a, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [subst, Tm.lamFree, lamFree_subst hθ hφ f hl.1, lamFree_subst hθ hφ a hl.2]
  | .pquote c, hl => by
      simp only [Tm.lamFree] at hl
      simp [subst, Tm.lamFree, lamFree_subst hθ hφ c hl]
  | .letP p w b, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [subst, Tm.lamFree, lamFree_subst hθ hφ p hl.1.1, lamFree_subst hθ hφ w hl.1.2,
        lamFree_subst hθ hφ b hl.2]
  | .alt t₁ t₂, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp [subst, Tm.lamFree, lamFree_subst hθ hφ t₁ hl.1, lamFree_subst hθ hφ t₂ hl.2]

omit [DecidableEq S] in
/-- On first-order terms, instantiating one parameter and then the others is
instantiating all of them at once, when the first argument mentions none of the
others. -/
theorem subst_single_paramSub (p : Nm X) (v : Tm S X) (ps : List (Nm X)) (vs : List (Tm S X))
    (hv : ∀ q ∈ freeParams v, paramSub ps vs q = none) :
    ∀ B : Tm S X, B.lamFree = true →
      subst Sub.none (paramSub ps vs) (subst Sub.none (Sub.single p v) B) =
        subst Sub.none (paramSub (p :: ps) (v :: vs)) B
  | .sym _, _ | .fn _, _ | .quote _, _ | .ctx _ _, _ => rfl
  | .var _, _ => rfl
  | .pvar q, _ => by
      by_cases hq : q = p
      · subst hq
        simp only [subst, Sub.single, if_true, Option.getD_some, paramSub]
        rw [subst_eq_of_agree v Sub.none Sub.none (paramSub ps vs) Sub.none (fun _ _ => rfl)
          (fun q hq' => by simpa [Sub.none] using hv q hq'), subst_none_none]
      · simp [subst, Sub.single, paramSub, hq]
  | .lam _ _ _, hl => by simp [Tm.lamFree] at hl
  | .app f a, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [subst]
      rw [subst_single_paramSub p v ps vs hv f hl.1, subst_single_paramSub p v ps vs hv a hl.2]
  | .pquote c, hl => by
      simp only [Tm.lamFree] at hl
      simp only [subst]
      rw [subst_single_paramSub p v ps vs hv c hl]
  | .letP q w b, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [subst]
      rw [subst_single_paramSub p v ps vs hv q hl.1.1, subst_single_paramSub p v ps vs hv w hl.1.2,
        subst_single_paramSub p v ps vs hv b hl.2]
  | .alt t₁ t₂, hl => by
      simp only [Tm.lamFree, Bool.and_eq_true] at hl
      simp only [subst]
      rw [subst_single_paramSub p v ps vs hv t₁ hl.1, subst_single_paramSub p v ps vs hv t₂ hl.2]

omit [DecidableEq S] in
/-- **Dispatching a closure is dropping it into its rule**: dropping the
closure's arguments into the rule's equation gives the lambda the closure
stands for, the lambda its rule instance activates. -/
theorem dropArgs_eqn (x : Nm X) (own : List X) :
    ∀ (ps : List (Nm X)) (vs : List (Tm S X)) (B : Tm S X), ps.Nodup → x ∉ ps →
      B.lamFree = true → vs.length = ps.length → (∀ v ∈ vs, v.lamFree = true) →
      (∀ v ∈ vs, ∀ q ∈ freeParams v, q ∉ ps) →
      dropArgs (ps.foldr (fun c acc => .lam c [] acc) (.lam x own B)) vs =
        some (.lam x own (subst Sub.none (paramSub ps vs) B))
  | [], [], B, _, _, _, _, _, _ => by simp [dropArgs, paramSub, subst_none_none]
  | p :: ps, v :: vs, B, hnd, hx, hlf, hl, hvl, hv => by
      have hp : p ∉ ps := (List.nodup_cons.mp hnd).1
      have hxp : x ≠ p := fun e => hx (e ▸ List.mem_cons_self)
      simp only [List.foldr_cons, dropArgs]
      rw [subst_single_foldr_lam v ps _ hp]
      simp only [subst, none_hideOwn, single_hideParam_ne hxp]
      have hvl' : v.lamFree = true := hvl v List.mem_cons_self
      rw [dropArgs_eqn x own ps vs _ (List.nodup_cons.mp hnd).2
        (fun h => hx (List.mem_cons_of_mem _ h))
        (lamFree_subst (by intro _ _ h; cases h) (by
          intro n w h
          simp only [Sub.single] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact hvl'
          · cases h) B hlf)
        (by simpa using hl) (fun w hw => hvl w (List.mem_cons_of_mem _ hw))
        (fun w hw q hq hqs => hv w (List.mem_cons_of_mem _ hw) q hq (List.mem_cons_of_mem _ hqs))]
      congr 2
      apply subst_single_paramSub p v ps vs _ B hlf
      intro q hq
      have hlen : vs.length = ps.length := by simpa using hl
      exact (paramSub_eq_none_iff ps vs q hlen).2
        (fun hqs => hv v List.mem_cons_self q hq (List.mem_cons_of_mem _ hqs))
  | [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl

namespace CloTable

/-- A decidable check of one rule of a table. -/
def ruleOK (T : CloTable S X) (κ : S) (r : ApplyRule S X) : Bool :=
  r.own.all (fun y => decide (T.ownerRank y = some (T.rank κ))) &&
    decide (T.paramRank r.x = some (T.rank κ)) && r.body.lamFree &&
    (freeNames r.body).all (ownKey r.own) &&
    (freeParams r.body).all fun p => decide (p ∈ r.params ∨ p = r.x)

omit [DecidableEq S] in
/-- A table whose rules pass `ruleOK` is well formed. -/
theorem wf_of_ruleOK (T : CloTable S X) (h : ∀ κ r, T.rule κ = some r → T.ruleOK κ r = true) :
    T.WF := by
  have e : ∀ κ r, T.rule κ = some r →
      (∀ y ∈ r.own, T.ownerRank y = some (T.rank κ)) ∧ T.paramRank r.x = some (T.rank κ) ∧
        r.body.lamFree = true ∧ (∀ n ∈ freeNames r.body, ownKey r.own n = true) ∧
        ∀ p ∈ freeParams r.body, p ∈ r.params ∨ p = r.x := by
    intro κ r hr
    have := h κ r hr
    simp only [ruleOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  exact ⟨fun κ r hr => (e κ r hr).1, fun κ r hr => (e κ r hr).2.1, fun κ r hr => (e κ r hr).2.2.1,
    fun κ r hr => (e κ r hr).2.2.2.1, fun κ r hr => (e κ r hr).2.2.2.2⟩

end CloTable

end Mettapedia.GSLT.LanguageDef.TemplateScope

/-! ## Examples -/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.DefunCorpus

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus (Sp)

/-- Symbols of the examples: data, numerals, and closure constructors. -/
inductive DSy where
  | Pair | g | n1 | n2 | n3 | CloL | CloOut | CloIn
  deriving DecidableEq, Repr

abbrev DT := Tm DSy Sp

/-- `$y`. -/
def sv (s : Sp) : DT := .var (.src s)
/-- A parameter occurrence. -/
def pv (s : Sp) : DT := .pvar (.src s)
/-- A lambda that owns nothing. -/
def lm (s : Sp) (b : DT) : DT := .lam (.src s) [] b
def ap (f a : DT) : DT := .app f a
def k (s : DSy) : DT := .sym s
def pair (a b : DT) : DT := ap (ap (k .Pair) a) b
/-- `(let $s v b)`. -/
def lt (s : Sp) (v b : DT) : DT := .letP (sv s) v b

/-- No equations. -/
def noProg : DSy → Option DT := fun _ => none

theorem noProg_rel (T : CloTable DSy Sp) (F : DSy) :
    OptRel (fun e e' => T.rel e e' = true ∧ T.good e' = true) (noProg F) (noProg F) := by
  simp [noProg, OptRel]

/-! ### Row B4: a captured reference that the call refines -/

/-- `L = (lam z (let $y z (g $y)))`, capturing `$y` (row B4's elaboration). -/
def L : DT := lm .z (lt .y (pv .z) (ap (k .g) (sv .y)))

/-- Row B4: `(let $f L (Pair ($f 1) $y))`. -/
def srcB4 : DT := lt .f L (pair (ap (sv .f) (k .n1)) (sv .y))

/-- `L`'s apply rule, `(= (apply (CloL $y) z) (let $y z (g $y)))`: the captured
`$y` is the leading parameter. -/
def ruleL : ApplyRule DSy Sp := ⟨[.src .y], .src .z, [], .letP (pv .y) (pv .z) (ap (k .g) (pv .y))⟩

/-- Row B4 defunctionalized: `(let $f (CloL $y) (Pair ($f 1) $y))`. -/
def tgtB4 : DT := lt .f (ap (k .CloL) (sv .y)) (pair (ap (sv .f) (k .n1)) (sv .y))

def tabB4 : CloTable DSy Sp where
  rule s := if s = .CloL then some ruleL else none
  rank _ := 0
  ownerRank _ := none
  paramRank p := if p = .src .z then some 0 else none

theorem tabB4_wf : tabB4.WF := tabB4.wf_of_ruleOK (by
  intro κ r h
  cases κ <;> simp [tabB4] at h
  subst h
  decide)

/-- **Row B4.**  The source and the defunctionalized program are related; both
answer `(Pair (g 1) 1)` — the call refines the captured `$y` through the
closure, as through the lambda.  `L`'s apply rule is `L`'s lifted equation, and
dropping the closure's argument into it gives `L` back. -/
theorem defun_B4 :
    tabB4.rel srcB4 tgtB4 = true ∧ tabB4.good tgtB4 = true ∧
      answers .static noProg 40 srcB4 = some [pair (ap (k .g) (k .n1)) (k .n1)] ∧
      answersD tabB4 noProg 40 tgtB4 = some [pair (ap (k .g) (k .n1)) (k .n1)] ∧
      ruleL.eqn = lifted [.src .y] L ∧ dropArgs ruleL.eqn [sv .y] = some L := by
  decide

/-- The general theorem on row B4: every lambda-free answer bag of the source is
an answer bag of the machine. -/
theorem defun_B4_bags (bag : List DT) (h : AnswerBag .static noProg srcB4 bag)
    (hlf : ∀ a ∈ bag, a.lamFree = true) : ∃ n, answersD tabB4 noProg n tgtB4 = some bag :=
  (answerBag_defun tabB4 tabB4_wf noProg noProg (noProg_rel tabB4) srcB4 tgtB4 defun_B4.1
    defun_B4.2.1).1 bag h hlf

/-! ### Row B1: a private local renamed per call -/

/-- `L₁ = (lam z (let $y z (g $y)))` owning `$y` (row B1's elaboration). -/
def L1 : DT := .lam (.src .z) [.y] (lt .y (pv .z) (ap (k .g) (sv .y)))

/-- Row B1: `(let $f L₁ (Pair ($f 1) ($f 2)))`. -/
def srcB1 : DT := lt .f L1 (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n2)))

/-- `L₁`'s apply rule: it captures nothing, and owns `$y`. -/
def ruleL1 : ApplyRule DSy Sp := ⟨[], .src .z, [.y], lt .y (pv .z) (ap (k .g) (sv .y))⟩

/-- Row B1 defunctionalized: `(let $f CloL (Pair ($f 1) ($f 2)))`. -/
def tgtB1 : DT := lt .f (k .CloL) (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n2)))

def tabB1 : CloTable DSy Sp where
  rule s := if s = .CloL then some ruleL1 else none
  rank _ := 0
  ownerRank s := if s = .y then some 0 else none
  paramRank p := if p = .src .z then some 0 else none

theorem tabB1_wf : tabB1.WF := tabB1.wf_of_ruleOK (by
  intro κ r h
  cases κ <;> simp [tabB1] at h
  subst h
  decide)

/-- **Row B1.**  Each call of the closure renames its rule's own `$y`, as each
call of the lambda does: both answer `(Pair (g 1) (g 2))`. -/
theorem defun_B1 :
    tabB1.rel srcB1 tgtB1 = true ∧ tabB1.good tgtB1 = true ∧
      answers .static noProg 40 srcB1 = some [pair (ap (k .g) (k .n1)) (ap (k .g) (k .n2))] ∧
      answersD tabB1 noProg 40 tgtB1 = some [pair (ap (k .g) (k .n1)) (ap (k .g) (k .n2))] := by
  decide

/-! ### A curried function used partially -/

/-- `(lam z (lam w (Pair z w)))`. -/
def Lout : DT := lm .z (lm .w (pair (pv .z) (pv .w)))

/-- `(let $r (Lout 1) (Pair ($r 2) ($r 3)))`. -/
def srcCur : DT := lt .r (ap Lout (k .n1)) (pair (ap (sv .r) (k .n2)) (ap (sv .r) (k .n3)))

/-- The outer rule returns the inner closure, capturing the parameter `z`. -/
def ruleOut : ApplyRule DSy Sp := ⟨[], .src .z, [], ap (k .CloIn) (pv .z)⟩

/-- The inner rule: the captured `z` leads, then `w`. -/
def ruleIn : ApplyRule DSy Sp := ⟨[.src .z], .src .w, [], pair (pv .z) (pv .w)⟩

/-- `(let $r (CloOut 1) (Pair ($r 2) ($r 3)))`. -/
def tgtCur : DT := lt .r (ap (k .CloOut) (k .n1)) (pair (ap (sv .r) (k .n2)) (ap (sv .r) (k .n3)))

/-- The inner constructor gets the smaller rank: its argument, the outer
parameter, has rank 1. -/
def tabCur : CloTable DSy Sp where
  rule s := if s = .CloOut then some ruleOut else if s = .CloIn then some ruleIn else none
  rank s := if s = .CloOut then 1 else 0
  ownerRank _ := none
  paramRank p := if p = .src .z then some 1 else if p = .src .w then some 0 else none

theorem tabCur_wf : tabCur.WF := tabCur.wf_of_ruleOK (by
  intro κ r h
  cases κ <;> simp [tabCur] at h <;> subst h <;> decide)

/-- **A curried function used partially.**  `(Lout 1)` is the closure
`(CloIn 1)`, a first-order value bound by `let` and called twice; both programs
answer `(Pair (Pair 1 2) (Pair 1 3))`. -/
theorem defun_curried :
    tabCur.rel srcCur tgtCur = true ∧ tabCur.good tgtCur = true ∧
      answers .static noProg 40 srcCur =
        some [pair (pair (k .n1) (k .n2)) (pair (k .n1) (k .n3))] ∧
      answersD tabCur noProg 40 tgtCur =
        some [pair (pair (k .n1) (k .n2)) (pair (k .n1) (k .n3))] := by
  decide

/-! ### Closures are data -/

/-- **Closures are data; lambdas are not.**  On the model's own evaluator a
closure is a first-order term: `let` destructures `(CloL $y)`, with `$y` bound
to 1, and reads the captured value, and a pattern hole binds it.  The lambda
it stands for cannot be destructured: the same `let` has no answer, and no
hole binds it. -/
theorem closures_are_data :
    answers .static noProg 40
        (lt .y (k .n1) (.letP (ap (k .CloL) (sv .a)) (ap (k .CloL) (sv .y)) (sv .a))) =
      some [k .n1] ∧
    answers .static noProg 40 (lt .y (k .n1) (.letP (ap (k .CloL) (sv .a)) L (sv .a))) =
      some [] ∧
    (matchT Store.empty (ap (k .CloL) (sv .a)) (ap (k .CloL) (k .n1))).map
        (fun σ => σ (.src .a)) = some (some (.sym .n1)) ∧
    matchT Store.empty (sv .a) L = none := by
  decide

/-! ### Negative: a free name that a rule owns -/

/-- `L₂ = (lam z (let $y z (Pair $y $a)))`, owning `$y` and capturing `$a`. -/
def L2 : DT := .lam (.src .z) [.y] (lt .y (pv .z) (pair (sv .y) (sv .a)))

/-- `(let $a $y (let $y $w (let $f L₂ ($f 1))))`: the query's `$y` is the
spelling `L₂` owns. -/
def srcCap : DT := lt .a (sv .y) (lt .y (sv .w) (lt .f L2 (ap (sv .f) (k .n1))))

def ruleL2 : ApplyRule DSy Sp := ⟨[.src .a], .src .z, [.y], lt .y (pv .z) (pair (sv .y) (pv .a))⟩

def tgtCap : DT :=
  lt .a (sv .y) (lt .y (sv .w) (lt .f (ap (k .CloL) (sv .a)) (ap (sv .f) (k .n1))))

def tabCap : CloTable DSy Sp where
  rule s := if s = .CloL then some ruleL2 else none
  rank _ := 0
  ownerRank s := if s = .y then some 0 else none
  paramRank p := if p = .src .z then some 0 else none

/-- **Negative: the goodness hypothesis is needed.**  The two programs are
related, but the target is not good: its free `$y` is the spelling the rule
owns.  The model's substitution then captures in the source — `$a := $y` puts
`$y` under `L₂`'s own binder, where the later `$y := $w` cannot reach it — and
the source answers `(Pair 1 1)`, while the closure carries `$y` outside the
binder, receives `$w`, and the machine answers `(Pair 1 $w)`. -/
theorem defun_needs_good :
    tabCap.rel srcCap tgtCap = true ∧ tabCap.good tgtCap = false ∧
      answers .static noProg 40 srcCap = some [pair (k .n1) (k .n1)] ∧
      answersD tabCap noProg 40 tgtCap = some [pair (k .n1) (sv .w)] := by
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.DefunCorpus
