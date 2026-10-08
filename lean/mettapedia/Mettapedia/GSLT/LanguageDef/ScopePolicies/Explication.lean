import Mettapedia.GSLT.LanguageDef.ScopePolicies.Explicit

/-!
# Writing out what the query-wide policy and lexical fresh inferred

* `explicateQ` — the query-wide policy: a lambda with no crossing set shares
  every name its region uses; a `let` with none shares every name of its
  pattern.  `elabQ_explicateQ`: exact on text whose lambdas carry no crossing
  set.
* `explicateLF` — lexical fresh: the same for a lambda; a `let` shares the
  names of its pattern that it does not introduce, the names in force at each
  place being those of the source.  `elabQ_explicateLF`: on text whose lambdas
  carry no crossing set, the explicit form elaborates, under the query-wide
  policy and hence under every policy, to what lexical fresh elaborates the
  source to.
* `Program.map`, `Program.All`, `elabState_map` — a map of text that keeps the
  written names and the elaboration of every form keeps the judgment of the
  core that a program elaborates to.
* `ownList_order_witness` — where exactness stops in the slot model: a text
  whose rule-M elaboration and whose explicit form differ in the order of one
  own list, and in nothing else.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u} {X : Type v}

/-! ## The query-wide policy -/

/-- **The explicit form of a text under the query-wide policy.** -/
def explicateQ : Src S X → Src S X
  | .lam z none b => .lam z (some (Src.uses (explicateQ b))) (explicateQ b)
  | .lam z (some sh) b => .lam z (some sh) (explicateQ b)
  | .app f a => .app (explicateQ f) (explicateQ a)
  | .letS p w b none =>
      .letS (explicateQ p) (explicateQ w) (explicateQ b) (some (Src.patNames p))
  | .letS p w b (some sh) => .letS (explicateQ p) (explicateQ w) (explicateQ b) (some sh)
  | .unify p w b => .unify (explicateQ p) (explicateQ w) (explicateQ b)
  | .alt t₁ t₂ => .alt (explicateQ t₁) (explicateQ t₂)
  | .new ys b => .new ys (explicateQ b)
  | .form z b => .form z (explicateQ b)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .quote c => .quote c
  | .pquote c => .pquote c

theorem explicit_explicateQ : ∀ t : Src S X, explicit (explicateQ t) = true
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none b => by simp [explicateQ, explicit, explicit_explicateQ b]
  | .lam _ (some _) b => by simp [explicateQ, explicit, explicit_explicateQ b]
  | .app f a => by simp [explicateQ, explicit, explicit_explicateQ f, explicit_explicateQ a]
  | .letS p w b none => by
      simp [explicateQ, explicit, explicit_explicateQ p, explicit_explicateQ w,
        explicit_explicateQ b]
  | .letS p w b (some _) => by
      simp [explicateQ, explicit, explicit_explicateQ p, explicit_explicateQ w,
        explicit_explicateQ b]
  | .unify p w b => by
      simp [explicateQ, explicit, explicit_explicateQ p, explicit_explicateQ w,
        explicit_explicateQ b]
  | .alt t₁ t₂ => by simp [explicateQ, explicit, explicit_explicateQ t₁, explicit_explicateQ t₂]
  | .new _ b => by simp [explicateQ, explicit, explicit_explicateQ b]
  | .form _ b => by simp [explicateQ, explicit, explicit_explicateQ b]

theorem patNames_explicateQ : ∀ t : Src S X, Src.patNames (explicateQ t) = Src.patNames t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none _ => rfl
  | .lam _ (some _) _ => rfl
  | .app f a => by
      simp only [explicateQ, Src.patNames, patNames_explicateQ f, patNames_explicateQ a]
  | .letS _ _ _ none => rfl
  | .letS _ _ _ (some _) => rfl
  | .unify _ _ _ => rfl
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .form _ _ => rfl

theorem names_explicateQ : ∀ t : Src S X, Src.names (explicateQ t) = Src.names t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none b => by simp only [explicateQ, Src.names, names_explicateQ b]
  | .lam _ (some _) b => by simp only [explicateQ, Src.names, names_explicateQ b]
  | .app f a => by
      simp only [explicateQ, Src.names, names_explicateQ f, names_explicateQ a]
  | .letS p w b none => by
      simp only [explicateQ, Src.names, names_explicateQ p, names_explicateQ w,
        names_explicateQ b]
  | .letS p w b (some _) => by
      simp only [explicateQ, Src.names, names_explicateQ p, names_explicateQ w,
        names_explicateQ b]
  | .unify p w b => by
      simp only [explicateQ, Src.names, names_explicateQ p, names_explicateQ w,
        names_explicateQ b]
  | .alt t₁ t₂ => by
      simp only [explicateQ, Src.names, names_explicateQ t₁, names_explicateQ t₂]
  | .new _ b => by simp only [explicateQ, Src.names, names_explicateQ b]
  | .form _ b => by simp only [explicateQ, Src.names, names_explicateQ b]

variable [DecidableEq X]

/-- **Writing out what the query-wide policy inferred changes no
elaboration**, on text whose lambdas carry no crossing set. -/
theorem elabQ_explicateQ : ∀ (t : Src S X) (env : REnv X) (pos : Owner),
    lamPlain t = true → elabQ env pos (explicateQ t) = elabQ env pos t
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .sv _, _, _, _ => rfl
  | .par _, _, _, _ => rfl
  | .quote _, _, _, _ => rfl
  | .pquote _, _, _, _ => rfl
  | .lam z none b, env, pos, h => by
      simp only [lamPlain, Option.isNone_none, Bool.true_and] at h
      simp only [explicateQ, elabQ, crossOwn, filter_not_mem_self, List.dedup_nil, List.map_nil,
        REnv.update_nil]
      rw [elabQ_explicateQ b _ _ h]
  | .lam _ (some _) _, _, _, h => by simp [lamPlain] at h
  | .app f a, env, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ f _ _ h.1, elabQ_explicateQ a _ _ h.2]
  | .letS p w b none, env, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [explicateQ, elabQ, crossOwn, patNames_explicateQ, filter_not_mem_self,
        List.dedup_nil]
      rw [elabQ_explicateQ p _ _ hp, elabQ_explicateQ w _ _ hw, elabQ_explicateQ b _ _ hb]
  | .letS p w b (some sh), env, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [explicateQ, elabQ, patNames_explicateQ]
      cases crossOwn (some sh) (Src.patNames p) [] with
      | nil =>
          simp only []
          rw [elabQ_explicateQ p _ _ hp, elabQ_explicateQ w _ _ hw, elabQ_explicateQ b _ _ hb]
      | cons y ys =>
          simp only []
          rw [elabQ_explicateQ p _ _ hp, elabQ_explicateQ w _ _ hw, elabQ_explicateQ b _ _ hb]
  | .unify p w b, env, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ p _ _ hp, elabQ_explicateQ w _ _ hw, elabQ_explicateQ b _ _ hb]
  | .alt t₁ t₂, env, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ t₁ _ _ h.1, elabQ_explicateQ t₂ _ _ h.2]
  | .new [] b, env, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ b _ _ h]
  | .new (y₀ :: ys) b, env, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ b _ _ h]
  | .form z b, env, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateQ, elabQ]
      rw [elabQ_explicateQ b _ _ h]

/-! ## Lexical fresh -/

/-- **The explicit form of a text under lexical fresh**, `cr` being the names
in force.  A `let` shares the names of its pattern that it does not
introduce. -/
def explicateLF : List X → Src S X → Src S X
  | cr, .lam z none b => .lam z (some (Src.uses (explicateLF cr b))) (explicateLF cr b)
  | cr, .lam z (some sh) b =>
      .lam z (some sh) (explicateLF (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) b)
  | cr, .app f a => .app (explicateLF cr f) (explicateLF cr a)
  | cr, .letS p w b xs =>
      .letS (explicateLF (crossIn xs (lfIntro xs p cr) cr) p) (explicateLF cr w)
        (explicateLF (crossIn xs (lfIntro xs p cr) cr) b)
        (some ((Src.patNames p).filter fun y => decide (y ∉ lfIntro xs p cr)))
  | cr, .unify p w b => .unify (explicateLF cr p) (explicateLF cr w) (explicateLF cr b)
  | cr, .alt t₁ t₂ => .alt (explicateLF cr t₁) (explicateLF cr t₂)
  | cr, .new ys b => .new ys (explicateLF (cr.filter fun y => decide (y ∉ ys)) b)
  | cr, .form z b => .form z (explicateLF cr b)
  | _, .sym s => .sym s
  | _, .fn F => .fn F
  | _, .sv y => .sv y
  | _, .par z => .par z
  | _, .quote c => .quote c
  | _, .pquote c => .pquote c

theorem explicit_explicateLF : ∀ (t : Src S X) (cr : List X), explicit (explicateLF cr t) = true
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none b, cr => by simp [explicateLF, explicit, explicit_explicateLF b]
  | .lam _ (some _) b, cr => by simp [explicateLF, explicit, explicit_explicateLF b]
  | .app f a, cr => by
      simp [explicateLF, explicit, explicit_explicateLF f, explicit_explicateLF a]
  | .letS p w b _, cr => by
      simp [explicateLF, explicit, explicit_explicateLF p, explicit_explicateLF w,
        explicit_explicateLF b]
  | .unify p w b, cr => by
      simp [explicateLF, explicit, explicit_explicateLF p, explicit_explicateLF w,
        explicit_explicateLF b]
  | .alt t₁ t₂, cr => by
      simp [explicateLF, explicit, explicit_explicateLF t₁, explicit_explicateLF t₂]
  | .new _ b, cr => by simp [explicateLF, explicit, explicit_explicateLF b]
  | .form _ b, cr => by simp [explicateLF, explicit, explicit_explicateLF b]

theorem patNames_explicateLF : ∀ (t : Src S X) (cr : List X),
    Src.patNames (explicateLF cr t) = Src.patNames t
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none _, _ => rfl
  | .lam _ (some _) _, _ => rfl
  | .app f a, cr => by
      simp only [explicateLF, Src.patNames, patNames_explicateLF f, patNames_explicateLF a]
  | .letS _ _ _ _, _ => rfl
  | .unify _ _ _, _ => rfl
  | .alt _ _, _ => rfl
  | .new _ _, _ => rfl
  | .form _ _, _ => rfl

theorem names_explicateLF : ∀ (t : Src S X) (cr : List X),
    Src.names (explicateLF cr t) = Src.names t
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .pquote _, _ => rfl
  | .lam _ none b, cr => by simp only [explicateLF, Src.names, names_explicateLF b]
  | .lam _ (some _) b, cr => by simp only [explicateLF, Src.names, names_explicateLF b]
  | .app f a, cr => by
      simp only [explicateLF, Src.names, names_explicateLF f, names_explicateLF a]
  | .letS p w b _, cr => by
      simp only [explicateLF, Src.names, names_explicateLF p, names_explicateLF w,
        names_explicateLF b]
  | .unify p w b, cr => by
      simp only [explicateLF, Src.names, names_explicateLF p, names_explicateLF w,
        names_explicateLF b]
  | .alt t₁ t₂, cr => by
      simp only [explicateLF, Src.names, names_explicateLF t₁, names_explicateLF t₂]
  | .new _ b, cr => by simp only [explicateLF, Src.names, names_explicateLF b]
  | .form _ b, cr => by simp only [explicateLF, Src.names, names_explicateLF b]

/-- Sharing the names of its pattern that a `let` does not introduce under
lexical fresh makes it introduce, under every policy, what lexical fresh
introduced. -/
theorem crossOwn_lfIntro (xs : Option (List X)) (p : Src S X) (cr : List X) :
    crossOwn (some ((Src.patNames p).filter fun y => decide (y ∉ lfIntro xs p cr)))
        (Src.patNames p) [] = lfIntro xs p cr := by
  cases xs with
  | none =>
      simp only [lfIntro, crossOwn]
      exact filter_filter_dedup (Src.patNames p) fun y => decide (y ∉ cr)
  | some sh =>
      simp only [lfIntro, crossOwn]
      exact filter_filter_dedup (Src.patNames p) fun y => decide (y ∉ sh)

/-- **The explicit form elaborates, under the query-wide policy, to what
lexical fresh elaborates the source to**, on text whose lambdas carry no
crossing set. -/
theorem elabQ_explicateLF : ∀ (t : Src S X) (env : REnv X) (cr : List X) (pos : Owner),
    lamPlain t = true → elabQ env pos (explicateLF cr t) = elabLF env cr pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .lam z none b, env, cr, pos, h => by
      simp only [lamPlain, Option.isNone_none, Bool.true_and] at h
      simp only [explicateLF, elabQ, elabLF, crossOwn, filter_not_mem_self, List.dedup_nil,
        List.map_nil, REnv.update_nil, crossIn_none_nil]
      rw [elabQ_explicateLF b _ _ _ h]
  | .lam _ (some _) _, _, _, _, h => by simp [lamPlain] at h
  | .app f a, env, cr, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF f _ _ _ h.1, elabQ_explicateLF a _ _ _ h.2]
  | .letS p w b xs, env, cr, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [explicateLF, elabQ, elabLF, patNames_explicateLF, crossOwn_lfIntro]
      cases lfIntro xs p cr with
      | nil =>
          simp only []
          rw [elabQ_explicateLF p _ _ _ hp, elabQ_explicateLF w _ _ _ hw,
            elabQ_explicateLF b _ _ _ hb]
      | cons y ys =>
          simp only []
          rw [elabQ_explicateLF p _ _ _ hp, elabQ_explicateLF w _ _ _ hw,
            elabQ_explicateLF b _ _ _ hb]
  | .unify p w b, env, cr, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF p _ _ _ hp, elabQ_explicateLF w _ _ _ hw,
        elabQ_explicateLF b _ _ _ hb]
  | .alt t₁ t₂, env, cr, pos, h => by
      simp only [lamPlain, Bool.and_eq_true] at h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF t₁ _ _ _ h.1, elabQ_explicateLF t₂ _ _ _ h.2]
  | .new [] b, env, cr, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF b _ _ _ h, filter_not_mem_nil]
  | .new (y₀ :: ys) b, env, cr, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF b _ _ _ h]
  | .form z b, env, cr, pos, h => by
      simp only [lamPlain] at h
      simp only [explicateLF, elabQ, elabLF]
      rw [elabQ_explicateLF b _ _ _ h]

/-- **Writing out what lexical fresh inferred changes no elaboration**, on text
whose lambdas carry no crossing set; the explicit form no longer depends on
the names in force. -/
theorem elabLF_explicateLF (t : Src S X) (env : REnv X) (cr cr' : List X) (pos : Owner)
    (h : lamPlain t = true) : elabLF env cr' pos (explicateLF cr t) = elabLF env cr pos t :=
  (elabLF_explicit _ _ _ _ (explicit_explicateLF t cr)).trans (elabQ_explicateLF t env cr pos h)

/-! ## Programs -/

omit [DecidableEq X] in
/-- Every equation and the query of a program satisfy a condition. -/
def Program.All (good : Src S X → Prop) (program : Program S X) : Prop :=
  (∀ F body, program.clauses F = some body → good body) ∧ good program.query

omit [DecidableEq X] in
/-- Map the text of every equation and of the query. -/
def Program.map (convert : Src S X → Src S X) (program : Program S X) : Program S X :=
  ⟨fun F => (program.clauses F).map convert, convert program.query⟩

omit [DecidableEq X] in
theorem Program.All.map {good good' : Src S X → Prop} {convert : Src S X → Src S X}
    {program : Program S X} (all : program.All good) (maps : ∀ t, good t → good' (convert t)) :
    (program.map convert).All good' := by
  refine ⟨fun F body found => ?_, maps _ all.2⟩
  simp only [Program.map, Option.map_eq_some_iff] at found
  obtain ⟨source, sourceFound, rfl⟩ := found
  exact maps _ (all.1 F source sourceFound)

omit [DecidableEq X] in
theorem Program.All.mono {good good' : Src S X → Prop} {program : Program S X}
    (all : program.All good) (weaker : ∀ t, good t → good' t) : program.All good' :=
  ⟨fun F body found => weaker _ (all.1 F body found), weaker _ all.2⟩

omit [DecidableEq X] in
theorem Program.all_and {good good' : Src S X → Prop} {program : Program S X}
    (first : program.All good) (second : program.All good') :
    program.All fun t => good t ∧ good' t :=
  ⟨fun F body found => ⟨first.1 F body found, second.1 F body found⟩, first.2, second.2⟩

omit [DecidableEq X] in
theorem Program.all_true (program : Program S X) : program.All fun _ => True :=
  ⟨fun _ _ _ => trivial, trivial⟩

/-- **A map of text that keeps the written names and the elaboration of every
form keeps the judgment that a program elaborates to.**  The two policies
share their lifetime and readout. -/
theorem elabState_map (o o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    (good : Src S X → Prop) (convert : Src S X → Src S X)
    (names : ∀ t, good t → Src.names (convert t) = Src.names t)
    (forms : ∀ root t, good t → elabForm o' root (convert t) = elabForm o root t)
    {program : Program S X} (all : program.All good) :
    elabState ⟨o', l, r⟩ u unit (.program (program.map convert)) =
      elabState ⟨o, l, r⟩ u unit (.program program) := by
  have atForm : ∀ root t, good t →
      elabCfgX ⟨o', l, r⟩ root (convert t) = elabCfgX ⟨o, l, r⟩ root t := by
    intro root t ht
    cases l <;> simp only [elabCfgX, forms root t ht]
  have clauses : progSlot ⟨o', l, r⟩ u unit (program.map convert).clauses =
      progSlot ⟨o, l, r⟩ u unit program.clauses := by
    funext F
    simp only [progSlot, Program.map]
    cases hF : program.clauses F with
    | none => rfl
    | some body =>
        simp only [Option.map_some, clauseOf, rootSpellings, elabCfg,
          names body (all.1 F body hF), atForm [5] body (all.1 F body hF)]
  have query : elabCfg ⟨o', l, r⟩ [] (program.map convert).query =
      elabCfg ⟨o, l, r⟩ [] program.query := by
    simp only [elabCfg, Program.map, atForm [] program.query all.2]
  show Core.run _ (progSlot ⟨o', l, r⟩ u unit (program.map convert).clauses)
      (elabCfg ⟨o', l, r⟩ [] (program.map convert).query) =
    Core.run _ (progSlot ⟨o, l, r⟩ u unit program.clauses) (elabCfg ⟨o, l, r⟩ [] program.query)
  rw [clauses, query]
  rfl

/-- **Explicit capture, on every program**: the explicit form elaborates under
every ownership policy to what explicit capture elaborates the source to. -/
theorem elabState_explicateEC (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    (program : Program S X) :
    elabState ⟨o', l, r⟩ u unit (.program (program.map explicateEC)) =
      elabState ⟨.explicitCapture, l, r⟩ u unit (.program program) :=
  elabState_map .explicitCapture o' l r u unit (fun _ => True) explicateEC
    (fun t _ => names_explicateEC t)
    (fun root t _ =>
      (elabForm_explicit o' .explicitCapture root (explicit_explicateEC t)).trans
        (elabEC_explicateEC t _ _))
    program.all_true

/-- **The query-wide policy, on programs whose lambdas carry no crossing
set.** -/
theorem elabState_explicateQ (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    {program : Program S X} (plain : program.All fun t => lamPlain t = true) :
    elabState ⟨o', l, r⟩ u unit (.program (program.map explicateQ)) =
      elabState ⟨.queryWide, l, r⟩ u unit (.program program) :=
  elabState_map .queryWide o' l r u unit (fun t => lamPlain t = true) explicateQ
    (fun t _ => names_explicateQ t)
    (fun root t ht =>
      (elabForm_explicit o' .queryWide root (explicit_explicateQ t)).trans
        (elabQ_explicateQ t _ _ ht))
    plain

/-- **Lexical fresh, on programs whose lambdas carry no crossing set.** -/
theorem elabState_explicateLF (o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    {program : Program S X} (plain : program.All fun t => lamPlain t = true) :
    elabState ⟨o', l, r⟩ u unit (.program (program.map (explicateLF []))) =
      elabState ⟨.lexicalFresh, l, r⟩ u unit (.program program) :=
  elabState_map .lexicalFresh o' l r u unit (fun t => lamPlain t = true) (explicateLF [])
    (fun t _ => names_explicateLF t [])
    (fun root t ht =>
      (elabForm_explicit o' .queryWide root (explicit_explicateLF t [])).trans
        (elabQ_explicateLF t _ _ _ ht))
    plain

omit [DecidableEq X] in
/-- The explicit forms are explicit programs. -/
theorem Program.explicit_map_explicateEC (program : Program S X) :
    (program.map explicateEC).Explicit :=
  program.all_true.map fun t _ => explicit_explicateEC t

/-! ## Where exactness stops in the slot model -/

/-- `(lam z (($a $b) (lam w $a)))`, the names numbered `a = 0`, `b = 1`,
`z = 2`, `w = 3`. -/
def orderSource : Src Unit ℕ :=
  .lam 2 none (.app (.app (.sv 0) (.sv 1)) (.lam 3 none (.sv 0)))

/-- Its explicit form: the inner lambda shares `$a`; the outer one shares
nothing. -/
def orderExplicit : Src Unit ℕ :=
  .lam 2 (some []) (.app (.app (.sv 0) (.sv 1)) (.lam 3 (some [0]) (.sv 0)))

/-- The body both elaborate to. -/
def orderBody : Tm Unit (Slot ℕ) :=
  .app (.app (.var (.src ([0], 0))) (.var (.src ([0], 1))))
    (.lam (parName 3) [] (.var (.src ([0], 0))))

/-- **The order of an own list.**  Rule M gives the outer lambda the own list
`[a, b]`.  The explicit form, under every ownership policy, gives it `[b, a]`:
the name that the inner lambda shares counts as used last.  The bodies are the
same term. -/
theorem ownList_order_witness :
    explicit orderExplicit = true ∧
    elabForm .mercury [] orderSource = .lam (parName 2) [([0], 0), ([0], 1)] orderBody ∧
    (∀ o : Ownership,
      elabForm o [] orderExplicit = .lam (parName 2) [([0], 1), ([0], 0)] orderBody) ∧
    elabForm .mercury [] orderSource ≠ elabForm .mercury [] orderExplicit := by
  refine ⟨by decide, by decide, ?_, by decide⟩
  intro o
  cases o <;> decide

#print axioms elabQ_explicateQ
#print axioms elabQ_explicateLF
#print axioms elabLF_explicateLF
#print axioms elabState_map
#print axioms elabState_explicateEC
#print axioms elabState_explicateQ
#print axioms elabState_explicateLF
#print axioms ownList_order_witness

end Mettapedia.GSLT.LanguageDef.ScopePolicies
