import Mettapedia.GSLT.LanguageDef.ScopePolicies.Policies

/-!
# The explicit form: what the ownership policies have in common

A written crossing set and a written `new` mean the same under every ownership
policy.  Text in which every lambda and every `let` carries its crossing set is
**fully explicit** (`explicit`).

## The policies coincide on explicit text

* `elabMS_explicit`, `elabEC_explicit`, `elabLF_explicit` — on explicit text
  rule M, explicit capture and lexical fresh elaborate to the very term that
  the query-wide policy elaborates to, in every context;
  `elabForm_explicit`, `elabCfg_explicit`, `elabState_explicit` — hence at a
  form, under every lifetime, and for a whole program.
* `agreement_explicit` — in the identity model too: explicit text has no
  refining pattern and no un-introduced name.

## Writing out what a policy inferred

* `explicateEC` — explicit capture: a lambda with no crossing set shares
  nothing, `{}`; a `let` with none shares every name of its pattern.  Exact on
  every text (`elabEC_explicateEC`).
* `explicateQ` — query-wide: a lambda with no crossing set shares every name
  its region uses.  Exact on text whose lambdas carry no crossing set
  (`elabQ_explicateQ`).
* `explicateLF` — lexical fresh: the same for a lambda; a `let` shares the
  names of its pattern that it does not introduce.  Exact on text whose
  lambdas carry no crossing set (`elabLF_explicateLF`).

Rule M is the case of the existing translator `toLexical`, which is exact in
the identity model and writes crossing sets and `new` blocks; see
`ScopePolicies.Translators`.

## Where exactness stops in the slot model

A lambda's own list is a list, in the order of the last occurrences among the
names its region uses, and a name that a nested lambda shares counts as used
after the names written directly (`Src.uses`).  Writing a crossing set on a
nested lambda therefore can reorder the own list of an enclosing lambda that
carries a crossing set of its own; and under rule M it reorders the own list
that the rule infers.  `ownList_order_witness` is the smallest instance:
the two own lists `[a, b]` and `[b, a]`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ScopePolicies

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.IdSlot

universe u v

variable {S : Type u} {X : Type v}

/-! ## Explicit text -/

/-- **Fully explicit text**: every lambda and every `let` carries its crossing
set.  A quotation is code: no policy elaborates what it contains.  A lambda
formed at run time owns nothing under every policy, so it is explicit when its
body is. -/
def explicit : Src S X → Bool
  | .lam _ xs b => xs.isSome && explicit b
  | .app f a => explicit f && explicit a
  | .letS p w b xs => xs.isSome && explicit p && explicit w && explicit b
  | .unify p w b => explicit p && explicit w && explicit b
  | .alt t₁ t₂ => explicit t₁ && explicit t₂
  | .new _ b => explicit b
  | .form _ b => explicit b
  | _ => true

/-- Text whose lambdas carry no crossing set. -/
def lamPlain : Src S X → Bool
  | .lam _ xs b => xs.isNone && lamPlain b
  | .app f a => lamPlain f && lamPlain a
  | .letS p w b _ => lamPlain p && lamPlain w && lamPlain b
  | .unify p w b => lamPlain p && lamPlain w && lamPlain b
  | .alt t₁ t₂ => lamPlain t₁ && lamPlain t₂
  | .new _ b => lamPlain b
  | .form _ b => lamPlain b
  | _ => true

variable [DecidableEq X]

/-! ## The policies coincide on explicit text -/

/-- **Rule M on explicit text is the query-wide policy.** -/
theorem elabMS_explicit : ∀ (t : Src S X) (E : List X) (env : REnv X) (pos : Owner),
    explicit t = true → elabMS E env pos t = elabQ env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, h => by simp [explicit] at h
  | .lam z (some sh) b, E, env, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and] at h
      simp only [elabMS, elabQ, crossOwn]
      rw [elabMS_explicit b _ _ _ h]
  | .app f a, E, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit f _ _ _ h.1, elabMS_explicit a _ _ _ h.2]
  | .letS _ _ _ none, _, _, _, h => by simp [explicit] at h
  | .letS p w b (some sh), E, env, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabMS, elabQ]
      cases crossOwn (some sh) (Src.patNames p) [] with
      | nil =>
          simp only []
          rw [elabMS_explicit p _ _ _ hp, elabMS_explicit w _ _ _ hw, elabMS_explicit b _ _ _ hb]
      | cons y ys =>
          simp only []
          rw [elabMS_explicit p _ _ _ hp, elabMS_explicit w _ _ _ hw, elabMS_explicit b _ _ _ hb]
  | .unify p w b, E, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit p _ _ _ hp, elabMS_explicit w _ _ _ hw, elabMS_explicit b _ _ _ hb]
  | .alt t₁ t₂, E, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit t₁ _ _ _ h.1, elabMS_explicit t₂ _ _ _ h.2]
  | .new [] b, E, env, pos, h => by
      simp only [explicit] at h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit b _ _ _ h]
  | .new (y₀ :: ys) b, E, env, pos, h => by
      simp only [explicit] at h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit b _ _ _ h]
  | .form z b, E, env, pos, h => by
      simp only [explicit] at h
      simp only [elabMS, elabQ]
      rw [elabMS_explicit b _ _ _ h]

/-- **Explicit capture on explicit text is the query-wide policy.** -/
theorem elabEC_explicit : ∀ (t : Src S X) (env : REnv X) (pos : Owner),
    explicit t = true → elabEC env pos t = elabQ env pos t
  | .sym _, _, _, _ => rfl
  | .fn _, _, _, _ => rfl
  | .sv _, _, _, _ => rfl
  | .par _, _, _, _ => rfl
  | .quote _, _, _, _ => rfl
  | .pquote _, _, _, _ => rfl
  | .lam _ none _, _, _, h => by simp [explicit] at h
  | .lam z (some sh) b, env, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and] at h
      simp only [elabEC, elabQ, crossOwn]
      rw [elabEC_explicit b _ _ h]
  | .app f a, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit f _ _ h.1, elabEC_explicit a _ _ h.2]
  | .letS _ _ _ none, _, _, h => by simp [explicit] at h
  | .letS p w b (some sh), env, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabEC, elabQ]
      cases crossOwn (some sh) (Src.patNames p) [] with
      | nil =>
          simp only []
          rw [elabEC_explicit p _ _ hp, elabEC_explicit w _ _ hw, elabEC_explicit b _ _ hb]
      | cons y ys =>
          simp only []
          rw [elabEC_explicit p _ _ hp, elabEC_explicit w _ _ hw, elabEC_explicit b _ _ hb]
  | .unify p w b, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit p _ _ hp, elabEC_explicit w _ _ hw, elabEC_explicit b _ _ hb]
  | .alt t₁ t₂, env, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit t₁ _ _ h.1, elabEC_explicit t₂ _ _ h.2]
  | .new [] b, env, pos, h => by
      simp only [explicit] at h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit b _ _ h]
  | .new (y₀ :: ys) b, env, pos, h => by
      simp only [explicit] at h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit b _ _ h]
  | .form z b, env, pos, h => by
      simp only [explicit] at h
      simp only [elabEC, elabQ]
      rw [elabEC_explicit b _ _ h]

/-- **Lexical fresh on explicit text is the query-wide policy**, whatever names
are in force. -/
theorem elabLF_explicit : ∀ (t : Src S X) (env : REnv X) (cr : List X) (pos : Owner),
    explicit t = true → elabLF env cr pos t = elabQ env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, h => by simp [explicit] at h
  | .lam z (some sh) b, env, cr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and] at h
      simp only [elabLF, elabQ, crossOwn]
      rw [elabLF_explicit b _ _ _ h]
  | .app f a, env, cr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit f _ _ _ h.1, elabLF_explicit a _ _ _ h.2]
  | .letS _ _ _ none, _, _, _, h => by simp [explicit] at h
  | .letS p w b (some sh), env, cr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabLF, elabQ, lfIntro, crossOwn]
      cases ((Src.patNames p).filter fun y => decide (y ∉ sh)).dedup with
      | nil =>
          simp only []
          rw [elabLF_explicit p _ _ _ hp, elabLF_explicit w _ _ _ hw, elabLF_explicit b _ _ _ hb]
      | cons y ys =>
          simp only []
          rw [elabLF_explicit p _ _ _ hp, elabLF_explicit w _ _ _ hw, elabLF_explicit b _ _ _ hb]
  | .unify p w b, env, cr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit p _ _ _ hp, elabLF_explicit w _ _ _ hw, elabLF_explicit b _ _ _ hb]
  | .alt t₁ t₂, env, cr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit t₁ _ _ _ h.1, elabLF_explicit t₂ _ _ _ h.2]
  | .new [] b, env, cr, pos, h => by
      simp only [explicit] at h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit b _ _ _ h]
  | .new (y₀ :: ys) b, env, cr, pos, h => by
      simp only [explicit] at h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit b _ _ _ h]
  | .form z b, env, cr, pos, h => by
      simp only [explicit] at h
      simp only [elabLF, elabQ]
      rw [elabLF_explicit b _ _ _ h]

/-- **The ownership policies coincide on explicit text**, at a form. -/
theorem elabForm_explicit (o o' : Ownership) (root : Owner) {t : Src S X}
    (h : explicit t = true) : elabForm o root t = elabForm o' root t := by
  have toQ : ∀ ownership : Ownership,
      elabForm ownership root t = elabQ (fun _ => root) root t := by
    intro ownership
    cases ownership
    · rfl
    · exact elabMS_explicit t _ _ _ h
    · exact elabLF_explicit t _ _ _ h
    · exact elabEC_explicit t _ _ h
  rw [toQ o, toQ o']

/-- The same under every lifetime, with the slots exported. -/
theorem elabCfgX_explicit (o o' : Ownership) (l : Lifetime) (r r' : Readout) (root : Owner)
    {t : Src S X} (h : explicit t = true) :
    elabCfgX ⟨o, l, r⟩ root t = elabCfgX ⟨o', l, r'⟩ root t := by
  cases l <;> simp only [elabCfgX, elabForm_explicit o o' root h]

/-- **The ownership policies coincide on explicit text**, under every lifetime
and readout. -/
theorem elabCfg_explicit (o o' : Ownership) (l : Lifetime) (r r' : Readout) (root : Owner)
    {t : Src S X} (h : explicit t = true) :
    elabCfg ⟨o, l, r⟩ root t = elabCfg ⟨o', l, r'⟩ root t := by
  simp only [elabCfg, elabCfgX_explicit o o' l r r' root h]

/-- An equation with an explicit body is one clause under every ownership
policy. -/
theorem clauseOf_explicit (o o' : Ownership) (l : Lifetime) (r r' : Readout) (root : Owner)
    (u : X) (unit : S) {body : Src S X} (h : explicit body = true) :
    clauseOf ⟨o, l, r⟩ root u unit body = clauseOf ⟨o', l, r'⟩ root u unit body := by
  simp only [clauseOf, elabCfg, elabCfgX_explicit o o' l r r' root h]

/-- An explicit program: every equation and the query are explicit. -/
def Program.Explicit (program : Program S X) : Prop :=
  (∀ F body, program.clauses F = some body → explicit body = true) ∧
    explicit program.query = true

/-- The equations of an explicit program are the same under every ownership
policy. -/
theorem progSlot_explicit (o o' : Ownership) (l : Lifetime) (r r' : Readout) (u : X) (unit : S)
    {cl : S → Option (Src S X)} (h : ∀ F body, cl F = some body → explicit body = true) :
    progSlot ⟨o, l, r⟩ u unit cl = progSlot ⟨o', l, r'⟩ u unit cl := by
  funext F
  simp only [progSlot]
  cases hF : cl F with
  | none => rfl
  | some body => simp only [Option.map_some, clauseOf_explicit o o' l r r' [5] u unit (h F body hF)]

/-- **The ownership policies coincide on explicit programs**: one judgment of
the core, under every ownership policy. -/
theorem elabState_explicit (o o' : Ownership) (l : Lifetime) (r : Readout) (u : X) (unit : S)
    {program : Program S X} (h : program.Explicit) :
    elabState ⟨o, l, r⟩ u unit (.program program) =
      elabState ⟨o', l, r⟩ u unit (.program program) := by
  simp only [elabState, progSlot_explicit o o' l r r u unit h.1,
    elabCfg_explicit o o' l r r [] h.2]
  rfl

/-! ## The identity model on explicit text -/

/-- Explicit text has no refining pattern. -/
theorem refiningAt_explicit : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    explicit t = true → refiningAt E cr env fr pos t = []
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _, h => by simp [explicit] at h
  | .lam z (some sh) b, E, cr, env, fr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and] at h
      simp only [refiningAt]
      exact refiningAt_explicit b _ _ _ _ _ h
  | .app f a, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [refiningAt, refiningAt_explicit f _ _ _ _ _ h.1,
        refiningAt_explicit a _ _ _ _ _ h.2, List.append_nil]
  | .letS _ _ _ none, _, _, _, _, _, h => by simp [explicit] at h
  | .letS p w b (some sh), E, cr, env, fr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [refiningAt, refiningAt_explicit p _ _ _ _ _ hp,
        refiningAt_explicit w _ _ _ _ _ hw, refiningAt_explicit b _ _ _ _ _ hb, List.append_nil]
  | .unify p w b, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [refiningAt, refiningAt_explicit p _ _ _ _ _ hp,
        refiningAt_explicit w _ _ _ _ _ hw, refiningAt_explicit b _ _ _ _ _ hb, List.append_nil]
  | .alt t₁ t₂, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [refiningAt, refiningAt_explicit t₁ _ _ _ _ _ h.1,
        refiningAt_explicit t₂ _ _ _ _ _ h.2, List.append_nil]
  | .new ys b, E, cr, env, fr, pos, h => by
      simp only [explicit] at h
      simp only [refiningAt]
      exact refiningAt_explicit b _ _ _ _ _ h
  | .form z b, E, cr, env, fr, pos, h => by
      simp only [explicit] at h
      simp only [refiningAt]
      exact refiningAt_explicit b _ _ _ _ _ h

/-- Explicit text has no un-introduced name. -/
theorem unintroducedAt_explicit : ∀ (t : Src S X) (E cr : List X) (env : IEnv X)
    (fr pos : Owner), explicit t = true → unintroducedAt E cr env fr pos t = []
  | .sym _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _, h => by simp [explicit] at h
  | .lam z (some sh) b, E, cr, env, fr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and] at h
      simp only [unintroducedAt]
      exact unintroducedAt_explicit b _ _ _ _ _ h
  | .app f a, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [unintroducedAt, unintroducedAt_explicit f _ _ _ _ _ h.1,
        unintroducedAt_explicit a _ _ _ _ _ h.2, List.append_nil]
  | .letS _ _ _ none, _, _, _, _, _, h => by simp [explicit] at h
  | .letS p w b (some sh), E, cr, env, fr, pos, h => by
      simp only [explicit, Option.isSome_some, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [unintroducedAt, unintroducedAt_explicit p _ _ _ _ _ hp,
        unintroducedAt_explicit w _ _ _ _ _ hw, unintroducedAt_explicit b _ _ _ _ _ hb,
        List.append_nil]
  | .unify p w b, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      obtain ⟨⟨hp, hw⟩, hb⟩ := h
      simp only [unintroducedAt, unintroducedAt_explicit p _ _ _ _ _ hp,
        unintroducedAt_explicit w _ _ _ _ _ hw, unintroducedAt_explicit b _ _ _ _ _ hb,
        List.append_nil]
  | .alt t₁ t₂, E, cr, env, fr, pos, h => by
      simp only [explicit, Bool.and_eq_true] at h
      simp only [unintroducedAt, unintroducedAt_explicit t₁ _ _ _ _ _ h.1,
        unintroducedAt_explicit t₂ _ _ _ _ _ h.2, List.append_nil]
  | .new ys b, E, cr, env, fr, pos, h => by
      simp only [explicit] at h
      simp only [unintroducedAt]
      exact unintroducedAt_explicit b _ _ _ _ _ h
  | .form z b, E, cr, env, fr, pos, h => by
      simp only [explicit] at h
      simp only [unintroducedAt]
      exact unintroducedAt_explicit b _ _ _ _ _ h

/-- **In the identity model too, rule M and lexical fresh coincide on explicit
text** (an instance of `agreement`: the census is empty). -/
theorem agreement_explicit (R : Owner) {t : Src S X} (h : explicit t = true) :
    elabLFFormAt R t = elabMFormAt R t :=
  agreement (refiningAt_explicit t _ _ _ _ _ h) (unintroducedAt_explicit t _ _ _ _ _ h)

/-- **The translator from rule M leaves explicit text unchanged.** -/
theorem toLexicalAt_explicit (R : Owner) {t : Src S X} (h : explicit t = true) :
    toLexicalAt R t = t :=
  toLexicalAt_eq_self (refiningAt_explicit t _ _ _ _ _ h) (unintroducedAt_explicit t _ _ _ _ _ h)

/-! ## Small facts about lists of names -/

omit [DecidableEq X] in
/-- No name of a list is outside the list. -/
theorem filter_not_mem_self [DecidableEq X] (l : List X) :
    (l.filter fun y => decide (y ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y hy
  simpa using hy

/-- Sharing the names of a pattern that a `let` does not introduce makes it
introduce the same names. -/
theorem filter_filter_dedup (l : List X) (keep : X → Bool) :
    (l.filter fun y => decide (y ∉ l.filter fun z => decide (z ∉ (l.filter keep).dedup))).dedup =
      (l.filter keep).dedup := by
  congr 1
  apply List.filter_congr
  intro y hy
  have key : y ∈ (l.filter keep).dedup ↔ keep y = true := by
    rw [List.mem_dedup, List.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have inner : y ∈ (l.filter fun z => decide (z ∉ (l.filter keep).dedup)) ↔ ¬ keep y = true := by
    rw [List.mem_filter, decide_eq_true_eq, key]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  by_cases hk : keep y = true
  · rw [hk]
    exact decide_eq_true fun h => inner.1 h hk
  · have off : keep y = false := by simpa using hk
    rw [off]
    exact decide_eq_false fun h => h (inner.2 hk)

/-- Pointing no spelling anywhere changes no environment. -/
theorem REnv.update_nil (env : REnv X) (o : Owner) : env.update [] o = env := by
  funext y
  simp [REnv.update]

/-! ## Writing out what explicit capture inferred -/

/-- **The explicit form of a text under explicit capture**: a lambda with no
crossing set shares nothing; a `let` with none shares every name of its
pattern. -/
def explicateEC : Src S X → Src S X
  | .lam z none b => .lam z (some []) (explicateEC b)
  | .lam z (some sh) b => .lam z (some sh) (explicateEC b)
  | .app f a => .app (explicateEC f) (explicateEC a)
  | .letS p w b none =>
      .letS (explicateEC p) (explicateEC w) (explicateEC b) (some (Src.patNames p))
  | .letS p w b (some sh) => .letS (explicateEC p) (explicateEC w) (explicateEC b) (some sh)
  | .unify p w b => .unify (explicateEC p) (explicateEC w) (explicateEC b)
  | .alt t₁ t₂ => .alt (explicateEC t₁) (explicateEC t₂)
  | .new ys b => .new ys (explicateEC b)
  | .form z b => .form z (explicateEC b)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .quote c => .quote c
  | .pquote c => .pquote c

omit [DecidableEq X] in
theorem explicit_explicateEC : ∀ t : Src S X, explicit (explicateEC t) = true
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none b => by simp [explicateEC, explicit, explicit_explicateEC b]
  | .lam _ (some _) b => by simp [explicateEC, explicit, explicit_explicateEC b]
  | .app f a => by simp [explicateEC, explicit, explicit_explicateEC f, explicit_explicateEC a]
  | .letS p w b none => by
      simp [explicateEC, explicit, explicit_explicateEC p, explicit_explicateEC w,
        explicit_explicateEC b]
  | .letS p w b (some _) => by
      simp [explicateEC, explicit, explicit_explicateEC p, explicit_explicateEC w,
        explicit_explicateEC b]
  | .unify p w b => by
      simp [explicateEC, explicit, explicit_explicateEC p, explicit_explicateEC w,
        explicit_explicateEC b]
  | .alt t₁ t₂ => by simp [explicateEC, explicit, explicit_explicateEC t₁, explicit_explicateEC t₂]
  | .new _ b => by simp [explicateEC, explicit, explicit_explicateEC b]
  | .form _ b => by simp [explicateEC, explicit, explicit_explicateEC b]

omit [DecidableEq X] in
theorem patNames_explicateEC : ∀ t : Src S X, Src.patNames (explicateEC t) = Src.patNames t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none _ => rfl
  | .lam _ (some _) _ => rfl
  | .app f a => by
      simp only [explicateEC, Src.patNames, patNames_explicateEC f, patNames_explicateEC a]
  | .letS _ _ _ none => rfl
  | .letS _ _ _ (some _) => rfl
  | .unify _ _ _ => rfl
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .form _ _ => rfl

omit [DecidableEq X] in
theorem direct_explicateEC : ∀ t : Src S X, Src.direct (explicateEC t) = Src.direct t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none _ => rfl
  | .lam _ (some _) _ => rfl
  | .app f a => by
      simp only [explicateEC, Src.direct, direct_explicateEC f, direct_explicateEC a]
  | .letS p w b none => by
      simp only [explicateEC, Src.direct, direct_explicateEC p, direct_explicateEC w,
        direct_explicateEC b]
  | .letS p w b (some _) => by
      simp only [explicateEC, Src.direct, direct_explicateEC p, direct_explicateEC w,
        direct_explicateEC b]
  | .unify p w b => by
      simp only [explicateEC, Src.direct, direct_explicateEC p, direct_explicateEC w,
        direct_explicateEC b]
  | .alt t₁ t₂ => by
      simp only [explicateEC, Src.direct, direct_explicateEC t₁, direct_explicateEC t₂]
  | .new _ b => by simp only [explicateEC, Src.direct, direct_explicateEC b]
  | .form _ b => by simp only [explicateEC, Src.direct, direct_explicateEC b]

omit [DecidableEq X] in
/-- A lambda that shares nothing shares, with the scope around it, what a
lambda with no crossing set does. -/
theorem sharedUp_explicateEC : ∀ t : Src S X, Src.sharedUp (explicateEC t) = Src.sharedUp t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none _ => rfl
  | .lam _ (some _) _ => rfl
  | .app f a => by
      simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC f, sharedUp_explicateEC a]
  | .letS p w b none => by
      simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC p, sharedUp_explicateEC w,
        sharedUp_explicateEC b]
  | .letS p w b (some _) => by
      simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC p, sharedUp_explicateEC w,
        sharedUp_explicateEC b]
  | .unify p w b => by
      simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC p, sharedUp_explicateEC w,
        sharedUp_explicateEC b]
  | .alt t₁ t₂ => by
      simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC t₁, sharedUp_explicateEC t₂]
  | .new _ b => by simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC b]
  | .form _ b => by simp only [explicateEC, Src.sharedUp, sharedUp_explicateEC b]

omit [DecidableEq X] in
theorem uses_explicateEC (t : Src S X) : Src.uses (explicateEC t) = Src.uses t := by
  simp only [Src.uses, direct_explicateEC, sharedUp_explicateEC]

omit [DecidableEq X] in
theorem names_explicateEC : ∀ t : Src S X, Src.names (explicateEC t) = Src.names t
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .lam _ none b => by simp only [explicateEC, Src.names, names_explicateEC b]
  | .lam _ (some _) b => by simp only [explicateEC, Src.names, names_explicateEC b]
  | .app f a => by
      simp only [explicateEC, Src.names, names_explicateEC f, names_explicateEC a]
  | .letS p w b none => by
      simp only [explicateEC, Src.names, names_explicateEC p, names_explicateEC w,
        names_explicateEC b]
  | .letS p w b (some _) => by
      simp only [explicateEC, Src.names, names_explicateEC p, names_explicateEC w,
        names_explicateEC b]
  | .unify p w b => by
      simp only [explicateEC, Src.names, names_explicateEC p, names_explicateEC w,
        names_explicateEC b]
  | .alt t₁ t₂ => by
      simp only [explicateEC, Src.names, names_explicateEC t₁, names_explicateEC t₂]
  | .new _ b => by simp only [explicateEC, Src.names, names_explicateEC b]
  | .form _ b => by simp only [explicateEC, Src.names, names_explicateEC b]

/-- **Writing out what explicit capture inferred changes no elaboration**, on
every text and in every context. -/
theorem elabEC_explicateEC : ∀ (t : Src S X) (env : REnv X) (pos : Owner),
    elabEC env pos (explicateEC t) = elabEC env pos t
  | .sym _, _, _ => rfl
  | .fn _, _, _ => rfl
  | .sv _, _, _ => rfl
  | .par _, _, _ => rfl
  | .quote _, _, _ => rfl
  | .pquote _, _, _ => rfl
  | .lam z none b, env, pos => by
      simp only [explicateEC, elabEC, crossOwn, uses_explicateEC, filter_not_mem_nil]
      rw [elabEC_explicateEC b]
  | .lam z (some sh) b, env, pos => by
      simp only [explicateEC, elabEC, crossOwn, uses_explicateEC]
      rw [elabEC_explicateEC b]
  | .app f a, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC f, elabEC_explicateEC a]
  | .letS p w b none, env, pos => by
      simp only [explicateEC, elabEC, crossOwn, patNames_explicateEC, filter_not_mem_self,
        List.dedup_nil]
      rw [elabEC_explicateEC p, elabEC_explicateEC w, elabEC_explicateEC b]
  | .letS p w b (some sh), env, pos => by
      simp only [explicateEC, elabEC, patNames_explicateEC]
      cases crossOwn (some sh) (Src.patNames p) [] with
      | nil =>
          simp only []
          rw [elabEC_explicateEC p, elabEC_explicateEC w, elabEC_explicateEC b]
      | cons y ys =>
          simp only []
          rw [elabEC_explicateEC p, elabEC_explicateEC w, elabEC_explicateEC b]
  | .unify p w b, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC p, elabEC_explicateEC w, elabEC_explicateEC b]
  | .alt t₁ t₂, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC t₁, elabEC_explicateEC t₂]
  | .new [] b, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC b]
  | .new (y₀ :: ys) b, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC b]
  | .form z b, env, pos => by
      simp only [explicateEC, elabEC]
      rw [elabEC_explicateEC b]

#print axioms elabForm_explicit
#print axioms elabState_explicit
#print axioms agreement_explicit
#print axioms elabEC_explicateEC

end Mettapedia.GSLT.LanguageDef.ScopePolicies
