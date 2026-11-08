import Mettapedia.Machines.AdmissionRewriting.Dialects

/-!
# The prepared tier's normal forms in PeTTa

CeTTa's prepared tier admits these spellings, in its PeTTa lane only, as their
normal forms, without rewriting the stored equations (`TierRule`):

* rule 1, `(if c t)` as `(if c t (empty))`;
* rule 5, `(superpose (x))` as `x`;
* rule 8, `(let $y e $y)` as `e`;
* `(case k (($v b) arms..))` as `(let $v k b)`, no arm written `Empty`
  (`caseVar_sound`);
* `(let* (ps.. ($y e)) $y)` as `(let* (ps..) e)` (`letStarLast_sound`).

**In PeTTa each normal form means what the spelling means**, its answers, their
multiplicity and order, and its effects in order included (`eval` is a trace),
at the root (`tier_rule_sound`) and at every position that is not held
(`CtxStep`, `tier_sound`, `tier_star_sound`). Rule 8 is not one of the
normalizer's rules (`Rule.letEta` rewrites a `let` source only), so the context
closure here is its own, for any dialect whose non-Boolean `if` does not quote its
spelling (`ctx_sound`).

**Rule 1 is a guarded equation**: `(if c t)` runs `t` on each `True` answer of
`c` and answers nothing on any other (`petta_if2_guarded`), which is what the
tier compiles as a scalar guard, or as an `if` whose else branch is zero where
the run produces answers; where the run wants one answer the else branch
declines to the canonical evaluator, and whatever the tier answers is the
spelling's answer (`decline_exact`).

**Rule 8's guard** (`letNamed_guarded`, `letNamed_unguarded`): the rule is the
meaning of a source `(let $y e $y)` only where `$y` is a fresh binder; where `$y`
is bound the `let` compares (`(s 4)` with `(= (s $y) (let $y 3 $y))` answers
nothing, the rewritten body `3`).

**HE differs** (controls from `Dialects`): the two-armed `if` is an arity
error in HE (`Dialects.he_if2`), and HE's `let` evaluates a held value again
(`Dialects.he_letEta_differs`), so rules 1 and 8 are PeTTa's; rule 5 holds in HE
as well (`he_sup1`). HE runs a binder arm on an empty key, so the `case` rule is
PeTTa's (`he_caseVar_differs`). A held position is never rewritten
(`Dialects.petta_quote_differs`).

**The binder rules' guards.** The `case` rule needs no arm written `Empty`
(`petta_emptyArm_differs`) and a fresh binder: a bound one compares and falls
through to the next arm (`caseVar_bound_falls_through`), unless the arm is alone,
where the comparing `let` is the `case` (`caseBound_single`). CeTTa now applies
it exactly so: no arm written `Empty`, and a first-arm variable fresh once the key
is compiled, or a lone arm. The `let*` rule is rule 8
under the pairs before it (`letStar_snoc_let`). Rule 8's guard reads the binder
after the bound expression: one that binds and retires `$y` makes the source a
comparison (`TypedCalls.LetScopes.Controls.rule8_checked_before`); CeTTa now reads
it there (`TypedCalls.LetScopes.rule8_c_order_exact`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.TierNormalForms

open AdmissionRewriting Dialects

/-- No arm is written `Empty`: CeTTa's PeTTa view declines a `case` that has one
(`petta_case_arms_write_empty`). -/
def NoEmptyArm (arms : List (Pat × Tm)) : Prop :=
  ∀ a ∈ arms, ∀ l : Lit, a.1 = .lit l → l.matches (.sym .emp) = false

/-- The spellings the tier admits by their normal forms. -/
inductive TierRule : Tm → Tm → Prop
  | if2 (c t : Tm) : TierRule (.if2 c t) (.if3 c t .empty)
  | sup1 (x : Tm) : TierRule (.sup [x]) x
  | letVar (e : Tm) : TierRule (.let_ e (.var 0)) e
  | caseVar (k b : Tm) (arms : List (Pat × Tm)) (h : NoEmptyArm arms) :
      TierRule (.case_ k ((.bind, b) :: arms)) (.let_ k b)
  | letStarLast (ps : List Tm) (e : Tm) : TierRule (.letStar (ps ++ [e]) (.var 0)) (.letStar ps e)

/-- A rewrite by a root relation at any position that is not held. -/
inductive CtxStep (Rt : Tm → Tm → Prop) : Tm → Tm → Prop
  | root {t t' : Tm} : Rt t t' → CtxStep Rt t t'
  | tup (pre post : List Tm) {x x' : Tm} :
      CtxStep Rt x x' → CtxStep Rt (.tup (pre ++ x :: post)) (.tup (pre ++ x' :: post))
  | if3c {c c' : Tm} (t e : Tm) : CtxStep Rt c c' → CtxStep Rt (.if3 c t e) (.if3 c' t e)
  | if3t (c : Tm) {t t' : Tm} (e : Tm) : CtxStep Rt t t' → CtxStep Rt (.if3 c t e) (.if3 c t' e)
  | if3e (c t : Tm) {e e' : Tm} : CtxStep Rt e e' → CtxStep Rt (.if3 c t e) (.if3 c t e')
  | if2c {c c' : Tm} (t : Tm) : CtxStep Rt c c' → CtxStep Rt (.if2 c t) (.if2 c' t)
  | if2t (c : Tm) {t t' : Tm} : CtxStep Rt t t' → CtxStep Rt (.if2 c t) (.if2 c t')
  | letE {e e' : Tm} (b : Tm) : CtxStep Rt e e' → CtxStep Rt (.let_ e b) (.let_ e' b)
  | letB (e : Tm) {b b' : Tm} : CtxStep Rt b b' → CtxStep Rt (.let_ e b) (.let_ e b')
  | letStarE (pre post : List Tm) {e e' : Tm} (b : Tm) :
      CtxStep Rt e e' → CtxStep Rt (.letStar (pre ++ e :: post) b) (.letStar (pre ++ e' :: post) b)
  | letStarB (es : List Tm) {b b' : Tm} : CtxStep Rt b b' → CtxStep Rt (.letStar es b) (.letStar es b')
  | caseE {e e' : Tm} (alts : List (Pat × Tm)) :
      CtxStep Rt e e' → CtxStep Rt (.case_ e alts) (.case_ e' alts)
  | caseB (e : Tm) (pre post : List (Pat × Tm)) (p : Pat) {b b' : Tm} :
      CtxStep Rt b b' → CtxStep Rt (.case_ e (pre ++ (p, b) :: post)) (.case_ e (pre ++ (p, b') :: post))
  | sup (pre post : List Tm) {x x' : Tm} :
      CtxStep Rt x x' → CtxStep Rt (.sup (pre ++ x :: post)) (.sup (pre ++ x' :: post))
  | once {b b' : Tm} : CtxStep Rt b b' → CtxStep Rt (.once b) (.once b')
  | call (f : Name) (pre post : List Tm) {x x' : Tm} :
      CtxStep Rt x x' → CtxStep Rt (.call f (pre ++ x :: post)) (.call f (pre ++ x' :: post))
  | iterCOps (k : Iter) (pre post : List Tm) {x x' : Tm} (f : Name) :
      CtxStep Rt x x' → CtxStep Rt (.iterC k (pre ++ x :: post) f) (.iterC k (pre ++ x' :: post) f)
  | iterBOps (k : Iter) (pre post : List Tm) {x x' : Tm} (b : Tm) :
      CtxStep Rt x x' → CtxStep Rt (.iterB k (pre ++ x :: post) b) (.iterB k (pre ++ x' :: post) b)
  | iterBBody (k : Iter) (ops : List Tm) {b b' : Tm} :
      CtxStep Rt b b' → CtxStep Rt (.iterB k ops b) (.iterB k ops b')

/-- Facts that hold of nothing: every environment respects them. -/
def noFacts : Facts := fun _ => false

theorem sat_noFacts (ρ : List Val) : Sat noFacts ρ := fun _ h => by cases h

theorem pushN_noFacts : ∀ n : ℕ, pushN n noFacts = noFacts
  | 0 => rfl
  | n + 1 => by
      rw [pushN_succ]
      have : push noFacts = noFacts := by
        funext k
        cases k <;> rfl
      rw [this, pushN_noFacts n]

theorem scope_noFacts (p : Pat) : p.scope noFacts = noFacts := by
  cases p with
  | bind => funext k; cases k <;> rfl
  | lit l => rfl

/-- **A root relation sound in every environment is sound at every position
that is not held**, on a dialect whose non-Boolean `if` does not read its own
spelling. -/
theorem ctx_sound {D : Dialect} (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    {Rt : Tm → Tm → Prop} (hR : ∀ t t', Rt t t' → ∀ ρ, eval D t ρ = eval D t' ρ) {t t' : Tm}
    (h : CtxStep Rt t t') : ∀ ρ, eval D t ρ = eval D t' ρ := by
  induction h with
  | root r => exact hR _ _ r
  | tup pre post _ ih => intro ρ; simp only [eval, evalArgs_congr (ih ρ)]
  | if3c t e _ ih =>
    intro ρ; simp only [eval, ih ρ]; congr 1
    exact bindT_congr _ fun v => by rw [hnb]
  | if3t c e _ ih =>
    intro ρ; simp only [eval, ih ρ]; congr 1
    exact bindT_congr _ fun v => by rw [hnb]
  | if3e c t _ ih =>
    intro ρ; simp only [eval, ih ρ]; congr 1
    exact bindT_congr _ fun v => by rw [hnb]
  | if2c t _ ih =>
    intro ρ; simp only [eval, ih ρ, hif2, if_true]; congr 1
    exact bindT_congr _ fun v => by rw [hnb]
  | if2t c _ ih =>
    intro ρ; simp only [eval, ih ρ, hif2, if_true]; congr 1
    exact bindT_congr _ fun v => by rw [hnb]
  | letE b _ ih => intro ρ; simp only [eval, ih ρ]
  | letB e _ ih =>
    intro ρ; simp only [eval]; congr 1
    exact bindT_congr _ fun v => ih (v :: ρ)
  | letStarE pre post b _ ih =>
    intro ρ; simp only [eval]; congr 1
    exact evalLS_congr_src post _ pre noFacts ρ (sat_noFacts ρ) fun ρ' _ => ih ρ'
  | letStarB es _ ih =>
    intro ρ; simp only [eval]; congr 1
    exact evalLS_congr_k es noFacts ρ (sat_noFacts ρ) fun ρ' _ => ih ρ'
  | caseE alts _ ih => intro ρ; simp only [eval, ih ρ]
  | caseB e pre post p _ ih =>
    intro ρ; simp only [eval]; congr 1
    rw [onEmpty_congr (Γ := noFacts) (sat_noFacts ρ) (fun ρ' _ => ih ρ') pre post]
    congr 1
    exact bindT_congr _ fun v => select_congr (Γ := noFacts) v (sat_noFacts ρ) (fun ρ' _ => ih ρ') pre post
  | sup pre post _ ih => intro ρ; simp only [eval, evalSup_congr (ih ρ)]
  | once _ ih => intro ρ; simp only [eval, ih ρ]
  | call f pre post _ ih => intro ρ; simp only [eval, evalArgs_congr (ih ρ)]
  | iterCOps k pre post f _ ih => intro ρ; simp only [eval, evalArgs_congr (ih ρ)]
  | iterBOps k pre post b _ ih => intro ρ; simp only [eval, evalArgs_congr (ih ρ)]
  | iterBBody k ops _ ih =>
    intro ρ; simp only [eval]; congr 1
    exact bindT_congr _ fun v => iterate_congr k (fun vs _ => ih _) v

/-- **Rule 8 in PeTTa**: `(let $y e $y)` is `e`, trace for trace. -/
theorem petta_letVar (e : Tm) (ρ : List Val) : eval petta (.let_ e (.var 0)) ρ = eval petta e ρ := by
  simp only [eval, petta, List.nil_append, List.getD_cons_zero]
  exact bindT_ret_right _

theorem onEmpty_noEmptyArm {D : Dialect} (hce : D.caseEmpty ≠ .matching) :
    ∀ (arms : List (Pat × Tm)), NoEmptyArm arms → ∀ ρ, onEmpty D arms ρ = []
  | [], _, _ => by simp [onEmpty]
  | (p, b) :: rest, h, ρ => by
      have hrest : NoEmptyArm rest := fun a ha => h a (List.mem_cons_of_mem _ ha)
      cases hc : D.caseEmpty with
      | none => simp [onEmpty, hc]
      | literal =>
          cases p with
          | bind =>
              simp only [onEmpty, hc]
              exact onEmpty_noEmptyArm hce rest hrest ρ
          | lit l =>
              have hl : l.matches (.sym .emp) = false := h (.lit l, b) List.mem_cons_self l rfl
              simp only [onEmpty, hc, hl, Bool.false_eq_true, if_false]
              exact onEmpty_noEmptyArm hce rest hrest ρ
      | matching => exact absurd hc hce

/-- **A `case` whose first arm is a binder is a `let`**, on a dialect that runs no
binder on an empty key, when no arm is written `Empty`: the binder matches every
answer of the key, and an empty key runs no arm. -/
theorem caseVar_sound {D : Dialect} (hce : D.caseEmpty ≠ .matching) (k b : Tm) (arms : List (Pat × Tm))
    (h : NoEmptyArm arms) (ρ : List Val) :
    eval D (.case_ k ((.bind, b) :: arms)) ρ = eval D (.let_ k b) ρ := by
  have hz : onEmpty D ((.bind, b) :: arms) ρ = [] := by
    cases hc : D.caseEmpty with
    | none => simp [onEmpty, hc]
    | literal =>
        simp only [onEmpty, hc]
        exact onEmpty_noEmptyArm hce arms h ρ
    | matching => exact absurd hc hce
  simp only [eval, select, hz, ite_self, List.append_nil]

theorem evalLS_snoc (D : Dialect) (e : Tm) (k : List Val → Trace) :
    ∀ (ps : List Tm) (ρ : List Val),
      evalLS D (ps ++ [e]) k ρ = evalLS D ps (fun ρ' => bindT (eval D e ρ') fun v => k (v :: ρ')) ρ
  | [], ρ => by simp [evalLS]
  | p :: ps, ρ => by
      simp only [List.cons_append, evalLS]
      exact bindT_congr _ fun v => evalLS_snoc D e k ps (v :: ρ)

/-- **`let*`'s last pair is a `let` under the pairs before it**, on an unmetered
dialect. -/
theorem letStar_snoc_let {D : Dialect} (hm : D.meter = []) (ps : List Tm) (e b : Tm) (ρ : List Val) :
    eval D (.letStar (ps ++ [e]) b) ρ = eval D (.letStar ps (.let_ e b)) ρ := by
  simp only [eval, hm, List.nil_append]
  rw [evalLS_snoc]

/-- **`(let* (ps.. ($y e)) $y)` is `(let* (ps..) e)`**, on a dialect that reads a
variable as its value. -/
theorem letStarLast_sound {D : Dialect} (hvr : ∀ v, D.varRead v = ret v) (ps : List Tm) (e : Tm)
    (ρ : List Val) : eval D (.letStar (ps ++ [e]) (.var 0)) ρ = eval D (.letStar ps e) ρ := by
  simp only [eval]
  rw [evalLS_snoc]
  congr 2
  funext ρ'
  simp only [List.getD_cons_zero, hvr]
  exact bindT_ret_right _

/-- **Each normal form means what its spelling means in PeTTa.** -/
theorem tier_rule_sound {t t' : Tm} (h : TierRule t t') (ρ : List Val) : eval petta t ρ = eval petta t' ρ := by
  cases h with
  | if2 c t => exact if2_sound petta rfl rfl c t (.inl rfl) ρ
  | sup1 => exact sup1_sound petta rfl _ ρ
  | letVar => exact petta_letVar _ ρ
  | caseVar k b arms h => exact caseVar_sound (by decide) k b arms h ρ
  | letStarLast ps e => exact letStarLast_sound (fun _ => rfl) ps e ρ

/-- **At every position that is not held.** -/
theorem tier_sound {t t' : Tm} (h : CtxStep TierRule t t') (ρ : List Val) :
    eval petta t ρ = eval petta t' ρ :=
  ctx_sound (fun _ _ _ => rfl) rfl (fun _ _ r ρ => tier_rule_sound r ρ) h ρ

/-- **Any number of such rewrites.** -/
theorem tier_star_sound {t t' : Tm} (h : Relation.ReflTransGen (CtxStep TierRule) t t') (ρ : List Val) :
    eval petta t ρ = eval petta t' ρ := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, tier_sound hs ρ]

/-- **Rule 1 is a guarded equation**: the then-branch's run on each `True`
answer of the condition, nothing on any other, effects in order. -/
theorem petta_if2_guarded (c t : Tm) (ρ : List Val) :
    eval petta (.if2 c t) ρ = bindT (eval petta c ρ) fun v => branch3 v (eval petta t ρ) [] [] := by
  simp [eval, petta]

/-- The single-answer tier's `(if c t)`: the then-branch on `True`; otherwise it
declines to the canonical evaluator. -/
def declineIf2 (v : Val) (tr : Trace) : Option Trace :=
  match v with
  | .sym .tru => some tr
  | _ => none

/-- **Declining is exact**: on a condition with one answer and no effect,
whatever the single-answer tier answers is the spelling's answer. -/
theorem decline_exact (c t : Tm) (ρ : List Val) (v : Val) (hc : eval petta c ρ = ret v) (tr : Trace)
    (h : declineIf2 v (eval petta t ρ) = some tr) : tr = eval petta (.if2 c t) ρ := by
  rw [petta_if2_guarded, hc, bindT_ret]
  match v, h with
  | .sym .tru, h =>
      simp only [declineIf2, Option.some.injEq] at h
      subst h
      rfl

/-- The else branch the tier declines on answers nothing in PeTTa. -/
theorem decline_branch_empty (c t : Tm) (ρ : List Val) (v : Val) (hc : eval petta c ρ = ret v)
    (hv : declineIf2 v (eval petta t ρ) = none) : eval petta (.if2 c t) ρ = [] := by
  rw [petta_if2_guarded, hc, bindT_ret]
  cases v with
  | sym s =>
      cases s with
      | tru => simp [declineIf2] at hv
      | fls => rfl
      | emp => rfl
      | other n => rfl
  | int n => rfl
  | tup vs => rfl
  | syn t => rfl

/-- Rule 5 holds in HE too. -/
theorem he_sup1 (x : Tm) (ρ : List Val) : eval he (.sup [x]) ρ = eval he x ρ := sup1_sound he rfl x ρ

/-- **Rules 1 and 8 are PeTTa's**: in HE the two-armed `if` is an arity
error, and `let` evaluates a held value again. -/
theorem he_rules_differ :
    eval he (.if2 tt (.lit (.int 1))) [] ≠ eval he (.if3 tt (.lit (.int 1)) .empty) [] ∧
      eval he (.let_ quoted (.var 0)) [] ≠ eval he quoted [] := by
  refine ⟨?_, he_letEta_differs⟩
  rw [he_if2.1, he_if2.2]
  simp [ret, errorVal]

/-! ## Rule 8 for a named `$y`, and its guard

A source `(let $y e $y)` is rule 8's form `.let_ e (.var 0)` only where `$y` is a
fresh binder. Where the context binds `$y` (an argument, an enclosing binder) the
`let` unifies the two values, and where an earlier binder of `$y` ended its scope
PeTTa's binding persists, which CeTTa's compiler marks by retiring `$y`; the rule
is applied where `$y` is neither bound nor retired, and retires `$y`
(`TypedCalls.LetScopes.rule8_guarded`). -/

open Classical in
/-- **`(let $y e $y)` in PeTTa, read against what the context binds to `$y`**:
a binding where `$y` is unbound, a comparison of the two values where it is
bound. -/
noncomputable def letNamed (D : Dialect) (bound : Option Val) (e : Tm) (ρ : List Val) : Trace :=
  bindT (eval D e ρ) fun v =>
    match bound with
    | none => ret v
    | some w => if v = w then ret v else []

/-- **The guarded rule**: where `$y` is unbound, `(let $y e $y)` is `e`, trace for
trace. -/
theorem letNamed_guarded (e : Tm) (ρ : List Val) : letNamed petta none e ρ = eval petta e ρ :=
  bindT_ret_right _

/-- **The unguarded rule changes the answer** (`(= (s $y) (let $y 3 $y))`,
`(s 4)`): the `let` compares `3` with `4` and answers nothing, where `3` answers
`3`. -/
theorem letNamed_unguarded :
    letNamed petta (some (.int 4)) (.lit (.int 3)) [] = [] ∧ eval petta (.lit (.int 3)) [] = ret (.int 3) := by
  refine ⟨?_, rfl⟩
  simp only [letNamed, eval, Lit.val, bindT_ret]
  rw [if_neg (by simp)]

/-! ## The `case` and `let*` rules' guards

`(case k (($v b) arms..))` is `(let $v k b)` only where `$v` is a fresh binder; where
the context binds `$v`, PeTTa's `case` compares and on a mismatch tries the next arm,
where the `let` answers nothing (`caseVar_bound_falls_through`). An empty key runs an
arm written `Empty` in PeTTa (`petta_emptyArm_differs`), which CeTTa declines, and a
binder arm in HE (`he_caseVar_differs`). The `let*` rule is rule 8 under the pairs
before it (`letStar_snoc_let`), with rule 8's guard. -/

/-- **HE runs a binder arm on an empty key**: `(case (empty) (($v 1)))` answers `1`,
`(let $v (empty) 1)` nothing (Rust: `[1]`, `[]`). -/
theorem he_caseVar_differs :
    eval he (.case_ .empty [(.bind, .lit (.int 1))]) [] = ret (.int 1) ∧
      eval he (.let_ .empty (.lit (.int 1))) [] = [] := by
  constructor <;> rfl

/-- **An arm written `Empty` runs on an empty key in PeTTa**: `(case (empty) (($v 1)
(Empty 2)))` answers `2`, the `let` nothing (stable-fixed PeTTa: `2`). -/
theorem petta_emptyArm_differs :
    eval petta (.case_ .empty [(.bind, .lit (.int 1)), (.lit (.sym .emp), .lit (.int 2))]) [] = ret (.int 2) ∧
      eval petta (.let_ .empty (.lit (.int 1))) [] = [] := by
  constructor <;> rfl

open Classical in
/-- `(let $v e b)` where the context binds `$v` to `w`: a comparison. -/
noncomputable def letBound (D : Dialect) (w : Val) (e b : Tm) (ρ : List Val) : Trace :=
  bindT (eval D e ρ) fun v => if v = w then eval D b ρ else []

/-- **A bound binder arm falls through in PeTTa** (`(= (f $v) (case 3 (($v 10) ($w
20))))`, `(f 4)`; stable-fixed PeTTa: `20`): the first arm compares `3` with `4` and
the next arm answers `20`, where the `let` made of the first arm compares and answers
nothing. -/
theorem caseVar_bound_falls_through :
    eval petta (.case_ (.lit (.int 3)) [(.lit (.int 4), .lit (.int 10)), (.bind, .lit (.int 20))]) [] =
        ret (.int 20) ∧
      letBound petta (.int 4) (.lit (.int 3)) (.lit (.int 10)) [] = [] := by
  constructor
  · rfl
  · simp only [letBound, eval, Lit.val, bindT_ret]
    rw [if_neg (by simp)]

theorem lit_matches_iff (l : Lit) (v : Val) : l.matches v = true ↔ v = l.val := by
  cases l with
  | int n =>
      cases v <;> simp [Lit.matches, Lit.val, eq_comm]
  | sym s =>
      cases v <;> simp [Lit.matches, Lit.val, eq_comm]

/-- **A lone bound arm is the comparing `let`** (the `case` rule's second side
condition): `(case k (($v b)))` with `$v` bound to a literal other than `Empty`
runs `b` on each answer equal to it and nothing otherwise, as `(let $v k b)` does.
On an empty key PeTTa runs no arm for a variable bound to `Empty` either
(stable-fixed PeTTa: `(f Empty)` with `(= (f $v) (case (empty) (($v 1))))` answers
nothing). -/
theorem caseBound_single (k b : Tm) (l : Lit) (hl : l.matches (.sym .emp) = false) (ρ : List Val) :
    eval petta (.case_ k [(.lit l, b)]) ρ = letBound petta l.val k b ρ := by
  classical
  have hz : onEmpty petta [(.lit l, b)] ρ = [] := by
    simp [onEmpty, petta, hl]
  have hm : petta.meter = [] := rfl
  simp only [eval]
  rw [hz, hm]
  simp only [ite_self, List.nil_append, List.append_nil, letBound]
  apply bindT_congr
  intro v
  simp only [select]
  by_cases hv : v = l.val
  · rw [if_pos ((lit_matches_iff l v).mpr hv), if_pos hv]
  · have : l.matches v = false := by
      cases h : l.matches v
      · rfl
      · exact absurd ((lit_matches_iff l v).mp h) hv
    rw [this, if_neg hv]
    simp

end Mettapedia.Machines.AdmissionRewriting.TierNormalForms
