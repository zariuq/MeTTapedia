import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEErrorProtocol

/-!
# Binder scopes in the prepared machine against HE's bindings

HE's `let` is `unify` with `Empty` (its standard library); PeTTa's `let` unifies
as well. A variable a `let` binds stays bound on the evaluation path, through the
rest of the equation's body, and a `let` of a bound variable compares its value
with the bound one. `chain` substitutes its value into its template only, and
binds nothing afterwards. CeTTa's machine scopes its binders: a `let`'s variable
is in scope in its body, and a `let` of a variable in scope is an equality test.
The two agree where no variable is bound again after its scope ended, which is
what CeTTa's compiler now enforces: an ended scope retires its variables and a
later binder of a retired variable rejects the body; the branches of an `if`
compile under the retirements made before them and what follows sees all of
theirs; `chain` does not retire.

**The model** (`Ex`): variables, literals, a two-argument operation evaluated
left to right, `let`, `chain` and `if`.
* `he`: bindings threaded through evaluation (HE's and PeTTa's `let`);
* `mach`: lexical scopes (the machine);
* `adm`: the compiler's admission with its retirements;
* `admOld`: the admission before the fix, which ends scopes without retiring.

**Theorem** (`mach_eq_he`, `admitted_exact`): on every body the compiler
admits, the machine's value is HE's, from any environments that agree on the
variables in scope and leave the others unbound (`Inv`). The invariant HE's run
keeps is that a variable outside the scope is unbound unless retired, so a
retired variable's lingering binding is never read or bound again.

**Controls.**
* `Controls.sibling_relet`: `(+ (let $x 1 $x) (let $x $b $x))` at `$b = 2`:
  HE answers nothing, the old admission accepts it and the machine answers `3`,
  and the admission rejects it.
* `Controls.chain_then_let`: `(+ (chain (+ 1 1) $x $x) (let $x 3 $x))` is admitted
  and answers `5` in both.
* `Controls.branch_retires`: a `let` in one branch of an `if` retires its
  variable for what follows.
* HE's interpreter reproduces the sibling case once `unify` has its library
  declaration `(-> Atom Atom Atom Atom %Undefined%)`, which keeps its arguments
  unevaluated (`Controls.he_t7`): `(t7 2)` answers `Empty`, `(t7 1)` answers `2`.

**PeTTa's rule 8**, `(let $y e $y)` as `e` (`rule8_guarded`): exact where `$y` is
neither in scope nor retired after `e`, the admission of the rewritten form
retiring `$y` as the original's does; where `$y` is bound the rule changes the
answer (`Controls.rule8_unguarded`: `(= (s $y) (let $y 3 $y))`, `(s 4)`). The guard
is read after `e`: an `e` that binds `$y` retires it, and the source is then a
comparison the admission rejects, where a guard read before `e` rewrites it
(`Controls.rule8_checked_before`: `(let $y (let $y 1 2) $y)` answers nothing, its
rewrite `2`). CeTTa's compile now reads the guard after `e` (`admRule8C`), and its
admission is the source's (`rule8_c_order_exact`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.LetScopes

/-! ## The model -/

/-- Bodies with named variables: a variable, a literal, an operation on two
arguments evaluated left to right, `let`, `chain` and `if` (a nonzero condition
takes the first branch). -/
inductive Ex where
  | var (x : String)
  | lit (n : ℤ)
  | add (a b : Ex)
  | let_ (x : String) (v b : Ex)
  | chain (v : Ex) (x : String) (b : Ex)
  | ite (c t e : Ex)

/-- An environment: the variables bound, with their values. -/
abbrev Env := String → Option ℤ

/-- **HE's evaluation**: bindings are threaded through evaluation and persist;
a `let` of a bound variable compares; `chain` binds its variable for its
template only. -/
def he : Env → Ex → Option (ℤ × Env)
  | ρ, .var x => (ρ x).map fun n => (n, ρ)
  | ρ, .lit n => some (n, ρ)
  | ρ, .add a b => (he ρ a).bind fun p => (he p.2 b).map fun q => (p.1 + q.1, q.2)
  | ρ, .let_ x v b => (he ρ v).bind fun p =>
      match p.2 x with
      | some w => if w = p.1 then he p.2 b else none
      | none => he (Function.update p.2 x (some p.1)) b
  | ρ, .chain v x b => (he ρ v).bind fun p =>
      (he (Function.update p.2 x (some p.1)) b).map fun q => (q.1, Function.update q.2 x (p.2 x))
  | ρ, .ite c t e => (he ρ c).bind fun p => if p.1 ≠ 0 then he p.2 t else he p.2 e

/-- **The machine's evaluation**: lexical scopes; a `let` of a variable in scope
compares. -/
def mach : Env → Ex → Option ℤ
  | ρ, .var x => ρ x
  | _, .lit n => some n
  | ρ, .add a b => (mach ρ a).bind fun m => (mach ρ b).map fun n => m + n
  | ρ, .let_ x v b => (mach ρ v).bind fun w =>
      match ρ x with
      | some w' => if w' = w then mach ρ b else none
      | none => mach (Function.update ρ x (some w)) b
  | ρ, .chain v x b => (mach ρ v).bind fun w => mach (Function.update ρ x (some w)) b
  | ρ, .ite c t e => (mach ρ c).bind fun n => if n ≠ 0 then mach ρ t else mach ρ e

/-- **The compiler's admission** (`prepared_pure_context_end_scope`,
`prepared_pure_alternatives_*`): from the variables in scope and those retired,
the retired ones after the body, or a rejection. A variable read must be in
scope; a binder of a retired variable rejects; an ended `let` scope retires its
variable; the branches of an `if` compile under the same retirements and what
follows sees all of theirs; `chain` binds a variable neither in scope nor
retired and does not retire it. -/
def adm : Finset String → Finset String → Ex → Option (Finset String)
  | ctx, ret, .var x => if x ∈ ctx then some ret else none
  | _, ret, .lit _ => some ret
  | ctx, ret, .add a b => (adm ctx ret a).bind fun r => adm ctx r b
  | ctx, ret, .let_ x v b => (adm ctx ret v).bind fun r =>
      if x ∈ r then none
      else if x ∈ ctx then adm ctx r b
      else (adm (insert x ctx) r b).map fun r' => insert x r'
  | ctx, ret, .chain v x b => (adm ctx ret v).bind fun r =>
      if x ∈ ctx ∨ x ∈ r then none else adm (insert x ctx) r b
  | ctx, ret, .ite c t e => (adm ctx ret c).bind fun r =>
      (adm ctx r t).bind fun rt => (adm ctx r e).map fun re => rt ∪ re

/-- The admission before the fix: an ended scope drops its variable without
retiring it, so a later `let` of it binds afresh. -/
def admOld : Finset String → Ex → Bool
  | ctx, .var x => decide (x ∈ ctx)
  | _, .lit _ => true
  | ctx, .add a b => admOld ctx a && admOld ctx b
  | ctx, .let_ x v b => admOld ctx v && admOld (insert x ctx) b
  | ctx, .chain v x b => admOld ctx v && decide (x ∉ ctx) && admOld (insert x ctx) b
  | ctx, .ite c t e => admOld ctx c && admOld ctx t && admOld ctx e

/-! ## The machine is HE on admitted bodies -/

/-- **What the two runs keep**: HE's environment and the machine's agree on the
variables in scope, which are bound; the machine binds nothing else; HE binds
nothing outside the scope that is not retired. -/
structure Inv (ctx ret : Finset String) (ρh ρm : Env) : Prop where
  scope : ∀ x ∈ ctx, ρh x = ρm x ∧ (ρm x).isSome
  out : ∀ x, x ∉ ctx → ρm x = none
  unbound : ∀ x, x ∉ ctx → x ∉ ret → ρh x = none

theorem Inv.mono_ret {ctx ret ret' : Finset String} {ρh ρm : Env} (h : Inv ctx ret ρh ρm)
    (le : ret ⊆ ret') : Inv ctx ret' ρh ρm :=
  ⟨h.scope, h.out, fun x hc hr => h.unbound x hc fun hx => hr (le hx)⟩

/-- Binding a variable outside the scope and the retired ones, in both runs. -/
theorem Inv.bind {ctx ret : Finset String} {ρh ρm : Env} (h : Inv ctx ret ρh ρm) (x : String) (w : ℤ) :
    Inv (insert x ctx) ret (Function.update ρh x (some w)) (Function.update ρm x (some w)) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy hr => ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      simp
    · have hy' : y ∈ ctx := by simpa [hyx] using hy
      simpa [Function.update, hyx] using h.scope y hy'
  · have hyx : y ≠ x := fun e => hy (by simp [e])
    have hy' : y ∉ ctx := fun e => hy (by simp [e])
    simpa [Function.update, hyx] using h.out y hy'
  · have hyx : y ≠ x := fun e => hy (by simp [e])
    have hy' : y ∉ ctx := fun e => hy (by simp [e])
    simpa [Function.update, hyx] using h.unbound y hy' hr

/-- **On an admitted body the machine's value is HE's**, and HE's environment
afterwards keeps the invariant with the variables retired after the body. -/
theorem mach_eq_he :
    ∀ (e : Ex) (ctx ret r : Finset String) (ρh ρm : Env), adm ctx ret e = some r → Inv ctx ret ρh ρm →
      (he ρh e).map Prod.fst = mach ρm e ∧ ∀ p, he ρh e = some p → Inv ctx r p.2 ρm
  | .var x, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm] at ha
      split_ifs at ha with hx
      cases ha
      obtain ⟨heq, -⟩ := hi.scope x hx
      refine ⟨?_, fun p hp => ?_⟩
      · simp only [he, mach, heq, Option.map_map]
        cases ρm x <;> rfl
      · simp only [he] at hp
        cases hx' : ρh x with
        | none => simp [hx'] at hp
        | some n =>
            simp only [hx', Option.map_some, Option.some.injEq] at hp
            subst hp
            exact hi
  | .lit n, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm, Option.some.injEq] at ha
      subst ha
      refine ⟨rfl, fun p hp => ?_⟩
      simp only [he, Option.some.injEq] at hp
      subst hp
      exact hi
  | .add a b, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm] at ha
      cases har : adm ctx ret a with
      | none => simp [har] at ha
      | some r1 =>
          simp only [har, Option.bind_some] at ha
          obtain ⟨iha, ihaE⟩ := mach_eq_he a ctx ret r1 ρh ρm har hi
          cases hea : he ρh a with
          | none =>
              simp only [hea, Option.map_none] at iha
              refine ⟨?_, fun p hp => by simp [he, hea] at hp⟩
              simp [he, mach, hea, ← iha]
          | some pa =>
              simp only [hea, Option.map_some] at iha
              have hi1 := ihaE pa hea
              obtain ⟨ihb, ihbE⟩ := mach_eq_he b ctx r1 r pa.2 ρm ha hi1
              refine ⟨?_, fun p hp => ?_⟩
              · simp only [he, mach, hea, Option.bind_some, ← iha]
                cases heb : he pa.2 b with
                | none =>
                    simp only [heb, Option.map_none] at ihb
                    simp [← ihb]
                | some pb =>
                    simp only [heb, Option.map_some] at ihb
                    simp [← ihb]
              · simp only [he, hea, Option.bind_some] at hp
                cases heb : he pa.2 b with
                | none => simp [heb] at hp
                | some pb =>
                    simp only [heb, Option.map_some, Option.some.injEq] at hp
                    subst hp
                    exact ihbE pb heb
  | .let_ x v b, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm] at ha
      cases hav : adm ctx ret v with
      | none => simp [hav] at ha
      | some r1 =>
          simp only [hav, Option.bind_some] at ha
          obtain ⟨ihv, ihvE⟩ := mach_eq_he v ctx ret r1 ρh ρm hav hi
          split_ifs at ha with hxr hxc
          · -- a `let` of a variable in scope: a test in both
            cases hev : he ρh v with
            | none =>
                simp only [hev, Option.map_none] at ihv
                refine ⟨?_, fun p hp => by simp [he, hev] at hp⟩
                simp [he, mach, hev, ← ihv]
            | some pv =>
                simp only [hev, Option.map_some] at ihv
                have hi1 := ihvE pv hev
                obtain ⟨heq, hsome⟩ := hi1.scope x hxc
                obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp hsome
                have hpx : pv.2 x = some w0 := heq.trans hw0
                obtain ⟨ihb, ihbE⟩ := mach_eq_he b ctx r1 r pv.2 ρm ha hi1
                refine ⟨?_, fun p hp => ?_⟩
                · simp only [he, mach, hev, Option.bind_some, ← ihv, hpx, hw0]
                  split_ifs
                  · exact ihb
                  · rfl
                · simp only [he, hev, Option.bind_some, hpx] at hp
                  split_ifs at hp
                  exact ihbE p hp
          · -- a `let` of a variable neither in scope nor retired: both bind
            cases hab : adm (insert x ctx) r1 b with
            | none => simp [hab] at ha
            | some r2 =>
                simp only [hab, Option.map_some, Option.some.injEq] at ha
                subst ha
                cases hev : he ρh v with
                | none =>
                    simp only [hev, Option.map_none] at ihv
                    refine ⟨?_, fun p hp => by simp [he, hev] at hp⟩
                    simp [he, mach, hev, ← ihv]
                | some pv =>
                    simp only [hev, Option.map_some] at ihv
                    have hi1 := ihvE pv hev
                    have hpx : pv.2 x = none := hi1.unbound x hxc hxr
                    have hmx : ρm x = none := hi1.out x hxc
                    obtain ⟨ihb, ihbE⟩ := mach_eq_he b (insert x ctx) r1 r2 _ _ hab (hi1.bind x pv.1)
                    refine ⟨?_, fun p hp => ?_⟩
                    · simp only [he, mach, hev, Option.bind_some, ← ihv, hpx, hmx]
                      exact ihb
                    · simp only [he, hev, Option.bind_some, hpx] at hp
                      have hi2 := ihbE p hp
                      refine ⟨fun y hy => ?_, fun y hy => hi1.out y hy, fun y hy hr => ?_⟩
                      · have hyx : y ≠ x := fun e => hxc (e ▸ hy)
                        simpa [Function.update, hyx] using hi2.scope y (by simp [hy])
                      · have hyx : y ≠ x := fun e => hr (by simp [e])
                        have hr' : y ∉ r2 := fun e => hr (by simp [e])
                        exact hi2.unbound y (by simp [hyx, hy]) hr'
  | .chain v x b, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm] at ha
      cases hav : adm ctx ret v with
      | none => simp [hav] at ha
      | some r1 =>
          simp only [hav, Option.bind_some] at ha
          split_ifs at ha with hx
          have hxc : x ∉ ctx := fun e => hx (.inl e)
          have hxr : x ∉ r1 := fun e => hx (.inr e)
          obtain ⟨ihv, ihvE⟩ := mach_eq_he v ctx ret r1 ρh ρm hav hi
          cases hev : he ρh v with
          | none =>
              simp only [hev, Option.map_none] at ihv
              refine ⟨?_, fun p hp => by simp [he, hev] at hp⟩
              simp [he, mach, hev, ← ihv]
          | some pv =>
              simp only [hev, Option.map_some] at ihv
              have hi1 := ihvE pv hev
              have hpx : pv.2 x = none := hi1.unbound x hxc hxr
              obtain ⟨ihb, ihbE⟩ := mach_eq_he b (insert x ctx) r1 r _ _ ha (hi1.bind x pv.1)
              refine ⟨?_, fun p hp => ?_⟩
              · simp only [he, mach, hev, Option.bind_some, ← ihv, Option.map_map]
                rw [← ihb]
                cases he (Function.update pv.2 x (some pv.1)) b <;> rfl
              · simp only [he, hev, Option.bind_some] at hp
                cases heb : he (Function.update pv.2 x (some pv.1)) b with
                | none => simp [heb] at hp
                | some pb =>
                    simp only [heb, Option.map_some, Option.some.injEq] at hp
                    subst hp
                    have hi2 := ihbE pb heb
                    refine ⟨fun y hy => ?_, fun y hy => hi1.out y hy, fun y hy hr => ?_⟩
                    · have hyx : y ≠ x := fun e => hxc (e ▸ hy)
                      simpa [Function.update, hyx] using hi2.scope y (by simp [hy])
                    · by_cases hyx : y = x
                      · subst hyx
                        simp [Function.update, hpx]
                      · simpa [Function.update, hyx] using hi2.unbound y (by simp [hyx, hy]) hr
  | .ite c t e, ctx, ret, r, ρh, ρm, ha, hi => by
      simp only [adm] at ha
      cases hac : adm ctx ret c with
      | none => simp [hac] at ha
      | some r1 =>
          simp only [hac, Option.bind_some] at ha
          cases hat : adm ctx r1 t with
          | none => simp [hat] at ha
          | some rt =>
              simp only [hat, Option.bind_some] at ha
              cases hae : adm ctx r1 e with
              | none => simp [hae] at ha
              | some re =>
                  simp only [hae, Option.map_some, Option.some.injEq] at ha
                  subst ha
                  obtain ⟨ihc, ihcE⟩ := mach_eq_he c ctx ret r1 ρh ρm hac hi
                  cases hec : he ρh c with
                  | none =>
                      simp only [hec, Option.map_none] at ihc
                      refine ⟨?_, fun p hp => by simp [he, hec] at hp⟩
                      simp [he, mach, hec, ← ihc]
                  | some pc =>
                      simp only [hec, Option.map_some] at ihc
                      have hi1 := ihcE pc hec
                      obtain ⟨iht, ihtE⟩ := mach_eq_he t ctx r1 rt pc.2 ρm hat hi1
                      obtain ⟨ihe, iheE⟩ := mach_eq_he e ctx r1 re pc.2 ρm hae hi1
                      refine ⟨?_, fun p hp => ?_⟩
                      · simp only [he, mach, hec, Option.bind_some, ← ihc]
                        split_ifs
                        · exact iht
                        · exact ihe
                      · simp only [he, hec, Option.bind_some] at hp
                        split_ifs at hp
                        · exact (ihtE p hp).mono_ret Finset.subset_union_left
                        · exact (iheE p hp).mono_ret Finset.subset_union_right

/-- **An admitted equation body answers HE's value**, its parameters bound to
the arguments in both runs. -/
theorem admitted_exact (e : Ex) (ctx : Finset String) (r : Finset String) (ρ : Env)
    (ha : adm ctx ∅ e = some r) (bound : ∀ x ∈ ctx, (ρ x).isSome) (only : ∀ x, x ∉ ctx → ρ x = none) :
    (he ρ e).map Prod.fst = mach ρ e :=
  (mach_eq_he e ctx ∅ r ρ ρ ha ⟨fun x hx => ⟨rfl, bound x hx⟩, only, fun x hx _ => only x hx⟩).1

/-! ## PeTTa's rule 8 -/

/-- **Rule 8 where `$y` is neither in scope nor retired** (`(let $y e $y)` as
`e`): the machine's value is the same, and the admission of the rewritten form
retires `$y` as the original's does, so HE's answers follow by `mach_eq_he`. -/
theorem rule8_guarded (ctx ret : Finset String) (y : String) (e : Ex) (ρ : Env) (hy : ρ y = none)
    (fresh : y ∉ ctx) (notRetired : ∀ r, adm ctx ret e = some r → y ∉ r) :
    mach ρ (.let_ y e (.var y)) = mach ρ e ∧
      adm ctx ret (.let_ y e (.var y)) = (adm ctx ret e).map fun r => insert y r := by
  constructor
  · simp only [mach, hy]
    cases mach ρ e with
    | none => rfl
    | some w => simp [Function.update]
  · simp only [adm]
    cases hae : adm ctx ret e with
    | none => rfl
    | some r =>
        have hyr : y ∉ r := notRetired r hae
        simp [hyr, fresh]

/-- **CeTTa's compile of `(let $y e $y)`** in PeTTa with normalization on: `e`
first, then the guard on the scope and on the retirements `e` leaves; where it
holds the bound value is the result and `$y` is retired, otherwise the `let`
compiles as written. The `let*` rule is the same at its last pair
(`AdmissionRewriting.TierNormalForms.letStar_snoc_let`). -/
def admRule8C (ctx ret : Finset String) (y : String) (e : Ex) : Option (Finset String) :=
  (adm ctx ret e).bind fun r =>
    if y ∉ ctx ∧ y ∉ r then some (insert y r) else adm ctx ret (.let_ y e (.var y))

/-- **The C's order is the guarded rule**: its admission is the source's, so the
rule never admits a body the admission rejects, and where it rewrites, the machine
answers the source's value. -/
theorem rule8_c_order_exact (ctx ret : Finset String) (y : String) (e : Ex) :
    admRule8C ctx ret y e = adm ctx ret (.let_ y e (.var y)) ∧
      ∀ r ρ, adm ctx ret e = some r → y ∉ ctx → y ∉ r → ρ y = none →
        mach ρ (.let_ y e (.var y)) = mach ρ e := by
  refine ⟨?_, fun r ρ hr hctx hret hρ => (rule8_guarded ctx ret y e ρ hρ hctx fun r' hr' => by
    rw [hr] at hr'
    cases hr'
    exact hret).1⟩
  unfold admRule8C
  cases hae : adm ctx ret e with
  | none => simp [adm, hae]
  | some r =>
      simp only [Option.bind_some]
      split_ifs with h
      · obtain ⟨hctx, hret⟩ := h
        simp [adm, hae, hret, hctx]
      · rfl

/-! ## Controls -/

namespace Controls

/-- `(+ (let $x 1 $x) (let $x $b $x))`. -/
def siblings : Ex := .add (.let_ "x" (.lit 1) (.var "x")) (.let_ "x" (.var "b") (.var "x"))

/-- `$b` bound to `2`. -/
def bTwo : Env := fun x => if x = "b" then some 2 else none

/-- **The sibling re-binding** (`tests/he/typed_rule_controls/let_rebinding`): HE
answers nothing at `$b = 2` (the second `let` compares `2` with `1`); the old
admission accepted the body and the machine answered `3`; the admission with
retirements rejects it. -/
theorem sibling_relet :
    he bTwo siblings = none ∧ admOld {"b"} siblings = true ∧ mach bTwo siblings = some 3 ∧
      adm {"b"} ∅ siblings = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `(+ (chain (+ 1 1) $x $x) (let $x 3 $x))`: `chain` does not retire. -/
def chainThenLet : Ex := .add (.chain (.add (.lit 1) (.lit 1)) "x" (.var "x")) (.let_ "x" (.lit 3) (.var "x"))

theorem chain_then_let :
    adm ∅ ∅ chainThenLet = some {"x"} ∧ (he (fun _ => none) chainThenLet).map Prod.fst = some 5 ∧
      mach (fun _ => none) chainThenLet = some 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `(+ (if $c (let $x 1 $x) 0) (let $x 2 $x))`: the `let` in one branch retires
`$x` for what follows. -/
def branchLet : Ex := .add (.ite (.var "c") (.let_ "x" (.lit 1) (.var "x")) (.lit 0)) (.let_ "x" (.lit 2) (.var "x"))

theorem branch_retires :
    adm {"c"} ∅ branchLet = none ∧ admOld {"c"} branchLet = true ∧
      he (fun x => if x = "c" then some 1 else none) branchLet = none ∧
      mach (fun x => if x = "c" then some 1 else none) branchLet = some 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Rule 8 where `$y` is bound** (`(= (s $y) (let $y 3 $y))`, `(s 4)`): the
`let` compares and answers nothing, while `e` answers `3`. -/
theorem rule8_unguarded :
    mach (fun x => if x = "y" then some 4 else none) (.let_ "y" (.lit 3) (.var "y")) = none ∧
      mach (fun x => if x = "y" then some 4 else none) (.lit 3) = some 3 ∧
      (he (fun x => if x = "y" then some 4 else none) (.let_ "y" (.lit 3) (.var "y"))).map Prod.fst = none := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `(let $y (let $y 1 2) $y)`: the bound expression binds `$y`, and its scope
ends. -/
def innerRebind : Ex := .let_ "y" (.let_ "y" (.lit 1) (.lit 2)) (.var "y")

/-- **Rule 8's guard must be read after the bound expression**
(`(= (f) (let $y (let $y 1 2) $y))`; stable-fixed PeTTa and CeTTa's canonical
evaluator answer nothing, CeTTa's machine `2`): `$y` is neither in scope nor
retired before `(let $y 1 2)`, which binds and retires it. HE and PeTTa answer
nothing (the outer `let` compares `1` with `2`), the admission rejects the source,
and the rewritten body answers `2`. -/
theorem rule8_checked_before :
    he (fun _ => none) innerRebind = none ∧ adm ∅ ∅ innerRebind = none ∧
      adm ∅ ∅ (.let_ "y" (.lit 1) (.lit 2)) = some {"y"} ∧
      mach (fun _ => none) (.let_ "y" (.lit 1) (.lit 2)) = some 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### HE's interpreter -/

section HE

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter (symbol apply equation typed)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls (arrowAtom answersWith)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns.Controls (num)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEErrorProtocol (letType)

/-- `unify`'s library declaration: its arguments are held, so its else branch
`Empty` is not evaluated as an argument. -/
def unifyType : Atom :=
  arrowAtom [Atom.atomType, Atom.atomType, Atom.atomType, Atom.atomType, Atom.undefinedType]

/-- HE's `let` as its standard library defines it, with
`(= (t7 $b) (+ (let $x 1 $x) (let $x $b $x)))` and
`(= (c1) (+ (chain (+ 1 1) $x $x) (let $x 3 $x)))`. -/
def letSpace : Space := Space.ofList [
  typed "unify" unifyType,
  typed "let" letType,
  equation (apply "let" [.var "pattern", .var "atom", .var "template"])
    (apply "unify" [.var "atom", .var "pattern", .var "template", symbol "Empty"]),
  typed "+" (arrowAtom [symbol "Number", symbol "Number", symbol "Number"]),
  equation (apply "t7" [.var "b"])
    (apply "+" [apply "let" [.var "x", num 1, .var "x"], apply "let" [.var "x", .var "b", .var "x"]]),
  equation (apply "c1" [])
    (apply "+" [apply "chain" [apply "+" [num 1, num 1], .var "x", .var "x"],
      apply "let" [.var "x", num 3, .var "x"]])]

/-- **HE's interpreter on the sibling re-binding**: `(t7 2)` answers `Empty` (no
answer) and `(t7 1)` answers `2`, at budgets twenty-four and forty. -/
theorem he_t7 :
    answersWith letSpace (apply "t7" [num 2]) 24 = [symbol "Empty"] ∧
      answersWith letSpace (apply "t7" [num 2]) 40 = [symbol "Empty"] ∧
      answersWith letSpace (apply "t7" [num 1]) 24 = [num 2] ∧
      answersWith letSpace (apply "t7" [num 1]) 40 = [num 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`chain` binds nothing afterwards**: `(c1)` answers `5`. -/
theorem he_chain_then_let :
    answersWith letSpace (apply "c1" []) 24 = [num 5] ∧ answersWith letSpace (apply "c1" []) 40 = [num 5] := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end HE

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.LetScopes
