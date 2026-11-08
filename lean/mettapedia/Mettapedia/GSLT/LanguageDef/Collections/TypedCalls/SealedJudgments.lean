import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedSorts

/-!
# Values certify, computations refute: the two judgments of PeTTa's `ai` profile

PeTTa's relation reads a function's declared result twice: as the type of what
running a call returns, and as the type of the call held as data. The `ai`
profile keeps the two apart.

* **The value judgment** (`SealedSorts.sealedInfo`) types data: a function's rows
  never type an application of it, which has its tuple type alone
  (`value_ignores_comp`), while a constructor's application is typed through the
  same rows the computation judgment reads (`value_eq_comp_of_ctor`). It alone
  certifies: a guard accepts a value through it, and only it licenses a fold's
  cell-test drop. A held call is never certified at a sealed sort
  (`held_call_not_certified`, `held_call_not_certified_nat`), whatever its
  declared result.
* **The computation judgment** (`compInfo`, `CompTypable`, `compTypable_iff_row`)
  types a call by its head's declared rows, the arguments typed as values: what
  running the call returns. It may refute: a call whose answers cannot pass a
  guard need not run (`refute_exact`, `refute_checked_call`, `refute_version`).
  It never certifies: running `(build 1 Nil)` returns a `(List Number)`, and the
  held call is none (`Controls.held_build_two_judgments`).

**Refuting is exact by shape, not by unification.** Every answer of a checked call
passed its result guard at the declared result `R`, and a version proves it does
(`SealedSorts.sealed_version_results`). Rejecting the call at a request `T` has the
answers, multiplicities included, of running it and checking each answer at `T`,
exactly when no ground value of `R` passes the guard at `T` (`RefutesGround`). That
holds when `R` and `T` are no metatype names and have different head paths
(`shapeOf`), under functional declarations whose rows are rigid in head, a
function's range aside, since it types no value of the profile (`SealedRigidSig`,
`refutesGround_of_shape`; `Controls.idt_exempt`, while a constant declared at a type
variable breaks the rule, `Controls.poly_constant_breaks`). Three controls bound
the rule:
* two closed types that do not unify may share a value: `Nil` passes both
  `(List Number)` and `(List String)` (`Controls.nil_in_both_lists`), so
  `(build 0 Nil)` at `(List String)` must run;
* a metatype request accepts by the value's metatype: `(Cons 1 Nil)` passes
  `Expression` (`Controls.cell_passes_expression`);
* a variable passes every guard (`Controls.variable_passes_all`), so the answers must
  be ground.
Positive: a `(List Number)` call is refuted at `Nat` (`Controls.list_refutes_nat`),
and so is `build` through its version (`Controls.build_refuted_at_nat`).

**Versions are the full checked call in the profile.** PeTTa's protocol reads the
relation only through the records it guards, so it is stated over any relation
(`chainCallI`), and PeTTa's own protocol is its instance at `info Γ`
(`chainCall_eq_I`). Over the profile's relation the version theorem holds as for
PeTTa's (`sversion_eq_protocol`, `schecked_call_eq`), and for every relation the
contract analysis accepts through constructors only
(`sealed_accepted_version_eq_protocol`, `sealed_accepted_checked_call_eq`): the
fast paths that skip guards stay sound in the profile. Positive:
`Controls.build_version_is_protocol`. Negative: data built through a function's
row passes PeTTa's analysis and is no value of its declared sort in the profile,
so the profile's checked call answers nothing where a version that trusted the
analysis would answer the held call (`Controls.function_head_construction_breaks`);
the side condition `ExprSafe` is needed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedJudgments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open TypedCalls.Controls (listOf consRow cons_constructor)
open CertifiedSpines
open TypedFoldBound (termRows)
open SealedSorts

/-! ## The protocol of a closed row over any relation -/

section ProtocolOver

variable (I : Atom → Info) (kind : Atom → String)

/-- The guards of the parameters, as in `guards`, over the relation `I`. -/
noncomputable def guardsI : ℕ → List (Ty String) → List Atom → List (Eqn CallVar) →
    Multiset (List (Eqn CallVar))
  | _, [], [], S => {S}
  | k, A :: As, v :: vs, S =>
      if demand A = .guarded then
        (guard (atGuard k) S (A.map .inl) (I v) (kind v)).bind (guardsI (k + 1) As vs)
      else guardsI (k + 1) As vs S
  | _, [], _ :: _, _ => 0
  | _, _ :: _, [], _ => 0

/-- The result guard of a row over the relation `I`. -/
noncomputable def resultGuardI (k : ℕ) (R : Ty String) (S : List (Eqn CallVar)) (r : Atom) :
    Multiset Atom :=
  if ResultGuarded R then (guard (atGuard k) S (R.map .inl) (I r) (kind r)).map fun _ => r
  else {r}

/-- **The protocol of one row over the relation `I`**: the arguments' guards, the
body, and the result's guard. -/
noncomputable def chainCallI (body : List Atom → Multiset Atom) (τ : Ty String) (vs : List Atom) :
    Multiset Atom :=
  match arrowSplit τ with
  | some (As, R) =>
      (guardsI I kind 0 As vs []).bind fun S => (body vs).bind (resultGuardI I kind As.length R S)
  | none => 0

/-- The product of the guard counts of the guarded parameters of a closed row. -/
noncomputable def argCountI : List (Ty Empty) → List Atom → ℕ
  | [], [] => 1
  | A :: As, v :: vs =>
      (if demand A.lift = .guarded then guardCount (I v) A (kind v) else 1) * argCountI As vs
  | [], _ :: _ => 0
  | _ :: _, [] => 0

theorem guards_closed_bindI {β : Type} (n : ℕ) (f : List (Eqn CallVar) → Multiset β)
    (t : Multiset β) (hf : ∀ S, StoreOK n S → f S = t) :
    ∀ (k : ℕ) (As : List (Ty Empty)) (vs : List Atom) (S : List (Eqn CallVar)),
      k + As.length ≤ n → StoreOK k S →
      (guardsI I kind k (As.map Ty.lift) vs S).bind f = argCountI I kind As vs • t
  | k, [], [], S, le, hS => by
      simp [guardsI, argCountI, hf S (hS.mono (by simpa using le)), one_nsmul]
  | k, A :: As, v :: vs, S, le, hS => by
      simp only [List.length_cons] at le
      simp only [List.map_cons, guardsI, argCountI]
      split_ifs with hd
      · rw [Multiset.bind_assoc]
        have each : ∀ S' ∈ guard (atGuard k) S ((A.lift : Ty String).map Sum.inl) (I v) (kind v),
            (guardsI I kind (k + 1) (As.map Ty.lift) vs S').bind f = argCountI I kind As vs • t := by
          intro S' hS'
          rw [lift_map_inl] at hS'
          exact guards_closed_bindI n f t hf (k + 1) As vs S' (by omega)
            (guard_closed_stores hS A _ _ S' hS')
        rw [Multiset.bind_congr each, bind_const', lift_map_inl,
          card_guard_closed (atGuard k) (atGuard_injective k) S hS.fresh hS.1 A _ _, ← mul_nsmul,
          Nat.mul_comm]
      · rw [one_mul]
        exact guards_closed_bindI n f t hf (k + 1) As vs S (by omega) (hS.mono (by omega))
  | _, [], _ :: _, _, _, _ => by simp [guardsI, argCountI]
  | _, _ :: _, [], _, _, _ => by simp [guardsI, argCountI]

theorem resultGuard_closedI {k : ℕ} {S : List (Eqn CallVar)} (hS : StoreOK k S) (R : Ty Empty)
    (r : Atom) :
    resultGuardI I kind k R.lift S r =
      if ResultGuarded R.lift then guardCount (I r) R (kind r) • {r} else {r} := by
  unfold resultGuardI
  split_ifs
  · rw [lift_map_inl, Multiset.map_const',
      card_guard_closed (atGuard k) (atGuard_injective k) S hS.fresh hS.1 R _ _,
      Multiset.nsmul_singleton]
  · rfl

/-- **The protocol of a closed row factors**, over any relation: each answer of the
body counted by its result guard, the whole counted by the argument guards. -/
theorem chainCall_closedI (body : List Atom → Multiset Atom) (As : List (Ty Empty)) (R : Ty Empty)
    (vs : List Atom) :
    chainCallI I kind body (arrow (As.map Ty.lift) R.lift) vs =
      argCountI I kind As vs • (body vs).bind fun r =>
        if ResultGuarded R.lift then guardCount (I r) R (kind r) • {r} else {r} := by
  unfold chainCallI
  rw [arrowSplit_arrow]
  dsimp only
  rw [List.length_map]
  refine guards_closed_bindI I kind As.length _ _ (fun S hS => ?_) 0 As vs [] (by omega)
    StoreOK.nil
  exact Multiset.bind_congr fun r _ => resultGuard_closedI I kind hS R r

end ProtocolOver

/-- PeTTa's guards are the guards over its relation. -/
theorem guards_eq_I (Γ : Decls) (kind : Atom → String) :
    ∀ (k : ℕ) (As : List (Ty String)) (vs : List Atom) (S : List (Eqn CallVar)),
      guards Γ kind k As vs S = guardsI (info Γ) kind k As vs S
  | _, [], [], _ => rfl
  | k, A :: As, v :: vs, S => by
      simp only [guards, guardsI]
      split_ifs
      · congr 1
        funext S'
        exact guards_eq_I Γ kind (k + 1) As vs S'
      · exact guards_eq_I Γ kind (k + 1) As vs S
  | _, [], _ :: _, _ => rfl
  | _, _ :: _, [], _ => rfl

/-- **PeTTa's protocol is the protocol over its relation**, so the profile's protocol is
PeTTa's with the relation swapped. -/
theorem chainCall_eq_I (Γ : Decls) (kind : Atom → String) (body : List Atom → Multiset Atom)
    (τ : Ty String) (vs : List Atom) :
    chainCall Γ kind body τ vs = chainCallI (info Γ) kind body τ vs := by
  unfold chainCall chainCallI
  cases h : arrowSplit τ with
  | none => rfl
  | some p =>
      obtain ⟨As, R⟩ := p
      simp only
      rw [guards_eq_I]
      rfl

/-! ## Versions are the full checked call in the profile -/

section SealedProtocol

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs] (grounded : String → Bool)

/-- **The full checked call of the profile**, at every call. -/
noncomputable def sealedProtocolRun (body : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (row : Ty String) : ℕ → List Atom → Multiset Atom
  | 0, _ => 0
  | n + 1, vs =>
      chainCallI (sealedInfo Γ funs) (metatype grounded) (body (sealedProtocolRun body row n)) row vs

variable {Γ funs grounded}

theorem SHolds.guardCount {v : Atom} {T : Ty Empty} (h : SHolds Γ funs grounded v T) :
    TypedCalls.guardCount (sealedInfo Γ funs v) T (metatype grounded v) = 1 := by
  unfold SHolds at h
  split_ifs at h with hm
  · exact h
  · rw [guardCount_of_ne (sealedInfo Γ funs v) T (metatype grounded v)
      fun same => hm (same ▸ metaName_metatype grounded v)]
    exact h

theorem SHolds.of_guardCount (hΓ : Functional Γ) {v : Atom} {T : Ty Empty}
    (h : TypedCalls.guardCount (sealedInfo Γ funs v) T (metatype grounded v) ≠ 0) :
    SHolds Γ funs grounded v T := by
  unfold SHolds
  split_ifs with hm
  · unfold TypedCalls.guardCount at h ⊢
    have := sealed_count_le_one (funs := funs) hΓ v T
    split_ifs at h ⊢ with h0 h1 <;> omega
  · rw [guardCount_of_ne (sealedInfo Γ funs v) T (metatype grounded v)
      fun same => hm (same ▸ metaName_metatype grounded v)] at h
    have := sealed_count_le_one (funs := funs) hΓ v T
    omega

/-- The entry facts make every argument guard succeed exactly once. -/
theorem sargCount_of_entryFacts : ∀ {As : List (Ty Empty)} {vs : List Atom},
    SEntryFacts Γ funs grounded As vs → argCountI (sealedInfo Γ funs) (metatype grounded) As vs = 1
  | [], [], _ => rfl
  | A :: As, v :: vs, .cons hA hAs => by
      simp only [argCountI]
      rw [sargCount_of_entryFacts hAs, mul_one]
      split_ifs with hg
      · exact SHolds.guardCount (hA hg)
      · rfl

/-- Under functional declarations, arguments that pass a closed row's guards meet the
entry facts. -/
theorem sentryFacts_of_argCount (hΓ : Functional Γ) :
    ∀ {As : List (Ty Empty)} {vs : List Atom},
      argCountI (sealedInfo Γ funs) (metatype grounded) As vs ≠ 0 → SEntryFacts Γ funs grounded As vs
  | [], [], _ => .nil
  | A :: As, v :: vs, h => by
      simp only [argCountI] at h
      refine .cons (fun hg => ?_) (sentryFacts_of_argCount hΓ fun h0 => h (by rw [h0, mul_zero]))
      rw [if_pos hg] at h
      exact SHolds.of_guardCount hΓ fun h0 => h (by rw [h0, zero_mul])
  | [], _ :: _, h => (h rfl).elim
  | _ :: _, [], h => by simp [argCountI] at h

/-- The hypotheses of the version theorem in the profile's relation. -/
structure SVersionHyps (bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom)
    (As : List (Ty Empty)) (R : Ty Empty) : Prop where
  resultGuarded : ResultGuarded R.lift
  calls : ∀ o o' : List Atom → Multiset Atom,
    (∀ ws, SEntryFacts Γ funs grounded As ws → o ws = o' ws) →
    (∀ ws, SEntryFacts Γ funs grounded As ws → ∀ r ∈ o ws, SHolds Γ funs grounded r R) →
    ∀ vs, SEntryFacts Γ funs grounded As vs → bodyP o vs = bodyV o' vs
  results : ∀ o : List Atom → Multiset Atom,
    (∀ ws, SEntryFacts Γ funs grounded As ws → ∀ r ∈ o ws, SHolds Γ funs grounded r R) →
    ∀ vs, SEntryFacts Γ funs grounded As vs → ∀ r ∈ bodyV o vs, SHolds Γ funs grounded r R

theorem sversion_results {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : SVersionHyps (Γ := Γ) (funs := funs) (grounded := grounded) bodyP bodyV As R) :
    ∀ n vs, SEntryFacts Γ funs grounded As vs → ∀ r ∈ versionRun bodyV n vs, SHolds Γ funs grounded r R
  | 0, _, _, r, hr => absurd hr (Multiset.notMem_zero r)
  | n + 1, vs, hvs, r, hr => h.results _ (sversion_results h n) vs hvs r hr

/-- **The version is the profile's protocol**: on arguments meeting the entry facts,
the run whose calls to themselves skip the protocol has, at every fuel, exactly
the answers of the run whose every call runs it. -/
theorem sversion_eq_protocol {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : SVersionHyps (Γ := Γ) (funs := funs) (grounded := grounded) bodyP bodyV As R) :
    ∀ n vs, SEntryFacts Γ funs grounded As vs →
      sealedProtocolRun Γ funs grounded bodyP (arrow (As.map Ty.lift) R.lift) n vs = versionRun bodyV n vs
  | 0, _, _ => rfl
  | n + 1, vs, hvs => by
      simp only [sealedProtocolRun, versionRun]
      rw [chainCall_closedI, sargCount_of_entryFacts hvs, one_nsmul]
      simp only [if_pos h.resultGuarded]
      rw [h.calls _ _ (sversion_eq_protocol h n) (fun ws hws r hr => by
          rw [sversion_eq_protocol h n ws hws] at hr
          exact sversion_results h n ws hws r hr) vs hvs]
      refine (Multiset.bind_congr (g := fun r => ({r} : Multiset Atom)) fun r hr => ?_).trans ?_
      · rw [SHolds.guardCount (h.results _ (sversion_results h n) vs hvs r hr), one_nsmul]
      · rw [Multiset.bind_singleton, Multiset.map_id']

/-- **A checked call has the same answers through the version**, on every argument
list, in the profile. -/
theorem schecked_call_eq (hΓ : Functional Γ)
    {bodyP bodyV : (List Atom → Multiset Atom) → List Atom → Multiset Atom}
    {As : List (Ty Empty)} {R : Ty Empty}
    (h : SVersionHyps (Γ := Γ) (funs := funs) (grounded := grounded) bodyP bodyV As R) (n : ℕ)
    (vs : List Atom) :
    chainCallI (sealedInfo Γ funs) (metatype grounded)
        (bodyP (sealedProtocolRun Γ funs grounded bodyP (arrow (As.map Ty.lift) R.lift) n))
        (arrow (As.map Ty.lift) R.lift) vs =
      chainCallI (sealedInfo Γ funs) (metatype grounded) (bodyV (versionRun bodyV n))
        (arrow (As.map Ty.lift) R.lift) vs := by
  rw [chainCall_closedI, chainCall_closedI]
  by_cases h0 : argCountI (sealedInfo Γ funs) (metatype grounded) As vs = 0
  · rw [h0, zero_nsmul, zero_nsmul]
  · have hvs := sentryFacts_of_argCount hΓ h0
    rw [h.calls _ _ (sversion_eq_protocol h n) (fun ws hws r hr => by
      rw [sversion_eq_protocol h n ws hws] at hr
      exact sversion_results h n ws hws r hr) vs hvs]

variable {res : String → Ty Empty} {ent : String → List (Ty Empty)}

/-- Oracles that agree wherever the analysis calls them, in the profile. -/
def SOracleAgree (ent : String → List (Ty Empty)) (As : List (Ty String)) (O O' : Oracle) : Prop :=
  (∀ ws, SEntryPoly Γ funs grounded As ws → O.self ws = O'.self ws) ∧
    ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → O.enter f ws = O'.enter f ws

variable {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty String)} {E : Env}

mutual
/-- **The calls the analysis checks are made where the oracles agree**, in the profile. -/
theorem sealed_eval_congr (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O O' : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O) (agree : SOracleAgree (Γ := Γ) (funs := funs)
      (grounded := grounded) ent As O O') :
    ∀ (e : Expr) (ρ : List (String × Atom)), SMeetsFacts Γ funs grounded Φ ρ → ExprSafe funs e →
      CallsOK Γ res ent Φ R As e → e.eval E O ρ = e.eval E O' ρ
  | .var _, _, _, _, _ => rfl
  | .const _, _, _, _, _ => rfl
  | .ctor c args, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | ctor hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (sealed_evalAll_congr hΓ hE hO agree args ρ facts) e he (exprSafeAll_mem safe.2 e he)
              (hargs e he)]
  | .self args, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | self hargs typed =>
          simp only [Expr.eval]
          rw [← Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (sealed_evalAll_congr hΓ hE hO agree args ρ facts) e he (exprSafeAll_mem safe e he)
              (hargs e he)]
          refine Multiset.bind_congr fun ws hws => agree.1 ws ?_
          exact forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
            fun A e w he hA hw hg => by
              obtain ⟨τ, hτ⟩ := hA hg
              exact ⟨τ, List.forall_iff_forall_mem.mp
                (sealed_evalAll_sound hΓ hE hO args ρ facts) e he (exprSafeAll_mem safe e he) _ hτ
                  (hargs e he) w hw⟩
  | .prim op args, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | prim hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (sealed_evalAll_congr hΓ hE hO agree args ρ facts) e he (exprSafeAll_mem safe e he)
              (hargs e he)]
  | .call f args, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | call hargs =>
          simp only [Expr.eval]
          rw [Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (sealed_evalAll_congr hΓ hE hO agree args ρ facts) e he (exprSafeAll_mem safe e he)
              (hargs e he)]
  | .enter f args, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | enter hargs typed =>
          simp only [Expr.eval]
          rw [← Expr.evalAll_congr args fun e he => List.forall_iff_forall_mem.mp
            (sealed_evalAll_congr hΓ hE hO agree args ρ facts) e he (exprSafeAll_mem safe e he)
              (hargs e he)]
          refine Multiset.bind_congr fun ws hws => agree.2 f ws ?_
          exact forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
            fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
              (sealed_evalAll_sound hΓ hE hO args ρ facts) e he (exprSafeAll_mem safe e he) A (hA hg)
                (hargs e he) w hw
  | .letE p val body, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | letE hcv hcb =>
          simp only [Expr.eval]
          rw [sealed_eval_congr hΓ hE hO agree val ρ facts safe.1 hcv]
          refine Multiset.bind_congr fun w _ => ?_
          split
          · next ρ' hm =>
              exact sealed_eval_congr hΓ hE hO agree body ρ'
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) safe.2 hcb
          · rfl
  | .ifE c t e, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | ifE hcc hct hce =>
          simp only [Expr.eval]
          rw [sealed_eval_congr hΓ hE hO agree c ρ facts safe.1 hcc,
            sealed_eval_congr hΓ hE hO agree t ρ facts safe.2.1 hct,
            sealed_eval_congr hΓ hE hO agree e ρ facts safe.2.2 hce]
  | .empty, _, _, _, _ => rfl
  | .caseE key pats bodies, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | caseE hck hcbs =>
          simp only [Expr.eval]
          rw [sealed_eval_congr hΓ hE hO agree key ρ facts safe.1 hck]
          exact Multiset.bind_congr fun w _ =>
            sealed_evalArms_congr hΓ hE hO agree w pats bodies ρ facts (exprSafeAll_mem safe.2) hcbs
  | .matchE src p t, ρ, facts, safe, hc => by
      rw [ExprSafe] at safe
      cases hc with
      | matchE hcs hct =>
          simp only [Expr.eval]
          rw [sealed_eval_congr hΓ hE hO agree src ρ facts safe.1 hcs]
          refine Multiset.bind_congr fun sp _ => Multiset.bind_congr fun row _ => ?_
          split
          · next ρ' hm =>
              exact sealed_eval_congr hΓ hE hO agree t ρ'
                (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) safe.2 hct
          · rfl

/-- The list version. -/
theorem sealed_evalAll_congr (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O O' : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O)
    (agree : SOracleAgree (Γ := Γ) (funs := funs) (grounded := grounded) ent As O O') :
    ∀ (args : List Expr) (ρ : List (String × Atom)), SMeetsFacts Γ funs grounded Φ ρ →
      List.Forall (fun e => ExprSafe funs e → CallsOK Γ res ent Φ R As e → e.eval E O ρ = e.eval E O' ρ)
        args
  | [], _, _ => trivial
  | e :: es, ρ, facts => (List.forall_cons _ e es).mpr
      ⟨sealed_eval_congr hΓ hE hO agree e ρ facts, sealed_evalAll_congr hΓ hE hO agree es ρ facts⟩

/-- The arms of a `case`. -/
theorem sealed_evalArms_congr (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O O' : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O)
    (agree : SOracleAgree (Γ := Γ) (funs := funs) (grounded := grounded) ent As O O') (w : Atom) :
    ∀ (pats : List Pat) (bodies : List Expr) (ρ : List (String × Atom)),
      SMeetsFacts Γ funs grounded Φ ρ → (∀ b ∈ bodies, ExprSafe funs b) →
      (∀ b ∈ bodies, CallsOK Γ res ent Φ R As b) →
      Expr.evalArms E O ρ w pats bodies = Expr.evalArms E O' ρ w pats bodies
  | p :: ps, b :: bs, ρ, facts, safe, hcbs => by
      simp only [Expr.evalArms]
      split
      · next ρ' hm =>
          exact sealed_eval_congr hΓ hE hO agree b ρ'
            (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) (safe b (by simp)) (hcbs b (by simp))
      · exact sealed_evalArms_congr hΓ hE hO agree w ps bs ρ facts (fun b' hb' => safe b' (by simp [hb']))
          fun b' hb' => hcbs b' (by simp [hb'])
  | [], _, _, _, _, _ => by simp [Expr.evalArms]
  | _ :: _, [], _, _, _, _ => by simp [Expr.evalArms]
end

/-- **An accepted relation meets the version hypotheses in the profile**, when its
analysis types data through constructors only. -/
theorem sealed_accepted_versionHyps (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation}
    (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f)) :
    SVersionHyps (Γ := Γ) (funs := funs) (grounded := grounded) (fun o => equationsBody E eqs ⟨o, enP⟩)
      (fun o => equationsBody E eqs ⟨o, enV⟩) Cs R where
  resultGuarded := rg
  calls o o' agree oracle vs hvs := by
    unfold equationsBody
    refine Multiset.bind_congr fun eq heq => ?_
    split
    · next ρ hm =>
        exact sealed_eval_congr hΓ hE
          ⟨fun ws hws => oracle ws ((sentryPoly_lift_iff Cs ws).mp hws),
            fun f ws hws r hr => enRes f ws hws r (enAgree f ws hws ▸ hr)⟩
          ⟨fun ws hws => agree ws ((sentryPoly_lift_iff Cs ws).mp hws), enAgree⟩ eq.rhs ρ
          (sealed_eqFacts_sound hΓ (acc eq heq).linear (safe eq heq).2 hm hvs) (safe eq heq).1
          (acc eq heq).calls
    · rfl
  results o oracle vs hvs r hr := by
    unfold equationsBody at hr
    obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
    split at hr
    · next ρ hm =>
        exact sealed_eval_sound hΓ hE ⟨fun ws hws => oracle ws ((sentryPoly_lift_iff Cs ws).mp hws), enRes⟩
          eq.rhs ρ (sealed_eqFacts_sound hΓ (acc eq heq).linear (safe eq heq).2 hm hvs) (safe eq heq).1 R
          (acc eq heq).result (acc eq heq).calls r hr
    · exact absurd hr (Multiset.notMem_zero r)

/-- **The version of an accepted relation is the profile's protocol**, at every fuel,
on arguments meeting the entry facts. -/
theorem sealed_accepted_version_eq_protocol (hΓ : Functional Γ) {Cs : List (Ty Empty)}
    {eqs : List Equation} (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : SEntryFacts Γ funs grounded Cs vs) :
    sealedProtocolRun Γ funs grounded (fun o => equationsBody E eqs ⟨o, enP⟩)
        (arrow (Cs.map Ty.lift) R.lift) n vs =
      versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs :=
  sversion_eq_protocol (sealed_accepted_versionHyps hΓ rg acc safe hE enP enV enAgree enRes) n vs hvs

/-- **A checked call of an accepted relation has the profile's protocol's answers
through the version**, for every argument list: the guard-skipping fast path is sound
in the profile. -/
theorem sealed_accepted_checked_call_eq (hΓ : Functional Γ) {Cs : List (Ty Empty)}
    {eqs : List Equation} (rg : ResultGuarded R.lift) (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enP enV : String → List Atom → Multiset Atom)
    (enAgree : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → enP f ws = enV f ws)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) :
    chainCallI (sealedInfo Γ funs) (metatype grounded)
        (equationsBody E eqs ⟨sealedProtocolRun Γ funs grounded (fun o => equationsBody E eqs ⟨o, enP⟩)
          (arrow (Cs.map Ty.lift) R.lift) n, enP⟩)
        (arrow (Cs.map Ty.lift) R.lift) vs =
      chainCallI (sealedInfo Γ funs) (metatype grounded)
        (equationsBody E eqs ⟨versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n, enV⟩)
        (arrow (Cs.map Ty.lift) R.lift) vs :=
  schecked_call_eq hΓ (sealed_accepted_versionHyps hΓ rg acc safe hE enP enV enAgree enRes) n vs

end SealedProtocol

/-! ## Refutation by the computation judgment -/

section Shapes

/-- The head path of a closed type: a symbol, or an application by its length and
the head path of its first element. -/
inductive Shape where
  | leaf (s : String)
  | nil
  | node (n : ℕ) (head : Shape)
  deriving DecidableEq

/-- The head path of a closed type. -/
def shapeOf : Ty Empty → Shape
  | .var v => v.elim
  | .sym s => .leaf s
  | .app [] => .nil
  | .app (h :: ts) => .node (ts.length + 1) (shapeOf h)

/-- A type whose head path has no variable: all its instances share their head path. -/
def Rigid {V : Type} : Ty V → Prop
  | .var _ => False
  | .sym _ => True
  | .app [] => True
  | .app (h :: _) => Rigid h

theorem shapeOf_bind {V : Type} : ∀ (t : Ty V), Rigid t → ∀ σ σ' : V → Ty Empty,
    shapeOf (t.bind σ) = shapeOf (t.bind σ')
  | .var _, h, _, _ => h.elim
  | .sym _, _, _, _ => by simp [shapeOf]
  | .app [], _, _, _ => by simp [Ty.bind_app, shapeOf]
  | .app (h :: ts), hr, σ, σ' => by
      simp only [Ty.bind_app, List.map_cons, shapeOf, List.length_map]
      rw [shapeOf_bind h hr σ σ']

theorem rigid_map {V W : Type} (g : V → W) : ∀ t : Ty V, Rigid t → Rigid (t.map g)
  | .var _, h => h.elim
  | .sym _, _ => by simp [Ty.map, Rigid]
  | .app [], _ => by simp [Ty.map, Ty.bind_app, Rigid]
  | .app (h :: ts), hr => by
      have := rigid_map g h hr
      simpa [Ty.map, Ty.bind_app, Rigid] using this

/-- **A derivation with a rigid type meets requests of one head path only.** -/
theorem meets_shape {d : Deriv} (hr : Rigid d.ty) {A B : Ty Empty} (hA : Meets d A) (hB : Meets d B) :
    shapeOf A = shapeOf B := by
  obtain ⟨σ, -, hσ⟩ := meets_iff.mp hA
  obtain ⟨σ', -, hσ'⟩ := meets_iff.mp hB
  rw [← hσ, ← hσ']
  exact shapeOf_bind d.ty hr σ σ'

/-- A row rigid in head, as a symbol's own type and, for an arrow, in its range. -/
def RigidRow (ρ : Ty String) : Prop := Rigid ρ ∧ ∀ As R, arrowSplit ρ = some (As, R) → Rigid R

/-- **Every row is rigid in head**: no row is a type variable or applies one at its head. -/
def RigidSig (Γ : Decls) : Prop := ∀ s, ∀ ρ ∈ Γ s, RigidRow ρ

/-- **Every row is rigid in head, a function's range aside**: each row is rigid as its
symbol's own type, and an arrow row's range is rigid unless the symbol is a function,
whose range types no value of the profile (`termRows` keeps no row of a function). This
is the condition the implementation checks. -/
def SealedRigidSig (Γ : Decls) (funs : String → Prop) : Prop :=
  ∀ s, ∀ ρ ∈ Γ s, Rigid ρ ∧ (¬ funs s → ∀ As R, arrowSplit ρ = some (As, R) → Rigid R)

/-- Rigid rows are rigid under every set of functions. -/
theorem RigidSig.sealed {Γ : Decls} (rig : RigidSig Γ) (funs : String → Prop) :
    SealedRigidSig Γ funs :=
  fun s ρ hρ => ⟨(rig s ρ hρ).1, fun _ => (rig s ρ hρ).2⟩

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

mutual
/-- **Every derivation of a ground value is rigid in head** in the profile's relation,
when every row is. -/
theorem sealed_rigid (rig : SealedRigidSig Γ funs) :
    ∀ v : Atom, Ground v → ∀ d ∈ eff (sealedInfo Γ funs v), Rigid d.ty
  | .var _, hg, _, _ => hg.elim
  | .symbol s, _, d, hd => by
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := sealed_mem_symbol_cands hc
        exact rigid_map _ ρ (rig s ρ hρ).1
      · simp [undefinedDeriv, undefinedTy, Rigid]
  | .grounded g, _, d, hd => by
      rw [sealedInfo_grounded] at hd
      rcases grounded_ty hd with rfl | ⟨c, -, rfl⟩
      · simp [undefinedDeriv, undefinedTy, Rigid]
      · simp [classDeriv, Rigid]
  | .expression [], _, d, hd => by
      rcases mem_eff hd with hc | rfl
      · rw [sealedInfo_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp [Rigid]
      · simp [undefinedDeriv, undefinedTy, Rigid]
  | .expression (x :: xs), hg, d, hd => by
      rcases mem_eff hd with hc | rfl
      · rcases sealed_mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hs, -, E, -, rfl⟩ := mem_funTrees hf
          rw [sealed_rows] at hρ
          match x, hρ with
          | .symbol s, hρ =>
              simp only at hρ
              unfold termRows at hρ
              split_ifs at hρ with hf
              · simp at hρ
              · exact rigid_map _ R ((rig s ρ hρ).2 hf As R hs)
        · obtain ⟨dh, hdh, p, -, rfl⟩ := mem_tupleTrees_cons ht
          have := sealed_rigid rig x hg.1 dh hdh
          simpa [Rigid, Deriv.push] using rigid_map _ dh.ty this
      · simp [undefinedDeriv, undefinedTy, Rigid]
end

end Shapes

section Refutation

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs] (grounded : String → Bool)

/-- **The guard at a closed type over a bag of answers**, in the profile's relation:
each answer continues once per way it passes. -/
noncomputable def sealedCheck (T : Ty Empty) (m : Multiset Atom) : Multiset Atom :=
  m.bind fun r => TypedCalls.guardCount (sealedInfo Γ funs r) T (metatype grounded r) • {r}

/-- **A declared result refutes a request** when no ground value of the result passes
the guard at the request. -/
def RefutesGround (R T : Ty Empty) : Prop :=
  ∀ v, Ground v → SHolds Γ funs grounded v R →
    TypedCalls.guardCount (sealedInfo Γ funs v) T (metatype grounded v) = 0

variable {Γ funs grounded}

/-- **Refuting by shape**: under functional declarations rigid in head, a result and
a request that are no metatype names and differ in head path share no ground value. -/
theorem refutesGround_of_shape (hΓ : Functional Γ) (rig : SealedRigidSig Γ funs) {R T : Ty Empty}
    (hR : ¬ MetaName R) (hT : ¬ MetaName T) (shape : shapeOf R ≠ shapeOf T) :
    RefutesGround Γ funs grounded R T := by
  classical
  intro v hg hv
  have hc := hv.count hR
  rw [guardCount_of_ne (sealedInfo Γ funs v) T (metatype grounded v)
      fun same => hT (same ▸ metaName_metatype grounded v),
    sealed_count_eq_ite hΓ v T]
  rw [sealed_count_eq_ite hΓ v R] at hc
  split_ifs at hc with hR'
  split_ifs with hT'
  · exact absurd (meets_shape (sealed_rigid (funs := funs) rig v hg _
      (by rw [sealed_eff_deriv hΓ v]; exact Multiset.mem_singleton_self _)) hR' hT') shape
  · rfl

/-- **Rejecting is exact**: on answers that each meet the declared result and are
ground, checking at a refuted request leaves no answer, multiplicities included. -/
theorem refute_exact {R T : Ty Empty} (refutes : RefutesGround Γ funs grounded R T) {m : Multiset Atom}
    (contract : ∀ r ∈ m, SHolds Γ funs grounded r R) (ground : ∀ r ∈ m, Ground r) :
    sealedCheck Γ funs grounded T m = 0 := by
  unfold sealedCheck
  have none : ∀ r ∈ m,
      (TypedCalls.guardCount (sealedInfo Γ funs r) T (metatype grounded r) • {r} : Multiset Atom) =
        (fun _ => (0 : Multiset Atom)) r := fun r hr => by
    rw [refutes r (ground r hr) (contract r hr), zero_nsmul]
  rw [Multiset.bind_congr none]
  simp

/-- **A checked call is refuted by its own declared result**: every answer passed its
result guard, so a refuted request leaves none of its ground answers. -/
theorem refute_checked_call (hΓ : Functional Γ) {R T : Ty Empty}
    (refutes : RefutesGround Γ funs grounded R T) (rg : ResultGuarded R.lift)
    (body : List Atom → Multiset Atom) (Cs : List (Ty Empty)) (vs : List Atom)
    (ground : ∀ r ∈ chainCallI (sealedInfo Γ funs) (metatype grounded) body
      (arrow (Cs.map Ty.lift) R.lift) vs, Ground r) :
    sealedCheck Γ funs grounded T
      (chainCallI (sealedInfo Γ funs) (metatype grounded) body (arrow (Cs.map Ty.lift) R.lift) vs) = 0 := by
  refine refute_exact refutes (fun r hr => ?_) ground
  rw [chainCall_closedI] at hr
  simp only [if_pos rg] at hr
  obtain ⟨-, hr⟩ := Multiset.mem_nsmul.mp hr
  obtain ⟨r', -, hr⟩ := Multiset.mem_bind.mp hr
  obtain ⟨hne, hr⟩ := Multiset.mem_nsmul.mp hr
  rw [Multiset.mem_singleton] at hr
  subst hr
  exact SHolds.of_guardCount hΓ hne

variable {res : String → Ty Empty} {ent : String → List (Ty Empty)} {E : Env}

/-- **Refuting a call through its version**: the version proves its declared result
(`SealedSorts.sealed_version_results`), so on ground answers a refuted request
leaves none. -/
theorem refute_version (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation}
    {R T : Ty Empty} (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (refutes : RefutesGround Γ funs grounded R T) (n : ℕ) (vs : List Atom)
    (hvs : SEntryFacts Γ funs grounded Cs vs)
    (ground : ∀ r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs, Ground r) :
    sealedCheck Γ funs grounded T (versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs) = 0 :=
  refute_exact refutes (fun r hr => sealed_version_results hΓ acc safe hE enV enRes n vs hvs r hr) ground

end Refutation

/-! ## The two judgments -/

section TwoJudgments

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs]

/-- **The computation judgment** of a call `(f args)`: through `f`'s declared rows,
its arguments typed by the value judgment; what running the call returns, per its
declaration. -/
noncomputable def compInfo (f : String) (args : List Atom) : Multiset Deriv :=
  funTrees (info Γ (.symbol f)) (args.map (sealedInfo Γ funs))

/-- Running the call may return a value of `T`, per its declaration. -/
def CompTypable (f : String) (args : List Atom) (T : Ty Empty) : Prop :=
  ∃ d ∈ compInfo Γ funs f args, Meets d T

variable {Γ funs}

open Classical in
/-- The derivations through one closed row, the fields contributing one derivation each. -/
theorem funTrees_of_row {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (js : List Info) (ds : List Deriv)
    (hjs : List.Forall₂ (fun j d => eff j = {d}) js ds) (len : js.length = As.length) :
    funTrees (info Γ (.symbol C)) js =
      (({(⟨R.map DVar.own, ctorEqs 1 As ds⟩ : Deriv)} : Multiset Deriv)).filter fun d => Sat d.eqs := by
  have args : argEqs 1 As js = {ctorEqs 1 As ds} := argEqs_singletons 1 As _ _ (by simp [len]) hjs
  unfold funTrees
  rw [info_symbol, row]
  simp only [Multiset.coe_singleton, Multiset.singleton_bind, arrowSplit_arrow, len, if_true, args,
    Multiset.map_singleton]

/-- **The computation judgment reads the declaration**: running `(f args)` returns a
value of `T` exactly when `f`'s row, the arguments' value derivations and `T` have a
common solution. -/
theorem compTypable_iff_row (hΓ : Functional Γ) {f : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ f = [arrow As R]) (args : List Atom) (len : args.length = As.length) (T : Ty Empty) :
    CompTypable Γ funs f args T ↔
      Sat (ctorEqs 1 As (args.map (sealedDeriv (funs := funs) hΓ)) ++ [(R.map DVar.own, T.lift)]) := by
  classical
  unfold CompTypable compInfo
  rw [funTrees_of_row row _ _ (sealed_forall₂_deriv hΓ args) (by simp [len])]
  constructor
  · rintro ⟨d, hd, hm⟩
    obtain ⟨hd, -⟩ := Multiset.mem_filter.mp hd
    rw [Multiset.mem_singleton] at hd
    subst hd
    exact hm
  · intro h
    exact ⟨_, Multiset.mem_filter.mpr ⟨Multiset.mem_singleton_self _, h.left⟩, h⟩

/-- **For data the two judgments agree**: an application of a constructor is typed by
the value judgment through the same rows the computation judgment reads, or by its
tuple type where they give nothing. -/
theorem value_eq_comp_of_ctor {f : String} (hc : ¬ funs f) (args : List Atom) :
    (sealedInfo Γ funs (.expression (.symbol f :: args))).cands =
      if Multiset.card (compInfo Γ funs f args) = 0 then
        tupleTrees (info Γ (.symbol f) :: args.map (sealedInfo Γ funs))
      else compInfo Γ funs f args := by
  rw [sealedInfo_ctor hc]
  rfl

/-- **For a call the value judgment ignores the computation judgment**: a held
application of a function is typed by its tuple type alone. -/
theorem value_ignores_comp {f : String} (hf : funs f) (args : List Atom) :
    (sealedInfo Γ funs (.expression (.symbol f :: args))).cands =
      tupleTrees (sealedInfo Γ funs (.symbol f) :: args.map (sealedInfo Γ funs)) := by
  rw [sealedInfo_expression, List.map_cons]
  have none : funTrees (sealedInfo Γ funs (.symbol f)) (args.map (sealedInfo Γ funs)) = 0 := by
    unfold funTrees
    rw [sealedInfo_symbol]
    simp [termRows, hf]
  simp only [nodeInfo, none, Multiset.card_zero, if_true]

/-- **A held call is never certified at a sealed list sort**, whatever its declared
result: the certification side reads the value judgment only. -/
theorem held_call_not_certified (h : SealedListClosed Γ funs) (hΓ : Functional Γ) {f : String}
    (hf : funs f) {args : List Atom} (hg : Ground (.expression (.symbol f :: args))) (τ : Ty Empty) :
    count (sealedInfo Γ funs (.expression (.symbol f :: args))) (listOf τ) = 0 := by
  have le := sealed_count_le_one (funs := funs) hΓ (.expression (.symbol f :: args)) (listOf τ)
  by_contra hne
  have spine := sealedLicensed_of_closed h τ _ hg (by omega)
  rcases spine.head with same | ⟨x, r, same⟩
  · cases same
  · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact h.cons_not_fun (same.1 ▸ hf)

/-- **A held call is never certified at a sealed Peano sort.** -/
theorem held_call_not_certified_nat (h : SealedNatClosed Γ funs) (hΓ : Functional Γ) {f : String}
    (hf : funs f) {args : List Atom} (hg : Ground (.expression (.symbol f :: args))) :
    count (sealedInfo Γ funs (.expression (.symbol f :: args))) (.sym "Nat") = 0 := by
  have le := sealed_count_le_one (funs := funs) hΓ (.expression (.symbol f :: args)) (.sym "Nat")
  by_contra hne
  have spine := sealed_nat_spine_of_count h _ hg (by omega)
  rcases spine.head with same | ⟨n, same⟩
  · cases same
  · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact h.succ_not_fun (same.1 ▸ hf)

theorem sealedDeriv_eq_theDeriv (hΓ : Functional Γ) {v : Atom} (h : NoHeldCalls funs v) :
    sealedDeriv (funs := funs) hΓ v = theDeriv hΓ v := by
  have := sealed_eff_deriv (funs := funs) hΓ v
  rw [eff_eq_of_cands (sealed_cands_eq Γ funs v h), eff_theDeriv hΓ v] at this
  exact (Multiset.singleton_inj.mp this).symm

end TwoJudgments

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (sym num app listNumber)
open CertifiedSpines.Controls (listNum count_int count_nil_of)
open TypedFoldBound.Controls (listTDecls listTFuns heldBuild listTDecls_functional numRow eqRow buildRow sumRow)
open SealedSorts.Controls (sealed_listT_closed consOne cons_typed_both buildDecls buildFuns buildDecls_functional
  buildEqs build_accepted build_safe senv_ok build_closed buildBody)

/-- **e02 under the two judgments**: running `(build 1 Nil)` returns a `(List Number)`
per `build`'s declaration, and the held call is no `(List Number)`. -/
theorem held_build_two_judgments :
    CompTypable listTDecls listTFuns "build" [num 1, sym "Nil"] listNum ∧
      count (sealedInfo listTDecls listTFuns heldBuild) listNum = 0 := by
  refine ⟨?_, held_call_not_certified sealed_listT_closed listTDecls_functional (by simp [listTFuns])
    (by simp [Ground, GroundAll]) _⟩
  rw [compTypable_iff_row listTDecls_functional (As := [.sym "Number", listOf (.sym "Number")])
    (R := listOf (.sym "Number")) (by simp [listTDecls, buildRow]) [num 1, sym "Nil"] rfl listNum]
  have same : [num 1, sym "Nil"].map (sealedDeriv (funs := listTFuns) listTDecls_functional) =
      [num 1, sym "Nil"].map (theDeriv listTDecls_functional) := by
    simp only [List.map_cons, List.map_nil]
    rw [sealedDeriv_eq_theDeriv listTDecls_functional (by simp [NoHeldCalls]),
      sealedDeriv_eq_theDeriv listTDecls_functional (by simp [NoHeldCalls])]
  rw [same]
  have := count_ctor listTDecls_functional (C := "build") (As := [.sym "Number", listOf (.sym "Number")])
    (R := listOf (.sym "Number")) (by simp [listTDecls, buildRow]) [num 1, sym "Nil"] rfl
    listNum (by simp [Named, listNum, listOf])
  rw [show info listTDecls (.expression (.symbol "build" :: [num 1, sym "Nil"])) =
      info listTDecls heldBuild from rfl, TypedFoldBound.Controls.held_build_certified.1] at this
  split_ifs at this with hsat
  exact hsat

theorem rigidRow_arrow (As : List (Ty String)) (R : Ty String) (hR : Rigid R) : RigidRow (arrow As R) :=
  ⟨by simp [arrow, Rigid], fun As' R' h => by
    rw [arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hR⟩

theorem rigidRow_list (a : Ty String) : RigidRow (listOf a) :=
  ⟨by simp [listOf, Rigid], fun As R h => by simp [listOf, arrowSplit] at h⟩

theorem listT_rigid : RigidSig listTDecls := by
  intro s ρ hρ
  unfold listTDecls at hρ
  split_ifs at hρ <;> simp only [List.mem_singleton, List.not_mem_nil] at hρ <;> subst hρ <;>
    simp [RigidRow, Rigid, listOf, consRow, buildRow, sumRow, numRow, eqRow, arrow, arrowSplit]

/-- **Refuting by shape, positive**: no ground `(List Number)` passes the guard at `Nat`,
so a call declared to return `(List Number)` is rejected at `Nat` before it runs. -/
theorem list_refutes_nat (grounded : String → Bool) :
    RefutesGround listTDecls listTFuns grounded listNum (.sym "Nat") :=
  refutesGround_of_shape listTDecls_functional (listT_rigid.sealed _) (by simp [MetaName, listNum, listOf])
    (by simp [MetaName]) (by simp [shapeOf, listNum, listOf])

/-- **Two closed types that do not unify may share a value**: `Nil` passes both
`(List Number)` and `(List String)`, whose head paths agree, so a call declared to
return `(List Number)`, such as `(build 0 Nil)`, must run at `(List String)`. -/
theorem nil_in_both_lists (grounded : String → Bool) :
    listNum ≠ listOf (.sym "String") ∧ shapeOf listNum = shapeOf (listOf (.sym "String")) ∧
      Ground (sym "Nil") ∧ SHolds listTDecls listTFuns grounded (sym "Nil") listNum ∧
      TypedCalls.guardCount (sealedInfo listTDecls listTFuns (sym "Nil")) (listOf (.sym "String"))
        (metatype grounded (sym "Nil")) = 1 ∧
      ¬ RefutesGround listTDecls listTFuns grounded listNum (listOf (.sym "String")) := by
  have nilAt : ∀ τ : Ty Empty, count (sealedInfo listTDecls listTFuns (sym "Nil")) (listOf τ) = 1 := fun τ => by
    rw [sealed_count_eq listTDecls listTFuns (sym "Nil") trivial]
    exact count_nil_of listTDecls_functional (by simp [listTDecls]) τ
  have passes : TypedCalls.guardCount (sealedInfo listTDecls listTFuns (sym "Nil")) (listOf (.sym "String"))
      (metatype grounded (sym "Nil")) = 1 := by
    rw [guardCount_of_ne (sealedInfo listTDecls listTFuns (sym "Nil")) (listOf (.sym "String"))
      (metatype grounded (sym "Nil")) (by simp [listOf]), nilAt]
  have holds : SHolds listTDecls listTFuns grounded (sym "Nil") listNum := SHolds.of_count (nilAt _)
  refine ⟨by simp [listNum, listOf], by simp [shapeOf, listNum, listOf], trivial, holds, passes,
    fun refutes => ?_⟩
  have := refutes (sym "Nil") trivial holds
  rw [passes] at this
  exact absurd this (by decide)

/-- **A metatype request accepts by the value's metatype**: `(Cons 1 Nil)`, a
`(List Number)`, passes `Expression`, so a metatype request refutes nothing. -/
theorem cell_passes_expression (grounded : String → Bool) :
    SHolds listTDecls listTFuns grounded consOne listNum ∧
      TypedCalls.guardCount (sealedInfo listTDecls listTFuns consOne) (.sym "Expression")
        (metatype grounded consOne) = 1 ∧
      ¬ RefutesGround listTDecls listTFuns grounded listNum (.sym "Expression") := by
  have holds : SHolds listTDecls listTFuns grounded consOne listNum := SHolds.of_count cons_typed_both.2
  have zero : count (sealedInfo listTDecls listTFuns consOne) (.sym "Expression") = 0 := by
    have := sealed_count_le_one (funs := listTFuns) listTDecls_functional consOne (.sym "Expression")
    by_contra hne
    have one : count (sealedInfo listTDecls listTFuns consOne) (.sym "Expression") = 1 := by omega
    have both := refutesGround_of_shape (funs := listTFuns) (grounded := grounded) listTDecls_functional
      (listT_rigid.sealed _) (R := listNum) (T := .sym "Nat") (by simp [MetaName, listNum, listOf]) (by simp [MetaName])
      (by simp [shapeOf, listNum, listOf])
    have hR : Meets (sealedDeriv (funs := listTFuns) listTDecls_functional consOne) listNum := by
      have := cons_typed_both.2
      rw [sealed_count_eq_ite listTDecls_functional] at this
      split_ifs at this with h
      exact h
    have hT : Meets (sealedDeriv (funs := listTFuns) listTDecls_functional consOne) (.sym "Expression") := by
      rw [sealed_count_eq_ite listTDecls_functional] at one
      split_ifs at one with h
      exact h
    have rig := sealed_rigid (funs := listTFuns) (listT_rigid.sealed _) consOne
      (by simp [consOne, app, sym, num, Ground, GroundAll]) _
      (by rw [sealed_eff_deriv listTDecls_functional consOne]; exact Multiset.mem_singleton_self _)
    have := meets_shape rig hR hT
    simp [shapeOf, listNum, listOf] at this
  have passes : TypedCalls.guardCount (sealedInfo listTDecls listTFuns consOne) (.sym "Expression")
      (metatype grounded consOne) = 1 := by
    unfold TypedCalls.guardCount
    rw [if_pos zero]
    simp [consOne, app, metatype]
  refine ⟨holds, passes, fun refutes => ?_⟩
  have := refutes consOne (by simp [consOne, app, sym, num, Ground, GroundAll]) holds
  rw [passes] at this
  exact absurd this (by decide)

/-- **A variable passes every guard**, so refuting needs ground answers: `$x` meets
`(List Number)` and passes `Nat`. -/
theorem variable_passes_all (grounded : String → Bool) :
    SHolds listTDecls listTFuns grounded (.var "x") listNum ∧
      TypedCalls.guardCount (sealedInfo listTDecls listTFuns (.var "x")) (.sym "Nat")
        (metatype grounded (.var "x")) = 1 ∧ ¬ Ground (.var "x") := by
  refine ⟨SHolds.of_count ?_, ?_, fun h => h⟩
  · rw [sealedInfo_var]
    exact count_var _ _ _
  · rw [guardCount_of_ne (sealedInfo listTDecls listTFuns (.var "x")) (.sym "Nat")
      (metatype grounded (.var "x")) (by simp [metatype]), sealedInfo_var]
    exact count_var _ _ _

theorem decls_rigid : RigidSig TypedCalls.Controls.decls := by
  intro s ρ hρ
  unfold TypedCalls.Controls.decls at hρ
  split_ifs at hρ <;> simp only [List.mem_singleton, List.not_mem_nil] at hρ
  all_goals subst hρ
  all_goals first
    | exact rigidRow_arrow _ _ (by simp [Rigid, listOf])
    | exact rigidRow_list _

theorem buildDecls_rigid : RigidSig buildDecls := by
  intro s ρ hρ
  by_cases hb : s = "build"
  · subst hb
    simp only [buildDecls, if_true, List.mem_singleton] at hρ
    subst hρ
    exact rigidRow_arrow _ _ (by simp [Rigid, listOf])
  · simp only [buildDecls, if_neg hb] at hρ
    exact decls_rigid s ρ hρ

/-- **`build` refuted at `Nat`, before it runs**: on arguments meeting its entry facts,
checking its ground answers at `Nat` leaves none, so rejecting the call there has the
answers of running it. -/
theorem build_refuted_at_nat (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : SEntryFacts buildDecls buildFuns grounded [.sym "Number", listNum] vs)
    (ground : ∀ r ∈ versionRun buildBody n vs, Ground r) :
    sealedCheck buildDecls buildFuns grounded (.sym "Nat") (versionRun buildBody n vs) = 0 :=
  refute_version (res := TypedCalls.Controls.noRes) (ent := TypedCalls.Controls.noEnt)
    buildDecls_functional (build_accepted _ _) build_safe (senv_ok grounded _) TypedCalls.Controls.noCallee
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))
    (refutesGround_of_shape buildDecls_functional (buildDecls_rigid.sealed _) (by simp [MetaName, listNum, listOf])
      (by simp [MetaName]) (by simp [shapeOf, listNum, listOf])) n vs hvs ground

/-- `(: idt (-> $t $t))` beside `build`'s declarations: a polymorphic function. -/
def idtDecls : Decls := fun s => if s = "idt" then [arrow [.var "t"] (.var "t")] else buildDecls s

/-- `build` and `idt` have equations. -/
def idtFuns (s : String) : Prop := s = "build" ∨ s = "idt"

instance : DecidablePred idtFuns := fun s => by unfold idtFuns; infer_instance

theorem idtDecls_functional : Functional idtDecls := by
  intro s
  unfold idtDecls
  split_ifs
  · simp
  · exact buildDecls_functional s

/-- **A function's range need not be rigid** (positive): `idt`'s range `$t` is no
rigid type, so the declarations are not `RigidSig`; they are `SealedRigidSig`, since
a function's range types no value of the profile, and a `(List Number)` call is still
refuted at `Nat`. -/
theorem idt_exempt (grounded : String → Bool) :
    ¬ RigidSig idtDecls ∧ SealedRigidSig idtDecls idtFuns ∧
      RefutesGround idtDecls idtFuns grounded listNum (.sym "Nat") := by
  have sealedRig : SealedRigidSig idtDecls idtFuns := by
    intro s ρ hρ
    by_cases hs : s = "idt"
    · subst hs
      simp only [idtDecls, if_true, List.mem_singleton] at hρ
      subst hρ
      exact ⟨by simp [arrow, Rigid], fun hf => absurd (Or.inr rfl) hf⟩
    · simp only [idtDecls, if_neg hs] at hρ
      exact (buildDecls_rigid.sealed idtFuns) s ρ hρ
  refine ⟨fun rig => ?_, sealedRig, refutesGround_of_shape idtDecls_functional sealedRig
    (by simp [MetaName, listNum, listOf]) (by simp [MetaName]) (by simp [shapeOf, listNum, listOf])⟩
  have := (rig "idt" (arrow [.var "t"] (.var "t")) (by simp [idtDecls])).2 [.var "t"] (.var "t")
    (arrowSplit_arrow _ _)
  simp [Rigid] at this

/-- `(: c $t)` beside the list declarations: a constant, no function, declared at a
type variable. -/
def polyDecls : Decls := fun s => if s = "c" then [.var "t"] else listTDecls s

theorem polyDecls_functional : Functional polyDecls := by
  intro s
  unfold polyDecls
  split_ifs
  · simp
  · exact listTDecls_functional s

theorem count_poly_constant (T : Ty Empty) : count (info polyDecls (sym "c")) T = 1 := by
  classical
  rw [count_eq_ite polyDecls_functional, if_pos]
  have : theDeriv polyDecls_functional (sym "c") = ⟨(Ty.var "t").map DVar.own, []⟩ := by
    have h' := eff_theDeriv polyDecls_functional (sym "c")
    rw [info_symbol] at h'
    unfold eff at h'
    simpa [polyDecls] using h'.symm
  rw [this]
  exact meets_iff.mpr ⟨fun _ => T, by simp, by simp [Ty.map]⟩

/-- **The exemption is a function's alone** (negative): `c` is no function and is
declared at `$t`, so the declarations are not `SealedRigidSig`, and refuting by shape
fails there: the ground `c` holds at `(List Number)` and passes the guard at `Nat`. -/
theorem poly_constant_breaks (grounded : String → Bool) :
    ¬ SealedRigidSig polyDecls listTFuns ∧
      ¬ RefutesGround polyDecls listTFuns grounded listNum (.sym "Nat") := by
  have at_ : ∀ T : Ty Empty, count (sealedInfo polyDecls listTFuns (sym "c")) T = 1 := fun T => by
    rw [sealed_count_eq polyDecls listTFuns (sym "c") trivial]
    exact count_poly_constant T
  refine ⟨fun rig => by simpa [Rigid] using (rig "c" (.var "t") (by simp [polyDecls])).1,
    fun refutes => ?_⟩
  have := refutes (sym "c") trivial (SHolds.of_count (at_ listNum))
  rw [guardCount_of_ne (sealedInfo polyDecls listTFuns (sym "c")) (.sym "Nat")
    (metatype grounded (sym "c")) (by simp [metatype]; split_ifs <;> decide), at_] at this
  exact absurd this (by decide)

theorem listNum_guarded : ResultGuarded (listNum.lift : Ty String) := by
  simp [ResultGuarded, listNum, listOf, Ty.lift, Ty.map, Unchecked]

/-- **`build`'s version is its full checked call in the profile** (positive): at every
fuel, on arguments meeting its entry facts there. -/
theorem build_version_is_protocol (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : SEntryFacts buildDecls buildFuns grounded [.sym "Number", listNum] vs) :
    sealedProtocolRun buildDecls buildFuns grounded buildBody
        (arrow ([.sym "Number", listNum].map Ty.lift) listNum.lift) n vs =
      versionRun buildBody n vs :=
  sealed_accepted_version_eq_protocol (res := TypedCalls.Controls.noRes) (ent := TypedCalls.Controls.noEnt)
    buildDecls_functional listNum_guarded (build_accepted _ _) build_safe (senv_ok grounded _)
    TypedCalls.Controls.noCallee TypedCalls.Controls.noCallee (fun _ _ _ => rfl)
    (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r)) n vs hvs

/-- `(= (mkb) (build 1 Nil))` written as data built by `build`, a function: the
construction the analysis would accept through `build`'s row. -/
def mkbEqs : List Equation := [⟨[], .ctor "build" [.const (num 1), .const (sym "Nil")]⟩]

abbrev mkbBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody TypedCalls.Controls.env mkbEqs ⟨o, TypedCalls.Controls.noCallee⟩

/-- **The side condition is needed** (negative): data built through a function's row
is accepted by PeTTa's analysis and is no `(List Number)` in the profile, so the
profile's checked call answers nothing where a version that trusted the analysis
would answer the held `(build 1 Nil)`. CeTTa refuses a function head as a
constructor in the profile. -/
theorem function_head_construction_breaks (grounded : String → Bool) :
    Accepted listTDecls TypedCalls.Controls.noRes TypedCalls.Controls.noEnt [] listNum (mkbEqs.head (by simp [mkbEqs])) ∧
      ¬ ExprSafe listTFuns (mkbEqs.head (by simp [mkbEqs])).rhs ∧
      versionRun mkbBody 1 [] = {heldBuild} ∧
      sealedProtocolRun listTDecls listTFuns grounded mkbBody
        (arrow (([] : List (Ty Empty)).map Ty.lift) listNum.lift) 1 [] = 0 := by
  have body : mkbBody (fun _ => 0) [] = {heldBuild} := by
    simp [mkbBody, equationsBody, mkbEqs, Pat.matchAll, Expr.eval, Expr.evalAll, heldBuild, app, sym, num]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [mkbEqs, Pat.varsAll], rfl, .ctor fun e he => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact .const
    · have inst : (buildRow : Ty String) = arrow [.sym "Number", listOf (.sym "Number")] (listOf (.sym "Number")) := rfl
      have hR : ((listOf (Ty.sym "Number") : Ty String).bind fun _ => Ty.sym "Number") = listNum := by
        simp [listOf, listNum]
      rw [← hR]
      refine HasType.ctor (Bs := [.sym "Number", listOf (.sym "Number")]) (σ := fun _ => .sym "Number")
        (by simp [listTDecls, inst]) ?_ rfl ?_ ?_
      · exact TypedCalls.CertifiedSpines.Controls.closed_constructor _ _ (by simp [Named, listOf]) (by simp [listOf])
      · intro q hq _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp [MetaName, listOf]
      · intro q hq _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
          List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact .const (by simpa using count_int listTDecls 1)
        · exact .const (by simpa [listOf] using count_nil_of listTDecls_functional (by simp [listTDecls]) (.sym "Number"))
  · simp [mkbEqs, ExprSafe, listTFuns]
  · exact body
  · simp only [sealedProtocolRun]
    rw [chainCall_closedI]
    simp only [argCountI, one_nsmul, if_pos listNum_guarded]
    rw [body, Multiset.singleton_bind,
      guardCount_of_ne (sealedInfo listTDecls listTFuns heldBuild) listNum (metatype grounded heldBuild)
        (by simp [listNum, listOf]),
      held_build_two_judgments.2, zero_nsmul]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedJudgments
