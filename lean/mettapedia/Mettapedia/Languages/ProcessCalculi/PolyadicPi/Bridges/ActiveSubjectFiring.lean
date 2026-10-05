import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectResidual

/-!
# Exact endpoints of private unary firings through structural equations

The update releases the selected unary guard using an existing ambient datum
and removes the output on the same subject. It follows the actual scope and
parallel equations. When exactly two linear offers have that subject, every
supplied communication exposure has an untouched residual frame. A fresh
scope observation distinct from the ambient datum reconstructs the actual
received name, so the conclusion concerns the supplied endpoint in its
original context, rather than only a renamed observation of that endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectFiring

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier ScopedCommunicationInversion
open ActiveSubjectResidual

local instance {Γ : Ctx sig} : DecidableEq (Var Γ Srt.nm) := decEqVar (S := sig)

/-- A simultaneous selected-subject update on existing process syntax.
Other inputs retain their suspended bodies; only selected unary guards open. -/
def release {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Name Γ → Proc Γ → Proc Γ
  | _, _, _, .var name => .var name
  | _, _, _, .op .nil .nil => nil
  | _, environment, datum, .op .par (.cons first (.cons second .nil)) =>
      par (release fresh subject environment datum first) (release fresh subject environment datum second)
  | _, environment, datum, .op .inp1 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then inst body datum else inp1 channel body
  | _, environment, _, .op .inp2 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then nil else inp2 channel body
  | _, environment, _, .op .out1 (.cons channel (.cons payload .nil)) =>
      if onSubject environment subject channel then nil else out1 channel payload
  | _, environment, _, .op .out2 (.cons channel (.cons first (.cons second .nil))) =>
      if onSubject environment subject channel then nil else out2 channel first second
  | _, environment, datum, .op .nu (.cons body .nil) =>
      nu (release fresh subject (prependRen fresh environment) (weaken datum) body)
  | _, environment, datum, .op .rep (.cons body .nil) => rep (release fresh subject environment datum body)
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem onSubject_rename {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (subject : Var Ω .nm) (channel : Name Γ) :
    onSubject environment subject (rename reindex channel) =
      onSubject (fun sort name => environment sort (reindex sort name)) subject channel := by
  cases channel with
  | var name => rfl
  | op operator _ => cases operator

private theorem extension_comp {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (fresh : Var Ω .nm) :
    (fun sort name => prependRen fresh environment sort (liftRen reindex [.nm] sort name)) =
      prependRen fresh (fun sort name => environment sort (reindex sort name)) := by
  funext sort name
  cases name <;> rfl

theorem release_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω)
      (datum : Name Γ) (process : Proc Γ),
      release fresh subject environment (rename reindex datum) (rename reindex process) =
        rename reindex (release fresh subject (fun sort name => environment sort (reindex sort name)) datum process)
  | _, _, _, _, _, .var _ => by simp only [rename, release]
  | _, _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, release, nil]
  | _, _, reindex, environment, datum, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, release, par]
      rw [release_rename fresh subject reindex environment datum first,
        release_rename fresh subject reindex environment datum second]
  | _, _, reindex, environment, datum, .op .inp1 (.cons channel (.cons body .nil)) => by
      simp only [inp1, rename, renameArgs, liftRen, release]
      rw [onSubject_rename reindex environment subject channel]
      split
      · exact (rename_inst reindex body datum).symm
      · rfl
  | _, _, reindex, environment, _, .op .inp2 (.cons channel (.cons body .nil)) => by
      simp only [inp2, rename, renameArgs, liftRen, release]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, _, .op .out1 (.cons channel (.cons payload .nil)) => by
      simp only [out1, rename, renameArgs, liftRen, release]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      simp only [out2, rename, renameArgs, liftRen, release]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, datum, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, release, nu]
      rw [← rename_weaken reindex datum,
        release_rename fresh subject (liftRen reindex [.nm]) _ (weaken datum) body, extension_comp]
  | _, _, reindex, environment, datum, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, release, rep]
      rw [release_rename fresh subject reindex environment datum body]
termination_by _ _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem inst_variables {Γ : Ctx sig} (body : Proc (.nm :: Γ)) (datum : Var Γ .nm) :
    inst body (.var datum) = rename (nameRen datum) body := by
  unfold inst
  have environments : extend (.var datum) = (fun sort name => Term.var (nameRen datum sort name)) := by
    funext sort name
    cases name <;> rfl
  rw [environments, bind_var_eq_rename]

private theorem structural_inst {Γ : Ctx sig} {first second : Proc (.nm :: Γ)}
    (equal : StructuralEq first second) (datum : Name Γ) :
    StructuralEq (inst first datum) (inst second datum) := by
  cases datum with
  | var name => simp only [inst_variables]; exact equal.rename (nameRen name)
  | op operator _ => cases operator

private theorem swap_environment {Γ Ω : Ctx sig} (fresh : Var Ω .nm) (environment : Ren sig Γ Ω) :
    (fun sort name => prependRen fresh (prependRen fresh environment) sort (swapRen sort name)) =
      prependRen fresh (prependRen fresh environment) := by
  funext sort name
  cases name with
  | zero => rfl
  | succ name => cases name <;> rfl

private theorem double_weaken_swap {Γ : Ctx sig} (datum : Name Γ) :
    rename swapRen (weaken (t := Srt.nm) (weaken (t := Srt.nm) datum)) =
      weaken (t := Srt.nm) (weaken (t := Srt.nm) datum) := by
  cases datum with
  | var name => rfl
  | op operator _ => cases operator

/-- The selected update respects every actual static equation. Opening
an input follows genuine name substitution, including input-body congruence. -/
theorem release_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ (environment : Ren sig Γ Ω) (datum : Name Γ),
      StructuralEq (release fresh subject environment datum first)
        (release fresh subject environment datum second) := by
  induction equal with
  | refl => intro environment datum; exact .refl _
  | symm _ ih => intro environment datum; exact .symm (ih environment datum)
  | trans _ _ firstIH secondIH => intro environment datum; exact .trans (firstIH environment datum) (secondIH environment datum)
  | parComm => intro environment datum; simp only [par, release]; exact .parComm _ _
  | parAssoc => intro environment datum; simp only [par, release]; exact .parAssoc _ _ _
  | parUnit => intro environment datum; simp only [par, nil, release]; exact .parUnit _
  | nuUnused =>
      intro environment datum
      simp only [nu, release, weaken]
      rw [release_rename]
      exact .nuUnused _
  | nuPar =>
      intro environment datum
      simp only [nu, par, release, weaken]
      rw [release_rename]
      exact .nuPar _ _
  | nuSwap =>
      intro environment datum
      simp only [nu, release]
      conv_rhs => rw [← double_weaken_swap datum]
      rw [release_rename, swap_environment]
      exact .nuSwap _
  | repUnfold => intro environment datum; simp only [rep, par, release]; exact .repUnfold _
  | par _ _ firstIH secondIH => intro environment datum; simp only [par, release]; exact .par (firstIH environment datum) (secondIH environment datum)
  | nu _ ih => intro environment datum; simp only [nu, release]; exact .nu (ih _ (weaken datum))
  | inp1 channel equal _ =>
      intro environment datum
      simp only [inp1, release]
      split
      · exact structural_inst equal datum
      · exact .inp1 channel equal
  | inp2 channel equal _ =>
      intro environment datum
      simp only [inp2, release]
      split
      · exact .refl _
      · exact .inp2 channel equal
  | rep _ ih => intro environment datum; simp only [rep, release]; exact .rep (ih environment datum)

theorem release_of_count_zero {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω) (datum : Name Γ) (process : Proc Γ),
      count fresh subject environment process = 0 → release fresh subject environment datum process = process
  | _, _, _, .var _, _ => by simp only [release]
  | _, _, _, .op .nil .nil, _ => by simp only [release, nil]
  | _, environment, datum, .op .par (.cons first (.cons second .nil)), zero => by
      simp only [count, Nat.add_eq_zero_iff] at zero
      simp only [release]
      rw [release_of_count_zero fresh subject environment datum first zero.1,
        release_of_count_zero fresh subject environment datum second zero.2]
      rfl
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [release]
      split
      · simp_all
      · rfl
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [release]
      split
      · simp_all
      · rfl
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [release]
      split
      · simp_all
      · rfl
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), zero => by
      simp only [count] at zero
      simp only [release]
      split
      · simp_all
      · rfl
  | _, environment, datum, .op .nu (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [release]
      rw [release_of_count_zero fresh subject (prependRen fresh environment) (weaken datum) body zero]
      rfl
  | _, environment, datum, .op .rep (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [release]
      rw [release_of_count_zero fresh subject environment datum body zero]
      rfl
termination_by _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem nameKey_ne {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω) (subject : Var Ω .nm)
    (excluded : ∀ name, environment .nm name ≠ subject) (name : Name Γ) :
    ActiveMarkedNames.nameKey (environment .nm) name ≠ subject := by
  cases name with
  | var name => exact excluded name
  | op operator _ => cases operator

/-- Existing code whose free names and newly bound names avoid the selected
key has no active offer on that key, including below persistent components. -/
theorem count_zero_of_excluded {Ω : Ctx sig} (fresh subject : Var Ω .nm)
    (different : fresh ≠ subject) :
    ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω) (process : Proc Γ),
      (∀ name, environment .nm name ≠ subject) → count fresh subject environment process = 0
  | _, _, .var _, _ => by simp only [count]
  | _, _, .op .nil .nil, _ => by simp only [count]
  | _, environment, .op .par (.cons first (.cons second .nil)), excluded => by
      simp only [count, count_zero_of_excluded fresh subject different environment first excluded,
        count_zero_of_excluded fresh subject different environment second excluded, Nat.zero_add]
  | _, environment, .op .inp1 (.cons channel (.cons _ .nil)), excluded => by
      simp only [count, onSubject, nameKey_ne environment subject excluded channel, decide_false, Bool.false_eq_true, ite_false]
  | _, environment, .op .inp2 (.cons channel (.cons _ .nil)), excluded => by
      simp only [count, onSubject, nameKey_ne environment subject excluded channel, decide_false, Bool.false_eq_true, ite_false]
  | _, environment, .op .out1 (.cons channel (.cons _ .nil)), excluded => by
      simp only [count, onSubject, nameKey_ne environment subject excluded channel, decide_false, Bool.false_eq_true, ite_false]
  | _, environment, .op .out2 (.cons channel (.cons _ (.cons _ .nil))), excluded => by
      simp only [count, onSubject, nameKey_ne environment subject excluded channel, decide_false, Bool.false_eq_true, ite_false]
  | _, environment, .op .nu (.cons body .nil), excluded => by
      simp only [count]
      apply count_zero_of_excluded fresh subject different (prependRen fresh environment) body
      intro name
      cases name with
      | zero => exact different
      | succ name => exact excluded name
  | _, environment, .op .rep (.cons body .nil), excluded => by
      simpa only [count] using count_zero_of_excluded fresh subject different environment body excluded
termination_by _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- The existing scoped world read in one observation context. Every
new scope name uses the separate fresh key; old ambient names keep their keys. -/
def scopeEnvironment {Ω : Ctx sig} (fresh : Var Ω .nm) :
    {Γ Δ : Ctx sig} → Scope Γ Δ → Ren sig Γ Ω → Ren sig Δ Ω
  | _, _, .nil, environment => environment
  | _, _, .bind rest, environment => scopeEnvironment fresh rest (prependRen fresh environment)

theorem count_scope {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (environment : Ren sig Γ Ω) (process : Proc Δ),
      count fresh subject environment (scope.close process) =
        count fresh subject (scopeEnvironment fresh scope environment) process
  | _, _, .nil, _, _ => rfl
  | _, _, .bind rest, environment, process => by
      simp only [Scope.close, nu, count, scopeEnvironment]
      exact count_scope fresh subject rest (prependRen fresh environment) process

theorem release_scope {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (environment : Ren sig Γ Ω)
      (datum : Name Γ) (process : Proc Δ),
      release fresh subject environment datum (scope.close process) =
        scope.close (release fresh subject (scopeEnvironment fresh scope environment)
          (rename scope.inclusion datum) process)
  | _, _, .nil, _, _, _ => by simp only [Scope.close, Scope.inclusion, scopeEnvironment, rename_id]
  | _, _, .bind rest, environment, datum, process => by
      simp only [Scope.close, nu, release, scopeEnvironment]
      rw [release_scope fresh subject rest (prependRen fresh environment) (weaken datum) process]
      simp only [weaken, rename_comp, Scope.inclusion]

/-- An observation distinct from the fresh key reconstructs its original
ambient variable exactly, even though fresh keys themselves are not injective. -/
theorem scope_name_back {Ω : Ctx sig} (fresh wanted : Var Ω .nm)
    (different : fresh ≠ wanted) :
    ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (environment : Ren sig Γ Ω) (old : Var Γ .nm),
      (∀ name, environment .nm name = wanted → name = old) →
      ∀ actual, scopeEnvironment fresh scope environment .nm actual = wanted →
        actual = scope.inclusion .nm old
  | _, _, .nil, environment, old, back, actual, observed => back actual observed
  | _, _, .bind rest, environment, old, back, actual, observed => by
      apply scope_name_back fresh wanted different rest (prependRen fresh environment) (.succ old) ?_ actual observed
      intro name key
      cases name with
      | zero => exact False.elim (different key)
      | succ name => exact congrArg Var.succ (back name key)

theorem scope_names_back {Ω Γ Δ : Ctx sig} (fresh wanted : Var Ω .nm)
    (different : fresh ≠ wanted) (scope : Scope Γ Δ) (environment : Ren sig Γ Ω)
    (old : Var Γ .nm) (back : ∀ name, environment .nm name = wanted → name = old)
    (actual : Name Δ)
    (observed : ActiveMarkedNames.nameKey (scopeEnvironment fresh scope environment .nm) actual = wanted) :
    actual = rename scope.inclusion (.var old) := by
  cases actual with
  | var name => exact congrArg Term.var (scope_name_back fresh wanted different scope environment old back name observed)
  | op operator _ => cases operator

/-- The predicate records the selected actual unary communication, its
interpreted subject and its exact received ambient datum. -/
def UnaryChoice {Ω Γ : Ctx sig} (subject : Var Ω .nm)
    (environment : Ren sig Γ Ω) (datum : Name Γ) :
    {redex reduct : Proc Γ} → Communication redex reduct → Prop
  | _, _, .unary channel actualDatum _ => onSubject environment subject channel = true ∧ actualDatum = datum
  | _, _, .binary _ _ _ _ => False

def SelectedUnary {Ω Γ : Ctx sig} {source target : Proc Γ}
    (fresh subject : Var Ω .nm) (environment : Ren sig Γ Ω) (datum : Name Γ)
    (exposure : Exposure source target) : Prop :=
  UnaryChoice subject (scopeEnvironment fresh exposure.scope environment)
    (rename exposure.scope.inclusion datum) exposure.selected

/-- Every supplied unary firing on a subject with exactly two nonpersistent
active offers is the actual update of the original process. In particular,
its exposed frame and its final endpoint are retained through all scopes. -/
theorem supplied_unary_endpoint {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    (environment : Ren sig Γ Ω) (datum : Name Γ) {source target : Proc Γ}
    (exposure : Exposure source target)
    (safe : repFree fresh subject environment source)
    (unique : count fresh subject environment source ≤ 2)
    (received : SelectedUnary fresh subject environment datum exposure) :
    StructuralEq (release fresh subject environment datum source) target := by
  have counted := count_structural fresh subject exposure.before environment safe
  have updated := release_structural fresh subject exposure.before environment datum
  rcases exposure with ⟨world, scope, redex, reduct, selected, frame, before, after⟩
  cases selected with
  | binary => exact False.elim received
  | unary channel actualDatum body =>
      simp only [SelectedUnary, UnaryChoice] at received
      obtain ⟨matching, rfl⟩ := received
      rw [count_scope] at counted
      simp only [par, out1, inp1, count, matching, ite_true] at counted
      have zero : count fresh subject (scopeEnvironment fresh scope environment) frame = 0 := by omega
      have untouched := release_of_count_zero fresh subject (scopeEnvironment fresh scope environment)
        (rename scope.inclusion datum) frame zero
      rw [release_scope] at updated
      simp only [par, out1, inp1, release, matching, ite_true, untouched] at updated
      exact .trans updated (.trans (scope.congr (.par
        (.trans (.parComm _ _) (.parUnit _)) (.refl frame))) after)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectFiring
