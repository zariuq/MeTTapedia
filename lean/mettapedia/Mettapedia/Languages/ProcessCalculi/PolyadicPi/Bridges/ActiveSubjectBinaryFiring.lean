import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectFiring

/-!
# Actual endpoints of linear binary communications

The update opens the selected binary guard using two ambient names in their
authored order, removes its selected-subject output, and leaves every other
guard suspended. It commutes with all static equations. Consequently a
supplied communication on a subject with two nonpersistent active offers
has exactly the endpoint obtained by updating the original process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectBinaryFiring

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ScopedActiveFrontier ScopedCommunicationInversion
open ActiveSubjectResidual

local instance {Γ : Ctx sig} : DecidableEq (Var Γ Srt.nm) := decEqVar (S := sig)

/-- A physical two-field update of the existing process, rather than a
transition relation or an interpretation of its names in a quotient. -/
def releasePair {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Name Γ → Name Γ → Proc Γ → Proc Γ
  | _, _, _, _, .var name => .var name
  | _, _, _, _, .op .nil .nil => nil
  | _, environment, first, second, .op .par (.cons left (.cons right .nil)) =>
      par (releasePair fresh subject environment first second left)
        (releasePair fresh subject environment first second right)
  | _, environment, _, _, .op .inp1 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then nil else inp1 channel body
  | _, environment, first, second, .op .inp2 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then openPair body first second else inp2 channel body
  | _, environment, _, _, .op .out1 (.cons channel (.cons payload .nil)) =>
      if onSubject environment subject channel then nil else out1 channel payload
  | _, environment, _, _, .op .out2 (.cons channel (.cons first (.cons second .nil))) =>
      if onSubject environment subject channel then nil else out2 channel first second
  | _, environment, first, second, .op .nu (.cons body .nil) =>
      nu (releasePair fresh subject (prependRen fresh environment) (weaken first) (weaken second) body)
  | _, environment, first, second, .op .rep (.cons body .nil) =>
      rep (releasePair fresh subject environment first second body)
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem onSubject_rename {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (subject : Var Ω .nm) (channel : Name Γ) :
    onSubject environment subject (rename reindex channel) =
      onSubject (fun sort name => environment sort (reindex sort name)) subject channel := by
  cases channel with
  | var => rfl
  | op operator _ => cases operator

private theorem extension_comp {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (environment : Ren sig Δ Ω) (fresh : Var Ω .nm) :
    (fun sort name => prependRen fresh environment sort (liftRen reindex [.nm] sort name)) =
      prependRen fresh (fun sort name => environment sort (reindex sort name)) := by
  funext sort name
  cases name <;> rfl

theorem releasePair_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω)
      (first second : Name Γ) (process : Proc Γ),
      releasePair fresh subject environment (rename reindex first) (rename reindex second)
        (rename reindex process) =
      rename reindex (releasePair fresh subject
        (fun sort name => environment sort (reindex sort name)) first second process)
  | _, _, _, _, _, _, .var _ => by simp only [rename, releasePair]
  | _, _, _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, releasePair, nil]
  | _, _, reindex, environment, first, second, .op .par (.cons left (.cons right .nil)) => by
      simp only [rename, renameArgs, liftRen, releasePair, par]
      rw [releasePair_rename fresh subject reindex environment first second left,
        releasePair_rename fresh subject reindex environment first second right]
  | _, _, reindex, environment, _, _, .op .inp1 (.cons channel (.cons body .nil)) => by
      simp only [inp1, rename, renameArgs, liftRen, releasePair]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, first, second, .op .inp2 (.cons channel (.cons body .nil)) => by
      simp only [inp2, rename, renameArgs, liftRen, releasePair]
      rw [onSubject_rename reindex environment subject channel]
      split
      · exact (rename_openPair reindex body first second).symm
      · rfl
  | _, _, reindex, environment, _, _, .op .out1 (.cons channel (.cons payload .nil)) => by
      simp only [out1, rename, renameArgs, liftRen, releasePair]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, _, _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      simp only [out2, rename, renameArgs, liftRen, releasePair]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, first, second, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, releasePair, nu]
      rw [← rename_weaken reindex first, ← rename_weaken reindex second,
        releasePair_rename fresh subject (liftRen reindex [.nm]) _ (weaken first) (weaken second) body,
        extension_comp]
  | _, _, reindex, environment, first, second, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, releasePair, rep]
      rw [releasePair_rename fresh subject reindex environment first second body]
termination_by _ _ _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem structural_openPair {Γ : Ctx sig} {left right : Proc (.nm :: .nm :: Γ)}
    (equal : StructuralEq left right) (first second : Name Γ) :
    StructuralEq (openPair left first second) (openPair right first second) := by
  cases first with
  | op operator _ => cases operator
  | var first =>
      cases second with
      | op operator _ => cases operator
      | var second =>
          simp only [openPair_variables]
          exact equal.rename (pairRen first second)

private theorem swap_environment {Γ Ω : Ctx sig} (fresh : Var Ω .nm) (environment : Ren sig Γ Ω) :
    (fun sort name => prependRen fresh (prependRen fresh environment) sort (swapRen sort name)) =
      prependRen fresh (prependRen fresh environment) := by
  funext sort name
  cases name with
  | zero => rfl
  | succ name => cases name <;> rfl

private theorem double_weaken_swap {Γ : Ctx sig} (name : Name Γ) :
    rename swapRen (weaken (t := Srt.nm) (weaken (t := Srt.nm) name)) =
      weaken (t := Srt.nm) (weaken (t := Srt.nm) name) := by
  cases name with
  | var => rfl
  | op operator _ => cases operator

/-- Actual two-field opening respects every declared static equation,
including arbitrary changes inside the suspended binary guard. -/
theorem releasePair_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {left right : Proc Γ} (equal : StructuralEq left right) :
    ∀ (environment : Ren sig Γ Ω) (first second : Name Γ),
      StructuralEq (releasePair fresh subject environment first second left)
        (releasePair fresh subject environment first second right) := by
  induction equal with
  | refl => intro environment first second; exact .refl _
  | symm _ ih => intro environment first second; exact .symm (ih environment first second)
  | trans _ _ leftIH rightIH => intro environment first second; exact .trans (leftIH environment first second) (rightIH environment first second)
  | parComm => intro environment first second; simp only [par, releasePair]; exact .parComm _ _
  | parAssoc => intro environment first second; simp only [par, releasePair]; exact .parAssoc _ _ _
  | parUnit => intro environment first second; simp only [par, nil, releasePair]; exact .parUnit _
  | nuUnused =>
      intro environment first second
      simp only [nu, releasePair, weaken]
      rw [releasePair_rename]
      exact .nuUnused _
  | nuPar =>
      intro environment first second
      simp only [nu, par, releasePair, weaken]
      rw [releasePair_rename]
      exact .nuPar _ _
  | nuSwap =>
      intro environment first second
      simp only [nu, releasePair]
      conv_rhs => rw [← double_weaken_swap first, ← double_weaken_swap second]
      rw [releasePair_rename, swap_environment]
      exact .nuSwap _
  | repUnfold => intro environment first second; simp only [rep, par, releasePair]; exact .repUnfold _
  | par _ _ leftIH rightIH => intro environment first second; simp only [par, releasePair]; exact .par (leftIH environment first second) (rightIH environment first second)
  | nu _ ih => intro environment first second; simp only [nu, releasePair]; exact .nu (ih _ (weaken first) (weaken second))
  | inp1 channel equal _ =>
      intro environment first second
      simp only [inp1, releasePair]
      split
      · exact .refl _
      · exact .inp1 channel equal
  | inp2 channel equal _ =>
      intro environment first second
      simp only [inp2, releasePair]
      split
      · exact structural_openPair equal first second
      · exact .inp2 channel equal
  | rep _ ih => intro environment first second; simp only [rep, releasePair]; exact .rep (ih environment first second)

theorem releasePair_of_count_zero {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω) (first second : Name Γ) (process : Proc Γ),
      count fresh subject environment process = 0 →
        releasePair fresh subject environment first second process = process
  | _, _, _, _, .var _, _ => by simp only [releasePair]
  | _, _, _, _, .op .nil .nil, _ => by simp only [releasePair, nil]
  | _, environment, first, second, .op .par (.cons left (.cons right .nil)), zero => by
      simp only [count, Nat.add_eq_zero_iff] at zero
      simp only [releasePair]
      rw [releasePair_of_count_zero fresh subject environment first second left zero.1,
        releasePair_of_count_zero fresh subject environment first second right zero.2]
      rfl
  | _, _, _, _, .op .inp1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [releasePair]
      split
      · simp_all
      · rfl
  | _, _, _, _, .op .inp2 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [releasePair]
      split
      · simp_all
      · rfl
  | _, _, _, _, .op .out1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [releasePair]
      split
      · simp_all
      · rfl
  | _, _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), zero => by
      simp only [count] at zero
      simp only [releasePair]
      split
      · simp_all
      · rfl
  | _, environment, first, second, .op .nu (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [releasePair]
      rw [releasePair_of_count_zero fresh subject (prependRen fresh environment) (weaken first) (weaken second) body zero]
      rfl
  | _, environment, first, second, .op .rep (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [releasePair]
      rw [releasePair_of_count_zero fresh subject environment first second body zero]
      rfl
termination_by _ _ _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem releasePair_scope {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (environment : Ren sig Γ Ω)
      (first second : Name Γ) (process : Proc Δ),
      releasePair fresh subject environment first second (scope.close process) =
        scope.close (releasePair fresh subject
          (ActiveSubjectFiring.scopeEnvironment fresh scope environment)
          (rename scope.inclusion first) (rename scope.inclusion second) process)
  | _, _, .nil, _, _, _, _ => by simp only [Scope.close, Scope.inclusion, ActiveSubjectFiring.scopeEnvironment, rename_id]
  | _, _, .bind rest, environment, first, second, process => by
      simp only [Scope.close, nu, releasePair, ActiveSubjectFiring.scopeEnvironment]
      rw [releasePair_scope fresh subject rest (prependRen fresh environment) (weaken first) (weaken second) process]
      simp only [weaken, rename_comp, Scope.inclusion]

/-- The actual selected binary redex receives the two original ambient
names, in the same order, beneath its entire private telescope. -/
def BinaryChoice {Ω Γ : Ctx sig} (subject : Var Ω .nm)
    (environment : Ren sig Γ Ω) (first second : Name Γ) :
    {redex reduct : Proc Γ} → Communication redex reduct → Prop
  | _, _, .unary _ _ _ => False
  | _, _, .binary channel actualFirst actualSecond _ =>
      onSubject environment subject channel = true ∧ actualFirst = first ∧ actualSecond = second

def SelectedBinary {Ω Γ : Ctx sig} {source target : Proc Γ}
    (fresh subject : Var Ω .nm) (environment : Ren sig Γ Ω) (first second : Name Γ)
    (exposure : Exposure source target) : Prop :=
  BinaryChoice subject (ActiveSubjectFiring.scopeEnvironment fresh exposure.scope environment)
    (rename exposure.scope.inclusion first) (rename exposure.scope.inclusion second) exposure.selected

/-- An arbitrary supplied binary firing with two linear offers reaches the
actual two-field update of its original source, with the supplied endpoint
and untouched frame retained. -/
theorem supplied_binary_endpoint {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    (environment : Ren sig Γ Ω) (first second : Name Γ) {source target : Proc Γ}
    (exposure : Exposure source target)
    (safe : repFree fresh subject environment source)
    (unique : count fresh subject environment source ≤ 2)
    (received : SelectedBinary fresh subject environment first second exposure) :
    StructuralEq (releasePair fresh subject environment first second source) target := by
  have counted := count_structural fresh subject exposure.before environment safe
  have updated := releasePair_structural fresh subject exposure.before environment first second
  rcases exposure with ⟨world, scope, redex, reduct, selected, frame, before, after⟩
  cases selected with
  | unary => exact False.elim received
  | binary channel actualFirst actualSecond body =>
      simp only [SelectedBinary, BinaryChoice] at received
      obtain ⟨matching, rfl, rfl⟩ := received
      rw [ActiveSubjectFiring.count_scope] at counted
      simp only [par, out2, inp2, count, matching, ite_true] at counted
      have zero : count fresh subject (ActiveSubjectFiring.scopeEnvironment fresh scope environment) frame = 0 := by omega
      have untouched := releasePair_of_count_zero fresh subject
        (ActiveSubjectFiring.scopeEnvironment fresh scope environment)
        (rename scope.inclusion first) (rename scope.inclusion second) frame zero
      rw [releasePair_scope] at updated
      simp only [par, out2, inp2, releasePair, matching, ite_true, untouched] at updated
      exact .trans updated (.trans (scope.congr (.par
        (.trans (.parComm _ _) (.parUnit _)) (.refl frame))) after)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectBinaryFiring
