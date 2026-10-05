import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSyntaxMarking
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolScopeReflection

/-!
# Opening a selected private binder through actual static equations

The interpreter below opens marked active restrictions and retains all other
scopes. Input guards remain opaque. Used private scopes inside an autonomous
replicated body require a different treatment from guarded input servers;
this boundary is recorded by an invariant of the existing static equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

theorem count_bound_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (body : Proc (.nm :: Γ)) :
    countVar (Var.zero : Var (.nm :: Δ) .nm) (rename (liftRen environment [.nm]) body) =
      countVar (Var.zero : Var (.nm :: Γ) .nm) body := by
  refine countVar_rename_of_reflect (liftRen environment [.nm]) Var.zero ?_ body
  intro sort name
  cases name <;> rfl

theorem count_weaken {Γ : Ctx sig} (name : Var Γ .nm) (process : Proc Γ) :
    countVar (Var.succ name : Var (.nm :: Γ) .nm) (weaken process) = countVar name process := by
  refine countVar_rename_of_reflect (fun _ name => Var.succ name) name ?_ process
  intro sort other
  rfl

theorem count_swap {Γ : Ctx sig} (name : Var (.nm :: .nm :: Γ) .nm)
    (process : Proc (.nm :: .nm :: Γ)) :
    countVar (swapRen .nm name) (rename swapRen process) = countVar name process := by
  refine countVar_rename_of_reflect swapRen name ?_ process
  intro sort other
  cases name with
  | zero => cases other with
    | zero => rfl
    | succ other => cases other <;> rfl
  | succ name => cases name with
    | zero => cases other with
      | zero => rfl
      | succ other => cases other <;> rfl
    | succ name => cases other with
      | zero => rfl
      | succ other => cases other <;> rfl

/-- Static equations preserve the absence of an actual free name. Replication
may change its occurrence count, so equality of counts is not asserted. -/
theorem support_zero_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) :
    ∀ name : Var Γ .nm, countVar name first = 0 ↔ countVar name second = 0 := by
  induction equal with
  | refl => intro name; rfl
  | symm _ ih => intro name; exact (ih name).symm
  | trans _ _ leftIH rightIH => intro name; exact (leftIH name).trans (rightIH name)
  | parComm => intro name; simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff, and_comm]
  | parAssoc => intro name; simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff, and_assoc]
  | parUnit => intro name; simp only [par, nil, countVar, countVarArgs, weakenVar, Nat.add_zero]
  | nuUnused => intro name; simp only [nu, countVar, countVarArgs, weakenVar, Nat.add_zero]; rw [count_weaken]
  | nuPar => intro name; simp only [nu, par, countVar, countVarArgs, weakenVar, Nat.add_zero]; rw [count_weaken]
  | nuSwap process =>
      intro name
      simp only [nu, countVar, countVarArgs, weakenVar, Nat.add_zero]
      have swapped := count_swap (.succ (.succ name)) process
      simp only [swapRen, exchangeRen] at swapped
      rw [swapped]
  | repUnfold => intro name; simp only [rep, par, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff, and_self]
  | par _ _ leftIH rightIH =>
      intro name
      simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff]
      exact and_congr (leftIH name) (rightIH name)
  | nu _ ih => intro name; simpa only [nu, countVar, countVarArgs, weakenVar, Nat.add_zero] using ih (.succ name)
  | inp1 channel _ ih =>
      intro name
      simp only [inp1, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff]
      exact and_congr Iff.rfl (ih (.succ name))
  | inp2 channel _ ih =>
      intro name
      simp only [inp2, countVar, countVarArgs, weakenVar, Nat.add_zero, Nat.add_eq_zero_iff]
      exact and_congr Iff.rfl (ih (.succ (.succ name)))
  | rep _ ih => intro name; simpa only [rep, countVar, countVarArgs, weakenVar, Nat.add_zero] using ih name

/-- All active restrictions are unused. Suspended input continuations are
not active, and may themselves allocate private names. -/
def Vacuous : {Γ : Ctx sig} → Proc Γ → Prop
  | _, .var _ => True
  | _, .op .nil .nil => True
  | _, .op .par (.cons first (.cons second .nil)) => Vacuous first ∧ Vacuous second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => True
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, .op .out1 (.cons _ (.cons _ .nil)) => True
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | Γ, .op .nu (.cons body .nil) => countVar (Var.zero : Var (Srt.nm :: Γ) Srt.nm) body = 0 ∧ Vacuous body
  | _, .op .rep (.cons body .nil) => Vacuous body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem vacuous_rename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
    Vacuous (rename environment process) ↔ Vacuous process
  | _, _, _, .var _ => by simp only [rename, Vacuous]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, Vacuous]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, Vacuous]
      exact and_congr (vacuous_rename environment first) (vacuous_rename environment second)
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Vacuous]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Vacuous]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Vacuous]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, Vacuous]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, Vacuous]
      rw [count_bound_rename]
      exact and_congr Iff.rfl (vacuous_rename (liftRen environment [.nm]) body)
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, Vacuous]
      exact vacuous_rename environment body
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem vacuous_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : Vacuous first ↔ Vacuous second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ leftIH rightIH => exact leftIH.trans rightIH
  | parComm => simp only [par, Vacuous, and_comm]
  | parAssoc => simp only [par, Vacuous, and_assoc]
  | parUnit => simp only [par, nil, Vacuous, and_true]
  | nuUnused =>
      simp only [nu, Vacuous]
      rw [countVar_zero_of_weaken]
      simp only [true_and, weaken, vacuous_rename]
  | nuPar =>
      simp only [nu, par, Vacuous, countVar, countVarArgs, weakenVar, Nat.add_zero]
      rw [countVar_zero_of_weaken]
      simp only [Nat.add_zero, weaken, vacuous_rename, and_assoc]
  | nuSwap process =>
      simp only [nu, Vacuous, countVar, countVarArgs, weakenVar, Nat.add_zero, vacuous_rename]
      have first := count_swap (.zero : Var (Srt.nm :: Srt.nm :: _) Srt.nm) process
      have second := count_swap (.succ .zero : Var (Srt.nm :: Srt.nm :: _) Srt.nm) process
      simp only [swapRen, exchangeRen] at first second
      rw [first, second]
      exact and_left_comm
  | repUnfold => simp only [rep, par, Vacuous, and_self]
  | par _ _ leftIH rightIH => simpa only [par, Vacuous] using and_congr leftIH rightIH
  | nu equal ih => simpa only [nu, Vacuous] using and_congr (support_zero_structural equal .zero) ih
  | inp1 => simp only [inp1, Vacuous]
  | inp2 => simp only [inp2, Vacuous]
  | rep _ ih => simpa only [rep, Vacuous] using ih

/-- Active replication may contain guarded servers and unused private scopes,
but no used private scope above an input guard. -/
def Safe : {Γ : Ctx sig} → Proc Γ → Prop
  | _, .var _ => True
  | _, .op .nil .nil => True
  | _, .op .par (.cons first (.cons second .nil)) => Safe first ∧ Safe second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => True
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, .op .out1 (.cons _ (.cons _ .nil)) => True
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | _, .op .nu (.cons body .nil) => Safe body
  | _, .op .rep (.cons body .nil) => Vacuous body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem safe_of_vacuous : ∀ {Γ : Ctx sig} (process : Proc Γ), Vacuous process → Safe process
  | _, .var _, _ => by simp only [Safe]
  | _, .op .nil .nil, _ => by simp only [Safe]
  | _, .op .par (.cons first (.cons second .nil)), safe => by
      simp only [Vacuous] at safe
      simp only [Safe]
      exact ⟨safe_of_vacuous first safe.1, safe_of_vacuous second safe.2⟩
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [Safe]
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [Safe]
  | _, .op .out1 (.cons _ (.cons _ .nil)), _ => by simp only [Safe]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _ => by simp only [Safe]
  | _, .op .nu (.cons body .nil), safe => by
      simp only [Vacuous] at safe
      simp only [Safe]
      exact safe_of_vacuous body safe.2
  | _, .op .rep (.cons _ .nil), safe => by simpa only [Safe, Vacuous] using safe
termination_by _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem safe_rename : ∀ {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (process : Proc Γ),
    Safe (rename environment process) ↔ Safe process
  | _, _, _, .var _ => by simp only [rename, Safe]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, Safe]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, Safe]
      exact and_congr (safe_rename environment first) (safe_rename environment second)
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Safe]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Safe]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, Safe]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, Safe]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, Safe]
      exact safe_rename (liftRen environment [.nm]) body
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, Safe]
      exact vacuous_rename environment body
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem safe_structural {Γ : Ctx sig} {first second : Proc Γ}
    (equal : StructuralEq first second) : Safe first ↔ Safe second := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ leftIH rightIH => exact leftIH.trans rightIH
  | parComm => simp only [par, Safe, and_comm]
  | parAssoc => simp only [par, Safe, and_assoc]
  | parUnit => simp only [par, nil, Safe, and_true]
  | nuUnused => simp only [nu, Safe, weaken, safe_rename]
  | nuPar => simp only [nu, par, Safe, weaken, safe_rename]
  | nuSwap => simp only [nu, Safe, safe_rename]
  | repUnfold process =>
      simp only [rep, par, Safe]
      exact ⟨fun safe => ⟨safe_of_vacuous process safe, safe⟩, And.right⟩
  | par _ _ leftIH rightIH => simpa only [par, Safe] using and_congr leftIH rightIH
  | nu _ ih => simpa only [nu, Safe] using ih
  | inp1 => simp only [inp1, Safe]
  | inp2 => simp only [inp2, Safe]
  | rep equal _ => simpa only [rep, Safe] using vacuous_structural equal


/-- The all-unopened specialization of the shared syntax marking. -/
abbrev ordinary {Γ : Ctx sig} (process : Proc Γ) : ActiveMarking.Tree Bool :=
  ActiveSyntaxMarking.mark false process

theorem ordinary_fits {Γ : Ctx sig} (process : Proc Γ) : Fits (ordinary process) process :=
  ActiveSyntaxMarking.mark_fits false process

/-- An active telescope with no used restriction is actual weakening of a
process in its original context. This retains the supplied body exactly. -/
theorem vacuous_scope_strengthening {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ)
    (unused : Vacuous (scope.close body)) :
    ∃ original : Proc Γ, body = rename scope.inclusion original ∧ Vacuous original ∧
      StructuralEq (scope.close body) original := by
  induction scope with
  | nil => exact ⟨body, (rename_id body).symm, unused, .refl body⟩
  | @bind Γ Δ rest ih =>
      simp only [Scope.close, nu, Vacuous] at unused
      obtain ⟨inside, bodyEqual, insideVacuous, insideEqual⟩ := ih body unused.2
      have nameUnused : countVar (Var.zero : Var (Srt.nm :: Γ) Srt.nm) inside = 0 :=
        (support_zero_structural insideEqual .zero).mp unused.1
      obtain ⟨original, _, originalEqual⟩ := exists_unweaken inside nameUnused
      have insideIsWeak : inside = weaken original := originalEqual.symm
      refine ⟨original, ?_, ?_, ?_⟩
      · rw [bodyEqual, insideIsWeak]
        simp only [weaken, rename_comp, Scope.inclusion]
      · rw [insideIsWeak] at insideVacuous
        exact (vacuous_rename _ original).mp insideVacuous
      · refine (StructuralEq.nu insideEqual).trans ?_
        rw [insideIsWeak]
        exact .nuUnused original

/-- Interpret an opened active restriction as the supplied physical name.
Other restrictions remain genuine binders; input continuations are reindexed
as guarded syntax and their internal marks are not executed. -/
def openMarked : {Γ Δ : Ctx sig} → Var Δ .nm → Ren sig Γ Δ → ActiveMarking.Tree Bool → Proc Γ → Proc Δ
  | _, _, _, environment, _, .var name => .var (environment .pr name)
  | _, _, _, _, _, .op .nil .nil => nil
  | _, _, opened, environment, marked, .op .par (.cons p (.cons q .nil)) =>
      match marked with
      | .par first second => par (openMarked opened environment first p) (openMarked opened environment second q)
      | _ => rename environment (par p q)
  | _, _, _, environment, _, .op .inp1 (.cons channel (.cons body .nil)) => rename environment (inp1 channel body)
  | _, _, _, environment, _, .op .inp2 (.cons channel (.cons body .nil)) => rename environment (inp2 channel body)
  | _, _, _, environment, _, .op .out1 (.cons channel (.cons datum .nil)) => rename environment (out1 channel datum)
  | _, _, _, environment, _, .op .out2 (.cons channel (.cons first (.cons second .nil))) => rename environment (out2 channel first second)
  | _, _, opened, environment, marked, .op .nu (.cons body .nil) =>
      match marked with
      | .nu selected marked =>
          if selected then openMarked opened (prependRen opened environment) marked body
          else nu (openMarked (.succ opened) (liftRen environment [.nm]) marked body)
      | _ => rename environment (nu body)
  | _, _, opened, environment, marked, .op .rep (.cons body .nil) =>
      match marked with
      | .rep marked => rep (openMarked opened environment marked body)
      | _ => rename environment (rep body)
termination_by _ _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Reindexing the supplied source changes the name interpretation, not the
selected constructor origins. -/
theorem openMarked_rename {Γ Δ Ω : Ctx sig} (reindex : Ren sig Γ Δ)
    (opened : Var Ω .nm) (environment : Ren sig Δ Ω)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    openMarked opened environment marked (rename reindex process) =
      openMarked opened (fun sort name => environment sort (reindex sort name)) marked process := by
  induction fits generalizing Δ Ω with
  | var name => simp only [openMarked, rename]
  | nil => simp only [openMarked, rename, renameArgs, nil]
  | par _ _ leftIH rightIH =>
      simp only [par, openMarked, rename, renameArgs, liftRen]
      rw [leftIH, rightIH]
  | @inp1 Γ origin channel body marked _ _ =>
      simpa only [inp1, openMarked, rename, renameArgs] using
        rename_comp reindex environment (inp1 channel body)
  | @inp2 Γ origin channel body marked _ _ =>
      simpa only [inp2, openMarked, rename, renameArgs] using
        rename_comp reindex environment (inp2 channel body)
  | @out1 Γ origin channel datum =>
      simpa only [out1, openMarked, rename, renameArgs] using
        rename_comp reindex environment (out1 channel datum)
  | @out2 Γ origin channel first second =>
      simpa only [out2, openMarked, rename, renameArgs] using
        rename_comp reindex environment (out2 channel first second)
  | @nu Γ selected body marked _ ih =>
      simp only [nu, openMarked, rename, renameArgs]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        exact congrArg (fun environment => nu (openMarked opened.succ environment marked body)) (by
          funext sort name
          cases name <;> rfl)
      · simp only [↓reduceIte]
        rw [ih]
        exact congrArg (fun environment => openMarked opened environment marked body) (by
          funext sort name
          cases name <;> rfl)
  | rep _ ih =>
      simp only [rep, openMarked, rename, renameArgs, liftRen]
      rw [ih]


theorem openMarked_map {Γ Δ Ω : Ctx sig} (reindex : Ren sig Δ Ω)
    (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    rename reindex (openMarked opened environment marked process) =
      openMarked (reindex .nm opened) (fun sort name => reindex sort (environment sort name)) marked process := by
  induction fits generalizing Δ Ω with
  | var => simp only [openMarked, rename]
  | nil => simp only [openMarked, nil, rename, renameArgs]
  | par _ _ leftIH rightIH =>
      simp only [par, openMarked, rename, renameArgs, liftRen]
      rw [leftIH, rightIH]
  | @inp1 Γ origin channel body marked _ _ =>
      simpa only [inp1, openMarked] using rename_comp environment reindex (inp1 channel body)
  | @inp2 Γ origin channel body marked _ _ =>
      simpa only [inp2, openMarked] using rename_comp environment reindex (inp2 channel body)
  | @out1 Γ origin channel datum =>
      simpa only [out1, openMarked] using rename_comp environment reindex (out1 channel datum)
  | @out2 Γ origin channel first second =>
      simpa only [out2, openMarked] using rename_comp environment reindex (out2 channel first second)
  | @nu Γ selected body marked _ ih =>
      simp only [nu, openMarked]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte, rename, renameArgs]
        rw [ih]
        exact congrArg (fun environment => nu (openMarked (.succ (reindex .nm opened)) environment marked body)) (by
          funext sort name
          cases name <;> rfl)
      · simp only [↓reduceIte]
        rw [ih]
        exact congrArg (fun environment => openMarked (reindex .nm opened) environment marked body) (by
          funext sort name
          cases name <;> rfl)
  | rep _ ih =>
      simp only [rep, openMarked, rename, renameArgs, liftRen]
      rw [ih]

theorem open_ordinary : ∀ {Γ Δ : Ctx sig} (opened : Var Δ .nm)
    (environment : Ren sig Γ Δ) (process : Proc Γ),
    openMarked opened environment (ordinary process) process = rename environment process
  | _, _, _, _, .var _ => by simp only [ordinary, ActiveSyntaxMarking.mark, openMarked, rename]
  | _, _, _, _, .op .nil .nil => by simp only [ordinary, ActiveSyntaxMarking.mark, openMarked, nil, rename, renameArgs]
  | _, _, opened, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, openMarked, par, rename, renameArgs, liftRen]
      rw [open_ordinary opened environment first, open_ordinary opened environment second]
  | _, _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [openMarked, inp1]
  | _, _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [openMarked, inp2]
  | _, _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [openMarked, out1]
  | _, _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [openMarked, out2]
  | _, _, opened, environment, .op .nu (.cons body .nil) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, openMarked, Bool.false_eq_true, ↓reduceIte, nu, rename, renameArgs]
      rw [open_ordinary opened.succ (liftRen environment [.nm]) body]
  | _, _, opened, environment, .op .rep (.cons body .nil) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, openMarked, rep, rename, renameArgs, liftRen]
      rw [open_ordinary opened environment body]
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- Opening marks on unused active restrictions loses no behavior or syntax
modulo the actual unused-scope equation. -/
theorem vacuous_open {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process)
    (unused : Vacuous process) :
    StructuralEq (openMarked opened environment marked process) (rename environment process) := by
  induction fits generalizing Δ with
  | var => simp only [openMarked, rename]; exact .refl _
  | nil => simp only [nil, openMarked, rename, renameArgs]; exact .refl _
  | par _ _ leftIH rightIH =>
      simp only [par, Vacuous] at unused
      simpa only [par, openMarked, rename, renameArgs, liftRen] using
        StructuralEq.par (leftIH opened environment unused.1) (rightIH opened environment unused.2)
  | inp1 => simp only [inp1, openMarked]; exact .refl _
  | inp2 => simp only [inp2, openMarked]; exact .refl _
  | out1 => simp only [out1, openMarked]; exact .refl _
  | out2 => simp only [out2, openMarked]; exact .refl _
  | @nu Γ selected body marked bodyFits ih =>
      simp only [nu, Vacuous] at unused
      simp only [nu, openMarked]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [rename, renameArgs, nu] using
          StructuralEq.nu (ih opened.succ (liftRen environment [.nm]) unused.2)
      · simp only [↓reduceIte]
        obtain ⟨original, _, weakEqual⟩ := exists_unweaken body unused.1
        have equal : body = weaken original := weakEqual.symm
        refine (ih opened (prependRen opened environment) unused.2).trans ?_
        rw [equal]
        simp only [weaken, rename_comp]
        have included : (fun sort name => prependRen opened environment sort (.succ name)) = environment := rfl
        rw [included]
        exact .symm ((StructuralEq.nuUnused original).rename environment)
  | rep _ ih =>
      simp only [rep, Vacuous] at unused
      simpa only [rep, openMarked, rename, renameArgs, liftRen] using
        StructuralEq.rep (ih opened environment unused)


theorem transport_fits {Γ : Ctx sig} {m n : ActiveMarking.Tree Bool}
    {p q : Proc Γ} (tracked : Transport m p n q) : Fits m p → Fits n q := by
  induction tracked with
  | refl => exact id
  | trans _ _ leftIH rightIH => exact fun fits => rightIH (leftIH fits)
  | parComm => intro fits; cases fits with
    | par first second => exact .par second first
  | parAssoc => intro fits; cases fits with
    | par first third => cases first with
      | par first second => exact .par first (.par second third)
  | parAssocBack => intro fits; cases fits with
    | par first later => cases later with
      | par second third => exact .par (.par first second) third
  | parUnit => intro fits; cases fits with
    | par first empty => exact first
  | parUnitBack => exact fun fits => .par fits .nil
  | nuUnused => intro fits; cases fits with
    | nu origin body => exact Fits.ofRename _ _ _ body
  | nuUnusedBack => exact fun fits => .nu _ (fits.rename _)
  | nuPar origin m n process frame => intro fits; cases fits with
    | par privateFits frameFits =>
      cases privateFits
      rename_i bodyFits
      exact .nu origin (.par bodyFits (frameFits.rename _))
  | nuParBack origin m n process frame =>
      intro fits
      cases fits
      rename_i bodyFits
      cases bodyFits with
    | par privateFits frameFits => exact .par (.nu origin privateFits) (Fits.ofRename _ _ _ frameFits)
  | nuSwap outer inner marked process =>
      intro fits
      cases fits
      rename_i innerFits
      cases innerFits
      rename_i bodyFits
      exact .nu inner (.nu outer (bodyFits.rename _))
  | nuSwapBack outer inner marked process =>
      intro fits
      cases fits
      rename_i outerFits
      cases outerFits
      rename_i bodyFits
      exact .nu outer (.nu inner (Fits.ofRename _ _ _ bodyFits))
  | repUnfold => intro fits; cases fits with
    | rep body => exact .par body (.rep body)
  | repFold => intro fits; cases fits with
    | par copy server => exact server
  | par _ _ leftIH rightIH => intro fits; cases fits with
    | par first second => exact .par (leftIH first) (rightIH second)
  | nu origin _ ih => intro fits; cases fits with
    | nu _ body => exact .nu origin (ih body)
  | inp1 origin channel _ ih => intro fits; cases fits with
    | inp1 _ _ body => exact .inp1 origin channel (ih body)
  | inp2 origin channel _ ih => intro fits; cases fits with
    | inp2 _ _ body => exact .inp2 origin channel (ih body)
  | rep _ ih => intro fits; cases fits with
    | rep body => exact .rep (ih body)

private theorem open_weaken {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    openMarked opened.succ (liftRen environment [.nm]) marked (weaken process) =
      weaken (openMarked opened environment marked process) := by
  rw [weaken, openMarked_rename _ _ _ fits]
  exact (openMarked_map (fun _ name => name.succ) opened environment fits).symm

private theorem structural_of_eq {Γ : Ctx sig} {first second : Proc Γ}
    (equal : first = second) : StructuralEq first second := equal ▸ StructuralEq.refl first

private theorem open_exchange {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    (outer inner : Bool) {marked : ActiveMarking.Tree Bool}
    {body : Proc (.nm :: .nm :: Γ)} (fits : Fits marked body) :
    StructuralEq (openMarked opened environment (.nu outer (.nu inner marked)) (nu (nu body)))
      (openMarked opened environment (.nu inner (.nu outer marked)) (nu (nu (rename swapRen body)))) := by
  simp only [nu, openMarked]
  cases outer <;> cases inner <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have natural := openMarked_map (swapRen (Γ := Δ)) opened.succ.succ
        (liftRen (liftRen environment [.nm]) [.nm]) fits
    rw [openMarked_rename _ _ _ fits]
    refine (StructuralEq.nuSwap _).trans ?_
    apply StructuralEq.nu
    apply StructuralEq.nu
    have environmentEqual :
        (fun sort name => swapRen sort (liftRen (liftRen environment [.nm]) [.nm] sort name)) =
        (fun sort name => liftRen (liftRen environment [.nm]) [.nm] sort (swapRen sort name)) := by
      funext sort name
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl
    change rename swapRen (openMarked opened.succ.succ (liftRen (liftRen environment [.nm]) [.nm]) marked body) =
      openMarked opened.succ.succ (fun sort name => swapRen sort (liftRen (liftRen environment [.nm]) [.nm] sort name)) marked body at natural
    rw [environmentEqual] at natural
    exact natural ▸ StructuralEq.refl _
  · rw [openMarked_rename _ _ _ fits]
    apply StructuralEq.nu
    apply structural_of_eq
    congr 1
    funext sort name
    cases name with
    | zero => rfl
    | succ name => cases name <;> rfl
  · rw [openMarked_rename _ _ _ fits]
    apply StructuralEq.nu
    apply structural_of_eq
    congr 1
    funext sort name
    cases name with
    | zero => rfl
    | succ name => cases name <;> rfl
  · rw [openMarked_rename _ _ _ fits]
    apply structural_of_eq
    congr 1
    funext sort name
    cases name with
    | zero => rfl
    | succ name => cases name <;> rfl

/-- Every supplied marked static derivation commutes with opening, for the
SC-invariant guarded-server fragment. Equal copies may have different marks;
the replication cases therefore use actual unused-scope equations. -/
theorem open_transport {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {m n : ActiveMarking.Tree Bool} {p q : Proc Γ} (tracked : Transport m p n q)
    (fits : Fits m p) (safe : Safe p) :
    StructuralEq (openMarked opened environment m p) (openMarked opened environment n q) := by
  induction tracked generalizing Δ with
  | refl => exact .refl _
  | trans left right leftIH rightIH =>
      exact (leftIH opened environment fits safe).trans
        (rightIH opened environment (transport_fits left fits) ((safe_structural left.erase).mp safe))
  | parComm => simp only [par, openMarked]; exact .parComm _ _
  | parAssoc => simp only [par, openMarked]; exact .parAssoc _ _ _
  | parAssocBack => simp only [par, openMarked]; exact .symm (.parAssoc _ _ _)
  | parUnit => simp only [par, nil, openMarked]; exact .parUnit _
  | parUnitBack => simp only [par, nil, openMarked]; exact .symm (.parUnit _)
  | nuUnused origin marked process =>
      cases fits with
      | nu _ weakFits =>
        have originalFits := Fits.ofRename _ process marked weakFits
        simp only [nu, openMarked]
        cases origin
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [open_weaken opened environment originalFits]
          exact .nuUnused _
        · simp only [↓reduceIte]
          rw [weaken, openMarked_rename _ _ _ originalFits]
          exact .refl _
  | nuUnusedBack origin marked process =>
      simp only [nu, openMarked]
      cases origin
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [open_weaken opened environment fits]
        exact .symm (.nuUnused _)
      · simp only [↓reduceIte]
        rw [weaken, openMarked_rename _ _ _ fits]
        exact .refl _
  | nuPar origin first second process frame =>
      cases fits with
      | par privateFits frameFits => cases privateFits with
        | nu _ bodyFits =>
          simp only [nu, par, openMarked]
          cases origin
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [open_weaken opened environment frameFits]
            exact .nuPar _ _
          · simp only [↓reduceIte]
            rw [weaken, openMarked_rename _ _ _ frameFits]
            exact .refl _
  | nuParBack origin first second process frame =>
      cases fits with
      | nu _ bodyFits => cases bodyFits with
        | par privateFits weakFrameFits =>
          have frameFits := Fits.ofRename _ frame second weakFrameFits
          simp only [nu, par, openMarked]
          cases origin
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [open_weaken opened environment frameFits]
            exact .symm (.nuPar _ _)
          · simp only [↓reduceIte]
            rw [weaken, openMarked_rename _ _ _ frameFits]
            exact .refl _
  | nuSwap outer inner marked process =>
      cases fits with
      | nu _ innerFits => cases innerFits with
        | nu _ bodyFits => exact open_exchange opened environment outer inner bodyFits
  | nuSwapBack outer inner marked process =>
      cases fits with
      | nu _ outerFits => cases outerFits with
        | nu _ bodyFits =>
          exact .symm (open_exchange opened environment outer inner (Fits.ofRename _ process marked bodyFits))
  | repUnfold => simp only [rep, par, openMarked]; exact .repUnfold _
  | repFold copy server process =>
      cases fits with
      | par copyFits replicatedFits => cases replicatedFits with
        | rep serverFits =>
          simp only [par, rep, Safe] at safe
          have same : StructuralEq (openMarked opened environment copy process)
              (openMarked opened environment server process) :=
            (vacuous_open opened environment copyFits safe.2).trans
              (vacuous_open opened environment serverFits safe.2).symm
          simp only [par, rep, openMarked]
          exact (StructuralEq.par same (.refl _)).trans (.symm (.repUnfold _))
  | par _ _ leftIH rightIH =>
      cases fits with
      | par leftFits rightFits =>
          simp only [par, Safe] at safe
          simpa only [par, openMarked] using
            StructuralEq.par (leftIH opened environment leftFits safe.1) (rightIH opened environment rightFits safe.2)
  | nu origin _ ih =>
      cases fits with
      | nu _ bodyFits =>
          simp only [nu, Safe] at safe
          simp only [nu, openMarked]
          cases origin
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact .nu (ih opened.succ (liftRen environment [.nm]) bodyFits safe)
          · simp only [↓reduceIte]
            exact ih opened (prependRen opened environment) bodyFits safe
  | inp1 origin channel body ih =>
      simpa only [inp1, openMarked, rename, renameArgs, liftRen] using
        StructuralEq.inp1 (rename environment channel) (body.erase.rename (liftRen environment [.nm]))
  | inp2 origin channel body ih =>
      simpa only [inp2, openMarked, rename, renameArgs, liftRen] using
        StructuralEq.inp2 (rename environment channel) (body.erase.rename (liftRen environment [.nm, .nm]))
  | rep tracked ih =>
      cases fits with
      | rep bodyFits =>
          simp only [rep, Safe] at safe
          simpa only [rep, openMarked] using StructuralEq.rep
            (ih opened environment bodyFits (safe_of_vacuous _ safe))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
