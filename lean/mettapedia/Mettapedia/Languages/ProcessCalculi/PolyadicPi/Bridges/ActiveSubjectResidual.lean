import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveGuardedBodies

/-!
# Linear residuals selected by an actual subject key

These functions inspect existing active prefixes; suspended input bodies are
opaque. A sorted name interpretation identifies one subject to remove. Static
equations commute with that removal. Absence from replicated active bodies is
the additional condition needed for finite occurrence counts to be invariant.
It distinguishes a private protocol actor from unrelated unary servers on
other subjects, which an arity-only condition cannot distinguish.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectResidual

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

local instance {Γ : Ctx sig} : DecidableEq (Var Γ Srt.nm) := decEqVar (S := sig)

def onSubject {Γ Ω : Ctx sig} (environment : Ren sig Γ Ω)
    (subject : Var Ω .nm) (channel : Name Γ) : Bool :=
  decide (ActiveMarkedNames.nameKey (environment .nm) channel = subject)

def count {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Proc Γ → Nat
  | _, _, .var _ => 0
  | _, _, .op .nil .nil => 0
  | _, environment, .op .par (.cons first (.cons second .nil)) =>
      count fresh subject environment first + count fresh subject environment second
  | _, environment, .op .inp1 (.cons channel (.cons _ .nil)) => if onSubject environment subject channel then 1 else 0
  | _, environment, .op .inp2 (.cons channel (.cons _ .nil)) => if onSubject environment subject channel then 1 else 0
  | _, environment, .op .out1 (.cons channel (.cons _ .nil)) => if onSubject environment subject channel then 1 else 0
  | _, environment, .op .out2 (.cons channel (.cons _ (.cons _ .nil))) => if onSubject environment subject channel then 1 else 0
  | _, environment, .op .nu (.cons body .nil) => count fresh subject (prependRen fresh environment) body
  | _, environment, .op .rep (.cons body .nil) => count fresh subject environment body
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

def repFree {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Proc Γ → Prop
  | _, _, .var _ => True
  | _, _, .op .nil .nil => True
  | _, environment, .op .par (.cons first (.cons second .nil)) =>
      repFree fresh subject environment first ∧ repFree fresh subject environment second
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .out1 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | _, environment, .op .nu (.cons body .nil) => repFree fresh subject (prependRen fresh environment) body
  | _, environment, .op .rep (.cons body .nil) => count fresh subject environment body = 0
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

def remove {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    {Γ : Ctx sig} → Ren sig Γ Ω → Proc Γ → Proc Γ
  | _, _, .var name => .var name
  | _, _, .op .nil .nil => nil
  | _, environment, .op .par (.cons first (.cons second .nil)) =>
      par (remove fresh subject environment first) (remove fresh subject environment second)
  | _, environment, .op .inp1 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then nil else inp1 channel body
  | _, environment, .op .inp2 (.cons channel (.cons body .nil)) =>
      if onSubject environment subject channel then nil else inp2 channel body
  | _, environment, .op .out1 (.cons channel (.cons datum .nil)) =>
      if onSubject environment subject channel then nil else out1 channel datum
  | _, environment, .op .out2 (.cons channel (.cons first (.cons second .nil))) =>
      if onSubject environment subject channel then nil else out2 channel first second
  | _, environment, .op .nu (.cons body .nil) => nu (remove fresh subject (prependRen fresh environment) body)
  | _, environment, .op .rep (.cons body .nil) => rep (remove fresh subject environment body)
termination_by _ _ process => termSize process
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

theorem count_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω) (process : Proc Γ),
      count fresh subject environment (rename reindex process) =
        count fresh subject (fun sort name => environment sort (reindex sort name)) process
  | _, _, _, _, .var _ => by simp only [rename, count]
  | _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, count]
  | _, _, reindex, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, count]
      rw [count_rename fresh subject reindex environment first, count_rename fresh subject reindex environment second]
  | _, _, reindex, environment, .op .inp1 (.cons channel (.cons _ .nil)) => by
      simp only [rename, renameArgs, liftRen, count]
      rw [onSubject_rename reindex environment subject channel]
  | _, _, reindex, environment, .op .inp2 (.cons channel (.cons _ .nil)) => by
      simp only [rename, renameArgs, liftRen, count]
      rw [onSubject_rename reindex environment subject channel]
  | _, _, reindex, environment, .op .out1 (.cons channel (.cons _ .nil)) => by
      simp only [rename, renameArgs, liftRen, count]
      rw [onSubject_rename reindex environment subject channel]
  | _, _, reindex, environment, .op .out2 (.cons channel (.cons _ (.cons _ .nil))) => by
      simp only [rename, renameArgs, liftRen, count]
      rw [onSubject_rename reindex environment subject channel]
  | _, _, reindex, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, count]
      rw [count_rename fresh subject (liftRen reindex [.nm]) _ body, extension_comp]
  | _, _, reindex, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, count]
      exact count_rename fresh subject reindex environment body
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem repFree_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω) (process : Proc Γ),
      repFree fresh subject environment (rename reindex process) ↔
        repFree fresh subject (fun sort name => environment sort (reindex sort name)) process
  | _, _, _, _, .var _ => by simp only [rename, repFree]
  | _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, repFree]
  | _, _, reindex, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, repFree]
      rw [repFree_rename fresh subject reindex environment first, repFree_rename fresh subject reindex environment second]
  | _, _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [rename, renameArgs, repFree]
  | _, _, reindex, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, repFree]
      rw [repFree_rename fresh subject (liftRen reindex [.nm]) _ body, extension_comp]
  | _, _, reindex, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, repFree, count_rename]
      rfl
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem remove_rename {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ Δ : Ctx sig} (reindex : Ren sig Γ Δ) (environment : Ren sig Δ Ω) (process : Proc Γ),
      remove fresh subject environment (rename reindex process) =
        rename reindex (remove fresh subject (fun sort name => environment sort (reindex sort name)) process)
  | _, _, _, _, .var _ => by simp only [rename, remove]
  | _, _, _, _, .op .nil .nil => by simp only [rename, renameArgs, remove, nil]
  | _, _, reindex, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, remove, par]
      rw [remove_rename fresh subject reindex environment first, remove_rename fresh subject reindex environment second]
  | _, _, reindex, environment, .op .inp1 (.cons channel (.cons body .nil)) => by
      simp only [inp1, rename, renameArgs, liftRen, remove]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, .op .inp2 (.cons channel (.cons body .nil)) => by
      simp only [inp2, rename, renameArgs, liftRen, remove]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, .op .out1 (.cons channel (.cons datum .nil)) => by
      simp only [out1, rename, renameArgs, liftRen, remove]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, .op .out2 (.cons channel (.cons first (.cons second .nil))) => by
      simp only [out2, rename, renameArgs, liftRen, remove]
      rw [onSubject_rename reindex environment subject channel]
      split <;> rfl
  | _, _, reindex, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, remove, nu]
      rw [remove_rename fresh subject (liftRen reindex [.nm]) _ body, extension_comp]
  | _, _, reindex, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, remove, rep]
      rw [remove_rename fresh subject reindex environment body]
termination_by _ _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem repFree_of_count_zero {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω) (process : Proc Γ),
      count fresh subject environment process = 0 → repFree fresh subject environment process
  | _, _, .var _, _ => by simp only [repFree]
  | _, _, .op .nil .nil, _ => by simp only [repFree]
  | _, environment, .op .par (.cons first (.cons second .nil)), zero => by
      simp only [count, Nat.add_eq_zero_iff] at zero
      simp only [repFree]
      exact ⟨repFree_of_count_zero fresh subject environment first zero.1,
        repFree_of_count_zero fresh subject environment second zero.2⟩
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, _, .op .out1 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _ => by simp only [repFree]
  | _, environment, .op .nu (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [repFree]
      exact repFree_of_count_zero fresh subject (prependRen fresh environment) body zero
  | _, _, .op .rep (.cons _ .nil), zero => by simpa only [repFree, count] using zero
termination_by _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

private theorem swap_environment {Γ Ω : Ctx sig} (fresh : Var Ω .nm) (environment : Ren sig Γ Ω) :
    (fun sort name => prependRen fresh (prependRen fresh environment) sort (swapRen sort name)) =
      prependRen fresh (prependRen fresh environment) := by
  funext sort name
  cases name with
  | zero => rfl
  | succ name => cases name <;> rfl

/-- Availability is static-invariant even when replication changes finite
multiplicity. This zero law is weaker than equality of occurrence counts. -/
theorem count_zero_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ environment : Ren sig Γ Ω,
      count fresh subject environment first = 0 ↔ count fresh subject environment second = 0 := by
  induction equal with
  | refl => intro environment; rfl
  | symm _ ih => intro environment; exact (ih environment).symm
  | trans _ _ firstIH secondIH => intro environment; exact (firstIH environment).trans (secondIH environment)
  | parComm => intro environment; simp only [par, count, Nat.add_eq_zero_iff, and_comm]
  | parAssoc => intro environment; simp only [par, count, Nat.add_eq_zero_iff, and_assoc]
  | parUnit => intro environment; simp only [par, nil, count, Nat.add_zero]
  | nuUnused => intro environment; simp only [nu, count, weaken, count_rename]; rfl
  | nuPar => intro environment; simp only [nu, par, count, weaken, count_rename]; rfl
  | nuSwap => intro environment; simp only [nu, count, count_rename, swap_environment]
  | repUnfold => intro environment; simp only [rep, par, count, Nat.add_eq_zero_iff, and_self]
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, count, Nat.add_eq_zero_iff]
      exact and_congr (firstIH environment) (secondIH environment)
  | nu _ ih => intro environment; simpa only [nu, count] using ih (prependRen fresh environment)
  | inp1 => intro environment; simp only [inp1, count]
  | inp2 => intro environment; simp only [inp2, count]
  | rep _ ih => intro environment; simpa only [rep, count] using ih environment

theorem repFree_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ environment : Ren sig Γ Ω,
      repFree fresh subject environment first ↔ repFree fresh subject environment second := by
  induction equal with
  | refl => intro environment; rfl
  | symm _ ih => intro environment; exact (ih environment).symm
  | trans _ _ firstIH secondIH => intro environment; exact (firstIH environment).trans (secondIH environment)
  | parComm => intro environment; simp only [par, repFree, and_comm]
  | parAssoc => intro environment; simp only [par, repFree, and_assoc]
  | parUnit => intro environment; simp only [par, nil, repFree, and_true]
  | nuUnused => intro environment; simp only [nu, repFree, weaken, repFree_rename]; rfl
  | nuPar => intro environment; simp only [nu, par, repFree, weaken, repFree_rename]; rfl
  | nuSwap => intro environment; simp only [nu, repFree, repFree_rename, swap_environment]
  | repUnfold process =>
      intro environment
      simp only [rep, par, repFree]
      exact ⟨fun zero => ⟨repFree_of_count_zero fresh subject environment process zero, zero⟩, And.right⟩
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, repFree]
      exact and_congr (firstIH environment) (secondIH environment)
  | nu _ ih => intro environment; simpa only [nu, repFree] using ih (prependRen fresh environment)
  | inp1 => intro environment; simp only [inp1, repFree]
  | inp2 => intro environment; simp only [inp2, repFree]
  | rep equal _ => intro environment; simpa only [rep, repFree] using count_zero_structural fresh subject equal environment

/-- With no matching active server body, structural rearrangement preserves
every occurrence of the selected subject, including equal duplicate offers. -/
theorem count_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ (environment : Ren sig Γ Ω), repFree fresh subject environment first →
      count fresh subject environment first = count fresh subject environment second := by
  induction equal with
  | refl => intro environment _; rfl
  | symm equal ih => intro environment safe; exact (ih environment ((repFree_structural fresh subject equal environment).mpr safe)).symm
  | trans first _ firstIH secondIH =>
      intro environment safe
      exact (firstIH environment safe).trans (secondIH environment ((repFree_structural fresh subject first environment).mp safe))
  | parComm => intro environment _; simp only [par, count, Nat.add_comm]
  | parAssoc => intro environment _; simp only [par, count, Nat.add_assoc]
  | parUnit => intro environment _; simp only [par, nil, count, Nat.add_zero]
  | nuUnused => intro environment _; simp only [nu, count, weaken, count_rename]; rfl
  | nuPar => intro environment _; simp only [nu, par, count, weaken, count_rename]; rfl
  | nuSwap => intro environment _; simp only [nu, count, count_rename, swap_environment]
  | repUnfold => intro environment safe; simp only [rep, repFree] at safe; simp only [rep, par, count, safe, Nat.zero_add]
  | par _ _ firstIH secondIH =>
      intro environment safe
      simp only [par, repFree] at safe
      simp only [par, count]
      exact congrArg₂ Nat.add (firstIH environment safe.1) (secondIH environment safe.2)
  | nu _ ih =>
      intro environment safe
      simp only [nu, repFree] at safe
      simpa only [nu, count] using ih (prependRen fresh environment) safe
  | inp1 => intro environment _; simp only [inp1, count]
  | inp2 => intro environment _; simp only [inp2, count]
  | rep equal _ =>
      intro environment safe
      simp only [rep, repFree] at safe
      have sameZero := (count_zero_structural fresh subject equal environment).mp safe
      simp only [rep, count, safe, sameZero]

/-- Erasing the selected active subjects commutes with every actual static
law. This uses the genuine syntax equations, rather than only a bag of labels. -/
theorem remove_structural {Ω Γ : Ctx sig} (fresh subject : Var Ω .nm)
    {first second : Proc Γ} (equal : StructuralEq first second) :
    ∀ environment : Ren sig Γ Ω,
      StructuralEq (remove fresh subject environment first) (remove fresh subject environment second) := by
  induction equal with
  | refl => intro environment; exact .refl _
  | symm _ ih => intro environment; exact .symm (ih environment)
  | trans _ _ firstIH secondIH => intro environment; exact .trans (firstIH environment) (secondIH environment)
  | parComm => intro environment; simp only [par, remove]; exact .parComm _ _
  | parAssoc => intro environment; simp only [par, remove]; exact .parAssoc _ _ _
  | parUnit => intro environment; simp only [par, nil, remove]; exact .parUnit _
  | nuUnused => intro environment; simp only [nu, remove, weaken, remove_rename]; exact .nuUnused _
  | nuPar => intro environment; simp only [nu, par, remove, weaken, remove_rename]; exact .nuPar _ _
  | nuSwap => intro environment; simp only [nu, remove, remove_rename, swap_environment]; exact .nuSwap _
  | repUnfold => intro environment; simp only [rep, par, remove]; exact .repUnfold _
  | par _ _ firstIH secondIH =>
      intro environment
      simp only [par, remove]
      exact .par (firstIH environment) (secondIH environment)
  | nu _ ih =>
      intro environment
      simp only [nu, remove]
      exact .nu (ih (prependRen fresh environment))
  | inp1 channel equal _ =>
      intro environment
      simp only [inp1, remove]
      split
      · exact .refl _
      · exact .inp1 channel equal
  | inp2 channel equal _ =>
      intro environment
      simp only [inp2, remove]
      split
      · exact .refl _
      · exact .inp2 channel equal
  | rep _ ih =>
      intro environment
      simp only [rep, remove]
      exact .rep (ih environment)

theorem remove_of_count_zero {Ω : Ctx sig} (fresh subject : Var Ω .nm) :
    ∀ {Γ : Ctx sig} (environment : Ren sig Γ Ω) (process : Proc Γ),
      count fresh subject environment process = 0 → remove fresh subject environment process = process
  | _, _, .var _, _ => by simp only [remove]
  | _, _, .op .nil .nil, _ => by simp only [remove, nil]
  | _, environment, .op .par (.cons first (.cons second .nil)), zero => by
      simp only [count, Nat.add_eq_zero_iff] at zero
      simp only [remove]
      rw [remove_of_count_zero fresh subject environment first zero.1,
        remove_of_count_zero fresh subject environment second zero.2]
      rfl
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [remove]
      split
      · simp_all
      · rfl
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [remove]
      split
      · simp_all
      · rfl
  | _, _, .op .out1 (.cons _ (.cons _ .nil)), zero => by
      simp only [count] at zero
      simp only [remove]
      split
      · simp_all
      · rfl
  | _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), zero => by
      simp only [count] at zero
      simp only [remove]
      split
      · simp_all
      · rfl
  | _, environment, .op .nu (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [remove]
      rw [remove_of_count_zero fresh subject (prependRen fresh environment) body zero]
      rfl
  | _, environment, .op .rep (.cons body .nil), zero => by
      simp only [count] at zero
      simp only [remove]
      rw [remove_of_count_zero fresh subject environment body zero]
      rfl
termination_by _ _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectResidual
