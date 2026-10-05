import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

/-!
# Closing a single opened active private binder

A marked active binder is counted only when its physical bound name is used.
Unused marked scopes may be inserted or removed by the genuine static laws.
Finite linear marking, together with absence from replicated active bodies,
allows the opened name to be closed again without changing the supplied term.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

private def usedNumber (occurrences : Nat) : Nat := if occurrences = 0 then 0 else 1

def contribution {Γ : Ctx sig} (selected : Bool) (body : Proc (.nm :: Γ)) : Nat :=
  if selected then usedNumber (countVar (Var.zero : Var (.nm :: Γ) .nm) body) else 0

def markedCount : {Γ : Ctx sig} → ActiveMarking.Tree Bool → Proc Γ → Nat
  | _, _, .var _ => 0
  | _, _, .op .nil .nil => 0
  | _, marked, .op .par (.cons first (.cons second .nil)) => match marked with
      | .par left right => markedCount left first + markedCount right second
      | _ => 0
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)) => 0
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)) => 0
  | _, _, .op .out1 (.cons _ (.cons _ .nil)) => 0
  | _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => 0
  | _, marked, .op .nu (.cons body .nil) => match marked with
      | .nu selected marked => contribution selected body + markedCount marked body
      | _ => 0
  | _, marked, .op .rep (.cons body .nil) => match marked with
      | .rep marked => markedCount marked body
      | _ => 0
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

def Linear : {Γ : Ctx sig} → ActiveMarking.Tree Bool → Proc Γ → Prop
  | _, _, .var _ => True
  | _, _, .op .nil .nil => True
  | _, marked, .op .par (.cons first (.cons second .nil)) => match marked with
      | .par left right => Linear left first ∧ Linear right second
      | _ => True
  | _, _, .op .inp1 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .inp2 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .out1 (.cons _ (.cons _ .nil)) => True
  | _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => True
  | _, marked, .op .nu (.cons body .nil) => match marked with
      | .nu _ marked => Linear marked body
      | _ => True
  | _, marked, .op .rep (.cons body .nil) => match marked with
      | .rep marked => markedCount marked body = 0
      | _ => True
termination_by _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem markedCount_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    markedCount marked (rename environment process) = markedCount marked process := by
  induction fits generalizing Δ with
  | var => simp only [rename, markedCount]
  | nil => simp only [nil, rename, renameArgs, markedCount]
  | par _ _ leftIH rightIH =>
      simp only [par, rename, renameArgs, liftRen, markedCount]
      rw [leftIH, rightIH]
  | inp1 => simp only [inp1, rename, renameArgs, markedCount]
  | inp2 => simp only [inp2, rename, renameArgs, markedCount]
  | out1 => simp only [out1, rename, renameArgs, markedCount]
  | out2 => simp only [out2, rename, renameArgs, markedCount]
  | nu selected _ ih =>
      simp only [nu, rename, renameArgs, markedCount, contribution]
      rw [count_bound_rename, ih]
  | rep _ ih => simp only [rep, rename, renameArgs, liftRen, markedCount]; exact ih environment

theorem linear_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    Linear marked (rename environment process) ↔ Linear marked process := by
  induction fits generalizing Δ with
  | var => simp only [rename, Linear]
  | nil => simp only [nil, rename, renameArgs, Linear]
  | par _ _ leftIH rightIH =>
      simp only [par, rename, renameArgs, liftRen, Linear]
      exact and_congr (leftIH environment) (rightIH environment)
  | inp1 => simp only [inp1, rename, renameArgs, Linear]
  | inp2 => simp only [inp2, rename, renameArgs, Linear]
  | out1 => simp only [out1, rename, renameArgs, Linear]
  | out2 => simp only [out2, rename, renameArgs, Linear]
  | nu _ _ ih => simpa only [nu, rename, renameArgs, Linear] using ih (liftRen environment [Srt.nm])
  | rep bodyFits => simp only [rep, rename, renameArgs, liftRen, Linear, markedCount_rename environment bodyFits]

theorem markedCount_vacuous {Γ : Ctx sig} {marked : ActiveMarking.Tree Bool}
    {process : Proc Γ} (fits : Fits marked process) (unused : Vacuous process) :
    markedCount marked process = 0 := by
  induction fits with
  | var => simp only [markedCount]
  | nil => simp only [nil, markedCount]
  | par _ _ leftIH rightIH =>
      simp only [par, Vacuous] at unused
      simp only [par, markedCount, leftIH unused.1, rightIH unused.2, Nat.add_zero]
  | inp1 => simp only [inp1, markedCount]
  | inp2 => simp only [inp2, markedCount]
  | out1 => simp only [out1, markedCount]
  | out2 => simp only [out2, markedCount]
  | nu selected _ ih =>
      simp only [nu, Vacuous] at unused
      simp only [nu, markedCount, contribution, usedNumber, unused.1, ↓reduceIte, ih unused.2, Nat.add_zero]
      cases selected <;> rfl
  | rep _ ih => simp only [rep, Vacuous] at unused; simpa only [rep, markedCount] using ih unused

theorem linear_of_count_zero {Γ : Ctx sig} {marked : ActiveMarking.Tree Bool}
    {process : Proc Γ} (fits : Fits marked process) (zero : markedCount marked process = 0) :
    Linear marked process := by
  induction fits with
  | var => simp only [Linear]
  | nil => simp only [nil, Linear]
  | par _ _ leftIH rightIH =>
      simp only [par, markedCount, Nat.add_eq_zero_iff] at zero
      simpa only [par, Linear] using And.intro (leftIH zero.1) (rightIH zero.2)
  | inp1 => simp only [inp1, Linear]
  | inp2 => simp only [inp2, Linear]
  | out1 => simp only [out1, Linear]
  | out2 => simp only [out2, Linear]
  | nu _ _ ih =>
      simp only [nu, markedCount, Nat.add_eq_zero_iff] at zero
      simpa only [nu, Linear] using ih zero.2
  | rep => simpa only [rep, Linear, markedCount] using zero

theorem linear_of_safe {Γ : Ctx sig} {marked : ActiveMarking.Tree Bool}
    {process : Proc Γ} (fits : Fits marked process) (safe : Safe process) : Linear marked process := by
  induction fits with
  | var => simp only [Linear]
  | nil => simp only [nil, Linear]
  | par _ _ leftIH rightIH =>
      simp only [par, Safe] at safe
      simpa only [par, Linear] using And.intro (leftIH safe.1) (rightIH safe.2)
  | inp1 => simp only [inp1, Linear]
  | inp2 => simp only [inp2, Linear]
  | out1 => simp only [out1, Linear]
  | out2 => simp only [out2, Linear]
  | nu _ _ ih => simp only [nu, Safe] at safe; simpa only [nu, Linear] using ih safe
  | rep bodyFits =>
      simp only [rep, Safe] at safe
      simpa only [rep, Linear] using markedCount_vacuous bodyFits safe

/-- Removing only unused marked scopes agrees with ordinary reindexing. -/
theorem count_zero_open {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process)
    (zero : markedCount marked process = 0) :
    StructuralEq (openMarked opened environment marked process) (rename environment process) := by
  induction fits generalizing Δ with
  | var => simp only [openMarked, rename]; exact .refl _
  | nil => simp only [nil, openMarked, rename, renameArgs]; exact .refl _
  | par _ _ leftIH rightIH =>
      simp only [par, markedCount, Nat.add_eq_zero_iff] at zero
      simpa only [par, openMarked, rename, renameArgs, liftRen] using
        StructuralEq.par (leftIH opened environment zero.1) (rightIH opened environment zero.2)
  | inp1 => simp only [inp1, openMarked]; exact .refl _
  | inp2 => simp only [inp2, openMarked]; exact .refl _
  | out1 => simp only [out1, openMarked]; exact .refl _
  | out2 => simp only [out2, openMarked]; exact .refl _
  | @nu Γ selected body marked bodyFits ih =>
      simp only [nu, markedCount, Nat.add_eq_zero_iff] at zero
      simp only [nu, openMarked]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [rename, renameArgs, nu] using StructuralEq.nu (ih opened.succ (liftRen environment [Srt.nm]) zero.2)
      · simp only [↓reduceIte]
        have unused : countVar (Var.zero : Var (.nm :: Γ) .nm) body = 0 := by
          simpa only [contribution, usedNumber, ↓reduceIte, ite_eq_left_iff, Nat.one_ne_zero, imp_false, not_not] using zero.1
        obtain ⟨original, _, weakEqual⟩ := exists_unweaken body unused
        refine (ih opened (prependRen opened environment) zero.2).trans ?_
        rw [← weakEqual]
        simp only [weaken, rename_comp]
        have included : (fun sort name => prependRen opened environment sort (.succ name)) = environment := rfl
        rw [included]
        exact .symm ((StructuralEq.nuUnused original).rename environment)
  | rep _ ih =>
      simp only [rep, markedCount] at zero
      simpa only [rep, openMarked, rename, renameArgs, liftRen] using StructuralEq.rep (ih opened environment zero)


private theorem marked_exchange {Γ : Ctx sig} (outer inner : Bool)
    {marked : ActiveMarking.Tree Bool} {body : Proc (.nm :: .nm :: Γ)} (fits : Fits marked body) :
    markedCount (.nu outer (.nu inner marked)) (nu (nu body)) =
      markedCount (.nu inner (.nu outer marked)) (nu (nu (rename swapRen body))) := by
  have first := count_swap (.zero : Var (.nm :: .nm :: Γ) .nm) body
  have second := count_swap (.succ .zero : Var (.nm :: .nm :: Γ) .nm) body
  simp only [swapRen, exchangeRen] at first second
  simp only [nu, markedCount, contribution, countVar, countVarArgs, weakenVar, Nat.add_zero]
  rw [markedCount_rename swapRen fits, first, second]
  exact Nat.add_left_comm _ _ _

private theorem contribution_structural {Γ : Ctx sig} {first second : Proc (.nm :: Γ)}
    (equal : StructuralEq first second) (selected : Bool) : contribution selected first = contribution selected second := by
  unfold contribution
  split
  · unfold usedNumber
    simp only [support_zero_structural equal .zero]
  · rfl

/-- The existing static rules preserve the number of used opened binders on
the guarded-server fragment, including differently marked equal copies. -/
theorem markedCount_transport {Γ : Ctx sig} {m n : ActiveMarking.Tree Bool}
    {p q : Proc Γ} (tracked : Transport m p n q) (fits : Fits m p) (safe : Safe p) :
    markedCount m p = markedCount n q := by
  induction tracked with
  | refl => rfl
  | trans left right leftIH rightIH =>
      exact (leftIH fits safe).trans
        (rightIH (transport_fits left fits) ((safe_structural left.erase).mp safe))
  | parComm => simp only [par, markedCount, Nat.add_comm]
  | parAssoc => simp only [par, markedCount, Nat.add_assoc]
  | parAssocBack => simp only [par, markedCount, Nat.add_assoc]
  | parUnit => simp only [par, nil, markedCount, Nat.add_zero]
  | parUnitBack => simp only [par, nil, markedCount, Nat.add_zero]
  | nuUnused origin marked process =>
      cases fits
      rename_i bodyFits
      have originalFits := Fits.ofRename _ process marked bodyFits
      simp only [nu, markedCount, contribution]
      rw [countVar_zero_of_weaken]
      simp only [weaken, markedCount_rename _ originalFits, usedNumber, ↓reduceIte, ite_self, Nat.zero_add]

  | nuUnusedBack origin marked process =>
      simp only [nu, markedCount, contribution]
      rw [countVar_zero_of_weaken]
      simp only [weaken, markedCount_rename _ fits, usedNumber, ↓reduceIte, ite_self, Nat.zero_add]

  | nuPar origin first second process frame =>
      cases fits with
      | par privateFits frameFits =>
          simp only [nu, par, markedCount, contribution, countVar, countVarArgs, weakenVar, Nat.add_zero]
          rw [countVar_zero_of_weaken]
          simp only [weaken, markedCount_rename _ frameFits]
          simp only [Nat.add_zero, Nat.add_assoc]
  | nuParBack origin first second process frame =>
      cases fits
      rename_i bodyFits
      cases bodyFits with
      | par privateFits weakFits =>
          have frameFits := Fits.ofRename _ frame second weakFits
          simp only [nu, par, markedCount, contribution, countVar, countVarArgs, weakenVar, Nat.add_zero]
          rw [countVar_zero_of_weaken]
          simp only [weaken, markedCount_rename _ frameFits]
          simp only [Nat.add_zero, Nat.add_assoc]
  | nuSwap outer inner marked process =>
      cases fits
      rename_i innerFits
      cases innerFits
      rename_i bodyFits
      exact marked_exchange outer inner bodyFits
  | nuSwapBack outer inner marked process =>
      cases fits
      rename_i outerFits
      cases outerFits
      rename_i bodyFits
      exact (marked_exchange outer inner (Fits.ofRename _ process marked bodyFits)).symm
  | repUnfold marked process =>
      cases fits
      rename_i bodyFits
      simp only [rep, Safe] at safe
      simp only [rep, par, markedCount, markedCount_vacuous bodyFits safe, Nat.add_zero]
  | repFold copy server process =>
      cases fits with
      | par copyFits replicatedFits =>
          cases replicatedFits
          rename_i serverFits
          simp only [par, rep, Safe] at safe
          simp only [par, rep, markedCount, markedCount_vacuous copyFits safe.2,
            markedCount_vacuous serverFits safe.2, Nat.add_zero]
  | par _ _ leftIH rightIH =>
      cases fits with
      | par firstFits secondFits =>
          simp only [par, Safe] at safe
          simp only [par, markedCount, leftIH firstFits safe.1, rightIH secondFits safe.2]
  | nu origin tracked ih =>
      cases fits
      rename_i bodyFits
      simp only [nu, Safe] at safe
      simp only [nu, markedCount, ih bodyFits safe, contribution_structural tracked.erase origin]
  | inp1 => simp only [inp1, markedCount]
  | inp2 => simp only [inp2, markedCount]
  | rep tracked ih =>
      cases fits
      rename_i bodyFits
      simp only [rep, Safe] at safe
      simpa only [rep, markedCount] using ih bodyFits (safe_of_vacuous _ safe)


theorem markedCount_ordinary : ∀ {Γ : Ctx sig} (process : Proc Γ), markedCount (ordinary process) process = 0
  | _, .var _ => by simp only [markedCount]
  | _, .op .nil .nil => by simp only [markedCount]
  | _, .op .par (.cons first (.cons second .nil)) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, markedCount, markedCount_ordinary first,
        markedCount_ordinary second, Nat.add_zero]
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [markedCount]
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [markedCount]
  | _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [markedCount]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by simp only [markedCount]
  | _, .op .nu (.cons body .nil) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, markedCount, contribution, Bool.false_eq_true,
        ↓reduceIte, markedCount_ordinary body, Nat.zero_add]
  | _, .op .rep (.cons body .nil) => by
      simp only [ordinary, ActiveSyntaxMarking.mark, markedCount, markedCount_ordinary body]
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem contribution_le_one {Γ : Ctx sig} (selected : Bool) (body : Proc (.nm :: Γ)) :
    contribution selected body ≤ 1 := by
  unfold contribution usedNumber
  split <;> (first | split <;> omega | omega)

theorem contribution_le_of_support {Γ : Ctx sig} (selected : Bool)
    (source target : Proc (.nm :: Γ))
    (absent : countVar (Var.zero : Var (.nm :: Γ) .nm) source = 0 →
      countVar (Var.zero : Var (.nm :: Γ) .nm) target = 0) :
    contribution selected target ≤ contribution selected source := by
  cases selected
  · simp only [contribution, Bool.false_eq_true, ↓reduceIte, Nat.le_refl]
  · by_cases zero : countVar (Var.zero : Var (.nm :: Γ) .nm) source = 0
    · simp only [contribution, usedNumber, zero, absent zero, ↓reduceIte, Nat.le_refl]
    · have targetBound := contribution_le_one true target
      simpa only [contribution, usedNumber, zero, ↓reduceIte] using targetBound

/-- One physical opened name can be reclosed when it originates from at most
one used active binder, and not from an autonomous replicated private scope. -/
theorem close_open_single : ∀ {Γ : Ctx sig} (process : Proc Γ) (marked : ActiveMarking.Tree Bool)
    (_fits : Fits marked process) (_linear : Linear marked process) (_single : markedCount marked process ≤ 1),
    StructuralEq (nu (openMarked (Var.zero : Var (.nm :: Γ) .nm) (fun _ name => name.succ) marked process)) process
  | Γ, process, marked, fits, linear, single => by
    by_cases zero : markedCount marked process = 0
    · exact (StructuralEq.nu (count_zero_open .zero (fun _ name => name.succ) fits zero)).trans (.nuUnused process)
    · generalize sourceEqual : process = source at fits linear single zero ⊢
      cases fits with
      | var => simp only [markedCount] at zero; exact False.elim (zero True.intro)
      | nil => simp only [nil, markedCount] at zero; exact False.elim (zero True.intro)
      | inp1 => simp only [inp1, markedCount] at zero; exact False.elim (zero True.intro)
      | inp2 => simp only [inp2, markedCount] at zero; exact False.elim (zero True.intro)
      | out1 => simp only [out1, markedCount] at zero; exact False.elim (zero True.intro)
      | out2 => simp only [out2, markedCount] at zero; exact False.elim (zero True.intro)
      | @par Γ first second left right firstFits secondFits =>
          simp only [par, Linear] at linear
          simp only [par, markedCount] at single
          simp only [par, openMarked]
          by_cases rightZero : markedCount right second = 0
          · have leftBound : markedCount left first ≤ 1 := by omega
            exact (StructuralEq.nu (StructuralEq.par (.refl _)
              (count_zero_open .zero (fun _ name => name.succ) secondFits rightZero))).trans
                ((StructuralEq.nuPar _ second).symm.trans
                  (StructuralEq.par (close_open_single first left firstFits linear.1 leftBound) (.refl second)))
          · have leftZero : markedCount left first = 0 := by omega
            have rightBound : markedCount right second ≤ 1 := by omega
            exact (StructuralEq.nu (StructuralEq.par
              (count_zero_open .zero (fun _ name => name.succ) firstFits leftZero) (.refl _))).trans
                ((StructuralEq.nu (.parComm _ _)).trans
                  ((StructuralEq.nuPar _ first).symm.trans
                    ((StructuralEq.par (close_open_single second right secondFits linear.2 rightBound) (.refl first)).trans
                      (.parComm _ _))))
      | @nu Γ selected body inner bodyFits =>
          simp only [nu, Linear] at linear
          simp only [nu, markedCount] at single
          simp only [nu, openMarked]
          cases selected
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have bodyBound : markedCount inner body ≤ 1 := by simpa only [contribution, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] using single
            have natural := openMarked_map (swapRen (Γ := Γ))
              (Var.succ Var.zero : Var (.nm :: .nm :: Γ) .nm)
              (liftRen (fun _ name => name.succ) [Srt.nm]) bodyFits
            change rename swapRen (openMarked (Var.succ Var.zero) (liftRen (fun _ name => name.succ) [Srt.nm]) inner body) =
              openMarked Var.zero (fun sort name => swapRen sort (liftRen (fun _ name => name.succ) [Srt.nm] sort name)) inner body at natural
            have environmentEqual :
                (fun sort name => swapRen sort (liftRen (fun _ name => name.succ) [Srt.nm] sort name)) =
                (fun (_ : Srt) (name : Var (Srt.nm :: Γ) _) => name.succ) := by
              funext sort name
              cases name <;> rfl
            rw [environmentEqual] at natural
            refine (StructuralEq.nuSwap _).trans (StructuralEq.nu ?_)
            rw [natural]
            exact close_open_single body inner bodyFits linear bodyBound
          · simp only [↓reduceIte]
            by_cases unused : countVar (Var.zero : Var (.nm :: Γ) .nm) body = 0
            · obtain ⟨original, _, weakEqual⟩ := exists_unweaken body unused
              have originalFits := Fits.ofRename (fun _ name => name.succ) original inner (weakEqual ▸ bodyFits)
              have originalLinear : Linear inner original := by
                apply (linear_rename (fun _ name => name.succ) originalFits).mp
                change Linear inner (weaken original)
                rw [weakEqual]
                exact linear
              have bodyBound : markedCount inner body ≤ 1 := by
                simpa only [contribution, usedNumber, unused, ↓reduceIte, Nat.zero_add] using single
              have originalBound : markedCount inner original ≤ 1 := by
                rw [← markedCount_rename (fun _ name => name.succ) originalFits]
                change markedCount inner (weaken original) ≤ 1
                rw [weakEqual]
                exact bodyBound
              have smaller : termSize original < termSize body + 1 := by
                rw [← weakEqual]
                simp only [weaken, termSize_rename]
                omega
              rw [← weakEqual, weaken, openMarked_rename _ _ _ originalFits]
              exact (close_open_single original inner originalFits originalLinear originalBound).trans
                (.symm (.nuUnused original))
            · have bodyZero : markedCount inner body = 0 := by
                simp only [contribution, usedNumber, unused, ↓reduceIte] at single
                omega
              have included : prependRen (Var.zero : Var (.nm :: Γ) .nm)
                  (fun (_ : Srt) (name : Var Γ _) => name.succ) = (fun _ name => name) := by
                funext sort name
                cases name <;> rfl
              rw [included]
              exact StructuralEq.nu (by
                simpa only [rename_id] using count_zero_open .zero (fun _ name => name) bodyFits bodyZero)
      | rep bodyFits =>
          simp only [rep, Linear] at linear
          exact False.elim (zero (by simpa only [rep, markedCount] using linear))
termination_by _ process _ _ _ _ => termSize process
decreasing_by all_goals rw [sourceEqual]
              all_goals try simp only [par, nu, termSize, argsSize]
              all_goals omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
