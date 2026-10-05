import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningExecution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkingLabels

/-!
# Prefix origins through physical private-scope opening

Paired marks track the physical binder selected for opening and independent
prefix origins. Guards are reindexed as suspended syntax. The opened marking
therefore retains the chosen input, output and continuation through actual
scope equations and retained-server unfolding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningOrigins

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveMarkingLabels ActiveHeaderInvariant ScopedActiveFrontier ScopedCommunicationInversion
open ScopedOpening

universe u

def openedTree {Label : Type u} : ActiveMarking.Tree (Bool × Label) → ActiveMarking.Tree Label
  | .var => .var
  | .nil => .nil
  | .par first second => .par (openedTree first) (openedTree second)
  | .inp1 origin body => .inp1 origin.2 (labels Prod.snd body)
  | .inp2 origin body => .inp2 origin.2 (labels Prod.snd body)
  | .out1 origin => .out1 origin.2
  | .out2 origin => .out2 origin.2
  | .nu origin body => if origin.1 then openedTree body else .nu origin.2 (openedTree body)
  | .rep body => .rep (openedTree body)

theorem openedTree_unselected {Label : Type u} (marked : ActiveMarking.Tree Label) :
    openedTree (labels (fun origin => (false, origin)) marked) = marked := by
  induction marked <;> simp only [openedTree, labels, Bool.false_eq_true, ↓reduceIte, *,
    labels_comp]
  all_goals rw [show (Prod.snd ∘ (fun origin : Label => (false, origin))) = id from rfl, labels_id]

theorem labels_unselected_ordinary {Label : Type u} {Γ : Ctx sig} {marked : ActiveMarking.Tree Label}
    {process : Proc Γ} (fits : Fits marked process) :
    labels (fun _ : Label => false) marked = ordinary process := by
  induction fits with
  | var => simp only [ordinary, ActiveSyntaxMarking.mark, labels]
  | nil => simp only [ordinary, ActiveSyntaxMarking.mark, labels, nil]
  | par _ _ leftIH rightIH => simp only [ordinary, ActiveSyntaxMarking.mark, labels, par, leftIH, rightIH]
  | inp1 _ _ _ ih => simp only [ordinary, ActiveSyntaxMarking.mark, labels, inp1, ih]
  | inp2 _ _ _ ih => simp only [ordinary, ActiveSyntaxMarking.mark, labels, inp2, ih]
  | out1 => simp only [ordinary, ActiveSyntaxMarking.mark, labels, out1]
  | out2 => simp only [ordinary, ActiveSyntaxMarking.mark, labels, out2]
  | nu _ _ ih => simp only [ordinary, ActiveSyntaxMarking.mark, labels, nu, ih]
  | rep _ ih => simp only [ordinary, ActiveSyntaxMarking.mark, labels, rep, ih]

theorem opened_fits {Label : Type u} {Γ Δ : Ctx sig} (opened : Var Δ .nm)
    (environment : Ren sig Γ Δ) {marked : ActiveMarking.Tree (Bool × Label)} {process : Proc Γ}
    (fits : Fits marked process) :
    Fits (openedTree marked) (openMarked opened environment (labels Prod.fst marked) process) := by
  induction fits generalizing Δ with
  | var => simpa only [openedTree, labels, openMarked] using Fits.var (environment _ _)
  | nil => simpa only [openedTree, labels, nil, openMarked] using (Fits.nil (Γ := Δ))
  | par _ _ leftIH rightIH =>
      simpa only [openedTree, labels, par, openMarked] using
        Fits.par (leftIH opened environment) (rightIH opened environment)
  | inp1 origin channel bodyFits _ =>
      simpa only [openedTree, labels, inp1, openMarked, rename, renameArgs, liftRen] using
        Fits.inp1 origin.2 (rename environment channel) ((fits_labels Prod.snd bodyFits).rename (liftRen environment [.nm]))
  | inp2 origin channel bodyFits _ =>
      simpa only [openedTree, labels, inp2, openMarked, rename, renameArgs, liftRen] using
        Fits.inp2 origin.2 (rename environment channel) ((fits_labels Prod.snd bodyFits).rename (liftRen environment [.nm, .nm]))
  | out1 origin channel datum =>
      simpa only [openedTree, labels, out1, openMarked, rename, renameArgs, liftRen] using
        Fits.out1 origin.2 (rename environment channel) (rename environment datum)
  | out2 origin channel first second =>
      simpa only [openedTree, labels, out2, openMarked, rename, renameArgs, liftRen] using
        Fits.out2 origin.2 (rename environment channel) (rename environment first) (rename environment second)
  | nu origin _ ih =>
      rcases origin with ⟨selected, origin⟩
      simp only [openedTree, labels, nu, openMarked]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact .nu origin (ih opened.succ (liftRen environment [.nm]))
      · simp only [↓reduceIte]
        exact ih opened (prependRen opened environment)
  | rep _ ih => simpa only [openedTree, labels, rep, openMarked] using Fits.rep (ih opened environment)

private theorem vacuous_origin_open {Label : Type u} {Γ Δ : Ctx sig}
    (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree (Bool × Label)} {process : Proc Γ} (fits : Fits marked process)
    (unused : Vacuous process) :
    Transport (openedTree marked) (openMarked opened environment (labels Prod.fst marked) process)
      (labels Prod.snd marked) (rename environment process) ∧
    Transport (labels Prod.snd marked) (rename environment process)
      (openedTree marked) (openMarked opened environment (labels Prod.fst marked) process) := by
  induction fits generalizing Δ with
  | var => simp only [openedTree, labels, openMarked]; exact ⟨.refl _ _, .refl _ _⟩
  | nil => simp only [openedTree, labels, nil, openMarked, rename, renameArgs]; exact ⟨.refl _ _, .refl _ _⟩
  | par _ _ leftIH rightIH =>
      simp only [par, Vacuous] at unused
      simp only [openedTree, labels, par, openMarked, rename, renameArgs, liftRen]
      exact ⟨.par (leftIH opened environment unused.1).1 (rightIH opened environment unused.2).1,
        .par (leftIH opened environment unused.1).2 (rightIH opened environment unused.2).2⟩
  | inp1 => simp only [openedTree, labels, inp1, openMarked]; exact ⟨.refl _ _, .refl _ _⟩
  | inp2 => simp only [openedTree, labels, inp2, openMarked]; exact ⟨.refl _ _, .refl _ _⟩
  | out1 => simp only [openedTree, labels, out1, openMarked]; exact ⟨.refl _ _, .refl _ _⟩
  | out2 => simp only [openedTree, labels, out2, openMarked]; exact ⟨.refl _ _, .refl _ _⟩
  | @nu Γ origin body marked bodyFits ih =>
      simp only [nu, Vacuous] at unused
      rcases origin with ⟨selected, origin⟩
      cases selected
      · simp only [openedTree, labels, nu, openMarked, Bool.false_eq_true, ↓reduceIte, rename, renameArgs]
        exact ⟨.nu origin (ih opened.succ (liftRen environment [.nm]) unused.2).1,
          .nu origin (ih opened.succ (liftRen environment [.nm]) unused.2).2⟩
      · obtain ⟨old, _, equal⟩ := exists_unweaken body unused.1
        have bodyIncluded : rename (liftRen environment [.nm]) body = weaken (rename environment old) := by
          rw [← equal, rename_weaken]
        have bodyOpened : rename (prependRen opened environment) body = rename environment old := by
          rw [← equal, weaken, rename_comp]
          rfl
        have result := ih opened (prependRen opened environment) unused.2
        rw [bodyOpened] at result
        simp only [openedTree, labels, nu, openMarked, ↓reduceIte, rename, renameArgs]
        rw [bodyIncluded]
        exact ⟨result.1.trans (.nuUnusedBack origin _ _),
          (Transport.nuUnused origin _ _).trans result.2⟩
  | rep _ ih =>
      simp only [rep, Vacuous] at unused
      simp only [openedTree, labels, rep, openMarked, rename, renameArgs, liftRen]
      exact ⟨.rep (ih opened environment unused).1, .rep (ih opened environment unused).2⟩

private theorem open_weaken {Γ Δ : Ctx sig} (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {marked : ActiveMarking.Tree Bool} {process : Proc Γ} (fits : Fits marked process) :
    openMarked opened.succ (liftRen environment [.nm]) marked (weaken process) =
      weaken (openMarked opened environment marked process) := by
  rw [weaken, openMarked_rename _ _ _ fits]
  exact (openMarked_map (fun _ name => name.succ) opened environment fits).symm

private theorem equal_transport {Label : Type u} {Γ : Ctx sig} (marked : ActiveMarking.Tree Label)
    {source target : Proc Γ} (same : source = target) : Transport marked source marked target :=
  same ▸ Transport.refl marked source

private theorem origin_exchange {Label : Type u} {Γ Δ : Ctx sig}
    (opened : Var Δ .nm) (environment : Ren sig Γ Δ) (outer inner : Bool × Label)
    {marked : ActiveMarking.Tree (Bool × Label)} {body : Proc (.nm :: .nm :: Γ)}
    (fits : Fits marked body) :
    Transport (openedTree (.nu outer (.nu inner marked)))
      (openMarked opened environment (labels Prod.fst (.nu outer (.nu inner marked))) (nu (nu body)))
      (openedTree (.nu inner (.nu outer marked)))
      (openMarked opened environment (labels Prod.fst (.nu inner (.nu outer marked)))
        (nu (nu (rename swapRen body)))) ∧
    Transport (openedTree (.nu inner (.nu outer marked)))
      (openMarked opened environment (labels Prod.fst (.nu inner (.nu outer marked)))
        (nu (nu (rename swapRen body))))
      (openedTree (.nu outer (.nu inner marked)))
      (openMarked opened environment (labels Prod.fst (.nu outer (.nu inner marked))) (nu (nu body))) := by
  have booleanFits := fits_labels Prod.fst fits
  rcases outer with ⟨outer, outerLabel⟩
  rcases inner with ⟨inner, innerLabel⟩
  simp only [openedTree, labels, nu, openMarked]
  cases outer <;> cases inner <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have natural := openMarked_map (swapRen (Γ := Δ)) opened.succ.succ
        (liftRen (liftRen environment [.nm]) [.nm]) booleanFits
    rw [openMarked_rename _ _ _ booleanFits]
    have environmentEqual :
        (fun sort name => swapRen sort (liftRen (liftRen environment [.nm]) [.nm] sort name)) =
        (fun sort name => liftRen (liftRen environment [.nm]) [.nm] sort (swapRen sort name)) := by
      funext sort name
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl
    change rename swapRen (openMarked opened.succ.succ (liftRen (liftRen environment [.nm]) [.nm])
      (labels Prod.fst marked) body) =
      openMarked opened.succ.succ
        (fun sort name => swapRen sort (liftRen (liftRen environment [.nm]) [.nm] sort name))
        (labels Prod.fst marked) body at natural
    rw [environmentEqual] at natural
    exact ⟨(Transport.nuSwap outerLabel innerLabel (openedTree marked) _).trans
        (.nu innerLabel (.nu outerLabel (equal_transport _ natural))),
      (Transport.nu innerLabel (.nu outerLabel (equal_transport _ natural.symm))).trans
        (.nuSwapBack outerLabel innerLabel (openedTree marked) _)⟩
  · rw [openMarked_rename _ _ _ booleanFits]
    have same :
        openMarked opened.succ (prependRen opened.succ (liftRen environment [.nm]))
          (labels Prod.fst marked) body =
        openMarked opened.succ
          (fun sort name => liftRen (prependRen opened environment) [.nm] sort (swapRen sort name))
          (labels Prod.fst marked) body := by
      congr 1
      funext sort name
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl
    exact ⟨.nu outerLabel (equal_transport _ same), .nu outerLabel (equal_transport _ same.symm)⟩
  · rw [openMarked_rename _ _ _ booleanFits]
    have same :
        openMarked opened.succ (liftRen (prependRen opened environment) [.nm])
          (labels Prod.fst marked) body =
        openMarked opened.succ
          (fun sort name => prependRen opened.succ (liftRen environment [.nm]) sort (swapRen sort name))
          (labels Prod.fst marked) body := by
      congr 1
      funext sort name
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl
    exact ⟨.nu innerLabel (equal_transport _ same), .nu innerLabel (equal_transport _ same.symm)⟩
  · rw [openMarked_rename _ _ _ booleanFits]
    have same :
        openMarked opened (prependRen opened (prependRen opened environment))
          (labels Prod.fst marked) body =
        openMarked opened
          (fun sort name => prependRen opened (prependRen opened environment) sort (swapRen sort name))
          (labels Prod.fst marked) body := by
      congr 1
      funext sort name
      cases name with
      | zero => rfl
      | succ name => cases name <;> rfl
    exact ⟨equal_transport _ same, equal_transport _ same.symm⟩

/-- Opening retains independent prefix origins through the actual static
derivation. A copied guarded server keeps the surviving server's own labels. -/
theorem open_transport_origins {Label : Type u} {Γ Δ : Ctx sig}
    (opened : Var Δ .nm) (environment : Ren sig Γ Δ)
    {before after : ActiveMarking.Tree (Bool × Label)} {source target : Proc Γ}
    (tracked : Transport before source after target) (fits : Fits before source) (safe : Safe source) :
    Transport (openedTree before) (openMarked opened environment (labels Prod.fst before) source)
      (openedTree after) (openMarked opened environment (labels Prod.fst after) target) := by
  induction tracked generalizing Δ with
  | refl => exact .refl _ _
  | trans left right leftIH rightIH =>
      have nextFits := fits_of_labels Prod.fst _
        (transport_fits (transport_labels Prod.fst left) (fits_labels Prod.fst fits))
      exact .trans (leftIH opened environment fits safe)
        (rightIH opened environment nextFits ((safe_structural left.erase).mp safe))
  | parComm => simp only [openedTree, labels, par, openMarked]; exact .parComm _ _ _ _
  | parAssoc => simp only [openedTree, labels, par, openMarked]; exact .parAssoc _ _ _ _ _ _
  | parAssocBack => simp only [openedTree, labels, par, openMarked]; exact .parAssocBack _ _ _ _ _ _
  | parUnit => simp only [openedTree, labels, par, nil, openMarked]; exact .parUnit _ _
  | parUnitBack => simp only [openedTree, labels, par, nil, openMarked]; exact .parUnitBack _ _
  | nuUnused origin marked process =>
      cases fits with
      | nu _ weakFits =>
        have originalFits := Fits.ofRename _ process marked weakFits
        have booleanFits := fits_labels Prod.fst originalFits
        rcases origin with ⟨selected, origin⟩
        simp only [openedTree, labels, nu, openMarked]
        cases selected
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [open_weaken opened environment booleanFits]
          exact .nuUnused origin _ _
        · simp only [↓reduceIte]
          rw [weaken, openMarked_rename _ _ _ booleanFits]
          exact .refl _ _
  | nuUnusedBack origin marked process =>
      have booleanFits := fits_labels Prod.fst fits
      rcases origin with ⟨selected, origin⟩
      simp only [openedTree, labels, nu, openMarked]
      cases selected
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [open_weaken opened environment booleanFits]
        exact .nuUnusedBack origin _ _
      · simp only [↓reduceIte]
        rw [weaken, openMarked_rename _ _ _ booleanFits]
        exact .refl _ _
  | nuPar origin first second process frame =>
      cases fits with
      | par privateFits frameFits => cases privateFits with
        | nu _ bodyFits =>
          have booleanFits := fits_labels Prod.fst frameFits
          rcases origin with ⟨selected, origin⟩
          simp only [openedTree, labels, nu, par, openMarked]
          cases selected
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [open_weaken opened environment booleanFits]
            exact .nuPar origin _ _ _ _
          · simp only [↓reduceIte]
            rw [weaken, openMarked_rename _ _ _ booleanFits]
            exact .refl _ _
  | nuParBack origin first second process frame =>
      cases fits with
      | nu _ bodyFits => cases bodyFits with
        | par privateFits weakFrameFits =>
          have booleanFits := fits_labels Prod.fst (Fits.ofRename _ frame second weakFrameFits)
          rcases origin with ⟨selected, origin⟩
          simp only [openedTree, labels, nu, par, openMarked]
          cases selected
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [open_weaken opened environment booleanFits]
            exact .nuParBack origin _ _ _ _
          · simp only [↓reduceIte]
            rw [weaken, openMarked_rename _ _ _ booleanFits]
            exact .refl _ _
  | nuSwap outer inner marked process =>
      cases fits with
      | nu _ innerFits => cases innerFits with
        | nu _ bodyFits => exact (origin_exchange opened environment outer inner bodyFits).1
  | nuSwapBack outer inner marked process =>
      cases fits with
      | nu _ outerFits => cases outerFits with
        | nu _ bodyFits => exact (origin_exchange opened environment outer inner (Fits.ofRename _ process marked bodyFits)).2
  | repUnfold => simp only [openedTree, labels, rep, par, openMarked]; exact .repUnfold _ _
  | repFold copy server process =>
      cases fits with
      | par copyFits replicatedFits => cases replicatedFits with
        | rep serverFits =>
          simp only [par, rep, Safe] at safe
          have copied := vacuous_origin_open opened environment copyFits safe.2
          have serving := vacuous_origin_open opened environment serverFits safe.2
          simp only [openedTree, labels, par, rep, openMarked]
          exact (Transport.par copied.1 (Transport.rep serving.1)).trans
            ((Transport.repFold (labels Prod.snd copy) (labels Prod.snd server) _).trans
              (Transport.rep serving.2))
  | par _ _ leftIH rightIH =>
      cases fits with
      | par leftFits rightFits =>
          simp only [par, Safe] at safe
          simpa only [openedTree, labels, par, openMarked] using
            Transport.par (leftIH opened environment leftFits safe.1) (rightIH opened environment rightFits safe.2)
  | nu origin _ ih =>
      cases fits with
      | nu _ bodyFits =>
          simp only [nu, Safe] at safe
          rcases origin with ⟨selected, origin⟩
          simp only [openedTree, labels, nu, openMarked]
          cases selected
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact .nu origin (ih opened.succ (liftRen environment [.nm]) bodyFits safe)
          · simp only [↓reduceIte]
            exact ih opened (prependRen opened environment) bodyFits safe
  | inp1 origin channel body _ =>
      simpa only [openedTree, labels, inp1, openMarked, rename, renameArgs, liftRen] using
        Transport.inp1 origin.2 (rename environment channel)
          (transport_rename (liftRen environment [.nm]) (transport_labels Prod.snd body))
  | inp2 origin channel body _ =>
      simpa only [openedTree, labels, inp2, openMarked, rename, renameArgs, liftRen] using
        Transport.inp2 origin.2 (rename environment channel)
          (transport_rename (liftRen environment [.nm, .nm]) (transport_labels Prod.snd body))
  | rep tracked ih =>
      cases fits with
      | rep bodyFits =>
          simp only [rep, Safe] at safe
          simpa only [openedTree, labels, rep, openMarked] using
            Transport.rep (ih opened environment bodyFits (safe_of_vacuous _ safe))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningOrigins
