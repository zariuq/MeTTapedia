import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking

/-!
# Removing selected non-replicated prefixes preserves the static frame

Active constructor marks identify a supplied prefix before structural
rearrangement. An input's suspended body remains opaque. Removal commutes
with the actual scoped equations when the selected header is absent from
replicated bodies; that hypothesis rules out contracting a selected linear
actor with an equal persistent server. Counts retain duplicate occurrences,
in contrast to the set of available header observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActivePrefixResidual

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

universe u

/-- Every replicated active component is free of this header. Input bodies
are guarded and therefore do not contribute to the condition. -/
def repFree (header : Header) : {Γ : Ctx sig} → Proc Γ → Bool
  | _, .var _ => true
  | _, .op .nil .nil => true
  | _, .op .par (.cons first (.cons second .nil)) => repFree header first && repFree header second
  | _, .op .inp1 (.cons _ (.cons _ .nil)) => true
  | _, .op .inp2 (.cons _ (.cons _ .nil)) => true
  | _, .op .out1 (.cons _ (.cons _ .nil)) => true
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => true
  | _, .op .nu (.cons body .nil) => repFree header body
  | _, .op .rep (.cons body .nil) => !visible header body
termination_by _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem repFree_of_not_visible (header : Header) : ∀ {Γ : Ctx sig} (process : Proc Γ),
    visible header process = false → repFree header process = true
  | _, .var _, _ => by simp only [repFree]
  | _, .op .nil .nil, _ => by simp only [repFree]
  | _, .op .par (.cons first (.cons second .nil)), absent => by
      simp only [visible, Bool.or_eq_false_iff] at absent
      simp only [repFree, repFree_of_not_visible header first absent.1,
        repFree_of_not_visible header second absent.2, Bool.true_and]
  | _, .op .inp1 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, .op .inp2 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, .op .out1 (.cons _ (.cons _ .nil)), _ => by simp only [repFree]
  | _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))), _ => by simp only [repFree]
  | _, .op .nu (.cons body .nil), absent => by
      simp only [repFree]
      apply repFree_of_not_visible header body
      simpa only [visible] using absent
  | _, .op .rep (.cons body .nil), absent => by
      simp only [visible] at absent
      simp only [repFree, absent, Bool.not_false]
termination_by _ process _ => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem repFree_rename (header : Header) : ∀ {Γ Δ : Ctx sig}
    (environment : Ren sig Γ Δ) (process : Proc Γ),
    repFree header (rename environment process) = repFree header process
  | _, _, _, .var _ => by simp only [rename, repFree]
  | _, _, _, .op .nil .nil => by simp only [rename, renameArgs, repFree]
  | _, _, environment, .op .par (.cons first (.cons second .nil)) => by
      simp only [rename, renameArgs, liftRen, repFree]
      rw [repFree_rename header environment first, repFree_rename header environment second]
  | _, _, _, .op .inp1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, .op .inp2 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, .op .out1 (.cons _ (.cons _ .nil)) => by simp only [rename, renameArgs, repFree]
  | _, _, _, .op .out2 (.cons _ (.cons _ (.cons _ .nil))) => by
      simp only [rename, renameArgs, repFree]
  | _, _, environment, .op .nu (.cons body .nil) => by
      simp only [rename, renameArgs, repFree]
      exact repFree_rename header (liftRen environment [.nm]) body
  | _, _, environment, .op .rep (.cons body .nil) => by
      simp only [rename, renameArgs, liftRen, repFree, visible_rename]
termination_by _ _ _ process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

/-- The absence of a selected header in persistent bodies belongs to the
actual structural class, including both directions of server unfolding. -/
theorem repFree_structural {Γ : Ctx sig} (header : Header) {p q : Proc Γ}
    (equal : StructuralEq p q) : repFree header p = repFree header q := by
  induction equal with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | parComm p q => simpa only [par, repFree] using Bool.and_comm (repFree header p) (repFree header q)
  | parAssoc p q r => simpa only [par, repFree] using Bool.and_assoc (repFree header p) (repFree header q) (repFree header r)
  | parUnit p => simp only [par, nil, repFree, Bool.and_true]
  | nuUnused p => simpa only [nu, repFree, weaken] using repFree_rename header (fun _ name => .succ name) p
  | nuPar p q => simp only [nu, par, repFree, weaken, repFree_rename]
  | nuSwap p => simpa only [nu, repFree] using (repFree_rename header swapRen p).symm
  | repUnfold p =>
      cases present : visible header p with
      | false => simp only [rep, par, repFree, present, Bool.not_false,
          repFree_of_not_visible header p present, Bool.true_and]
      | true => simp only [rep, par, repFree, present, Bool.not_true, Bool.and_false]
  | par _ _ firstIH secondIH => simpa only [par, repFree] using congrArg₂ Bool.and firstIH secondIH
  | nu _ ih => simpa only [nu, repFree] using ih
  | inp1 => simp only [inp1, repFree]
  | inp2 => simp only [inp2, repFree]
  | rep h _ => simpa only [rep, repFree] using congrArg Bool.not (visible_structural header h)

/-- Number of active occurrences with this header and origin outside servers.
Prefix bodies remain suspended and server copies are not counted as linear. -/
def count {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    ActiveMarking.Tree Label → Nat
  | .var | .nil | .rep _ => 0
  | .par first second => count header origin first + count header origin second
  | .nu _ body => count header origin body
  | .inp1 label _ => if header = .input1 ∧ origin = label then 1 else 0
  | .inp2 label _ => if header = .input2 ∧ origin = label then 1 else 0
  | .out1 label => if header = .output1 ∧ origin = label then 1 else 0
  | .out2 label => if header = .output2 ∧ origin = label then 1 else 0

theorem count_of_not_visible {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) (absent : visible header process = false) :
    count header origin marked = 0 := by
  induction fits with
  | var => rfl
  | nil => rfl
  | par _ _ firstIH secondIH =>
      simp only [par, visible, Bool.or_eq_false_iff] at absent
      simp only [count, firstIH absent.1, secondIH absent.2, Nat.zero_add]
  | inp1 => cases header <;> simp_all [inp1, visible, count]
  | inp2 => cases header <;> simp_all [inp2, visible, count]
  | out1 => cases header <;> simp_all [out1, visible, count]
  | out2 => cases header <;> simp_all [out2, visible, count]
  | nu _ _ ih => exact ih (by simpa only [nu, visible] using absent)
  | rep => rfl

/-- Static transport also transports constructor shape at its exact endpoint. -/
theorem transport_fits {Label : Type u} {Γ : Ctx sig} {m n : ActiveMarking.Tree Label}
    {p q : Proc Γ} (tracked : Transport m p n q) (fits : Fits m p) : Fits n q := by
  induction tracked with
  | refl => exact fits
  | trans _ _ firstIH secondIH => exact secondIH (firstIH fits)
  | parComm => cases fits with | par first second => exact .par second first
  | parAssoc => cases fits with | par first third => cases first with | par first second => exact .par first (.par second third)
  | parAssocBack => cases fits with | par first last => cases last with | par second third => exact .par (.par first second) third
  | parUnit => cases fits with | par first last => exact first
  | parUnitBack => exact .par fits .nil
  | nuUnused => cases fits with | nu _ body => exact body.ofRename _ _ _
  | nuUnusedBack origin => exact .nu origin (fits.rename _)
  | nuPar origin => cases fits with | par left right => cases left with | nu _ body => exact .nu origin (.par body (right.rename _))
  | nuParBack => cases fits with | nu _ inside => cases inside with | par body frame => exact .par (.nu _ body) (frame.ofRename _ _ _)
  | nuSwap outer inner => cases fits with | nu _ inside => cases inside with | nu _ body => exact .nu inner (.nu outer (body.rename _))
  | nuSwapBack outer inner => cases fits with | nu _ inside => cases inside with | nu _ body => exact .nu outer (.nu inner (body.ofRename _ _ _))
  | repUnfold => cases fits with | rep body => exact .par body (.rep body)
  | repFold => cases fits with | par copy server => exact server
  | par _ _ firstIH secondIH => cases fits with | par first second => exact .par (firstIH first) (secondIH second)
  | nu origin _ ih => cases fits with | nu _ body => exact .nu origin (ih body)
  | inp1 origin channel _ ih => cases fits with | inp1 _ _ body => exact .inp1 origin channel (ih body)
  | inp2 origin channel _ ih => cases fits with | inp2 _ _ body => exact .inp2 origin channel (ih body)
  | rep _ ih => cases fits with | rep body => exact .rep (ih body)

/-- Real structural rearrangement preserves the number of selected linear
actors, rather than only their availability. -/
theorem count_transport {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) {Γ : Ctx sig} {m n : ActiveMarking.Tree Label} {p q : Proc Γ}
    (tracked : Transport m p n q) (fits : Fits m p) (safe : repFree header p = true) :
    count header origin m = count header origin n := by
  induction tracked with
  | refl => rfl
  | trans first second firstIH secondIH =>
      exact (firstIH fits safe).trans (secondIH (transport_fits first fits)
        ((repFree_structural header first.erase).symm.trans safe))
  | parComm => simp only [count, Nat.add_comm]
  | parAssoc => simp only [count, Nat.add_assoc]
  | parAssocBack => simp only [count, Nat.add_assoc]
  | parUnit => simp only [count, Nat.add_zero]
  | parUnitBack => simp only [count, Nat.add_zero]
  | nuUnused => rfl
  | nuUnusedBack => rfl
  | nuPar => rfl
  | nuParBack => rfl
  | nuSwap => rfl
  | nuSwapBack => rfl
  | repUnfold =>
      cases fits with
      | rep body =>
          simp only [rep, repFree, Bool.not_eq_true'] at safe
          simp only [count, count_of_not_visible header origin body safe, Nat.zero_add]
  | repFold =>
      cases fits with
      | par copy server =>
          simp only [par, rep, repFree, Bool.and_eq_true, Bool.not_eq_true'] at safe
          simp only [count, count_of_not_visible header origin copy safe.2, Nat.zero_add]
  | par first second firstIH secondIH =>
      cases fits with
      | par firstFits secondFits =>
          simp only [par, repFree, Bool.and_eq_true] at safe
          simp only [count, firstIH firstFits safe.1, secondIH secondFits safe.2]
  | nu origin _ ih => cases fits with | nu _ body => exact ih body (by simpa only [nu, repFree] using safe)
  | inp1 => rfl
  | inp2 => rfl
  | rep => rfl

/-- Remove only the selected active prefix from the constructor marking.
Stored continuations and entire persistent servers are retained. -/
def cutTree {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    ActiveMarking.Tree Label → ActiveMarking.Tree Label
  | .var => .var
  | .nil => .nil
  | .par first second => .par (cutTree header origin first) (cutTree header origin second)
  | .nu label body => .nu label (cutTree header origin body)
  | .inp1 label body => if header = .input1 ∧ origin = label then .nil else .inp1 label body
  | .inp2 label body => if header = .input2 ∧ origin = label then .nil else .inp2 label body
  | .out1 label => if header = .output1 ∧ origin = label then .nil else .out1 label
  | .out2 label => if header = .output2 ∧ origin = label then .nil else .out2 label
  | .rep body => .rep body

theorem cutTree_of_count_zero {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) (marked : ActiveMarking.Tree Label) (zero : count header origin marked = 0) :
    cutTree header origin marked = marked := by
  induction marked with
  | var => rfl
  | nil => rfl
  | par first second firstIH secondIH =>
      simp only [count] at zero
      simp only [cutTree, firstIH (by omega), secondIH (by omega)]
  | nu label body ih => simpa only [cutTree] using congrArg (ActiveMarking.Tree.nu label) (ih zero)
  | inp1 => simp_all only [count, cutTree]; split <;> simp_all
  | inp2 => simp_all only [count, cutTree]; split <;> simp_all
  | out1 => simp_all only [count, cutTree]; split <;> simp_all
  | out2 => simp_all only [count, cutTree]; split <;> simp_all
  | rep => rfl

/-- Erase a real selected linear prefix, retaining every unselected process
and every duplicate in the active parallel tree. -/
def remove {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    {Γ : Ctx sig} → ActiveMarking.Tree Label → Proc Γ → Proc Γ
  | _, _, .var name => .var name
  | _, _, .op .nil .nil => nil
  | _, marked, .op .par (.cons first (.cons second .nil)) => match marked with
      | .par left right => par (remove header origin left first) (remove header origin right second)
      | _ => par first second
  | _, marked, .op .inp1 (.cons channel (.cons body .nil)) => match marked with
      | .inp1 label _ => if header = .input1 ∧ origin = label then nil else inp1 channel body
      | _ => inp1 channel body
  | _, marked, .op .inp2 (.cons channel (.cons body .nil)) => match marked with
      | .inp2 label _ => if header = .input2 ∧ origin = label then nil else inp2 channel body
      | _ => inp2 channel body
  | _, marked, .op .out1 (.cons channel (.cons datum .nil)) => match marked with
      | .out1 label => if header = .output1 ∧ origin = label then nil else out1 channel datum
      | _ => out1 channel datum
  | _, marked, .op .out2 (.cons channel (.cons first (.cons second .nil))) => match marked with
      | .out2 label => if header = .output2 ∧ origin = label then nil else out2 channel first second
      | _ => out2 channel first second
  | _, marked, .op .nu (.cons body .nil) => match marked with
      | .nu _ inner => nu (remove header origin inner body)
      | _ => nu body
  | _, _, .op .rep (.cons body .nil) => rep body
termination_by _ _marked process => termSize process
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem remove_of_count_zero {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) (zero : count header origin marked = 0) :
    remove header origin marked process = process := by
  induction fits with
  | var => simp only [remove]
  | nil => simp only [nil, remove]
  | par _ _ firstIH secondIH =>
      simp only [count] at zero
      simp only [par, remove]
      rw [firstIH (by omega), secondIH (by omega)]
  | inp1 => simp_all only [count, remove, inp1]; split <;> simp_all
  | inp2 => simp_all only [count, remove, inp2]; split <;> simp_all
  | out1 => simp_all only [count, remove, out1]; split <;> simp_all
  | out2 => simp_all only [count, remove, out2]; split <;> simp_all
  | nu _ _ ih => simpa only [nu, remove] using congrArg nu (ih zero)
  | rep => simp only [rep, remove]

theorem remove_fits {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) : Fits (cutTree header origin marked) (remove header origin marked process) := by
  induction fits with
  | var name => simpa only [cutTree, remove] using Fits.var (Label := Label) name
  | nil => simpa only [nil, cutTree, remove] using (Fits.nil : Fits (ActiveMarking.Tree.nil : ActiveMarking.Tree Label) (nil : Proc _))
  | par _ _ firstIH secondIH => simpa only [par, remove, cutTree] using Fits.par firstIH secondIH
  | inp1 label channel body =>
      simp only [inp1, remove, cutTree]
      split
      · exact .nil
      · exact .inp1 label channel body
  | inp2 label channel body =>
      simp only [inp2, remove, cutTree]
      split
      · exact .nil
      · exact .inp2 label channel body
  | out1 label channel datum =>
      simp only [out1, remove, cutTree]
      split
      · exact .nil
      · exact .out1 label channel datum
  | out2 label channel first second =>
      simp only [out2, remove, cutTree]
      split
      · exact .nil
      · exact .out2 label channel first second
  | nu label _ ih => simpa only [nu, remove, cutTree] using Fits.nu label ih
  | rep body => simpa only [cutTree, rep, remove] using Fits.rep body

theorem remove_rename {Label : Type u} [DecidableEq Label] (header : Header)
    (origin : Label) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) {Δ : Ctx sig} (environment : Ren sig Γ Δ) :
    remove header origin marked (rename environment process) =
      rename environment (remove header origin marked process) := by
  induction fits generalizing Δ with
  | var => simp only [rename, remove]
  | nil => simp only [nil, rename, renameArgs, remove]
  | par _ _ firstIH secondIH =>
      simp only [par, rename, renameArgs, liftRen, remove]
      rw [firstIH environment, secondIH environment]
  | inp1 =>
      simp only [inp1, rename, renameArgs, remove]
      split <;> simp only [nil, rename, renameArgs]
  | inp2 =>
      simp only [inp2, rename, renameArgs, remove]
      split <;> simp only [nil, rename, renameArgs]
  | out1 =>
      simp only [out1, rename, renameArgs, remove]
      split <;> simp only [nil, rename, renameArgs]
  | out2 =>
      simp only [out2, rename, renameArgs, remove]
      split <;> simp only [nil, rename, renameArgs]
  | nu _ _ ih =>
      simp only [nu, rename, renameArgs, remove]
      rw [ih (liftRen environment [.nm])]
  | rep => simp only [rep, rename, renameArgs, remove]

theorem repFree_remove {Label : Type u} [DecidableEq Label] (header removed : Header)
    (origin : Label) {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) :
    repFree header (remove removed origin marked process) = repFree header process := by
  induction fits with
  | var => simp only [remove]
  | nil => simp only [nil, remove]
  | par _ _ firstIH secondIH => simp only [par, remove, repFree, firstIH, secondIH]
  | inp1 => simp only [inp1, remove]; split <;> simp only [nil, repFree]
  | inp2 => simp only [inp2, remove]; split <;> simp only [nil, repFree]
  | out1 => simp only [out1, remove]; split <;> simp only [nil, repFree]
  | out2 => simp only [out2, remove]; split <;> simp only [nil, repFree]
  | nu _ _ ih => simpa only [nu, remove, repFree] using ih
  | rep => simp only [rep, remove]

/-- Removing a selected linear prefix follows the same actual scoped
equations. Congruence inside guarded bodies is retained without pretending
that a guarded body's syntax has been decoded literally. -/
theorem remove_transport {Label : Type u} [DecidableEq Label] (header : Header)
    (chosen : Label) {Γ : Ctx sig} {m n : ActiveMarking.Tree Label} {p q : Proc Γ}
    (tracked : Transport m p n q) (fits : Fits m p) (safe : repFree header p = true) :
    Transport (cutTree header chosen m) (remove header chosen m p)
      (cutTree header chosen n) (remove header chosen n q) := by
  induction tracked with
  | refl => exact .refl _ _
  | trans first second firstIH secondIH =>
      exact .trans (firstIH fits safe) (secondIH (transport_fits first fits)
        ((repFree_structural header first.erase).symm.trans safe))
  | parComm => simpa only [cutTree, par, remove] using (Transport.parComm _ _ _ _)
  | parAssoc => simpa only [cutTree, par, remove] using (Transport.parAssoc _ _ _ _ _ _)
  | parAssocBack => simpa only [cutTree, par, remove] using (Transport.parAssocBack _ _ _ _ _ _)
  | parUnit => simpa only [cutTree, par, nil, remove] using (Transport.parUnit _ _)
  | parUnitBack => simpa only [cutTree, par, nil, remove] using (Transport.parUnitBack _ _)
  | nuUnused origin marked process =>
      cases fits with
      | nu _ body =>
          have fitP := Fits.ofRename (fun _ name => .succ name) process marked body
          simp only [cutTree, nu, remove, weaken]
          rw [remove_rename header chosen fitP]
          exact .nuUnused origin _ _
  | nuUnusedBack origin marked process =>
      simp only [cutTree, nu, remove, weaken]
      rw [remove_rename header chosen fits]
      exact .nuUnusedBack origin _ _
  | nuPar origin first second process frame =>
      cases fits with
      | par left right =>
          simp only [cutTree, par, nu, remove, weaken]
          rw [remove_rename header chosen right]
          exact .nuPar origin _ _ _ _
  | nuParBack origin first second process frame =>
      cases fits with
      | nu _ inside => cases inside with
          | par body frameFits =>
              have fitF := Fits.ofRename (fun _ name => .succ name) frame second frameFits
              simp only [cutTree, par, nu, remove, weaken]
              rw [remove_rename header chosen fitF]
              exact .nuParBack origin _ _ _ _
  | nuSwap outer inner marked process =>
      cases fits with
      | nu _ inside => cases inside with
          | nu _ body =>
              simp only [cutTree, nu, remove]
              rw [remove_rename header chosen body]
              exact .nuSwap outer inner _ _
  | nuSwapBack outer inner marked process =>
      cases fits with
      | nu _ inside => cases inside with
          | nu _ body =>
              have fitP := Fits.ofRename swapRen process marked body
              simp only [cutTree, nu, remove]
              rw [remove_rename header chosen fitP]
              exact .nuSwapBack outer inner _ _
  | repUnfold marked process =>
      cases fits with
      | rep body =>
          simp only [rep, repFree, Bool.not_eq_true'] at safe
          have zero := count_of_not_visible header chosen body safe
          simp only [cutTree, rep, par, remove, cutTree_of_count_zero header chosen marked zero,
            remove_of_count_zero header chosen body zero]
          exact .repUnfold _ _
  | repFold copy server process =>
      cases fits with
      | par copyFits serverFits =>
          simp only [par, rep, repFree, Bool.and_eq_true, Bool.not_eq_true'] at safe
          have zero := count_of_not_visible header chosen copyFits safe.2
          simp only [cutTree, rep, par, remove, cutTree_of_count_zero header chosen copy zero,
            remove_of_count_zero header chosen copyFits zero]
          exact .repFold _ _ _
  | par first second firstIH secondIH =>
      cases fits with
      | par firstFits secondFits =>
          simp only [par, repFree, Bool.and_eq_true] at safe
          simpa only [cutTree, par, remove] using
            Transport.par (firstIH firstFits safe.1) (secondIH secondFits safe.2)
  | nu origin _ ih =>
      cases fits with
      | nu _ body =>
          simpa only [cutTree, nu, remove] using
            Transport.nu origin (ih body (by simpa only [nu, repFree] using safe))
  | inp1 origin channel original _ =>
      simp only [cutTree, inp1, remove]
      split
      · exact .refl _ _
      · exact .inp1 origin channel original
  | inp2 origin channel original _ =>
      simp only [cutTree, inp2, remove]
      split
      · exact .refl _ _
      · exact .inp2 origin channel original
  | rep original _ => simpa only [cutTree, rep, remove] using Transport.rep original

theorem count_scope {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    ∀ {Γ Δ : Ctx sig} {scope : Scope Γ Δ} (binders : ScopeMarks Label scope)
      (marked : ActiveMarking.Tree Label), count header origin (binders.close marked) = count header origin marked
  | _, _, _, .nil, _ => rfl
  | _, _, _, .bind _ rest, marked => count_scope header origin rest marked

theorem remove_scope {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    ∀ {Γ Δ : Ctx sig} {scope : Scope Γ Δ} (binders : ScopeMarks Label scope)
      (marked : ActiveMarking.Tree Label) (process : Proc Δ),
      remove header origin (binders.close marked) (scope.close process) =
        scope.close (remove header origin marked process)
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .bind _ rest, marked, process => by
      simp only [ScopeMarks.close, Scope.close, nu, remove]
      exact congrArg nu (remove_scope header origin rest marked process)

theorem count_cutTree_other {Label : Type u} [DecidableEq Label] (kept removed : Header)
    (chosen erased : Label) (different : kept ≠ removed) (marked : ActiveMarking.Tree Label) :
    count kept chosen (cutTree removed erased marked) = count kept chosen marked := by
  induction marked with
  | var => rfl
  | nil => rfl
  | par _ _ firstIH secondIH => simp only [cutTree, count, firstIH, secondIH]
  | nu _ _ ih => simpa only [cutTree, count] using ih
  | inp1 => simp only [cutTree]; split <;> simp_all [count]
  | inp2 => simp only [cutTree]; split <;> simp_all [count]
  | out1 => simp only [cutTree]; split <;> simp_all [count]
  | out2 => simp only [cutTree]; split <;> simp_all [count]
  | rep => rfl

theorem cutTree_scope {Label : Type u} [DecidableEq Label] (header : Header) (origin : Label) :
    ∀ {Γ Δ : Ctx sig} {scope : Scope Γ Δ} (binders : ScopeMarks Label scope)
      (marked : ActiveMarking.Tree Label),
      cutTree header origin (binders.close marked) = binders.close (cutTree header origin marked)
  | _, _, _, .nil, _ => rfl
  | _, _, _, .bind label rest, marked => by
      simp only [ScopeMarks.close, cutTree]
      exact congrArg (ActiveMarking.Tree.nu label) (cutTree_scope header origin rest marked)

/-- For a supplied binary firing, unique selected linear origins determine
the actual untouched frame, modulo exactly the same private telescope.
The frame may contain arbitrarily many other actors and persistent servers. -/
theorem binary_frame_residual {Label : Type u} [DecidableEq Label] {Γ : Ctx sig}
    {marked : ActiveMarking.Tree Label} {source target : Proc Γ}
    (fits : Fits marked source) (exposure : Exposure source target)
    (traced : TracedExposure marked exposure)
    (binary : inputHeader exposure.selected = .input2)
    (safeInput : repFree .input2 source = true) (safeOutput : repFree .output2 source = true)
    (uniqueInput : count .input2 traced.continuation.inputOrigin marked ≤ 1)
    (uniqueOutput : count .output2 traced.continuation.outputOrigin marked ≤ 1) :
    StructuralEq
      (remove .output2 traced.continuation.outputOrigin
        (cutTree .input2 traced.continuation.inputOrigin marked)
        (remove .input2 traced.continuation.inputOrigin marked source))
      (exposure.scope.close exposure.frame) := by
  have inputCount := count_transport .input2 traced.continuation.inputOrigin traced.transport fits safeInput
  have outputCount := count_transport .output2 traced.continuation.outputOrigin traced.transport fits safeOutput
  have cutInput := remove_transport .input2 traced.continuation.inputOrigin traced.transport fits safeInput
  have cutBoth := remove_transport .output2 traced.continuation.outputOrigin cutInput
    (remove_fits .input2 traced.continuation.inputOrigin fits)
    ((repFree_remove .output2 .input2 traced.continuation.inputOrigin fits).trans safeOutput)
  rcases exposure with ⟨world, scope, redex, reduct, selected, frame, before, after⟩
  rcases traced with ⟨binders, redexMarks, frameMarks, communication, frameFits,
    transportedFits, tracked, originalInput, originalOutput⟩
  cases selected with
  | unary => simp only [inputHeader] at binary; cases binary
  | binary channel first second body =>
    cases communication with
    | binary _ _ _ _ outputOrigin inputOrigin continuation bodyFits =>
      simp only [MarkedCommunication.inputOrigin, MarkedCommunication.outputOrigin,
        count_scope, count] at inputCount outputCount uniqueInput uniqueOutput
      have frameInput : count .input2 inputOrigin frameMarks = 0 := by
        simp at inputCount
        omega
      have frameOutput : count .output2 outputOrigin frameMarks = 0 := by
        simp at outputCount
        omega
      have removeInputFrame := remove_of_count_zero .input2 inputOrigin frameFits frameInput
      have cutInputFrame := cutTree_of_count_zero .input2 inputOrigin frameMarks frameInput
      have removeOutputFrame := remove_of_count_zero .output2 outputOrigin frameFits frameOutput
      have exactResidual := cutBoth.erase
      simp only [MarkedCommunication.inputOrigin, MarkedCommunication.outputOrigin,
        cutTree_scope, remove_scope, par, inp2, out2, remove, cutTree] at exactResidual
      simp only [removeInputFrame, cutInputFrame, removeOutputFrame] at exactResidual
      simp [remove, nil] at exactResidual
      exact .trans exactResidual (scope.congr
        (.trans (.par (.parUnit nil) (.refl frame))
          (.trans (.parComm _ _) (.parUnit frame))))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActivePrefixResidual
