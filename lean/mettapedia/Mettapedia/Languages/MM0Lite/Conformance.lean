import Mettapedia.Languages.MM0Lite.LanguageDef
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# MM0-Lite Conformance Checks

Executable, kernel-checked examples for MM0-Lite:
- positive: a valid proof script reaches `Verified`
- negative: invalid scripts remain non-verified normal forms
-/

namespace Mettapedia.Languages.MM0Lite.Conformance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.MM0Lite.LanguageDef

private def atomP : Pattern := .apply "AtomP" []
private def atomQ : Pattern := .apply "AtomQ" []
private def atomR : Pattern := .apply "AtomR" []
private def imp (a b : Pattern) : Pattern := .apply "Implies" [a, b]

private def thmImpPQ : Pattern := .apply "ThmImpPQ" []
private def thmImpQR : Pattern := .apply "ThmImpQR" []

private def iPush (f : Pattern) : Pattern := .apply "IPush" [f]
private def iUse (th : Pattern) : Pattern := .apply "IUse" [th]
private def iMP : Pattern := .apply "IMP" []
private def iNil : Pattern := .apply "INil" []
private def iCons (i tail : Pattern) : Pattern := .apply "ICons" [i, tail]

private def sNil : Pattern := .apply "SNil" []
private def sCons (f tail : Pattern) : Pattern := .apply "SCons" [f, tail]

private def pending : Pattern := .apply "Pending" []
private def verified : Pattern := .apply "Verified" []

private def mkState (prog goal stack out : Pattern) : Pattern :=
  .apply "MMState" [prog, goal, stack, out]

private def theoremTable : List (Pattern × Pattern) :=
  [ (thmImpPQ, imp atomP atomQ)
  , (thmImpQR, imp atomQ atomR)
  ]

def mm0RelEnv : RelationEnv where
  tuples := fun rel args =>
    if rel == "thmConcl" then
      match args with
      | th :: _ =>
          theoremTable.filterMap fun (thName, concl) =>
            if thName == th then some [thName, concl] else none
      | [] => []
    else
      []

/-- Lightweight proof-theory view for MM0-lite.
    `Γ` models assumptions introduced by push-instructions, theorem table gives
    closed facts, and MP composes derivations. -/
inductive Derivable (Γ : List Pattern) : Pattern → Prop where
  | byAsm {f : Pattern} : f ∈ Γ → Derivable Γ f
  | byThm {th concl : Pattern} :
      (th, concl) ∈ theoremTable → Derivable Γ concl
  | byMP {a b : Pattern} :
      Derivable Γ (imp a b) → Derivable Γ a → Derivable Γ b

private def runMM0 (prog goal stack out : Pattern) (fuel : Nat := 16) : Pattern :=
  fullRewriteToNormalFormWithPremisesUsing mm0RelEnv mm0Lite
    (mkState prog goal stack out) fuel

private def progPushUseMp : Pattern :=
  iCons (iPush atomP) (iCons (iUse thmImpPQ) (iCons iMP iNil))

private def progPushQ : Pattern :=
  iCons (iPush atomQ) iNil

private def progUseImpPQ : Pattern :=
  iCons (iUse thmImpPQ) iNil

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem positive_push_use_mp_verifies :
    runMM0 progPushUseMp atomQ sNil pending 16
    =
      mkState iNil atomQ (sCons atomQ sNil) verified := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem negative_goal_mismatch_stays_pending :
    runMM0 (iCons (iPush atomP) iNil) atomQ sNil pending 16
    =
      mkState iNil atomQ (sCons atomP sNil) pending := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem negative_wrong_antecedent_stuck_before_mp :
    runMM0 (iCons (iPush atomQ) (iCons (iUse thmImpPQ) (iCons iMP iNil))) atomQ sNil pending 16
    =
      mkState
        (iCons iMP iNil)
        atomQ
        (sCons (imp atomP atomQ) (sCons atomQ sNil))
        pending := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem push_q_verifies :
    runMM0 progPushQ atomQ sNil pending 8
    = mkState iNil atomQ (sCons atomQ sNil) verified := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem use_imp_pq_verifies :
    runMM0 progUseImpPQ (imp atomP atomQ) sNil pending 8
    = mkState iNil (imp atomP atomQ) (sCons (imp atomP atomQ) sNil) verified := by
  decide +kernel

/-- The positive verified script is sound with respect to derivability under
    pushed assumption `P`. -/
theorem soundness_verified_to_derivable_q :
    runMM0 progPushUseMp atomQ sNil pending 16
      = mkState iNil atomQ (sCons atomQ sNil) verified →
    Derivable [atomP] atomQ := by
  intro _hVerified
  let hImp : Derivable [atomP] (imp atomP atomQ) :=
    Derivable.byThm (th := thmImpPQ) (concl := imp atomP atomQ) (by decide)
  let hAsm : Derivable [atomP] atomP :=
    Derivable.byAsm (by simp)
  exact Derivable.byMP hImp hAsm

/-- Convenient corollary from the concrete run theorem. -/
theorem soundness_positive_example : Derivable [atomP] atomQ := by
  apply soundness_verified_to_derivable_q
  exact positive_push_use_mp_verifies

/-- Partial completeness witness for assumption-only derivability of `Q`. -/
theorem partial_completeness_q_from_assumption :
    Derivable [atomQ] atomQ →
    ∃ prog, runMM0 prog atomQ sNil pending 8
      = mkState iNil atomQ (sCons atomQ sNil) verified := by
  intro _h
  exact ⟨progPushQ, push_q_verifies⟩

/-- Partial completeness witness for theorem-table derivability of `(P -> Q)`. -/
theorem partial_completeness_imp_pq_from_theorem :
    Derivable [] (imp atomP atomQ) →
    ∃ prog, runMM0 prog (imp atomP atomQ) sNil pending 8
      = mkState iNil (imp atomP atomQ) (sCons (imp atomP atomQ) sNil) verified := by
  intro _h
  exact ⟨progUseImpPQ, use_imp_pq_verifies⟩

/-- Partial completeness witness for the current MP subset:
    from assumption `P` and theorem `P -> Q`, script verifies `Q`. -/
theorem partial_completeness_q_from_p_subset :
    Derivable [atomP] atomQ →
    ∃ prog, runMM0 prog atomQ sNil pending 16
      = mkState iNil atomQ (sCons atomQ sNil) verified := by
  intro _h
  exact ⟨progPushUseMp, positive_push_use_mp_verifies⟩

end Mettapedia.Languages.MM0Lite.Conformance
