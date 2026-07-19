import Mettapedia.Languages.Metamath.MMLean4Bridge

/-!
# Exact successful graph of the live Metamath hypothesis checker

`Metamath.Kernel.CheckHypOK` mirrors the successful branches of the executable
`DB.checkHyp`, and `checkHyp_complete` already proves the completeness
direction.  This module proves the missing reflection direction, yielding an
iff rather than treating the mirror relation as an unchecked precondition.
-/

namespace Mettapedia.Languages.Metamath.InferenceCheckHypGraph

open Mettapedia.Languages.Metamath.MMLean4Bridge

/-- Every successful live hypothesis check exposes all conditions in the
explicit recursive `CheckHypOK` relation. -/
theorem checkHypOK_of_checkHyp_ok
    (db : RuntimeDB) (hyps : Array String) (stack : Array RuntimeFormula)
    (off : { offset : Nat // offset + hyps.size = stack.size })
    (i : Nat)
    (substitutionIn substitutionOut :
      Std.HashMap String RuntimeFormula)
    (hsuccess :
      db.checkHyp hyps stack off i substitutionIn =
        .ok substitutionOut) :
    Metamath.Kernel.CheckHypOK db hyps stack off i
      substitutionIn substitutionOut := by
  generalize hfuel : hyps.size - i = fuel
  revert i substitutionIn substitutionOut hsuccess hfuel
  induction fuel with
  | zero =>
      intro i substitutionIn substitutionOut hsuccess hfuel
      have hge : ¬ i < hyps.size := by omega
      have hresult :=
        Metamath.Verify.DB.checkHyp_base
          db hyps stack off i substitutionIn hge
      rw [hresult] at hsuccess
      have hout : substitutionOut = substitutionIn :=
        Except.ok.inj hsuccess.symm
      simp [Metamath.Kernel.CheckHypOK, hge, hout]
  | succ fuel ih =>
      intro i substitutionIn substitutionOut hsuccess hfuel
      have hlt : i < hyps.size := by omega
      cases hfind : db.find? hyps[i] with
      | none =>
          unfold Metamath.Verify.DB.checkHyp at hsuccess
          simp only [hlt, dif_pos] at hsuccess
          rw [hfind] at hsuccess
          by_cases hhead : stack[off.1 + i].hasConstHead
          · simp [hhead] at hsuccess
          · simp [hhead] at hsuccess
      | some object =>
          cases object with
          | const name =>
              unfold Metamath.Verify.DB.checkHyp at hsuccess
              simp only [hlt, dif_pos] at hsuccess
              rw [hfind] at hsuccess
              by_cases hhead : stack[off.1 + i].hasConstHead
              · simp [hhead] at hsuccess
              · simp [hhead] at hsuccess
          | var name =>
              unfold Metamath.Verify.DB.checkHyp at hsuccess
              simp only [hlt, dif_pos] at hsuccess
              rw [hfind] at hsuccess
              by_cases hhead : stack[off.1 + i].hasConstHead
              · simp [hhead] at hsuccess
              · simp [hhead] at hsuccess
          | assert formula frame label =>
              unfold Metamath.Verify.DB.checkHyp at hsuccess
              simp only [hlt, dif_pos] at hsuccess
              rw [hfind] at hsuccess
              by_cases hhead : stack[off.1 + i].hasConstHead
              · simp [hhead] at hsuccess
              · simp [hhead] at hsuccess
          | hyp essential formula label =>
              cases essential with
              | false =>
                  have hequation :=
                    Metamath.Verify.DB.checkHyp_step_hyp_false
                      db hyps stack off i substitutionIn formula label
                        hlt hfind
                  rw [hequation] at hsuccess
                  have hhead : stack[off.1 + i]!.hasConstHead = true := by
                    cases hvalue : stack[off.1 + i]!.hasConstHead with
                    | false => simp [hvalue] at hsuccess
                    | true => rfl
                  have hshape : formula.isFloatShape = true := by
                    cases hvalue : formula.isFloatShape with
                    | false => simp [hhead, hvalue] at hsuccess
                    | true => rfl
                  have htypecode :
                      (formula[0]! == stack[off.1 + i]![0]!) = true := by
                    cases hvalue :
                        (formula[0]! == stack[off.1 + i]![0]!) with
                    | false => simp [hhead, hshape, hvalue] at hsuccess
                    | true => rfl
                  have hduplicate :
                      substitutionIn.contains formula[1]!.value = false := by
                    cases hvalue :
                        substitutionIn.contains formula[1]!.value with
                    | false => rfl
                    | true =>
                        simp [hhead, hshape, htypecode, hvalue] at hsuccess
                  have htail :
                      db.checkHyp hyps stack off (i + 1)
                          (substitutionIn.insert formula[1]!.value
                            (stack[off.1 + i]!)) =
                        .ok substitutionOut := by
                    simpa [hhead, hshape, htypecode, hduplicate] using hsuccess
                  have hfuelTail : hyps.size - (i + 1) = fuel := by omega
                  have htailOK :=
                    ih (i + 1)
                      (substitutionIn.insert formula[1]!.value
                        (stack[off.1 + i]!))
                      substitutionOut htail hfuelTail
                  unfold Metamath.Kernel.CheckHypOK
                  simp [hlt, hfind, hhead, hshape, htypecode, hduplicate,
                    htailOK]
              | true =>
                  have hequation :=
                    Metamath.Verify.DB.checkHyp_step_hyp_true
                      db hyps stack off i substitutionIn formula label
                        hlt hfind
                  rw [hequation] at hsuccess
                  have hhead : stack[off.1 + i]!.hasConstHead = true := by
                    cases hvalue : stack[off.1 + i]!.hasConstHead with
                    | false => simp [hvalue] at hsuccess
                    | true => rfl
                  have hformulaHead : formula.hasConstHead = true := by
                    cases hvalue : formula.hasConstHead with
                    | false => simp [hhead, hvalue] at hsuccess
                    | true => rfl
                  have hsymbols :
                      db.formulaSymsRespectFrame formula
                          (Metamath.Verify.Frame.mk #[] hyps) = true := by
                    cases hvalue :
                        db.formulaSymsRespectFrame formula
                          (Metamath.Verify.Frame.mk #[] hyps) with
                    | false => simp [hhead, hformulaHead, hvalue] at hsuccess
                    | true => rfl
                  have htypecode :
                      (formula[0]! == stack[off.1 + i]![0]!) = true := by
                    cases hvalue :
                        (formula[0]! == stack[off.1 + i]![0]!) with
                    | false =>
                        simp [hhead, hformulaHead, hsymbols, hvalue] at hsuccess
                    | true => rfl
                  cases hsubst : formula.subst substitutionIn with
                  | error error =>
                      simp [hhead, hformulaHead, hsymbols, htypecode, hsubst]
                        at hsuccess
                  | ok substituted =>
                      have hresult :
                          (substituted == stack[off.1 + i]!) = true := by
                        cases hvalue :
                            (substituted == stack[off.1 + i]!) with
                        | false =>
                            simp [hhead, hformulaHead, hsymbols, htypecode,
                              hsubst, hvalue] at hsuccess
                        | true => rfl
                      have hsubstitution :
                          formula.subst substitutionIn =
                            .ok (stack[off.1 + i]!) := by
                        have heq : substituted = stack[off.1 + i]! :=
                          LawfulBEq.eq_of_beq hresult
                        simpa [heq] using hsubst
                      have htail :
                          db.checkHyp hyps stack off (i + 1)
                              substitutionIn = .ok substitutionOut := by
                        simpa [hhead, hformulaHead, hsymbols, htypecode,
                          hsubst, hresult] using hsuccess
                      have hfuelTail : hyps.size - (i + 1) = fuel := by omega
                      have htailOK :=
                        ih (i + 1) substitutionIn substitutionOut
                          htail hfuelTail
                      unfold Metamath.Kernel.CheckHypOK
                      simp [hlt, hfind, hhead, hformulaHead, hsymbols,
                        htypecode, hsubstitution, htailOK]

/-- Exact success characterization of `DB.checkHyp`. -/
theorem checkHypOK_iff_checkHyp_ok
    (db : RuntimeDB) (hyps : Array String) (stack : Array RuntimeFormula)
    (off : { offset : Nat // offset + hyps.size = stack.size })
    (i : Nat)
    (substitutionIn substitutionOut :
      Std.HashMap String RuntimeFormula) :
    Metamath.Kernel.CheckHypOK db hyps stack off i
        substitutionIn substitutionOut ↔
      db.checkHyp hyps stack off i substitutionIn =
        .ok substitutionOut := by
  constructor
  · exact Metamath.Kernel.checkHyp_complete
      db hyps stack off i substitutionIn substitutionOut
  · exact checkHypOK_of_checkHyp_ok
      db hyps stack off i substitutionIn substitutionOut

end Mettapedia.Languages.Metamath.InferenceCheckHypGraph
