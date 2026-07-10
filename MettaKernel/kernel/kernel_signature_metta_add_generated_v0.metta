; =============================================================================
; kernel_signature_metta_add_generated_v0.metta
;
; Classification: derived/generated.
;
; Generated from addDeclsKernelReachabilitySig via the generic LF-signature
; renderer.  This file compares the generated signature expression with the
; kernel fixture used by the proof-term checks; it does not define a checker
; and does not validate traces.
; =============================================================================

!(import! &self kernel_signature_metta_add_v0)

(= (ma-generated-metta-add-sig)
(SCons (DConst __ldName (Srt type))
(SCons (DConst __ldIndex (Srt type))
(SCons (DConst __ldPattern (Srt type))
(SCons (DConst __ldPatternList (Srt type))
(SCons (DConst __ldNameList (Srt type))
(SCons (DConst __ldColl (Srt type))
(SCons (DConst __ldNoName (Con __ldName))
(SCons (DConst __ldNameNil (Con __ldNameList))
(SCons (DConst __ldNameCons (Pi (Con __ldName) (Pi (Con __ldNameList) (Con __ldNameList))))
(SCons (DConst __ldPNil (Con __ldPatternList))
(SCons (DConst __ldPCons (Pi (Con __ldPattern) (Pi (Con __ldPatternList) (Con __ldPatternList))))
(SCons (DConst __ldPBVar (Pi (Con __ldIndex) (Con __ldPattern)))
(SCons (DConst __ldPFVar (Pi (Con __ldName) (Con __ldPattern)))
(SCons (DConst __ldPApply (Pi (Con __ldName) (Pi (Con __ldPatternList) (Con __ldPattern))))
(SCons (DConst __ldPLambda (Pi (Con __ldName) (Pi (Con __ldPattern) (Con __ldPattern))))
(SCons (DConst __ldPMultiLambda (Pi (Con __ldIndex) (Pi (Con __ldNameList) (Pi (Con __ldPattern) (Con __ldPattern)))))
(SCons (DConst __ldPSubst (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Con __ldPattern))))
(SCons (DConst __ldPCollection (Pi (Con __ldColl) (Pi (Con __ldPatternList) (Pi (Con __ldName) (Con __ldPattern)))))
(SCons (DConst __ldCollVec (Con __ldColl))
(SCons (DConst __ldCollHashBag (Con __ldColl))
(SCons (DConst __ldCollHashSet (Con __ldColl))
(SCons (DConst __ldEquationRule (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst __ldRewriteRule (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MTerm (Srt type))
(SCons (DConst name:add (Con __ldName))
(SCons (DConst name:Z (Con __ldName))
(SCons (DConst name:n (Con __ldName))
(SCons (DConst name:S (Con __ldName))
(SCons (DConst name:m (Con __ldName))
(SCons (DConst rewrite:add-z (App (App (Con __ldRewriteRule) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:Z)) (Con __ldPNil))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (App (Con __ldPFVar) (Con name:n))))
(SCons (DConst rewrite:add-s (App (App (Con __ldRewriteRule) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:m))) (Con __ldPNil)))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:m))) (App (App (Con __ldPCons) (App (Con __ldPFVar) (Con name:n))) (Con __ldPNil))))) (Con __ldPNil)))))
(SCons (DConst MeTTaAdd:Reduces (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MeTTaAdd:EvalEq (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Srt type))))
(SCons (DConst MeTTaAdd:reduces-refl (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (Var 0)) (Var 0))))
(SCons (DConst MeTTaAdd:reduces-trans (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (App (App (Con MeTTaAdd:Reduces) (Var 4)) (Var 2))))))))
(SCons (DConst MeTTaAdd:eval-eq-intro (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 1)) (Var 0)) (App (App (Con MeTTaAdd:EvalEq) (Var 2)) (Var 1))))))
(SCons (DConst MeTTaAdd:reduces-apply-head (Pi (Con __ldName) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPatternList) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 2)) (Var 1)) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (Var 1)))) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 2)) (Var 1))))))))))
(SCons (DConst MeTTaAdd:reduces-apply-second (Pi (Con __ldName) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (Con __ldPattern) (Pi (App (App (Con MeTTaAdd:Reduces) (Var 1)) (Var 0)) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (App (App (Con __ldPCons) (Var 2)) (Con __ldPNil))))) (App (App (Con __ldPApply) (Var 4)) (App (App (Con __ldPCons) (Var 3)) (App (App (Con __ldPCons) (Var 1)) (Con __ldPNil)))))))))))
(SCons (DConst MeTTaAdd:rewrite:add-z (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:Z)) (Con __ldPNil))) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (Var 0))))
(SCons (DConst MeTTaAdd:rewrite:add-s (Pi (Con __ldPattern) (Pi (Con __ldPattern) (App (App (Con MeTTaAdd:Reduces) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (Var 1)) (Con __ldPNil)))) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (App (App (Con __ldPApply) (Con name:S)) (App (App (Con __ldPCons) (App (App (Con __ldPApply) (Con name:add)) (App (App (Con __ldPCons) (Var 1)) (App (App (Con __ldPCons) (Var 0)) (Con __ldPNil))))) (Con __ldPNil)))))))
SNil)))))))))))))))))))))))))))))))))))))))))

; petta_skip_next
!(assertEqual (ma-generated-metta-add-sig) (ma-metta-add-sig))
!(assertEqual (sig-has-name MeTTaAdd:rewrite:add-s (ma-generated-metta-add-sig)) True)
!(assertEqual (sig-has-name MeTTaAdd:rewrite:add-z (ma-generated-metta-add-sig)) True)
!(assertEqual (sig-has-name MeTTaAdd:reduces-apply-head (ma-generated-metta-add-sig)) True)
!(assertEqual (sig-has-name MeTTaAdd:reduces-apply-second (ma-generated-metta-add-sig)) True)
!(assertEqual (sig-has-name __ldMultiBinder (ma-generated-metta-add-sig)) False)
!(assertEqual (sig-admitted (ma-generated-metta-add-sig)) True)
