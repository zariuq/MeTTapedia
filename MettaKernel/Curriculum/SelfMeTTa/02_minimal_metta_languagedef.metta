; ============================================================================
; SelfMeTTa 02: minimal-MeTTa LanguageDef with checked evaluation witnesses.
;
; Classification: derived curriculum artifact.  Guest MeTTa programs are data:
; a LanguageDef carrying an RCons/Rule table plus MSym/MApp/MVar guest terms.
; Search is untrusted; only the imported witness checker substrate is trusted in
; this file.
;
; Source anchors:
; - lean/externals/LeaTTa/README.md, "The faithful core" and oracle sections.
; - lean/externals/LeaTTa/book/Docs/Operational.lean, MOPS QUERY semantics.
; - hyperon/hyperon-experimental/docs/minimal-metta.md, eval/unify fragments.
; LeaTTa is the read-only oracle for the MOPS/minimal-MeTTa claims here.
;
; v2 fragment covered: pure equality rules, first-order $-variable patterns
; represented as MVar data, deterministic single-result rewrite steps at an
; explicitly witnessed MApp position path, and fuel-bounded trace checking to a
; context-normal form.  The old EvalStep form is retained as a root-step
; witness; reflection traces use EvalStepAt with PHere/PFun/PArg.
;
; v1 exclusions: superpose/collapse nondeterminism, grounded operations
; including car-atom/cdr-atom argument-reduction subtleties, spaces/state
; mutation, and binders.  The fragment is first-order, so there are no capture
; obligations in this rung.
; ============================================================================

!(import! &self selfmetta_v2_substrate)

(= (sm_ld $rules) (sm_v2_ld SelfMeTTa02 $rules))

; ---------- guest term constructors for the calibration corpus ---------------
(= (mz) (MSym Z))
(= (ms $n) (MApp (MSym S) $n))
(= (madd $x $y) (MApp (MApp (MSym Add) $x) $y))

(= (mnil) (MSym Nil))
(= (msnoc $xs $x) (MApp (MApp (MSym Snoc) $xs) $x))
(= (mcons $x $xs) (MApp (MApp (MSym Cons) $x) $xs))
(= (mappend $xs $ys) (MApp (MApp (MSym Append) $xs) $ys))

(= (mchain_call $state) (MApp (MSym CalChain) $state))
(= (mchain0) (mchain_call (MSym Chain0)))
(= (mchain1) (mchain_call (MSym Chain1)))
(= (mchain2) (mchain_call (MSym Chain2)))
(= (mchain3) (mchain_call (MSym Chain3)))
(= (mchain4) (mchain_call (MSym Chain4)))
(= (mchain5) (MSym Chain5))

(= (mstuck) (MApp (MSym Stuck) (MSym A)))
(= (mwrap $x) (MApp (MSym Wrap) $x))
(= (mpair $x $y) (MApp (MApp (MSym Pair) $x) $y))

; ---------- guest LanguageDefs ----------------------------------------------
(= (sm_add_rules)
   (RCons (Rule add_z (madd (MVar x) (mz)) (MVar x))
   (RCons (Rule add_s (madd (MVar x) (ms (MVar y))) (madd (ms (MVar x)) (MVar y)))
          RNil)))
(= (sm_add_ld) (sm_ld (sm_add_rules)))

(= (sm_append_rules)
   (RCons (Rule append_nil (mappend (mnil) (MVar ys)) (MVar ys))
   (RCons (Rule append_snoc (mappend (msnoc (MVar xs) (MVar x)) (MVar ys))
                              (mappend (MVar xs) (mcons (MVar x) (MVar ys))))
          RNil)))
(= (sm_append_ld) (sm_ld (sm_append_rules)))

(= (sm_chain_rules)
   (RCons (Rule chain_0 (mchain0) (mchain1))
   (RCons (Rule chain_1 (mchain1) (mchain2))
   (RCons (Rule chain_2 (mchain2) (mchain3))
   (RCons (Rule chain_3 (mchain3) (mchain4))
   (RCons (Rule chain_4 (mchain4) (mchain5))
          RNil))))))
(= (sm_chain_ld) (sm_ld (sm_chain_rules)))

(= (sm_stuck_ld) (sm_ld RNil))

(= (sm_context_rules)
   (RCons (Rule a_to_b (MSym A) (MSym B)) RNil))
(= (sm_context_ld) (sm_ld (sm_context_rules)))

(= (sm_dup_rules)
   (RCons (Rule same_pair (mpair (MVar x) (MVar x)) (MSym Same)) RNil))
(= (sm_dup_ld) (sm_ld (sm_dup_rules)))

(= (sm_order_rules)
   (RCons (Rule exact_a (MSym A) (MSym Hit))
   (RCons (Rule catch_any (MVar x) (MSym Miss)) RNil)))
(= (sm_order_ld) (sm_ld (sm_order_rules)))

; ---------- calibration traces checked by the witness checker ----------------
(= (sm_add_start) (madd (mz) (ms (ms (mz)))))
(= (sm_add_mid1) (madd (ms (mz)) (ms (mz))))
(= (sm_add_mid2) (madd (ms (ms (mz))) (mz)))
(= (sm_add_final) (ms (ms (mz))))
(= (sm_add_trace)
   (TCons (EvalStep (sm_add_start) (sm_sig2 x (mz) y (ms (mz))) add_s (sm_add_mid1))
   (TCons (EvalStep (sm_add_mid1) (sm_sig2 x (ms (mz)) y (mz)) add_s (sm_add_mid2))
   (TCons (EvalStep (sm_add_mid2) (sm_sig1 x (ms (ms (mz)))) add_z (sm_add_final))
          TNil))))

(= (sm_append_start)
   (mappend (msnoc (msnoc (mnil) (MSym A)) (MSym B)) (mcons (MSym C) (mnil))))
(= (sm_append_mid1)
   (mappend (msnoc (mnil) (MSym A)) (mcons (MSym B) (mcons (MSym C) (mnil)))))
(= (sm_append_mid2)
   (mappend (mnil) (mcons (MSym A) (mcons (MSym B) (mcons (MSym C) (mnil))))))
(= (sm_append_final) (mcons (MSym A) (mcons (MSym B) (mcons (MSym C) (mnil)))))
(= (sm_append_trace)
   (TCons
     (EvalStep (sm_append_start)
       (sm_sig3 xs (msnoc (mnil) (MSym A)) x (MSym B) ys (mcons (MSym C) (mnil)))
       append_snoc
       (sm_append_mid1))
   (TCons
     (EvalStep (sm_append_mid1)
       (sm_sig3 xs (mnil) x (MSym A) ys (mcons (MSym B) (mcons (MSym C) (mnil))))
       append_snoc
       (sm_append_mid2))
   (TCons
     (EvalStep (sm_append_mid2)
       (sm_sig1 ys (sm_append_final))
       append_nil
       (sm_append_final))
     TNil))))

(= (sm_chain_trace)
   (TCons (EvalStep (mchain0) SNil chain_0 (mchain1))
   (TCons (EvalStep (mchain1) SNil chain_1 (mchain2))
   (TCons (EvalStep (mchain2) SNil chain_2 (mchain3))
   (TCons (EvalStep (mchain3) SNil chain_3 (mchain4))
   (TCons (EvalStep (mchain4) SNil chain_4 (mchain5))
          TNil))))))

(= (sm_context_start) (mwrap (MSym A)))
(= (sm_context_final) (mwrap (MSym B)))
(= (sm_context_trace)
   (TCons (EvalStepAt (sm_context_start) (PArg PHere) SNil a_to_b (sm_context_final))
          TNil))

(= (sm_dup_start) (mpair (MSym A) (MSym A)))
(= (sm_dup_final) (MSym Same))
(= (sm_dup_trace)
   (TCons (EvalStep (sm_dup_start) (sm_sig1 x (MSym A)) same_pair (sm_dup_final))
          TNil))

; ---------- native calibration rules for CeTTa and LeaTTa oracle agreement ---
(= (CalAdd $x Z) $x)
(= (CalAdd $x (S $y)) (CalAdd (S $x) $y))

(= (CalAppend Nil $ys) $ys)
(= (CalAppend (Snoc $xs $x) $ys) (CalAppend $xs (Cons $x $ys)))

(= (CalChain Chain0) (CalChain Chain1))
(= (CalChain Chain1) (CalChain Chain2))
(= (CalChain Chain2) (CalChain Chain3))
(= (CalChain Chain3) (CalChain Chain4))
(= (CalChain Chain4) Chain5)

; ============================ CHECKS =========================================
!(assertEqual (sm_match (madd (MVar x) (ms (MVar y))) (sm_add_start) SNil)
  (Ok (sm_sig2 x (mz) y (ms (mz)))))
!(assertEqual (sm_inst (madd (ms (MVar x)) (MVar y)) (sm_sig2 x (mz) y (ms (mz))))
  (Ok (sm_add_mid1)))

!(assertEqual (sm_check_normalize (sm_add_ld) (sm_add_start) 3 (sm_add_trace) (sm_add_final))
  (Ok (sm_add_final)))
!(assertEqual (sm_check_normalize (sm_append_ld) (sm_append_start) 3 (sm_append_trace) (sm_append_final))
  (Ok (sm_append_final)))
!(assertEqual (sm_check_normalize (sm_chain_ld) (mchain0) 5 (sm_chain_trace) (mchain5))
  (Ok (mchain5)))
!(assertEqual (sm_check_normalize (sm_stuck_ld) (mstuck) 0 TNil (mstuck))
  (Ok (mstuck)))
!(assertEqual (sm_check_normalize (sm_context_ld) (sm_context_start) 1
    (sm_context_trace) (sm_context_final))
  (Ok (sm_context_final)))
!(assertEqual (sm_check_normalize (sm_dup_ld) (sm_dup_start) 1 (sm_dup_trace) (sm_dup_final))
  (Ok (sm_dup_final)))

; Required rejection classes.
!(assertEqual
  (sm_check_normalize (sm_add_ld) (sm_add_start) 3
    (TCons (EvalStep (sm_add_start) (sm_sig2 x (mz) y (ms (mz))) add_s (MSym Wrong)) TNil)
    (MSym Wrong))
  (Err wrong_rhs))
!(assertEqual
  (sm_check_normalize (sm_add_ld) (sm_add_start) 3
    (TCons (EvalStep (sm_add_start) (sm_sig2 x (MSym Bad) y (ms (mz))) add_s (sm_add_mid1)) TNil)
    (sm_add_mid1))
  (Err wrong_sigma))
!(assertEqual
  (sm_check_normalize (sm_add_ld) (sm_add_start) 0 TNil (sm_add_final))
  (Err skipped_step))
!(assertEqual
  (sm_check_normalize (sm_add_ld) (mstuck) 1
    (TCons (EvalStep (mstuck) SNil add_z (mz)) TNil)
    (mz))
  (Err non_matching_lhs))
!(assertEqual
  (sm_check_normalize (sm_context_ld) (sm_context_start) 1
    (TCons (EvalStepAt (sm_context_start) (PFun PHere) SNil a_to_b (sm_context_final)) TNil)
    (sm_context_final))
  (Err wrong_position))
!(assertEqual
  (sm_check_normalize (sm_context_ld) (sm_context_start) 1
    (TCons (EvalStepAt (sm_context_start) (PArg (PArg PHere)) SNil a_to_b (sm_context_final)) TNil)
    (sm_context_final))
  (Err wrong_position))
!(assertEqual
  (sm_check_normalize (sm_dup_ld) (sm_dup_start) 1
    (TCons (EvalStep (sm_dup_start) (sm_sig1 x (MSym B)) same_pair (sm_dup_final)) TNil)
    (sm_dup_final))
  (Err wrong_sigma))
!(assertEqual
  (sm_check_normalize (sm_order_ld) (MSym A) 1
    (TCons (EvalStep (MSym A) (sm_sig1 x (MSym A)) catch_any (MSym Miss)) TNil)
    (MSym Miss))
  (Err wrong_rule_order))

; Fuel and final-normality teeth.
!(assertEqual (sm_check_normalize (sm_chain_ld) (mchain0) 4 (sm_chain_trace) (mchain5))
  (Err fuel_exhausted))
!(assertEqual
  (sm_check_normalize (sm_add_ld) (sm_add_start) 1
    (TCons (EvalStep (sm_add_start) (sm_sig2 x (mz) y (ms (mz))) add_s (sm_add_mid1)) TNil)
    (sm_add_mid1))
  (Err final_not_normal))

; Native MeTTa calibration: the same rule families evaluate under the host.
!(assertEqual (CalAdd Z (S (S Z))) (S (S Z)))
!(assertEqual
  (CalAppend (Snoc (Snoc Nil A) B) (Cons C Nil))
  (Cons A (Cons B (Cons C Nil))))
!(assertEqual (CalChain Chain0) Chain5)
!(assertEqualToResult (CalStuck A) ((CalStuck A)))
