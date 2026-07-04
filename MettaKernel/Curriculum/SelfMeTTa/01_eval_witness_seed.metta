; =============================================================================
; SelfMeTTa 01: evaluation-witness seed.
;
; Classification: derived curriculum seed over a generic finite rule table.
; This is not a MeTTa parser/evaluator claim.  It checks that a successful
; surface parse is accompanied by a rule witness whose lhs/rhs agree with a
; named rule in the table.
; =============================================================================

(= (rule-lookup $name RNil) None)
(= (rule-lookup $name (RCons (Rule $rname $lhs $rhs) $rest))
   (if (== $name $rname) (Some (Rule $rname $lhs $rhs)) (rule-lookup $name $rest)))

(= (mw-check-step $rules $expr NoWitness) (Err missing-witness))
(= (mw-check-step $rules $expr (UseRule $name $claimed-rhs))
   (let $found (rule-lookup $name $rules)
     (unify $found (Some (Rule $rname $lhs $rhs))
       (if (== $expr $lhs)
           (if (== $claimed-rhs $rhs)
               (Ok (EvalStep $expr $rhs (Footprint (RuleName $rname))))
               (Err wrong-rhs))
           (Err lhs-mismatch))
       (Err no-rule))))

(= (surface-parse raw-add-z) (Some (MEval (MApp (MApp (MSym add) (MSym z)) (MSym n)))))
(= (surface-parse raw-add-s) (Some (MEval (MApp (MApp (MSym add) (MSym s)) (MSym n)))))
(= (surface-parse raw-unknown) None)

(= (accept-surface-eval $raw $rules $witness)
   (let $parsed (surface-parse $raw)
     (unify $parsed (Some $expr)
       (mw-check-step $rules $expr $witness)
       (Err parse-failed))))

(= (add-zero-expr) (MEval (MApp (MApp (MSym add) (MSym z)) (MSym n))))
(= (add-zero-rule) (Rule add-zero (add-zero-expr) (MSym n)))
(= (self-rules) (RCons (add-zero-rule) RNil))
(= (add-zero-witness) (UseRule add-zero (MSym n)))

!(assertEqual (surface-parse raw-add-z) (Some (add-zero-expr)))
!(assertEqual (accept-surface-eval raw-add-z (self-rules) (add-zero-witness))
              (Ok (EvalStep (add-zero-expr) (MSym n) (Footprint (RuleName add-zero)))))

; Parser success is not proof: the same parsed expression needs a witness.
!(assertEqual (accept-surface-eval raw-add-z (self-rules) NoWitness) (Err missing-witness))
!(assertEqual (accept-surface-eval raw-add-z (self-rules) (UseRule add-zero (MSym z))) (Err wrong-rhs))
!(assertEqual (accept-surface-eval raw-add-s (self-rules) (add-zero-witness)) (Err lhs-mismatch))
!(assertEqual (accept-surface-eval raw-add-z (self-rules) (UseRule missing-rule (MSym n))) (Err no-rule))
!(assertEqual (accept-surface-eval raw-unknown (self-rules) (add-zero-witness)) (Err parse-failed))
