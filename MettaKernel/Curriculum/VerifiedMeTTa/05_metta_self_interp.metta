; VerifiedMeTTa 05: meta-circular MeTTa, Stage 1.
;
; Semantic sources: LeaTTa MOPS/equality-rule semantics for the deterministic
; core, with DeclMatchSpec as the named matching boundary for future HE
; alignment.  Fragment v1: the deterministic MOPS core needed by the
; equality-rule corpus entries -- (= lhs rhs) equalities, immutable encoded
; facts for the entry-04 one-fact query, first-order $-variable matching,
; leftmost reduction, fuel-bounded normalization.
; Excluded in this file: superpose/collapse nondeterminism, grounded guest
; operations, mutable spaces/state.  The entry-04 `match &self` case below is
; the finite immutable fact-table query only; it is not general spaces/state.

; ---------------------------------------------------------------------------
; Direct corpus rules used for the differential checks.

(= (add Z $n) $n)
(= (add (S $m) $n) (S (add $m $n)))

(= (listAppend Nil $ys) $ys)
(= (listAppend (Cons $x $xs) $ys) (Cons $x (listAppend $xs $ys)))

(= (len Nil) Z)
(= (len (Cons $x $xs)) (S (len $xs)))

(= (rev Nil) Nil)
(= (rev (Cons $x $xs)) (listAppend (rev $xs) (Cons $x Nil)))

; ---------------------------------------------------------------------------
; Guest syntax as data.
;
;   (MISym s)         guest symbol
;   (MIVar v)         guest variable
;   (MIApp h args)    guest expression with symbol head h and MI-list args
;   MINil/MICons      lists for arguments, rules, facts, and bindings

(= (mi-fuel-0) FZ)
(= (mi-fuel-1) (FS (mi-fuel-0)))
(= (mi-fuel-2) (FS (mi-fuel-1)))
(= (mi-fuel-3) (FS (mi-fuel-2)))
(= (mi-fuel-4) (FS (mi-fuel-3)))
(= (mi-fuel-5) (FS (mi-fuel-4)))
(= (mi-fuel-6) (FS (mi-fuel-5)))
(= (mi-fuel-7) (FS (mi-fuel-6)))
(= (mi-fuel-8) (FS (mi-fuel-7)))
(= (mi-fuel-9) (FS (mi-fuel-8)))
(= (mi-fuel-10) (FS (mi-fuel-9)))
(= (mi-fuel-11) (FS (mi-fuel-10)))
(= (mi-fuel-12) (FS (mi-fuel-11)))
(= (mi-fuel-13) (FS (mi-fuel-12)))
(= (mi-fuel-14) (FS (mi-fuel-13)))
(= (mi-fuel-15) (FS (mi-fuel-14)))
(= (mi-fuel-16) (FS (mi-fuel-15)))
(= (mi-fuel-17) (FS (mi-fuel-16)))
(= (mi-fuel-18) (FS (mi-fuel-17)))
(= (mi-fuel-19) (FS (mi-fuel-18)))
(= (mi-fuel-20) (FS (mi-fuel-19)))
(= (mi-fuel-21) (FS (mi-fuel-20)))
(= (mi-fuel-22) (FS (mi-fuel-21)))
(= (mi-fuel-23) (FS (mi-fuel-22)))
(= (mi-fuel-24) (FS (mi-fuel-23)))
(= (mi-fuel-25) (FS (mi-fuel-24)))
(= (mi-fuel-26) (FS (mi-fuel-25)))
(= (mi-fuel-27) (FS (mi-fuel-26)))
(= (mi-fuel-28) (FS (mi-fuel-27)))
(= (mi-fuel-29) (FS (mi-fuel-28)))
(= (mi-fuel-30) (FS (mi-fuel-29)))
(= (mi-fuel-31) (FS (mi-fuel-30)))
(= (mi-fuel-32) (FS (mi-fuel-31)))
(= (mi-fuel-33) (FS (mi-fuel-32)))
(= (mi-fuel-34) (FS (mi-fuel-33)))
(= (mi-fuel-35) (FS (mi-fuel-34)))
(= (mi-fuel-36) (FS (mi-fuel-35)))
(= (mi-fuel-37) (FS (mi-fuel-36)))
(= (mi-fuel-38) (FS (mi-fuel-37)))
(= (mi-fuel-39) (FS (mi-fuel-38)))
(= (mi-fuel-40) (FS (mi-fuel-39)))

; ---------------------------------------------------------------------------
; First-order matching and substitution.

(= (mi-lookup $v $bs)
   (case $bs
     ((MIBNil MINone)
      ((MIBCons $w $t $rest)
        (if (== $v $w) (MISome $t) (mi-lookup $v $rest))))))

(= (mi-match-var $v $term $bs)
   (case (mi-lookup $v $bs)
     ((MINone (MIMatchOk (MIBCons $v $term $bs)))
      ((MISome $old) (if (== $old $term) (MIMatchOk $bs) MIMatchFail)))))

(= (mi-match-list $ps $ts $bs)
   (case $ps
     ((MINil
        (case $ts
          ((MINil (MIMatchOk $bs))
           ($other MIMatchFail))))
      ((MICons $p $prest)
        (case $ts
          (((MICons $t $trest)
             (case (mi-match $p $t $bs)
               (((MIMatchOk $bs2) (mi-match-list $prest $trest $bs2))
                (MIMatchFail MIMatchFail))))
           ($other MIMatchFail)))))))

(= (mi-match $pattern $term $bs)
   (case $pattern
     (((MIVar $v) (mi-match-var $v $term $bs))
      ((MISym $s)
        (case $term
          (((MISym $t) (if (== $s $t) (MIMatchOk $bs) MIMatchFail))
           ($other MIMatchFail))))
      ((MIApp $h $args)
        (case $term
          (((MIApp $h2 $args2)
             (if (== $h $h2) (mi-match-list $args $args2 $bs) MIMatchFail))
           ($other MIMatchFail))))
      ($other MIMatchFail))))

(= (mi-subst $bs $term)
   (case $term
     (((MIVar $v)
        (case (mi-lookup $v $bs)
          (((MISome $value) $value)
           (MINone $term))))
      ((MISym $s) $term)
      ((MIApp $h $args) (MIApp $h (mi-subst-list $bs $args)))
      ($other $term))))

(= (mi-subst-list $bs $args)
   (case $args
     ((MINil MINil)
      ((MICons $x $xs) (MICons (mi-subst $bs $x) (mi-subst-list $bs $xs))))))

; ---------------------------------------------------------------------------
; One deterministic MOPS step: root rule first, then leftmost child.

(= (mi-query-root $rules $pattern $template)
   (case $rules
     ((MIRNil MINoRoot)
      ((MIRCons (MIFact $fact) $rest)
        (mi-query-rootK $rest $pattern $template (mi-match $pattern $fact MIBNil)))
      ((MIRCons (MIRule $lhs $rhs) $rest)
        (mi-query-root $rest $pattern $template)))))

(= (mi-query-rootK $rest $pattern $template $r)
   (case $r
     (((MIMatchOk $bs) (MIRootStep (mi-subst $bs $template)))
      (MIMatchFail (mi-query-root $rest $pattern $template)))))

(= (mi-root $rules $term)
   (case $term
     (((MIApp match (MICons (MISym Self) (MICons $pattern (MICons $template MINil))))
        (mi-query-root $rules $pattern $template))
      ($other (mi-root-table $rules $term)))))

(= (mi-root-table $rules $term)
   (case $rules
     ((MIRNil MINoRoot)
      ((MIRCons (MIFact $fact) $rest)
        (mi-root-table $rest $term))
      ((MIRCons (MIRule $lhs $rhs) $rest)
        (case (mi-match $lhs $term MIBNil)
          (((MIMatchOk $bs) (MIRootStep (mi-subst $bs $rhs)))
           (MIMatchFail (mi-root-table $rest $term))))))))

(= (mi-step-args $rules $args)
   (case $args
     ((MINil MINoArgsStep)
      ((MICons $x $xs)
        (case (mi-step $rules $x)
          (((MIStep $x2) (MIArgsStep (MICons $x2 $xs)))
           (MINoStep
             (case (mi-step-args $rules $xs)
               (((MIArgsStep $xs2) (MIArgsStep (MICons $x $xs2)))
                (MINoArgsStep MINoArgsStep))))))))))

(= (mi-step $rules $term)
   (case (mi-root $rules $term)
     (((MIRootStep $next) (MIStep $next))
      (MINoRoot
        (case $term
          (((MIApp $h $args)
             (case (mi-step-args $rules $args)
               (((MIArgsStep $args2) (MIStep (MIApp $h $args2)))
                (MINoArgsStep MINoStep))))
           ($other MINoStep)))))))

(= (mi-eval $rules $term FZ) (MIExhausted $term))
(= (mi-eval $rules $term (FS $fuel))
   (case (mi-step $rules $term)
     (((MIStep $next) (mi-eval $rules $next $fuel))
      (MINoStep (MIDone $term)))))

(= (mi-run $rules $term $fuel) (mi-decode-verdict (mi-eval $rules $term $fuel)))
(= (mi-decode-verdict (MIDone $term)) (mi-decode $term))
(= (mi-decode-verdict (MIExhausted $term)) (MIExhausted $term))

; ---------------------------------------------------------------------------
; Decoding the closed normal forms used by the corpus differentials.

(= (mi-decode (MISym Z)) Z)
(= (mi-decode (MISym Nil)) Nil)
(= (mi-decode (MIApp S (MICons $x MINil))) (S (mi-decode $x)))
(= (mi-decode (MIApp Cons (MICons $x (MICons $xs MINil))))
   (Cons (mi-decode $x) (mi-decode $xs)))
(= (mi-decode (MIApp N (MICons $x MINil))) (N (mi-decode $x)))
(= (mi-decode (MIApp add (MICons $x (MICons $y MINil))))
   (add (mi-decode $x) (mi-decode $y)))
(= (mi-decode (MIApp listAppend (MICons $x (MICons $y MINil))))
   (listAppend (mi-decode $x) (mi-decode $y)))
(= (mi-decode (MIApp len (MICons $x MINil))) (len (mi-decode $x)))
(= (mi-decode (MIApp rev (MICons $x MINil))) (rev (mi-decode $x)))

; ---------------------------------------------------------------------------
; Encoded corpus rule sets.

(= (mi-rules-add)
   (MIRCons
     (MIRule
       (MIApp add (MICons (MISym Z) (MICons (MIVar n) MINil)))
       (MIVar n))
     (MIRCons
       (MIRule
         (MIApp add
           (MICons (MIApp S (MICons (MIVar m) MINil))
             (MICons (MIVar n) MINil)))
         (MIApp S
           (MICons
             (MIApp add (MICons (MIVar m) (MICons (MIVar n) MINil)))
             MINil)))
       MIRNil)))

(= (mi-rules-append-len)
   (MIRCons
     (MIRule
       (MIApp listAppend (MICons (MISym Nil) (MICons (MIVar ys) MINil)))
       (MIVar ys))
     (MIRCons
       (MIRule
         (MIApp listAppend
           (MICons (MIApp Cons (MICons (MIVar x) (MICons (MIVar xs) MINil)))
             (MICons (MIVar ys) MINil)))
         (MIApp Cons
           (MICons (MIVar x)
             (MICons
               (MIApp listAppend (MICons (MIVar xs) (MICons (MIVar ys) MINil)))
               MINil))))
       (MIRCons
         (MIRule
           (MIApp len (MICons (MISym Nil) MINil))
           (MISym Z))
         (MIRCons
           (MIRule
             (MIApp len
               (MICons (MIApp Cons (MICons (MIVar x) (MICons (MIVar xs) MINil))) MINil))
             (MIApp S
               (MICons (MIApp len (MICons (MIVar xs) MINil)) MINil)))
           MIRNil)))))

(= (mi-rules-rev)
   (MIRCons
     (MIRule
       (MIApp listAppend (MICons (MISym Nil) (MICons (MIVar ys) MINil)))
       (MIVar ys))
     (MIRCons
       (MIRule
         (MIApp listAppend
           (MICons (MIApp Cons (MICons (MIVar x) (MICons (MIVar xs) MINil)))
             (MICons (MIVar ys) MINil)))
         (MIApp Cons
           (MICons (MIVar x)
             (MICons
               (MIApp listAppend (MICons (MIVar xs) (MICons (MIVar ys) MINil)))
               MINil))))
       (MIRCons
         (MIRule
           (MIApp rev (MICons (MISym Nil) MINil))
           (MISym Nil))
         (MIRCons
           (MIRule
             (MIApp rev
               (MICons (MIApp Cons (MICons (MIVar x) (MICons (MIVar xs) MINil))) MINil))
             (MIApp listAppend
               (MICons
                 (MIApp rev (MICons (MIVar xs) MINil))
                 (MICons
                   (MIApp Cons (MICons (MIVar x) (MICons (MISym Nil) MINil)))
                   MINil))))
           MIRNil)))))

; ---------------------------------------------------------------------------
; Encoded corpus inputs.

(= (mi-Z) (MISym Z))
(= (mi-S $x) (MIApp S (MICons $x MINil)))
(= (mi-Nil) (MISym Nil))
(= (mi-Cons $x $xs) (MIApp Cons (MICons $x (MICons $xs MINil))))

(= (mi-add $x $y) (MIApp add (MICons $x (MICons $y MINil))))
(= (mi-listAppend $x $y) (MIApp listAppend (MICons $x (MICons $y MINil))))
(= (mi-len $x) (MIApp len (MICons $x MINil)))
(= (mi-rev $x) (MIApp rev (MICons $x MINil)))
(= (mi-N $x) (MIApp N (MICons $x MINil)))
(= (mi-verified-answer $x) (MIApp verified-answer (MICons $x MINil)))
(= (mi-match-self $pattern $template)
   (MIApp match (MICons (MISym Self) (MICons $pattern (MICons $template MINil)))))

(= (mi-one) (mi-S (mi-Z)))
(= (mi-two) (mi-S (mi-one)))
(= (mi-three) (mi-S (mi-two)))

(= (mi-list-0-1) (mi-Cons (mi-Z) (mi-Cons (mi-one) (mi-Nil))))
(= (mi-list-2) (mi-Cons (mi-two) (mi-Nil)))
(= (mi-list-0-1-2) (mi-Cons (mi-Z) (mi-Cons (mi-one) (mi-Cons (mi-two) (mi-Nil)))))
(= (mi-list-2-1-0) (mi-Cons (mi-two) (mi-Cons (mi-one) (mi-Cons (mi-Z) (mi-Nil)))))
(= (mi-match-query)
   (mi-match-self (mi-verified-answer (MIVar answer)) (MIVar answer)))
(= (mi-missing-query)
   (mi-match-self (MIApp missing-answer (MICons (MIVar answer) MINil)) (MIVar answer)))

(= (mi-rules-match-query)
   (MIRCons
     (MIFact (mi-verified-answer (mi-N (mi-two))))
     MIRNil))

; ---------------------------------------------------------------------------
; Stage-1 differentials and required negative verdicts.

!(assertEqual
  (mi-run (mi-rules-add) (mi-add (mi-Z) (mi-one)) (mi-fuel-6))
  (add Z (S Z)))

!(assertEqual
  (mi-run (mi-rules-add) (mi-add (mi-two) (mi-one)) (mi-fuel-10))
  (add (S (S Z)) (S Z)))

!(assertEqual
  (mi-run (mi-rules-add) (mi-add (mi-one) (mi-two)) (mi-fuel-10))
  (add (S Z) (S (S Z))))

!(assertEqual
  (mi-run (mi-rules-append-len) (mi-listAppend (mi-list-0-1) (mi-list-2)) (mi-fuel-20))
  (listAppend (Cons Z (Cons (S Z) Nil)) (Cons (S (S Z)) Nil)))

!(assertEqual
  (mi-run (mi-rules-append-len) (mi-len (mi-listAppend (mi-list-0-1) (mi-list-2))) (mi-fuel-30))
  (len (listAppend (Cons Z (Cons (S Z) Nil)) (Cons (S (S Z)) Nil))))

!(assertEqual
  (mi-run (mi-rules-rev) (mi-rev (mi-list-0-1-2)) (mi-fuel-40))
  (rev (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil)))))

!(assertEqual
  (mi-run (mi-rules-rev) (mi-rev (mi-rev (mi-list-0-1-2))) (mi-fuel-40))
  (rev (rev (Cons Z (Cons (S Z) (Cons (S (S Z)) Nil))))))

!(assertEqualToResult
  (mi-run (mi-rules-match-query) (mi-match-query) (mi-fuel-8))
  ((N (S (S Z)))))

!(assertEqual
  (mi-match (MIVar fresh) (mi-one) MIBNil)
  (MIMatchOk (MIBCons fresh (mi-one) MIBNil)))

!(assertEqual
  (mi-eval (mi-rules-match-query) (mi-missing-query) (mi-fuel-8))
  (MIDone (mi-missing-query)))

!(assertEqual
  (mi-eval MIRNil (MIApp missing (MICons (MISym Z) MINil)) (mi-fuel-3))
  (MIDone (MIApp missing (MICons (MISym Z) MINil))))

!(assertEqual
  (mi-eval (mi-rules-add) (mi-add (mi-two) (mi-one)) FZ)
  (MIExhausted (mi-add (mi-two) (mi-one))))
