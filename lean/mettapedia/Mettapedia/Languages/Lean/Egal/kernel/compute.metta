; The computations of the reading by kernel conversion.
;
; A term of the reading is computed by need: the arguments an equation of
; Lean asks the form of are computed first, then the equation is used at the
; whole (rules.metta), each of its premises proved by the typing prover
; (typing.metta); the other arguments wait, so a conditional computes only
; the branch it takes.  The answer is
; the value and the kernel's theorem that the term equals it.
;
;   (egal:equality)            the reading's equational theory
;   (egal:open-computation)    the laws of equality and the rules, once
;   (egal:compute TERM)        (Conv VALUE THEOREM), or Same for a value
;   (egal:forget-computation)  forget the answers and facts kept so far
;   (egal:compute-open TERM)   the same with open premises carried as
;                              hypotheses: (Computed VALUE THEOREM PREMISES)
;   (Cv.lean)                  one step at a term: arithmetic between
;                              numerals, else the rules with views of
;                              numerals, the prover told the term
;   (egal:evaluator)           the conversion egal:compute runs
(= (egal:equality) (Equality (egal:theory) (egal:id "eq")))
(= (conv:run-with (Cv.lean) $E $ctx $t)
   (let $number (conv:run $E $ctx (Cv.orelse (Cv.numeral) (Cv.numeral-lemma)) $t)
     (egal:learned
       (if (== $number Same)
           (let $ruled (egal:rules-at $E $ctx $t)
             (if (== $ruled Same)
                 (if (conv:nonlinear $E $ctx lean (mgt:head $t)) (egal:after-strong $E $ctx $t) Same)
                 $ruled))
           $number))))
; A step that was made can be learned from: the failures kept before it may no longer hold.
(= (egal:learned $step) (if (== $step Same) Same (let $epoch (typ:new-epoch) $step)))
(= (egal:rules-at $E $ctx $t)
   (conv:run $E $ctx (Cv.viewed lean (Cv.lean-view (Prover.lean-at $t)) (Prover.lean-at $t) None) $t))
; A rule that names one part of its left side twice compares two parts of
; the term, and they may be equal only as values under their binders (a
; proposition met once as written and once computed).  Where no rule
; applies at such a head, the binder forms of the term are computed inside
; and the rules are tried once more.
(= (egal:after-strong $E $ctx $t)
   (if (mgt:whole $E $t) (egal:after-strong-whole $E $ctx $t) Same))
; Only a whole term is computed so: a name with some of its arguments is a
; function, and the equation of a part lifted into it would be between
; functions, which the congruence of sets does not state.
(= (egal:after-strong-whole $E $ctx $t)
   (let $inside (egal:strong-parts $E $ctx $t $t () Same)
     (case $inside
       ((Same Same)
        ((Conv $t2 $theorem)
         (let $again (egal:rules-at $E $ctx $t2)
           (if (== $again Same) Same (conv:join $E $ctx $t $inside $again))))))))
; Each part of the term computed inside, and kept with the part it came
; from: a constructor node among the parts is a value like any other, typed
; by what it was computed from (the premise of the rule that takes the node
; apart is proved from that type).
(= (egal:strong-parts $E $ctx $t $node $path $acc)
   (case $node
     (((Tm.app $f $x)
       (let $acc1 (egal:strong-parts $E $ctx $t $f (mgt:snoc $path fun) $acc)
         (egal:strong-part $E $ctx $t $x (mgt:snoc $path arg) $acc1)))
      ($other $acc))))
(= (egal:strong-part $E $ctx $t $x $path $acc)
   (case $x
     (((Tm.app $g $y)
       (if (mgt:whole $E $x)
           (let $r (conv:strong-inside $E $ctx (egal:evaluator) $x)
             (case $r
               ((Same $acc)
                ((Conv $x2 $theorem)
                 (let $kept (conv:keep-origin $E $ctx $x2 $x $theorem)
                   (conv:join $E $ctx $t $acc (conv:lift $E $ctx (conv:result $t $acc) $path $x $r)))))))
           (egal:strong-parts $E $ctx $t $x $path $acc)))
      ($other $acc))))
; The view of a numeral as Lean's zero or successor.  A tower is one by
; LeanNum_0 or LeanNum_S as it stands; a numeral in digits is first written
; as the successor of the numeral before it (numerals.metta).
(= (conv:run-with (Cv.lean-view $prover) $E $ctx $t)
   (let $plain (conv:run $E $ctx (Cv.rules lean-views $prover (wire:literal 0)) $t)
     (if (== $plain Same)
         (case $t
           (((Tm.app (Tm.named $head) $x)
             (if (== $head (egal:id "LeanNum")) (egal:digits-view $E $ctx $prover $t $x (num:numeral-value $x)) Same))
            ($other Same)))
         $plain)))
(= (egal:digits-view $E $ctx $prover $t $x $n)
   (if (== $n None) Same
       (if (< $n 1) Same
           (case (num:successor $E $ctx (- $n 1))
             (((Conv $same $next)
               (let* (($before (num:next (wire:natural (- $n 1))))
                      ($shown (Tm.app (wire:named "LeanNum") $before))
                      ($first (Conv $shown (num:within $E $ctx (Tm.app (wire:named "LeanNum") (Tm.db 0)) $x $before
                                                      (eq:sym $E $ctx $before $x $next)))))
                 (case (conv:run $E $ctx (Cv.rule (egal:id "LeanNum_S") $prover) $shown)
                   ((Same Same)
                    ($second (conv:join $E $ctx $t $first $second))))))
              ($other Same))))))
(= (egal:evaluator) (Cv.eval-needed lean (Cv.lean)))
(= (egal:compute $term) (conv:run (egal:equality) (mg:empty-context) (egal:evaluator) $term))
; What a computation kept (answers, origins, typing facts, failures) is
; evidence, in a space of its own.  Forgetting it is taking a new space, so
; that the next computation starts from the theory alone.
(= (egal:forget-computation) (let $space (new-space) (conv:keep-evidence-in $space)))
; The term computed with what stays open carried as hypotheses.  A premise
; of an equation that is neither proved nor refuted is an open goal; the
; computation is run again in a context that assumes it, and so on while a
; round opens new ones (an assumed premise lets the computation reach
; further).  The answer is (Computed VALUE THEOREM PREMISES) with THEOREM
; stating P1 -> .. -> Pk -> TERM = VALUE in the empty context (no premise,
; and it is TERM = VALUE), or (Stopped PREMISES) where the term is its own
; value.  The theorem depends on the premises as stated and on nothing else:
; whoever proves them has the equation.
(= (egal:compute-open $term) (egal:open-rounds $term ()))
(= (egal:open-rounds $term $assumed)
   (let* (($E (egal:equality))
          ($ctx (conv:assuming $E (mg:empty-context) $assumed))
          ($answer (conv:run $E $ctx (egal:evaluator) $term))
          ($new (egal:assumable $E $ctx (conv:open-premises $E $ctx) $assumed)))
     (if (== $new ())
         (case (conv:close-over $E $answer $assumed)
           (((Conv $value $theorem) (Computed $value $theorem $assumed))
            ($other (Stopped $assumed))))
         (egal:open-rounds $term (egal:joined $assumed $new)))))
; The open premises that are new and not refuted.
(= (egal:assumable $E $ctx $open $assumed)
   (if (== $open ()) ()
       (let* (($p (car-atom $open)) ($rest (egal:assumable $E $ctx (cdr-atom $open) $assumed)))
         (if (== (mgt:position $p $assumed 0) None)
             (if (typ:refuted $E $ctx $p) $rest (cons-atom $p $rest))
             $rest))))
(= (egal:joined $xs $ys) (if (== $ys ()) $xs (egal:joined (mgt:snoc $xs (car-atom $ys)) (cdr-atom $ys))))
(= (egal:open-computation)
   (let* (($evidence (egal:forget-computation)) ($laws (eq:init (egal:equality)))) (rules:open (egal:equality))))
