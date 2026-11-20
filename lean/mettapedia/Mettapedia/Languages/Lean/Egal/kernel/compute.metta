; The computations of the reading by kernel conversion.
;
; A term of the reading is computed by need: the arguments an equation of
; Lean asks the form of are computed first, then the equation is used at the
; whole (rules.metta), each of its premises proved by the typing prover
; (typing.metta); the other arguments wait, so a conditional computes only
; the branch it takes.  The answer is
; the value and the kernel's theorem that the term equals it.
;
;   (lean:equality)            the reading's equational theory
;   (lean:open-computation)    the laws of equality and the rules, once
;   (lean:compute TERM)        (Conv VALUE THEOREM), or Same for a value
;   (lean:forget-computation)  forget the answers and facts kept so far
;   (lean:compute-open TERM)   the same with open premises carried as
;                              hypotheses: (Computed VALUE THEOREM PREMISES)
;   (Cv.lean)                  one step at a term: arithmetic between
;                              numerals, else the rules with views of
;                              numerals, the prover told the term
;   (lean:evaluator)           the conversion lean:compute runs
(= (lean:equality) (Equality (lean:theory) (lean:id "eq")))
(= (conv:run-with (Cv.lean) $E $ctx $t)
   (let* (($epoch (typ:new-epoch))
          ($number (conv:run $E $ctx (Cv.orelse (Cv.numeral) (Cv.numeral-lemma)) $t)))
     (if (== $number Same)
         (let $ruled (lean:rules-at $E $ctx $t)
           (if (== $ruled Same)
               (if (conv:nonlinear $E $ctx lean (mgt:head $t)) (lean:after-strong $E $ctx $t) Same)
               $ruled))
         $number)))
(= (lean:rules-at $E $ctx $t)
   (conv:run $E $ctx (Cv.viewed lean (Cv.lean-view (Prover.lean-at $t)) (Prover.lean-at $t) None) $t))
; A rule that names one part of its left side twice compares two parts of
; the term, and they may be equal only as values under their binders (a
; proposition met once as written and once computed).  Where no rule
; applies at such a head, the binder forms of the term are computed inside
; and the rules are tried once more.
(= (lean:after-strong $E $ctx $t)
   (if (mgt:whole $E $t) (lean:after-strong-whole $E $ctx $t) Same))
; Only a whole term is computed so: a name with some of its arguments is a
; function, and the equation of a part lifted into it would be between
; functions, which the congruence of sets does not state.
(= (lean:after-strong-whole $E $ctx $t)
   (let $inside (lean:strong-parts $E $ctx $t $t () Same)
     (case $inside
       ((Same Same)
        ((Conv $t2 $theorem)
         (let $again (lean:rules-at $E $ctx $t2)
           (if (== $again Same) Same (conv:join $E $ctx $t $inside $again))))))))
; Each part of the term computed inside, and kept with the part it came
; from: a constructor node among the parts is a value like any other, typed
; by what it was computed from (the premise of the rule that takes the node
; apart is proved from that type).
(= (lean:strong-parts $E $ctx $t $node $path $acc)
   (case $node
     (((Tm.app $f $x)
       (let $acc1 (lean:strong-parts $E $ctx $t $f (mgt:snoc $path fun) $acc)
         (lean:strong-part $E $ctx $t $x (mgt:snoc $path arg) $acc1)))
      ($other $acc))))
(= (lean:strong-part $E $ctx $t $x $path $acc)
   (case $x
     (((Tm.app $g $y)
       (if (mgt:whole $E $x)
           (let $r (conv:strong-inside $E $ctx (lean:evaluator) $x)
             (case $r
               ((Same $acc)
                ((Conv $x2 $theorem)
                 (let $kept (conv:keep-origin $E $ctx $x2 $x $theorem)
                   (conv:join $E $ctx $t $acc (conv:lift $E $ctx (conv:result $t $acc) $path $x $r)))))))
           (lean:strong-parts $E $ctx $t $x $path $acc)))
      ($other $acc))))
; The view of a numeral as Lean's zero or successor.  A tower is one by
; LeanNum_0 or LeanNum_S as it stands; a numeral in digits is first written
; as the successor of the numeral before it (numerals.metta).
(= (conv:run-with (Cv.lean-view $prover) $E $ctx $t)
   (let $plain (conv:run $E $ctx (Cv.rules lean-views $prover (wire:literal 0)) $t)
     (if (== $plain Same)
         (case $t
           (((Tm.app (Tm.named $head) $x)
             (if (== $head (lean:id "LeanNum")) (lean:digits-view $E $ctx $prover $t $x (num:numeral-value $x)) Same))
            ($other Same)))
         $plain)))
(= (lean:digits-view $E $ctx $prover $t $x $n)
   (if (== $n None) Same
       (if (< $n 1) Same
           (case (num:successor $E $ctx (- $n 1))
             (((Conv $same $next)
               (let* (($before (num:next (wire:natural (- $n 1))))
                      ($shown (Tm.app (wire:named "LeanNum") $before))
                      ($first (Conv $shown (num:within $E $ctx (Tm.app (wire:named "LeanNum") (Tm.db 0)) $x $before
                                                      (eq:sym $E $ctx $before $x $next)))))
                 (case (conv:run $E $ctx (Cv.rule (lean:id "LeanNum_S") $prover) $shown)
                   ((Same Same)
                    ($second (conv:join $E $ctx $t $first $second))))))
              ($other Same))))))
(= (lean:evaluator) (Cv.eval-needed lean (Cv.lean)))
(= (lean:compute $term) (conv:run (lean:equality) (mg:empty-context) (lean:evaluator) $term))
; What a computation kept (answers, origins, typing facts, failures) is
; evidence, in a space of its own.  Forgetting it is taking a new space, so
; that the next computation starts from the theory alone.
(= (lean:forget-computation) (let $space (new-space) (conv:keep-evidence-in $space)))
; The term computed with what stays open carried as hypotheses.  A premise
; of an equation that is neither proved nor refuted is an open goal; the
; computation is run again in a context that assumes it, and so on while a
; round opens new ones (an assumed premise lets the computation reach
; further).  The answer is (Computed VALUE THEOREM PREMISES) with THEOREM
; stating P1 -> .. -> Pk -> TERM = VALUE in the empty context (no premise,
; and it is TERM = VALUE), or (Stopped PREMISES) where the term is its own
; value.  The theorem depends on the premises as stated and on nothing else:
; whoever proves them has the equation.
(= (lean:compute-open $term) (lean:open-rounds $term ()))
(= (lean:open-rounds $term $assumed)
   (let* (($E (lean:equality))
          ($ctx (conv:assuming $E (mg:empty-context) $assumed))
          ($answer (conv:run $E $ctx (lean:evaluator) $term))
          ($new (lean:assumable $E $ctx (conv:open-premises $E $ctx) $assumed)))
     (if (== $new ())
         (case (conv:close-over $E $answer $assumed)
           (((Conv $value $theorem) (Computed $value $theorem $assumed))
            ($other (Stopped $assumed))))
         (lean:open-rounds $term (lean:joined $assumed $new)))))
; The open premises that are new and not refuted.
(= (lean:assumable $E $ctx $open $assumed)
   (if (== $open ()) ()
       (let* (($p (car-atom $open)) ($rest (lean:assumable $E $ctx (cdr-atom $open) $assumed)))
         (if (== (mgt:position $p $assumed 0) None)
             (if (typ:refuted $E $ctx $p) $rest (cons-atom $p $rest))
             $rest))))
(= (lean:joined $xs $ys) (if (== $ys ()) $xs (lean:joined (mgt:snoc $xs (car-atom $ys)) (cdr-atom $ys))))
(= (lean:open-computation)
   (let* (($evidence (lean:forget-computation)) ($laws (eq:init (lean:equality)))) (rules:open (lean:equality))))
