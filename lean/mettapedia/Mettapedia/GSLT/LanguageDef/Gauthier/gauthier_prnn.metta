; # Gauthier PRNN languageDef - MeTTa/CeTTa evaluator twin
;
; Executable mirror of `Prnn.lean`: list-valued PRNN programs over two integer-list
; registers plus explicit `prog`, `seq`, and `embv` globals.  Results are explicit
; `Some list` / `None`, matching the Lean side's partial-operation discipline.

; ---- environment and helpers ------------------------------------------------------------

(= (prnn-default-env) (prnn-env () () ()))
(= (prnn-sample-env) (prnn-env (42 7) (3 1 4) ((5) (8) (13))))

(= (prnn-head-list $xs)
   (if (== (size-atom $xs) 0)
       None
       (Some (car-atom $xs))))

(= (prnn-head-result $r)
   (if (== $r None)
       None
       (prnn-head-result-some $r)))

(= (prnn-head-result-some (Some $xs))
   (prnn-head-list $xs))

(= (prnn-singleton-incr $xs)
   (if (== (size-atom $xs) 0)
       None
       (Some ((+ (car-atom $xs) 1)))))

(= (prnn-list-get $xs $i)
   (if (< $i 0)
       None
       (prnn-list-get-nonneg $xs $i)))

(= (prnn-list-get-nonneg $xs $i)
   (if (== (size-atom $xs) 0)
       None
       (if (== $i 0)
           (Some (car-atom $xs))
           (prnn-list-get-nonneg (cdr-atom $xs) (- $i 1)))))

(= (prnn-mod-index $i $n)
   (if (<= $n 0)
       None
       (if (< $i 0)
           (prnn-mod-index (+ $i $n) $n)
           (Some (- $i (* $n (// $i $n)))))))

(= (prnn-embv-get (prnn-env $prog $seq $embv) $i)
   (prnn-embv-get-index $embv (prnn-mod-index $i (size-atom $embv))))

(= (prnn-embv-get-index $embv $r)
   (if (== $r None)
       None
       (prnn-embv-get-index-some $embv $r)))

(= (prnn-embv-get-index-some $embv (Some $i))
   (prnn-list-get $embv $i))

(= (prnn-apply2 addi $a $b) (Some (+ $a $b)))
(= (prnn-apply2 diff $a $b) (Some (- $a $b)))
(= (prnn-apply2 mult $a $b) (Some (* $a $b)))
(= (prnn-apply2 divi $a $b) (if (== $b 0) None (Some (// $a $b))))
(= (prnn-apply2 modu $a $b) (if (== $b 0) None (Some (- $a (* $b (// $a $b))))))

(= (prnn-mkE $op $ra $rb)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (prnn-mkE-some $op $ra $rb))))

(= (prnn-mkE-some $op (Some $va) (Some $vb))
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $vb) 0)
           None
           (prnn-mkE-finish (prnn-apply2 $op (car-atom $va) (car-atom $vb))
                             (cdr-atom $va)))))

(= (prnn-mkE-finish $r $tail)
   (if (== $r None)
       None
       (prnn-mkE-finish-some $r $tail)))

(= (prnn-mkE-finish-some (Some $c) $tail)
   (Some (cons-atom $c $tail)))

; ---- evaluator core ---------------------------------------------------------------------

(= (prnn-ev zero $x $y $env) (Some (0)))
(= (prnn-ev one $x $y $env) (Some (1)))
(= (prnn-ev two $x $y $env) (Some (2)))
(= (prnn-ev xreg $x $y $env) (Some $x))
(= (prnn-ev yreg $x $y $env) (Some $y))
(= (prnn-ev prog $x $y (prnn-env $prog $seq $embv)) (Some $prog))
(= (prnn-ev seq $x $y (prnn-env $prog $seq $embv)) (Some $seq))

(= (prnn-ev (embv $a) $x $y $env)
   (prnn-embv (prnn-ev $a $x $y $env) $env))

(= (prnn-embv $ra $env)
   (if (== $ra None)
       None
       (prnn-embv-some $ra $env)))

(= (prnn-embv-some (Some $va) $env)
   (if (== (size-atom $va) 0)
       None
       (prnn-embv-get $env (car-atom $va))))

(= (prnn-ev (addi $a $b) $x $y $env)
   (prnn-mkE addi (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))
(= (prnn-ev (diff $a $b) $x $y $env)
   (prnn-mkE diff (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))
(= (prnn-ev (mult $a $b) $x $y $env)
   (prnn-mkE mult (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))
(= (prnn-ev (divi $a $b) $x $y $env)
   (prnn-mkE divi (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))
(= (prnn-ev (modu $a $b) $x $y $env)
   (prnn-mkE modu (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))

(= (prnn-ev (cond $c $t $e) $x $y $env)
   (prnn-cond (prnn-ev $c $x $y $env) $t $e $x $y $env))

(= (prnn-cond $rc $t $e $x $y $env)
   (if (== $rc None)
       None
       (prnn-cond-some $rc $t $e $x $y $env)))

(= (prnn-cond-some (Some $vc) $t $e $x $y $env)
   (if (== (size-atom $vc) 0)
       None
       (if (<= (car-atom $vc) 0)
           (prnn-ev $t $x $y $env)
           (prnn-ev $e $x $y $env))))

(= (prnn-ev (push $a $b) $x $y $env)
   (prnn-push (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)))

(= (prnn-push $ra $rb)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (prnn-push-some $ra $rb))))

(= (prnn-push-some (Some $va) (Some $vb))
   (if (== (size-atom $va) 0)
       None
       (Some (cons-atom (car-atom $va) $vb))))

(= (prnn-ev (pop $a) $x $y $env)
   (prnn-pop (prnn-ev $a $x $y $env)))

(= (prnn-pop $ra)
   (if (== $ra None)
       None
       (prnn-pop-some $ra)))

(= (prnn-pop-some (Some $va))
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $va) 1)
           (Some $va)
           (Some (cdr-atom $va)))))

; ---- loops and comprehension ------------------------------------------------------------

(= (prnn-ev (loop $body $n $x0) $x $y $env)
   (prnn-loop-start (prnn-ev $n $x $y $env) (prnn-ev $x0 $x $y $env) $body $env))

(= (prnn-loop-start $rn $rx0 $body $env)
   (if (== $rn None)
       None
       (if (== $rx0 None)
           None
           (prnn-loop-start-some $rn $rx0 $body $env))))

(= (prnn-loop-start-some (Some $vn) (Some $vx0) $body $env)
   (if (== (size-atom $vn) 0)
       None
       (if (<= (car-atom $vn) 0)
           (Some $vx0)
           (prnn-loop $body (car-atom $vn) $vx0 (1) $env))))

(= (prnn-loop $body $k $x1 $x2 $env)
   (if (<= $k 0)
       (Some $x1)
       (prnn-loop-step $body $k $x1 $x2 $env)))

(= (prnn-loop-step $body $k $x1 $x2 $env)
   (prnn-loop-step-results $body $k
      (prnn-ev $body $x1 $x2 $env)
      (prnn-singleton-incr $x2) $env))

(= (prnn-loop-step-results $body $k $rx1 $rx2 $env)
   (if (== $rx1 None)
       None
       (if (== $rx2 None)
           None
           (prnn-loop-step-results-some $body $k $rx1 $rx2 $env))))

(= (prnn-loop-step-results-some $body $k (Some $x1p) (Some $x2p) $env)
   (prnn-loop $body (- $k 1) $x1p $x2p $env))

(= (prnn-ev (loop2 $f $g $n $a $b) $x $y $env)
   (prnn-loop2-start
      (prnn-ev $n $x $y $env) (prnn-ev $a $x $y $env) (prnn-ev $b $x $y $env)
      $f $g $env))

(= (prnn-loop2-start $rn $ra $rb $f $g $env)
   (if (== $rn None)
       None
       (if (== $ra None)
           None
           (if (== $rb None)
               None
               (prnn-loop2-start-some $rn $ra $rb $f $g $env)))))

(= (prnn-loop2-start-some (Some $vn) (Some $va) (Some $vb) $f $g $env)
   (if (== (size-atom $vn) 0)
       None
       (if (<= (car-atom $vn) 0)
           (Some $va)
           (prnn-loop2 $f $g (car-atom $vn) $va $vb $env))))

(= (prnn-loop2 $f $g $k $x1 $x2 $env)
   (if (<= $k 0)
       (Some $x1)
       (prnn-loop2-step $f $g $k $x1 $x2 $env)))

(= (prnn-loop2-step $f $g $k $x1 $x2 $env)
   (prnn-loop2-step-results $f $g $k
      (prnn-ev $f $x1 $x2 $env) (prnn-ev $g $x1 $x2 $env) $env))

(= (prnn-loop2-step-results $f $g $k $rx1 $rx2 $env)
   (if (== $rx1 None)
       None
       (if (== $rx2 None)
           None
           (prnn-loop2-step-results-some $f $g $k $rx1 $rx2 $env))))

(= (prnn-loop2-step-results-some $f $g $k (Some $x1p) (Some $x2p) $env)
   (prnn-loop2 $f $g (- $k 1) $x1p $x2p $env))

(= (prnn-ev (compr $f $n) $x $y $env)
   (prnn-compr-start (prnn-ev $n $x $y $env) $f $env))

(= (prnn-compr-start $rn $f $env)
   (if (== $rn None)
       None
       (prnn-compr-start-some $rn $f $env)))

(= (prnn-compr-start-some (Some $vn) $f $env)
   (if (== (size-atom $vn) 0)
       None
       (prnn-compr $f (car-atom $vn) -1 (-1) $env)))

(= (prnn-compr $f $target $seen $cand $env)
   (if (>= $seen $target)
       (Some $cand)
       (prnn-compr-next $f $target $seen $cand $env)))

(= (prnn-compr-next $f $target $seen $cand $env)
   (prnn-compr-next-incr $f $target $seen (prnn-singleton-incr $cand) $env))

(= (prnn-compr-next-incr $f $target $seen $rcand $env)
   (if (== $rcand None)
       None
       (prnn-compr-next-incr-some $f $target $seen $rcand $env)))

(= (prnn-compr-next-incr-some $f $target $seen (Some $candp) $env)
   (prnn-compr-check $f $target $seen $candp (prnn-ev $f $candp (0) $env) $env))

(= (prnn-compr-check $f $target $seen $cand $rv $env)
   (if (== $rv None)
       None
       (prnn-compr-check-some $f $target $seen $cand $rv $env)))

(= (prnn-compr-check-some $f $target $seen $cand (Some $v) $env)
   (if (== (size-atom $v) 0)
       None
       (if (<= (car-atom $v) 0)
           (prnn-compr $f $target (+ $seen 1) $cand $env)
           (prnn-compr $f $target $seen $cand $env))))

; ---- OEIS seeded terms ------------------------------------------------------------------

(= (prnn-term-env $p $k $env)
   (prnn-head-result (prnn-ev $p ($k) (0) $env)))

(= (prnn-term $p $k)
   (prnn-term-env $p $k (prnn-default-env)))

; ---- executable validation --------------------------------------------------------------

; PRNN/org factorial by `loop (mult x y) x one`.
!(assertEqual (prnn-term (loop (mult xreg yreg) xreg one) 0) (Some 1))
!(assertEqual (prnn-term (loop (mult xreg yreg) xreg one) 4) (Some 24))
!(assertEqual (prnn-term (loop (mult xreg yreg) xreg one) 6) (Some 720))

; List operations.
!(assertEqual (prnn-term (pop (push xreg yreg)) 5) (Some 0))

; PRNN globals.
!(assertEqual (prnn-term-env prog 0 (prnn-sample-env)) (Some 42))
!(assertEqual (prnn-term-env seq 0 (prnn-sample-env)) (Some 3))
!(assertEqual (prnn-term-env (embv xreg) 1 (prnn-sample-env)) (Some 8))
!(assertEqual (prnn-term-env (embv xreg) 4 (prnn-sample-env)) (Some 8))

; Comprehension and explicit partial operations.
!(assertEqual (prnn-term (compr xreg zero) 0) (Some 0))
!(assertEqual (prnn-ev (divi xreg zero) (5) (0) (prnn-default-env)) None)
!(assertEqual (prnn-ev (modu xreg zero) (5) (0) (prnn-default-env)) None)
!(assertEqual (prnn-ev (pop yreg) (0) () (prnn-default-env)) None)
!(assertEqual (prnn-ev (embv xreg) (0) (0) (prnn-default-env)) None)
