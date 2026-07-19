; # Gauthier E2 languageDef - MeTTa/CeTTa evaluator twin
;
; Executable mirror of `E2.lean`: one two-list evaluator core with scalar `org`, list ops,
; matchback, ramsey edge, arcagi, and `loop2snd` operations sharing the same semantics.
; Results are explicit `Some list` / `None` so partial operations stay visible.

; ---- option/list helpers ---------------------------------------------------------------

(= (e2head-list $xs)
   (if (== (size-atom $xs) 0)
       None
       (Some (car-atom $xs))))

(= (e2head-result $r)
   (if (== $r None)
       None
       (e2head-result-some $r)))

(= (e2head-result-some (Some $xs))
   (e2head-list $xs))

(= (e2singleton-incr $xs)
   (if (== (size-atom $xs) 0)
       None
       (Some ((+ (car-atom $xs) 1)))))

(= (e2apply2 addi $a $b) (Some (+ $a $b)))
(= (e2apply2 diff $a $b) (Some (- $a $b)))
(= (e2apply2 mult $a $b) (Some (* $a $b)))
(= (e2apply2 divi $a $b) (if (== $b 0) None (Some (// $a $b))))
(= (e2apply2 modu $a $b) (if (== $b 0) None (Some (- $a (* $b (// $a $b))))))

(= (e2mkE $op $ra $rb)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (e2mkE-some $op $ra $rb))))

(= (e2mkE-some $op (Some $va) (Some $vb))
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $vb) 0)
           None
           (e2mkE-finish (e2apply2 $op (car-atom $va) (car-atom $vb)) (cdr-atom $va)))))

(= (e2mkE-finish $r $tail)
   (if (== $r None)
       None
       (e2mkE-finish-some $r $tail)))

(= (e2mkE-finish-some (Some $c) $tail)
   (Some (cons-atom $c $tail)))

; ---- world/oracle helpers ---------------------------------------------------------------

(= (e2default-back $i)
   (if (== $i 0) (Some -57)
   (if (== $i 1) (Some 19)
   (if (== $i 2) (Some -58)
   (if (== $i 3) (Some 100)
   (if (== $i 4) (Some -46)
   (if (== $i 5) (Some 0)
   (if (== $i 6) (Some 39)
   (if (== $i 7) (Some 82)
   (if (== $i 8) (Some 89)
   (if (== $i 9) (Some 1)
   (if (== $i 10) (Some 81)
   (if (== $i 11) (Some -83)
   (if (== $i 12) (Some 49)
   (if (== $i 13) (Some 94)
   (if (== $i 14) (Some 59)
   (if (== $i 15) (Some 55)
       None)))))))))))))))))

(= (e2edge3 $i)
   (if (== $i 0) (Some 7)
   (if (== $i 1) (Some 8)
   (if (== $i 2) (Some 9)
   (if (== $i 3) (Some 7)
   (if (== $i 4) (Some 8)
   (if (== $i 5) (Some 9)
       None)))))))

(= (e2world-back $world $i)
   (e2default-back $i))

(= (e2world-edge $world $i)
   (if (== $world edge3) (e2edge3 $i) None))

(= (e2world-matrix $world $a $b)
   (if (and (== $a 0) (== $b 0)) (Some 0) None))

(= (e2world-color $world $i)
   (if (== $i 0) (Some 0) None))

(= (e2world-dim $world inputHeight) 1)
(= (e2world-dim $world inputWidth) 1)
(= (e2world-dim $world commonHeight) 1)
(= (e2world-dim $world commonWidth) 1)

; ---- evaluator core ---------------------------------------------------------------------

(= (e2ev zero $x $y $world) (Some (0)))
(= (e2ev one $x $y $world) (Some (1)))
(= (e2ev two $x $y $world) (Some (2)))
(= (e2ev xreg $x $y $world) (Some $x))
(= (e2ev yreg $x $y $world) (Some $y))

(= (e2ev (addi $a $b) $x $y $world)
   (e2mkE addi (e2ev $a $x $y $world) (e2ev $b $x $y $world)))
(= (e2ev (diff $a $b) $x $y $world)
   (e2mkE diff (e2ev $a $x $y $world) (e2ev $b $x $y $world)))
(= (e2ev (mult $a $b) $x $y $world)
   (e2mkE mult (e2ev $a $x $y $world) (e2ev $b $x $y $world)))
(= (e2ev (divi $a $b) $x $y $world)
   (e2mkE divi (e2ev $a $x $y $world) (e2ev $b $x $y $world)))
(= (e2ev (modu $a $b) $x $y $world)
   (e2mkE modu (e2ev $a $x $y $world) (e2ev $b $x $y $world)))

(= (e2ev (cond $c $t $e) $x $y $world)
   (e2cond (e2ev $c $x $y $world) $t $e $x $y $world))

(= (e2cond $rc $t $e $x $y $world)
   (if (== $rc None)
       None
       (e2cond-some $rc $t $e $x $y $world)))

(= (e2cond-some (Some $vc) $t $e $x $y $world)
   (if (== (size-atom $vc) 0)
       None
       (if (<= (car-atom $vc) 0)
           (e2ev $t $x $y $world)
           (e2ev $e $x $y $world))))

(= (e2ev (push $a $b) $x $y $world)
   (e2push (e2ev $a $x $y $world) (e2ev $b $x $y $world)))

(= (e2push $ra $rb)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (e2push-some $ra $rb))))

(= (e2push-some (Some $va) (Some $vb))
   (if (== (size-atom $va) 0)
       None
       (Some (cons-atom (car-atom $va) $vb))))

(= (e2ev (pop $a) $x $y $world)
   (e2pop (e2ev $a $x $y $world)))

(= (e2pop $ra)
   (if (== $ra None)
       None
       (e2pop-some $ra)))

(= (e2pop-some (Some $va))
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $va) 1)
           (Some $va)
           (Some (cdr-atom $va)))))

(= (e2ev (loop $body $n $x0) $x $y $world)
   (e2loop-start (e2ev $n $x $y $world) (e2ev $x0 $x $y $world) $body $world))

(= (e2loop-start $rn $rx0 $body $world)
   (if (== $rn None)
       None
       (if (== $rx0 None)
           None
           (e2loop-start-some $rn $rx0 $body $world))))

(= (e2loop-start-some (Some $vn) (Some $vx0) $body $world)
   (if (== (size-atom $vn) 0)
       None
       (if (< (car-atom $vn) 0)
           (Some $vx0)
           (e2loop $body (car-atom $vn) $vx0 (1) $world))))

(= (e2loop $body $k $x1 $x2 $world)
   (if (<= $k 0)
       (Some $x1)
       (e2loop-step $body $k $x1 $x2 $world)))

(= (e2loop-step $body $k $x1 $x2 $world)
   (e2loop-step-results $body $k (e2ev $body $x1 $x2 $world) (e2singleton-incr $x2) $world))

(= (e2loop-step-results $body $k $rx1 $rx2 $world)
   (if (== $rx1 None)
       None
       (if (== $rx2 None)
           None
           (e2loop-step-results-some $body $k $rx1 $rx2 $world))))

(= (e2loop-step-results-some $body $k (Some $x1p) (Some $x2p) $world)
   (e2loop $body (- $k 1) $x1p $x2p $world))

(= (e2ev (loop2 $f $g $n $a $b) $x $y $world)
   (e2loop2-start (e2ev $n $x $y $world) (e2ev $a $x $y $world) (e2ev $b $x $y $world) $f $g $world))

(= (e2loop2-start $rn $ra $rb $f $g $world)
   (if (== $rn None)
       None
       (if (== $ra None)
           None
           (if (== $rb None)
               None
               (e2loop2-start-some $rn $ra $rb $f $g $world)))))

(= (e2loop2-start-some (Some $vn) (Some $va) (Some $vb) $f $g $world)
   (if (== (size-atom $vn) 0)
       None
       (if (< (car-atom $vn) 0)
           (Some $va)
           (e2loop2 $f $g (car-atom $vn) $va $vb $world))))

(= (e2loop2 $f $g $k $x1 $x2 $world)
   (if (<= $k 0)
       (Some $x1)
       (e2loop2-step $f $g $k $x1 $x2 $world)))

(= (e2loop2-step $f $g $k $x1 $x2 $world)
   (e2loop2-step-results $f $g $k (e2ev $f $x1 $x2 $world) (e2ev $g $x1 $x2 $world) $world))

(= (e2loop2-step-results $f $g $k $rx1 $rx2 $world)
   (if (== $rx1 None)
       None
       (if (== $rx2 None)
           None
           (e2loop2-step-results-some $f $g $k $rx1 $rx2 $world))))

(= (e2loop2-step-results-some $f $g $k (Some $x1p) (Some $x2p) $world)
   (e2loop2 $f $g (- $k 1) $x1p $x2p $world))

(= (e2ev (loop2snd $f $g $n $a $b) $x $y $world)
   (e2loop2snd-start (e2ev $n $x $y $world) (e2ev $a $x $y $world) (e2ev $b $x $y $world) $f $g $world))

(= (e2loop2snd-start $rn $ra $rb $f $g $world)
   (if (== $rn None)
       None
       (if (== $ra None)
           None
           (if (== $rb None)
               None
               (e2loop2snd-start-some $rn $ra $rb $f $g $world)))))

(= (e2loop2snd-start-some (Some $vn) (Some $va) (Some $vb) $f $g $world)
   (if (== (size-atom $vn) 0)
       None
       (if (< (car-atom $vn) 0)
           (Some $vb)
           (e2loop2snd $f $g (car-atom $vn) $va $vb $world))))

(= (e2loop2snd $f $g $k $x1 $x2 $world)
   (if (<= $k 0)
       (Some $x2)
       (e2loop2snd-step $f $g $k $x1 $x2 $world)))

(= (e2loop2snd-step $f $g $k $x1 $x2 $world)
   (e2loop2snd-step-results $f $g $k (e2ev $f $x1 $x2 $world) (e2ev $g $x1 $x2 $world) $world))

(= (e2loop2snd-step-results $f $g $k $rx1 $rx2 $world)
   (if (== $rx1 None)
       None
       (if (== $rx2 None)
           None
           (e2loop2snd-step-results-some $f $g $k $rx1 $rx2 $world))))

(= (e2loop2snd-step-results-some $f $g $k (Some $x1p) (Some $x2p) $world)
   (e2loop2snd $f $g (- $k 1) $x1p $x2p $world))

(= (e2ev (compr $f $n) $x $y $world)
   (e2compr-start (e2ev $n $x $y $world) $f $world))

(= (e2compr-start $rn $f $world)
   (if (== $rn None)
       None
       (e2compr-start-some $rn $f $world)))

(= (e2compr-start-some (Some $vn) $f $world)
   (if (== (size-atom $vn) 0)
       None
       (if (< (car-atom $vn) 0)
           None
           (e2compr $f (car-atom $vn) 0 (0) $world))))

(= (e2compr $f $target $seen $cand $world)
   (e2compr-check $f $target $seen $cand (e2ev $f $cand (0) $world) $world))

(= (e2compr-check $f $target $seen $cand $rv $world)
   (if (== $rv None)
       None
       (e2compr-check-some $f $target $seen $cand $rv $world)))

(= (e2compr-check-some $f $target $seen $cand (Some $v) $world)
   (if (== (size-atom $v) 0)
       None
       (if (<= (car-atom $v) 0)
           (if (>= $seen $target)
               (Some $cand)
               (e2compr-next $f $target (+ $seen 1) $cand $world))
           (e2compr-next $f $target $seen $cand $world))))

(= (e2compr-next $f $target $seen $cand $world)
   (e2compr-next-incr $f $target $seen (e2singleton-incr $cand) $world))

(= (e2compr-next-incr $f $target $seen $rcand $world)
   (if (== $rcand None)
       None
       (e2compr-next-incr-some $f $target $seen $rcand $world)))

(= (e2compr-next-incr-some $f $target $seen (Some $candp) $world)
   (e2compr $f $target $seen $candp $world))

; ---- variant/oracle operations ----------------------------------------------------------

(= (e2ev (back $a) $x $y $world)
   (e2back (e2ev $a $x $y $world) $world))

(= (e2back $ra $world)
   (if (== $ra None)
       None
       (e2back-some $ra $world)))

(= (e2back-some (Some $va) $world)
   (if (== (size-atom $va) 0)
       None
       (if (< (car-atom $va) 0)
           (Some (0))
           (e2back-value (e2world-back $world (car-atom $va))))))

(= (e2back-value $rv)
   (if (== $rv None)
       None
       (e2back-value-some $rv)))

(= (e2back-value-some (Some $v))
   (Some ($v)))

(= (e2ev (edge $a) $x $y $world)
   (e2edge (e2ev $a $x $y $world) $world))

(= (e2edge $ra $world)
   (if (== $ra None)
       None
       (e2edge-some $ra $world)))

(= (e2edge-some (Some $va) $world)
   (if (== (size-atom $va) 0)
       None
       (e2edge-value (e2world-edge $world (car-atom $va)))))

(= (e2edge-value $rv)
   (if (== $rv None)
       None
       (e2edge-value-some $rv)))

(= (e2edge-value-some (Some $v))
   (Some ($v)))

(= (e2ev (equalcolor $a $b $c $d) $x $y $world)
   (e2equalcolor
      (e2ev $a $x $y $world) (e2ev $b $x $y $world)
      (e2ev $c $x $y $world) (e2ev $d $x $y $world) $world))

(= (e2equalcolor $ra $rb $rc $rd $world)
   (if (== $ra None) None
   (if (== $rb None) None
   (if (== $rc None) None
   (if (== $rd None) None
       (e2equalcolor-some $ra $rb $rc $rd $world))))))

(= (e2equalcolor-some (Some $va) (Some $vb) (Some $vc) (Some $vd) $world)
   (if (== (size-atom $va) 0) None
   (if (== (size-atom $vb) 0) None
   (if (== (size-atom $vc) 0) None
   (if (== (size-atom $vd) 0) None
       (e2equalcolor-values
          (e2world-matrix $world (car-atom $va) (car-atom $vb))
          (e2world-matrix $world (car-atom $vc) (car-atom $vd))))))))

(= (e2equalcolor-values $ca $cb)
   (if (== $ca None)
       (Some (-1))
       (if (== $cb None)
           (Some (-1))
           (e2equalcolor-values-some $ca $cb))))

(= (e2equalcolor-values-some (Some $ca) (Some $cb))
   (if (== $ca $cb) (Some (1)) (Some (0))))

(= (e2ev (isOut $a $b) $x $y $world)
   (e2isOut (e2ev $a $x $y $world) (e2ev $b $x $y $world) $world))

(= (e2isOut $ra $rb $world)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (e2isOut-some $ra $rb $world))))

(= (e2isOut-some (Some $va) (Some $vb) $world)
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $vb) 0)
           None
           (if (== (e2world-matrix $world (car-atom $va) (car-atom $vb)) None)
               (Some (1))
               (Some (0))))))

(= (e2ev (isColori $a $b $c) $x $y $world)
   (e2isColori (e2ev $a $x $y $world) (e2ev $b $x $y $world) (e2ev $c $x $y $world) $world))

(= (e2isColori $ra $rb $rc $world)
   (if (== $ra None) None
   (if (== $rb None) None
   (if (== $rc None) None
       (e2isColori-some $ra $rb $rc $world)))))

(= (e2isColori-some (Some $va) (Some $vb) (Some $vc) $world)
   (if (== (size-atom $va) 0) None
   (if (== (size-atom $vb) 0) None
   (if (== (size-atom $vc) 0) None
       (e2isColori-values
          (e2world-matrix $world (car-atom $va) (car-atom $vb))
          (e2world-color $world (car-atom $vc)))))))

(= (e2isColori-values $cell $color)
   (if (== $cell None)
       (Some (-1))
       (if (== $color None)
           (Some (-1))
           (e2isColori-values-some $cell $color))))

(= (e2isColori-values-some (Some $cell) (Some $color))
   (if (== $cell $color) (Some (1)) (Some (0))))

(= (e2ev (isEqual $a $b) $x $y $world)
   (e2isEqual (e2ev $a $x $y $world) (e2ev $b $x $y $world)))

(= (e2isEqual $ra $rb)
   (if (== $ra None)
       None
       (if (== $rb None)
           None
           (e2isEqual-some $ra $rb))))

(= (e2isEqual-some (Some $va) (Some $vb))
   (if (== (size-atom $va) 0)
       None
       (if (== (size-atom $vb) 0)
           None
           (if (== (car-atom $va) (car-atom $vb)) (Some (1)) (Some (0))))))

(= (e2ev inputHeight $x $y $world) (Some ((e2world-dim $world inputHeight))))
(= (e2ev inputWidth $x $y $world) (Some ((e2world-dim $world inputWidth))))
(= (e2ev commonHeight $x $y $world) (Some ((e2world-dim $world commonHeight))))
(= (e2ev commonWidth $x $y $world) (Some ((e2world-dim $world commonWidth))))

; ---- OEIS seeded terms ------------------------------------------------------------------

(= (e2term $p $k)
   (e2term-world $p $k default))

(= (e2term-world $p $k $world)
   (e2head-result (e2ev $p ($k) (0) $world)))

; ---- executable validation --------------------------------------------------------------

; E2 `org`: factorial by `loop (mult x y) x one`.
!(assertEqual (e2term (loop (mult xreg yreg) xreg one) 0) (Some 1))
!(assertEqual (e2term (loop (mult xreg yreg) xreg one) 1) (Some 1))
!(assertEqual (e2term (loop (mult xreg yreg) xreg one) 4) (Some 24))
!(assertEqual (e2term (loop (mult xreg yreg) xreg one) 6) (Some 720))

; List ops: push the input onto `[0]`, then pop back to `[0]`.
!(assertEqual (e2term (pop (push xreg yreg)) 5) (Some 0))

; Matchback default vector.
!(assertEqual (e2term (back xreg) 0) (Some -57))
!(assertEqual (e2term (back xreg) 3) (Some 100))
!(assertEqual (e2term (back xreg) 4) (Some -46))

; Ramsey edge oracle with the explicit `[7,8,9]` world used by the Lean probe.
!(assertEqual (e2term-world (edge xreg) 0 edge3) (Some 7))
!(assertEqual (e2term-world (edge xreg) 3 edge3) (Some 7))
!(assertEqual (e2term-world (edge xreg) 4 edge3) (Some 8))

; Arcagi default 1x1 matrix and dimensions.
!(assertEqual (e2term (equalcolor zero zero zero zero) 0) (Some 1))
!(assertEqual (e2term (isOut xreg zero) 0) (Some 0))
!(assertEqual (e2term (isOut xreg zero) 1) (Some 1))
!(assertEqual (e2term inputHeight 0) (Some 1))
!(assertEqual (e2term commonWidth 0) (Some 1))

; SMT `loop2snd`: increment the second register `x` times and return it.
!(assertEqual (e2term (loop2snd (addi xreg one) (addi yreg one) xreg xreg yreg) 0) (Some 0))
!(assertEqual (e2term (loop2snd (addi xreg one) (addi yreg one) xreg xreg yreg) 5) (Some 5))

; Partial-operation validation.
!(assertEqual (e2ev (divi xreg zero) (5) (0) default) None)
!(assertEqual (e2ev (modu xreg zero) (5) (0) default) None)
!(assertEqual (e2ev (pop yreg) (0) () default) None)
!(assertEqual (e2ev (back xreg) (99) (0) default) None)
!(assertEqual (e2ev (edge xreg) (0) (0) default) None)
