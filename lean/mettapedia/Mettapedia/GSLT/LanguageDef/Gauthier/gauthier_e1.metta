; # Gauthier E1 languageDef - MeTTa/CeTTa evaluator twin
;
; Executable mirror of `E1.lean`: one scalar-register evaluator over `(x,y,z)` plus an
; explicit store for the stateful array/turing variants.  Results are explicit
; `Some (res value store)` / `None`, so partial operations stay visible.
;
; Grounding:
;   repos/oeis-synthesis/src/exec.sml lines 126-146: scalar constants/registers/arithmetic.
;   repos/oeis-synthesis/src/exec.sml lines 160-172: array/read and assign.
;   repos/oeis-synthesis/src/exec.sml lines 192-201: turing next/prev/read/write.
;   repos/oeis-synthesis/src/exec.sml lines 218-227 and 271-277: loop/loope/compr.
;   repos/oeis-synthesis/src/exec.sml lines 290-299: array/minimal/turing evaluator order.

; ---- small store/list helpers -----------------------------------------------------------

(= (e1zero-store) (store (0 0 0 0 0 0 0 0) 0))
(= (e1input-store $k) (store ($k 0 0 0 0 0 0 0) 0))

(= (e1list-get $xs $i)
   (if (< $i 0)
       None
       (e1list-get-nonneg $xs $i)))

(= (e1list-get-nonneg $xs $i)
   (if (== (size-atom $xs) 0)
       None
       (if (== $i 0)
           (Some (car-atom $xs))
           (e1list-get-nonneg (cdr-atom $xs) (- $i 1)))))

(= (e1list-set $xs $i $v)
   (if (< $i 0)
       None
       (e1list-set-nonneg $xs $i $v)))

(= (e1list-set-nonneg $xs $i $v)
   (if (== (size-atom $xs) 0)
       None
       (if (== $i 0)
           (Some (cons-atom $v (cdr-atom $xs)))
           (e1list-set-cons (car-atom $xs)
                             (e1list-set-nonneg (cdr-atom $xs) (- $i 1) $v)))))

(= (e1list-set-cons $head $tail-result)
   (if (== $tail-result None)
       None
       (e1list-set-cons-some $head $tail-result)))

(= (e1list-set-cons-some $head (Some $tail))
   (Some (cons-atom $head $tail)))

(= (e1option-int-or-zero $r)
   (if (== $r None)
       0
       (e1option-int-or-zero-some $r)))

(= (e1option-int-or-zero-some (Some $v)) $v)

(= (e1array-read (store $tape $ptr) $i)
   (e1option-int-or-zero (e1list-get $tape $i)))

(= (e1store-write (store $tape $ptr) $i $v)
   (e1store-write-result (store $tape $ptr) $ptr (e1list-set $tape $i $v)))

(= (e1store-write-result $old $ptr $r)
   (if (== $r None)
       $old
       (e1store-write-result-some $ptr $r)))

(= (e1store-write-result-some $ptr (Some $tape))
   (store $tape $ptr))

(= (e1store-next (store $tape $ptr))
   (if (< (+ $ptr 1) (size-atom $tape))
       (Some (store $tape (+ $ptr 1)))
       None))

(= (e1store-prev (store $tape $ptr))
   (if (<= $ptr 0)
       (store $tape $ptr)
       (store $tape (- $ptr 1))))

(= (e1store-read-ptr (store $tape $ptr))
   (e1list-get $tape $ptr))

(= (e1store-write-ptr-noop (store $tape $ptr) $v)
   (if (== (e1list-get $tape $ptr) None)
       None
       (Some (store $tape $ptr))))

(= (e1result-value $r)
   (if (== $r None)
       None
       (e1result-value-some $r)))

(= (e1result-value-some (Some (res $v $st))) (Some $v))

; ---- evaluator core ---------------------------------------------------------------------

(= (e1ev zero $x $y $z $st) (Some (res 0 $st)))
(= (e1ev one $x $y $z $st) (Some (res 1 $st)))
(= (e1ev two $x $y $z $st) (Some (res 2 $st)))
(= (e1ev xreg $x $y $z $st) (Some (res $x $st)))
(= (e1ev yreg $x $y $z $st) (Some (res $y $st)))
(= (e1ev zreg $x $y $z $st) (Some (res $z $st)))

(= (e1ev (suc $p) $x $y $z $st)
   (e1unary suc (e1ev $p $x $y $z $st)))

(= (e1ev (pred $p) $x $y $z $st)
   (e1unary pred (e1ev $p $x $y $z $st)))

(= (e1unary $op $rp)
   (if (== $rp None)
       None
       (e1unary-some $op $rp)))

(= (e1unary-some suc (Some (res $v $st))) (Some (res (+ $v 1) $st)))
(= (e1unary-some pred (Some (res $v $st))) (Some (res (- $v 1) $st)))

(= (e1apply2 addi $a $b) (Some (+ $a $b)))
(= (e1apply2 diff $a $b) (Some (- $a $b)))
(= (e1apply2 mult $a $b) (Some (* $a $b)))
(= (e1apply2 divi $a $b) (if (== $b 0) None (Some (// $a $b))))
(= (e1apply2 modu $a $b) (if (== $b 0) None (Some (- $a (* $b (// $a $b))))))

(= (e1ev (addi $a $b) $x $y $z $st)
   (e1bin addi (e1ev $a $x $y $z $st) $b $x $y $z))
(= (e1ev (diff $a $b) $x $y $z $st)
   (e1bin diff (e1ev $a $x $y $z $st) $b $x $y $z))
(= (e1ev (mult $a $b) $x $y $z $st)
   (e1bin mult (e1ev $a $x $y $z $st) $b $x $y $z))
(= (e1ev (divi $a $b) $x $y $z $st)
   (e1bin divi (e1ev $a $x $y $z $st) $b $x $y $z))
(= (e1ev (modu $a $b) $x $y $z $st)
   (e1bin modu (e1ev $a $x $y $z $st) $b $x $y $z))

(= (e1bin $op $ra $b $x $y $z)
   (if (== $ra None)
       None
       (e1bin-left-some $op $ra $b $x $y $z)))

(= (e1bin-left-some $op (Some (res $va $st1)) $b $x $y $z)
   (e1bin-right $op $va (e1ev $b $x $y $z $st1)))

(= (e1bin-right $op $va $rb)
   (if (== $rb None)
       None
       (e1bin-right-some $op $va $rb)))

(= (e1bin-right-some $op $va (Some (res $vb $st2)))
   (e1bin-finish (e1apply2 $op $va $vb) $st2))

(= (e1bin-finish $r $st)
   (if (== $r None)
       None
       (e1bin-finish-some $r $st)))

(= (e1bin-finish-some (Some $v) $st) (Some (res $v $st)))

(= (e1ev (cond $c $t $e) $x $y $z $st)
   (e1cond (e1ev $c $x $y $z $st) $t $e $x $y $z))

(= (e1cond $rc $t $e $x $y $z)
   (if (== $rc None)
       None
       (e1cond-some $rc $t $e $x $y $z)))

(= (e1cond-some (Some (res $vc $st1)) $t $e $x $y $z)
   (if (<= $vc 0)
       (e1ev $t $x $y $z $st1)
       (e1ev $e $x $y $z $st1)))

; ---- scalar loops/search ----------------------------------------------------------------

(= (e1ev (loop $body $n $x0) $x $y $z $st)
   (e1loop-start (e1ev $n $x $y $z $st) $x0 $body $x $y $z))

(= (e1loop-start $rn $x0 $body $x $y $z)
   (if (== $rn None)
       None
       (e1loop-start-some $rn $x0 $body $x $y $z)))

(= (e1loop-start-some (Some (res $k $st1)) $x0 $body $x $y $z)
   (e1loop-x0 $k (e1ev $x0 $x $y $z $st1) $body))

(= (e1loop-x0 $k $rx0 $body)
   (if (== $rx0 None)
       None
       (e1loop-x0-some $k $rx0 $body)))

(= (e1loop-x0-some $k (Some (res $x0v $st2)) $body)
   (if (<= $k 0)
       (Some (res $x0v $st2))
       (e1loop $body $k $x0v 1 $x0v $st2 loop-counter)))

; The tagged worker carries the source counter explicitly.
(= (e1loop $body $k $x1 $x2 $x3 $st $tag)
   (if (<= $k 0)
       (Some (res $x1 $st))
       (e1loop-step2 $body $k $x2 $x3 (e1ev $body $x1 $x2 $x3 $st))))

(= (e1loop-step2 $body $k $x2 $x3 $rbody)
   (if (== $rbody None)
       None
       (e1loop-step2-some $body $k $x2 $x3 $rbody)))

(= (e1loop-step2-some $body $k $x2 $x3 (Some (res $x1p $stp)))
   (e1loop $body (- $k 1) $x1p (+ $x2 1) $x3 $stp loop-counter))

(= (e1ev (loop2 $f $g $n $a $b) $x $y $z $st)
   (e1loop2-start (e1ev $n $x $y $z $st) $a $b $f $g $x $y $z))

(= (e1loop2-start $rn $a $b $f $g $x $y $z)
   (if (== $rn None)
       None
       (e1loop2-start-some $rn $a $b $f $g $x $y $z)))

(= (e1loop2-start-some (Some (res $k $st1)) $a $b $f $g $x $y $z)
   (e1loop2-a $k (e1ev $a $x $y $z $st1) $b $f $g $x $y $z))

(= (e1loop2-a $k $ra $b $f $g $x $y $z)
   (if (== $ra None)
       None
       (e1loop2-a-some $k $ra $b $f $g $x $y $z)))

(= (e1loop2-a-some $k (Some (res $av $st2)) $b $f $g $x $y $z)
   (e1loop2-b $k $av (e1ev $b $x $y $z $st2) $f $g))

(= (e1loop2-b $k $av $rb $f $g)
   (if (== $rb None)
       None
       (e1loop2-b-some $k $av $rb $f $g)))

(= (e1loop2-b-some $k $av (Some (res $bv $st3)) $f $g)
   (e1loop2 $f $g $k $av $bv 1 $st3))

(= (e1loop2 $f $g $k $x1 $x2 $x3 $st)
   (if (<= $k 0)
       (Some (res $x1 $st))
       (e1loop2-step $f $g $k $x1 $x2 $x3 (e1ev $f $x1 $x2 $x3 $st))))

(= (e1loop2-step $f $g $k $x1 $x2 $x3 $rf)
   (if (== $rf None)
       None
       (e1loop2-step-f-some $f $g $k $x1 $x2 $x3 $rf)))

(= (e1loop2-step-f-some $f $g $k $x1 $x2 $x3 (Some (res $x1p $stf)))
   (e1loop2-step-g $f $g $k $x3 $x1p (e1ev $g $x1 $x2 $x3 $stf)))

(= (e1loop2-step-g $f $g $k $x3 $x1p $rg)
   (if (== $rg None)
       None
       (e1loop2-step-g-some $f $g $k $x3 $x1p $rg)))

(= (e1loop2-step-g-some $f $g $k $x3 $x1p (Some (res $x2p $stg)))
   (e1loop2 $f $g (- $k 1) $x1p $x2p (+ $x3 1) $stg))

(= (e1ev (compr $f $n) $x $y $z $st)
   (e1compr-start (e1ev $n $x $y $z $st) $f))

(= (e1compr-start $rn $f)
   (if (== $rn None)
       None
       (e1compr-start-some $rn $f)))

(= (e1compr-start-some (Some (res $target $st1)) $f)
   (if (< $target 0)
       (e1compr $f 0 0 0 $st1)
       (e1compr $f $target 0 0 $st1)))

(= (e1compr $f $target $seen $cand $st)
   (e1compr-check $f $target $seen $cand (e1ev $f $cand 0 0 $st)))

(= (e1compr-check $f $target $seen $cand $rv)
   (if (== $rv None)
       None
       (e1compr-check-some $f $target $seen $cand $rv)))

(= (e1compr-check-some $f $target $seen $cand (Some (res $v $stp)))
   (if (<= $v 0)
       (if (>= $seen $target)
           (Some (res $cand $stp))
           (e1compr $f $target (+ $seen 1) (+ $cand 1) $stp))
       (e1compr $f $target $seen (+ $cand 1) $stp)))

; ---- array and turing operations --------------------------------------------------------

(= (e1ev (array $a) $x $y $z $st)
   (e1array (e1ev $a $x $y $z $st)))

(= (e1array $ra)
   (if (== $ra None)
       None
       (e1array-some $ra)))

(= (e1array-some (Some (res $idx $st1)))
   (Some (res (e1array-read $st1 $idx) $st1)))

(= (e1ev (assign $a $b) $x $y $z $st)
   (e1assign-left (e1ev $a $x $y $z $st) $b $x $y $z))

(= (e1assign-left $ra $b $x $y $z)
   (if (== $ra None)
       None
       (e1assign-left-some $ra $b $x $y $z)))

(= (e1assign-left-some (Some (res $idx $st1)) $b $x $y $z)
   (e1assign-right $idx (e1ev $b $x $y $z $st1)))

(= (e1assign-right $idx $rb)
   (if (== $rb None)
       None
       (e1assign-right-some $idx $rb)))

(= (e1assign-right-some $idx (Some (res $v $st2)))
   (Some (res 0 (e1store-write $st2 $idx $v))))

(= (e1ev next $x $y $z $st)
   (e1next (e1store-next $st)))

(= (e1next $r)
   (if (== $r None)
       None
       (e1next-some $r)))

(= (e1next-some (Some $st)) (Some (res 0 $st)))

(= (e1ev prev $x $y $z $st)
   (Some (res 0 (e1store-prev $st))))

(= (e1ev read $x $y $z $st)
   (e1read (e1store-read-ptr $st) $st))

(= (e1read $rv $st)
   (if (== $rv None)
       None
       (e1read-some $rv $st)))

(= (e1read-some (Some $v) $st) (Some (res $v $st)))

(= (e1ev (write $a) $x $y $z $st)
   (e1write (e1ev $a $x $y $z $st)))

(= (e1write $ra)
   (if (== $ra None)
       None
       (e1write-some $ra)))

(= (e1write-some (Some (res $v $st1)))
   (e1write-finish (e1store-write-ptr-noop $st1 $v)))

(= (e1write-finish $rst)
   (if (== $rst None)
       None
       (e1write-finish-some $rst)))

(= (e1write-finish-some (Some $st2)) (Some (res 0 $st2)))

(= (e1ev (loope $body $n) $x $y $z $st)
   (e1loope-start (e1ev $n $x $y $z $st) $body))

(= (e1loope-start $rn $body)
   (if (== $rn None)
       None
       (e1loope-start-some $rn $body)))

(= (e1loope-start-some (Some (res $k $st1)) $body)
   (e1loope $body $k $st1))

(= (e1loope $body $k $st)
   (if (<= $k 0)
       (Some (res 0 $st))
       (e1loope-step $body $k (e1ev $body 0 0 0 $st))))

(= (e1loope-step $body $k $rbody)
   (if (== $rbody None)
       None
       (e1loope-step-some $body $k $rbody)))

(= (e1loope-step-some $body $k (Some (res $v $stp)))
   (e1loope $body (- $k 1) $stp))

; ---- table-order metadata ---------------------------------------------------------------

(= (e1-array-op-name 9) xreg)
(= (e1-array-op-name 10) yreg)
(= (e1-array-op-name 11) array)
(= (e1-array-op-name 12) assign)
(= (e1-array-op-name 13) loop)

; ---- OEIS seeded terms ------------------------------------------------------------------

(= (e1term-store $p $k $st)
   (e1result-value (e1ev $p $k 0 0 $st)))

(= (e1term $p $k)
   (e1term-store $p $k (e1zero-store)))

(= (e1turing-term $p $k)
   (e1term-store $p $k (e1input-store $k)))

; ---- executable validation --------------------------------------------------------------

; Minimal: identity and doubling.
!(assertEqual (e1term xreg 7) (Some 7))
!(assertEqual (e1term (loop (suc xreg) xreg xreg) 7) (Some 14))

; E1 `org`: factorial by `loop (mult x y) x one`.
!(assertEqual (e1term (loop (mult xreg yreg) xreg one) 0) (Some 1))
!(assertEqual (e1term (loop (mult xreg yreg) xreg one) 4) (Some 24))
!(assertEqual (e1term (loop (mult xreg yreg) xreg one) 6) (Some 720))

; Array follows evaluator order: ids 9/10/11/12/13 are x/y/array/assign/loop.
!(assertEqual (e1-array-op-name 9) xreg)
!(assertEqual (e1-array-op-name 13) loop)

; Array: assign cell 0 from x, then read it through the same sequential evaluator.
!(assertEqual (e1term (addi (assign zero xreg) (array zero)) 5) (Some 5))
!(assertEqual (e1term (loop (addi xreg one) xreg xreg) 7) (Some 14))

; Turing: input lives in tape cell 0; source write is a no-op read check.
!(assertEqual (e1turing-term read 7) (Some 7))
!(assertEqual (e1turing-term (addi (write two) read) 4) (Some 4))

; Partial-operation validation.
!(assertEqual (e1ev (divi xreg zero) 5 0 0 (e1zero-store)) None)
!(assertEqual (e1ev (modu xreg zero) 5 0 0 (e1zero-store)) None)
!(assertEqual (e1ev next 0 0 0 (store (0) 0)) None)
!(assertEqual (e1ev read 0 0 0 (store () 0)) None)
!(assertEqual (e1term (array xreg) 99) (Some 0))
