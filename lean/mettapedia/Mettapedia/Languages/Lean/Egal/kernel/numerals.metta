; Arithmetic on the reading's numerals, as kernel theorems.
;
; A numeral of the document is a tower of ordsucc below a bound and, from
; there on, quotient :: last digit (terms.metta: wire:natural).  Lean's
; kernel adds and multiplies literals by arithmetic and not by recursion;
; here the same sums are theorems, made from the Digits library by the
; schoolbook: one digit a step, a table lemma for each pair of digits, a
; carry lemma where the digits pass ten.
;
;   (Cv.numeral)              add_nat a b, mul_nat a b and ordsucc a between
;                             numerals: (Conv NUMERAL THEOREM)
;   (num:value TERM)          the number a numeral is, or None
;   (num:add E CONTEXT A B)   add_nat D(a) D(b) = D(a+b), D the form with
;                             every digit apart
;   (num:mul E CONTEXT A B)   mul_nat D(a) D(b) = D(a*b)
;   (num:succ E CONTEXT A)    ordsucc D(a) = D(a+1)
;   (Cv.numeral-lemma)        Lean's division, remainder, subtraction and
;                             order decision between numerals, each by the
;                             library's lemma with its witnesses computed
;   (num:order E CONTEXT P)   a :e b for numerals a below b, or None
;
; The numbers are CeTTa's integers (exact at any size); they only say which
; lemma comes next.  A wrong step is a theorem the kernel does not make.
; Read after typing.metta.

(= (num:div10 $n) (/ (- $n (% $n 10)) 10))
(= (num:value $t)
   (case $t
     (((Tm.named $e) (if (== $e (lean:id "Empty")) 0 None))
      ((Tm.app (Tm.named $s) $m)
       (if (== $s (lean:id "ordsucc")) (let $v (num:value $m) (if (== $v None) None (+ $v 1))) None))
      ((Tm.app (Tm.app (Tm.named $d) $q) $r)
       (if (== $d (lean:id "NumD"))
           (let* (($vq (num:value $q)) ($vr (num:value $r)))
             (if (== $vq None) None (if (== $vr None) None (+ (* 10 $vq) $vr))))
           None))
      ($other None))))
; The number of a term that is the document's numeral for it.
(= (num:numeral-value $t)
   (let $v (num:value $t) (if (== $v None) None (if (== $t (wire:natural $v)) $v None))))
; D(n): every digit apart.
(= (num:digits $n)
   (if (< $n 10) (wire:literal $n)
       (let* (($q (num:digits (num:div10 $n))) ($d (wire:literal (% $n 10))))
         (Tm.app (Tm.app (wire:named "NumD") $q) $d))))
(= (num:pair $q $d) (Tm.app (Tm.app (wire:named "NumD") $q) $d))
(= (num:sum $x $y) (Tm.app (Tm.app (wire:named "add_nat") $x) $y))
(= (num:product $x $y) (Tm.app (Tm.app (wire:named "mul_nat") $x) $y))
(= (num:next $x) (Tm.app (wire:named "ordsucc") $x))

; A known of the library by its source name, and one instantiated: its
; quantifiers take TERMS in order, its equation premises are the GIVEN
; theorems, its nat_p premises are proved by the typing prover.
(= (num:known $E $ctx $source) (mg:known-in (eq:theory $E) $ctx (lean:id $source)))
(= (num:instance $E $ctx $source $terms $given)
   (let* (($known (num:known $E $ctx $source)) ($statement (mg:proposition $known)))
     (case (rule:instantiate $E $ctx (Prover.num $given) None $known $statement 0 (num:binds $terms 0))
       (((Instance $thm $stated) $thm)
        ($other (Error (num:instance $source) (LeanUnproved "a premise of the lemma")))))))
(= (num:binds $terms $k)
   (if (== $terms ()) ()
       (let* (($t (car-atom $terms)) ($rest (num:binds (cdr-atom $terms) (+ $k 1)))) (cons-atom ($k $t) $rest))))
(= (conv:witness-with (Prover.num $given) $E $ctx $body $k $binds) None)
(= (conv:prove-with (Prover.num $given) $E $ctx $p)
   (let $found (num:given $p $given)
     (if (== $found None)
         (let $typed (typ:prove $E $ctx () $p) (if (== $typed None) (empty) $typed))
         $found)))
; The given theorem that states the premise as it is written.  (No kernel
; conversion: unfolding add_nat on numerals would compute them in unary.)
(= (num:given $p $given)
   (if (== $given ()) None
       (if (== (mgt:beta (mg:proposition (car-atom $given))) (mgt:beta $p)) (car-atom $given)
           (num:given $p (cdr-atom $given)))))
(= (num:name $prefix $i) (format-args "{}{}" ($prefix $i)))
(= (num:name2 $prefix $i $j) (format-args "{}{}_{}" ($prefix $i $j)))
; f X = f Y from X = Y, f a function of one place written with its hole.
(= (num:within $E $ctx $context $x $y $xy) (eq:cong $E $ctx (Tm.lam (Tp.base 0) $context) $x $y $xy))
; P X from P Y and X = Y.
(= (num:back $E $ctx $property $x $y $xy $py) (eq:mp $E $ctx (Tm.lam (Tp.base 0) $property) $x $y $xy $py))

; The document's numeral of n equals D(n).
(= (num:to-digits $E $ctx $n)
   (if (< $n 10) (eq:refl $E $ctx (wire:literal $n))
       (if (< $n (num-bound)) (num:known $E $ctx (num:name "NumD_lit_" $n))
           (let* (($qn (num:div10 $n)) ($d (wire:literal (% $n 10)))
                  ($q (wire:natural $qn)) ($q2 (num:digits $qn))
                  ($eq-q (num:to-digits $E $ctx $qn)) ($eq-d (eq:refl $E $ctx $d)))
             (num:instance $E $ctx "NumD_cong" ($q $q2 $d $d) ($eq-q $eq-d))))))

; The sum of two digits, or one more: the table lemma, and past nine its
; value written 1 :: x.
(= (num:digit-sum $E $ctx $prefix $left $a $b $s)
   (let $table (num:known $E $ctx (num:name2 $prefix $a $b))
     (if (< $s 10) $table
         (eq:trans $E $ctx $left (wire:literal $s) (num:digits $s) $table
                   (num:known $E $ctx (num:name "NumD_lit_" $s))))))
; add_nat da db = add_nat 10 x, or the same of ordsucc (add_nat da db).
(= (num:digit-carry $E $ctx $prefix $left $a $b $s)
   (eq:trans $E $ctx $left (wire:literal $s) (num:sum (wire:literal 10) (wire:literal (- $s 10)))
             (num:known $E $ctx (num:name2 $prefix $a $b))
             (num:known $E $ctx (num:name "Dsplit_" $s))))

(= (num:add $E $ctx $a $b)
   (if (== $b 0) (let $x (num:digits $a) (num:instance $E $ctx "add_nat_0R" ($x) ()))
       (if (== $a 0) (let $y (num:digits $b) (num:instance $E $ctx "add_nat_0L" ($y) ()))
           (if (< $a 10)
               (if (< $b 10)
                   (num:digit-sum $E $ctx "Dadd_" (num:sum (wire:literal $a) (wire:literal $b)) $a $b (+ $a $b))
                   (num:long $E $ctx plain $a $b))
               (num:long $E $ctx plain $a $b)))))
; ordsucc (add_nat D(a) D(b)) = D(a+b+1)
(= (num:addc $E $ctx $a $b)
   (if (< $a 10)
       (if (< $b 10)
           (num:digit-sum $E $ctx "Daddc_" (num:next (num:sum (wire:literal $a) (wire:literal $b))) $a $b (+ (+ $a $b) 1))
           (num:long $E $ctx carried $a $b))
       (num:long $E $ctx carried $a $b)))
; One column: the last digits by the table, the rest by the sum of the
; quotients, with a carry into them where the digits pass ten.  A number of
; one digit stands as 0 :: digit for the step and is written back after it.
(= (num:long $E $ctx $mode $a $b)
   (let* (($da (% $a 10)) ($db (% $b 10)) ($qa (num:div10 $a)) ($qb (num:div10 $b))
          ($s (if (== $mode plain) (+ $da $db) (+ (+ $da $db) 1)))
          ($QA (num:digits $qa)) ($QB (num:digits $qb)) ($DA (wire:literal $da)) ($DB (wire:literal $db))
          ($column (num:sum $DA $DB))
          ($left (if (== $mode plain) $column (num:next $column)))
          ($prefix (if (== $mode plain) "Dadd_" "Daddc_"))
          ($A (num:pair $QA $DA)) ($B (num:pair $QB $DB)))
     (if (< $s 10)
         (let* (($QC (num:digits (+ $qa $qb))) ($DC (wire:literal $s))
                ($high (num:add $E $ctx $qa $qb))
                ($low (num:known $E $ctx (num:name2 $prefix $da $db)))
                ($step (num:instance $E $ctx (if (== $mode plain) "NumD_add_step" "NumD_addc_step")
                                     ($QA $QB $DA $DB $QC $DC) ($high $low))))
           (num:unpad $E $ctx $mode $a $b $A $B (num:pair $QC $DC) $step))
         (let* (($QC (num:digits (+ (+ $qa $qb) 1))) ($DC (wire:literal (- $s 10)))
                ($high (num:addc $E $ctx $qa $qb))
                ($low (num:digit-carry $E $ctx $prefix $left $da $db $s))
                ($step (num:instance $E $ctx (if (== $mode plain) "NumD_add_carry" "NumD_addc_carry")
                                     ($QA $QB $DA $DB $QC $DC) ($high $low))))
           (num:unpad $E $ctx $mode $a $b $A $B (num:pair $QC $DC) $step)))))
(= (num:whole $mode $x $y) (if (== $mode plain) (num:sum $x $y) (num:next (num:sum $x $y))))
(= (num:unpad $E $ctx $mode $a $b $A $B $C $step)
   (let* (($first (if (< $a 10) (num:unpad-one $E $ctx $a (eq:of $E (num:whole $mode (Tm.db 0) $B) $C) $step) $step))
          ($A2 (if (< $a 10) (wire:literal $a) $A)))
     (if (< $b 10) (num:unpad-one $E $ctx $b (eq:of $E (num:whole $mode $A2 (Tm.db 0)) $C) $first) $first)))
; From a statement about 0 :: d the same about d.
(= (num:unpad-one $E $ctx $d $property $about-padded)
   (let* (($D (wire:literal $d)) ($padded (num:pair (wire:literal 0) $D))
          ($zero (num:instance $E $ctx "NumD_zero" ($D) ())))
     (num:back $E $ctx $property $D $padded (eq:sym $E $ctx $padded $D $zero) $about-padded)))

(= (num:mul $E $ctx $a $b)
   (if (== $b 0) (let $x (num:digits $a) (num:instance $E $ctx "mul_nat_0R" ($x) ()))
       (if (== $a 0) (let $y (num:digits $b) (num:instance $E $ctx "mul_nat_0L" ($y) ()))
           (if (< $b 10) (num:mul-digit $E $ctx $a $b) (num:mul-long $E $ctx $a $b)))))
; A times a digit: A times one less, and A added.
(= (num:mul-digit $E $ctx $a $b)
   (let* (($A (num:digits $a)) ($less (wire:literal (- $b 1))) ($p (* $a (- $b 1)))
          ($P (num:digits $p)) ($R (num:digits (* $a $b)))
          ($t0 (num:product $A (wire:literal $b)))
          ($t1 (num:sum $A (num:product $A $less)))
          ($t2 (num:sum $A $P))
          ($unfold (num:instance $E $ctx "mul_nat_SR" ($A $less) ()))
          ($inner (num:mul $E $ctx $a (- $b 1)))
          ($lifted (num:within $E $ctx (num:sum (mgt:shift $A 1 0) (Tm.db 0)) (num:product $A $less) $P $inner))
          ($added (num:add $E $ctx $a $p)))
     (eq:trans $E $ctx $t0 $t1 $R $unfold (eq:trans $E $ctx $t1 $t2 $R $lifted $added))))
; A times q :: d is (A times q) :: 0 and A times d, added.
(= (num:mul-long $E $ctx $a $b)
   (let* (($d (% $b 10)) ($q (num:div10 $b))
          ($A (num:digits $a)) ($Q (num:digits $q)) ($D (wire:literal $d))
          ($pq (* $a $q)) ($pd (* $a $d))
          ($PQ (num:digits $pq)) ($PD (num:digits $pd)) ($zero (wire:literal 0))
          ($t0 (num:product $A (num:pair $Q $D)))
          ($t1 (num:sum (num:pair (num:product $A $Q) $zero) (num:product $A $D)))
          ($t2 (num:sum (num:pair $PQ $zero) (num:product $A $D)))
          ($t3 (num:sum (num:pair $PQ $zero) $PD))
          ($R (num:digits (* $a $b)))
          ($split (num:instance $E $ctx "mul_NumD" ($A $Q $D) ()))
          ($high (num:mul $E $ctx $a $q))
          ($low (num:mul $E $ctx $a $d))
          ($lift-high (num:within $E $ctx (num:sum (num:pair (Tm.db 0) $zero) (num:product $A $D)) (num:product $A $Q) $PQ $high))
          ($lift-low (num:within $E $ctx (num:sum (num:pair $PQ $zero) (Tm.db 0)) (num:product $A $D) $PD $low))
          ($added (num:add $E $ctx (* 10 $pq) $pd)))
     (eq:trans $E $ctx $t0 $t1 $R $split
       (eq:trans $E $ctx $t1 $t2 $R $lift-high (eq:trans $E $ctx $t2 $t3 $R $lift-low $added)))))

(= (num:succ $E $ctx $a)
   (if (< $a 9) (eq:refl $E $ctx (wire:literal (+ $a 1)))
       (if (== $a 9) (num:known $E $ctx "NumD_lit_10")
           (if (< (% $a 10) 9)
               (let* (($Q (num:digits (num:div10 $a))) ($D (wire:literal (% $a 10))))
                 (num:instance $E $ctx "NumD_S" ($Q $D) ()))
               (let* (($A (num:digits $a)) ($R (num:digits (+ $a 1)))
                      ($with-zero (num:addc $E $ctx $a 0))
                      ($plain (num:instance $E $ctx "add_nat_0R" ($A) ())))
                 (num:back $E $ctx (eq:of $E (num:next (Tm.db 0)) $R) $A (num:sum $A (wire:literal 0))
                           (eq:sym $E $ctx (num:sum $A (wire:literal 0)) $A $plain) $with-zero))))))

; Between the document's numerals: both sides taken to D, the sum made
; there, the result taken back.
(= (num:binary $E $ctx $op $a $b)
   (let* (($Na (wire:natural $a)) ($Nb (wire:natural $b)) ($Da (num:digits $a)) ($Db (num:digits $b))
          ($c (if (== $op add) (+ $a $b) (* $a $b)))
          ($Nc (wire:natural $c)) ($Dc (num:digits $c))
          ($t0 (num:apply $op $Na $Nb)) ($t1 (num:apply $op $Da $Nb)) ($t2 (num:apply $op $Da $Db))
          ($left (num:within $E $ctx (num:apply $op (Tm.db 0) $Nb) $Na $Da (num:to-digits $E $ctx $a)))
          ($right (num:within $E $ctx (num:apply $op $Da (Tm.db 0)) $Nb $Db (num:to-digits $E $ctx $b)))
          ($made (if (== $op add) (num:add $E $ctx $a $b) (num:mul $E $ctx $a $b)))
          ($back (eq:sym $E $ctx $Nc $Dc (num:to-digits $E $ctx $c))))
     (Conv $Nc (eq:trans $E $ctx $t0 $t1 $Nc $left
                 (eq:trans $E $ctx $t1 $t2 $Nc $right (eq:trans $E $ctx $t2 $Dc $Nc $made $back))))))
(= (num:apply $op $x $y) (if (== $op add) (num:sum $x $y) (num:product $x $y)))
(= (num:successor $E $ctx $a)
   (let* (($Na (wire:natural $a)) ($Da (num:digits $a)) ($Nc (wire:natural (+ $a 1))) ($Dc (num:digits (+ $a 1)))
          ($left (num:within $E $ctx (num:next (Tm.db 0)) $Na $Da (num:to-digits $E $ctx $a)))
          ($made (num:succ $E $ctx $a))
          ($back (eq:sym $E $ctx $Nc $Dc (num:to-digits $E $ctx (+ $a 1)))))
     (Conv $Nc (eq:trans $E $ctx (num:next $Na) (num:next $Da) $Nc $left
                 (eq:trans $E $ctx (num:next $Da) $Dc $Nc $made $back)))))
(= (conv:run-with (Cv.numeral) $E $ctx $t)
   (case $t
     (((Tm.app (Tm.app (Tm.named $op) $x) $y)
       (if (== $op (lean:id "add_nat")) (num:between $E $ctx add $x $y)
           (if (== $op (lean:id "mul_nat")) (num:between $E $ctx mul $x $y) Same)))
      ((Tm.app (Tm.named $op) $x)
       (if (== $op (lean:id "ordsucc"))
           (let $a (num:numeral-value $x)
             (if (== $a None) Same
                 (if (== (num:next $x) (wire:natural (+ $a 1))) Same (num:successor $E $ctx $a))))
           Same))
      ($other Same))))
(= (num:between $E $ctx $op $x $y)
   (let* (($a (num:numeral-value $x)) ($b (num:numeral-value $y)))
     (if (== $a None) Same (if (== $b None) Same (num:binary $E $ctx $op $a $b)))))

; Lean's functions between numerals.  The library states each with the
; numbers written as the lemma needs them: a dividend as q * n + r, the
; larger number of an order as m + k.  The witnesses are computed here, the
; lemma instantiated, and its left side, whose value is the term, is taken
; to the term by the arithmetic above.
(= (conv:run-with (Cv.numeral-lemma) $E $ctx $t)
   (case $t
     (((Tm.app (Tm.app (Tm.named $f) (Tm.app (Tm.named $l1) $x)) (Tm.app (Tm.named $l2) $y))
       (if (== $l1 (lean:id "LeanNum"))
           (if (== $l2 (lean:id "LeanNum"))
               (let* (($m (num:numeral-value $x)) ($n (num:numeral-value $y)))
                 (if (== $m None) Same (if (== $n None) Same (num:lemma-for $E $ctx $f $m $n $t))))
               Same)
           Same))
      ($other Same))))
(= (num:lemma-for $E $ctx $f $m $n $t)
   (if (== $f (lean:id "Lean_Nat_div")) (if (< $n 1) Same (num:euclid $E $ctx "Lean_Nat_div_num" $m $n $t))
       (if (== $f (lean:id "Lean_Nat_mod")) (if (< $n 1) Same (num:euclid $E $ctx "Lean_Nat_mod_num" $m $n $t))
           (if (== $f (lean:id "Lean_Nat_sub")) (if (< $m $n) Same (num:minus $E $ctx $m $n $t))
               (if (== $f (lean:id "Lean_Nat_decLe"))
                   (if (> $m $n) (num:not-le $E $ctx $m $n $t) (num:le $E $ctx $m $n $t))
                   Same)))))
(= (num:euclid $E $ctx $source $m $n $t)
   (let* (($r (% $m $n)) ($q (/ (- $m $r) $n))
          ($N1 (wire:natural (- $n 1))) ($R (wire:natural $r)) ($Q (wire:natural $q)))
     (num:presented $E $ctx $t (num:instance $E $ctx $source ($N1 $R $Q) ()))))
(= (num:le $E $ctx $m $n $t)
   (let* (($M (wire:natural $m)) ($K (wire:natural (- $n $m))))
     (num:presented $E $ctx $t (num:instance $E $ctx "Lean_Nat_decLe_num_true" ($M $K) ()))))
(= (num:not-le $E $ctx $m $n $t)
   (let* (($M (wire:natural $m)) ($N (wire:natural $n)))
     (num:presented $E $ctx $t (num:instance $E $ctx "Lean_Nat_decLe_num_false" ($M $N) ()))))
(= (num:minus $E $ctx $m $n $t)
   (let* (($k (- $m $n)) ($K (wire:natural $k)) ($N (wire:natural $n)) ($M (wire:natural $m)))
     (case (num:binary $E $ctx add $k $n)
       (((Conv $same $sum) (num:presented $E $ctx $t (num:instance $E $ctx "LeanNum_sub_eq" ($K $N $M) ($sum))))
        ($other Same)))))
; An instance L = R of a lemma, where the value of L is the term: the term = R.
(= (num:presented $E $ctx $t $instance)
   (case $instance
     (((Error $call $why) Same)
      ($thm
       (case (eq:sides $E (mgt:beta (mg:proposition $thm)))
         (((Sides $left $right)
           (if (== $left $t) (Conv $right $thm)
               (case (conv:run $E $ctx (Cv.eval (Cv.numeral)) $left)
                 (((Conv $value $equation)
                   (if (== $value $t)
                       (Conv $right (eq:trans $E $ctx $t $left $right (eq:sym $E $ctx $left $t $equation) $thm))
                       Same))
                  ($other Same)))))
          ($other Same)))))))

; a :e b between numerals, a below b: a :e ordsucc (a + k) by In_ordsucc_add,
; and a + k is the numeral before b.
(= (num:order $E $ctx $q)
   (case (typ:parts $q)
     (((Member $X $Y)
       (let* (($x (num:numeral-value $X)) ($y (num:value $Y)))
         (if (== $x None) None (if (== $y None) None (if (< $x $y) (num:below $E $ctx $x $X $y $Y) None)))))
      ($other None))))
(= (num:below $E $ctx $x $X $y $Y)
   (let* (($k (- (- $y 1) $x)) ($K (wire:natural $k)) ($P (wire:natural (- $y 1)))
          ($base (num:instance $E $ctx "In_ordsucc_add" ($X $K) ())))
     (case (num:binary $E $ctx add $x $k)
       (((Conv $same $equation)
         (let $before (num:back $E $ctx (typ:member $X (num:next (Tm.db 0))) $P (num:sum $X $K)
                                (eq:sym $E $ctx (num:sum $X $K) $P $equation) $base)
           (if (== $Y (num:next $P)) $before
               (case (num:successor $E $ctx (- $y 1))
                 (((Conv $numeral $next)
                   (if (== $numeral $Y)
                       (num:back $E $ctx (typ:member $X (Tm.db 0)) $Y (num:next $P)
                                 (eq:sym $E $ctx (num:next $P) $Y $next) $before)
                       None))
                  ($other None))))))
        ($other None)))))
