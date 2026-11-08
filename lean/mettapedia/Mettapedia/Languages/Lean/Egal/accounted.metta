; Every expected test has exactly one outcome: joined (one theorem
; Lean_test_N) or refused (one reason "test N: ..." among the refusals).
;
;   cetta --lang petta accounted.metta OUTCOMES.tsv ANSWERS.metta COMPUTATIONS.mg REFUSALS.txt
;
; (OUTCOMES.tsv comes first: --lang petta reads leading .metta arguments as programs.)
;
; The expected tests are the (LeanTest N) facts of ANSWERS.metta, one per Lean
; test whether or not CeTTa answered it, so that the denominator cannot shrink.
; OUTCOMES.tsv gets one row per expected test (a target may have none: its
; theorems are its claims).  A test with no outcome, two
; theorems, two reasons, or both a theorem and a reason, and an outcome for a
; test that is not expected, are defects of the generator: they are named on
; standard error and the exit status is 1.

!(import! &self fs)
!(import! &self str)
!(import! &self system)

(= (nth-of $xs $k) (if (== $k 0) (car-atom $xs) (nth-of (cdr-atom $xs) (- $k 1))))
(= (len-of $xs) (if (== $xs ()) 0 (+ 1 (len-of (cdr-atom $xs)))))
(= (append-lists $xs $ys) (if (== $xs ()) $ys (cons-atom (car-atom $xs) (append-lists (cdr-atom $xs) $ys))))

; The number spelled by a nonempty run of digits, or None.
(= (digits-number $s)
   (if (== $s "") None
       (if (str:is-all-in digit $s) (str:string->number $s) None)))

; (LeanTest 13) -> 13
(= (expected-id $line)
   (if (not (str:starts-with $line "(LeanTest ")) None
       (let* (($ws (str:split-whitespace $line)) ($w (nth-of $ws 1)) ($n (str:byte-length $w)))
         (if (str:ends-with $w ")") (digits-number (str:byte-slice $w 0 (- $n 1))) None))))

; Theorem Lean_test_13 : ... -> 13; Theorem Lean_test_13_answer_typed : ... -> None
(= (joined-id $line)
   (if (not (str:starts-with $line "Theorem Lean_test_")) None
       (let* (($ws (str:split-whitespace $line)))
         (if (< (len-of $ws) 3) None
             (if (not (== (nth-of $ws 2) ":")) None
                 (let $w (nth-of $ws 1) (digits-number (str:byte-slice $w 10 (str:byte-length $w)))))))))

; test 13: reason -> (13 "reason")
(= (refusal-of $line)
   (if (not (str:starts-with $line "test ")) None
       (let $k (str:find $line ": ")
         (if (< $k 0) None
             (let $id (digits-number (str:byte-slice $line 5 $k))
               (if (== $id None) None
                   ($id (str:byte-slice $line (+ $k 2) (str:byte-length $line)))))))))

(= (ids-of $f $lines)
   (if (== $lines ()) ()
       (let* (($x ($f (car-atom $lines))) ($rest (ids-of $f (cdr-atom $lines))))
         (if (== $x None) $rest (cons-atom $x $rest)))))

(= (count-in $x $xs)
   (if (== $xs ()) 0 (+ (if (== (car-atom $xs) $x) 1 0) (count-in $x (cdr-atom $xs)))))
(= (refusal-ids $rs) (if (== $rs ()) () (cons-atom (car-atom (car-atom $rs)) (refusal-ids (cdr-atom $rs)))))
(= (reason-for $i $rs)
   (if (== $rs ()) ""
       (let ($j $why) (car-atom $rs) (if (== $j $i) $why (reason-for $i (cdr-atom $rs))))))

; (row text) or (defect text) for one expected test.
(= (outcome $i $joined $refused)
   (let* (($j (count-in $i $joined)) ($r (count-in $i (refusal-ids $refused))))
     (if (and (== $j 1) (== $r 0)) (row (format-args "{}\tjoined\t" ($i)))
     (if (and (== $j 0) (== $r 1)) (row (format-args "{}\trefused\t{}" ($i (reason-for $i $refused))))
     (if (and (== $j 0) (== $r 0)) (defect (format-args "test {}: neither a theorem nor a reason" ($i)))
     (if (and (> $j 0) (> $r 0)) (defect (format-args "test {}: both a theorem and a reason" ($i)))
     (if (> $j 1) (defect (format-args "test {}: {} theorems" ($i $j)))
         (defect (format-args "test {}: {} reasons" ($i $r))))))))))

(= (outcomes $ids $joined $refused)
   (if (== $ids ()) ()
       (cons-atom (outcome (car-atom $ids) $joined $refused) (outcomes (cdr-atom $ids) $joined $refused))))

; Outcomes for tests that are not expected.
(= (unexpected $xs $expected $what)
   (if (== $xs ()) ()
       (let $rest (unexpected (cdr-atom $xs) $expected $what)
         (if (== (count-in (car-atom $xs) $expected) 0)
             (cons-atom (defect (format-args "test {}: a {} for a test that is not expected" ((car-atom $xs) $what))) $rest)
             $rest))))

(= (texts-of $tag $os)
   (if (== $os ()) ()
       (let $rest (texts-of $tag (cdr-atom $os))
         (case (car-atom $os) ((($tag $t) (cons-atom $t $rest)) ($_ $rest))))))

(= (account $answers $comps $refusals $out)
   (let* (($expected (ids-of expected-id (fs:read-lines $answers)))
          ($joined (ids-of joined-id (fs:read-lines $comps)))
          ($refused (ids-of refusal-of (fs:read-lines $refusals)))
          ($os (outcomes $expected $joined $refused))
          ($extra (append-lists (unexpected $joined $expected "theorem")
                                (unexpected (refusal-ids $refused) $expected "reason")))
          ($rows (texts-of row $os))
          ($defects (append-lists (texts-of defect $os) (texts-of defect $extra)))
          ($_w (fs:write $out (format-args "test\toutcome\treason\n{}\n" ((str:join "\n" $rows))))))
     (if (== $defects ())
         (println! (format-args "outcomes: {} expected, {} joined, {} refused" ((len-of $expected) (len-of $joined) (len-of $refused))))
         (let $_e (system:write stderr (format-args "accounted: generator defects:\n{}\n" ((str:join "\n" $defects))))
           (system:exit 1)))))


(= (missing $paths)
   (if (== $paths ()) ()
       (let $rest (missing (cdr-atom $paths)) (if (fs:exists (car-atom $paths)) $rest (cons-atom (car-atom $paths) $rest)))))

!(let* (($o (system:arg 0)) ($a (system:arg 1)) ($c (system:arg 2)) ($r (system:arg 3)) ($gone (missing ($a $c $r))))
   (if (== $gone ()) (account $a $c $r $o)
       (let $_e (system:write stderr (format-args "accounted: missing input {}\n" ((car-atom $gone)))) (system:exit 1))))
