; The reader's terms and the kernel's terms are the same terms.
;
; For each test of the code-equation slice, the statement "the Lean term's
; reading equals the reading of CeTTa's answer" is built here from the
; reader's terms as kernel data (terms.metta) and compared with what the
; checked document states for that test (session.metta).
;
;   same      the kernel finds the two convertible
;   written   they are the same data as built, before any conversion
;   crossed   a test's term with the answer of another test, of the same type
;             and another value, is not convertible with the document's
;             statement
;
; It also writes two documents for the two checkers (check.sh): the built
; statements as Megalodon text, each closed by the document's own theorem,
; and one crossed statement closed the same way, which must be refused.
;
;   cetta ... check-statements.metta WORK   after the reader, session.metta and
;                                           terms.metta, with a session open

(= (statement-of $i)
   (let* (($t (comp-term $i)) ($T (comp-type $i)) ($v (readback (answer-of $i) $T)))
     (lean:eq (wire $t ()) (wire $v ()))))
(= (crossed-statement $i $j)
   (let* (($t (comp-term $i)) ($T (comp-type $j)) ($v (readback (answer-of $j) $T)))
     (lean:eq (wire $t ()) (wire $v ()))))
(= (convertible-with-test $built $i)
   (case (mg:try-convertible-bounded (lean:theory) (mg:empty-context) $built (lean:proposition (test-name $i)) 100000000)
     (((Error $call $why) False)
      ($answer $answer))))
(= (count-true $xs) (if (== $xs ()) 0 (+ (if (== (car-atom $xs) True) 1 0) (count-true (cdr-atom $xs)))))

(= (test-ids) (collapse (match &self (LeanTest $i) $i)))
(= (same-all $ids)
   (if (== $ids ()) ()
       (cons-atom (convertible-with-test (statement-of (car-atom $ids)) (car-atom $ids)) (same-all (cdr-atom $ids)))))
(= (written-all $ids)
   (if (== $ids ()) ()
       (cons-atom (== (statement-of (car-atom $ids)) (lean:proposition (test-name (car-atom $ids)))) (written-all (cdr-atom $ids)))))

; The crossed pairs: each test with the next one of its type and another answer.
(= (next-other $i $ids)
   (if (== $ids ()) None
       (let $j (car-atom $ids)
         (if (if (== (comp-type $i) (comp-type $j)) (not (== (answer-of $i) (answer-of $j))) False)
             $j (next-other $i (cdr-atom $ids))))))
(= (crossed-pairs $ids)
   (if (== $ids ()) ()
       (let $j (next-other (car-atom $ids) (cdr-atom $ids))
         (if (== $j None) (crossed-pairs (cdr-atom $ids))
             (cons-atom ((car-atom $ids) $j) (crossed-pairs (cdr-atom $ids)))))))
(= (refused-all $pairs)
   (if (== $pairs ()) ()
       (let ($i $j) (car-atom $pairs)
         (cons-atom (not (convertible-with-test (crossed-statement $i $j) $i)) (refused-all (cdr-atom $pairs))))))

(= (restated $prefix $statement $i)
   (format-args "Theorem {}_{} : {}.\nexact {}.\nQed.\n" ($prefix (test-name $i) (lean:text $statement) (test-name $i))))
(= (restated-all $ids)
   (if (== $ids ()) ()
       (cons-atom (restated "bridged" (statement-of (car-atom $ids)) (car-atom $ids)) (restated-all (cdr-atom $ids)))))

!(let* (($work (system:arg 0)) ($ids (test-ids)) ($pairs (crossed-pairs $ids))
        ($same (same-all $ids)) ($written (written-all $ids)) ($refused (refused-all $pairs))
        ($_r (fs:write (format-args "{}/restated.mg" ($work)) (join "" (restated-all $ids))))
        ($_c (case (car-atom $pairs)
               ((($i $j) (fs:write (format-args "{}/crossed.mg" ($work)) (restated "crossed" (crossed-statement $i $j) $i)))))))
   (println! (format-args "statements: {} tests; {} equal the document's in the kernel ({} as written); crossed: {} of {} refused"
                          ((length-of $ids) (count-true $same) (count-true $written) (count-true $refused) (length-of $pairs)))))
