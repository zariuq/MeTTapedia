; The tests by kernel conversion: the reader's term of a test is computed in
; the live theory, and the theorem the kernel made must state what the
; document's theorem of that test states.  Read after check-statements.metta.
;
; (computed-today) lists the tests that are computed this way.  Every one of
; them must be; the others are named as not yet.  A theorem of one test must
; not state another test's statement.  check.sh runs (compute:report I J) for
; each listed test I in a process of its own, J the next one listed.
(= (computed-today) (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30))
(= (compute:theorem $i)
   (let* (($t (wire (comp-term $i) ())) ($v (wire (readback (answer-of $i) (comp-type $i)) ())))
     (case (lean:compute $t)
       (((Conv $t2 $theorem) (if (== $t2 $v) $theorem stopped))
        ($other stopped)))))
(= (compute:states $theorem $j)
   (if (== $theorem stopped) False
       (case (mg:try-convertible (lean:theory) (mg:empty-context) (mg:proposition $theorem) (lean:proposition (test-name $j)))
         (((Error $call $why) False) ($same $same)))))
; "computed I OWN CROSSED": whether test I is computed to a theorem that
; states its own statement, and whether that theorem is refused as test J's.
(= (compute:report $i $j)
   (let* (($opened (lean:open-computation))
          ($theorem (compute:theorem $i))
          ($own (compute:states $theorem $i))
          ($other (compute:states $theorem $j)))
     (println! (format-args "computed {} {} {}" ($i (if $own yes no) (if $other accepted refused))))))
; "open I N VALUE": test I computed with what stays open carried as
; hypotheses: N premises are open, and VALUE says whether the value reached
; under them is the document's (same), another (differs: a premise that was
; assumed is false, or the computation is not finished), or none (stopped).
(= (compute:report-open $i)
   (let* (($opened (lean:open-computation))
          ($t (wire (comp-term $i) ()))
          ($v (wire (readback (answer-of $i) (comp-type $i)) ())))
     (case (lean:compute-open $t)
       (((Computed $value $theorem $premises)
         (println! (format-args "open {} {} {}" ($i (length-of $premises) (if (== $value $v) same differs)))))
        ((Stopped $premises) (println! (format-args "open {} {} stopped" ($i (length-of $premises)))))
        ($other (println! (format-args "open {} 0 stopped" ($i))))))))

