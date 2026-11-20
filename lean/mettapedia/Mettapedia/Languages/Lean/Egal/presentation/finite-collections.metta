; A worked use of the finite-collection computations.
;
; Two questions about finite sets of numbers, asked as MeTTa calls of the
; definitions exported from Lean (Finset.range, Finset.sum, Finset.filter,
; Finset.card: Lean's own equation theorems, as MeTTa rules).  CeTTa answers
; each call by running those rules.  The same computation is a theorem of the
; Egal reading, checked by Megalodon and by mg-check; it is shown beside the
; answer, and its right side must be the reading of that answer.
;
; Run from the directory of the Egal reading, after the prelude and the rules
; of the code-equation slice:
;
;   cetta --lang petta --no-results CodeEquations/prelude.metta \
;         artifacts/lean-code-equations/core/rules.metta \
;         presentation/finite-collections.metta
;
; ../check.sh runs it and compares what it prints with
; finite-collections.expected.

!(import! &self fs)
!(import! &self str)
!(import! &self system)

; The two functions the calls pass: each number itself, and whether a number
; leaves no remainder by three.
(= (itself $n) (%id $n))
(= (multiple-of-three $x) (%instDecidableEqNat (Nat.mod $x 3) 0))

; (Use K TITLE LEAN CALL THEOREM): what is asked, how Lean writes it, the
; MeTTa call, and the theorem of generated/LeanComputations.mg for it.
(Use 1 "The sum of the numbers below eleven"
       "(Finset.range 11).sum id"
       (Finset.sum (Nat.instAddCommMonoid) (Finset.range 11) itself)
       "Lean_test_29")
(Use 2 "How many numbers below twenty are multiples of three"
       "(Finset.filter (fun x => x % 3 = 0) (Finset.range 20)).card"
       (Finset.card (Finset.filter multiple-of-three (Finset.range 20)))
       "Lean_test_30")
; The comparison is a real one: the first call beside the second theorem.
(Use 3 "The first call cited with the theorem of the second"
       "(Finset.range 11).sum id"
       (Finset.sum (Nat.instAddCommMonoid) (Finset.range 11) itself)
       "Lean_test_30")

; The statement of a theorem of the checked document: from its name to the
; full stop that ends it.
(= (statement-of $document $theorem)
   (let* (($start (str:find $document (format-args "Theorem {} : " ($theorem))))
          ($rest (str:byte-slice $document $start (str:byte-length $document)))
          ($end (str:find $rest ".\n")))
     (str:byte-slice $rest 0 (+ $end 1))))

(= (shown $document $title $lean $call $theorem)
   (let* (($answers (collapse (eval $call)))
          ($result (car-atom $answers))
          ($statement (statement-of $document $theorem))
          ($agrees (str:ends-with $statement (format-args "= (LeanNum {})." ($result)))))
     (format-args "{}\n  Lean     {}\n  MeTTa    {}\n  result   {}\n  checked  as a theorem of the Egal reading:\n{}\n  {}\n\n"
                  ($title $lean (quote $call) $result $statement
                   (if $agrees "The statement's right side is the reading of the result."
                               "NOT THE SAME: the statement's right side is not the reading of the result.")))))

(= (show $document $k)
   (match &self (Use $k $title $lean $call $theorem)
     (system:write stdout (shown $document $title $lean $call $theorem))))

!(let $document (fs:read-text "generated/LeanComputations.mg")
   (let $one (show $document 1) (let $two (show $document 2) (show $document 3))))
