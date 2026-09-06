;; ============================================================
;;  08 · TWO LIBRARIANS
;;  Discriminator: cost and provenance under extensional equality
;; ============================================================
;;
;;  Question this instrument asks:
;;    Two librarians answer the same question with the same number.
;;    One read it from a cache computed at revision 2; the other
;;    recomputed it at revision 3.  Extensionally equal.  May the
;;    system erase the difference?  For which clients?
;;
;;  What to look for: the answer column is identical; the receipt
;;  columns are not; and whether "compact erasure" is lawful flips
;;  depending on the client.  Cost, freshness, and provenance are
;;  observer-indexed valuations — not parts of the answer, not
;;  nothing.
;; ============================================================

;; --- the ledger by revision -----------------------------------------
!(add-atom &self (sighting s1 raven black 1))
!(add-atom &self (sighting s2 raven black 1))
!(add-atom &self (sighting s3 raven black 2))
!(add-atom &self (sighting s4 crow  black 3))      ; rev 3 added a CROW
(= (count-black-ravens $rev)
   (length (collapse (match &self (sighting $id raven black $r)
                       (if (<= $r $rev) $id (empty))))))

;; --- librarian A: answers from a cache built at revision 2 ------------
(= (cache-answer) 3)
(= (librarian-a) (Answer 3 (Receipt (source cache) (built-at 2) (energy 1))))

;; --- librarian B: recomputes at revision 3 ------------------------------
(= (librarian-b)
   (let $n (count-black-ravens 3)
     (Answer $n (Receipt (source fresh) (built-at 3) (energy 7)))))

(= (answer-of  (Answer $n $r)) $n)
(= (receipt-of (Answer $n $r)) $r)

!(println! "--- the two answers ---")
!(println! (A (librarian-a)))
!(println! (B (librarian-b)))
!(println! "--- extensionally equal? ---")
(= (same-answer) (== (answer-of (librarian-a)) (answer-of (librarian-b))))
!(println! (answers (answer-of (librarian-a)) (answer-of (librarian-b))))
!(println! (equal (same-answer)))

;; --- clients = observers of the (Answer, Receipt) pair -----------------
(= (client-pure    (Answer $n $r)) $n)
(= (client-fresh   (Answer $n (Receipt $s (built-at $b) $e))) ($n fresh-as-of $b))
(= (client-budget  (Answer $n (Receipt $s $b (energy $e)))) ($n cost $e))
(= (client-auditor (Answer $n (Receipt (source $s) $b $e))) ($n from $s))

(= (erasure-lawful-for $client)
   (if (== ($client (librarian-a)) ($client (librarian-b)))
       (ERASURE-LAWFUL client-cannot-tell)
       (ERASURE-FAILS client-distinguishes)))

!(println! "--- may the receipt be erased to the bare answer? ---")
!(println! (pure-client    (erasure-lawful-for client-pure)))
!(println! (fresh-client   (erasure-lawful-for client-fresh)))
!(println! (budget-client  (erasure-lawful-for client-budget)))
!(println! (auditor-client (erasure-lawful-for client-auditor)))

;; --- fairness: a scheduler valuation, also an observer -------------------
;;  Two schedules with identical answer sets; one starved librarian B.
(= (schedule-fair)     ((serve a) (serve b) (serve a) (serve b)))
(= (schedule-starving) ((serve a) (serve a) (serve a) (serve a)))
(= (answers-of $sched) (n-black-ravens 3))          ; both yield the same answers
(= (served $who $sched) (length (collapse (let $s (superpose $sched) (case $s (((serve $who) $who) ($_ (empty))))))))
!(println! "--- same answers, different fairness (a valuation on the history) ---")
!(println! (fair     (b-served (served b (schedule-fair)))))
!(println! (starving (b-served (served b (schedule-starving)))))

;; Reading: the answer is the extensional readout; receipts, cost, and
;; schedule fairness are valuations on the history beneath it.  Prime's
;; choice: do these belong in judgmental equality (never), in a modality
;; (maybe, for freshness), or only as observer-indexed valuations that a
;; declared client may or may not see (the shape this file exhibits)?
