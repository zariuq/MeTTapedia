;; ============================================================
;;  01 · THE TEA HOUSE MESSAGES
;;  Discriminator: revision-sensitive rho continuation
;; ============================================================
;;
;;  Question this instrument asks:
;;    A receipt records a delivered message together with the
;;    revision of the world at which it was delivered.  Two receipts
;;    carry the SAME message (same "endpoint").  May one be substituted
;;    for the other inside a continuation?
;;
;;  Candidate semantics simulated below:
;;    EXT  the continuation sees only the endpoint (the message)
;;         -> receipts with equal messages are interchangeable.
;;    INT  the continuation's type depends on the receipt itself
;;         (revision / owner / occurrence)
;;         -> equal messages, different receipts, different behavior.
;;
;;  What to look for in the output: the two continuations disagree on
;;  receipt r-late.  The observer table shows WHO can tell.
;;  If Prime keeps INT underneath and licenses EXT only per declared
;;  observer, both rows below are correct at once.
;; ============================================================

;; --- the world: a menu that changes at revision 5 ------------------
(= (price matcha 3) 4)      ; menu revision 3: matcha costs 4
(= (price matcha 7) 6)      ; menu revision 7: matcha costs 6
(= (current-revision) 7)
(= (price-now $item) (price $item (current-revision)))

;; --- two deliveries of the same order ------------------------------
;;  (Receipt message revision owner)
!(add-atom &self (Receipt matcha 3 guest-a))   ; ordered before the change
!(add-atom &self (Receipt matcha 7 guest-b))   ; ordered after the change

;; --- the endpoint: what an extensional observer sees ---------------
(= (endpoint (Receipt $m $r $o)) $m)

;; --- continuation, candidate EXT: reads only the endpoint ----------
(= (k-ext $receipt) (charge (endpoint $receipt) (price-now (endpoint $receipt))))

;; --- continuation, candidate INT: type depends on the receipt ------
(= (k-int (Receipt $m $r $o)) (charge $m (price $m $r) (for $o at-revision $r)))

;; --- run both continuations on both receipts -----------------------
!(println! "--- same endpoint? ---")
!(println! (collapse (match &self (Receipt $m $r $o) (endpoint (Receipt $m $r $o)))))

!(println! "--- candidate EXT: continuation on each receipt ---")
!(println! (collapse (match &self (Receipt $m $r $o) (k-ext (Receipt $m $r $o)))))

!(println! "--- candidate INT: continuation on each receipt ---")
!(println! (collapse (match &self (Receipt $m $r $o) (k-int (Receipt $m $r $o)))))

;; --- the substitution question, asked explicitly -------------------
(= (substitutable $k $r1 $r2) (== ($k $r1) ($k $r2)))
(= (r-early) (Receipt matcha 3 guest-a))
(= (r-late)  (Receipt matcha 7 guest-b))

!(println! "--- may r-early replace r-late inside the continuation? ---")
!(println! (EXT says (substitutable k-ext (r-early) (r-late))))
!(println! (INT says (substitutable k-int (r-early) (r-late))))

;; --- observer table -------------------------------------------------
;;  An observer is a function of the receipt.  Erasing the receipt down
;;  to its endpoint is lawful exactly for observers invariant under it.
(= (obs-endpoint $r) (endpoint $r))
(= (obs-charge   $r) (k-int $r))
(= (obs-audit    (Receipt $m $rev $o)) (audited $o $rev))

(= (erasure-lawful-for $obs)
   (if (== ($obs (r-early)) ($obs (r-late))) lawful NOT-lawful))

!(println! "--- erasure to endpoint, per observer ---")
!(println! (endpoint-observer (erasure-lawful-for obs-endpoint)))
!(println! (charge-observer   (erasure-lawful-for obs-charge)))
!(println! (audit-observer    (erasure-lawful-for obs-audit)))

;; Reading: "same message" is a fact about the extensional readout.
;; Whether it licenses substitution is a fact about the OBSERVER.
;; Prime's choice: is the receipt part of the continuation's type
;; (INT underneath, EXT licensed per observer), or is the endpoint the
;; whole story (EXT only, revision bugs invisible to the type system)?
