;; ============================================================
;;  03 · THE RAVEN LEDGER
;;  Discriminator: PLN evidence overlap — thin vs proof-relevant
;; ============================================================
;;
;;  Question this instrument asks:
;;    Two argument packets support "ravens are black".  As NUMBERS they
;;    are identical.  As PROVENANCE they may share a sighting.  Does
;;    the combination rule need to see the pair of routes, or only the
;;    two numbers?
;;
;;  Candidate semantics simulated below:
;;    THIN   combine by adding counts (only the numbers are visible).
;;    ROUTE  combine by taking the UNION of source sightings
;;           (the pair of routes and their overlap are visible).
;;
;;  What to look for: THIN gives the same answer for packet-beta and
;;  packet-beta-prime.  ROUTE does not.  Any consumer that must not
;;  double-count evidence is a consumer whose action differs on the
;;  two parallel routes — exactly the M1-vs-M2 discriminator, on a
;;  problem an AGI actually has.
;; ============================================================

;; --- sightings: (sighting id) — every one a black raven -------------
;;  evidence packets are lists of sighting ids
(= (alpha)      (s1 s2 s3))      ; 3 positive sightings
(= (beta)       (s3 s4))         ; 2 positive — SHARES s3 with alpha
(= (beta-prime) (s4 s5))         ; 2 positive — independent of alpha

;; --- list helpers ----------------------------------------------------
(= (has-elem $x $l)
   (if (== $l ()) False
       (if (== (car-atom $l) $x) True (has-elem $x (cdr-atom $l)))))
(= (merge-sources $a $b)
   (if (== $b ()) $a
       (let $h (car-atom $b)
         (if (has-elem $h $a) (merge-sources $a (cdr-atom $b))
                              (merge-sources (cons-atom $h $a) (cdr-atom $b))))))

;; --- counts-primal evidence: (n+ , n-) ; all sightings positive here --
(= (n-plus $packet) (length $packet))
(= (strength $n) (/ $n $n))                      ; all positive: 1
(= (confidence $n) (/ $n (+ $n 2)))               ; k = 2 prior weight

;; --- candidate THIN: combination sees only the counts ----------------
(= (thin-combine $p $q) (+ (n-plus $p) (n-plus $q)))

;; --- candidate ROUTE: combination sees the sources ---------------------
(= (route-combine $p $q) (n-plus (merge-sources $p $q)))

!(println! "--- the two packets look numerically identical ---")
!(println! (packet-beta (n+ (n-plus (beta))) packet-beta-prime (n+ (n-plus (beta-prime)))))

!(println! "--- THIN combination with alpha ---")
!(println! (alpha+beta       (n+ (thin-combine (alpha) (beta)))))
!(println! (alpha+beta-prime (n+ (thin-combine (alpha) (beta-prime)))))

!(println! "--- ROUTE combination with alpha ---")
!(println! (alpha+beta       (n+ (route-combine (alpha) (beta)))
                             (sources (merge-sources (alpha) (beta)))))
!(println! (alpha+beta-prime (n+ (route-combine (alpha) (beta-prime)))
                             (sources (merge-sources (alpha) (beta-prime)))))

!(println! "--- resulting confidence (THIN vs ROUTE) ---")
!(println! (thin  alpha+beta (confidence (thin-combine (alpha) (beta)))
                  alpha+beta-prime (confidence (thin-combine (alpha) (beta-prime)))))
!(println! (route alpha+beta (confidence (route-combine (alpha) (beta)))
                  alpha+beta-prime (confidence (route-combine (alpha) (beta-prime)))))

;; --- the discriminator, stated as a boolean ---------------------------
(= (thin-distinguishes)  (if (== (thin-combine (alpha) (beta)) (thin-combine (alpha) (beta-prime))) False True))
(= (route-distinguishes) (if (== (route-combine (alpha) (beta)) (route-combine (alpha) (beta-prime))) False True))

!(println! "--- does the combination rule distinguish the two parallel routes? ---")
!(println! (THIN (thin-distinguishes) ROUTE (route-distinguishes)))

;; Reading: a revision/combination rule that must avoid double-counting
;; is a required consumer that acts differently on two evidence routes
;; with identical numerical readouts.  Prime's choice: does that route
;; data live as ordinary dependent data (displayed over a thin mode
;; core, reified and quotable), or must the mode comparisons themselves
;; be proof-relevant?  Either way, THIN is disqualified as the semantics
;; of evidence.
