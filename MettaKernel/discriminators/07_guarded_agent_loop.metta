;; ============================================================
;;  07 · THE GARDENER'S DIARY
;;  Discriminator: a self-referential rule that revises itself
;; ============================================================
;;
;;  Question this instrument asks:
;;    The gardener's watering rule is itself revised by watering
;;    outcomes.  The rule affects its own next revision.  Which
;;    recursion discipline makes this well-defined?
;;
;;    NAIVE    today's rule refers to today's rule  -> no fixed point
;;             (we bound it with fuel and watch it fail to settle).
;;    GUARDED  today's rule refers only to YESTERDAY's rule (a "later"
;;             modality: every self-reference is behind one tick)
;;             -> a well-defined, stable stream of rules.
;;
;;  What to look for: NAIVE oscillates or refuses to converge inside
;;  its fuel; GUARDED produces a day-by-day sequence that settles.
;; ============================================================

;; --- the self-revising rule: watering amount --------------------------
;;  "water w; if the soil was dry after watering w, water more; else less"
;;  Soil dryness after watering w is 10 - w (a toy world).
(= (dry-after $w) (- 10 $w))

;; --- NAIVE: same-day self-reference, bounded by fuel -----------------
;;  amount(today) = if dry-after(amount(today)) > 3 then amount(today)+2 else amount(today)-1
;;  Unrolled with fuel; each unrolling asks for the very value it is
;;  defining.  Watch it never agree with itself.
(= (naive $fuel $guess)
   (if (== $fuel 0) (NO-FIXED-POINT last-guess $guess)
       (let $next (if (> (dry-after $guess) 3) (+ $guess 2) (- $guess 1))
         (if (== $next $guess) (FIXED $guess) (naive (- $fuel 1) $next)))))

(= (trace-naive $f $g)
   (if (== $f 0) ()
       (let $next (if (> (dry-after $g) 3) (+ $g 2) (- $g 1))
         (cons-atom $g (trace-naive (- $f 1) $next)))))

!(println! "--- NAIVE: same-day self-reference (fuel 8, start 2) ---")
!(println! (naive 8 2))
!(println! (trace-naive 6 2))

;; --- GUARDED: the rule at day t+1 depends only on day t ---------------
;;  (amount 0) is given; (amount (t+1)) is computed from (amount t).
;;  Self-reference is always one tick behind: well-founded by construction.
(= (amount $t)
   (if (== $t 0) 2
       (let $prev (amount (- $t 1))
         (if (> (dry-after $prev) 3) (+ $prev 2) (- $prev 1)))))
(= (diary $t) (if (== $t 0) ((day 0 (amount 0)))
                  (let $rest (diary (- $t 1))
                    (cons-atom (day $t (amount $t)) $rest))))

!(println! "--- GUARDED: each day refers only to the previous day ---")
!(println! (diary 7))

;; --- what GUARDED buys and costs -------------------------------------
!(println! "--- the discipline in one line each ---")
!(println! (NAIVE   every-self-reference-is-a-fixed-point-obligation no-general-solution))
!(println! (GUARDED self-reference-only-behind-a-tick productive-by-construction))
!(println! (COST    the-tick-is-part-of-the-type the-agent-cannot-consult-its-own-current-rule))

;; Reading: an agent that revises its own rules is the normal case for
;; a world-modeling system.  Prime's choice: is "later" a native
;; modality (self-reference typed as productive, the guarded law an
;; invariant of the language), or a programming convention the agent
;; is trusted to follow?  The NAIVE column shows what the convention
;; is protecting you from.  (The cubical/path variant — transporting
;; the evolving state along a path of revisions — is the Agda-lab
;; experiment; it is not simulated here.)
