;; ============================================================
;;  02 · LANTERN LOGIC
;;  Discriminator: one authored rule set, two independent consumers
;; ============================================================
;;
;;  Question this instrument asks:
;;    Can ONE authored language definition (rules as data) drive BOTH
;;    an operational stepper (execution) and a judgment elaborator
;;    (derivability), with neither consumer defined in terms of the
;;    other — and do both reject the same stale certificate?
;;    This is the "GSLT generates NTT" architecture in miniature:
;;    if it works here, "inverse OSLF" is architecture, not slogan.
;;
;;  The language: lanterns that pass flame.
;;    (rule NAME premise1 premise2 conclusion)
;; ============================================================

;; --- the authored rule set (the ONLY place the language is defined) --
!(add-atom &self (rule pass-flame (lit $a) (unlit $b) (lit $b)))
!(add-atom &self (rule snuff      (lit $a) (windy $a) (unlit $a)))

;; --- the world -------------------------------------------------------
!(add-atom &self (fact (lit east)))
!(add-atom &self (fact (unlit west)))
!(add-atom &self (fact (unlit north)))

(= (holds $p) (match &self (fact $p) True))

;; --- CONSUMER 1: operational stepper ---------------------------------
;;  A step fires any rule instance whose premises hold, producing its
;;  conclusion as a new fact.  Rules are consulted as DATA.
(= (fireable)
   (match &self (rule $n $p1 $p2 $c)
     (if (holds $p1) (if (holds $p2) (fires $n $c) (empty)) (empty))))

!(println! "--- consumer 1 (operational): what can fire now? ---")
!(println! (collapse (fireable)))

;; --- CONSUMER 2: judgment elaborator ---------------------------------
;;  A goal is derivable if it is a fact, or some rule concludes it from
;;  derivable premises.  Same rule atoms, different reading.
(= (nonempty $l) (if (== $l ()) False True))
(= (fact? $p) (nonempty (collapse (holds $p))))
;;  A fact is derivable by itself; otherwise a rule whose premises are
;;  (recursively) derivable concludes it, up to a derivation depth.
;;  Derivations are ground because facts bind their variables when matched.
(= (derivable $g) (derivable-at $g 2))
(= (derivable-at $g $depth) (match &self (fact $g) (by-fact $g)))
(= (derivable-at $g $depth)
   (if (== $depth 0) (empty)
       (match &self (rule $n $p1 $p2 $g)
         (let $d1 (derivable-at $p1 (- $depth 1))
           (let $d2 (derivable-at $p2 (- $depth 1))
             (by-rule $n $d1 $d2 $g))))))

!(println! "--- consumer 2 (elaborator): is (lit west) derivable?  (ALL derivations to depth 2 —")
!(println! "    one direct, two detours: the proof-relevant fibre, visible) ---")
!(println! (collapse (derivable (lit west))))
!(println! "--- consumer 2: is (lit north) derivable? ---")
!(println! (collapse (derivable (lit north))))

;; --- agreement: the two consumers must concur ------------------------
;;  Operational says "pass-flame fires producing (lit west)";
;;  elaborator says "(lit west) by-rule pass-flame".  Same rule atom.
(= (op-reaches $c)   (match &self (rule $n $p1 $p2 $c)
                        (if (holds $p1) (if (holds $p2) yes (empty)) (empty))))
(= (agree-on $c)     (== (nonempty (collapse (op-reaches $c)))
                         (nonempty (collapse (derivable $c)))))

!(println! "--- agreement on (lit west): operational reaches it / elaborator derives it ---")
!(println! (operational (nonempty (collapse (op-reaches (lit west))))
            elaborator  (nonempty (collapse (derivable (lit west))))
            agree       (agree-on (lit west))))

;; --- certificates: replayed against the rule atoms --------------------
;;  (cert rule-name premise1 premise2 conclusion) claims one step.
(= (check-cert (cert $n $p1 $p2 $c))
   (case (collapse (match &self (rule $n $p1 $p2 $c) ok))
     (((ok) (if (holds $p1) (if (holds $p2) ACCEPT (REJECT premise2-fails))
                            (REJECT premise1-fails)))
      ($_ (REJECT no-such-rule-instance)))))

!(println! "--- honest certificate ---")
!(println! (check-cert (cert pass-flame (lit east) (unlit west) (lit west))))

!(println! "--- STALE certificate: conclusion tampered (north instead of west) ---")
!(println! (check-cert (cert pass-flame (lit east) (unlit west) (lit north))))

;; --- now MUTATE the language: change a rule, re-check the old cert ----
!(remove-atom &self (rule pass-flame (lit $a) (unlit $b) (lit $b)))
!(add-atom &self (rule pass-flame (lit $a) (unlit $b) (glowing $b)))

!(println! "--- after mutating pass-flame, the once-honest certificate: ---")
!(println! (check-cert (cert pass-flame (lit east) (unlit west) (lit west))))
!(println! "--- and the operational consumer now produces: ---")
!(println! (collapse (fireable)))

;; Reading: both consumers were driven by the same rule atoms and both
;; changed together when the atoms changed.  Neither was defined via the
;; other.  Prime's choice: is THIS the generation discipline (rules are
;; the single source; execution and elaboration are two functors out of
;; them), or do we keep hand-written interpreters that can drift apart?
