;; ============================================================
;;  05 · THE APPRENTICE CHECKER
;;  Discriminator: quoted self-inspection and kernel admission
;; ============================================================
;;
;;  Question this instrument asks:
;;    An agent reads its own (quoted) rule set, invents a new derived
;;    rule, and submits it with a certificate.  What must the kernel
;;    gate do?  Two gates are simulated:
;;
;;    TRUSTING  believes the generator's word ("this macro is fine").
;;    REPLAY    re-derives the certificate step by step against the
;;              BASE rules only, never consulting the generator.
;;
;;  What to look for: an honest macro passes both gates; a corrupted
;;  certificate passes TRUSTING and is rejected by REPLAY.  Generator
;;  severance is the difference between the two columns.
;; ============================================================

;; --- base rules (quoted data the agent can inspect) --------------------
!(add-atom &self (rule pass-flame (lit $a) (unlit $b) (lit $b)))
!(add-atom &self (fact (lit east)))
!(add-atom &self (fact (unlit mid)))
!(add-atom &self (fact (unlit west)))
(= (holds $p) (match &self (fact $p) True))

;; --- the agent inspects its rules ------------------------------------
!(println! "--- the agent reads its own rule set ---")
!(println! (collapse (match &self (rule $n $p1 $p2 $c) (quote (rule $n $p1 $p2 $c)))))

;; --- the agent synthesizes a derived rule: RELAY = two passes -----------
;;  relay: (lit a) (unlit m) (unlit w)  ==>  (lit w)
;;  with certificate = the base steps that justify it
(= (proposed-macro)
   (macro relay ((lit $a) (unlit $m) (unlit $w)) (lit $w)))
(= (honest-cert)
   (steps (cert pass-flame (lit east) (unlit mid)  (lit mid))
          (cert pass-flame (lit mid)  (unlit west) (lit west))))
;;  a corrupted certificate: skips the middle step
(= (corrupt-cert)
   (steps (cert pass-flame (lit east) (unlit west) (lit west))
          (cert pass-flame (lit east) (unlit mid)  (lit west))))   ; wrong conclusion

;; --- one certificate step, replayed against base rules ------------------
;;  A step is licensed iff some base rule instance matches it and its
;;  premises are established (facts or earlier established conclusions).
(= (step-ok (cert $n $p1 $p2 $c) $established)
   (case (collapse (match &self (rule $n $p1 $p2 $c) ok))
     (((ok) (if (known $p1 $established)
                (if (known $p2 $established) ok (bad-premise $p2))
                (bad-premise $p1)))
      ($_ (no-rule-instance (cert $n $p1 $p2 $c))))))
(= (known $p $established)
   (if (has-elem $p $established) True (case (collapse (holds $p)) (((True) True) ($_ False)))))
(= (has-elem $x $l)
   (if (== $l ()) False
       (if (== (car-atom $l) $x) True (has-elem $x (cdr-atom $l)))))

;; --- REPLAY gate: fold through the steps, accumulating conclusions -------
(= (replay $steps $est)
   (if (== $steps ()) (ACCEPT established $est)
       (let $s (car-atom $steps)
         (let $verdict (step-ok $s $est)
           (if (== $verdict ok)
               (let (cert $n $p1 $p2 $c) $s (replay (cdr-atom $steps) (cons-atom $c $est)))
               (REJECT $verdict))))))
(= (replay-gate (steps $a $b)) (replay ($a $b) ()))

;; --- TRUSTING gate: accepts whatever the generator asserts ---------------
(= (trusting-gate $cert) (ACCEPT because-the-generator-said-so))

!(println! "--- honest certificate ---")
!(println! (TRUSTING (trusting-gate (honest-cert))))
!(println! (REPLAY   (replay-gate (honest-cert))))

!(println! "--- corrupted certificate (generator severed: gate never asks it) ---")
!(println! (TRUSTING (trusting-gate (corrupt-cert))))
!(println! (REPLAY   (replay-gate (corrupt-cert))))

;; --- admission: only a replay-accepted macro becomes usable -------------
(= (admit $macro $cert)
   (let $r (replay-gate $cert)
     (let $head (car-atom $r)
       (if (== $head ACCEPT) (ADMITTED $macro) (NOT-ADMITTED $r)))))
!(println! "--- admission verdicts ---")
!(println! (admit (proposed-macro) (honest-cert)))
!(println! (admit (proposed-macro) (corrupt-cert)))

;; Reading: quotation lets the agent SEE its rules; admission requires
;; the kernel to RE-DERIVE, never to trust.  Prime's choices exposed:
;; how much reflection the language needs (the agent only needed quote
;; and match), whether equality of certificate steps is computational
;; (it was: match on rule instances), and which artifacts are checkable
;; independently of who produced them (all of them, here).
