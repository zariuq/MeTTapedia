;; ============================================================
;;  10 · THE RETRACTED SIGHTING
;;  Discriminator: what may "forgetting" do to a world model?
;; ============================================================
;;
;;  Question this instrument asks:
;;    A ledger holds bird sightings.  Conclusions carry (n+ n-)
;;    counts and the list of sightings that support them.  Sighting
;;    s4 (the crow) is retracted.  Three policies "forget" s4:
;;      RESET-TO-PRIOR  puts the prior (1 1) on every claim touching s4
;;      ZERO-IN-SCOPE   zeroes claims supported ONLY by s4, touches
;;                      nothing else
;;      CAUSAL-DELETE   removes s4 from every support and recounts
;;    Two laws are checked on each:
;;      L1  no manufactured evidence: every count is <= before
;;      L2  support-closed: every retained conclusion keeps a support
;;          that avoids the forgotten sighting
;;
;;  What to look for: the earlier interface (idempotent, untouched
;;  outside scope) admits all three.  L1 rejects RESET.  L2 rejects
;;  ZERO, because the aggregate claim keeps standing on the retracted
;;  sighting.  Only CAUSAL-DELETE passes both.
;; ============================================================

;; --- small list library (Cons/Nil; avoid Prolog-colliding names) ---------
(= (contains $x Nil) False)
(= (contains $x (Cons $h $t)) (if (== $x $h) True (contains $x $t)))
(= (all-scope $s Nil) True)
(= (all-scope $s (Cons $h $t)) (and (== $h $s) (all-scope $s $t)))
(= (remove $x Nil) Nil)
(= (remove $x (Cons $h $t)) (if (== $x $h) (remove $x $t) (Cons $h (remove $x $t))))
(= (len Nil) 0)
(= (len (Cons $h $t)) (+ 1 (len $t)))
(= (map-claims $f Nil) Nil)
(= (map-claims $f (Cons $c $r)) (Cons ($f $c) (map-claims $f $r)))

;; --- the world model before retraction ------------------------------------
;;  (Claim name (Ev n+ n-) support)
(= (before)
   (Cons (Claim raven-black (Ev 3 0) (Cons s1 (Cons s2 (Cons s3 Nil))))
   (Cons (Claim crow-black  (Ev 1 0) (Cons s4 Nil))
   (Cons (Claim birds-black (Ev 4 0) (Cons s1 (Cons s2 (Cons s3 (Cons s4 Nil)))))
   Nil))))

(= (scope) s4)

;; --- three forgetting policies, per claim -----------------------------------
(= (reset-claim (Claim $n (Ev $p $m) $sup))
   (if (contains (scope) $sup)
       (Claim $n (Ev 1 1) Nil)
       (Claim $n (Ev $p $m) $sup)))

(= (zero-claim (Claim $n (Ev $p $m) $sup))
   (if (all-scope (scope) $sup)
       (Claim $n (Ev 0 0) Nil)
       (Claim $n (Ev $p $m) $sup)))

(= (causal-claim (Claim $n (Ev $p $m) $sup))
   (let $rest (remove (scope) $sup)
     (Claim $n (Ev (len $rest) 0) $rest)))

;; --- the two laws ----------------------------------------------------------
(= (l1-claim (Claim $n (Ev $p $m) $s) (Claim $n2 (Ev $p2 $m2) $s2))
   (and (<= $p2 $p) (<= $m2 $m)))
(= (l1-all Nil Nil) True)
(= (l1-all (Cons $a $ar) (Cons $b $br)) (and (l1-claim $a $b) (l1-all $ar $br)))

(= (l2-claim (Claim $n (Ev $p $m) $s))
   (if (> (+ $p $m) 0) (not (contains (scope) $s)) True))
(= (l2-all Nil) True)
(= (l2-all (Cons $c $r)) (and (l2-claim $c) (l2-all $r)))

(= (show $policy)
   (let $after (map-claims $policy (before))
     (Report $policy
             (after $after)
             (L1-no-manufactured-evidence (if (l1-all (before) $after) HOLDS VIOLATED))
             (L2-support-closed           (if (l2-all $after) HOLDS VIOLATED)))))

!(println! "--- before retraction ---")
!(println! (before))
!(println! "--- policy RESET-TO-PRIOR ---")
!(println! (show reset-claim))
!(println! "--- policy ZERO-IN-SCOPE ---")
!(println! (show zero-claim))
!(println! "--- policy CAUSAL-DELETE ---")
!(println! (show causal-claim))
