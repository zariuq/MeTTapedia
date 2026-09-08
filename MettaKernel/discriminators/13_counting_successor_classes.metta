;; ============================================================
;;  13 · THE COUNTING CLERK
;;  Discriminator: finitely many successor classes, and who is watching
;; ============================================================
;;
;;  Question this instrument asks:
;;    Over the equation-saturated step a process reaches every
;;    spelling of each successor, so it has unboundedly many successor
;;    TERMS; yet it has finitely many successor CLASSES.  A clerk who
;;    counts terms never finishes; a clerk who counts canonical keys
;;    does.  With the count finite, a logical equivalence can be turned
;;    into a bisimulation by a finite conjunction of separating
;;    formulas.  But separating what from what depends on the
;;    observation set: with no observations two processes whose
;;    successors are both stuck are bisimilar; with the observation
;;    "has a waiting input" they are not, and one diamond formula
;;    tells them apart.
;;
;;  What to look for: the same successor class is reached under many
;;  spellings (one key); the class count is small; the bounded
;;  bisimulation check flips with the observation set; the separating
;;  formula gives the same verdict on every spelling.
;; ============================================================

;; --- terms, order, canonical key (as in instrument 11) ----------------------
(= (rank Zero)        0)
(= (rank (Drop $n))   1)
(= (rank (Out $n $p)) 2)
(= (rank (In $n $b))  3)
(= (rank (Par $l))    4)
(= (rank (Q $p))      5)
(= (rank (V $i))      6)

(= (lt-list Nil Nil) False)
(= (lt-list Nil (Cons $y $ys)) True)
(= (lt-list (Cons $x $xs) Nil) False)
(= (lt-list (Cons $x $xs) (Cons $y $ys))
   (if (lt $x $y) True (if (lt $y $x) False (lt-list $xs $ys))))
(= (lt $a $b)
   (if (< (rank $a) (rank $b)) True
       (if (< (rank $b) (rank $a)) False (lt-same $a $b))))
(= (lt-same Zero Zero) False)
(= (lt-same (Drop $m) (Drop $n)) (lt $m $n))
(= (lt-same (Out $m $p) (Out $n $q))
   (if (lt $m $n) True (if (lt $n $m) False (lt $p $q))))
(= (lt-same (In $m $a) (In $n $b))
   (if (lt $m $n) True (if (lt $n $m) False (lt $a $b))))
(= (lt-same (Par $l) (Par $k)) (lt-list $l $k))
(= (lt-same (Q $p) (Q $q)) (lt $p $q))
(= (lt-same (V $i) (V $j)) (< $i $j))
(= (place $x Nil) (Cons $x Nil))
(= (place $x (Cons $y $ys))
   (if (lt $x $y) (Cons $x (Cons $y $ys)) (Cons $y (place $x $ys))))
(= (order-terms Nil) Nil)
(= (order-terms (Cons $x $xs)) (place $x (order-terms $xs)))
(= (join-lists Nil $ys) $ys)
(= (join-lists (Cons $x $xs) $ys) (Cons $x (join-lists $xs $ys)))
(= (splice Nil) Nil)
(= (splice (Cons (Par $inner) $rest)) (join-lists $inner (splice $rest)))
(= (splice (Cons Zero $rest)) (splice $rest))
(= (splice (Cons (Drop $n) $rest)) (Cons (Drop $n) (splice $rest)))
(= (splice (Cons (Out $n $p) $rest)) (Cons (Out $n $p) (splice $rest)))
(= (splice (Cons (In $n $b) $rest)) (Cons (In $n $b) (splice $rest)))
(= (unwrap-bag Nil) Zero)
(= (unwrap-bag (Cons $x Nil)) $x)
(= (unwrap-bag (Cons $x (Cons $y $rest))) (Par (Cons $x (Cons $y $rest))))
(= (canon-list Nil) Nil)
(= (canon-list (Cons $x $xs)) (Cons (canon $x) (canon-list $xs)))
(= (canon Zero) Zero)
(= (canon (Drop $n)) (Drop (canon-name $n)))
(= (canon (Out $n $p)) (Out (canon-name $n) (canon $p)))
(= (canon (In $n $b)) (In (canon-name $n) (canon $b)))
(= (canon (Par $l)) (unwrap-bag (order-terms (splice (canon-list $l)))))
(= (canon-name (V $i)) (V $i))
(= (canon-name (Q $p)) (quote-of (canon $p)))
(= (quote-of (Drop $n)) $n)
(= (quote-of Zero) (Q Zero))
(= (quote-of (Out $n $p)) (Q (Out $n $p)))
(= (quote-of (In $n $b)) (Q (In $n $b)))
(= (quote-of (Par $l)) (Q (Par $l)))

;; --- the declared substitution (as in instrument 11) -------------------------
(= (subst-dec $d $q Zero) Zero)
(= (subst-dec $d $q (Drop $n)) (drop-after $d $q $n))
(= (subst-dec $d $q (Out $n $p)) (Out (subst-name-dec $d $q $n) (subst-dec $d $q $p)))
(= (subst-dec $d $q (In $n $b)) (In (subst-name-dec $d $q $n) (subst-dec (+ $d 1) $q $b)))
(= (subst-dec $d $q (Par $l)) (Par (subst-dec-list $d $q $l)))
(= (subst-dec-list $d $q Nil) Nil)
(= (subst-dec-list $d $q (Cons $x $xs)) (Cons (subst-dec $d $q $x) (subst-dec-list $d $q $xs)))
(= (drop-after $d $q (V $i)) (if (== $i $d) $q (Drop (V $i))))
(= (drop-after $d $q (Q $p)) (Drop (Q (subst-dec $d $q $p))))
(= (subst-name-dec $d $q (V $i)) (if (== $i $d) (Q $q) (V $i)))
(= (subst-name-dec $d $q (Q $p)) (Q (subst-dec $d $q $p)))

;; --- every COMM redex of a canonical bag, and the successor classes --------
(= (same-channel $m $n) (== (canon-name $m) (canon-name $n)))
(= (remove-first $x Nil) Nil)
(= (remove-first $x (Cons $y $ys)) (if (== $x $y) $ys (Cons $y (remove-first $x $ys))))

;; contracta of one output against every matching input in the bag
(= (fire-against $n $q $all Nil) Nil)
(= (fire-against $n $q $all (Cons (In $m $body) $rest))
   (if (same-channel $n $m)
       (Cons (canon (Par (Cons (subst-dec 0 $q $body)
                               (remove-first (In $m $body) (remove-first (Out $n $q) $all)))))
             (fire-against $n $q $all $rest))
       (fire-against $n $q $all $rest)))
(= (fire-against $n $q $all (Cons (Out $m $p) $rest)) (fire-against $n $q $all $rest))
(= (fire-against $n $q $all (Cons Zero $rest)) (fire-against $n $q $all $rest))
(= (fire-against $n $q $all (Cons (Drop $m) $rest)) (fire-against $n $q $all $rest))
(= (fire-against $n $q $all (Cons (Par $l) $rest)) (fire-against $n $q $all $rest))

(= (contracta Nil $all) Nil)
(= (contracta (Cons (Out $n $q) $rest) $all) (join-lists (fire-against $n $q $all $all) (contracta $rest $all)))
(= (contracta (Cons (In $n $b) $rest) $all) (contracta $rest $all))
(= (contracta (Cons Zero $rest) $all) (contracta $rest $all))
(= (contracta (Cons (Drop $n) $rest) $all) (contracta $rest $all))
(= (contracta (Cons (Par $l) $rest) $all) (contracta $rest $all))

(= (in-list $x Nil) False)
(= (in-list $x (Cons $y $ys)) (if (== $x $y) True (in-list $x $ys)))
(= (dedup Nil) Nil)
(= (dedup (Cons $x $xs)) (if (in-list $x $xs) (dedup $xs) (Cons $x (dedup $xs))))

;; successor classes of a process: canonical contracta of its canonical form
(= (successor-classes $p) (successor-classes-of (canon $p)))
(= (successor-classes-of (Par $l)) (dedup (contracta $l $l)))
(= (successor-classes-of Zero) Nil)
(= (successor-classes-of (Drop $n)) Nil)
(= (successor-classes-of (Out $n $p)) Nil)
(= (successor-classes-of (In $n $b)) Nil)

(= (how-many Nil) 0)
(= (how-many (Cons $x $xs)) (+ 1 (how-many $xs)))

;; --- observation sets ---------------------------------------------------------
;;  an observation set is a list of atom names; each atom is read on the
;;  canonical representative, so it is a predicate on classes by construction
(= (observe has-input $p) (has-input-canon (canon $p)))
(= (has-input-canon (In $n $b)) True)
(= (has-input-canon (Par $l)) (any-input $l))
(= (has-input-canon Zero) False)
(= (has-input-canon (Drop $n)) False)
(= (has-input-canon (Out $n $p)) False)
(= (any-input Nil) False)
(= (any-input (Cons (In $n $b) $rest)) True)
(= (any-input (Cons (Out $n $p) $rest)) (any-input $rest))
(= (any-input (Cons Zero $rest)) (any-input $rest))
(= (any-input (Cons (Drop $n) $rest)) (any-input $rest))
(= (any-input (Cons (Par $l) $rest)) (any-input $rest))

(= (atoms-agree Nil $p $q) True)
(= (atoms-agree (Cons $a $rest) $p $q)
   (if (== (observe $a $p) (observe $a $q)) (atoms-agree $rest $p $q) False))

;; --- bounded bisimulation over successor classes ------------------------------
(= (all-matched $obs $n Nil $qs) True)
(= (all-matched $obs $n (Cons $p $ps) $qs)
   (if (some-match $obs $n $p $qs) (all-matched $obs $n $ps $qs) False))
(= (some-match $obs $n $p Nil) False)
(= (some-match $obs $n $p (Cons $q $qs))
   (if (bisim-upto $obs $n $p $q) True (some-match $obs $n $p $qs)))

(= (bisim-upto $obs $n $p $q)
   (if (== $n 0) True
       (if (atoms-agree $obs $p $q)
           (and (all-matched $obs (- $n 1) (successor-classes $p) (successor-classes $q))
                (all-matched $obs (- $n 1) (successor-classes $q) (successor-classes $p)))
           False)))

;; --- Hennessy–Milner formulas: Top, (Atom a), (And f g), (Not f), (Dia f) -------
(= (sat Top $p) True)
(= (sat (Atom $a) $p) (observe $a $p))
(= (sat (And $f $g) $p) (and (sat $f $p) (sat $g $p)))
(= (sat (Not $f) $p) (not (sat $f $p)))
(= (sat (Dia $f) $p) (some-sat $f (successor-classes $p)))
(= (some-sat $f Nil) False)
(= (some-sat $f (Cons $c $cs)) (if (sat $f $c) True (some-sat $f $cs)))

;; --- the scenario ---------------------------------------------------------------
(= (nil-name) (Q Zero))
(= (one-name) (Q (Drop (Q Zero))))     ; a second name, @(*@0): equal to @0 by quote/drop
(= (other-name) (Q (Out (Q Zero) Zero))) ; a genuinely different name, @(@0!(0))
(= (sender)   (Out (nil-name) Zero))
(= (letter)   (Par (Cons (In (nil-name) (Drop (V 0))) (Cons (sender) Nil))))
;; the receiver keeps a second, waiting input after delivery
(= (waiting-letter)
   (Par (Cons (In (nil-name) (Par (Cons (Drop (V 0)) (Cons (In (other-name) Zero) Nil))))
              (Cons (sender) Nil))))
;; spellings of the letter's successor: many terms, one key
(= (spelling-1) (Par (Cons Zero Nil)))
(= (spelling-2) (Par Nil))
(= (spelling-3) (Par (Cons Zero (Cons (Par (Cons Zero Nil)) Nil))))
;; respellings of the two processes
(= (letter-respelled) (Par (Cons (sender) (Cons (In (one-name) (Drop (V 0))) Nil))))
(= (waiting-respelled)
   (Par (Cons (Par (Cons (sender) Nil))
              (Cons (In (one-name) (Par (Cons (In (other-name) Zero) (Cons (Drop (V 0)) Nil)))) Nil))))

!(println! "--- many successor terms, one successor class ---")
!(println! (successor-spellings (spelling-1) (spelling-2) (spelling-3)))
!(println! (their-keys (canon (spelling-1)) (canon (spelling-2)) (canon (spelling-3))))
!(println! (successor-classes-of-the-letter (successor-classes (letter))))
!(println! (class-count (how-many (successor-classes (letter)))))

!(println! "--- the waiting letter: also one successor class, a different one ---")
!(println! (successor-classes-of-the-waiting-letter (successor-classes (waiting-letter))))
!(println! (class-count (how-many (successor-classes (waiting-letter)))))

!(println! "--- bounded bisimulation, depth 3, under two observation sets ---")
!(println! (no-observations (bisim-upto Nil 3 (letter) (waiting-letter))))
!(println! (observing-has-input (bisim-upto (Cons has-input Nil) 3 (letter) (waiting-letter))))

!(println! "--- one separating formula: <>(has-input) ---")
!(println! (letter-satisfies (sat (Dia (Atom has-input)) (letter))))
!(println! (waiting-letter-satisfies (sat (Dia (Atom has-input)) (waiting-letter))))

!(println! "--- the verdicts survive respelling ---")
!(println! (keys-agree (== (canon (letter)) (canon (letter-respelled))) (== (canon (waiting-letter)) (canon (waiting-respelled)))))
!(println! (respelled-letter-satisfies (sat (Dia (Atom has-input)) (letter-respelled))))
!(println! (respelled-waiting-satisfies (sat (Dia (Atom has-input)) (waiting-respelled))))
!(println! (respelled-bisim-no-observations (bisim-upto Nil 3 (letter-respelled) (waiting-respelled))))
!(println! (respelled-bisim-has-input (bisim-upto (Cons has-input Nil) 3 (letter-respelled) (waiting-respelled))))

!(println! "--- verdict ---")
!(println! "count classes, not terms; the separating conjunction is finite because the class count is")
!(println! "bisimilarity is relative to the observation set; the formula reads classes, so respelling changes nothing")
