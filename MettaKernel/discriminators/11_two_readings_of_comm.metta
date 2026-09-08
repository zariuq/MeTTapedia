;; ============================================================
;;  11 · THE RECEIVED LETTER
;;  Discriminator: the substitution interpretation is not an equation
;; ============================================================
;;
;;  Question this instrument asks:
;;    A receiver waits on a channel and, on delivery, DROPS the name
;;    it receives: for(y <- @0){ *y }.  A sender delivers the quoted
;;    nil: @0!(0).  Both readers of the authored COMM rule match the
;;    same redex with the same bindings.  The SYNTACTIC reader
;;    instantiates the substitution node structurally and is left with
;;    the drop of a quotation, *(@0).  The DECLARED reader (the
;;    reflective substitution of the calculus) exposes the payload, 0.
;;
;;  What to look for: the two contracta have different canonical
;;  keys, so no authored or presentation-derived equation identifies
;;  them; the gap is a rule interpretation, not a missing law.  By
;;  contrast the NAME-level quote/drop, @(*x) = x, is an equation:
;;  both spellings of the channel get the same key, and the redex is
;;  found either way.
;; ============================================================

;; --- terms ------------------------------------------------------------------
;;  processes:  Zero | (Drop n) | (Out n p) | (In n body) | (Par list)
;;  names:      (Q p) | (V i)          (V i: de Bruijn index of a bound name)
;;  lists:      Nil | (Cons x rest)

;; --- a total order on terms, for canonical sorting ---------------------------
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

;; --- the presentation-derived bag laws, as one canonical key ---------------
;;  flatten nested parallel, absorb the unit, sort; then collapse the
;;  empty and singleton wrappers.  Names normalise the quote of a drop.
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

;; --- the two readers of the COMM contractum p[@q / y] ------------------------
;;  Both take the body with the received name as (V depth).  The syntactic
;;  reader replaces the variable everywhere.  The declared reader does the
;;  same, except that a DROP of the substituted variable exposes the payload.
(= (subst-syn $d $q Zero) Zero)
(= (subst-syn $d $q (Drop $n)) (Drop (subst-name $d $q $n)))
(= (subst-syn $d $q (Out $n $p)) (Out (subst-name $d $q $n) (subst-syn $d $q $p)))
(= (subst-syn $d $q (In $n $b)) (In (subst-name $d $q $n) (subst-syn (+ $d 1) $q $b)))
(= (subst-syn $d $q (Par $l)) (Par (subst-syn-list $d $q $l)))
(= (subst-syn-list $d $q Nil) Nil)
(= (subst-syn-list $d $q (Cons $x $xs)) (Cons (subst-syn $d $q $x) (subst-syn-list $d $q $xs)))

(= (subst-name $d $q (V $i)) (if (== $i $d) (Q $q) (V $i)))
(= (subst-name $d $q (Q $p)) (Q (subst-syn $d $q $p)))

(= (subst-dec $d $q Zero) Zero)
(= (subst-dec $d $q (Drop $n)) (drop-after $d $q $n))
(= (subst-dec $d $q (Out $n $p)) (Out (subst-name-dec $d $q $n) (subst-dec $d $q $p)))
(= (subst-dec $d $q (In $n $b)) (In (subst-name-dec $d $q $n) (subst-dec (+ $d 1) $q $b)))
(= (subst-dec $d $q (Par $l)) (Par (subst-dec-list $d $q $l)))
(= (subst-dec-list $d $q Nil) Nil)
(= (subst-dec-list $d $q (Cons $x $xs)) (Cons (subst-dec $d $q $x) (subst-dec-list $d $q $xs)))

;; a matched drop exposes the payload; any other drop is structural
(= (drop-after $d $q (V $i)) (if (== $i $d) $q (Drop (V $i))))
(= (drop-after $d $q (Q $p)) (Drop (Q (subst-dec $d $q $p))))

(= (subst-name-dec $d $q (V $i)) (if (== $i $d) (Q $q) (V $i)))
(= (subst-name-dec $d $q (Q $p)) (Q (subst-dec $d $q $p)))

;; --- matching the authored COMM redex in a parallel bag ---------------------
;;  { n!(q) | for(<- n'){ body } | ...rest } with n and n' the same channel.
;;  The matcher compares channels by canonical key (the declared matcher);
;;  the raw matcher compares them syntactically.
(= (same-channel-raw $m $n) (== $m $n))
(= (same-channel-key $m $n) (== (canon-name $m) (canon-name $n)))

(= (remove-first $x Nil) Nil)
(= (remove-first $x (Cons $y $ys)) (if (== $x $y) $ys (Cons $y (remove-first $x $ys))))

;; find one (Out n q) and one (In n' body) whose channels agree under `same`
(= (find-redex $same Nil $all) NoRedex)
(= (find-redex $same (Cons (Out $n $q) $rest) $all)
   (case (find-input $same $n $all)
     (((In $m $body) (Redex $n $q $body (remove-first (In $m $body) (remove-first (Out $n $q) $all))))
      (NoInput (find-redex $same $rest $all)))))
(= (find-redex $same (Cons (In $n $b) $rest) $all) (find-redex $same $rest $all))
(= (find-redex $same (Cons Zero $rest) $all) (find-redex $same $rest $all))
(= (find-redex $same (Cons (Drop $n) $rest) $all) (find-redex $same $rest $all))
(= (find-redex $same (Cons (Par $l) $rest) $all) (find-redex $same $rest $all))

(= (find-input $same $n Nil) NoInput)
(= (find-input $same $n (Cons (In $m $body) $rest))
   (if ($same $n $m) (In $m $body) (find-input $same $n $rest)))
(= (find-input $same $n (Cons (Out $m $q) $rest)) (find-input $same $n $rest))
(= (find-input $same $n (Cons Zero $rest)) (find-input $same $n $rest))
(= (find-input $same $n (Cons (Drop $m) $rest)) (find-input $same $n $rest))
(= (find-input $same $n (Cons (Par $l) $rest)) (find-input $same $n $rest))

;; one COMM step under a reader of the contractum
(= (comm $same $reader (Par $l))
   (case (find-redex $same $l $l)
     (((Redex $n $q $body $rest) (Stepped (Par (Cons ($reader 0 $q $body) $rest))))
      (NoRedex Stuck))))
(= (comm $same $reader Zero) Stuck)
(= (comm $same $reader (Drop $n)) Stuck)
(= (comm $same $reader (Out $n $p)) Stuck)
(= (comm $same $reader (In $n $b)) Stuck)

(= (key-of (Stepped $p)) (Key (canon $p)))
(= (key-of Stuck) Stuck)

;; --- the scenario ---------------------------------------------------------
(= (nil-name) (Q Zero))
(= (receiver) (In (nil-name) (Drop (V 0))))
(= (sender)   (Out (nil-name) Zero))
(= (letter)   (Par (Cons (receiver) (Cons (sender) Nil))))

;; the same letter with its channel spelled as the quote of a drop: @(*@0)
(= (spelled-name) (Q (Drop (Q Zero))))
(= (letter-respelled) (Par (Cons (In (spelled-name) (Drop (V 0))) (Cons (sender) Nil))))

!(println! "--- the letter and its canonical key ---")
!(println! (the-letter (letter)))
!(println! (key (canon (letter))))

!(println! "--- one COMM step, two readers of the contractum ---")
!(println! (syntactic (comm same-channel-key subst-syn (letter))))
!(println! (declared  (comm same-channel-key subst-dec (letter))))

!(println! "--- canonical keys of the two contracta: no equation relates them ---")
!(println! (syntactic-key (key-of (comm same-channel-key subst-syn (letter)))))
!(println! (declared-key  (key-of (comm same-channel-key subst-dec (letter)))))
!(println! (same-key (== (key-of (comm same-channel-key subst-syn (letter)))
                         (key-of (comm same-channel-key subst-dec (letter))))))

!(println! "--- the syntactic contractum is inert: a free drop of a quote never fires ---")
!(println! (syntactic-then (case (comm same-channel-key subst-syn (letter))
                             (((Stepped $p) (comm same-channel-key subst-dec $p))))))

!(println! "--- by contrast, the NAME-level quote/drop is an equation ---")
!(println! (respelled-channel (spelled-name)))
!(println! (channel-keys-agree (== (canon-name (spelled-name)) (canon-name (nil-name)))))
!(println! (letter-keys-agree (== (canon (letter-respelled)) (canon (letter)))))
!(println! (raw-matcher-on-respelled (comm same-channel-raw subst-dec (letter-respelled))))
!(println! (key-matcher-on-respelled (comm same-channel-key subst-dec (letter-respelled))))

!(println! "--- verdict ---")
!(println! "name-level quote/drop: an equation (same key, redex found after normalising the channel)")
!(println! "process-level drop-of-quote: NOT an equation (different keys); it is the substitution reading")
