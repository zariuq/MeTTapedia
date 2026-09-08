;; ============================================================
;;  12 · TWO SPELLINGS, ONE PROCESS
;;  Discriminator: which observations are predicates on equation classes?
;; ============================================================
;;
;;  Question this instrument asks:
;;    A process can be written in several ways that the calculus
;;    equates: inside a singleton parallel wrapper, { *@0 } versus
;;    *@0; with its name spelled as the quote of a drop, *@(*@0)
;;    versus *@0; with the redex nested one bag deeper.  Three
;;    readers look at such a pair.  The RAW SPATIAL reader asks "is
;;    the outermost constructor a drop?" of the spelling it is given.
;;    The MODULO reader asks the same question of the canonical
;;    representative.  The BEHAVIOURAL reader asks "can it step?"
;;    over the equation-saturated step (step the canonical
;;    representative) and, for contrast, over the raw step.
;;
;;  What to look for: the raw spatial reader gives different answers
;;  to equal processes, so it is not a predicate on classes; the
;;  modulo reader and the saturated behavioural reader agree on every
;;  spelling.  The raw step misses the nested redex; the saturated
;;  step finds it.
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

;; --- the raw and modulo spatial readers -------------------------------------
;;  a spatial type: (Headed c args) with args a list of types; Top matches all
(= (headed-raw Top $p) True)
(= (headed-raw (Headed Drop (Cons $a Nil)) (Drop $n)) (headed-raw $a $n))
(= (headed-raw (Headed Drop (Cons $a Nil)) Zero) False)
(= (headed-raw (Headed Drop (Cons $a Nil)) (Out $n $p)) False)
(= (headed-raw (Headed Drop (Cons $a Nil)) (In $n $b)) False)
(= (headed-raw (Headed Drop (Cons $a Nil)) (Par $l)) False)
(= (headed-raw (Headed Quote (Cons $a Nil)) (Q $p)) (headed-raw $a $p))
(= (headed-raw (Headed Quote (Cons $a Nil)) (V $i)) False)

(= (headed-modulo $type $p) (headed-raw $type (canon $p)))

;; --- the raw and saturated behavioural readers ("can it step?") -------------
(= (same-channel $m $n) (== (canon-name $m) (canon-name $n)))
(= (has-input-for $n Nil) False)
(= (has-input-for $n (Cons (In $m $b) $rest)) (if (same-channel $n $m) True (has-input-for $n $rest)))
(= (has-input-for $n (Cons (Out $m $q) $rest)) (has-input-for $n $rest))
(= (has-input-for $n (Cons Zero $rest)) (has-input-for $n $rest))
(= (has-input-for $n (Cons (Drop $m) $rest)) (has-input-for $n $rest))
(= (has-input-for $n (Cons (Par $l) $rest)) (has-input-for $n $rest))

(= (has-redex Nil $all) False)
(= (has-redex (Cons (Out $n $q) $rest) $all) (if (has-input-for $n $all) True (has-redex $rest $all)))
(= (has-redex (Cons (In $n $b) $rest) $all) (has-redex $rest $all))
(= (has-redex (Cons Zero $rest) $all) (has-redex $rest $all))
(= (has-redex (Cons (Drop $n) $rest) $all) (has-redex $rest $all))
(= (has-redex (Cons (Par $l) $rest) $all) (has-redex $rest $all))

;; the raw step looks only at the top-level bag of the spelling it is given
(= (can-step-raw (Par $l)) (has-redex $l $l))
(= (can-step-raw Zero) False)
(= (can-step-raw (Drop $n)) False)
(= (can-step-raw (Out $n $p)) False)
(= (can-step-raw (In $n $b)) False)
;; the saturated step first moves to the canonical representative
(= (can-step-saturated $p) (can-step-raw (canon $p)))

;; --- the spellings ----------------------------------------------------------
(= (plain)     (Drop (Q Zero)))
(= (wrapped)   (Par (Cons (Drop (Q Zero)) Nil)))
(= (respelled) (Drop (Q (Drop (Q Zero)))))

(= (receiver) (In (Q Zero) (Drop (V 0))))
(= (sender)   (Out (Q Zero) Zero))
(= (letter)        (Par (Cons (receiver) (Cons (sender) Nil))))
(= (letter-nested) (Par (Cons (Par (Cons (receiver) (Cons (sender) Nil))) (Cons Zero Nil))))

(= (drop-shape)       (Headed Drop (Cons Top Nil)))
(= (quote-drop-shape) (Headed Drop (Cons (Headed Quote (Cons (Headed Drop (Cons Top Nil)) Nil)) Nil)))

!(println! "--- three spellings of one process, one key ---")
!(println! (spelling-plain (plain)))
!(println! (spelling-wrapped (wrapped)))
!(println! (spelling-respelled (respelled)))
!(println! (keys-agree (and (== (canon (plain)) (canon (wrapped))) (== (canon (plain)) (canon (respelled))))))

!(println! "--- the raw spatial reader, 'headed by a drop' ---")
!(println! (raw-plain (headed-raw (drop-shape) (plain))))
!(println! (raw-wrapped (headed-raw (drop-shape) (wrapped))))
!(println! (raw-disagrees-on-equal-processes (not (== (headed-raw (drop-shape) (plain)) (headed-raw (drop-shape) (wrapped))))))

!(println! "--- the raw spatial reader, 'drop of a quote of a drop' ---")
!(println! (raw-respelled (headed-raw (quote-drop-shape) (respelled))))
!(println! (raw-plain (headed-raw (quote-drop-shape) (plain))))
!(println! (raw-disagrees-on-equal-processes (not (== (headed-raw (quote-drop-shape) (respelled)) (headed-raw (quote-drop-shape) (plain))))))

!(println! "--- the modulo reader agrees on every spelling ---")
!(println! (modulo-drop (headed-modulo (drop-shape) (plain)) (headed-modulo (drop-shape) (wrapped)) (headed-modulo (drop-shape) (respelled))))
!(println! (modulo-quote-drop (headed-modulo (quote-drop-shape) (plain)) (headed-modulo (quote-drop-shape) (wrapped)) (headed-modulo (quote-drop-shape) (respelled))))

!(println! "--- the behavioural reader: the letter and its nested spelling ---")
!(println! (letter-keys-agree (== (canon (letter)) (canon (letter-nested)))))
!(println! (raw-step (can-step-raw (letter)) (can-step-raw (letter-nested))))
!(println! (saturated-step (can-step-saturated (letter)) (can-step-saturated (letter-nested))))

!(println! "--- verdict ---")
!(println! "raw spatial reading: not a predicate on classes (separates equal spellings)")
!(println! "modulo reading and saturated behavioural reading: predicates on classes")
