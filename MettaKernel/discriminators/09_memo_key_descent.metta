;; ============================================================
;;  09 · THE CLERK'S LEDGER
;;  Discriminator: memoization is an observer; the key must descend
;; ============================================================
;;
;;  Question this instrument asks:
;;    A clerk memoizes "what did it cost to elaborate this term?",
;;    keyed by the term's printed shape.  Two elaborations share a
;;    shape but differ in colour (provenance), and colour changes
;;    cost.  The clerk answers the second request from the first
;;    entry.  A second clerk keys by (shape, colour).  A third clerk
;;    uses the second clerk's key but evicts the whole table every
;;    night.  A fourth clerk uses the FIRST key but serves a client
;;    who only asks for the shape.
;;
;;  What to look for: the wrong answer appears exactly where the
;;  client reads a coordinate the key erased.  Soundness belongs to
;;  the pair (key, client), not to the key.  Eviction changes only
;;  whether an answer came from the store; never the answer.
;; ============================================================

;; --- terms: (Term shape colour) ------------------------------------------
(= (cost (Term $s red))   7)
(= (cost (Term $s plain)) 1)
(= (shape (Term $s $c))   $s)

(= (t-red)   (Term 0 red))
(= (t-plain) (Term 0 plain))

;; --- two keys -------------------------------------------------------------
(= (syntax-key (Term $s $c)) $s)
(= (colour-key (Term $s $c)) ($s $c))

;; --- a memo table is a list of (Entry key value) ---------------------------
(= (lookup $k Nil) Miss)
(= (lookup $k (Cons (Entry $k2 $v) $rest))
   (if (== $k $k2) (Hit $v) (lookup $k $rest)))

(= (store $key $client $table $x)
   (Cons (Entry ($key $x) ($client $x)) $table))

(= (memo $key $client $table $x)
   (case (lookup ($key $x) $table)
     (((Hit $v) ($v from-store))
      (Miss     (($client $x) computed)))))

(= (value ($v $how)) $v)
(= (how   ($v $how)) $how)

;; --- the experiment: store the red term, then ask about the plain one -------
(= (run $key $client)
   (let $table (store $key $client Nil (t-red))
     (memo $key $client $table (t-plain))))

(= (judge $key $client)
   (if (== (value (run $key $client)) ($client (t-plain)))
       SOUND
       UNSOUND-KEY-FOR-THIS-CLIENT))

;; --- eviction: ask for the red term again, with and without the store ------
(= (repeat-with-store)
   (memo colour-key cost (store colour-key cost Nil (t-red)) (t-red)))
(= (repeat-evicted)
   (memo colour-key cost Nil (t-red)))

!(println! "--- ground truth for the plain term ---")
!(println! (cost-plain (cost (t-plain))))
!(println! (shape-plain (shape (t-plain))))

!(println! "--- clerk A: key = shape, client = cost ---")
!(println! (answer (run syntax-key cost)))
!(println! (result (judge syntax-key cost)))

!(println! "--- clerk B: key = (shape colour), client = cost ---")
!(println! (answer (run colour-key cost)))
!(println! (result (judge colour-key cost)))

!(println! "--- clerk C: clerk B's key, but the table is evicted every night ---")
!(println! (repeat-red-with-store (repeat-with-store)))
!(println! (repeat-red-evicted    (repeat-evicted)))
!(println! (same-value (== (value (repeat-with-store)) (value (repeat-evicted)))))
!(println! (same-reuse (== (how (repeat-with-store)) (how (repeat-evicted)))))

!(println! "--- clerk D: key = shape, client = shape ---")
!(println! (answer (run syntax-key shape)))
!(println! (result (judge syntax-key shape)))

!(println! "--- the two-by-two: soundness belongs to (key, client) ---")
!(println! (key-shape  client-cost  (judge syntax-key cost)))
!(println! (key-shape  client-shape (judge syntax-key shape)))
!(println! (key-colour client-cost  (judge colour-key cost)))
!(println! (key-colour client-shape (judge colour-key shape)))
