; The sampler against the exact posterior on a corpus small enough to enumerate: three proofs, five
; nodes that may root fragments, 32 derivations, with d = 0.5 and theta = 1 held and the base learned
; from the tables.  A derivation's exact probability is that of its fragments in sequence with every
; seating summed out: each fragment joins a table of its dish, a table of size s weighing s - d, or
; opens one, weighing (theta + d T) P0, with P0 from the base that the tables before it built.  The
; sum runs over every seating by putting each fragment at each table size in turn and taking it away
; again.  Every move (single site, blocked, by type) is run alone and against this posterior.
(TransportProof toy1 (pcite f ((app a ()) (app b ()))))
(TransportProof toy2 (pcite f ((app a ()) (app c ()))))
(TransportProof toy3 (pcite g ((app a ()))))
!(tsg:load (toy1 toy2 toy3) 11)
!(tsg:set-flag hyper-frozen True)
(= (ctl:set-hyp $k $d $th)
   (let ($d0 $th0) (tsg:hyp $k) (let $r (remove-atom &self (TsgHyp $k $d0 $th0)) (add-atom &self (TsgHyp $k $d $th)))))
!(let* (($a (ctl:set-hyp proof 0.5 1.0)) ($b (ctl:set-hyp term 0.5 1.0))) (ctl:set-hyp level 0.5 1.0))
(CtlSeen none 0)

; the sites, and a derivation as a number: bit i set iff site i roots a fragment
(= (ctl:sites) (msort (collapse (match &self (TsgNode $i $k $c $r $rk $ks $b $m) (if (tsg:steppable? $i) $i (empty))))))
(= (ctl:code $cs $w) (if (== $cs ()) 0 (+ (if (tsg:bnd? (car-atom $cs)) $w 0) (ctl:code (cdr-atom $cs) (* 2 $w)))))
(= (ctl:set-code $cs $c)
   (if (== $cs ()) done
       (let* (($s (car-atom $cs)) ($x (tsg:set-root $s (== (% $c 2) 1))))
         (ctl:set-code (cdr-atom $cs) (floor-math (/ $c 2))))))
; the fragments of the derivation in place, tree by tree, each in pre-order
(= (ctl:trees) (msort (collapse (match &self (TsgRoot $u $c) $u))))
(= (ctl:frags-of $rs) (if (== $rs ()) () (term:concat (tsg:tree-frags (tsg:reverse (tsg:preorder (car-atom $rs) ()) ()) ()) (ctl:frags-of (cdr-atom $rs)))))
(= (ctl:frags) (ctl:frags-of (ctl:trees)))

; the exact log probability of fragments in sequence, every seating summed out: the I-th customer
; (rooted at the number I, below every node) opens a table or joins each of its dish's tables in turn
(= (ex:marg $frs $i)
   (if (== $frs ()) 0.0
       (let* (((fr $k $kd $d $t $s $r) (car-atom $frs))
              ($rest (cdr-atom $frs))
              (($N $T) (tsg:rest $kd)) (($dd $th) (tsg:hyp $kd))
              ($den (tsg:ln (+ $N $th)))
              ($tabs (collapse (match &self (TsgTable $tid $k $kd $sz) ($tid $sz))))
              ($wnew (- (+ (tsg:ln (+ $th (* $dd $T))) (tsg:logp0 $d ())) $den))
              ($vnew (let $x (tsg:sit $i $k $kd $d $t $s new) (let $v (ex:marg $rest (- $i 1)) (let $y (tsg:leave $i $k $kd $d) $v)))))
         (ex:joins $k $kd $d $t $s $tabs $dd $den $rest $i (+ $wnew $vnew)))))
(= (ex:joins $k $kd $d $t $s $tabs $dd $den $rest $i $acc)
   (if (== $tabs ()) $acc
       (let* ((($tid $sz) (car-atom $tabs))
              ($w (- (tsg:ln (- $sz $dd)) $den))
              ($v (let $x (tsg:sit $i $k $kd $d $t $s $tid) (let $v2 (ex:marg $rest (- $i 1)) (let $y (tsg:leave $i $k $kd $d) $v2)))))
         (ex:joins $k $kd $d $t $s (cdr-atom $tabs) $dd $den $rest $i (tsg:lse $acc (+ $w $v))))))
; with the restaurants empty: every derivation's exact log probability, ((CODE LOGP) ..)
(= (ctl:exact $cs $c $n $acc)
   (if (== $c $n) $acc
       (let* (($s (ctl:set-code $cs $c)) ($lp (ex:marg (ctl:frags) -1)))
         (ctl:exact $cs (+ $c 1) $n (cons-atom ($c $lp) $acc)))))
(= (ctl:lse-all $xs $acc) (if (== $xs ()) $acc (let ($c $lp) (car-atom $xs) (ctl:lse-all (cdr-atom $xs) (tsg:lse $acc $lp)))))

; empty the restaurants, enumerate, then seat the all-roots derivation again
!(let $fs (ctl:frags) (let $x (tsg:remove-frags (tsg:reverse $fs ()) 0.0 ()) (println! (restaurants emptied))))
!(let $cs (ctl:sites) (println! (sites $cs)))
; the sum is the same in another order (the model is exchangeable): the all-roots derivation forwards
; and backwards
!(let* (($cs (ctl:sites)) ($s (ctl:set-code $cs 31)) ($fs (ctl:frags)) ($a (ex:marg $fs -1)) ($b (ex:marg (tsg:reverse $fs ()) -1)))
   (println! (control exchangeable (if (< (abs-math (- $a $b)) 1.0e-9) ok (FAILED $a $b)))))
(= (ctl:exact-half $d)
   (let* (($a (ctl:set-hyp proof $d 1.0)) ($b (ctl:set-hyp term $d 1.0))
          ($xs (ctl:exact (ctl:sites) 0 32 ())))
     $xs))
!(let* (($xs0 (ctl:exact-half 0.0)) ($a (add-atom &self (CtlExact d0 $xs0)))
        ($xs (ctl:exact-half 0.5)) ($b (add-atom &self (CtlExact d05 $xs))))
   (println! (exact-done)))
!(let* (($cs (ctl:sites)) ($s (ctl:set-code $cs 31)) ($x (tsg:add-frags (ctl:frags) 0.0 ()))) (println! (seated all-roots)))
!(tsg:recount)

; a chain of one kind of move, counting the derivation after every fourth round
(= (ctl:round site) (tsg:sweep-nodes 0 (tsg:nodes)))
(= (ctl:round block) (tsg:block-each (ctl:trees) 0))
(= (ctl:round type) (ty:sweep-each 5 (tw 0 0 0)))
(= (ctl:round mixed) (let* (($a (tsg:sweep-nodes 0 (tsg:nodes))) ($b (tsg:block-each (ctl:trees) 0))) (ty:sweep-each 5 (tw 0 0 0))))
(= (ctl:rounds $m $k) (if (== $k 0) done (let $s (ctl:round $m) (ctl:rounds $m (- $k 1)))))
(= (ctl:count $m $c)
   (let* (($o (tsg:get1 (collapse (match &self (CtlSeen ($m $c) $n) $n)) 0))
          ($r (if (== $o 0) done (remove-atom &self (CtlSeen ($m $c) $o))))
          ($o1 (+ $o 1)))
     (add-atom &self (CtlSeen ($m $c) $o1))))
(= (ctl:run $m $cs $i $n)
   (if (== $i $n) done
       (let* (($s (ctl:rounds $m 4)) ($c (ctl:count $m (ctl:code $cs 1)))) (ctl:run $m $cs (+ $i 1) $n))))
; Pearson's statistic of the counts against an exact posterior
(= (ctl:pearson $m $xs $z $n $chi)
   (if (== $xs ()) $chi
       (let* ((($c $lp) (car-atom $xs)) ($e (* (exp (- $lp $z)) $n))
              ($o (tsg:get1 (collapse (match &self (CtlSeen ($m $c) $k) $k)) 0)))
         (ctl:pearson $m (cdr-atom $xs) $z $n (+ $chi (/ (* (- $o $e) (- $o $e)) $e))))))
; NAME ok when the counts fit the exact posterior (Pearson's statistic below 52.2, the 0.99 quantile
; on 31 degrees of freedom) and do not fit the posterior with d = 0
(= (ctl:test $m $name $n)
   (let* (($cs (ctl:sites)) ($r (ctl:run $m $cs 0 $n)) ($xs (car-atom (collapse (match &self (CtlExact d05 $x) $x))))
          ($x0 (car-atom (collapse (match &self (CtlExact d0 $y) $y))))
          ($chi (ctl:pearson $m $xs (ctl:lse-all $xs neg) $n 0.0))
          ($chi0 (ctl:pearson $m $x0 (ctl:lse-all $x0 neg) $n 0.0))
          ($p (println! (pearson $m (exact $chi) (with-d0 $chi0) (degrees-of-freedom 31)))))
     (println! (control $name (if (and (< $chi 52.2) (> $chi0 52.2)) ok FAILED)))))
!(ctl:test site posterior-single-site 4000)
!(ctl:test block posterior-blocked 4000)
!(ctl:test type posterior-type 4000)
!(ctl:test mixed posterior-all-moves 4000)
!(tsg:recount)

; a draw from options whose weights are far from 1 is the normalized one: two options of equal weight
; near e^-1000 (the scale of a large proof's inside) are each taken half the time
(= (ctl:pick-count $k $a)
   (if (== $k 0) $a
       (let (opt $w $h $i) (tsg:pick-opt ((opt -1000.0 first first) (opt -1000.0 second second)) (+ -1000.0 (tsg:ln 2.0)) (tsg:uniform))
         (ctl:pick-count (- $k 1) (if (== $h first) (+ $a 1) $a)))))
!(let $f (ctl:pick-count 2000 0) (println! (control pick-normalized (if (and (> $f 900) (< $f 1100)) ok (FAILED (first $f) (of 2000))))))
