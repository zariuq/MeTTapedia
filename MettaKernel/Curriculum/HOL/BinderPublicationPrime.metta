; Run beside HOLLightBinderPublication.holr. The certificate is the HOL Light
; source proof. The requested sequent below is constructed independently.
!(import! &self holkernel)
!(import! &self tcalc)

(= (predicate-type $dom) (T "fun" $dom (T "bool")))
(= (predicate $dom) (c "cross_pred" (predicate-type $dom)))
(= (other-predicate $dom) (v "g" (predicate-type $dom)))
(= (function-equality $dom $l $r)
   (A (A (c "=" (T "fun" (predicate-type $dom) (T "fun" (predicate-type $dom) (T "bool")))) $l) $r))
(= (at-binder $f $name) (L (v $name (T "bool")) (A $f (v $name (T "bool")))))
(= (hypothesis $dom) (function-equality $dom (predicate $dom) (other-predicate $dom)))
(= (requested $name)
   (thm ((hypothesis (T "bool")))
        (function-equality (T "bool") (at-binder (predicate (T "bool")) $name)
                           (at-binder (other-predicate (T "bool")) $name))))

; Dense parent slots follow the order of the HOL Light export. The recipient
; can check this receipt without the source file or the issuing kernel.
(= (portable-proof)
   (proof (declare "cross_pred" (predicate-type (V "A")))
          ((HolNode 0 (REFL (v "x" (V "A"))) ())
           (HolNode 1 (ASSUME (hypothesis (V "A"))) ())
           (HolNode 2 (MK_COMB) (1 0))
           (HolNode 3 (ABS (v "x" (V "A"))) (2))
           (HolNode 4 (INST_TYPE (((T "bool") (V "A")))) (3)))
          4))

(= (recheck (proof (declare $name $type) $nodes $root) $sequent)
  (let* (($k (hol:kernel standard))
         (hol:ok (hol:new-constant $k $name $type)))
    (case (hol:check-dag $k $nodes $root)
      (((hol:refused $code $why) False)
       ((hol:error $code $why) False)
       ($t (if (hol:admits $k $t) (== (hol:sequent $t) $sequent) False))))))

; Compare the one hypothesis and the conclusion using HOL alpha-conversion.
; The transform consumes the request and publishes the kernel's representative.
(= (same-judgment $k (thm ($p) $q) (thm ($r) $s))
   (if (hol:aconv $k $p $r) (hol:aconv $k $q $s) False))
(= (same-judgment $k (thm () $q) $s) False)

(= (publication-step $state)
  (tcalc:step
    ((step one)
     (rule publish
       (take (request $target))
       (read (checked $target $sequent $receipt True True))
       (make (published $sequent $receipt))))
    "" $state))

(= (publish $k $wanted)
  (let* (($proof (hol:theorem $k "BINDER_PUBLICATION"))
         ($actual (hol:sequent $proof))
         ($event (hol:event $proof))
         ($live (hol:admits $k $proof))
         ($portable (portable-proof))
         ($equal (if $live (if (same-judgment $k $wanted $actual) (recheck $portable $actual) False) False)))
    (publication-step
      ((request $wanted)
       (checked $wanted $actual (receipt "BINDER_PUBLICATION" $event $portable)
                $live $equal)))))

; Inspect the committed state, including the actual sequent and the receipt.
(= (observe $k $h $q)
  (let* (($actual (hol:sequent $h)) ($event (hol:event $h)) ($out (publish $k $q)))
    (case $out
      ((($interpretation (successor $basis (published $s (receipt "BINDER_PUBLICATION" $i $graph)))
          (stepped (successors 1) (finished true)))
        (issued (== $s $actual) (== $i $event) (recheck $graph $s)))
       (($interpretation (stepped (successors 0) (finished true))) refused)
       ($unexpected (unexpected $unexpected))))))

!(bind! &k (hol:kernel standard))
!(bind! &base (hol:checkpoint &k))
!(hol:replay &k "HOLLightBinderPublication.holr")
!(bind! &h (hol:theorem &k "BINDER_PUBLICATION"))
!(bind! &round (publish &k (requested "x")))
!(let ($policy (successor $basis $publication) $stats) &round $publication)
!(let* ((($i (successor $basis $publication) $s) &round)
        (($j (stepped (successors $n) (finished true))) (publication-step ($basis $publication))))
   (second-firing-count $n))
!(let ($i (successor $basis (published $s (receipt $label $event (proof $decl $nodes $root)))) $stats) &round
   (wrong-receipt-root (recheck (proof $decl $nodes 0) $s)))
!(exact (observe &k &h (requested "x")))
!(alpha (observe &k &h (requested "y")))
!(let (thm ($p) $q) (requested "x") (erased (observe &k &h (thm () $q))))
!(let (thm ($p) $q) (requested "x") (forged (observe &k &h (thm ($p) $p))))
!(hol:new-constant &k "unrelated" (T "bool"))
!(extended (observe &k &h (requested "x")))
!(hol:restore &k &base)
!(hol:new-constant &k "cross_pred" (T "bool"))
!(incompatible (observe &k &h (requested "x")))
