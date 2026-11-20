; A typed constructor has typed fields.
;
; For a constructor C of a family F the document proves
;   C_typed    the fields typed  ->  C fields :e F
;   F_ind      induction over F, one case for each constructor
;   C_injK     C fields = C fields'  ->  the K-th are equal
;   F_noconf   two different constructors make different nodes
; From these the converse of C_typed follows, one theorem for each field:
;   C fields :e F  ->  field :e its type
; (inv:field E C K) proves it once in the theory, for the argument at
; position K of C (parameters counted), and answers its name, or None.
;
; With it a value's parts are typed from the value's own type; and a value
; has the type of the term it was computed from.  So a decision procedure
; that computes isTrue P 0 proves 0 :e P, the proposition it decided.

(= (inv:field $E $c $k)
   (let $kept (collapse (match &self (FieldInversion $c $k $name) $name))
     (if (== $kept ())
         (let $made (inv:make $E $c $k)
           (let $done (add-atom &self (FieldInversion $c $k $made)) $made))
         (car-atom $kept))))
(= (inv:make $E $c $k)
   (let $typed (collapse (match &self (CtorTyped $c $id) $id))
     (if (== $typed ()) None
         (let $claim (inv:claim (mg:proposition (mg:known (eq:theory $E) (car-atom $typed))) $k)
           (if (== $claim None) None
               (let* (($name (inv:name $c $k))
                      ($proved (mg:prove-by (eq:theory $E) $name $claim
                                 (Tac.intros (Tac.prove (eq:name $E) (Prover.field-inversion $k))))))
                 (case $proved
                   (((Error $call $why) None)
                    ($theorem $name)))))))))
(= (inv:name (Tm.named $id) $k) (format-args "{}_field_{}" ($id $k)))
; The claim, read off the typing lemma: all its quantifiers, its conclusion
; as the premise, and the premise it has for the variable at argument K.
(= (inv:claim $statement $k)
   (case (rule:conclusion $statement 0)
     (((Concludes $n $conclusion)
       (case (typ:parts $conclusion)
         (((Member $node $type)
           (case (mgt:nth (mgt:spine-args $node) $k)
             (((Tm.db $v)
               (if (inv:sets-only $statement)
                   (let $premise (inv:premise-of $statement 0 (- (- $n 1) $v) $n)
                     (if (== $premise None) None (inv:quantify $n (Tm.imp $conclusion $premise))))
                   None))
              ($other None))))
          ($other None))))
      ($other None))))
(= (inv:sets-only $p)
   (case $p
     (((Tm.all $A $body) (if (== $A (Tp.base 0)) (inv:sets-only $body) False))
      ((Tm.imp $q $rest) (inv:sets-only $rest))
      ($other True))))
; The premise #0 :e T met right after binder B (from outside, from 0),
; lifted to stand under all N binders.
(= (inv:premise-of $p $j $b $n)
   (case $p
     (((Tm.all $A $body) (inv:premise-of $body (+ $j 1) $b $n))
      ((Tm.imp $q $rest)
       (if (== (- $j 1) $b)
           (case (typ:parts $q)
             (((Member $s $T) (if (== $s (Tm.db 0)) (mgt:shift $q (- $n $j) 0) (inv:premise-of $rest $j $b $n)))
              ($other (inv:premise-of $rest $j $b $n))))
           (inv:premise-of $rest $j $b $n)))
      ($other None))))
(= (inv:quantify $n $p) (if (== $n 0) $p (inv:quantify (- $n 1) (Tm.all (Tp.base 0) $p))))

; The proof.  In hand: H, C fields :e F params.  Induction over F with the
; property "d = C fields -> goal" gives it for every d :e F, so for C fields
; itself.
(= (conv:witness-with (Prover.field-inversion $k) $E $ctx $body $q $binds) None)
(= (conv:witness-with (Prover.inversion-case $k) $E $ctx $body $q $binds) None)
(= (conv:prove-with (Prover.field-inversion $k) $E $ctx $goal)
   (let $found (inv:prove $E $ctx $k $goal) (if (== $found None) (empty) $found)))
(= (inv:prove $E $ctx $k $goal)
   (case (typ:parts (car-atom (mg:hypotheses $ctx)))
     (((Member $node $ftype)
       (let* (($F (mgt:head $ftype))
              ($inds (collapse (match &self (FamilyInd $F $id) $id))))
         (if (== $inds ()) None
             (let* (($ind (inv:apply-terms (mg:known-in (eq:theory $E) $ctx (car-atom $inds)) (mgt:spine-args $ftype)))
                    ($motive (Tm.lam (Tp.base 0)
                               (Tm.imp (eq:of $E (Tm.db 0) (mgt:shift $node 1 0)) (mgt:shift $goal 1 0)))))
               (case (mg:try-term-app $ind $motive)
                 (((Error $call $why) None)
                  ($thm (inv:finish $E $ctx $node (inv:cases $E $ctx $k $thm)))))))))
      ($other None))))
(= (inv:apply-terms $thm $terms)
   (if (== $terms ()) $thm (inv:apply-terms (mg:term-app $thm (car-atom $terms)) (cdr-atom $terms))))
; Each case of the induction proved and discharged.
(= (inv:cases $E $ctx $k $thm)
   (case (mg:proposition $thm)
     (((Tm.imp $case $rest)
       (let $proved (collapse (mg:run (Tac.intros (Tac.prove (eq:name $E) (Prover.inversion-case $k)))
                                      (eq:theory $E) $ctx (mgt:beta $case)))
         (if (== $proved ()) None
             (case (mg:try-proof-app $thm (car-atom $proved))
               (((Error $call $why) None)
                ($next (inv:cases $E $ctx $k $next)))))))
      ($other $thm))))
(= (inv:finish $E $ctx $node $thm)
   (if (== $thm None) None
       (case (mg:try-term-app $thm $node)
         (((Error $c1 $w1) None)
          ($at (case (mg:try-proof-app $at (mg:hyp (eq:theory $E) $ctx 0))
                 (((Error $c2 $w2) None)
                  ($implied (case (mg:try-proof-app $implied (eq:refl $E $ctx $node))
                              (((Error $c3 $w3) None)
                               ($done $done)))))))))))
; One case.  In hand, innermost: C' fields' = C fields.  Another constructor
; is absurd; the same one has equal fields, and the hypothesis that types the
; K-th field' is moved along those equations.
(= (conv:prove-with (Prover.inversion-case $k) $E $ctx $goal)
   (let $found (inv:case $E $ctx $k $goal) (if (== $found None) (empty) $found)))
(= (inv:case $E $ctx $k $goal)
   (case (eq:sides $E (car-atom (mg:hypotheses $ctx)))
     (((Sides $made $node)
       (let $heq (mg:hyp (eq:theory $E) $ctx 0)
         (if (== (mgt:head $made) (mgt:head $node))
             (inv:same $E $ctx $k $goal $heq $made $node)
             (inv:absurd $E $ctx $goal (inv:false-from $E $ctx $heq $made $node)))))
      ($other None))))
(= (inv:same $E $ctx $k $goal $heq $made $node)
   (let* (($margs (mgt:spine-args $made)) ($args (mgt:spine-args $node))
          ($z (mgt:nth $margs $k)))
     (case (typ:infer-variable $E $ctx $z (mg:hypotheses $ctx) 0)
       (((Typed $Tz $typed)
         (let $moved (inv:move $E $ctx $heq (mgt:head $made) $made $node $margs $args 0 $typed)
           (if (== $moved None) None
               (let $checked (collapse (mg:exact (eq:theory $E) $ctx $goal $moved))
                 (if (== $checked ()) None (car-atom $checked))))))
        ($other None)))))
; The theorem with each field' replaced by the field it equals.
(= (inv:move $E $ctx $heq $c $made $node $margs $args $m $current)
   (if (== $margs ()) $current
       (let* (($z (car-atom $margs)) ($y (car-atom $args))
              ($next (inv:move-one $E $ctx $heq $c $made $node $m $z $y $current)))
         (if (== $next None) None
             (inv:move $E $ctx $heq $c $made $node (cdr-atom $margs) (cdr-atom $args) (+ $m 1) $next)))))
(= (inv:move-one $E $ctx $heq $c $made $node $m $z $y $current)
   (if (== $z $y) $current
       (case $z
         (((Tm.db $i)
           (let $prop (mgt:beta (mg:proposition $current))
             (if (mgt:mentions $prop $i)
                 (let $equal (inv:fields-equal $E $ctx $heq $c $m $made $node)
                   (if (== $equal None) None
                       (eq:mp $E $ctx (inv:abstract $prop $i) $y $z (eq:sym $E $ctx $z $y $equal) $current)))
                 $current)))
          ($other $current)))))
; field' = field at argument M, by the injectivity theorem.
(= (inv:fields-equal $E $ctx $heq $c $m $made $node)
   (let $ids (collapse (match &self (CtorInj $c $m $id) $id))
     (if (== $ids ()) None
         (let* (($known (mg:known-in (eq:theory $E) $ctx (car-atom $ids)))
                ($statement (mg:proposition $known)))
           (case (rule:conclusion $statement 0)
             (((Concludes $n $conclusion)
               (case (eq:sides $E (rules:final-premise $statement None))
                 (((Sides $pa $pb)
                   (let $binds (mgt:match $pb $node $n 0 (mgt:match $pa $made $n 0 ()))
                     (if (== $binds fail) None
                         (case (rule:instantiate $E $ctx (Prover.tactic Tac.assumption) None $known $statement 0 $binds)
                           (((Instance $thm $stated) $thm)
                            ($other None))))))
                  ($other None))))
              ($other None)))))))
(= (inv:abstract $t $i) (Tm.lam (Tp.base 0) (inv:rebind (mgt:shift $t 1 0) (+ $i 1) 0)))
(= (inv:rebind $t $i $d)
   (case $t
     (((Tm.db $j) (if (== $j (+ $i $d)) (Tm.db $d) $t))
      ((Tm.app $f $x) (let $g (inv:rebind $f $i $d) (let $y (inv:rebind $x $i $d) (Tm.app $g $y))))
      ((Tm.lam $A $b) (let $c (inv:rebind $b $i (+ $d 1)) (Tm.lam $A $c)))
      ((Tm.all $A $b) (let $c (inv:rebind $b $i (+ $d 1)) (Tm.all $A $c)))
      ((Tm.imp $p $q) (let $a (inv:rebind $p $i $d) (let $c (inv:rebind $q $i $d) (Tm.imp $a $c))))
      ((Tm.typeApp $m $A) (let $n (inv:rebind $m $i $d) (Tm.typeApp $n $A)))
      ($other $t))))
; False, from an equation between nodes of two different constructors.
(= (inv:false-from $E $ctx $heq $a $b)
   (let* (($c1 (mgt:head $a)) ($c2 (mgt:head $b))
          ($direct (collapse (match &self (CtorDistinct $c1 $c2 $id) $id))))
     (if (== $direct ())
         (let $turned (collapse (match &self (CtorDistinct $c2 $c1 $id) $id))
           (if (== $turned ()) None
               (inv:refute $E $ctx (car-atom $turned) $b $a (eq:sym $E $ctx $a $b $heq))))
         (inv:refute $E $ctx (car-atom $direct) $a $b $heq))))
(= (inv:refute $E $ctx $id $a $b $equation)
   (let* (($known (mg:known-in (eq:theory $E) $ctx $id)) ($statement (mg:proposition $known)))
     (case (rule:conclusion $statement 0)
       (((Concludes $n (Tm.app (Tm.app $neq $pa) $pb))
         (let $binds (mgt:match $pb $b $n 0 (mgt:match $pa $a $n 0 ()))
           (if (== $binds fail) None
               (case (rule:instantiate $E $ctx Prover.none None $known $statement 0 $binds)
                 (((Instance $thm $stated)
                   (case (mg:try-proof-app $thm $equation)
                     (((Error $call $why) None) ($false $false))))
                  ($other None))))))
        ($other None)))))
(= (inv:absurd $E $ctx $goal $false)
   (if (== $false None) None
       (case (mg:try-proof-app (mg:known-in (eq:theory $E) $ctx (lean:id "FalseE")) $false)
         (((Error $c1 $w1) None)
          ($all (case (mg:try-term-app $all $goal) (((Error $c2 $w2) None) ($done $done))))))))
