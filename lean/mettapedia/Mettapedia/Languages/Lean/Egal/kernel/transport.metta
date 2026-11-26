; Lean's proofs carried into the kernel.
;
; (TransportTheorem C (binder ..) P) and (TransportProof C PROOF) come from
; the transport export (artifacts/lean-declarations/transport/proofs.metta).
; A transported theorem states what the reading's cited lemma states: a type
; is any set, a term lies in its type, a hypothesis is the proof value of its
; proposition, and then 0 :e P.  Its proof is Lean's term, followed: an
; abstraction is a binder of the context, and the kernel's prover makes only
; the side conditions the term leaves to definition.  A theorem whose
; statement or proof applies a quotient primitive at a level this reading does
; not interpret (TransportOutsideProfile C PART WHY) is not followed; where a
; library theorem states the same, it is cited instead (TrFoundation).
;
;   (tr:claim C)      the kernel proposition C states, or None
;   (tr:prove E C)    the kernel theorem of (tr:claim C), or (Unfollowed C WHY)
;   (tr:prove-with E C PROOF)
;                     the same, following PROOF in place of Lean's (a control: a
;                     proof of another statement must not follow)

; The export keeps the proofs inside terms, (by p), for the way back to Lean.  This reading
; is of sets, where a proof is 0 whatever its term: each is read as (proof).
(= (tr:erase-proofs $ep_t)
   (if (== (get-metatype $ep_t) Expression)
       (if (== $ep_t ()) ()
           (if (== (car-atom $ep_t) by) (proof) (tr:erase-proofs-list $ep_t)))
       $ep_t))
(= (tr:erase-proofs-list $el_xs)
   (if (== $el_xs ()) () (cons-atom (tr:erase-proofs (car-atom $el_xs)) (tr:erase-proofs-list (cdr-atom $el_xs)))))
(= (tr:stated $c)
   (let $found (collapse (match &self (TransportTheorem $c $bs $P) (Stated $bs $P)))
     (if (== $found ()) None
         (case (car-atom $found)
           (((Stated $bs0 $P0)
             (let* (($bs1 (tr:erase-proofs $bs0)) ($P1 (tr:erase-proofs $P0))
                    ($bs2 (tr:read-binders $bs1)) ($P2 (norm-term $P1)))
               (Stated $bs2 $P2))))))))
; A statement is read as a value is (tr:value): matchers at their bodies.
(= (tr:read-binders $rb_bs)
   (if (== $rb_bs ()) ()
       (let* (($rb_b (tr:read-binder (car-atom $rb_bs))) ($rb_rest (tr:read-binders (cdr-atom $rb_bs))))
         (cons-atom $rb_b $rb_rest))))
(= (tr:read-binder $rd_b)
   (case $rd_b
     (((hyp $rd_h $rd_Q) (let $rd_Q1 (norm-term $rd_Q) (hyp $rd_h $rd_Q1)))
      ((term $rd_v $rd_T) (let $rd_T1 (norm-term $rd_T) (term $rd_v $rd_T1)))
      ($rd_other $rd_other))))
(= (tr:proof-of $c)
   (let $found (collapse (match &self (TransportProof $c $p) $p))
     (if (== $found ()) None (tr:erase-proofs (car-atom $found)))))
(= (tr:zero) (Tm.named (egal:id "Empty")))

; The claim: binders outermost first; ENV the term variables, innermost first.
(= (tr:claim $c)
   (case (tr:stated $c)
     (((Stated $bs $P) (tr:claim-levels (tr:levels-of $c) $bs $P ()))
      ($other None))))
; The faithful reading: each level parameter of the theorem, in Lean's order, is a
; natural number; then the binders.
(= (tr:levels-of $c)
   (let $found (collapse (match &self (TransportLevels $c $ls) $ls))
     (if (== $found ()) () (car-atom $found))))
(= (tr:nat-p $t) (Tm.app (Tm.named (egal:id "nat_p")) $t))
(= (tr:claim-levels $ls $bs $P $env)
   (if (== $ls ()) (tr:claim-over $bs $P $env)
       (Tm.all (Tp.base 0)
         (Tm.imp (tr:nat-p (Tm.db 0))
                 (tr:claim-levels (cdr-atom $ls) $bs $P (cons-atom (car-atom $ls) $env))))))
; A binder's type: a type of Type l is a member of Sort (l + 1), of Sort l a member of
; Sort l; a term lies in its type.
(= (tr:binder-type $b)
   (case $b
     (((type $v $l) (univ-of $l))
      ((sort $v $l) (sort-of $l))
      ((term $v $T) $T))))
; A binder's type in the kernel: Type l is LeanUniv l, Sort l is LeanSort l.
(= (tr:wire-type $D $env)
   (case $D
     (((univ-of $l) (Tm.app (wire:named "LeanUniv") (wire:level (lvl $l) $env)))
      ((sort-of $l) (Tm.app (wire:named "LeanSort") (wire:level (lvl $l) $env)))
      ($_ (tr:wire $D $env)))))
(= (tr:claim-over $bs $P $env)
   (if (== $bs ()) (typ:member (tr:zero) (tr:wire $P $env))
       (let $rest (cdr-atom $bs)
         (case (car-atom $bs)
           (((hyp $h $Q)
             (Tm.imp (typ:member (tr:zero) (tr:wire $Q $env))
                     (tr:claim-over (tr:proof-for-all $rest $h) (csubst $P (($h (proof)))) $env)))
            ($b
             (let $v (car-atom (cdr-atom $b))
               (Tm.all (Tp.base 0)
                 (Tm.imp (typ:member (Tm.db 0) (mgt:shift (tr:wire-type (tr:binder-type $b) $env) 1 0))
                         (tr:claim-over $rest $P (cons-atom $v $env)))))))))))
; A hypothesis's value is 0: the binders after it see (proof) for it.
(= (tr:proof-for-all $bs $h)
   (if (== $bs ()) ()
       (let $rest (tr:proof-for-all (cdr-atom $bs) $h)
         (case (car-atom $bs)
           (((term $v $T) (cons-atom (term $v (csubst $T (($h (proof))))) $rest))
            ((hyp $g $Q) (cons-atom (hyp $g (csubst $Q (($h (proof))))) $rest))
            ($b (cons-atom $b $rest)))))))

; The proof followed.  Each binder of the statement takes one abstraction of
; the proof; SENV names the statement's variables and PENV the proof's (the
; two may name one variable differently).  Then the body is proved, and the
; theorem is closed over the context.
(= (tr:prove $E $c) (tr:prove-with $E $c (tr:proof-of $c)))
(= (tr:prove-with $E $c $proof)
   (let $outside (collapse (match &self (TransportOutsideProfile $c $part $why) ($part $why)))
     (if (not (== $outside ())) (Unfollowed $c (outside-profile (car-atom $outside)))
         (case (tr:stated $c)
           (((Stated $bs $P)
             (if (== $proof None) (Unfollowed $c no-proof)
                 (tr:follow-levels $E (mg:empty-context) (tr:levels-of $c) $bs $P $proof () () ())))
            ($other (Unfollowed $c no-statement)))))))
; Each level parameter: a variable of the logic and the hypothesis that it is a natural
; number; Lean's proof has no abstraction for it.
(= (tr:follow-levels $E $ctx $ls $bs $P $proof $senv $penv $kinds)
   (if (== $ls ()) (tr:follow-binders $E $ctx $bs $P $proof $senv $penv $kinds)
       (case (mg:try-term-binder (eq:theory $E) $ctx (Tp.base 0))
         (((Error $c $w) (Unfollowed level-binder $w))
          ($c1 (case (mg:try-proof-binder (eq:theory $E) $c1 (tr:nat-p (Tm.db 0)))
                 (((Error $c2 $w2) (Unfollowed level-binder $w2))
                  ($c2 (tr:follow-levels $E $c2 (cdr-atom $ls) $bs $P $proof
                         (cons-atom (car-atom $ls) $senv) (cons-atom (car-atom $ls) $penv) (cons-atom V $kinds))))))))))
(= (tr:follow-binders $E $ctx $bs $P $proof $senv $penv $kinds)
   (if (== $bs ()) (tr:closed $E $kinds (tr:follow $E $ctx $penv (tr:hyps-of $ctx) (tr:renamed $P $senv $penv) $proof))
       (case $proof
         (((plam $x $T $body)
           (let $rest (cdr-atom $bs)
             (case (car-atom $bs)
               (((type $v $l) (tr:bind-term $E $ctx (tr:renamed (tr:binder-type (car-atom $bs)) $senv $penv) $rest $P $body (cons-atom $v $senv) (cons-atom $x $penv) $kinds))
                ((sort $v $l) (tr:bind-term $E $ctx (tr:renamed (tr:binder-type (car-atom $bs)) $senv $penv) $rest $P $body (cons-atom $v $senv) (cons-atom $x $penv) $kinds))
                ((term $v $D) (tr:bind-term $E $ctx (tr:renamed $D $senv $penv) $rest $P $body (cons-atom $v $senv) (cons-atom $x $penv) $kinds))
                ((hyp $h $Q)
                 (case (mg:try-proof-binder (eq:theory $E) $ctx (typ:member (tr:zero) (tr:wire (tr:renamed $Q $senv $penv) $penv)))
                   (((Error $call $why) (Unfollowed binder $why))
                    ($c1 (let $kept (tr:note-hyp $c1 $x)
                           (tr:follow-binders $E $c1 (tr:proof-for-all $rest $h) (csubst $P (($h (proof)))) $body $senv $penv (cons-atom H $kinds)))))))))))
          ($other
           (case (tr:eta $proof (car-atom $bs))
             (((Eta $x $applied) (tr:follow-binders $E $ctx $bs $P (plam $x none $applied) $senv $penv $kinds))
              ($none (Unfollowed binders $other)))))))))
; A proof shorter than its statement (Lean's term eta-reduced): the binder is
; taken, and the proof is applied to it, a variable as a term, a hypothesis as
; a proof.
(= (tr:eta $proof $b)
   (let $arg (case $b (((hyp $h $Q) (Arg $h (phyp $h ())))
                       ((type $v $l) (Arg $v (var $v)))
                       ((sort $v $l) (Arg $v (var $v)))
                       ((term $v $D) (Arg $v (var $v)))))
     (case ($arg $proof)
       ((((Arg $x $a) (pcite $c $args)) (Eta $x (pcite $c (tr:snoc $args $a))))
        (((Arg $x $a) (pctor $c $args)) (Eta $x (pctor $c (tr:snoc $args $a))))
        (((Arg $x $a) (prec $c $args)) (Eta $x (prec $c (tr:snoc $args $a))))
        (((Arg $x $a) (pquot $c $args)) (Eta $x (pquot $c (tr:snoc $args $a))))
        (((Arg $x $a) (phyp $h $args)) (Eta $x (phyp $h (tr:snoc $args $a))))
        (((Arg $x $a) (pproj $S $i $of $args)) (Eta $x (pproj $S $i $of (tr:snoc $args $a))))
        ($o None)))))
(= (tr:snoc $xs $a) (if (== $xs ()) (cons-atom $a ()) (cons-atom (car-atom $xs) (tr:snoc (cdr-atom $xs) $a))))
; A term variable: a binder of the logic, and (where D is not None) the
; hypothesis that it lies in D.  D is in the proof's names.
(= (tr:bind-term $E $ctx $D $rest $P $body $senv $penv $kinds)
   (case (mg:try-term-binder (eq:theory $E) $ctx (Tp.base 0))
     (((Error $call $why) (Unfollowed binder $why))
      ($c1 (if (== $D None) (tr:follow-binders $E $c1 $rest $P $body $senv $penv (cons-atom T $kinds))
               (case (mg:try-proof-binder (eq:theory $E) $c1 (typ:member (Tm.db 0) (mgt:shift (tr:wire-type $D (cdr-atom $penv)) 1 0)))
                 (((Error $call2 $why2) (Unfollowed binder $why2))
                  ($c2 (tr:follow-binders $E $c2 $rest $P $body $senv $penv (cons-atom V $kinds))))))))))
; The statement's variables under the proof's names.
(= (tr:renamed $P $senv $penv)
   (if (== $senv ()) $P
       (let $s (car-atom $senv)
         (let $p (car-atom $penv)
           (tr:renamed (if (== $s $p) $P (csubst $P (($s (var $p))))) (cdr-atom $senv) (cdr-atom $penv))))))
; Which hypotheses of a context are Lean's (a proof variable of the
; statement): (TrHyp CTX NAME) rows; the kernel numbers hypotheses from the
; innermost, so a name's number is its place in the context's list.
(= (tr:note-hyp $ctx $x) (add-atom &self (TrHyp $ctx $x)))
(= (tr:hyps-of $ctx) ())
; The theorem closed over the context in the order of the statement's
; binders, innermost first: a hypothesis is discharged; a term variable has
; its membership discharged and is generalized; a type is generalized.  So it
; states what the claim states.
(= (tr:closed $E $kinds $theorem)
   (case $theorem
     (((Unfollowed $a $b) (Unfollowed $a $b))
      ($thm (tr:close-kinds $thm $kinds)))))
(= (tr:close-kinds $thm $kinds)
   (if (== $kinds ()) $thm
       (let $next (case (car-atom $kinds)
                    ((H (mg:try-proof-lam $thm))
                     (T (mg:try-term-lam $thm))
                     (V (case (mg:try-proof-lam $thm)
                          (((Error $c $w) (Error $c $w))
                           ($t1 (mg:try-term-lam $t1)))))))
         (case $next
           (((Error $c $w) (Unfollowed closing $w))
            ($t (tr:close-kinds $t (cdr-atom $kinds))))))))
; The body.  A goal is a kernel proposition 0 :e T in CTX; the proof's terms
; are in ENV's names.  A proof goal is followed by Lean's term, node by node:
; the kernel's prover makes only the side conditions the term leaves to
; definition (that a term lies in its type, a constructor's premises, a
; canonical form), never a proof goal by itself, so that a theorem followed is
; Lean's proof followed.  Every result is restated as its goal.
(= (tr:follow $E $ctx $env $hyps $P $proof)
   (tr:follow-goal $E $ctx $env (typ:member (tr:zero) (tr:wire $P $env)) $proof))
(= (tr:follow-goal $E $ctx $env $goal $proof)
   (tr:follow-by-term $E $ctx $env $goal $proof))
(= (tr:follow-by-term $E $ctx $env $goal $proof)
   (case $proof
     (((plam $x $T $body) (tr:follow-lam $E $ctx $env $goal $x $body))
      ((phave $fact $by $body) (tr:follow-have $E $ctx $env $goal $fact $by $body))
      ((phyp $h $args) (tr:follow-hyp $E $ctx $env $goal $h $args))
      ((pcite propext $args) (tr:follow-propext $E $ctx $env $goal $args))
      ((pcite $c $args) (tr:follow-cite $E $ctx $env $goal $c $args))
      ((pctor $c $args) (tr:follow-proof-ok $E $ctx $env $goal $c $args))
      ((prec Eq.rec $args) (tr:follow-eq-rec $E $ctx $env $goal $args))
      ((prec $r $args) (tr:follow-proof-ok $E $ctx $env $goal $r $args))
      ((pproj $S $i $x $args) (tr:follow-proj $E $ctx $env $goal $S $i $x $args))
      ($other (Unfollowed (tr:head-of $proof) $goal)))))
; The projection of a structure's proof field (LeanProofProjection F S ctor i
; np): the reader's theorem for Lean's projection F (proved from S's
; elimination and the field's guard), at S's parameters, read from the
; value's type, and at the value; further arguments apply it as a hypothesis
; is applied.
(= (tr:follow-proj $E $ctx $env $goal $S $i $x $args)
   (let $found (collapse (match &self (LeanProofProjection $f $S $c $i $np) (Proj $f $np)))
     (if (== $found ()) (tr:follow-data-proj $E $ctx $env $goal $S $i $x $args)
         (case (car-atom $found)
           (((Proj $f $np)
             (case (mg:try-known-in (eq:theory $E) $ctx (egal:id (format-args "{}_proof" ((egal $f)))))
               (((Error $c1 $w1) (Unfollowed (no-proof-projection $f) $w1))
                ($thm
                  (let $v (tr:wire (tr:value $x) $env)
                    (case (typ:infer $E $ctx () $v)
                      ((None (Unfollowed (untyped-value $S) $goal))
                       ((Typed $T $typed)
                        (case (tr:apply-steps $thm (tr:param-steps $E $ctx (tr:last-n (tr:type-args $T ()) $np)))
                          (((Error $c2 $w2) (Unfollowed proj-params $w2))
                           ($t1 (case (tr:apply-steps $t1 ((T $v) (P $typed)))
                                  (((Error $c3 $w3) (Unfollowed proj-value $w3))
                                   ($t2 (case (tr:hyp-apply $E $ctx $env $t2 $args)
                                          (((Unfollowed $a $b) (Unfollowed $a $b))
                                           ($t3 (tr:as-goal $E $ctx $t3 $goal)))))))))))))))))))))))
; The arguments of a type that is a family applied to them, in order.
(= (tr:type-args $T $acc)
   (case $T (((Tm.app $F $a) (tr:type-args $F (cons-atom $a $acc))) ($other $acc))))
(= (tr:last-n $xs $n)
   (if (== $n 0) () (if (== (length-of $xs) $n) $xs (tr:last-n (cdr-atom $xs) $n))))
(= (tr:term-steps $xs) (if (== $xs ()) () (cons-atom (T (car-atom $xs)) (tr:term-steps (cdr-atom $xs)))))
(= (tr:head-of $p) (case $p ((($h $c $args) ($h $c)) ($other $other))))
; The value of an argument: a proof is 0, a term is itself.
(= (tr:is-proof $a)
   (case $a ((($h $x $y) (if (== $h phyp) True (if (== $h pcite) True (if (== $h pctor) True (if (== $h prec) True (== $h pquot))))))
             (($h $x $y $z) (if (== $h plam) True (if (== $h phave) True (== $h pproj))))
             (($h $x $y $z $w) (== $h pproj))
             ($other False))))
; A term is read as the reader reads it: a matcher's application is its case analysis.
(= (tr:value $a) (if (tr:is-proof $a) (proof) (norm-term $a)))
(= (tr:values $args) (if (== $args ()) () (cons-atom (tr:value (car-atom $args)) (tr:values (cdr-atom $args)))))
(= (tr:goal-type $goal) (case (typ:parts $goal) (((Member $z $T) $T) ($other None))))

; An abstraction against a product Pi A F: x is a variable lying in A; the
; body is followed against F's body; the theorem is discharged and
; generalized, and Pi_0_In gives 0 :e Pi A F.
(= (tr:pi-parts $T)
   (case $T
     (((Tm.app (Tm.app (Tm.named $pi) $A) (Tm.lam $ty $B))
       (if (== $pi (egal:id "Pi")) (Parts $A (Tm.lam $ty $B) $B) None))
      ($other None))))
(= (tr:follow-lam $E $ctx $env $goal $x $body)
   (case (tr:pi-parts (mgt:beta (tr:goal-type $goal)))
     (((Parts $A $F $B)
       (case (mg:try-term-binder (eq:theory $E) $ctx (Tp.base 0))
         (((Error $c $w) (Unfollowed lam-binder $w))
          ($c1 (case (mg:try-proof-binder (eq:theory $E) $c1 (typ:member (Tm.db 0) (mgt:shift $A 1 0)))
                 (((Error $c $w) (Unfollowed lam-hyp $w))
                  ($c2 (let $inner (tr:follow-under $E $c2 (cons-atom $x $env) (mgt:shift $A 1 0) (typ:member (tr:zero) $B) $body)
                         (case $inner
                           (((Unfollowed $a $b) (Unfollowed $a $b))
                            ($thm (tr:pi-intro $E $ctx $A $F $thm $goal))))))))))))
      ($other (tr:follow-lam-opened $E $ctx $env $goal $x $body)))))
(= (tr:pi-intro $E $ctx $A $F $thm $goal)
   (case (mg:try-proof-lam $thm)
     (((Error $c $w) (Unfollowed discharge $w))
      ($t1 (case (mg:try-term-lam $t1)
             (((Error $c $w) (Unfollowed generalize $w))
              ($t2 (let $pi (mg:known-in (eq:theory $E) $ctx (egal:id "Pi_0_In"))
                     (case (tr:apply-steps $pi ((T $A) (T $F) (P $t2)))
                       (((Error $c $w) (Unfollowed pi-0-in $w))
                        ($p3 (tr:as-goal $E $ctx $p3 $goal))))))))))))
; A theorem restated as the goal, where the kernel finds them convertible, or,
; for two memberships of one element, where the two types have one value under
; the rules of the reading (beta of a set function among them): the equation
; of each type with that value is the kernel's, and the theorem is carried
; along it (typ:retype-inside).
(= (tr:as-goal $E $ctx $thm $goal)
   (let $restated (collapse (mg:exact (eq:theory $E) $ctx $goal $thm))
     (if (== $restated ()) (tr:as-goal-by-value $E $ctx $thm $goal) (car-atom $restated))))
(= (tr:as-goal-by-value $E $ctx $thm $goal)
   (case ((typ:parts (mgt:beta (mg:proposition $thm))) (typ:parts (mgt:beta $goal)))
     ((((Member $z1 $T1) (Member $z $T))
       (if (== $z1 $z)
           (let $r (typ:retype-inside $E $ctx $z $T1 $T $thm)
             (if (== $r None) (Unfollowed restate $goal) $r))
           (Unfollowed restate $goal)))
      ($other (Unfollowed restate $goal)))))
(= (tr:follow-hyp $E $ctx $env $goal $h $args)
   (let* (($t (tr:wire (apv (var $h) (tr:values $args)) $env)) ($T (tr:goal-type $goal))
          ($typed (typ:prove $E $ctx () (typ:member $t $T))))
     (if (== $typed None)
         (tr:follow-proof-hyp $E $ctx $env $goal $args 0 (length-of (mg:hypotheses $ctx)) ())
         (tr:zero-in $E $ctx $t $T $typed $goal))))
; A hypothesis that is a proof (its value 0) of a product of propositions,
; applied to arguments: each argument instantiates it by Pi_0_ap, a term typed
; by the prover, a proof followed as its goal.  Which hypothesis of the context
; Lean's name is need not be tracked: each is tried, and the kernel accepts
; only one whose instance is the goal (any one is as good, every proof is 0).
(= (tr:follow-proof-hyp $E $ctx $env $goal $args $i $n $tried)
   (if (>= $i $n) (Unfollowed hypothesis (Refused (Goal (egal:text $goal)) (Arguments $args) (Tried $tried)))
       (case (tr:hyp-apply $E $ctx $env (mg:hyp (eq:theory $E) $ctx $i) $args)
         (((Unfollowed $a $b)
           (tr:follow-proof-hyp $E $ctx $env $goal $args (+ $i 1) $n (cons-atom (At $i $a $b) $tried)))
          ($done (case (tr:as-goal-opened $E $ctx $done $goal)
                   (((Unfollowed $a $b)
                     (tr:follow-proof-hyp $E $ctx $env $goal $args (+ $i 1) $n
                       (cons-atom (At $i applied (egal:text (mgt:beta (mg:proposition $done)))) $tried)))
                    ($ok $ok))))))))
(= (tr:hyp-apply $E $ctx $env $thm $args)
   (if (== $args ()) $thm
       (case (tr:pi-parts (mgt:beta (tr:goal-type (mgt:beta (mg:proposition $thm)))))
         (((Parts $A $F $B)
           (let* (($a (car-atom $args))
                  ($v (tr:wire (tr:value $a) $env))
                  ($in (typ:member $v $A))
                  ($by (if (tr:is-proof $a) (tr:follow-goal $E $ctx $env $in $a) (typ:prove $E $ctx () $in))))
             (case $by
               (((Unfollowed $x $y) (Unfollowed $x $y))
                (None (Unfollowed hypothesis-argument $in))
                ($hv (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id "Pi_0_ap")) ((T $A) (T $F) (P $thm) (T $v) (P $hv)))
                       (((Error $c $w) (Unfollowed pi-0-ap $w))
                        ($next (tr:hyp-apply $E $ctx $env $next (cdr-atom $args))))))))))
          ($other (tr:hyp-apply-opened $E $ctx $env $thm $args))))))
(= (tr:zero-in $E $ctx $t $T $typed $goal)
   (let $prop (tr:prop-of $E $ctx $T)
     (if (== $prop None) (Unfollowed not-a-proposition $goal)
         (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id "Lean_prop_0_of")) ((T $T) (P $prop) (T $t) (P $typed)))
           (((Error $c $w) (Unfollowed prop-0-of $w))
            ($a4 (tr:as-goal $E $ctx $a4 $goal)))))))

; A theorem applied to arguments: its transported theorem, kept once.
(= (tr:follow-cite $E $ctx $env $goal $c $args)
   (case (tr:theorem-name $E $c)
     (((Unfollowed $a $b) (Unfollowed (cites $c) $a))
      ($name (tr:known-at $E $ctx $env $goal (mg:known-in (eq:theory $E) $ctx $name) $args)))))
; A constructor or a recursor of a proposition, read as Lean states its type:
; the family's lemma that 0 lies there (Lean_F_C_proof_ok, Lean_F_rec_proof_ok),
; instantiated at the arguments in Lean's order.
(= (tr:follow-proof-ok $E $ctx $env $goal $c $args)
   (case (mg:try-known-in (eq:theory $E) $ctx (egal:id (format-args "{}_proof_ok" ((egal $c)))))
     (((Error $x $w) (Unfollowed (no-proof-ok $c) $goal))
      ($thm (tr:known-at $E $ctx $env $goal $thm $args)))))
; A known instantiated at the arguments, then restated as the goal.
(= (tr:known-at $E $ctx $env $goal $thm $args)
   (case (tr:instantiate $E $ctx $env $thm $args)
     (((Unfollowed $a $b) (Unfollowed $a $b))
      ($done (tr:as-goal $E $ctx $done $goal)))))
; Each argument fills the next quantifier: its value is the term (a proof's
; is 0).  A premise that types the value just given (a membership of it) is
; proved by following the argument when it is a proof, by the prover when it
; is a term; any other premise is filled by the next argument.
(= (tr:instantiate $E $ctx $env $thm $args)
   (if (== $args ()) $thm
       (let* (($a (car-atom $args)) ($rest (cdr-atom $args)) ($p (mgt:beta (mg:proposition $thm))))
         (case $p
           (((Tm.all $T $body)
             (let $v (tr:value-at $T $a $env)
               (case $v
                 (((Unfollowed $u $w) $v)
                  ($val (case (mg:try-term-app $thm $val)
                          (((Error $c $w) (Unfollowed instantiate (Refused (With (egal:text $val)) (At (egal:text $p)) (Why $w))))
                           ($t1 (tr:premise-of $E $ctx $env $t1 $a $val $rest)))))))))
            ((Tm.imp $premise $more) (tr:premise-by $E $ctx $env $thm $premise $a $rest))
            ; more arguments than quantifiers: the conclusion is a product (a motive that is a
            ; function of a proof), applied to the rest
            ($other (tr:hyp-apply $E $ctx $env $thm $args)))))))
; The value given to a quantifier: the argument's value, or, for a quantifier
; over functions of sets, Lean's abstraction read as one function of sets per
; binder (a statement over every function need not state their domains).
(= (tr:value-at $T $a $env)
   (case $a
     (((level $L) (wire:level $L $env))
      ($_ (tr:value-at-term $T $a $env)))))
(= (tr:value-at-term $T $a $env)
   (case $T
     (((Tp.arr $A $B)
       (case $a
         (((lam $x $Tx $body)
           (let $inner (tr:value-at $B $body (cons-atom $x $env))
             (case $inner (((Unfollowed $u $w) $inner) ($b (Tm.lam (Tp.base 0) $b))))))
          ($other (Unfollowed function-argument $a)))))
      ($other (tr:wire (tr:value $a) $env)))))
(= (tr:premise-of $E $ctx $env $thm $a $val $rest)
   (case (mgt:beta (mg:proposition $thm))
     (((Tm.imp $premise $more)
       (if (tr:types-value $premise $val)
           (tr:premise-by $E $ctx $env $thm $premise $a $rest)
           (if (== $premise (tr:nat-p $val))
               (case (tr:prove-nat $E $ctx $val)
                 ((None (Unfollowed level-premise (egal:text $premise)))
                  ($pn (case (mg:try-proof-app $thm $pn)
                         (((Error $c $w) (Unfollowed level-premise $w))
                          ($t1 (tr:instantiate $E $ctx $env $t1 $rest)))))))
               (tr:instantiate $E $ctx $env $thm $rest))))
      ($other (tr:instantiate $E $ctx $env $thm $rest)))))
(= (tr:types-value $premise $v)
   (case (typ:parts $premise) (((Member $z $T) (== $z $v)) ($other False))))
(= (tr:premise-by $E $ctx $env $thm $premise $a $rest)
   (let $pf (if (tr:is-proof $a) (tr:follow-goal $E $ctx $env (tr:as-membership-of-zero $premise) $a)
                (let $by (typ:prove $E $ctx () $premise) (if (== $by None) (tr:prove-canonical $E $ctx $premise) $by)))
     (case $pf
       (((Unfollowed $x $y) (Unfollowed $x $y))
        ($q (case (mg:try-proof-app $thm (tr:as-premise $E $ctx $q $premise))
              (((Error $c $w) (Unfollowed premise $w))
               ($t1 (tr:instantiate $E $ctx $env $t1 $rest)))))))))
; A proof's premise reads x :e T with x its value 0.
(= (tr:as-membership-of-zero $premise) $premise)
(= (tr:as-premise $E $ctx $q $premise)
   (case (tr:as-goal $E $ctx $q $premise) (((Unfollowed $a $b) $q) ($r $r))))

; Eq.rec: from m in motive a (refl) and h in a = b, motive b h.  The equation
; of h is the kernel's equality (LeanEq_sound); the motive is carried along it.
(= (tr:follow-eq-rec $E $ctx $env $goal $args)
   (if (< (length-of $args) 6) (Unfollowed eq-rec-arguments $goal)
       (if (> (length-of $args) 6) (tr:follow-eq-rec-further $E $ctx $env $goal $args)
           (let* (($A (mgt:nth $args 0)) ($a (mgt:nth $args 1)) ($motive (mgt:nth $args 2))
                  ($m (mgt:nth $args 3)) ($b (mgt:nth $args 4)) ($h (mgt:nth $args 5)))
             (case $motive
               (((lam $x $T1 (lam $hx $T2 $body))
                 (case (tr:follow $E $ctx $env () (app Eq ($A $a $b)) $h)
                   (((Unfollowed $u $v) (Unfollowed $u $v))
                    ($thm-h
                      (let* (($Mz (csubst $body (($hx (proof)))))
                             ($thm-m (tr:follow $E $ctx $env () (csubst $Mz (($x $a))) $m)))
                        (case $thm-m
                          (((Unfollowed $u $v) (Unfollowed $u $v))
                           ($tm (tr:eq-transport $E $ctx $env $goal $A $a $b $x $Mz $thm-h $tm)))))))))
                ($other (Unfollowed eq-rec-motive $goal))))))))
(= (tr:eq-transport $E $ctx $env $goal $A $a $b $x $Mz $thm-h $thm-m)
   (let* (($A1 (tr:wire $A $env)) ($a1 (tr:wire $a $env)) ($b1 (tr:wire $b $env)) ($z (tr:zero))
          ($sound (mg:known-in (eq:theory $E) $ctx (egal:id "LeanEq_sound"))))
     (case (tr:apply-steps $sound ((T $A1) (T $a1) (T $b1) (T $z) (P $thm-h)))
       (((Error $c $w) (Unfollowed eq-sound $w))
        ($ab (let $motive (Tm.lam (Tp.base 0) (typ:member (tr:zero) (tr:wire $Mz (cons-atom $x $env))))
               (case (mg:try-convertible (eq:theory $E) $ctx (mg:proposition $thm-m) (mgt:beta (Tm.app $motive $a1)))
                 ((True (tr:as-goal $E $ctx (eq:mp $E $ctx $motive $b1 $a1 (eq:sym $E $ctx $a1 $b1 $ab) $thm-m) $goal))
                  ($other (Unfollowed eq-rec-minor-form $goal))))))))))

; propext a b h: equivalent propositions are equal (Lean_propext_value), and
; then 0 :e Eq Prop a b (Lean_Eq_proof_of).
(= (tr:follow-propext $E $ctx $env $goal $args)
   (if (== (length-of $args) 3)
       (let* (($a (mgt:nth $args 0)) ($b (mgt:nth $args 1)) ($h (mgt:nth $args 2))
              ($iff (tr:follow $E $ctx $env () (app Iff ($a $b)) $h)))
         (case $iff
           (((Unfollowed $u $v) (Unfollowed $u $v))
            ($thm-iff
              (let* (($a1 (tr:wire $a $env)) ($b1 (tr:wire $b $env)) ($prop (Tm.named (egal:id "LeanProp")))
                     ($ta (typ:prove $E $ctx () (typ:member $a1 $prop)))
                     ($tb (typ:prove $E $ctx () (typ:member $b1 $prop))))
                (if (or (== $ta None) (== $tb None)) (Unfollowed propext-not-propositions $goal)
                    (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id "Lean_propext_value"))
                                          ((T $a1) (P $ta) (T $b1) (P $tb) (P $thm-iff)))
                      (((Error $c $w) (Unfollowed propext $w))
                       ($eq (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id "Lean_Eq_proof_of")) ((T $prop) (T $a1) (T $b1) (P $eq)))
                              (((Error $c $w) (Unfollowed propext-eq $w))
                               ($done (tr:as-goal $E $ctx $done $goal)))))))))))))
       (Unfollowed propext-arguments $goal)))
; A known applied to terms (T t) and proofs (P p) in order.
(= (tr:apply-steps $thm $steps)
   (if (== $steps ()) $thm
       (let $next (case (car-atom $steps)
                    (((T $t) (mg:try-term-app $thm $t))
                     ((P $p) (mg:try-proof-app $thm $p))))
         (case $next
           (((Error $c $w) (Error $c $w))
            ($t1 (tr:apply-steps $t1 (cdr-atom $steps))))))))

; The transported theorem of C: followed once, kept in the theory under a
; name of its own; the name is what a citation reads.
; A foundation (TrFoundation C LIB): Lean proves C from what the reading does
; not interpret at C's levels (its quotient axiom); the library's theorem LIB
; is cited instead, and only where it states exactly what C's claim states.
(TrFoundation funext Lean_funext)
(= (tr:theorem-name $E $c)
   (let $found (collapse (match &self (TrFoundation $c $lib) $lib))
     (if (== $found ()) (tr:theorem-name-transported $E $c) (tr:foundation $E $c (car-atom $found)))))
(= (tr:foundation $E $c $lib)
   (case (mg:try-known-in (eq:theory $E) (mg:empty-context) (egal:id $lib))
     (((Error $x $w) (Unfollowed (no-foundation $c) $w))
      ($thm (if (== (mg:try-convertible (eq:theory $E) (mg:empty-context) (mg:proposition $thm) (tr:claim $c)) True)
                (egal:id $lib)
                (Unfollowed (foundation-differs $c $lib) $lib))))))
(= (tr:theorem-name-transported $E $c)
   (let $kept (collapse (match &self (TrTheorem $c $name) $name))
     (if (== $kept ())
         (let $thm (tr:prove $E $c)
           (case $thm
             (((Unfollowed $a $b) (Unfollowed $a $b))
              ($t (let* (($name (format-args "Lean_{}_transported" ((egal $c)))))
                    (case (mg:try-publish (eq:theory $E) $t $name)
                      (((Error $x $w) (Unfollowed publish $w))
                       ($published (let $done (add-atom &self (TrTheorem $c $name)) $name)))))))))
         (car-atom $kept))))

; Transport mode: the document's hand proofs of Lean's lemmas (LemmaProof),
; and the lemmas for the proofs inside definitions, which cite them (the
; rules' companions), are set aside, so that a transported theorem rests on
; Lean's proof alone.
(= (tr:enter)
   (let* (($hands (tr:hand-ids (collapse (match &self (LemmaProof $x) $x))))
          ($companions (collapse (match &self (ConvCompanion $n $c) (Companion $n $c))))
          ($names (append-lists $hands (tr:companion-names $companions)))
          ($a (tr:mark-all $names))
          ($rows (collapse (match &self (TypRules $key $declared) (Rules $key $declared))))
          ($b (tr:without-marked $rows))
          ($c (tr:drop-companions $companions)))
     (TrMode (hands (length-of $hands)) (companions (length-of $companions)))))
(= (tr:hand-ids $xs)
   (if (== $xs ()) ()
       (let* (($id (egal:id (format-args "{}_proof" ((car-atom $xs))))) ($rest (tr:hand-ids (cdr-atom $xs))))
         ; only the hand proofs this document holds: a name it lacks is not a mark
         (case $id (((Error $at $why) $rest) ($present (cons-atom $present $rest)))))))
(= (tr:companion-names $rows)
   (if (== $rows ()) ()
       (case (car-atom $rows) (((Companion $n $c) (cons-atom $c (tr:companion-names (cdr-atom $rows))))))))
(= (tr:mark-all $ids)
   (if (== $ids ()) done
       (let* (($id (car-atom $ids)) ($kept (add-atom &self (TrSetAside $id)))) (tr:mark-all (cdr-atom $ids)))))
(= (tr:marked $name) (not (== (collapse (match &self (TrSetAside $name) yes)) ())))
; Every declared list of lemmas, without the lemmas set aside.
(= (tr:without-marked $rows)
   (if (== $rows ()) done
       (case (car-atom $rows)
         (((Rules $key $declared)
           (let $kept (tr:unmarked $declared)
             (let $next (if (== $kept $declared) done
                            (let $gone (remove-atom &self (TypRules $key $declared)) (add-atom &self (TypRules $key $kept))))
               (tr:without-marked (cdr-atom $rows)))))))))
(= (tr:unmarked $names)
   (if (== $names ()) ()
       (let $rest (tr:unmarked (cdr-atom $names))
         (if (tr:marked (car-atom $names)) $rest (cons-atom (car-atom $names) $rest)))))
(= (tr:drop-companions $rows)
   (if (== $rows ()) done
       (case (car-atom $rows)
         (((Companion $n $c)
           (let $gone (remove-atom &self (ConvCompanion $n $c)) (tr:drop-companions (cdr-atom $rows))))))))



; A level is a natural number: 0, a successor, or a level variable whose hypothesis is in
; the context.
(= (tr:prove-nat $E $ctx $t)
   (case $t
     (((Tm.app (Tm.app (Tm.named $op) $A) $B)
       (if (== $op (egal:id "LeanLevelMax")) (tr:prove-nat-two $E $ctx "LeanLevelMax_nat" $A $B)
       (if (== $op (egal:id "LeanLevelIMax")) (tr:prove-nat-two $E $ctx "LeanLevelIMax_nat" $A $B)
           None)))
      ((Tm.app (Tm.named $s) $X)
       (if (== $s (egal:id "ordsucc"))
           (let $px (tr:prove-nat $E $ctx $X)
             (if (== $px None) None
                 (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id "nat_ordsucc")) ((T $X) (P $px)))
                   (((Error $c $w) None) ($ok $ok)))))
           None))
      ((Tm.named $s)
       (if (== $s (egal:id "Empty")) (mg:known-in (eq:theory $E) $ctx (egal:id "nat_0")) None))
      ($other (tr:hyp-stating $E $ctx (tr:nat-p $t) 0 (length-of (mg:hypotheses $ctx)))))))
(= (tr:hyp-stating $E $ctx $P $i $n)
   (if (>= $i $n) None
       (let $h (mg:hyp (eq:theory $E) $ctx $i)
         (if (== (mgt:beta (mg:proposition $h)) $P) $h (tr:hyp-stating $E $ctx $P (+ $i 1) $n)))))

; A typing premise whose sort is written at a successor level (LeanSort (ordsucc l), from a
; theorem's Sort l binder at a successor level): proved in the canonical form the typing
; lemmas state (LeanUniv l; LeanProp at 0), then restated as written.
(= (tr:prove-canonical $E $ctx $premise)
   (let $canon (tr:canon-sorts $premise)
     (if (== $canon $premise) (Unfollowed argument-type $premise)
         (let $by (typ:prove $E $ctx () $canon)
           (if (== $by None) (Unfollowed argument-type $canon)
               (case (tr:as-goal $E $ctx $by $premise)
                 (((Unfollowed $a $b) (Unfollowed argument-type-restate $premise))
                  ($ok $ok))))))))
(= (tr:canon-sorts $t)
   (case $t
     (((Tm.app (Tm.named $s) $L)
       (if (== $s (egal:id "LeanSort"))
           (case $L
             (((Tm.app (Tm.named $o) $k) (if (== $o (egal:id "ordsucc")) (Tm.app (Tm.named (egal:id "LeanUniv")) $k) $t))
              ((Tm.named $z) (if (== $z (egal:id "Empty")) (Tm.named (egal:id "LeanProp")) $t))
              ($other $t)))
           (Tm.app (Tm.named $s) (tr:canon-sorts $L))))
      ((Tm.app $f $x) (Tm.app (tr:canon-sorts $f) (tr:canon-sorts $x)))
      ((Tm.lam $A $b) (Tm.lam $A (tr:canon-sorts $b)))
      ((Tm.all $A $b) (Tm.all $A (tr:canon-sorts $b)))
      ((Tm.imp $P $Q) (Tm.imp (tr:canon-sorts $P) (tr:canon-sorts $Q)))
      ($other $other))))

; A faithful theorem's parameters when the use gives no levels (a projection): for each type
; parameter, its level and that level's nat_p evidence, then the type and its universe
; membership, read from the context's hypothesis A :e LeanUniv L.
(= (tr:param-steps $E $ctx $As)
   (if (== $As ()) ()
       (let $A (car-atom $As)
         (case (tr:univ-hyp $E $ctx $A 0 (length-of (mg:hypotheses $ctx)))
           (((Univ $L $member)
             (let $nat (tr:prove-nat $E $ctx $L)
               (if (== $nat None) (tr:term-steps $As)
                   (cons-atom (T $L) (cons-atom (P $nat) (cons-atom (T $A) (cons-atom (P $member) (tr:param-steps $E $ctx (cdr-atom $As)))))))))
            ($none (cons-atom (T $A) (tr:param-steps $E $ctx (cdr-atom $As)))))))))
(= (tr:univ-hyp $E $ctx $A $i $n)
   (if (>= $i $n) None
       (let $h (mg:hyp (eq:theory $E) $ctx $i)
         (case (typ:parts (mgt:beta (mg:proposition $h)))
           (((Member $x (Tm.app (Tm.named $u) $L))
             (if (and (== $x $A) (== $u (egal:id "LeanUniv"))) (Univ $L $h) (tr:univ-hyp $E $ctx $A (+ $i 1) $n)))
            ($other (tr:univ-hyp $E $ctx $A (+ $i 1) $n)))))))

; A proof read out of a data structure (b.1, the hypothesis brecOn hands at a recursive field
; of below): x's type, evaluated by the rules (below at a constructor is a PProd), is the
; structure S at its parameters; the field's typing (S_field{i}_typed) puts the field in its
; type, a proposition, so 0 lies there.
(= (tr:follow-data-proj $E $ctx $env $goal $S $i $x $args)
   (let $v (tr:wire (tr:value $x) $env)
     (case (typ:infer $E $ctx () $v)
       ((None (Unfollowed (untyped-value $S) $goal))
        ((Typed $T $typed)
         (let* (($T2 (conv:result $T (conv:run $E $ctx (Cv.strong (egal:evaluator)) $T)))
                ($typed2 (if (== $T2 $T) $typed (typ:retype-inside $E $ctx $v $T $T2 $typed))))
           (if (== $typed2 None) (Unfollowed (data-proj-retype $S) $goal)
               (case (mg:try-known-in (eq:theory $E) $ctx (egal:id (format-args "{}_field{}_typed" ((egal $S) $i))))
                 (((Error $c $w) (Unfollowed (no-field-typing $S $i) $goal))
                  ($lemma
                    (case (tr:apply-steps $lemma (append-lists (tr:term-steps (tr:type-args $T2 ())) ((T $v) (P $typed2))))
                      (((Error $c2 $w2) (Unfollowed (data-proj $S $i) $w2))
                       ($ft (case (typ:parts (mg:proposition $ft))
                              (((Member $t $A) (tr:field-applied $E $ctx $env $goal $t $A $ft $args))
                               ($other (Unfollowed (data-proj-field $S $i) $goal)))))))))))))))))

; Eq.rec whose motive is a product (a proof of a function type), applied to more: the first six
; at the motive's statement at b, then that proof applied to the rest.
(= (tr:follow-eq-rec-further $E $ctx $env $goal $args)
   (let* (($first (take-n $args 6)) ($more (drop-n $args 6)) ($motive (mgt:nth $args 2)) ($b (mgt:nth $args 4)))
     (case $motive
       (((lam $x $T1 (lam $hx $T2 $body))
         (let* (($Mb (csubst (csubst $body (($hx (proof)))) (($x $b))))
                ($g1 (typ:member (tr:zero) (tr:wire $Mb $env)))
                ($t1 (tr:follow-eq-rec $E $ctx $env $g1 $first)))
           (case $t1
             (((Unfollowed $u $v) $t1)
              ($thm (case (tr:hyp-apply $E $ctx $env $thm $more)
                      (((Unfollowed $u2 $v2) (Unfollowed $u2 $v2))
                       ($t2 (tr:as-goal $E $ctx $t2 $goal)))))))))
        ($other (Unfollowed eq-rec-motive $goal))))))

; A maximum of two levels is a level (max and imax).
(= (tr:prove-nat-two $E $ctx $lemma $A $B)
   (let* (($pa (tr:prove-nat $E $ctx $A)) ($pb (tr:prove-nat $E $ctx $B)))
     (if (or (== $pa None) (== $pb None)) None
         (case (tr:apply-steps (mg:known-in (eq:theory $E) $ctx (egal:id $lemma)) ((T $A) (P $pa) (T $B) (P $pb)))
           (((Error $c $w) None) ($ok $ok))))))

; A hypothesis read one step further, as Lean's conversion reads it: a guard
; (x in {z :e 1 | z :e P}, a proof stored as a field) gives 0 :e P, and a type
; named by a definition (Not c) is the definition's body, only for a proof
; (its value 0) and only onto a product: below that are the sets themselves,
; which no argument applies.  None: no step left.
(= (tr:opened $op_E $op_ctx $op_thm)
   (case (typ:parts (mgt:beta (mg:proposition $op_thm)))
     (((Member $op_x $op_T)
       (let $op_by (tr:open-guard $op_E $op_ctx $op_thm $op_x $op_T)
         (if (== $op_by None)
             (let $op_def (if (== $op_x (tr:zero)) (tr:open-definition $op_E $op_ctx $op_thm $op_x $op_T) None)
               (if (== $op_def None) (tr:open-evaluated $op_E $op_ctx $op_thm $op_x $op_T) $op_def))
             $op_by)))
      ($op_other None))))
(= (tr:open-guard $og_E $og_ctx $og_thm $og_x $og_T)
   (case $og_T
     (((Tm.app (Tm.app (Tm.named $og_sep) $og_one) (Tm.lam $og_ty $og_body))
       (if (== $og_sep (egal:id "Sep"))
           (case (typ:parts $og_body)
             (((Member (Tm.db 0) $og_P)
               (let $og_p (mgt:beta (Tm.app (Tm.lam $og_ty $og_P) (tr:zero)))
                 (case (tr:apply-steps (mg:known-in (eq:theory $og_E) $og_ctx (egal:id "Lean_of_guard"))
                                       ((T $og_p) (T $og_x) (P $og_thm)))
                   (((Error $og_c $og_w) None) ($og_ok $og_ok)))))
              ($og_no None)))
           None))
      ($og_other None))))
(= (tr:open-definition $od_E $od_ctx $od_thm $od_x $od_T)
   (let $od_body (typ:unfold-head $od_T)
     (if (or (== $od_body None) (== (tr:pi-parts $od_body) None)) None
         (tr:stated-as $od_E $od_ctx (typ:member $od_x $od_body) $od_thm))))
(= (tr:as-goal-opened $ao_E $ao_ctx $ao_thm $ao_goal)
   (case (tr:as-goal $ao_E $ao_ctx $ao_thm $ao_goal)
     (((Unfollowed $ao_a $ao_b)
       (let $ao_open (tr:guard-of $ao_E $ao_ctx $ao_thm)
         (if (== $ao_open None) (Unfollowed $ao_a $ao_b)
             (tr:as-goal-opened $ao_E $ao_ctx $ao_open $ao_goal))))
      ($ao_ok $ao_ok))))
(= (tr:hyp-apply-opened $ha_E $ha_ctx $ha_env $ha_thm $ha_args)
   (let $ha_open (tr:opened $ha_E $ha_ctx $ha_thm)
     (if (== $ha_open None)
         (Unfollowed hypothesis-not-a-product (Refused (Proposition (egal:text (mg:proposition $ha_thm))) (Arguments $ha_args)))
         (tr:hyp-apply $ha_E $ha_ctx $ha_env $ha_open $ha_args))))
(= (tr:guard-of $gd_E $gd_ctx $gd_thm)
   (case (typ:parts (mgt:beta (mg:proposition $gd_thm)))
     (((Member $gd_x $gd_T) (tr:open-guard $gd_E $gd_ctx $gd_thm $gd_x $gd_T))
      ($gd_other None))))

; A theorem stating P itself, from one whose proposition converts to P: the identity
; at P applied to it (mg:exact checks the conversion and keeps the old proposition).
(= (tr:stated-as $sa_E $sa_ctx $sa_P $sa_thm)
   (case (mg:try-proof-binder (eq:theory $sa_E) $sa_ctx $sa_P)
     (((Error $sa_c $sa_w) None)
      ($sa_in (case (mg:try-proof-lam-of (mg:hyp (eq:theory $sa_E) $sa_in 0) $sa_P)
                (((Error $sa_c2 $sa_w2) None)
                 ($sa_id (case (mg:try-proof-app $sa_id $sa_thm)
                           (((Error $sa_c3 $sa_w3) None)
                            ($sa_ok $sa_ok))))))))))
; An abstraction against a product named by a definition (Not p): followed against the
; definition's body, and stated as the goal.
(= (tr:follow-lam-opened $lo_E $lo_ctx $lo_env $lo_goal $lo_x $lo_body)
   (case (typ:parts (mgt:beta $lo_goal))
     (((Member $lo_z $lo_T)
       (let $lo_open (typ:unfold-head $lo_T)
         (if (or (== $lo_open None) (== (tr:pi-parts $lo_open) None))
             (tr:follow-lam-evaluated $lo_E $lo_ctx $lo_env $lo_goal $lo_z $lo_T $lo_x $lo_body)
             (case (tr:follow-lam $lo_E $lo_ctx $lo_env (typ:member $lo_z $lo_open) $lo_x $lo_body)
               (((Unfollowed $lo_a $lo_b) (Unfollowed $lo_a $lo_b))
                ($lo_thm (let $lo_r (tr:stated-as $lo_E $lo_ctx $lo_goal $lo_thm)
                           (if (== $lo_r None) (Unfollowed lam-restate $lo_goal) $lo_r))))))))
      ($lo_other (Unfollowed lam-not-against-a-product $lo_goal)))))
; A field that is a proof (an induction hypothesis in a below tower), applied: it is 0 in
; its type, which is then a product for the arguments.
(= (tr:field-applied $fa_E $fa_ctx $fa_env $fa_goal $fa_t $fa_A $fa_thm $fa_args)
   (if (== $fa_args ()) (tr:zero-in $fa_E $fa_ctx $fa_t $fa_A $fa_thm $fa_goal)
       (case (tr:zero-in $fa_E $fa_ctx $fa_t $fa_A $fa_thm (typ:member (tr:zero) $fa_A))
         (((Unfollowed $fa_u $fa_w) (Unfollowed $fa_u $fa_w))
          ($fa_zero (case (tr:hyp-apply $fa_E $fa_ctx $fa_env $fa_zero $fa_args)
                      (((Unfollowed $fa_u2 $fa_w2) (Unfollowed $fa_u2 $fa_w2))
                       ($fa_done (tr:as-goal $fa_E $fa_ctx $fa_done $fa_goal)))))))))
; T is a proposition: proved, or T is a function into propositions at any argument
; (a motive at a proof, whose value 0 nothing types again).
(= (tr:prop-of $po_E $po_ctx $po_T)
   (let $po_by (typ:prove $po_E $po_ctx () (typ:member $po_T (Tm.named (egal:id "LeanProp"))))
     (if (== $po_by None)
         (let $po_guard (tr:prop-guard $po_E $po_ctx $po_T)
           (if (== $po_guard None) (tr:prop-applied $po_E $po_ctx $po_T) $po_guard))
         $po_by)))
; A guard {z :e 1 | z :e P} is a proposition (Lean_ProofField P, unfolded).
(= (tr:prop-guard $pg_E $pg_ctx $pg_T)
   (case $pg_T
     (((Tm.app (Tm.app (Tm.named $pg_sep) $pg_one) (Tm.lam $pg_ty $pg_body))
       (if (and (== $pg_sep (egal:id "Sep")) (== $pg_one (wire:literal 1)))
           (case (typ:parts $pg_body)
             (((Member (Tm.db 0) $pg_P)
               (let $pg_p (mgt:beta (Tm.app (Tm.lam $pg_ty $pg_P) (tr:zero)))
                 (case (tr:apply-steps (mg:known-in (eq:theory $pg_E) $pg_ctx (egal:id "Lean_ProofField_prop")) ((T $pg_p)))
                   (((Error $pg_c $pg_w) None) ($pg_ok $pg_ok)))))
              ($pg_no None)))
           None))
      ($pg_other None))))
(= (tr:prop-applied $pa_E $pa_ctx $pa_T)
   (case $pa_T
     (((Tm.app (Tm.app (Tm.named $pa_ap) $pa_f) $pa_x)
       (if (== $pa_ap (egal:id "ap"))
           (case (typ:infer $pa_E $pa_ctx () $pa_f)
             (((Typed $pa_Tf $pa_typed) (tr:prop-family $pa_E $pa_ctx $pa_f $pa_x (typ:pi-parts $pa_Tf) $pa_typed))
              ($pa_o None)))
           None))
      ($pa_other None))))
(= (tr:prop-family $pf_E $pf_ctx $pf_f $pf_x $pf_parts $pf_typed)
   (case $pf_parts
     (((PiOf $pf_X $pf_Y)
       (if (== (mgt:beta (Tm.app $pf_Y $pf_x)) (Tm.named (egal:id "LeanProp")))
           (case (mg:try-known-in (eq:theory $pf_E) $pf_ctx (egal:id "LeanPropFamily_ap_In"))
             (((Error $pf_c $pf_w) None)
              ($pf_rule (case (tr:apply-steps $pf_rule ((T $pf_X) (T $pf_f) (P $pf_typed) (T $pf_x)))
                          (((Error $pf_c2 $pf_w2) None) ($pf_ok $pf_ok))))))
           None))
      ($pf_other None))))
; An abstraction against a motive at its arguments: the product is its value, each beta
; step under its membership, and the proof is retyped along those steps.
(= (tr:follow-lam-evaluated $le_E $le_ctx $le_env $le_goal $le_z $le_T $le_x $le_body)
   (let $le_T2 (mgt:beta (conv:result $le_T (conv:run $le_E $le_ctx (Cv.strong (egal:evaluator)) $le_T)))
     (if (== (tr:pi-parts $le_T2) None) (Unfollowed lam-not-against-a-product $le_goal)
         (case (tr:follow-lam $le_E $le_ctx $le_env (typ:member $le_z $le_T2) $le_x $le_body)
           (((Unfollowed $le_a $le_b) (Unfollowed $le_a $le_b))
            ($le_thm (let $le_r (typ:retype-inside $le_E $le_ctx $le_z $le_T2 $le_T $le_thm)
                       (if (== $le_r None) (Unfollowed lam-retype $le_goal) $le_r))))))))
; Under a variable of a proposition, that proposition holds of 0 (proof irrelevance): a
; hypothesis for the body, discharged by Lean_prop_0_of before the binder closes.
(= (tr:follow-under $fu_E $fu_ctx $fu_env $fu_A $fu_goal $fu_body)
   (let $fu_fact (tr:proof-variable $fu_E $fu_ctx $fu_A)
     (if (== $fu_fact None) (tr:follow-goal $fu_E $fu_ctx $fu_env $fu_goal $fu_body)
         (let $fu_P (typ:member (tr:zero) $fu_A)
           (case (mg:try-proof-binder (eq:theory $fu_E) $fu_ctx $fu_P)
             (((Error $fu_c $fu_w) (tr:follow-goal $fu_E $fu_ctx $fu_env $fu_goal $fu_body))
              ($fu_in (case (tr:follow-goal $fu_E $fu_in $fu_env $fu_goal $fu_body)
                        (((Unfollowed $fu_a $fu_b) (Unfollowed $fu_a $fu_b))
                         ($fu_thm (tr:cut $fu_thm $fu_P $fu_fact)))))))))))
(= (tr:cut $cut_thm $cut_P $cut_fact)
   (case (mg:try-proof-lam-of $cut_thm $cut_P)
     (((Error $cut_c $cut_w) (Unfollowed cut $cut_w))
      ($cut_imp (case (mg:try-proof-app $cut_imp $cut_fact)
                  (((Error $cut_c2 $cut_w2) (Unfollowed cut $cut_w2))
                   ($cut_ok $cut_ok)))))))
(= (tr:proof-variable $pv_E $pv_ctx $pv_A)
   (let $pv_prop (tr:prop-of $pv_E $pv_ctx $pv_A)
     (if (== $pv_prop None) None
         (case (typ:infer-variable $pv_E $pv_ctx (Tm.db 0) (mg:hypotheses $pv_ctx) 0)
           (((Typed $pv_T $pv_in)
             (case (tr:apply-steps (mg:known-in (eq:theory $pv_E) $pv_ctx (egal:id "Lean_prop_0_of"))
                                   ((T $pv_A) (P $pv_prop) (T (Tm.db 0)) (P $pv_in)))
               (((Error $pv_c $pv_w) None) ($pv_ok $pv_ok))))
            ($pv_none None))))))
; A proof in hand whose type is a motive at its arguments (an induction hypothesis): it is
; 0 in the product that the motive's value is.  Only onto a product, from what was none.
(= (tr:open-evaluated $oe_E $oe_ctx $oe_thm $oe_x $oe_T)
   (case $oe_T
     (((Tm.app (Tm.app (Tm.named $oe_ap) $oe_f) $oe_a)
       (if (== $oe_ap (egal:id "ap")) (tr:open-motive $oe_E $oe_ctx $oe_thm $oe_x $oe_T) None))
      ($oe_other None))))
(= (tr:open-motive $om_E $om_ctx $om_thm $om_x $om_T)
   (let $om_T2 (mgt:beta (conv:result $om_T (conv:run $om_E $om_ctx (Cv.strong (egal:evaluator)) $om_T)))
     (if (== (tr:pi-parts $om_T2) None) None
         (let $om_at (typ:retype-inside $om_E $om_ctx $om_x $om_T $om_T2 $om_thm)
           (if (== $om_at None) None
               (if (== $om_x (tr:zero)) $om_at
                   (case (tr:zero-in $om_E $om_ctx $om_x $om_T2 $om_at (typ:member (tr:zero) $om_T2))
                     (((Unfollowed $om_u $om_w) None) ($om_ok $om_ok)))))))))
; A cut Lean's proof has silently (a motive at a proof): the fact proved, then a hypothesis
; for the proof that uses it, then discharged.
(= (tr:follow-have $hv_E $hv_ctx $hv_env $hv_goal $hv_fact $hv_by $hv_body)
   (let* (($hv_T (norm-term $hv_fact)) ($hv_P (typ:member (tr:zero) (tr:wire $hv_T $hv_env))))
     (case (tr:follow-goal $hv_E $hv_ctx $hv_env $hv_P $hv_by)
       (((Unfollowed $hv_a $hv_b) (Unfollowed $hv_a $hv_b))
        ($hv_proof
          (case (mg:try-proof-binder (eq:theory $hv_E) $hv_ctx $hv_P)
            (((Error $hv_c $hv_w) (Unfollowed cut-binder $hv_w))
             ($hv_in (case (tr:follow-goal $hv_E $hv_in $hv_env $hv_goal $hv_body)
                       (((Unfollowed $hv_a2 $hv_b2) (Unfollowed $hv_a2 $hv_b2))
                        ($hv_thm (tr:cut $hv_thm $hv_P $hv_proof))))))))))))
; A term enters the kernel with its matchers at their bodies, whether it is from a statement,
; an argument, a motive or a binder.  Only that: the reading must commute with substitution
; (a motive read and then instantiated is the instance read), as beta-normalizing would not.
(= (tr:wire $tw_t $tw_env) (wire (expand $tw_t) $tw_env))
