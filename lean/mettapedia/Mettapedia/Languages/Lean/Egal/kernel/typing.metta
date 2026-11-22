; Typing judgments as kernel theorems.
;
; A type of the Lean reading is a set, and "t has type T" is the theorem
; t :e T.  The prover here makes such theorems by the structure of the term:
;
;   a variable         by the hypothesis that introduces it
;   a named head       by the typing lemma declared for that head, its premises
;                      proved in turn (the arguments' types, levels, numerals)
;   an application f x of a set f (ap)
;                      the type of f is computed first; it is a function space
;                      Pi X Y, and f x :e Y x follows from x :e X (ap_Pi)
;   a function         under its binder, by typing its body at a variable of
;                      the domain (lam_Pi, a typing lemma with a quantified
;                      premise); its type is computed the same way, the
;                      family of result types read off the body's type
;
;   (typ:declare NAME)             the known NAME (a kernel name) is a typing
;                                  lemma, kept under the head of its subject
;   (Prover.lean)                  the prover, for megalodon_equations
;   (typ:infer E CONTEXT PATH T)   (Typed TYPE THEOREM) or None
;
; The typing lemmas are directed by syntax: a premise types a part of the
; subject, so a proof follows the term and ends with it.  No depth is
; counted.  A goal that comes up again while it is being proved is given up,
; which is what stops a lemma that is not of that kind: PATH holds the goals
; above along one proof, and the goals being proved anywhere are kept as
; evidence (a proof may compute, and the computation may ask again).
;
; "P holds" is 0 :e P.  It is proved by a proof in hand (h :e P, and every
; proof is 0), by the field of a constructor node (the node is typed by what
; it was computed from), by a lemma (as the goal stands, and for a goal about
; a variable after a view of a numeral), or, where the goal speaks of no
; variable and a lemma says which F decides it, by the value of F: a fact
; about closed terms is settled by running its decision.  "P does not hold"
; is (0 :e P) -> False, from Lean's proof of P -> False.
;
; Read after session.metta and terms.metta, with megalodon_equations imported;
; invert.metta, numerals.metta and compute.metta are read with it.  (An order
; between two numerals, a :e b, is proved by numerals.metta.)
;
; With (TypTrace on) in the space, each goal that is not proved is printed,
; the innermost first.

(= (typ:member $t $T) (Tm.app (Tm.app (Tm.named (lean:id "In")) $t) $T))
; (Member T TYPE) for a membership, Other for anything else.
(= (typ:parts $p)
   (case $p
     (((Tm.app (Tm.app (Tm.named $in) $t) $T) (if (== $in (lean:id "In")) (Member $t $T) Other))
      ($other Other))))
(= (typ:pi-parts $T)
   (case $T
     (((Tm.app (Tm.app (Tm.named $pi) $X) $Y) (if (== $pi (lean:id "Pi")) (PiOf $X $Y) Other))
      ($other Other))))
; The key a lemma or a goal is filed under: the head of the typed term, or
; for another predicate the predicate with the head of its first argument.
; The proof of a proposition is 0, so "P holds" is 0 :e P, filed under the
; head of P.
(= (typ:key $p)
   (case (typ:parts $p)
     (((Member $t $T) (if (== $t (Tm.named (lean:id "Empty"))) (KeyOf truth (mgt:head $T)) (mgt:head $t)))
      ($other (case $p
                (((Tm.app $f $x) (KeyOf (mgt:head $f) (mgt:head $x)))
                 ($atom (KeyOf $atom None))))))))

(= (typ:declared $key)
   (let $kept (collapse (match &self (TypRules $key $names) $names))
     (if (== $kept ()) () (car-atom $kept))))
; The key the lemma is kept under, or Refused when its conclusion is not
; about a named head (such a lemma gives no direction to a search).
(= (typ:declare $name)
   (let* (($statement (mg:proposition (mg:known (lean:theory) $name)))
          ($shape (rule:conclusion $statement 0)))
     (case $shape
       (((Concludes $n $conclusion)
         (let $key (typ:key (mgt:eta $conclusion))
           (if (typ:named-key $key)
               (let* (($before (typ:declared $key))
                      ($names (mgt:snoc $before $name))
                      ($gone (if (== $before ()) () (remove-atom &self (TypRules $key $before))))
                      ($done (add-atom &self (TypRules $key $names)))
                      ($decision (typ:note-decision $name (mgt:eta $conclusion))))
                 $key)
               Refused)))))))
; A lemma F x .. :e Lean_Decidable (R x ..) says that F decides R: it is
; kept under the head R, (TypDecision R NAME).
(= (typ:note-decision $name $conclusion)
   (case (typ:parts $conclusion)
     (((Member $call (Tm.app (Tm.named $family) $R))
       (if (== $family (lean:id "Lean_Decidable"))
           (case (mgt:head $R)
             (((Tm.named $head) (add-atom &self (TypDecision (Tm.named $head) $name)))
              ($other none)))
           none))
      ($other none))))
(= (typ:decisions $head) (collapse (match &self (TypDecision $head $name) $name)))
(= (typ:named-key $key)
   (case $key
     (((Tm.named $name) True)
      ((KeyOf (Tm.named $name) $first) True)
      ((KeyOf truth (Tm.named $name)) True)
      ($other False))))

; ---- the prover ----

(= (conv:prove-with (Prover.lean) $E $ctx $p)
   (let $found (typ:prove $E $ctx () $p) (if (== $found None) (empty) $found)))
; At a redex: the term a rule is being applied to.  A premise that types a
; field of a constructor node in the redex can then be proved from the type
; of the node (invert.metta).
(= (conv:prove-with (Prover.lean-at $redex) $E $ctx $p)
   (let $found (typ:prove $E $ctx (cons-atom (Redex $redex) ()) $p) (if (== $found None) (empty) $found)))
(= (conv:prove-with (Prover.lean-below $path) $E $ctx $p)
   (let $found (typ:prove $E $ctx $path $p) (if (== $found None) (empty) $found)))

(= (typ:prove $E $ctx $path $p)
   (let $q (mgt:beta $p)
     (case $q
       (((Tm.all $A $body) (typ:under $E $ctx $path $q))
        ((Tm.imp $premise $rest)
         (let $negative (typ:negative $E $ctx $path $q)
           (if (== $negative None) (typ:under $E $ctx $path $q) $negative)))
        ($other
         (let $assumed (collapse (mg:assumption (eq:theory $E) $ctx $q))
           (if (== $assumed ()) (typ:closed-or-here $E $ctx $path $q) (car-atom $assumed))))))))
; A goal that speaks of no variable of the context is the same fact under
; every binder: it is proved once, in the empty context, kept there under a
; name, and read in the context by that name.  Where the empty context does
; not prove it, it is tried in the context (a hypothesis there may be what it
; needs).  Where its decision has refuted it, only a proof in hand is looked
; for (in a branch that is not taken, a hypothesis can state what is false).
(= (typ:closed-or-here $E $ctx $path $q)
   (if (conv:in-empty-context $ctx) (typ:known-or-proved $E $ctx $path $q)
       (if (typ:about-a-variable $ctx $q) (typ:known-or-proved $E $ctx $path $q)
           (let $closed (typ:known-or-proved $E (mg:empty-context) (typ:goals-above $path) $q)
             (if (== $closed None)
                 (if (== (typ:settled-before $E (mg:empty-context) () $q) Refuted)
                     (typ:proof-in-hand $E $ctx $path $q)
                     (typ:known-or-proved $E $ctx $path $q))
                 (let $read (typ:read-settled $E $ctx $q)
                   (if (== $read None) (typ:known-or-proved $E $ctx $path $q) $read)))))))
; "A does not hold" is written (0 :e A) -> False.  Lean's proof of it is a
; member of A -> False: the field of an isFalse node, typed from the node as
; any field is.  The library's Lean_refutation_0 turns such a member into the
; statement.  (Where there is none, the goal is tried under its premise.)
(= (typ:negative $E $ctx $path $q)
   (case $q
     (((Tm.imp $premise $rest)
       (if (== $rest (Tm.named (lean:id "False")))
           (case (typ:parts $premise)
             (((Member $z $A)
               (if (== $z (Tm.named (lean:id "Empty"))) (typ:not-true $E $ctx $path $A $q) None))
              ($other None)))
           None))
      ($other None))))
(= (typ:not-true $E $ctx $path $A $q)
   (let* (($zero (Tm.named (lean:id "Empty")))
          ($not (Tm.app (Tm.app (Tm.named (lean:id "Pi")) $A) (Tm.lam (Tp.base 0) (Tm.named (lean:id "Lean_False_Prop")))))
          ($refutation (typ:prove $E $ctx $path (typ:member $zero $not))))
     (if (== $refutation None) None
         (let $prop (typ:prove $E $ctx $path (typ:member $A (Tm.named (lean:id "LeanProp"))))
           (if (== $prop None) None
               (case (mg:try-proof-app (mg:term-app (mg:known-in (eq:theory $E) $ctx (lean:id "Lean_refutation_0")) $A) $prop)
                 (((Error $c1 $w1) None)
                  ($for-A
                   (case (mg:try-proof-app (mg:term-app $for-A $zero) $refutation)
                     (((Error $c2 $w2) None)
                      ($both (typ:left-of $E $ctx $q $both
                                          (Tm.app (Tm.app (Tm.named (lean:id "nIn")) $zero) $A)
                                          (eq:of $E $zero $zero)))))))))))))
; The left part of a proved conjunction, as the goal states it.
(= (typ:left-of $E $ctx $q $both $left $right)
   (case (mg:try-proof-app (mg:term-app (mg:term-app (mg:known-in (eq:theory $E) $ctx (lean:id "andEL")) $left) $right) $both)
     (((Error $c3 $w3) None)
      ($proved
       (let $checked (collapse (mg:exact (eq:theory $E) $ctx $q $proved))
         (if (== $checked ()) None (car-atom $checked)))))))
; What the prover keeps (facts proved, goals that failed, the epoch) is
; evidence, kept where the equation library keeps its own, and like its rows
; under the name of the theory's equality (a sealed theory inside a query
; cannot be looked up by an index).
(= (typ:evidence) (conv:evidence))
(= (typ:evidence-for $ctx) (conv:evidence-for $ctx))
; A universe level that a lemma or an equation of Lean leaves open is read
; off the premise that says "X lives at this level" (X :e LeanSort l, or
; X :e LeanUniv l): the type of X is computed, and it names the level.  So
; no level is guessed.  X is a later quantifier that the match bound, or a
; term with no variable of the statement left in it.
(= (conv:witness-with (Prover.lean) $E $ctx $body $k $binds) (typ:witness $E $ctx $body $k $binds 0))
(= (conv:witness-with (Prover.lean-at $redex) $E $ctx $body $k $binds) (typ:witness $E $ctx $body $k $binds 0))
(= (conv:witness-with (Prover.lean-below $path) $E $ctx $body $k $binds) (typ:witness $E $ctx $body $k $binds 0))
(= (typ:witness $E $ctx $p $k $binds $d)
   (case $p
     (((Tm.all $A $body) (typ:witness $E $ctx $body $k $binds (+ $d 1)))
      ((Tm.imp $premise $rest)
       (let $found (typ:witness-in $E $ctx $premise $k $binds $d)
         (if (== $found None) (typ:witness $E $ctx $rest $k $binds $d) $found)))
      ($other None))))
(= (typ:witness-in $E $ctx $premise $k $binds $d)
   (case (typ:parts $premise)
     (((Member $x (Tm.app (Tm.named $sort) $level))
       (if (== $level (Tm.db $d))
           (if (or (== $sort (lean:id "LeanSort")) (== $sort (lean:id "LeanUniv")))
               (typ:level-of $E $ctx $sort (typ:witness-subject $x $k $binds $d))
               None)
           None))
      ($other None))))
(= (typ:witness-subject $x $k $binds $d)
   (case $x
     (((Tm.db $i) (if (< $i $d) (mgt:bound (- (+ $k $d) $i) $binds) None))
      ($other (if (typ:mentions-upto $x $d) None (mgt:shift $x (- 0 (+ $d 1)) 0))))))
(= (typ:mentions-upto $x $i)
   (if (< $i 0) False (if (mgt:mentions $x $i) True (typ:mentions-upto $x (- $i 1)))))
(= (typ:level-of $E $ctx $sort $subject)
   (if (== $subject None) None
       (let* (($key (eq:name $E)) ($kept (collapse (match (typ:evidence) (TypLevel $key $ctx $sort $subject $level) $level))))
         (if (== $kept ())
             (let* (($level (case (typ:infer $E $ctx () $subject)
                              (((Typed $type $theorem) (typ:level-from $sort $type))
                               ($other None))))
                    ($done (add-atom (typ:evidence) (TypLevel $key $ctx $sort $subject $level))))
               $level)
             (car-atom $kept)))))
; Sort 0 is the propositions and Sort (l + 1) the universe l.
(= (typ:level-from $sort $type)
   (case $type
     (((Tm.app (Tm.named $u) $level)
       (if (== $u (lean:id "LeanUniv"))
           (if (== $sort (lean:id "LeanUniv")) $level (Tm.app (Tm.named (lean:id "ordsucc")) $level))
           (if (== $u (lean:id "LeanSort"))
               (if (== $sort (lean:id "LeanSort")) $level
                   (case $level (((Tm.app (Tm.named $s) $below) (if (== $s (lean:id "ordsucc")) $below None)) ($zero None))))
               None)))
      ((Tm.named $prop)
       (if (== $prop (lean:id "LeanProp")) (if (== $sort (lean:id "LeanSort")) (wire:literal 0) None) None))
      ($other None))))
; Whether a proposition is refuted here: its negation is proved (x /:e T for
; a membership, P -> False otherwise).  An open goal that is refuted is not
; open: it is decided, the other way.
(= (typ:refuted $E $ctx $p)
   (let $negation (case (typ:parts $p)
                    (((Member $x $T) (Tm.app (Tm.app (Tm.named (lean:id "nIn")) $x) $T))
                     ($other (Tm.imp $p (Tm.named (lean:id "False"))))))
     (not (== (typ:prove $E $ctx () $negation) None))))
; A fact proved once is kept: the same goal in the same context is one
; lookup.  (So what a step established, a later step can use: the proof of a
; decided proposition, found when its decision was taken apart, is there
; when the branch is entered.)
(= (typ:known-or-proved $E $ctx $path $q)
   (let* (($key (eq:name $E)) ($kept (collapse (match (typ:evidence-for $ctx) (TypFact $key $ctx $q $theorem) $theorem))))
     (if (== $kept ())
         (if (typ:on-path $q $path) None
             (if (typ:failed-before $E $ctx $q) None
                 (if (typ:being-proved $E $ctx $q) None
                     (let* (($below (cons-atom $q $path))
                            ($mark (add-atom (typ:evidence) (TypProving $key $ctx $q)))
                            ($proved (if (== (collapse (match &self (TypTrace on) on)) ())
                                         (typ:atomic $E $ctx $below $q)
                                         (typ:atomic-traced $E $ctx $below $q)))
                            ($unmark (remove-atom (typ:evidence) (TypProving $key $ctx $q))))
                       (if (== $proved None)
                           (typ:fail $E $ctx $q)
                           (let* (($held (conv:seal-out $E $ctx $proved)) ($done (add-atom (typ:evidence-for $ctx) (TypFact $key $ctx $q $held)))) $proved))))))
         (conv:seal-in $E $ctx (car-atom $kept)))))
; A goal that is being proved is not started again.  The goals above are
; known along one proof (typ:on-path); but a proof may compute (a type is
; computed, a decision is run), the computation may ask for a premise, and
; that premise may be the goal the proof began with.  So the goals being
; proved are also kept as evidence, where every such ask finds them.
(= (typ:being-proved $E $ctx $q)
   (let $key (eq:name $E)
     (not (== (collapse (match (typ:evidence) (TypProving $key $ctx $q) proving)) ()))))
; A goal that failed is not tried again while nothing new can be known: the
; failures are kept for an epoch, and a new epoch begins after each step that
; a computation makes and after each evaluation made for a type the first
; time (those are what add origins and change the term a rule is applied
; to; an attempt that makes no step, or an answer met again, adds nothing),
; where a failure was kept in the epoch that ends.  Without this a goal with several routes
; fails once for every route of every goal above it.  A failure is looked up
; with the current epoch, so the rows of earlier epochs are left as they are:
; removing a row costs the size of the goal in it, and a long computation
; has hundreds of thousands of them.
(= (typ:epoch)
   (let $kept (collapse (match (typ:evidence) (TypEpoch $n) $n)) (if (== $kept ()) 0 (car-atom $kept))))
(= (typ:failed-before $E $ctx $q)
   (let* (($epoch (typ:epoch)) ($key (eq:name $E)))
     (not (== (collapse (match (typ:evidence-for $ctx) (TypFail $key $ctx $q $epoch) failed)) ()))))
(= (typ:fail $E $ctx $q)
   (let* (($epoch (typ:epoch)) ($key (eq:name $E))
          ($done (add-atom (typ:evidence-for $ctx) (TypFail $key $ctx $q $epoch)))
          ($noted (if (== (collapse (match (typ:evidence) (TypFailedIn $epoch) noted)) ())
                      (add-atom (typ:evidence) (TypFailedIn $epoch))
                      ())))
     None))
(= (typ:new-epoch)
   (let $n (typ:epoch)
     (if (== (collapse (match (typ:evidence) (TypFailedIn $n) noted)) ()) same
         (let* (($gone (if (== $n 0) () (remove-atom (typ:evidence) (TypEpoch $n))))
                ($m (+ $n 1))
                ($done (add-atom (typ:evidence) (TypEpoch $m))))
           $m))))
; An evaluation made for a type tells something new the first time; met again it is the
; answer kept, and the failures kept since still hold.
(= (typ:learned $E $ctx $how $T $answer)
   (if (== $answer Same) same
       (let* (($key (eq:name $E))
              ($seen (collapse (match (typ:evidence-for $ctx) (TypLearned $key $ctx $how $T) seen))))
         (if (== $seen ())
             (let $noted (add-atom (typ:evidence-for $ctx) (TypLearned $key $ctx $how $T)) (typ:new-epoch))
             same))))
(= (typ:on-path $q $path)
   (if (== $path ()) False (if (== (car-atom $path) $q) True (typ:on-path $q (cdr-atom $path)))))
; Under binders the variables are new, so the goals above are other goals.
(= (typ:under $E $ctx $path $q)
   (let $proved (collapse (mg:run (Tac.intros (Tac.prove (eq:name $E) (Prover.lean))) (eq:theory $E) $ctx $q))
     (if (== $proved ()) None (car-atom $proved))))
(= (typ:atomic $E $ctx $path $q)
   (case (typ:settled-before $E $ctx $path $q)
     ((None (typ:searched $E $ctx $path $q))
      (Refuted None)
      ($proved $proved))))
(= (typ:searched $E $ctx $path $q)
   (let $direct (typ:direct $E $ctx $path $q)
     (if (== $direct None)
         (case (typ:parts $q)
           (((Member $t $T) (typ:indirect $E $ctx $path $t $T))
            ($other None)))
         $direct)))
(= (typ:direct $E $ctx $path $q)
   (let $step (conv:known-fact $E $ctx $q)
     (if (== $step None) (typ:direct-searched $E $ctx $path $q) $step)))
; (A fact a step of a rule established, its companion at the step's
; arguments, is read first.)
(= (typ:direct-searched $E $ctx $path $q)
   (if (== $q (Tm.named (lean:id "False"))) (typ:contradiction $E $ctx (mg:hypotheses $ctx) 0)
       (let $order (num:order $E $ctx $q)
         (if (== $order None)
             (let $field (typ:proof-field $E $ctx $path $q)
               (if (== $field None)
                   (let $in-hand (typ:proof-in-hand $E $ctx $path $q)
                     (if (== $in-hand None) (typ:direct-lemma $E $ctx $path $q) $in-hand))
                   $field))
             $order))))
; Every proof is 0.  A proposition is a subset of 1, so where a hypothesis
; h :e P is in hand (the branch of a conditional is entered under such an h)
; and P is a proposition, 0 :e P: h is in 1 by PowerE, so h = 0 by In_1_eq_0.
; The lemma is proved once in the theory, as Lean_proof_is_zero.
(= (typ:proof-in-hand $E $ctx $path $q)
   (case (typ:parts $q)
     (((Member $z $P)
       (if (== $z (Tm.named (lean:id "Empty")))
           (typ:proof-from $E $ctx $path $P (mg:hypotheses $ctx) 0)
           None))
      ($other None))))
(= (typ:proof-from $E $ctx $path $P $hyps $index)
   (if (== $hyps ()) None
       (case (typ:parts (car-atom $hyps))
         (((Member $h $P2)
           (if (== $P2 $P)
               (let $is-prop (typ:prove $E $ctx $path (typ:member $P (Tm.named (lean:id "LeanProp"))))
                 (if (== $is-prop None) (typ:proof-from $E $ctx $path $P (cdr-atom $hyps) (+ $index 1))
                     (typ:proof-is-zero $E $ctx $P $is-prop $h (mg:hyp (eq:theory $E) $ctx $index))))
               (typ:proof-from $E $ctx $path $P (cdr-atom $hyps) (+ $index 1))))
          ($other (typ:proof-from $E $ctx $path $P (cdr-atom $hyps) (+ $index 1)))))))
(= (typ:proof-is-zero $E $ctx $P $is-prop $h $has)
   (let $lemma (typ:proof-is-zero-lemma $E)
     (if (== $lemma None) None
         (case (mg:try-proof-app (mg:term-app (mg:known-in (eq:theory $E) $ctx $lemma) $P) $is-prop)
           (((Error $c1 $w1) None)
            ($for-P (case (mg:try-proof-app (mg:term-app $for-P $h) $has)
                      (((Error $c2 $w2) None)
                       ($done $done)))))))))
; forall p, p :e LeanProp -> forall h, h :e p -> 0 :e p
(= (typ:proof-is-zero-lemma $E)
   (case (mg:try-known (eq:theory $E) "Lean_proof_is_zero")
     (((Error $call $why)
       (let* (($in (Tm.named (lean:id "In"))) ($zero (Tm.named (lean:id "Empty"))) ($prop (Tm.named (lean:id "LeanProp")))
              ($claim (Tm.all (Tp.base 0) (Tm.imp (Tm.app (Tm.app $in (Tm.db 0)) $prop)
                        (Tm.all (Tp.base 0) (Tm.imp (Tm.app (Tm.app $in (Tm.db 0)) (Tm.db 1))
                                                    (Tm.app (Tm.app $in $zero) (Tm.db 1))))))))
         (case (mg:prove-by (eq:theory $E) "Lean_proof_is_zero" $claim (Tac.intros (Tac.prove (eq:name $E) (Prover.proof-is-zero))))
           (((Error $call2 $why2) None)
            ($proved "Lean_proof_is_zero")))))
      ($known "Lean_proof_is_zero"))))
(= (conv:witness-with (Prover.proof-is-zero) $E $ctx $body $k $binds) None)
; in hand: p (variable 1), p :e LeanProp (hypothesis 1), h (variable 0), h :e p (hypothesis 0)
(= (conv:prove-with (Prover.proof-is-zero) $E $ctx $goal)
   (let* (($th (eq:theory $E)) ($p (Tm.db 1)) ($h (Tm.db 0)) ($zero (Tm.named (lean:id "Empty")))
          ($one (Tm.app (Tm.named (lean:id "ordsucc")) $zero))
          ($sub (mg:try-proof-app (mg:term-app (mg:term-app (mg:known-in $th $ctx (lean:id "PowerE")) $one) $p) (mg:hyp $th $ctx 1))))
     (case $sub
       (((Error $c1 $w1) (empty))
        ($subset
         (case (mg:try-proof-app (mg:term-app $subset $h) (mg:hyp $th $ctx 0))
           (((Error $c2 $w2) (empty))
            ($in-one
             (case (mg:try-proof-app (mg:term-app (mg:known-in $th $ctx (lean:id "In_1_eq_0")) $h) $in-one)
               (((Error $c3 $w3) (empty))
                ($h-is-zero
                 (eq:mp $E $ctx (Tm.lam (Tp.base 0) (typ:member (Tm.db 0) (Tm.db 2))) $zero $h
                        (eq:sym $E $ctx $h $zero $h-is-zero) (mg:hyp $th $ctx 0)))))))))))))
; The proof field of a structure is typed 0 :e {z :e 1 | z :e P}: that is
; 0 :e P, by Lean_ProofField_intro (the kernel unfolds Lean_ProofField).
(= (typ:proof-field $E $ctx $path $q)
   (case (typ:parts $q)
     (((Member $z (Tm.app (Tm.app (Tm.named $sep) $one) (Tm.lam $A $body)))
       (if (and (== $sep (lean:id "Sep")) (== $z (Tm.named (lean:id "Empty"))))
           (case (typ:parts $body)
             (((Member $inner-subject $P1)
               (if (and (== $inner-subject (Tm.db 0)) (not (mgt:mentions $P1 0)))
                   (let* (($P (mgt:shift $P1 -1 0))
                          ($holds (typ:prove $E $ctx $path (typ:member $z $P))))
                     (if (== $holds None) None
                         (case (mg:try-proof-app
                                 (mg:term-app (mg:known-in (eq:theory $E) $ctx (lean:id "Lean_ProofField_intro")) $P) $holds)
                           (((Error $call $why) None)
                            ($thm (let $checked (collapse (mg:exact (eq:theory $E) $ctx $q $thm))
                                    (if (== $checked ()) None (car-atom $checked))))))))
                   None))
              ($other None)))
           None))
      ($other None))))
; False, where an equation in hand is between nodes of different constructors.
(= (typ:contradiction $E $ctx $hyps $index)
   (if (== $hyps ()) None
       (case (eq:sides $E (car-atom $hyps))
         (((Sides $a $b)
           (let $false (if (== (mgt:head $a) (mgt:head $b)) None
                           (typ:absurd-equation $E $ctx (mg:hyp (eq:theory $E) $ctx $index) $a $b))
             (if (== $false None) (typ:contradiction $E $ctx (cdr-atom $hyps) (+ $index 1)) $false)))
          ($other (typ:contradiction $E $ctx (cdr-atom $hyps) (+ $index 1)))))))
; Two different constructors; or a numeral against a constructor, the
; numeral seen as Lean's zero or successor first.
(= (typ:absurd-equation $E $ctx $equation $a $b)
   (let $direct (inv:false-from $E $ctx $equation $a $b)
     (if (== $direct None) (typ:absurd-viewed $E $ctx $equation $a $b) $direct)))
(= (typ:absurd-viewed $E $ctx $equation $a $b)
   (case (conv:run $E $ctx (Cv.lean-view (Prover.lean)) $a)
     (((Conv $a2 $view)
       (if (== (mgt:head $a2) (mgt:head $b)) None
           (inv:false-from $E $ctx (eq:trans $E $ctx $a2 $a $b (eq:sym $E $ctx $a $a2 $view) $equation) $a2 $b)))
      ($other
       (case (conv:run $E $ctx (Cv.lean-view (Prover.lean)) $b)
         (((Conv $b2 $view)
           (if (== (mgt:head $a) (mgt:head $b2)) None
               (inv:false-from $E $ctx (eq:trans $E $ctx $a $b $b2 $equation $view) $a $b2)))
          ($none None)))))))
(= (typ:direct-lemma $E $ctx $path $q)
   (case (typ:parts $q)
     (((Member (Tm.app (Tm.app (Tm.named $ap) $f) $x) $T)
       (if (== $ap (lean:id "ap")) (typ:applied $E $ctx $path $f $x $q)
           (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q)))
      ((Member $zero $T)
       (if (== $zero (Tm.named (lean:id "Empty")))
           (let $declared (typ:declared (typ:key $q))
             (if (== $declared ()) (typ:by-definition $E $ctx $path $zero $T $q) (typ:try $E $ctx $path $declared $q)))
           (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q)))
      ($other
       (case $q
         (((Tm.app (Tm.named $pred) $n)
           (if (== $pred (lean:id "nat_p")) (typ:natural $E $ctx $path $n $q)
               (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q)))
          ($else (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q))))))))

; Where no lemma states the goal as it is written:
;   the type the term has by its lemmas, where that type and the wanted one
;   have the same value (a type is a term and is computed like one);
;   or the type of a term this one was computed from (the evaluator keeps
;   s = t for every t it reached: a value has the type of what it came from).
(= (typ:indirect $E $ctx $path $t $T)
   (if (typ:has-decision $E $ctx $t $T)
       (let $by-inversion (typ:by-inversion $E $ctx $path $t $T)
         (if (== $by-inversion None)
             (case (typ:settle $E $ctx $path $T)
               ((None (typ:indirect-general $E $ctx $path $t $T))
                (Refuted None)
                ($proved $proved)))
             $by-inversion))
       (typ:indirect-general $E $ctx $path $t $T)))
(= (typ:indirect-general $E $ctx $path $t $T)
   (let $by-type (typ:by-type $E $ctx $t $T (typ:infer $E $ctx $path $t))
     (if (== $by-type None)
         (let $by-origin (typ:by-origin $E $ctx $path $t $T (typ:origins $E $ctx $t))
           (if (== $by-origin None)
               (let $by-inversion (typ:by-inversion $E $ctx $path $t $T)
                 (if (== $by-inversion None)
                     (let $at-value (typ:at-value $E $ctx $path $t $T)
                       (if (== $at-value None) (typ:by-step-value $E $ctx $t $T) $at-value))
                     $by-inversion))
               $by-origin))
         $by-type)))
;   or, for 0 in a proposition, a fact a step kept (a rule's companion)
;   whose type has the same value as the wanted one: the two are one set.
(= (typ:by-step-value $E $ctx $t $T)
   (if (== $t (Tm.named (lean:id "Empty")))
       (let $facts (conv:known-facts $E $ctx)
         (if (== $facts ()) None
             (let $wanted (conv:run $E $ctx (Cv.strong (lean:evaluator)) $T)
               (typ:step-value-in $E $ctx $t $T $wanted (conv:result $T $wanted) $facts))))
       None))
(= (typ:step-value-in $E $ctx $t $T $wanted $value $facts)
   (if (== $facts ()) None
       (let $found (case (car-atom $facts)
                     (((Fact $p $theorem)
                       (case (typ:parts $p)
                         (((Member $s $X)
                           (if (== $s $t)
                               (let $kept (conv:run $E $ctx (Cv.strong (lean:evaluator)) $X)
                                 (if (== (conv:result $X $kept) $value)
                                     (typ:from-value $E $ctx $t $T $wanted (typ:to-value $E $ctx $t $X $kept $theorem))
                                     None))
                               None))
                          ($other None))))
                      ($other None)))
         (if (== $found None) (typ:step-value-in $E $ctx $t $T $wanted $value (cdr-atom $facts)) $found))))
;   or, last, at the value of the type: a type that is not yet a value is
;   computed (a proposition about closed terms becomes one a constructor
;   proves: the length of the first half = 4 becomes 4 = 4).
(= (typ:at-value $E $ctx $path $t $T)
   (let $answer (conv:run $E $ctx (Cv.strong (lean:evaluator)) $T)
     (case $answer
       ((Same None)
        ((Conv $value $equation)
         (let* (($epoch (typ:learned $E $ctx strong $T $answer))
                ($proved (typ:prove $E $ctx $path (typ:member $t $value))))
           (if (== $proved None) None (typ:from-value $E $ctx $t $T $answer $proved))))))))
;   For "R a .. holds" where the goal speaks of no variable and a lemma says
;   that F decides R (F x .. :e Lean_Decidable (R x ..)), the routes above
;   come second: a fact about closed terms that a decision procedure settles
;   is settled by it.  First what a node in the redex says (its field is the
;   proof), then the value of F a ..: isTrue gives the proof, by the type of
;   the node; isFalse says that the goal does not hold, and nothing more is
;   tried.  The decision is run in the empty context, once: the fact is the
;   same under every binder, and is read there by its name.
;
; (typ:decision-of E CTX P): the terms F a .. that decide P.
(= (typ:has-decision $E $ctx $t $T)
   (if (== $t (Tm.named (lean:id "Empty"))) (not (== (typ:decision-of $E $ctx $T) ())) False))
(= (typ:decision-of $E $ctx $P)
   (if (typ:about-a-variable $ctx $P) ()
       (typ:decisions-from $E $ctx $P (typ:decisions (mgt:head $P)))))
(= (typ:decisions-from $E $ctx $P $names)
   (if (== $names ()) ()
       (let* (($one (typ:decision-by $E $ctx $P (car-atom $names)))
              ($rest (typ:decisions-from $E $ctx $P (cdr-atom $names))))
         (if (== $one None) $rest (cons-atom $one $rest)))))
(= (typ:decision-by $E $ctx $P $name)
   (case (rule:conclusion (mg:proposition (mg:known-in (eq:theory $E) $ctx $name)) 0)
     (((Concludes $n $conclusion)
       (case (typ:parts (mgt:eta $conclusion))
         (((Member $call (Tm.app $family $R))
           (let $binds (mgt:match $R $P $n 0 ())
             (if (== $binds fail) None (typ:fill $call $n $binds))))
          ($other None))))
      ($other None))))
; A pattern with its variables filled from the matcher's bindings; None
; where one is not bound, or where the pattern has a binder.
(= (typ:fill $pattern $n $binds)
   (case $pattern
     (((Tm.db $j) (mgt:bound (- (- $n 1) $j) $binds))
      ((Tm.app $f $x)
       (let $filled (typ:fill $f $n $binds)
         (if (== $filled None) None
             (let $argument (typ:fill $x $n $binds)
               (if (== $argument None) None (Tm.app $filled $argument))))))
      ((Tm.lam $A $b) None)
      ($other $other))))
; What is already settled about the goal q, read in CTX: the proof kept for
; it, what a decision that has come to a value says (the proof, or Refuted),
; or None.  A goal that was decided is not searched for.
(= (typ:settled-before $E $ctx $path $q)
   (case (typ:parts $q)
     (((Member $z $P)
       (if (== $z (Tm.named (lean:id "Empty")))
           (let $decisions (typ:decision-of $E $ctx $P)
             (if (== $decisions ()) None
                 (let $kept (typ:read-settled $E $ctx $q)
                   (if (== $kept None)
                       (typ:deliver $E $ctx $q
                                    (typ:read-decisions $E (mg:empty-context) (typ:goals-above $path) $P $decisions))
                       $kept))))
           None))
      ($other None))))
; The same, and where no decision has come to a value yet one is run.
(= (typ:settle $E $ctx $path $P)
   (let* (($q (typ:member (Tm.named (lean:id "Empty")) $P))
          ($before (typ:settled-before $E $ctx $path $q)))
     (if (== $before None)
         (let* (($decisions (typ:decision-of $E $ctx $P))
                ($ran (typ:run-decisions $E (mg:empty-context) (typ:goals-above $path) $P $decisions)))
           (typ:deliver $E $ctx $q $ran))
         $before)))
; A proof made in the empty context is kept there under a name (the row of
; the goal says which) and is the theorem of that name in CTX.
(= (typ:deliver $E $ctx $q $found)
   (case $found
     ((None None)
      (Refuted Refuted)
      ($proved
       (let* (($empty (mg:empty-context)) ($key (eq:name $E))
              ($held (conv:seal-out $E $empty $proved))
              ($done (add-atom (typ:evidence-for $empty) (TypFact $key $empty $q $held))))
         (if (conv:in-empty-context $ctx) $proved (typ:read-settled $E $ctx $q)))))))
(= (typ:read-settled $E $ctx $q)
   (let* (($empty (mg:empty-context)) ($key (eq:name $E))
          ($kept (collapse (match (typ:evidence-for $empty) (TypFact $key $empty $q $held) $held))))
     (if (== $kept ()) None
         (case (car-atom $kept)
           (((Named $name) (mg:known-in (eq:theory $E) $ctx $name))
            ($other None))))))
(= (typ:read-decisions $E $ctx $path $P $decisions)
   (if (== $decisions ()) None
       (let $kept (conv:kept $E $ctx (lean:evaluator) (car-atom $decisions))
         (if (== $kept ()) (typ:read-decisions $E $ctx $path $P (cdr-atom $decisions))
             (let $said (typ:decision-says $E $ctx $path $P (car-atom $kept))
               (if (== $said None) (typ:read-decisions $E $ctx $path $P (cdr-atom $decisions)) $said))))))
; The goals above, without the redex: the decision is read in the empty
; context, where the term a rule is being applied to may not be a term.
(= (typ:goals-above $path)
   (if (== $path ()) ()
       (case (car-atom $path)
         (((Redex $term) (typ:goals-above (cdr-atom $path)))
          ($goal (let $rest (typ:goals-above (cdr-atom $path)) (cons-atom $goal $rest)))))))
(= (typ:decision-says $E $ctx $path $P $answer)
   (case $answer
     (((Conv $node $equation)
       (if (== (mgt:head $node) (Tm.named (lean:id "Lean_Decidable_isTrue_node")))
           (typ:invert-node $E $ctx $path (Tm.named (lean:id "Empty")) $P $node)
           (if (== (mgt:head $node) (Tm.named (lean:id "Lean_Decidable_isFalse_node"))) Refuted None)))
      ($other None))))
; A decision is run.  It may be the very one whose computation asked (a rule
; on the way has "P holds" as its premise).  A decision that is being
; decided is not started again: the first run comes to its value and keeps
; it, and the computation that asked finds it kept.
(= (typ:run-decisions $E $ctx $path $P $decisions)
   (if (== $decisions ()) None
       (let $found (typ:run-decision $E $ctx $path $P (car-atom $decisions))
         (if (== $found None) (typ:run-decisions $E $ctx $path $P (cdr-atom $decisions)) $found))))
(= (typ:run-decision $E $ctx $path $P $decision)
   (let* (($key (eq:name $E))
          ($running (collapse (match (typ:evidence) (TypDeciding $key $decision) running))))
     (if (== $running ())
         (let* (($mark (add-atom (typ:evidence) (TypDeciding $key $decision)))
                ($answer (conv:run $E $ctx (lean:evaluator) $decision))
                ($unmark (remove-atom (typ:evidence) (TypDeciding $key $decision))))
           (typ:decision-says $E $ctx $path $P $answer))
         None)))
;   or, for a field of a constructor node in the redex, the type of the node
;   turned around (invert.metta): the node is typed by what it came from.
(= (typ:redex-of $path)
   (if (== $path ()) None
       (case (car-atom $path) (((Redex $t) $t) ($other (typ:redex-of (cdr-atom $path)))))))
(= (typ:by-inversion $E $ctx $path $y $T)
   (let $redex (typ:redex-of $path)
     (if (== $redex None) None (typ:invert-in $E $ctx $path $y $T (mgt:spine-args $redex)))))
(= (typ:invert-in $E $ctx $path $y $T $terms)
   (if (== $terms ()) None
       (let $found (typ:invert-node $E $ctx $path $y $T (car-atom $terms))
         (if (== $found None) (typ:invert-in $E $ctx $path $y $T (cdr-atom $terms)) $found))))
(= (typ:invert-node $E $ctx $path $y $T $node)
   (let* (($args (mgt:spine-args $node)) ($k (mgt:position $y $args 0)))
     (if (== $k None) (typ:invert-in $E $ctx $path $y $T $args)
         (let $name (inv:field $E (mgt:head $node) $k)
           (if (== $name None) (typ:invert-in $E $ctx $path $y $T $args)
               (let $found (typ:invert-with $E $ctx $path $y $T $node $name)
                 (if (== $found None) (typ:invert-in $E $ctx $path $y $T $args) $found)))))))
(= (typ:invert-with $E $ctx $path $y $T $node $name)
   (let* (($known (mg:known-in (eq:theory $E) $ctx $name))
          ($statement (mg:proposition $known)))
     (case (rule:conclusion $statement 0)
       (((Concludes $n $conclusion)
         (case (typ:parts (rules:final-premise $statement None))
           (((Member $pattern $ftype)
             (let $binds (mgt:match $pattern $node $n 0 ())
               (if (== $binds fail) None
                   (case (rule:instantiate $E $ctx (Prover.lean-below $path) (wire:literal 0) $known $statement 0 $binds)
                     (((Instance $thm $stated)
                       (case (typ:parts (mgt:beta $stated))
                         (((Member $s $type) (typ:by-type $E $ctx $y $T (Typed $type $thm)))
                          ($other None))))
                      ($other None))))))
            ($other None))))
        ($other None)))))
(= (typ:by-type $E $ctx $t $T $inferred)
   (case $inferred
     (((Typed $T1 $thm) (if (== $T1 $T) $thm (typ:retype $E $ctx $t $T1 $T $thm)))
      ($other None))))
(= (typ:retype $E $ctx $t $T1 $T $thm) (typ:retype-by-values $E $ctx $t $T1 $T $thm))
(= (typ:retype-by-values $E $ctx $t $T1 $T $thm)
   (let* (($a1 (conv:run $E $ctx (lean:evaluator) $T1))
          ($a2 (conv:run $E $ctx (lean:evaluator) $T))
          ($epoch1 (typ:learned $E $ctx needed $T1 $a1))
          ($epoch2 (typ:learned $E $ctx needed $T $a2)))
     (if (== (conv:result $T1 $a1) (conv:result $T $a2))
         (typ:from-value $E $ctx $t $T $a2 (typ:to-value $E $ctx $t $T1 $a1 $thm))
         (typ:retype-inside $E $ctx $t $T1 $T $thm))))
; The two types as values also inside their binders (a proposition that
; quantifies, a function type): equal there, they are the same type.
(= (typ:retype-inside $E $ctx $t $T1 $T $thm)
   (let* (($s1 (conv:run $E $ctx (Cv.strong (lean:evaluator)) $T1))
          ($s2 (conv:run $E $ctx (Cv.strong (lean:evaluator)) $T)))
     (if (== (conv:result $T1 $s1) (conv:result $T $s2))
         (typ:from-value $E $ctx $t $T $s2 (typ:to-value $E $ctx $t $T1 $s1 $thm))
         (let $checked (collapse (mg:exact (eq:theory $E) $ctx (typ:member $t $T) $thm))
           (if (== $checked ()) None (car-atom $checked))))))
; t :e T1 and T1 = N give t :e N;  t :e N and T = N give t :e T.
(= (typ:to-value $E $ctx $t $T1 $a1 $thm)
   (case $a1
     ((Same $thm)
      ((Conv $N $e) (eq:mp $E $ctx (typ:in-type $t) $N $T1 (eq:sym $E $ctx $T1 $N $e) $thm)))))
(= (typ:from-value $E $ctx $t $T $a2 $thm)
   (case $a2
     ((Same $thm)
      ((Conv $N $e) (eq:mp $E $ctx (typ:in-type $t) $T $N $e $thm)))))
(= (typ:in-type $t) (Tm.lam (Tp.base 0) (typ:member (mgt:shift $t 1 0) (Tm.db 0))))
(= (typ:of-type $T) (Tm.lam (Tp.base 0) (typ:member (Tm.db 0) (mgt:shift $T 1 0))))
(= (typ:origins $E $ctx $v) (conv:origins $E $ctx $v))
(= (typ:by-origin $E $ctx $path $v $T $origins)
   (if (== $origins ()) None
       (let $found (typ:from-origin $E $ctx $path $v $T (car-atom $origins))
         (if (== $found None) (typ:by-origin $E $ctx $path $v $T (cdr-atom $origins)) $found))))
(= (typ:from-origin $E $ctx $path $v $T (Origin $s $thm))
   (let $typed (typ:prove $E $ctx $path (typ:member $s $T))
     (if (== $typed None) None
         (eq:mp $E $ctx (typ:of-type $T) $v $s (eq:sym $E $ctx $s $v $thm) $typed))))
; nat_p of a numeral written with ordsucc, by its own structure.
(= (typ:natural $E $ctx $path $n $q)
   (case $n
     (((Tm.app (Tm.named $s) $m)
       (if (== $s (lean:id "ordsucc"))
           (let $inner (typ:prove $E $ctx $path (Tm.app (Tm.named (lean:id "nat_p")) $m))
             (if (== $inner None) None
                 (case (mg:try-proof-app (mg:term-app (mg:known-in (eq:theory $E) $ctx (lean:id "nat_ordsucc")) $m) $inner)
                   (((Error $call $why) None) ($thm $thm)))))
           (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q)))
      ($other (typ:try $E $ctx $path (typ:declared (typ:key $q)) $q)))))
(= (typ:try $E $ctx $path $names $q)
   (if (== $names ()) None
       (let $found (typ:lemma $E $ctx $path (car-atom $names) $q)
         (if (== $found None) (typ:try $E $ctx $path (cdr-atom $names) $q) $found))))
; A lemma whose conclusion matches the goal, its premises proved in turn.
(= (typ:lemma $E $ctx $path $name $q)
   (let* (($known (mg:known-in (eq:theory $E) $ctx $name))
          ($statement (mg:proposition $known))
          ($shape (rule:conclusion $statement 0)))
     (case $shape
       (((Concludes $n $conclusion)
         (let $binds (mgt:match (mgt:eta $conclusion) $q $n 0 ())
           (if (== $binds fail) (typ:lemma-viewed $E $ctx $path $name (mgt:eta $conclusion) $q)
               (case (rule:instantiate $E $ctx (Prover.lean-below $path) (wire:literal 0) $known $statement 0 $binds)
                 (((Instance $thm $stated)
                   (let $checked (collapse (mg:exact (eq:theory $E) $ctx $q $thm))
                     (if (== $checked ()) None (car-atom $checked))))
                  ($other None))))))))))
; A lemma is matched as a rule is: as the goal stands, then after a view.
; Where the lemma's conclusion asks for a constructor and the goal has a
; numeral there (succ b against 95), the numeral is seen as that constructor
; (95 = succ 94), the lemma proves the goal so written, and the view carries
; the proof back to the goal as it stood.  This is for a goal that speaks of
; a variable of the context (succ x <= 95).  A fact about numerals alone is
; decided by computing: its decision is computed and taken apart, and where
; it is false no lemma is tried on it.
(= (typ:lemma-viewed $E $ctx $path $name $pattern $q)
   (if (typ:about-a-variable $ctx $q)
       (case (mgt:mismatch $pattern $q ())
         (((At $at)
           (let $part (mgt:subterm $q $at)
             (case (conv:run $E $ctx (Cv.lean-view (Prover.lean)) $part)
               (((Conv $seen $view)
                 (let $proved (typ:lemma $E $ctx $path $name (mgt:replace $q $at $seen))
                   (if (== $proved None) None
                       (eq:mp $E $ctx (mgt:context $q $at) $part $seen $view $proved))))
                ($other None)))))
          ($other None)))
       None))
(= (typ:about-a-variable (Megalodon.context $depth $types $hypotheses) $q)
   (typ:mentions-upto $q (- (mgt:count (cdr-atom $types)) 1)))

; f x :e T for a set f: the type of f, a function space, gives the type of f x.
(= (typ:applied $E $ctx $path $f $x $q)
   (case (typ:apply-typed $E $ctx $path $f $x)
     (((Typed $T $thm)
       (let $checked (collapse (mg:exact (eq:theory $E) $ctx $q $thm))
         (if (== $checked ()) None (car-atom $checked))))
      ($other None))))
(= (typ:apply-typed $E $ctx $path $f $x)
   (case (typ:infer $E $ctx $path $f)
     (((Typed $Tf $thm-f)
       (case (typ:pi-parts $Tf)
         (((PiOf $X $Y)
           (let $thm-x (typ:prove $E $ctx $path (typ:member $x $X))
             (if (== $thm-x None) None
                 (let $ap-pi (mg:known-in (eq:theory $E) $ctx (lean:id "ap_Pi"))
                   (case (mg:try-proof-app
                           (mg:term-app (mg:term-app (mg:term-app (mg:term-app $ap-pi $X) $Y) $f) $x) $thm-f)
                     (((Error $call $why) None)
                      ($step (case (mg:try-proof-app $step $thm-x)
                               (((Error $call2 $why2) None)
                                ($thm (Typed (mgt:beta (Tm.app $Y $x)) $thm)))))))))))
          ($other None))))
      ($other None))))

; The type of a term, computed: (Typed TYPE THEOREM) or None.
(= (typ:infer $E $ctx $path $t)
   (case $t
     (((Tm.db $i) (typ:infer-variable $E $ctx $t (mg:hypotheses $ctx) 0))
      ($other (typ:infer-structural $E $ctx $path $t)))))
(= (typ:infer-structural $E $ctx $path $t)
   (case $t
     (((Tm.app (Tm.app (Tm.named $ap) $f) $x)
       (if (== $ap (lean:id "ap")) (typ:apply-typed $E $ctx $path $f $x)
           (if (== $ap (lean:id "Sigma")) (typ:infer-function $E $ctx $f $x)
               (typ:infer-head $E $ctx $path (typ:declared (mgt:head $t)) $t))))
      ($other (typ:infer-head $E $ctx $path (typ:declared (mgt:head $t)) $t)))))
; A function lam X F (written with Sigma, which lam is): its body, typed at a
; variable of X, gives the family Y of its result types, and lam_Pi gives
; lam X F :e Pi X Y.
(= (typ:infer-function $E $ctx $X $F)
   (case (mg:try-term-binder (eq:theory $E) $ctx (Tp.base 0))
     (((Error $c1 $w1) None)
      ($inner
       (let* (($hyp (typ:member (Tm.db 0) (mgt:shift $X 1 0)))
              ($body (mgt:beta (Tm.app (mgt:shift $F 1 0) (Tm.db 0)))))
         (case (mg:try-proof-binder (eq:theory $E) $inner $hyp)
           (((Error $c2 $w2) None)
            ($inner2
             (case (typ:infer $E $inner2 () $body)
               (((Typed $Tb $thm) (typ:close-function $E $ctx $X $F $hyp $Tb $thm))
                ($other None)))))))))))
(= (typ:close-function $E $ctx $X $F $hyp $Tb $thm)
   (case (mg:try-proof-lam-of $thm $hyp)
     (((Error $c3 $w3) None)
      ($closed1
       (case (mg:try-term-lam-at $closed1 (Tp.base 0))
         (((Error $c4 $w4) None)
          ($closed
           (let* (($Y (Tm.lam (Tp.base 0) $Tb))
                  ($lemma (mg:known-in (eq:theory $E) $ctx (lean:id "lam_Pi"))))
             (case (mg:try-proof-app (mg:term-app (mg:term-app (mg:term-app $lemma $X) $Y) $F) $closed)
               (((Error $c5 $w5) None)
                ($typed (Typed (Tm.app (Tm.app (Tm.named (lean:id "Pi")) $X) $Y) $typed))))))))))))
(= (typ:infer-variable $E $ctx $t $hyps $index)
   (if (== $hyps ()) None
       (case (typ:parts (car-atom $hyps))
         (((Member $s $T)
           (if (== $s $t) (Typed $T (mg:hyp (eq:theory $E) $ctx $index))
               (typ:infer-variable $E $ctx $t (cdr-atom $hyps) (+ $index 1))))
          ($other (typ:infer-variable $E $ctx $t (cdr-atom $hyps) (+ $index 1)))))))
(= (typ:infer-head $E $ctx $path $names $t)
   (if (== $names ()) None
       (let $found (if (typ:checks-only (car-atom $names)) None (typ:infer-lemma $E $ctx $path (car-atom $names) $t))
         (if (== $found None) (typ:infer-head $E $ctx $path (cdr-atom $names) $t) $found))))
; An inferred type is read by the rules that follow (a proposition's is LeanProp), so it
; is given in normal form.  A lemma whose type is a level still to be computed
; (Sort (imax u v)) proves a goal so stated, and is no rule of inference (TypChecksOnly).
(= (typ:checks-only $co_name) (not (== (collapse (match &self (TypChecksOnly $co_name) yes)) ())))
(= (typ:infer-lemma $E $ctx $path $name $t)
   (let* (($known (mg:known-in (eq:theory $E) $ctx $name))
          ($statement (mg:proposition $known))
          ($shape (rule:conclusion $statement 0)))
     (case $shape
       (((Concludes $n $conclusion)
         (case (typ:parts (mgt:eta $conclusion))
           (((Member $pattern $T)
             (let $binds (mgt:match $pattern $t $n 0 ())
               (if (== $binds fail) None
                   (case (rule:instantiate $E $ctx (Prover.lean-below $path) (wire:literal 0) $known $statement 0 $binds)
                     (((Instance $thm $stated)
                       (case (typ:parts (mgt:beta $stated))
                         (((Member $s $type) (Typed $type $thm))
                          ($other None))))
                      ($other None))))))
            ($other None))))))))
(= (typ:atomic-traced $E $ctx $path $q)
   (let $r (typ:atomic $E $ctx $path $q)
     (if (== $r None) (let $shown (println! (unproved (lean:text $q))) None) $r)))

; A proposition named by a definition that no lemma speaks of is looked at
; as the definition's body: the two are one set, and the kernel converts
; them, so the theorem found for the body is the theorem for the name.
(= (typ:by-definition $E $ctx $path $zero $T $q)
   (let $unfolded (typ:unfold-head $T)
     (if (== $unfolded None) None
         (let $proved (typ:prove $E $ctx $path (typ:member $zero $unfolded))
           (if (== $proved None) None
               (let $restated (collapse (mg:exact (eq:theory $E) $ctx $q $proved))
                 (if (== $restated ()) None (car-atom $restated))))))))
(= (typ:unfold-head $T)
   (case (mgt:head $T)
     (((Tm.named $d)
       (let $found (collapse (mg:declaration (lean:theory) $d))
         (if (== $found ()) None
             (let $decl (car-atom $found)
               (if (== (car-atom $decl) Megalodon.definition)
                   (mgt:beta (typ:apply-all (mgt:nth $decl 3) (mgt:spine-args $T)))
                   None)))))
      ($other None))))
(= (typ:apply-all $f $args)
   (if (== $args ()) $f (typ:apply-all (Tm.app $f (car-atom $args)) (cdr-atom $args))))
