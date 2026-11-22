; The rules and typing lemmas of the reading, taken from the checked document.
;
; The document is the library.  A theorem the reader generated as a way to
; compute (an equation theorem F_eq_K, a recursor or case equation X_iotaK or X_miotaK,
; a projection of a constructor P_mk, an application F_ap, an unfolding
; F_unfold) is a rule of the set "lean".  A function that Lean defines by
; well-founded recursion is read by fuel, and the libraries prove Lean's own
; equations for it (X_equation, X_equation_K): those are declared before all
; others, so that such a function is computed by its equations and its
; definition by fuel is not unfolded; a theorem that types a head (F_In,
; C_typed, T_type_In, X_Prop_prop), or says that a proposition holds (a
; constructor of it, C_proof_ok; a proof Lean cites, X_proof), is a typing
; lemma.  Only the reading's own
; theorems (Lean_...) are classed: the class is read from the name, the
; rule's shape from the statement.
;
;   (rules:open E)   the fixed rules, the numerals, then every rule and lemma
;                    of the open session's theory; (Loaded COMPUTE TYPING
;                    REFUSED) for the last

(= (rules:strip-digits $s)
   (let $n (str:byte-length $s)
     (if (== $n 0) $s
         (if (str:is-all-in digit (str:byte-slice $s (- $n 1) $n))
             (rules:strip-digits (str:byte-slice $s 0 (- $n 1))) $s))))
(= (rules:ends-any $s $suffixes)
   (if (== $suffixes ()) False
       (if (str:ends-with $s (car-atom $suffixes)) True (rules:ends-any $s (cdr-atom $suffixes)))))
; compute, typing or none
(= (rules:class $source)
   (if (not (str:starts-with $source "Lean")) none (rules:class-by-suffix $source)))
(= (rules:class-by-suffix $source)
   (if (rules:equation-name $source) equation (rules:class-by-kind $source)))
(= (rules:equation-name $source)
   (if (str:ends-with $source "_equation") True (str:ends-with (rules:strip-digits $source) "_equation_")))
; A typing lemma, or a theorem that a proposition holds: a constructor of a
; proposition (C_proof_ok), a proof that Lean cites (X_proof, X_proof_K).  A
; recursor of a proposition read as Lean states it (F_rec_proof_ok) is not
; one: its conclusion is its motive's, so no goal names it; the transport
; follower cites it where Lean's proof applies the recursor.
(= (rules:typing-name $source)
   (if (str:ends-with $source "_rec_proof_ok") False
       (if (rules:ends-any $source ("_In" "_typed" "_Prop_prop" "_PropPacked_prop" "_proof_ok" "_proof")) True
           (str:ends-with (rules:strip-digits $source) "_proof_"))))
(= (rules:class-by-kind $source)
   (if (rules:typing-name $source) typing
       (if (rules:ends-any $source ("_mk" "_ap" "_unfold")) compute
           (let $stem (rules:strip-digits $source)
             (if (== $stem $source) none
                 (if (rules:ends-any $stem ("_eq_" "_iota" "_miota")) compute none))))))
(= (rules:names $items)
   (if (== $items ()) ()
       (case (car-atom $items)
         (((source $name) (let $rest (rules:names (cdr-atom $items)) (cons-atom $name $rest)))
          ((also $a) (let $rest (rules:names (cdr-atom $items)) (cons-atom $a $rest)))
          ((also $a $b) (let $rest (rules:names (cdr-atom $items)) (cons-atom $a (cons-atom $b $rest))))
          ($other (rules:names (cdr-atom $items)))))))
(= (rules:class-of-names $names)
   (if (== $names ()) none
       (let $c (rules:class (car-atom $names)) (if (== $c none) (rules:class-of-names (cdr-atom $names)) $c))))
; What the document proves about a family and its constructors, kept for
; the inversion of typing: (FamilyInd F ID), (CtorTyped C ID),
; (CtorInj C K ID) for the argument at position K, (CtorDistinct C1 C2 ID).
(= (rules:final-premise $p $last)
   (case $p
     (((Tm.all $A $b) (rules:final-premise $b $last))
      ((Tm.imp $q $r) (rules:final-premise $r $q))
      ($other $last))))
(= (rules:family-facts $E $id $names)
   (if (== $names ()) none
       (let $made (rules:family-fact $E $id (car-atom $names))
         (if (== $made none) (rules:family-facts $E $id (cdr-atom $names)) $made))))
(= (rules:family-fact $E $id $source)
   (if (not (str:starts-with $source "Lean")) none
       (if (str:ends-with $source "_ind") (rules:ind-fact $E $id)
           (if (str:ends-with $source "_typed") (rules:typed-fact $E $id)
               (let $stem (rules:strip-digits $source)
                 (if (== $stem $source) none
                     (if (str:ends-with $stem "_inj") (rules:inj-fact $E $id)
                         (if (rules:noconf-p $stem) (rules:distinct-fact $E $id) none))))))))
(= (rules:noconf-p $stem)
   (if (str:ends-with $stem "_")
       (str:ends-with (rules:strip-digits (str:byte-slice $stem 0 (- (str:byte-length $stem) 1))) "_noconf")
       False))
(= (rules:ind-fact $E $id)
   (case (typ:parts (rules:final-premise (mg:proposition (mg:known (eq:theory $E) $id)) None))
     (((Member $d $T) (let* (($F (mgt:head $T)) ($done (add-atom &self (FamilyInd $F $id)))) ind))
      ($other none))))
(= (rules:typed-fact $E $id)
   (case (rule:conclusion (mg:proposition (mg:known (eq:theory $E) $id)) 0)
     (((Concludes $n $c)
       (case (typ:parts $c)
         (((Member $t $T) (let* (($ctor (mgt:head $t)) ($done (add-atom &self (CtorTyped $ctor $id)))) typed))
          ($other none))))
      ($other none))))
(= (rules:inj-fact $E $id)
   (let $p (mg:proposition (mg:known (eq:theory $E) $id))
     (case (eq:sides $E (rules:final-premise $p None))
       (((Sides $a $b)
         (case (rule:conclusion $p 0)
           (((Concludes $n $c)
             (case (eq:sides $E $c)
               (((Sides $x $y)
                 (let $k (mgt:position $x (mgt:spine-args $a) 0)
                   (if (== $k None) none
                       (let* (($ctor (mgt:head $a)) ($done (add-atom &self (CtorInj $ctor $k $id)))) inj))))
                ($other none))))
            ($other none))))
        ($other none)))))
(= (rules:distinct-fact $E $id)
   (case (rule:conclusion (mg:proposition (mg:known (eq:theory $E) $id)) 0)
     (((Concludes $n (Tm.app (Tm.app $neq $a) $b))
       (let* (($c1 (mgt:head $a)) ($c2 (mgt:head $b)) ($done (add-atom &self (CtorDistinct $c1 $c2 $id)))) distinct))
      ($other none))))

; (Loaded COMPUTE TYPING REFUSED): how many of each class were declared, and
; the names that were not: of the class compute and not concluding with an
; equation, or of the class typing and not about a named head.
(= (rules:declare-one $E $pass $declaration $sum)
   (let* (($kind (car-atom $declaration)) ($id (car-atom (cdr-atom $declaration))))
     (if (or (== $kind Megalodon.theorem) (== $kind Megalodon.axiom))
         (let $names (rules:names (cdr-atom $declaration))
           (if (== $pass equations)
               (if (== (rules:class-of-names $names) equation) (rules:declare-rule $E $id $names $sum) $sum)
               (rules:declare-other $E $id $names $sum)))
         $sum)))
(= (rules:declare-rule $E $id $names $sum)
   (case (conv:declare $E (mg:empty-context) lean $id)
     (((Error $call $why) (rules:refused $sum (car-atom $names)))
      ($head (let $kept (add-atom &self (EquationHead $head)) (rules:counted $sum compute))))))
; The head of the left side of a known equation, or None.
(= (rules:left-head $E $id)
   (case (rule:conclusion (mg:proposition (mg:known (eq:theory $E) $id)) 0)
     (((Concludes $n $conclusion)
       (case (eq:sides $E $conclusion)
         (((Sides $left $right) (mgt:head (mgt:eta $left)))
          ($other None))))
      ($other None))))
; A function that has Lean's own equations is computed by them alone: the
; equations and the unfolding that the reader generated for its definition by
; fuel are set aside, (RuleSetAside NAME), so that an equation whose premise
; is not proved leaves the term undecided instead of unfolding the fuel.
(= (rules:has-equations $head)
   (not (== (collapse (match &self (EquationHead $head) yes)) ())))
; The reading defines a decision procedure it has no recursor shape for as
; the canonical decision of its type.  Unfolding that definition is no step
; of Lean's: it leaves the procedure for the truth of its proposition.  It is
; set aside too, and the procedure is computed by Lean's equations for it.
(= (rules:canonical-unfolding $E $id $names)
   (if (rules:any-ends $names "_unfold")
       (case (rule:conclusion (mg:proposition (mg:known (eq:theory $E) $id)) 0)
         (((Concludes $n $conclusion)
           (case (eq:sides $E $conclusion)
             (((Sides $left $right) (== (mgt:head $right) (Tm.named (lean:id "Lean_DecCanon"))))
              ($other False))))
          ($other False)))
       False))
(= (rules:any-ends $names $suffix)
   (if (== $names ()) False
       (if (str:ends-with (car-atom $names) $suffix) True (rules:any-ends (cdr-atom $names) $suffix))))
(= (rules:set-aside $E $id $names)
   (if (rules:has-equations (rules:left-head $E $id)) True (rules:canonical-unfolding $E $id $names)))
(= (rules:declare-other $E $id $names $sum)
         (let $family (rules:family-facts $E $id $names)
           (case (rules:class-of-names $names)
             ((compute (if (rules:set-aside $E $id $names)
                           (let* (($name (car-atom $names)) ($kept (add-atom &self (RuleSetAside $name)))) $sum)
                           (case (conv:declare $E (mg:empty-context) lean $id)
                             (((Error $call $why) (rules:refused $sum (car-atom $names)))
                              ($head (rules:counted $sum compute))))))
              (typing (let $companion (rules:position-companion $id (car-atom $names))
                        (if (== (typ:declare $id) Refused) (rules:refused $sum (car-atom $names)) (rules:counted $sum typing))))
              ($other $sum)))))
(= (rules:counted (Loaded $c $t $refused) $class)
   (if (== $class compute) (Loaded (+ $c 1) $t $refused) (Loaded $c (+ $t 1) $refused)))
(= (rules:refused (Loaded $c $t $refused) $name)
   (let $more (cons-atom $name $refused) (Loaded $c $t $more)))
(= (rules:declare-list $E $pass $declarations $sum)
   (if (== $declarations ()) $sum
       (let $next (rules:declare-one $E $pass (car-atom $declarations) $sum)
         (rules:declare-list $E $pass (cdr-atom $declarations) $next))))
(= (rules:load $E)
   (let* (($inventory (mg:inventory (lean:theory)))
          ($declarations (cdr-atom $inventory))
          ($first (rules:declare-list $E equations $declarations (Loaded 0 0 ()))))
     (rules:declare-list $E others $declarations $first)))

; The rules that are not the reader's theorems: beta, addition and
; multiplication on numerals (declared first, so that numerals are computed
; as numbers and not by Lean's recursion; the sums themselves are made by
; numerals.metta), what a sort is (Sort 0 the propositions, Sort (l+1) the
; universe l, so that a type is compared with a sort by computing it), the
; lift of a function to a quotient at a class (the proof that the function
; respects the relation is an argument like the others, and its premise is
; its typing: the step of the definition that wrote the lift keeps that proof
; as a fact, its companion; where it is not proved it stays an open goal),
; the two ways a canonical decision is taken apart (by
; the truth of its proposition, likewise open where not proved), and the
; typing lemmas of numerals and functions.  A product of a family and a
; function are binder forms: what is computed under their binder is carried
; out by the lemmas that families equal at every point give equal products
; and equal functions.
(= (rules:declare-names $E $set $sources)
   (if (== $sources ()) done
       (let $head (conv:declare $E (mg:empty-context) $set (lean:id (car-atom $sources)))
         (rules:declare-names $E $set (cdr-atom $sources)))))
(= (rules:type-names $sources)
   (if (== $sources ()) done
       (let $key (typ:declare (lean:id (car-atom $sources))) (rules:type-names (cdr-atom $sources)))))
; A product of propositions is a proposition.  The library states it of
; Power 1, which LeanProp is by definition; a typing lemma is found by what
; it is stated of, so it is stated here of LeanProp, proved by the library's.
(= (rules:product-of-propositions $E)
   (case (mg:try-known (eq:theory $E) "Lean_Pi_prop")
     (((Error $call $why)
       (let* (($in (Tm.named (lean:id "In"))) ($pi (Tm.named (lean:id "Pi"))) ($prop (Tm.named (lean:id "LeanProp")))
              ($claim (Tm.all (Tp.base 0) (Tm.all (Tp.arr (Tp.base 0) (Tp.base 0))
                        (Tm.imp (Tm.all (Tp.base 0) (Tm.imp (Tm.app (Tm.app $in (Tm.db 0)) (Tm.db 2))
                                                             (Tm.app (Tm.app $in (Tm.app (Tm.db 1) (Tm.db 0))) $prop)))
                                (Tm.app (Tm.app $in (Tm.app (Tm.app $pi (Tm.db 1)) (Tm.lam (Tp.base 0) (Tm.app (Tm.db 1) (Tm.db 0)))))
                                        $prop))))))
         (case (mg:prove-by (eq:theory $E) "Lean_Pi_prop" $claim (Tac.exact (mg:known (eq:theory $E) (lean:id "LeanPi_prop"))))
           (((Error $call2 $why2) (Error $call2 $why2))
            ($proved (typ:declare "Lean_Pi_prop"))))))
      ($known (typ:declare "Lean_Pi_prop")))))
; Lean's formation rule at a computed level: for checking, not for inference.
(= (rules:checks-only $cs_sources)
   (if (== $cs_sources ()) done
       (let* (($cs_id (lean:id (car-atom $cs_sources))) ($cs_kept (add-atom &self (TypChecksOnly $cs_id))))
         (rules:checks-only (cdr-atom $cs_sources)))))
(= (rules:fixed $E)
   (let* (($computing (rules:declare-names $E lean ("beta" "LeanNum_add" "LeanNum_mul" "LeanSort_0" "LeanSort_S"
                                                    "Lean_Quot_lift_beta_value" "Lean_DecCanon_rec_true" "Lean_DecCanon_rec_false")))
          ($typing (rules:type-names ("nat_0" "nat_ordsucc" "NumD_p" "LeanNum_In" "lam_Pi" "Lean_ProofField_intro"
                                       "LeanProp_In_LeanUniv" "LeanUniv_In_S" "LeanPi_LeanUniv"
                                       "LeanPi_LeanSort_max_In" "LeanPi_LeanSort_In")))
          ($product (rules:product-of-propositions $E))
          ($checking (rules:checks-only ("LeanPi_LeanSort_max_In" "LeanPi_LeanSort_In")))
          ($strict (rules:strict-names ("Lean_Nat_div" "Lean_Nat_mod" "Lean_Nat_sub" "Lean_Nat_decLe")))
          ($pi (conv:declare-binder (Tm.named (lean:id "Pi")) (lean:id "Pi_family_eq")))
          ($sigma (conv:declare-binder (Tm.named (lean:id "Sigma")) (lean:id "Sigma_family_eq")))
          ($applying (rules:declare-names $E lean-beta ("beta")))
          ($inside (conv:declare-inside lean lean-beta (rules:inside-functions))))
     done))
; A function that a recursion passes on to its next call is passed on as its
; value: beta is applied inside it first (megalodon_equations, Cv.eval-needed).
; Lean's decision for a bounded quantifier hands each level the predicate of
; the level above restricted to a smaller bound; computed as written, the
; predicate at depth d is d functions nested in one another and is applied
; through all of them, so deciding a quantifier below n costs about n * n / 2
; applications.  Passed on as its value it is one function at every depth.
(= (rules:inside-functions) (Cv.eval-needed lean-beta (Cv.rules lean-beta (Prover.lean) (wire:literal 0))))
; Functions computed between numerals by a lemma of the library
; (numerals.metta) take their arguments computed.
(= (rules:strict-names $sources)
   (if (== $sources ()) done
       (let* (($head (Tm.named (lean:id (car-atom $sources)))) ($kept (conv:declare-strict lean $head)))
         (rules:strict-names (cdr-atom $sources)))))
; A numeral LeanNum n is Lean's zero or successor, by LeanNum_0 and LeanNum_S:
; these are views, used where an equation of Lean asks for a constructor.
; The same two turned around are rules: a successor of a numeral, or zero,
; is a numeral again.
(= (rules:numerals $E)
   (let* (($z (eq:turned $E (lean:id "LeanNum_0") "LeanNum_0_turned"))
          ($s (eq:turned $E (lean:id "LeanNum_S") "LeanNum_S_turned"))
          ($a (conv:declare $E (mg:empty-context) lean "LeanNum_0_turned"))
          ($b (conv:declare $E (mg:empty-context) lean "LeanNum_S_turned"))
          ($c (conv:declare $E (mg:empty-context) lean-views (lean:id "LeanNum_0")))
          ($d (conv:declare $E (mg:empty-context) lean-views (lean:id "LeanNum_S"))))
     done))
(= (rules:open $E)
   (let* (($fixed (rules:fixed $E)) ($numerals (rules:numerals $E))) (rules:load $E)))

; The proof a definition makes at a place of an equation's right side is the
; reader's lemma eqn_proof_K, over the definition's arguments; the equation
; writes it as 0.  So the lemma is the equation's companion: where the
; equation applies, the lemma at the same arguments is a fact of the step
; (megalodon_equations, conv:declare-companion).
(= (rules:position-companion $id $source)
   (let $stem (rules:strip-digits $source)
     (if (== $stem $source) none
         (if (str:ends-with $stem "_proof_")
             (let $n (str:byte-length $stem)
               (conv:declare-companion (lean:id (str:byte-slice $stem 0 (- $n 7))) $id))
             none))))
