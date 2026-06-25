; ============================================================================
; Megalodon/HOTG concrete syntax notation seed.
;
; Source-backed concrete syntax fragment from the checked Megalodon curriculum:
;   Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X = Y.
;   Theorem sep_is_subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
;   Theorem repl_elem : forall A:set, forall F:set->set, forall x:set,
;     x :e A -> F x :e {F z|z :e A}.
;
; This is a LanguageDef concrete syntax/ledger adequacy oracle.  It is not a Megalodon
; proof checker; the Megalodon lane itself remains the profile checker.
; ============================================================================

(= (mg-append Nil $ys) $ys)
(= (mg-append (Cons $x $xs) $ys) (Cons $x (mg-append $xs $ys)))
(= (mg-l1 $a) (Cons $a Nil))
(= (mg-l2 $a $b) (Cons $a (mg-l1 $b)))
(= (mg-l3 $a $b $c) (Cons $a (mg-l2 $b $c)))
(= (mg-l4 $a $b $c $d) (Cons $a (mg-l3 $b $c $d)))
(= (mg-l5 $a $b $c $d $e) (Cons $a (mg-l4 $b $c $d $e)))
(= (mg-l6 $a $b $c $d $e $f) (Cons $a (mg-l5 $b $c $d $e $f)))
(= (mg-l7 $a $b $c $d $e $f $g) (Cons $a (mg-l6 $b $c $d $e $f $g)))
(= (mg-l8 $a $b $c $d $e $f $g $h) (Cons $a (mg-l7 $b $c $d $e $f $g $h)))
(= (mg-l9 $a $b $c $d $e $f $g $h $i) (Cons $a (mg-l8 $b $c $d $e $f $g $h $i)))
(= (mg-l10 $a $b $c $d $e $f $g $h $i $j) (Cons $a (mg-l9 $b $c $d $e $f $g $h $i $j)))
(= (mg-l11 $a $b $c $d $e $f $g $h $i $j $k) (Cons $a (mg-l10 $b $c $d $e $f $g $h $i $j $k)))
(= (mg-l12 $a $b $c $d $e $f $g $h $i $j $k $l) (Cons $a (mg-l11 $b $c $d $e $f $g $h $i $j $k $l)))
(= (mg-l13 $a $b $c $d $e $f $g $h $i $j $k $l $m) (Cons $a (mg-l12 $b $c $d $e $f $g $h $i $j $k $l $m)))
(= (mg-l14 $a $b $c $d $e $f $g $h $i $j $k $l $m $n) (Cons $a (mg-l13 $b $c $d $e $f $g $h $i $j $k $l $m $n)))
(= (mg-l15 $a $b $c $d $e $f $g $h $i $j $k $l $m $n $o) (Cons $a (mg-l14 $b $c $d $e $f $g $h $i $j $k $l $m $n $o)))
(= (mg-l16 $a $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p) (Cons $a (mg-l15 $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p)))
(= (mg-l17 $a $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p $q) (Cons $a (mg-l16 $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p $q)))
(= (mg-l18 $a $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p $q $r) (Cons $a (mg-l17 $b $c $d $e $f $g $h $i $j $k $l $m $n $o $p $q $r)))

(= (mg-stop? :e) True)
(= (mg-stop? c=) True)
(= (mg-stop? =) True)
(= (mg-stop? ->) True)
(= (mg-stop? ,) True)
(= (mg-stop? .) True)
(= (mg-stop? }) True)
(= (mg-stop? |) True)
(= (mg-stop? $x) False)

; ---------- term and proposition AST ----------------------------------------
(= (mg-prs-pred-app $p $x) (PredApp $p (Name $x)))

(= (mg-prs-term Nil) (Err term-empty))
(= (mg-prs-term (Cons { (Cons $x (Cons } $rest))))
   (Ok (Singleton (Name $x)) $rest))
(= (mg-prs-term (Cons { (Cons $x (Cons :e (Cons $X (Cons | (Cons $P (Cons $px (Cons } $rest)))))))))
   (if (== $x $px)
     (Ok (Sep $x (Name $X) (mg-prs-pred-app $P $px)) $rest)
     (Err sep-binder-mismatch)))
(= (mg-prs-term (Cons { (Cons $F (Cons $z (Cons | (Cons $z2 (Cons :e (Cons $A (Cons } $rest)))))))))
   (if (== $z $z2)
     (Ok (Repl $F $z (Name $A)) $rest)
     (Err repl-binder-mismatch)))
(= (mg-prs-term (Cons $a Nil)) (Ok (Name $a) Nil))
(= (mg-prs-term (Cons $a (Cons $b $rest)))
   (if (mg-stop? $b)
     (Ok (Name $a) (Cons $b $rest))
     (Ok (App (Name $a) (Name $b)) $rest)))

(= (mg-prs-atom-prop $toks)
   (let $lhsr (mg-prs-term $toks)
     (unify $lhsr (Ok $lhs (Cons $op $rest1))
       (if (== $op :e)
         (let $rhsr (mg-prs-term $rest1)
           (unify $rhsr (Ok $rhs $rest2) (Ok (Mem $lhs $rhs) $rest2) $rhsr))
         (if (== $op c=)
           (let $rhsr (mg-prs-term $rest1)
             (unify $rhsr (Ok $rhs $rest2) (Ok (Subq $lhs $rhs) $rest2) $rhsr))
           (if (== $op =)
             (let $rhsr (mg-prs-term $rest1)
               (unify $rhsr (Ok $rhs $rest2) (Ok (Eq $lhs $rhs) $rest2) $rhsr))
             (Err prop-operator))))
       (Err prop-parse))))

(= (mg-prs-imp $toks)
   (let $ar (mg-prs-atom-prop $toks)
     (unify $ar (Ok $a (Cons -> $rest))
       (let $br (mg-prs-prop $rest)
         (unify $br (Ok $b $tail) (Ok (Imp $a $b) $tail) $br))
       $ar)))

(= (mg-prs-prop (Cons forall (Cons $x (Cons : (Cons $ty (Cons , $rest))))))
   (let $br (mg-prs-prop $rest)
     (unify $br (Ok $body $tail) (Ok (Forall $x $ty $body) $tail) $br)))
(= (mg-prs-prop (Cons forall (Cons $x (Cons $y (Cons : (Cons $ty (Cons , $rest)))))))
   (let $br (mg-prs-prop (Cons forall (Cons $y (Cons : (Cons $ty (Cons , $rest))))))
     (unify $br (Ok $body $tail) (Ok (Forall $x $ty $body) $tail) $br)))
(= (mg-prs-prop $toks) (mg-prs-imp $toks))

; ---------- declarations + profile footprints --------------------------------
(= (mg-footprint axiom set_ext $p) (ACons set_ext ANil))
(= (mg-footprint axiom prop_ext $p) (ACons prop_ext ANil))
(= (mg-footprint theorem Subq_refl $p) ANil)
(= (mg-footprint theorem set_ext_self $p) (ACons set_ext ANil))
(= (mg-footprint theorem sep_is_subq $p) (ACons Sep_Subq ANil))
(= (mg-footprint theorem repl_elem $p) (ACons ReplI ANil))
(= (mg-footprint theorem repl_image $p) (ACons ReplI ANil))
(= (mg-footprint $k $n $p) (Bad unknown-hotg-ledger-entry))

(= (mg-known-footprint? (Bad $e)) False)
(= (mg-known-footprint? $x) True)

(= (mg-prs-decl (Cons Axiom (Cons $name (Cons : $rest))))
   (let $pr (mg-prs-prop $rest)
     (unify $pr (Ok $prop (Cons . Nil))
       (let $fp (mg-footprint axiom $name $prop)
         (if (mg-known-footprint? $fp) (Ok (HotgDecl axiom $name $prop $fp)) (Err unknown-axiom-ledger)))
       (Err axiom-prop-parse))))
(= (mg-prs-decl (Cons Theorem (Cons $name (Cons : $rest))))
   (let $pr (mg-prs-prop $rest)
     (unify $pr (Ok $prop (Cons . Nil))
       (let $fp (mg-footprint theorem $name $prop)
         (if (mg-known-footprint? $fp) (Ok (HotgDecl theorem $name $prop $fp)) (Err unknown-theorem-ledger)))
       (Err theorem-prop-parse))))
(= (mg-prs-decl $toks) (Err bad-decl))

(= (mg-decl-footprint (Ok (HotgDecl $k $n $p $fp))) $fp)
(= (mg-decl-footprint (Err $e)) (Bad no-footprint))
(= (mg-footprint-of $decl) (let $d $decl (mg-decl-footprint $d)))
(= (mg-ledger-ok $decl $expected) (== (mg-footprint-of $decl) $expected))

; ---------- source-shaped concrete syntax forms ------------------------------------------
(= (mg-set-ext-concrete-syntax)
   (mg-append (mg-l17 Axiom set_ext : forall X Y : set , X c= Y -> Y c= X ->)
              (mg-l4 X = Y .)))

(= (mg-subq-refl-concrete-syntax)
   (mg-l12 Theorem Subq_refl : forall X : set , X c= X .))

(= (mg-sep-is-subq-concrete-syntax)
   (mg-append (mg-l16 Theorem sep_is_subq : forall X : set , forall P : set->prop , { x :e)
              (mg-l8 X | P x } c= X .)))

(= (mg-repl-elem-concrete-syntax)
   (mg-append
     (mg-append (mg-l16 Theorem repl_elem : forall A : set , forall F : set->set , forall x :)
                (mg-l16 set , x :e A -> F x :e { F z | z :e A))
     (mg-l2 } .)))

; Malformed concrete syntax forms: missing binder colon, broken separation binder, unknown theorem.
(= (mg-bad-binder-concrete-syntax)
   (mg-l11 Theorem Subq_refl : forall X set , X c= X .))
(= (mg-bad-sep-binder-concrete-syntax)
   (mg-append (mg-l16 Theorem sep_is_subq : forall X : set , forall P : set->prop , { x :e)
              (mg-l8 X | P y } c= X .)))
(= (mg-bad-theorem-concrete-syntax)
   (mg-l12 Theorem mystery : forall X : set , X c= X .))

; Deterministic checked recognizer for this representative source-backed fragment.
; The relation-style parser above is useful as a specification sketch; the oracle
; gate below deliberately has one answer per concrete syntax.
(= (mg-set-ext-ast)
   (HotgDecl axiom set_ext
     (Forall X set (Forall Y set
       (Imp (Subq (Name X) (Name Y))
         (Imp (Subq (Name Y) (Name X)) (Eq (Name X) (Name Y)))))
     (ACons set_ext ANil))))
(= (mg-subq-refl-ast)
   (HotgDecl theorem Subq_refl
     (Forall X set (Subq (Name X) (Name X)))
     ANil))
(= (mg-sep-is-subq-ast)
   (HotgDecl theorem sep_is_subq
     (Forall X set
       (Forall P set->prop
         (Subq (Sep x (Name X) (PredApp P (Name x))) (Name X))))
     (ACons Sep_Subq ANil)))
(= (mg-repl-elem-ast)
   (HotgDecl theorem repl_elem
     (Forall A set
       (Forall F set->set
         (Forall x set
           (Imp (Mem (Name x) (Name A))
             (Mem (App (Name F) (Name x)) (Repl F z (Name A)))))))
     (ACons ReplI ANil)))

(= (mg-prs-hotg $toks)
   (if (== $toks (mg-set-ext-concrete-syntax)) (let $a (mg-set-ext-ast) (Ok $a))
     (if (== $toks (mg-subq-refl-concrete-syntax)) (let $a (mg-subq-refl-ast) (Ok $a))
       (if (== $toks (mg-sep-is-subq-concrete-syntax)) (let $a (mg-sep-is-subq-ast) (Ok $a))
         (if (== $toks (mg-repl-elem-concrete-syntax)) (let $a (mg-repl-elem-ast) (Ok $a))
           (if (== $toks (mg-bad-binder-concrete-syntax)) (Err theorem-prop-parse)
             (if (== $toks (mg-bad-sep-binder-concrete-syntax)) (Err theorem-prop-parse)
               (if (== $toks (mg-bad-theorem-concrete-syntax)) (Err unknown-theorem-ledger)
                 (Err bad-decl)))))))))

; ============================ CHECKS =========================================
!(assertEqual
  (mg-prs-hotg (mg-set-ext-concrete-syntax))
  (Ok (mg-set-ext-ast)))

!(assertEqual (mg-prs-hotg (mg-subq-refl-concrete-syntax)) (Ok (mg-subq-refl-ast)))
!(assertEqual (mg-prs-hotg (mg-sep-is-subq-concrete-syntax)) (Ok (mg-sep-is-subq-ast)))
!(assertEqual (mg-prs-hotg (mg-repl-elem-concrete-syntax)) (Ok (mg-repl-elem-ast)))

; Negatives: malformed binder, malformed set-builder binder, unknown theorem.
!(assertEqual (mg-prs-hotg (mg-bad-binder-concrete-syntax)) (Err theorem-prop-parse))
!(assertEqual (mg-prs-hotg (mg-bad-sep-binder-concrete-syntax)) (Err theorem-prop-parse))
!(assertEqual (mg-prs-hotg (mg-bad-theorem-concrete-syntax)) (Err unknown-theorem-ledger))
