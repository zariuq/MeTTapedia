; Egal readings of Lean functions and computations.
;
; Input, besides the families (families.metta) and generate.metta's helpers:
;   the atoms of artifacts/lean-declarations/terms.metta:
;     (LeanFunction f (thm ..))  (LeanEquation thm (binder ..) type lhs rhs)
;     (LeanComputation i term type)  (EgalName name ident)
;     terms: (var x) | (num n) | (app c (arg ..)); binders: (type x level) | (term x type)
;   (CeTTaAnswer i (value)): the answer of test i on CeTTa.
;
; A function whose equations split one argument over the constructors of an
; admitted family, and recur only on recursive fields with the other
; arguments unchanged, is defined through the family's recursor; Lean's own
; equation theorems are then proved from the recursor's iota equations.  A
; function given by one equation without patterns is its right side.
; Anything else is refused with its reason.
;
; A computation is replayed by those equations, innermost first, and Nat.add
; on numerals by the reading of numerals (LeanNum_add_eq), as CeTTa computes
; it natively.  The theorem states that the term's reading equals the reading
; of CeTTa's answer, so a wrong answer is refused by the checkers.

; The text functions (str:...) are used from here on.
!(import! &self str)
!(import! &self fs)
!(import! &self system)

; ---- terms ----

; A name as text.  An argument list headed by a bare name would be read as
; a call when the name is a built-in function (id, not, ...).
(= (nm $x) (format-args "{}{}" ("" $x)))

(= (lookup-var $x $sub)
   (if (== $sub ()) $x
       (let ($k $v) (car-atom $sub) (if (== $k $x) $v (lookup-var $x (cdr-atom $sub))))))

(= (is-ctor $c) (if (== (ctor-owner $c) None) False True))

(= (is-family $c)
   (let $found (collapse (match &self (LeanAdmitted $c $cs) $c)) (if (== $found ()) (is-block $c) True)))

(= (library-head $c)
   (case $c
     (((EgalLibrary proof-field) "Lean_ProofField")
      ((EgalLibrary record-field $owner $i) (format-args "(Lean_RecordField {})" ($i)))
      ($_ None))))
(= (is-library-head $c) (not (== (library-head $c) None)))

(= (head-text $c)
   (if (is-library-head $c) (library-head $c)
   (if (is-subsingleton-rec $c) (subsingleton-name $c)
   (if (is-ctor $c) (format-args "{}_node" ((egal $c)))
       (if (prop-fam $c) (format-args "{}_Prop" ((egal $c))) (egal $c))))))
; The large eliminator of a subsingleton (Eq.rec at any sort): distinct from
; the family's own recursor over its proof nodes.
(= (subsingleton-name $f) (format-args "{}_elim" ((egal (rec-family $f)))))

; A term as Egal text, variables renamed by $sub.
(= (remove-key $x $sub)
   (if (== $sub ()) ()
       (let ($k $v) (car-atom $sub)
         (if (== $k $x) (remove-key $x (cdr-atom $sub)) (cons-atom ($k $v) (remove-key $x (cdr-atom $sub)))))))

(= (render $t $sub)
   (case $t
     (((var $x) (lookup-var $x $sub))
      ((num $k) (format-args "(LeanNum {})" ((num-arg $k))))
      ((prop) "LeanProp")
      ((proof) "0")
      ((canon $P) (format-args "(Lean_DecCanon {})" ((render $P $sub))))
      ((txt $s) $s)
      ((apv $f $args) (format-args "({} {})" ((render $f $sub) (join " " (render-all $args $sub)))))
      ((lam $x $T $b)
       (let $h (eta-head $x $b (remove-key $x $sub))
         (if (== $h None) (format-args "(fun {} :e {} => {})" ($x (render $T $sub) (render $b (remove-key $x $sub))))
             (format-args "(Sigma {} {})" ((render $T $sub) $h)))))
      ((arrow $A $B) (format-args "(Pi_ ux :e {}, {})" ((render $A $sub) (render $B $sub))))
      ((pi $x $A $B)
       (let $h (eta-head $x $B (remove-key $x $sub))
         (if (== $h None) (format-args "(Pi_ {} :e {}, {})" ($x (render $A $sub) (render $B (remove-key $x $sub))))
             (format-args "(Pi {} {})" ((render $A $sub) $h)))))
      ((app $c $args)
       (if (is-cases-on $c) (render-cases $c $args $sub)
       (if (== $args ()) (head-text $c)
           (format-args "({} {})" ((head-text $c) (join " " (render-all $args $sub)))))))
      ($_ (if (is-sort-term $t) (sort-or-render $t) $t)))))

; X.casesOn params motive major minors, for a family without indices or
; recursive fields, is X's recursor at the minors and the major.
(= (render-cases $c $args $sub)
   (if (has-cases-eliminator (cases-family $c)) (render-cases-elim $c $args $sub) (render-cases-rec $c $args $sub)))
; A family with recursive fields has its own case eliminator: the minors as
; they are, with no induction hypotheses.
(= (render-cases-elim $c $args $sub)
   (let* (($F (cases-family $c)) ($np (param-count $F))
          ($ps (take-n $args $np)) ($rest (drop-n $args (+ $np 1))))
     (format-args "({}_casesOn {})" ((egal $F) (join " " (render-all (append-lists $ps (append-lists (cdr-atom $rest) ((car-atom $rest)))) $sub))))))
(= (render-cases-rec $c $args $sub)
   (let* (($F (cases-family $c)) ($np (param-count $F))
          ($ps (take-n $args $np)) ($rest (drop-n $args (+ $np 1)))
          ($major (car-atom $rest))
          ($minors (wrap-minors $F $ps (motive-of (nth $args $np)) (cdr-atom $rest) 0)))
     (format-args "({}_rec {})" ((egal $F) (join " " (render-all (append-lists $ps (append-lists $minors ($major))) $sub))))))

(= (render-all $ts $sub)
   (if (== $ts ()) () (cons-atom (render (car-atom $ts) $sub) (render-all (cdr-atom $ts) $sub))))

; ---- the checkers' normal form ----
; Both checkers keep a proved statement beta-eta normal, but a goal and a
; tactic's terms as written; a rewrite then replaces only the copies written
; like its instantiated pattern.  So every term is written eta-normal: a
; binder whose body applies something to the bound variable alone, last,
; is that something (fun c :e A => f t c is Sigma A (f t)).  None when the
; body is not of that form.
(= (eta-head $x $b $sub)
   (case $b
     (((apv $f $args)
       (if (eta-tail $x $args (cons-atom $f (init-list $args)))
           (let $init (init-list $args)
             (if (== $init ()) (format-args "(ap {})" ((render $f $sub)))
                 (format-args "(ap {})" ((render (apv $f $init) $sub)))))
           None))
      ((app $c $args)
       (if (== $args ()) None
       (if (is-cases-on $c) (eta-cases $x $c $args $sub)
       (if (eta-tail $x $args (init-list $args))
           (let $init (init-list $args)
             (if (if (is-function $c) (> (length-of $args) (arity-of $c)) False)
                 (format-args "(ap {})" ((render (app $c $init) $sub)))
                 (if (== $init ()) (head-text $c) (render (app $c $init) $sub))))
           None))))
      ($_ None))))
(= (eta-tail $x $args $rest)
   (if (== (last-of $args) (var $x)) (not (any-occurs $x $rest)) False))
; X.casesOn writes its major last.
(= (eta-cases $x $c $args $sub)
   (let $i (+ (param-count (cases-family $c)) 1)
     (if (> (length-of $args) $i)
         (if (== (nth $args $i) (var $x))
             (if (any-occurs $x (remove-nth $args $i)) None (strip-last-arg (render (app $c $args) $sub) $x))
             None)
         None)))
(= (strip-last-arg $t $x)
   (let* (($suf (format-args " {})" ($x))) ($n (str:byte-length $t)) ($m (str:byte-length $suf)))
     (if (> $n $m)
         (if (== (str:byte-slice $t (- $n $m) $n) $suf)
             (let $inner (str:byte-slice $t 1 (- $n $m))
               (case (str:find $inner " ") (((TextNotFound $_) $inner) ($_ (format-args "({})" ($inner))))))
             None)
         None)))
(= (init-list $xs) (if (== (cdr-atom $xs) ()) () (cons-atom (car-atom $xs) (init-list (cdr-atom $xs)))))
(= (remove-nth $xs $i)
   (if (== $i 0) (cdr-atom $xs) (cons-atom (car-atom $xs) (remove-nth (cdr-atom $xs) (- $i 1)))))
(= (occurs-free $y $t)
   (case $t
     (((var $x) (== $x $y))
      ((app $c $args) (any-occurs $y $args))
      ((apv $f $args) (if (occurs-free $y $f) True (any-occurs $y $args)))
      ((lam $x $T $b) (if (occurs-free $y $T) True (if (== $x $y) False (occurs-free $y $b))))
      ((pi $x $A $B) (if (occurs-free $y $A) True (if (== $x $y) False (occurs-free $y $B))))
      ((arrow $A $B) (if (occurs-free $y $A) True (occurs-free $y $B)))
      ((canon $P) (occurs-free $y $P))
      ($_ False))))
(= (any-occurs $y $ts) (if (== $ts ()) False (if (occurs-free $y (car-atom $ts)) True (any-occurs $y (cdr-atom $ts)))))
; A meta-level function fun x => b, in the same normal form.
(= (meta-fun-text $x $b $sub)
   (let $h (eta-head $x $b (remove-key $x $sub))
     (if (== $h None) (format-args "(fun {} => {})" ($x (render $b (remove-key $x $sub)))) $h)))

; Substitution of terms for variables.
(= (fsubst $t $bind)
   (case $t
     (((var $x) (lookup-var-term $x $bind $t))
      ((num $k) $t)
      ((prop) $t)
      ((proof) $t)
      ((canon $P) (canon (fsubst $P $bind)))
      ((apv $f $args) (apv (fsubst $f $bind) (fsubst-all $args $bind)))
      ((lam $x $T $b) (lam $x (fsubst $T $bind) (fsubst $b (remove-key $x $bind))))
      ((arrow $A $B) (arrow (fsubst $A $bind) (fsubst $B $bind)))
      ((pi $x $A $B) (pi $x (fsubst $A $bind) (fsubst $B (remove-key $x $bind))))
      ((app $c $args) (app $c (fsubst-all $args $bind))))))

(= (fsubst-all $ts $bind)
   (if (== $ts ()) () (cons-atom (fsubst (car-atom $ts) $bind) (fsubst-all (cdr-atom $ts) $bind))))

(= (lookup-var-term $x $bind $default)
   (if (== $bind ()) $default
       (let ($k $v) (car-atom $bind) (if (== $k $x) $v (lookup-var-term $x (cdr-atom $bind) $default)))))

(= (is-fvar $t) (case $t (((var $x) True) ($_ False))))
(= (var-name $t) (case $t (((var $x) $x))))

; ---- case trees ----
; Lean's X.casesOn takes, for each constructor, a minor over the fields; the
; reading is X's recursor, whose method also takes one result per recursive
; field, here unused.  A matcher (Lean's function for a match) is read by its
; definition, a tree of X.casesOn over its discriminants: an application of
; a matcher is that tree at the application's arguments, beta-reduced.

(= (fvs $t)
   (case $t
     (((var $x) ($x))
      ((apv $f $args) (fvs-list (cons-atom $f $args)))
      ((lam $x $T $b) (union-names (fvs $T) (remove-name $x (fvs $b))))
      ((pi $x $A $B) (union-names (fvs $A) (remove-name $x (fvs $B))))
      ((arrow $A $B) (union-names (fvs $A) (fvs $B)))
      ((app $c $args) (fvs-list $args))
      ((canon $P) (fvs $P))
      ($_ ()))))
(= (fvs-list $ts) (if (== $ts ()) () (union-names (fvs (car-atom $ts)) (fvs-list (cdr-atom $ts)))))
(= (remove-name $x $xs)
   (if (== $xs ()) ()
       (if (== (car-atom $xs) $x) (remove-name $x (cdr-atom $xs)) (cons-atom (car-atom $xs) (remove-name $x (cdr-atom $xs))))))
(= (bind-fvs $bind)
   (if (== $bind ()) () (let ($k $v) (car-atom $bind) (union-names (fvs $v) (bind-fvs (cdr-atom $bind))))))
; Source names may be symbols and generated names strings. Both render as the
; same target identifier, so freshness must compare their identifier spelling.
; Internal field/parameter keys remain structured data, never identifiers.
(= (same-identifier $x $y)
   (if (or (== (get-metatype $x) Expression) (== (get-metatype $y) Expression))
       (== $x $y) (== (nm $x) (nm $y))))
(= (identifier-in $x $names)
   (if (== $names ()) False
       (if (same-identifier $x (car-atom $names)) True (identifier-in $x (cdr-atom $names)))))
(= (fresh-name $x $avoid) (if (identifier-in $x $avoid) (fresh-name (format-args "{}_c" ($x)) $avoid) $x))

; Substitution that renames a binder rather than capture a variable.
(= (csubst $t $bind)
   (if (== $bind ()) $t
   (case $t
     (((var $x) (lookup-var-term $x $bind $t))
      ((apv $f $args) (apv (csubst $f $bind) (csubst-all $args $bind)))
      ((app $c $args) (app $c (csubst-all $args $bind)))
      ((arrow $A $B) (arrow (csubst $A $bind) (csubst $B $bind)))
      ((canon $P) (canon (csubst $P $bind)))
      ((lam $x $T $b) (let ($y $b2) (csubst-binder $x $b $bind) (lam $y (csubst $T $bind) $b2)))
      ((pi $x $A $B) (let ($y $B2) (csubst-binder $x $B $bind) (pi $y (csubst $A $bind) $B2)))
      ($_ $t)))))
(= (csubst-all $ts $bind) (if (== $ts ()) () (cons-atom (csubst (car-atom $ts) $bind) (csubst-all (cdr-atom $ts) $bind))))
(= (csubst-binder $x $b $bind)
   (let $bind2 (remove-key $x $bind)
     (if (identifier-in $x (bind-fvs $bind2))
         (let $y (fresh-name $x (union-names (bind-fvs $bind2) (fvs $b)))
           ($y (csubst $b (cons-atom ($x (var $y)) $bind2))))
         ($x (csubst $b $bind2)))))

(= (beta-norm $t)
   (case $t
     (((apv $f $args) (beta-apply (beta-norm $f) (beta-norm-all $args)))
      ((app $c $args) (app $c (beta-norm-all $args)))
      ((lam $x $T $b) (lam $x (beta-norm $T) (beta-norm $b)))
      ((pi $x $A $B) (pi $x (beta-norm $A) (beta-norm $B)))
      ((arrow $A $B) (arrow (beta-norm $A) (beta-norm $B)))
      ((canon $P) (canon (beta-norm $P)))
      ($_ $t))))
(= (beta-norm-all $ts) (if (== $ts ()) () (cons-atom (beta-norm (car-atom $ts)) (beta-norm-all (cdr-atom $ts)))))
(= (beta-apply $f $as)
   (if (== $as ()) $f
       (case $f
         (((lam $x $T $b)
           (if (inlines $x $b (car-atom $as))
               (beta-apply (beta-norm (csubst $b (($x (car-atom $as))))) (cdr-atom $as))
               (apv $f $as)))
          ((apv $g $bs) (apv $g (append-lists $bs $as)))
          ($_ (apv $f $as))))))

; A binding (fun x => b) a is put in place when that copies no computation:
; a is a variable or a value, or b uses x at most once.  Otherwise it stays a
; binding (Lean's let), and a is computed once, before the binding is used.
(= (inlines $x $b $a)
   (if (is-trivial $a) True (<= (occ $x $b) 1)))
(= (is-trivial $a)
   (case $a
     (((var $y) True) ((num $k) True) ((proof) True) ((prop) True)
      ((lam $x $T $b) True) ((arrow $A $B) True) ((pi $x $A $B) True)
      ((app $c $args) (is-value $a))
      ($_ False))))
(= (is-binding $t)
   (case $t
     (((apv (lam $x $T $b) $args) (not (inlines $x $b (car-atom $args))))
      ($_ False))))
(= (occ $x $t)
   (case $t
     (((var $y) (if (== $x $y) 1 0))
      ((apv $f $args) (occ-list $x (cons-atom $f $args)))
      ((app $c $args) (occ-list $x $args))
      ((lam $y $T $b) (+ (occ $x $T) (if (== $x $y) 0 (occ $x $b))))
      ((pi $y $A $B) (+ (occ $x $A) (if (== $x $y) 0 (occ $x $B))))
      ((arrow $A $B) (+ (occ $x $A) (occ $x $B)))
      ((canon $P) (occ $x $P))
      ($_ 0))))
(= (occ-list $x $ts) (if (== $ts ()) 0 (+ (occ $x (car-atom $ts)) (occ-list $x (cdr-atom $ts)))))

(= (matcher-def $M)
   (let $found (collapse (match &self (LeanMatcher $M $bs $body) (mdef $bs $body)))
     (if (== $found ()) None (car-atom $found))))
(= (is-matcher $M) (if (== (matcher-def $M) None) False True))
(= (binder-name $b) (case $b (((term $x $t) $x) ((type $x $l) $x) ((sort $x $l) $x) ((hyp $x $p) $x))))
(= (binder-names $bs) (if (== $bs ()) () (cons-atom (binder-name (car-atom $bs)) (binder-names (cdr-atom $bs)))))
(= (zip-bind $xs $ts)
   (if (== $xs ()) () (if (== $ts ()) () (cons-atom ((car-atom $xs) (car-atom $ts)) (zip-bind (cdr-atom $xs) (cdr-atom $ts))))))

(= (expand $t)
   (case $t
     (((app $c $args)
       (let* (($as (expand-all $args)) ($d (matcher-def $c)))
         (if (== $d None) (if (is-cases-on $c) (cases-saturate $c $as) (app $c $as)) (expand-matcher $c $d $as))))
      ((apv $f $args) (apv (expand $f) (expand-all $args)))
      ((lam $x $T $b) (lam $x (expand $T) (expand $b)))
      ((pi $x $A $B) (pi $x (expand $A) (expand $B)))
      ((arrow $A $B) (arrow (expand $A) (expand $B)))
      ($_ $t))))
; X.casesOn applied past its minors (a match on h : e = e applied to the
; proof of e = e) is the case analysis applied to the rest.
(= (cases-saturate $c $as)
   (let* (($F (cases-family $c))
          ($k (+ (+ (+ (param-count $F) 2) (index-count $F)) (length-of (constructors-of $F)))))
     (if (> (length-of $as) $k) (apv (app $c (take-n $as $k)) (drop-n $as $k)) (app $c $as))))
(= (expand-all $ts) (if (== $ts ()) () (cons-atom (expand (car-atom $ts)) (expand-all (cdr-atom $ts)))))
(= (expand-matcher $c $d $as)
   (case $d
     (((mdef $bs $body)
       (let* (($xs (binder-names $bs)) ($n (length-of $xs)))
         (if (< (length-of $as) $n) (app $c $as)
             (let $inst (csubst $body (zip-bind $xs (take-n $as $n)))
               (expand (beta-norm (if (== (length-of $as) $n) $inst (apv $inst (drop-n $as $n))))))))))))
(= (norm-term $t) (beta-norm (expand $t)))

; The minor of constructor k as the recursor's method.
(= (wrap-minors $F $ps $R $minors $k)
   (if (== $minors ()) ()
       (cons-atom (wrap-minor $F $ps $R (car-atom $minors) $k) (wrap-minors $F $ps $R (cdr-atom $minors) (+ $k 1)))))
; $M is the motive's result: a type, or (dmotive z R) when it depends on the
; value z; an induction hypothesis lies in the motive at its field.
(= (wrap-minor $F $ps $M $minor $k)
   (let* (($c (nth (constructors-of $F) $k)) ($nr (rec-count (ctor-fields $c))))
     (if (== $nr 0) $minor
         (wrap-fields $minor (ctor-field-types (ctor-name $c) $ps) (ctor-fields $c) $M $k 0 ()))))
(= (rec-count $fs) (if (== $fs ()) 0 (+ (if (is-rec (car-atom $fs)) 1 0) (rec-count (cdr-atom $fs)))))
(= (wrap-fields $minor $Ts $fs $M $k $i $recv)
   (if (== $Ts ()) (ih-lams $minor $recv $M $k 0)
       (case $minor
         (((lam $x $T $b)
           (lam $x $T (wrap-fields $b (cdr-atom $Ts) (cdr-atom $fs) $M $k (+ $i 1) (rec-push (car-atom $fs) (var $x) $recv))))
          ($_ (let $w (format-args "e{}_{}" ($k $i))
                (lam $w (car-atom $Ts)
                  (wrap-fields (apv-one $minor (var $w)) (cdr-atom $Ts) (cdr-atom $fs) $M $k (+ $i 1) (rec-push (car-atom $fs) (var $w) $recv)))))))))
(= (rec-push $fd $v $recv) (if (is-rec $fd) (append-lists $recv ($v)) $recv))
(= (apv-one $f $a) (case $f (((apv $g $as) (apv $g (append-lists $as ($a)))) ($_ (apv $f ($a))))))
(= (ih-lams $b $recv $M $k $j)
   (if (== $recv ()) $b
       (lam (format-args "ih{}_{}" ($k $j)) (motive-at $M (car-atom $recv)) (ih-lams $b (cdr-atom $recv) $M $k (+ $j 1)))))
(= (motive-of $motive)
   (case $motive (((lam $x $T $R) (if (mentions $R $x) (dmotive $x $R) $R)) ($_ None))))
(= (motive-at $M $v) (case $M (((dmotive $z $R) (fsubst $R (($z $v)))) ($_ $M))))
(= (motive-text $M $sub)
   (case $M (((dmotive $z $R) (format-args "(fun {} => {})" ($z (render $R (remove-key $z $sub)))))
             ($_ (format-args "(fun _ => {})" ((render $M $sub)))))))
; The recursive results the recursor passes: the case analysis at each
; recursive field.
(= (ih-terms $c $ps $motive $minors $fields $fds)
   (if (== $fds ()) ()
       (let $rest (ih-terms $c $ps $motive $minors (cdr-atom $fields) (cdr-atom $fds))
         (if (is-rec (car-atom $fds))
             (cons-atom (app $c (append-lists $ps (cons-atom $motive (cons-atom (car-atom $fields) $minors)))) $rest)
             $rest))))

; ---- nested patterns and patterns at several arguments ----
; A function whose equations have nested patterns, or patterns at several
; arguments, is read by one split: at the argument it recurs on (or the
; first with a pattern), one equation per constructor, its right side the
; remaining patterns as case analyses, compiled column by column in the
; order of Lean's equations (the first that matches applies).  The split's
; equations are proved from the recursor; Lean's own, from them by the case
; analyses' iota and beta.

(= (splitname $f $k) (split $f $k))
; A function taking proofs as arguments (Lean's helpers for well-founded
; recursion) is not split.
(= (has-proof-arg $eqs)
   (if (== $eqs ()) False (if (member-term (proof) (lhs-args (car-atom $eqs))) True (has-proof-arg (cdr-atom $eqs)))))
(= (needs-split $f $eqs)
   (if (== $eqs ()) False
   (if (has-proof-arg $eqs) False
   (let* (($n (length-of (lhs-args (car-atom $eqs)))) ($ps (pattern-positions $eqs 0 $n)))
     (if (== $ps ()) False
     (if (> (length-of $ps) 1) True
     (let $m (car-atom $ps)
       (if (any-var-at $eqs $m) True (any-nested-at $eqs $m)))))))))
(= (any-var-at $eqs $m)
   (if (== $eqs ()) False (if (is-fvar (nth (lhs-args (car-atom $eqs)) $m)) True (any-var-at (cdr-atom $eqs) $m))))
(= (any-nested-at $eqs $m)
   (if (== $eqs ()) False
       (if (all-vars (pattern-fields (pattern-of (nth (lhs-args (car-atom $eqs)) $m)))) (any-nested-at (cdr-atom $eqs) $m) True)))
(= (pattern-fields $pat)
   (case $pat (((app $K $args) (if (is-ctor $K) (drop-n $args (param-count (family-of-ctor $K))) ())) ($_ ()))))
(= (is-ctor-pat $p) (case $p (((app $K $as) (is-ctor $K)) ($_ False))))

(= (recursive-eqns $f $eqs)
   (if (== $eqs ()) False (if (calls-self (eqn-rhs (car-atom $eqs)) $f) True (recursive-eqns $f (cdr-atom $eqs)))))
(= (split-at $f $eqs $n)
   (let $ps (ctor-positions $eqs 0 $n)
     (if (== $ps ()) None
         (if (recursive-eqns $f $eqs) (first-structural-col $f $eqs $ps) (car-atom $ps)))))
(= (ctor-positions $eqs $i $n)
   (if (>= $i $n) ()
       (let $rest (ctor-positions $eqs (+ $i 1) $n)
         (if (any-ctor-at $eqs $i) (cons-atom $i $rest) $rest))))
(= (any-ctor-at $eqs $i)
   (if (== $eqs ()) False (if (is-ctor-pat (pattern-of (nth (lhs-args (car-atom $eqs)) $i))) True (any-ctor-at (cdr-atom $eqs) $i))))
(= (first-structural-col $f $eqs $ps)
   (if (== $ps ()) None
       (if (structural-col $f $eqs (car-atom $ps)) (car-atom $ps) (first-structural-col $f $eqs (cdr-atom $ps)))))
(= (structural-col $f $eqs $m)
   (if (== $eqs ()) True
       (let* (($e (car-atom $eqs)) ($pat (pattern-of (nth (lhs-args $e) $m))))
         (if (calls-on-fields (eqn-rhs $e) $f $m (pattern-fields $pat)) (structural-col $f (cdr-atom $eqs) $m) False))))
(= (calls-on-fields $t $f $m $fields)
   (case $t
     (((app $c $as)
       (if (== $c $f)
           (if (member-term (nth $as $m) $fields) (calls-on-fields-list $as $f $m $fields) False)
           (calls-on-fields-list $as $f $m $fields)))
      ((apv $g $as) (calls-on-fields-list (cons-atom $g $as) $f $m $fields))
      ((lam $x $T $b) (calls-on-fields $b $f $m $fields))
      ($_ True))))
(= (calls-on-fields-list $ts $f $m $fields)
   (if (== $ts ()) True (if (calls-on-fields (car-atom $ts) $f $m $fields) (calls-on-fields-list (cdr-atom $ts) $f $m $fields) False)))

; The variable for argument p of the split, and a row's variables named by position.
(= (arg-var $p) (format-args "s{}" ($p)))
(= (row-sbind $args $p)
   (if (== $args ()) ()
       (let $rest (row-sbind (cdr-atom $args) (+ $p 1))
         (if (is-fvar (car-atom $args)) (cons-atom ((var-name (car-atom $args)) (var (arg-var $p))) $rest) $rest))))
; The binder of argument p of the split: a row's binder kind and type there.
(= (col-binder $eqs $p)
   (let $e (row-with-var $eqs $p)
     (if (== $e None)
         (let* (($e0 (car-atom $eqs)) ($pat (pattern-of (nth (lhs-args $e0) $p))) ($K (app-head $pat))
                ($F (family-of-ctor $K)))
           (term (arg-var $p) (fsubst (app $F (take-n (app-args $pat) (param-count $F))) (row-sbind (lhs-args $e0) 0))))
         (let* (($x (var-name (nth (lhs-args $e) $p))) ($sb (row-sbind (lhs-args $e) 0)))
           (case (binder-of $x (eqn-binders $e))
             (((type $y $l) (type (arg-var $p) $l))
              ((sort $y $l) (sort (arg-var $p) $l))
              ((term $y $t) (term (arg-var $p) (fsubst $t $sb)))))))))
(= (row-with-var $eqs $p)
   (if (== $eqs ()) None (if (is-fvar (nth (lhs-args (car-atom $eqs)) $p)) (car-atom $eqs) (row-with-var (cdr-atom $eqs) $p))))
(= (binder-of $x $bs)
   (if (== $bs ()) None (if (== (binder-name (car-atom $bs)) $x) (car-atom $bs) (binder-of $x (cdr-atom $bs)))))
(= (col-binders $eqs $p $n)
   (if (>= $p $n) () (cons-atom (col-binder $eqs $p) (col-binders $eqs (+ $p 1) $n))))
(= (binder-type-of $b) (case $b (((term $x $t) $t) ($_ None))))

(= (split-eqns $f $eqs)
   (if (not (needs-split $f $eqs)) None
   (let* (($n (length-of (lhs-args (car-atom $eqs)))) ($m (split-at $f $eqs $n)))
     (if (== $m None) None
     (let* (($bs (col-binders $eqs 0 $n)) ($Tm (binder-type-of (nth $bs $m))))
       (if (== $Tm None) None
       (let* (($F (app-head $Tm)) ($cs (constructors-of $F))
              ($e0 (car-atom $eqs)) ($R (split-result-type $f $e0))
              ($out (split-eqns-for $f $eqs $m $n $bs $Tm $R $cs 0)))
         (if (any-failed $out) None $out))))))))
(= (any-failed $xs) (if (== $xs ()) False (case (car-atom $xs) (((fail $why) True) ($_ (any-failed (cdr-atom $xs)))))))
; The result type over the split's argument names s0, s1, ..: the declared
; type's result when it depends on the arguments (Decidable (x = y)), which no
; single equation's type shows; otherwise the first equation's type.
(= (split-result-type $f $e0)
   (if (dep-typed $f)
       (let $T (fn-type $f) (fsubst (type-result-of $T) (named-binds (type-binders-of $T 0) 0 arg-var)))
       (fsubst (eqn-type $e0) (row-sbind (lhs-args $e0) 0))))
(= (named-binds $bs $p $namer)
   (if (== $bs ()) ()
       (cons-atom ((car-atom (car-atom $bs)) (var ($namer $p))) (named-binds (cdr-atom $bs) (+ $p 1) $namer))))
; The declared result type over the positional names a0, a1, ...
(= (pos-result $f)
   (let $T (fn-type $f) (fsubst (type-result-of $T) (named-binds (type-binders-of $T 0) 0 pos-name))))

(= (split-eqns-for $f $eqs $m $n $bs $Tm $R $cs $k)
   (if (== $cs ()) ()
       (cons-atom (split-eqn $f $eqs $m $n $bs $Tm $R (ctor-name (car-atom $cs)) $k)
                  (split-eqns-for $f $eqs $m $n $bs $Tm $R (cdr-atom $cs) (+ $k 1)))))

(= (t-name $i) (format-args "t{}" ($i)))
(= (t-vars $Ts $i) (if (== $Ts ()) () (cons-atom (var (t-name $i)) (t-vars (cdr-atom $Ts) (+ $i 1)))))
(= (t-binders $Ts $i) (if (== $Ts ()) () (cons-atom (term (t-name $i) (car-atom $Ts)) (t-binders (cdr-atom $Ts) (+ $i 1)))))
(= (s-args $p $n $m $kterm)
   (if (>= $p $n) () (cons-atom (if (== $p $m) $kterm (var (arg-var $p))) (s-args (+ $p 1) $n $m $kterm))))
(= (cols-of-binders $bs $m $p $tcols)
   (if (== $bs ()) ()
       (let $rest (cols-of-binders (cdr-atom $bs) $m (+ $p 1) $tcols)
         (if (== $p $m) (append-lists $tcols $rest)
             (cons-atom (cv (var (arg-var $p)) (binder-type-of (car-atom $bs))) $rest)))))
(= (t-cols $Ts $i) (if (== $Ts ()) () (cons-atom (cv (var (t-name $i)) (car-atom $Ts)) (t-cols (cdr-atom $Ts) (+ $i 1)))))
(= (split-binders $bs $m $p $tbs)
   (if (== $bs ()) ()
       (let $rest (split-binders (cdr-atom $bs) $m (+ $p 1) $tbs)
         (if (== $p $m) (append-lists $tbs $rest) (cons-atom (car-atom $bs) $rest)))))

(= (split-eqn $f $eqs $m $n $bs $Tm $R $K $k)
   (let* (($ps (app-args $Tm)) ($Ts (ctor-field-types $K $ps)) ($tvs (t-vars $Ts 0))
          ($kterm (app $K (append-lists $ps $tvs)))
          ($cols (cols-of-binders $bs $m 0 (t-cols $Ts 0)))
          ($rows (rows-at-top $eqs $m $K $kterm (length-of $Ts)))
          ($RK (fsubst $R (((arg-var $m) $kterm))))
          ($body (compile-matrix $rows $cols $RK 1)))
     (case $body
       (((fail $why) (fail $why))
        ($_ (eqn (splitname $f $k) (split-binders $bs $m 0 (t-binders $Ts 0)) $RK
                 (app $f (s-args 0 $n $m $kterm)) $body))))))

; A row of the pattern matrix: its patterns, its right side, and the values
; already given to its variables.
(= (wilds $k) (if (== $k 0) () (cons-atom (wild) (wilds (- $k 1)))))
(= (rows-at-top $eqs $m $K $kterm $nf)
   (if (== $eqs ()) ()
       (let* (($e (car-atom $eqs)) ($args (lhs-args $e)) ($pat (pattern-of (nth $args $m)))
              ($rest (rows-at-top (cdr-atom $eqs) $m $K $kterm $nf)))
         (case $pat
           (((var $x) (cons-atom (row (splice $args $m (wilds $nf)) (eqn-rhs $e) (($x $kterm))) $rest))
            ((app $K2 $as)
             (if (== $K2 $K)
                 (cons-atom (row (splice $args $m (drop-n $as (param-count (family-of-ctor $K)))) (eqn-rhs $e) ()) $rest)
                 $rest))
            ($_ $rest))))))

(= (row-pats $r) (case $r (((row $ps $rhs $b) $ps))))
(= (first-ctor-col $pats $j)
   (if (== $pats ()) None
       (if (is-ctor-pat (pattern-of (car-atom $pats))) $j (first-ctor-col (cdr-atom $pats) (+ $j 1)))))
(= (col-term $c) (case $c (((cv $t $T) $t))))
(= (col-type $c) (case $c (((cv $t $T) $T))))
(= (pat-binds $pats $cols)
   (if (== $pats ()) ()
       (let $rest (pat-binds (cdr-atom $pats) (cdr-atom $cols))
         (case (car-atom $pats) (((var $x) (cons-atom ($x (col-term (car-atom $cols))) $rest)) ($_ $rest))))))

(= (compile-matrix $rows $cols $R $d)
   (if (== $rows ()) (fail "patterns that do not cover every case")
       (let* (($r (car-atom $rows)) ($j (first-ctor-col (row-pats $r) 0)))
         (if (== $j None)
             (case $r (((row $pats $rhs $b) (fsubst $rhs (append-lists (pat-binds $pats $cols) $b)))))
             (split-matrix $rows $cols $R $d $j)))))

(= (split-matrix $rows $cols $R $d $j)
   (let* (($col (nth $cols $j)) ($T (col-type $col)) ($G (app-head $T)) ($ps (app-args $T))
          ($co (cases-on-of $G)))
     (if (== $co None) (fail (format-args "no case analysis exported for {}" ((nm $G))))
         (let $minors (minors-for $rows $cols $R $d $j $ps (constructors-of $G) 0)
           (if (any-failed $minors) (car-atom (failed-of $minors))
               (let $z (format-args "z{}" ($d))
                 (app $co (append-lists $ps (cons-atom (lam $z $T (at-col $R $col (var $z))) (cons-atom (col-term $col) $minors))))))))))
; A result type at a column's value: where the type depends on the column
; (Decidable (x = y) at y), the case analysis's motive depends on its value.
(= (at-col $R $col $v)
   (case (col-term $col) (((var $x) (fsubst $R (($x $v)))) ($_ $R))))
(= (failed-of $xs) (if (== $xs ()) () (case (car-atom $xs) (((fail $w) (cons-atom (fail $w) ())) ($_ (failed-of (cdr-atom $xs)))))))
(= (cases-on-of $G)
   (let $found (collapse (match &self (LeanCasesOn $c $G) $c)) (if (== $found ()) None (car-atom $found))))

(= (c-name $d $i $l) (format-args "c{}_{}_{}" ($d $i $l)))
(= (c-cols $Ts $d $i $l) (if (== $Ts ()) () (cons-atom (cv (var (c-name $d $i $l)) (car-atom $Ts)) (c-cols (cdr-atom $Ts) $d $i (+ $l 1)))))
(= (lam-cols $cs $body) (if (== $cs ()) $body (case (car-atom $cs) (((cv (var $x) $T) (lam $x $T (lam-cols (cdr-atom $cs) $body)))))))
(= (col-terms $cs) (if (== $cs ()) () (cons-atom (col-term (car-atom $cs)) (col-terms (cdr-atom $cs)))))
(= (splice $xs $j $ys)
   (append-lists (take-n $xs $j) (append-lists $ys (drop-n $xs (+ $j 1)))))

(= (minors-for $rows $cols $R $d $j $ps $cs $i)
   (if (== $cs ()) ()
       (let* (($K (ctor-name (car-atom $cs))) ($Ts (ctor-field-types $K $ps)) ($fc (c-cols $Ts $d $i 0))
              ($kterm (app $K (append-lists $ps (col-terms $fc))))
              ($rows2 (rows-at $rows $j $K $kterm (length-of $Ts)))
              ($body (compile-matrix $rows2 (splice $cols $j $fc) (at-col $R (nth $cols $j) $kterm) (+ $d 1))))
         (cons-atom (case $body (((fail $w) (fail $w)) ($_ (lam-cols $fc $body))))
                    (minors-for $rows $cols $R $d $j $ps (cdr-atom $cs) (+ $i 1))))))

(= (rows-at $rows $j $K $kterm $nf)
   (if (== $rows ()) ()
       (let $rest (rows-at (cdr-atom $rows) $j $K $kterm $nf)
         (case (car-atom $rows)
           (((row $pats $rhs $b)
             (let $p (pattern-of (nth $pats $j))
               (case $p
                 (((wild) (cons-atom (row (splice $pats $j (wilds $nf)) $rhs $b) $rest))
                  ((var $x) (cons-atom (row (splice $pats $j (wilds $nf)) $rhs (cons-atom ($x $kterm) $b)) $rest))
                  ((app $K2 $as)
                   (if (== $K2 $K)
                       (cons-atom (row (splice $pats $j (drop-n $as (param-count (family-of-ctor $K)))) $rhs $b) $rest)
                       $rest))
                  ($_ $rest))))))))))

; Lean's equations of a split function: rewrite with the split's equation
; at Lean's left side, then reduce its case analyses on constructors (iota)
; and the minors' applications (beta) until Lean's right side is reached.
(= (lean-eqn-theorems $f $eqs)
   (if (== $eqs ()) "" (format-args "{}{}" ((lean-eqn-theorem $f (car-atom $eqs)) (lean-eqn-theorems $f (cdr-atom $eqs))))))
(= (has-hyp $bs)
   (if (== $bs ()) False
       (case (car-atom $bs)
         (((hyp $x $p) (if (is-cond-hyp $p) True (has-hyp (cdr-atom $bs))))
          ($_ (has-hyp (cdr-atom $bs)))))))
; A condition says an earlier pattern does not apply: forall ys, x = p -> False.
; Any other hypothesis (h : a = b in Eq.ndrec) is a proof argument.
(= (is-cond-hyp $P)
   (case $P
     (((pi $y $T $B) (is-cond-hyp $B))
      ((arrow (app Eq ($T (var $x) $pattern)) $rest) (exclusion-tail $rest))
      ($_ False))))
(= (exclusion-tail $P)
   (case $P
     (((arrow (app Eq ($T (var $x) $pattern)) $rest) (exclusion-tail $rest))
      ((app False ()) True) ($_ False))))
; The proof of a proof argument's proposition at an instance.
(= (hyp-proof $P)
   (case $P
     (((app Eq ($T $a $c)) (if (== $a $c) (format-args "(Lean_eq_refl {})" ((render $a ()))) (prove-prop $P)))
      ($_ (prove-prop $P)))))

(= (stmt-ctx $bs)
   (let $base (stmt-value-ctx $bs) (append-lists (stmt-proof-ctx $bs $base) $base)))
(= (stmt-value-ctx $bs)
   (if (== $bs ()) ()
       (let $rest (stmt-value-ctx (cdr-atom $bs))
         (case (car-atom $bs)
           (((term $x $T) (cons-atom ($x (format-args "H_{}" ($x))) (cons-atom ((ty $x) $T) $rest)))
            ((type $x $l) (cons-atom ($x (format-args "H_{}" ($x))) $rest))
            ((sort $x $l) (cons-atom ($x (format-args "H_{}" ($x))) $rest))
            ((hyp $x $P) (cons-atom ((ReservedName $x) ()) $rest))
            ($_ $rest))))))
(= (stmt-proof-ctx $bs $ctx)
   (if (== $bs ()) ()
       (let $rest (stmt-proof-ctx (cdr-atom $bs) $ctx)
         (case (car-atom $bs)
           (((hyp $x $P) (cons-atom ((ProofOf $P) (native-proof $P (nm $x) $ctx 0)) $rest))
            ($_ $rest))))))
(= (known-proof $P $ctx)
   (if (== $ctx ()) None
       (case (car-atom $ctx)
         ((((ProofOf $Q) $proof) (if (alpha-eq $P $Q ()) $proof (known-proof $P (cdr-atom $ctx))))
          ($_ (known-proof $P (cdr-atom $ctx)))))))

; Names introduced by proof conversion avoid both free and bound source names.
(= (all-term-names $t)
   (case $t
     (((var $x) ($x))
      ((pi $x $A $B) (cons-atom $x (union-names (all-term-names $A) (all-term-names $B))))
      ((lam $x $A $B) (cons-atom $x (union-names (all-term-names $A) (all-term-names $B))))
      ((arrow $A $B) (union-names (all-term-names $A) (all-term-names $B)))
      ((app $c $args) (all-term-names-list $args))
      ((apv $f $args) (all-term-names-list (cons-atom $f $args))) ($_ ()))))
(= (all-term-names-list $ts)
   (if (== $ts ()) () (union-names (all-term-names (car-atom $ts)) (all-term-names-list (cdr-atom $ts)))))
(= (ctx-names $ctx)
   (if (== $ctx ()) ()
       (let ($key $value) (car-atom $ctx)
         (let $rest (ctx-names (cdr-atom $ctx))
           (case $key
             (((ReservedName $name) (cons-atom $name $rest))
              ($_ (if (== (get-metatype $key) Expression) $rest (cons-atom $key $rest)))))))))
(= (bridge-name $kind $n $P $ctx)
   (fresh-name (format-args "bridge_{}_{}" ($kind $n)) (union-names (all-term-names $P) (ctx-names $ctx))))

; A native statement hypothesis is converted to the proof value of its
; proposition. Unsupported logical forms remain an explicit missing proof.
(= (native-proof $P $h $ctx $n)
   (case $P
     (((app Eq ($T $a $b)) (format-args "(Lean_Eq_proof_of {} {} {} {})"
        ((render $T ()) (render $a ()) (render $b ()) $h)))
      ((app False ()) (format-args "(FalseE {} (0 :e Lean_False_Prop))" ($h)))
      ((app And ($A $B))
       (format-args "(Lean_And_intro_proof_ok {} {} 0 {} 0 {})"
         ((render $A ()) (render $B ())
          (native-proof $A (format-args "(andEL ({}) ({}) {})" ((stmt-native $A) (stmt-native $B) $h)) $ctx (+ $n 1))
          (native-proof $B (format-args "(andER ({}) ({}) {})" ((stmt-native $A) (stmt-native $B) $h)) $ctx (+ $n 1)))))
      ((arrow $A $B)
       (let* (($x (bridge-name "x" $n $P $ctx)) ($hx (bridge-name "h" $n $P $ctx))
              ($pa (format-args "(Lean_prop_0_of {} {} {} {})" ((render $A ()) (typ $A () $ctx) $x $hx)))
              ($native (proof-native $A $pa $ctx (+ $n 1))))
         (format-args "(Pi_0_In {} (fun _ => {}) (fun {} {} => {}))"
           ((render $A ()) (render $B ()) $x $hx
            (native-proof $B (format-args "({} {})" ($h $native)) $ctx (+ $n 1))))))
      ((pi $x $A $B)
       (let* (($hx (bridge-name "h" $n $P $ctx))
              ($ctx2 (cons-atom ($x $hx) (cons-atom ((ty $x) $A) $ctx))))
         (format-args "(Pi_0_In {} (fun {} => {}) (fun {} {} => {}))"
           ((render $A ()) $x (render $B ()) $x $hx
            (native-proof $B (format-args "({} {} {})" ($h $x $hx)) $ctx2 (+ $n 1))))))
      ((app Or $args) "UNDECIDED_native_disjunction")
      ((app Exists $args) "UNDECIDED_native_existential")
      ($_ $h))))
(= (proof-native $P $h $ctx $n)
   (case $P
     (((app Eq ($T $a $b)) (format-args "(LeanEq_sound {} {} {} 0 {})"
        ((render $T ()) (render $a ()) (render $b ()) $h)))
      ((app False ()) (format-args "(Lean_False_Prop_empty 0 {})" ($h)))
      ((app And ($A $B))
       (format-args "(andI ({}) ({}) {} {})"
         ((stmt-native $A) (stmt-native $B)
          (proof-native $A (format-args "(LeanAnd_left {} {} {} {} 0 {})"
            ((render $A ()) (typ $A () $ctx) (render $B ()) (typ $B () $ctx) $h)) $ctx (+ $n 1))
          (proof-native $B (format-args "(LeanAnd_right {} {} {} {} 0 {})"
            ((render $A ()) (typ $A () $ctx) (render $B ()) (typ $B () $ctx) $h)) $ctx (+ $n 1)))))
      ((arrow $A $B)
       (let* (($ha (bridge-name "native" $n $P $ctx))
              ($pa (native-proof $A $ha $ctx (+ $n 1)))
              ($pb (format-args "(Lean_prop_0_of {} {} (0 0) (ap_Pi {} (fun _ => {}) 0 0 {} {}))"
                ((render $B ()) (typ $B () $ctx) (render $A ()) (render $B ()) $h $pa))))
         (format-args "(fun {} => {})" ($ha (proof-native $B $pb $ctx (+ $n 1))))))
      ((pi $x $A $B)
       (let* (($hx (bridge-name "h" $n $P $ctx))
              ($ctx2 (cons-atom ($x $hx) (cons-atom ((ty $x) $A) $ctx)))
              ($pb (format-args "(Lean_prop_0_of {} {} (0 {}) (ap_Pi {} (fun {} => {}) 0 {} {} {}))"
                ((render $B ()) (typ $B () $ctx2) $x (render $A ()) $x (render $B ()) $x $h $hx))))
         (format-args "(fun {} {} => {})" ($x $hx (proof-native $B $pb $ctx2 (+ $n 1))))))
      ((app Or $args) "UNDECIDED_native_disjunction")
      ((app Exists $args) "UNDECIDED_native_existential")
      ($_ $h))))

(= (lean-eqn-theorem $f $e)
   (if (has-hyp (eqn-binders $e)) (cond-eqn-theorem $f $e)
   (let* (($m (shape-m (shape-of $f))) ($ctx (stmt-ctx (eqn-binders $e)))
          ($pf (split-chain $f (lhs-args $e) (eqn-rhs $e) $ctx)))
     (case $pf
       (((stuck $why) (equation-by-cases $f $e $why))
        ((proof $lines) (format-args "{}Theorem {} : {}.
{}
{}{}Qed.
" ((receipt-comment (eqn-name $e) $f) (egal (eqn-name $e)) (statement-text $e) (eqn-intros $e)
   (literal-zero-line $e $m) $lines))))))))

; A source equation may leave the compiler's chosen split argument general.
; Prove it over all constructors, using the existing split equations in each
; case. This retains the original source statement and its receipt.
(= (equation-by-cases $f $e $why)
   (let* (($bs (eqn-binders $e)) ($tbs (type-binders $bs))
          ($patterns (case-equation-patterns (eqns-of $f) (lhs-args $e)))
          ($pf (if (== (hyp-names $bs) ())
                 (cases-proof equation $f (term-todo $bs) (lhs-args $e) (eqn-rhs $e)
                   $patterns () (stmt-ctx $tbs)) (stuck $why))))
     (case $pf
       (((stuck $reason) (format-args "(** {} not proved here: {} **)\n" ((nm (eqn-name $e)) $reason)))
        ((proof $lines) (format-args "{}Theorem {} : {}.\n{}\n{}Qed.\n"
          ((receipt-comment (eqn-name $e) $f) (egal (eqn-name $e)) (statement-text $e)
           (stmt-intros $tbs ()) $lines)))))))
(= (case-equation-patterns $eqs $args)
   (if (== $eqs ()) ()
       (cons-atom (hy (eqn-name (car-atom $eqs))
                     (excl () (zip-pairs $args (lhs-args (car-atom $eqs)))))
         (case-equation-patterns (cdr-atom $eqs) $args))))

; The proof that f at args equals rhs: the split equation of the constructor
; at the split column, then the chain of case analyses' iota steps and betas.
(= (split-chain $f $args $rhs $ctx)
   (let* (($s (shape-of $f)) ($m (shape-m $s))
          ($args1 (if (== (nth $args $m) (num 0)) (replace-at $args $m (app Nat.zero ()) 0) $args)))
     (if (not (is-ctor-pat (pattern-of (nth $args1 $m))))
         (stuck "a variable where the split has a pattern, which needs a proof by cases")
   (let* (($K (app-head (pattern-of (nth $args1 $m))))
          ($k (ctor-index-in (constructors-of (shape-fam $s)) $K 0))
          ($se (nth (eqns-of $f) $k))
          ($inst (fmatch-list (lhs-args $se) (replace-at $args1 $m (pattern-deep (nth $args1 $m)) 0) ())))
     (if (== $inst fail) (stuck "its left side does not instantiate the split")
     (let $lines (chain (csubst (eqn-rhs $se) $inst) $rhs $ctx 400)
       (case $lines
         (((stuck $why) (stuck $why))
          ($_ (proof (format-args "rewrite {} {}.
{}" ((egal (eqn-name $se)) (join " " (split-inst-args (eqn-binders $se) $inst $ctx ())) $lines))))))))))))

; ---- equations under hypotheses, proved by cases ----
; Lean states an equation after overlapping ones under hypotheses that the
; earlier patterns do not apply: forall ys, x = p -> ... -> False.  The proof
; splits a variable while some hypothesis has a constructor where the
; variable stands; a case that an earlier pattern matches contradicts its
; hypothesis, and any other case reduces by the split equation.

(= (hyp-parse $P $ys)
   (case $P
     (((pi $y $T $B) (hyp-parse $B (append-lists $ys (($y $T)))))
      ($_ (excl $ys (hyp-pairs $P))))))
(= (hyp-pairs $P)
   (case $P
     (((arrow (app Eq ($T (var $x) $p)) $B) (cons-atom ((var $x) $p) (hyp-pairs $B)))
      ($_ ()))))
(= (hyp-names $bs)
   (if (== $bs ()) () (case (car-atom $bs) (((hyp $x $P) (cons-atom $x (hyp-names (cdr-atom $bs)))) ($_ (hyp-names (cdr-atom $bs)))))))
(= (hyp-list $bs)
   (if (== $bs ()) ()
       (case (car-atom $bs)
         (((hyp $x $P) (cons-atom (hy $x (hyp-parse $P ())) (hyp-list (cdr-atom $bs))))
          ($_ (hyp-list (cdr-atom $bs)))))))
(= (type-binders $bs)
   (if (== $bs ()) ()
       (case (car-atom $bs)
         (((type $x $l) (cons-atom (car-atom $bs) (type-binders (cdr-atom $bs))))
          ((sort $x $l) (cons-atom (car-atom $bs) (type-binders (cdr-atom $bs))))
          ($_ (type-binders (cdr-atom $bs)))))))
(= (term-todo $bs)
   (if (== $bs ()) ()
       (case (car-atom $bs)
         (((term $x $T) (cons-atom (tv $x $T) (term-todo (cdr-atom $bs))))
          ($_ (term-todo (cdr-atom $bs)))))))

; A pattern for matching: the literal 0 is Nat.zero.
(= (zero-pat $p)
   (case $p
     (((num 0) (app Nat.zero ()))
      ((app $c $ps) (app $c (zero-pats $ps)))
      ($_ $p))))
(= (zero-pats $ps) (if (== $ps ()) () (cons-atom (zero-pat (car-atom $ps)) (zero-pats (cdr-atom $ps)))))
(= (has-num $p)
   (case $p (((num $k) True) ((app $c $ps) (any-num $ps)) ($_ False))))
(= (any-num $ps) (if (== $ps ()) False (if (has-num (car-atom $ps)) True (any-num (cdr-atom $ps)))))

; Whether a pattern can still match a term: clash on different constructors.
(= (pat-clash $p $t)
   (case $p
     (((app $c $ps)
       (if (is-ctor $c)
           (case $t
             (((app $d $ts) (if (is-ctor $d) (if (== $c $d) (pats-clash $ps $ts) True) False))
              ($_ False)))
           False))
      ($_ False))))
(= (pats-clash $ps $ts)
   (if (== $ps ()) False (if (pat-clash (car-atom $ps) (car-atom $ts)) True (pats-clash (cdr-atom $ps) (cdr-atom $ts)))))
(= (pairs-clash $pairs)
   (if (== $pairs ()) False
       (let ($t $p) (car-atom $pairs) (if (pat-clash (zero-pat $p) $t) True (pairs-clash (cdr-atom $pairs))))))
; Whether a pattern has a constructor where the term has the variable x.
(= (ctor-at-var $p $t $x)
   (case $p
     (((app $c $ps)
       (if (is-ctor $c)
           (case $t
             (((var $y) (== $y $x))
              ((app $d $ts) (if (== $c $d) (ctor-at-var-list $ps $ts $x) False))
              ($_ False)))
           False))
      ($_ False))))
(= (ctor-at-var-list $ps $ts $x)
   (if (== $ps ()) False (if (ctor-at-var (car-atom $ps) (car-atom $ts) $x) True (ctor-at-var-list (cdr-atom $ps) (cdr-atom $ts) $x))))
(= (pairs-need $pairs $x)
   (if (== $pairs ()) False
       (let ($t $p) (car-atom $pairs) (if (ctor-at-var (zero-pat $p) $t $x) True (pairs-need (cdr-atom $pairs) $x)))))
(= (hyp-needs-split $hyps $x)
   (if (== $hyps ()) False
       (case (car-atom $hyps)
         (((hy $h (excl $ys $pairs))
           (if (pairs-clash $pairs) (hyp-needs-split (cdr-atom $hyps) $x)
               (if (pairs-need $pairs $x) True (hyp-needs-split (cdr-atom $hyps) $x))))))))
(= (pairs-match $pairs)
   (if (pairs-clash $pairs) fail
       (fmatch-list (zero-pats (pairs-pats $pairs)) (pairs-terms $pairs) ())))
(= (pairs-pats $pairs) (if (== $pairs ()) () (let ($t $p) (car-atom $pairs) (cons-atom $p (pairs-pats (cdr-atom $pairs))))))
(= (pairs-terms $pairs) (if (== $pairs ()) () (let ($t $p) (car-atom $pairs) (cons-atom $t (pairs-terms (cdr-atom $pairs))))))
(= (subst-hyps $hyps $bind)
   (if (== $hyps ()) ()
       (case (car-atom $hyps)
         (((hy $h (excl $ys $pairs))
           (cons-atom (hy $h (excl $ys (subst-pairs $pairs $bind))) (subst-hyps (cdr-atom $hyps) $bind)))))))
(= (subst-pairs $pairs $bind)
   (if (== $pairs ()) () (let ($t $p) (car-atom $pairs) (cons-atom ((csubst $t $bind) $p) (subst-pairs (cdr-atom $pairs) $bind)))))

(= (cond-eqn-theorem $f $e)
   (let* (($bs (eqn-binders $e)) ($tbs (type-binders $bs))
          ($pf (cases-proof cond $f (term-todo $bs) (lhs-args $e) (eqn-rhs $e) (hyp-list $bs) (hyp-names $bs) (stmt-ctx $tbs))))
     (case $pf
       (((stuck $why) (format-args "(** {} not proved here: {} **)
" ((nm (eqn-name $e)) $why)))
        ((proof $lines) (format-args "(** {}: stated under the hypotheses that earlier patterns do not apply; proved by cases. **)
Theorem {} : {}.
{}
{}Qed.
" ((nm (eqn-name $e)) (egal (eqn-name $e)) (statement-text $e) (stmt-intros $tbs ()) $lines)))))))

(= (cases-proof $mode $f $todo $args $rhs $hyps $hnames $ctx)
   (if (== $todo ()) (cases-leaf $mode $f $args $rhs $hyps $hnames $ctx)
   (case (car-atom $todo)
     (((ih $x) (prepend-proof (format-args "assume IH_{}. " ($x)) (cases-proof $mode $f (cdr-atom $todo) $args $rhs $hyps $hnames $ctx)))
      ((tv $x $T)
       (if (hyp-needs-split $hyps $x) (split-var $mode $f $x $T (cdr-atom $todo) $args $rhs $hyps $hnames $ctx)
           (prepend-proof (format-args "let {}. assume H_{}: {} :e {}. " ($x $x $x (render $T ())))
             (cases-proof $mode $f (cdr-atom $todo) $args $rhs $hyps $hnames
               (cons-atom ($x (format-args "H_{}" ($x))) (cons-atom ((ty $x) $T) $ctx))))))))))
; ---- the type of a function whose result type depends on its arguments ----
(= (fn-type $f)
   (let $found (collapse (match &self (LeanFunctionType $f $T) $T)) (if (== $found ()) None (car-atom $found))))
(= (type-binders-of $T $i)
   (case $T
     (((pi $x $A $B) (cons-atom ($x $A) (type-binders-of $B (+ $i 1))))
      ((arrow $A $B) (cons-atom ((format-args "a{}" ($i)) $A) (type-binders-of $B (+ $i 1))))
      ($_ ()))))
(= (type-result-of $T)
   (case $T (((pi $x $A $B) (type-result-of $B)) ((arrow $A $B) (type-result-of $B)) ($_ $T))))
(= (dep-typed $f)
   (let $T (fn-type $f)
     (if (== $T None) False
         (let $R (type-result-of $T) (dep-mentions $R (type-binders-of $T 0))))))
; Only value arguments count: a result type that mentions a type parameter
; (Option α) is the ordinary polymorphic case.
(= (dep-mentions $R $bs)
   (if (== $bs ()) False
       (let ($x $A) (car-atom $bs)
         (if (is-sort-term $A) (dep-mentions $R (cdr-atom $bs))
             (if (mentions $R $x) True (dep-mentions $R (cdr-atom $bs)))))))
(= (is-sort-term $A)
   (if (== (get-metatype $A) Expression) (if (== (car-atom $A) sort) True (== $A (prop))) False))
; f's value lies in its type, by cases on the arguments its equations
; distinguish; each case is the equation's right side, typed.
(= (dep-in-theorem $f)
   (let* (($T (fn-type $f)) ($bs (type-binders-of $T 0)) ($R (type-result-of $T))
          ($xs (map-atom $bs $b (car-atom $b))) ($args (map-atom $xs $x (var $x)))
          ($eqns (eqn-hyps (fn-thms $f) $args))
          ($pf (cases-proof typing $f (bind-todo $bs) $args $R $eqns () ())))
     (case $pf
       (((stuck $w) (format-args "(** {}: its type not proved here: {} **)
" ((nm $f) $w)))
        ((proof $l) (format-args "Theorem {}_In : {}{} {} :e {}.
{}Qed.
{}" ((egal $f) (join "" (map-atom $bs $b (format-args "forall {} :e {}, " ((car-atom $b) (render (car-atom (cdr-atom $b)) ())))))
   (egal $f) (join " " $xs) (render $R ()) $l (canonical-theorem $f $bs $xs $R))))))))
; A decision procedure read from its definition is the canonical element of
; Decidable p, since that type has one element (Lean_Decidable_unique).
(= (canonical-theorem $f $bs $xs $R)
   (case $R
     (((app Decidable ($P))
       (let $ctx (bind-ctx $bs)
         (format-args "Theorem {}_canonical : {}{} {} = Lean_DecCanon {}.
{}exact Lean_Decidable_unique {} {} ({} {}) ({}_In {}).
Qed.
" ((egal $f) (join "" (map-atom $bs $b (format-args "forall {} :e {}, " ((car-atom $b) (render (car-atom (cdr-atom $b)) ())))))
   (egal $f) (join " " $xs) (render $P ())
   (join "" (map-atom $bs $b (format-args "let {}. assume H_{}: {} :e {}. " ((car-atom $b) (car-atom $b) (car-atom $b) (render (car-atom (cdr-atom $b)) ())))))
   (render $P ()) (typ $P () $ctx) (egal $f) (join " " $xs) (egal $f) (join " " (map-atom $xs $x (format-args "{} H_{}" ($x $x))))))))
      ($_ ""))))
(= (fn-canonical-theorem $f)
   (let* (($T (fn-type $f)) ($bs (type-binders-of $T 0)))
     (canonical-theorem $f $bs (map-atom $bs $b (car-atom $b)) (type-result-of $T))))
(= (bind-ctx $bs)
   (if (== $bs ()) ()
       (let ($x $T) (car-atom $bs) (cons-atom ($x (format-args "H_{}" ($x))) (cons-atom ((ty $x) $T) (bind-ctx (cdr-atom $bs)))))))
(= (bind-todo $bs)
   (if (== $bs ()) () (cons-atom (tv (car-atom (car-atom $bs)) (car-atom (cdr-atom (car-atom $bs)))) (bind-todo (cdr-atom $bs)))))
(= (eqn-hyps $thms $args)
   (if (== $thms ()) ()
       (let* (($t (car-atom $thms)) ($e (eqn-of $t)))
         (cons-atom (hy $t (excl () (zip-pairs $args (lhs-args $e)))) (eqn-hyps (cdr-atom $thms) $args)))))
(= (zip-pairs $ts $ps)
   (if (== $ts ()) () (cons-atom ((car-atom $ts) (car-atom $ps)) (zip-pairs (cdr-atom $ts) (cdr-atom $ps)))))

(= (prepend-proof $text $pf)
   (case $pf (((proof $l) (proof (format-args "{}{}" ($text $l)))) ($_ $pf))))

; Case analysis of x : T, by the family's induction (or, for the main member
; of a nested block, its case analysis), one block per constructor.
(= (split-var $mode $f $x $T $rest $args $rhs $hyps $hnames $ctx)
   (case $T
     (((app $F $ps)
       (let* (($cs (constructors-of $F)) ($n (length-of $cs))
              ($cases (split-cases $mode $f $x $F $ps $cs 0 $rest $args $rhs $hyps $hnames $ctx)))
         (case $cases
           (((stuck $w) (stuck $w))
            ($_ (proof (format-args "apply {}_{}{}.
{}" ((egal $F) (if (is-block $F) "cases" "ind") (join-sp (render-all $ps ())) $cases))))))))
      ($_ (stuck "a case analysis of a variable whose type is not a family")))))
(= (split-cases $mode $f $x $F $ps $cs $k $rest $args $rhs $hyps $hnames $ctx)
   (if (== $cs ()) ""
   (let* (($c (car-atom $cs)) ($K (ctor-name $c)) ($Ts (ctor-field-types $K $ps)) ($fs (ctor-fields $c))
          ($vs (let $js (range-from 0 (length-of $Ts)) (map-atom $js $j (format-args "{}_{}" ($x $j)))))
          ($node (app $K (append-lists $ps (map-atom $vs $v (var $v)))))
          ($bind (($x $node)))
          ($todo (append-lists (field-todo $vs $Ts)
                   (append-lists (if (is-block $F) () (ih-todo $vs $fs)) $rest)))
          ($pf (cases-proof $mode $f $todo (csubst-all $args $bind) (csubst $rhs $bind) (subst-hyps $hyps $bind) $hnames $ctx))
          ($more (split-cases $mode $f $x $F $ps (cdr-atom $cs) (+ $k 1) $rest $args $rhs $hyps $hnames $ctx)))
     (case $pf
       (((stuck $w) (stuck $w))
        ((proof $l)
         (case $more
           (((stuck $w) (stuck $w))
            ($_ (format-args "{ {}}
{}" ($l $more)))))))))))
(= (field-todo $vs $Ts)
   (if (== $vs ()) () (cons-atom (tv (car-atom $vs) (car-atom $Ts)) (field-todo (cdr-atom $vs) (cdr-atom $Ts)))))
(= (ih-todo $vs $fs)
   (if (== $vs ()) ()
       (if (is-rec (car-atom $fs)) (cons-atom (ih (car-atom $vs)) (ih-todo (cdr-atom $vs) (cdr-atom $fs)))
           (ih-todo (cdr-atom $vs) (cdr-atom $fs)))))

; A case: assume the hypotheses; one an earlier pattern matches is refuted,
; otherwise the equation holds by the split.
(= (cases-leaf typing $f $args $R $eqns $hnames $ctx)
   (case (first-match $eqns)
     (((hit $h $ys $pairs $b)
       (let $e (eqn-of $h)
         (proof (format-args "rewrite {}{}.
exact {}.
" ((egal $h) (join-sp (split-inst-args (eqn-binders $e) $b $ctx ())) (typ-at (csubst (eqn-rhs $e) $b) $R () $ctx))))))
      ($_ (stuck "a case no equation covers")))))
(= (cases-leaf cond $f $args $rhs $hyps $hnames $ctx)
   (let $intro (join "" (map-atom $hnames $h (format-args "assume {}. " ($h))))
     (let $hit (first-match $hyps)
       (case $hit
         (((hit $h $ys $pairs $b)
           (proof (format-args "{}apply FalseE. apply {}{}.
{}" ($intro $h (join-sp (hyp-inst-args $ys $b $ctx)) (join "" (map-atom $pairs $pr (pair-goal $pr)))))))
          ($_ (prepend-proof $intro (split-chain $f $args $rhs $ctx))))))))
(= (cases-leaf equation $f $args $rhs $patterns $hnames $ctx)
   (split-chain $f $args $rhs $ctx))
(= (first-match $hyps)
   (if (== $hyps ()) None
       (case (car-atom $hyps)
         (((hy $h (excl $ys $pairs))
           (let $b (pairs-match $pairs)
             (if (== $b fail) (first-match (cdr-atom $hyps)) (hit $h $ys $pairs $b))))))))
(= (hyp-inst-args $ys $b $ctx)
   (if (== $ys ()) ()
       (let* ((($y $T) (car-atom $ys)) ($v (lookup-var-term $y $b (var $y))))
         (cons-atom (render $v ()) (cons-atom (typ-at $v (fsubst $T $b) () $ctx) (hyp-inst-args (cdr-atom $ys) $b $ctx))))))
(= (pair-goal $pr)
   (let ($t $p) $pr (if (has-num $p) "rewrite LeanNum_0. reflexivity.
" "reflexivity.
")))

; Lean's arguments with numerals at patterns read as constructors.
(= (pattern-args $args) (if (== $args ()) () (cons-atom (pattern-deep (car-atom $args)) (pattern-args (cdr-atom $args)))))
(= (pattern-deep $t) (let $p (pattern-of $t) (case $p (((app $c $as) (app $c (pattern-args $as))) ($_ $p)))))

(= (split-inst-args $bs $inst $ctx $levels)
   (if (== $bs ()) ()
       (let $b (car-atom $bs)
         (case $b
           (((hyp $x $P) (cons-atom (hyp-proof (fsubst $P $inst)) (split-inst-args (cdr-atom $bs) $inst $ctx $levels)))
            ((type $x $l)
             (let* (($t (lookup-var-term $x $inst (var $x))) ($tt (render $t ())) ($pf (typ $t () $ctx)))
               (if (or (== $l 0) (member-term $l $levels))
                   (cons-atom $tt (cons-atom $pf (split-inst-args (cdr-atom $bs) $inst $ctx $levels)))
                   (cons-atom $l (cons-atom (format-args "H_{}" ($l)) (cons-atom $tt (cons-atom $pf
                     (split-inst-args (cdr-atom $bs) $inst $ctx (cons-atom $l $levels)))))))))
            ((sort $x $l)
             (let* (($t (lookup-var-term $x $inst (var $x))) ($tt (render $t ())) ($pf (typ $t () $ctx)))
               (if (member-term $l $levels)
                   (cons-atom $tt (cons-atom $pf (split-inst-args (cdr-atom $bs) $inst $ctx $levels)))
                   (cons-atom $l (cons-atom (format-args "H_{}" ($l)) (cons-atom $tt (cons-atom $pf
                     (split-inst-args (cdr-atom $bs) $inst $ctx (cons-atom $l $levels)))))))))
            ((term $x $T)
             (let $t (lookup-var-term $x $inst (var $x))
               (cons-atom (render $t ()) (cons-atom (typ-at $t (fsubst $T $inst) () $ctx)
                 (split-inst-args (cdr-atom $bs) $inst $ctx $levels))))))))))

; Terms equal up to the names of bound variables.
(= (alpha-eq $a $b $env)
   (case $a
     (((var $x) (case $b (((var $y) (== (lookup-var-term $x $env (var $x)) (var $y))) ($_ False))))
      ((lam $x $T $p) (case $b (((lam $y $U $q) (if (alpha-eq $T $U $env) (alpha-eq $p $q (cons-atom ($x (var $y)) $env)) False)) ($_ False))))
      ((pi $x $T $p) (case $b (((pi $y $U $q) (if (alpha-eq $T $U $env) (alpha-eq $p $q (cons-atom ($x (var $y)) $env)) False)) ($_ False))))
      ((app $c $as) (case $b (((app $d $bs) (if (== $c $d) (alpha-eq-list $as $bs $env) False)) ($_ False))))
      ((apv $f $as) (case $b (((apv $g $bs) (if (alpha-eq $f $g $env) (alpha-eq-list $as $bs $env) False)) ($_ False))))
      ((arrow $A $B) (case $b (((arrow $C $D) (if (alpha-eq $A $C $env) (alpha-eq $B $D $env) False)) ($_ False))))
      ($_ (== $a $b)))))
(= (alpha-eq-list $as $bs $env)
   (if (== $as ()) (== $bs ())
       (if (== $bs ()) False
           (if (alpha-eq (car-atom $as) (car-atom $bs) $env) (alpha-eq-list (cdr-atom $as) (cdr-atom $bs) $env) False))))

(= (chain $t $target $ctx $n)
   (if (alpha-eq $t $target ()) "reflexivity.
"
   (if (== $n 0) (stuck "too many steps")
   (let $r (find-case-redex $t)
     (if (== $r None) (stuck (format-args "the left side stops at {}" ((render $t ()))))
       (case (case-redex-step $r $ctx)
         (((step $new $ls)
           (let $rest (chain (replace-term $t $r $new) $target $ctx (- $n 1))
             (case $rest (((stuck $w) (stuck $w)) ($_ (format-args "{}
{}" ((join "
" $ls) $rest)))))))
          ((unfold $from $to $ls)
           (let $rest (chain (replace-term $t $from $to) (replace-term $target $from $to) $ctx (- $n 1))
             (case $rest (((stuck $w) (stuck $w)) ($_ (format-args "{}
{}" ((join "
" $ls) $rest)))))))
          ((stuck $w) (stuck $w)))))))))

(= (find-case-redex $t)
   (case $t
     (((apv $f $args)
       (let $inner (find-case-redex-list (cons-atom $f $args))
         (if (== $inner None) (if (is-binding $t) None (case $f (((lam $x $T $b) $t) ($_ None)))) $inner)))
      ((app $c $args)
       (let $inner (find-case-redex-list $args)
         (if (== $inner None) (if (is-cases-on $c) (if (cases-major-ready $c $args) $t None) None) $inner)))
      ($_ None))))
(= (find-case-redex-list $ts)
   (if (== $ts ()) None
       (let $r (find-case-redex (car-atom $ts)) (if (== $r None) (find-case-redex-list (cdr-atom $ts)) $r))))
(= (cases-major-ready $c $args)
   (let $major (nth $args (+ (param-count (cases-family $c)) 1))
     (case $major (((num $k) True) ((app $K $as) (is-ctor $K)) ($_ False)))))

(= (case-redex-step $r $ctx)
   (case $r
     (((apv $f $as) (beta-step-ctx $r $ctx))
      ((app $c $args)
       (let $major (nth $args (+ (param-count (cases-family $c)) 1))
         (case $major
           (((num $k)
             (if (== $k 0) (unfold (num 0) (app Nat.zero ()) ("rewrite LeanNum_0."))
                 (unfold (num $k) (app Nat.succ ((num (- $k 1))))
                   (unfold-num-lines $k))))
            ($_ (cases-step-ctx $c $args $ctx)))))))))


; After a case analysis's iota, its minor is applied to the fields and the
; recursive results: beta at once, so that the recursive results (unused by a
; case analysis) are never reduced themselves.
(= (iota-then-betas $t $line $ctx)
   (let $r (betas $t $ctx () (case $t (((apv $f $as) (length-of $as)) ($_ 0))))
     (case $r (((done $u $ls) (step $u (cons-atom $line $ls)))))))
; Beta for the k arguments the minor was given, and no further: a binding in
; the minor's body waits for its value.
(= (betas $t $ctx $acc $k)
   (if (== $k 0) (done $t $acc)
   (case $t
     (((apv (lam $x $T $b) $args)
       (case (beta-step-ctx $t $ctx)
         (((step $u $ls) (betas $u $ctx (append-lists $acc (written-beta $t $ls)) (- $k 1))))))
      ($_ (done $t $acc))))))
(= (beta-step-ctx $r $ctx)
   (case $r
     (((apv (lam $x $T $b) $args)
       (let* (($v (car-atom $args)) ($body (csubst $b (($x $v)))) ($rest (cdr-atom $args)))
         (step (if (== $rest ()) $body (apv $body $rest))
           ((format-args "rewrite beta {} {} {} {}." ((render $T ()) (meta-fun-text $x $b ()) (render $v ()) (typ-at $v $T () $ctx))))))))))

(= (cases-step-ctx $c $args $ctx)
   (let* (($F (cases-family $c)) ($np (param-count $F)) ($ps (take-n $args $np))
          ($rest (drop-n $args (+ $np 1))) ($major (car-atom $rest)) ($minors (cdr-atom $rest)))
     (case $major
       (((app $K $kargs)
         (let* (($cs (constructors-of $F)) ($k (ctor-index-in $cs $K 0)) ($fields (drop-n $kargs $np))
                ($motive (nth $args $np)) ($R (motive-of $motive)) ($elim (has-cases-eliminator $F))
                ($minor (if $elim (nth $minors $k) (wrap-minor $F $ps $R (nth $minors $k) $k)))
                ($ihs (if $elim () (ih-terms $c $ps $motive $minors $fields (ctor-fields (nth $cs $k)))))
                ($all (append-lists $fields $ihs)))
           (iota-then-betas (if (== $all ()) $minor (apv $minor $all))
             (format-args "rewrite {}_{}{}{}{}{}." ((egal $F) (if $elim "casesOn_iota" "iota") $k (join-sp (render-all $ps ()))
                (join-sp (render-all (if $elim $minors (wrap-minors $F $ps $R $minors 0)) ()))
                (join-sp (typ-fields-at $fields (ctor-field-types $K $ps) () $ctx))))
             $ctx)))))))

; ---- equations ----

(= (fn-thms $f) (car-atom (collapse (match &self (LeanFunction $f $thms) $thms))))
(= (proj-info $f)
   (let $found (collapse (match &self (LeanProjection $f $S $ctor $i $np) (proj $S $ctor $i $np)))
     (if (== $found ()) None (car-atom $found))))
(= (is-projection $f) (if (== (proj-info $f) None) False True))
(= (cases-family $c)
   (let $found (collapse (match &self (LeanCasesOn $c $F) $F))
     (if (== $found ()) None (car-atom $found))))
(= (is-cases-on $c) (if (== (cases-family $c) None) False True))
(= (prop-fam $c)
   (let $found (collapse (match &self (LeanFamily (Family $c $ps $is Prop $cs) $u $e $k) True))
     (if (== $found ()) False True)))
(= (intrinsic $f)
   (if (not (or (== $f Quot) (or (== $f Quot.mk) (== $f Quot.lift)))) None
   (let $found (collapse (match &self (LeanIntrinsic $f $kind $binders $result) (primitive $kind $binders $result)))
     (if (== (length-of $found) 1)
         (let $entry (car-atom $found)
           (case $entry
             (((primitive $kind $bs $R)
               (if (or (and (== $f Quot) (== $kind type))
                       (or (and (== $f Quot.mk) (== $kind constructor))
                           (and (== $f Quot.lift) (== $kind lift)))) $entry None))))) None))))
(= (is-intrinsic $f) (not (== (intrinsic $f) None)))
(= (intrinsic-value $f)
   (case (intrinsic $f) (((primitive type $bs $R) True) ((primitive constructor $bs $R) True) ($_ False))))
(= (intrinsic-binders $f) (case (intrinsic $f) (((primitive $kind $bs $R) $bs))))
(= (intrinsic-params $f) (map-atom (intrinsic-binders $f) $b (var (binder-name $b))))
(= (intrinsic-call-args $f)
   (map-atom (intrinsic-binders $f) $b
     (case $b (((hyp $x $P) (proof)) ($_ (var (binder-name $b)))))))
(= (is-function $f)
   (if (is-intrinsic $f) True
       (let $found (collapse (match &self (LeanFunction $f $thms) $f)) (if (== $found ()) False True))))
(= (eqn-of $thm)
   (case (car-atom (collapse (match &self (LeanEquation $thm $bs $ty $l $r) (eqn $thm $bs $ty $l $r))))
     (((eqn $n $bs $ty $l $r) (let $r2 (norm-term $r) (eqn $n $bs $ty $l $r2))))))
(= (eqn-name $e) (case $e (((eqn $n $bs $ty $l $r) $n))))
(= (eqn-binders $e) (case $e (((eqn $n $bs $ty $l $r) $bs))))
(= (eqn-type $e) (case $e (((eqn $n $bs $ty $l $r) $ty))))
(= (eqn-lhs $e) (case $e (((eqn $n $bs $ty $l $r) $l))))
(= (eqn-rhs $e) (case $e (((eqn $n $bs $ty $l $r) $r))))
(= (lhs-args $e) (case (eqn-lhs $e) (((app $f $args) $args))))
;; ---- inaccessible arguments ----
; An argument whose declared type is an indexed family at earlier arguments
; determines them: d : Deriv a b forces a and b.  Lean's equations show a
; forced argument as an inaccessible pattern, the constructor's index there;
; it is not matched.  The reading takes it as a variable, so the equation
; holds at every value of it, and Lean's is its instance at the indices.  The
; equation's type stays Lean's, at the constructor's indices: the recursor's
; motive there.
; A proof argument is never matched (proofs are irrelevant), so its type
; forces nothing: h : x + 1 <= fuel leaves fuel a pattern.
(= (lean-eqns-of $f) (let $thms (fn-thms $f) (unforce-eqns $f (map-atom $thms $thm (eqn-of $thm)))))
(= (forced-positions $f $eqs)
   (let $T (fn-type $f)
     (if (== $T None) () (let $bs (type-binders-of $T 0) (forced-in $bs $bs $eqs)))))
(= (forced-in $bs $all $eqs)
   (if (== $bs ()) ()
       (union-names
         (if (proof-everywhere $eqs (binder-pos (car-atom (car-atom $bs)) $all 0)) () (forced-by (car-atom $bs) $all))
         (forced-in (cdr-atom $bs) $all $eqs))))
(= (proof-everywhere $eqs $i)
   (if (== $eqs ()) True
       (let $as (lhs-args (car-atom $eqs))
         (if (< $i (length-of $as))
             (if (== (nth $as $i) (proof)) (proof-everywhere (cdr-atom $eqs) $i) False)
             False))))
(= (forced-by $b $all)
   (let ($x $A) $b
     (case $A
       (((app $F $args)
         (let $q (declared-index-count $F)
           (if (== $q 0) () (index-var-positions (drop-n $args (- (length-of $args) $q)) $all))))
        ($_ ())))))
(= (declared-index-count $F)
   (let $found (collapse (match &self (LeanFamily (Family $F $ps (indices $is) $s $cs) $u $e $k) $is))
     (if (== $found ()) 0 (length-of (car-atom $found)))))
(= (index-var-positions $is $all)
   (if (== $is ()) ()
       (let $rest (index-var-positions (cdr-atom $is) $all)
         (case (car-atom $is)
           (((var $y) (let $p (binder-pos $y $all 0) (if (< $p 0) $rest (cons-atom $p $rest))))
            ($_ $rest))))))
(= (binder-pos $y $bs $i)
   (if (== $bs ()) -1 (let ($x $A) (car-atom $bs) (if (== $x $y) $i (binder-pos $y (cdr-atom $bs) (+ $i 1))))))
(= (unforce-eqns $f $eqs)
   (let $P (forced-positions $f $eqs)
     (if (== $P ()) $eqs (map-atom $eqs $e (unforce-eqn $f $P $e)))))
(= (unforce-eqn $f $P $e)
   (case $e
     (((eqn $n $bs $ty (app $g $args) $r)
       (let $args2 (unforce-args $args $P 0)
         (if (== $args2 $args) $e (unforce-eqn-at $f $P $e $args2)))))))
(= (unforce-eqn-at $f $P $e $args2)
   (case $e
     (((eqn $n $bs $ty (app $g $args) $r)
       (let* (
              ($T (fn-type $f))
              ($dbs (type-binders-of $T 0))
              ($new (forced-binders $P $args $args2 (inst-binder-types $dbs $args2 ()))))
         (eqn $n (append-lists $bs $new) $ty (app $g $args2) $r))))))
(= (forced-name $i) (format-args "v_forced{}" ($i)))
(= (unforce-args $args $P $i)
   (if (== $args ()) ()
       (cons-atom (if (forced-pattern-at $P $i (car-atom $args)) (var (forced-name $i)) (car-atom $args))
                  (unforce-args (cdr-atom $args) $P (+ $i 1)))))
(= (forced-pattern-at $P $i $a) (if (member-term $i $P) (not (is-fvar $a)) False))
(= (forced-binders $P $args $args2 $Ts)
   (forced-binders-at $P $args $Ts 0))
(= (forced-binders-at $P $args $Ts $i)
   (if (== $args ()) ()
       (let $rest (forced-binders-at $P (cdr-atom $args) (cdr-atom $Ts) (+ $i 1))
         (if (forced-pattern-at $P $i (car-atom $args)) (cons-atom (term (forced-name $i) (car-atom $Ts)) $rest) $rest))))

; The equations a function is read by: Lean's, or, for nested patterns and
; patterns at several arguments, the equations of one split (see below).
; (Pure: adding atoms to &self would make it a dynamic space, which the
; loaded declarations are not part of.)
(= (eqns-of $f)
   (let* (($l (lean-eqns-of $f)) ($s (split-eqns $f $l))) (if (== $s None) $l $s)))
(= (is-split $f) (if (== (split-eqns $f (lean-eqns-of $f)) None) False True))

(= (app-head $t) (case $t (((app $c $args) $c) ($_ None))))
(= (app-args $t) (case $t (((app $c $args) $args) ($_ ()))))

; A pattern: the literal 0 is the constructor Nat.zero.
(= (calls-self $t $f) (if (== (fns-in-all $t) ()) False (member-term $f (fns-in-all $t))))
(= (fns-in-all $t)
   (case $t
     (((app $c $args) (if (is-library-head $c) (fns-in-all-list $args)
                         (union-names (cons-atom $c ()) (fns-in-all-list $args))))
      ((apv $g $args) (fns-in-all-list (cons-atom $g $args)))
      ((lam $x $T $b) (fns-in-all-list ($T $b)))
      ((arrow $A $B) (fns-in-all-list ($A $B)))
      ((pi $y $A $B) (fns-in-all-list ($A $B)))
      ((canon $P) (fns-in-all $P))
      ($_ ()))))
(= (fns-in-all-list $ts) (if (== $ts ()) () (union-names (fns-in-all (car-atom $ts)) (fns-in-all-list (cdr-atom $ts)))))

(= (pattern-of $t)
   (case $t (((num $k) (if (== $k 0) (app Nat.zero ()) (app Nat.succ ((num (- $k 1)))))) ($_ $t))))

; Positions where some equation has a pattern rather than a variable.
(= (pattern-positions $eqs $i $n)
   (if (>= $i $n) ()
       (if (any-pattern-at $eqs $i)
           (cons-atom $i (pattern-positions $eqs (+ $i 1) $n))
           (pattern-positions $eqs (+ $i 1) $n))))

; A proof argument (proof) is irrelevant: not a pattern.
(= (any-pattern-at $eqs $i)
   (if (== $eqs ()) False
       (let $a (nth (lhs-args (car-atom $eqs)) $i)
         (if (or (is-fvar $a) (== $a (proof))) (any-pattern-at (cdr-atom $eqs) $i) True))))

(= (all-vars $ts) (if (== $ts ()) True (if (is-fvar (car-atom $ts)) (all-vars (cdr-atom $ts)) False)))
(= (all-vars-or-proofs $ts) (if (== $ts ()) True (if (or (is-fvar (car-atom $ts)) (== (car-atom $ts) (proof))) (all-vars-or-proofs (cdr-atom $ts)) False)))

(= (family-of-ctor $c) (case (ctor-owner $c) (((owner $fam $ctor) $fam))))
(= (ctor-index-in $cs $c $i)
   (if (== $cs ()) -1 (if (== (ctor-name (car-atom $cs)) $c) $i (ctor-index-in (cdr-atom $cs) $c (+ $i 1)))))
(= (param-count $fam) (length-of (params-of $fam)))

; The equation for constructor k, if any.
(= (eqn-for-ctor $eqs $m $c)
   (if (== $eqs ()) None
       (if (== (app-head (pattern-of (nth (lhs-args (car-atom $eqs)) $m))) $c) (car-atom $eqs)
           (eqn-for-ctor (cdr-atom $eqs) $m $c))))

; The shape of a function: (structural m fam eqs-in-ctor-order) | (direct eq) | (refused reason).
; A decision procedure is read from its definition when its equations are
; closed (Bool.decEq: one per pair of constructors, with proofs of closed
; propositions), or when it is another name for one that is.
(= (decision-by-definition $f)
   (if (== (fn-type $f) None) False
   (if (dep-has-typing $f) True
   (let $eqs (lean-eqns-of $f)
     (if (all-closed $eqs) True
         (if (== (length-of $eqs) 1)
             (case (eqn-rhs (car-atom $eqs))
               (((app $g $as) (if (all-vars $as) (if (is-function $g) (decision-by-definition $g) False) False))
                ($_ False)))
             False))))))
; A typing lemma proved in Egal by hand (proofs/functions/E_In.mgproof): its
; statement is generated from the function's declared type.
; Whether a function whose result type depends on its arguments has a typing
; lemma: proved by hand, by cases on closed equations, or as another name for
; one that has.
(= (dep-has-typing $f)
   (if (is-intrinsic $f) True
   (if (has-typing-proof $f) True
   (if (dep-structural $f) True
   (let $eqs (lean-eqns-of $f)
     (if (all-closed $eqs) True
         (if (== (length-of $eqs) 1)
             (case (eqn-rhs (car-atom $eqs))
               (((app $g $as) (if (is-function $g) (if (dep-typed $g) (dep-has-typing $g) True) False))
                ($_ False)))
             False)))))))
; A structural function whose result type depends on its arguments is typed
; by its recursor at the dependent motive (E_f_recIn).
(= (dep-structural $f)
   (if (is-function $f)
       (if (dep-typed $f) (case (shape-of-eqns $f) (((structural $m $F $eqs) True) ($_ False))) False)
       False))
(= (untyped-comment $f)
   (format-args "(** {}'s type, which depends on its arguments, is not proved here yet. **)
" ((nm $f))))
(= (has-typing-proof $f)
   (let $e (egal $f) (if (== (collapse (match &self (TypingProof $e) True)) ()) False True)))
(= (all-closed $eqs)
   (if (== $eqs ()) True (if (== (eqn-binders (car-atom $eqs)) ()) (all-closed (cdr-atom $eqs)) False)))

(= (shape-of $f)
   (if (is-intrinsic $f) (intrinsic $f)
   (if (is-subsingleton-rec $f) (subsingleton (rec-family $f))
   (if (is-projection $f) (projection-shape $f)
   (if (not (is-function $f))
       (let $why (collapse (match &self (LeanFunctionRefused $f $r) $r))
         (refused (if (== $why ()) "not exported with equations" (car-atom $why))))
   (if (has-hyp-eqns (lean-eqns-of $f))
       (let $direct (proof-input-direct $f)
         (if (not (== $direct None)) (direct $direct)
           (if (is-split $f) (shape-of-eqns $f) (refused "equations stated under hypotheses that are not read as one split"))))
       (shape-of-eqns $f)))))))
; A direct wrapper may have erased proof inputs. Its hypotheses must be
; exactly supplied by those input positions, and its full typing needs a
; checked proof file. Conditional equations without such inputs stay guarded.
(= (proof-input-direct $f)
   (if (not (has-typing-proof $f)) None
       (let $eqs (lean-eqns-of $f)
         (if (not (== (length-of $eqs) 1)) None
             (let* (($e (car-atom $eqs)) ($args (lhs-args $e))
                    ($types (inst-binder-types (type-binders-of (fn-type $f) 0) $args ())))
               (if (and (plain-proof-args $args)
                        (and (not (calls-self (eqn-rhs $e) $f))
                             (hypotheses-from-inputs (eqn-binders $e) $args $types))) $e None))))))
(= (plain-proof-args $args)
   (if (== $args ()) True
       (if (or (is-fvar (car-atom $args)) (== (car-atom $args) (proof)))
           (plain-proof-args (cdr-atom $args)) False)))
(= (proof-input-for $P $args $types)
   (if (or (== $args ()) (== $types ())) False
       (if (and (== (car-atom $args) (proof)) (alpha-eq $P (car-atom $types) ())) True
           (proof-input-for $P (cdr-atom $args) (cdr-atom $types)))))
(= (hypotheses-from-inputs $binders $args $types)
   (if (== $binders ()) True
       (case (car-atom $binders)
         (((hyp $name $P) (if (proof-input-for $P $args $types)
             (hypotheses-from-inputs (cdr-atom $binders) $args $types) False))
          ($_ (hypotheses-from-inputs (cdr-atom $binders) $args $types))))))
; ---- the large eliminator of a subsingleton proposition ----
; Lean lets a proposition with one constructor whose fields are proofs
; (Eq, And) eliminate into any sort (Elimination anySort).  With proofs
; irrelevant, eliminating a proof returns the minor premise at the fields.
(= (rec-family $f)
   (let $found (collapse (match &self (LeanRecursor $f $F) $F)) (if (== $found ()) None (car-atom $found))))
(= (subsingleton-family $F)
   (let $found (collapse (match &self (LeanFamily (Family $F $ps $is Prop (constructors $cs)) $u (Elimination anySort) $k) $cs))
     (if (== $found ()) False (== (length-of (car-atom $found)) 1))))
(= (is-subsingleton-rec $f)
   (let $F (rec-family $f) (if (== $F None) False (subsingleton-family $F))))
(= (subsingleton-recs $fs)
   (if (== $fs ()) ()
       (let $rest (subsingleton-recs (cdr-atom $fs))
         (if (is-subsingleton-rec (car-atom $fs)) (cons-atom (car-atom $fs) $rest) $rest))))
(= (subsingleton-field-count $F) (length-of (ctor-fields (car-atom (constructors-of $F)))))
(= (subsingleton-text $f $F)
   (let* (($np (param-count $F)) ($ni (index-count $F)) ($n (+ (+ $np 3) $ni)) ($m (+ $np 1))
          ($xs (vars-of $n "a")) ($k (subsingleton-field-count $F))
          ($val (if (== $k 0) (format-args "a{}" ($m))
                    (format-args "(a{} {})" ($m (join " " (map-atom (range-from 0 $k) $i "0")))))))
     (format-args "(** {}: {} is a proposition with one constructor that may eliminate into any sort; with proofs
    irrelevant, eliminating a proof returns the minor premise. **)
Definition {} : {} := fun {} => {}.
Theorem {}_eq : forall {}, {} {} = {}.
let {}. reflexivity.
Qed.
" ((nm $f) (nm $F) (subsingleton-name $f) (fun-type $n) (join " " $xs) $val (subsingleton-name $f) (join " " $xs)
   (subsingleton-name $f) (join " " $xs) $val (join " " $xs)))))
(= (subsingleton-step $g $F $args)
   (let* (($m (+ (param-count $F) 1)) ($minor (nth $args $m)) ($k (subsingleton-field-count $F))
          ($val (if (== $k 0) $minor (apv $minor (map-atom (range-from 0 $k) $i (proof))))))
     (step $val ((format-args "rewrite {}_eq {}." ((subsingleton-name $g) (join " " (render-all $args ()))))))))
(= (has-hyp-eqns $eqs) (if (== $eqs ()) False (if (has-hyp (eqn-binders (car-atom $eqs))) True (has-hyp-eqns (cdr-atom $eqs)))))
(= (shape-of-eqns $f)
   (let* (($eqs (eqns-of $f)) ($n (length-of (lhs-args (car-atom $eqs))))
          ($ps (pattern-positions $eqs 0 $n)))
     (if (== $ps ())
         (if (== (length-of $eqs) 1)
             (if (calls-self (eqn-rhs (car-atom $eqs)) $f)
                 (refused "a recursive equation without patterns (well-founded recursion)")
                 (direct (car-atom $eqs)))
             (refused "several equations without patterns"))
         (if (> (length-of $ps) 1) (refused "patterns at several arguments")
             (structural-shape $f $eqs (car-atom $ps))))))

; A data projection of an admitted structure: one constructor and no
; recursive fields. Proof fields retain their dependent guard types.
(= (projection-shape $f)
   (case (proj-info $f)
     (((proj $S $ctor $i $np)
       (if (not (is-family $S)) (refused (format-args "a projection of {}, which is not admitted" ((nm $S))))
           (let $cs (constructors-of $S)
             (if (not (== (length-of $cs) 1)) (refused "a projection of a family with several constructors")
                 (let $fs (ctor-fields (car-atom $cs))
                   (if (not (all-record-fields $fs)) (refused "a projection of a structure with recursive fields")
                       (if (is-guard (nth $fs $i)) (refused "a proof-field projection needs its guard elimination theorem")
                           (projection $S $ctor $i $np)))))))))))
(= (all-record-fields $fs)
   (if (== $fs ()) True
       (case (car-atom $fs)
         (((data $t) (all-record-fields (cdr-atom $fs)))
          ((guard $p) (all-record-fields (cdr-atom $fs))) ($_ False)))))

(= (structural-shape $f $eqs $m)
   (let* (($pat (pattern-of (nth (lhs-args (car-atom $eqs)) $m))) ($c0 (app-head $pat)))
     (if (== $c0 None) (refused "a pattern that is not a constructor")
     (if (not (is-ctor $c0)) (refused "a pattern that is not a constructor of an admitted family")
     (let* (($fam (family-of-ctor $c0)) ($cs (constructors-of $fam)))
       (if (not (== (length-of $cs) (length-of $eqs))) (refused "not one equation per constructor")
       (let $ordered (ordered-eqns $eqs $m $cs)
         (if (== $ordered None) (refused "not one equation per constructor")
         (let $why (check-structural $f $ordered $m $fam)
           (if (== $why ok) (structural $m $fam $ordered) (refused $why)))))))))))

(= (ordered-eqns $eqs $m $cs)
   (if (== $cs ()) ()
       (let* (($e (eqn-for-ctor $eqs $m (ctor-name (car-atom $cs))))
              ($rest (ordered-eqns $eqs $m (cdr-atom $cs))))
         (if (== $e None) None (if (== $rest None) None (cons-atom $e $rest))))))

; Each pattern is a constructor applied to its parameters and distinct field
; variables; the other arguments are variables; recursive calls pass the same
; variables and a recursive field at the pattern's position.
(= (check-structural $f $eqs $m $fam)
   (if (== $eqs ()) ok
       (let $why (check-eqn $f (car-atom $eqs) $m $fam)
         (if (== $why ok) (check-structural $f (cdr-atom $eqs) $m $fam) $why))))

(= (check-eqn $f $e $m $fam)
   (let* (($args (lhs-args $e)) ($pat (pattern-of (nth $args $m)))
          ($fields (drop-n (app-args $pat) (param-count $fam))))
     (if (not (all-vars $fields)) "a nested pattern"
     (if (not (all-vars-or-proofs (others $args $m 0))) "patterns at several arguments"
     (if (and (mentions-any (eqn-type $e) $fields) (not (dep-typed $f))) "a result type depending on the fields"
     (if (acc-types-read-fields $e $m (fn-accs $f $m) $fields) "an accumulator whose type depends on the fields"
         (check-calls $f (eqn-rhs $e) $args $m (rec-field-vars $pat $fam))))))))

(= (acc-types-read-fields $e $m $accs $fields)
   (if (== $accs ()) False
       (let $x (var-name (nth (lhs-args $e) (car-atom $accs)))
         (if (mentions-any (binder-type $x (eqn-binders $e)) $fields) True
             (acc-types-read-fields $e $m (cdr-atom $accs) $fields)))))

(= (others $args $m $i)
   (if (== $args ()) ()
       (if (== $i $m) (others (cdr-atom $args) $m (+ $i 1))
           (cons-atom (car-atom $args) (others (cdr-atom $args) $m (+ $i 1))))))

(= (mentions-any $t $vars)
   (if (== $vars ()) False (if (mentions $t (var-name (car-atom $vars))) True (mentions-any $t (cdr-atom $vars)))))

(= (mentions $t $x)
   (case $t
     (((var $y) (== $y $x))
      ((num $k) False)
      ((prop) False)
      ((proof) False)
      ((canon $P) (mentions $P $x))
      ((apv $f $args) (if (mentions $f $x) True (mentions-list $args $x)))
      ((lam $y $T $b) (if (mentions $T $x) True (if (== $y $x) False (mentions $b $x))))
      ((arrow $A $B) (if (mentions $A $x) True (mentions $B $x)))
      ((pi $y $A $B) (if (mentions $A $x) True (if (== $y $x) False (mentions $B $x))))
      ((app $c $args) (mentions-list $args $x)))))
(= (mentions-list $ts $x) (if (== $ts ()) False (if (mentions (car-atom $ts) $x) True (mentions-list (cdr-atom $ts) $x))))

; The recursive field variables of a pattern.
(= (rec-field-vars $pat $fam)
   (let* (($c (app-head $pat)) ($cs (constructors-of $fam))
          ($k (ctor-index-in $cs $c 0)) ($fs (ctor-fields (nth $cs $k)))
          ($vars (drop-n (app-args $pat) (param-count $fam))))
     (rec-vars $fs $vars)))
(= (rec-vars $fs $vars)
   (if (== $fs ()) ()
       (if (is-rec (car-atom $fs)) (cons-atom (car-atom $vars) (rec-vars (cdr-atom $fs) (cdr-atom $vars)))
           (rec-vars (cdr-atom $fs) (cdr-atom $vars)))))

(= (check-calls $f $t $args $m $recs)
   (case $t
     (((var $y) ok)
      ((num $k) ok)
      ((prop) ok)
      ((proof) ok)
      ((apv $g $as) (check-calls-list $f (cons-atom $g $as) $args $m $recs))
      ((lam $y $T $b) (check-calls-list $f ($T $b) $args $m $recs))
      ((arrow $A $B) ok)
      ((pi $y $A $B) ok)
      ((app $c $as)
       (if (== $c $f)
           (if (and (same-others-but $as $args $m (fn-accs $f $m) 0) (member-term (nth $as $m) $recs))
               (check-calls-list $f $as $args $m $recs)
               "a recursive call that is not structural")
           (check-calls-list $f $as $args $m $recs))))))
(= (check-calls-list $f $ts $args $m $recs)
   (if (== $ts ()) ok
       (let $why (check-calls $f (car-atom $ts) $args $m $recs)
         (if (== $why ok) (check-calls-list $f (cdr-atom $ts) $args $m $recs) $why))))

; Accumulators: positions other than the pattern where a recursive call
; passes another argument than the equation's own variable.
(= (fn-accs $f $m)
   (let* (($eqs (eqns-of $f)) ($found (accs-of-eqns $eqs $f $m)) ($n (arity-of $f)))
     (positions-in (range-from 0 $n) $found)))
(= (positions-in $ps $found)
   (if (== $ps ()) ()
       (let $rest (positions-in (cdr-atom $ps) $found)
         (if (member-term (car-atom $ps) $found) (cons-atom (car-atom $ps) $rest) $rest))))
(= (accs-of-eqns $eqs $f $m)
   (if (== $eqs ()) ()
       (union-names (accs-in (eqn-rhs (car-atom $eqs)) $f $m (lhs-args (car-atom $eqs)))
                    (accs-of-eqns (cdr-atom $eqs) $f $m))))
(= (accs-in $t $f $m $args)
   (case $t
     (((app $c $as)
       (let $inner (accs-in-list $as $f $m $args)
         (if (== $c $f) (union-names (diff-positions $as $args $m 0) $inner) $inner)))
      ((apv $g $as) (accs-in-list (cons-atom $g $as) $f $m $args))
      ((lam $x $T $b) (accs-in-list ($T $b) $f $m $args))
      ($_ ()))))
(= (accs-in-list $ts $f $m $args)
   (if (== $ts ()) () (union-names (accs-in (car-atom $ts) $f $m $args) (accs-in-list (cdr-atom $ts) $f $m $args))))
(= (diff-positions $as $args $m $i)
   (if (== $as ()) ()
       (let $rest (diff-positions (cdr-atom $as) (cdr-atom $args) $m (+ $i 1))
         (if (or (== $i $m) (== (car-atom $as) (car-atom $args))) $rest (cons-atom $i $rest)))))

(= (same-others $as $args $m $i)
   (if (== $as ()) True
       (if (== $i $m) (same-others (cdr-atom $as) (cdr-atom $args) $m (+ $i 1))
           (if (== (car-atom $as) (car-atom $args)) (same-others (cdr-atom $as) (cdr-atom $args) $m (+ $i 1)) False))))

(= (same-others-but $as $args $m $accs $i)
   (if (== $as ()) True
       (if (or (== $i $m) (member-term $i $accs)) (same-others-but (cdr-atom $as) (cdr-atom $args) $m $accs (+ $i 1))
           (if (== (car-atom $as) (car-atom $args)) (same-others-but (cdr-atom $as) (cdr-atom $args) $m $accs (+ $i 1)) False))))

(= (member-term $t $ts) (if (== $ts ()) False (if (== (car-atom $ts) $t) True (member-term $t (cdr-atom $ts)))))

; The functions a function's equations apply.
(= (fn-deps $f)
   (union-names (proof-library-deps $f)
   (if (is-projection $f) ()
       (case (shape-of $f)
         (((subsingleton $F) ())
          ($_ (let $eqs (eqns-of $f) (deps-of-eqns $eqs $f))))))))
; Everything an equation's statement applies: its right side, its type and
; the types of its binders.
(= (deps-of-eqns $eqs $f)
   (if (== $eqs ()) ()
       (let $e (car-atom $eqs)
         (union-names (fns-in (eqn-rhs $e) $f)
           (union-names (fns-in (eqn-type $e) $f)
             (union-names (binder-deps (eqn-binders $e) $f) (deps-of-eqns (cdr-atom $eqs) $f)))))))
(= (binder-deps $bs $f)
   (if (== $bs ()) ()
       (union-names (case (car-atom $bs) (((term $x $t) (fns-in $t $f)) ((hyp $x $P) (fns-in $P $f)) ($_ ())))
                    (binder-deps (cdr-atom $bs) $f))))
(= (fns-in $t $f)
   (case $t
     (((var $y) ())
      ((num $k) ())
      ((prop) ())
      ((proof) ())
      ((apv $g $as) (fns-in-list (cons-atom $g $as) $f))
      ((lam $y $T $b) (fns-in-list ($T $b) $f))
      ((arrow $A $B) (fns-in-list ($A $B) $f))
      ((pi $y $A $B) (fns-in-list ($A $B) $f))
      ((app $c $as)
       (let $inner (fns-in-list $as $f)
         (if (or (is-library-head $c) (or (== $c $f) (or (is-ctor $c) (or (is-family $c) (is-cases-on $c))))) $inner (union-names (cons-atom $c ()) $inner))))
      ($_ ()))))
(= (fns-in-list $ts $f) (if (== $ts ()) () (union-names (fns-in (car-atom $ts) $f) (fns-in-list (cdr-atom $ts) $f))))
(= (union-names $xs $ys)
   (if (== $xs ()) $ys
       (if (member-term (car-atom $xs) $ys) (union-names (cdr-atom $xs) $ys)
           (cons-atom (car-atom $xs) (union-names (cdr-atom $xs) $ys)))))

; ---- canonical methods ----
; A method of the recursor, from the equation of its constructor: the
; arguments other than the pattern are a0, a1, ..; the pattern's fields are
; y0, y1, ..; the result of the recursive call on field i is r{i}.

(= (pos-name $p) (format-args "a{}" ($p)))
(= (field-name $i) (format-args "y{}" ($i)))
(= (ih-name $i) (format-args "r{}" ($i)))

(= (param-renames $args $m $p)
   (if (== $args ()) ()
       (if (or (== $p $m) (== (car-atom $args) (proof))) (param-renames (cdr-atom $args) $m (+ $p 1))
           (cons-atom ((var-name (car-atom $args)) (var (pos-name $p)))
                      (param-renames (cdr-atom $args) $m (+ $p 1))))))

(= (field-renames $vars $i)
   (if (== $vars ()) ()
       (cons-atom ((var-name (car-atom $vars)) (var (field-name $i)))
                  (field-renames (cdr-atom $vars) (+ $i 1)))))

(= (index-of-term $t $ts $i)
   (if (== $ts ()) -1 (if (== (car-atom $ts) $t) $i (index-of-term $t (cdr-atom $ts) (+ $i 1)))))

; Recursive calls of f become their results r{i}.
(= (acc-args $as $accs)
   (if (== $accs ()) () (cons-atom (nth $as (car-atom $accs)) (acc-args $as (cdr-atom $accs)))))

(= (calls-to-ihs $t $f $m $fvars)
   (case $t
     (((var $y) $t)
      ((num $k) $t)
      ((prop) $t)
      ((proof) $t)
      ((apv $g $as) (apv (calls-to-ihs $g $f $m $fvars) (calls-to-ihs-list $as $f $m $fvars)))
      ((lam $y $T $b) (lam $y (calls-to-ihs $T $f $m $fvars) (calls-to-ihs $b $f $m $fvars)))
      ((arrow $A $B) $t)
      ((pi $y $A $B) $t)
      ((app $c $as)
       (if (== $c $f)
           (let $accs (fn-accs $f $m)
             (if (== $accs ()) (var (ih-name (index-of-term (nth $as $m) $fvars 0)))
                 (apv (var (ih-name (index-of-term (nth $as $m) $fvars 0)))
                      (calls-to-ihs-list (acc-args $as $accs) $f $m $fvars))))
           (app $c (calls-to-ihs-list $as $f $m $fvars)))))))
(= (calls-to-ihs-list $ts $f $m $fvars)
   (if (== $ts ()) () (cons-atom (calls-to-ihs (car-atom $ts) $f $m $fvars) (calls-to-ihs-list (cdr-atom $ts) $f $m $fvars))))

(= (binder-type $x $bs)
   (if (== $bs ()) None
       (case (car-atom $bs)
         (((term $y $t) (if (== $y $x) $t (binder-type $x (cdr-atom $bs))))
          ((sort $y $l) (binder-type $x (cdr-atom $bs)))
          ((type $y $l) (binder-type $x (cdr-atom $bs)))
          ((hyp $y $p) (binder-type $x (cdr-atom $bs)))))))

; (cmethod (layers (ly name type) ..) body result-type)
(= (cmethod $f $e $m $fam)
   (let* (($args (lhs-args $e)) ($pat (pattern-of (nth $args $m)))
          ($fvars (drop-n (app-args $pat) (param-count $fam)))
          ($ren (append-lists (param-renames $args $m 0) (field-renames $fvars 0)))
          ($recs (rec-field-vars $pat $fam))
          ($body (fsubst (calls-to-ihs (eqn-rhs $e) $f $m $fvars) $ren))
          ($R (fsubst (eqn-type $e) $ren))
          ($accs (fn-accs $f $m))
          ($Ts (acc-types $e $accs $ren))
          ($flayers (field-layers $fvars 0 (eqn-binders $e) $ren))
          ($ilayers (if (dep-typed $f) (dep-ih-layers $f $m $accs $Ts $fvars $recs 0)
                        (ih-layers $fvars $recs 0 (arrows $Ts $R))))
          ($alayers (acc-layers $accs $Ts)))
     (cmethod (append-lists $flayers (append-lists $ilayers $alayers)) $body $R)))

(= (arrows $Ts $R) (if (== $Ts ()) $R (arrow (car-atom $Ts) (arrows (cdr-atom $Ts) $R))))
(= (acc-types $e $accs $ren)
   (if (== $accs ()) ()
       (cons-atom (fsubst (binder-type (var-name (nth (lhs-args $e) (car-atom $accs))) (eqn-binders $e)) $ren)
                  (acc-types $e (cdr-atom $accs) $ren))))
(= (acc-layers $accs $Ts)
   (if (== $accs ()) ()
       (cons-atom (ly (pos-name (car-atom $accs)) (car-atom $Ts) acc (car-atom $accs))
                  (acc-layers (cdr-atom $accs) (cdr-atom $Ts)))))
(= (accs-applied $head $names)
   (if (== $names ()) $head (format-args "({} {})" ($head (join " " $names)))))

(= (field-layers $vars $i $bs $ren)
   (if (== $vars ()) ()
       (cons-atom (ly (field-name $i) (fsubst (binder-type (var-name (car-atom $vars)) $bs) $ren) fld $i)
                  (field-layers (cdr-atom $vars) (+ $i 1) $bs $ren))))

(= (ih-layers $vars $recs $i $R)
   (if (== $vars ()) ()
       (if (member-term (car-atom $vars) $recs)
           (cons-atom (ly (ih-name $i) $R ih $i) (ih-layers (cdr-atom $vars) $recs (+ $i 1) $R))
           (ih-layers (cdr-atom $vars) $recs (+ $i 1) $R))))

; With a result type depending on the arguments, the result of the
; recursive call on field i lies in the type at that field: the product over
; the accumulators of the declared result at y_i.
(= (dep-ih-layers $f $m $accs $Ts $vars $recs $i)
   (if (== $vars ()) ()
       (let $rest (dep-ih-layers $f $m $accs $Ts (cdr-atom $vars) $recs (+ $i 1))
         (if (member-term (car-atom $vars) $recs)
             (cons-atom (ly (ih-name $i) (dep-pi $f $m $accs $Ts (var (field-name $i))) ih $i) $rest)
             $rest))))
(= (dep-pi $f $m $accs $Ts $t)
   (pis-of $accs $Ts (fsubst (pos-result $f) (((pos-name $m) $t)))))
(= (pis-of $accs $Ts $R)
   (if (== $accs ()) $R (pi (pos-name (car-atom $accs)) (car-atom $Ts) (pis-of (cdr-atom $accs) (cdr-atom $Ts) $R))))

(= (cm-layers $cm) (case $cm (((cmethod $ls $b $R) $ls))))
(= (cm-body $cm) (case $cm (((cmethod $ls $b $R) $b))))
(= (cm-result $cm) (case $cm (((cmethod $ls $b $R) $R))))

(= (ly-name $l) (case $l (((ly $n $t $kind $i) $n))))
(= (ly-type $l) (case $l (((ly $n $t $kind $i) $t))))
(= (ly-kind $l) (case $l (((ly $n $t $kind $i) $kind))))
(= (ly-index $l) (case $l (((ly $n $t $kind $i) $i))))

; The method as Egal text: its unapplied layers as set functions, the
; parameters and applied layers given by $sub.
(= (lam-text $layers $body $sub)
   (if (== $layers ()) (render $body $sub)
       (let $l (car-atom $layers)
         (format-args "(fun {} :e {} => {})"
           ((ly-name $l) (render (ly-type $l) $sub) (lam-text (cdr-atom $layers) $body (remove-key (ly-name $l) $sub)))))))

(= (pi-text $layers $R $sub)
   (if (== $layers ()) (render $R $sub)
       (let $l (car-atom $layers)
         (format-args "(Pi_ {} :e {}, {})"
           ((ly-name $l) (render (ly-type $l) $sub) (pi-text (cdr-atom $layers) $R (remove-key (ly-name $l) $sub)))))))

; ---- the structural definition ----

(= (pos-subst $pnames $p)
   (if (== $pnames ()) ()
       (cons-atom ((pos-name $p) (car-atom $pnames)) (pos-subst (cdr-atom $pnames) (+ $p 1)))))

(= (shape-m $s) (case $s (((structural $m $fam $eqs) $m))))
(= (shape-fam $s) (case $s (((structural $m $fam $eqs) $fam))))
(= (shape-eqs $s) (case $s (((structural $m $fam $eqs) $eqs))))

; The family's parameters at the pattern, as canonical terms.
(= (fam-params-c $f $s)
   (let* (($e (car-atom (shape-eqs $s))) ($args (lhs-args $e)) ($m (shape-m $s))
          ($pat (pattern-of (nth $args $m))))
     (fsubst-all (take-n (app-args $pat) (param-count (shape-fam $s))) (param-renames $args $m 0))))

(= (methods-text $f $s $sub)
   (let $eqs (shape-eqs $s)
     (join " " (methods-list $f $eqs (shape-m $s) (shape-fam $s) $sub 0))))
(= (methods-list $f $eqs $m $fam $sub $k)
   (if (== $eqs ()) ()
       (let $cm (cmethod $f (car-atom $eqs) $m $fam)
         (cons-atom (method-ref $f $k $m $cm $sub)
                    (methods-list $f (cdr-atom $eqs) $m $fam $sub (+ $k 1))))))

; ---- methods as named definitions ----
; Layer i of method k is a definition over the fixed parameters and the
; earlier layers (E_f_method{k}_{i}).  Its application lemma is one beta and
; its typing lemma one lam_Pi, so proofs cite names, not the method's text.
(= (method-name $f $k $i) (format-args "{}_method{}_{}" ((egal $f) $k $i)))
(= (fixed-positions $f $m)
   (let $accs (fn-accs $f $m) (fixed-pos (range-from 0 (arity-of $f)) $m $accs (eqns-of $f))))
(= (fixed-pos $ps $m $accs $eqs)
   (if (== $ps ()) ()
       (let* (($p (car-atom $ps)) ($rest (fixed-pos (cdr-atom $ps) $m $accs $eqs)))
         (if (or (== $p $m) (member-term $p $accs)) $rest
             (if (proof-everywhere $eqs $p) $rest (cons-atom $p $rest))))))
(= (method-ref $f $k $m $cm $sub)
   (if (== (cm-layers $cm) ()) (render (cm-body $cm) $sub)
       (applied-text (method-name $f $k 0) (map-atom (fixed-positions $f $m) $p (render (var (pos-name $p)) $sub)))))
(= (applied-text $head $args) (if (== $args ()) $head (format-args "({} {})" ($head (join " " $args)))))
(= (layer-names $ls) (map-atom $ls $l (ly-name $l)))
; The fixed parameters' binders and introductions: a type parameter is any set.
(= (fixed-binders-text $f $m $ps $famT)
   (join "" (map-atom $ps $p
     (if (== (nth (pos-kinds $f) $p) type) (format-args "forall {}, " ((pos-name $p)))
         (format-args "forall {} :e {}, " ((pos-name $p) (pos-type $f $p $m $famT ())))))))
(= (fixed-intros-text $f $m $ps $famT)
   (join "" (map-atom $ps $p
     (if (== (nth (pos-kinds $f) $p) type) (format-args "let {}. " ((pos-name $p)))
         (format-args "let {}. assume H{}: {} :e {}. " ((pos-name $p) $p (pos-name $p) (pos-type $f $p $m $famT ())))))))
(= (fixed-args-hyps $f $ps)
   (join "" (map-atom $ps $p
     (if (== (nth (pos-kinds $f) $p) type) (format-args " {}" ((pos-name $p))) (format-args " {} H{}" ((pos-name $p) $p))))))
(= (fixed-ctx $f $m $ps)
   (if (== $ps ()) ()
       (let* (($p (car-atom $ps)) ($rest (fixed-ctx $f $m (cdr-atom $ps))))
         (if (== (nth (pos-kinds $f) $p) type) $rest
             (let* (($e (car-atom (eqns-of $f))) ($x (var-name (nth (lhs-args $e) $p)))
                    ($ren (param-renames (lhs-args $e) $m 0)))
               (cons-atom ((pos-name $p) (format-args "H{}" ($p)))
                 (cons-atom ((ty (pos-name $p)) (fsubst (binder-type $x (eqn-binders $e)) $ren)) $rest)))))))

(= (methods-lift-text $f $s)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($eqs (shape-eqs $s))
          ($famT (render (app $fam (fam-params-c $f $s)) ())) ($ps (fixed-positions $f $m)))
     (methods-lift-list $f $eqs $m $fam $famT $ps 0)))
(= (methods-lift-list $f $eqs $m $fam $famT $ps $k)
   (if (== $eqs ()) ""
       (let* (($cm (cmethod $f (car-atom $eqs) $m $fam)) ($ls (cm-layers $cm)))
         (format-args "{}{}"
           ((if (== $ls ()) "" (layers-lift-text $f $k $ls $ls (cm-body $cm) (cm-result $cm) $m $famT $ps 0 ()))
            (methods-lift-list $f (cdr-atom $eqs) $m $fam $famT $ps (+ $k 1)))))))
; Layers from the last to the first, so that each definition follows the one it names.
(= (layers-lift-text $f $k $all $ls $body $R $m $famT $ps $i $before)
   (if (== $ls ()) ""
       (format-args "{}{}"
         ((layers-lift-text $f $k $all (cdr-atom $ls) $body $R $m $famT $ps (+ $i 1) (append-lists $before ((car-atom $ls))))
          (layer-lift-text $f $k $all $body $R $m $famT $ps $i $before (car-atom $ls) (cdr-atom $ls))))))
(= (layer-lift-text $f $k $all $body $R $m $famT $ps $i $before $l $after)
   (let* (($N (method-name $f $k $i)) ($z (ly-name $l)) ($T (render (ly-type $l) ()))
          ($params (append-lists (map-atom $ps $p (pos-name $p)) (layer-names $before)))
          ($nparams (length-of $params))
          ($next (if (== $after ()) (render $body ())
                     (applied-text (method-name $f $k (+ $i 1)) (append-lists $params ($z)))))
          ($head (applied-text $N $params))
          ($lets (join "" (map-atom $params $x (format-args "let {}. " ($x)))))
          ($ctx0 (fixed-ctx $f $m $ps))
          ($ctx (layer-ctx (append-lists $before ($l)) $ctx0))
          ($proof (if (== $after ()) (typ $body () $ctx)
                      (format-args "({}_In{}{} {} H{})"
                        ((method-name $f $k (+ $i 1)) (fixed-args-hyps $f $ps)
                         (join "" (map-atom $before $b (format-args " {} H{}" ((ly-name $b) (ly-name $b))))) $z $z))))
          ; A dependent result at the constructor is first rewritten to the
          ; body's own type.
          ($conv (if (== $after ()) (if (dep-typed $f) (convert-type $R $ctx 0 ()) None) None))
          ($lines (if (== $conv None) () (conv-lines $conv)))
          ($finish
           (if (== $lines ())
               (format-args "exact lam_Pi {} (fun {} => {}) (fun {} => {}) (fun {} H{} => {})." ($T $z (pi-text $after $R ()) $z $next $z $z $proof))
               (format-args "prove (fun {} :e {} => {}) :e {}.
apply lam_Pi {} (fun {} => {}) (fun {} => {}).
let {}. assume H{}: {} :e {}.
prove {} :e {}.
{}
exact {}." ($z $T $next (pi-text (cons-atom $l $after) $R ()) $T $z (pi-text $after $R ()) $z $next $z $z $z $T $next (render $R ()) (join "
" $lines) $proof)))))
     (format-args "Definition {} : {} := {}(fun {} :e {} => {}).
Theorem {}_ap : {}forall {} :e {}, {} {} = {}.
{}let {}. assume H: {} :e {}.
exact beta {} (fun {} => {}) {} H.
Qed.
Theorem {}_In : {}{}{} :e {}.
{}{}{}
Qed.
"
       ($N (fun-type $nparams) (if (== $params ()) "" (format-args "fun {} => " ((join " " $params)))) $z $T $next
        $N (if (== $params ()) "" (format-args "forall {}, " ((join " " $params)))) $z $T $head $z $next
        $lets $z $z $T
        $T $z $next $z
        $N (fixed-binders-text $f $m $ps $famT)
        (join "" (map-atom $before $b (format-args "forall {} :e {}, " ((ly-name $b) (render (ly-type $b) ())))))
        $head (pi-text (cons-atom $l $after) $R ())
        (fixed-intros-text $f $m $ps $famT)
        (join "" (map-atom $before $b (format-args "let {}. assume H{}: {} :e {}. " ((ly-name $b) (ly-name $b) (ly-name $b) (render (ly-type $b) ())))))
        $finish))))
(= (layer-ctx $ls $ctx)
   (if (== $ls ()) $ctx
       (let $l (car-atom $ls)
         (layer-ctx (cdr-atom $ls) (cons-atom ((ly-name $l) (format-args "H{}" ((ly-name $l)))) (cons-atom ((ty (ly-name $l)) (ly-type $l)) $ctx))))))

; "E_rec params methods", the recursor applied but for the major argument.
(= (rec-prefix $f $s $sub)
   (let* (($fam (shape-fam $s)) ($ps (render-all (fam-params-c $f $s) $sub)))
     (format-args "{}_rec{} {}" ((egal $fam) (if (== $ps ()) "" (format-args " {}" ((join " " $ps)))) (methods-text $f $s $sub)))))

(= (map-names $ps) (if (== $ps ()) () (cons-atom (pos-name (car-atom $ps)) (map-names (cdr-atom $ps)))))

(= (arity-of $f)
   (if (is-intrinsic $f) (length-of (intrinsic-binders $f))
   (case (proj-info $f)
     (((proj $S $ctor $i $np) (+ $np 1))
      ($_ (length-of (lhs-args (car-atom (eqns-of $f)))))))))
(= (fun-type $n) (if (== $n 0) "set" (format-args "set -> {}" ((fun-type (- $n 1))))))

(= (definition-text $f $s)
   (let* (($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0)))
     (case $s
       (((structural $m $fam $eqs)
         (format-args "Definition {} : {} := fun {} => {}.
" ((egal $f) (fun-type $n) (join " " $ps)
   (accs-applied (format-args "{} {}" ((rec-prefix $f $s $sub) (nth $ps $m)))
     (let $accs (fn-accs $f $m) (map-names $accs))))))
        ((direct $e)
         (let $ren (param-renames (lhs-args $e) -1 0)
           (if (== $n 0)
               (format-args "Definition {} : set := {}.
" ((egal $f) (render (eqn-rhs $e) ())))
               (format-args "Definition {} : {} := fun {} => {}.
" ((egal $f) (fun-type $n) (join " " $ps) (render (fsubst (eqn-rhs $e) $ren) $sub))))))))))

; ---- typing ----

(= (binder-kind $x $bs)
   (if (== $bs ()) term
       (case (car-atom $bs)
         (((type $y $l) (if (== $y $x) type (binder-kind $x (cdr-atom $bs))))
          ((sort $y $l) (if (== $y $x) type (binder-kind $x (cdr-atom $bs))))
          ((term $y $t) (if (== $y $x) (if (is-family-type $t) family term) (binder-kind $x (cdr-atom $bs))))
          ((hyp $y $p) (binder-kind $x (cdr-atom $bs)))))))
; A family of types (a motive, α → Sort u).  Its value is never computed with;
; a typing lemma takes it with its meaning, a function of the meta level.
(= (is-family-type $T)
   (case $T (((arrow $A $B) (family-end $B)) ((pi $x $A $B) (family-end $B)) ($_ False))))
(= (family-end $T)
   (case $T
     (((arrow $A $B) (family-end $B)) ((pi $x $A $B) (family-end $B))
      ; A predicate computes truth values and remains an ordinary function
      ; value. A family into Sort has a separate type-level meaning.
      ((prop) False) ($_ (is-sort-term $T)))))
(= (family-arity $T) (case $T (((arrow $A $B) (+ 1 (family-arity $B))) ((pi $x $A $B) (+ 1 (family-arity $B))) ($_ 0))))
(= (meaning-name $x) (format-args "{}_F" ($x)))
; The meaning of a family given as a function: the meta-level function.
(= (meta-render $t $sub)
   (case $t
     (((lam $x $T $b) (format-args "(fun {} => {})" ($x (meta-render-body $b (remove-key $x $sub)))))
      ($_ "UNDECIDED"))))
(= (meta-render-body $b $sub) (case $b (((lam $x $T $c) (meta-render $b $sub)) ($_ (render (beta-norm $b) $sub)))))

(= (kinds-of $args $bs)
   (if (== $args ()) ()
       (cons-atom (if (is-fvar (car-atom $args)) (binder-kind (var-name (car-atom $args)) $bs)
                      (if (== (car-atom $args) (proof)) proof term))
                  (kinds-of (cdr-atom $args) $bs))))

(= (pos-kinds $f)
   (if (is-intrinsic $f)
       (kinds-of (intrinsic-params $f) (intrinsic-binders $f))
   (case (proj-info $f)
     (((proj $S $ctor $i $np) (append-lists (repeat-kind type $np) (term)))
      ($_ (let $e (car-atom (eqns-of $f)) (kinds-of (lhs-args $e) (eqn-binders $e))))))))
(= (repeat-kind $k $n) (if (== $n 0) () (cons-atom $k (repeat-kind $k (- $n 1)))))

; A proof that the reading of t lies in the reading of its type; $ctx gives
; the proofs for variables.
(= (typ $t $sub $ctx)
   (case $t
     (((var $x) (lookup-var $x $ctx))
      ((num $k) (format-args "(LeanNum_In {} {})" ((num-arg $k) (num-natproof $k))))
      ((apv $f $args)
       (typ-apv (render $f $sub) (typ $f $sub $ctx) (type-of $f $ctx) $args $sub $ctx))
      ; A product of propositions is a proposition (impredicativity).
      ((pi $x $A $B)
       (let $hx (format-args "H{}" ($x))
         (format-args "(LeanPi_prop {} (fun {} => {}) (fun {} {} => {}))"
           ((render $A $sub) $x (render $B (remove-key $x $sub)) $x $hx
            (typ $B (remove-key $x $sub) (cons-atom ($x $hx) (cons-atom ((ty $x) $A) $ctx)))))))
      ((arrow $A $B)
       (format-args "(LeanPi_prop {} (fun ux => {}) (fun ux Hux => {}))"
         ((render $A $sub) (render $B $sub) (typ $B $sub $ctx))))
      ((lam $x $T $b)
       (let* (($hx (format-args "H{}" ($x)))
              ($ctx2 (cons-atom ($x $hx) (cons-atom ((ty $x) $T) $ctx)))
              ($sub2 (remove-key $x $sub)))
         (format-args "(lam_Pi {} (fun {} => {}) (fun {} => {}) (fun {} {} => {}))"
           ((render $T $sub) $x (render (type-of $b $ctx2) $sub2) $x (render $b $sub2) $x $hx (typ $b $sub2 $ctx2)))))
      ((app $c $args)
       (if (== $c (EgalLibrary proof-field))
           (format-args "(Lean_ProofField_prop {})" ((render (car-atom $args) $sub)))
       (if (is-ctor $c) (typ-ctor $c $args $sub $ctx)
           (if (prop-fam $c) (format-args "({}_Prop_prop {})" ((egal $c) (join " " (render-all $args $sub))))
               (if (is-cases-on $c) (typ-cases $c $args $sub $ctx)
                   (typ-fn $c $args $sub $ctx)))))))))

; Case analysis with a motive that does not depend on its value: the
; recursor's typing at that result, each minor typed at its Pi type.
(= (cases-parts $c $args)
   (let* (($F (cases-family $c)) ($np (param-count $F)) ($ps (take-n $args $np))
          ($motive (nth $args $np)) ($rest (drop-n $args (+ $np 1))))
     (parts $F $ps $motive (car-atom $rest) (cdr-atom $rest))))


; A motive that depends on the value (Decidable (x = z) at z) is the
; recursor's motive as it is, each minor typed at the motive at its constructor.
(= (typ-cases $c $args $sub $ctx)
   (case (cases-parts $c $args)
     (((parts $F $ps $motive $major $minors)
       (let* (($M (motive-of $motive)) ($elim (has-cases-eliminator $F)))
         (format-args "({}_{}{} {}{} {} {})"
           ((egal $F) (if $elim "casesOn_type" "rec_type") (join-sp (render-all $ps $sub)) (motive-text $M $sub)
            (join-sp (typ-minors (if $elim $minors (wrap-minors $F $ps $M $minors 0)) $sub $ctx)) (render $major $sub) (typ $major $sub $ctx))))))))

(= (typ-minors $ms $sub $ctx)
   (if (== $ms ()) ()
       (cons-atom (render (car-atom $ms) $sub)
         (cons-atom (typ (car-atom $ms) $sub $ctx) (typ-minors (cdr-atom $ms) $sub $ctx)))))

; A proof that t lies in T: a proof term proves its proposition.
(= (typ-at $t $T $sub $ctx)
   (case $t (((proof) (proof-at $T $sub $ctx))
             ($_ (if (conv-worthy $T) (typ-at-conv $t $T $sub $ctx) (typ $t $sub $ctx))))))

; A proof of P where hypotheses are in scope (the branches of a dite): P is a
; hypothesis (its proof, as every proof, is 0); a refutation of an equation
; of constructors, by no confusion or by injectivity at a field a hypothesis
; refutes; otherwise P's proof by itself.
(= (prove-prop-in $P $ctx)
   (let $known (known-proof $P $ctx)
     (if (not (== $known None)) $known
   (let $h (hyp-for $P $ctx $ctx)
     (if (== $h None)
         (case $P
           (((app Iff
                ((app Eq ((app Nat ()) (app Nat.mod ($n $d)) (num 0)))
                 (app Exists ((app Nat ())
                   (lam $x (app Nat ()) (app Eq ((app Nat ()) $n (app Nat.mul ($d (var $x))))))))))
             (format-args "(Lean_mod_divisibility_iff {} {} {} {})"
               ((render $d ()) (typ $d () $ctx) (render $n ()) (typ $n () $ctx))))
            ((app And ($A $B))
             (format-args "(Lean_And_intro_proof_ok {} {} 0 {} 0 {})"
               ((render $A ()) (render $B ()) (prove-prop-in $A $ctx) (prove-prop-in $B $ctx))))
            ((arrow $A (app False ())) (refute-in $A $ctx))
            ((pi $x $A $B) (prove-pi-value $x $A $B $ctx))
            ((arrow $A $B)
             (prove-pi-value (bridge-name "intro" 0 $P $ctx) $A $B $ctx))
            ((app (EgalLibrary proof-field) ($condition))
             (format-args "(Lean_ProofField_intro {} {})"
               ((render $condition ()) (prove-prop-in $condition $ctx))))
            ($_ (prove-prop $P))))
         (let ($x $hx) $h (format-args "(Lean_prop_0_of {} {} {} {})" ((render $P ()) (typ $P () $ctx) $x $hx))))))))
(= (prove-pi-value $x $A $B $ctx)
   (let* (($hx (bridge-name "hyp" 0 (pi $x $A $B) $ctx))
          ($next (cons-atom ((ReservedName $hx) True)
            (cons-atom ($x $hx) (cons-atom ((ty $x) $A) $ctx)))))
     (format-args "(Pi_0_In {} (fun {} => {}) (fun {} {} => {}))"
       ((render $A ()) $x (render $B ()) $x $hx (prove-prop-in $B $next)))))
(= (hyp-for $P $ctxs $ctx)
   (if (== $ctxs ()) None
       (case (car-atom $ctxs)
         ((((ty $x) $T) (if (== $T $P) ($x (lookup-var $x $ctx)) (hyp-for $P (cdr-atom $ctxs) $ctx)))
          ($_ (hyp-for $P (cdr-atom $ctxs) $ctx))))))
(= (refute-in $A $ctx)
   (case $A
     (((app And ($P $Q)) (refute-and $P $Q $ctx))
      ((arrow $P (app False ()))
       (case (hyp-for $P $ctx $ctx)
         ((None (prove-prop (arrow $A (app False ()))))
          (($x $hx) (format-args "(LeanNot_double {} {} {})"
            ((render $P ()) (typ $P () $ctx) (prove-prop-in $P $ctx)))))))
      ((app Eq ($T (app $c $xs) (app $d $ys)))
       (if (not (both-ctors-any $c $d)) (prove-prop (arrow $A (app False ())))
           (let $np (param-count (family-of-ctor $c))
             (if (== $c $d)
                 (inj-refute $T $c $np $xs $ys $A $ctx)
                 (format-args "(Lean_refute_0 {} {} {})" ((render $A ()) (typ $A () $ctx) (noconf-refute-args $T $c $d $np $xs $ys)))))))
      ($_ (prove-prop (arrow $A (app False ())))))))
(= (refute-and $P $Q $ctx)
   (let $left (hyp-for (arrow $P (app False ())) $ctx $ctx)
     (if (== $left None)
         (case (hyp-for (arrow $Q (app False ())) $ctx $ctx)
           ((None (prove-prop (arrow (app And ($P $Q)) (app False ()))))
            (($x $hx) (format-args "(LeanAnd_refute_right {} {} {} {} {} {})"
              ((render $P ()) (typ $P () $ctx) (render $Q ()) (typ $Q () $ctx) $x $hx)))))
         (case $left
           ((($x $hx) (format-args "(LeanAnd_refute_left {} {} {} {} {} {})"
             ((render $P ()) (typ $P () $ctx) (render $Q ()) (typ $Q () $ctx) $x $hx))))))))
(= (both-ctors-any $c $d)
   (if (is-ctor $c) (if (is-ctor $d) (== (family-of-ctor $c) (family-of-ctor $d)) False) False))
; Distinct constructors with fields: the family's no-confusion at its
; parameters and both constructors' fields.
(= (noconf-refute-args $T $c $d $np $xs $ys)
   (let* (($i (ctor-index $c)) ($j (ctor-index $d)) ($E (egal (family-of-ctor $c)))
          ($ps (render-all (take-n $xs $np) ())) ($cx (render (app $c $xs) ())) ($dy (render (app $d $ys) ()))
          ($eq (format-args "(LeanEq_sound {} {} {} 0 H)" ((render $T ()) $cx $dy))))
     (if (< $i $j)
         (format-args "(fun H => {}_noconf{}_{}{} {})" ($E $i $j (join-sp (append-lists $ps (append-lists (render-all (drop-n $xs $np) ()) (render-all (drop-n $ys $np) ())))) $eq))
         (format-args "(fun H => {}_noconf{}_{}{} (eq_sym_i {} {} {}))"
           ($E $j $i (join-sp (append-lists $ps (append-lists (render-all (drop-n $ys $np) ()) (render-all (drop-n $xs $np) ())))) $cx $dy $eq)))))
; One constructor: a field i whose equation a hypothesis h refutes; the
; constructor's injectivity at i turns the equation of the two into one of
; the fields, which h refutes.
(= (inj-refute $T $c $np $xs $ys $A $ctx)
   (let $k (refuted-field (drop-n $xs $np) (drop-n $ys $np) 0 $ctx)
     (if (== $k None) "UNDECIDED"
         (let* ((($i $B $h $hh) $k) ($fs (drop-n $xs $np)) ($gs (drop-n $ys $np))
                ($a (nth $fs $i)) ($b (nth $gs $i)) ($Ei (app Eq ($B $a $b))))
           (format-args "(Lean_refute_by {} {} {} {} {} {} (fun H => Lean_Eq_proof_of {} {} {} ({}_inj{}{} (LeanEq_sound {} {} {} 0 H))))"
             ((render $Ei ()) (typ $Ei () $ctx) $h $hh (render $A ()) (typ $A () $ctx)
              (render $B ()) (render $a ()) (render $b ())
              (egal $c) $i (join-sp (append-lists (render-all (take-n $xs $np) ()) (append-lists (render-all $fs ()) (render-all $gs ()))))
              (render $T ()) (render (app $c $xs) ()) (render (app $c $ys) ())))))))
(= (refuted-field $fs $gs $i $ctx)
   (if (== $fs ()) None
       (let* (($a (car-atom $fs)) ($b (car-atom $gs)) ($B (type-of $a $ctx))
              ($h (hyp-for (arrow (app Eq ($B $a $b)) (app False ())) $ctx $ctx)))
         (if (== $h None) (refuted-field (cdr-atom $fs) (cdr-atom $gs) (+ $i 1) $ctx)
             (let ($x $hx) $h ($i $B $x $hx))))))

; A proof that f a1 .. lies in the codomain, argument by argument (ap_Pi).
(= (typ-apv $ftext $fproof $ftype $args $sub $ctx)
   (if (== $args ()) $fproof
       (case $ftype
         (((pi $x $A $B)
           (let* (($a (car-atom $args)) ($atext (render $a $sub)))
             (typ-apv (format-args "({} {})" ($ftext $atext))
                      (format-args "(ap_Pi {} (fun {} => {}) {} {} {} {})"
                        ((render $A $sub) $x (render $B (remove-key $x $sub)) $ftext $atext $fproof (typ-at $a $A $sub $ctx)))
                      (fsubst $B (($x $a))) (cdr-atom $args) $sub $ctx)))
          ((arrow $A $B)
           (let* (($a (car-atom $args)) ($atext (render $a $sub)))
             (typ-apv (format-args "({} {})" ($ftext $atext))
                      (format-args "(ap_Pi {} (fun _ => {}) {} {} {} {})"
                        ((render $A $sub) (render $B $sub) $ftext $atext $fproof (typ $a $sub $ctx)))
                      $B (cdr-atom $args) $sub $ctx)))))))

; The type of a term; variable types are the context's (ty x) entries.
(= (type-of $t $ctx)
   (case $t
     (((var $x) (lookup-var (ty $x) $ctx))
      ((num $k) (app Nat ()))
      ((apv $f $args) (apply-type (type-of $f $ctx) $args))
      ((lam $x $T $b)
       (let $B (type-of $b (cons-atom ((ty $x) $T) $ctx))
         (if (mentions $B $x) (pi $x $T $B) (arrow $T $B))))
      ((app $c $args)
       (if (or (== $c (EgalLibrary proof-field)) (prop-fam $c)) (prop)
       (if (is-cases-on $c) (case (cases-parts $c $args) (((parts $F $ps $motive $major $minors) (motive-at (motive-of $motive) $major))))
       (if (is-ctor $c)
           (let $fam (family-of-ctor $c) (app $fam (take-n $args (param-count $fam))))
           (fn-result-type $c $args))))))))

(= (apply-type $T $args)
   (if (== $args ()) $T
       (case $T
         (((arrow $A $B) (apply-type $B (cdr-atom $args)))
          ((pi $x $A $B) (apply-type (fsubst $B (($x (car-atom $args)))) (cdr-atom $args)))))))

(= (peel-arrows $T $n)
   (if (== $n 0) $T (case $T (((arrow $A $B) (peel-arrows $B (- $n 1)))))))

; A function's result type at its arguments: its first equation's type with
; the variables of the left side's other arguments replaced.
(= (fn-result-type $g $args)
   (if (is-intrinsic $g)
       (case (intrinsic $g)
         (((primitive $kind $bs $R) (beta-norm (fsubst $R (var-binds (intrinsic-params $g) $args))))))
   (case (proj-info $g)
     (((proj $S $ctor $i $np)
       (field-fterm (nth (struct-fields $S) $i) (app $S (take-n $args $np)) (params-of $S) (take-n $args $np)))
      ($_ (fn-result-type-eqn $g $args))))))
(= (struct-fields $S) (ctor-fields (car-atom (constructors-of $S))))
(= (fn-result-type-eqn $g $args)
   (let* (($e (car-atom (eqns-of $g))) ($bind (var-binds (lhs-args $e) $args)))
     (beta-norm (fsubst (eqn-type $e) $bind))))
(= (var-binds $ps $as)
   (if (== $ps ()) ()
       (let $rest (var-binds (cdr-atom $ps) (cdr-atom $as))
         (if (is-fvar (car-atom $ps)) (cons-atom ((var-name (car-atom $ps)) (car-atom $as)) $rest) $rest))))

(= (typ-ctor $c $args $sub $ctx)
   (let* (($np (param-count (family-of-ctor $c)))
          ($all (append-lists (render-all (take-n $args $np) $sub)
                  (typ-fields-at (drop-n $args $np) (ctor-field-types $c (take-n $args $np)) $sub $ctx))))
     (if (== $all ()) (format-args "{}_typed" ((egal $c)))
         (format-args "({}_typed {})" ((egal $c) (join " " $all))))))

(= (ctor-field-types $c $targs)
   (let* (($F (family-of-ctor $c)) ($cs (constructors-of $F))
          ($fs (ctor-fields (nth $cs (ctor-index-in $cs $c 0)))))
     (ctor-field-types-list $fs (app $F $targs) (params-of $F) $targs)))
(= (ctor-field-types-list $fs $T $params $targs)
   (if (== $fs ()) ()
       (cons-atom (field-fterm (car-atom $fs) $T $params $targs) (ctor-field-types-list (cdr-atom $fs) $T $params $targs))))
(= (typ-fields-at $args $Ts $sub $ctx)
   (typ-instantiated-fields $args (instantiate-field-types $Ts $args) $sub $ctx))
(= (typ-instantiated-fields $args $Ts $sub $ctx)
   (if (== $args ()) ()
       (cons-atom (render (car-atom $args) $sub)
         (cons-atom (typ-at (car-atom $args) (car-atom $Ts) $sub $ctx) (typ-instantiated-fields (cdr-atom $args) (cdr-atom $Ts) $sub $ctx)))))

(= (field-bindings $args $i)
   (if (== $args ()) ()
       (cons-atom ((GuardField $i) (car-atom $args)) (field-bindings (cdr-atom $args) (+ $i 1)))))
(= (used-bindings $bindings $names)
   (if (== $bindings ()) ()
       (let ($name $value) (car-atom $bindings)
         (if (member-term $name $names)
             (cons-atom ($name $value) (used-bindings (cdr-atom $bindings) $names))
             (used-bindings (cdr-atom $bindings) $names)))))
(= (instantiate-field-types $types $args)
   (let $bindings (field-bindings $args 0)
     (map-atom $types $type (csubst $type (used-bindings $bindings (fvs $type))))))

(= (typ-fields $args $sub $ctx)
   (if (== $args ()) ()
       (cons-atom (render (car-atom $args) $sub)
         (cons-atom (typ (car-atom $args) $sub $ctx) (typ-fields (cdr-atom $args) $sub $ctx)))))

(= (typ-fn $g $args $sub $ctx)
   (format-args "({}_In {})" ((egal $g) (join " " (typ-args-raw $args (pos-kinds $g) (arg-types $g $args) (arg-types-raw $g $args) $sub $ctx)))))
; The declared types instantiated as written: Megalodon expects these (a
; set-level lambda applied is not reduced by conversion).
; A family argument (a motive) is passed with a meta-level copy, and the
; lemma applies the copy: there the application is reduced by conversion,
; as the copy's body (beta normal) with the arguments put in place.
(= (arg-types-raw $g $args)
   (let $T (fn-type $g) (if (== $T None) () (inst-binder-types-raw (type-binders-of $T 0) $args (pos-kinds $g) ()))))
(= (inst-binder-types-raw $bs $args $ks $bind)
   (if (== $bs ()) ()
       (if (== $args ()) ()
           (let* (($b (car-atom $bs)) ($x (car-atom $b)) ($A (car-atom (cdr-atom $b)))
                  ($k (if (== $ks ()) term (car-atom $ks)))
                  ($v (if (== $k family) (fam-val (car-atom $args)) (car-atom $args))))
             (cons-atom (if (or (is-sort-term $A) (is-family-type $A)) None (fam-beta (fsubst $A $bind)))
               (inst-binder-types-raw (cdr-atom $bs) (cdr-atom $args) (if (== $ks ()) () (cdr-atom $ks)) (cons-atom ($x $v) $bind)))))))
(= (fam-beta $t)
   (case $t
     (((fam-val $V) $V)
      ((apv $f $args)
       (let $as (fam-beta-all $args)
         (case $f (((fam-val $V) (meta-apply $V $as)) ($_ (apv (fam-beta $f) $as))))))
      ((app $c $args) (app $c (fam-beta-all $args)))
      ((lam $x $T $b) (lam $x (fam-beta $T) (fam-beta $b)))
      ((pi $x $A $B) (pi $x (fam-beta $A) (fam-beta $B)))
      ((arrow $A $B) (arrow (fam-beta $A) (fam-beta $B)))
      ((canon $P) (canon (fam-beta $P)))
      ($_ $t))))
(= (fam-beta-all $ts) (if (== $ts ()) () (cons-atom (fam-beta (car-atom $ts)) (fam-beta-all (cdr-atom $ts)))))
(= (meta-apply $V $as)
   (let ($xs $body) (lam-chain $V ())
     (if (< (length-of $as) (length-of $xs)) (apv $V $as)
         (if (== $xs ()) (apv $V $as)
             (let* (($n (length-of $xs)) ($r (csubst (beta-norm $body) (zip-bind $xs (take-n $as $n)))))
               (if (== (length-of $as) $n) $r (apv $r (drop-n $as $n))))))))
(= (lam-chain $t $acc)
   (case $t (((lam $x $T $b) (lam-chain $b (append-lists $acc ($x)))) ($_ ($acc $t)))))
; typ-args, an argument whose type as written needs reduction converted.
(= (typ-args-raw $args $ks $Ts $Rs $sub $ctx)
   (if (== $args ()) ()
       (let* (($a (car-atom $args)) ($T (if (== $Ts ()) None (car-atom $Ts))) ($TR (if (== $Rs ()) None (car-atom $Rs)))
              ($rest (typ-args-raw (cdr-atom $args) (cdr-atom $ks) (if (== $Ts ()) () (cdr-atom $Ts)) (if (== $Rs ()) () (cdr-atom $Rs)) $sub $ctx)))
         (if (== (car-atom $ks) type) (cons-atom (render $a $sub) $rest)
         (if (== (car-atom $ks) family) (cons-atom (render $a $sub) (cons-atom (meta-render $a $sub) $rest))
             (cons-atom (render $a $sub)
               (cons-atom (if (== $a (proof)) (proof-at (if (== $TR None) $T $TR) $sub $ctx)
                            (if (== $T None) (typ $a $sub $ctx)
                              (if (== $TR None) (typ-at $a $T $sub $ctx)
                                  (if (and (not (== $TR $T)) (conv-worthy $TR)) (typ-at-conv $a $TR $sub $ctx) (typ-at $a $T $sub $ctx))))
                 $rest))))))))

; Each argument at its declared type, the earlier arguments put in place: a
; proof argument is proved at it.
(= (typ-args $args $ks $Ts $sub $ctx)
   (if (== $args ()) ()
       (let* (($a (car-atom $args)) ($T (if (== $Ts ()) None (car-atom $Ts)))
              ($rest (typ-args (cdr-atom $args) (cdr-atom $ks) (if (== $Ts ()) () (cdr-atom $Ts)) $sub $ctx)))
         (if (== (car-atom $ks) type) (cons-atom (render $a $sub) $rest)
         (if (== (car-atom $ks) family) (cons-atom (render $a $sub) (cons-atom (meta-render $a $sub) $rest))
             (cons-atom (render $a $sub)
               (cons-atom (if (== $T None) (typ $a $sub $ctx) (typ-at $a $T $sub $ctx)) $rest)))))))
(= (arg-types $g $args)
   (let $T (fn-type $g) (if (== $T None) () (inst-binder-types (type-binders-of $T 0) $args ()))))
(= (inst-binder-types $bs $args $bind)
   (if (== $bs ()) ()
       (if (== $args ()) ()
           (let ($x $A) (car-atom $bs)
             (cons-atom (if (or (is-sort-term $A) (is-family-type $A)) None (beta-norm (fsubst $A $bind)))
               (inst-binder-types (cdr-atom $bs) (cdr-atom $args) (cons-atom ($x (car-atom $args)) $bind)))))))

; A proof that a method lies in its Pi type: lam_Pi, layer by layer.
(= (hm-proof $layers $body $sub $ctx $R)
   (if (== $layers ()) (typ $body $sub $ctx)
       (let* (($l (car-atom $layers)) ($z (ly-name $l)) ($rest (cdr-atom $layers))
              ($hz (format-args "H{}" ($z))))
         (format-args "(lam_Pi {} (fun {} => {}) (fun {} => {}) (fun {} {} => {}))"
           ((render (ly-type $l) $sub) $z (pi-text $rest $R (remove-key $z $sub)) $z (lam-text $rest $body (remove-key $z $sub))
            $z $hz (hm-proof $rest $body (remove-key $z $sub) (cons-atom ($z $hz) (cons-atom ((ty $z) (ly-type $l)) $ctx)) $R))))))

; E_f_In: the function's value lies in its result type.
(= (in-theorem $f $s)
   (if (== (fn-accs $f (shape-m $s)) ()) (in-theorem-plain $f $s) (in-theorem-acc $f $s)))

; With its typing written in Egal (a proof argument's proposition is not
; read), only the recursor's typing at the motive is generated.
(= (rec-in-theorem $f $s)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($e1 (car-atom (shape-eqs $s)))
          ($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0))
          ($ks (pos-kinds $f)) ($accs (fn-accs $f $m))
          ($cm1 (cmethod $f $e1 $m $fam)) ($R (cm-result $cm1))
          ($ren1 (param-renames (lhs-args $e1) $m 0))
          ($Ts (acc-types $e1 $accs $ren1))
          ($PiR (arrows $Ts $R))
          ($famT (major-type-text $f $s $sub))
          ($ctx (append-lists (pos-hyps $ks $m 0) (pos-tys $f $ks $m 0)))
          ($hms (hm-list $f (shape-eqs $s) $m $fam $sub $ctx))
          ($fps (let $fp (render-all (fam-params-c $f $s) $sub) (if (== $fp ()) "" (format-args " {}" ((join " " $fp))))))
          ($prefix (rec-prefix $f $s $sub)))
     (format-args "Theorem {}_recIn : {}forall t :e {}, {} t :e {}.
{}let t. assume Ht: t :e {}.
exact {}_rec_type{} {} {} {}t Ht.
Qed.
"
       ((egal $f) (fixed-binders $f $ks $m $accs 0 $famT $sub) $famT $prefix (render $PiR $sub)
        (fixed-intros $f $ks $m $accs 0 $famT $sub) $famT
        (egal $fam) $fps (rec-motive-text $f $m $accs $Ts $R $sub) $hms (major-index-text $f $m $sub)))))
(= (in-theorem-acc $f $s)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($e1 (car-atom (shape-eqs $s)))
          ($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0))
          ($ks (pos-kinds $f)) ($accs (fn-accs $f $m))
          ($cm1 (cmethod $f $e1 $m $fam)) ($dep (dep-typed $f)) ($R (if $dep (pos-result $f) (cm-result $cm1)))
          ($ren1 (param-renames (lhs-args $e1) $m 0))
          ($Ts (acc-types $e1 $accs $ren1))
          ($PiR (if $dep (dep-pi $f $m $accs $Ts (var "t")) (arrows $Ts $R)))
          ($famT (major-type-text $f $s $sub))
          ($ctx (append-lists (pos-hyps $ks $m 0) (pos-tys $f $ks $m 0)))
          ($hms (hm-list $f (shape-eqs $s) $m $fam $sub $ctx))
          ($fps (let $fp (render-all (fam-params-c $f $s) $sub) (if (== $fp ()) "" (format-args " {}" ((join " " $fp))))))
          ($prefix (rec-prefix $f $s $sub)))
     (format-args "Theorem {}_recIn : {}forall t :e {}, {} t :e {}.
{}let t. assume Ht: t :e {}.
exact {}_rec_type{} {} {} {}t Ht.
Qed.
Theorem {}_In : {}{} {} :e {}.
{}exact {}.
Qed.
"
       ((egal $f) (fixed-binders $f $ks $m $accs 0 $famT $sub) $famT $prefix (render $PiR $sub)
        (fixed-intros $f $ks $m $accs 0 $famT $sub) $famT
        (egal $fam) $fps (rec-motive-text $f $m $accs $Ts $R $sub) $hms (major-index-text $f $m $sub)
        (egal $f) (in-binders $f $ks $m 0 $famT $sub) (egal $f) (join " " $ps) (render $R $sub)
        (in-intros $f $ks $m 0 $famT $sub)
        (if $dep
            (ap-chain-dep (format-args "({} a{})" ($prefix $m))
                  (format-args "({}_recIn {})" ((egal $f) (join " " (in-rec-args $ks $m $accs 0))))
                  $accs $Ts $R $sub)
            (ap-chain (format-args "({} a{})" ($prefix $m))
                  (format-args "({}_recIn {})" ((egal $f) (join " " (in-rec-args $ks $m $accs 0))))
                  $accs $Ts $R $sub))))))

; Inside E_f_In: the fixed parameters with their hypotheses H_p, then the major.
(= (in-rec-args $ks $m $accs $p)
   (if (== $ks ()) ((format-args "a{}" ($m)) (format-args "H{}" ($m)))
       (let $rest (in-rec-args (cdr-atom $ks) $m $accs (+ $p 1))
         (if (or (== $p $m) (member-term $p $accs)) $rest
             (if (== (car-atom $ks) proof) $rest
             (if (== (car-atom $ks) type) (cons-atom (format-args "a{}" ($p)) $rest)
                 (cons-atom (format-args "a{}" ($p)) (cons-atom (format-args "H{}" ($p)) $rest))))))))

(= (fixed-binders $f $ks $m $accs $p $famT $sub)
   (if (== $ks ()) ""
       (format-args "{}{}"
         ((if (or (or (== $p $m) (member-term $p $accs)) (== (car-atom $ks) proof)) ""
              (if (== (car-atom $ks) type) (format-args "forall a{}, " ($p))
                  (format-args "forall a{} :e {}, " ($p (pos-type $f $p $m $famT $sub)))))
          (fixed-binders $f (cdr-atom $ks) $m $accs (+ $p 1) $famT $sub)))))

(= (fixed-intros $f $ks $m $accs $p $famT $sub)
   (if (== $ks ()) ""
       (format-args "{}{}"
         ((if (or (or (== $p $m) (member-term $p $accs)) (== (car-atom $ks) proof)) ""
              (if (== (car-atom $ks) type) (format-args "let a{}. " ($p))
                  (format-args "let a{}. assume H{}: a{} :e {}. " ($p $p $p (pos-type $f $p $m $famT $sub)))))
          (fixed-intros $f (cdr-atom $ks) $m $accs (+ $p 1) $famT $sub)))))

; The same with a result depending on the accumulators: each application's
; codomain is the product over the remaining ones, at the accumulator applied.
(= (ap-chain-dep $cur $proof $accs $Ts $R $sub)
   (if (== $accs ()) $proof
       (let* (($p (car-atom $accs)) ($T (car-atom $Ts)) ($B (pis-of (cdr-atom $accs) (cdr-atom $Ts) $R)))
         (ap-chain-dep (format-args "({} a{})" ($cur $p))
                   (format-args "(ap_Pi {} (fun a{} => {}) {} a{} {} H{})" ((render $T $sub) $p (render $B (remove-key (pos-name $p) $sub)) $cur $p $proof $p))
                   (cdr-atom $accs) (cdr-atom $Ts) $R $sub))))
; A proof that the recursor's function applied to the accumulators lies in R.
(= (ap-chain $cur $proof $accs $Ts $R $sub)
   (if (== $accs ()) $proof
       (let* (($p (car-atom $accs)) ($T (car-atom $Ts)) ($B (arrows (cdr-atom $Ts) $R)))
         (ap-chain (format-args "({} a{})" ($cur $p))
                   (format-args "(ap_Pi {} (fun _ => {}) {} a{} {} H{})" ((render $T $sub) (render $B $sub) $cur $p $proof $p))
                   (cdr-atom $accs) (cdr-atom $Ts) $R $sub))))

(= (in-theorem-plain $f $s)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($e1 (car-atom (shape-eqs $s)))
          ($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0))
          ($ks (pos-kinds $f))
          ($cm1 (cmethod $f $e1 $m $fam)) ($R (if (dep-typed $f) (pos-result $f) (cm-result $cm1)))
          ($famT (major-type-text $f $s $sub))
          ($ctx (append-lists (pos-hyps $ks $m 0) (pos-tys $f $ks $m 0)))
          ($hms (hm-list $f (shape-eqs $s) $m $fam $sub $ctx)))
     (format-args "Theorem {}_In : {}{} {} :e {}.
{}exact {}_rec_type{} {} {} {}{} H{}.
Qed.
"
       ((egal $f) (in-binders $f $ks $m 0 $famT $sub) (egal $f) (join " " $ps) (render $R $sub)
        (in-intros $f $ks $m 0 $famT $sub)
        (egal $fam) (let $fps (render-all (fam-params-c $f $s) $sub) (if (== $fps ()) "" (format-args " {}" ((join " " $fps)))))
        (rec-motive-text $f $m () () $R $sub) $hms (major-index-text $f $m $sub) (pos-name $m) $m))))
; The recursor's motive: constant, or the declared result at the major t when
; it depends on the arguments.
(= (rec-motive-text $f $m $accs $Ts $R $sub)
   (let $is (major-index-args $f $m)
     (if (== $is ())
         (if (dep-typed $f)
             (format-args "(fun t => {})" ((render (dep-pi $f $m $accs $Ts (var "t")) $sub)))
             (format-args "(fun _ => {})" ((render (arrows $Ts $R) $sub))))
         (format-args "(fun {} t => {})"
           ((join " " (ivar-names (length-of $is)))
            (render (if (dep-typed $f) (fsubst (dep-pi $f $m $accs $Ts (var "t")) (index-binds $is 0)) (arrows $Ts $R)) $sub))))))
; An indexed family's recursor takes a motive over its indices and the
; major; the indices of the major's declared type that are the function's
; arguments become the motive's index variables.
(= (major-decl-type $f $m)
   (let* (($T (fn-type $f)) ($bs (type-binders-of $T 0)))
     (fsubst (car-atom (cdr-atom (nth $bs $m))) (named-binds $bs 0 pos-name))))
(= (major-index-args $f $m)
   (let $T (fn-type $f)
     (if (== $T None) ()
         (case (major-decl-type $f $m)
           (((app $F $args)
             (let $q (declared-index-count $F) (if (== $q 0) () (drop-n $args (- (length-of $args) $q)))))
            ($_ ()))))))
(= (index-binds $is $k)
   (if (== $is ()) ()
       (let $rest (index-binds (cdr-atom $is) (+ $k 1))
         (case (car-atom $is) (((var $x) (cons-atom ($x (var (ivar-name $k))) $rest)) ($_ $rest))))))
(= (ivar-name $k) (format-args "i{}" ($k)))
(= (ivar-names $q) (map-atom (range-from 0 $q) $k (ivar-name $k)))
; The major's type, and the indices passed to the recursor's typing.
(= (major-type-text $f $s $sub)
   (if (== (major-index-args $f (shape-m $s)) ()) (render (app (shape-fam $s) (fam-params-c $f $s)) $sub)
       (render (major-decl-type $f (shape-m $s)) $sub)))
; The motive's index binders, for an indexed family ("i0 i1 ").
(= (index-binder-text $f $m) (join "" (map-atom (ivar-names (length-of (major-index-args $f $m))) $x (format-args "{} " ($x)))))
(= (major-index-text $f $m $sub)
   (join "" (map-atom (major-index-args $f $m) $i (format-args "{} " ((render $i $sub))))))

(= (pos-hyps $ks $m $p)
   (if (== $ks ()) ()
       (let $rest (pos-hyps (cdr-atom $ks) $m (+ $p 1))
         (if (or (== (car-atom $ks) type) (== (car-atom $ks) proof)) $rest (cons-atom ((pos-name $p) (format-args "H{}" ($p))) $rest)))))

(= (pos-tys $f $ks $m $p)
   (if (== $ks ()) ()
       (let $rest (pos-tys $f (cdr-atom $ks) $m (+ $p 1))
         (if (or (or (== $p $m) (== (car-atom $ks) type)) (== (car-atom $ks) proof)) $rest
             (let* (($e (car-atom (eqns-of $f))) ($x (var-name (nth (lhs-args $e) $p)))
                    ($ren (param-renames (lhs-args $e) $m 0)))
               (cons-atom ((ty (pos-name $p)) (fsubst (binder-type $x (eqn-binders $e)) $ren)) $rest))))))

(= (pos-type $f $p $m $famT $sub)
   (if (== $p $m) $famT
       (let* (($e (car-atom (eqns-of $f))) ($x (var-name (nth (lhs-args $e) $p)))
              ($ren (param-renames (lhs-args $e) $m 0)))
         (render (fsubst (binder-type $x (eqn-binders $e)) $ren) $sub))))

(= (in-binders $f $ks $m $p $famT $sub)
   (if (== $ks ()) ""
       (format-args "{}{}"
         ((if (== (car-atom $ks) type) (format-args "forall {}, " ((pos-name $p)))
              (format-args "forall {} :e {}, " ((pos-name $p) (pos-type $f $p $m $famT $sub))))
          (in-binders $f (cdr-atom $ks) $m (+ $p 1) $famT $sub)))))

(= (in-intros $f $ks $m $p $famT $sub)
   (if (== $ks ()) ""
       (format-args "{}{}"
         ((if (== (car-atom $ks) type) (format-args "let {}. " ((pos-name $p)))
              (format-args "let {}. assume H{}: {} :e {}. " ((pos-name $p) $p (pos-name $p) (pos-type $f $p $m $famT $sub))))
          (in-intros $f (cdr-atom $ks) $m (+ $p 1) $famT $sub)))))

(= (hm-list $f $eqs $m $fam $sub $ctx) (hm-list-k $f $eqs $m $fam $sub $ctx 0))
(= (hm-list-k $f $eqs $m $fam $sub $ctx $k)
   (if (== $eqs ()) ""
       (let* (($cm (cmethod $f (car-atom $eqs) $m $fam))
              ($M (method-ref $f $k $m $cm $sub))
              ($H (if (== (cm-layers $cm) ()) (hm-proof (cm-layers $cm) (cm-body $cm) $sub $ctx (cm-result $cm))
                      (format-args "({}_In{})" ((method-name $f $k 0) (fixed-args-hyps $f (fixed-positions $f $m))))))
              ($rest (hm-list-k $f (cdr-atom $eqs) $m $fam $sub $ctx (+ $k 1))))
         (if (== $rest "") (format-args "{} {}" ($M $H)) (format-args "{} {} {}" ($M $H $rest))))))

; ---- Lean's equation theorems ----

; Binders of a statement: a level parameter is introduced with its first type.
(= (stmt-binders $bs $levels)
   (if (== $bs ()) ""
       (case (car-atom $bs)
         (((type $x $l)
           (if (or (== $l 0) (member-term $l $levels))
               (format-args "forall {} :e LeanUniv {}, {}" ($x $l (stmt-binders (cdr-atom $bs) $levels)))
               (format-args "forall {}, nat_p {} -> forall {} :e LeanUniv {}, {}" ($l $l $x $l (stmt-binders (cdr-atom $bs) (cons-atom $l $levels))))))
          ((term $x $t)
           (format-args "forall {} :e {}, {}" ($x (render $t ()) (stmt-binders (cdr-atom $bs) $levels))))
          ((hyp $x $P) (format-args "({}) -> {}" ((stmt-native $P) (stmt-binders (cdr-atom $bs) $levels))))
          ((sort $x $l)
           (if (member-term $l $levels)
               (format-args "forall {} :e LeanSort {}, {}" ($x $l (stmt-binders (cdr-atom $bs) $levels)))
               (format-args "forall {}, nat_p {} -> forall {} :e LeanSort {}, {}" ($l $l $x $l (stmt-binders (cdr-atom $bs) (cons-atom $l $levels))))))))))

(= (stmt-intros $bs $levels)
   (if (== $bs ()) ""
       (case (car-atom $bs)
         (((hyp $x $P) (format-args "assume {}. {}" ($x (stmt-intros (cdr-atom $bs) $levels))))
          ((type $x $l)
           (if (or (== $l 0) (member-term $l $levels))
               (format-args "let {}. assume H_{}: {} :e LeanUniv {}. {}" ($x $x $x $l (stmt-intros (cdr-atom $bs) $levels)))
               (format-args "let {}. assume H_{}: nat_p {}. let {}. assume H_{}: {} :e LeanUniv {}. {}" ($l $l $l $x $x $x $l (stmt-intros (cdr-atom $bs) (cons-atom $l $levels))))))
          ((term $x $t)
           (format-args "let {}. assume H_{}: {} :e {}. {}" ($x $x $x (render $t ()) (stmt-intros (cdr-atom $bs) $levels))))
          ((sort $x $l)
           (if (member-term $l $levels)
               (format-args "let {}. assume H_{}: {} :e LeanSort {}. {}" ($x $x $x $l (stmt-intros (cdr-atom $bs) $levels)))
               (format-args "let {}. assume H_{}: nat_p {}. let {}. assume H_{}: {} :e LeanSort {}. {}" ($l $l $l $x $x $x $l (stmt-intros (cdr-atom $bs) (cons-atom $l $levels))))))))))

(= (statement-text $e)
   (let $free (free-levels (eqn-binders $e))
     (format-args "{}{}{} = {}" ((join "" (map-atom $free $l (format-args "forall {}, nat_p {} -> " ($l $l))))
                                 (stmt-binders (eqn-binders $e) $free) (render (eqn-lhs $e) ()) (render (eqn-rhs $e) ())))))
; Universe levels that only term binders' types mention (Sort u1 in a motive's
; type): quantified first, before the binders.
(= (free-levels $bs) (free-levels-acc $bs () ()))
(= (free-levels-acc $bs $bound $acc)
   (if (== $bs ()) $acc
       (case (car-atom $bs)
         (((type $x $l) (free-levels-acc (cdr-atom $bs) (cons-atom $l $bound) $acc))
          ((sort $x $l) (free-levels-acc (cdr-atom $bs) (cons-atom $l $bound) $acc))
          ((term $x $T) (free-levels-acc (cdr-atom $bs) $bound (fresh-levels (stmt-levels $T ()) $bound $acc)))
          ($_ (free-levels-acc (cdr-atom $bs) $bound $acc))))))
(= (fresh-levels $ls $bound $acc)
   (if (== $ls ()) $acc
       (let $l (car-atom $ls)
         (fresh-levels (cdr-atom $ls) $bound (if (or (member-term $l $bound) (member-term $l $acc)) $acc (append-lists $acc ($l)))))))
(= (eqn-intros $e)
   (let $bs (eqn-binders $e) (format-args "{}{}" ((free-level-intros $bs) (stmt-intros $bs (free-levels $bs))))))
(= (free-level-intros $bs)
   (join "" (map-atom (free-levels $bs) $l (format-args "let {}. assume H_{}: nat_p {}. " ($l $l $l)))))

; The right side with each recursive call unfolded to the recursor.
(= (render-unfold $t $f $m $prefix $accs) (render (unfold-calls $t $f $m $prefix $accs) ()))
(= (unfold-calls $t $f $m $prefix $accs)
   (case $t
     (((app $c $args)
       (if (== $c $f)
           (txt (accs-applied (format-args "({} {})" ($prefix (render-unfold (nth $args $m) $f $m $prefix $accs)))
                  (render-unfold-all (acc-args $args $accs) $f $m $prefix $accs)))
           (app $c (unfold-calls-all $args $f $m $prefix $accs))))
      ((apv $g $args) (apv (unfold-calls $g $f $m $prefix $accs) (unfold-calls-all $args $f $m $prefix $accs)))
      ((lam $x $T $b) (lam $x (unfold-calls $T $f $m $prefix $accs) (unfold-calls $b $f $m $prefix $accs)))
      ((arrow $A $B) (arrow (unfold-calls $A $f $m $prefix $accs) (unfold-calls $B $f $m $prefix $accs)))
      ((pi $x $A $B) (pi $x (unfold-calls $A $f $m $prefix $accs) (unfold-calls $B $f $m $prefix $accs)))
      ($_ $t))))
(= (unfold-calls-all $ts $f $m $prefix $accs)
   (if (== $ts ()) () (cons-atom (unfold-calls (car-atom $ts) $f $m $prefix $accs) (unfold-calls-all (cdr-atom $ts) $f $m $prefix $accs))))
(= (render-unfold-all $ts $f $m $prefix $accs)
   (if (== $ts ()) () (cons-atom (render-unfold (car-atom $ts) $f $m $prefix $accs) (render-unfold-all (cdr-atom $ts) $f $m $prefix $accs))))

(= (arg-names $args $p $m)
   (if (== $args ()) ()
       (cons-atom (if (== $p $m) "_" (if (== (car-atom $args) (proof)) "0" (var-name (car-atom $args))))
                  (arg-names (cdr-atom $args) (+ $p 1) $m))))

(= (field-args-text $vars)
   (if (== $vars ()) ""
       (let $x (var-name (car-atom $vars)) (format-args " {} H_{}{}" ($x $x (field-args-text (cdr-atom $vars)))))))

; The actual argument of each layer: the field variables, then the unfolded
; recursive calls.
(= (layer-actuals $layers $fvars $prefix $pnames)
   (if (== $layers ()) ()
       (let* (($l (car-atom $layers)) ($z (ly-name $l)) ($i (ly-index $l)))
         (cons-atom ($z (case (ly-kind $l)
                          ((ih (format-args "({} {})" ($prefix (var-name (nth $fvars $i)))))
                           (acc (nth $pnames $i))
                           ($_ (var-name (nth $fvars $i))))))
                    (layer-actuals (cdr-atom $layers) $fvars $prefix $pnames)))))

; Proof that an actual argument lies in its layer's domain.
(= (actual-proof $l $fvars $f $pnames $ks $m)
   (case (ly-kind $l)
     ((acc (format-args "H_{}" ((nth $pnames (ly-index $l)))))
      (ih (let $x (var-name (nth $fvars (ly-index $l)))
            (let $accs (fn-accs $f $m)
              (if (== $accs ())
                  (format-args "({}_In {})" ((egal $f) (join " " (in-call-args $pnames $ks $m 0 $x))))
                  (format-args "({}_recIn {})" ((egal $f) (join " " (rec-call-args $pnames $ks $m $accs 0 $x))))))))
      ($_ (format-args "H_{}" ((var-name (nth $fvars (ly-index $l)))))))))

; The arguments of E_f_recIn: the fixed parameters, then the major value.
(= (rec-call-args $pnames $ks $m $accs $p $x)
   (if (== $pnames ()) ($x (format-args "H_{}" ($x)))
       (let $rest (rec-call-args (cdr-atom $pnames) (cdr-atom $ks) $m $accs (+ $p 1) $x)
         (if (or (or (== $p $m) (member-term $p $accs)) (== (car-atom $ks) proof)) $rest
             (if (== (car-atom $ks) type) (cons-atom (car-atom $pnames) $rest)
                 (cons-atom (car-atom $pnames) (cons-atom (format-args "H_{}" ((car-atom $pnames))) $rest)))))))

(= (in-call-args $pnames $ks $m $p $x)
   (if (== $pnames ()) ()
       (let $rest (in-call-args (cdr-atom $pnames) (cdr-atom $ks) $m (+ $p 1) $x)
         (if (== $p $m) (cons-atom $x (cons-atom (format-args "H_{}" ($x)) $rest))
             (if (== (car-atom $ks) type) (cons-atom (car-atom $pnames) $rest)
                 (cons-atom (car-atom $pnames) (cons-atom (format-args "H_{}" ((car-atom $pnames))) $rest)))))))

(= (beta-lines $layers $body $sub $actuals $fvars $f $pnames $ks $m $k)
   (beta-lines-i $layers $sub $actuals $fvars $f $pnames $ks $m $k 0 ""))
(= (beta-lines-i $layers $sub $actuals $fvars $f $pnames $ks $m $k $i $prev)
   (if (== $layers ()) ""
       (let* (($l (car-atom $layers)) ($z (ly-name $l)) ($rest (cdr-atom $layers))
              ($arg (lookup-var $z $actuals))
              ($fixed (join "" (map-atom (fixed-positions $f $m) $p (format-args " {}" ((render (var (pos-name $p)) $sub)))))))
         (format-args "rewrite {}_ap{}{} {} {}.
{}"
           ((method-name $f $k $i) $fixed $prev $arg (actual-proof $l $fvars $f $pnames $ks $m)
            (beta-lines-i $rest $sub $actuals $fvars $f $pnames $ks $m $k (+ $i 1) (format-args "{} {}" ($prev $arg))))))))

(= (eqn-theorem $f $s $e $k)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($args (lhs-args $e))
          ($pnames (arg-names $args 0 $m)) ($sub (pos-subst $pnames 0))
          ($ks (pos-kinds $f))
          ($prefix (rec-prefix $f $s $sub))
          ($pat (pattern-of (nth $args $m)))
          ($fvars (drop-n (app-args $pat) (param-count $fam)))
          ($cm (cmethod $f $e $m $fam))
          ($actuals (layer-actuals (cm-layers $cm) $fvars $prefix $pnames))
          ($accs (fn-accs $f $m))
          ($fps (render-all (fam-params-c $f $s) $sub)))
     (format-args "{}Theorem {} : {}.
{}
{}prove {} = {}.
rewrite {}_iota{}{} {}{}.
{}reflexivity.
Qed.
"
       ((receipt-comment (eqn-name $e) $f) (egal (eqn-name $e)) (statement-text $e) (eqn-intros $e)
        (literal-zero-line $e $m)
        (accs-applied (format-args "({} {})" ($prefix (render $pat ()))) (pick-names $pnames $accs))
        (render-unfold (eqn-rhs $e) $f $m $prefix $accs)
        (egal $fam) $k (if (== $fps ()) "" (format-args " {}" ((join " " $fps)))) (methods-text $f $s $sub) (field-args-text $fvars)
        (beta-lines (cm-layers $cm) (cm-body $cm) $sub $actuals $fvars $f $pnames $ks $m $k)))))

; A literal 0 at the pattern is read as the constructor there (LeanNum_0_at).
(= (replace-at $args $m $t $p)
   (if (== $args ()) ()
       (cons-atom (if (== $p $m) $t (car-atom $args)) (replace-at (cdr-atom $args) $m $t (+ $p 1)))))

(= (literal-zero-line $e $m)
   (if (== (nth (lhs-args $e) $m) (num 0))
       (let* (($lhs (eqn-lhs $e)) ($f (app-head $lhs))
              ($ctx (app $f (replace-at (lhs-args $e) $m (var zpat) 0))))
         (format-args "apply LeanNum_0_at (fun zpat => {}) {}.
" ((render $ctx ()) (render (eqn-rhs $e) ()))))
       ""))

; A receipt: the equation is the theorem a MeTTa rule of the slice was taken
; from, with the same statement digest.
(= (receipt-comment $thm $f)
   (let $found (collapse (match &self (LeanReceipt $thm $d) $d))
     (if (== $found ()) ""
         (let $pw (collapse (match &self (LeanPointwise $thm $k) $k))
           (format-args "(** Receipt: {} is the source of the MeTTa rule for {}, statement digest {}.{}{} **)
" ($thm $f (car-atom $found)
   (if (== $pw ()) "" (format-args " Read pointwise: Lean states it between functions, here at {} more argument(s)." ((car-atom $pw))))
   (if (== (collapse (match &self (LeanUniverseProfile $f $kind $levels) $kind)) ()) ""
       " At the declared Type universe profile.")))))))

(= (pick-names $names $ps)
   (if (== $ps ()) () (cons-atom (nth $names (car-atom $ps)) (pick-names $names (cdr-atom $ps)))))

(= (eqn-theorems $f $s $eqs $k)
   (if (== $eqs ()) ""
       (format-args "{}{}" ((eqn-theorem $f $s (car-atom $eqs) $k) (eqn-theorems $f $s (cdr-atom $eqs) (+ $k 1))))))

(= (direct-theorem $f $e)
   (format-args "{}Theorem {} : {}.
{}
reflexivity.
Qed.
{}" ((receipt-comment (eqn-name $e) $f) (egal (eqn-name $e)) (statement-text $e) (eqn-intros $e) (unfold-theorem $f $e))))
; The definition unfolded, for every argument: what a computation rewrites by.
; Lean's equation theorem, with its binders' types, is proved above.
(= (unfold-theorem $f $e)
   (let* (($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0)) ($ren (param-renames (lhs-args $e) -1 0)))
     (if (== $n 0)
         (format-args "Theorem {}_unfold : {} = {}.
reflexivity.
Qed.
" ((egal $f) (egal $f) (render (eqn-rhs $e) ())))
         (format-args "Theorem {}_unfold : forall {}, {} {} = {}.
let {}. reflexivity.
Qed.
" ((egal $f) (join " " $ps) (egal $f) (join " " $ps) (render (fsubst (eqn-rhs $e) $ren) $sub) (join " " $ps))))))
; A step of a computation by a definition with no patterns: its unfolding.
(= (unfold-step $g $e $args)
   (let $b (fmatch-list (lhs-args $e) $args ())
     (if (== $b fail) (stuck (format-args "{} does not match" ((eqn-name $e))))
         (step (fsubst (eqn-rhs $e) $b)
           ((format-args "rewrite {}_unfold{}." ((egal $g) (join-sp (render-all $args ())))))))))

; A projection, through its structure's recursor: its value lies in the
; field's type, and on a constructor it is that field.
(= (projection-text $f $S $ctor $i $np)
   (let* (($ps (vars-of $np "a")) ($targs (map-vars $ps)) ($fs (struct-fields $S))
          ($m (length-of $fs))
          ($Fs (instantiate-field-types (field-fterms $fs (params-of $S) $targs) (map-vars (vars-of $m "y"))))
          ($sub (pos-subst $ps 0))
          ($layers (proj-layers $Fs 0))
          ($M (lam-text $layers (var (field-name $i)) ()))
          ($Ri (nth $Fs $i))
          ($E (egal $S)) ($P (if (== $np 0) "" (format-args " {}" ((join " " $ps)))))
          ($famT (if (== $np 0) $E (format-args "({}{})" ($E $P))))
          ($node (if (== $m 0) (format-args "{}_node{}" ((egal $ctor) $P))
                     (format-args "({}_node{} {})" ((egal $ctor) $P (join " " (vars-of $m "y")))))))
     (format-args "(** Projection: {}, field {} of {}. **)
Definition {} : {} := fun {} s => {}_rec{} {} s.
Theorem {}_In : {}forall s :e {}, {}{} s :e {}.
{}let s. assume Hs: s :e {}.
exact {}_rec_type{} (fun _ => {}) {} {} s Hs.
Qed.
Theorem {}_mk : {}{}{}{} {} = y{}.
{}{}prove {}_rec{} {} {} = y{}.
rewrite {}_iota0{} {}{}.
{}reflexivity.
Qed.
"
       ((nm $f) $i $S
        (egal $f) (fun-type (+ $np 1)) (join " " $ps) $E $P $M
        (egal $f) (forall-plain $ps) $famT (egal $f) $P (render $Ri ())
        (let-plain $ps) $famT
        $E $P (render $Ri ()) $M (hm-proof $layers (var (field-name $i)) () () $Ri)
        (egal $f) (forall-plain $ps) (proj-binders $layers) (egal $f) $P $node $i
        (let-plain $ps) (u-intros $layers ()) $E $P $M $node $i
        $E $P $M (proj-field-args $m)
        (beta-lines-plain $layers (var (field-name $i)))))))

(= (map-vars $ps) (if (== $ps ()) () (cons-atom (var (car-atom $ps)) (map-vars (cdr-atom $ps)))))
(= (field-fterms $fs $params $targs)
   (if (== $fs ()) ()
       (cons-atom (field-fterm (car-atom $fs) None $params $targs) (field-fterms (cdr-atom $fs) $params $targs))))
(= (proj-layers $Fs $i)
   (if (== $Fs ()) () (cons-atom (ly (field-name $i) (car-atom $Fs) fld $i) (proj-layers (cdr-atom $Fs) (+ $i 1)))))
(= (forall-plain $ps) (if (== $ps ()) "" (format-args "forall {}, " ((join " " $ps)))))
(= (let-plain $ps) (if (== $ps ()) "" (format-args "let {}. " ((join " " $ps)))))
(= (proj-binders $layers)
   (if (== $layers ()) ""
       (let $l (car-atom $layers)
         (format-args "forall {} :e {}, {}" ((ly-name $l) (render (ly-type $l) ()) (proj-binders (cdr-atom $layers)))))))
(= (proj-field-args $m)
   (join "" (let $js (range-from 0 $m) (map-atom $js $j (format-args " y{} Hy{}" ($j $j))))))
(= (beta-lines-plain $layers $body)
   (if (== $layers ()) ""
       (let* (($l (car-atom $layers)) ($z (ly-name $l)))
         (format-args "rewrite beta {} (fun {} => {}) {} H{}.
{}" ((render (ly-type $l) ()) $z (lam-text (cdr-atom $layers) $body ()) $z $z (beta-lines-plain (cdr-atom $layers) $body))))))

(= (function-text $f)
   (let $s (shape-of $f)
     (case $s
       (((projection $S $ctor $i $np) (projection-text $f $S $ctor $i $np))
        ((subsingleton $F) (subsingleton-text $f $F))
       ((structural $m $fam $eqs)
         (if (is-split $f)
             (if (and (dep-typed $f) (or (has-typing-proof $f) (all-closed (lean-eqns-of $f))))
                 (format-args "(** {}, from its equation theorems, split at argument {} **)
{}{}{}{}" ((nm $f) $m (format-args "{}{}" ((methods-lift-text $f $s) (definition-text $f $s))) (eqn-theorems $f $s $eqs 0)
                   (lean-eqn-theorems $f (lean-eqns-of $f))
                   (if (has-typing-proof $f) (typing-proof-theorem $f) (dep-in-theorem $f))))
             ; Typed by its recursor at the dependent motive, before the split's
             ; equations, whose betas use it.
             (if (dep-typed $f)
                 (format-args "(** {}, from its equation theorems, split at argument {} **)
{}{}{}{}{}" ((nm $f) $m (format-args "{}{}" ((methods-lift-text $f $s) (definition-text $f $s))) (in-theorem $f $s) (eqn-theorems $f $s $eqs 0)
                   (lean-eqn-theorems $f (lean-eqns-of $f)) (fn-canonical-theorem $f)))
                 (format-args "(** {}, from its equation theorems, split at argument {} **)
{}{}{}{}" ((nm $f) $m (format-args "{}{}" ((methods-lift-text $f $s) (definition-text $f $s))) (in-theorem $f $s) (eqn-theorems $f $s $eqs 0)
                   (lean-eqn-theorems $f (lean-eqns-of $f))))))
             (format-args "(** {}, from its equation theorems **)
{}{}{}{}" ((nm $f) (format-args "{}{}" ((methods-lift-text $f $s) (definition-text $f $s)))
               (if (has-typing-proof $f) (rec-in-theorem $f $s) (in-theorem $f $s))
               (if (has-typing-proof $f) (format-args "{}{}" ((eqn-theorems $f $s $eqs 0) (typing-proof-theorem $f))) (eqn-theorems $f $s $eqs 0))
               (if (== (fn-accs $f $m) ()) (unique-theorem $f $s) "")))))
        ((direct $e)
         (if (has-typing-proof $f)
             (format-args "(** {}, from its equation theorem **)
{}{}{}" ((nm $f) (definition-text $f $s) (direct-theorem $f $e) (typing-proof-theorem $f)))
         (if (and (dep-typed $f) (not (dep-has-typing $f)))
             (format-args "(** {}, from its equation theorem **)
{}{}{}" ((nm $f) (definition-text $f $s) (direct-theorem $f $e) (untyped-comment $f)))
             (format-args "(** {}, from its equation theorem **)
{}{}{}" ((nm $f) (definition-text $f $s) (direct-in-theorem $f $e) (direct-theorem $f $e))))))))))
; The generated statement of f's typing, with its proof written in Egal.
; Membership needs no universe levels: a type argument is any set, while a
; proposition argument ranges over LeanProp. A family argument comes with
; its meaning, in which the statement is read.
(= (typing-proof-theorem $f)
   (let* (($T (fn-type $f)) ($bs (type-binders-of $T 0)) ($R (type-result-of $T))
          ($xs (map-atom $bs $b (car-atom $b))) ($mb (meaning-binds $bs)))
     (format-args "(** {}'s type: the statement generated from Lean's, proved in Egal. **)
Theorem {}_In : {}{} {} :e {}.
PROOF-FILE {}_In
Qed.
{}" ((nm $f) (egal $f) (typing-binders $bs $mb)
   (egal $f) (join " " $xs) (render (fsubst $R $mb) ()) (egal $f) (canonical-theorem $f $bs $xs $R)))))
(= (meaning-binds $bs)
   (if (== $bs ()) ()
       (let (($x $A) $rest) ((car-atom $bs) (meaning-binds (cdr-atom $bs)))
         (if (is-family-type $A) (cons-atom ($x (var (meaning-name $x))) $rest) $rest))))
(= (typing-binders $bs $mb)
   (if (== $bs ()) ""
       (let* ((($x $A) (car-atom $bs)) ($rest (typing-binders (cdr-atom $bs) $mb)))
         (if (== $A (prop)) (format-args "forall {} :e LeanProp, {}" ($x $rest))
         (if (is-sort-term $A) (format-args "forall {}, {}" ($x $rest))
         (if (is-family-type $A)
             (format-args "forall {}, forall {}:{}, {}" ($x (meaning-name $x) (fun-type (family-arity $A)) $rest))
             (format-args "forall {} :e {}, {}" ($x (render (fsubst $A $mb) ()) $rest))))))))

; A direct definition lies in its result type: its right side does.  A
; type (RuleFamily := Tm -> Tm x Tm) lies in its universe.
(= (direct-in-theorem $f $e)
   (if (is-sort-term (fn-type $f)) (type-def-in-theorem $f $e) (direct-in-theorem-value $f $e)))
; (The sort's level is read by position: a pattern headed by sort would be
; evaluated, sort being a builtin.)
(= (type-def-in-theorem $f $e)
   (let $L (car-atom (cdr-atom (fn-type $f)))
     (if (not (== (get-metatype $L) Expression)) ""
     (if (not (== (car-atom $L) lvl)) ""
       (let $n (car-atom (cdr-atom $L))
         (if (> $n 0)
             (let $pf (type-in (eqn-rhs $e) (- $n 1) (natproof (- $n 1)))
               (if (== $pf None) ""
                   (format-args "Theorem {}_In : {} :e LeanSort {}.
rewrite LeanSort_S {} {}.
exact {}.
Qed.
" ((egal $f) (egal $f) $n (- $n 1) (natproof (- $n 1)) $pf))))
             ""))))))
; A proof that a closed type lies in the universe u: a product by
; LeanPi_LeanUniv, an admitted family by its universe lemma; None otherwise.
(= (type-in $T $u $hu)
   (case $T
     (((arrow $A $B) (type-in-pi "_" $A $B $u $hu))
      ((pi $x $A $B) (type-in-pi $x $A $B $u $hu))
      ((app $F $ps)
       (if (and (is-family $F) (not (prop-fam $F)))
           (let $pfs (type-in-list $ps $u $hu)
             (if (== $pfs None) None
                 (format-args "({}_type_In {}{} {}{})"
                   ((egal $F) (join "" (map-atom $ps $p (format-args "{} " ((render $p ()))))) $u $hu (join "" (map-atom $pfs $q (format-args " {}" ($q))))))))
           None))
      ($_ None))))
(= (type-in-pi $x $A $B $u $hu)
   (let* (($pa (type-in $A $u $hu)) ($pb (type-in $B $u $hu)))
     (if (or (== $pa None) (== $pb None)) None
         (format-args "(LeanPi_LeanUniv {} {} {} {} (fun {} => {}) (fun {} _ => {}))"
           ($u $hu (render $A ()) $pa $x (render $B ()) $x $pb)))))
(= (type-in-list $ts $u $hu)
   (if (== $ts ()) ()
       (let* (($p (type-in (car-atom $ts) $u $hu)) ($rest (type-in-list (cdr-atom $ts) $u $hu)))
         (if (or (== $p None) (== $rest None)) None (cons-atom $p $rest)))))
(= (direct-in-theorem-value $f $e)
   (let* (($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0))
          ($ren (param-renames (lhs-args $e) -1 0)) ($ks (pos-kinds $f))
          ($ctx (append-lists (pos-hyps $ks -1 0) (pos-tys $f $ks -1 0)))
          ($R (fsubst (eqn-type $e) $ren)) ($rhs (fsubst (eqn-rhs $e) $ren))
          ($cas (rhs-conv-claims $rhs $sub $ctx)))
     (format-args "Theorem {}_In : {}{} :e {}.
{}{}exact {}.
Qed.
"
       ((egal $f) (in-binders $f $ks -1 0 "" $sub)
        (if (== $n 0) (egal $f) (format-args "{} {}" ((egal $f) (join " " $ps)))) (render $R $sub)
        (in-intros $f $ks -1 0 "" $sub) (ca-claims $cas)
        (if (== $cas ()) (typ $rhs $sub $ctx) (rhs-typ-cl $rhs $sub $ctx $cas))))))
; A direct definition applying a function whose arguments need the reduction.
(= (rhs-conv-claims $rhs $sub $ctx)
   (case $rhs
     (((app $g $args)
       (if (is-function $g) (conv-arg-claims $args (arg-types $g $args) (pos-kinds $g) 0 $sub $ctx) ()))
      ($_ ()))))
(= (rhs-typ-cl $rhs $sub $ctx $cas)
   (case $rhs
     (((app $g $args)
       (format-args "({}_In {})" ((egal $g) (join " " (typ-args-cl $args (pos-kinds $g) (arg-types $g $args) $sub $ctx $cas 0))))))))

; ---- which functions are read, in order ----

(= (all-functions)
   (append-lists (collapse (match &self (LeanProjection $f $S $c $i $np) $f))
     (append-lists (subsingleton-recs (collapse (match &self (LeanRecursor $f $F) $f)))
                   (collapse (match &self (LeanFunction $f $thms) $f)))))

; Why a function is not read, or ok.
(= (prepared-readability $f)
   (let $cached (collapse (match &self (EgalPreparedReadability $f $why) $why))
     (if (== $cached ()) (why-not $f ()) (car-atom $cached))))
; Batch drivers call this after loading their complete, immutable inventory.
; Refreshing it discards the previous batch's answers; recursive checks still
; use their own stack rather than borrowing a partially computed answer.
(= (prepare-readability)
   (let $_clear
     (map-atom (collapse (match &self (EgalPreparedReadability $f $why) (prepared $f $why))) $entry
       (let (prepared $f $why) $entry (remove-atom &self (EgalPreparedReadability $f $why))))
     (map-atom (all-functions) $f
       (let $why (why-not $f ()) (add-atom &self (EgalPreparedReadability $f $why))))))

(= (why-not $f $stack)
   (if (is-intrinsic $f) ok
   (if (member-term $f $stack) "recursion through other functions"
   (if (unreconstructed-proofs $f) "erased proofs in the definition or its equations are not reconstructed"
   (if (split-with-proofs $f) "proofs inside a definition read through its patterns (not transported yet)"
   (if (proof-arg-untyped $f) "a proof argument, whose typing is not proved here (not transported yet)"
       (case (shape-of $f)
         (((refused $why) $why)
          ((subsingleton $F) ok)
          ($s (why-not-deps (fn-deps $f) (cons-atom $f $stack)))))))))))
(= (unreconstructed-proofs $f)
   (if (is-function $f)
       (if (has-typing-proof $f) False
           (if (eqns-mention-proof (lean-eqns-of $f))
               (not (automatic-proof-candidate $f)) False)) False))
; A function with a proof argument (h : a = b) is read only with a typing
; proof written in Egal: its typing needs the argument's proposition.
(= (proof-arg-untyped $f)
   (if (is-function $f)
       (if (has-proof-arg-hyp (lean-eqns-of $f))
           (if (has-typing-proof $f) False (not (automatic-proof-candidate $f))) False) False))
(= (has-proof-arg-hyp $eqs)
   (if (== $eqs ()) False (if (proof-hyp-in (eqn-binders (car-atom $eqs))) True (has-proof-arg-hyp (cdr-atom $eqs)))))
(= (proof-hyp-in $bs)
   (if (== $bs ()) False
       (case (car-atom $bs)
         (((hyp $x $P) (if (is-cond-hyp $P) (proof-hyp-in (cdr-atom $bs)) True))
          ($_ (proof-hyp-in (cdr-atom $bs)))))))
(= (split-with-proofs $f)
   (if (is-function $f)
       (if (is-split $f)
           (if (decision-by-definition $f) False
               (if (eqns-mention-proof (lean-eqns-of $f)) (not (automatic-proof-candidate $f)) False)) False)
       False))
; Candidate generation does not establish a theorem. Both target checkers
; must accept the emitted proofs before any computation is qualified. This
; gate keeps missing typing proofs and source equations as named refusals.
(= (text-has $text $part)
   (case (str:find $text $part) (((TextNotFound $_) False) ($_ True))))
(= (automatic-proof-candidate $f)
   (case (shape-of $f)
     (((structural $m $F $eqs) (generated-proof-candidate $f))
      ((direct $e) (generated-proof-candidate $f))
      ($_ False))))
(= (generated-proof-candidate $f)
   (let $candidates (collapse (function-text $f))
     (if (== (length-of $candidates) 1)
         (proof-candidate-text $f (car-atom $candidates)) False)))
(= (proof-candidate-text $f $text)
   (if (== (get-metatype $text) Grounded)
       (if (text-has $text "UNDECIDED") False
       (if (text-has $text "not proved here") False
       (if (text-has $text "PROOF-FILE") False
       (if (text-has $text (format-args "Theorem {}_In :" ((egal $f))))
           (candidate-equations-present (lean-eqns-of $f) $text) False)))) False))
(= (candidate-equations-present $eqs $text)
   (if (== $eqs ()) True
       (if (text-has $text (format-args "Theorem {} :" ((egal (eqn-name (car-atom $eqs))))))
           (candidate-equations-present (cdr-atom $eqs) $text) False)))
(= (eqns-mention-proof $eqs)
   (if (== $eqs ()) False (if (has-proof-term (eqn-rhs (car-atom $eqs))) True (eqns-mention-proof (cdr-atom $eqs)))))
(= (has-proof-term $t)
   (case $t
     (((proof) True)
      ((app $c $args) (has-proof-list $args))
      ((apv $g $args) (has-proof-list (cons-atom $g $args)))
      ((lam $x $T $b) (has-proof-term $b))
      ($_ False))))
(= (has-proof-list $ts) (if (== $ts ()) False (if (has-proof-term (car-atom $ts)) True (has-proof-list (cdr-atom $ts)))))

(= (why-not-deps $gs $stack)
   (if (== $gs ()) ok
       (let $why (why-not (car-atom $gs) $stack)
         (if (== $why ok) (why-not-deps (cdr-atom $gs) $stack)
             (format-args "applies {}, which is not read" ((car-atom $gs)))))))

(= (read-functions $fs)
   (if (== $fs ()) ()
       (let $rest (read-functions (cdr-atom $fs))
         (if (== (why-not (car-atom $fs) ()) ok) (cons-atom (car-atom $fs) $rest) $rest))))

(= (all-in $xs $ys)
   (if (== $xs ()) True
       (if (or (is-intrinsic (car-atom $xs)) (member-term (car-atom $xs) $ys)) (all-in (cdr-atom $xs) $ys) False)))
(= (remove-term $x $xs)
   (if (== $xs ()) () (if (== (car-atom $xs) $x) (cdr-atom $xs) (cons-atom (car-atom $xs) (remove-term $x (cdr-atom $xs))))))
(= (first-ready $ps $done)
   (if (== $ps ()) None (if (all-in (fn-deps (car-atom $ps)) $done) (car-atom $ps) (first-ready (cdr-atom $ps) $done))))
(= (topo $pending $done)
   (if (== $pending ()) $done
       (let $ready (first-ready $pending $done)
         (if (== $ready None) $done (topo (remove-term $ready $pending) (append-lists $done (cons-atom $ready ())))))))

(= (function-order) (let $fs (all-functions) (topo (read-functions $fs) ())))

(= (refusal-lines $fs)
   (if (== $fs ()) ()
       (let* (($f (car-atom $fs)) ($why (why-not $f ())) ($rest (refusal-lines (cdr-atom $fs))))
         (if (== $why ok) $rest (cons-atom (format-args "{}: {}" ((nm $f) $why)) $rest)))))

(= (proof-library-uses $f) (collapse (match &self (EgalTypingUses $f $key) $key)))
(= (proof-library-spec $key)
   (let $found (collapse (match &self (EgalProofLibrary $key $deps $files) (ProofLibrary $deps $files)))
     (if (== (length-of $found) 1) (car-atom $found)
         (let $_err (system:write stderr (format-args "proof library {} has no unique declaration\n" ($key)))
           (system:exit 1)))))
(= (proof-library-deps $f) (proof-libraries-deps (proof-library-uses $f)))
(= (proof-libraries-deps $keys)
   (if (== $keys ()) ()
       (let (ProofLibrary $deps $files) (proof-library-spec (car-atom $keys))
         (union-names $deps (proof-libraries-deps (cdr-atom $keys))))))
(= (proof-library-files $files)
   (if (== $files ()) ""
       (let* (($roots (collapse (match &self (EgalProofLibraryRoot $root) $root)))
              ($path (car-atom $files)))
         (if (== (length-of $roots) 1)
             (format-args "(** Embedded proof support: {} **)\n{}\n{}"
               ($path (fs:read-text (format-args "{}/{}" ((car-atom $roots) $path)))
                (proof-library-files (cdr-atom $files))))
             (let $_err (system:write stderr "proof library root is missing or ambiguous\n") (system:exit 1))))))
(= (proof-libraries-before $keys $seen)
   (if (== $keys ()) (ProofPreamble "" $seen)
       (let $key (car-atom $keys)
         (if (member-term $key $seen) (proof-libraries-before (cdr-atom $keys) $seen)
             (let* (((ProofLibrary $deps $files) (proof-library-spec $key))
                    ((ProofPreamble $tail $next) (proof-libraries-before (cdr-atom $keys) (cons-atom $key $seen))))
               (ProofPreamble (str:concat (proof-library-files $files) $tail) $next))))))
(= (ordered-function-sections $fs $seen)
   (if (== $fs ()) ()
       (let* (($f (car-atom $fs))
              ((ProofPreamble $prefix $next) (proof-libraries-before (proof-library-uses $f) $seen)))
         (cons-atom (str:concat $prefix (function-text $f))
           (ordered-function-sections (cdr-atom $fs) $next)))))
(= (source-equation-proof $owner $entry)
   (let ($equation $lemma) $entry
     (let $sources (collapse (match &self (LeanSourceEquations $owner $qs) $qs))
       (if (and (== (length-of $sources) 1) (member-term $equation (car-atom $sources)))
           (format-args "{}Theorem {} : {}.\nexact {}.\nQed.\n"
             ((receipt-comment $equation $owner) (egal $equation) (statement-text (eqn-of $equation)) $lemma))
           (let $_error (system:write stderr
             (format-args "source-equation proof {} is not an exported obligation of {}\n" ($equation $owner)))
             (system:exit 1))))))
(= (source-equation-sections $order)
   (collapse (match &self (EgalSourceEquationProofs $owner $files $entries)
     (if (member-term $owner $order)
         (str:concat (proof-library-files $files)
           (join "\n" (map-atom $entries $entry (source-equation-proof $owner $entry)))) ""))))
(= (source-hyp-names $bs)
   (if (== $bs ()) ()
       (case (car-atom $bs)
         (((hyp $name $P) (cons-atom $name (source-hyp-names (cdr-atom $bs))))
          ($_ (source-hyp-names (cdr-atom $bs)))))))
(= (signature-intros $bs)
   (str:concat (free-level-intros $bs) (stmt-intros $bs (free-levels $bs))))
(= (signature-prefix $bs)
   (let $free (free-levels $bs)
     (str:concat (join "" (map-atom $free $l (format-args "forall {}, nat_p {} -> " ($l $l))))
       (stmt-binders $bs $free))))
(= (intrinsic-type-proof $f $kind $bs $args $ctx)
   (case $kind
     ((type
       (case (car-atom $bs)
         (((type $A $u)
           (format-args "(Lean_Quot_type_In {} {} {} {} {})"
             ((render (nth $args 0) ()) (render (nth $args 1) ()) $u
              (if (== $u 0) "nat_0" (format-args "H_{}" ($u))) (typ (nth $args 0) () $ctx)))))))
      (constructor
       (format-args "(Lean_Quot_mk_In {} {} {} {} {})"
         ((render (nth $args 0) ()) (render (nth $args 1) ()) (typ (nth $args 1) () $ctx)
          (render (nth $args 2) ()) (typ (nth $args 2) () $ctx))))
      (lift
       (format-args "(Lean_Quot_lift_typed {} {} {} {} {} {} 0 {} {})"
         ((render (nth $args 0) ()) (render (nth $args 1) ()) (render (nth $args 2) ())
          (render (nth $args 3) ()) (typ (nth $args 3) () $ctx) (car-atom (source-hyp-names $bs))
          (render (nth $args 5) ()) (typ (nth $args 5) () $ctx)))))))
(= (intrinsic-type-contract $f)
   (case (intrinsic $f)
     (((primitive $kind $bs $R)
       (let* (($args (intrinsic-call-args $f)) ($ctx (stmt-ctx $bs)))
         (format-args "Theorem {}_source_type : {}{} :e {}.\n{}exact {}.\nQed.\n"
           ((egal $f) (signature-prefix $bs) (render (app $f $args) ()) (render $R ())
            (signature-intros $bs) (intrinsic-type-proof $f $kind $bs $args $ctx))))))))
(= (intrinsic-law-proof $f $e)
   (let* (($args (lhs-args $e)) ($ctx (stmt-ctx (eqn-binders $e)))
          ($hyp (car-atom (source-hyp-names (eqn-binders $e)))))
     (if (== $f Quot.mk)
         (let $y (nth (app-args (eqn-rhs $e)) 2)
           (format-args "(Lean_Quot_mk_sound {} {} {} {} {} {} {})"
             ((render (nth $args 0) ()) (render (nth $args 1) ())
              (render (nth $args 2) ()) (typ (nth $args 2) () $ctx) (render $y ()) (typ $y () $ctx) $hyp)))
         (let $x (nth (app-args (nth $args 5)) 2)
           (format-args "(Lean_Quot_lift_beta {} {} {} {} {} {} 0 {} {})"
             ((render (nth $args 0) ()) (render (nth $args 1) ()) (render (nth $args 2) ())
              (render (nth $args 3) ()) (typ (nth $args 3) () $ctx) $hyp (render $x ()) (typ $x () $ctx)))))))
(= (intrinsic-law-contracts $f)
   (join "\n" (collapse (match &self (LeanPrimitiveLaw $f $law)
     (let $e (eqn-of $law)
       (format-args "(** Kernel law: {} at the declared Type profile. **)\nTheorem {} : {}.\n{}exact {}.\nQed.\n"
         ($law (egal $law) (statement-text $e) (eqn-intros $e) (intrinsic-law-proof $f $e))))))))
(= (intrinsic-contracts)
   (collapse (match &self (LeanIntrinsic $f $kind $bs $R)
     (if (is-intrinsic $f)
         (let $laws (collapse (match &self (LeanPrimitiveLaw $f $law) $law))
           (if (== (length-of $laws) (if (== $kind type) 0 1))
               (str:concat (intrinsic-type-contract $f) (intrinsic-law-contracts $f))
               (let $_error (system:write stderr
                 (format-args "primitive {} has an incomplete or ambiguous kernel-law inventory\n" ($f)))
                 (system:exit 1)))) ""))))
(= (functions-section)
   (let $order (function-order)
     (append-lists (intrinsic-contracts)
       (append-lists (ordered-function-sections $order ()) (source-equation-sections $order)))))

; ---- reading CeTTa's answers (Represents) ----
; A CeTTa value is read at the Lean type of the computation: an integer at
; Nat as LeanNum, true and false at Bool, a constructor applied to its fields
; as the constructor's node at the type's parameters.

(= (sort-fterm $s $params $targs)
   (if (== (get-metatype $s) Expression)
       (if (== (car-atom $s) ->)
           (arrow (sort-fterm (nth $s 1) $params $targs) (sort-fterm (nth $s 2) $params $targs))
           (app (car-atom $s) (sort-fterms (cdr-atom $s) $params $targs)))
       (if (== $s Prop) (prop)
           (let $i (param-index $s $params 0)
             (if (>= $i 0) (nth $targs $i) (app $s ()))))))
(= (sort-fterms $ss $params $targs)
   (if (== $ss ()) () (cons-atom (sort-fterm (car-atom $ss) $params $targs) (sort-fterms (cdr-atom $ss) $params $targs))))

(= (field-fterm $fd $T $params $targs)
   (case $fd
     (((data $s) (sort-fterm $s $params $targs)) ((rec $is) $T)
      ((guard $p) (app (EgalLibrary proof-field) ((guard-fterm $p $params $targs)))))))

; Guard expressions use ordinary applications, including calls to the proved
; target library. Existing substitution and binder handling therefore apply.
(= (guard-fterm $p $params $targs)
   (let* (($template (guard-template $p $params)) ($bindings (guard-param-bindings $targs 0)))
     (csubst $template (used-bindings $bindings (fvs $template)))))
(= (guard-param-bindings $args $i)
   (if (== $args ()) ()
       (cons-atom ((GuardParam $i) (car-atom $args)) (guard-param-bindings (cdr-atom $args) (+ $i 1)))))
(= (guard-template $p $params)
   (let $number (closed-nat $p)
     (if (== $number None) (guard-template-open $p $params) (num $number))))
(= (guard-template-open $p $params)
   (case $p
     (((field $i) (var (GuardField $i)))
      ((bound $name) (var $name))
      ((const $name)
       (let $i (param-index $name $params 0)
         (if (>= $i 0) (var (GuardParam $i)) (sort-fterm $name () ()))))
      ((pi $name $A $B) (pi $name (guard-template $A $params) (guard-template $B $params)))
      ((project $owner $i $record)
       (app (EgalLibrary record-field $owner $i) ((guard-template $record $params))))
      ((app $f $x) (guard-apply (guard-template $f $params) (guard-template $x $params))))))
(= (guard-apply $f $x)
   (case $f
     (((app $c $as) (app $c (append-lists $as ($x))))
      ((apv $g $as) (apv $g (append-lists $as ($x))))
      ($_ (apv $f ($x))))))

(= (cetta-ctor-name $c)
   (if (== $c true) Bool.true (if (== $c false) Bool.false $c)))

(= (readback $v $T)
   (if (and (== $T (app Nat ())) (== (get-metatype $v) Grounded)) (num $v)
       (case $T
         (((app $fam $targs)
           (if (== (get-metatype $v) Expression)
               (readback-ctor (cetta-ctor-name (car-atom $v)) (cdr-atom $v) $fam $targs $T)
               (readback-ctor (cetta-ctor-name $v) () $fam $targs $T)))
          ($_ (stuck "an answer at a type that is not a family"))))))

(= (readback-ctor $c $vs $fam $targs $T)
   (if (not (is-ctor $c)) (stuck (format-args "{} is not a constructor" ((nm $c))))
   (if (not (== (family-of-ctor $c) $fam)) (stuck (format-args "{} is not a constructor of {}" ((nm $c) $fam)))
   (let* (($cs (constructors-of $fam)) ($fds (ctor-fields (nth $cs (ctor-index-in $cs $c 0)))))
     (if (not (== (length-of $fds) (length-of $vs))) (stuck "an answer with erased fields")
         (let $fields (readback-fields $vs $fds $T (params-of $fam) $targs)
           (if (== $fields stuck) (stuck "an unreadable field")
               (app $c (append-lists $targs $fields)))))))))

(= (readback-fields $vs $fds $T $params $targs)
   (if (== $vs ()) ()
       (let* (($r (readback (car-atom $vs) (field-fterm (car-atom $fds) $T $params $targs)))
              ($rest (readback-fields (cdr-atom $vs) (cdr-atom $fds) $T $params $targs)))
         (if (or (== $rest stuck) (is-stuck $r)) stuck (cons-atom $r $rest)))))

(= (is-stuck $x) (case $x (((stuck $why) True) ($_ False))))

; ---- replaying a computation ----

(= (is-value $t)
   (case $t
     (((num $k) True)
      ((var $x) False)
      ((prop) True)
      ((proof) True)
      ((canon $P) False)
      ((lam $x $T $b) True)
      ((arrow $A $B) True)
      ((pi $x $A $B) True)
      ((apv $f $args) False)
      ((app $c $args) (if (or (intrinsic-value $c) (or (is-ctor $c) (is-family $c))) (all-values $args) False)))))
(= (all-values $ts) (if (== $ts ()) True (if (is-value (car-atom $ts)) (all-values (cdr-atom $ts)) False)))

; The leftmost innermost application of a function.
(= (find-redex $t)
   (case $t
     (((num $k) None)
      ((var $x) None)
      ((prop) None)
      ((proof) None)
      ((canon $P) (let $inner (find-redex $P) (if (== $inner None) $t $inner)))
      ((lam $x $T $b) None)
      ((arrow $A $B) None)
      ((pi $x $A $B) None)
      ((apv $f $args)
       (let $inner (find-redex-list (cons-atom $f $args))
         (if (== $inner None) (case $f (((lam $x $T $b) $t) ($_ None))) $inner)))
      ((app $c $args)
       (if (is-cases-on $c) (find-cases-redex $t $c $args)
       (if (== $c ite) (find-ite-redex $t $args)
       (let $inner (find-redex-list $args)
         (if (== $inner None) (if (or (intrinsic-value $c) (or (is-ctor $c) (is-family $c))) None $t) $inner))))))))
; A case analysis evaluates its major premise, then only the chosen minor:
; the minors are not evaluated before the iota step selects one.  So does
; ite (Lean inlines it, macro_inline): its decision first, then one branch.
(= (find-ite-redex $t $args)
   (let $inner (find-redex-list (take-n $args 3))
     (if (== $inner None) (if (is-value (nth $args 2)) $t None) $inner)))
(= (find-cases-redex $t $c $args)
   (let* (($major (nth $args (+ (param-count (cases-family $c)) 1))) ($inner (find-redex $major)))
     (if (== $inner None) (if (is-value $major) $t None) $inner)))
(= (find-redex-list $ts)
   (if (== $ts ()) None
       (let $r (find-redex (car-atom $ts)) (if (== $r None) (find-redex-list (cdr-atom $ts)) $r))))

; Every occurrence is replaced, binder and Pi types included, as Megalodon's
; rewrite does; the printed instances of later steps must match its goal.
(= (replace-term $t $r $new)
   (if (== $t $r) $new
       (case $t
         (((app $c $args) (app $c (replace-terms $args $r $new)))
          ((apv $f $args) (apv (replace-term $f $r $new) (replace-terms $args $r $new)))
          ((lam $x $T $b) (lam $x (replace-term $T $r $new) (replace-term $b $r $new)))
          ((arrow $A $B) (arrow (replace-term $A $r $new) (replace-term $B $r $new)))
          ((pi $x $A $B) (pi $x (replace-term $A $r $new) (replace-term $B $r $new)))
          ((canon $P) (canon (replace-term $P $r $new)))
          ($_ $t)))))
(= (replace-terms $ts $r $new)
   (if (== $ts ()) () (cons-atom (replace-term (car-atom $ts) $r $new) (replace-terms (cdr-atom $ts) $r $new))))

(= (fmatch $p $t $b)
   (case $p
     (((var $x) (let $old (lookup-var-term $x $b None)
                  (if (== $old None) (cons-atom ($x $t) $b) (if (== $old $t) $b fail))))
      ((num $k) (if (== $t $p) $b fail))
      ((proof) $b)
      ((app $c $ps) (case $t (((app $d $ts) (if (== $c $d) (fmatch-list $ps $ts $b) fail)) ($_ fail)))))))
(= (fmatch-list $ps $ts $b)
   (if (== $ps ()) $b
       (let $b2 (fmatch (car-atom $ps) (car-atom $ts) $b)
         (if (== $b2 fail) fail (fmatch-list (cdr-atom $ps) (cdr-atom $ts) $b2)))))

; A proof that a closed type lies in LeanUniv 0.
(= (tin $T)
   (case $T
     (((app $fam $args)
       (if (== $args ()) (format-args "({}_type_In 0 nat_0)" ((egal $fam)))
           (format-args "({}_type_In {} 0 nat_0 {})" ((egal $fam) (join " " (render-all $args ())) (join " " (tin-all $args)))))))))
(= (tin-all $ts) (if (== $ts ()) () (cons-atom (tin-arg (car-atom $ts)) (tin-all (cdr-atom $ts)))))
; A proposition as a family's argument (Decidable (n <= m)) lies in the universe
; because it lies in LeanProp.
(= (tin-arg $a)
   (if (is-prop-term $a) (format-args "(Lean_prop_In_LeanUniv 0 nat_0 {} {})" ((render $a ()) (typ $a () ()))) (tin $a)))
(= (is-prop-term $a) (case $a (((app $c $as) (prop-fam $c)) ($_ False))))

; The arguments instantiating an equation theorem: level parameters at 0.
(= (inst-text $bs $b $levels) (inst-text-ctx $bs $b $levels ()))
(= (inst-text-ctx $bs $b $levels $ctx)
   (if (== $bs ()) ""
       (case (car-atom $bs)
         (((hyp $x $P) (format-args " {}{}" ((hyp-proof (fsubst $P $b)) (inst-text-ctx (cdr-atom $bs) $b $levels $ctx))))
          ((type $x $l)
           (let $T (lookup-var-term $x $b None)
             (if (or (== $l 0) (member-term $l $levels))
                 (format-args " {} {}{}" ((render $T ()) (tin $T) (inst-text-ctx (cdr-atom $bs) $b $levels $ctx)))
                 (format-args " 0 nat_0 {} {}{}" ((render $T ()) (tin $T) (inst-text-ctx (cdr-atom $bs) $b (cons-atom $l $levels) $ctx))))))
          ((term $x $ty)
           (let $v (lookup-var-term $x $b None)
             (format-args " {} {}{}" ((render $v ()) (typ-at $v (fsubst $ty $b) () $ctx) (inst-text-ctx (cdr-atom $bs) $b $levels $ctx)))))
          ((sort $x $l)
           (let $T (lookup-var-term $x $b None)
             (format-args "{} {} (In_eq_rs {} (LeanSort 1) (LeanUniv 0) (LeanSort_S 0 nat_0) {}){}"
               ((if (member-term $l $levels) "" " 1 nat_1") (render $T ()) (render $T ()) (tin $T)
                (inst-text-ctx (cdr-atom $bs) $b (cons-atom $l $levels) $ctx)))))))))

(= (both-nums $args)
   (case $args ((((num $a) (num $b)) True) ($_ False))))

(= (add-proof $a $b)
   (if (== $b 0) (format-args "rewrite add_nat_0R {}. reflexivity." ($a))
       (format-args "rewrite add_nat_SR {} {} {}. {}" ($a (- $b 1) (natproof (- $b 1)) (add-proof-tail $a (- $b 1))))))
(= (add-proof-tail $a $b)
   (if (== $b 0) (format-args "rewrite add_nat_0R {}. reflexivity." ($a))
       (format-args "rewrite add_nat_SR {} {} {}. {}" ($a (- $b 1) (natproof (- $b 1)) (add-proof-tail $a (- $b 1))))))

(= (arith-step $args $n)
   (case $args
     ((((num $a) (num $b))
       (let $c (+ $a $b)
         (if (< $c (num-bound))
             (step (num $c)
               ((format-args "claim A{}: add_nat {} {} = {}.
{ {} }" ($n $a $b $c (add-proof $a $b)))
                (format-args "rewrite LeanNum_add_eq {} {} {} {} {} A{}." ($a (natproof $a) $b (natproof $b) $c $n))))
             (step (num $c)
               ((let $sc (add-script $a $b 0 "S")
                  (format-args "claim A{}: add_nat {} {} = {}.
{}
{}exact {}.
{}" ($n (num-arg $a) (num-arg $b) (num-arg $c) "{" (cl-text $sc) (cl-pf $sc) "}")))
                (format-args "rewrite LeanNum_add_eq {} {} {} {} {} A{}."
                  ((num-arg $a) (num-natproof-d $a) (num-arg $b) (num-natproof-d $b) (num-arg $c) $n))))))))))

; Multiplication of numerals: the products c_j = a * j, each from the one
; before by mul_nat_SR and an addition.
(= (mul-claims $a $j $b $n)
   (if (> $j $b) ""
       (let* (($c (* $a $j)) ($prev (* $a (- $j 1))))
         (format-args "claim P{}_{}: mul_nat {} {} = {}.
{ {} }
{}" ($n $j $a $j $c
     (if (== $j 0) (format-args "exact mul_nat_0R {}." ($a))
         (format-args "rewrite mul_nat_SR {} {} {}. rewrite P{}_{}. {}" ($a (- $j 1) (natproof (- $j 1)) $n (- $j 1) (add-proof $a $prev))))
     (mul-claims $a (+ $j 1) $b $n))))))

(= (mul-step $args $n)
   (case $args
     ((((num $a) (num $b))
       (let $c (* $a $b)
         (if (< $c (num-bound))
             (step (num $c)
               ((mul-claims $a 0 $b $n)
                (format-args "rewrite LeanNum_mul_eq {} {} {} {} {} P{}_{}." ($a (natproof $a) $b (natproof $b) $c $n $b))))
             (step (num $c)
               ((let $sc (mul-script $a $b "S")
                  (format-args "claim P{}: mul_nat {} {} = {}.
{}
{}exact {}.
{}" ($n (num-arg $a) (num-arg $b) (num-arg $c) "{" (cl-text $sc) (cl-pf $sc) "}")))
                (format-args "rewrite LeanNum_mul_eq {} {} {} {} {} P{}."
                  ((num-arg $a) (num-natproof-d $a) (num-arg $b) (num-natproof-d $b) (num-arg $c) $n))))))))))

; Division and remainder of numerals, as CeTTa computes them: q and r
; computed, x = q y + r checked digit by digit, then the characterization of
; the read Nat.div and Nat.mod (Lean_Nat_div_num, Lean_Nat_mod_num in
; Library/NatDiv.mg), cited through an equation between the dividends, not
; a rewrite of a literal.
(= (div-num-args $args)
   (case $args
     ((((num $x) (num $y)) (> $y 0))
      ($_ False))))
; (cl claims name): mul_nat a b = a b, and add_nat a b = a + b.
(= (prod-claims $a $b $tag)
   (let $c (* $a $b)
     (if (if (== $a 0) (>= $b (num-bound)) False)
         (cl (format-args "claim P{}: mul_nat 0 {} = 0.
{ exact mul_nat_0L {} {}. }
" ($tag (num-arg $b) (num-arg $b) (num-natproof-d $b))) (format-args "P{}" ($tag)))
     (if (< $c (num-bound))
         (cl (mul-claims $a 0 $b $tag) (format-args "P{}_{}" ($tag $b)))
         (let $sc (mul-script $a $b "S")
           (cl (format-args "claim P{}: mul_nat {} {} = {}.
{}
{}exact {}.
{}
" ($tag (num-arg $a) (num-arg $b) (num-arg $c) "{" (cl-text $sc) (cl-pf $sc) "}")) (format-args "P{}" ($tag))))))))
(= (sum-claims $a $b $tag)
   (let $c (+ $a $b)
     (if (< $c (num-bound))
         (cl (format-args "claim A{}: add_nat {} {} = {}.
{ {} }
" ($tag $a $b $c (add-proof $a $b))) (format-args "A{}" ($tag)))
         (let $sc (add-script $a $b 0 "S")
           (cl (format-args "claim A{}: add_nat {} {} = {}.
{}
{}exact {}.
{}
" ($tag (num-arg $a) (num-arg $b) (num-arg $c) "{" (cl-text $sc) (cl-pf $sc) "}")) (format-args "A{}" ($tag)))))))
(= (divmod-step $g $args $n)
   (case $args
     ((((num $x) (num $y)) (if (< $y (num-bound)) (divmod-step-small $g $x $y $n) (divmod-step-big $g $x $y $n)))
      ($_ (stuck "a division of numerals")))))
; A divisor at or above the bound of literals is ordsucc (y - 1) in digits
; (succ-eq), and the remainder's bound r + d = y - 1 an addition of digits.
(= (divmod-step-big $g $x $y $n)
   (let* (($r (% $x $y)) ($q (idiv $x $y)) ($p (* $q $y)) ($y1 (- $y 1)) ($d (- $y1 $r))
          ($tag (format-args "Q{}" ($n))) ($tagb (format-args "R{}" ($n)))
          ($pc (prod-claims $q $y $tag)) ($sc (sum-claims $p $r $tag)) ($bc (sum-claims $r $d $tagb))
          ($X (num-arg $x)) ($Y (num-arg $y)) ($Q (num-arg $q)) ($R (num-arg $r)) ($Y1 (num-arg $y1))
          ($YS (format-args "(ordsucc {})" ($Y1)))
          ($sum (format-args "add_nat (mul_nat {} {}) {}" ($Q $YS $R)))
          ($div (== $g Nat.div))
          ($F (if $div "Lean_Nat_div" "Lean_Nat_mod"))
          ($thm (if $div "Lean_Nat_div_num_add" "Lean_Nat_mod_num_add"))
          ($V (if $div $Q $R)))
     (step (num (if $div $q $r))
       ((format-args "{}{}{}claim Ey{}: {} = {}.
{ exact {}. }
claim Cq{}: {} = {}.
{ rewrite Ey{}. rewrite {}. exact {}. }
claim Dq{}: {} (LeanNum {}) (LeanNum {}) = LeanNum {}.
{ exact eq_i_tra ({} (LeanNum {}) (LeanNum {})) ({} (LeanNum {}) (LeanNum {})) (LeanNum {})
    (f_eq_i (fun z => {} (LeanNum {}) (LeanNum z)) {} {} (eq_sym_i {} {} Ey{}))
    (eq_i_tra ({} (LeanNum {}) (LeanNum {})) ({} (LeanNum ({})) (LeanNum {})) (LeanNum {})
      (f_eq_i (fun z => {} (LeanNum z) (LeanNum {})) {} ({}) (eq_sym_i ({}) {} Cq{}))
      ({} {} {} {} {} {} {} {} {} {})). }
rewrite Dq{}."
         ((cl-text $pc) (cl-text $sc) (cl-text $bc)
          $n $YS $Y (succ-eq $y1)
          $n $sum $X $n (cl-pf $pc) (cl-pf $sc)
          $n $F $X $Y $V
          $F $X $Y $F $X $YS $V
          $F $X $Y $YS $YS $Y $n
          $F $X $YS $F $sum $YS $V
          $F $YS $X $sum $sum $X $n
          $thm $Y1 (num-natproof-d $y1) $R (num-natproof-d $r) (format-args "{} {}" ((num-arg $d) (num-natproof-d $d))) (cl-pf $bc) $Q (num-natproof-d $q) ""
          $n))))))
(= (divmod-step-small $g $x $y $n)
   (let $args ((num $x) (num $y))
   (case $args
     ((((num $x) (num $y))
       (let* (($r (% $x $y)) ($q (idiv $x $y)) ($p (* $q $y)) ($tag (format-args "Q{}" ($n)))
              ($pc (prod-claims $q $y $tag)) ($sc (sum-claims $p $r $tag))
              ($X (num-arg $x)) ($Y (num-arg $y)) ($Q (num-arg $q)) ($R (num-arg $r))
              ($sum (format-args "add_nat (mul_nat {} {}) {}" ($Q $Y $R)))
              ($div (== $g Nat.div))
              ($F (if $div "Lean_Nat_div" "Lean_Nat_mod"))
              ($thm (if $div "Lean_Nat_div_num" "Lean_Nat_mod_num"))
              ($V (if $div $Q $R)))
         (step (num (if $div $q $r))
           ((format-args "{}{}claim Cq{}: {} = {}.
{ rewrite {}. exact {}. }
claim Dq{}: {} (LeanNum {}) (LeanNum {}) = LeanNum {}.
{ exact eq_i_tra ({} (LeanNum {}) (LeanNum {})) ({} (LeanNum ({})) (LeanNum {})) (LeanNum {})
    (f_eq_i (fun z => {} (LeanNum z) (LeanNum {})) {} ({}) (eq_sym_i ({}) {} Cq{}))
    ({} {} {} {} {} {} {} {}). }
rewrite Dq{}."
             ((cl-text $pc) (cl-text $sc) $n $sum $X (cl-pf $pc) (cl-pf $sc)
              $n $F $X $Y $V
              $F $X $Y $F $sum $Y $V
              $F $Y $X $sum $sum $X $n
              $thm (- $y 1) (natproof (- $y 1)) $R (natproof $r) (inproof $r $y) $Q (num-natproof-d $q)
              $n))))))
      ($_ (stuck "a division of numerals"))))))

; A numeral at a pattern position: an equation with the literal 0 applies
; directly; otherwise the numeral is unfolded to its constructor, everywhere
; in the goal, as rewrite does.
(= (eqn-with-literal-zero $eqs $m)
   (if (== $eqs ()) None
       (if (== (nth (lhs-args (car-atom $eqs)) $m) (num 0)) (car-atom $eqs) (eqn-with-literal-zero (cdr-atom $eqs) $m))))

(= (numeral-step $eqs $m $k $args)
   (if (== $k 0)
       (let $e (eqn-with-literal-zero $eqs $m)
         (if (== $e None)
             (unfold (num 0) (app Nat.zero ()) ("rewrite LeanNum_0."))
             (eqn-step $e $args)))
       (unfold (num $k) (app Nat.succ ((num (- $k 1))))
         (unfold-num-lines $k))))

(= (eqn-step $e $args) (eqn-step-ctx $e $args ()))
(= (eqn-step-ctx $e $args $ctx)
   (let $b (fmatch-list (lhs-args $e) $args ())
     (if (== $b fail) (stuck (format-args "{} does not match" ((eqn-name $e))))
         (step (fsubst (eqn-rhs $e) $b)
           ((format-args "rewrite {}{}{}." ((egal (eqn-name $e))
               (join "" (map-atom (free-levels (eqn-binders $e)) $l " 0 nat_0"))
               (inst-text-ctx (eqn-binders $e) $b (free-levels (eqn-binders $e)) $ctx))))))))

; Closed propositions on numerals: a proof that 0 lies in P, or that it does not.
(= (le-chain $m $n)
   (if (== $n $m) (format-args "(Lean_Nat_le_refl_num {})" ($m))
       (format-args "(Lean_Nat_le_succ_num {} {} {} {})" ($m (- $n 1) (natproof (- $n 1)) (le-chain $m (- $n 1))))))

; Decisions between numerals are proved along unary chains, so only below
; the bound of literals; above it they are not decided here.
(= (small-nums $m $n) (if (< $m (num-bound)) (< $n (num-bound)) False))
; 0 below a positive numeral: its leading digits are positive (NumD_pos).
(= (pos-pf $k)
   (if (< $k (num-bound)) (format-args "(nat_0_in_ordsucc {} {})" ((- $k 1) (dnat (- $k 1))))
       (let* (($q (q-of $k)) ($d (d-of $k)))
         (format-args "(NumD_pos {} {} {} {} {})" ((num-arg $q) (num-natproof-d $q) (pos-pf $q) $d (dnat $d))))))
; ---- propositions between naturals, on their numerals ----
; A unfolded numeral (a successor of a numeral, the zero node) is the numeral
; again (LeanNum_S, LeanNum_0): a proposition is decided, proved and refuted
; on its numeral view, and the proof carried back by the equation between the
; two (f_eq_i on the hole, one step per unfolded numeral).
(= (num-node-in $t)
   (case $t
     (((app Nat.zero ()) $t)
      ((app Nat.succ ((num $k))) (if (< (+ $k 1) (num-bound)) $t None))
      ((app $c $args) (num-node-in-list $args))
      ((apv $f $args) (num-node-in-list (cons-atom $f $args)))
      ($_ None))))
(= (num-node-in-list $ts)
   (if (== $ts ()) None
       (let $r (num-node-in (car-atom $ts)) (if (== $r None) (num-node-in-list (cdr-atom $ts)) $r))))
(= (num-node-step $r)
   (case $r
     (((app Nat.zero ()) ((num 0) "(eq_sym_i (LeanNum 0) Lean_Nat_zero_node LeanNum_0)"))
      ((app Nat.succ ((num $k)))
       (let $k1 (+ $k 1)
         ((num $k1) (format-args "(eq_sym_i (LeanNum {}) (Lean_Nat_succ_node (LeanNum {})) (LeanNum_S {} {}))" ($k1 $k $k (natproof $k)))))))))
; (nview P' eq): eq proves P = P', or None when P is its own view.
(= (num-view $P) (num-view-acc $P ((render $P ())) ()))
(= (num-view-acc $P $ts $ps)
   (let $r (num-node-in $P)
     (if (== $r None) (nview $P (if (== $ps ()) None (chain-pf $ts $ps)))
         (let ($new $eq) (num-node-step $r)
           (let* (($P2 (replace-term $P $r $new))
                  ($cl (format-args "(fun ZcZ => {})" ((render (replace-term $P $r (var "ZcZ")) ()))))
                  ($pf (format-args "(f_eq_i {} {} {} {})" ($cl (render $r ()) (render $new ()) $eq))))
             (num-view-acc $P2 (append-lists $ts ((render $P2 ()))) (append-lists $ps ($pf))))))))
(= (decide-prop $P) (case (num-view $P) (((nview $V $eq) (decide-prop-0 $V)))))
(= (prove-prop $P)
   (case (num-view $P)
     (((nview $V $eq)
       (if (== $eq None) (prove-prop-0 $P)
           (let $pf (prove-prop-0 $V)
             (if (== $pf "UNDECIDED") $pf
                 (format-args "(In_eq_r 0 {} {} (eq_sym_i {} {} {}) {})" ((render $V ()) (render $P ()) (render $P ()) (render $V ()) $eq $pf)))))))))
(= (refute-prop $P)
   (case (num-view $P)
     (((nview $V $eq)
       (if (== $eq None) (refute-prop-0 $P)
           (let $pf (refute-prop-0 $V)
             (if (== $pf "UNDECIDED") $pf
                 (format-args "(fun H => {} (In_eq_r 0 {} {} {} H))" ($pf (render $P ()) (render $V ()) $eq)))))))))
(= (decide-prop-0 $P)
   (case $P
     (((app Exists ((app Nat ())
         (lam $x (app Nat ()) (app Eq ((app Nat ()) (num $n) (app Nat.mul ((num $d) (var $x))))))))
       (divides-numerals $d $n))
      ((app Nat.le ((num $m) (num $n))) (if (small-nums $m $n) (if (<= $m $n) True False) None))
      ((app Eq ((app Nat ()) (num $m) (num $n))) (if (small-nums $m $n) (if (== $m $n) True False) None))
      ((app Eq ($T (app $c ()) (app $d ()))) (if (both-ctors $c $d) (if (== $c $d) True False) None))
      ($_ None))))
; Equality of two nullary constructors of one family (Bool.true = Bool.true).
(= (both-ctors $c $d)
   (if (is-ctor $c) (if (is-ctor $d) (== (family-of-ctor $c) (family-of-ctor $d)) False) False))
(= (ctor-index $c) (ctor-index-in (constructors-of (family-of-ctor $c)) $c 0))
(= (noconf-refute $T $c $d)
   (let* (($i (ctor-index $c)) ($j (ctor-index $d)) ($E (egal (family-of-ctor $c)))
          ($eq (format-args "(LeanEq_sound {} {} {} 0 H)" ((render $T ()) (head-text $c) (head-text $d)))))
     (if (< $i $j)
         (format-args "(fun H => {}_noconf{}_{} {})" ($E $i $j $eq))
         (format-args "(fun H => {}_noconf{}_{} (eq_sym_i {} {} {}))" ($E $j $i (head-text $c) (head-text $d) $eq)))))

(= (prove-prop-0 $P)
   (case $P
     (((app Exists ((app Nat ())
         (lam $x (app Nat ()) (app Eq ((app Nat ()) (num $n) (app Nat.mul ((num $d) (var $x))))))))
       (if (divides-numerals $d $n)
           (let $q (if (== $d 0) 0 (idiv $n $d))
             (format-args "(LeanNatDivides_num_intro {} {} {} {} {} {} {})"
               ((num-arg $d) (num-natproof-d $d) (num-arg $n) (num-natproof-d $n)
                (num-arg $q) (num-natproof-d $q) (mul-eq $d $q)))) "UNDECIDED"))
      ((app Nat.le ((num $m) (num $n))) (le-chain $m $n))
      ((app Eq ((app Nat ()) (num $m) (num $n))) (format-args "(Lean_Eq_num_refl {})" ($m)))
      ((app Eq ($T $a $a)) (format-args "(Lean_Eq_refl_proof_ok {} {})" ((render $T ()) (render $a ()))))
      ((app Nat.le ($a $a)) (format-args "(Lean_Nat_le_refl_proof_ok {})" ((render $a ()))))
      ((arrow $A (app False ())) (format-args "(Lean_refute_0 {} {} {})" ((render $A ()) (typ $A () ()) (refute-prop $A))))
      ($_ "UNDECIDED"))))

(= (refute-prop-0 $P)
   (case $P
     (((app Exists ((app Nat ())
         (lam $x (app Nat ()) (app Eq ((app Nat ()) (num $n) (app Nat.mul ((num $d) (var $x))))))))
       (if (divides-numerals $d $n) "UNDECIDED"
           (let $r (if (== $d 0) $n (% $n $d))
             (format-args "(LeanNatDivides_num_refute {} {} {} {} {} {} (neq_of_In_l {} 0 {}) {})"
               ((num-arg $d) (num-natproof-d $d) (num-arg $n) (num-natproof-d $n)
                (num-arg $r) (num-natproof-d $r) (num-arg $r) (pos-pf $r) (mod-eq $n $d))))))
      ((app Nat.le ((num $m) (num $n)))
       (format-args "(Lean_Nat_le_num_not {} {} {} {} {})" ($m (natproof $m) $n (natproof $n) (inproof $n $m))))
      ((app Eq ((app Nat ()) (num $m) (num $n)))
       (if (small-nums $m $n)
           (format-args "(Lean_Eq_num_not {} {} {} {} {})" ($m (natproof $m) $n (natproof $n)
             (if (< $n $m) (format-args "(neq_of_In_l {} {} {})" ($m $n (inproof $n $m)))
                 (format-args "(neq_of_In_r {} {} {})" ($m $n (inproof $m $n))))))
       (if (== $n 0)
           (format-args "(Lean_Eq_num_not {} {} 0 nat_0 (neq_of_In_l {} 0 {}))" ((num-arg $m) (num-natproof-d $m) (num-arg $m) (pos-pf $m)))
       (if (== $m 0)
           (format-args "(Lean_Eq_num_not 0 nat_0 {} {} (neq_of_In_r 0 {} {}))" ((num-arg $n) (num-natproof-d $n) (num-arg $n) (pos-pf $n)))
           "UNDECIDED"))))
      ((app Eq ($T (app $c ()) (app $d ()))) (noconf-refute $T $c $d))
      ($_ "UNDECIDED"))))

; The canonical element of a decided proposition.
(= (canon-step $P)
   (case (decide-prop $P)
     ((True (step (app Decidable.isTrue ($P (proof)))
              ((format-args "rewrite Lean_DecCanon_true {} {}." ((render $P ()) (prove-prop $P))))))
      (False (step (app Decidable.isFalse ($P (proof)))
               ((format-args "rewrite Lean_DecCanon_false {} {}." ((render $P ()) (refute-prop $P))))))
      ($_ (stuck "a proposition this reading cannot decide")))))

; Case analysis on a constructor: the family's iota, then the minor applied
; to the fields.
(= (cases-step $c $args)
   (let* (($F (cases-family $c)) ($np (param-count $F)) ($ps (take-n $args $np))
          ($rest (drop-n $args (+ $np 1))) ($major (car-atom $rest)) ($minors (cdr-atom $rest)))
     (case $major
       (((app $K $kargs)
         (if (not (is-ctor $K)) (stuck "a case analysis of a value that is not a constructor")
             (let* (($cs (constructors-of $F)) ($k (ctor-index-in $cs $K 0)) ($fields (drop-n $kargs $np))
                    ($motive (nth $args $np)) ($R (motive-of $motive)) ($elim (has-cases-eliminator $F))
                    ($minor (if $elim (nth $minors $k) (wrap-minor $F $ps $R (nth $minors $k) $k)))
                    ($ihs (if $elim () (ih-terms $c $ps $motive $minors $fields (ctor-fields (nth $cs $k)))))
                    ($all (append-lists $fields $ihs)))
               (iota-then-betas (if (== $all ()) $minor (apv $minor $all))
                 (format-args "rewrite {}_{}{}{}{}{}." ((egal $F) (if $elim "casesOn_iota" "iota") $k (join-sp (render-all $ps ()))
                    (join-sp (render-all (if $elim $minors (wrap-minors $F $ps $R $minors 0)) ()))
                    (join-sp (typ-fields-at $fields (ctor-field-types $K $ps) () ()))))
                 ()))))
        ((num $k)
         (if (== $k 0) (unfold (num 0) (app Nat.zero ()) ("rewrite LeanNum_0."))
             (unfold (num $k) (app Nat.succ ((num (- $k 1))))
               (unfold-num-lines $k))))
        ($_ (stuck "a case analysis of a value that is not a constructor"))))))

(= (beta-step $r)
   (case $r
     (((apv (lam $x $T $b) $args)
       (let* (($v (car-atom $args)) ($body (fsubst $b (($x $v)))) ($rest (cdr-atom $args)))
         (step (if (== $rest ()) $body (apv $body $rest))
           ((format-args "rewrite beta {} {} {} {}." ((render $T ()) (meta-fun-text $x $b ()) (render $v ()) (typ-at $v $T () ()))))))))))

(= (step-of $r $n)
   (if (== $r None) (stuck "no step applies")
   (case $r
     (((apv $f $as) (beta-step $r))
      ((canon $P) (canon-step $P))
      ($_ (step-of-app $r $n))))))

(= (proj-step $g $args) (proj-step-ctx $g $args ()))
(= (proj-step-ctx $g $args $ctx)
   (case (proj-info $g)
     (((proj $S $ctor $i $np)
       (let $sv (nth $args $np)
         (case $sv
           (((app $c $cargs)
             (if (== $c $ctor)
                 (let* (($fields (drop-n $cargs $np)))
                   (step (nth $fields $i)
                     ((format-args "rewrite {}_mk{}{}." ((egal $g) (proj-params-text (take-n $args $np)) (join-sp (typ-fields $fields () $ctx)))))))
                 (stuck (format-args "{} applied to {}" ((nm $g) $c)))))
            ($_ (stuck (format-args "{} applied to a value that is not a constructor" ((nm $g))))))))))))
(= (proj-params-text $ps)
   (if (== $ps ()) "" (format-args " {}{}" ((render (car-atom $ps) ()) (proj-params-text (cdr-atom $ps))))))
(= (join-sp $xs) (if (== $xs ()) "" (format-args " {}" ((join " " $xs)))))

(= (step-of-app $r $n)
   (if (is-projection (app-head $r)) (proj-step (app-head $r) (app-args $r))
   (if (is-cases-on (app-head $r)) (cases-step (app-head $r) (app-args $r))
   (step-of-app-fn $r $n))))

(= (step-of-app-fn $r $n)
   (let* (($g (app-head $r)) ($args (app-args $r)))
     (if (and (== $g Nat.mul) (both-nums $args)) (mul-step $args $n)
     (if (and (== $g Nat.add) (both-nums $args)) (arith-step $args $n)
     (let $why (prepared-readability $g)
     (if (not (== $why ok)) (stuck (format-args "{} is not read: {}" ((nm $g) $why)))
     (if (and (or (== $g Nat.div) (== $g Nat.mod)) (div-num-args $args)) (divmod-step $g $args $n)
         (case (shape-of $g)
           (((primitive lift $bs $R) (quotient-lift-step $args))
            ((primitive $kind $bs $R) (stuck "a quotient primitive is not a reducible lift"))
            ((structural $m $fam $eqs)
             (let $hit (if (is-split $g) (lean-eqn-hit $g (lean-eqns-of $g) $args) None)
             (if (not (== $hit None)) (eqn-step $hit $args)
             (let $major (nth $args $m)
               (case $major
                 (((num $k) (numeral-step $eqs $m $k $args))
                  ($_ (if (not (is-ctor (app-head $major))) (stuck (format-args "{} recurs on a value that is not a constructor" ((nm $g))))
                          (let $e (eqn-for-ctor $eqs $m (app-head $major))
                            (if (and (== $major (app Nat.zero ())) (== (nth (lhs-args $e) $m) (num 0)))
                                (unfold (app Nat.zero ()) (num 0) ("rewrite <- LeanNum_0."))
                                (eqn-step $e $args)))))))))))
            ((direct $e) (unfold-step $g $e $args))
            ((subsingleton $F) (subsingleton-step $g $F $args)))))))))))

(= (quotient-lift-step $args)
   (case $args
     ((($A $relation $B $function $respect (app Quot.mk ($sourceA $sourceRelation $value)))
       (let $types (arg-types-raw Quot.lift $args)
         (step (apv $function ($value))
           ((format-args "rewrite Lean_Quot_lift_beta_value {} {} {} {} {} {} {} {} {} {}."
             ((render $A ()) (render $relation ()) (typ $relation () ()) (render $B ())
              (render $function ()) (typ $function () ()) (render $respect ())
              (typ-at $respect (nth $types 4) () ()) (render $value ()) (typ $value () ())))))))
      ($_ (stuck "a quotient lift requires a constructor representative")))))

; A split function at arguments one of Lean's own equations matches is
; rewritten by that equation at once (it is a proved theorem whatever the
; order of Lean's patterns); only an equation stated under hypotheses waits
; for the split and its case analyses.
; Only an equation the reading proves: for a split function, one with a
; pattern at the split column (lean-eqn-theorem); a variable there needs a
; proof by cases, so the split's own equations apply instead.
(= (lean-eqn-hit $g $eqs $args)
   (if (== $eqs ()) None
       (let $e (car-atom $eqs)
         (if (has-hyp (eqn-binders $e)) (lean-eqn-hit $g (cdr-atom $eqs) $args)
         (if (not (split-proved $g $e)) (lean-eqn-hit $g (cdr-atom $eqs) $args)
             (if (== (fmatch-list (lhs-args $e) $args ()) fail) (lean-eqn-hit $g (cdr-atom $eqs) $args) $e))))))
(= (split-proved $g $e)
   (if (is-split $g)
       (let $p (nth (lhs-args $e) (shape-m (shape-of $g)))
         (if (== $p (num 0)) True (is-ctor-pat (pattern-of $p))))
       True))

; The largest numeral of a term.
(= (max-num $t)
   (case $t
     (((num $k) $k)
      ((app $c $args) (max-num-list $args 0))
      ((apv $f $args) (max-num-list (cons-atom $f $args) 0))
      ((lam $x $T $b) (max-num-list ($T $b) 0))
      ((arrow $A $B) (max-num-list ($A $B) 0))
      ((pi $x $A $B) (max-num-list ($A $B) 0))
      ($_ 0))))
(= (max-num-list $ts $acc)
   (if (== $ts ()) $acc
       (let $k (max-num (car-atom $ts)) (max-num-list (cdr-atom $ts) (if (> $k $acc) $k $acc)))))

; Replay the left side to a value; numeral unfolding rewrites both sides.
; Numerals above the bound are digits, so their size stays logarithmic.
(= (replay $t $rhs $n $acc)
   (if (is-value $t) (done $t $rhs $acc)
   (if (> $n 2000) (stuck "more than 2000 steps")
       (let* (($r (find-redex $t)) ($st (step-of $r $n)))
         (case $st
           (((step $new $lines0)
             (let* (($lines (robust-beta $t $r $lines0))
                    ($t2 (replace-term $t $r $new))
                    ($folded (fold-step $t2 $rhs $acc $lines)))
               (case $folded (((folded $t3 $rhs3 $acc3) (replay $t3 $rhs3 (+ $n 1) $acc3))))))
            ((unfold $old $new $lines)
             (replay (replace-term $t $old $new) (replace-term $rhs $old $new) (+ $n 1) (append-lists $acc $lines)))
            ((stuck $why) (stuck $why))))))))

; ---- beta with the reduct written out ----
; Megalodon's rewrite finds its first match up to beta and delta, then
; replaces only the copies syntactically equal to that instance.  The beta
; lemma's right side is a meta-level application (F x), so after it the goal
; holds a redex the model has reduced; when the redex occurs more than once,
; a later rewrite would take one copy only.  There the beta step cites the
; lemma through eq_i_tra with the reduct written out.
(= (count-occ $t $r)
   (if (== $t $r) 1
       (case $t
         (((app $c $args) (count-occ-list $args $r))
          ((apv $f $args) (count-occ-list (cons-atom $f $args) $r))
          ((lam $x $T $b) (count-occ-list ($T $b) $r))
          ((pi $x $A $B) (count-occ-list ($A $B) $r))
          ((arrow $A $B) (count-occ-list ($A $B) $r))
          ((canon $P) (count-occ $P $r))
          ($_ 0)))))
(= (count-occ-list $ts $r) (if (== $ts ()) 0 (+ (count-occ (car-atom $ts) $r) (count-occ-list (cdr-atom $ts) $r))))
; After an iota the minor's betas are written out always: the case analysis
; does not see how often its redex occurs.
(= (written-beta $r $lines)
   (case $r
     (((apv (lam $x $T $b) $args)
       (if (not (== (length-of $lines) 1)) $lines
           (let $pf (eq-of-line (car-atom $lines))
             (if (== $pf None) $lines
                 (let* (($L (render (apv (lam $x $T $b) (cons-atom (car-atom $args) ())) ()))
                        ($R (render (csubst $b (($x (car-atom $args)))) ())))
                   ((format-args "rewrite (eq_i_tra {} {} {} ({}) (Lean_eq_refl {}))." ($L $R $R $pf $R))))))))
      ($_ $lines))))
(= (robust-beta $t $r $lines)
   (case $r
     (((apv (lam $x $T $b) $args)
       (if (< (count-occ $t $r) 2) $lines
           (if (not (== (length-of $lines) 1)) $lines
               (let $pf (eq-of-line (car-atom $lines))
                 (if (== $pf None) $lines
                     (let* (($L (render (apv (lam $x $T $b) (cons-atom (car-atom $args) ())) ()))
                            ($R (render (fsubst $b (($x (car-atom $args)))) ())))
                       ((format-args "rewrite (eq_i_tra {} {} {} ({}) (Lean_eq_refl {}))." ($L $R $R $pf $R)))))))))
      ($_ $lines))))

; ---- numerals in digits ----
; Above the bound a numeral is its digits (Library/Digits.mg).  Equations
; between numerals are proof terms: views of a numeral as q :: d, the digit
; laws, the tables of literals and digit sums, chained by transitivity.  No
; literal is rewritten (a literal is a chain inside every larger one).
(= (q-of $k) (idiv $k (num-radix)))
(= (d-of $k) (% $k (num-radix)))
(= (qd-text $q $d) (format-args "({} :: {})" ((num-arg $q) $d)))
(= (refl-pf $t) (format-args "(Lean_eq_refl {})" ($t)))
(= (sym-pf $x $y $p) (format-args "(eq_sym_i {} {} {})" ($x $y $p)))
(= (last-of $xs) (if (== (cdr-atom $xs) ()) (car-atom $xs) (last-of (cdr-atom $xs))))
; t0 = tn from the proofs of t0 = t1, ..., t(n-1) = tn.
(= (chain-pf $ts $ps)
   (if (== (cdr-atom $ps) ()) (car-atom $ps)
       (format-args "(eq_i_tra {} {} {} {} {})"
         ((car-atom $ts) (nth $ts 1) (last-of $ts) (car-atom $ps) (chain-pf (cdr-atom $ts) (cdr-atom $ps))))))
; k = q :: d.
(= (view-pf $k)
   (if (< $k (num-radix)) (sym-pf (qd-text 0 $k) (num-arg $k) (format-args "(NumD_zero {} {})" ($k (dnat $k))))
       (if (< $k (num-bound)) (format-args "NumD_lit_{}" ($k))
           (refl-pf (num-arg $k)))))
; q :: d = the numeral of radix * q + d.
(= (unview-pf $q $d)
   (let $v (+ (* (num-radix) $q) $d)
     (if (>= $v (num-bound)) (refl-pf (qd-text $q $d))
         (if (>= $v (num-radix)) (sym-pf (num-arg $v) (qd-text $q $d) (format-args "NumD_lit_{}" ($v)))
             (format-args "(NumD_zero {} {})" ($d (dnat $d)))))))
; add_nat a b = a + b, and ordsucc (add_nat a b) = a + b + 1.
; A zero summand ends the recursion: add_nat_0R, add_nat_0L, and a carry
; into it is a successor.
(= (add-eq $a $b)
   (if (and (< $a (num-radix)) (< $b (num-radix))) (format-args "Dadd_{}_{}" ($a $b))
   (if (== $b 0) (format-args "(add_nat_0R {})" ((num-arg $a)))
   (if (== $a 0) (format-args "(add_nat_0L {} {})" ((num-arg $b) (num-natproof-d $b)))
       (add-digits $a $b 0)))))
(= (addc-eq $a $b)
   (if (and (< $a (num-radix)) (< $b (num-radix))) (format-args "Daddc_{}_{}" ($a $b))
   (if (== $b 0)
       (chain-pf ((format-args "(ordsucc (add_nat {} 0))" ((num-arg $a))) (format-args "(ordsucc {})" ((num-arg $a))) (num-arg (+ $a 1)))
                 ((format-args "(ordsucc_cong (add_nat {} 0) {} (add_nat_0R {}))" ((num-arg $a) (num-arg $a) (num-arg $a))) (succ-eq $a)))
   (if (== $a 0)
       (chain-pf ((format-args "(ordsucc (add_nat 0 {}))" ((num-arg $b))) (format-args "(ordsucc {})" ((num-arg $b))) (num-arg (+ $b 1)))
                 ((format-args "(ordsucc_cong (add_nat 0 {}) {} (add_nat_0L {} {}))" ((num-arg $b) (num-arg $b) (num-arg $b) (num-natproof-d $b))) (succ-eq $b)))
       (add-digits $a $b 1)))))
(= (add-digits $a $b $c)
   (let* (($R (num-radix)) ($qa (q-of $a)) ($da (d-of $a)) ($qb (q-of $b)) ($db (d-of $b))
          ($A (num-arg $a)) ($B (num-arg $b)) ($QA (num-arg $qa)) ($QB (num-arg $qb))
          ($s (+ (+ $da $db) $c)) ($v (+ (+ $a $b) $c))
          ($Q (format-args "(add_nat {} {})" ($QA $QB)))
          ($sum (format-args "(add_nat {} {})" ($A $B)))
          ($lhs (if (== $c 0) $sum (format-args "(ordsucc {})" ($sum))))
          ($v1 (format-args "(add_nat {} {})" ((qd-text $qa $da) (qd-text $qb $db))))
          ($t1 (if (== $c 0) $v1 (format-args "(ordsucc {})" ($v1))))
          ($c1 (format-args "(add_nat_cong {} {} {} {} {} {})" ($A (qd-text $qa $da) $B (qd-text $qb $db) (view-pf $a) (view-pf $b))))
          ($p1 (if (== $c 0) $c1 (format-args "(ordsucc_cong {} {} {})" ($sum $v1 $c1))))
          ($dsum (if (== $c 0) (format-args "(add_nat {} {})" ($da $db)) (format-args "(ordsucc (add_nat {} {}))" ($da $db))))
          ($t2 (format-args "({} :: {})" ($Q $dsum)))
          ($p2 (format-args "({} {} {} {} {} {} {} {} {})"
                 ((if (== $c 0) "NumD_add" "NumD_addc") $QA (num-natproof-d $qa) $QB (num-natproof-d $qb) $da (dnat $da) $db (dnat $db))))
          ($t3 (format-args "({} :: {})" ($Q $s)))
          ($p3 (format-args "(NumD_cong {} {} {} {} {} {})"
                 ($Q $Q $dsum $s (refl-pf $Q) (format-args "{}_{}_{}" ((if (== $c 0) "Dadd" "Daddc") $da $db))))))
     (if (< $s $R)
         (chain-pf ($lhs $t1 $t2 $t3 (qd-text (+ $qa $qb) $s) (num-arg $v))
                   ($p1 $p2 $p3
                    (format-args "(NumD_cong {} {} {} {} {} {})" ($Q (num-arg (+ $qa $qb)) $s $s (add-eq $qa $qb) (refl-pf $s)))
                    (unview-pf (+ $qa $qb) $s)))
         (let* (($s1 (- $s $R)) ($SQ (format-args "(ordsucc {})" ($Q))) ($q1 (+ (+ $qa $qb) 1)))
           (chain-pf ($lhs $t1 $t2 $t3 (format-args "({} :: add_nat {} {})" ($Q $R $s1)) (format-args "({} :: {})" ($SQ $s1))
                      (qd-text $q1 $s1) (num-arg $v))
                     ($p1 $p2 $p3
                      (format-args "(NumD_cong {} {} {} (add_nat {} {}) {} Dsplit_{})" ($Q $Q $s $R $s1 (refl-pf $Q) $s))
                      (format-args "(NumD_carry {} (add_nat_p {} {} {} {}) {} {})" ($Q $QA (num-natproof-d $qa) $QB (num-natproof-d $qb) $s1 (dnat $s1)))
                      (format-args "(NumD_cong {} {} {} {} {} {})" ($SQ (num-arg $q1) $s1 $s1 (addc-eq $qa $qb) (refl-pf $s1)))
                      (unview-pf $q1 $s1)))))))
; Proof terms for arithmetic needed inside an erased branch hypothesis.
; The ordinary replay still shares its larger calculations through claims.
(= (divides-numerals $d $n) (if (== $d 0) (== $n 0) (== (% $n $d) 0)))
(= (mul-eq $a $b)
   (let $A (num-arg $a)
     (if (== $b 0) (format-args "(mul_nat_0R {})" ($A))
     (if (< $b (num-radix))
         (let* (($m (- $b 1)) ($M (num-arg $m)) ($p (* $a $m)) ($P (num-arg $p)))
           (chain-pf
             ((format-args "(mul_nat {} {})" ($A (num-arg $b)))
              (format-args "(add_nat {} (mul_nat {} {}))" ($A $A $M))
              (format-args "(add_nat {} {})" ($A $P)) (num-arg (* $a $b)))
             ((format-args "(mul_nat_SR {} {} {})" ($A $M (num-natproof-d $m)))
              (format-args "(f_eq_i (fun z => add_nat {} z) (mul_nat {} {}) {} {})" ($A $A $M $P (mul-eq $a $m)))
              (add-eq $a $p))))
         (let* (($q (q-of $b)) ($d (d-of $b)) ($B (num-arg $b)) ($Q (num-arg $q))
                ($x (* $a $q)) ($y (* $a $d)) ($x10 (* (num-radix) $x)))
           (chain-pf
             ((format-args "(mul_nat {} {})" ($A $B))
              (format-args "(mul_nat {} {})" ($A (qd-text $q $d)))
              (format-args "(add_nat (mul_nat {} {} :: 0) (mul_nat {} {}))" ($A $Q $A $d))
              (format-args "(add_nat {} {})" ((qd-text $x 0) (num-arg $y)))
              (format-args "(add_nat {} {})" ((num-arg $x10) (num-arg $y))) (num-arg (* $a $b)))
             ((format-args "(f_eq_i (fun z => mul_nat {} z) {} {} {})" ($A $B (qd-text $q $d) (view-pf $b)))
              (format-args "(mul_NumD {} {} {} {} {} {})" ($A (num-natproof-d $a) $Q (num-natproof-d $q) $d (dnat $d)))
              (format-args "(add_nat_cong (mul_nat {} {} :: 0) {} (mul_nat {} {}) {} (NumD_cong (mul_nat {} {}) {} 0 0 {} (Lean_eq_refl 0)) {})"
                ($A $Q (qd-text $x 0) $A $d (num-arg $y) $A $Q (num-arg $x) (mul-eq $a $q) (mul-eq $a $d)))
              (format-args "(f_eq_i (fun z => add_nat z {}) {} {} {})" ((num-arg $y) (qd-text $x 0) (num-arg $x10) (unview-pf $x 0)))
              (add-eq $x10 $y))))))))

(= (mod-eq $n $d)
   (if (== $d 0)
       (format-args "(Lean_mod_zero (LeanNum {}) (LeanNum_In {} {}))" ((num-arg $n) (num-arg $n) (num-natproof-d $n)))
       (let* (($q (idiv $n $d)) ($r (% $n $d)) ($p (* $q $d)) ($d1 (- $d 1)) ($gap (- $d1 $r))
              ($N (num-arg $n)) ($D (num-arg $d)) ($Q (num-arg $q)) ($R (num-arg $r)) ($D1 (num-arg $d1))
              ($DS (format-args "(ordsucc {})" ($D1)))
              ($sum (format-args "(add_nat (mul_nat {} {}) {})" ($Q $DS $R)))
              ($eq (chain-pf
                     ($sum (format-args "(add_nat (mul_nat {} {}) {})" ($Q $D $R))
                      (format-args "(add_nat {} {})" ((num-arg $p) $R)) $N)
                     ((format-args "(f_eq_i (fun z => add_nat (mul_nat {} z) {}) {} {} {})" ($Q $R $DS $D (succ-eq $d1)))
                      (format-args "(f_eq_i (fun z => add_nat z {}) (mul_nat {} {}) {} {})" ($R $Q $D (num-arg $p) (mul-eq $q $d)))
                      (add-eq $p $r)))))
         (chain-pf
           ((format-args "(Lean_Nat_mod (LeanNum {}) (LeanNum {}))" ($N $D))
            (format-args "(Lean_Nat_mod (LeanNum {}) (LeanNum {}))" ($N $DS))
            (format-args "(Lean_Nat_mod (LeanNum {}) (LeanNum {}))" ($sum $DS))
            (format-args "(LeanNum {})" ($R)))
           ((format-args "(f_eq_i (fun z => Lean_Nat_mod (LeanNum {}) (LeanNum z)) {} {} {})"
              ($N $D $DS (sym-pf $DS $D (succ-eq $d1))))
            (format-args "(f_eq_i (fun z => Lean_Nat_mod (LeanNum z) (LeanNum {})) {} {} {})"
              ($DS $N $sum (sym-pf $sum $N $eq)))
            (format-args "(Lean_Nat_mod_num_add {} {} {} {} {} {} {} {} {})"
              ($D1 (num-natproof-d $d1) $R (num-natproof-d $r) (num-arg $gap) (num-natproof-d $gap)
               (add-eq $r $gap) $Q (num-natproof-d $q))))))))

; ---- arithmetic between numerals, as scripts ----
; An equation between numerals is proved by a script: each operand prefix's
; nat_p fact once, then one claim per digit, citing the claim of the digits
; before it and a step lemma (NumD_add_step and its carry forms).  A result
; is (cl claims proof): the claims to state, and the name or term proving the
; equation.  Claim names carry the tag of their equation.
(= (cl-text $c) (case $c (((cl $t $p) $t))))
(= (cl-pf $c) (case $c (((cl $t $p) $p))))
(= (nat-ref $v $tag $k) (if (< $v (num-bound)) (format-args "Dnat_{}" ($v)) (format-args "{}N{}" ($tag $k))))
(= (nat-claims $v $tag $k)
   (if (< $v (num-bound)) ""
       (format-args "{}claim {}N{}: nat_p {}.
{} exact NumD_p {} {} {} Dnat_{}. {}
" ((nat-claims (q-of $v) $tag (+ $k 1)) $tag $k (num-arg $v) "{" (num-arg (q-of $v)) (nat-ref (q-of $v) $tag (+ $k 1)) (d-of $v) (d-of $v) "}"))))
(= (lhs-text $A $B $c)
   (if (== $c 0) (format-args "(add_nat {} {})" ($A $B)) (format-args "(ordsucc (add_nat {} {}))" ($A $B))))
(= (digit-fact $da $db $c $s $c1 $s1)
   (let $base (format-args "{}_{}_{}" ((if (== $c 0) "Dadd" "Daddc") $da $db))
     (if (== $c1 0) $base
         (format-args "(eq_i_tra {} {} (add_nat {} {}) {} Dsplit_{})" ((lhs-text $da $db $c) $s (num-radix) $s1 $base $s)))))
(= (view-cong $a $b $c $qa $da $qb $db)
   (let $p (format-args "(add_nat_cong {} {} {} {} {} {})" ((num-arg $a) (qd-text $qa $da) (num-arg $b) (qd-text $qb $db) (view-pf $a) (view-pf $b)))
     (if (== $c 0) $p
         (format-args "(ordsucc_cong (add_nat {} {}) (add_nat {} {}) {})" ((num-arg $a) (num-arg $b) (qd-text $qa $da) (qd-text $qb $db) $p)))))
; lhs(a, b, c) = a + b + c at level k, the operands prefixes of the
; equation's (their nat_p claims tagged $ta, $tb).
(= (add-claims $a $b $c $k $ta $tb $tag)
   (if (and (< $a (num-radix)) (< $b (num-radix))) (cl "" (format-args "{}_{}_{}" ((if (== $c 0) "Dadd" "Daddc") $a $b)))
   (if (or (== $a 0) (== $b 0)) (cl "" (if (== $c 0) (add-eq $a $b) (addc-eq $a $b)))
   (let* (($R (num-radix)) ($qa (q-of $a)) ($da (d-of $a)) ($qb (q-of $b)) ($db (d-of $b))
          ($s (+ (+ $da $db) $c)) ($c1 (if (>= $s $R) 1 0)) ($s1 (if (>= $s $R) (- $s $R) $s))
          ($sub (add-claims $qa $qb $c1 (+ $k 1) $ta $tb $tag))
          ($q (+ (+ $qa $qb) $c1)) ($v (+ (+ $a $b) $c))
          ($lemma (if (== $c 0) (if (== $c1 0) "NumD_add_step" "NumD_add_carry") (if (== $c1 0) "NumD_addc_step" "NumD_addc_carry")))
          ($core (format-args "({} {} {} {} {} {} Dnat_{} {} Dnat_{} {} {}{} {} {})"
                   ($lemma (num-arg $qa) (nat-ref $qa $ta (+ $k 1)) (num-arg $qb) (nat-ref $qb $tb (+ $k 1)) $da $da $db $db
                    (num-arg $q) $s1 (if (== $c1 0) "" (format-args " Dnat_{}" ($s1))) (cl-pf $sub) (digit-fact $da $db $c $s $c1 $s1))))
          ($lhsT (lhs-text (num-arg $a) (num-arg $b) $c))
          ($lhsV (lhs-text (qd-text $qa $da) (qd-text $qb $db) $c))
          ($rhsV (qd-text $q $s1)) ($rhsT (num-arg $v))
          ($pf1 (if (and (>= $a (num-bound)) (>= $b (num-bound))) $core
                    (format-args "(eq_i_tra {} {} {} {} {})" ($lhsT $lhsV $rhsV (view-cong $a $b $c $qa $da $qb $db) $core))))
          ($pf (if (>= $v (num-bound)) $pf1
                   (format-args "(eq_i_tra {} {} {} {} {})" ($lhsT $rhsV $rhsT $pf1 (unview-pf $q $s1))))))
     (cl (format-args "{}claim {}E{}: {} = {}.
{} exact {}. {}
" ((cl-text $sub) $tag $k $lhsT $rhsT "{" $pf "}"))
         (format-args "{}E{}" ($tag $k)))))))
(= (add-script $a $b $c $tag)
   (let* (($ta (format-args "{}a" ($tag))) ($tb (format-args "{}b" ($tag))) ($sub (add-claims $a $b $c 0 $ta $tb $tag)))
     (cl (format-args "{}{}{}" ((nat-claims $a $ta 0) (nat-claims $b $tb 0) (cl-text $sub))) (cl-pf $sub))))
; mul_nat a b = a * b: by a digit, repeated addition; by digits, a shift
; (q :: 0) and an addition.  $na is a's nat_p proof.
(= (mul-claims-d $a $b $na $tag)
   (let $A (num-arg $a)
     (if (== $b 0) (cl "" (format-args "(mul_nat_0R {})" ($A)))
         (if (< $b (num-radix))
             (let* (($m (- $b 1)) ($pm (* $a $m)) ($ab (* $a $b))
                    ($sm (mul-claims-d $a $m $na (format-args "{}m" ($tag)))) ($sa (add-script $a $pm 0 (format-args "{}s" ($tag)))))
               (cl (format-args "{}{}claim {}M: mul_nat {} {} = {}.
{} exact {}. {}
" ((cl-text $sm) (cl-text $sa) $tag $A $b (num-arg $ab) "{"
   (chain-pf ((format-args "(mul_nat {} {})" ($A $b)) (format-args "(add_nat {} (mul_nat {} {}))" ($A $A $m))
              (format-args "(add_nat {} {})" ($A (num-arg $pm))) (num-arg $ab))
             ((format-args "(mul_nat_SR {} {} Dnat_{})" ($A $m $m))
              (format-args "(add_nat_cong {} {} (mul_nat {} {}) {} {} {})" ($A $A $A $m (num-arg $pm) (refl-pf $A) (cl-pf $sm)))
              (cl-pf $sa)))
   "}"))
                   (format-args "{}M" ($tag))))
             (let* (($qb (q-of $b)) ($db (d-of $b)) ($B (num-arg $b)) ($QB (num-arg $qb))
                    ($x (* $a $qb)) ($y (* $a $db)) ($x10 (* (num-radix) $x)) ($ab (* $a $b))
                    ($sq (mul-claims-d $a $qb $na (format-args "{}q" ($tag))))
                    ($sd (mul-claims-d $a $db $na (format-args "{}d" ($tag))))
                    ($st (add-script $x10 $y 0 (format-args "{}t" ($tag)))))
               (cl (format-args "{}{}{}claim {}M: mul_nat {} {} = {}.
{} exact {}. {}
" ((cl-text $sq) (cl-text $sd) (cl-text $st) $tag $A $B (num-arg $ab) "{"
   (chain-pf ((format-args "(mul_nat {} {})" ($A $B)) (format-args "(mul_nat {} {})" ($A (qd-text $qb $db)))
              (format-args "(add_nat (mul_nat {} {} :: 0) (mul_nat {} {}))" ($A $QB $A $db))
              (format-args "(add_nat {} {})" ((qd-text $x 0) (num-arg $y)))
              (format-args "(add_nat {} {})" ((num-arg $x10) (num-arg $y))) (num-arg $ab))
             ((format-args "(mul_nat_cong {} {} {} {} {} {})" ($A $A $B (qd-text $qb $db) (refl-pf $A) (view-pf $b)))
              (format-args "(mul_NumD {} {} {} {} {} Dnat_{})" ($A $na $QB (num-natproof-d $qb) $db $db))
              (format-args "(add_nat_cong (mul_nat {} {} :: 0) {} (mul_nat {} {}) {} (NumD_cong (mul_nat {} {}) {} 0 0 {} (Lean_eq_refl 0)) {})"
                ($A $QB (qd-text $x 0) $A $db (num-arg $y) $A $QB (num-arg $x) (cl-pf $sq) (cl-pf $sd)))
              (format-args "(add_nat_cong {} {} {} {} {} {})" ((qd-text $x 0) (num-arg $x10) (num-arg $y) (num-arg $y) (unview-pf $x 0) (refl-pf (num-arg $y))))
              (cl-pf $st)))
   "}"))
                   (format-args "{}M" ($tag))))))))
(= (mul-script $a $b $tag)
   (let* (($tn (format-args "{}n" ($tag))) ($sub (mul-claims-d $a $b (nat-ref $a $tn 0) $tag)))
     (cl (format-args "{}{}" ((nat-claims $a $tn 0) (cl-text $sub))) (cl-pf $sub))))

; ordsucc k = k + 1.
(= (succ-eq $k)
   (if (< (+ $k 1) (num-bound)) (refl-pf (num-arg (+ $k 1)))
       (let* (($q (q-of $k)) ($d (d-of $k)) ($K (num-arg $k)) ($Q (num-arg $q)) ($R (num-radix))
              ($s0 (format-args "(ordsucc {})" ($K))) ($s1 (format-args "(ordsucc {})" ((qd-text $q $d))))
              ($p0 (format-args "(ordsucc_cong {} {} {})" ($K (qd-text $q $d) (view-pf $k))))
              ($pS (format-args "(NumD_S {} {} {})" ($Q $d (dnat $d)))))
         (if (< $d (- $R 1))
             (chain-pf ($s0 $s1 (qd-text $q (+ $d 1)) (num-arg (+ $k 1))) ($p0 $pS (unview-pf $q (+ $d 1))))
             (chain-pf ($s0 $s1 (format-args "({} :: {})" ($Q $R)) (format-args "({} :: add_nat {} 0)" ($Q $R)) (format-args "(ordsucc {} :: 0)" ($Q))
                        (qd-text (+ $q 1) 0) (num-arg (+ $k 1)))
                       ($p0 $pS
                        (format-args "(NumD_cong {} {} {} (add_nat {} 0) {} (eq_sym_i (add_nat {} 0) {} (add_nat_0R {})))" ($Q $Q $R $R (refl-pf $Q) $R $R $R))
                        (format-args "(NumD_carry {} {} 0 nat_0)" ($Q (num-natproof-d $q)))
                        (format-args "(NumD_cong (ordsucc {}) {} 0 0 {} (Lean_eq_refl 0))" ($Q (num-arg (+ $q 1)) (succ-eq $q)))
                        (unview-pf (+ $q 1) 0)))))))
; Unfolding k into the successor of k - 1, and folding j + 1 back: through
; the digits above the bound.
(= (unfold-num-lines $k)
   (if (< $k (num-bound)) ((format-args "rewrite LeanNum_S {} {}." ((- $k 1) (natproof (- $k 1)))))
       ((format-args "rewrite <- {}." ((succ-eq (- $k 1))))
        (format-args "rewrite LeanNum_S {} {}." ((num-arg (- $k 1)) (num-natproof-d (- $k 1)))))))
(= (fold-num-lines $j)
   (if (< (+ $j 1) (num-bound)) ((format-args "rewrite <- LeanNum_S {} {}." ($j (natproof $j))))
       ((format-args "rewrite <- LeanNum_S {} {}." ((num-arg $j) (num-natproof-d $j)))
        (format-args "rewrite {}." ((succ-eq $j))))))

; ---- tabled replay ----
; A computation whose plain replay exceeds the step bound (Nat.choose recurs
; twice, so the same calls recur) is replayed with a table.  Each distinct
; call of a read function is proved once, as a claim call = value, and cited
; wherever it recurs; the claims come before the chain that cites them, in
; the order they are first needed.  A claim's own chain is replayed twice:
; once to learn its value and its calls' claims, once with the value known
; (numeral unfolding rewrites both sides of the goal), every call then a hit.
(= (tabled-call $r)
   (case $r
     (((app $g $args)
       (if (is-function $g)
           (if (or (or (== $g Nat.add) (== $g Nat.mul)) (or (== $g Nat.div) (== $g Nat.mod))) (if (both-nums $args) False True) True)
           False))
      ($_ False))))
(= (memo-find $r $memo)
   (if (== $memo ()) None
       (case (car-atom $memo)
         (((memo $c $v $name) (if (== $c $r) (car-atom $memo) (memo-find $r (cdr-atom $memo))))))))
(= (tmax) 20000)
; Reduce t to a value: (tdone value rhs lines claims memo k n) or (stuck why).
(= (treplay $t $rhs $memo $k $lines $claims $n $top)
   (if (is-value $t) (tdone $t $rhs $lines $claims $memo $k $n)
   (if (> $n (tmax)) (stuck (format-args "more than {} steps in a tabled replay" ((tmax))))
   (let $r (find-redex $t)
     (if (and (tabled-call $r) (not (== $r $top)))
         (let $hit (memo-find $r $memo)
           (if (not (== $hit None))
               (case $hit
                 (((memo $c $v $name)
                   (treplay (replace-term $t $r $v) $rhs $memo $k (append-lists $lines ((format-args "rewrite {}." ($name)))) $claims (+ $n 1) $top))))
               (let $sub (tclaim $r $memo $k $n)
                 (case $sub
                   (((tc $v $name $text $memo2 $k2 $n2)
                     (treplay (replace-term $t $r $v) $rhs $memo2 $k2 (append-lists $lines ((format-args "rewrite {}." ($name))))
                       (format-args "{}{}" ($claims $text)) (+ $n2 1) $top))
                    ((stuck $w) (stuck $w)))))))
         (let $st (step-of $r $n)
           (case $st
             (((step $new $ls0)
               (let* (($ls (robust-beta $t $r $ls0)) ($t2 (replace-term $t $r $new)) ($f (fold-step $t2 $rhs () $ls)))
                 (case $f (((folded $t3 $rhs3 $ls3) (treplay $t3 $rhs3 $memo $k (append-lists $lines $ls3) $claims (+ $n 1) $top))))))
              ((unfold $old $new $ls)
               (treplay (replace-term $t $old $new) (replace-term $rhs $old $new) $memo $k (append-lists $lines $ls) $claims (+ $n 1) $top))
              ((stuck $w) (stuck $w))))))))))
; The claim T_k : r = v, its calls' claims before it.
(= (tclaim $r $memo $k $n)
   (let $run1 (treplay $r (num 0) $memo (+ $k 1) () "" $n $r)
     (case $run1
       (((stuck $w) (stuck $w))
        ((tdone $v $rhs1 $ls1 $claims1 $memo1 $k1 $n1)
         (let $run2 (treplay $r $v $memo1 $k1 () "" $n1 $r)
           (case $run2
             (((stuck $w) (stuck $w))
              ((tdone $v2 $rhs2 $ls2 $claims2 $memo2 $k2 $n2)
               (let* (($name (format-args "T{}" ($k))) ($lines (fold-numerals $v2 $rhs2 $ls2)))
                 (tc $v $name
                   (format-args "{}{}claim {}: {} = {}.
{}
{}
reflexivity.
{}
" ($claims1 $claims2 $name (render $r ()) (render $v ()) "{" (lines $lines) "}"))
                   (cons-atom (memo $r $v $name) $memo2) $k2 $n2)))))))))))
; The computation t = rhs by the table.
(= (tabled-computation $t $rhs)
   (let $run (treplay $t $rhs () 0 () "" 0 None)
     (case $run
       (((stuck $w) (stuck $w))
        ((tdone $v $rhs2 $ls $claims $memo $k $n) (tproof $claims (fold-numerals $v $rhs2 $ls)))))))

; ---- typing modulo projection reduction ----
; An argument whose declared binder type applies a projection to an
; instance argument (maxOfLe's DecidableRel (LE.le α inst)) is typed at the
; binder type instantiated (LE.le Nat instLENat).  That type is reduced: a
; closed projection term is rewritten to its field (under binders too, being
; closed), each binder is entered by lam_Pi, and inside it the redexes left
; (a beta at the bound variables) are reduced under its hypothesis.  The
; typing is a claim; the term that needs it cites the claim.
(= (has-var $t) (has-free $t ()))
(= (has-free $t $bound)
   (case $t
     (((var $x) (not (member-term $x $bound)))
      ((app $c $args) (any-has-free $args $bound))
      ((apv $f $args) (if (has-free $f $bound) True (any-has-free $args $bound)))
      ((lam $x $T $b) (if (has-free $T $bound) True (has-free $b (cons-atom $x $bound))))
      ((pi $x $A $B) (if (has-free $A $bound) True (has-free $B (cons-atom $x $bound))))
      ((arrow $A $B) (if (has-free $A $bound) True (has-free $B $bound)))
      ((canon $P) (has-free $P $bound))
      ($_ False))))
(= (any-has-free $ts $bound) (if (== $ts ()) False (if (has-free (car-atom $ts) $bound) True (any-has-free (cdr-atom $ts) $bound))))
(= (any-has-var $ts) (any-has-free $ts ()))
; The first closed projection application in t, under binders too.
(= (closed-proj-in $t)
   (case $t
     (((app $c $args)
       (if (and (is-projection $c) (not (any-has-var $args))) $t (closed-proj-in-list $args)))
      ((apv $f $args) (closed-proj-in-list (cons-atom $f $args)))
      ((lam $x $T $b) (closed-proj-in-list ($T $b)))
      ((pi $x $A $B) (closed-proj-in-list ($A $B)))
      ((arrow $A $B) (closed-proj-in-list ($A $B)))
      ((canon $P) (closed-proj-in $P))
      ($_ None))))
(= (closed-proj-in-list $ts)
   (if (== $ts ()) None
       (let $r (closed-proj-in (car-atom $ts)) (if (== $r None) (closed-proj-in-list (cdr-atom $ts)) $r))))
; Rewrite every closed projection term of T to its value: (cc T' lines) or None.
(= (closed-conv $T $lines $n)
   (if (> $n 50) None
       (let $p (closed-proj-in $T)
         (if (== $p None) (cc $T $lines)
             (let $c (convert-type $p () 0 ())
               (if (== $c None) None
                   (closed-conv (replace-term $T $p (conv-type $c)) (append-lists $lines (conv-lines $c)) (+ $n 1))))))))
; Lines proving the goal a :e T.
(= (lam-script $a $T $sub $ctx)
   (case ($a $T)
     ((((lam $x $A $b) (pi $y $B $C)) (lam-script-at $x $A $b $B (fsubst $C (($y (var $x)))) $sub $ctx))
      (((lam $x $A $b) (arrow $B $C)) (lam-script-at $x $A $b $B $C $sub $ctx))
      ($_ (let $c (convert-type $T $ctx 0 ())
            (if (== $c None) None
                (append-lists (conv-lines $c) ((format-args "exact {}." ((typ-at $a (conv-type $c) $sub $ctx)))))))))))
(= (lam-script-at $x $A $b $B $C $sub $ctx)
   (let* (($sub2 (remove-key $x $sub)) ($hx (format-args "H{}" ($x)))
          ($ctx2 (cons-atom ($x $hx) (cons-atom ((ty $x) $B) $ctx)))
          ($inner (lam-script $b $C $sub2 $ctx2)))
     (if (== $inner None) None
         (cons-atom (format-args "apply lam_Pi {} (fun {} => {}) (fun {} => {})." ((render $B $sub) $x (render $C $sub2) $x (render $b $sub2)))
           (cons-atom (format-args "let {}. assume {}: {} :e {}." ($x $hx $x (render $B $sub)))
             (cons-atom (format-args "prove {} :e {}." ((render $b $sub2) (render $C $sub2))) $inner))))))
; The claim of an argument's typing, when its binder type needs the reduction.
(= (arg-conv-claim $a $T $sub $ctx $name)
   (let $cc (closed-conv $T () 0)
     (case $cc
       (((cc $T1 $ls)
         (let $body (lam-script $a $T1 $sub $ctx)
           (if (== $body None) None
               (format-args "claim {}: {} :e {}.
{}
{}
{}
" ($name (render $a $sub) (render $T $sub) "{" (lines (append-lists $ls $body)) "}")))))
        ($_ None)))))
; The arguments of an application whose binder types need it: ((index name claim) ...).
(= (conv-arg-claims $args $Ts $ks $i $sub $ctx)
   (if (== $args ()) ()
       (let* (($T (if (== $Ts ()) None (car-atom $Ts)))
              ($rest (conv-arg-claims (cdr-atom $args) (if (== $Ts ()) () (cdr-atom $Ts)) (cdr-atom $ks) (+ $i 1) $sub $ctx)))
         (if (== $T None) $rest
         (if (not (or (== (car-atom $ks) term) (== (car-atom $ks) proof))) $rest
         (if (== (closed-proj-in $T) None) $rest
             (let* (($name (format-args "Harg{}" ($i))) ($cl (arg-conv-claim (car-atom $args) $T $sub $ctx $name)))
               (if (== $cl None) $rest (cons-atom (ca $i $name $cl) $rest)))))))))
(= (ca-name-at $cas $i) (if (== $cas ()) None (case (car-atom $cas) (((ca $j $n $c) (if (== $j $i) $n (ca-name-at (cdr-atom $cas) $i)))))))
(= (ca-claims $cas) (join "" (map-atom $cas $c (case $c (((ca $j $n $t) $t))))))
; typ-args with the claimed arguments cited by name.
(= (typ-args-cl $args $ks $Ts $sub $ctx $cas $i)
   (if (== $args ()) ()
       (let* (($a (car-atom $args)) ($T (if (== $Ts ()) None (car-atom $Ts)))
              ($rest (typ-args-cl (cdr-atom $args) (cdr-atom $ks) (if (== $Ts ()) () (cdr-atom $Ts)) $sub $ctx $cas (+ $i 1)))
              ($nm (ca-name-at $cas $i)))
         (if (== (car-atom $ks) type) (cons-atom (render $a $sub) $rest)
         (if (== (car-atom $ks) family) (cons-atom (render $a $sub) (cons-atom (meta-render $a $sub) $rest))
             (cons-atom (render $a $sub)
               (cons-atom (if (not (== $nm None)) $nm (if (== $T None) (typ $a $sub $ctx) (typ-at $a $T $sub $ctx))) $rest)))))))

; ---- typing at a declared type, modulo its redexes ----
; Beta conversion under binders carries its own domain hypotheses. Only
; certified equations are used to transport the proof value back to the
; source type; normalization alone never counts as conversion evidence.
(= (beta-needed $t)
   (case $t
     (((apv $f $args)
       (or (case $f (((lam $x $A $b) (not (== $args ()))) ($_ False)))
           (beta-needed-list (cons-atom $f $args))))
      ((app $f $args) (beta-needed-list $args))
      ((lam $x $A $b) (or (beta-needed $A) (beta-needed $b)))
      ((pi $x $A $b) (or (beta-needed $A) (beta-needed $b)))
      ((arrow $A $B) (or (beta-needed $A) (beta-needed $B)))
      ($_ False))))
(= (beta-needed-list $xs)
   (if (== $xs ()) False (or (beta-needed (car-atom $xs)) (beta-needed-list (cdr-atom $xs)))))
(= (ceq-type $c) (case $c (((ceq $t $p) $t))))
(= (ceq-proof $c) (case $c (((ceq $t $p) $p))))
(= (ceq-chain $start $first $second)
   (if (or (== $first None) (== $second None)) None
       (let* (((ceq $middle $p) $first) ((ceq $end $q) $second))
         (ceq $end
           (if (== $p None) $q
           (if (== $q None) $p
               (format-args "(eq_i_tra {} {} {} {} {})"
                 ((render $start ()) (render $middle ()) (render $end ()) $p $q))))))))
(= (beta-children-of $t)
   (case $t (((app $f $args) $args) ((apv $f $args) (cons-atom $f $args)))))
(= (beta-rebuild $t $children)
   (case $t (((app $f $args) (app $f $children))
            ((apv $f $args) (apv (car-atom $children) (cdr-atom $children))))))
(= (replace-position $xs $i $value)
   (if (== $i 0) (cons-atom $value (cdr-atom $xs))
       (cons-atom (car-atom $xs) (replace-position (cdr-atom $xs) (- $i 1) $value))))
(= (beta-cert-children $start $acc $i $ctx $n)
   (let* (($current (ceq-type $acc)) ($children (beta-children-of $current)))
     (if (>= $i (length-of $children)) $acc
         (let* (($old (nth $children $i)) ($child (beta-certificate $old $ctx (- $n 1))))
           (if (== $child None) None
               (let* (($new (ceq-type $child)) ($next (beta-rebuild $current (replace-position $children $i $new)))
                      ($hole (bridge-name "hole" $n $current $ctx))
                      ($proof (if (== (ceq-proof $child) None) None
                        (format-args "(f_eq_i (fun {} => {}) {} {} {})"
                          ($hole (render (beta-rebuild $current (replace-position $children $i (var $hole))) ())
                           (render $old ()) (render $new ()) (ceq-proof $child))))))
                 (beta-cert-children $start (ceq-chain $start $acc (ceq $next $proof)) (+ $i 1) $ctx $n)))))))
(= (beta-binder-node $template $x $A $B)
   (case $template (((lam $old $D $body) (lam $x $A $B))
                   ((pi $old $D $body) (pi $x $A $B))
                   ((arrow $D $body) (arrow $A $B)))))
(= (beta-cert-binder $t $x $A $B $ctx $n)
   (let* (($fresh (fresh-name $x (ctx-names $ctx))) ($body (csubst $B (($x (var $fresh)))))
          ($hx (bridge-name "bound" $n $t $ctx))
          ($bodyCtx (cons-atom ((ReservedName $hx) True)
            (cons-atom ($fresh $hx) (cons-atom ((ty $fresh) $A) $ctx))))
          ($domainCert (beta-certificate $A $ctx (- $n 1)))
          ($bodyCert (beta-certificate $body $bodyCtx (- $n 1))))
     (if (or (== $domainCert None) (== $bodyCert None)) None
       (let* (($Anew (ceq-type $domainCert)) ($Bnew (ceq-type $bodyCert))
              ($middle (beta-binder-node $t $fresh $A $Bnew))
              ($end (beta-binder-node $t $fresh $Anew $Bnew))
              ($family (case $t (((lam $a $b $c) "Sigma_family_eq") ($_ "Pi_family_eq"))))
              ($bodyProof (if (== (ceq-proof $bodyCert) None) None
                (format-args "({} {} (fun {} => {}) (fun {} => {}) (fun {} {} => {}))"
                  ($family (render $A ()) $fresh (render $body ()) $fresh (render $Bnew ())
                   $fresh $hx (ceq-proof $bodyCert)))))
              ($hole (bridge-name "domain" $n $t $ctx))
              ($domainProof (if (== (ceq-proof $domainCert) None) None
                (format-args "(f_eq_i (fun {} => {}) {} {} {})"
                  ($hole (render (beta-binder-node $t $fresh (var $hole) $Bnew) ())
                   (render $A ()) (render $Anew ()) (ceq-proof $domainCert))))))
         (ceq-chain $t (ceq $middle $bodyProof) (ceq $end $domainProof))))))
(= (beta-root-certificate $t $ctx)
   (case (beta-step-ctx $t $ctx)
     (((step $new $lines)
       (if (not (== (length-of $lines) 1)) None
           (let $proof (eq-of-line (car-atom $lines))
             (if (== $proof None) None
                 (let* (($sides (step-eq-sides $t $new)) ($hole (bridge-name "beta" 0 $t $ctx))
                        ($context (csubst (eq-hole $t) (("ZcZ" (var $hole))))))
                   (ceq $new (format-args "(f_eq_i (fun {} => {}) {} {} ({}))"
                     ($hole (render $context ()) (render (car-atom $sides) ())
                      (render (nth $sides 1) ()) $proof))))))))
      ($_ None))))
(= (beta-cert-application $t $ctx $n)
   (let $children (beta-cert-children $t (ceq $t None) 0 $ctx $n)
     (if (== $children None) None
       (let $middle (ceq-type $children)
         (case $middle
           (((apv (lam $x $A $body) $args)
             (if (== $args ()) $children
               (let $root (beta-root-certificate $middle $ctx)
                 (if (== $root None) None
                   (ceq-chain $t (ceq-chain $t $children $root)
                     (beta-certificate (ceq-type $root) $ctx (- $n 1)))))))
            ($_ $children)))))))
(= (beta-certificate $t $ctx $n)
   (if (not (beta-needed $t)) (ceq $t None)
   (if (<= $n 0) None
     (case $t
       (((pi $x $A $B) (beta-cert-binder $t $x $A $B $ctx $n))
        ((lam $x $A $B) (beta-cert-binder $t $x $A $B $ctx $n))
        ((arrow $A $B) (beta-cert-binder $t (bridge-name "arrow" $n $t $ctx) $A $B $ctx $n))
        ((app $f $args) (beta-cert-application $t $ctx $n))
        ((apv $f $args) (beta-cert-application $t $ctx $n))
        ($_ (ceq $t None)))))))
(= (proof-at $P $sub $ctx)
   (let $known (known-proof $P $ctx)
     (if (not (== $known None)) $known
     (if (or (not (== $sub ())) (not (beta-needed $P))) (prove-prop-in $P $ctx)
       (case (beta-certificate $P $ctx 64)
         (((ceq $normal $equation)
           (if (== $equation None) (prove-prop-in $P $ctx)
               (format-args "(In_eq_r 0 {} {} (eq_sym_i {} {} {}) {})"
                 ((render $normal ()) (render $P ()) (render $P ()) (render $normal ()) $equation
                  (prove-prop-in $normal $ctx)))))
          ($_ "UNDECIDED_typed_beta_conversion")))))))

; An argument's declared type, instantiated, may hold a projection of a
; constructor or a beta redex outside any binder (ite's Decidable (LE.le Nat
; (LE.mk Nat le) x y)) where the argument's own type has the reduct.  The
; type is reduced by the replay's steps, each step's equation (the term its
; rewrite cites) lifted into the type by a context (f_eq_i), the equations
; chained, and the argument's typing carried back along them (In_eq_r).
(= (eq-of-line $l)
   (let $n (str:byte-length $l)
     (if (< $n 10) None
         (if (== (str:byte-slice $l 0 8) "rewrite ")
             (if (== (str:byte-slice $l 8 10) "<-") None
                 (if (== (str:byte-slice $l (- $n 1) $n) ".") (str:byte-slice $l 8 (- $n 1)) None))
             None))))
; (ceq T' proof-of-T=T'), the proof None when T has no redex; None when a
; step is not a single rewrite.
(= (conv-eq $T $sub $ctx $n)
   (let $r (find-redex $T)
     (if (== $r None) (ceq $T None)
         (if (> $n 30) None
             (let $st (conv-step $r $ctx)
               (case $st
                 (((step $new $ls)
                   (if (not (== (length-of $ls) 1)) None
                       (let $x (eq-of-line (car-atom $ls))
                         (if (== $x None) None
                             (let* (($T1 (replace-term $T $r $new))
                                    ($eq (step-eq-sides $r $new))
                                    ($cl (format-args "(fun ZcZ => {})" ((render (replace-term $T $r (eq-hole $r)) $sub))))
                                    ($p1 (format-args "(f_eq_i {} {} {} ({}))" ($cl (render (car-atom $eq) $sub) (render (car-atom (cdr-atom $eq)) $sub) $x)))
                                    ($rest (conv-eq $T1 $sub $ctx (+ $n 1))))
                               (case $rest
                                 (((ceq $T2 $p2)
                                   (if (== $p2 None) (ceq $T1 $p1)
                                       (ceq $T2 (format-args "(eq_i_tra {} {} {} {} {})"
                                                  ((render $T $sub) (render $T1 $sub) (render $T2 $sub) $p1 $p2)))))
                                  ($_ None))))))))
                  ($_ None))))))))
; The sides of a step's equation, and the hole its context leaves: a beta
; at several arguments proves the first application only (f a1 = body), the
; rest applied to the hole.
(= (step-eq-sides $r $new)
   (case $r
     (((apv (lam $x $A $b) $args)
       (if (== (cdr-atom $args) ()) ($r $new)
           ((apv (lam $x $A $b) (cons-atom (car-atom $args) ())) (case $new (((apv $g $rest) $g) ($_ $new))))))
      ($_ ($r $new)))))
(= (eq-hole $r)
   (case $r
     (((apv (lam $x $A $b) $args) (if (== (cdr-atom $args) ()) (var "ZcZ") (apv (var "ZcZ") (cdr-atom $args))))
      ($_ (var "ZcZ")))))
; Worth converting: a closed projection or a beta redex outside binders.
(= (conv-worthy $T)
   (case $T
     (((app $c $args) (if (is-projection $c) (if (any-has-var $args) (any-conv-worthy $args) True) (any-conv-worthy $args)))
      ((apv $f $args) (case $f (((lam $x $A $b) True) ($_ (any-conv-worthy (cons-atom $f $args))))))
      ($_ False))))
(= (any-conv-worthy $ts) (if (== $ts ()) False (if (conv-worthy (car-atom $ts)) True (any-conv-worthy (cdr-atom $ts)))))
(= (typ-at-conv $t $T $sub $ctx)
   (let $c (conv-eq $T $sub $ctx 0)
     (case $c
       (((ceq $T2 $pf)
         (if (== $pf None) (typ $t $sub $ctx)
             (format-args "(In_eq_r {} {} {} (eq_sym_i {} {} {}) {})"
               ((render $t $sub) (render $T2 $sub) (render $T $sub) (render $T $sub) (render $T2 $sub) $pf (typ $t $sub $ctx)))))
        ($_ (typ $t $sub $ctx))))))

; ---- converting a type under hypotheses ----
; A dependent result type at a constructor mentions functions applied to the
; constructor's node (generalize_sound: Deriv (generalize d x).1 ...).  It is
; rewritten to a type without redexes, each step typed under the hypotheses
; in scope ($ctx): equations, projections, case analyses and beta.
(= (convert-type $t $ctx $n $acc)
   (if (> $n 200) None
       (let $r (find-redex $t)
         (if (== $r None) (conv $t $acc)
             (let $st (conv-step $r $ctx)
               (case $st
                 (((step $new $lines) (convert-type (replace-term $t $r $new) $ctx (+ $n 1) (append-lists $acc $lines)))
                  ($_ None))))))))
(= (conv-step $r $ctx)
   (case $r
     (((apv $f $as) (beta-step-ctx $r $ctx))
      ($_ (let* (($g (app-head $r)) ($args (app-args $r)))
            (if (is-projection $g) (proj-step-ctx $g $args $ctx)
            (if (is-cases-on $g) (cases-step-ctx $g $args $ctx)
            (if (not (is-function $g)) (stuck "not a function")
                (let $hit (lean-eqn-hit $g (lean-eqns-of $g) $args)
                  (if (== $hit None) (stuck "no equation applies") (eqn-step-ctx $hit $args $ctx)))))))))))
(= (conv-type $c) (case $c (((conv $t $ls) $t))))
(= (conv-lines $c) (case $c (((conv $t $ls) $ls))))

; After a step other than an unfolding, the successors of numerals it left
; are folded back into numerals at once, so that numerals stay numerals and
; natively computed operations apply to them.
(= (fold-step $t $rhs $acc $lines)
   (fold-succs $t $rhs (append-lists $acc $lines)))
(= (fold-succs $l $r $acc)
   (let $j (find-succ-num-list ($l $r))
     (if (== $j None) (folded $l $r $acc)
         (let $old (app Nat.succ ((num $j)))
           (fold-succs (replace-term $l $old (num (+ $j 1))) (replace-term $r $old (num (+ $j 1)))
             (append-lists $acc (fold-num-lines $j)))))))

; Fold unfolded numerals back on both sides: zero first, then successors of
; numerals, innermost first.
(= (find-succ-num $t)
   (case $t
     (((app Nat.succ ((num $j))) $j)
      ((canon $P) (find-succ-num $P))
      ((app $c $args) (find-succ-num-list $args))
      ((apv $f $args) (find-succ-num-list (cons-atom $f $args)))
      ((lam $x $T $b) (find-succ-num-list ($T $b)))
      ((arrow $A $B) (find-succ-num-list ($A $B)))
      ((pi $x $A $B) (find-succ-num-list ($A $B)))
      ($_ None))))
(= (find-succ-num-list $ts)
   (if (== $ts ()) None
       (let $j (find-succ-num (car-atom $ts)) (if (== $j None) (find-succ-num-list (cdr-atom $ts)) $j))))
(= (has-zero-node $t)
   (case $t
     (((app Nat.zero ()) True)
      ((canon $P) (has-zero-node $P))
      ((app $c $args) (any-zero $args))
      ((apv $f $args) (any-zero (cons-atom $f $args)))
      ((lam $x $T $b) (any-zero ($T $b)))
      ((arrow $A $B) (any-zero ($A $B)))
      ((pi $x $A $B) (any-zero ($A $B)))
      ($_ False))))
(= (any-zero $ts) (if (== $ts ()) False (if (has-zero-node (car-atom $ts)) True (any-zero (cdr-atom $ts)))))

(= (fold-numerals $l $r $acc)
   (if (or (has-zero-node $l) (has-zero-node $r))
       (fold-numerals (replace-term $l (app Nat.zero ()) (num 0)) (replace-term $r (app Nat.zero ()) (num 0))
         (append-lists $acc ("rewrite <- LeanNum_0.")))
       (let $j (find-succ-num-list ($l $r))
         (if (== $j None) $acc
             (let $old (app Nat.succ ((num $j)))
               (fold-numerals (replace-term $l $old (num (+ $j 1))) (replace-term $r $old (num (+ $j 1)))
                 (append-lists $acc (fold-num-lines $j))))))))

; ---- the theorems of one computation ----

(= (comp-term $i) (car-atom (collapse (match &self (LeanComputation $i $t $ty) $t))))
(= (comp-type $i) (car-atom (collapse (match &self (LeanComputation $i $t $ty) $ty))))
(= (has-comp $i) (let $found (collapse (match &self (LeanComputation $i $t $ty) $i)) (if (== $found ()) False True)))
(= (answer-of $i)
   (let $found (collapse (match &self (CeTTaAnswer $i $v) $v))
     (if (== $found ()) None (car-atom (car-atom $found)))))

(= (source-text $i)
   (let $found (collapse (match &self (LeanSource $i $src) $src))
     (if (== $found ()) "" (format-args ": {}" ((car-atom $found))))))

(= (test-name $i) (if (< $i 10) (format-args "Lean_test_0{}" ($i)) (format-args "Lean_test_{}" ($i))))

; (computation name text) or (stuck reason)
(= (computation $i $answer $name)
   (computation-candidate (computation-raw $i $answer $name)))

; A computed value is not a proof if replay could not reconstruct a branch
; hypothesis. Keep that failure visible before emitting a theorem candidate.
(= (computation-candidate $result)
   (case $result
     (((computation $name $text)
       (if (or (text-has $text "UNDECIDED")
               (or (text-has $text "not proved here") (text-has $text "PROOF-FILE")))
           (stuck "a proof required by computation replay is not reconstructed")
           $result))
      ($_ $result))))

(= (computation-raw $i $answer $name)
   (if (not (has-comp $i)) (stuck "not a first-order term")
   (let* (($t (comp-term $i)) ($T (comp-type $i)) ($v (readback $answer $T)))
     (if (is-stuck $v) $v
         (let $run (replay $t $v 0 ())
           (case $run
             (((stuck $why)
               (if (== $why "more than 2000 steps")
                   (case (tabled-computation $t $v)
                     (((tproof $claims $tl)
                       (computation $name
                         (format-args "Theorem {} : {} = {}.
{}{}
reflexivity.
Qed.
" ($name (render $t ()) (render $v ()) $claims (lines $tl)))))
                      ((stuck $w2) (stuck $w2))))
                   (stuck $why)))
              ((done $value $vrhs $steps)
               (let $lines (fold-numerals $value $vrhs $steps)
               (computation $name
                 (format-args "Theorem {} : {} = {}.
{}
reflexivity.
Qed.
" ($name (render $t ()) (render $v ()) (lines $lines)))))))))))))

(= (answer-theorems $i $answer $name)
   (let* (($T (comp-type $i)) ($v (readback $answer $T)))
     (if (== $T (app Nat ()))
         (format-args "Theorem {}_answer_typed : {} :e {}.
exact {}.
Qed.
Theorem {}_unique : forall k, nat_p k -> {} = LeanNum k -> k = {}.
let k. assume Hk: nat_p k. assume H: {} = LeanNum k.
apply eq_sym_i {} k.
apply LeanNum_inj {} {} k Hk.
rewrite <- {}. exact H.
Qed.
" ($name (render $v ()) (render $T ()) (typ $v () ())
   $name (render (comp-term $i) ()) (num-arg $answer) (render (comp-term $i) ())
   (num-arg $answer) (num-arg $answer) (num-natproof $answer) $name))
         (format-args "Theorem {}_answer_typed : {} :e {}.
exact {}.
Qed.
" ($name (render $v ()) (render $T ()) (typ $v () ()))))))

(= (computation-section $i)
   (let $a (answer-of $i)
     (if (== $a None) (stuck "no CeTTa answer")
         (let $c (computation $i $a (test-name $i))
           (case $c
             (((computation $name $text)
               (computation $name (format-args "(** Test {} of the code-equation slice{} **)
{}{}" ($i (source-text $i) $text (answer-theorems $i $a $name)))))
              ((stuck $why) (stuck $why))))))))

; ---- uniqueness: Lean's equations determine the function ----
; Any g satisfying Lean's equation theorems equals the generated function on
; the family: induction through the recursor's typing, with the motive
; {z :e 1 | g .. t .. = f .. t ..}.

; A term with the head f written as h.
(= (render-h $t $f $h $sub) (render (head-as $t $f $h) $sub))
(= (head-as $t $f $h)
   (case $t
     (((app $c $args)
       (let $as (head-as-all $args $f $h)
         (if (== $c $f) (if (== $as ()) (txt $h) (apv (txt $h) $as)) (app $c $as))))
      ((apv $g $args) (apv (head-as $g $f $h) (head-as-all $args $f $h)))
      ((lam $x $T $b) (lam $x (head-as $T $f $h) (head-as $b $f $h)))
      ((arrow $A $B) (arrow (head-as $A $f $h) (head-as $B $f $h)))
      ((pi $x $A $B) (pi $x (head-as $A $f $h) (head-as $B $f $h)))
      ($_ $t))))
(= (head-as-all $ts $f $h) (if (== $ts ()) () (cons-atom (head-as (car-atom $ts) $f $h) (head-as-all (cdr-atom $ts) $f $h))))
(= (render-h-all $ts $f $h $sub)
   (if (== $ts ()) () (cons-atom (render-h (car-atom $ts) $f $h $sub) (render-h-all (cdr-atom $ts) $f $h $sub))))

(= (hyp-text $f $e)
   (format-args "({}{} = {})" ((stmt-binders (eqn-binders $e) ()) (render-h (eqn-lhs $e) $f g ()) (render-h (eqn-rhs $e) $f g ()))))

(= (hyps-text $f $eqs)
   (if (== $eqs ()) "" (format-args "{} -> {}" ((hyp-text $f (car-atom $eqs)) (hyps-text $f (cdr-atom $eqs))))))

(= (hyp-intros $eqs $k)
   (if (== $eqs ()) "" (format-args "assume Hg{}. {}" ($k (hyp-intros (cdr-atom $eqs) (+ $k 1))))))

; The arguments instantiating equation e at canonical names: levels at u,
; parameters a_p, fields y_i.
(= (canon-inst $bs $e $m $fam $levels)
   (if (== $bs ()) ""
       (let* (($args (lhs-args $e)) ($pat (pattern-of (nth $args $m)))
              ($fvars (drop-n (app-args $pat) (param-count $fam))))
         (case (car-atom $bs)
           (((type $x $l)
             (let $p (index-of-term (var $x) $args 0)
               (format-args "{}{} H{}{}"
                 ((if (or (== $l 0) (member-term $l $levels)) "" " u Hu") (format-args " a{}" ($p)) $p
                  (canon-inst (cdr-atom $bs) $e $m $fam (if (== $l 0) $levels (cons-atom $l $levels)))))))
            ((term $x $t)
             (let* (($p (index-of-term (var $x) $args 0)) ($i (index-of-term (var $x) $fvars 0)))
               (if (>= $p 0)
                   (format-args " a{} H{}{}" ($p $p (canon-inst (cdr-atom $bs) $e $m $fam $levels)))
                   (format-args " y{} Hy{}{}" ($i $i (canon-inst (cdr-atom $bs) $e $m $fam $levels)))))))))))

; The motive at t, over the canonical parameters.
(= (args-with $n $m $t)
   (let $ps (vars-of $n "a") (join " " (replace-at $ps $m $t 0))))
(= (motive-at-text $f $n $m $t)
   (format-args "{}z :e 1 | g {} = {} {}{}" ("{" (args-with $n $m $t) (egal $f) (args-with $n $m $t) "}")))

; The canonical layers of method k with each recursive result typed by the motive.
(= (unique-layers $layers $f $n $m)
   (if (== $layers ()) ()
       (let $l (car-atom $layers)
         (cons-atom (if (== (ly-kind $l) ih)
                        (ly (ly-name $l) (var (motive-at-text $f $n $m (field-name (ly-index $l)))) ih (ly-index $l))
                        $l)
                    (unique-layers (cdr-atom $layers) $f $n $m)))))

; Types of layers may be text (the motive) or terms.
(= (layer-type-text $l $sub)
   (case (ly-type $l) (((var $t) (lookup-var $t $sub)) ($_ (render (ly-type $l) $sub)))))

(= (u-lam-text $layers $sub)
   (if (== $layers ()) "0"
       (let $l (car-atom $layers)
         (format-args "(fun {} :e {} => {})" ((ly-name $l) (layer-type-text $l $sub) (u-lam-text (cdr-atom $layers) $sub))))))

(= (u-pi-text $layers $final $sub)
   (if (== $layers ()) $final
       (let $l (car-atom $layers)
         (format-args "(Pi_ {} :e {}, {})" ((ly-name $l) (layer-type-text $l $sub) (u-pi-text (cdr-atom $layers) $final $sub))))))

(= (u-hm-proof $layers $final $sub $k $acc)
   (if (== $layers ()) (format-args "(L{}{})" ($k $acc))
       (let* (($l (car-atom $layers)) ($z (ly-name $l)) ($rest (cdr-atom $layers)))
         (format-args "(lam_Pi {} (fun {} => {}) (fun {} => {}) (fun {} H{} => {}))"
           ((layer-type-text $l $sub) $z (u-pi-text $rest $final $sub) $z (u-lam-text $rest $sub)
            $z $z (u-hm-proof $rest $final $sub $k (format-args "{} {} H{}" ($acc $z $z))))))))

(= (u-binders $layers $sub)
   (if (== $layers ()) ""
       (let $l (car-atom $layers)
         (format-args "forall {} :e {}, {}" ((ly-name $l) (layer-type-text $l $sub) (u-binders (cdr-atom $layers) $sub))))))

(= (u-intros $layers $sub)
   (if (== $layers ()) ""
       (let $l (car-atom $layers)
         (format-args "let {}. assume H{}: {} :e {}. {}" ((ly-name $l) (ly-name $l) (ly-name $l) (layer-type-text $l $sub) (u-intros (cdr-atom $layers) $sub))))))

(= (ih-rewrites $layers $f $n $m $body)
   (if (== $layers ()) ""
       (let $l (car-atom $layers)
         (format-args "{}{}"
           ((if (and (== (ly-kind $l) ih) (mentions $body (ly-name $l)))
                (format-args "rewrite SepE2 1 (fun z:set => g {} = {} {}) {} H{}. "
                  ((args-with $n $m (field-name (ly-index $l))) (egal $f) (args-with $n $m (field-name (ly-index $l))) (ly-name $l) (ly-name $l)))
                "")
            (ih-rewrites (cdr-atom $layers) $f $n $m $body))))))

(= (unique-claim $f $s $e $k $n $sub)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s))
          ($cm (cmethod $f $e $m $fam))
          ($layers (unique-layers (cm-layers $cm) $f $n $m))
          ($pat (pattern-of (nth (lhs-args $e) $m)))
          ($ren (append-lists (param-renames (lhs-args $e) $m 0)
                              (field-renames (drop-n (app-args $pat) (param-count $fam)) 0)))
          ($node (render (fsubst $pat $ren) $sub))
          ($inst (canon-inst (eqn-binders $e) $e $m $fam ()))
          ($lit (if (== (nth (lhs-args $e) $m) (num 0)) "rewrite <- LeanNum_0. " "")))
     (format-args "claim L{}: {}0 :e {}.
{} {}apply SepI 1 (fun z:set => g {} = {} {}) 0 In_0_1.
  prove g {} = {} {}.
  {}rewrite Hg{}{}. rewrite {}{}. {}reflexivity. {}
"
       ($k (u-binders $layers $sub) (motive-at-text $f $n $m $node)
        "{" (u-intros $layers $sub) (args-with $n $m $node) (egal $f) (args-with $n $m $node)
        (args-with $n $m $node) (egal $f) (args-with $n $m $node)
        $lit $k $inst (egal (eqn-name $e)) $inst (ih-rewrites $layers $f $n $m (cm-body $cm)) "}"))))

(= (unique-claims $f $s $eqs $k $n $sub)
   (if (== $eqs ()) ""
       (format-args "{}{}" ((unique-claim $f $s (car-atom $eqs) $k $n $sub) (unique-claims $f $s (cdr-atom $eqs) (+ $k 1) $n $sub)))))

(= (unique-methods $f $s $eqs $k $n $sub)
   (if (== $eqs ()) ""
       (let* (($m (shape-m $s)) ($fam (shape-fam $s))
              ($cm (cmethod $f (car-atom $eqs) $m $fam))
              ($layers (unique-layers (cm-layers $cm) $f $n $m))
              ($pat (pattern-of (nth (lhs-args (car-atom $eqs)) $m)))
              ($ren (append-lists (param-renames (lhs-args (car-atom $eqs)) $m 0)
                                  (field-renames (drop-n (app-args $pat) (param-count $fam)) 0)))
              ($final (motive-at-text $f $n $m (render (fsubst $pat $ren) $sub)))
              ($rest (unique-methods $f $s (cdr-atom $eqs) (+ $k 1) $n $sub)))
         (format-args "{} {}{}" ((u-lam-text $layers $sub) (u-hm-proof $layers $final $sub $k "")
                                 (if (== $rest "") "" (format-args " {}" ($rest))))))))

(= (unique-binders $ks $m $p $famT $f $sub)
   (if (== $ks ()) ""
       (format-args "{}{}"
         ((if (== $p $m) (format-args "forall a{} :e {}, " ($p $famT))
              (if (== (car-atom $ks) type) (format-args "forall a{} :e LeanUniv u, " ($p))
                  (format-args "forall a{} :e {}, " ($p (pos-type $f $p $m $famT $sub)))))
          (unique-binders (cdr-atom $ks) $m (+ $p 1) $famT $f $sub)))))

(= (unique-intros $ks $m $p $famT $f $sub)
   (if (== $ks ()) ""
       (format-args "let a{}. assume H{}: a{} :e {}. {}"
         ($p $p $p
          (if (== $p $m) $famT (if (== (car-atom $ks) type) "LeanUniv u" (pos-type $f $p $m $famT $sub)))
          (unique-intros (cdr-atom $ks) $m (+ $p 1) $famT $f $sub)))))

(= (unique-theorem $f $s)
   (let* (($m (shape-m $s)) ($fam (shape-fam $s)) ($eqs (shape-eqs $s))
          ($n (arity-of $f)) ($ps (vars-of $n "a")) ($sub (pos-subst $ps 0))
          ($ks (pos-kinds $f))
          ($famT (major-type-text $f $s $sub))
          ($fps (render-all (fam-params-c $f $s) $sub)))
     (format-args "Theorem {}_unique : forall g:{}, {}forall u, nat_p u -> {}g {} = {} {}.
let g. {}let u. assume Hu: nat_p u. {}
{}claim LC: {}_rec{} {} a{} :e (fun {}t:set => {}) {}a{}.
{} exact {}_rec_type{} (fun {}t:set => {}) {} {}a{} H{}. {}
exact SepE2 1 (fun z:set => g {} = {} {}) ({}_rec{} {} a{}) LC.
Qed.
"
       ((egal $f) (fun-type $n) (hyps-text $f $eqs) (unique-binders $ks $m 0 $famT $f $sub)
        (join " " $ps) (egal $f) (join " " $ps)
        (hyp-intros $eqs 0) (unique-intros $ks $m 0 $famT $f $sub)
        (unique-claims $f $s $eqs 0 $n $sub)
        (egal $fam) (if (== $fps ()) "" (format-args " {}" ((join " " $fps)))) (unique-method-list $f $s $eqs $n $sub) $m
        (index-binder-text $f $m) (motive-at-text $f $n $m "t") (major-index-text $f $m $sub) $m
        "{" (egal $fam) (if (== $fps ()) "" (format-args " {}" ((join " " $fps)))) (index-binder-text $f $m) (motive-at-text $f $n $m "t")
        (unique-methods $f $s $eqs 0 $n $sub) (major-index-text $f $m $sub) $m $m "}"
        (join " " $ps) (egal $f) (join " " $ps)
        (egal $fam) (if (== $fps ()) "" (format-args " {}" ((join " " $fps)))) (unique-method-list $f $s $eqs $n $sub) $m))))

(= (unique-method-list $f $s $eqs $n $sub)
   (if (== $eqs ()) ""
       (let* (($m (shape-m $s)) ($fam (shape-fam $s))
              ($cm (cmethod $f (car-atom $eqs) $m $fam))
              ($rest (unique-method-list $f $s (cdr-atom $eqs) $n $sub)))
         (format-args "{}{}" ((u-lam-text (unique-layers (cm-layers $cm) $f $n $m) $sub)
                              (if (== $rest "") "" (format-args " {}" ($rest))))))))

; A wrong answer for a control: the first natural number in the answer, plus one.
(= (wrong-answer $i) (bump-first (answer-of $i)))
(= (bump-first $v)
   (if (== (get-metatype $v) Grounded) (+ $v 1)
       (if (== (get-metatype $v) Expression) (bump-first-list $v) $v)))
(= (bump-first-list $vs)
   (if (== $vs ()) ()
       (let $h (bump-first (car-atom $vs))
         (if (== $h (car-atom $vs)) (cons-atom $h (bump-first-list (cdr-atom $vs))) (cons-atom $h (cdr-atom $vs))))))

; ---- theorems of a carried development ----
; A theorem's statement in Egal's own logic: Lean's forall and implication are
; Egal's, an equation is equality of sets, an existential over a type and a
; conjunction are Egal's; any other proposition P holds when 0 :e P, its truth
; value.
(= (stmt-native $P)
   (case $P
     (((pi $x $A $B) (format-args "forall {} :e {}, {}" ($x (sort-or-render $A) (stmt-native $B))))
      ((app Or ($Q $R)) (format-args "({}) \\/ ({})" ((stmt-native $Q) (stmt-native $R))))
      ((arrow $A $B) (format-args "({}) -> {}" ((stmt-native $A) (stmt-native $B))))
      ((app Eq ($T $a $b)) (format-args "{} = {}" ((render $a ()) (render $b ()))))
      ((app Exists ($T (lam $x $A $Q))) (format-args "exists {} :e {}, {}" ($x (render $A ()) (stmt-native $Q))))
      ((app And ($Q $R)) (format-args "({}) /\\ ({})" ((stmt-native $Q) (stmt-native $R))))
      ((app False ()) "False")
      ($_ (format-args "0 :e {}" ((render $P ())))))))
(= (theorem-statements)
   (collapse (match &self (LeanTheorem $t $P) (stmt-line $t (stmt-top $P)))))
; A statement quantifies its universe levels first.  Proofs inside it read
; as 0, and a binder over a proposition ranges over its proof set ({0} when
; it holds), so a motive applied to proofs (head_induction_on) reads
; consistently.
(= (stmt-top $P)
   (format-args "{}{}" ((join "" (map-atom (stmt-levels $P ()) $l (format-args "forall {}, nat_p {} -> " ($l $l))))
                        (stmt-native $P))))
(= (stmt-levels $t $acc)
   (case $t
     (((lvl $l) (if (member-term $l $acc) $acc (append-lists $acc ($l))))
      ((num $k) $acc)
      ($_ (if (== (get-metatype $t) Expression) (stmt-levels-list $t $acc) $acc)))))
(= (stmt-levels-list $ts $acc)
   (if (== $ts ()) $acc (stmt-levels-list (cdr-atom $ts) (stmt-levels (car-atom $ts) $acc))))
; A sort as a binder's domain: Sort (u+1) is the universe LeanUniv u.
(= (sort-or-render $A)
   (if (is-sort-term $A)
       (if (== $A (prop)) "LeanProp"
           (let $L (car-atom (cdr-atom $A))
             (if (== (get-metatype $L) Expression)
                 (if (== (car-atom $L) lsucc) (format-args "LeanUniv {}" ((level-text (car-atom (cdr-atom $L)))))
                     (format-args "LeanSort {}" ((level-text $L))))
                 (format-args "LeanSort {}" ((level-text $L))))))
       (render $A ())))
(= (level-text $L)
   (case $L
     (((lvl $l) $l)
      ((lsucc $X) (format-args "(ordsucc {})" ((level-text $X))))
      ($_ $L))))
