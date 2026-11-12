; The reader's terms as kernel terms.
;
; interpret.metta writes a term as Megalodon text (render).  wire builds the
; same term as the kernel's data, case for case, so that what the reader says
; and what the kernel holds are one term: names become the kernel's names of
; their declarations, binders become de Bruijn indices, a bounded function is
; Sigma at its domain (Megalodon's reading of fun x :e A => b) and a dependent
; function space is Pi at its.  The text
; needs every term written eta-normal; the kernel normalizes its own terms,
; so wire writes each binder as it is.
;
;   (wire TERM ENV)        ENV: the bound variables, innermost first
;   (lean:eq LEFT RIGHT)   the equation of two kernel terms of type set
;
; Read after interpret.metta and session.metta.

(= (wire:named $source) (Tm.named (lean:id $source)))
; F applied to ARGS, where F still takes ARITY arguments as a function of the
; logic.  Megalodon reads the application of a set as the set-theoretic one,
; ap; so do the arguments past the arity.
(= (wire:apply $f $arity $args)
   (if (== $args ()) $f
       (if (> $arity 0)
           (wire:apply (Tm.app $f (car-atom $args)) (- $arity 1) (cdr-atom $args))
           (wire:apply (Tm.app (Tm.app (wire:named "ap") $f) (car-atom $args)) 0 (cdr-atom $args)))))
(= (wire:minus $a $b) (if (> $a $b) (- $a $b) 0))
; Megalodon's numeral: K successors of the empty set.
(= (wire:literal $k) (if (== $k 0) (wire:named "Empty") (Tm.app (wire:named "ordsucc") (wire:literal (- $k 1)))))
; A natural number as the reader writes it: a literal below the bound, the
; digits q :: d above it (Library/Digits.mg).
(= (wire:natural $k)
   (if (< $k (num-bound)) (wire:literal $k)
       (Tm.app (Tm.app (wire:named "NumD") (wire:natural (idiv $k (num-radix)))) (wire:literal (% $k (num-radix))))))

(= (wire:index $x $env $i)
   (if (== $env ()) (Error (LeanTermForm (var $x)) (LeanTerm "a variable that no binder of the term binds"))
       (if (== (car-atom $env) $x) (Tm.db $i) (wire:index $x (cdr-atom $env) (+ $i 1)))))

(= (wire:level $L $env)
   (case $L
     (((lvl $l) (wire:index $l $env 0))
      ((lsucc $X) (Tm.app (wire:named "ordsucc") (wire:level $X $env)))
      ($_ (if (== (get-metatype $L) Grounded) (wire:literal $L)
              (Error (LeanTermForm $L) (LeanTerm "a universe level with no reading")))))))
(= (wire:sort $A $env)
   (if (== $A (prop)) (wire:named "LeanProp")
       (let $L (car-atom (cdr-atom $A))
         (if (== (get-metatype $L) Expression)
             (if (== (car-atom $L) lsucc)
                 (Tm.app (wire:named "LeanUniv") (wire:level (car-atom (cdr-atom $L)) $env))
                 (Tm.app (wire:named "LeanSort") (wire:level $L $env)))
             (Tm.app (wire:named "LeanSort") (wire:level $L $env))))))

; The head of an application, as head-text names it, and the arguments it
; takes as a function of the logic.
(= (wire:head $c)
   (case $c
     (((EgalLibrary proof-field) (wire:named "Lean_ProofField"))
      ((EgalLibrary proof-by) (wire:literal 0))
      ((EgalLibrary cite $thm) (wire:literal 0))
      ((EgalLibrary record-field $owner $i) (Tm.app (wire:named "Lean_RecordField") (wire:literal $i)))
      ($_ (wire:named (head-text $c))))))
(= (wire:head-arity $c)
   (case $c
     (((EgalLibrary proof-field) (lean:arity "Lean_ProofField"))
      ((EgalLibrary proof-by) 0)
      ((EgalLibrary cite $thm) 0)
      ((EgalLibrary record-field $owner $i) (wire:minus (lean:arity "Lean_RecordField") 1))
      ($_ (lean:arity (head-text $c))))))
; The same for any term: what is left of its head's arity.  A variable and a
; binder are sets.
(= (wire:arity $t)
   (case $t
     (((txt $s) (lean:arity $s))
      ((app $c $args)
       (if (is-proof-node $c) 0
       (if (is-cases-on $c) 0
           (wire:minus (wire:head-arity $c) (length-of $args)))))
      ($_ 0))))

(= (wire:all $ts $env)
   (if (== $ts ()) () (cons-atom (wire (car-atom $ts) $env) (wire:all (cdr-atom $ts) $env))))

; X.casesOn, as render-cases writes it: the family's case eliminator where it
; has one, its recursor at the wrapped minors otherwise.
(= (wire:cases $c $args $env)
   (let* (($F (cases-family $c)) ($np (param-count $F))
          ($ps (take-n $args $np)) ($rest (drop-n $args (+ $np 1))))
     (if (has-cases-eliminator $F)
         (let $name (format-args "{}_casesOn" ((egal $F)))
           (wire:apply (wire:named $name) (lean:arity $name)
                       (wire:all (append-lists $ps (append-lists (cdr-atom $rest) ((car-atom $rest)))) $env)))
         (let* (($minors (wrap-minors $F $ps (motive-of (nth $args $np)) (cdr-atom $rest) 0))
                ($name (format-args "{}_rec" ((egal $F)))))
           (wire:apply (wire:named $name) (lean:arity $name)
                       (wire:all (append-lists $ps (append-lists $minors ((car-atom $rest)))) $env))))))

(= (wire $t $env)
   (case $t
     (((var $x) (wire:index $x $env 0))
      ((num $k) (Tm.app (wire:named "LeanNum") (wire:natural $k)))
      ((prop) (wire:named "LeanProp"))
      ((proof) (wire:literal 0))
      ((canon $P) (Tm.app (wire:named "Lean_DecCanon") (wire $P $env)))
      ((txt $s) (wire:named $s))
      ((apv $f $args) (wire:apply (wire $f $env) (wire:arity $f) (wire:all $args $env)))
      ((lam $x $T $b)
       (Tm.app (Tm.app (wire:named "Sigma") (wire $T $env)) (Tm.lam (Tp.base 0) (wire $b (cons-atom $x $env)))))
      ((arrow $A $B)
       (Tm.app (Tm.app (wire:named "Pi") (wire $A $env)) (Tm.lam (Tp.base 0) (wire $B (cons-atom ux $env)))))
      ((pi $x $A $B)
       (Tm.app (Tm.app (wire:named "Pi") (wire $A $env)) (Tm.lam (Tp.base 0) (wire $B (cons-atom $x $env)))))
      ((app $c $args)
       (if (is-proof-node $c) (wire:literal 0)
       (if (is-cases-on $c) (wire:cases $c $args $env)
           (wire:apply (wire:head $c) (wire:head-arity $c) (wire:all $args $env)))))
      ($_ (if (is-sort-term $t) (wire:sort $t $env)
              (Error (LeanTermForm $t) (LeanTerm "a term form with no reading")))))))

(= (lean:eq $left $right)
   (Tm.app (Tm.app (Tm.typeApp (wire:named "eq") (Tp.base 0)) $left) $right))

; ---- kernel terms as Megalodon text ----
; The way back: a kernel term written so that Megalodon reads the same term.
; A declaration is written by its first source name, a bound variable by its
; binder (x0, x1, .. outermost first), an application in full (the
; set-theoretic one as ap), and the equation of two sets with =.
;
;   (lean:text TERM)   TERM has no free variables

(= (lean:source-name $id)
   (let $kept (collapse (match &self (LeanSourceName $id $name) $name))
     (if (== $kept ())
         (let $name (lean:first-source (mg:declaration (lean:theory) $id) $id)
           (let $_kept (add-atom &self (LeanSourceName $id $name)) $name))
         (car-atom $kept))))
(= (lean:first-source $declaration $id)
   (let $found (lean:source-item (cdr-atom $declaration))
     (if (== $found None) (Error (LeanName $id) (LeanSession "the declaration has no source name")) $found)))
(= (lean:source-item $items)
   (if (== $items ()) None
       (case (car-atom $items)
         (((source $name) $name)
          ($_ (lean:source-item (cdr-atom $items)))))))

(= (wire:type-text $A)
   (case $A
     (((Tp.base 0) "set")
      ((Tp.prop) "prop")
      ((Tp.arr $a $b) (format-args "({} -> {})" ((wire:type-text $a) (wire:type-text $b))))
      ($_ (Error (LeanTypeForm $A) (LeanTerm "a type with no text"))))))
(= (wire:text $t $depth)
   (case $t
     (((Tm.db $i) (format-args "x{}" ((- (- $depth 1) $i))))
      ((Tm.named $id) (lean:source-name $id))
      ((Tm.app (Tm.app (Tm.typeApp (Tm.named $id) (Tp.base 0)) $a) $b)
       (if (== $id (lean:id "eq"))
           (format-args "({} = {})" ((wire:text $a $depth) (wire:text $b $depth)))
           (Error (LeanTermForm $t) (LeanTerm "a polymorphic constant with no text"))))
      ((Tm.app $f $x) (format-args "({} {})" ((wire:text $f $depth) (wire:text $x $depth))))
      ((Tm.lam $A $b) (format-args "(fun x{} : {} => {})" ($depth (wire:type-text $A) (wire:text $b (+ $depth 1)))))
      ((Tm.all $A $b) (format-args "(forall x{} : {}, {})" ($depth (wire:type-text $A) (wire:text $b (+ $depth 1)))))
      ((Tm.imp $p $q) (format-args "({} -> {})" ((wire:text $p $depth) (wire:text $q $depth))))
      ($_ (Error (LeanTermForm $t) (LeanTerm "a kernel term with no text"))))))
(= (lean:text $t) (wire:text $t 0))
