; Egal instances of admitted Lean inductive families.
;
; Input: the atoms of artifacts/lean-declarations/families.metta in &self:
;   (LeanFamily (Family Name (parameters Ps) (indices Is) Sort (constructors ..)) ..)
;   (LeanAdmitted Name ((Ctor (fields F..) (result (I..))) ..))
;     F = (data Sort) | (rec (I..)) | (guard I);  I = (field p) | (const c) | (app I I)
;   Guards also have (pi binder domain body) and (bound binder); those
;   binders are distinct from the constructor's fields.
;   A guard is a proof field whose proposition reads earlier fields; its sort
;   is the proposition's truth value {z :e 1 | z :e P}, an inductive
;   proposition read as E_Prop.
;   (EgalName LeanName EgalIdent)
; Output: (egal-instance Name) is the list of lines of one Megalodon section:
; the family's signature as finite sequences read by SeqAt, its types,
; constructor nodes and their typing, and the facts the general construction
; (IndFamily in LeanInEgal.mg) asks of a signature.  Every proof applies
; theorems of that construction and of the sequence layer; none searches.

; ---- strings ----

(= (join $sep $xs)
   (if (== $xs ()) ""
       (if (== (cdr-atom $xs) ()) (car-atom $xs)
           (format-args "{}{}{}" ((car-atom $xs) $sep (join $sep (cdr-atom $xs)))))))

(= (lines $xs) (join "
" $xs))

; ---- sequences, numerals and their proofs ----

(= (seq $xs)
   (if (== $xs ()) "SeqNil"
       (format-args "(SeqCons ({}) {})" ((car-atom $xs) (seq (cdr-atom $xs))))))

(= (natproof $n)
   (if (== $n 0) "nat_0"
       (format-args "(nat_ordsucc {} {})" ((- $n 1) (natproof (- $n 1))))))

; A natural number's numeral: a literal below the radix squared, otherwise its
; digits over such a literal (Library/Digits.mg: q :: d is ten times q plus d),
; so that no unary chain is longer than the bound.
(= (num-radix) 10)
(= (num-bound) 100)
(= (idiv $a $b) (/ (- $a (% $a $b)) $b))
(= (num-text $k)
   (if (< $k (num-bound)) (format-args "{}" ($k))
       (format-args "{} :: {}" ((num-text (idiv $k (num-radix))) (% $k (num-radix))))))
; As an argument: digits in parentheses.
(= (num-arg $k) (if (< $k (num-bound)) (format-args "{}" ($k)) (format-args "({})" ((num-text $k)))))
; nat_p of a numeral: a literal's from its unary chain, a numeral in digits'
; from the digits (Library/Digits.mg's Dnat_k names every literal's).
(= (num-natproof $k) (if (< $k (num-bound)) (natproof $k) (num-natproof-d $k)))
(= (dnat $k) (format-args "Dnat_{}" ($k)))
(= (num-natproof-d $k)
   (if (< $k (num-bound)) (dnat $k)
       (format-args "(NumD_p {} {} {} {})"
         ((num-arg (idiv $k (num-radix))) (num-natproof-d (idiv $k (num-radix))) (% $k (num-radix)) (dnat (% $k (num-radix)))))))

; A proof of j :e m, for j < m.
(= (inproof $j $m)
   (if (== $m (+ $j 1)) (format-args "(ordsuccI2 {})" ($j))
       (format-args "(ordsuccI1 {} {} {})" ((- $m 1) $j (inproof $j (- $m 1))))))

; Rewrite the outermost SeqAt at position k, then continue.
(= (lookup $k $cont)
   (if (== $k 0) (format-args "rewrite SeqAt_0. {}" ($cont))
       (format-args "rewrite SeqAt_S. {} {} {} exact {}."
         ("{" (lookup (- $k 1) $cont) "}" (natproof (- $k 1))))))

; ---- lists ----

(= (length-of $xs) (if (== $xs ()) 0 (+ 1 (length-of (cdr-atom $xs)))))

(= (nth $xs $i) (if (== $i 0) (car-atom $xs) (nth (cdr-atom $xs) (- $i 1))))

(= (drop-n $xs $n) (if (== $n 0) $xs (drop-n (cdr-atom $xs) (- $n 1))))
(= (take-n $xs $n) (if (== $n 0) () (cons-atom (car-atom $xs) (take-n (cdr-atom $xs) (- $n 1)))))
(= (list-has $x $xs) (if (== $xs ()) False (if (== (car-atom $xs) $x) True (list-has $x (cdr-atom $xs)))))

(= (range-from $i $n) (if (>= $i $n) () (cons-atom $i (range-from (+ $i 1) $n))))

(= (append-lists $xs $ys)
   (if (== $xs ()) $ys (cons-atom (car-atom $xs) (append-lists (cdr-atom $xs) $ys))))

; ---- names ----

(= (egal $name)
   (case $name
     (((split $f $k) (format-args "{}_split{}" ((egal $f) $k)))
      ((bk $c) (format-args "{}_b" ((egal $c))))
      ($_ (let $found (collapse (match &self (EgalName $name $e) $e))
            (if (== $found ()) (format-args "UNKNOWN_{}" ($name)) (car-atom $found)))))))

(= (param-index $name $params $i)
   (if (== $params ()) -1
       (let (: $n $t) (car-atom $params)
         (if (== $n $name) $i (param-index $name (cdr-atom $params) (+ $i 1))))))

(= (symbol-text $s $params)
   (let $i (param-index $s $params 0)
     (if (>= $i 0) (format-args "P{}" ($i)) (egal $s))))

; A sort term: parameters are section variables, families their Egal sets.
; A sort term: a function type A -> B is the set of functions Pi_; Prop is
; LeanProp; an inductive proposition is its truth value E_Prop.
(= (prop-family $name)
   (let $found (collapse (match &self (LeanFamily (Family $name $ps $is Prop $cs) $u $e $k) True))
     (if (== $found ()) False True)))

(= (sort-head-text $s $params)
   (if (prop-family $s) (format-args "{}_Prop" ((egal $s))) (symbol-text $s $params)))

(= (sort-text $t $params)
   (if (== (get-metatype $t) Expression)
       (if (== (car-atom $t) ->)
           (format-args "(Pi_ ux :e {}, {})" ((sort-text (nth $t 1) $params) (sort-text (nth $t 2) $params)))
           (let $args (cdr-atom $t)
             (format-args "({} {})" ((sort-head-text (car-atom $t) $params) (join " " (map-atom $args $u (sort-text $u $params)))))))
       (if (== $t Prop) "LeanProp" (sort-head-text $t $params))))

; An index term, with fields read from the argument tuple a ("a") or as the
; constructor's variables ("x").  An index is read as the term reader reads
; a value: a constructor applied to all its arguments is its node, and a
; closed natural is its literal (LeanNum), so that an index and a value a
; function computes are the same set.
(= (index-text $i $mode $params)
   (let $k (closed-nat $i)
     (if (== $k None) (index-text-open $i $mode $params) (format-args "(LeanNum {})" ((num-arg $k))))))
(= (index-text-open $i $mode $params)
   (case $i
     (((field $p) (case $mode
                    ((a (format-args "(a {})" ($p)))
                     (x (format-args "x{}" ($p)))
                     ((tuple $m $S) (format-args "(TupArgs {} {} {})" ($m $S $p)))
                     ((mixed $j0) (if (< $p $j0) (format-args "(a {})" ($p)) (format-args "x{}" ($p)))))))
      ((const $c) (if (full-ctor-app $c 0) (format-args "{}_node" ((egal $c))) (symbol-text $c $params)))
      ((bound $name) (format-args "{}" ($name)))
      ((project $owner $field $record)
       (format-args "((proj1 {}) {})" ((index-text $record $mode $params) $field)))
      ((code $n) (format-args "{}" ($n)))
      ((app $f $x)
       (let* (($h (index-head $i)) ($as (index-args $i)))
         (if (full-ctor-app $h (length-of $as))
             (format-args "({}_node {})" ((egal $h) (join " " (map-atom $as $y (index-text $y $mode $params)))))
             (format-args "({} {})" ((index-text $f $mode $params) (index-text $x $mode $params)))))))))

; A closed natural: zero and successors of closed naturals.
(= (closed-nat $i)
   (case $i
     (((const Nat.zero) 0)
      ((app (const Nat.succ) $x) (let $k (closed-nat $x) (if (== $k None) None (+ $k 1))))
      ($_ None))))
(= (index-head $i) (case $i (((app $f $x) (index-head $f)) ((const $c) $c) ($_ None))))
(= (index-args $i) (case $i (((app $f $x) (append-lists (index-args $f) (cons-atom $x ()))) ($_ ()))))
; A constructor applied to its parameters and all its fields.
(= (full-ctor-app $c $n)
   (if (== $c None) False
       (case (ctor-owner $c)
         (((owner $fam $ctor) (== $n (+ (length-of (params-of $fam)) (length-of (ctor-fields $ctor)))))
          ($_ False)))))

; The index of a family with several indices is the tuple of its values.
(= (indices-text $is $mode $params)
   (if (== $is ()) "0"
       (if (== (cdr-atom $is) ()) (index-text (car-atom $is) $mode $params)
           (format-args "(setsum {} {})"
             ((index-text (car-atom $is) $mode $params) (indices-text (cdr-atom $is) $mode $params))))))

;
; ---- a family's indices ----
; A family with several indices is curried, as Lean's is: E i0 i1.  Inside,
; its fiber is at the tuple of the indices (setsum i0 i1), and the motive of
; its recursor takes each index, read from the tuple by projections.

(= (fam-app $E $q $is $mode $params)
   (if (== $q 0) $E
       (if (== $q 1) (format-args "({} {})" ($E (indices-text $is $mode $params)))
           (format-args "({} {})" ($E (join " " (map-atom $is $i (index-text $i $mode $params))))))))
; The indices a section's family takes.  A block's index, a member's tag and
; the member's own indices, is one tuple: the members are Lean's families,
; the block is their encoding.
(= (section-q $name)
   (case $name
     (((bk $F) (if (== (index-count $name) 0) 0 1))
      ($_ (if (is-prop $name) (if (== (index-count $name) 0) 0 1) (index-count $name))))))
(= (ivar-list $q $p) (map-atom (range-from 0 $q) $j (format-args "{}{}" ($p $j))))
(= (tuple-text $xs)
   (if (== (cdr-atom $xs) ()) (car-atom $xs) (format-args "(setsum {} {})" ((car-atom $xs) (tuple-text (cdr-atom $xs))))))
(= (motive-ty $q) (format-args "{}set -> set" ((join "" (map-atom (range-from 0 $q) $j "set -> ")))))
; The q components of a tuple.
(= (proj-texts $q $i)
   (if (== $q 1) (cons-atom $i ())
       (cons-atom (format-args "(proj0 {})" ($i)) (proj-texts (- $q 1) (format-args "(proj1 {})" ($i))))))
(= (cprime-text $q $E)
   (if (== $q 0) "C" (format-args "(fun t:set => C {} t)" ((join " " (proj-texts $q (format-args "(IndIdx {} t)" ((sig $E)))))))))
; Moving a motive between its indices and their tuple's projections.
(= (motive-pair $q) (if (== $q 2) "In_motive2_pair" "motive_with_more_than_two_indices_not_read"))
(= (motive-unpair $q) (if (== $q 2) "In_motive2_unpair" "motive_with_more_than_two_indices_not_read"))

; ---- the declaration ----

(= (family-of $name)
   (case $name
     (((bk $F)
       (case (family-of $F)
         (((Family $n $ps $is $s $cs)
           (let $m0 (car-atom (block-members $F))
             (Family (bk $F) $ps (indices (cons-atom (: tag Nat) (member-indices $m0))) (member-sort $m0) ()))))))
      ($_ (family-of-decl $name)))))
(= (family-of-decl $name)
   (car-atom (collapse (match &self (LeanFamily (Family $name $ps $is $sort $cs) $u $e $k)
                         (Family $name $ps $is $sort $cs)))))

(= (params-of $name)
   (case (family-of $name) (((Family $n (parameters $ps) $is $s $cs) $ps))))

(= (index-count $name)
   (case (family-of $name) (((Family $n $ps (indices $is) $s $cs) (length-of $is)))))

(= (constructors-of $name)
   (case $name
     (((bk $F) (block-ctors $F))
      ($_ (let $found (collapse (match &self (LeanAdmitted $name $cs) $cs))
            (if (== $found ()) (member-view-ctors $name) (car-atom $found)))))))

(= (ctor-name $c) (case $c ((($n $fs $r) $n))))
(= (ctor-fields $c) (case $c ((($n $fs $r) (cdr-atom $fs)))))
(= (ctor-result $c) (case $c ((($n $fs (result $is)) $is))))

(= (is-rec $f) (case $f (((rec $is) True) ($_ False))))
(= (is-guard $f) (case $f (((guard $p) True) ($_ False))))

; A guard's proposition, read from the fields in $mode: an inductive
; proposition at its head is its truth value E_Prop.
(= (guard-text $i $mode $params)
   (case $i
     (((const $c) (if (is-prop $c) (format-args "{}_Prop" ((egal $c))) (index-text $i $mode $params)))
      ((pi $binder $domain $body)
       (format-args "(Pi_ {} :e {}, {})"
         ($binder (guard-text $domain $mode $params) (guard-text $body $mode $params))))
      ((app $f $x) (format-args "({} {})" ((guard-text $f $mode $params) (index-text $x $mode $params))))
      ($_ (index-text $i $mode $params)))))

(= (guard-sort $p $mode $params)
   (format-args "{}z :e 1 | z :e {}{}" ("{" (guard-text $p $mode $params) "}")))

; ---- signature ----

(= (sig $E) (format-args "{}_K {}_T {}_N {}_R {}_F {}_Ix {}_O {}_B" ($E $E $E $E $E $E $E $E)))

(= (field-flag $f) (if (is-rec $f) "1" "0"))
(= (field-sort $f $params) (case $f (((data $t) (sort-text $t $params)) ((guard $p) (guard-sort $p a $params)) ($_ "0"))))
(= (field-index $f $params) (case $f (((rec $is) (indices-text $is a $params)) ($_ "0"))))

; Every data sort of the family, in constructor and field order.
(= (field-data-sorts $fs $params)
   (if (== $fs ()) ()
       (let $rest (field-data-sorts (cdr-atom $fs) $params)
         (if (is-rec (car-atom $fs)) $rest
             (cons-atom (if (is-guard (car-atom $fs)) "1" (field-sort (car-atom $fs) $params)) $rest)))))

(= (data-sorts $cs $params)
   (if (== $cs ()) ()
       (append-lists (field-data-sorts (ctor-fields (car-atom $cs)) $params)
         (data-sorts (cdr-atom $cs) $params))))

(= (union-text $sorts)
   (if (== $sorts ()) "0"
       (union-prefix $sorts (- (length-of $sorts) 1))))

; The union of the first i+1 sorts, left-nested.
(= (union-prefix $sorts $i)
   (if (== $i 0) (format-args "({})" ((nth $sorts 0)))
       (format-args "({} :\\/: ({}))" ((union-prefix $sorts (- $i 1)) (nth $sorts $i)))))

; A proof of x :e B from h : x :e (sort i).
(= (union-member $sorts $i $x $h)
   (lift-member $sorts $i (- (length-of $sorts) 1) $x
     (if (== $i 0) $h
         (format-args "(binunionI2 {} ({}) {} {})"
           ((union-prefix $sorts (- $i 1)) (nth $sorts $i) $x $h)))))

(= (lift-member $sorts $i $top $x $h)
   (if (>= $i $top) $h
       (lift-member $sorts (+ $i 1) $top $x
         (format-args "(binunionI1 {} ({}) {} {})"
           ((union-prefix $sorts $i) (nth $sorts (+ $i 1)) $x $h)))))

; The signature's sequences, rendered once for its Lets and its facts.
(= (ns-seq $cs) (let $xs (map-atom $cs $c (format-args "{}" ((length-of (ctor-fields $c))))) (seq $xs)))
(= (rs-seq $cs) (let $xs (map-atom $cs $c (let $fs (ctor-fields $c) (seq (map-atom $fs $f (field-flag $f))))) (seq $xs)))
(= (fs-seq $cs $params) (let $xs (map-atom $cs $c (let $fs (ctor-fields $c) (seq (map-atom $fs $f (field-sort $f $params))))) (seq $xs)))
(= (ix-seq $cs $params) (ix-seq-mode $cs $params a))
(= (os-seq $cs $params) (os-seq-mode $cs $params a))
(= (ix-seq-mode $cs $params $mode)
   (let $xs (map-atom $cs $c (let $fs (ctor-fields $c) (seq (map-atom $fs $f (field-index-mode $f $params $mode))))) (seq $xs)))
(= (os-seq-mode $cs $params $mode)
   (let $xs (map-atom $cs $c (indices-text (ctor-result $c) $mode $params)) (seq $xs)))
(= (field-index-mode $f $params $mode) (case $f (((rec $is) (indices-text $is $mode $params)) ($_ "0"))))

(= (signature-lets $E $cs $params)
   ((format-args "Let {}_K : set := {}." ($E (length-of $cs)))
    (format-args "Let {}_T : set -> set := fun k => k." ($E))
    (format-args "Let {}_N : set -> set := fun k => SeqAt {} k." ($E (ns-seq $cs)))
    (format-args "Let {}_R : set -> set -> prop := fun k j => 0 :e SeqAt (SeqAt {} k) j." ($E (rs-seq $cs)))
    (format-args "Let {}_F : set -> set -> set -> set := fun k j a => SeqAt (SeqAt {} k) j." ($E (fs-seq $cs $params)))
    (format-args "Let {}_Ix : set -> set -> set -> set := fun k j a => SeqAt (SeqAt {} k) j." ($E (ix-seq $cs $params)))
    (format-args "Let {}_O : set -> set -> set := fun k a => SeqAt {} k." ($E (os-seq $cs $params)))
    (format-args "Let {}_B : set := {}." ($E (union-text (data-sorts $cs $params))))))

; ---- cases below a natural ----

; A proof of forall j :e m, P j from the proofs of P 0, .., P (m-1).
(= (below $m $P $cases)
   (if (== $m 0) (format-args "(Below_0 {})" ($P))
       (format-args "(Below_S {} {} {} {})"
         ((- $m 1) $P (below (- $m 1) $P (take-list $cases (- $m 1))) (nth $cases (- $m 1))))))

(= (take-list $xs $n) (if (== $n 0) () (cons-atom (car-atom $xs) (take-list (cdr-atom $xs) (- $n 1)))))

; ---- facts read from the signature ----

; The position, among all data sorts, of data field j of constructor k.
(= (data-offset $cs $k $j)
   (if (== $k 0) (count-data (take-list (ctor-fields (car-atom $cs)) $j))
       (+ (count-data (ctor-fields (car-atom $cs))) (data-offset (cdr-atom $cs) (- $k 1) $j))))

(= (count-data $fs)
   (if (== $fs ()) 0 (+ (if (is-rec (car-atom $fs)) 0 1) (count-data (cdr-atom $fs)))))

(= (fact-lines $E $cs $params)
   (append-lists
     (let $ks (range-from 0 (length-of $cs)) (map-atom $ks $k (ctor-fact-lines $E $cs $params $k)))
     ()))

(= (ctor-fact-lines $E $cs $params $k)
   (let* (($c (nth $cs $k))
          ($fs (ctor-fields $c))
          ($m (length-of $fs)))
     (format-args "{}{}{}"
       ((format-args "Theorem {}_N{} : SeqAt {} {} = {}.
{}
Qed.
" ($E $k (ns-seq $cs) $k $m (lookup $k "reflexivity.")))
        (format-args "Theorem {}_O{} : forall a, SeqAt {} {} = {}.
let a. {}
Qed.
" ($E $k (os-seq $cs $params) $k (indices-text (ctor-result $c) a $params) (lookup $k "reflexivity.")))
        (join "" (let $mlist4 (range-from 0 $m) (map-atom $mlist4 $j (field-fact-text $E $cs $params $k $j))))))))

(= (field-fact-text $E $cs $params $k $j)
   (let $f (nth (ctor-fields (nth $cs $k)) $j)
     (if (is-rec $f)
         (format-args "Theorem {}_R{}_{} : 0 :e SeqAt (SeqAt {} {}) {}.
{}
Qed.
Theorem {}_Ix{}_{} : forall a, SeqAt (SeqAt {} {}) {} = {}.
let a. {}
Qed.
"
           ($E $k $j (rs-seq $cs) $k $j (lookup $k (lookup $j "exact In_0_1."))
            $E $k $j (ix-seq $cs $params) $k $j (field-index $f $params) (lookup $k (lookup $j "reflexivity."))))
         (format-args "Theorem {}_nR{}_{} : ~ (0 :e SeqAt (SeqAt {} {}) {}).
{}
Qed.
Theorem {}_F{}_{} : forall a, SeqAt (SeqAt {} {}) {} = {}.
let a. {}
Qed.
"
           ($E $k $j (rs-seq $cs) $k $j (lookup $k (lookup $j "exact EmptyE 0."))
            $E $k $j (fs-seq $cs $params) $k $j (field-sort $f $params) (lookup $k (lookup $j "reflexivity.")))))))

; ---- the facts the general construction asks of a signature ----

(= (bounded-text $E $cs $params)
   (let* (($n (length-of $cs))
          ($sorts (data-sorts $cs $params))
          ($fieldcases (let $mlist5 (range-from 0 $n) (map-atom $mlist5 $k (bounded-ctor-text $E $cs $params $sorts $k))))
          ($P "(fun k => forall a, forall j :e {}_N k, ~ {}_R k j -> {}_F k j a c= {}_B)"))
     (format-args "{}Theorem {}_bounded : IndBounded {}.
let k. assume Hk: k :e {}_K.
exact {} k Hk.
Qed.
"
       ((join "" $fieldcases) $E (sig $E) $E
        (below $n (format-args $P ($E $E $E $E))
          (let $mlist6 (range-from 0 $n) (map-atom $mlist6 $k (format-args "{}_bd{}" ($E $k)))))))))

(= (bounded-ctor-text $E $cs $params $sorts $k)
   (let* (($fs (ctor-fields (nth $cs $k)))
          ($m (length-of $fs))
          ($P (format-args "(fun j => ~ {}_R {} j -> {}_F {} j a c= {}_B)" ($E $k $E $k $E))))
     (format-args "{}Theorem {}_bd{} : forall a, forall j :e {}_N {}, ~ {}_R {} j -> {}_F {} j a c= {}_B.
let a j. assume Hj: j :e {}_N {}. assume Hnr: ~ {}_R {} j.
exact {} j (In_eq_r j ({}_N {}) {} {}_N{} Hj) Hnr.
Qed.
"
       ((join "" (let $mlist7 (range-from 0 $m) (map-atom $mlist7 $j (bounded-field-text $E $cs $params $sorts $k $j))))
        $E $k $E $k $E $k $E $k $E $E $k $E $k
        (below $m $P (let $mlist8 (range-from 0 $m) (map-atom $mlist8 $j (format-args "({}_bd{}_{} a)" ($E $k $j)))))
        $E $k $m $E $k))))

(= (bounded-field-text $E $cs $params $sorts $k $j)
   (let $f (nth (ctor-fields (nth $cs $k)) $j)
     (if (is-rec $f)
         (format-args "Theorem {}_bd{}_{} : forall a, ~ {}_R {} {} -> {}_F {} {} a c= {}_B.
let a. assume Hnr: ~ {}_R {} {}. apply FalseE. exact Hnr {}_R{}_{}.
Qed.
" ($E $k $j $E $k $j $E $k $j $E $E $k $j $E $k $j))
         (format-args "Theorem {}_bd{}_{} : forall a, ~ {}_R {} {} -> {}_F {} {} a c= {}_B.
let a. assume Hnr: ~ {}_R {} {}. let z. assume Hz: z :e {}_F {} {} a.
exact {}.
Qed.
"
           ($E $k $j $E $k $j $E $k $j $E $E $k $j $E $k $j
            (union-member $sorts (data-offset $cs $k $j) "z"
              (guard-member $f $params a "z"
                (format-args "(In_eq_r z ({}_F {} {} a) ({}) ({}_F{}_{} a) Hz)"
                  ($E $k $j (field-sort $f $params) $E $k $j)))))))))

; From x :e (the field's sort), x :e (its union member): a guard's sort lies in 1.
(= (guard-member $f $params $mode $x $h)
   (case $f
     (((guard $p) (format-args "(SepE1 1 (fun z => z :e {}) {} {})" ((guard-text $p $mode $params) $x $h)))
      ($_ $h))))

(= (distinct-text $E)
   (format-args "Theorem {}_distinct : IndDistinct {}.
let k. assume Hk: k :e {}_K. let k'. assume Hk': k' :e {}_K. assume H: k = k'. exact H.
Qed.
" ($E (sig $E) $E $E)))

(= (arity-text $E $cs)
   (let $n (length-of $cs)
     (format-args "{}Theorem {}_arity : forall k :e {}_K, nat_p ({}_N k).
let k. assume Hk: k :e {}_K.
exact {} k Hk.
Qed.
"
       ((join "" (let $mlist9 (range-from 0 $n) (map-atom $mlist9 $k
          (format-args "Theorem {}_ar{} : nat_p ({}_N {}).
prove nat_p (SeqAt {} {}). rewrite {}_N{}. exact {}.
Qed.
" ($E $k $E $k (ns-seq $cs) $k $E $k (natproof (length-of (ctor-fields (nth $cs $k)))))))))
        $E $E $E $E
        (below $n (format-args "(fun k => nat_p ({}_N k))" ($E))
          (let $mlist10 (range-from 0 $n) (map-atom $mlist10 $k (format-args "{}_ar{}" ($E $k)))))))))

; ---- one section ----

; A family without constructors (False, Empty): the general construction at
; K = 0, whose carrier has no member; an inductive proposition is false.
(= (empty-section $name)
   (let* (($E (egal $name)) ($S (sig $E)))
     ((format-args "(** ---- {}, generated from its Lean declaration ---- **)" ($name))
      "" (format-args "Section {}_Section." ($E)) ""
      (format-args "Let {}_K : set := 0." ($E))
      (format-args "Let {}_T : set -> set := fun k => k." ($E))
      (format-args "Let {}_N : set -> set := fun k => 0." ($E))
      (format-args "Let {}_R : set -> set -> prop := fun k j => 0 :e 0." ($E))
      (format-args "Let {}_F : set -> set -> set -> set := fun k j a => 0." ($E))
      (format-args "Let {}_Ix : set -> set -> set -> set := fun k j a => 0." ($E))
      (format-args "Let {}_O : set -> set -> set := fun k a => 0." ($E))
      (format-args "Let {}_B : set := 0." ($E))
      ""
      (format-args "Definition {}_All : set := IndCarrier {}." ($E $S))
      (format-args "Definition {} : set := IndFiber {} 0." ($E $S))
      (format-args "Theorem {}_empty : forall t, t /:e {}.
let t. assume Ht: t :e {}.
apply IndCarrier_inv {} t (SepE1 {}_All (fun x:set => IndIdx {} x = 0) t Ht).
let k. assume Hk: k :e {}_K /\\ exists a :e IndArgs {} {}_All k, t = IndNode {} k a.
exact EmptyE k (andEL (k :e {}_K) (exists a :e IndArgs {} {}_All k, t = IndNode {} k a) Hk).
Qed." ($E $E $E $S $E $S $E $S $E $S $E $S $E $S))
      (if (is-prop $name)
          (format-args "Definition {}_Prop : set := {}x :e 1 | exists w, w :e {}{}.
Theorem {}_Prop_prop : {}_Prop :e LeanProp.
exact PowerI 1 {}_Prop (Sep_Subq 1 (fun x:set => exists w, w :e {})).
Qed.
Theorem {}_Prop_false : forall t, t /:e {}_Prop.
let t. assume Ht: t :e {}_Prop.
apply SepE2 1 (fun x:set => exists w, w :e {}) t Ht.
let w. assume Hw: w :e {}. exact {}_empty w Hw.
Qed." ($E "{" $E "}" $E $E $E $E $E $E $E $E $E $E $E))
          "")
      (format-args "End {}_Section." ($E)))))

(= (egal-section $name)
   (if (== (constructors-of $name) ()) (empty-section $name) (egal-section-ctors $name)))

(= (egal-section-ctors $name)
   (let* (($E (egal $name))
          ($cs (constructors-of $name))
          ($params (params-of $name))
          ($q (section-q $name))
          ($vars (let $mlist11 (range-from 0 (length-of $params)) (map-atom $mlist11 $i (format-args "Variable P{} : set." ($i))))))
     (append-lists
       ((format-args "(** ---- {}, generated from its Lean declaration ---- **)" ($name))
        "" (format-args "Section {}_Section." ($E)) "")
       (append-lists $vars
         (append-lists (signature-lets $E $cs $params)
           ("" (format-args "Definition {}_All : set := IndCarrier {}." ($E (sig $E)))
            (if (== $q 0) (format-args "Definition {} : set := IndFiber {} 0." ($E (sig $E)))
                (if (== $q 1) (format-args "Definition {} : set -> set := IndFiber {}." ($E (sig $E)))
                    (format-args "Definition {} : {} := fun {} => IndFiber {} {}."
                      ($E (node-type $q) (join " " (ivar-list $q i)) (sig $E) (tuple-text (ivar-list $q i))))))
            ""
            (fact-text $E $cs $params)
            (bounded-text $E $cs $params)
            (distinct-text $E)
            (arity-text $E $cs)
            (let $ks (range-from 0 (length-of $cs)) (join "" (map-atom $ks $k (ctor-text $name $cs $params $q $k))))
            (rec-text $name $cs $params $q)
            (rec-type-text $name $cs $params $q)
            (if (has-cases-eliminator $name) (cases-text $name $cs $params $q) "")
            (if (has-cases-eliminator $name) (cases-type-text $name $cs $params $q) "")
            (if (and (== $q 0) (not (is-prop $name))) (ind-text $name $cs $params) "")
            (if (and (== $q 1) (is-prop $name)) (indexed-ind-text $name $cs $params) "")
            (noconf-text $name $cs)
            (inj-text $name $cs)
            (fiber-text $name $q)
            (if (is-prop $name) (prop-text $name $cs $params $q) (in-text $name $cs $params $q))
            (format-args "End {}_Section.{}" ($E (if (== $name Nat) (format-args "

{}" ((nat-literals-text))) "")))))))))

; Lean's Nat literals, read with the Nat family (Numerals.mg has the rest).
(= (nat-literals-text) "(** Lean's natural number literals: the literal n is the ordinal n carried
    into Lean_Nat by zero and successor.  Families after Nat read their
    closed natural indices this way, as the term reader reads literals. **)

Definition LeanNum : set -> set :=
  fun n => nat_primrec Lean_Nat_zero_node (fun _ r => Lean_Nat_succ_node r) n.

Theorem LeanNum_0 : LeanNum 0 = Lean_Nat_zero_node.
exact nat_primrec_0 Lean_Nat_zero_node (fun _ r => Lean_Nat_succ_node r).
Qed.

Theorem LeanNum_S : forall n, nat_p n -> LeanNum (ordsucc n) = Lean_Nat_succ_node (LeanNum n).
let n. assume Hn: nat_p n.
exact nat_primrec_S Lean_Nat_zero_node (fun _ r => Lean_Nat_succ_node r) n Hn.
Qed.

Theorem LeanNum_In : forall n, nat_p n -> LeanNum n :e Lean_Nat.
apply nat_ind.
- rewrite LeanNum_0. exact Lean_Nat_zero_typed.
- let n. assume Hn: nat_p n. assume IH: LeanNum n :e Lean_Nat.
  rewrite LeanNum_S n Hn. exact Lean_Nat_succ_typed (LeanNum n) IH.
Qed.

Theorem LeanNum_inj : forall m, nat_p m -> forall n, nat_p n -> LeanNum m = LeanNum n -> m = n.
apply nat_ind (fun m => forall n, nat_p n -> LeanNum m = LeanNum n -> m = n).
- let n. assume Hn: nat_p n.
  apply nat_inv n Hn.
  + assume H0: n = 0. assume _. rewrite H0. reflexivity.
  + assume Hex: exists k, nat_p k /\\ n = ordsucc k.
    apply Hex. let k. assume Hk: nat_p k /\\ n = ordsucc k.
    apply Hk. assume Hk1: nat_p k. assume Hk2: n = ordsucc k.
    rewrite Hk2. rewrite LeanNum_0. rewrite LeanNum_S k Hk1.
    assume H: Lean_Nat_zero_node = Lean_Nat_succ_node (LeanNum k).
    prove False. exact Lean_Nat_noconf0_1 (LeanNum k) H.
- let m. assume Hm: nat_p m.
  assume IH: forall n, nat_p n -> LeanNum m = LeanNum n -> m = n.
  let n. assume Hn: nat_p n.
  apply nat_inv n Hn.
  + assume H0: n = 0. rewrite H0. rewrite LeanNum_0. rewrite LeanNum_S m Hm.
    assume H: Lean_Nat_succ_node (LeanNum m) = Lean_Nat_zero_node.
    prove False. exact Lean_Nat_noconf0_1 (LeanNum m) (eq_sym_i (Lean_Nat_succ_node (LeanNum m)) Lean_Nat_zero_node H).
  + assume Hex: exists k, nat_p k /\\ n = ordsucc k.
    apply Hex. let k. assume Hk: nat_p k /\\ n = ordsucc k.
    apply Hk. assume Hk1: nat_p k. assume Hk2: n = ordsucc k.
    rewrite Hk2. rewrite LeanNum_S m Hm. rewrite LeanNum_S k Hk1.
    assume H: Lean_Nat_succ_node (LeanNum m) = Lean_Nat_succ_node (LeanNum k).
    rewrite IH k Hk1 (Lean_Nat_succ_inj0 (LeanNum m) (LeanNum k) H).
    reflexivity.
Qed.
")

(= (fact-text $E $cs $params) (join "" (fact-lines $E $cs $params)))

; ---- constructors ----

(= (xs-of $m) (let $is (range-from 0 $m) (map-atom $is $i (format-args "x{}" ($i)))))
(= (tuple-of $m) (seq (xs-of $m)))

; The type of field j, its variables the earlier fields.
(= (field-type $E $q $f $params)
   (case $f
     (((data $t) (sort-text $t $params))
      ((guard $p) (guard-sort $p x $params))
      ((rec $is) (fam-app $E $q $is x $params)))))

(= (result-type $E $q $c $params)
   (fam-app $E $q (ctor-result $c) x $params))

; forall x0 :e T0, .., body
(= (binders $E $q $fs $params $j $body)
   (if (== $fs ()) $body
       (format-args "forall x{} :e {}, {}"
         ($j (field-type $E $q (car-atom $fs) $params) (binders $E $q (cdr-atom $fs) $params (+ $j 1) $body)))))

; let x0. assume H0: x0 :e T0. ..
(= (intros $E $q $fs $params $j)
   (if (== $fs ()) ""
       (format-args "let x{}. assume H{}: x{} :e {}. {}"
         ($j $j $j (field-type $E $q (car-atom $fs) $params) (intros $E $q (cdr-atom $fs) $params (+ $j 1))))))

(= (applied $head $m) (if (== $m 0) $head (format-args "{} {}" ($head (join " " (xs-of $m))))))
(= (hyp-args $m) (let $is (range-from 0 $m) (join " " (map-atom $is $i (format-args "x{} H{}" ($i $i))))))

(= (ctor-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($S (tuple-of $m))
          ($T (format-args "(TupArgs {} {})" ($m $S)))
          ($tmode (tuple $m $S))
          ($rt (result-type $E $q $c $params)))
     (join "" (
       (if (== $m 0)
           (format-args "Definition {}_node : set := IndNode {} {} (TupArgs 0 SeqNil).
" ($C (sig $E) $k))
           (format-args "Definition {}_node : {} := fun {} => IndNode {} {} {}.
" ($C (node-type $m) (join " " (xs-of $m)) (sig $E) $k $T)))
       (if (== (length-of $cs) 1) (record-fields-text $E $C $k $m $S $T) "")
       (args-text $E $C $cs $params $q $k $fs $m $S $T $tmode)
       (typed-text $E $C $cs $params $q $k $fs $m $S $T $tmode $rt)
       (if (and (== $q 0) (in-index (ctor-name $c))) (node-in-text $E $C $cs $params $k $m $S $T) "")
       (term-text $E $C $params $q $fs $m $rt)))))

; Field readback is proved once for each single-constructor family. The
; equation holds on the full constructor tuple, including proof positions.
(= (record-fields-text $E $C $k $m $S $T)
   (join "" (map-atom (range-from 0 $m) $j
     (format-args "Theorem {}_field{} : forall {}, (proj1 ({}_node {})) {} = x{}.
let {}.
prove (proj1 (IndNode {} {} {})) {} = x{}.
rewrite IndNode_fields {} {} {} {}.
rewrite TupArgs_at {} {} {} {}.
{}
Qed.
" ($C $j (join " " (xs-of $m)) $C (join " " (xs-of $m)) $j $j
     (join " " (xs-of $m)) (sig $E) $k $T $j $j
     (sig $E) $k $T $j $m $S $j (inproof $j $m) (lookup $j "reflexivity."))))))

; A node of a family without indices lies in a universe that holds its
; fields: for the constructors read in some family's indices.
(= (node-in-text $E $C $cs $params $k $m $S $T)
   (let $js (range-from 0 $m)
     (format-args "Theorem {}_node_In : forall u, nat_p u -> {}{} :e LeanUniv u.
let u. assume Hu: nat_p u. {}
claim Ht: TransSet (LeanUniv u).
{} exact LeanUniv_TransSet u Hu. {}
claim Hz: ZF_closed (LeanUniv u).
{} exact LeanUniv_ZF_closed u Hu. {}
{}claim Lo: {}_O {} {} = 0.
{} prove SeqAt {} {} = 0. rewrite {}_O{} {}. reflexivity. {}
prove IndNode {} {} {} :e LeanUniv u.
exact IndNode_univ (LeanUniv u) Ht Hz {} {} {} (LeanUniv_nat_In u Hu {} {})
  (In_eq_ls ({}_O {} {}) 0 (LeanUniv u) Lo (LeanUniv_0_In u Hu))
  (TupArgs_univ (LeanUniv u) Ht Hz {} (LeanUniv_nat_In u Hu {} {}) {} {}).
Qed.
"
       ($C (join "" (map-atom $js $j (format-args "forall x{} :e LeanUniv u, " ($j)))) (applied (format-args "{}_node" ($C)) $m)
        (join "" (map-atom $js $j (format-args "let x{}. assume H{}: x{} :e LeanUniv u. " ($j $j $j))))
        "{" "}" "{" "}"
        (join "" (map-atom $js $j (format-args "claim U{}: SeqAt {} {} = x{}.
{} {} {}
" ($j $S $j $j "{" (lookup $j "reflexivity.") "}"))))
        $E $k $T
        "{" (os-seq $cs $params) $k $E $k $T "}"
        (sig $E) $k $T
        (sig $E) $k $T $k (natproof $k)
        $E $k $T
        $m $m (natproof $m) $S
        (below $m (format-args "(fun j => SeqAt {} j :e LeanUniv u)" ($S))
          (map-atom $js $j (format-args "(In_eq_ls (SeqAt {} {}) x{} (LeanUniv u) U{} H{})" ($S $j $j $j $j))))))))

(= (node-type $m) (if (== $m 0) "set" (format-args "set -> {}" ((node-type (- $m 1))))))

; Claims U_j : SeqAt S j = x_j and T_j : TupArgs m S j = x_j, for every field.
(= (tuple-claims $m $S)
   (let $js (range-from 0 $m)
     (join "" (map-atom $js $j
       (format-args "claim U{}: SeqAt {} {} = x{}.
{} {} {}
claim T{}: TupArgs {} {} {} = x{}.
{} rewrite TupArgs_at {} {} {} {}. exact U{}. {}
" ($j $S $j $j "{" (lookup $j "reflexivity.") "}"
   $j $m $S $j $j "{" $m $S $j (inproof $j $m) $j "}"))))))

; Claims V_j, I_j for recursive fields: membership and index.
(= (rec-claims $E $q $fs $params $j)
   (if (== $fs ()) ""
       (let $rest (rec-claims $E $q (cdr-atom $fs) $params (+ $j 1))
         (case (car-atom $fs)
           (((rec $is)
             (let $idx (if (== $q 0) "0" (indices-text $is x $params))
               (format-args "claim V{}: x{} :e {}_All.
{} exact SepE1 {}_All (fun x:set => IndIdx {} x = {}) x{} H{}. {}
claim I{}: IndIdx {} x{} = {}.
{} exact SepE2 {}_All (fun x:set => IndIdx {} x = {}) x{} H{}. {}
{}" ($j $j $E "{" $E (sig $E) $idx $j $j "}" $j (sig $E) $j $idx "{" $E (sig $E) $idx $j $j "}" $rest))))
            ($_ $rest))))))

(= (args-text $E $C $cs $params $q $k $fs $m $S $T $tmode)
   (let* (($sorts (data-sorts $cs $params))
          ($Ppi (format-args "(fun j => SeqAt {} j :e {}_B :\\/: {}_All)" ($S $E $E)))
          ($Pfit (format-args "(fun j => ({}_R {} j -> {} j :e {}_All /\\ IndIdx {} ({} j) = {}_Ix {} j {}) /\\ (~ {}_R {} j -> {} j :e {}_F {} j {}))"
                    ($E $k $T $E (sig $E) $T $E $k $T $E $k $T $E $k $T)))
          ($js (range-from 0 $m))
          ($picases (map-atom $js $j (format-args "M{}" ($j))))
          ($fitcases (map-atom $js $j (format-args "D{}" ($j)))))
     (format-args "Theorem {}_args : {}.
{}
{}{}{}{}prove {} :e {}a :e Pi_ j :e SeqAt {} {}, {}_B :\\/: {}_All | IndFits {} {}_All {} a{}.
rewrite {}_N{}.
apply SepI (Pi_ j :e {}, {}_B :\\/: {}_All) (fun a => IndFits {} {}_All {} a) {}.
- exact lam_Pi {} (fun j => {}_B :\\/: {}_All) (fun j => SeqAt {} j) {}.
- prove IndFits {} {}_All {} {}.
  let j. assume Hj: j :e {}_N {}.
  exact {} j (In_eq_r j ({}_N {}) {} {}_N{} Hj).
Qed.
"
       ($C (binders $E $q $fs $params 0 (format-args "{} :e IndArgs {} {}_All {}" ($T (sig $E) $E $k)))
        (intros $E $q $fs $params 0)
        (tuple-claims $m $S)
        (rec-claims $E $q $fs $params 0)
        (join "" (map-atom $js $j (pi-claim $E $q $fs $params $sorts $cs $k $j $S)))
        (join "" (map-atom $js $j (fit-claim $E $q $fs $params $cs $k $j $m $S $T $tmode)))
        $T "{" (ns-seq $cs) $k $E $E (sig $E) $E $k "}"
        $E $k
        $m $E $E (sig $E) $E $k $T
        $m $E $E $S (below $m $Ppi $picases)
        (sig $E) $E $k $T
        $E $k
        (below $m $Pfit $fitcases) $E $k $m $E $k))))

(= (pi-claim $E $q $fs $params $sorts $cs $k $j $S)
   (let $f (nth $fs $j)
     (format-args "claim M{}: SeqAt {} {} :e {}_B :\\/: {}_All.
{} exact In_eq_ls (SeqAt {} {}) x{} ({}_B :\\/: {}_All) {} {}. {}
"
       ($j $S $j $E $E "{" $S $j $j $E $E
        (format-args "U{}" ($j))
        (if (is-rec $f)
            (format-args "(binunionI2 {}_B {}_All x{} V{})" ($E $E $j $j))
            (format-args "(binunionI1 {}_B {}_All x{} {})"
              ($E $E $j (union-member $sorts (data-offset $cs $k $j) (format-args "x{}" ($j))
                          (guard-member $f $params x (format-args "x{}" ($j)) (format-args "H{}" ($j)))))))
        "}"))))

(= (fit-claim $E $q $fs $params $cs $k $j $m $S $T $tmode)
   (let $f (nth $fs $j)
     (if (is-rec $f)
         (format-args "claim D{}: ({}_R {} {} -> {} {} :e {}_All /\\ IndIdx {} ({} {}) = {}_Ix {} {} {}) /\\ (~ {}_R {} {} -> {} {} :e {}_F {} {} {}).
{} apply andI.
  - assume Hr: {}_R {} {}. apply andI.
    + exact In_eq_ls ({} {}) x{} {}_All T{} V{}.
    + rewrite T{}. prove IndIdx {} x{} = SeqAt (SeqAt {} {}) {}. rewrite {}_Ix{}_{} {}. {} exact I{}.
  - assume Hnr: ~ {}_R {} {}. apply FalseE. exact Hnr {}_R{}_{}.
{}
"
           ($j $E $k $j $T $j $E (sig $E) $T $j $E $k $j $T $E $k $j $T $j $E $k $j $T
            "{" $E $k $j $T $j $j $E $j $j
            $j (sig $E) $j (ix-seq-mode $cs $params $tmode) $k $j $E $k $j $T
            (index-rewrites (rec-indices $f) $m)
            $j
            $E $k $j $E $k $j
            "}"))
         (format-args "claim D{}: ({}_R {} {} -> {} {} :e {}_All /\\ IndIdx {} ({} {}) = {}_Ix {} {} {}) /\\ (~ {}_R {} {} -> {} {} :e {}_F {} {} {}).
{} apply andI.
  - assume Hr: {}_R {} {}. apply FalseE. exact {}_nR{}_{} Hr.
  - assume Hnr: ~ {}_R {} {}. {}exact In_eq_ls ({} {}) x{} ({}_F {} {} {}) T{} (In_eq_rs x{} ({}_F {} {} {}) {} ({}_F{}_{} {}) {}).
{}
"
           ($j $E $k $j $T $j $E (sig $E) $T $j $E $k $j $T $E $k $j $T $j $E $k $j $T
            "{" $E $k $j $E $k $j
            $E $k $j (guard-claim $f $params $j $m $tmode)
            $T $j $j $E $k $j $T $j
            $j $E $k $j $T (field-sort-mode $f $params $tmode) $E $k $j $T
            (if (is-guard $f) (format-args "G{}" ($j)) (format-args "H{}" ($j)))
            "}")))))

; A data field's sort with its fields read in $mode.
(= (field-sort-mode $f $params $mode)
   (case $f (((guard $p) (guard-sort $p $mode $params)) ($_ (field-sort $f $params)))))

; For a guard, the claim that x_j lies in its sort over the tuple: the
; tuple's fields are the variables (T_p), then H_j.
(= (guard-claim $f $params $j $m $tmode)
   (case $f
     (((guard $p)
       (format-args "claim G{}: x{} :e {}.
    {} {}exact H{}. {}
    " ($j $j (guard-sort $p $tmode $params) "{" (index-rewrites ($p) $m) $j "}")))
      ($_ ""))))

(= (rec-indices $f) (case $f (((rec $is) $is))))

; Rewrites T_p for every field p an index term reads.
(= (index-rewrites $is $m)
   (join "" (let $ps (distinct-fields (fields-read-list $is) ()) (map-atom $ps $p (format-args "rewrite T{}. " ($p))))))

; One rewrite replaces every occurrence of a field, including under binders.
(= (distinct-fields $xs $seen)
   (if (== $xs ()) ()
       (if (list-has (car-atom $xs) $seen) (distinct-fields (cdr-atom $xs) $seen)
           (cons-atom (car-atom $xs) (distinct-fields (cdr-atom $xs) (cons-atom (car-atom $xs) $seen))))))

(= (fields-read-list $is)
   (if (== $is ()) () (append-lists (fields-read (car-atom $is)) (fields-read-list (cdr-atom $is)))))

(= (fields-read $i)
   (case $i (((field $p) ($p)) ((const $c) ()) ((code $n) ()) ((bound $name) ())
            ((app $f $x) (append-lists (fields-read $f) (fields-read $x)))
            ((project $owner $field $record) (fields-read $record))
            ((pi $binder $domain $body) (append-lists (fields-read $domain) (fields-read $body))))))

(= (typed-text $E $C $cs $params $q $k $fs $m $S $T $tmode $rt)
   (let $c (nth $cs $k)
     (format-args "Theorem {}_typed : {}.
{}
{}claim L: {} :e IndFiber {} ({}_O {} {}).
{} exact IndNode_Fiber {} {}_bounded {} {} {}_ar{} {} ({}_args {}). {}
claim Lo: {}_O {} {} = {}.
{} prove SeqAt {} {} = {}. rewrite {}_O{} {}. {}reflexivity. {}
exact In_fam_eq (IndFiber {}) ({}_O {} {}) {} Lo ({}) L.
Qed.
"
       ($C (binders $E $q $fs $params 0 (format-args "{} :e {}" ((applied (format-args "{}_node" ($C)) $m) $rt)))
        (intros $E $q $fs $params 0)
        (tuple-claims $m $S)
        (applied (format-args "{}_node" ($C)) $m) (sig $E) $E $k $T
        "{" (sig $E) $E $k (inproof $k (length-of $cs)) $E $k $T $C (hyp-args $m) "}"
        $E $k $T (if (== $q 0) "0" (indices-text (ctor-result $c) x $params))
        "{" (os-seq-mode $cs $params $tmode) $k (if (== $q 0) "0" (indices-text (ctor-result $c) x $params))
        $E $k $T (index-rewrites (ctor-result $c) $m) "}"
        (sig $E) $E $k $T (if (== $q 0) "0" (indices-text (ctor-result $c) x $params))
        (applied (format-args "{}_node" ($C)) $m)))))

; The constructor as a Lean term, and its type.
(= (term-text $E $C $params $q $fs $m $rt)
   (if (== $m 0)
       (format-args "Definition {} : set := {}_node.
Theorem {}_type : {} :e {}.
exact {}_typed.
Qed.
" ($C $C $C $C $rt $C))
       (format-args "Definition {} : set := {}.
Theorem {}_type : {} :e {}.
exact {}.
Qed.
"
         ($C (lam-text $E $q $fs $params 0 (applied (format-args "{}_node" ($C)) $m))
          $C $C (pi-text $E $q $fs $params 0 $rt)
          (lam-proof $E $C $q $fs $params 0 $m $rt)))))

(= (lam-text $E $q $fs $params $j $body)
   (if (== $fs ()) $body
       (format-args "(fun x{} :e {} => {})" ($j (field-type $E $q (car-atom $fs) $params) (lam-text $E $q (cdr-atom $fs) $params (+ $j 1) $body)))))

(= (pi-text $E $q $fs $params $j $rt)
   (if (== $fs ()) $rt
       (format-args "(Pi_ x{} :e {}, {})" ($j (field-type $E $q (car-atom $fs) $params) (pi-text $E $q (cdr-atom $fs) $params (+ $j 1) $rt)))))

; lam_Pi, field by field, ending in the node's typing.
(= (lam-proof $E $C $q $fs $params $j $m $rt)
   (if (== $fs ()) (format-args "({}_typed {})" ($C (hyp-args $m)))
       (format-args "(lam_Pi {} (fun x{} => {}) (fun x{} => {}) (fun x{} H{} => {}))"
         ((field-type $E $q (car-atom $fs) $params)
          $j (pi-text $E $q (cdr-atom $fs) $params (+ $j 1) $rt)
          $j (lam-text $E $q (cdr-atom $fs) $params (+ $j 1) (applied (format-args "{}_node" ($C)) $m))
          $j $j (lam-proof $E $C $q (cdr-atom $fs) $params (+ $j 1) $m $rt)))))

; ---- the recursor ----

(= (hs-of $n) (let $is (range-from 0 $n) (map-atom $is $i (format-args "h{}" ($i)))))

; Recursive positions of a constructor.
(= (rec-positions $fs $j)
   (if (== $fs ()) ()
       (let $rest (rec-positions (cdr-atom $fs) (+ $j 1))
         (if (is-rec (car-atom $fs)) (cons-atom $j $rest) $rest))))

; Lean's minor premise k applied to the fields, then the recursive results.
(= (method-app $k $fs $field $result)
   (let* (($js (range-from 0 (length-of $fs)))
          ($ps (rec-positions $fs 0))
          ($args (append-lists (map-atom $js $j (format-args $field ($j)))
                               (map-atom $ps $p (format-args $result ($p))))))
     (if (== $args ()) (format-args "h{}" ($k))
         (format-args "(h{} {})" ($k (join " " $args))))))

(= (methods-seq $cs $field $result)
   (let $ks (range-from 0 (length-of $cs))
     (seq (map-atom $ks $k (method-app $k (ctor-fields (nth $cs $k)) $field $result)))))

(= (method-fun $cs) (format-args "(fun k a r:set => SeqAt {} k)" ((methods-seq $cs "(a {})" "(r {})"))))

(= (rec-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($ks (range-from 0 $n)))
     (format-args "Definition {}_rec : {} := fun {} t => IndRec {} {} t.
{}"
       ($E (node-type (+ $n 1)) $hs (sig $E) (method-fun $cs)
        (join "" (map-atom $ks $k (iota-text $name $cs $params $q $k)))))))

(= (iota-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($S (tuple-of $m))
          ($T (format-args "(TupArgs {} {})" ($m $S)))
          ($M (method-fun $cs))
          ($recs (format-args "(IndRes {} {} (fun j => IndRec {} {} ({} j)))" ((sig $E) $k (sig $E) $M $T)))
          ($ps (rec-positions $fs 0))
          ($rhs (method-app $k $fs "x{}" (format-args "({}_rec {} x{})" ($E $hs "{}"))))
          ($node (applied (format-args "{}_node" ($C)) $m)))
     (format-args "Theorem {}_iota{} : forall {}, {}.
let {}. {}
{}{}prove IndRec {} {} (IndNode {} {} {}) = {}.
rewrite IndRec_iota {} {}_distinct {}_bounded {}_arity {} {} {} {} ({}_args {}).
prove SeqAt {} {} = {}.
{}
Qed.
"
       ($E $k $hs (binders $E $q $fs $params 0 (format-args "{}_rec {} ({}) = {}" ($E $hs $node $rhs)))
        $hs (intros $E $q $fs $params 0)
        (tuple-claims $m $S)
        (join "" (map-atom $ps $p
           (format-args "claim R{}: {} {} = {}_rec {} x{}.
{} rewrite IndRes_at {} {} (fun j => IndRec {} {} ({} j)) {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{}. prove IndRec {} {} ({} {}) = IndRec {} {} x{}. rewrite T{}. reflexivity. {}
" ($p $recs $p $E $hs $p
   "{" (sig $E) $k (sig $E) $M $T $p $p $E $k $m $E $k (inproof $p $m) $E $k $p
   (sig $E) $M $T $p (sig $E) $M $p $p "}"))))
        (sig $E) $M (sig $E) $k $T $rhs
        (sig $E) $E $E $E $M $k (inproof $k $n) $T $C (hyp-args $m)
        (methods-seq $cs (format-args "({} {})" ($T "{}")) (format-args "({} {})" ($recs "{}"))) $k $rhs
        (lookup $k (format-args "{}{}reflexivity."
                     ((join "" (map-atom $ps $p (format-args "rewrite R{}. " ($p))))
                      (join "" (let $js (range-from 0 $m) (map-atom $js $j (format-args "rewrite T{}. " ($j))))))))))))

; ---- the recursor's dependent typing ----

; Types with fields below j0 read from the tuple a, the others bound as x.
(= (field-type-m $E $q $f $params $j0)
   (case $f
     (((data $t) (sort-text $t $params))
      ((guard $p) (guard-sort $p (mixed $j0) $params))
      ((rec $is) (fam-app $E $q $is (mixed $j0) $params)))))

(= (mode-args $m $j0) (let $is (range-from 0 $m) (join " " (map-atom $is $i (index-text (field $i) (mixed $j0) ())))))

(= (node-m $C $m $j0) (if (== $m 0) (format-args "{}_node" ($C)) (format-args "({}_node {})" ($C (mode-args $m $j0)))))

; The motive at a field's index, applied to a value.
(= (motive-at $q $is $value $mode $params)
   (if (== $q 0) (format-args "(C {})" ($value))
       (if (== $q 1) (format-args "(C {} {})" ((indices-text $is $mode $params) $value))
           (format-args "(C {} {})" ((join " " (map-atom $is $i (index-text $i $mode $params))) $value)))))

(= (motive-result $q $c $C $m $j0 $params)
   (motive-at $q (ctor-result $c) (node-m $C $m $j0) (mixed $j0) $params))

; Pi binders for fields j.., then the IHs from position t of the recursive positions, then the result.
(= (pi-chain $E $q $c $C $params $j $t $j0)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)))
     (if (< $j $m)
         (format-args "(Pi_ x{} :e {}, {})"
           ($j (field-type-m $E $q (nth $fs $j) $params $j0) (pi-chain $E $q $c $C $params (+ $j 1) $t $j0)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (format-args "(Pi_ y{} :e {}, {})"
                 ($p (motive-at $q (rec-indices (nth $fs $p)) (index-text (field $p) (mixed $j0) ()) (mixed $j0) $params)
                  (pi-chain $E $q $c $C $params $j (+ $t 1) $j0))))
             (motive-result $q $c $C $m $j0 $params)))))

(= (method-type $E $q $c $C $params) (pi-chain $E $q $c $C $params 0 0 0))

; ap_Pi steps: fields first, then the recursive results.
(= (apply-chain $E $q $c $C $params $j $t $acc $prev)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)))
     (if (< $j $m)
         (apply-chain $E $q $c $C $params (+ $j 1) $t
           (format-args "({} (a {}))" ($acc $j))
           (format-args "(ap_Pi {} (fun x{} => {}) {} (a {}) {} G{})"
             ((field-type-m $E $q (nth $fs $j) $params $j) $j (pi-chain $E $q $c $C $params (+ $j 1) $t $j) $acc $j $prev $j)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (apply-chain $E $q $c $C $params $j (+ $t 1)
                 (format-args "({} (r {}))" ($acc $p))
                 (format-args "(ap_Pi {} (fun y{} => {}) {} (r {}) {} Y{})"
                   ((motive-at $q (rec-indices (nth $fs $p)) (format-args "(a {})" ($p)) (mixed $m) $params)
                    $p (pi-chain $E $q $c $C $params $j (+ $t 1) $m) $acc $p $prev $p))))
             $prev))))

(= (applied-method $k $c)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0))
          ($js (range-from 0 $m))
          ($args (append-lists (map-atom $js $j (format-args "(a {})" ($j))) (map-atom $ps $p (format-args "(r {})" ($p))))))
     (if (== $args ()) (format-args "h{}" ($k)) (format-args "(h{} {})" ($k (join " " $args))))))


(= (hm-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($ps (rec-positions $fs 0))
          ($js (range-from 0 $m))
          ($M (method-fun $cs))
          ($Cty (motive-ty $q))
          ($Cp (cprime-text $q $E))
          ($Sa (seq (map-atom $js $j (format-args "(a {})" ($j)))))
          ($am (applied-method $k $c))
          ($ridx (if (== $q 0) "0" (indices-text (ctor-result $c) a $params)))
          ($nodeA (node-m $C $m $m)))
     (format-args "Theorem {}_HM{} : forall C:{}, forall {}, h{} :e {} -> forall a :e IndArgs {} {}_All {}, forall r:set -> set, (forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j)) -> {} {} a (IndRes {} {} r) :e {} (IndNode {} {} a).
let C {}. assume Hh: h{} :e {}.
let a. assume Ha: a :e IndArgs {} {}_All {}. let r. assume Hr: forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j).
claim Fi: IndFits {} {}_All {} a.
{ exact IndArgs_Fits {} {}_All {} a Ha. }
claim Pm: a :e Pi_ j :e {}, {}_B :\\/: {}_All.
{ exact In_fam_eq (fun X:set => Pi_ j :e X, {}_B :\\/: {}_All) ({}_N {}) {} {}_N{} a (IndArgs_Pi {} {}_All {} a Ha). }
{}{}claim Ea: TupArgs {} {} = a.
{ exact eq_i_tra (TupArgs {} {}) (fun j :e {} => a j) a (lam_ext {} (fun j => SeqAt {} j) (fun j => a j) {}) (Pi_eta {} (fun j => {}_B :\\/: {}_All) a Pm). }
{}claim Lv: {} :e {}.
{ exact {}. }
claim Lm: {} {} a (IndRes {} {} r) = {}.
{ prove SeqAt {} {} = {}. {} }
claim Ln: {} = IndNode {} {} a.
{ prove IndNode {} {} (TupArgs {} {}) = IndNode {} {} a. rewrite Ea. reflexivity. }
{}
Qed.
"
       ($E $k $Cty $hs $k (method-type $E $q $c $C $params) (sig $E) $E $k $E $k $E $k $Cp $M $k (sig $E) $k $Cp (sig $E) $k
        $hs $k (method-type $E $q $c $C $params)
        (sig $E) $E $k $E $k $E $k $Cp
        (sig $E) $E $k (sig $E) $E $k
        $m $E $E $E $E $E $k $m $E $k (sig $E) $E $k
        (join "" (map-atom $js $j (hm-field-claim $E $q $c $params $k $j $m)))
        (join "" (map-atom $js $j (format-args "claim U{}: SeqAt {} {} = (a {}).
{} {} {}
" ($j $Sa $j $j "{" (lookup $j "reflexivity.") "}"))))
        $m $Sa $m $Sa $m $m $Sa (below $m (format-args "(fun j => SeqAt {} j = a j)" ($Sa)) (map-atom $js $j (format-args "U{}" ($j)))) $m $E $E
        (join "" (map-atom $ps $p (format-args "claim Rp{}: IndRes {} {} r {} = r {}.
{} exact IndRes_at {} {} r {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{}. {}
" ($p (sig $E) $k $p $p "{" (sig $E) $k $p $p $E $k $m $E $k (inproof $p $m) $E $k $p "}"))))
        $am (motive-result $q $c $C $m $m $params)
        (if (== $m 0) "Hh" (if (== (length-of $ps) 0) (apply-chain $E $q $c $C $params 0 0 (format-args "h{}" ($k)) "Hh") (apply-chain $E $q $c $C $params 0 0 (format-args "h{}" ($k)) "Hh")))
        $M $k (sig $E) $k $am
        (methods-seq $cs "(a {})" (format-args "(IndRes {} {} r {})" ((sig $E) $k "{}"))) $k $am
        (lookup $k (format-args "{}reflexivity." ((join "" (map-atom $ps $p (format-args "rewrite Rp{}. " ($p)))))))
        $nodeA (sig $E) $k
        (sig $E) $k $m $Sa (sig $E) $k
        (hm-final $E $q $c $C $params $k $m $M $am $ridx $nodeA)))))

(= (hm-rec-evidence $E $q $f $params $k $j $m $idx)
   (let $ih (format-args "Hr {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{}"
              ($j $j $E $k $m $E $k (inproof $j $m) $E $k $j))
     (if (== $q 0) $ih
       (let $transport (format-args "In_fam_eq (fun z:set => C {} (a {})) (IndIdx {} (a {})) {} (SepE2 {}_All (fun x:set => IndIdx {} x = {}) (a {}) G{}) (r {}) ({})"
              ((if (== $q 1) "z" (join " " (proj-texts $q z))) $j (sig $E) $j $idx
               $E (sig $E) $idx $j $j $j $ih))
         (if (== $q 1) $transport
             (format-args "{} C {} (a {}) (r {}) ({})"
               ((motive-unpair $q) (join " " (map-atom (rec-indices $f) $i (index-text $i a $params)))
                $j $j $transport)))))))

(= (hm-field-claim $E $q $c $params $k $j $m)
   (let $f (nth (ctor-fields $c) $j)
     (if (is-rec $f)
         (let $idx (if (== $q 0) "0" (indices-text (rec-indices $f) a $params))
           (format-args "claim G{}: (a {}) :e {}.
{} apply Fi {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}). assume H1. assume H2. apply H1 {}_R{}_{}. assume H3: a {} :e {}_All. assume H4: IndIdx {} (a {}) = {}_Ix {} {} a.
  prove (a {}) :e {}x :e {}_All | IndIdx {} x = {}{}.
  apply SepI {}_All (fun x:set => IndIdx {} x = {}) (a {}) H3.
  exact eq_i_tra (IndIdx {} (a {})) ({}_Ix {} {} a) {} H4 ({}_Ix{}_{} a). {}
claim Y{}: r {} :e {}.
{} exact {}. {}
"
             ($j $j (field-type-m $E $q $f $params $m)
              "{" $j $j $E $k $m $E $k (inproof $j $m) $E $k $j $j $E (sig $E) $j $E $k $j
              $j "{" $E (sig $E) $idx "}"
              $E (sig $E) $idx $j
              (sig $E) $j $E $k $j $idx $E $k $j "}"
              $j $j (motive-at $q (rec-indices $f) (format-args "(a {})" ($j)) a $params)
              "{"
              (hm-rec-evidence $E $q $f $params $k $j $m $idx)
              "}")))
         (format-args "claim G{}: (a {}) :e {}.
{} apply Fi {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}). assume H1. assume H2. exact In_eq_r (a {}) ({}_F {} {} a) {} ({}_F{}_{} a) (H2 {}_nR{}_{}). {}
"
           ($j $j (field-sort $f $params)
            "{" $j $j $E $k $m $E $k (inproof $j $m) $j $E $k $j (field-sort $f $params) $E $k $j $E $k $j "}")))))

(= (hm-final $E $q $c $C $params $k $m $M $am $ridx $nodeA)
   (if (>= $q 2) (hm-final-n $E $q $c $C $params $k $m $M $am $ridx $nodeA)
   (if (== $q 0)
       (format-args "exact In_eq_ls ({} {} a (IndRes {} {} r)) {} (C (IndNode {} {} a)) Lm (In_fam_eq (fun z:set => C z) {} (IndNode {} {} a) Ln {} Lv)."
         ($M $k (sig $E) $k $am (sig $E) $k $nodeA (sig $E) $k $am))
       (format-args "claim Lo: {} = IndIdx {} (IndNode {} {} a).
{} exact eq_i_tra {} ({}_O {} a) (IndIdx {} (IndNode {} {} a)) (eq_sym_i ({}_O {} a) {} ({}_O{} a)) (eq_sym_i (IndIdx {} (IndNode {} {} a)) ({}_O {} a) (IndIdx_Node {} {} a)). {}
exact In_eq_ls ({} {} a (IndRes {} {} r)) {} (C (IndIdx {} (IndNode {} {} a)) (IndNode {} {} a)) Lm (In_fam_eq (fun z:set => C z (IndNode {} {} a)) {} (IndIdx {} (IndNode {} {} a)) Lo {} (In_fam_eq (fun z:set => C {} z) {} (IndNode {} {} a) Ln {} Lv))."
         ($ridx (sig $E) (sig $E) $k
          "{" $ridx $E $k (sig $E) (sig $E) $k $E $k $ridx $E $k (sig $E) (sig $E) $k $E $k (sig $E) $k "}"
          $M $k (sig $E) $k $am (sig $E) (sig $E) $k (sig $E) $k
          (sig $E) $k $ridx (sig $E) (sig $E) $k $am $ridx $nodeA (sig $E) $k $am)))))

; A family with several indices: the method's value at the indices, moved to
; the projections of the node's index.
(= (hm-final-n $E $q $c $C $params $k $m $M $am $ridx $nodeA)
   (let* (($node (format-args "(IndNode {} {} a)" ((sig $E) $k)))
          ($is (join " " (map-atom (ctor-result $c) $i (index-text $i a $params))))
          ($ps (join " " (proj-texts $q (format-args "(IndIdx {} {})" ((sig $E) $node)))))
          ($pz (join " " (proj-texts $q z))))
     (format-args "claim Lo: {} = IndIdx {} {}.
{} exact eq_i_tra {} ({}_O {} a) (IndIdx {} {}) (eq_sym_i ({}_O {} a) {} ({}_O{} a)) (eq_sym_i (IndIdx {} {}) ({}_O {} a) (IndIdx_Node {} {} a)). {}
exact In_eq_ls ({} {} a (IndRes {} {} r)) {} (C {} {}) Lm
  (In_fam_eq (fun z:set => C {} {}) {} (IndIdx {} {}) Lo {}
    ({} C {} {} {} (In_fam_eq (fun z:set => C {} z) {} {} Ln {} Lv)))."
       ($ridx (sig $E) $node
        "{" $ridx $E $k (sig $E) $node $E $k $ridx $E $k (sig $E) $node $E $k (sig $E) $k "}"
        $M $k (sig $E) $k $am $ps $node
        $pz $node $ridx (sig $E) $node $am
        (motive-pair $q) $is $node $am $is $nodeA $node $am))))

(= (rec-type-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($ks (range-from 0 $n))
          ($Cty (motive-ty $q))
          ($Cp (cprime-text $q $E))
          ($M (method-fun $cs))
          ($hyps (join " " (map-atom $ks $k (format-args "forall h{} :e {}," ($k (method-type $E $q (nth $cs $k) (egal (ctor-name (nth $cs $k))) $params))))))
          ($HM (format-args "(fun k => forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a))"
                 ((sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E)))))
     (format-args "{}Theorem {}_rec_type : forall C:{}, {} {}.
let C. {}{}
claim HM: forall k :e {}_K, forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a).
{ let k. assume Hk: k :e {}_K. exact {} k Hk. }
{}
Qed.
"
       ((join "" (map-atom $ks $k (hm-text $name $cs $params $q $k)))
        $E $Cty $hyps
        (if (== $q 0) (format-args "forall t :e {}, {}_rec {} t :e C t" ($E $E $hs))
            (if (== $q 1) (format-args "forall i, forall t :e {} i, {}_rec {} t :e C i t" ($E $E $hs))
                (let $is (join " " (ivar-list $q i))
                  (format-args "forall {}, forall t :e {} {}, {}_rec {} t :e C {} t" ($is $E $is $E $hs $is)))))
        "" (join " " (map-atom $ks $k (format-args "let h{}. assume Hh{}." ($k $k))))
        $E (sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E)
        $E (below $n $HM (map-atom $ks $k (format-args "({}_HM{} C {} Hh{})" ($E $k $hs $k))))
        (if (== $q 0)
            (format-args "let t. assume Ht: t :e {}.
exact IndRec_type {} {}_distinct {}_bounded {}_arity {} C HM t (SepE1 {}_All (fun x:set => IndIdx {} x = 0) t Ht)."
              ($E (sig $E) $E $E $E $M $E (sig $E)))
            (if (== $q 1)
            (format-args "let i t. assume Ht: t :e {} i.
exact In_fam_eq (fun z:set => C z t) (IndIdx {} t) i (SepE2 {}_All (fun x:set => IndIdx {} x = i) t Ht) ({}_rec {} t) (IndRec_type {} {}_distinct {}_bounded {}_arity {} {} HM t (SepE1 {}_All (fun x:set => IndIdx {} x = i) t Ht))."
              ($E (sig $E) $E (sig $E) $E $hs (sig $E) $E $E $E $M $Cp $E (sig $E)))
            (let* (($iv (ivar-list $q i)) ($is (join " " $iv)) ($tu (tuple-text $iv)))
            (format-args "let {} t. assume Ht: t :e {} {}.
exact {} C {} t ({}_rec {} t) (In_fam_eq (fun z:set => C {} t) (IndIdx {} t) {} (SepE2 {}_All (fun x:set => IndIdx {} x = {}) t Ht) ({}_rec {} t)
  (IndRec_type {} {}_distinct {}_bounded {}_arity {} {} HM t (SepE1 {}_All (fun x:set => IndIdx {} x = {}) t Ht)))."
              ($is $E $is (motive-unpair $q) $is $E $hs (join " " (proj-texts $q z)) (sig $E) $tu $E (sig $E) $tu $E $hs
               (sig $E) $E $E $E $M $Cp $E (sig $E) $tu)))))))))


; ---- the case analysis: the eliminator with no induction hypotheses ----
; Lean's casesOn of a family with recursive fields, read as its own
; eliminator: each minor premise takes the constructor's fields only.

(= (method-app-c $k $fs $field)
   (let* (($js (range-from 0 (length-of $fs))) ($args (map-atom $js $j (format-args $field ($j)))))
     (if (== $args ()) (format-args "h{}" ($k)) (format-args "(h{} {})" ($k (join " " $args))))))
(= (methods-seq-c $cs $field)
   (let $ks (range-from 0 (length-of $cs))
     (seq (map-atom $ks $k (method-app-c $k (ctor-fields (nth $cs $k)) $field)))))
(= (method-fun-c $cs) (format-args "(fun k a r:set => SeqAt {} k)" ((methods-seq-c $cs "(a {})"))))
(= (applied-method-c $k $c) (method-app-c $k (ctor-fields $c) "(a {})"))
(= (method-type-c $E $q $c $C $params) (pi-chain $E $q $c $C $params 0 (length-of (rec-positions (ctor-fields $c) 0)) 0))
(= (has-rec-field $cs)
   (if (== $cs ()) False (if (== (rec-positions (ctor-fields (car-atom $cs)) 0) ()) (has-rec-field (cdr-atom $cs)) True)))
(= (has-cases-eliminator $name)
   (if (== (index-count $name) 0) (if (is-prop $name) False (has-rec-field (constructors-of $name))) False))

(= (cases-text $name $cs $params $q)
   (let* (($E (egal $name)) ($n (length-of $cs)) ($hs (join " " (hs-of $n))) ($ks (range-from 0 $n)))
     (format-args "Definition {}_casesOn : {} := fun {} t => IndRec {} {} t.
{}"
       ($E (node-type (+ $n 1)) $hs (sig $E) (method-fun-c $cs)
        (join "" (map-atom $ks $k (cases-iota-text $name $cs $params $q $k)))))))

(= (cases-iota-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($S (tuple-of $m))
          ($T (format-args "(TupArgs {} {})" ($m $S)))
          ($M (method-fun-c $cs))
          ($recs (format-args "(IndRes {} {} (fun j => IndRec {} {} ({} j)))" ((sig $E) $k (sig $E) $M $T)))
          ($ps (rec-positions $fs 0))
          ($rhs (method-app-c $k $fs "x{}"))
          ($node (applied (format-args "{}_node" ($C)) $m)))
     (format-args "Theorem {}_casesOn_iota{} : forall {}, {}.
let {}. {}
{}{}prove IndRec {} {} (IndNode {} {} {}) = {}.
rewrite IndRec_iota {} {}_distinct {}_bounded {}_arity {} {} {} {} ({}_args {}).
prove SeqAt {} {} = {}.
{}
Qed.
"
       ($E $k $hs (binders $E $q $fs $params 0 (format-args "{}_casesOn {} ({}) = {}" ($E $hs $node $rhs)))
        $hs (intros $E $q $fs $params 0)
        (tuple-claims $m $S)
        ""
        (sig $E) $M (sig $E) $k $T $rhs
        (sig $E) $E $E $E $M $k (inproof $k $n) $T $C (hyp-args $m)
        (methods-seq-c $cs (format-args "({} {})" ($T "{}"))) $k $rhs
        (lookup $k (format-args "{}{}reflexivity."
                     (""
                      (join "" (let $js (range-from 0 $m) (map-atom $js $j (format-args "rewrite T{}. " ($j))))))))))))

(= (hm-c-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($ps (rec-positions $fs 0))
          ($js (range-from 0 $m))
          ($M (method-fun-c $cs))
          ($Cty (motive-ty $q))
          ($Cp (cprime-text $q $E))
          ($Sa (seq (map-atom $js $j (format-args "(a {})" ($j)))))
          ($am (applied-method-c $k $c))
          ($ridx (if (== $q 0) "0" (indices-text (ctor-result $c) a $params)))
          ($nodeA (node-m $C $m $m)))
     (format-args "Theorem {}_casesOn_HM{} : forall C:{}, forall {}, h{} :e {} -> forall a :e IndArgs {} {}_All {}, forall r:set -> set, (forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j)) -> {} {} a (IndRes {} {} r) :e {} (IndNode {} {} a).
let C {}. assume Hh: h{} :e {}.
let a. assume Ha: a :e IndArgs {} {}_All {}. let r. assume Hr: forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j).
claim Fi: IndFits {} {}_All {} a.
{ exact IndArgs_Fits {} {}_All {} a Ha. }
claim Pm: a :e Pi_ j :e {}, {}_B :\\/: {}_All.
{ exact In_fam_eq (fun X:set => Pi_ j :e X, {}_B :\\/: {}_All) ({}_N {}) {} {}_N{} a (IndArgs_Pi {} {}_All {} a Ha). }
{}{}claim Ea: TupArgs {} {} = a.
{ exact eq_i_tra (TupArgs {} {}) (fun j :e {} => a j) a (lam_ext {} (fun j => SeqAt {} j) (fun j => a j) {}) (Pi_eta {} (fun j => {}_B :\\/: {}_All) a Pm). }
{}claim Lv: {} :e {}.
{ exact {}. }
claim Lm: {} {} a (IndRes {} {} r) = {}.
{ prove SeqAt {} {} = {}. {} }
claim Ln: {} = IndNode {} {} a.
{ prove IndNode {} {} (TupArgs {} {}) = IndNode {} {} a. rewrite Ea. reflexivity. }
{}
Qed.
"
       ($E $k $Cty $hs $k (method-type-c $E $q $c $C $params) (sig $E) $E $k $E $k $E $k $Cp $M $k (sig $E) $k $Cp (sig $E) $k
        $hs $k (method-type-c $E $q $c $C $params)
        (sig $E) $E $k $E $k $E $k $Cp
        (sig $E) $E $k (sig $E) $E $k
        $m $E $E $E $E $E $k $m $E $k (sig $E) $E $k
        (join "" (map-atom $js $j (hm-field-claim $E $q $c $params $k $j $m)))
        (join "" (map-atom $js $j (format-args "claim U{}: SeqAt {} {} = (a {}).
{} {} {}
" ($j $Sa $j $j "{" (lookup $j "reflexivity.") "}"))))
        $m $Sa $m $Sa $m $m $Sa (below $m (format-args "(fun j => SeqAt {} j = a j)" ($Sa)) (map-atom $js $j (format-args "U{}" ($j)))) $m $E $E
        ""
        $am (motive-result $q $c $C $m $m $params)
        (if (== $m 0) "Hh" (if (== (length-of $ps) 0) (apply-chain $E $q $c $C $params 0 (length-of $ps) (format-args "h{}" ($k)) "Hh") (apply-chain $E $q $c $C $params 0 (length-of $ps) (format-args "h{}" ($k)) "Hh")))
        $M $k (sig $E) $k $am
        (methods-seq-c $cs "(a {})") $k $am
        (lookup $k "reflexivity.")
        $nodeA (sig $E) $k
        (sig $E) $k $m $Sa (sig $E) $k
        (hm-final $E $q $c $C $params $k $m $M $am $ridx $nodeA)))))

(= (cases-type-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($ks (range-from 0 $n))
          ($Cty (motive-ty $q))
          ($Cp (cprime-text $q $E))
          ($M (method-fun-c $cs))
          ($hyps (join " " (map-atom $ks $k (format-args "forall h{} :e {}," ($k (method-type-c $E $q (nth $cs $k) (egal (ctor-name (nth $cs $k))) $params))))))
          ($HM (format-args "(fun k => forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a))"
                 ((sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E)))))
     (format-args "{}Theorem {}_casesOn_type : forall C:{}, {} {}.
let C. {}{}
claim HM: forall k :e {}_K, forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a).
{ let k. assume Hk: k :e {}_K. exact {} k Hk. }
{}
Qed.
"
       ((join "" (map-atom $ks $k (hm-c-text $name $cs $params $q $k)))
        $E $Cty $hyps
        (if (== $q 0) (format-args "forall t :e {}, {}_casesOn {} t :e C t" ($E $E $hs))
            (format-args "forall i, forall t :e {} i, {}_rec {} t :e C i t" ($E $E $hs)))
        "" (join " " (map-atom $ks $k (format-args "let h{}. assume Hh{}." ($k $k))))
        $E (sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E)
        $E (below $n $HM (map-atom $ks $k (format-args "({}_casesOn_HM{} C {} Hh{})" ($E $k $hs $k))))
        (if (== $q 0)
            (format-args "let t. assume Ht: t :e {}.
exact IndRec_type {} {}_distinct {}_bounded {}_arity {} C HM t (SepE1 {}_All (fun x:set => IndIdx {} x = 0) t Ht)."
              ($E (sig $E) $E $E $E $M $E (sig $E)))
            (if (== $q 1)
            (format-args "let i t. assume Ht: t :e {} i.
exact In_fam_eq (fun z:set => C z t) (IndIdx {} t) i (SepE2 {}_All (fun x:set => IndIdx {} x = i) t Ht) ({}_rec {} t) (IndRec_type {} {}_distinct {}_bounded {}_arity {} {} HM t (SepE1 {}_All (fun x:set => IndIdx {} x = i) t Ht))."
              ($E (sig $E) $E (sig $E) $E $hs (sig $E) $E $E $E $M $Cp $E (sig $E)))
            (let* (($iv (ivar-list $q i)) ($is (join " " $iv)) ($tu (tuple-text $iv)))
            (format-args "let {} t. assume Ht: t :e {} {}.
exact {} C {} t ({}_rec {} t) (In_fam_eq (fun z:set => C {} t) (IndIdx {} t) {} (SepE2 {}_All (fun x:set => IndIdx {} x = {}) t Ht) ({}_rec {} t)
  (IndRec_type {} {}_distinct {}_bounded {}_arity {} {} HM t (SepE1 {}_All (fun x:set => IndIdx {} x = {}) t Ht)))."
              ($is $E $is (motive-unpair $q) $is $E $hs (join " " (proj-texts $q z)) (sig $E) $tu $E (sig $E) $tu $E $hs
               (sig $E) $E $E $E $M $Cp $E (sig $E) $tu)))))))))

; ---- induction ----
; P holds of every element when it holds of each constructor's node, given it
; holds of the recursive fields: the recursor's typing at the motive
; {z :e 1 | P t}, whose methods are all 0.

(= (pred-at $v) (format-args "{}z :e 1 | P {}{}" ("{" $v "}")))

; The method type of a constructor at that motive, from field j and recursive
; result t on.
(= (ind-chain $E $c $params $j $t)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)) ($C (egal (ctor-name $c))))
     (if (< $j $m)
         (format-args "(Pi_ x{} :e {}, {})" ($j (field-type-m $E 0 (nth $fs $j) $params 0) (ind-chain $E $c $params (+ $j 1) $t)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (format-args "(Pi_ y{} :e {}, {})" ($p (pred-at (format-args "x{}" ($p))) (ind-chain $E $c $params $j (+ $t 1)))))
             (pred-at (node-m $C $m 0))))))

; The hypothesis for a constructor: forall fields, P of each recursive field, P of the node.
(= (ind-hyp $E $c $params)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)) ($C (egal (ctor-name $c)))
          ($binders (join "" (let $js (range-from 0 $m) (map-atom $js $j (format-args "forall x{} :e {}, " ($j (field-type-m $E 0 (nth $fs $j) $params 0)))))))
          ($ihs (join "" (map-atom $ps $p (format-args "P x{} -> " ($p))))))
     (format-args "({}{}P {})" ($binders $ihs (node-m $C $m 0)))))

; The proof that 0 lies in that method type.
(= (ind-method $E $c $params $k)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)) ($node (node-m (egal (ctor-name $c)) $m 0))
          ($args (join "" (let $js (range-from 0 $m) (map-atom $js $j (format-args " x{} Hx{}" ($j $j))))))
          ($ihs (join "" (map-atom $ps $p (format-args " (SepE2 1 (fun z => P x{}) y{} Hy{})" ($p $p $p))))))
     (format-args "claim M{}: 0 :e {}.
{ {}{}exact SepI 1 (fun z => P {}) 0 In_0_1 (H{}{}{}). }
"
       ($k (ind-chain $E $c $params 0 0)
        (join "" (let $js (range-from 0 $m) (map-atom $js $j
          (format-args "apply Pi_0_In. let x{}. assume Hx{}: x{} :e {}.
  prove 0 :e {}.
  " ($j $j $j (field-type-m $E 0 (nth $fs $j) $params 0) (ind-chain $E $c $params (+ $j 1) 0))))))
        (join "" (let $ts (range-from 0 (length-of $ps)) (map-atom $ts $t
          (let $p (nth $ps $t)
            (format-args "apply Pi_0_In. let y{}. assume Hy{}: y{} :e {}.
  prove 0 :e {}.
  " ($p $p $p (pred-at (format-args "x{}" ($p))) (ind-chain $E $c $params $m (+ $t 1))))))))
        $node $k $args $ihs))))

(= (ind-text $name $cs $params)
   (let* (($E (egal $name)) ($n (length-of $cs)) ($ks (range-from 0 $n)))
     (format-args "Theorem {}_ind : forall P:set -> prop, {}forall t :e {}, P t.
let P.{}
{}let t. assume Ht: t :e {}.
exact SepE2 1 (fun z => P t) ({}_rec{} t) ({}_rec_type (fun t => {}z :e 1 | P t{}){} t Ht).
Qed.

"
       ($E (join "" (map-atom $ks $k (format-args "{} -> " ((ind-hyp $E (nth $cs $k) $params))))) $E
        (join "" (map-atom $ks $k (format-args " assume H{}." ($k))))
        (join "" (map-atom $ks $k (ind-method $E (nth $cs $k) $params $k)))
        $E $E (join "" (map-atom $ks $k " 0")) $E "{" "}" (join "" (map-atom $ks $k (format-args " 0 M{}" ($k))))))))

; ---- no confusion, and one index per value ----

; Native logical induction on an indexed evidence fiber. The public
; proposition may have several indices; the carrier stores their tuple.
(= (indexed-pred $is $value $params)
   (format-args "P {} {}" ((indices-text $is x $params) $value)))
(= (indexed-pred-set $is $value $params)
   (format-args "{}z :e 1 | {}{}" ("{" (indexed-pred $is $value $params) "}")))
(= (indexed-ind-chain $E $c $params $j $t)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0))
          ($C (egal (ctor-name $c))))
     (if (< $j $m)
         (format-args "(Pi_ x{} :e {}, {})"
           ($j (field-type-m $E 1 (nth $fs $j) $params 0)
            (indexed-ind-chain $E $c $params (+ $j 1) $t)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (format-args "(Pi_ y{} :e {}, {})"
                 ($p (indexed-pred-set (rec-indices (nth $fs $p)) (format-args "x{}" ($p)) $params)
                  (indexed-ind-chain $E $c $params $j (+ $t 1)))))
             (indexed-pred-set (ctor-result $c) (node-m $C $m 0) $params)))))
(= (indexed-ind-hyp $E $c $params)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0))
          ($binders (join "" (map-atom (range-from 0 $m) $j
             (format-args "forall x{} :e {}, " ($j (field-type-m $E 1 (nth $fs $j) $params 0))))))
          ($ihs (join "" (map-atom $ps $p (format-args "{} -> "
             ((indexed-pred (rec-indices (nth $fs $p)) (format-args "x{}" ($p)) $params)))))))
     (format-args "({}{}{})" ($binders $ihs
       (indexed-pred (ctor-result $c) (node-m (egal (ctor-name $c)) $m 0) $params)))))
(= (indexed-ind-method $E $c $params $k)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0))
          ($args (join "" (map-atom (range-from 0 $m) $j (format-args " x{} Hx{}" ($j $j)))))
          ($ihs (join "" (map-atom $ps $p (format-args " (SepE2 1 (fun z => {}) y{} Hy{})"
             ((indexed-pred (rec-indices (nth $fs $p)) (format-args "x{}" ($p)) $params) $p $p))))))
     (format-args "claim M{}: 0 :e {}.\n{ {}{}exact SepI 1 (fun z => {}) 0 In_0_1 (H{}{}{}). }\n"
       ($k (indexed-ind-chain $E $c $params 0 0)
        (join "" (map-atom (range-from 0 $m) $j
          (format-args "apply Pi_0_In. let x{}. assume Hx{}: x{} :e {}.\n  prove 0 :e {}.\n"
            ($j $j $j (field-type-m $E 1 (nth $fs $j) $params 0)
             (indexed-ind-chain $E $c $params (+ $j 1) 0)))))
        (join "" (map-atom (range-from 0 (length-of $ps)) $t
          (let $p (nth $ps $t)
            (format-args "apply Pi_0_In. let y{}. assume Hy{}: y{} :e {}.\n  prove 0 :e {}.\n"
              ($p $p $p (indexed-pred-set (rec-indices (nth $fs $p)) (format-args "x{}" ($p)) $params)
               (indexed-ind-chain $E $c $params $m (+ $t 1)))))))
        (indexed-pred (ctor-result $c) (node-m (egal (ctor-name $c)) $m 0) $params)
        $k $args $ihs))))
(= (indexed-ind-text $name $cs $params)
   (let* (($E (egal $name)) ($ks (range-from 0 (length-of $cs))))
     (format-args "Theorem {}_ind : forall P:set -> set -> prop, {}forall i, forall t :e {} i, P i t.\nlet P.{}\n{}let i t. assume Ht: t :e {} i.\nexact SepE2 1 (fun z => P i t) ({}_rec{} t) ({}_rec_type (fun i t => {}z :e 1 | P i t{}){} i t Ht).\nQed.\n"
       ($E (join "" (map-atom $ks $k (format-args "{} -> " ((indexed-ind-hyp $E (nth $cs $k) $params))))) $E
        (join "" (map-atom $ks $k (format-args " assume H{}." ($k))))
        (join "" (map-atom $ks $k (indexed-ind-method $E (nth $cs $k) $params $k)))
        $E $E (join "" (map-atom $ks $k " 0")) $E "{" "}"
        (join "" (map-atom $ks $k (format-args " 0 M{}" ($k))))))))

(= (nodes-binders $E $q $fs $params $var $body)
   (if (== $fs ()) $body
       (format-args "forall {}, {}" ((join " " (let $js (range-from 0 (length-of $fs)) (map-atom $js $j (format-args "{}{}" ($var $j))))) $body))))

(= (node-with $C $m $var)
   (if (== $m 0) (format-args "{}_node" ($C))
       (format-args "({}_node {})" ($C (join " " (let $js (range-from 0 $m) (map-atom $js $j (format-args "{}{}" ($var $j)))))))))

(= (tuple-with $m $var)
   (format-args "(TupArgs {} {})" ($m (seq (let $js (range-from 0 $m) (map-atom $js $j (format-args "{}{}" ($var $j))))))))

(= (noconf-text $name $cs)
   (let* (($E (egal $name)) ($n (length-of $cs)) ($ks (range-from 0 $n)))
     (join "" (map-atom $ks $k
       (join "" (let $ls (range-from (+ $k 1) $n) (map-atom $ls $l (noconf-pair $E $cs $k $l $n))))))))

(= (noconf-pair $E $cs $k $l $n)
   (let* (($ck (nth $cs $k)) ($cl (nth $cs $l))
          ($Ck (egal (ctor-name $ck))) ($Cl (egal (ctor-name $cl)))
          ($mk (length-of (ctor-fields $ck))) ($ml (length-of (ctor-fields $cl))))
     (format-args "Theorem {}_noconf{}_{} : {}.
{}assume H: {} = {}.
apply IndNode_inj {} {}_distinct {} {} {} {} {} {} H.
assume H1: {} = {}. assume H2.
exact In_irref {} (In_eq_rs {} {} {} H1 {}).
Qed.
"
       ($E $k $l
        (nodes-binders $E 0 (ctor-fields $ck) () "x" (nodes-binders $E 0 (ctor-fields $cl) () "y" (format-args "{} <> {}" ((node-with $Ck $mk "x") (node-with $Cl $ml "y")))))
        (if (== (+ $mk $ml) 0) ""
            (format-args "let {}. " ((join " " (append-lists (let $xjs (range-from 0 $mk) (map-atom $xjs $xj (format-args "x{}" ($xj)))) (let $yjs (range-from 0 $ml) (map-atom $yjs $yj (format-args "y{}" ($yj)))))))))
        (node-with $Ck $mk "x") (node-with $Cl $ml "y")
        (sig $E) $E $k (inproof $k $n) $l (inproof $l $n) (tuple-with $mk "x") (tuple-with $ml "y")
        $k $l
        $k $k $k $l (inproof $k $l)))))

; Constructor injectivity, one theorem per field: equal nodes of one
; constructor have equal fields (IndNode_args_inj at the field's position).
(= (inj-text $name $cs)
   (let* (($E (egal $name)) ($n (length-of $cs)) ($ks (range-from 0 $n)))
     (join "" (map-atom $ks $k (inj-ctor $E $cs $k $n)))))

(= (inj-ctor $E $cs $k $n)
   (let* (($c (nth $cs $k)) ($m (length-of (ctor-fields $c))) ($js (range-from 0 $m)))
     (join "" (map-atom $js $j (inj-field $E (egal (ctor-name $c)) $k $n $m $j)))))

(= (vars-of $m $var) (let $js (range-from 0 $m) (map-atom $js $j (format-args "{}{}" ($var $j)))))

(= (inj-field $E $C $k $n $m $j)
   (let* (($xs (vars-of $m "x")) ($ys (vars-of $m "y"))
          ($sx (seq $xs)) ($sy (seq $ys))
          ($nx (node-with $C $m "x")) ($ny (node-with $C $m "y")))
     (format-args "Theorem {}_inj{} : forall {} {}, {} = {} -> x{} = y{}.
let {} {}. assume H: {} = {}.
claim L: SeqAt {} {} = SeqAt {} {}.
{ exact IndNode_args_inj {} {}_distinct {} {} {} {} {} H {} {}. }
claim Lx: SeqAt {} {} = x{}.
{ {} }
claim Ly: SeqAt {} {} = y{}.
{ {} }
rewrite <- Lx. rewrite <- Ly. exact L.
Qed.
"
       ($C $j (join " " $xs) (join " " $ys) $nx $ny $j $j
        (join " " $xs) (join " " $ys) $nx $ny
        $sx $j $sy $j
        (sig $E) $E $k (inproof $k $n) $m $sx $sy $j (inproof $j $m)
        $sx $j $j (lookup $j "reflexivity.")
        $sy $j $j (lookup $j "reflexivity.")))))

(= (fiber-text $name $q)
   (let $E (egal $name)
     (if (== $q 0) ""
     (if (>= $q 2) (fiber-text-n $E $q)
         (format-args "Theorem {}_in_All : forall i t, t :e {} i -> t :e {}_All.
let i t. assume H: t :e {} i. exact SepE1 {}_All (fun x:set => IndIdx {} x = i) t H.
Qed.
Theorem {}_one_index : forall i i' t, t :e {} i -> t :e {} i' -> i = i'.
let i i' t. assume H: t :e {} i. assume H': t :e {} i'.
exact eq_i_tra i (IndIdx {} t) i' (eq_sym_i (IndIdx {} t) i (SepE2 {}_All (fun x:set => IndIdx {} x = i) t H)) (SepE2 {}_All (fun x:set => IndIdx {} x = i') t H').
Qed.
"
           ($E $E $E $E $E (sig $E) $E $E $E $E $E (sig $E) (sig $E) $E (sig $E) $E (sig $E)))))))

; With several indices, membership is at their tuple.
(= (fiber-text-n $E $q)
   (let* (($iv (ivar-list $q i)) ($jv (ivar-list $q j)) ($is (join " " $iv)) ($js (join " " $jv))
          ($ti (tuple-text $iv)) ($tj (tuple-text $jv)))
     (format-args "Theorem {}_in_All : forall {} t, t :e {} {} -> t :e {}_All.
let {} t. assume H: t :e {} {}. exact SepE1 {}_All (fun x:set => IndIdx {} x = {}) t H.
Qed.
Theorem {}_one_index : forall {} {} t, t :e {} {} -> t :e {} {} -> {} = {}.
let {} {} t. assume H: t :e {} {}. assume H': t :e {} {}.
exact eq_i_tra {} (IndIdx {} t) {} (eq_sym_i (IndIdx {} t) {} (SepE2 {}_All (fun x:set => IndIdx {} x = {}) t H)) (SepE2 {}_All (fun x:set => IndIdx {} x = {}) t H').
Qed.
"
       ($E $is $E $is $E $is $E $is $E (sig $E) $ti
        $E $is $js $E $is $E $js $ti $tj
        $is $js $E $is $E $js
        $ti (sig $E) $tj (sig $E) $ti $E (sig $E) $ti $E (sig $E) $tj))))

; ---- inductive propositions ----
; A proposition is the truth value of its fiber being inhabited; its proofs
; are 0.  The evidence trees above stay the carrier.  The recursor runs on the
; fiber's chosen member, with the motive taken at the proof 0.

(= (is-prop $name) (case (family-of $name) (((Family $n $ps $is Prop $cs) True) ($_ False))))

(= (prop-motive-at $q $is $mode $params)
   (if (== $q 0) "(C 0)" (format-args "(C {} 0)" ((indices-text $is $mode $params)))))

; Pi binders of a minor premise with the motive at proofs.
(= (ppi-chain $E $q $c $params $j $t $j0)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)))
     (if (< $j $m)
         (format-args "(Pi_ x{} :e {}, {})"
           ($j (field-type-m $E $q (nth $fs $j) $params $j0) (ppi-chain $E $q $c $params (+ $j 1) $t $j0)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (format-args "(Pi_ y{} :e {}, {})"
                 ($p (prop-motive-at $q (rec-indices (nth $fs $p)) (mixed $j0) $params) (ppi-chain $E $q $c $params $j (+ $t 1) $j0))))
             (prop-motive-at $q (ctor-result $c) (mixed $j0) $params)))))

(= (pmethod-type $E $q $c $params) (ppi-chain $E $q $c $params 0 0 0))

(= (prop-type-name $name)
   (format-args "{}_{}" ((egal $name) (if (> (index-count $name) 1) "PropPacked" "Prop"))))
; The proof-irrelevant fiber has one encoded index, as does IndFiber. Its
; public predicate keeps the source's separate indices for ordinary use.
(= (prop-text $name $cs $params $q)
   (format-args "{}{}" ((prop-text-core $name $cs $params $q) (prop-view-text $name))))
(= (prop-view-text $name)
   (let* (($n (index-count $name)) ($E (egal $name)) ($P (prop-type-name $name))
          ($xs (ivar-list $n i)) ($args (join " " $xs)))
     (if (> $n 1)
       (format-args "Definition {}_Prop : {} := fun {} => {} {}.
Theorem {}_Prop_prop : forall {}, {}_Prop {} :e LeanProp.
let {}. exact {}_prop {}.
Qed.
" ($E (node-type $n) $args $P (tuple-text $xs) $E $args $E $args $args $P (tuple-text $xs))) "")))

(= (prop-text-core $name $cs $params $q)
   (let* (($E (egal $name))
          ($P (prop-type-name $name))
          ($n (length-of $cs))
          ($ks (range-from 0 $n))
          ($hs (join " " (hs-of $n)))
          ($M (method-fun $cs))
          ($fib (if (== $q 0) $E (format-args "({} i)" ($E))))
          ($Cty (if (== $q 0) "set -> set" "set -> set -> set"))
          ($Cp (if (== $q 0) "(fun t:set => C 0)" (format-args "(fun t:set => C (IndIdx {} t) 0)" ((sig $E))))))
     (join "" (append-lists
       ((if (== $q 0)
            (format-args "Definition {} : set := {}x :e 1 | exists w, w :e {}{}.
Theorem {}_prop : {} :e LeanProp.
exact PowerI 1 {} (Sep_Subq 1 (fun x:set => exists w, w :e {})).
Qed.
" ($P "{" $E "}" $P $P $P $E))
            (format-args "Definition {} : set -> set := fun i => {}x :e 1 | exists w, w :e {} i{}.
Theorem {}_prop : forall i, {} i :e LeanProp.
let i. exact PowerI 1 ({} i) (Sep_Subq 1 (fun x:set => exists w, w :e {} i)).
Qed.
" ($P "{" $E "}" $P $P $P $E))))
       (append-lists
         (map-atom $ks $k (proof-ctor-text $name $cs $params $q $k))
         ((format-args "Definition {}_prec : {} := fun {} {}t => IndRec {} {} (Eps_i (fun w:set => w :e {})).
" ($E (node-type (+ $n (+ (if (== $q 0) 0 1) 1))) $hs (if (== $q 0) "" "i ") (sig $E) $M $fib))
          (join "" (map-atom $ks $k (phm-text $name $cs $params $q $k)))
          (prec-type-text $name $cs $params $q)
          (piota-text $name $cs $params $q)))))))

(= (proof-ctor-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($P (prop-type-name $name))
          ($c (nth $cs $k))
          ($C (egal (ctor-name $c)))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($pt (if (== $q 0) $P (format-args "({} {})" ($P (indices-text (ctor-result $c) x $params))))))
     (format-args "Definition {}_proof : set := {}.
Theorem {}_proof_ok : {}.
{}exact SepI 1 (fun x:set => exists w, w :e {}) 0 In_0_1 (fun p H => H ({}) ({}_typed {})).
Qed.
Theorem {}_proof_type : {}_proof :e {}.
exact {}.
Qed.
"
       ($C (lam-text $E $q $fs $params 0 "0")
        $C (binders $E $q $fs $params 0 (format-args "0 :e {}" ($pt)))
        (intros $E $q $fs $params 0)
        (if (== $q 0) $E (format-args "{} {}" ($E (indices-text (ctor-result $c) x $params))))
        (applied (format-args "{}_node" ($C)) $m) $C (hyp-args $m)
        $C $C (pi-text $E $q $fs $params 0 $pt)
        (proof-lam $E $C $q $fs $params 0 $m $pt)))))

(= (proof-lam $E $C $q $fs $params $j $m $pt)
   (if (== $fs ()) (format-args "({}_proof_ok {})" ($C (hyp-args $m)))
       (format-args "(lam_Pi {} (fun x{} => {}) (fun x{} => {}) (fun x{} H{} => {}))"
         ((field-type $E $q (car-atom $fs) $params)
          $j (pi-text $E $q (cdr-atom $fs) $params (+ $j 1) $pt)
          $j (lam-text $E $q (cdr-atom $fs) $params (+ $j 1) "0")
          $j $j (proof-lam $E $C $q (cdr-atom $fs) $params (+ $j 1) $m $pt)))))

(= (papply-chain $E $q $c $params $j $t $acc $prev)
   (let* (($fs (ctor-fields $c)) ($m (length-of $fs)) ($ps (rec-positions $fs 0)))
     (if (< $j $m)
         (papply-chain $E $q $c $params (+ $j 1) $t
           (format-args "({} (a {}))" ($acc $j))
           (format-args "(ap_Pi {} (fun x{} => {}) {} (a {}) {} G{})"
             ((field-type-m $E $q (nth $fs $j) $params $j) $j (ppi-chain $E $q $c $params (+ $j 1) $t $j) $acc $j $prev $j)))
         (if (< $t (length-of $ps))
             (let $p (nth $ps $t)
               (papply-chain $E $q $c $params $j (+ $t 1)
                 (format-args "({} (r {}))" ($acc $p))
                 (format-args "(ap_Pi {} (fun y{} => {}) {} (r {}) {} Y{})"
                   ((prop-motive-at $q (rec-indices (nth $fs $p)) (mixed $m) $params)
                    $p (ppi-chain $E $q $c $params $j (+ $t 1) $m) $acc $p $prev $p))))
             $prev))))

(= (phm-field-claim $E $q $c $params $k $j $m)
   (let $f (nth (ctor-fields $c) $j)
     (if (is-rec $f)
         (let $idx (if (== $q 0) "0" (indices-text (rec-indices $f) a $params))
           (format-args "claim G{}: (a {}) :e {}.
{} apply Fi {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}). assume H1. assume H2. apply H1 {}_R{}_{}. assume H3: a {} :e {}_All. assume H4: IndIdx {} (a {}) = {}_Ix {} {} a.
  prove (a {}) :e {}x :e {}_All | IndIdx {} x = {}{}.
  apply SepI {}_All (fun x:set => IndIdx {} x = {}) (a {}) H3.
  exact eq_i_tra (IndIdx {} (a {})) ({}_Ix {} {} a) {} H4 ({}_Ix{}_{} a). {}
claim Y{}: r {} :e {}.
{} exact {}. {}
"
             ($j $j (field-type-m $E $q $f $params $m)
              "{" $j $j $E $k $m $E $k (inproof $j $m) $E $k $j $j $E (sig $E) $j $E $k $j
              $j "{" $E (sig $E) $idx "}"
              $E (sig $E) $idx $j
              (sig $E) $j $E $k $j $idx $E $k $j "}"
              $j $j (prop-motive-at $q (rec-indices $f) a $params)
              "{"
              (if (== $q 0)
                  (format-args "Hr {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{}" ($j $j $E $k $m $E $k (inproof $j $m) $E $k $j))
                  (format-args "In_fam_eq (fun z:set => C z 0) (IndIdx {} (a {})) {} (SepE2 {}_All (fun x:set => IndIdx {} x = {}) (a {}) G{}) (r {}) (Hr {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{})"
                    ((sig $E) $j $idx $E (sig $E) $idx $j $j $j $j $j $E $k $m $E $k (inproof $j $m) $E $k $j)))
              "}")))
         (hm-field-claim $E $q $c $params $k $j $m))))

(= (phm-text $name $cs $params $q $k)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($c (nth $cs $k))
          ($fs (ctor-fields $c))
          ($m (length-of $fs))
          ($ps (rec-positions $fs 0))
          ($js (range-from 0 $m))
          ($M (method-fun $cs))
          ($Cty (if (== $q 0) "set -> set" "set -> set -> set"))
          ($Cp (if (== $q 0) "(fun t:set => C 0)" (format-args "(fun t:set => C (IndIdx {} t) 0)" ((sig $E)))))
          ($am (applied-method $k $c))
          ($ridx (if (== $q 0) "0" (indices-text (ctor-result $c) a $params))))
     (format-args "Theorem {}_PHM{} : forall C:{}, forall {}, h{} :e {} -> forall a :e IndArgs {} {}_All {}, forall r:set -> set, (forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j)) -> {} {} a (IndRes {} {} r) :e {} (IndNode {} {} a).
let C {}. assume Hh: h{} :e {}.
let a. assume Ha: a :e IndArgs {} {}_All {}. let r. assume Hr: forall j :e {}_N {}, {}_R {} j -> r j :e {} (a j).
claim Fi: IndFits {} {}_All {} a.
{ exact IndArgs_Fits {} {}_All {} a Ha. }
{}{}claim Lv: {} :e {}.
{ exact {}. }
claim Lm: {} {} a (IndRes {} {} r) = {}.
{ prove SeqAt {} {} = {}. {} }
{}
Qed.
"
       ($E $k $Cty $hs $k (pmethod-type $E $q $c $params) (sig $E) $E $k $E $k $E $k $Cp $M $k (sig $E) $k $Cp (sig $E) $k
        $hs $k (pmethod-type $E $q $c $params)
        (sig $E) $E $k $E $k $E $k $Cp
        (sig $E) $E $k (sig $E) $E $k
        (join "" (map-atom $js $j (phm-field-claim $E $q $c $params $k $j $m)))
        (join "" (map-atom $ps $p (format-args "claim Rp{}: IndRes {} {} r {} = r {}.
{} exact IndRes_at {} {} r {} (In_eq_rs {} ({}_N {}) {} {}_N{} {}) {}_R{}_{}. {}
" ($p (sig $E) $k $p $p "{" (sig $E) $k $p $p $E $k $m $E $k (inproof $p $m) $E $k $p "}"))))
        $am (prop-motive-at $q (ctor-result $c) a $params)
        (if (== $m 0) "Hh" (papply-chain $E $q $c $params 0 0 (format-args "h{}" ($k)) "Hh"))
        $M $k (sig $E) $k $am
        (methods-seq $cs "(a {})" (format-args "(IndRes {} {} r {})" ((sig $E) $k "{}"))) $k $am
        (lookup $k (format-args "{}reflexivity." ((join "" (map-atom $ps $p (format-args "rewrite Rp{}. " ($p)))))))
        (if (== $q 0)
            (format-args "exact In_eq_ls ({} {} a (IndRes {} {} r)) {} (C 0) Lm Lv." ($M $k (sig $E) $k $am))
            (format-args "claim Lo: {} = IndIdx {} (IndNode {} {} a).
{} exact eq_i_tra {} ({}_O {} a) (IndIdx {} (IndNode {} {} a)) (eq_sym_i ({}_O {} a) {} ({}_O{} a)) (eq_sym_i (IndIdx {} (IndNode {} {} a)) ({}_O {} a) (IndIdx_Node {} {} a)). {}
exact In_eq_ls ({} {} a (IndRes {} {} r)) {} (C (IndIdx {} (IndNode {} {} a)) 0) Lm (In_fam_eq (fun z:set => C z 0) {} (IndIdx {} (IndNode {} {} a)) Lo {} Lv)."
              ($ridx (sig $E) (sig $E) $k
               "{" $ridx $E $k (sig $E) (sig $E) $k $E $k $ridx $E $k (sig $E) (sig $E) $k $E $k (sig $E) $k "}"
               $M $k (sig $E) $k $am (sig $E) (sig $E) $k
               $ridx (sig $E) (sig $E) $k $am)))))))

(= (prec-type-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($P (prop-type-name $name))
          ($n (length-of $cs))
          ($hs (join " " (hs-of $n)))
          ($ks (range-from 0 $n))
          ($Cty (if (== $q 0) "set -> set" "set -> set -> set"))
          ($Cp (if (== $q 0) "(fun t:set => C 0)" (format-args "(fun t:set => C (IndIdx {} t) 0)" ((sig $E)))))
          ($M (method-fun $cs))
          ($fib (if (== $q 0) $E (format-args "({} i)" ($E))))
          ($prop (if (== $q 0) $P (format-args "({} i)" ($P))))
          ($hyps (join " " (map-atom $ks $k (format-args "forall h{} :e {}," ($k (pmethod-type $E $q (nth $cs $k) $params))))))
          ($HM (format-args "(fun k => forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a))"
                 ((sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E))))
          ($w "(Eps_i (fun w:set => w :e FIB))"))
     (format-args "Theorem {}_prec_type : forall C:{}, {}{} {}forall t :e {}, {}_prec {} {}t :e {}.
let C. {}{}
claim HM: forall k :e {}_K, forall a :e IndArgs {} {}_All k, forall r:set -> set, (forall j :e {}_N k, {}_R k j -> r j :e {} (a j)) -> {} k a (IndRes {} k r) :e {} (IndNode {} k a).
{ let k. assume Hk: k :e {}_K. exact {} k Hk. }
{}let t. assume Ht: t :e {}.
claim Hw0: (Eps_i (fun w:set => w :e {})) :e {}.
{ exact Eps_i_ex (fun w:set => w :e {}) (SepE2 1 (fun x:set => exists w, w :e {}) t Ht). }
claim Ht0: t = 0.
{ exact SingE 0 t (Subq_1_Sing0 t (SepE1 1 (fun x:set => exists w, w :e {}) t Ht)). }
claim L: IndRec {} {} (Eps_i (fun w:set => w :e {})) :e {} (Eps_i (fun w:set => w :e {})).
{ exact IndRec_type {} {}_distinct {}_bounded {}_arity {} {} HM (Eps_i (fun w:set => w :e {})) (SepE1 {}_All (fun x:set => IndIdx {} x = {}) (Eps_i (fun w:set => w :e {})) Hw0). }
{}
Qed.
"
       ($E $Cty
        (if (prop-only $name)
            (if (== $q 0) "(forall t, C t :e LeanProp) -> " "(forall i t, C i t :e LeanProp) -> ")
            "")
        $hyps (if (== $q 0) "" "forall i, ") $prop $E $hs (if (== $q 0) "" "i ") (if (== $q 0) "C t" "C i t")
        (if (prop-only $name) "assume HP. " "")
        (join " " (map-atom $ks $k (format-args "let h{}. assume Hh{}." ($k $k))))
        $E (sig $E) $E $E $E $Cp $M (sig $E) $Cp (sig $E)
        $E (below $n $HM (map-atom $ks $k (format-args "({}_PHM{} C {} Hh{})" ($E $k $hs $k))))
        (if (== $q 0) "" "let i. ")
        $prop
        $fib $fib $fib $fib $fib
        (sig $E) $M $fib $Cp $fib
        (sig $E) $E $E $E $M $Cp $fib $E (sig $E) (if (== $q 0) "0" "i") $fib
        (if (== $q 0)
            (format-args "exact In_fam_eq (fun z:set => C z) 0 t (eq_sym_i t 0 Ht0) (IndRec {} {} (Eps_i (fun w:set => w :e {}))) L." ((sig $E) $M $fib))
            (format-args "exact In_fam_eq (fun z:set => C i z) 0 t (eq_sym_i t 0 Ht0) (IndRec {} {} (Eps_i (fun w:set => w :e {}))) (In_fam_eq (fun z:set => C z 0) (IndIdx {} (Eps_i (fun w:set => w :e {}))) i (SepE2 {}_All (fun x:set => IndIdx {} x = i) (Eps_i (fun w:set => w :e {})) Hw0) (IndRec {} {} (Eps_i (fun w:set => w :e {}))) L)."
              ((sig $E) $M $fib (sig $E) $fib $E (sig $E) $fib (sig $E) $M $fib)))))))

; Iota for a single constructor without fields: the fiber's member is its node.
(= (piota-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($n (length-of $cs)))
     (if (and (== $n 1) (== (length-of (ctor-fields (car-atom $cs))) 0))
         (let* (($c (car-atom $cs)) ($C (egal (ctor-name $c)))
                ($ridx (if (== $q 0) "0" (indices-text (ctor-result $c) x $params)))
                ($fib (if (== $q 0) $E (format-args "({} {})" ($E $ridx))))
                ($M (method-fun $cs)))
           (format-args "Theorem {}_unique : forall w :e {}_All, w = {}_node.
let w. assume Hw: w :e {}_All.
apply IndCarrier_inv {} w Hw.
let k. assume Hk. apply Hk. assume Hk1: k :e {}_K.
assume Hk2: exists a :e IndArgs {} {}_All k, w = IndNode {} k a.
apply Hk2. let a. assume Ha. apply Ha. assume Ha1: a :e IndArgs {} {}_All k. assume Hwa: w = IndNode {} k a.
claim Lk: k = 0.
{} exact SingE 0 k (Subq_1_Sing0 k Hk1). {}
claim Ha0: a :e IndArgs {} {}_All 0.
{} exact In_fam_eq (IndArgs {} {}_All) k 0 Lk a Ha1. {}
claim La: a = 0.
{} apply Empty_eq a. let u. assume Hu: u :e a.
  apply PiE 0 (fun j => {}_B :\\/: {}_All) a (In_fam_eq (fun X:set => Pi_ j :e X, {}_B :\\/: {}_All) ({}_N 0) 0 {}_N0 a (IndArgs_Pi {} {}_All 0 a Ha0)).
  assume H1: forall u :e a, pair_p u /\\ u 0 :e 0. assume H2.
  apply H1 u Hu. assume Hp. assume Hu0: u 0 :e 0. exact EmptyE (u 0) Hu0. {}
claim Lt: TupArgs 0 SeqNil = 0.
{} apply Empty_eq (TupArgs 0 SeqNil). let u. assume Hu: u :e TupArgs 0 SeqNil.
  apply lamE 0 (fun j => SeqAt SeqNil j) u Hu. let j. assume Hj. apply Hj. assume Hj0: j :e 0. assume Hj1. exact EmptyE j Hj0. {}
rewrite Hwa. rewrite Lk. rewrite La.
prove IndNode {} 0 0 = IndNode {} 0 (TupArgs 0 SeqNil).
rewrite Lt. reflexivity.
Qed.
Theorem {}_piota : forall h0, {}_prec h0 {}0 = h0.
let h0.
claim Hw: {}_node :e {}.
{} exact {}_typed. {}
claim Le: Eps_i (fun w:set => w :e {}) = {}_node.
{} exact {}_unique (Eps_i (fun w:set => w :e {})) (SepE1 {}_All (fun x:set => IndIdx {} x = {}) (Eps_i (fun w:set => w :e {})) (Eps_i_ex (fun w:set => w :e {}) (fun p H => H {}_node Hw))). {}
prove IndRec {} {} (Eps_i (fun w:set => w :e {})) = h0.
rewrite Le.
prove IndRec {} {} (IndNode {} 0 (TupArgs 0 SeqNil)) = h0.
rewrite IndRec_iota {} {}_distinct {}_bounded {}_arity {} 0 (ordsuccI2 0) (TupArgs 0 SeqNil) {}_args.
prove SeqAt (SeqCons (h0) SeqNil) 0 = h0.
rewrite SeqAt_0. reflexivity.
Qed.
"
             ($E $E $C $E (sig $E) $E (sig $E) $E (sig $E) (sig $E) $E (sig $E)
              "{" "}"
              (sig $E) $E "{" (sig $E) $E "}"
              "{" $E $E $E $E $E $E (sig $E) $E "}"
              "{" "}"
              (sig $E) (sig $E)
              $E $E (if (== $q 0) "" (format-args "{} " ($ridx)))
              $C $fib "{" $C "}"
              $fib $C "{" $E $fib $E (sig $E) $ridx $fib $fib $C "}"
              (sig $E) $M $fib
              (sig $E) $M (sig $E)
              (sig $E) $E $E $E $M $C)))
         "")))

(= (prop-only $name)
   (let $found (collapse (match &self (LeanFamily (Family $name $ps $is $sort $cs) $u (Elimination propOnly) $k) True))
     (if (== $found ()) False True)))

; ---- universe membership ----

(= (find-ctor $fam $cs $c)
   (if (== $cs ()) None
       (if (== (ctor-name (car-atom $cs)) $c) (owner $fam (car-atom $cs)) (find-ctor $fam (cdr-atom $cs) $c))))

(= (first-owner $xs)
   (if (== $xs ()) None (if (== (car-atom $xs) None) (first-owner (cdr-atom $xs)) (car-atom $xs))))

(= (ctor-owner $c)
   (let $o (first-owner (collapse (match &self (LeanAdmitted $fam $cs) (find-ctor $fam $cs $c))))
     (if (== $o None) (first-owner (collapse (match &self (LeanBlockRecursor $F $r $res $mo $mi $k) (find-ctor $F (member-view-ctors $F) $c)))) $o)))

; A proof of (sort) :e LeanUniv u.
(= (sort-in $t $params)
   (if (== $t one) "(LeanUniv_nat_In u Hu 1 nat_1)"
   (if (== $t Prop) "(LeanProp_In_LeanUniv u Hu)"
   (if (and (not (== (get-metatype $t) Expression)) (prop-family $t))
       (format-args "(LeanProp_sub_In u Hu {} {}_Prop_prop)" ((sort-text $t $params) (egal $t)))
   (if (and (== (get-metatype $t) Expression) (prop-family (car-atom $t)))
       (let $args (cdr-atom $t)
         (format-args "(LeanProp_sub_In u Hu {} ({}_Prop_prop {}))"
           ((sort-text $t $params) (egal (car-atom $t)) (join " " (map-atom $args $a (sort-text $a $params))))))
   (if (and (== (get-metatype $t) Expression) (== (car-atom $t) ->))
       (format-args "(ZF_Pi_In (LeanUniv u) (LeanUniv_TransSet u Hu) (LeanUniv_ZF_closed u Hu) {} {} (fun _ => {}) (fun _ _ => {}))"
         ((sort-text (nth $t 1) $params) (sort-in (nth $t 1) $params) (sort-text (nth $t 2) $params) (sort-in (nth $t 2) $params)))
   (if (== (get-metatype $t) Expression)
       (let* (($f (car-atom $t)) ($args (cdr-atom $t)))
         (format-args "({}_type_In {} u Hu {})"
           ((egal $f) (join " " (map-atom $args $x (sort-text $x $params))) (join " " (map-atom $args $y (sort-in $y $params))))))
       (let $i (param-index $t $params 0)
         (if (>= $i 0) (format-args "HP{}" ($i)) (format-args "({}_type_In u Hu)" ((egal $t))))))))))))

; A proof of (index term over a) :e LeanUniv u: fields, parameters, literals,
; and nodes, by their fields' membership (C_node_In).
(= (idx-in $i $m $params)
   (let $k (closed-nat $i)
     (if (== $k None) (idx-in-open $i $m $params)
         (format-args "(Ht Lean_Nat (Lean_Nat_type_In u Hu) (LeanNum {}) (LeanNum_In {} {}))" ((num-arg $k) (num-arg $k) (num-natproof $k))))))
(= (idx-in-open $i $m $params)
   (case $i
     (((field $p) (format-args "(Ht V HV (a {}) (ap_Pi {} (fun j => V) a {} Ham {}))" ($p $m $p (inproof $p $m))))
      ((code $n) (format-args "(LeanUniv_nat_In u Hu {} {})" ($n (natproof $n))))
      ((const $c)
       (let $pi (param-index $c $params 0)
         (if (>= $pi 0) (format-args "HP{}" ($pi))
             (case (ctor-owner $c)
               (((owner $fam $ctor)
                 (format-args "(Ht {} ({}_type_In u Hu) {}_node {}_typed)" ((egal $fam) (egal $fam) (egal $c) (egal $c)))))))))
      ((app $f $x)
       (let* (($h (index-head $i)) ($as (index-args $i)))
         (if (full-ctor-app $h (length-of $as))
             (case (ctor-owner $h)
               (((owner $fam $ctor)
                 (let* (($np (length-of (params-of $fam))) ($ps (take-n $as $np)) ($xs (drop-n $as $np)))
                   (format-args "({}_node_In {}u Hu{})"
                     ((egal $h)
                      (join "" (map-atom $ps $y (format-args "{} " ((index-text $y a $params)))))
                      (join "" (map-atom $xs $y (format-args " {} {}" ((index-text $y a $params) (idx-in $y $m $params)))))))))))
             "index_term_not_read"))))))

; The constructors some family's index terms apply: their nodes get
; universe membership (C_node_In).
(= (ctors-in-index $i)
   (case $i
     (((app $f $x)
       (let $rest (append-lists (ctors-in-index-args (index-args $i)) ())
         (if (full-ctor-app (index-head $i) (length-of (index-args $i))) (cons-atom (index-head $i) $rest) $rest)))
      ($_ ()))))
(= (ctors-in-index-args $as) (if (== $as ()) () (append-lists (ctors-in-index (car-atom $as)) (ctors-in-index-args (cdr-atom $as)))))
(= (ctors-in-ctor $c)
   (append-lists (ctors-in-index-args (ctor-result $c)) (ctors-in-fields (ctor-fields $c))))
(= (ctors-in-fields $fs)
   (if (== $fs ()) ()
       (append-lists (case (car-atom $fs) (((rec $is) (ctors-in-index-args $is)) ($_ ())))
         (ctors-in-fields (cdr-atom $fs)))))
(= (ctors-in-ctors $cs) (if (== $cs ()) () (append-lists (ctors-in-ctor (car-atom $cs)) (ctors-in-ctors (cdr-atom $cs)))))
(= (index-ctors)
   (let $all (collapse (match &self (LeanAdmitted $F $cs) (ctors-in-ctors $cs)))
     (flatten-lists $all)))
(= (flatten-lists $ls) (if (== $ls ()) () (append-lists (car-atom $ls) (flatten-lists (cdr-atom $ls)))))
(= (in-index $c) (list-has $c (index-ctors)))

(= (indices-in $is $m $params)
   (if (== $is ()) "H0"
       (if (== (cdr-atom $is) ()) (idx-in (car-atom $is) $m $params)
           (format-args "(ZF_pair_In (LeanUniv u) Ht Hz {} {} {} {})"
             ((index-text (car-atom $is) a $params) (idx-in (car-atom $is) $m $params)
              (indices-text (cdr-atom $is) a $params) (indices-in (cdr-atom $is) $m $params))))))

(= (union-in $sorts $i $params $terms)
   (if (== $i 0) (sort-in (nth $terms 0) $params)
       (format-args "(ZF_binunion_closed (LeanUniv u) Hz {} {} ({}) {})"
         ((union-prefix $sorts (- $i 1)) (union-in $sorts (- $i 1) $params $terms) (nth $sorts $i) (sort-in (nth $terms $i) $params)))))

; Data sort terms, as authored, in field order.
(= (field-data-terms $fs)
   (if (== $fs ()) ()
       (let $rest (field-data-terms (cdr-atom $fs))
         (case (car-atom $fs) (((data $t) (cons-atom $t $rest)) ((guard $p) (cons-atom one $rest)) ($_ $rest))))))

(= (data-terms $cs)
   (if (== $cs ()) () (append-lists (field-data-terms (ctor-fields (car-atom $cs))) (data-terms (cdr-atom $cs)))))

(= (in-text $name $cs $params $q)
   (let* (($E (egal $name))
          ($n (length-of $cs))
          ($ks (range-from 0 $n))
          ($np (length-of $params))
          ($ps (range-from 0 $np))
          ($hyps (join "" (map-atom $ps $i (format-args "P{} :e LeanUniv u -> " ($i)))))
          ($hintros (join "" (map-atom $ps $i (format-args "assume HP{}: P{} :e LeanUniv u. " ($i $i)))))
          ($sorts (data-sorts $cs $params))
          ($terms (data-terms $cs))
          ($PO (format-args "(fun k => forall V :e LeanUniv u, forall a :e (Pi_ j :e {}_N k, V), {}_O k a :e LeanUniv u)" ($E $E))))
     (format-args "Theorem {}_In : forall u, nat_p u -> {}{}_All :e LeanUniv u.
let u. assume Hu: nat_p u. {}
claim Ht: TransSet (LeanUniv u).
{} exact LeanUniv_TransSet u Hu. {}
claim Hz: ZF_closed (LeanUniv u).
{} exact LeanUniv_ZF_closed u Hu. {}
claim H0: 0 :e LeanUniv u.
{} exact LeanUniv_0_In u Hu. {}
{}exact IndCarrier_In {} (LeanUniv u) Ht Hz (omega_In_LeanUniv u Hu) (LeanUniv_nat_In u Hu {} {}) {} {}_arity (fun k Hk => LeanUniv_nat_In u Hu k (nat_p_trans {} {} k Hk)) (fun k Hk => {} k Hk).
Qed.
Theorem {}_type_In : forall u, nat_p u -> {}{}.
let u. assume Hu: nat_p u. {}{}
exact IndFiber_In {} (LeanUniv u) (LeanUniv_TransSet u Hu) (LeanUniv_ZF_closed u Hu) ({}_In u Hu {}){}.
Qed.
"
       ($E $hyps $E $hintros
        "{" "}" "{" "}" "{" "}"
        (join "" (map-atom $ks $k (ho-claim $E $cs $params $k)))
        (sig $E) $n (natproof $n)
        (if (== $sorts ()) "H0" (union-in $sorts (- (length-of $sorts) 1) $params $terms))
        $E $n (natproof $n)
        (below $n $PO (map-atom $ks $k (format-args "HO{}" ($k))))
        $E $hyps (if (== $q 0) (format-args "{} :e LeanUniv u" ($E))
                   (if (== $q 1) (format-args "forall i, {} i :e LeanUniv u" ($E))
                       (format-args "forall {}, {} {} :e LeanUniv u" ((join " " (ivar-list $q i)) $E (join " " (ivar-list $q i))))))
        $hintros
        (if (== $q 0) "" (if (== $q 1) "let i. " (format-args "let {}. " ((join " " (ivar-list $q i))))))
        (sig $E) $E (join " " (map-atom $ps $i (format-args "HP{}" ($i))))
        (if (== $q 0) " 0" (if (== $q 1) " i" (format-args " {}" ((tuple-text (ivar-list $q i))))))))))

(= (ho-claim $E $cs $params $k)
   (let* (($c (nth $cs $k)) ($m (length-of (ctor-fields $c))))
     (format-args "claim HO{}: forall V :e LeanUniv u, forall a :e (Pi_ j :e {}_N {}, V), {}_O {} a :e LeanUniv u.
{} let V. assume HV: V :e LeanUniv u. let a. assume Ha: a :e (Pi_ j :e {}_N {}, V).
  claim Ham: a :e Pi_ j :e {}, V.
  {} exact In_fam_eq (fun X:set => Pi_ j :e X, V) ({}_N {}) {} {}_N{} a Ha. {}
  prove SeqAt {} {} :e LeanUniv u. rewrite {}_O{} a. exact {}. {}
"
       ($k $E $k $E $k "{" $E $k $m "{" $E $k $m $E $k "}"
        (os-seq $cs $params) $k $E $k (indices-in (ctor-result $c) $m $params) "}"))))

; ---- nested blocks ----
; A nested family (CEK.Val with a List CEK.Val field) is read by Lean's
; auxiliary block: one indexed family whose index is a member's code.  The
; container member (List CEK.Val) takes the container's own constructor
; numbers and index, so its nodes are Lean_List's nodes and its fiber is
; Lean_List of the main member (proved below); the main member's code is
; its tag plus one.  Lean's family is the main member's fiber, with its
; constructors, their typing, and its case analysis read from the block.

; (The export's members are rewritten as (mb tag type) inside the match:
; member is a built-in function, so a list headed by it would be called.)
(= (block-atom $F)
   (let* (($f1 (collapse (match &self (LeanAdmittedBlock $F (members (member $t0 $y0 $i0 $s0)) $cs)
                           (blk ((mb $t0 $y0 $i0 $s0)) $cs))))
          ($f2 (collapse (match &self (LeanAdmittedBlock $F (members (member $t0 $y0 $i0 $s0) (member $t1 $y1 $i1 $s1)) $cs)
                           (blk ((mb $t0 $y0 $i0 $s0) (mb $t1 $y1 $i1 $s1)) $cs))))
          ($f (append-lists $f1 $f2)))
     (if (== $f ()) None (car-atom $f))))
(= (is-block $F) (if (== (block-atom $F) None) False True))
(= (block-members $F) (case (block-atom $F) (((blk $ms $cs) $ms))))
(= (block-lean-ctors $F) (case (block-atom $F) (((blk $ms $cs) $cs))))
(= (member-tag $m) (case $m (((mb $t $ty $i $s) $t))))
(= (member-type $m) (case $m (((mb $t $ty $i $s) $ty))))
(= (member-indices $m) (case $m (((mb $t $ty (indices $is) $s) $is))))
(= (member-sort $m) (case $m (((mb $t $ty $i $s) $s))))
(= (member-at $ms $t)
   (if (== $ms ()) None (if (== (member-tag (car-atom $ms)) $t) (car-atom $ms) (member-at (cdr-atom $ms) $t))))
(= (is-container-member $m) (case (member-type $m) (((app $c $x) True) ($_ False))))
(= (tag-code $F $t) (if (is-container-member (member-at (block-members $F) $t)) 0 (+ $t 1)))
(= (ctor-tag $c) (case (car-atom (ctor-result $c)) (((tag $t) $t))))
(= (tag-is-container $F $t) (is-container-member (member-at (block-members $F) $t)))

; A recursive field into member t at its natural indices: into code c of the block.
(= (code-field $F $f)
   (case $f
     (((rec $is) (case (car-atom $is) (((tag $t) (rec (cons-atom (code (tag-code $F $t)) (cdr-atom $is)))) ($_ $f))))
      ($_ $f))))
(= (code-fields $F $fs) (if (== $fs ()) () (cons-atom (code-field $F (car-atom $fs)) (code-fields $F (cdr-atom $fs)))))
(= (block-ctor $F $c)
   ((bk (ctor-name $c)) (cons-atom fields (code-fields $F (ctor-fields $c)))
    (result (cons-atom (code (tag-code $F (ctor-tag $c))) (cdr-atom (ctor-result $c))))))
(= (block-ctors-where $F $cs $container)
   (if (== $cs ()) ()
       (let $rest (block-ctors-where $F (cdr-atom $cs) $container)
         (if (== (tag-is-container $F (ctor-tag (car-atom $cs))) $container)
             (cons-atom (block-ctor $F (car-atom $cs)) $rest) $rest))))
(= (block-ctors $F)
   (append-lists (block-ctors-where $F (block-lean-ctors $F) True) (block-ctors-where $F (block-lean-ctors $F) False)))

; The main member as a family of its own: a field into the container member
; is a data field of the container's type.
(= (term-sort $t) (case $t (((const $c) $c) ((app $f $x) (cons-atom (term-sort $f) ((term-sort $x)))))))
(= (view-field $F $f)
   (case $f
     (((rec ((tag $t)))
       (if (tag-is-container $F $t) (data (term-sort (member-type (member-at (block-members $F) $t)))) (rec ())))
      ($_ $f))))
(= (view-fields $F $fs) (if (== $fs ()) () (cons-atom (view-field $F (car-atom $fs)) (view-fields $F (cdr-atom $fs)))))
(= (member-view-ctors $F)
   (if (not (is-block $F)) ()
       (view-ctors-of $F (block-lean-ctors $F))))
(= (view-ctors-of $F $cs)
   (if (== $cs ()) ()
       (let $rest (view-ctors-of $F (cdr-atom $cs))
         (if (== (ctor-tag (car-atom $cs)) 0)
             (cons-atom ((ctor-name (car-atom $cs)) (cons-atom fields (view-fields $F (ctor-fields (car-atom $cs)))) (result ())) $rest)
             $rest))))

; ---- the main member of a block whose container member is List ----
; (Text of one theorem per construction step; every proof states each
; intermediate goal, since apply leaves beta-redexes in the goals it makes.)

(= (bk-name $c) (egal (bk $c)))
(= (block-main-ctors $F) (main-ctors-of (block-ctors $F) 0))
(= (main-ctors-of $cs $k)
   (if (== $cs ()) ()
       (let $rest (main-ctors-of (cdr-atom $cs) (+ $k 1))
         (if (== (ctor-result (car-atom $cs)) ((code 0))) $rest (cons-atom (mc $k (car-atom $cs)) $rest)))))
(= (mc-index $m) (case $m (((mc $k $c) $k))))
(= (mc-ctor $m) (case $m (((mc $k $c) $c))))
(= (lean-ctor-name $bc) (case (ctor-name $bc) (((bk $c) $c))))
(= (field-code $f) (case $f (((rec ((code $c))) $c) ($_ None))))

(= (xs-text $n) (join " " (vars-of $n "x")))
(= (node-at $name $n) (if (== $n 0) (format-args "{}_node" ($name)) (format-args "({}_node {})" ($name (xs-text $n)))))
(= (bfield-type $B $f) (case $f (((data $s) (sort-text $s ())) ((rec ((code $c))) (format-args "({} {})" ($B $c))))))
(= (vfield-type $E $f) (case $f (((data $s) (sort-text $s ())) ((rec ((code $c))) (if (== $c 0) (format-args "(Lean_List {})" ($E)) "NESTED_MAIN")))))

; The motive of each construction, at code c and term t.
(= (mot $kind $E $B $c $t)
   (case $kind
     ((sub (format-args "{}z :e 1 | {} = 0 -> {} :e Lean_List {}{}" ("{" $c $t $E "}")))
      (typ (format-args "({}_motive C {} {})" ($E $c $t))))))

; Pi_ over the fields from j, then the results of the recursive fields, then the motive at the node.
(= (pi-from $kind $E $B $fs $j $n $code $node)
   (if (< $j $n)
       (format-args "(Pi_ x{} :e {}, {})" ($j (bfield-type $B (nth $fs $j)) (pi-from $kind $E $B $fs (+ $j 1) $n $code $node)))
       (ih-pi-from $kind $E $B $fs 0 $n $code $node)))
(= (ih-pi-from $kind $E $B $fs $j $n $code $node)
   (if (>= $j $n) (mot $kind $E $B $code $node)
       (let $c (field-code (nth $fs $j))
         (if (== $c None) (ih-pi-from $kind $E $B $fs (+ $j 1) $n $code $node)
             (format-args "(Pi_ y{} :e {}, {})" ($j (mot $kind $E $B $c (format-args "x{}" ($j))) (ih-pi-from $kind $E $B $fs (+ $j 1) $n $code $node)))))))

; The steps proving 0 :e (pi-from ..), down to the motive.
(= (zero-steps $kind $E $B $fs $j $n $code $node)
   (if (< $j $n)
       (format-args "apply Pi_0_In. let x{}. assume Hx{}.
  prove 0 :e {}.
  {}" ($j $j (pi-from $kind $E $B $fs (+ $j 1) $n $code $node) (zero-steps $kind $E $B $fs (+ $j 1) $n $code $node)))
       (zero-ih-steps $kind $E $B $fs 0 $n $code $node)))
(= (zero-ih-steps $kind $E $B $fs $j $n $code $node)
   (if (>= $j $n) ""
       (let $c (field-code (nth $fs $j))
         (if (== $c None) (zero-ih-steps $kind $E $B $fs (+ $j 1) $n $code $node)
             (format-args "apply Pi_0_In. let y{}. assume Hy{}.
  prove 0 :e {}.
  {}" ($j $j (ih-pi-from $kind $E $B $fs (+ $j 1) $n $code $node) (zero-ih-steps $kind $E $B $fs (+ $j 1) $n $code $node)))))))

(= (view-section $F)
   (let* (($E (egal $F)) ($B (egal (bk $F))) ($bcs (block-ctors $F)) ($nb (length-of $bcs))
          ($bos (os-seq $bcs ())) ($los (os-seq (constructors-of List) ((: α Type))))
          ($nil (egal (ctor-name (nth $bcs 0)))) ($cons (egal (ctor-name (nth $bcs 1))))
          ($mains (block-main-ctors $F)))
     (format-args "(** ---- {}, the main member of its nested block ---- **)

Definition {} : set := {} 1.
{}{}{}{}{}{}{}{}{}{}"
       ($F $E $B
        (node-eq-text $E $B $nil $cons $bos $los)
        (sub-list-text $E $B $bcs)
        (list-sub-text $E $B $nil $cons)
        (format-args "Theorem {}_container : {} 0 = Lean_List {}.
apply set_ext.
- exact {}_sub_list.
- exact {}_list_sub.
Qed.

" ($B $B $E $B $B))
        (join "" (map-atom $mains $m (view-ctor-text $E $B (mc-ctor $m))))
        (motive-text $E)
        (view-rec-def $E $B $bcs $mains)
        (rec-container-text $E $B $nil $cons $nb)
        (join "" (view-iotas $E $B $bcs $mains 0))
        (view-rec-type $E $B $bcs $mains $nb)))))

(= (node-eq-text $E $B $nil $cons $bos $los)
   (format-args "Theorem {}_nil_eq : {}_node = Lean_List_nil_node {}.
claim Lb: SeqAt {} 0 = 0. {} {} {}
claim Ll: SeqAt {} 0 = 0. {} {} {}
prove setsum (setsum 0 (SeqAt {} 0)) (TupArgs 0 SeqNil) = setsum (setsum 0 (SeqAt {} 0)) (TupArgs 0 SeqNil).
rewrite Lb. rewrite Ll. reflexivity.
Qed.

Theorem {}_cons_eq : forall x0 x1, {}_node x0 x1 = Lean_List_cons_node {} x0 x1.
let x0 x1.
claim Lb: SeqAt {} 1 = 0. {} {} {}
claim Ll: SeqAt {} 1 = 0. {} {} {}
prove setsum (setsum 1 (SeqAt {} 1)) (TupArgs 2 (SeqCons (x0) (SeqCons (x1) SeqNil))) = setsum (setsum 1 (SeqAt {} 1)) (TupArgs 2 (SeqCons (x0) (SeqCons (x1) SeqNil))).
rewrite Lb. rewrite Ll. reflexivity.
Qed.

" ($B $nil $E $bos "{" (lookup 0 "reflexivity.") "}" $los "{" (lookup 0 "reflexivity.") "}" $bos $los
   $B $cons $E $bos "{" (lookup 1 "reflexivity.") "}" $los "{" (lookup 1 "reflexivity.") "}" $bos $los)))

; The container member lies in Lean_List: every block element at code 0 does.
(= (sub-claim $E $B $bc $k)
   (let* (($fs (ctor-fields $bc)) ($n (length-of $fs)) ($code (car-atom (ctor-result $bc)))
          ($c (case $code (((code $x) $x)))) ($node (node-at (egal (ctor-name $bc)) $n)))
     (format-args "claim H{}: 0 :e {}.
{ {}prove 0 :e {}.
  apply SepI 1 (fun z => {} = 0 -> {} :e Lean_List {}) 0 In_0_1.
  {} }
" ($k (pi-from sub $E $B $fs 0 $n $c $node) (zero-steps sub $E $B $fs 0 $n $c $node) (mot sub $E $B $c $node)
   $c $node $E
   (if (== $c 1) "assume H10: 1 = 0. apply FalseE. exact neq_1_0 H10."
       (if (== $n 0) (format-args "assume _. rewrite {}_nil_eq. exact Lean_List_nil_typed {}." ($B $E))
           (format-args "assume _.
  claim Lx1: x1 :e Lean_List {}.
  {} apply SepE2 1 (fun z => 0 = 0 -> x1 :e Lean_List {}) y1 Hy1. reflexivity. {}
  rewrite {}_cons_eq x0 x1. exact Lean_List_cons_typed {} x0 Hx0 x1 Lx1." ($E "{" $E "}" $B $E))))))))
(= (sub-claims $E $B $bcs $k)
   (if (== $bcs ()) "" (format-args "{}{}" ((sub-claim $E $B (car-atom $bcs) $k) (sub-claims $E $B (cdr-atom $bcs) (+ $k 1))))))
(= (zero-hs $n $k) (if (>= $k $n) "" (format-args " 0 H{}{}" ($k (zero-hs $n (+ $k 1))))))
(= (zero-ms $n) (if (== $n 0) "" (format-args " 0{}" ((zero-ms (- $n 1))))))
(= (sub-list-text $E $B $bcs)
   (let $nb (length-of $bcs)
     (format-args "Theorem {}_sub_list : forall t :e {} 0, t :e Lean_List {}.
{}let t. assume Ht: t :e {} 0.
claim L: {}_rec{} t :e {}z :e 1 | 0 = 0 -> t :e Lean_List {}{}.
{} exact {}_rec_type (fun i t => {}z :e 1 | i = 0 -> t :e Lean_List {}{}){} 0 t Ht. {}
apply SepE2 1 (fun z => 0 = 0 -> t :e Lean_List {}) ({}_rec{} t) L.
reflexivity.
Qed.

" ($B $B $E (sub-claims $E $B $bcs 0) $B $B (zero-ms $nb) "{" $E "}" "{" $B "{" $E "}" (zero-hs $nb 0) "}" $E $B (zero-ms $nb)))))

(= (list-sub-text $E $B $nil $cons)
   (format-args "Theorem {}_list_sub : forall t :e Lean_List {}, t :e {} 0.
claim H0: 0 :e {}z :e 1 | Lean_List_nil_node {} :e {} 0{}.
{} apply SepI 1 (fun z => Lean_List_nil_node {} :e {} 0) 0 In_0_1.
  rewrite <- {}_nil_eq. exact {}_typed. {}
claim H1: 0 :e (Pi_ x0 :e {}, (Pi_ x1 :e Lean_List {}, (Pi_ y1 :e {}z :e 1 | x1 :e {} 0{}, {}z :e 1 | Lean_List_cons_node {} x0 x1 :e {} 0{}))).
{} apply Pi_0_In. let x0. assume Hx0: x0 :e {}.
  prove 0 :e (Pi_ x1 :e Lean_List {}, (Pi_ y1 :e {}z :e 1 | x1 :e {} 0{}, {}z :e 1 | Lean_List_cons_node {} x0 x1 :e {} 0{})).
  apply Pi_0_In. let x1. assume Hx1.
  prove 0 :e (Pi_ y1 :e {}z :e 1 | x1 :e {} 0{}, {}z :e 1 | Lean_List_cons_node {} x0 x1 :e {} 0{}).
  apply Pi_0_In. let y1. assume Hy1: y1 :e {}z :e 1 | x1 :e {} 0{}.
  prove 0 :e {}z :e 1 | Lean_List_cons_node {} x0 x1 :e {} 0{}.
  apply SepI 1 (fun z => Lean_List_cons_node {} x0 x1 :e {} 0) 0 In_0_1.
  rewrite <- {}_cons_eq x0 x1.
  exact {}_typed x0 Hx0 x1 (SepE2 1 (fun z => x1 :e {} 0) y1 Hy1). {}
let t. assume Ht: t :e Lean_List {}.
exact SepE2 1 (fun z => t :e {} 0) (Lean_List_rec {} 0 0 t) (Lean_List_rec_type {} (fun t => {}z :e 1 | t :e {} 0{}) 0 H0 0 H1 t Ht).
Qed.

" ($B $E $B "{" $E $B "}" "{" $E $B $B $nil "}"
   $E $E "{" $B "}" "{" $E $B "}"
   "{" $E
   $E "{" $B "}" "{" $E $B "}"
   "{" $B "}" "{" $E $B "}"
   "{" $B "}"
   "{" $E $B "}"
   $E $B $B $cons $B "}"
   $E $B $E $E "{" $B "}")))

(= (ftype $n) (if (== $n 0) "set" (format-args "set -> {}" ((ftype (- $n 1))))))
(= (vfield-proof $B $f $j)
   (if (== (field-code $f) 0) (format-args "({}_list_sub x{} H{})" ($B $j $j)) (format-args "H{}" ($j))))
(= (vbinders $E $fs $j $n)
   (if (>= $j $n) "" (format-args "forall x{} :e {}, {}" ($j (vfield-type $E (nth $fs $j)) (vbinders $E $fs (+ $j 1) $n)))))
(= (vintros $E $fs $j $n)
   (if (>= $j $n) "" (format-args "let x{}. assume H{}: x{} :e {}. {}" ($j $j $j (vfield-type $E (nth $fs $j)) (vintros $E $fs (+ $j 1) $n)))))
(= (vtyped-args $B $fs $j $n)
   (if (>= $j $n) "" (format-args " x{} {}{}" ($j (vfield-proof $B (nth $fs $j) $j) (vtyped-args $B $fs (+ $j 1) $n)))))
(= (view-node $V $n) (if (== $n 0) (format-args "{}_node" ($V)) (format-args "({}_node {})" ($V (xs-text $n)))))

(= (view-ctor-text $E $B $bc)
   (let* (($V (egal (lean-ctor-name $bc))) ($bn (egal (ctor-name $bc))) ($fs (ctor-fields $bc)) ($n (length-of $fs)))
     (format-args "Definition {}_node : {} := {}.
Theorem {}_typed : {}{} :e {}.
{}exact {}_typed{}.
Qed.

" ($V (ftype $n) (if (== $n 0) (format-args "{}_node" ($bn)) (format-args "fun {} => {}_node {}" ((xs-text $n) $bn (xs-text $n))))
   $V (vbinders $E $fs 0 $n) (view-node $V $n) $E (vintros $E $fs 0 $n) $bn (vtyped-args $B $fs 0 $n)))))

(= (motive-text $E)
   (format-args "Definition {}_motive : (set -> set) -> set -> set -> set := fun C i t => if i = 1 then C t else 1.
Theorem {}_motive_main : forall C:set -> set, forall t, {}_motive C 1 t = C t.
let C t. claim L: 1 = 1. {} reflexivity. {} exact If_i_1 (1 = 1) (C t) 1 L.
Qed.
Theorem {}_motive_other : forall C:set -> set, forall t, {}_motive C 0 t = 1.
let C t. exact If_i_0 (0 = 1) (C t) 1 neq_0_1.
Qed.

" ($E $E $E "{" "}" $E $E)))

; A main constructor's method: its fields, then one unused result per container field.
(= (lam-fields $B $fs $j $n $i)
   (if (< $j $n) (format-args "(fun x{} :e {} => {})" ($j (bfield-type $B (nth $fs $j)) (lam-fields $B $fs (+ $j 1) $n $i)))
       (lam-ihs $fs 0 $n $i)))
(= (lam-ihs $fs $j $n $i)
   (if (>= $j $n) (if (== $n 0) (format-args "h{}" ($i)) (format-args "(h{} {})" ($i (xs-text $n))))
       (if (== (field-code (nth $fs $j)) None) (lam-ihs $fs (+ $j 1) $n $i)
           (format-args "(fun y{} :e 1 => {})" ($j (lam-ihs $fs (+ $j 1) $n $i))))))
(= (method-of $B $bc $i) (let $fs (ctor-fields $bc) (lam-fields $B $fs 0 (length-of $fs) $i)))
(= (methods-text-of $B $bcs $mains $i)
   (if (== $bcs ()) ""
       (if (== (ctor-result (car-atom $bcs)) ((code 0)))
           (format-args " 0{}" ((methods-text-of $B (cdr-atom $bcs) $mains $i)))
           (format-args " {}{}" ((method-of $B (car-atom $bcs) $i) (methods-text-of $B (cdr-atom $bcs) $mains (+ $i 1)))))))
(= (hs-text $m) (join " " (vars-of $m "h")))
(= (view-rec-def $E $B $bcs $mains)
   (let $m (length-of $mains)
     (format-args "Definition {}_rec : {} := fun {} t => {}_rec{} t.

" ($E (ftype (+ $m 1)) (hs-text $m) $B (methods-text-of $B $bcs $mains 0)))))

(= (hs-from $k $n) (if (>= $k $n) () (cons-atom (format-args "h{}" ($k)) (hs-from (+ $k 1) $n))))
(= (rec-container-text $E $B $nil $cons $nb)
   (let* (($hs (join " " (hs-from 2 $nb))) ($R (format-args "{}_rec 0 0 {}" ($B $hs))))
     (format-args "Theorem {}_rec_container : forall {}, forall t :e {} 0, {} t = 0.
let {}.
claim H0: 0 :e {}z :e 1 | {} (Lean_List_nil_node {}) = 0{}.
{} apply SepI 1 (fun z => {} (Lean_List_nil_node {}) = 0) 0 In_0_1.
  rewrite <- {}_nil_eq. exact {}_iota0 0 0 {}. {}
claim H1: 0 :e (Pi_ x0 :e {}, (Pi_ x1 :e Lean_List {}, (Pi_ y1 :e {}z :e 1 | {} x1 = 0{}, {}z :e 1 | {} (Lean_List_cons_node {} x0 x1) = 0{}))).
{} apply Pi_0_In. let x0. assume Hx0: x0 :e {}.
  prove 0 :e (Pi_ x1 :e Lean_List {}, (Pi_ y1 :e {}z :e 1 | {} x1 = 0{}, {}z :e 1 | {} (Lean_List_cons_node {} x0 x1) = 0{})).
  apply Pi_0_In. let x1. assume Hx1: x1 :e Lean_List {}.
  prove 0 :e (Pi_ y1 :e {}z :e 1 | {} x1 = 0{}, {}z :e 1 | {} (Lean_List_cons_node {} x0 x1) = 0{}).
  apply Pi_0_In. let y1. assume Hy1.
  prove 0 :e {}z :e 1 | {} (Lean_List_cons_node {} x0 x1) = 0{}.
  apply SepI 1 (fun z => {} (Lean_List_cons_node {} x0 x1) = 0) 0 In_0_1.
  rewrite <- {}_cons_eq x0 x1.
  rewrite {}_iota1 0 0 {} x0 Hx0 x1 ({}_list_sub x1 Hx1).
  rewrite ap_const_0 x0. rewrite ap_const_0 x1. rewrite ap_const_0 ({} x0).
  exact ap_const_0 ({} x1). {}
let t. assume Ht: t :e {} 0.
claim Lt: t :e Lean_List {}. {} exact {}_sub_list t Ht. {}
exact SepE2 1 (fun z => {} t = 0) (Lean_List_rec {} 0 0 t) (Lean_List_rec_type {} (fun t => {}z :e 1 | {} t = 0{}) 0 H0 0 H1 t Lt).
Qed.

" ($B $hs $B $R
   $hs
   "{" $R $E "}"
   "{" $R $E $B $B $hs "}"
   $E $E "{" $R "}" "{" $R $E "}"
   "{" $E
   $E "{" $R "}" "{" $R $E "}"
   $E
   "{" $R "}" "{" $R $E "}"
   "{" $R $E "}"
   $R $E $B $B $hs $B $R $R "}"
   $B $E "{" $B "}"
   $R $E $E "{" $R "}"))))

; Lean's iota for main constructor i (block constructor k).
(= (main-only $bcs)
   (if (== $bcs ()) ()
       (if (== (ctor-result (car-atom $bcs)) ((code 0))) (main-only (cdr-atom $bcs))
           (cons-atom (car-atom $bcs) (main-only (cdr-atom $bcs))))))
(= (iota-arg $B $fs $j)
   (if (== (field-code (nth $fs $j)) 0) (format-args "x{} L{}" ($j $j)) (format-args "x{} H{}" ($j $j))))
(= (iota-args $B $fs $j $n) (if (>= $j $n) "" (format-args " {}{}" ((iota-arg $B $fs $j) (iota-args $B $fs (+ $j 1) $n)))))
(= (container-claims $B $fs $j $n)
   (if (>= $j $n) ""
       (format-args "{}{}"
         ((if (== (field-code (nth $fs $j)) 0) (format-args "claim L{}: x{} :e {} 0. {} exact {}_list_sub x{} H{}. {}
" ($j $j $B "{" $B $j $j "}")) "")
          (container-claims $B $fs (+ $j 1) $n)))))
(= (container-rewrites $B $ms $fs $j $n)
   (if (>= $j $n) ""
       (format-args "{}{}"
         ((if (== (field-code (nth $fs $j)) 0) (format-args "rewrite {}_rec_container{} x{} L{}.
" ($B $ms $j $j)) "")
          (container-rewrites $B $ms $fs (+ $j 1) $n)))))
(= (beta-lines-f $B $fs $j $n $i)
   (if (< $j $n)
       (format-args "rewrite beta {} (fun x{} => {}) x{} {}.
{}" ((bfield-type $B (nth $fs $j)) $j (lam-fields $B $fs (+ $j 1) $n $i) $j
     (if (== (field-code (nth $fs $j)) 0) (format-args "L{}" ($j)) (format-args "H{}" ($j)))
     (beta-lines-f $B $fs (+ $j 1) $n $i)))
       (beta-lines-ih $fs 0 $n $i)))
(= (beta-lines-ih $fs $j $n $i)
   (if (>= $j $n) ""
       (if (== (field-code (nth $fs $j)) None) (beta-lines-ih $fs (+ $j 1) $n $i)
           (format-args "rewrite beta 1 (fun y{} => {}) 0 In_0_1.
{}" ($j (lam-ihs $fs (+ $j 1) $n $i) (beta-lines-ih $fs (+ $j 1) $n $i))))))

(= (view-iota $E $B $bcs $mains $bc $k $i)
   (let* (($V (egal (lean-ctor-name $bc))) ($bn (egal (ctor-name $bc))) ($fs (ctor-fields $bc)) ($n (length-of $fs))
          ($m (length-of $mains)) ($ms (methods-text-of $B $bcs $mains 0))
          ($mms (methods-text-of $B (main-only $bcs) $mains 0)))
     (format-args "Theorem {}_iota{} : forall {}, {}{}_rec {} {} = {}.
let {}. {}
{}prove {}_rec{} {} = {}.
rewrite {}_iota{}{}{}.
{}{}reflexivity.
Qed.

" ($E $i (hs-text $m) (vbinders $E $fs 0 $n) $E (hs-text $m) (view-node $V $n) (if (== $n 0) (format-args "h{}" ($i)) (format-args "(h{} {})" ($i (xs-text $n))))
   (hs-text $m) (vintros $E $fs 0 $n)
   (container-claims $B $fs 0 $n)
   $B $ms (node-at $bn $n) (if (== $n 0) (format-args "h{}" ($i)) (format-args "(h{} {})" ($i (xs-text $n))))
   $B $k $ms (iota-args $B $fs 0 $n)
   (container-rewrites $B $mms $fs 0 $n)
   (beta-lines-f $B $fs 0 $n $i)))))
(= (view-iotas $E $B $bcs $mains $i)
   (if (== $mains ()) ()
       (let $mm (car-atom $mains)
         (cons-atom (view-iota $E $B $bcs (cons-atom $mm (cdr-atom $mains)) (mc-ctor $mm) (mc-index $mm) $i)
                    (view-iotas-rest $E $B $bcs $mains (cdr-atom $mains) (+ $i 1))))))
(= (view-iotas-rest $E $B $bcs $all $rest $i)
   (if (== $rest ()) ()
       (let $mm (car-atom $rest)
         (cons-atom (view-iota $E $B $bcs $all (mc-ctor $mm) (mc-index $mm) $i)
                    (view-iotas-rest $E $B $bcs $all (cdr-atom $rest) (+ $i 1))))))

; The typing of the main member's case analysis, through the block's recursor
; at the motive that is C on the main member and 1 elsewhere.
(= (vpi-from $E $V $fs $j $n)
   (if (>= $j $n) (format-args "C {}" ((view-node $V $n)))
       (format-args "(Pi_ x{} :e {}, {})" ($j (vfield-type $E (nth $fs $j)) (vpi-from $E $V $fs (+ $j 1) $n)))))
(= (view-ap-chain $E $B $V $fs $j $i)
   (if (== $j 0) (format-args "Hh{}" ($i))
       (let $p (- $j 1)
         (format-args "(ap_Pi {} (fun x{} => {}) {} x{} {} {})"
           ((vfield-type $E (nth $fs $p)) $p (vpi-from $E $V $fs $j (length-of $fs))
            (if (== $p 0) (format-args "h{}" ($i)) (format-args "(h{} {})" ($i (xs-text $p))))
            $p (view-ap-chain $E $B $V $fs $p $i)
            (if (== (field-code (nth $fs $p)) 0) (format-args "({}_sub_list x{} Hx{})" ($B $p $p)) (format-args "Hx{}" ($p))))))))
(= (red-ih-pi $fs $j $n $node)
   (if (>= $j $n) (format-args "C {}" ($node))
       (if (== (field-code (nth $fs $j)) None) (red-ih-pi $fs (+ $j 1) $n $node)
           (format-args "(Pi_ y{} :e 1, {})" ($j (red-ih-pi $fs (+ $j 1) $n $node))))))
(= (lam-steps $E $B $fs $j $n $i $node)
   (if (< $j $n)
       (format-args "apply lam_Pi {} (fun x{} => {}) (fun x{} => {}).
  let x{}. assume Hx{}: x{} :e {}.
  prove {} :e {}.
  {}" ((bfield-type $B (nth $fs $j)) $j (pi-from typ $E $B $fs (+ $j 1) $n 1 $node) $j (lam-fields $B $fs (+ $j 1) $n $i)
       $j $j $j (bfield-type $B (nth $fs $j))
       (lam-fields $B $fs (+ $j 1) $n $i) (pi-from typ $E $B $fs (+ $j 1) $n 1 $node)
       (lam-steps $E $B $fs (+ $j 1) $n $i $node)))
       (format-args "{}rewrite {}_motive_main C {}.
  {}" ((view-ih-rewrites $E $fs 0 $n) $E $node (ih-lam-steps $fs 0 $n $i $node)))))
(= (view-ih-rewrites $E $fs $j $n)
   (if (>= $j $n) ""
       (format-args "{}{}"
         ((if (== (field-code (nth $fs $j)) 0) (format-args "rewrite {}_motive_other C x{}. " ($E $j)) "")
          (view-ih-rewrites $E $fs (+ $j 1) $n)))))
(= (ih-lam-steps $fs $j $n $i $node)
   (if (>= $j $n) ""
       (if (== (field-code (nth $fs $j)) None) (ih-lam-steps $fs (+ $j 1) $n $i $node)
           (format-args "apply lam_Pi 1 (fun y{} => {}) (fun y{} => {}).
  let y{}. assume Hy{}: y{} :e 1.
  prove {} :e {}.
  {}" ($j (red-ih-pi $fs (+ $j 1) $n $node) $j (lam-ihs $fs (+ $j 1) $n $i)
       $j $j $j (lam-ihs $fs (+ $j 1) $n $i) (red-ih-pi $fs (+ $j 1) $n $node)
       (ih-lam-steps $fs (+ $j 1) $n $i $node))))))

(= (type-claim $E $B $bc $k $i)
   (let* (($fs (ctor-fields $bc)) ($n (length-of $fs)) ($bn (egal (ctor-name $bc))) ($node (node-at $bn $n)))
     (if (== (ctor-result $bc) ((code 0)))
         (format-args "claim P{}: 0 :e {}.
{} {}prove 0 :e {}.
  rewrite {}_motive_other C {}. exact In_0_1. {}
" ($k (pi-from typ $E $B $fs 0 $n 0 $node) "{" (zero-steps typ $E $B $fs 0 $n 0 $node) (mot typ $E $B 0 $node) $E $node "}"))
         (let $V (egal (lean-ctor-name $bc))
           (format-args "claim P{}: {} :e {}.
{} {}exact {}. {}
" ($k (method-of $B $bc $i) (pi-from typ $E $B $fs 0 $n 1 $node) "{"
   (lam-steps $E $B $fs 0 $n $i $node) (view-ap-chain $E $B $V $fs $n $i) "}"))))))
(= (type-claims $E $B $bcs $k $i)
   (if (== $bcs ()) ""
       (let $bc (car-atom $bcs)
         (if (== (ctor-result $bc) ((code 0)))
             (format-args "{}{}" ((type-claim $E $B $bc $k $i) (type-claims $E $B (cdr-atom $bcs) (+ $k 1) $i)))
             (format-args "{}{}" ((type-claim $E $B $bc $k $i) (type-claims $E $B (cdr-atom $bcs) (+ $k 1) (+ $i 1))))))))
(= (type-args $B $bcs $k $i)
   (if (== $bcs ()) ""
       (let $bc (car-atom $bcs)
         (if (== (ctor-result $bc) ((code 0)))
             (format-args " 0 P{}{}" ($k (type-args $B (cdr-atom $bcs) (+ $k 1) $i)))
             (format-args " {} P{}{}" ((method-of $B $bc $i) $k (type-args $B (cdr-atom $bcs) (+ $k 1) (+ $i 1))))))))
(= (h-hyps $E $mains $i)
   (if (== $mains ()) ""
       (let* (($bc (mc-ctor (car-atom $mains))) ($fs (ctor-fields $bc)) ($V (egal (lean-ctor-name $bc))))
         (format-args "forall h{} :e {}, {}" ($i (vpi-from $E $V $fs 0 (length-of $fs)) (h-hyps $E (cdr-atom $mains) (+ $i 1)))))))
;  The main member's case analysis as a proposition: P holds of every element
; when it holds of each constructor's node (the view's recursor typing at
; the motive {z :e 1 | P t}, all methods 0).
(= (vcases-chain $E $V $fs $j $n)
   (if (>= $j $n) (pred-at (view-node $V $n))
       (format-args "(Pi_ x{} :e {}, {})" ($j (vfield-type $E (nth $fs $j)) (vcases-chain $E $V $fs (+ $j 1) $n)))))
(= (vcases-method $E $bc $i)
   (let* (($fs (ctor-fields $bc)) ($n (length-of $fs)) ($V (egal (lean-ctor-name $bc))) ($js (range-from 0 $n)))
     (format-args "claim M{}: 0 :e {}.
{ {}exact SepI 1 (fun z => P {}) 0 In_0_1 (H{}{}). }
"
       ($i (vcases-chain $E $V $fs 0 $n)
        (join "" (map-atom $js $j
          (format-args "apply Pi_0_In. let x{}. assume Hx{}: x{} :e {}.
  prove 0 :e {}.
  " ($j $j $j (vfield-type $E (nth $fs $j)) (vcases-chain $E $V $fs (+ $j 1) $n)))))
        (view-node $V $n) $i (join "" (map-atom $js $j (format-args " x{} Hx{}" ($j $j))))))))
(= (vcases-hyp $E $bc)
   (let* (($fs (ctor-fields $bc)) ($n (length-of $fs)) ($V (egal (lean-ctor-name $bc))) ($js (range-from 0 $n)))
     (format-args "({}P {})" ((join "" (map-atom $js $j (format-args "forall x{} :e {}, " ($j (vfield-type $E (nth $fs $j)))))) (view-node $V $n)))))
(= (view-cases $F)
   (let* (($E (egal $F)) ($mains (block-main-ctors $F)) ($m (length-of $mains)) ($is (range-from 0 $m)))
     (format-args "Theorem {}_cases : forall P:set -> prop, {}forall t :e {}, P t.
let P.{}
{}let t. assume Ht: t :e {}.
exact SepE2 1 (fun z => P t) ({}_rec{} t) ({}_rec_type (fun t => {}z :e 1 | P t{}){} t Ht).
Qed.
"
       ($E (join "" (map-atom $is $i (format-args "{} -> " ((vcases-hyp $E (mc-ctor (nth $mains $i))))))) $E
        (join "" (map-atom $is $i (format-args " assume H{}." ($i))))
        (join "" (map-atom $is $i (vcases-method $E (mc-ctor (nth $mains $i)) $i)))
        $E $E (join "" (map-atom $is $i " 0")) $E "{" "}" (join "" (map-atom $is $i (format-args " 0 M{}" ($i))))))))

;  The members of a mutual block (no container member): each member is the
; block at its code, as a family over its own indices and as a proposition.
(= (mutual-view-section $F)
   (let* (($B (egal (bk $F))) ($ms (block-members $F)))
     (join "" (map-atom $ms $m (mutual-member-text $F $B $m)))))
(= (mutual-member-text $F $B $m)
   (let* (($E (egal (member-head $m))) ($P (prop-type-name (bk $F)))
          ($c (tag-code $F (member-tag $m))) ($n (length-of (member-indices $m))))
     (if (== $n 0)
         (format-args "(** {}: the member of its mutual block at code {}. **)
Definition {} : set := {} {}.
Definition {}_Prop : set := {} {}.

" ((member-head $m) $c $E $B $c $E $P $c))
         (format-args "(** {}: the member of its mutual block at code {}, over its index. **)
Definition {} : set -> set := fun a => {} (setsum {} a).
Definition {}_Prop : set -> set := fun a => {} (setsum {} a).

" ((member-head $m) $c $E $B $c $E $P $c)))))
(= (member-head $m) (case (member-type $m) (((const $c) $c) ($_ None))))

(= (h-intros $m) (join " " (let $is (range-from 0 $m) (map-atom $is $i (format-args "let h{}. assume Hh{}." ($i $i))))))

(= (view-rec-type $E $B $bcs $mains $nb)
   (let* (($m (length-of $mains)) ($ms (methods-text-of $B $bcs $mains 0)))
     (format-args "Theorem {}_rec_type : forall C:set -> set, {}forall t :e {}, {}_rec {} t :e C t.
let C. {}
{}let t. assume Ht: t :e {}.
claim L: {}_rec{} t :e {}_motive C 1 t.
{} exact {}_rec_type ({}_motive C){} 1 t Ht. {}
rewrite <- {}_motive_main C t. exact L.
Qed.

Theorem {}_type_In : forall u, nat_p u -> {} :e LeanUniv u.
let u. assume Hu: nat_p u. exact {}_type_In u Hu 1.
Qed.
" ($E (h-hyps $E $mains 0) $E $E (hs-text $m)
   (h-intros $m)
   (type-claims $E $B $bcs 0 0) $E
   $B $ms $E
   "{" $B $E (type-args $B $bcs 0 0) "}"
   $E
   $E $E $B))))
