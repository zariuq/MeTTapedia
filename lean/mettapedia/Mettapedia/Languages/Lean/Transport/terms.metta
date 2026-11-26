; Lean's statements and proof terms as MeTTa holds them (the transport export), read for mining.
; A reference to an enclosing binder becomes its de Bruijn index, so a piece of a proof has one
; form wherever it stands: (var x) -> (dbv K), (phyp h ARGS) -> (dbh K ARGS).  Binder nodes keep
; their name as an annotation.  Names that no binder of the piece encloses stay as they are.

(= (term:h1 $a) (car-atom (cdr-atom $a)))
(= (term:h2 $a) (car-atom (cdr-atom (cdr-atom $a))))
(= (term:h3 $a) (car-atom (cdr-atom (cdr-atom (cdr-atom $a)))))
(= (term:expr? $e) (if (== (get-metatype $e) Expression) (not (== $e ())) False))
(= (term:binder? $b) (if (== $b plam) True (if (== $b lam) True (== $b pi))))
(= (term:proof-head? $p)
   (if (== $p pcite) True (if (== $p pctor) True (if (== $p prec) True (if (== $p pquot) True
   (if (== $p pproj) True (if (== $p plam) True (if (== $p phave) True (if (== $p dbh) True (== $p phyp))))))))))
(= (term:index $ix_x $ix_env $ix_k)
   (if (== $ix_env ()) None
       (if (== (car-atom $ix_env) $ix_x) $ix_k (term:index $ix_x (cdr-atom $ix_env) (+ $ix_k 1)))))
(= (term:nth $nt_xs $nt_k) (if (== $nt_k 0) (car-atom $nt_xs) (term:nth (cdr-atom $nt_xs) (- $nt_k 1))))
(= (term:concat $cc_a $cc_b)
   (if (== $cc_a ()) $cc_b (cons-atom (car-atom $cc_a) (term:concat (cdr-atom $cc_a) $cc_b))))
(= (term:length $ln_xs) (if (== $ln_xs ()) 0 (+ 1 (term:length (cdr-atom $ln_xs)))))

; to de Bruijn form, under ENV (innermost binder first)
(= (term:db $db_t $db_env)
   (if (term:expr? $db_t)
       (let $db_h (car-atom $db_t)
         (if (== $db_h var)
             (let $db_k (term:index (term:h1 $db_t) $db_env 0) (if (== $db_k None) $db_t (dbv $db_k)))
         (if (== $db_h phyp)
             (let* (($db_k2 (term:index (term:h1 $db_t) $db_env 0)) ($db_as (term:db-list (term:h2 $db_t) $db_env)))
               (if (== $db_k2 None) (phyp (term:h1 $db_t) $db_as) (dbh $db_k2 $db_as)))
         (if (term:binder? $db_h)
             (let* (($db_x (term:h1 $db_t)) ($db_ty (term:db (term:h2 $db_t) $db_env))
                    ($db_b (term:db (term:h3 $db_t) (cons-atom $db_x $db_env))))
               (cons-atom $db_h (cons-atom $db_x (cons-atom $db_ty (cons-atom $db_b ())))))
             (term:db-list $db_t $db_env)))))
       $db_t))
(= (term:db-list $dl_xs $dl_env)
   (if (== $dl_xs ()) () (cons-atom (term:db (car-atom $dl_xs) $dl_env) (term:db-list (cdr-atom $dl_xs) $dl_env))))

; back to names, under ENV
(= (term:named $nm_t $nm_env)
   (if (term:expr? $nm_t)
       (let $nm_h (car-atom $nm_t)
         (if (== $nm_h dbv) (var (term:nth $nm_env (term:h1 $nm_t)))
         (if (== $nm_h dbh) (phyp (term:nth $nm_env (term:h1 $nm_t)) (term:named-list (term:h2 $nm_t) $nm_env))
         (if (term:binder? $nm_h)
             (let* (($nm_x (term:h1 $nm_t)) ($nm_ty (term:named (term:h2 $nm_t) $nm_env))
                    ($nm_b (term:named (term:h3 $nm_t) (cons-atom $nm_x $nm_env))))
               (cons-atom $nm_h (cons-atom $nm_x (cons-atom $nm_ty (cons-atom $nm_b ())))))
             (term:named-list $nm_t $nm_env)))))
       $nm_t))
(= (term:named-list $nl_xs $nl_env)
   (if (== $nl_xs ()) () (cons-atom (term:named (car-atom $nl_xs) $nl_env) (term:named-list (cdr-atom $nl_xs) $nl_env))))

; size: the number of expression nodes
(= (term:size $sz_t) (if (term:expr? $sz_t) (+ 1 (term:size-list $sz_t)) 0))
(= (term:size-list $sl_xs) (if (== $sl_xs ()) 0 (+ (term:size (car-atom $sl_xs)) (term:size-list (cdr-atom $sl_xs)))))

; Does T refer to one of the D binders just above it (index in [CUT, CUT+D))?
(= (term:captures? $cp_t $cp_d $cp_cut)
   (if (term:expr? $cp_t)
       (let $cp_h (car-atom $cp_t)
         (if (or (== $cp_h dbv) (== $cp_h dbh))
             (let $cp_k (term:h1 $cp_t)
               (if (and (>= $cp_k $cp_cut) (< $cp_k (+ $cp_cut $cp_d))) True
                   (if (== $cp_h dbh) (term:captures-list? (term:h2 $cp_t) $cp_d $cp_cut) False)))
         (if (term:binder? $cp_h)
             (if (term:captures? (term:h2 $cp_t) $cp_d $cp_cut) True (term:captures? (term:h3 $cp_t) $cp_d (+ $cp_cut 1)))
             (term:captures-list? $cp_t $cp_d $cp_cut))))
       False))
(= (term:captures-list? $cl_xs $cl_d $cl_cut)
   (if (== $cl_xs ()) False (if (term:captures? (car-atom $cl_xs) $cl_d $cl_cut) True (term:captures-list? (cdr-atom $cl_xs) $cl_d $cl_cut))))

; T moved out of D binders: references past them drop by D
(= (term:down $dn_t $dn_d $dn_cut)
   (if (term:expr? $dn_t)
       (let $dn_h (car-atom $dn_t)
         (if (== $dn_h dbv)
             (let $dn_k (term:h1 $dn_t) (if (>= $dn_k $dn_cut) (dbv (- $dn_k $dn_d)) $dn_t))
         (if (== $dn_h dbh)
             (let* (($dn_k2 (term:h1 $dn_t)) ($dn_as (term:down-list (term:h2 $dn_t) $dn_d $dn_cut)))
               (if (>= $dn_k2 $dn_cut) (dbh (- $dn_k2 $dn_d) $dn_as) (dbh $dn_k2 $dn_as)))
         (if (term:binder? $dn_h)
             (cons-atom $dn_h (cons-atom (term:h1 $dn_t) (cons-atom (term:down (term:h2 $dn_t) $dn_d $dn_cut)
               (cons-atom (term:down (term:h3 $dn_t) $dn_d (+ $dn_cut 1)) ()))))
             (term:down-list $dn_t $dn_d $dn_cut)))))
       $dn_t))
(= (term:down-list $dw_xs $dw_d $dw_cut)
   (if (== $dw_xs ()) () (cons-atom (term:down (car-atom $dw_xs) $dw_d $dw_cut) (term:down-list (cdr-atom $dw_xs) $dw_d $dw_cut))))

; the theorems in dependency order (the export's TransportOrder row, as one list)
(= (term:order) (let $or_found (collapse (match &self (TransportOrderList $or_cs) $or_cs)) (car-atom $or_found)))
(= (term:member-of $mo_x $mo_xs) (if (== $mo_xs ()) False (if (== (car-atom $mo_xs) $mo_x) True (term:member-of $mo_x (cdr-atom $mo_xs)))))
