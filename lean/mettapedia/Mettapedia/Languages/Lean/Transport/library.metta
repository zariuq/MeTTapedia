; A library of lemmas from the grammar's posterior (after terms.metta and grammar.metta), written
; for Lean, and every proof rewritten to cite it.
;
; Which fragments become lemmas is a decision under the posterior.  A proof fragment F has mean
; customers C over the samples (its uses in the N training theorems) and an expected R uses in a new
; theorem (the posterior mean of the Pitman-Yor predictive times the fragments a theorem brings);
; each use saves the fragment's SIZE less the citation's two nodes, and the lemma costs its size
; and its parameters.  F becomes a lemma when, over the training theorems and the TOTAL - N others
; the library serves, the expected saving exceeds the cost.
;
; A lemma's parameters: one per hole, applied to the bound variables of the fragment above it (a
; higher-order pattern), one per variable the fragment refers to outside itself, and one universe
; per level hole or level name.  Lean infers the statement; a lemma it refuses is left out.
; A lemma's name is its fragment's content: lemma_ and the first hexadecimal digits of its key.
;
; Rewriting with the library is exact: for every proof, the smallest proof that cites the lemmas,
; by a dynamic program over the proof tree (at each proof node, the least of the node as it is,
; its children rewritten, and each lemma that fits there with its arguments rewritten).
;
;   (LibCandidate KEY TERM SIZE MEAN-CUSTOMERS MEAN-USES-PER-THEOREM)   from a sampler run
;   (LibPosterior D N)                                        the proof kind's d, training size
;   !(lib:choose TOTAL)      the lemmas worth having for TOTAL theorems: (LibLemma NAME TERM)
;   !(lib:rewrite-all ORDER) (RewrittenProof c p), (MinedLemma NAME LEVELS VALUE), (MinedBefore ..)

;;; names by content

(= (lib:prefix $px_cs $px_k $px_acc) (if (== $px_k 0) $px_acc (lib:prefix (cdr-atom $px_cs) (- $px_k 1) (atom_concat $px_acc (car-atom $px_cs)))))
(= (lib:name-of $nm_key) (lib:prefix (atom_chars $nm_key) 10 lemma_))

;;; the decision

; The saving of one citation of a fragment, exactly: its own nodes, less the citation's two, a
; level argument per universe, an argument per variable it refers to outside itself, and for each
; hole the abstraction over each of its binders above it (one node and the binder's type; a type
; that is itself a hole counts one).  The holes' contents stand in the proof and in the citation
; alike.
(= (lib:overhead $ov_t $ov_st $ov_d $ov_acc)
   (if (term:expr? $ov_t)
       (let $ov_h (car-atom $ov_t)
         (if (== $ov_h hole)
             (if (== (term:h1 $ov_t) level) (+ $ov_acc 1) (+ $ov_acc (lib:stack-cost $ov_st 0)))
         (if (if (== (get-metatype $ov_h) Symbol) (term:binder? $ov_h) False)
             (let $ov_a1 (lib:overhead (term:h2 $ov_t) $ov_st $ov_d $ov_acc)
               (lib:overhead (term:h3 $ov_t) (cons-atom (lib:type-size (term:h2 $ov_t)) $ov_st) (+ $ov_d 1) $ov_a1))
             (lib:overhead-list $ov_t $ov_st $ov_d $ov_acc))))
       $ov_acc))
(= (lib:overhead-list $ol_xs $ol_st $ol_d $ol_acc)
   (if (== $ol_xs ()) $ol_acc (lib:overhead-list (cdr-atom $ol_xs) $ol_st $ol_d (lib:overhead (car-atom $ol_xs) $ol_st $ol_d $ol_acc))))
(= (lib:type-size $ts_t) (if (if (term:expr? $ts_t) (== (car-atom $ts_t) hole) False) 1 (term:size $ts_t)))
(= (lib:stack-cost $sc_st $sc_acc) (if (== $sc_st ()) $sc_acc (lib:stack-cost (cdr-atom $sc_st) (+ $sc_acc (+ 1 (car-atom $sc_st))))))
(= (lib:saving $sv_term $sv_size)
   (let* (((pr $sv_body (ws $sv_hs $sv_fs $sv_ls $sv_n)) (lib:nm $sv_term () (ws () () () 1))))
     (- (- (- $sv_size 2) (* 2 (term:length $sv_ls))) (+ (term:length $sv_fs) (lib:overhead $sv_term () 0 0)))))
; the lemma's own size: its value as it is written, a function of its parameters, each a binder and
; its type
(= (lib:cost $cs_term)
   (let* (((pr $cs_body (ws $cs_hs $cs_fs $cs_ls $cs_n)) (lib:nm $cs_term () (ws () () () 1))))
     (+ (term:size $cs_body) (lib:params-size (term:concat $cs_hs (lib:frees-in-order $cs_fs ())) 0))))
; the utility, as a number: (training uses + (TOTAL - N) expected uses per theorem) SAVING - COST
(= (lib:utility $ut_h $ut_d $ut_n $ut_term $ut_size $ut_c $ut_r)
   (let* (($ut_uses (+ $ut_c (* (- $ut_h $ut_n) $ut_r)))
          ($ut_save (lib:saving $ut_term $ut_size)))
     (if (> $ut_save 0) (- (* $ut_uses $ut_save) (lib:cost $ut_term)) -1)))
; a lemma, filed also under the rule of its root (LibLemmaAt RK NAME TERM): it can fit only at a
; node whose own rule is the same (holes stand for expressions, binder names are _ on both sides)
(= (lib:add-lemma $al_n $al_t)
   (let* (($al_rk (tsg:root-rk $al_t proof)) ($al_a (add-atom &self (LibLemma $al_n $al_t))))
     (add-atom &self (LibLemmaAt $al_rk $al_n $al_t))))
(= (lib:choose $ch_h)
   (let* (($ch_sentinel (add-atom &self (LibLemmaAt none none none)))
          (($ch_d $ch_n) (car-atom (collapse (match &self (LibPosterior $ch_d0 $ch_n0) ($ch_d0 $ch_n0)))))
          ($ch_cs (collapse (match &self (LibCandidate $ch_k $ch_t $ch_s $ch_c $ch_u) ($ch_k $ch_t $ch_s $ch_c $ch_u))))
          ($ch_x (lib:choose-each $ch_cs $ch_h $ch_d $ch_n))
          ($ch_m (term:length (collapse (match &self (LibLemma $ch_nm $ch_tt) $ch_nm)))))
     (println! (lib-chosen (lemmas $ch_m) (of (term:length $ch_cs))))))
(= (lib:choose-each $ce_cs $ce_h $ce_d $ce_n)
   (if (== $ce_cs ()) done
       (let* ((($ce_k $ce_t $ce_s $ce_c $ce_u) (car-atom $ce_cs))
              ($ce_v (lib:utility $ce_h $ce_d $ce_n $ce_t $ce_s $ce_c $ce_u))
              ($ce_name (lib:name-of $ce_k))
              ($ce_a (if (> $ce_v 0) (lib:add-lemma $ce_name $ce_t) done)))
         (lib:choose-each (cdr-atom $ce_cs) $ce_h $ce_d $ce_n))))

;;; matching a fragment at a proof node (de Bruijn), D the fragment's binders above, STACK their
;;; binders in the proof (innermost first): (ma HOLES FREES LEVELS), each list in reverse, or Fail

(= (lib:kind-ok? $ko_k $ko_t) (if (term:expr? $ko_t) (== (tsg:kind-of $ko_t) $ko_k) False))
(= (lib:mt $mt_p $mt_t $mt_d $mt_st $mt_acc)
   (if (== $mt_acc Fail) Fail
   (if (term:expr? $mt_p)
       (let $mt_h (car-atom $mt_p)
         (if (== $mt_h hole)
             (if (== (term:length $mt_p) 2) (lib:mt-hole (term:h1 $mt_p) $mt_t $mt_st $mt_acc)
                 (lib:mt-rhole (term:h1 $mt_p) (term:h2 $mt_p) (term:h3 $mt_p) $mt_t $mt_d $mt_st $mt_acc))
         (if (== $mt_h dbv) (lib:mt-dbv (term:h1 $mt_p) $mt_t $mt_d $mt_acc)
         (if (== $mt_h dbh) (lib:mt-dbh $mt_p $mt_t $mt_d $mt_st $mt_acc)
         (if (== $mt_h lvl) (lib:mt-lvl (term:h1 $mt_p) $mt_t $mt_acc)
         (if (if (term:expr? $mt_t) (== (term:length $mt_p) (term:length $mt_t)) False)
             (if (if (== (get-metatype $mt_h) Symbol) (term:binder? $mt_h) False)
                 (if (== $mt_h (car-atom $mt_t))
                     (let $mt_a1 (lib:mt (term:h2 $mt_p) (term:h2 $mt_t) $mt_d $mt_st $mt_acc)
                       (lib:mt (term:h3 $mt_p) (term:h3 $mt_t) (+ $mt_d 1)
                               (cons-atom (bd $mt_h (term:h1 $mt_t) (term:h2 $mt_t)) $mt_st) $mt_a1))
                     Fail)
                 (lib:mt-list $mt_p $mt_t $mt_d $mt_st $mt_acc))
             Fail))))))
       (if (== $mt_p $mt_t) $mt_acc Fail))))
(= (lib:mt-list $ml_ps $ml_ts $ml_d $ml_st $ml_acc)
   (if (== $ml_acc Fail) Fail
   (if (== $ml_ps ()) $ml_acc
       (lib:mt-list (cdr-atom $ml_ps) (cdr-atom $ml_ts) $ml_d $ml_st
                    (lib:mt (car-atom $ml_ps) (car-atom $ml_ts) $ml_d $ml_st $ml_acc)))))
(= (lib:mt-hole $mh_k $mh_t $mh_st $mh_acc)
   (let (ma $mh_hs $mh_fs $mh_ls) $mh_acc
     (if (== $mh_k level)
         (if (if (term:expr? $mh_t) (== (car-atom $mh_t) lvl) False) (ma $mh_hs $mh_fs (cons-atom (value (term:h1 $mh_t)) $mh_ls)) Fail)
         (if (lib:kind-ok? $mh_k $mh_t) (ma (cons-atom (hv $mh_k $mh_t $mh_st none) $mh_hs) $mh_fs $mh_ls) Fail))))
; A hole of a lemma stated from its occurrences, (hole KIND ID KEEP): KEEP none, its value reaches no
; binder of the fragment and is passed as it is; KEEP all, a function of the fragment's binders above
; it.  Holes with one ID hold one value.
(= (lib:mt-rhole $mr_k $mr_id $mr_keep $mr_t $mr_d $mr_st $mr_acc)
   (if (lib:kind-ok? $mr_k $mr_t)
       (let* (((ma $mr_hs $mr_fs $mr_ls) $mr_acc)
              ($mr_ok (if (== $mr_keep none) (not (term:captures? $mr_t $mr_d 0)) True)))
         (if $mr_ok
             (let* (($mr_v (if (== $mr_keep none) (term:down $mr_t $mr_d 0) $mr_t))
                    ($mr_s (if (== $mr_keep none) () $mr_st))
                    ($mr_old (lib:hole-by-id $mr_hs $mr_id)))
               (if (== $mr_old none) (ma (cons-atom (hv $mr_k $mr_v $mr_s $mr_id) $mr_hs) $mr_fs $mr_ls)
                   (if (== $mr_old $mr_v) $mr_acc Fail)))
             Fail))
       Fail))
(= (lib:hole-by-id $hb_hs $hb_id)
   (if (== $hb_hs ()) none (let (hv $hb_k $hb_v $hb_s $hb_i) (car-atom $hb_hs) (if (== $hb_i $hb_id) $hb_v (lib:hole-by-id (cdr-atom $hb_hs) $hb_id)))))
(= (lib:mt-lvl $mv_x $mv_t $mv_acc)
   (if (== (lvl $mv_x) $mv_t)
       (if (== (get-metatype $mv_x) Symbol)
           (let (ma $mv_hs $mv_fs $mv_ls) $mv_acc
             (if (term:member-of (name $mv_x) $mv_ls) $mv_acc (ma $mv_hs $mv_fs (cons-atom (name $mv_x) $mv_ls))))
           $mv_acc)
       Fail))
; a free reference of the fragment is a parameter: any value that does not reach into the fragment's
; binders, the same at every occurrence
(= (lib:free $fr_idx $fr_v $fr_acc)
   (let (ma $fr_hs $fr_fs $fr_ls) $fr_acc
     (let $fr_old (lib:lookup $fr_fs $fr_idx)
       (if (== $fr_old none) (ma $fr_hs (cons-atom (fv $fr_idx $fr_v) $fr_fs) $fr_ls)
           (if (== $fr_old $fr_v) $fr_acc Fail)))))
(= (lib:lookup $lk_fs $lk_i) (if (== $lk_fs ()) none (let (fv $lk_j $lk_v) (car-atom $lk_fs) (if (== $lk_j $lk_i) $lk_v (lib:lookup (cdr-atom $lk_fs) $lk_i)))))
(= (lib:mt-dbv $md_k $md_t $md_d $md_acc)
   (if (< $md_k $md_d)
       (if (== (dbv $md_k) $md_t) $md_acc Fail)
       (if (term:captures? $md_t $md_d 0) Fail (lib:free (- $md_k $md_d) (term:down $md_t $md_d 0) $md_acc))))
(= (lib:mt-dbh $mb_p $mb_t $mb_d $mb_st $mb_acc)
   (let* (($mb_k (term:h1 $mb_p)) ($mb_as (term:h2 $mb_p)))
     (if (if (term:expr? $mb_t) (== (car-atom $mb_t) dbh) False)
         (let $mb_k2 (term:h1 $mb_t)
           (if (< $mb_k $mb_d)
               (if (== $mb_k $mb_k2) (lib:mt $mb_as (term:h2 $mb_t) $mb_d $mb_st $mb_acc) Fail)
               (if (< $mb_k2 $mb_d) Fail
                   (lib:mt $mb_as (term:h2 $mb_t) $mb_d $mb_st (lib:free (- $mb_k $mb_d) (dbh (- $mb_k2 $mb_d) ()) $mb_acc)))))
         Fail)))

;;; writing a fragment as a lemma (named form): (pr TERM (ws HOLES FREES LEVELS NEXT)).  The binders in
;;; scope are (bv NAME TYPE), innermost first; a parameter is (hp NAME TYPE): a hole under binders is
;;; a function of them, so its type is a product over their types; an outside reference applied to
;;; K arguments is a function of K arguments of types Lean infers, (fn IDX NAME K) while naming.

(= (lib:nth $nt_xs $nt_k) (if (== $nt_k 0) (car-atom $nt_xs) (lib:nth (cdr-atom $nt_xs) (- $nt_k 1))))
(= (lib:pname $pn_p $pn_i) (parse (format-args "{}_{}" ($pn_p $pn_i))))
(= (lib:vars $vs_env $vs_acc)
   (if (== $vs_env ()) $vs_acc (let (bv $vs_x $vs_t) (car-atom $vs_env) (lib:vars (cdr-atom $vs_env) (cons-atom (var $vs_x) $vs_acc)))))
; the product over the binders in scope, innermost wrapped first, so the outermost comes first
(= (lib:pi-over $po_env $po_t) (if (== $po_env ()) $po_t (let (bv $po_x $po_ty) (car-atom $po_env) (lib:pi-over (cdr-atom $po_env) (pi $po_x $po_ty $po_t)))))
; a function of K arguments of types left to Lean
(= (lib:arrows $ar_k $ar_i) (if (== $ar_k 0) (proof) (pi (lib:pname a $ar_i) (proof) (lib:arrows (- $ar_k 1) (+ $ar_i 1)))))
(= (lib:nm $nm_p $nm_env $nm_st)
   (if (term:expr? $nm_p)
       (let $nm_h (car-atom $nm_p)
         (if (== $nm_h hole)
             (if (== (term:length $nm_p) 2) (lib:nm-hole (term:h1 $nm_p) $nm_env $nm_st)
                 (lib:nm-rhole (term:h1 $nm_p) (term:h2 $nm_p) (term:h3 $nm_p) $nm_env $nm_st))
         (if (== $nm_h dbv) (lib:nm-dbv (term:h1 $nm_p) $nm_env $nm_st)
         (if (== $nm_h dbh) (lib:nm-dbh (term:h1 $nm_p) (term:h2 $nm_p) $nm_env $nm_st)
         (if (== $nm_h lvl) (lib:nm-lvl $nm_p $nm_st)
         (if (if (== (get-metatype $nm_h) Symbol) (term:binder? $nm_h) False)
             (let* (((ws $nb_hs $nb_fs $nb_ls $nb_n) $nm_st)
                    ($nb_x (lib:pname v $nb_n))
                    ((pr $nb_T $nb_st1) (lib:nm (term:h2 $nm_p) $nm_env (ws $nb_hs $nb_fs $nb_ls (+ $nb_n 1))))
                    ((pr $nb_B $nb_st2) (lib:nm (term:h3 $nm_p) (cons-atom (bv $nb_x $nb_T) $nm_env) $nb_st1)))
               (pr (cons-atom $nm_h (cons-atom $nb_x (cons-atom $nb_T (cons-atom $nb_B ())))) $nb_st2))
             (lib:nm-list $nm_p $nm_env $nm_st)))))))
       (pr $nm_p $nm_st)))
(= (lib:nm-list $nl_xs $nl_env $nl_st)
   (if (== $nl_xs ()) (pr () $nl_st)
       (let* (((pr $nl_a $nl_st1) (lib:nm (car-atom $nl_xs) $nl_env $nl_st))
              ((pr $nl_r $nl_st2) (lib:nm-list (cdr-atom $nl_xs) $nl_env $nl_st1)))
         (pr (cons-atom $nl_a $nl_r) $nl_st2))))
(= (lib:nm-hole $nh_k $nh_env $nh_st)
   (let (ws $nh_hs $nh_fs $nh_ls $nh_n) $nh_st
     (if (== $nh_k level)
         (let $nh_u (lib:pname u $nh_n) (pr (lvl $nh_u) (ws $nh_hs $nh_fs (cons-atom $nh_u $nh_ls) (+ $nh_n 1))))
         (let* (($nh_m (lib:pname m $nh_n)) ($nh_args (lib:vars $nh_env ()))
                ($nh_ty (lib:pi-over $nh_env (proof)))
                ($nh_st2 (ws (cons-atom (hp $nh_m $nh_ty) $nh_hs) $nh_fs $nh_ls (+ $nh_n 1))))
           (if (== $nh_k proof)
               (pr (phyp $nh_m $nh_args) $nh_st2)
               (if (== $nh_args ()) (pr (var $nh_m) $nh_st2) (pr (apv (var $nh_m) $nh_args) $nh_st2)))))))
; a hole of a lemma stated from its occurrences: one parameter per ID, s_ID, a function of the binders
; in scope only when KEEP is all
(= (lib:nm-rhole $nr_k $nr_id $nr_keep $nr_env $nr_st)
   (let* (((ws $nr_hs $nr_fs $nr_ls $nr_n) $nr_st)
          ($nr_m (lib:pname s $nr_id))
          ($nr_args (if (== $nr_keep none) () (lib:vars $nr_env ())))
          ($nr_ty (if (== $nr_keep none) (proof) (lib:pi-over $nr_env (proof))))
          ($nr_new (if (lib:has-param? $nr_hs $nr_m) False True))
          ($nr_st2 (if $nr_new (ws (cons-atom (hp $nr_m $nr_ty) $nr_hs) $nr_fs $nr_ls $nr_n) $nr_st)))
     (if (== $nr_k proof)
         (pr (phyp $nr_m $nr_args) $nr_st2)
         (if (== $nr_args ()) (pr (var $nr_m) $nr_st2) (pr (apv (var $nr_m) $nr_args) $nr_st2)))))
(= (lib:has-param? $hp_hs $hp_m) (if (== $hp_hs ()) False (let (hp $hp_n $hp_t) (car-atom $hp_hs) (if (== $hp_n $hp_m) True (lib:has-param? (cdr-atom $hp_hs) $hp_m)))))
(= (lib:lookup-name $ln_fs $ln_i) (if (== $ln_fs ()) none (let (fn $ln_j $ln_v $ln_k) (car-atom $ln_fs) (if (== $ln_j $ln_i) $ln_v (lib:lookup-name (cdr-atom $ln_fs) $ln_i)))))
(= (lib:free-name $fn_idx $fn_k $fn_st)
   (let (ws $fn_hs $fn_fs $fn_ls $fn_n) $fn_st
     (let $fn_old (lib:lookup-name $fn_fs $fn_idx)
       (if (== $fn_old none)
           (let $fn_f (lib:pname f $fn_n) (pr $fn_f (ws $fn_hs (cons-atom (fn $fn_idx $fn_f $fn_k) $fn_fs) $fn_ls (+ $fn_n 1))))
           (pr $fn_old $fn_st)))))
(= (lib:nm-dbv $nv_k $nv_env $nv_st)
   (let $nv_d (term:length $nv_env)
     (if (< $nv_k $nv_d) (let (bv $nv_x $nv_t) (lib:nth $nv_env $nv_k) (pr (var $nv_x) $nv_st))
         (let (pr $nv_f $nv_st2) (lib:free-name (- $nv_k $nv_d) 0 $nv_st) (pr (var $nv_f) $nv_st2)))))
(= (lib:nm-dbh $nd_k $nd_as $nd_env $nd_st)
   (let* (($nd_d (term:length $nd_env))
          ((pr $nd_head $nd_st1) (if (< $nd_k $nd_d) (let (bv $nd_x $nd_t) (lib:nth $nd_env $nd_k) (pr $nd_x $nd_st))
                                     (lib:free-name (- $nd_k $nd_d) (term:length $nd_as) $nd_st)))
          ((pr $nd_args $nd_st2) (lib:nm-list $nd_as $nd_env $nd_st1)))
     (pr (phyp $nd_head $nd_args) $nd_st2)))
(= (lib:nm-lvl $nn_p $nn_st)
   (let $nn_x (term:h1 $nn_p)
     (if (== (get-metatype $nn_x) Symbol)
         (let (ws $nn_hs $nn_fs $nn_ls $nn_n) $nn_st
           (if (term:member-of $nn_x $nn_ls) (pr $nn_p $nn_st) (pr $nn_p (ws $nn_hs $nn_fs (cons-atom $nn_x $nn_ls) $nn_n))))
         (pr $nn_p $nn_st))))
; the lemma: its levels in order and its value, a function of its parameters (the outside
; references, then the holes, each in the order met: a hole's type may name an outside reference,
; an outside reference's type names nothing)
(= (lib:wrap $wr_ps $wr_body) (if (== $wr_ps ()) $wr_body (let (hp $wr_n $wr_t) (car-atom $wr_ps) (plam $wr_n $wr_t (lib:wrap (cdr-atom $wr_ps) $wr_body)))))
(= (lib:frees-in-order $fo_fs $fo_acc)
   (if (== $fo_fs ()) $fo_acc
       (let (fn $fo_i $fo_f $fo_k) (car-atom $fo_fs) (lib:frees-in-order (cdr-atom $fo_fs) (cons-atom (hp $fo_f (lib:arrows $fo_k 1)) $fo_acc)))))
(= (lib:params-size $pz_ps $pz_acc) (if (== $pz_ps ()) $pz_acc (let (hp $pz_n $pz_t) (car-atom $pz_ps) (lib:params-size (cdr-atom $pz_ps) (+ $pz_acc (+ 1 (term:size $pz_t)))))))
(= (lib:emit $em_name $em_term)
   (let* (((pr $em_body (ws $em_hs $em_fs $em_ls $em_n)) (lib:nm $em_term () (ws () () () 1)))
          ($em_params (term:concat (lib:frees-in-order $em_fs ()) (tsg:reverse $em_hs ())))
          ($em_levels (tsg:reverse $em_ls ()))
          ($em_value (lib:wrap $em_params $em_body)))
     (add-atom &self (MinedLemma $em_name $em_levels $em_value))))

;;; citing a lemma: its level arguments, then the outside references' values, then its holes' values
;;; (each a function of the fragment's bound variables above it, its own rewritten)

(= (lib:abstract $ab_k $ab_v $ab_st)
   (if (== $ab_st ()) $ab_v
       (let (bd $ab_b $ab_x $ab_T) (car-atom $ab_st)
         (lib:abstract $ab_k (if (== $ab_k proof) (plam $ab_x $ab_T $ab_v) (lam $ab_x $ab_T $ab_v)) (cdr-atom $ab_st)))))
; a level argument: a level hole's value, or a level name passed as itself
(= (lib:level-arg $lg_x) (let $lg_v (term:h1 $lg_x) (level (lvl $lg_v))))
(= (lib:level-args $la_ls) (if (== $la_ls ()) () (cons-atom (lib:level-arg (car-atom $la_ls)) (lib:level-args (cdr-atom $la_ls)))))
; the holes' values in the order met, each ID once (HOLES as recorded, last met first)
(= (lib:hole-args $ha_hs $ha_acc) (lib:hole-args-in (tsg:reverse $ha_hs ()) () ()))
(= (lib:hole-args-in $hi_hs $hi_seen $hi_acc)
   (if (== $hi_hs ()) (tsg:reverse $hi_acc ())
       (let (hv $hi_k $hi_v $hi_st $hi_id) (car-atom $hi_hs)
         (if (if (== $hi_id none) False (term:member-of $hi_id $hi_seen))
             (lib:hole-args-in (cdr-atom $hi_hs) $hi_seen $hi_acc)
             (let (pr $hi_s $hi_v2) (lib:best $hi_v)
               (lib:hole-args-in (cdr-atom $hi_hs) (cons-atom $hi_id $hi_seen) (cons-atom (lib:abstract $hi_k $hi_v2 $hi_st) $hi_acc)))))))
(= (lib:free-args $fa_fs $fa_acc) (if (== $fa_fs ()) $fa_acc (let (fv $fa_i $fa_v) (car-atom $fa_fs) (lib:free-args (cdr-atom $fa_fs) (cons-atom $fa_v $fa_acc)))))
(= (lib:citation $ct_name $ct_m)
   (let (ma $ct_hs $ct_fs $ct_ls) $ct_m
     (pcite $ct_name (term:concat (lib:level-args (tsg:reverse $ct_ls ()))
                                  (term:concat (lib:free-args $ct_fs ()) (lib:hole-args $ct_hs ()))))))

;;; exact rewriting: the smallest proof citing the library, memoised by content

(= (lib:best $bs_t)
   (if (term:expr? $bs_t)
       (let* (($bs_key (sha256 (repr $bs_t)))
              ($bs_memo (collapse (match &self (LibMemo $bs_key $bs_s $bs_r) (pr $bs_s $bs_r)))))
         (if (== $bs_memo ())
             (let* (((pr $bs_s0 $bs_r0) (lib:children $bs_t 0 ()))
                    ($bs_here (pr (+ $bs_s0 1) $bs_r0))
                    ($bs_best (if (== (tsg:kind-of $bs_t) proof) (lib:try-lemmas $bs_t $bs_here) $bs_here))
                    ((pr $bs_size $bs_rew) $bs_best)
                    ($bs_a (add-atom &self (LibMemo $bs_key $bs_size $bs_rew))))
               $bs_best)
             (car-atom $bs_memo)))
       (pr 0 $bs_t)))
(= (lib:children $cd_xs $cd_s $cd_acc)
   (if (== $cd_xs ()) (pr $cd_s (tsg:reverse $cd_acc ()))
       (let (pr $cd_s1 $cd_r1) (lib:best (car-atom $cd_xs))
         (lib:children (cdr-atom $cd_xs) (+ $cd_s $cd_s1) (cons-atom $cd_r1 $cd_acc)))))
(= (lib:try-lemmas $tl_t $tl_best)
   (let* (($tl_rk (tsg:root-rk $tl_t proof))
          ($tl_ls (msort (collapse (match &self (LibLemmaAt $tl_rk $tl_n $tl_p) (pr $tl_n $tl_p))))))
     (lib:try-each $tl_ls $tl_t $tl_best)))
(= (lib:try-each $te_ls $te_t $te_best)
   (if (== $te_ls ()) $te_best
       (let* (((pr $te_n $te_p) (car-atom $te_ls))
              ($te_m (lib:mt $te_p $te_t 0 () (ma () () ())))
              ($te_best2 (if (== $te_m Fail) $te_best
                             (let* (($te_c (lib:citation $te_n $te_m)) ($te_s (term:size $te_c))
                                    ((pr $te_bs $te_br) $te_best))
                               (if (< $te_s $te_bs) (pr $te_s $te_c) $te_best)))))
         (lib:try-each (cdr-atom $te_ls) $te_t $te_best2))))

;;; the library over a corpus

(= (lib:citations $cs_t $cs_acc)
   (if (term:expr? $cs_t)
       (let $cs_acc2 (if (== (car-atom $cs_t) pcite)
                         (let $cs_n (term:h1 $cs_t)
                           (let $qz8 (collapse (match &self (LibLemma $cs_n $cs_p) yes)) (if (== $qz8 ()) $cs_acc (cons-atom $cs_n $cs_acc))))
                         $cs_acc)
         (lib:citations-list $cs_t $cs_acc2))
       $cs_acc))
(= (lib:citations-list $cl_xs $cl_acc) (if (== $cl_xs ()) $cl_acc (lib:citations-list (cdr-atom $cl_xs) (lib:citations (car-atom $cl_xs) $cl_acc))))
(= (lib:note-uses $nu_ns $nu_c)
   (if (== $nu_ns ()) done
       (let* (($nu_n (car-atom $nu_ns))
              ($nu_a (let $qz9 (collapse (match &self (MinedUse $nu_n $nu_c) yes)) (if (== $qz9 ()) (add-atom &self (MinedUse $nu_n $nu_c)) done)))
              ($nu_b (let $qz10 (collapse (match &self (MinedBefore $nu_n $nu_y) yes)) (if (== $qz10 ()) (add-atom &self (MinedBefore $nu_n $nu_c)) done))))
         (lib:note-uses (cdr-atom $nu_ns) $nu_c))))
(= (lib:rewrite-one $ro_c)
   (let $ro_ps (collapse (match &self (TransportProof $ro_c $ro_p) $ro_p))
     (if (== $ro_ps ()) (pr 0 0)
         (let* (($ro_old (tsg:strip (term:db (car-atom $ro_ps) ())))
                ((pr $ro_s $ro_new) (lib:best $ro_old))
                ($ro_before (term:size $ro_old))
                ($ro_x (if (== $ro_new $ro_old) done
                           (let* (($ro_named (term:named $ro_new ()))
                                  ($ro_a (add-atom &self (RewrittenProof $ro_c $ro_named))))
                             (lib:note-uses (lib:citations $ro_new ()) $ro_c))))
                ($ro_k (add-atom &self (MinedSize $ro_c $ro_before $ro_s))))
           (pr $ro_before $ro_s)))))
(= (lib:rewrite-list $rl_cs $rl_b $rl_a)
   (if (== $rl_cs ()) (pr $rl_b $rl_a)
       (let (pr $rl_b1 $rl_a1) (lib:rewrite-one (car-atom $rl_cs))
         (lib:rewrite-list (cdr-atom $rl_cs) (+ $rl_b $rl_b1) (+ $rl_a $rl_a1)))))
; drop lemmas Lean refused, given as (MinedRefused NAME), before rewriting
(= (lib:drop-refused)
   (let $dr_ns (collapse (match &self (MinedRefused $dr_n) $dr_n))
     (lib:drop-each $dr_ns)))
(= (lib:drop-each $de_ns)
   (if (== $de_ns ()) done
       (let* (($de_n (car-atom $de_ns))
              ($de_ps (collapse (match &self (LibLemma $de_n $de_p) $de_p)))
              ($de_x (if (== $de_ps ()) done
                         (let* (($de_p (car-atom $de_ps)) ($de_rk (tsg:root-rk $de_p proof))
                                ($de_r (remove-atom &self (LibLemmaAt $de_rk $de_n $de_p))))
                           (remove-atom &self (LibLemma $de_n $de_p))))))
         (lib:drop-each (cdr-atom $de_ns)))))
; every chosen lemma written for Lean, to be judged alone before any proof cites it
(= (lib:emit-all)
   (let $ea_ls (msort (collapse (match &self (LibLemma $ea_n $ea_p) (pr $ea_n $ea_p))))
     (lib:emit-all-each $ea_ls)))
(= (lib:emit-all-each $eb_ls) (if (== $eb_ls ()) done (let (pr $eb_n $eb_p) (car-atom $eb_ls) (let $eb_x (lib:emit $eb_n $eb_p) (lib:emit-all-each (cdr-atom $eb_ls))))))
(= (lib:lemma-names) (msort (collapse (match &self (MinedLemma $mn_n $mn_l $mn_v) $mn_n))))
(= (lib:emit-used)
   (let $eu_ls (collapse (match &self (LibLemma $eu_n $eu_p) (pr $eu_n $eu_p)))
     (lib:emit-each $eu_ls 0)))
(= (lib:emit-each $ee_ls $ee_k)
   (if (== $ee_ls ()) $ee_k
       (let (pr $ee_n $ee_p) (car-atom $ee_ls)
         (let $qz11 (collapse (match &self (MinedUse $ee_n $ee_c) yes)) (if (== $qz11 ())
             (lib:emit-each (cdr-atom $ee_ls) $ee_k)
             (let $ee_x (lib:emit $ee_n $ee_p) (lib:emit-each (cdr-atom $ee_ls) (+ $ee_k 1))))))))
(= (lib:rewrite-all $ra_order)
   (let* (($ra_d (lib:drop-refused))
          ((pr $ra_b $ra_a) (lib:rewrite-list $ra_order 0 0))
          ($ra_k (lib:emit-used)))
     (println! (MinedSizes (proofs-before $ra_b) (proofs-after $ra_a) (lemmas-used $ra_k)))))

; proof sizes before and after, for the training theorems, the held-out ones and the rest
(= (lib:sizes-by-split $ss_train $ss_held)
   (let $ss_rows (collapse (match &self (MinedSize $ss_c $ss_b $ss_a) ($ss_c $ss_b $ss_a)))
     (let (pr $ss_tr (pr $ss_ho $ss_ot)) (lib:split-sums $ss_rows $ss_train $ss_held (pr 0 0) (pr 0 0) (pr 0 0))
       (println! (MinedSizesByClass (training $ss_tr) (held-out $ss_ho) (other $ss_ot))))))
(= (lib:in? $in_x $in_xs) (if (== $in_xs ()) False (if (== (car-atom $in_xs) $in_x) True (lib:in? $in_x (cdr-atom $in_xs)))))
(= (lib:split-sums $su_rows $su_train $su_held $su_tr $su_ho $su_ot)
   (if (== $su_rows ()) (pr $su_tr (pr $su_ho $su_ot))
       (let* ((($su_c $su_b $su_a) (car-atom $su_rows))
              ((pr $su_tb $su_ta) $su_tr) ((pr $su_hb $su_ha) $su_ho) ((pr $su_ob $su_oa) $su_ot))
         (if (lib:in? $su_c $su_train)
             (lib:split-sums (cdr-atom $su_rows) $su_train $su_held (pr (+ $su_tb $su_b) (+ $su_ta $su_a)) $su_ho $su_ot)
         (if (lib:in? $su_c $su_held)
             (lib:split-sums (cdr-atom $su_rows) $su_train $su_held $su_tr (pr (+ $su_hb $su_b) (+ $su_ha $su_a)) $su_ot)
             (lib:split-sums (cdr-atom $su_rows) $su_train $su_held $su_tr $su_ho (pr (+ $su_ob $su_b) (+ $su_oa $su_a))))))))

;;; statements from occurrences: a lemma Lean refuses is stated again as what its occurrences in
;;; the training theorems have in common.  Per hole, over every occurrence: one value that reaches
;;; nothing outside the fragment is written in; a value that never reaches the fragment's binders
;;; makes the hole a parameter of no binder; holes with one such value in every occurrence are one
;;; parameter (a proof that type-checks only because two holes coincide is not a lemma with two).
;;;   !(lib:refine-refused TRAINING)   each (MinedRefused NAME) that is a lemma becomes NAMEr

(= (lib:has-outer? $ho_t $ho_d $ho_cut)
   (if (term:expr? $ho_t)
       (let $ho_h (car-atom $ho_t)
         (if (or (== $ho_h dbv) (== $ho_h dbh))
             (if (>= (term:h1 $ho_t) (+ $ho_cut $ho_d)) True
                 (if (== $ho_h dbh) (lib:has-outer-list? (term:h2 $ho_t) $ho_d $ho_cut) False))
             (if (term:binder? $ho_h)
                 (if (lib:has-outer? (term:h2 $ho_t) $ho_d $ho_cut) True (lib:has-outer? (term:h3 $ho_t) $ho_d (+ $ho_cut 1)))
                 (lib:has-outer-list? $ho_t $ho_d $ho_cut))))
       False))
(= (lib:has-outer-list? $hl_xs $hl_d $hl_cut)
   (if (== $hl_xs ()) False (if (lib:has-outer? (car-atom $hl_xs) $hl_d $hl_cut) True (lib:has-outer-list? (cdr-atom $hl_xs) $hl_d $hl_cut))))
; the refused patterns that are lemmas, filed by head symbol: (LibRefinePat HEAD NAME PATTERN)
(= (lib:refused-patterns $rp_ns $rp_acc)
   (if (== $rp_ns ()) $rp_acc
       (let* (($rp_n (car-atom $rp_ns))
              ($rp_q (collapse (match &self (LibLemma $rp_n $rp_p) $rp_p)))
              ($rp_acc2 (if (== $rp_q ()) $rp_acc
                            (let* (($rp_p (car-atom $rp_q)) ($rp_h (car-atom $rp_p))
                                   ($rp_a (add-atom &self (LibRefinePat $rp_h $rp_n $rp_p))))
                              (cons-atom (pr $rp_n $rp_p) $rp_acc)))))
         (lib:refused-patterns (cdr-atom $rp_ns) $rp_acc2))))
; every node of the training proofs where a refused pattern matches: (LibOcc NAME HOLES), the holes
; in the order met
(= (lib:walk-theorems $wt_cs)
   (if (== $wt_cs ()) done
       (let* (($wt_c (car-atom $wt_cs))
              ($wt_ps (collapse (match &self (TransportProof $wt_c $wt_p) $wt_p)))
              ($wt_x (if (== $wt_ps ()) done (lib:walk-node (tsg:strip (term:db (car-atom $wt_ps) ()))))))
         (lib:walk-theorems (cdr-atom $wt_cs)))))
(= (lib:walk-node $wn_t)
   (if (term:expr? $wn_t)
       (let* (($wn_h (car-atom $wn_t))
              ($wn_c (if (== (get-metatype $wn_h) Symbol)
                         (let $wn_cands (collapse (match &self (LibRefinePat $wn_h $wn_n $wn_p) (pr $wn_n $wn_p)))
                           (lib:try-occ $wn_cands $wn_t))
                         done)))
         (lib:walk-list $wn_t))
       done))
(= (lib:walk-list $wl_xs) (if (== $wl_xs ()) done (let $wl_x (lib:walk-node (car-atom $wl_xs)) (lib:walk-list (cdr-atom $wl_xs)))))
(= (lib:try-occ $to_cs $to_t)
   (if (== $to_cs ()) done
       (let* (((pr $to_n $to_p) (car-atom $to_cs))
              ($to_m (lib:mt $to_p $to_t 0 () (ma () () ())))
              ($to_x (if (== $to_m Fail) done
                         (let (ma $to_hs $to_fs $to_ls) $to_m
                           (let $to_ord (tsg:reverse $to_hs ()) (add-atom &self (LibOcc $to_n $to_ord)))))))
         (lib:try-occ (cdr-atom $to_cs) $to_t))))
; the I-th hole's entries across the occurrences
(= (lib:column $co_occs $co_i $co_acc)
   (if (== $co_occs ()) (tsg:reverse $co_acc ()) (lib:column (cdr-atom $co_occs) $co_i (cons-atom (tsg:nth (car-atom $co_occs) $co_i) $co_acc))))
(= (lib:all-equal? $ae_xs) (if (== $ae_xs ()) True (lib:all-equal-to? (cdr-atom $ae_xs) (car-atom $ae_xs))))
(= (lib:all-equal-to? $at_xs $at_x) (if (== $at_xs ()) True (if (== (car-atom $at_xs) $at_x) (lib:all-equal-to? (cdr-atom $at_xs) $at_x) False)))
(= (lib:any-captures? $ac_es) (if (== $ac_es ()) False (let (hv $ac_k $ac_v $ac_st $ac_id) (car-atom $ac_es) (if (term:captures? $ac_v (term:length $ac_st) 0) True (lib:any-captures? (cdr-atom $ac_es))))))
(= (lib:any-outer? $ao_es) (if (== $ao_es ()) False (let (hv $ao_k $ao_v $ao_st $ao_id) (car-atom $ao_es) (if (lib:has-outer? $ao_v (term:length $ao_st) 0) True (lib:any-outer? (cdr-atom $ao_es))))))
(= (lib:values $vs_es $vs_acc) (if (== $vs_es ()) (tsg:reverse $vs_acc ()) (let (hv $vs_k $vs_v $vs_st $vs_id) (car-atom $vs_es) (lib:values (cdr-atom $vs_es) (cons-atom $vs_v $vs_acc)))))
(= (lib:downs $dw_es $dw_acc) (if (== $dw_es ()) (tsg:reverse $dw_acc ()) (let (hv $dw_k $dw_v $dw_st $dw_id) (car-atom $dw_es) (lib:downs (cdr-atom $dw_es) (cons-atom (term:down $dw_v (term:length $dw_st) 0) $dw_acc)))))
; a hole's statement: (sfill VALUE), (sfirst KIND VALUES) or (skeep KIND)
(= (lib:hole-spec $hs_es)
   (let* (((hv $hs_k $hs_v $hs_st $hs_id) (car-atom $hs_es)) ($hs_vs (lib:values $hs_es ())))
     (if (if (lib:all-equal? $hs_vs) (not (lib:any-outer? $hs_es)) False) (sfill $hs_v)
         (if (lib:any-captures? $hs_es) (skeep $hs_k) (sfirst $hs_k (lib:downs $hs_es ()))))))
(= (lib:hole-specs $hp_i $hp_n $hp_occs $hp_acc)
   (if (>= $hp_i $hp_n) (tsg:reverse $hp_acc ())
       (lib:hole-specs (+ $hp_i 1) $hp_n $hp_occs (cons-atom (lib:hole-spec (lib:column $hp_occs $hp_i ())) $hp_acc))))
; parameters: an (sfirst ..) hole takes the ID of an earlier one with the same kind and values, else a
; new one; an (skeep ..) hole always a new one: (hole KIND ID KEEP) or the value written in
(= (lib:assign-ids $ai_specs $ai_seen $ai_next $ai_acc)
   (if (== $ai_specs ()) (tsg:reverse $ai_acc ())
       (let $ai_s (car-atom $ai_specs)
         (if (== (car-atom $ai_s) sfill) (lib:assign-ids (cdr-atom $ai_specs) $ai_seen $ai_next (cons-atom (term:h1 $ai_s) $ai_acc))
         (if (== (car-atom $ai_s) skeep) (lib:assign-ids (cdr-atom $ai_specs) $ai_seen (+ $ai_next 1) (cons-atom (hole (term:h1 $ai_s) $ai_next all) $ai_acc))
             (let* (($ai_key (pr (term:h1 $ai_s) (term:h2 $ai_s))) ($ai_old (lib:seen-id $ai_seen $ai_key)))
               (if (== $ai_old none)
                   (lib:assign-ids (cdr-atom $ai_specs) (cons-atom (pr $ai_key $ai_next) $ai_seen) (+ $ai_next 1) (cons-atom (hole (term:h1 $ai_s) $ai_next none) $ai_acc))
                   (lib:assign-ids (cdr-atom $ai_specs) $ai_seen $ai_next (cons-atom (hole (term:h1 $ai_s) $ai_old none) $ai_acc)))))))))
(= (lib:seen-id $si_xs $si_k) (if (== $si_xs ()) none (let (pr $si_key $si_id) (car-atom $si_xs) (if (== $si_key $si_k) $si_id (lib:seen-id (cdr-atom $si_xs) $si_k)))))
; the pattern with its holes (not its level holes) replaced in the order the matcher meets them
(= (lib:rebuild $rb_p $rb_rs)
   (if (term:expr? $rb_p)
       (let $rb_h (car-atom $rb_p)
         (if (if (== $rb_h hole) (not (== (term:h1 $rb_p) level)) False) (pr (car-atom $rb_rs) (cdr-atom $rb_rs))
         (if (if (== (get-metatype $rb_h) Symbol) (term:binder? $rb_h) False)
             (let* (((pr $rb_T $rb_r1) (lib:rebuild (term:h2 $rb_p) $rb_rs)) ((pr $rb_B $rb_r2) (lib:rebuild (term:h3 $rb_p) $rb_r1)))
               (pr (cons-atom $rb_h (cons-atom (term:h1 $rb_p) (cons-atom $rb_T (cons-atom $rb_B ())))) $rb_r2))
             (lib:rebuild-list $rb_p $rb_rs))))
       (pr $rb_p $rb_rs)))
(= (lib:rebuild-list $rl_xs $rl_rs)
   (if (== $rl_xs ()) (pr () $rl_rs)
       (let* (((pr $rl_a $rl_r1) (lib:rebuild (car-atom $rl_xs) $rl_rs)) ((pr $rl_b $rl_r2) (lib:rebuild-list (cdr-atom $rl_xs) $rl_r1)))
         (pr (cons-atom $rl_a $rl_b) $rl_r2))))
(= (lib:refine-one $ro_n $ro_p)
   (let $ro_occs (collapse (match &self (LibOcc $ro_n $ro_h) $ro_h))
     (if (== $ro_occs ()) none
         (let* (($ro_specs (lib:hole-specs 0 (term:length (car-atom $ro_occs)) $ro_occs ()))
                ($ro_repl (lib:assign-ids $ro_specs () 1 ()))
                ((pr $ro_p2 $ro_left) (lib:rebuild $ro_p $ro_repl))
                ($ro_rk (tsg:root-rk $ro_p proof))
                ($ro_r1 (remove-atom &self (LibLemmaAt $ro_rk $ro_n $ro_p)))
                ($ro_r2 (remove-atom &self (LibLemma $ro_n $ro_p)))
                ($ro_n2 (atom_concat $ro_n r))
                ($ro_a (lib:add-lemma $ro_n2 $ro_p2)))
           $ro_n2))))
(= (lib:refine-each $re_ps $re_acc)
   (if (== $re_ps ()) $re_acc
       (let* (((pr $re_n $re_p) (car-atom $re_ps)) ($re_x (lib:refine-one $re_n $re_p)))
         (lib:refine-each (cdr-atom $re_ps) (if (== $re_x none) $re_acc (+ $re_acc 1))))))
(= (lib:refine-refused $rr_cs)
   (let* (($rr_s1 (add-atom &self (LibRefinePat none none none))) ($rr_s2 (add-atom &self (LibOcc none ())))
          ($rr_ns (collapse (match &self (MinedRefused $rr_n) $rr_n)))
          ($rr_ps (lib:refused-patterns $rr_ns ()))
          ($rr_w (lib:walk-theorems $rr_cs))
          ($rr_k (lib:refine-each $rr_ps 0)))
     (println! (lib-refined (stated-again $rr_k) (of (term:length $rr_ps))))))
