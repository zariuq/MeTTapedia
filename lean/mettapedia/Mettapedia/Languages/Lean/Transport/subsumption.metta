; Which Lean theorems are instances of an earlier one?  A statement is a pattern over its own
; binders; an earlier theorem B covers A when B's conclusion matches A's and each of B's
; hypotheses, so instantiated, is one of A's.  Unmatched term arguments need
; compatible binders in A's context before proposing the citation. The proposal is kept as
; (RewrittenProof A proof) for the way back to Lean, and each finding is printed:
;   (InstanceOf A B (old-size N) (new-size M) (already-one-citation BOOL))

(= (subsume:member $mb_x $mb_xs) (if (== $mb_xs ()) False (if (== (car-atom $mb_xs) $mb_x) True (subsume:member $mb_x (cdr-atom $mb_xs)))))
(= (subsume:lookup $lk_x $lk_sig)
   (if (== $lk_sig ()) None
       (let ($lk_y $lk_v) (car-atom $lk_sig) (if (== $lk_y $lk_x) $lk_v (subsume:lookup $lk_x (cdr-atom $lk_sig))))))

(= (subsume:bind $bd_x $bd_t $bd_sig $bd_d)
   (if (term:captures? $bd_t $bd_d 0) Fail
       (let $bd_old (subsume:lookup $bd_x $bd_sig)
         (if (== $bd_old None) (cons-atom ($bd_x $bd_t) $bd_sig)
             (if (== $bd_old $bd_t) $bd_sig Fail)))))

(= (subsume:match $mt_p $mt_t $mt_vars $mt_sig $mt_d)
   (if (term:expr? $mt_p)
       (let $mt_h (car-atom $mt_p)
         (if (and (== $mt_h var) (subsume:member (term:h1 $mt_p) $mt_vars))
             (subsume:bind (term:h1 $mt_p) $mt_t $mt_sig $mt_d)
             (if (term:expr? $mt_t)
                 (if (== (term:length $mt_p) (term:length $mt_t))
                     (if (term:binder? $mt_h)
                         (if (== $mt_h (car-atom $mt_t))
                             (let $mt_s1 (subsume:match (term:h2 $mt_p) (term:h2 $mt_t) $mt_vars $mt_sig $mt_d)
                               (if (== $mt_s1 Fail) Fail (subsume:match (term:h3 $mt_p) (term:h3 $mt_t) $mt_vars $mt_s1 (+ $mt_d 1))))
                             Fail)
                         (subsume:match-list $mt_p $mt_t $mt_vars $mt_sig $mt_d))
                     Fail)
                 Fail)))
       (if (== $mt_p $mt_t) $mt_sig Fail)))
(= (subsume:match-list $ml_ps $ml_ts $ml_vars $ml_sig $ml_d)
   (if (== $ml_ps ()) $ml_sig
       (let $ml_s1 (subsume:match (car-atom $ml_ps) (car-atom $ml_ts) $ml_vars $ml_sig $ml_d)
         (if (== $ml_s1 Fail) Fail (subsume:match-list (cdr-atom $ml_ps) (cdr-atom $ml_ts) $ml_vars $ml_s1 $ml_d)))))

; B's hypotheses against A's, each used at most as often as it is given (backtracking)
(= (subsume:hyps $hy_bs $hy_as $hy_vars $hy_sig $hy_acc)
   (if (== $hy_bs ()) ($hy_sig $hy_acc)
       (subsume:hyp-try (car-atom $hy_bs) (cdr-atom $hy_bs) $hy_as $hy_as $hy_vars $hy_sig $hy_acc)))
(= (subsume:hyp-try $ht_p $ht_rest $ht_cands $ht_all $ht_vars $ht_sig $ht_acc)
   (if (== $ht_cands ()) Fail
       (let* ((($ht_g $ht_q) (car-atom $ht_cands))
              ($ht_s (subsume:match $ht_p $ht_q $ht_vars $ht_sig 0)))
         (if (== $ht_s Fail) (subsume:hyp-try $ht_p $ht_rest (cdr-atom $ht_cands) $ht_all $ht_vars $ht_sig $ht_acc)
             (let $ht_r (subsume:hyps $ht_rest $ht_all $ht_vars $ht_s (term:concat $ht_acc ($ht_g)))
               (if (== $ht_r Fail) (subsume:hyp-try $ht_p $ht_rest (cdr-atom $ht_cands) $ht_all $ht_vars $ht_sig $ht_acc) $ht_r))))))

; A statement read for matching: (vars hyps conclusion), inner binders as indices
(= (subsume:vars $vs_bs)
   (if (== $vs_bs ()) ()
       (let $vs_rest (subsume:vars (cdr-atom $vs_bs))
         (let $vs_b (car-atom $vs_bs) (if (== (car-atom $vs_b) hyp) $vs_rest (cons-atom (term:h1 $vs_b) $vs_rest))))))
(= (subsume:hyp-forms $hf_bs)
   (if (== $hf_bs ()) ()
       (let $hf_rest (subsume:hyp-forms (cdr-atom $hf_bs))
         (let $hf_b (car-atom $hf_bs)
           (if (== (car-atom $hf_b) hyp) (cons-atom ((term:h1 $hf_b) (term:db (term:h2 $hf_b) ())) $hf_rest) $hf_rest)))))
(= (subsume:hyp-pats $hp_forms) (if (== $hp_forms ()) () (cons-atom (term:h1 (car-atom $hp_forms)) (subsume:hyp-pats (cdr-atom $hp_forms)))))
(= (subsume:key $ky_t $ky_vars)
   (if (term:expr? $ky_t)
       (let $ky_h (car-atom $ky_t)
         (if (and (== $ky_h var) (subsume:member (term:h1 $ky_t) $ky_vars)) any
             (if (== $ky_h app) (app (term:h1 $ky_t)) $ky_h)))
       $ky_t))

; A proof that is already one citation, under the binders
(= (subsume:direct? $dr_p)
   (if (term:expr? $dr_p)
       (if (== (car-atom $dr_p) plam) (subsume:direct? (term:h3 $dr_p)) (== (car-atom $dr_p) pcite))
       False))

(= (subsume:index-all $ia_cs $ia_i)
   (if (== $ia_cs ()) done
       (let* (($ia_c (car-atom $ia_cs))
              ($ia_found (collapse (match &self (TransportTheorem $ia_c $ia_bs $ia_P) ($ia_bs $ia_P)))))
         (if (== $ia_found ()) (subsume:index-all (cdr-atom $ia_cs) (+ $ia_i 1))
             (let* ((($ia_bs2 $ia_P2) (car-atom $ia_found))
                    ($ia_vars (subsume:vars $ia_bs2))
                    ($ia_concl (term:db $ia_P2 ()))
                    ($ia_hyps (subsume:hyp-forms $ia_bs2))
                    ($ia_key (subsume:key $ia_concl $ia_vars))
                    ($ia_kept (add-atom &self (ImStmt $ia_c $ia_i $ia_bs2 $ia_vars $ia_hyps $ia_concl)))
                    ($ia_kk (add-atom &self (ImByKey $ia_key $ia_c))))
               (subsume:index-all (cdr-atom $ia_cs) (+ $ia_i 1)))))))

(= (subsume:stmt $st_c) (car-atom (collapse (match &self (ImStmt $st_c $st_i $st_bs $st_vars $st_hyps $st_concl) ($st_i $st_bs $st_vars $st_hyps $st_concl)))))

; The first earlier theorem B that covers A, as (B sig hyp-assignments) or None.
(= (subsume:cover $cv_a)
   (let* ((($cv_ia $cv_abs $cv_avars $cv_ahyps $cv_aconcl) (subsume:stmt $cv_a))
          ($cv_key (subsume:key $cv_aconcl ()))
          ($cv_cands (term:concat (collapse (match &self (ImByKey $cv_key $cv_b) $cv_b))
                                (collapse (match &self (ImByKey any $cv_b2) $cv_b2)))))
     (subsume:cover-try $cv_a $cv_ia $cv_abs $cv_ahyps $cv_aconcl $cv_cands)))
(= (subsume:cover-try $ct_a $ct_ia $ct_abs $ct_ahyps $ct_aconcl $ct_cands)
   (if (== $ct_cands ()) None
       (let* (($ct_b (car-atom $ct_cands))
              (($ct_ib $ct_bbs $ct_bvars $ct_bhyps $ct_bconcl) (subsume:stmt $ct_b))
              ($ct_r (if (or (== $ct_b $ct_a) (>= $ct_ib $ct_ia)) Fail
                         (let $ct_s (subsume:match $ct_bconcl $ct_aconcl $ct_bvars () 0)
                           (if (== $ct_s Fail) Fail (subsume:hyps (subsume:hyp-pats $ct_bhyps) $ct_ahyps $ct_bvars $ct_s ()))))))
         (if (== $ct_r Fail) (subsume:cover-try $ct_a $ct_ia $ct_abs $ct_ahyps $ct_aconcl (cdr-atom $ct_cands))
             (let ($ct_sig $ct_asg) $ct_r
               (let* (($ct_typed (subsume:propagate-binder-types $ct_bbs $ct_abs $ct_bvars $ct_sig))
                      ($ct_complete (subsume:complete-binders $ct_bbs $ct_abs $ct_bvars $ct_typed)))
                 (if (== $ct_complete Fail)
                     (subsume:cover-try $ct_a $ct_ia $ct_abs $ct_ahyps $ct_aconcl (cdr-atom $ct_cands))
                     ($ct_b $ct_complete $ct_asg))))))))

; A's proof by B: A's binders, then B at the matched values and hypotheses.
(= (subsume:args $ag_bbs $ag_sig $ag_asg)
   (if (== $ag_bbs ()) ()
       (let $ag_b (car-atom $ag_bbs)
         (if (== (car-atom $ag_b) hyp)
             (cons-atom (phyp (car-atom $ag_asg) ()) (subsume:args (cdr-atom $ag_bbs) $ag_sig (cdr-atom $ag_asg)))
             (let $ag_v (subsume:lookup (term:h1 $ag_b) $ag_sig)
               (cons-atom (term:named $ag_v ())
                          (subsume:args (cdr-atom $ag_bbs) $ag_sig $ag_asg)))))))
(= (subsume:binder-type $bt_b)
   (let $bt_k (car-atom $bt_b)
     (if (== $bt_k type) (cons-atom sort (cons-atom (lsucc (term:h2 $bt_b)) ()))
     (if (== $bt_k sort) (cons-atom sort (cons-atom (term:h2 $bt_b) ()))
         (term:h2 $bt_b)))))


(= (subsume:binder-by-name $bn_name $bn_binders)
   (if (== $bn_binders ()) None
       (let $bn_first (car-atom $bn_binders)
         (if (== $bn_name (term:h1 $bn_first)) $bn_first
             (subsume:binder-by-name $bn_name (cdr-atom $bn_binders))))))

(= (subsume:types-in-context $tc_binder $tc_value $tc_target $tc_vars $tc_sig)
   (if (term:expr? $tc_value)
       (if (== (car-atom $tc_value) var)
           (let $tc_a (subsume:binder-by-name (term:h1 $tc_value) $tc_target)
             (if (== $tc_a None) $tc_sig
                 (let $tc_match (subsume:match (term:db (subsume:binder-type $tc_binder) ())
                                                (term:db (subsume:binder-type $tc_a) ())
                                                $tc_vars $tc_sig 0)
                   (if (== $tc_match Fail) $tc_sig $tc_match))))
           $tc_sig)
       $tc_sig))

(= (subsume:propagate-binder-types $bt_source $bt_target $bt_vars $bt_sig)
   (if (== $bt_source ()) $bt_sig
       (let* (($bt_b (car-atom $bt_source))
              ($bt_value (subsume:lookup (term:h1 $bt_b) $bt_sig))
              ($bt_updated (subsume:types-in-context $bt_b $bt_value $bt_target $bt_vars $bt_sig)))
         (subsume:propagate-binder-types (cdr-atom $bt_source) $bt_target $bt_vars $bt_updated))))

; Supply unmatched term binders from the target's typed context. Matching their
; declared types may constrain an earlier variable of a dependent telescope.
(= (subsume:complete-binders $cb_bs $cb_as $cb_vars $cb_sig)
   (if (== $cb_bs ()) $cb_sig
       (let* (($cb_b (car-atom $cb_bs)) ($cb_rest (cdr-atom $cb_bs))
              ($cb_x (term:h1 $cb_b)))
         (if (or (== (car-atom $cb_b) hyp) (not (== (subsume:lookup $cb_x $cb_sig) None)))
             (subsume:complete-binders $cb_rest $cb_as $cb_vars $cb_sig)
             (subsume:local-argument $cb_b $cb_rest $cb_as $cb_as $cb_vars $cb_sig)))))

(= (subsume:local-argument $la_b $la_bs $la_candidates $la_as $la_vars $la_sig)
   (if (== $la_candidates ()) Fail
       (let* (($la_a (car-atom $la_candidates))
              ($la_rest (cdr-atom $la_candidates)))
         (if (== (car-atom $la_a) hyp)
             (subsume:local-argument $la_b $la_bs $la_rest $la_as $la_vars $la_sig)
             (let $la_types (subsume:match (term:db (subsume:binder-type $la_b) ())
                                            (term:db (subsume:binder-type $la_a) ())
                                            $la_vars $la_sig 0)
               (if (== $la_types Fail)
                   (subsume:local-argument $la_b $la_bs $la_rest $la_as $la_vars $la_sig)
                   (let $la_value (subsume:bind (term:h1 $la_b) (var (term:h1 $la_a)) $la_types 0)
                     (if (== $la_value Fail)
                         (subsume:local-argument $la_b $la_bs $la_rest $la_as $la_vars $la_sig)
                         (let $la_solution (subsume:complete-binders $la_bs $la_as $la_vars $la_value)
                           (if (== $la_solution Fail)
                               (subsume:local-argument $la_b $la_bs $la_rest $la_as $la_vars $la_sig)
                               $la_solution))))))))))

(= (subsume:wrap $wr_bs $wr_body)
   (if (== $wr_bs ()) $wr_body
       (let $wr_b (car-atom $wr_bs)
         (plam (term:h1 $wr_b) (subsume:binder-type $wr_b) (subsume:wrap (cdr-atom $wr_bs) $wr_body)))))

(= (subsume:run-one $ro_a)
   (let $ro_cover (subsume:cover $ro_a)
     (if (== $ro_cover None) none
         (let* ((($ro_b $ro_sig $ro_asg) $ro_cover)
                (($ro_ia $ro_abs $ro_avars $ro_ahyps $ro_aconcl) (subsume:stmt $ro_a))
                (($ro_ib $ro_bbs $ro_bvars $ro_bhyps $ro_bconcl) (subsume:stmt $ro_b))
                ($ro_old (car-atom (collapse (match &self (TransportProof $ro_a $ro_p) $ro_p))))
                ($ro_new (subsume:wrap $ro_abs (pcite $ro_b (subsume:args $ro_bbs $ro_sig $ro_asg))))
                ($ro_shown (println! (InstanceOf $ro_a $ro_b (old-size (term:size $ro_old)) (new-size (term:size $ro_new))
                                      (already-one-citation (subsume:direct? $ro_old)))))
                ($ro_row (add-atom &self (RewrittenProof $ro_a $ro_new))))
           found))))
(= (subsume:run $rn_cs)
   (if (== $rn_cs ()) done (let $rn_one (subsume:run-one (car-atom $rn_cs)) (subsume:run (cdr-atom $rn_cs)))))
