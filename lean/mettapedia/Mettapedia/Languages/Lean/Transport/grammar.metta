; Bayesian library learning over Lean's proofs (after terms.metta): a tree-substitution grammar
; whose fragments are reused under Pitman-Yor processes, sampled by a Markov chain whose every move
; leaves the posterior invariant.
;
; Every proof is a tree.  A derivation cuts each tree into fragments: every node that can stand
; for a proof, a term or a universe level is either the root of a fragment or inside its parent's
; fragment.  A fragment is a pattern: where a node below it roots another fragment, the pattern has
; a hole of that node's kind.  The model (Cohn, Blunsom and Goldwater, JMLR 2010; Liang, Jordan and
; Klein, ICML 2010 for programs):
;   - the fragments rooted at nodes of one kind (proof, term, level) are draws from a Pitman-Yor
;     process PY(d, theta, P0): a fragment used before is reused in proportion to its count less
;     the discount, a new one is drawn from the base P0;
;   - P0 builds a fragment node by node: each node's local form (its head and leaves, its children
;     as slots) from a Dirichlet-multinomial per category, and at each child that can root a
;     fragment, a stop (a hole) or an expansion from a Beta-Bernoulli per kind; the Dirichlet and
;     Beta priors are integrated out, so P0 is a product of Polya-urn predictives over the base
;     counts, which hold one copy of a fragment's decisions per table serving it;
;   - (d, theta) per kind have a uniform prior on a grid.
; Nothing is split: every theorem's proof is data once.  A fragment seen in one proof is evidence for
; itself discounted by d, and the posterior sets d.
;
; The sampler is exact in this sense: the seating of customers at tables is part of the state, and
; each move (one node by Gibbs sampling, one proof by Metropolis-Hastings, every site of one type by
; Metropolis-Hastings, (d, theta) on its grid) leaves the posterior invariant, so the chain's
; stationary distribution is the posterior; probabilities are computed in floating point
; logarithms.  controls/grammar.metta runs each move against the exact posterior of a corpus small
; enough to enumerate.  Randomness comes from a seeded generator, so a run is a function of the
; corpus and the seed.
;
; Fragments are open: a hole may stand under binders of its own fragment (as a lemma it is a
; parameter applied to those bound variables, a higher-order pattern), and a fragment may refer to
; binders above its root (as a lemma, those references are parameters too).  So every derivation
; has mass, and the lemma a fragment stands for is formed when it is written out.
;
;   !(tsg:run ORDER SEED BURN SAMPLES K)   load, BURN rounds, SAMPLES rounds collected; a round is K
;                                          type moves, a blocked move per proof, a pass over the
;                                          nodes, then (d, theta) per kind
;   !(tsg:print-library MIN N)             the posterior's proof fragments for library.metta
;   !(tsg:extend ORDER) !(tsg:held-sweeps R) !(tsg:held-report)   held-out proofs parsed and
;                                          their reuse set against the reuse predicted
;   !(tsg:recount)                         the state recomputed from the derivation

;;; a seeded stream: L'Ecuyer's combined multiplicative generator (CACM 1988), two states below
;;; 2^31, period about 2.3e18; a draw is uniform in (0, 1)

(= (tsg:seed $sd_s)
   (let $sd_old (collapse (match &self (TsgRng state $sd_x $sd_y) ($sd_x $sd_y)))
     (let $sd_r (if (== $sd_old ()) done (let ($sd_a $sd_b) (car-atom $sd_old) (remove-atom &self (TsgRng state $sd_a $sd_b))))
       (let* (($sd_1 (+ 1 (% $sd_s 2147483562))) ($sd_2 (+ 1 (% (* $sd_s 7) 2147483398))))
         (add-atom &self (TsgRng state $sd_1 $sd_2))))))
(= (tsg:uniform)
   (let* ((($un_a $un_b) (car-atom (collapse (match &self (TsgRng state $un_x $un_y) ($un_x $un_y)))))
          ($un_a2 (% (* $un_a 40014) 2147483563))
          ($un_b2 (% (* $un_b 40692) 2147483399))
          ($un_r (remove-atom &self (TsgRng state $un_a $un_b)))
          ($un_s (add-atom &self (TsgRng state $un_a2 $un_b2)))
          ($un_z (- $un_a2 $un_b2)))
     (/ (if (< $un_z 1) (+ $un_z 2147483562) $un_z) 2147483563)))

;;; logarithms

(= (tsg:ln $ln_x) (log-math 2.718281828459045 $ln_x))
; log (e^A + e^B), either may be the symbol neg (log 0)
(= (tsg:lse $ls_a $ls_b)
   (if (== $ls_a neg) $ls_b
   (if (== $ls_b neg) $ls_a
       (let $ls_m (max $ls_a $ls_b) (+ $ls_m (tsg:ln (+ (exp (- $ls_a $ls_m)) (exp (- $ls_b $ls_m)))))))))
(= (tsg:ln0 $l0_x) (if (> $l0_x 0) (tsg:ln $l0_x) neg))
(= (tsg:rising $ri_x $ri_k $ri_acc) (if (== $ri_k 0) $ri_acc (tsg:rising (+ $ri_x 1.0) (- $ri_k 1) (* $ri_acc $ri_x))))
; log Gamma(x), x > 0: Stirling's series from 7 on, the recurrence below
(= (tsg:lgamma $lg_x)
   (if (< $lg_x 7.0)
       (let $lg_k (- 7 (floor-math $lg_x))
         (- (tsg:lgamma (+ $lg_x $lg_k)) (tsg:ln (tsg:rising $lg_x $lg_k 1.0))))
       (let $lg_i (/ 1.0 $lg_x)
         (+ (- (* (- $lg_x 0.5) (tsg:ln $lg_x)) $lg_x)
            (+ 0.9189385332046727
               (* $lg_i (- 0.08333333333333333 (* (* $lg_i $lg_i) (- 0.002777777777777778 (* (* $lg_i $lg_i) 0.0007936507936507937))))))))))

;;; nodes

(= (tsg:level-struct? $lv_h) (if (== $lv_h level) True (if (== $lv_h lsucc) True (if (== $lv_h lmax) True (== $lv_h limax)))))
; a node's kind: proof, term or level if it can root a fragment, otherwise fixed
(= (tsg:kind-of $ko_e)
   (let $ko_h (car-atom $ko_e)
     (if (== (get-metatype $ko_h) Symbol)
         (if (term:proof-head? $ko_h) proof
         (if (== $ko_h lvl) level
         (if (tsg:level-struct? $ko_h) fixed
         (if (== $ko_h sort) fixed term))))
         fixed)))
; a fixed node's category is (fixed HEAD), never the bare head: a head may be a built-in name
(= (tsg:cat-of $co_e $co_kind)
   (if (== $co_kind fixed) (let $co_h (car-atom $co_e) (if (== (get-metatype $co_h) Symbol) (fixed $co_h) (fixed list))) $co_kind))
; a node's local form: its children as slots, a binder's name erased
(= (tsg:rule-list $rl_xs)
   (if (== $rl_xs ()) () (let $rl_x (car-atom $rl_xs) (cons-atom (if (term:expr? $rl_x) slot $rl_x) (tsg:rule-list (cdr-atom $rl_xs))))))
(= (tsg:rule-of $ro_e)
   (let $ro_h (car-atom $ro_e)
     (if (if (== (get-metatype $ro_h) Symbol) (term:binder? $ro_h) False)
         (cons-atom $ro_h (cons-atom _ (tsg:rule-list (cdr-atom (cdr-atom $ro_e)))))
         (tsg:rule-list $ro_e))))
(= (tsg:var-rule? $vr_r)
   (let $vr_h (car-atom $vr_r) (if (== $vr_h dbv) True (== $vr_h dbh))))
(= (tsg:fresh)
   (let* (($fr_n (car-atom (collapse (match &self (TsgNext count $fr_x) $fr_x))))
          ($fr_m (+ $fr_n 1))
          ($fr_r (remove-atom &self (TsgNext count $fr_n)))
          ($fr_a (add-atom &self (TsgNext count $fr_m))))
     $fr_n))
; sorted lists of free de Bruijn indices
(= (tsg:union $un_a $un_b)
   (if (== $un_a ()) $un_b (if (== $un_b ()) $un_a
       (let* (($un_x (car-atom $un_a)) ($un_y (car-atom $un_b)))
         (if (< $un_x $un_y) (cons-atom $un_x (tsg:union (cdr-atom $un_a) $un_b))
         (if (< $un_y $un_x) (cons-atom $un_y (tsg:union $un_a (cdr-atom $un_b)))
             (cons-atom $un_x (tsg:union (cdr-atom $un_a) (cdr-atom $un_b)))))))))
(= (tsg:unbind $ub_fv) (if (== $ub_fv ()) () (let $ub_k (car-atom $ub_fv) (if (== $ub_k 0) (tsg:unbind (cdr-atom $ub_fv)) (cons-atom (- $ub_k 1) (tsg:unbind (cdr-atom $ub_fv)))))))
(= (tsg:minfree $mf_fv) (if (== $mf_fv ()) 1000000 (car-atom $mf_fv)))
; (TsgNode ID KIND CAT RULE RK KIDS BODY MINFREE): RK the content key of (CAT RULE), KIDS the child
; nodes in order, BODY the position among them of a binder's body (-1 if none), MINFREE the least
; free index (1000000 if closed).
; Returns (ID FREE).
(= (tsg:build $bd_e $bd_parent)
   (let* (($bd_id (tsg:fresh))
          ($bd_kind (tsg:kind-of $bd_e))
          ($bd_cat (tsg:cat-of $bd_e $bd_kind))
          ($bd_rule (tsg:rule-of $bd_e))
          ($bd_rk (sha256 (repr ($bd_cat $bd_rule))))
          ($bd_h (car-atom $bd_e))
          ($bd_binder (if (== (get-metatype $bd_h) Symbol) (term:binder? $bd_h) False))
          ($bd_body (if $bd_binder (term:h3 $bd_e) none))
          ($bd_p (if (== $bd_parent none) done (add-atom &self (TsgParent $bd_id $bd_parent))))
          (($bd_kids $bd_bi $bd_fvk) (tsg:build-kids $bd_e $bd_id $bd_body 0 () -1 ()))
          ($bd_fv (if (tsg:var-rule? $bd_rule)
                      (tsg:union ((term:h1 $bd_e)) $bd_fvk)
                      $bd_fvk))
          ($bd_mf (tsg:minfree $bd_fv))
          ($bd_add (add-atom &self (TsgNode $bd_id $bd_kind $bd_cat $bd_rule $bd_rk $bd_kids $bd_bi $bd_mf))))
     ($bd_id $bd_fv)))
; the children: (KIDS BODY FREE); a binder's body contributes its free indices less its own
(= (tsg:build-kids $bk_xs $bk_id $bk_body $bk_i $bk_kids $bk_bi $bk_fv)
   (if (== $bk_xs ()) ((tsg:reverse $bk_kids ()) $bk_bi $bk_fv)
       (let $bk_x (car-atom $bk_xs)
         (if (term:expr? $bk_x)
             (let* ((($bk_c $bk_cfv) (tsg:build $bk_x $bk_id))
                    ($bk_isbody (if (== $bk_body none) False (== $bk_x $bk_body)))
                    ($bk_fv2 (tsg:union $bk_fv (if $bk_isbody (tsg:unbind $bk_cfv) $bk_cfv))))
               (tsg:build-kids (cdr-atom $bk_xs) $bk_id $bk_body (+ $bk_i 1) (cons-atom $bk_c $bk_kids)
                               (if $bk_isbody $bk_i $bk_bi) $bk_fv2))
             (tsg:build-kids (cdr-atom $bk_xs) $bk_id $bk_body $bk_i $bk_kids $bk_bi $bk_fv)))))
(= (tsg:reverse $rv_xs $rv_acc) (if (== $rv_xs ()) $rv_acc (tsg:reverse (cdr-atom $rv_xs) (cons-atom (car-atom $rv_xs) $rv_acc))))
(= (tsg:node $nd_u) (car-atom (collapse (match &self (TsgNode $nd_u $nd_k $nd_c $nd_r $nd_rk $nd_ks $nd_b $nd_m) ($nd_k $nd_c $nd_r $nd_rk $nd_ks $nd_b $nd_m)))))
(= (tsg:kind $kd_u) (car-atom (collapse (match &self (TsgNode $kd_u $kd_k $kd_c $kd_r $kd_rk $kd_ks $kd_b $kd_m) $kd_k))))
(= (tsg:bnd? $bn_u) (let $qz1 (collapse (match &self (TsgBnd $bn_u) yes)) (if (== $qz1 ()) False True)))

;;; fragments

; (TERM DECISIONS HOLES SIZE) of the fragment rooted at R; node OV counts as a root iff OB is 1 (OV
; none: the derivation as it is).  DECISIONS: (rule CAT RK) for every node, (stop KIND) or
; (expand KIND) at every child that can root a fragment.  HOLES: the nodes at its holes.  SIZE: its
; nodes.
(= (tsg:frag $fg_r $fg_ov $fg_ob)
   (let ($fg_t $fg_acc) (tsg:fn $fg_r $fg_ov $fg_ob (() () 0))
     (let ($fg_decs $fg_holes $fg_size) $fg_acc
       ($fg_t $fg_decs $fg_holes $fg_size))))
(= (tsg:root? $rt_k $rt_ov $rt_ob) (if (== $rt_k $rt_ov) (== $rt_ob 1) (tsg:bnd? $rt_k)))
(= (tsg:fn $fn_u $fn_ov $fn_ob $fn_acc)
   (let* ((($fn_kind $fn_cat $fn_rule $fn_rk $fn_kids $fn_bi $fn_mf) (tsg:node $fn_u))
          (($fn_d $fn_h $fn_s) $fn_acc)
          (($fn_terms $fn_acc2) (tsg:fn-kids $fn_kids $fn_ov $fn_ob
                                             ((cons-atom (rule $fn_cat $fn_rk) $fn_d) $fn_h (+ $fn_s 1)) ())))
     ((tsg:fill $fn_rule $fn_terms) $fn_acc2)))
(= (tsg:fn-kids $fk_ks $fk_ov $fk_ob $fk_acc $fk_terms)
   (if (== $fk_ks ()) ((tsg:reverse $fk_terms ()) $fk_acc)
       (let* (($fk_k (car-atom $fk_ks))
              ($fk_kk (tsg:kind $fk_k))
              (($fk_d $fk_h $fk_s) $fk_acc)
              (($fk_t $fk_acc2)
                 (if (== $fk_kk fixed) (tsg:fn $fk_k $fk_ov $fk_ob $fk_acc)
                     (if (tsg:root? $fk_k $fk_ov $fk_ob)
                         ((hole $fk_kk) ((cons-atom (stop $fk_kk) $fk_d) (cons-atom $fk_k $fk_h) $fk_s))
                         (tsg:fn $fk_k $fk_ov $fk_ob ((cons-atom (expand $fk_kk) $fk_d) $fk_h $fk_s))))))
         (tsg:fn-kids (cdr-atom $fk_ks) $fk_ov $fk_ob $fk_acc2 (cons-atom $fk_t $fk_terms)))))
; pairs are built as (pr A B): a tuple headed by data could be a call (a leaf may be a built-in name)
(= (tsg:fill-list $fl_xs $fl_ts)
   (if (== $fl_xs ()) (pr () $fl_ts)
       (let* (($fl_x (car-atom $fl_xs))
              ((pr $fl_y $fl_ts2) (if (== $fl_x slot) (pr (car-atom $fl_ts) (cdr-atom $fl_ts)) (pr $fl_x $fl_ts)))
              ((pr $fl_rest $fl_ts3) (tsg:fill-list (cdr-atom $fl_xs) $fl_ts2)))
         (pr (cons-atom $fl_y $fl_rest) $fl_ts3))))
(= (tsg:fill $fi_rule $fi_ts) (let (pr $fi_f $fi_r) (tsg:fill-list $fi_rule $fi_ts) $fi_f))
(= (tsg:key $ky_t) (sha256 (repr $ky_t)))
; the content key of a fragment's root form: the key of the node table's (CAT RULE) where it is rooted
(= (tsg:root-rk $rr_t $rr_k) (let* (($rr_c (tsg:cat-of $rr_t $rr_k)) ($rr_r (tsg:rule-of $rr_t))) (sha256 (repr ($rr_c $rr_r)))))

;;; the base measure: Polya urns over the base counts, one copy of a fragment's decisions per table

(= (tsg:get1 $g1_found $g1_default) (if (== $g1_found ()) $g1_default (car-atom $g1_found)))
(= (tsg:br $br_rk) (tsg:get1 (collapse (match &self (TsgBR $br_rk $br_n) $br_n)) 0))
(= (tsg:bt $bt_c) (tsg:get1 (collapse (match &self (TsgBT $bt_c $bt_n) $bt_n)) 0))
(= (tsg:bs $bs_k) (tsg:get1 (collapse (match &self (TsgBS $bs_k $bs_s $bs_e) ($bs_s $bs_e))) (0 0)))
(= (tsg:rc $rc_c) (tsg:get1 (collapse (match &self (TsgRC $rc_c $rc_n) $rc_n)) 1))
(= (tsg:alpha) (tsg:get1 (collapse (match &self (TsgAlpha base $al_a) $al_a)) 1))
(= (tsg:br-add $ba_rk $ba_dl)
   (let* (($ba_o (tsg:br $ba_rk)) ($ba_n (+ $ba_o $ba_dl))
          ($ba_x (if (== $ba_o 0) done (remove-atom &self (TsgBR $ba_rk $ba_o)))))
     (if (== $ba_n 0) done (add-atom &self (TsgBR $ba_rk $ba_n)))))
(= (tsg:bt-add $ta_c $ta_dl)
   (let* (($ta_o (tsg:bt $ta_c)) ($ta_n (+ $ta_o $ta_dl))
          ($ta_x (if (== $ta_o 0) done (remove-atom &self (TsgBT $ta_c $ta_o)))))
     (if (== $ta_n 0) done (add-atom &self (TsgBT $ta_c $ta_n)))))
(= (tsg:bs-add $sa_k $sa_which $sa_dl)
   (let* ((($sa_s $sa_e) (tsg:bs $sa_k))
          ($sa_s2 (if (== $sa_which stop) (+ $sa_s $sa_dl) $sa_s))
          ($sa_e2 (if (== $sa_which expand) (+ $sa_e $sa_dl) $sa_e))
          ($sa_x (remove-atom &self (TsgBS $sa_k $sa_s $sa_e))))
     (add-atom &self (TsgBS $sa_k $sa_s2 $sa_e2))))
;; Flags, (TsgFlag NAME VALUE), present from loading on: base-frozen holds the base counts and
;; (d, theta) fixed, hyper-frozen (d, theta) only (the controls' settings).  Every atom head the
;; sampler reads keeps an atom: a match on a head with none, right after a write, costs CeTTa time
;; in proportion to the whole space.
(= (tsg:flag $fl_n) (tsg:get1 (collapse (match &self (TsgFlag $fl_n $fl_v) $fl_v)) False))
(= (tsg:set-flag $sf_n $sf_v)
   (let $sf_o (collapse (match &self (TsgFlag $sf_n $sf_x) $sf_x))
     (let $sf_r (if (== $sf_o ()) done (remove-atom &self (TsgFlag $sf_n (car-atom $sf_o)))) (add-atom &self (TsgFlag $sf_n $sf_v)))))
(= (tsg:frozen?) (tsg:flag base-frozen))
(= (tsg:hyper-frozen?) (if (tsg:flag base-frozen) True (tsg:flag hyper-frozen)))
(= (tsg:base-apply $bq_decs $bq_dl) (if (tsg:frozen?) done (tsg:base-apply-each $bq_decs $bq_dl)))
(= (tsg:base-apply-each $bp_decs $bp_dl)
   (if (== $bp_decs ()) done
       (let* (($bp_x (car-atom $bp_decs))
              ($bp_u (if (== (car-atom $bp_x) rule)
                         (let* (($bp_c (term:h1 $bp_x)) ($bp_r (term:h2 $bp_x)) ($bp_a (tsg:br-add $bp_r $bp_dl)))
                           (tsg:bt-add $bp_c $bp_dl))
                         (tsg:bs-add (term:h1 $bp_x) (car-atom $bp_x) $bp_dl))))
         (tsg:base-apply-each (cdr-atom $bp_decs) $bp_dl))))
; association lists of (ITEM COUNT)
(= (tsg:loc $lc_l $lc_x)
   (if (== $lc_l ()) 0 (let (kv $lc_k $lc_n) (car-atom $lc_l) (if (== $lc_k $lc_x) $lc_n (tsg:loc (cdr-atom $lc_l) $lc_x)))))
(= (tsg:loc-inc $li_l $li_x)
   (if (== $li_l ()) ((kv $li_x 1))
       (let (kv $li_k $li_n) (car-atom $li_l)
         (if (== $li_k $li_x) (cons-atom (kv $li_k (+ $li_n 1)) (cdr-atom $li_l))
             (cons-atom (kv $li_k $li_n) (tsg:loc-inc (cdr-atom $li_l) $li_x))))))
; log P0 of a fragment's DECISIONS, the base counts increased by EXTRA's decisions: the product of
; each decision's Polya-urn predictive given the base and the decisions before it, which depends on
; the counts only (Mettapedia.ProbabilityTheory.Distributions.BetaBernoulliHorizon: seqProb_eq): per
; item seen M times on a base of B, (B + a)^(M rising); per urn, over its total.
(= (tsg:logp0 $l0_decs $l0_extra)
   (let* (($l0_h (tsg:histogram (msort $l0_decs) ()))
          ($l0_x (if (== $l0_extra ()) () (tsg:histogram (msort $l0_extra) ()))))
     (tsg:lp0-items $l0_h $l0_x () () 0.0)))
(= (tsg:hist-count $hc_h $hc_x) (tsg:loc $hc_h $hc_x))
(= (tsg:lrise $lr_b $lr_m) (- (tsg:lgamma (+ $lr_b $lr_m)) (tsg:lgamma $lr_b)))
; ITEMS: ((ITEM M) ..); CATS: per rule category (CAT M); KINDS: per kind (KIND STOPS EXPANDS)
(= (tsg:lp0-items $li_h $li_x $li_cats $li_kinds $li_acc)
   (if (== $li_h ()) (+ $li_acc (+ (tsg:lp0-cats $li_cats $li_x 0.0) (tsg:lp0-kinds $li_kinds $li_x 0.0)))
       (let* (((kv $li_item $li_m) (car-atom $li_h))
              ($li_extra (tsg:hist-count $li_x $li_item)))
         (if (== (car-atom $li_item) rule)
             (let* (($li_c (term:h1 $li_item)) ($li_r (term:h2 $li_item))
                    ($li_b (+ (+ (tsg:br $li_r) $li_extra) (/ (tsg:alpha) (tsg:rc $li_c)))))
               (tsg:lp0-items (cdr-atom $li_h) $li_x (tsg:add-to $li_cats $li_c $li_m) $li_kinds (+ $li_acc (tsg:lrise $li_b $li_m))))
             (let* (($li_k (term:h1 $li_item)) ($li_which (car-atom $li_item)))
               (tsg:lp0-items (cdr-atom $li_h) $li_x $li_cats (tsg:add-kind $li_kinds $li_k $li_which $li_m) $li_acc))))))
(= (tsg:add-to $at_l $at_k $at_m)
   (if (== $at_l ()) (($at_k $at_m))
       (let ($at_k2 $at_n) (car-atom $at_l)
         (if (== $at_k2 $at_k) (cons-atom ($at_k (+ $at_n $at_m)) (cdr-atom $at_l)) (cons-atom ($at_k2 $at_n) (tsg:add-to (cdr-atom $at_l) $at_k $at_m))))))
(= (tsg:add-kind $ak_l $ak_k $ak_which $ak_m)
   (if (== $ak_l ()) (if (== $ak_which stop) (($ak_k $ak_m 0)) (($ak_k 0 $ak_m)))
       (let ($ak_k2 $ak_s $ak_e) (car-atom $ak_l)
         (if (== $ak_k2 $ak_k)
             (cons-atom (if (== $ak_which stop) ($ak_k (+ $ak_s $ak_m) $ak_e) ($ak_k $ak_s (+ $ak_e $ak_m))) (cdr-atom $ak_l))
             (cons-atom ($ak_k2 $ak_s $ak_e) (tsg:add-kind (cdr-atom $ak_l) $ak_k $ak_which $ak_m))))))
; the extra decisions' totals per category and per kind
(= (tsg:extra-cat $ec_x $ec_c)
   (if (== $ec_x ()) 0
       (let (kv $ec_item $ec_m) (car-atom $ec_x)
         (+ (if (and (== (car-atom $ec_item) rule) (== (term:h1 $ec_item) $ec_c)) $ec_m 0) (tsg:extra-cat (cdr-atom $ec_x) $ec_c)))))
(= (tsg:lp0-cats $lc_cats $lc_x $lc_acc)
   (if (== $lc_cats ()) $lc_acc
       (let* ((($lc_c $lc_m) (car-atom $lc_cats))
              ($lc_b (+ (+ (tsg:bt $lc_c) (tsg:extra-cat $lc_x $lc_c)) (tsg:alpha))))
         (tsg:lp0-cats (cdr-atom $lc_cats) $lc_x (- $lc_acc (tsg:lrise $lc_b $lc_m))))))
(= (tsg:lp0-kinds $lk_kinds $lk_x $lk_acc)
   (if (== $lk_kinds ()) $lk_acc
       (let* ((($lk_k $lk_s $lk_e) (car-atom $lk_kinds))
              (($lk_bs $lk_be) (tsg:bs $lk_k))
              ($lk_s0 (+ (+ $lk_bs (tsg:hist-count $lk_x (stop $lk_k))) 1))
              ($lk_e0 (+ (+ $lk_be (tsg:hist-count $lk_x (expand $lk_k))) 1)))
         (tsg:lp0-kinds (cdr-atom $lk_kinds) $lk_x
            (+ $lk_acc (- (+ (tsg:lrise $lk_s0 $lk_s) (tsg:lrise $lk_e0 $lk_e)) (tsg:lrise (+ $lk_s0 $lk_e0) (+ $lk_s $lk_e))))))))

;;; restaurants: one per kind; customers are fragments, each at a table
;
; (TsgDish KEY KIND n t): a dish's customers and tables; (TsgTable TID KEY KIND SIZE): one of its
; tables; (TsgSeat R TID): the fragment rooted at node R sits at table TID; (TsgAt KEY R): R roots a
; fragment of dish KEY.  A customer leaves its own table.  A customer joining one of its dish's
; tables takes it in proportion to its size less d: a customer of the dish drawn uniformly (its
; table so in proportion to its size), the table taken with probability 1 - d / size and the draw
; made again otherwise.

(= (tsg:dish $ds_key) (tsg:get1 (collapse (match &self (TsgDish $ds_key $ds_k $ds_n $ds_t) ($ds_n $ds_t))) (0 0)))
(= (tsg:rest $rs_k) (car-atom (collapse (match &self (TsgRest $rs_k $rs_n $rs_t) ($rs_n $rs_t)))))
(= (tsg:hyp $hy_k) (car-atom (collapse (match &self (TsgHyp $hy_k $hy_d $hy_th) ($hy_d $hy_th)))))
; log of the predictive probability of dish KEY in restaurant K, its counts raised by DN DT and the
; restaurant's by DN2 DT2
(= (tsg:logpred $pd_k $pd_key $pd_lp0 $pd_dn $pd_dt $pd_dn2 $pd_dt2)
   (let* ((($pd_n $pd_t) (tsg:dish $pd_key)) (($pd_N $pd_T) (tsg:rest $pd_k)) (($pd_d $pd_th) (tsg:hyp $pd_k))
          ($pd_old (- (+ $pd_n $pd_dn) (* $pd_d (+ $pd_t $pd_dt))))
          ($pd_new (+ $pd_th (* $pd_d (+ $pd_T $pd_dt2)))))
     (- (tsg:lse (tsg:ln0 $pd_old) (+ (tsg:ln $pd_new) $pd_lp0)) (tsg:ln (+ (+ $pd_N $pd_dn2) $pd_th)))))
(= (tsg:set-dish $sd_key $sd_k $sd_n $sd_t $sd_n2 $sd_t2)
   (let $sd_r (if (== $sd_n 0) done (remove-atom &self (TsgDish $sd_key $sd_k $sd_n $sd_t)))
     (if (== $sd_n2 0) done (add-atom &self (TsgDish $sd_key $sd_k $sd_n2 $sd_t2)))))
(= (tsg:set-rest $sr_k $sr_dn $sr_dt)
   (let* ((($sr_n $sr_t) (tsg:rest $sr_k)) ($sr_n2 (+ $sr_n $sr_dn)) ($sr_t2 (+ $sr_t $sr_dt))
          ($sr_r (remove-atom &self (TsgRest $sr_k $sr_n $sr_t))))
     (add-atom &self (TsgRest $sr_k $sr_n2 $sr_t2))))
; histograms of table sizes, ((kv SIZE COUNT) ..), for the partition function
(= (tsg:hist-add $ha_h $ha_s $ha_dl)
   (if (== $ha_h ()) (if (> $ha_dl 0) ((kv $ha_s $ha_dl)) ())
       (let (kv $ha_k $ha_c) (car-atom $ha_h)
         (if (== $ha_k $ha_s)
             (let $ha_c2 (+ $ha_c $ha_dl) (if (== $ha_c2 0) (cdr-atom $ha_h) (cons-atom (kv $ha_k $ha_c2) (cdr-atom $ha_h))))
             (cons-atom (kv $ha_k $ha_c) (tsg:hist-add (cdr-atom $ha_h) $ha_s $ha_dl))))))
(= (tsg:table-size $ts_tid) (tsg:get1 (collapse (match &self (TsgTable $ts_tid $ts_key $ts_k $ts_s) $ts_s)) 0))
(= (tsg:seat-of $so_r) (car-atom (collapse (match &self (TsgSeat $so_r $so_t) $so_t))))
(= (tsg:new-table)
   (let* (($nt_n (car-atom (collapse (match &self (TsgNext table $nt_x) $nt_x))))
          ($nt_r (remove-atom &self (TsgNext table $nt_n))) ($nt_n2 (+ $nt_n 1)) ($nt_a (add-atom &self (TsgNext table $nt_n2))))
     $nt_n))
(= (tsg:note-dish $nd_key $nd_k $nd_term $nd_size)
   (let $qz2 (collapse (match &self (TsgInfo $nd_key $nd_ik $nd_it $nd_is) yes)) (if (== $qz2 ())
       (let* (($nd_rk (tsg:root-rk $nd_term $nd_k)) ($nd_a (add-atom &self (TsgByRoot $nd_rk $nd_key))))
         (add-atom &self (TsgInfo $nd_key $nd_k $nd_term $nd_size)))
       done)))
; the fragment rooted at R, of dish KEY, sits at table TID: one of the dish's tables, or (new, or a
; number that names no table) a table it opens, adding the dish's decisions to the base; the table
(= (tsg:sit $si_r $si_key $si_k $si_decs $si_term $si_size $si_tid)
   (let* ((($si_n $si_t) (tsg:dish $si_key))
          ($si_s (if (== $si_tid new) 0 (tsg:table-size $si_tid)))
          ($si_fresh (== $si_s 0))
          ($si_id (if (== $si_tid new) (tsg:new-table) $si_tid))
          ($si_info (if (== $si_n 0) (tsg:note-dish $si_key $si_k $si_term $si_size) done))
          ($si_tb (if $si_fresh done (remove-atom &self (TsgTable $si_id $si_key $si_k $si_s))))
          ($si_s2 (+ $si_s 1))
          ($si_ta (add-atom &self (TsgTable $si_id $si_key $si_k $si_s2)))
          ($si_se (add-atom &self (TsgSeat $si_r $si_id)))
          ($si_at (add-atom &self (TsgAt $si_key $si_r)))
          ($si_a (tsg:set-dish $si_key $si_k $si_n $si_t (+ $si_n 1) (if $si_fresh (+ $si_t 1) $si_t)))
          ($si_c (tsg:set-rest $si_k 1 (if $si_fresh 1 0)))
          ($si_bx (if $si_fresh (tsg:base-apply $si_decs 1) done)))
     $si_id))
; the fragment rooted at R, of dish KEY, leaves its table; an emptied table's decisions leave the
; base; the table
(= (tsg:leave $lv_r $lv_key $lv_k $lv_decs)
   (let* ((($lv_n $lv_t) (tsg:dish $lv_key))
          ($lv_id (tsg:seat-of $lv_r))
          ($lv_s (tsg:table-size $lv_id))
          ($lv_emptied (== $lv_s 1))
          ($lv_tb (remove-atom &self (TsgTable $lv_id $lv_key $lv_k $lv_s)))
          ($lv_s2 (- $lv_s 1))
          ($lv_ta (if $lv_emptied done (add-atom &self (TsgTable $lv_id $lv_key $lv_k $lv_s2))))
          ($lv_se (remove-atom &self (TsgSeat $lv_r $lv_id)))
          ($lv_at (remove-atom &self (TsgAt $lv_key $lv_r)))
          ($lv_a (tsg:set-dish $lv_key $lv_k $lv_n $lv_t (- $lv_n 1) (if $lv_emptied (- $lv_t 1) $lv_t)))
          ($lv_c (tsg:set-rest $lv_k -1 (if $lv_emptied -1 0)))
          ($lv_x (if $lv_emptied (tsg:base-apply $lv_decs -1) done)))
     $lv_id))
; one of dish KEY's tables, in proportion to its size less d
(= (tsg:join-table $jt_key $jt_d)
   (let $jt_rs (collapse (match &self (TsgAt $jt_key $jt_r) $jt_r)) (tsg:join-try $jt_rs (size-atom $jt_rs) $jt_d)))
(= (tsg:join-try $jy_rs $jy_n $jy_d)
   (let* (($jy_id (tsg:seat-of (index-atom $jy_rs (floor-math (* (tsg:uniform) $jy_n)))))
          ($jy_s (tsg:table-size $jy_id)))
     (if (< (* (tsg:uniform) $jy_s) (- $jy_s $jy_d)) $jy_id (tsg:join-try $jy_rs $jy_n $jy_d))))
; the fragment rooted at R sits: at one of its dish's tables in proportion to its size less d, or at
; a new one in proportion to (theta + d T) P0; the table
(= (tsg:seat $se_r $se_key $se_k $se_decs $se_lp0 $se_term $se_size)
   (let* ((($se_n $se_t) (tsg:dish $se_key)) (($se_N $se_T) (tsg:rest $se_k)) (($se_d $se_th) (tsg:hyp $se_k))
          ($se_lnew (+ (tsg:ln (+ $se_th (* $se_d $se_T))) $se_lp0))
          ($se_fresh (if (== $se_n 0) True
                         (< (tsg:ln (tsg:uniform)) (- $se_lnew (tsg:lse (tsg:ln (- $se_n (* $se_d $se_t))) $se_lnew))))))
     (tsg:seat-as $se_r $se_key $se_k $se_decs $se_term $se_size $se_fresh)))
; the same, a new table or not (FRESH) decided
(= (tsg:seat-as $sq_r $sq_key $sq_k $sq_decs $sq_term $sq_size $sq_fresh)
   (tsg:sit $sq_r $sq_key $sq_k $sq_decs $sq_term $sq_size
            (if $sq_fresh new (let ($sq_d $sq_th) (tsg:hyp $sq_k) (tsg:join-table $sq_key $sq_d)))))
(= (tsg:unseat $us_r $us_key $us_k $us_decs) (tsg:leave $us_r $us_key $us_k $us_decs))

;;; the Gibbs step at node V: is V a fragment root?

(= (tsg:up-root $ur_v)
   (let $ur_p (car-atom (collapse (match &self (TsgParent $ur_v $ur_x) $ur_x)))
     (if (tsg:bnd? $ur_p) $ur_p (tsg:up-root $ur_p))))
(= (tsg:step $sp_v)
   (let* (($sp_r (tsg:up-root $sp_v)) ($sp_rk (tsg:kind $sp_r)) ($sp_vk (tsg:kind $sp_v)) ($sp_b (tsg:bnd? $sp_v))
          (($sp_tu $sp_du $sp_hu $sp_su) (tsg:frag $sp_r $sp_v 1))
          (($sp_td $sp_dd $sp_hd $sp_sd) (tsg:frag $sp_v none 0))
          (($sp_tm $sp_dm $sp_hm $sp_sm) (tsg:frag $sp_r $sp_v 0))
          ($sp_ku (tsg:key $sp_tu)) ($sp_kd (tsg:key $sp_td)) ($sp_km (tsg:key $sp_tm))
          ($sp_out (if $sp_b
                       (let $sp_o1 (tsg:unseat $sp_r $sp_ku $sp_rk $sp_du) (tsg:unseat $sp_v $sp_kd $sp_vk $sp_dd))
                       (tsg:unseat $sp_r $sp_km $sp_rk $sp_dm)))
          ($sp_lp0u (tsg:logp0 $sp_du ())) ($sp_lp0d (tsg:logp0 $sp_dd ())) ($sp_lp0m (tsg:logp0 $sp_dm ()))
          ((pr $sp_jn $sp_fr) (tsg:split-parts $sp_rk $sp_vk $sp_ku $sp_du $sp_lp0u $sp_kd $sp_dd $sp_lp0d))
          ($sp_split (tsg:lse $sp_jn $sp_fr))
          ($sp_merge (tsg:logpred $sp_rk $sp_km $sp_lp0m 0 0 0 0))
          ($sp_choose-split (< (tsg:ln (tsg:uniform)) (- 0.0 (tsg:lse 0.0 (- $sp_merge $sp_split))))))
     (if $sp_choose-split
         ; the up fragment opens a table or joins one with the probabilities that include how the
         ; down fragment then fares (a new table raises T and the base)
         (let* (($sp_upfresh (if (== $sp_jn neg) True (< (tsg:ln (tsg:uniform)) (- $sp_fr $sp_split))))
                ($sp_a1 (tsg:seat-as $sp_r $sp_ku $sp_rk $sp_du $sp_tu $sp_su $sp_upfresh))
                ($sp_lp0d2 (if $sp_upfresh (tsg:logp0 $sp_dd ()) $sp_lp0d))
                ($sp_a2 (tsg:seat $sp_v $sp_kd $sp_vk $sp_dd $sp_lp0d2 $sp_td $sp_sd)))
           (if $sp_b done (add-atom &self (TsgBnd $sp_v))))
         (let $sp_a3 (tsg:seat $sp_r $sp_km $sp_rk $sp_dm $sp_lp0m $sp_tm $sp_sm)
           (if $sp_b (remove-atom &self (TsgBnd $sp_v)) done)))))
; (pr JOIN FRESH): log P(up joins a table, then down) and log P(up opens one, then down)
(= (tsg:split-parts $sl_rk $sl_vk $sl_ku $sl_du $sl_lp0u $sl_kd $sl_dd $sl_lp0d)
   (let* (($sl_lpu (tsg:logpred $sl_rk $sl_ku $sl_lp0u 0 0 0 0))
          (($sl_n $sl_t) (tsg:dish $sl_ku))
          (($sl_N $sl_T) (tsg:rest $sl_rk)) (($sl_d $sl_th) (tsg:hyp $sl_rk))
          ($sl_lold (tsg:ln0 (- $sl_n (* $sl_d $sl_t))))
          ($sl_lnew (+ (tsg:ln (+ $sl_th (* $sl_d $sl_T))) $sl_lp0u))
          ($sl_ltot (tsg:lse $sl_lold $sl_lnew))
          ($sl_same (if (== $sl_kd $sl_ku) 1 0))
          ($sl_rest (if (== $sl_vk $sl_rk) 1 0))
          ($sl_join (if (== $sl_lold neg) neg
                        (+ (- $sl_lold $sl_ltot)
                           (tsg:logpred $sl_vk $sl_kd $sl_lp0d $sl_same 0 $sl_rest 0))))
          ($sl_fresh (+ (- $sl_lnew $sl_ltot)
                        (tsg:logpred $sl_vk $sl_kd (tsg:logp0 $sl_dd $sl_du) $sl_same $sl_same $sl_rest $sl_rest))))
     (pr (if (== $sl_join neg) neg (+ $sl_lpu $sl_join)) (+ $sl_lpu $sl_fresh))))

;;; loading: every node that can root a fragment starts as a root (the derivation of a context-free
;;; grammar), and the sampler joins what recurs

(= (tsg:eligible? $el_k) (if (== $el_k proof) True (if (== $el_k term) True (== $el_k level))))
; a proof as Lean is given it: a cut (phave P h p) is written as p, so it is read as p
(= (tsg:strip $sp_t)
   (if (term:expr? $sp_t)
       (if (== (car-atom $sp_t) phave) (tsg:strip (term:h3 $sp_t)) (tsg:strip-list $sp_t))
       $sp_t))
(= (tsg:strip-list $sq_xs) (if (== $sq_xs ()) () (cons-atom (tsg:strip (car-atom $sq_xs)) (tsg:strip-list (cdr-atom $sq_xs)))))
(= (tsg:init-node $in_u)
   (let* ((($in_k $in_c $in_r $in_rk $in_ks $in_bi $in_mf) (tsg:node $in_u))
          ($in_a (if (tsg:eligible? $in_k) (if (tsg:bnd? $in_u) done (add-atom &self (TsgBnd $in_u))) done)))
     (tsg:init-kids $in_ks)))
(= (tsg:init-kids $ik_ks) (if (== $ik_ks ()) done (let $ik_x (tsg:init-node (car-atom $ik_ks)) (tsg:init-kids (cdr-atom $ik_ks)))))
(= (tsg:load-theorems $lt_cs)
   (if (== $lt_cs ()) done
       (let* (($lt_c (car-atom $lt_cs))
              ($lt_ps (collapse (match &self (TransportProof $lt_c $lt_p) $lt_p)))
              ($lt_x (if (== $lt_ps ()) done
                         (let* ((($lt_id $lt_fv) (tsg:build (tsg:strip (term:db (car-atom $lt_ps) ())) none))
                                ($lt_r (add-atom &self (TsgRoot $lt_id $lt_c)))
                                ($lt_b (add-atom &self (TsgBnd $lt_id))))
                           (tsg:init-node $lt_id)))))
         (tsg:load-theorems (cdr-atom $lt_cs)))))
; the number of distinct local forms per category, for the symmetric Dirichlet priors
(= (tsg:count-rules)
   (let $cr_pairs (collapse (match &self (TsgNode $cr_i $cr_k $cr_c $cr_r $cr_rk $cr_ks $cr_b $cr_m) (pr $cr_c $cr_rk)))
     (tsg:count-rules-of (tsg:distinct (msort $cr_pairs) ()) ())))
(= (tsg:distinct $dt_xs $dt_last)
   (if (== $dt_xs ()) () (let $dt_x (car-atom $dt_xs) (if (== $dt_x $dt_last) (tsg:distinct (cdr-atom $dt_xs) $dt_last) (cons-atom $dt_x (tsg:distinct (cdr-atom $dt_xs) $dt_x))))))
(= (tsg:count-rules-of $cro_ps $cro_acc)
   (if (== $cro_ps ())
       (tsg:store-rc $cro_acc)
       (let (pr $cro_c $cro_r) (car-atom $cro_ps) (tsg:count-rules-of (cdr-atom $cro_ps) (tsg:loc-inc $cro_acc $cro_c)))))
(= (tsg:store-rc $sr_l) (if (== $sr_l ()) done (let (kv $sr_c $sr_n) (car-atom $sr_l) (let $sr_a (add-atom &self (TsgRC $sr_c $sr_n)) (tsg:store-rc (cdr-atom $sr_l))))))
; seat every fragment of the initial derivation, in node order
(= (tsg:seat-all $sa_i $sa_n)
   (if (>= $sa_i $sa_n) done
       (let $sa_x (if (tsg:bnd? $sa_i)
                      (let* ((($sa_t $sa_d $sa_h $sa_s) (tsg:frag $sa_i none 0)))
                        (tsg:seat $sa_i (tsg:key $sa_t) (tsg:kind $sa_i) $sa_d (tsg:logp0 $sa_d ()) $sa_t $sa_s))
                      done)
         (tsg:seat-all (+ $sa_i 1) $sa_n))))
(= (tsg:nodes) (car-atom (collapse (match &self (TsgNext count $nn_x) $nn_x))))
(= (tsg:load $ld_order $ld_seed)
   (let* (($ld_f1 (tsg:set-flag base-frozen False)) ($ld_f2 (tsg:set-flag hyper-frozen False))
          ($ld_f3 (add-atom &self (TsgIn none 0.0 0.0))) ($ld_f4 (add-atom &self (TyClaim none))) ($ld_f5 (add-atom &self (TyKept none)))
          ($ld_f6 (add-atom &self (TsgPost none 0 0 0.0))) ($ld_f7 (add-atom &self (TsgSamples count 0)))
          ($ld_f8 (add-atom &self (TsgNext table 0))) ($ld_f9 (add-atom &self (TsgTable none none none 0))) ($ld_f10 (add-atom &self (TsgSeat none none)))
          ($ld_a (add-atom &self (TsgNext count 0)))
          ($ld_b (tsg:seed $ld_seed))
          ($ld_c (add-atom &self (TsgAlpha base 1)))
          ($ld_k1 (add-atom &self (TsgHyp proof 0.5 1.0))) ($ld_k2 (add-atom &self (TsgHyp term 0.5 1.0))) ($ld_k3 (add-atom &self (TsgHyp level 0.5 1.0)))
          ($ld_r1 (add-atom &self (TsgRest proof 0 0))) ($ld_r2 (add-atom &self (TsgRest term 0 0))) ($ld_r3 (add-atom &self (TsgRest level 0 0)))
          ($ld_s1 (add-atom &self (TsgBS proof 0 0))) ($ld_s2 (add-atom &self (TsgBS term 0 0))) ($ld_s3 (add-atom &self (TsgBS level 0 0)))
          ($ld_t (tsg:load-theorems $ld_order))
          ($ld_rc (tsg:count-rules))
          ($ld_seat (tsg:seat-all 0 (tsg:nodes))))
     (println! (tsg-loaded (nodes (tsg:nodes)) (roots (tsg:count-of TsgBnd))))))
(= (tsg:count-of TsgBnd) (term:length (collapse (match &self (TsgBnd $co_x) $co_x))))

;;; a sweep: every node that is not a theorem's root, in node order, then (d, theta) per kind

(= (tsg:sweep-nodes $sw_i $sw_n)
   (if (>= $sw_i $sw_n) done
       (let $sw_x (if (tsg:steppable? $sw_i) (tsg:step $sw_i) done)
         (tsg:sweep-nodes (+ $sw_i 1) $sw_n))))
(= (tsg:steppable? $st_u)
   (if (tsg:eligible? (tsg:kind $st_u))
       (let $qz3 (collapse (match &self (TsgRoot $st_u $st_c) yes)) (== $qz3 ()))
       False))
(= (tsg:sweep)
   (let* (($sw_a (tsg:sweep-nodes 0 (tsg:nodes)))
          ($sw_h (if (tsg:hyper-frozen?) done
                     (let* (($sw_b (tsg:hyper proof)) ($sw_c (tsg:hyper term))) (tsg:hyper level)))))
     (tsg:summary)))
(= (tsg:summary)
   (println! (tsg-state (roots (tsg:count-of TsgBnd)) (log-joint (tsg:log-joint))
                        (proof (tsg:rest proof) (tsg:hyp proof)) (term (tsg:rest term) (tsg:hyp term)) (level (tsg:rest level) (tsg:hyp level)))))
; The log probability of the derivation with its seating, exactly: per kind, the partition function of
; its table sizes; and the base urns, each the probability of the decisions its tables hold (rules
; per category, stops and expansions per kind), which depends on the counts only.  A chain that has
; mixed holds it level.
(= (tsg:log-joint)
   (+ (+ (tsg:log-eppf proof) (+ (tsg:log-eppf term) (tsg:log-eppf level))) (tsg:log-base)))
(= (tsg:log-eppf $le_k)
   (let* ((($le_n $le_T) (tsg:rest $le_k)) (($le_d $le_th) (tsg:hyp $le_k)))
     (if (== $le_T 0) 0.0 (tsg:eppf $le_d $le_th $le_n $le_T (tsg:merge-hists (tsg:sizes-of-kind $le_k) ())))))
(= (tsg:log-base)
   (let* (($lb_rules (collapse (match &self (TsgNode $lb_i $lb_k $lb_c $lb_r $lb_rk $lb_ks $lb_b $lb_m) (pr $lb_c $lb_rk))))
          ($lb_distinct (tsg:distinct (msort $lb_rules) ()))
          ($lb_r (tsg:log-base-rules $lb_distinct 0.0))
          ($lb_cats (collapse (match &self (TsgRC $lb_c2 $lb_n2) $lb_c2)))
          ($lb_t (tsg:log-base-totals $lb_cats 0.0))
          ($lb_s (tsg:log-base-stops (proof term level) 0.0)))
     (+ (- $lb_r $lb_t) $lb_s)))
(= (tsg:log-base-rules $lr_ps $lr_acc)
   (if (== $lr_ps ()) $lr_acc
       (let* (((pr $lr_c $lr_rk) (car-atom $lr_ps)) ($lr_n (tsg:br $lr_rk)))
         (tsg:log-base-rules (cdr-atom $lr_ps) (+ $lr_acc (tsg:lrise (/ (tsg:alpha) (tsg:rc $lr_c)) $lr_n))))))
(= (tsg:log-base-totals $lt_cs $lt_acc)
   (if (== $lt_cs ()) $lt_acc
       (let $lt_c (car-atom $lt_cs) (tsg:log-base-totals (cdr-atom $lt_cs) (+ $lt_acc (tsg:lrise (tsg:alpha) (tsg:bt $lt_c)))))))
(= (tsg:log-base-stops $ls_ks $ls_acc)
   (if (== $ls_ks ()) $ls_acc
       (let* (($ls_k (car-atom $ls_ks)) (($ls_s $ls_e) (tsg:bs $ls_k)))
         (tsg:log-base-stops (cdr-atom $ls_ks)
            (+ $ls_acc (- (+ (tsg:lrise 1.0 $ls_s) (tsg:lrise 1.0 $ls_e)) (tsg:lrise 2.0 (+ $ls_s $ls_e))))))))

;;; (d, theta) per kind: the exact posterior on a grid from the seating (the Pitman-Yor EPPF),
;;; under a uniform prior on the grid
(= (tsg:sizes-of-kind $sk_k)
   (let $sk_ss (collapse (match &self (TsgTable $sk_tid $sk_key $sk_k $sk_s) (if (== $sk_tid none) (empty) $sk_s)))
     ((tsg:histogram (msort $sk_ss) ()))))
(= (tsg:histogram $hg_xs $hg_acc)
   (if (== $hg_xs ()) $hg_acc
       (let $hg_x (car-atom $hg_xs)
         (if (== $hg_acc ()) (tsg:histogram (cdr-atom $hg_xs) ((kv $hg_x 1)))
             (let (kv $hg_k $hg_c) (car-atom $hg_acc)
               (if (== $hg_k $hg_x) (tsg:histogram (cdr-atom $hg_xs) (cons-atom (kv $hg_k (+ $hg_c 1)) (cdr-atom $hg_acc)))
                   (tsg:histogram (cdr-atom $hg_xs) (cons-atom (kv $hg_x 1) $hg_acc))))))))
; log EPPF: sum_{j<T} log(theta + j d) - log (theta+1)^(n-1) + sum_tables log (1-d)^(s-1)
(= (tsg:eppf $ep_d $ep_th $ep_n $ep_T $ep_hist)
   (let* (($ep_a (if (== $ep_T 0) 0.0
                     (if (== $ep_d 0.0) (* (- $ep_T 1) (tsg:ln $ep_th))
                         (+ (* (- $ep_T 1) (tsg:ln $ep_d))
                            (- (tsg:lgamma (+ (/ $ep_th $ep_d) $ep_T)) (tsg:lgamma (+ (/ $ep_th $ep_d) 1.0)))))))
          ($ep_b (- (tsg:lgamma (+ $ep_th $ep_n)) (tsg:lgamma (+ $ep_th 1.0))))
          ($ep_c (tsg:eppf-tables $ep_d $ep_hist 0.0)))
     (- (+ $ep_a $ep_c) $ep_b)))
(= (tsg:eppf-tables $et_d $et_hist $et_acc)
   (if (== $et_hist ()) $et_acc
       (let (kv $et_s $et_c) (car-atom $et_hist)
         (tsg:eppf-tables $et_d (cdr-atom $et_hist)
            (+ $et_acc (* $et_c (- (tsg:lgamma (- $et_s $et_d)) (tsg:lgamma (- 1.0 $et_d)))))))))
(= (tsg:grid-d) (0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.95))
(= (tsg:grid-th) (0.1 0.3 1.0 3.0 10.0 30.0 100.0 300.0 1000.0 3000.0))
(= (tsg:grid-points $gp_ds $gp_ths)
   (if (== $gp_ds ()) ()
       (term:concat (tsg:grid-row (car-atom $gp_ds) $gp_ths) (tsg:grid-points (cdr-atom $gp_ds) $gp_ths))))
(= (tsg:grid-row $gr_d $gr_ths) (if (== $gr_ths ()) () (cons-atom ($gr_d (car-atom $gr_ths)) (tsg:grid-row $gr_d (cdr-atom $gr_ths)))))
(= (tsg:merge-hists $mh_hs $mh_acc)
   (if (== $mh_hs ()) $mh_acc (tsg:merge-hists (cdr-atom $mh_hs) (tsg:merge-one (car-atom $mh_hs) $mh_acc))))
(= (tsg:merge-one $mo_h $mo_acc)
   (if (== $mo_h ()) $mo_acc (let (kv $mo_s $mo_c) (car-atom $mo_h) (tsg:merge-one (cdr-atom $mo_h) (tsg:hist-add $mo_acc $mo_s $mo_c)))))
(= (tsg:hyper $hp_k)
   (let* ((($hp_n $hp_T) (tsg:rest $hp_k)))
     (if (< $hp_T 2) done
         (let* (($hp_hist (tsg:merge-hists (tsg:sizes-of-kind $hp_k) ()))
                ($hp_pts (tsg:grid-points (tsg:grid-d) (tsg:grid-th)))
                ($hp_lls (tsg:grid-lls $hp_pts $hp_n $hp_T $hp_hist))
                ($hp_max (tsg:max-ll $hp_lls -1.0e300))
                ($hp_tot (tsg:sum-exp $hp_lls $hp_max 0.0))
                (($hp_d $hp_th) (tsg:pick $hp_lls $hp_max (* (tsg:uniform) $hp_tot)))
                (($hp_d0 $hp_th0) (tsg:hyp $hp_k))
                ($hp_r (remove-atom &self (TsgHyp $hp_k $hp_d0 $hp_th0))))
           (add-atom &self (TsgHyp $hp_k $hp_d $hp_th))))))
(= (tsg:grid-lls $gl_pts $gl_n $gl_T $gl_hist)
   (if (== $gl_pts ()) ()
       (let ($gl_d $gl_th) (car-atom $gl_pts)
         (cons-atom ($gl_d $gl_th (tsg:eppf $gl_d $gl_th $gl_n $gl_T $gl_hist)) (tsg:grid-lls (cdr-atom $gl_pts) $gl_n $gl_T $gl_hist)))))
(= (tsg:max-ll $ml_xs $ml_m) (if (== $ml_xs ()) $ml_m (let ($ml_d $ml_th $ml_l) (car-atom $ml_xs) (tsg:max-ll (cdr-atom $ml_xs) (max $ml_m $ml_l)))))
(= (tsg:sum-exp $se_xs $se_m $se_acc) (if (== $se_xs ()) $se_acc (let ($se_d $se_th $se_l) (car-atom $se_xs) (tsg:sum-exp (cdr-atom $se_xs) $se_m (+ $se_acc (exp (- $se_l $se_m)))))))
(= (tsg:pick $pk_xs $pk_m $pk_u)
   (let ($pk_d $pk_th $pk_l) (car-atom $pk_xs)
     (let $pk_w (exp (- $pk_l $pk_m))
       (if (or (< $pk_u $pk_w) (== (cdr-atom $pk_xs) ())) ($pk_d $pk_th) (tsg:pick (cdr-atom $pk_xs) $pk_m (- $pk_u $pk_w))))))

;;; checks and reports

; recount: the state against the derivation.  mismatched: dishes whose customers or tables disagree
; with the fragments in place; index-mismatched: roots missing from the index or entries without a
; root; rest-mismatched: restaurants whose totals are not their dishes' sums; base-mismatched: base
; counts that are not the decisions their tables hold.
(= (tsg:recount)
   (let* (($rc_pairs (collapse (match &self (TsgBnd $rc_u) (let ($rc_t $rc_d $rc_h $rc_s) (tsg:frag $rc_u none 0) (pr (tsg:key $rc_t) $rc_u)))))
          ($rc_keys (tsg:pr-firsts $rc_pairs ()))
          ($rc_hist (tsg:histogram (msort $rc_keys) ()))
          ($rc_bad (tsg:recount-check $rc_hist 0))
          ($rc_dishes (collapse (match &self (TsgDish $rc_k $rc_kd $rc_n $rc_t3) $rc_k)))
          ($rc_ix (tsg:index-bad $rc_pairs 0))
          ($rc_nix (term:length (collapse (match &self (TsgAt $rc_ik $rc_ir) $rc_ir))))
          ($rc_nseat (- (term:length (collapse (match &self (TsgSeat $rc_su $rc_st) $rc_su))) 1))
          ($rc_rest (tsg:rest-bad (proof term level) 0))
          ($rc_base (tsg:base-bad)))
     (println! (tsg-recount (fragments (term:length $rc_keys)) (dishes (term:length $rc_hist)) (stored-dishes (term:length $rc_dishes))
                            (mismatched $rc_bad) (index-mismatched (+ $rc_ix (if (and (== $rc_nix (term:length $rc_keys)) (== $rc_nseat (term:length $rc_keys))) 0 1)))
                            (rest-mismatched $rc_rest) (base-mismatched $rc_base)))))
(= (tsg:pr-firsts $pf_xs $pf_acc) (if (== $pf_xs ()) $pf_acc (let (pr $pf_a $pf_b) (car-atom $pf_xs) (tsg:pr-firsts (cdr-atom $pf_xs) (cons-atom $pf_a $pf_acc)))))
; a root is indexed under its fragment's key, and sits at one of that dish's tables
(= (tsg:index-bad $ib_ps $ib_acc)
   (if (== $ib_ps ()) $ib_acc
       (let* (((pr $ib_k $ib_u) (car-atom $ib_ps))
              ($ib_at (let $qz4 (collapse (match &self (TsgAt $ib_k $ib_u) yes)) (if (== $qz4 ()) False True)))
              ($ib_seats (collapse (match &self (TsgSeat $ib_u $ib_t) $ib_t)))
              ($ib_ok (if (== (size-atom $ib_seats) 1)
                          (let $ib_tid (car-atom $ib_seats) (let $qz5 (collapse (match &self (TsgTable $ib_tid $ib_k $ib_kd $ib_s) yes)) (if (== $qz5 ()) False True)))
                          False)))
         (tsg:index-bad (cdr-atom $ib_ps) (if (and $ib_at $ib_ok) $ib_acc (+ $ib_acc 1))))))
(= (tsg:rest-bad $rb_ks $rb_acc)
   (if (== $rb_ks ()) $rb_acc
       (let* (($rb_k (car-atom $rb_ks))
              ($rb_nts (collapse (match &self (TsgDish $rb_key $rb_k $rb_n $rb_t) (pr $rb_n $rb_t))))
              ($rb_sum (tsg:sum-pairs $rb_nts 0 0))
              (($rb_N $rb_T) (tsg:rest $rb_k)))
         (tsg:rest-bad (cdr-atom $rb_ks) (if (== $rb_sum (pr $rb_N $rb_T)) $rb_acc (+ $rb_acc 1))))))
(= (tsg:sum-pairs $sp_xs $sp_a $sp_b) (if (== $sp_xs ()) (pr $sp_a $sp_b) (let (pr $sp_n $sp_t) (car-atom $sp_xs) (tsg:sum-pairs (cdr-atom $sp_xs) (+ $sp_a $sp_n) (+ $sp_b $sp_t)))))
; every table holds its dish's decisions once; for a rule, also its category's total (cat CAT)
(= (tsg:base-bad)
   (if (tsg:frozen?) 0
       (let* (($bb_ds (collapse (match &self (TsgDish $bb_k $bb_kd $bb_n $bb_t) (pr $bb_k $bb_t))))
              ($bb_h (tsg:histogram (msort (tsg:table-decs $bb_ds ())) ())))
         (+ (tsg:base-check $bb_h 0) (tsg:base-extra $bb_h)))))
(= (tsg:table-decs $td_ds $td_acc)
   (if (== $td_ds ()) $td_acc
       (let* (((pr $td_k $td_t) (car-atom $td_ds))
              ($td_r (car-atom (collapse (match &self (TsgAt $td_k $td_rr) $td_rr))))
              (($td_tm $td_d $td_h $td_s) (tsg:frag $td_r none 0)))
         (tsg:table-decs (cdr-atom $td_ds) (tsg:repeat-onto (tsg:with-cats $td_d ()) $td_t $td_acc)))))
(= (tsg:repeat-onto $ro_d $ro_t $ro_acc) (if (== $ro_t 0) $ro_acc (tsg:repeat-onto $ro_d (- $ro_t 1) (term:concat $ro_d $ro_acc))))
(= (tsg:with-cats $wc_d $wc_acc)
   (if (== $wc_d ()) $wc_acc
       (let $wc_x (car-atom $wc_d)
         (tsg:with-cats (cdr-atom $wc_d) (if (== (car-atom $wc_x) rule) (cons-atom $wc_x (cons-atom (cat (term:h1 $wc_x)) $wc_acc)) (cons-atom $wc_x $wc_acc))))))
(= (tsg:base-check $bc_h $bc_acc)
   (if (== $bc_h ()) $bc_acc
       (let* (((kv $bc_x $bc_c) (car-atom $bc_h))
              ($bc_w (car-atom $bc_x))
              ($bc_have (if (== $bc_w rule) (tsg:br (term:h2 $bc_x))
                        (if (== $bc_w cat) (tsg:bt (term:h1 $bc_x))
                            (let ($bc_s $bc_e) (tsg:bs (term:h1 $bc_x)) (if (== $bc_w stop) $bc_s $bc_e))))))
         (tsg:base-check (cdr-atom $bc_h) (if (== $bc_have $bc_c) $bc_acc (+ $bc_acc 1))))))
(= (tsg:count-heads $ch_h $ch_w $ch_acc)
   (if (== $ch_h ()) $ch_acc (let (kv $ch_x $ch_c) (car-atom $ch_h) (tsg:count-heads (cdr-atom $ch_h) $ch_w (if (== (car-atom $ch_x) $ch_w) (+ $ch_acc 1) $ch_acc)))))
(= (tsg:count-items $ci_h $ci_w $ci_acc)
   (if (== $ci_h ()) $ci_acc (let (kv $ci_x $ci_c) (car-atom $ci_h) (tsg:count-items (cdr-atom $ci_h) $ci_w (if (== (car-atom $ci_x) $ci_w) (+ $ci_acc $ci_c) $ci_acc)))))
(= (tsg:bs-total $bt_ks $bt_acc) (if (== $bt_ks ()) $bt_acc (let ($bt_s $bt_e) (tsg:bs (car-atom $bt_ks)) (tsg:bs-total (cdr-atom $bt_ks) (+ $bt_acc (+ $bt_s $bt_e))))))
; stored counts with no table behind them
(= (tsg:base-extra $be_h)
   (let* (($be_nr (term:length (collapse (match &self (TsgBR $be_r $be_n) $be_r))))
          ($be_nc (term:length (collapse (match &self (TsgBT $be_c $be_n2) $be_c))))
          ($be_hs (+ (tsg:count-items $be_h stop 0) (tsg:count-items $be_h expand 0))))
     (+ (if (== $be_nr (tsg:count-heads $be_h rule 0)) 0 1)
        (+ (if (== $be_nc (tsg:count-heads $be_h cat 0)) 0 1) (if (== (tsg:bs-total (proof term level) 0) $be_hs) 0 1)))))
(= (tsg:firsts $fs_xs $fs_acc) (if (== $fs_xs ()) $fs_acc (tsg:firsts (cdr-atom $fs_xs) (cons-atom (car-atom (car-atom $fs_xs)) $fs_acc))))
(= (tsg:recount-check $rk_hist $rk_bad)
   (if (== $rk_hist ()) $rk_bad
       (let* (((kv $rk_key $rk_c) (car-atom $rk_hist)) (($rk_n $rk_t) (tsg:dish $rk_key))
              ($rk_ss (collapse (match &self (TsgTable $rk_tid $rk_key $rk_k $rk_s) $rk_s))))
         (tsg:recount-check (cdr-atom $rk_hist)
            (if (and (== $rk_n $rk_c) (and (== (size-atom $rk_ss) $rk_t) (== (tsg:sum-list $rk_ss 0) $rk_n))) $rk_bad (+ $rk_bad 1))))))
(= (tsg:sum-list $sl_xs $sl_acc) (if (== $sl_xs ()) $sl_acc (tsg:sum-list (cdr-atom $sl_xs) (+ $sl_acc (car-atom $sl_xs)))))
(= (tsg:print-top $pt_xs $pt_n)
   (if (or (== $pt_xs ()) (== $pt_n 0)) done
       (let ($pt_c $pt_t $pt_s $pt_term) (car-atom $pt_xs)
         (let $pt_p (println! (dish $pt_c $pt_t $pt_s $pt_term)) (tsg:print-top (cdr-atom $pt_xs) (- $pt_n 1))))))

;;; runs: theorems chosen by the content hash of their names (independent of any order), a burn-in,
;;; then the posterior's averages over sweeps

(= (tsg:hex-index $hi_s $hi_l $hi_i) (if (== (car-atom $hi_l) $hi_s) $hi_i (tsg:hex-index $hi_s (cdr-atom $hi_l) (+ $hi_i 1))))
(= (tsg:hexval $hv_c) (tsg:hex-index (repr $hv_c) ("0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "a" "b" "c" "d" "e" "f") 0))
(= (tsg:hex-int $hn_cs $hn_k $hn_acc) (if (== $hn_k 0) $hn_acc (tsg:hex-int (cdr-atom $hn_cs) (- $hn_k 1) (+ (* 16 $hn_acc) (tsg:hexval (car-atom $hn_cs))))))
; the theorem's hash, its first 8 hexadecimal digits, modulo M
(= (tsg:hash-mod $hm_c $hm_m) (% (tsg:hex-int (atom_chars (sha256 (repr $hm_c))) 8 0) $hm_m))
(= (tsg:part $pt_cs $pt_m $pt_r)
   (if (== $pt_cs ()) ()
       (let $pt_rest (tsg:part (cdr-atom $pt_cs) $pt_m $pt_r)
         (if (== (tsg:hash-mod (car-atom $pt_cs) $pt_m) $pt_r) (cons-atom (car-atom $pt_cs) $pt_rest) $pt_rest))))
; one round of the chain: K type moves, a blocked move per theorem, a sweep of single sites, then
; (d, theta) per kind
(= (tsg:round $rd_k)
   (let* (($rd_t (ty:sweep $rd_k))
          ($rd_b (let $rd_n (tsg:block-each (msort (collapse (match &self (TsgRoot $rd_u $rd_c) $rd_u))) 0)
                   (println! (tsg-blocked (accepted $rd_n))))))
     (tsg:sweep)))
(= (tsg:rounds $rr_n $rr_k) (if (== $rr_n 0) done (let $rr_x (tsg:round $rr_k) (tsg:rounds (- $rr_n 1) $rr_k))))
; one sample: every proof dish's customers, tables and expected uses per new theorem added to its
; running sums.  The predictive probability that the next proof fragment is F is a martingale, so F's
; expected uses among the next M fragments are M times it
; (Mettapedia.ProbabilityTheory.Distributions.PitmanYor: DishState.expectedUses_eq), and a new
; theorem brings n / N fragments on average (n proof fragments in the N training theorems): per
; theorem (n / N) (n_F - d t_F + (theta + d T) P0(F)) / (n + theta).
(= (tsg:collect)
   (let* (($cl_ds (collapse (match &self (TsgDish $cl_k proof $cl_n $cl_t) ($cl_k $cl_n $cl_t))))
          (($cl_N $cl_T) (tsg:rest proof))
          ($cl_m (- (size-atom (collapse (match &self (TsgRoot $cl_u $cl_c) $cl_u))) 0))
          ($cl_x (tsg:collect-each $cl_ds (/ $cl_N $cl_m)))
          ($cl_s (tsg:get1 (collapse (match &self (TsgSamples count $cl_m) $cl_m)) 0))
          ($cl_s2 (+ $cl_s 1))
          ($cl_r (remove-atom &self (TsgSamples count $cl_s))))
     (add-atom &self (TsgSamples count $cl_s2))))
(= (tsg:collect-each $ce_ds $ce_per)
   (if (== $ce_ds ()) done
       (let* ((($ce_k $ce_n $ce_t) (car-atom $ce_ds))
              ($ce_r0 (car-atom (collapse (match &self (TsgAt $ce_k $ce_rr) $ce_rr))))
              (($ce_tm $ce_d $ce_h $ce_s) (tsg:frag $ce_r0 none 0))
              ($ce_rate (* $ce_per (exp (tsg:logpred proof $ce_k (tsg:logp0 $ce_d ()) 0 0 0 0))))
              ($ce_old (collapse (match &self (TsgPost $ce_k $ce_a $ce_b $ce_q) ($ce_a $ce_b $ce_q))))
              (($ce_sn $ce_st $ce_sq) (tsg:get1 $ce_old (0 0 0.0)))
              ($ce_n2 (+ $ce_sn $ce_n)) ($ce_t2 (+ $ce_st $ce_t)) ($ce_q2 (+ $ce_sq $ce_rate))
              ($ce_r (if (== $ce_old ()) done (remove-atom &self (TsgPost $ce_k $ce_sn $ce_st $ce_sq))))
              ($ce_a2 (add-atom &self (TsgPost $ce_k $ce_n2 $ce_t2 $ce_q2))))
         (tsg:collect-each (cdr-atom $ce_ds) $ce_per))))
(= (tsg:sample-rounds $sm_n $sm_k) (if (== $sm_n 0) done (let* (($sm_x (tsg:round $sm_k)) ($sm_c (tsg:collect))) (tsg:sample-rounds (- $sm_n 1) $sm_k))))
; the N proof dishes with the most customers on average over the samples:
; (posterior-dish MEAN-CUSTOMERS MEAN-TABLES SIZE TERM)
(= (tsg:posterior $po_n)
   (let* (($po_s (tsg:get1 (collapse (match &self (TsgSamples count $po_m) $po_m)) 1))
          ($po_all (collapse (match &self (, (TsgPost $po_k $po_c $po_t $po_q) (TsgInfo $po_k proof $po_term $po_size))
                                 ($po_c $po_t $po_size $po_term)))))
     (tsg:print-post (tsg:reverse (msort $po_all) ()) $po_n $po_s)))
(= (tsg:print-post $pp_xs $pp_n $pp_s)
   (if (or (== $pp_xs ()) (== $pp_n 0)) done
       (let ($pp_c $pp_t $pp_z $pp_term) (car-atom $pp_xs)
         (let $pp_p (println! (posterior-dish (/ $pp_c $pp_s) (/ $pp_t $pp_s) $pp_z $pp_term))
           (tsg:print-post (cdr-atom $pp_xs) (- $pp_n 1) $pp_s)))))
; load ORDER, BURN rounds, then SAMPLES rounds each collected; K type moves a round
(= (tsg:run $rn_order $rn_seed $rn_burn $rn_samples $rn_k)
   (let* (($rn_l (tsg:load $rn_order $rn_seed))
          ($rn_b (tsg:rounds $rn_burn $rn_k))
          ($rn_s (tsg:sample-rounds $rn_samples $rn_k)))
     (tsg:posterior 40)))

;;; the held-out check: the held-out proofs parsed with the training posterior held fixed

; load more theorems into a sampled state: their nodes come after FROM; (d, theta) are not resampled
(= (tsg:extend $ex_order)
   (let* (($ex_from (tsg:nodes))
          ($ex_a (add-atom &self (TsgHeldFrom count $ex_from)))
          ($ex_t (tsg:load-theorems $ex_order))
          ($ex_s (tsg:predict-snapshot))
          ($ex_seat (tsg:seat-all $ex_from (tsg:nodes))))
     (println! (tsg-extended (from $ex_from) (nodes (tsg:nodes))))))
(= (tsg:held-from) (tsg:get1 (collapse (match &self (TsgHeldFrom count $hf_x) $hf_x)) 0))
; a held-out round: a blocked move on every held-out proof (it can take a training fragment whole),
; then every held-out node
(= (tsg:held-sweeps $hs_n)
   (if (== $hs_n 0) done
       (let* (($hs_from (tsg:held-from))
              ($hs_rs (msort (collapse (match &self (TsgRoot $hs_u $hs_c) (if (>= $hs_u $hs_from) $hs_u (empty))))))
              ($hs_b (tsg:block-each $hs_rs 0))
              ($hs_x (tsg:sweep-nodes $hs_from (tsg:nodes))))
         (tsg:held-sweeps (- $hs_n 1)))))
; before the held-out proofs are seated: for every proof dish of the training posterior, its
; predictive probability as the next proof fragment, (PredictedRate KEY P)
(= (tsg:predict-snapshot)
   (let $ps_ds (collapse (match &self (TsgDish $ps_k proof $ps_n $ps_t) $ps_k)) (tsg:predict-each $ps_ds)))
(= (tsg:predict-each $pe_ds)
   (if (== $pe_ds ()) done
       (let* (($pe_k (car-atom $pe_ds))
              ($pe_r0 (car-atom (collapse (match &self (TsgAt $pe_k $pe_rr) $pe_rr))))
              (($pe_tm $pe_d $pe_h $pe_s) (tsg:frag $pe_r0 none 0))
              ($pe_p (exp (tsg:logpred proof $pe_k (tsg:logp0 $pe_d ()) 0 0 0 0)))
              ($pe_a (add-atom &self (PredictedRate $pe_k $pe_p))))
         (tsg:predict-each (cdr-atom $pe_ds)))))
; the held-out proof fragments: (KEY COUNT) over the held-out nodes that root fragments
(= (tsg:held-uses)
   (let $hu_keys (collapse (match &self (TsgBnd $hu_u)
                             (if (and (>= $hu_u (tsg:held-from)) (== (tsg:kind $hu_u) proof))
                                 (let ($hu_t $hu_d $hu_h $hu_s) (tsg:frag $hu_u none 0) (tsg:key $hu_t))
                                 (empty))))
     (tsg:histogram (msort $hu_keys) ())))
; for the training's proof dishes with rate above a floor: predicted uses (rate times the held-out
; proof fragments) against uses found, summed by bands of predicted uses
(= (tsg:held-report)
   (let* (($hr_h (tsg:held-uses))
          ($hr_m (tsg:sum-counts $hr_h 0))
          ($hr_rates (collapse (match &self (PredictedRate $hr_k $hr_p) ($hr_k $hr_p))))
          ($hr_rows (tsg:held-rows $hr_rates $hr_h $hr_m ()))
          ($hr_pr (println! (held-out-proof-fragments $hr_m (training-dishes (term:length $hr_rates))))))
     (tsg:print-bands $hr_rows (0.1 1.0 10.0 100.0 1000000.0) 0.0)))
(= (tsg:sum-counts $sc_h $sc_acc) (if (== $sc_h ()) $sc_acc (let (kv $sc_k $sc_c) (car-atom $sc_h) (tsg:sum-counts (cdr-atom $sc_h) (+ $sc_acc $sc_c)))))
(= (tsg:held-rows $hw_rates $hw_h $hw_m $hw_acc)
   (if (== $hw_rates ()) $hw_acc
       (let* ((($hw_k $hw_p) (car-atom $hw_rates))
              ($hw_pred (* $hw_p $hw_m))
              ($hw_obs (tsg:loc $hw_h $hw_k)))
         (tsg:held-rows (cdr-atom $hw_rates) $hw_h $hw_m (cons-atom (row $hw_pred $hw_obs) $hw_acc)))))
; (band LOW HIGH DISHES PREDICTED FOUND) for predicted uses in [LOW, HIGH)
(= (tsg:print-bands $pb_rows $pb_cuts $pb_low)
   (if (== $pb_cuts ()) done
       (let* (($pb_high (car-atom $pb_cuts))
              (($pb_n $pb_p $pb_o) (tsg:band-sum $pb_rows $pb_low $pb_high 0 0.0 0))
              ($pb_x (println! (band $pb_low $pb_high (dishes $pb_n) (predicted $pb_p) (found $pb_o)))))
         (tsg:print-bands $pb_rows (cdr-atom $pb_cuts) $pb_high))))
(= (tsg:band-sum $bs_rows $bs_low $bs_high $bs_n $bs_p $bs_o)
   (if (== $bs_rows ()) ($bs_n $bs_p $bs_o)
       (let (row $bs_pr $bs_ob) (car-atom $bs_rows)
         (if (and (>= $bs_pr $bs_low) (< $bs_pr $bs_high))
             (tsg:band-sum (cdr-atom $bs_rows) $bs_low $bs_high (+ $bs_n 1) (+ $bs_p $bs_pr) (+ $bs_o $bs_ob))
             (tsg:band-sum (cdr-atom $bs_rows) $bs_low $bs_high $bs_n $bs_p $bs_o)))))

;;; the posterior handed to the library (library.metta): every proof dish with at least MIN mean
;;; customers over the samples, (LibCandidate KEY TERM SIZE MEAN-CUSTOMERS MEAN-USES-PER-THEOREM),
;;; and (LibPosterior D N): the proof kind's discount and the number of training theorems
(= (tsg:to-library $tl_min $tl_n)
   (let* (($tl_s (tsg:get1 (collapse (match &self (TsgSamples count $tl_m) $tl_m)) 1))
          ($tl_all (collapse (match &self (, (TsgPost $tl_k $tl_c $tl_t $tl_q) (TsgInfo $tl_k proof $tl_term $tl_size))
                                 ($tl_k $tl_term $tl_size $tl_c $tl_q))))
          ($tl_x (tsg:to-library-each $tl_all $tl_s $tl_min))
          (($tl_d $tl_th) (tsg:hyp proof))
          ($tl_a (add-atom &self (LibPosterior $tl_d $tl_n))))
     (println! (library-candidates (term:length (collapse (match &self (LibCandidate $tl_k2 $tl_t2 $tl_s2 $tl_c2 $tl_u2) x)))
                                   (discount $tl_d) (training $tl_n)))))
(= (tsg:to-library-each $te_xs $te_s $te_min)
   (if (== $te_xs ()) done
       (let* ((($te_k $te_term $te_size $te_c $te_q) (car-atom $te_xs))
              ($te_mc (/ $te_c $te_s)) ($te_mq (/ $te_q $te_s))
              ($te_a (if (>= $te_mc $te_min) (add-atom &self (LibCandidate $te_k $te_term $te_size $te_mc $te_mq)) done)))
         (tsg:to-library-each (cdr-atom $te_xs) $te_s $te_min))))
; the same, printed as atoms for a stored artifact, in the standard order of terms
(= (tsg:print-library $pl_min $pl_n)
   (let* (($pl_x (tsg:to-library $pl_min $pl_n))
          ($pl_rows (msort (collapse (match &self (LibCandidate $pl_k $pl_t $pl_s $pl_c $pl_u) (LibCandidate $pl_k $pl_t $pl_s $pl_c $pl_u)))))
          ($pl_p (collapse (match &self (LibPosterior $pl_d $pl_nn) (LibPosterior $pl_d $pl_nn)))))
     (tsg:print-rows (term:concat $pl_p $pl_rows))))
(= (tsg:print-rows $pr_xs) (if (== $pr_xs ()) done (let $pr_p (println! (car-atom $pr_xs)) (tsg:print-rows (cdr-atom $pr_xs)))))

;;; blocked moves: a whole proof's derivation at once (Cohn and Blunsom, ACL 2010)
;
; The proof's fragments leave the restaurants, last first; the probability of the derivation they
; formed, added in order, is collected as they leave (a fragment's predictive just after it left
; is the probability it had when added).  A proposal is drawn from the grammar the rest of the
; corpus gives, by an inside pass over the tree in which each fragment weighs its predictive
; probability with the base held as it is (a product over the fragment's nodes); the proposal
; probability of a derivation is the product of its fragments' weights over the inside total.  The
; proposed fragments are added in order, their predictive probabilities collected.  The move is
; accepted with probability min(1, P(new) Q(old) / (P(old) Q(new))); otherwise the old derivation
; is put back.

(= (tsg:preorder $po_u $po_acc)
   (let ($po_k $po_c $po_r $po_rk $po_ks $po_b $po_m) (tsg:node $po_u)
     (tsg:preorder-kids $po_ks (cons-atom $po_u $po_acc))))
(= (tsg:preorder-kids $pk_ks $pk_acc) (if (== $pk_ks ()) $pk_acc (tsg:preorder-kids (cdr-atom $pk_ks) (tsg:preorder (car-atom $pk_ks) $pk_acc))))
; a dish's term at node U: (dm HOLES INSIDE), the nodes at its holes and the nodes that can root a
; fragment strictly inside it, or Fail
(= (tsg:match-dish $mdt $mdu $mdacc)
   (if (== $mdacc Fail) Fail
       (let ($mdk $mdc $mdr $mdrk $mdks $mdb $mdm) (tsg:node $mdu)
         (if (== (tsg:rule-of $mdt) $mdr)
             (tsg:match-kids (tsg:expr-children $mdt ()) $mdks $mdacc)
             Fail))))
(= (tsg:expr-children $ec_t $ec_acc)
   (if (== $ec_t ()) (tsg:reverse $ec_acc ())
       (let $ec_x (car-atom $ec_t) (tsg:expr-children (cdr-atom $ec_t) (if (term:expr? $ec_x) (cons-atom $ec_x $ec_acc) $ec_acc)))))
(= (tsg:match-kids $mk_ts $mk_ks $mk_acc)
   (if (or (== $mk_acc Fail) (== $mk_ts ())) $mk_acc
       (let* (($mk_t (car-atom $mk_ts)) ($mk_k (car-atom $mk_ks)) ($mk_kk (tsg:kind $mk_k))
              ($mk_acc2 (if (if (term:expr? $mk_t) (== (car-atom $mk_t) hole) False)
                            (if (== (term:h1 $mk_t) $mk_kk)
                                (let (dm $mk_h $mk_i) $mk_acc (dm (cons-atom $mk_k $mk_h) $mk_i))
                                Fail)
                            (let $mk_a1 (if (tsg:eligible? $mk_kk) (let (dm $mk_h2 $mk_i2) $mk_acc (dm $mk_h2 (cons-atom $mk_k $mk_i2))) $mk_acc)
                              (tsg:match-dish $mk_t $mk_k $mk_a1)))))
         (tsg:match-kids (cdr-atom $mk_ts) (cdr-atom $mk_ks) $mk_acc2))))
; the base's static log probability of a node's local form, and of a stop or an expansion
(= (tsg:lrule $lr_c $lr_rk) (- (tsg:ln (+ (tsg:br $lr_rk) (/ (tsg:alpha) (tsg:rc $lr_c)))) (tsg:ln (+ (tsg:bt $lr_c) (tsg:alpha)))))
(= (tsg:lstop $ls_k $ls_which)
   (let ($ls_s $ls_e) (tsg:bs $ls_k)
     (- (tsg:ln (+ (if (== $ls_which stop) $ls_s $ls_e) 1)) (tsg:ln (+ (+ $ls_s $ls_e) 2)))))
(= (tsg:inside-of $io_u) (tsg:get1 (collapse (match &self (TsgIn $io_u $io_e $io_i) (pr $io_e $io_i))) none))
; the inside pass: (TsgIn U E I), E the log weight of the fragment-continuation at U (U's local
; form and below, holes weighed by their inside), I the log inside of a fragment rooted at U
(= (tsg:inside-node $in_u)
   (let* ((($in_k $in_c $in_r $in_rk $in_ks $in_b $in_m) (tsg:node $in_u))
          ($in_e (+ (tsg:lrule $in_c $in_rk) (tsg:inside-kids $in_ks 0.0)))
          ($in_i (if (tsg:eligible? $in_k) (tsg:inside-root $in_u $in_k $in_rk $in_e) neg)))
     (add-atom &self (TsgIn $in_u $in_e $in_i))))
(= (tsg:inside-kids $ik_ks $ik_acc)
   (if (== $ik_ks ()) $ik_acc
       (let* (($ik_c (car-atom $ik_ks)) ($ik_kk (tsg:kind $ik_c)) ((pr $ik_e $ik_i) (tsg:inside-of $ik_c))
              ($ik_v (if (tsg:eligible? $ik_kk)
                         (tsg:lse (+ (tsg:lstop $ik_kk stop) $ik_i) (+ (tsg:lstop $ik_kk expand) $ik_e))
                         $ik_e)))
         (tsg:inside-kids (cdr-atom $ik_ks) (+ $ik_acc $ik_v)))))
(= (tsg:hole-inside $hi_hs $hi_acc)
   (if (== $hi_hs ()) $hi_acc (let (pr $hi_e $hi_i) (tsg:inside-of (car-atom $hi_hs)) (tsg:hole-inside (cdr-atom $hi_hs) (+ $hi_acc $hi_i)))))
; the options at a fragment root U: (opt LOGW HOLES INSIDE) per cached dish that fits, and
; (opt LOGW new new) for a new fragment
(= (tsg:options $op_u $op_k $op_rk $op_e)
   (let* ((($op_n $op_T) (tsg:rest $op_k)) (($op_d $op_th) (tsg:hyp $op_k))
          ($op_den (tsg:ln (+ $op_n $op_th)))
          ($op_keys (collapse (match &self (TsgByRoot $op_rk $op_key) $op_key)))
          ($op_cached (tsg:cached-options $op_keys $op_u $op_d $op_den ())))
     (cons-atom (opt (+ (- (tsg:ln (+ $op_th (* $op_d $op_T))) $op_den) $op_e) new new) $op_cached)))
(= (tsg:cached-options $co_keys $co_u $co_d $co_den $co_acc)
   (if (== $co_keys ()) $co_acc
       (let* (($co_key (car-atom $co_keys)) (($co_n $co_t) (tsg:dish $co_key))
              ($co_acc2 (if (== $co_n 0) $co_acc
                            (let* (($co_term (car-atom (collapse (match &self (TsgInfo $co_key $co_ik $co_it $co_is) $co_it))))
                                   ($co_m (tsg:match-dish $co_term $co_u (dm () ()))))
                              (if (== $co_m Fail) $co_acc
                                  (let (dm $co_hs $co_ins) $co_m
                                    (cons-atom (opt (+ (- (tsg:ln (- $co_n (* $co_d $co_t))) $co_den) (tsg:hole-inside $co_hs 0.0)) $co_hs $co_ins)
                                               $co_acc)))))))
         (tsg:cached-options (cdr-atom $co_keys) $co_u $co_d $co_den $co_acc2))))
(= (tsg:lse-opts $lo_xs $lo_acc) (if (== $lo_xs ()) $lo_acc (let (opt $lo_w $lo_h $lo_i) (car-atom $lo_xs) (tsg:lse-opts (cdr-atom $lo_xs) (tsg:lse $lo_acc $lo_w)))))
(= (tsg:inside-root $ir_u $ir_k $ir_rk $ir_e) (tsg:lse-opts (tsg:options $ir_u $ir_k $ir_rk $ir_e) neg))
; drawing a derivation of the tree top-down from the inside weights, setting the roots
(= (tsg:set-root $sr_u $sr_b)
   (let $sr_now (tsg:bnd? $sr_u)
     (if (== $sr_now $sr_b) done (if $sr_b (add-atom &self (TsgBnd $sr_u)) (remove-atom &self (TsgBnd $sr_u))))))
; an option drawn with probability exp(W - TOT), TOT the log of the options' total: normalized in log
; space, so a total far below or above 0 (a large subtree, or a weight raised to BETA < 1) is exact
(= (tsg:pick-opt $pq_xs $pq_tot $pq_u)
   (let (opt $pq_w $pq_h $pq_i) (car-atom $pq_xs)
     (let $pq_p (exp (- $pq_w $pq_tot))
       (if (or (< $pq_u $pq_p) (== (cdr-atom $pq_xs) ())) (car-atom $pq_xs) (tsg:pick-opt (cdr-atom $pq_xs) $pq_tot (- $pq_u $pq_p))))))
(= (tsg:draw-at $da_u)
   (let* ((($da_k $da_c $da_r $da_rk $da_ks $da_b $da_m) (tsg:node $da_u))
          ((pr $da_e $da_i) (tsg:inside-of $da_u))
          ($da_opts (tsg:options $da_u $da_k $da_rk $da_e))
          ($da_tot (tsg:lse-opts $da_opts neg))
          ((opt $da_w $da_hs $da_ins) (tsg:pick-opt $da_opts $da_tot (tsg:uniform))))
     (if (== $da_hs new)
         (tsg:draw-new $da_ks)
         (let* (($da_x (tsg:set-roots $da_ins False)) ($da_y (tsg:set-roots $da_hs True)))
           (tsg:draw-each $da_hs)))))
(= (tsg:set-roots $sx_us $sx_b) (if (== $sx_us ()) done (let $sx_a (tsg:set-root (car-atom $sx_us) $sx_b) (tsg:set-roots (cdr-atom $sx_us) $sx_b))))
(= (tsg:draw-each $de_us) (if (== $de_us ()) done (let $de_x (tsg:draw-at (car-atom $de_us)) (tsg:draw-each (cdr-atom $de_us)))))
(= (tsg:draw-new $dn_ks)
   (if (== $dn_ks ()) done
       (let* (($dn_c (car-atom $dn_ks)) ($dn_kk (tsg:kind $dn_c)) ((pr $dn_e $dn_i) (tsg:inside-of $dn_c))
              ($dn_x (if (tsg:eligible? $dn_kk)
                         (let* (($dn_ls (+ (tsg:lstop $dn_kk stop) $dn_i)) ($dn_le (+ (tsg:lstop $dn_kk expand) $dn_e))
                                ($dn_stop (< (tsg:ln (tsg:uniform)) (- $dn_ls (tsg:lse $dn_ls $dn_le)))))
                           (if $dn_stop
                               (let $dn_a (tsg:set-root $dn_c True) (tsg:draw-at $dn_c))
                               (let $dn_a2 (tsg:set-root $dn_c False)
                                 (let ($dn_k2 $dn_c2 $dn_r2 $dn_rk2 $dn_ks2 $dn_b2 $dn_m2) (tsg:node $dn_c) (tsg:draw-new $dn_ks2)))))
                         (let ($dn_k3 $dn_c3 $dn_r3 $dn_rk3 $dn_ks3 $dn_b3 $dn_m3) (tsg:node $dn_c) (tsg:draw-new $dn_ks3)))))
         (tsg:draw-new (cdr-atom $dn_ks)))))
; the fragments of the tree, in pre-order: (fr KEY KIND DECS TERM SIZE ROOT)
(= (tsg:tree-frags $tf_nodes $tf_acc)
   (if (== $tf_nodes ()) (tsg:reverse $tf_acc ())
       (let $tf_u (car-atom $tf_nodes)
         (tsg:tree-frags (cdr-atom $tf_nodes)
            (if (tsg:bnd? $tf_u)
                (let ($tf_t $tf_d $tf_h $tf_s) (tsg:frag $tf_u none 0) (cons-atom (fr (tsg:key $tf_t) (tsg:kind $tf_u) $tf_d $tf_t $tf_s $tf_u) $tf_acc))
                $tf_acc)))))
; Fragments leave in the order given (a derivation's, last first): (pr LOGP SIZES), the sum of their
; predictive log probabilities just after leaving, and the sizes of the tables they left, in that
; order.
(= (tsg:remove-frags $rf_fs $rf_acc $rf_ss)
   (if (== $rf_fs ()) (pr $rf_acc (tsg:reverse $rf_ss ()))
       (let* (((fr $rf_k $rf_kd $rf_d $rf_t $rf_s $rf_r) (car-atom $rf_fs))
              ($rf_z (tsg:unseat $rf_r $rf_k $rf_kd $rf_d))
              ($rf_lp (tsg:logpred $rf_kd $rf_k (tsg:logp0 $rf_d ()) 0 0 0 0)))
         (tsg:remove-frags (cdr-atom $rf_fs) (+ $rf_acc $rf_lp) (cons-atom $rf_z $rf_ss)))))
; Fragments sit in order: (pr LOGP SIZES), their predictive log probabilities just before arriving,
; and the sizes of the tables they sat at.
(= (tsg:add-frags $af_fs $af_acc $af_ss)
   (if (== $af_fs ()) (pr $af_acc (tsg:reverse $af_ss ()))
       (let* (((fr $af_k $af_kd $af_d $af_t $af_s $af_r) (car-atom $af_fs))
              ($af_l0 (tsg:logp0 $af_d ()))
              ($af_lp (tsg:logpred $af_kd $af_k $af_l0 0 0 0 0))
              ($af_z (tsg:seat $af_r $af_k $af_kd $af_d $af_l0 $af_t $af_s)))
         (tsg:add-frags (cdr-atom $af_fs) (+ $af_acc $af_lp) (cons-atom $af_z $af_ss)))))
; exactly undone: fragments leave the tables they sit at; fragments sit back at the tables given,
; one each (a table that emptied opens again under its number)
(= (tsg:unseat-frags $uf_fs)
   (if (== $uf_fs ()) done
       (let* (((fr $uf_k $uf_kd $uf_d $uf_t $uf_s $uf_r) (car-atom $uf_fs))
              ($uf_x (tsg:leave $uf_r $uf_k $uf_kd $uf_d)))
         (tsg:unseat-frags (cdr-atom $uf_fs)))))
(= (tsg:reseat-frags $rs_fs $rs_ss)
   (if (== $rs_fs ()) done
       (let* (((fr $rs_k $rs_kd $rs_d $rs_t $rs_s $rs_r) (car-atom $rs_fs))
              ($rs_x (tsg:sit $rs_r $rs_k $rs_kd $rs_d $rs_t $rs_s (car-atom $rs_ss))))
         (tsg:reseat-frags (cdr-atom $rs_fs) (cdr-atom $rs_ss)))))
; a fragment's proposal weight: its predictive with the base held, P0 the product of its decisions'
; static probabilities
(= (tsg:logp0-static $ls_decs $ls_acc)
   (if (== $ls_decs ()) $ls_acc
       (let* (($ls_x (car-atom $ls_decs))
              ($ls_v (if (== (car-atom $ls_x) rule) (tsg:lrule (term:h1 $ls_x) (term:h2 $ls_x)) (tsg:lstop (term:h1 $ls_x) (car-atom $ls_x)))))
         (tsg:logp0-static (cdr-atom $ls_decs) (+ $ls_acc $ls_v)))))
(= (tsg:proposal-weights $pw_fs $pw_acc)
   (if (== $pw_fs ()) $pw_acc
       (let* (((fr $pw_k $pw_kd $pw_d $pw_t $pw_s $pw_r) (car-atom $pw_fs)))
         (tsg:proposal-weights (cdr-atom $pw_fs) (+ $pw_acc (tsg:logpred $pw_kd $pw_k (tsg:logp0-static $pw_d 0.0) 0 0 0 0))))))
(= (tsg:roots-of $ro_nodes) (collapse (let $ro_u (superpose $ro_nodes) (if (tsg:bnd? $ro_u) $ro_u (empty)))))
(= (tsg:clear-inside $ci_nodes) (if (== $ci_nodes ()) done
   (let* (($ci_u (car-atom $ci_nodes)) ($ci_x (collapse (match &self (TsgIn $ci_u $ci_e $ci_i) (remove-atom &self (TsgIn $ci_u $ci_e $ci_i))))))
     (tsg:clear-inside (cdr-atom $ci_nodes)))))
; one blocked move on the tree rooted at R: True if the proposal was accepted
(= (tsg:block $bk_r)
   (let* (($bk_pre (tsg:reverse (tsg:preorder $bk_r ()) ()))
          ($bk_post (tsg:reverse $bk_pre ()))
          ($bk_old (tsg:tree-frags $bk_pre ()))
          ($bk_oldroots (tsg:roots-of $bk_pre))
          ((pr $bk_pold $bk_olds) (tsg:remove-frags (tsg:reverse $bk_old ()) 0.0 ()))
          ($bk_qold (tsg:proposal-weights $bk_old 0.0))
          ($bk_in (tsg:inside-each $bk_post))
          ($bk_draw (tsg:draw-at $bk_r))
          ($bk_new (tsg:tree-frags $bk_pre ()))
          ($bk_qnew (tsg:proposal-weights $bk_new 0.0))
          ((pr $bk_pnew $bk_news) (tsg:add-frags $bk_new 0.0 ()))
          ($bk_la (- (- $bk_pnew $bk_qnew) (- $bk_pold $bk_qold)))
          ($bk_accept (< (tsg:ln (tsg:uniform)) $bk_la))
          ; a rejected proposal leaves exactly the state it found: the new fragments leave the tables
          ; they took, the old ones sit back at the tables they left
          ($bk_back (if $bk_accept done
                        (let* (($bk_r1 (tsg:unseat-frags (tsg:reverse $bk_new ())))
                               ($bk_r2 (tsg:restore-roots $bk_pre $bk_oldroots)))
                          (tsg:reseat-frags $bk_old (tsg:reverse $bk_olds ())))))
          ($bk_c (tsg:clear-inside $bk_post)))
     $bk_accept))
(= (tsg:inside-each $ie_nodes) (if (== $ie_nodes ()) done (let $ie_x (tsg:inside-node (car-atom $ie_nodes)) (tsg:inside-each (cdr-atom $ie_nodes)))))
(= (tsg:restore-roots $rr_nodes $rr_roots)
   (if (== $rr_nodes ()) done
       (let* (($rr_u (car-atom $rr_nodes)) ($rr_x (tsg:set-root $rr_u (term:member-of $rr_u $rr_roots))))
         (tsg:restore-roots (cdr-atom $rr_nodes) $rr_roots))))
(= (tsg:block-each $be_rs $be_acc)
   (if (== $be_rs ()) $be_acc
       (let $be_a (tsg:block (car-atom $be_rs)) (tsg:block-each (cdr-atom $be_rs) (if $be_a (+ $be_acc 1) $be_acc)))))

;;; type moves: every site of one type at once (Liang, Jordan and Klein, NAACL 2010)
;
; A site's type is what it decides between: UP, the fragment above it with a hole at it; DOWN, the
; fragment it roots; MERGED, UP with DOWN in that hole.  Sites of one type whose fragments do not
; reach each other are exchangeable: given the rest of the derivation, its probability depends on
; how many of them are merged, not on which.  A pattern that recurs pays for itself only once its
; occurrences merge together, and one merged alone costs more than it saves, so a move that changes
; one site, or one proof, at a time must climb through less probable derivations to reach it; a
; type move changes them together.
;
; The move at a seed site U: the sites of U's type are gathered, U first and then by node, each
; kept unless its fragments reach a site kept before it or are reached by one; their fragments leave
; the restaurants, the probability of the old derivation collected as they leave (as in a blocked
; move); a number of merged sites is drawn from a closed form Q and that many sites are chosen
; uniformly; the new fragments sit, the probability of the new derivation collected; and the move is
; accepted with probability min(1, P(new) Q(old) / (P(old) Q(new))), provided the seed gathers the
; same sites in the new derivation (otherwise no single move leads back, and the move is rejected).
; Each move leaves the posterior invariant whatever its seed, so any sequence of seeds does.

(= (tsg:nth $nt_xs $nt_i) (if (== $nt_i 0) (car-atom $nt_xs) (tsg:nth (cdr-atom $nt_xs) (- $nt_i 1))))
(= (tsg:kids-of $ko_u) (let ($ko_k $ko_c $ko_r $ko_rk $ko_ks $ko_b $ko_m) (tsg:node $ko_u) $ko_ks))
(= (ty:index-of $ix_x $ix_xs $ix_i) (if (== (car-atom $ix_xs) $ix_x) $ix_i (ty:index-of $ix_x (cdr-atom $ix_xs) (+ $ix_i 1))))
; the kid positions from R down to V, and the node at the end of such a path
(= (ty:path $pa_r $pa_v $pa_acc)
   (if (== $pa_v $pa_r) $pa_acc
       (let $pa_p (car-atom (collapse (match &self (TsgParent $pa_v $pa_x) $pa_x)))
         (ty:path $pa_r $pa_p (cons-atom (ty:index-of $pa_v (tsg:kids-of $pa_p) 0) $pa_acc)))))
(= (ty:at $at_r $at_p) (if (== $at_p ()) $at_r (ty:at (tsg:nth (tsg:kids-of $at_r) (car-atom $at_p)) (cdr-atom $at_p))))
; a site's type: (ty R UP DOWN MERGED), each fragment (fg KEY DECS TERM SIZE KIND), R the root above
(= (ty:of $to_v)
   (let* (($to_r (tsg:up-root $to_v))
          (($to_tu $to_du $to_hu $to_su) (tsg:frag $to_r $to_v 1))
          (($to_td $to_dd $to_hd $to_sd) (tsg:frag $to_v none 0))
          (($to_tm $to_dm $to_hm $to_sm) (tsg:frag $to_r $to_v 0))
          ($to_kr (tsg:kind $to_r)) ($to_kv (tsg:kind $to_v)))
     (ty $to_r (fg (tsg:key $to_tu) $to_du $to_tu $to_su $to_kr)
               (fg (tsg:key $to_td) $to_dd $to_td $to_sd $to_kv)
               (fg (tsg:key $to_tm) $to_dm $to_tm $to_sm $to_kr))))
(= (ty:keys $tk_t)
   (let (ty $tk_r (fg $tk_ku $tk_a1 $tk_a2 $tk_a3 $tk_a4) (fg $tk_kd $tk_b1 $tk_b2 $tk_b3 $tk_b4) (fg $tk_km $tk_c1 $tk_c2 $tk_c3 $tk_c4)) $tk_t
     (keys $tk_ku $tk_kd $tk_km)))
; the nodes a site's fragments reach: its root R, every node below down to and including the roots
; that bound them, the site itself counted as inside
(= (ty:region $rg_r $rg_v) (ty:region-kids (tsg:kids-of $rg_r) $rg_v (cons-atom $rg_r ())))
(= (ty:region-kids $rk_ks $rk_v $rk_acc)
   (if (== $rk_ks ()) $rk_acc
       (let* (($rk_c (car-atom $rk_ks))
              ($rk_bound (if (== $rk_c $rk_v) False (if (tsg:eligible? (tsg:kind $rk_c)) (tsg:bnd? $rk_c) False)))
              ($rk_acc2 (if $rk_bound (cons-atom $rk_c $rk_acc) (ty:region-kids (tsg:kids-of $rk_c) $rk_v (cons-atom $rk_c $rk_acc)))))
         (ty:region-kids (cdr-atom $rk_ks) $rk_v $rk_acc2))))
; the sites that may have the type: the node at the path below every root of UP or of MERGED
(= (ty:candidates $cd_ku $cd_km $cd_p)
   (let* (($cd_a (collapse (match &self (TsgAt $cd_ku $cd_r) $cd_r)))
          ($cd_b (collapse (match &self (TsgAt $cd_km $cd_r2) $cd_r2))))
     (msort (ty:ats (term:concat $cd_a $cd_b) $cd_p ()))))
(= (ty:ats $as_rs $as_p $as_acc) (if (== $as_rs ()) $as_acc (ty:ats (cdr-atom $as_rs) $as_p (cons-atom (ty:at (car-atom $as_rs) $as_p) $as_acc))))
; gathering: claims are (TyClaim NODE), kept sites (TyKept NODE); each head keeps an atom
(= (ty:claimed? $cl_u) (let $qz6 (collapse (match &self (TyClaim $cl_u) yes)) (if (== $qz6 ()) False True)))
(= (ty:kept? $kp_u) (let $qz7 (collapse (match &self (TyKept $kp_u) yes)) (if (== $qz7 ()) False True)))
(= (ty:any-kept? $ak_us) (if (== $ak_us ()) False (if (ty:kept? (car-atom $ak_us)) True (ty:any-kept? (cdr-atom $ak_us)))))
(= (ty:claim $cm_us) (if (== $cm_us ()) done (let $cm_a (add-atom &self (TyClaim (car-atom $cm_us))) (ty:claim (cdr-atom $cm_us)))))
(= (ty:keep $ke_u) (let* (($ke_a (ty:claim (ty:region (tsg:up-root $ke_u) $ke_u))) ($ke_b (add-atom &self (TyKept $ke_u)))) $ke_u))
(= (ty:clear)
   (let* (($cr_a (collapse (match &self (TyClaim $cr_u) (if (== $cr_u none) done (remove-atom &self (TyClaim $cr_u))))))
          ($cr_b (collapse (match &self (TyKept $cr_v) (if (== $cr_v none) done (remove-atom &self (TyKept $cr_v)))))))
     done))
; the sites gathered at seed U, U first: a candidate is kept if it is a site of the type, is not
; reached by a kept site, and reaches none
(= (ty:gather $ga_u $ga_keys $ga_cands)
   (let* (($ga_k (ty:keep $ga_u))
          ($ga_s (ty:gather-rest $ga_cands $ga_u $ga_keys (cons-atom $ga_u ())))
          ($ga_c (ty:clear)))
     (tsg:reverse $ga_s ())))
(= (ty:gather-rest $gr_cs $gr_u $gr_keys $gr_acc)
   (if (== $gr_cs ()) $gr_acc
       (let* (($gr_c (car-atom $gr_cs))
              ($gr_ok (if (== $gr_c $gr_u) False
                      (if (ty:claimed? $gr_c) False
                      (if (not (tsg:steppable? $gr_c)) False
                      (if (not (== (ty:keys (ty:of $gr_c)) $gr_keys)) False
                          (not (ty:any-kept? (ty:region (tsg:up-root $gr_c) $gr_c))))))))
              ($gr_acc2 (if $gr_ok (cons-atom (ty:keep $gr_c) $gr_acc) $gr_acc)))
         (ty:gather-rest (cdr-atom $gr_cs) $gr_u $gr_keys $gr_acc2))))
; a site's state (st V R SPLIT), and the fragments of a list of states, in order: UP then DOWN for a
; split site, MERGED for a merged one
(= (ty:states $ss_vs $ss_acc)
   (if (== $ss_vs ()) (tsg:reverse $ss_acc ())
       (let $ss_v (car-atom $ss_vs) (ty:states (cdr-atom $ss_vs) (cons-atom (st $ss_v (tsg:up-root $ss_v) (tsg:bnd? $ss_v)) $ss_acc)))))
(= (ty:frags $tf_sts $tf_t $tf_acc)
   (if (== $tf_sts ()) (tsg:reverse $tf_acc ())
       (let* (((st $tf_v $tf_r $tf_b) (car-atom $tf_sts))
              ((ty $tf_x (fg $tf_ku $tf_du $tf_tu $tf_su $tf_kr) (fg $tf_kd $tf_dd $tf_td $tf_sd $tf_kv) (fg $tf_km $tf_dm $tf_tm $tf_sm $tf_kr2)) $tf_t))
         (ty:frags (cdr-atom $tf_sts) $tf_t
            (if $tf_b
                (cons-atom (fr $tf_kd $tf_kv $tf_dd $tf_td $tf_sd $tf_v) (cons-atom (fr $tf_ku $tf_kr $tf_du $tf_tu $tf_su $tf_r) $tf_acc))
                (cons-atom (fr $tf_km $tf_kr $tf_dm $tf_tm $tf_sm $tf_r) $tf_acc))))))
(= (ty:merged-count $mc_sts $mc_acc) (if (== $mc_sts ()) $mc_acc (let (st $mc_v $mc_r $mc_b) (car-atom $mc_sts) (ty:merged-count (cdr-atom $mc_sts) (if $mc_b $mc_acc (+ $mc_acc 1))))))
(= (ty:set-states $sx_sts) (if (== $sx_sts ()) done (let (st $sx_v $sx_r $sx_b) (car-atom $sx_sts) (let $sx_a (tsg:set-root $sx_v $sx_b) (ty:set-states (cdr-atom $sx_sts))))))
; M of the sites, chosen uniformly, merged: each in turn with probability (left to merge)/(left)
(= (ty:choose $ch_sts $ch_m $ch_left $ch_acc)
   (if (== $ch_sts ()) (tsg:reverse $ch_acc ())
       (let* (((st $ch_v $ch_r $ch_b) (car-atom $ch_sts))
              ($ch_merge (< (* (tsg:uniform) $ch_left) $ch_m)))
         (ty:choose (cdr-atom $ch_sts) (if $ch_merge (- $ch_m 1) $ch_m) (- $ch_left 1) (cons-atom (st $ch_v $ch_r (not $ch_merge)) $ch_acc)))))
; The closed form: log Q(M), the probability of the derivation with M of the N sites merged when each
; dish's customers arrive with its weight raised by one per customer (no table after the first is
; opened) and each restaurant's by one per customer; a weight A enters through log A.
(= (ty:lrise $lr_la $lr_m)
   (if (== $lr_m 0) 0.0 (if (< $lr_la -30.0) (+ $lr_la (tsg:lgamma $lr_m)) (tsg:lrise (exp $lr_la) $lr_m))))
(= (ty:lweight $lw_key $lw_k $lw_decs)
   (let* ((($lw_n $lw_t) (tsg:dish $lw_key)) (($lw_N $lw_T) (tsg:rest $lw_k)) (($lw_d $lw_th) (tsg:hyp $lw_k)))
     (tsg:lse (tsg:ln0 (- $lw_n (* $lw_d $lw_t))) (+ (tsg:ln (+ $lw_th (* $lw_d $lw_T))) (tsg:logp0 $lw_decs ())))))
(= (ty:lq $q_m $q_c)
   (let* (((qc $q_n $q_am $q_au $q_ad $q_sameud $q_samek $q_nu $q_nd) $q_c)
          ($q_s (- $q_n $q_m))
          ($q_num (+ (ty:lrise $q_am $q_m)
                     (if $q_sameud (ty:lrise $q_au (* 2 $q_s)) (+ (ty:lrise $q_au $q_s) (ty:lrise $q_ad $q_s)))))
          ($q_den (if $q_samek (tsg:lrise $q_nu (- (* 2 $q_n) $q_m)) (+ (tsg:lrise $q_nu $q_n) (tsg:lrise $q_nd $q_s)))))
     (- $q_num $q_den)))
(= (ty:qc $qq_n $qq_t)
   (let* (((ty $qq_x (fg $qq_ku $qq_du $qq_tu $qq_su $qq_kr) (fg $qq_kd $qq_dd $qq_td $qq_sd $qq_kv) (fg $qq_km $qq_dm $qq_tm $qq_sm $qq_kr2)) $qq_t)
          (($qq_N1 $qq_T1) (tsg:rest $qq_kr)) (($qq_d1 $qq_th1) (tsg:hyp $qq_kr))
          (($qq_N2 $qq_T2) (tsg:rest $qq_kv)) (($qq_d2 $qq_th2) (tsg:hyp $qq_kv)))
     (qc $qq_n (ty:lweight $qq_km $qq_kr $qq_dm) (ty:lweight $qq_ku $qq_kr $qq_du) (ty:lweight $qq_kd $qq_kv $qq_dd)
         (== $qq_ku $qq_kd) (== $qq_kr $qq_kv) (+ $qq_N1 $qq_th1) (+ $qq_N2 $qq_th2))))
; M drawn with weight C(N, M) Q(M)
(= (ty:lchoose $lc_n $lc_m) (- (tsg:lgamma (+ $lc_n 1)) (+ (tsg:lgamma (+ $lc_m 1)) (tsg:lgamma (+ (- $lc_n $lc_m) 1)))))
(= (ty:m-weights $mw_m $mw_n $mw_c $mw_acc)
   (if (> $mw_m $mw_n) (tsg:reverse $mw_acc ())
       (ty:m-weights (+ $mw_m 1) $mw_n $mw_c (cons-atom (opt (+ (ty:lchoose $mw_n $mw_m) (ty:lq $mw_m $mw_c)) $mw_m $mw_m) $mw_acc))))
; one type move at seed U: (moved N MERGED-BEFORE MERGED-AFTER)
(= (ty:move $mv_u)
   (let* (($mv_t (ty:of $mv_u))
          ((keys $mv_ku $mv_kd $mv_km) (ty:keys $mv_t))
          ((ty $mv_r $mv_fu $mv_fd $mv_fm) $mv_t)
          ($mv_p (ty:path $mv_r $mv_u ()))
          ($mv_sites (ty:gather $mv_u (keys $mv_ku $mv_kd $mv_km) (ty:candidates $mv_ku $mv_km $mv_p)))
          ($mv_n (term:length $mv_sites))
          ($mv_st (ty:states $mv_sites ()))
          ($mv_mold (ty:merged-count $mv_st 0))
          ($mv_old (ty:frags $mv_st $mv_t ()))
          ((pr $mv_pold $mv_olds) (tsg:remove-frags (tsg:reverse $mv_old ()) 0.0 ()))
          ($mv_c (ty:qc $mv_n $mv_t))
          ($mv_ws (ty:m-weights 0 $mv_n $mv_c ()))
          ((opt $mv_w $mv_mnew $mv_y) (tsg:pick-opt $mv_ws (tsg:lse-opts $mv_ws neg) (tsg:uniform)))
          ($mv_nst (ty:choose $mv_st $mv_mnew $mv_n ()))
          ($mv_new (ty:frags $mv_nst $mv_t ()))
          ($mv_sx (ty:set-states $mv_nst))
          ((pr $mv_pnew $mv_news) (tsg:add-frags $mv_new 0.0 ()))
          ($mv_same (== (ty:gather $mv_u (keys $mv_ku $mv_kd $mv_km) (ty:candidates $mv_ku $mv_km $mv_p)) $mv_sites))
          ($mv_la (- (- $mv_pnew $mv_pold) (- (ty:lq $mv_mnew $mv_c) (ty:lq $mv_mold $mv_c))))
          ($mv_accept (if $mv_same (< (tsg:ln (tsg:uniform)) $mv_la) False))
          ($mv_back (if $mv_accept done
                        (let* (($mv_b1 (tsg:unseat-frags (tsg:reverse $mv_new ())))
                               ($mv_b2 (ty:set-states $mv_st)))
                          (tsg:reseat-frags $mv_old (tsg:reverse $mv_olds ()))))))
     (moved $mv_n $mv_mold (if $mv_accept $mv_mnew $mv_mold))))
; K type moves at seeds drawn uniformly among the nodes (a node that is not a site is passed over):
; (tsg-typed (moves M) (sites S) (changed C))
(= (ty:sweep $tw_k) (let (tw $tw_m $tw_s $tw_c) (ty:sweep-each $tw_k (tw 0 0 0)) (println! (tsg-typed (moves $tw_m) (sites $tw_s) (changed $tw_c)))))
(= (ty:sweep-each $te_k $te_acc)
   (if (== $te_k 0) $te_acc
       (let* (($te_u (floor-math (* (tsg:uniform) (tsg:nodes))))
              ((tw $te_m $te_s $te_c) $te_acc)
              ($te_acc2 (if (tsg:steppable? $te_u)
                            (let (moved $te_n $te_a $te_b) (ty:move $te_u)
                              (tw (+ $te_m 1) (+ $te_s $te_n) (+ $te_c (if (== $te_a $te_b) 0 (if (> $te_a $te_b) (- $te_a $te_b) (- $te_b $te_a))))))
                            $te_acc)))
         (ty:sweep-each (- $te_k 1) $te_acc2))))
