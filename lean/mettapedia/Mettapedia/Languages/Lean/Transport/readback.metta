; The way back: a theorem of the transport closure as MeTTa holds it (its binders, statement
; and proof term, artifacts/lean-declarations/transport/proofs.metta), written as Lean source
; for the commands of Readback.lean.  A cited theorem is the one written back before it
; (Back.«c»).
;
;   back_theorem «c» [levels] : STATEMENT := PROOF   c, to be judged by Lean's kernel
;   back_missing «c» [levels] : STATEMENT            c's proof is not in the data
;   back_lemma «m» [levels] := PROOF                 a lemma MeTTa mined, before its first use
;
; A theorem's proof is the one a transformation gave it, (RewrittenProof c p), if any, else
; Lean's, (TransportProof c p).  A cut (phave) is evidence that the set reading's beta needs
; and Lean's conversion does not, so it is left out.
;
;   !(back:all (c ..))    every theorem, in the order given (each after what it cites)
;   !(back:controls (c ..))   the controls: twins that must be accepted, corruptions that must not

; A Lean name is text before it stands in a tuple: at a tuple's head, a name PeTTa defines
; (id, and, append) would be a call.  PeTTa reads True and False as its booleans; Lean's names
; spelled so are the propositions (the booleans are Bool.true and Bool.false).
(= (back:name $nm_c) (if (== $nm_c True) "True" (if (== $nm_c False) "False" (repr $nm_c))))
(= (back:join $jn_xs $jn_sep)
   (if (== $jn_xs ()) ""
       (if (== (cdr-atom $jn_xs) ()) (car-atom $jn_xs)
           (format-args "{}{}{}" ((car-atom $jn_xs) $jn_sep (back:join (cdr-atom $jn_xs) $jn_sep))))))
(= (back:level $lv_L)
   (case $lv_L
     (((lvl $lv_l) (format-args "{}" ($lv_l)))
      ((lsucc $lv_X) (format-args "({} + 1)" ((back:level $lv_X))))
      ((lmax $lv_A $lv_B) (format-args "(max {} {})" ((back:level $lv_A) (back:level $lv_B))))
      ((limax $lv_A2 $lv_B2) (format-args "(imax {} {})" ((back:level $lv_A2) (back:level $lv_B2))))
      ($lv_other (format-args "{}" ($lv_other))))))
(= (back:levels $ls_Ls)
   (if (== $ls_Ls ()) ()
       (let* (($ls_h (back:level (car-atom $ls_Ls))) ($ls_t (back:levels (cdr-atom $ls_Ls)))) (cons-atom $ls_h $ls_t))))
; A sort is read by position: a pattern headed by sort would be evaluated.
(= (back:is-sort $is_t)
   (if (== (get-metatype $is_t) Expression) (if (== $is_t ()) False (== (car-atom $is_t) sort)) False))
(= (back:term $tm_t)
   (if (back:is-sort $tm_t) (format-args "(Sort ({}))" ((back:level (car-atom (cdr-atom $tm_t)))))
   (case $tm_t
     (((var $tm_x) (format-args "{}" ($tm_x)))
      ((num $tm_k) (format-args "(nat_lit {})" ($tm_k)))
      ((str $tm_s) (repr $tm_s))
      ((prop) "Prop")
      ; a proof inside a term, where the reading kept Lean's.
      ((by $tm_w) (back:term $tm_w))
      ((cite $tm_cc $tm_cas) (back:cite $tm_cc $tm_cas))
      ; an erased one: by proof irrelevance any proof of its proposition is it (the judge
      ; takes one in scope or reflexivity, and never searches among theorems).
      ((proof) "_")
      ((app $tm_c $tm_as)
       (let $tm_n (back:name $tm_c)
         (if (== $tm_as ()) (format-args "@{}" ($tm_n))
             (format-args "(@{} {})" ($tm_n (back:join (back:terms $tm_as) " "))))))
      ((apv $tm_f $tm_bs) (back:apply $tm_f $tm_bs))
      ((lam $tm_y $tm_T $tm_b) (format-args "(no_implicit_lambda% (fun ({} : {}) => {}))" ($tm_y (back:term $tm_T) (back:term $tm_b))))
      ((arrow $tm_A $tm_B) (format-args "({} → {})" ((back:term $tm_A) (back:term $tm_B))))
      ((pi $tm_z $tm_C $tm_D) (format-args "(∀ ({} : {}), {})" ($tm_z (back:term $tm_C) (back:term $tm_D))))
      ($tm_other "UNREADABLE_term")))))
; An applied head takes every argument as written, implicit and instance ones too: so @, and
; a constant's own arguments and the further ones in one application.
(= (back:apply $ap_f $ap_bs)
   (case $ap_f
     (((var $ap_x) (format-args "(@{} {})" ($ap_x (back:join (back:terms $ap_bs) " "))))
      ((app $ap_c $ap_as)
       (let $ap_n (back:name $ap_c) (format-args "(@{} {})" ($ap_n (back:join (back:terms (append $ap_as $ap_bs)) " ")))))
      ($ap_other (format-args "({} {})" ((back:term $ap_other) (back:join (back:terms $ap_bs) " ")))))))
(= (back:terms $ts_ts)
   (if (== $ts_ts ()) ()
       (let* (($ts_h (back:term (car-atom $ts_ts))) ($ts_r (back:terms (cdr-atom $ts_ts)))) (cons-atom $ts_h $ts_r))))
(= (back:applied $ad_head $ad_as)
   (if (== $ad_as ()) $ad_head (format-args "({} {})" ($ad_head (back:join (back:proofs $ad_as) " ")))))
; A citation's level arguments come first, then its arguments.
(= (back:level-args $la_as)
   (if (== $la_as ()) ()
       (case (car-atom $la_as)
         (((level $la_L) (cons-atom (level $la_L) (back:level-args (cdr-atom $la_as))))
          ($la_other ())))))
(= (back:cite-rest $cr_as)
   (if (== $cr_as ()) ()
       (case (car-atom $cr_as) (((level $cr_L) (back:cite-rest (cdr-atom $cr_as))) ($cr_other $cr_as)))))
(= (back:level-texts $lt_as)
   (if (== $lt_as ()) ()
       (case (car-atom $lt_as)
         (((level $lt_L) (let* (($lt_h (back:level $lt_L)) ($lt_r (back:level-texts (cdr-atom $lt_as)))) (cons-atom $lt_h $lt_r)))
          ($lt_other ())))))
(= (back:mined? $mi_c) (let $mi_q (collapse (match &self (MinedLemma $mi_c $mi_ls $mi_v) yes)) (if (== $mi_q ()) False True)))
(= (back:cite $ci_c $ci_as)
   (let* (($ci_back (or (not (== (collapse (match &self (TransportTheorem $ci_c $ci_bs $ci_P) yes)) ()))
                        (back:mined? $ci_c)))
          ($ci_text (back:name $ci_c))
          ($ci_name (if $ci_back (format-args "Back.«{}»" ($ci_text)) $ci_text))
          ($ci_ls (back:level-texts $ci_as))
          ($ci_head (if (== $ci_ls ()) (format-args "@{}" ($ci_name))
                        (format-args "@{}.{}{}{}" ($ci_name "{" (back:join $ci_ls ", ") "}")))))
     (back:applied $ci_head (back:cite-rest $ci_as))))
(= (back:proof $pf_p)
   (case $pf_p
     (((plam $pf_x $pf_T $pf_b) (format-args "(no_implicit_lambda% (fun ({} : {}) => {}))" ($pf_x (back:term $pf_T) (back:proof $pf_b))))
      ((phave $pf_fact $pf_by $pf_body) (back:proof $pf_body))
      ((phyp $pf_h $pf_hs) (back:applied (format-args "{}" ($pf_h)) $pf_hs))
      ((pcite $pf_c $pf_cs) (back:cite $pf_c $pf_cs))
      ((pctor $pf_k $pf_ks) (let $pf_kn (back:name $pf_k) (back:applied (format-args "@{}" ($pf_kn)) $pf_ks)))
      ((prec $pf_r $pf_rs) (let $pf_rn (back:name $pf_r) (back:applied (format-args "@{}" ($pf_rn)) $pf_rs)))
      ((pquot $pf_q $pf_qs) (let $pf_qn (back:name $pf_q) (back:applied (format-args "@{}" ($pf_qn)) $pf_qs)))
      ((pproj $pf_S $pf_i $pf_of $pf_ps)
       (let $pf_Sn (back:name $pf_S)
         (back:applied (format-args "(proj% {} {} ({}))" ($pf_Sn $pf_i (back:proof $pf_of))) $pf_ps)))
      ($pf_term (back:term $pf_term)))))
(= (back:proofs $ps_ps)
   (if (== $ps_ps ()) ()
       (let* (($ps_h (back:proof (car-atom $ps_ps))) ($ps_r (back:proofs (cdr-atom $ps_ps)))) (cons-atom $ps_h $ps_r))))
(= (back:statement $st_bs $st_P)
   (if (== $st_bs ()) (back:term $st_P)
       (let $st_rest (back:statement (cdr-atom $st_bs) $st_P)
         (case (car-atom $st_bs)
           (((type $st_v $st_l) (format-args "(∀ ({} : Type ({})), {})" ($st_v (back:level $st_l) $st_rest)))
            ((sort $st_w $st_m) (format-args "(∀ ({} : Sort ({})), {})" ($st_w (back:level $st_m) $st_rest)))
            ((term $st_x $st_T) (format-args "(∀ ({} : {}), {})" ($st_x (back:term $st_T) $st_rest)))
            ((hyp $st_h $st_Q) (format-args "(∀ ({} : {}), {})" ($st_h (back:term $st_Q) $st_rest))))))))

;;; theorems

; The proof a theorem is written with: a transformation's, else Lean's.
(= (back:proof-of $po_c)
   (let $po_new (collapse (match &self (RewrittenProof $po_c $po_p) $po_p))
     (if (== $po_new ())
         (let $po_old (collapse (match &self (TransportProof $po_c $po_q) $po_q))
           (if (== $po_old ()) None (car-atom $po_old)))
         (car-atom $po_new))))
; (BINDERS STATEMENT LEVELS PROOF) of a theorem, or None
(= (back:data $da_c)
   (let $da_found (collapse (match &self (, (TransportTheorem $da_c $da_bs $da_P) (TransportLevels $da_c $da_ls)) ($da_bs $da_P $da_ls)))
     (if (== $da_found ()) None
         (let* ((($da_binders $da_body $da_levels) (car-atom $da_found))
                ($da_proof (back:proof-of $da_c)))
           ($da_binders $da_body $da_levels $da_proof)))))
(= (back:line $ln_word $ln_key $ln_binders $ln_body $ln_levels $ln_proof)
   (println! (format-args "{} «{}» [{}] : {} := {}"
                          ($ln_word (back:name $ln_key) (back:join (back:levels $ln_levels) ", ")
                           (back:statement $ln_binders $ln_body) (back:proof $ln_proof)))))
; A lemma MeTTa mined, written before the first theorem that cites it; Lean infers its statement.
(= (back:lemma $lm_n)
   (let $lm_found (collapse (match &self (MinedLemma $lm_n $lm_ls $lm_v) ($lm_ls $lm_v)))
     (if (== $lm_found ()) done
         (let ($lm_levels $lm_value) (car-atom $lm_found)
           (println! (format-args "back_lemma «{}» [{}] := {}" ((back:name $lm_n) (back:join $lm_levels ", ") (back:proof $lm_value))))))))
(= (back:lemmas $ls_ns) (if (== $ls_ns ()) done (let $ls_one (back:lemma (car-atom $ls_ns)) (back:lemmas (cdr-atom $ls_ns)))))
(= (back:theorem $th_c)
   (let* (($th_pre (back:lemmas (collapse (match &self (MinedBefore $th_pre_n $th_c) $th_pre_n))))
          ($th_data (back:data $th_c)))
     (if (== $th_data None) skipped
         (let ($th_binders $th_body $th_levels $th_proof) $th_data
           (if (== $th_proof None)
               (println! (format-args "back_missing «{}» [{}] : {}"
                                      ((back:name $th_c) (back:join (back:levels $th_levels) ", ") (back:statement $th_binders $th_body))))
               (back:line back_theorem $th_c $th_binders $th_body $th_levels $th_proof))))))
(= (back:all $al_cs)
   (if (== $al_cs ()) done (let $al_done (back:theorem (car-atom $al_cs)) (back:all (cdr-atom $al_cs)))))

;;; controls: a theorem judged twice under Probe, as written (it must be accepted) and
;;; corrupted on its data (it must be refused)

; the right side of an equation made its successor: a statement the proof does not prove
(= (back:succ-right $sr_P)
   (case $sr_P (((app Eq ($sr_T $sr_L $sr_R)) (app Eq ($sr_T $sr_L (app Nat.succ ($sr_R))))) ($sr_other None))))
; one hypothesis put where another stood
(= (back:rename-hyp $rh_t $rh_from $rh_to)
   (if (term:expr? $rh_t)
       (if (== (car-atom $rh_t) phyp)
           (if (== (term:h1 $rh_t) $rh_from)
               (let $rh_args (back:rename-hyp (term:h2 $rh_t) $rh_from $rh_to) (phyp $rh_to $rh_args))
               (back:rename-hyp-list $rh_t $rh_from $rh_to))
           (back:rename-hyp-list $rh_t $rh_from $rh_to))
       $rh_t))
(= (back:rename-hyp-list $rl_xs $rl_from $rl_to)
   (if (== $rl_xs ()) () (cons-atom (back:rename-hyp (car-atom $rl_xs) $rl_from $rl_to) (back:rename-hyp-list (cdr-atom $rl_xs) $rl_from $rl_to))))
; the first citation of a mined lemma whose first two arguments differ, with them swapped, or None
(= (back:swap-here $sh_t)
   (if (== (car-atom $sh_t) pcite)
       (if (back:mined? (term:h1 $sh_t))
           (let* (($sh_as (term:h2 $sh_t)) ($sh_rest (back:cite-rest $sh_as)))
             (if (< (term:length $sh_rest) 2) None
                 (let* (($sh_x (car-atom $sh_rest)) ($sh_y (car-atom (cdr-atom $sh_rest))))
                   (if (== $sh_x $sh_y) None
                       (let $sh_args (term:concat (back:level-args $sh_as) (cons-atom $sh_y (cons-atom $sh_x (cdr-atom (cdr-atom $sh_rest)))))
                         (pcite (term:h1 $sh_t) $sh_args))))))
           None)
       None))
(= (back:swap-in $sw_t)
   (if (term:expr? $sw_t)
       (let $sw_here (back:swap-here $sw_t)
         (if (== $sw_here None) (back:swap-in-list $sw_t) $sw_here))
       None))
(= (back:swap-in-list $sl_xs)
   (if (== $sl_xs ()) None
       (let $sl_h (back:swap-in (car-atom $sl_xs))
         (if (== $sl_h None)
             (let $sl_t (back:swap-in-list (cdr-atom $sl_xs)) (if (== $sl_t None) None (cons-atom (car-atom $sl_xs) $sl_t)))
             (cons-atom $sl_h (cdr-atom $sl_xs))))))
(= (back:mined-control $mc_cs)
   (if (== $mc_cs ()) none
       (let* (($mc_c (car-atom $mc_cs)) ($mc_data (back:data $mc_c)))
         (if (== $mc_data None) (back:mined-control (cdr-atom $mc_cs))
             (let ($mc_binders $mc_body $mc_levels $mc_proof) $mc_data
               (let $mc_swapped (if (== $mc_proof None) None (back:swap-in $mc_proof))
                 (if (== $mc_swapped None) (back:mined-control (cdr-atom $mc_cs))
                     (let $mc_ok (back:line back_accept $mc_c $mc_binders $mc_body $mc_levels $mc_proof)
                       (back:line back_refuse $mc_c $mc_binders $mc_body $mc_levels $mc_swapped)))))))))
(= (back:controls $ct_cs)
   (let* ((($pe_bs $pe_P $pe_ls $pe_p) (back:data List.Perm.length_eq))
          ($c1 (back:line back_accept List.Perm.length_eq $pe_bs $pe_P $pe_ls $pe_p))
          ($c2 (back:line back_refuse List.Perm.length_eq $pe_bs (back:succ-right $pe_P) $pe_ls $pe_p))
          ($c3 (back:line back_refuse List.Perm.length_eq $pe_bs $pe_P $pe_ls (back:rename-hyp $pe_p v_ih v_a)))
          (($az_bs $az_P $az_ls $az_p) (back:data Nat.add_zero))
          ($c4 (back:line back_accept Nat.add_zero $az_bs $az_P $az_ls $az_p))
          ($c5 (back:line back_refuse Nat.mul_one $az_bs $az_P $az_ls $az_p)))
     (back:mined-control $ct_cs)))
