; ============================================================================
; SelfMeTTa v2 generic witness substrate.
;
; Classification: generic substrate.  Clients provide a LanguageDef name plus a
; guest rewrite table; this checker verifies explicit-position rewrite traces
; with ordered rules and repeated-pattern-variable matching.
; ============================================================================

(= (sm_v2_ld $name $rules)
   (LanguageDef $name
     (Syntax (Terms MSym MApp MVar) (Rules RNil RCons Rule)
             (Path PHere PFun PArg) (Trace TNil TCons EvalStep EvalStepAt))
     (Semantics PureMOPSContextRewrite)
     $rules))
(= (sm_ld_rules (LanguageDef $name $syntax $semantics $rules)) $rules)

; ---------- finite rule tables ----------------------------------------------
(= (sm_rule_lookup $name RNil) None)
(= (sm_rule_lookup $name (RCons (Rule $rname $lhs $rhs) $rest))
   (if (== $name $rname)
     (Some (Rule $rname $lhs $rhs))
     (sm_rule_lookup $name $rest)))

; ---------- substitutions ----------------------------------------------------
(= (sm_lookup $name SNil) None)
(= (sm_lookup $name (SCons (Bind $bname $term) $rest))
   (if (== $name $bname) (Some $term) (sm_lookup $name $rest)))

(= (sm_bind $name $term $sigma)
   (let $found (sm_lookup $name $sigma)
     (unify $found None
       (Ok (SCons (Bind $name $term) $sigma))
       (unify $found (Some $old)
         (if (== $old $term) (Ok $sigma) (Err sigma_conflict))
         (Err sigma_lookup_bad)))))

(= (sm_sig1 $x $tx) (SCons (Bind $x $tx) SNil))
(= (sm_sig2 $x $tx $y $ty) (SCons (Bind $y $ty) (SCons (Bind $x $tx) SNil)))
(= (sm_sig3 $x $tx $y $ty $z $tz)
   (SCons (Bind $z $tz) (SCons (Bind $y $ty) (SCons (Bind $x $tx) SNil))))

; ---------- first-order pattern matching over guest data ---------------------
(= (sm_match (MVar $name) $term $sigma) (sm_bind $name $term $sigma))
(= (sm_match (MSym $lhs) $term $sigma)
   (unify $term (MSym $rhs)
     (if (== $lhs $rhs) (Ok $sigma) (Err symbol_mismatch))
     (Err shape_mismatch)))
(= (sm_match (MApp $pf $pa) $term $sigma)
   (unify $term (MApp $tf $ta)
     (let $rf (sm_match $pf $tf $sigma)
       (unify $rf (Ok $sigma1) (sm_match $pa $ta $sigma1) $rf))
     (Err shape_mismatch)))

; ---------- sigma-instantiation of rhs terms --------------------------------
(= (sm_inst (MSym $name) $sigma) (Ok (MSym $name)))
(= (sm_inst (MVar $name) $sigma)
   (let $found (sm_lookup $name $sigma)
     (unify $found (Some $term) (Ok $term) (Err unbound_rhs_var))))
(= (sm_inst (MApp $f $a) $sigma)
   (let $rf (sm_inst $f $sigma)
     (unify $rf (Ok $f1)
       (let $ra (sm_inst $a $sigma)
         (unify $ra (Ok $a1) (Ok (MApp $f1 $a1)) $ra))
       $rf)))

; ---------- explicit position paths through guest MApp terms ----------------
(= (sm_focus PHere $term) (Ok $term))
(= (sm_focus (PFun $pos) $term)
   (unify $term (MApp $f $a) (sm_focus $pos $f) (Err wrong_position)))
(= (sm_focus (PArg $pos) $term)
   (unify $term (MApp $f $a) (sm_focus $pos $a) (Err wrong_position)))

(= (sm_replace PHere $term $new) (Ok $new))
(= (sm_replace (PFun $pos) $term $new)
   (unify $term (MApp $f $a)
     (let $rf (sm_replace $pos $f $new)
       (unify $rf (Ok $f1) (Ok (MApp $f1 $a)) $rf))
     (Err wrong_position)))
(= (sm_replace (PArg $pos) $term $new)
   (unify $term (MApp $f $a)
     (let $ra (sm_replace $pos $a $new)
       (unify $ra (Ok $a1) (Ok (MApp $f $a1)) $ra))
     (Err wrong_position)))

; ---------- witness checking -------------------------------------------------
(= (sm_rule_applies $term (Rule $name $lhs $rhs))
   (let $m (sm_match $lhs $term SNil)
     (unify $m (Ok $sigma) True False)))
(= (sm_prior_redex $rule_name RNil $term) False)
(= (sm_prior_redex $rule_name (RCons (Rule $rname $lhs $rhs) $rest) $term)
   (if (== $rule_name $rname)
     False
     (if (sm_rule_applies $term (Rule $rname $lhs $rhs))
       True
       (sm_prior_redex $rule_name $rest $term))))
(= (sm_has_redex $rules $term)
   (if (sm_has_root_redex $rules $term) True (sm_has_child_redex $rules $term)))
(= (sm_has_root_redex $rules $term) (sm_has_root_redex_go $rules $term))
(= (sm_has_root_redex_go RNil $term) False)
(= (sm_has_root_redex_go (RCons $rule $rest) $term)
   (if (sm_rule_applies $term $rule) True (sm_has_root_redex_go $rest $term)))
(= (sm_has_child_redex $rules $term)
   (unify $term (MApp $f $a)
     (if (sm_has_redex $rules $f) True (sm_has_redex $rules $a))
     False))
(= (sm_normal $rules $term) (if (sm_has_redex $rules $term) False True))

(= (sm_check_step $rules (EvalStep $expr $sigma $rule_name $expr1))
   (sm_check_step_at_impl non_matching_lhs $rules $expr PHere $sigma $rule_name $expr1))
(= (sm_check_step $rules (EvalStepAt $expr $pos $sigma $rule_name $expr1))
   (sm_check_step_at_impl wrong_position $rules $expr $pos $sigma $rule_name $expr1))

(= (sm_check_step_at_impl $match_err $rules $expr $pos $sigma $rule_name $expr1)
   (let $found (sm_rule_lookup $rule_name $rules)
     (unify $found (Some (Rule $rname $lhs $rhs))
       (let $focus_r (sm_focus $pos $expr)
         (unify $focus_r (Ok $focus)
           (if (sm_prior_redex $rule_name $rules $focus)
             (Err wrong_rule_order)
             (let $m (sm_match $lhs $focus SNil)
               (unify $m (Ok $actual_sigma)
                 (if (== $actual_sigma $sigma)
                   (let $ir (sm_inst $rhs $sigma)
                     (unify $ir (Ok $rhs1)
                       (let $rr (sm_replace $pos $expr $rhs1)
                         (unify $rr (Ok $expected_expr1)
                           (if (== $expr1 $expected_expr1) (Ok $expr1) (Err wrong_rhs))
                           $rr))
                       $ir))
                   (Err wrong_sigma))
                 (Err $match_err))))
           $focus_r))
       (Err no_rule))))

(= (sm_step_from $step)
   (unify $step (EvalStep $from $sigma $rule_name $to)
     (Ok $from)
     (unify $step (EvalStepAt $from2 $pos $sigma2 $rule_name2 $to2)
       (Ok $from2)
       (Err malformed_step))))

(= (sm_trace_fits $fuel TNil) True)
(= (sm_trace_fits $fuel (TCons $step $rest))
   (if (== $fuel 0) False (sm_trace_fits (- $fuel 1) $rest)))

(= (sm_check_trace $rules $current TNil $final)
   (if (== $current $final)
     (if (sm_normal $rules $final) (Ok $final) (Err final_not_normal))
     (Err skipped_step)))
(= (sm_check_trace $rules $current (TCons $step $rest) $final)
   (let $from_r (sm_step_from $step)
     (unify $from_r (Ok $from)
     (if (== $current $from)
       (let $checked (sm_check_step $rules $step)
         (unify $checked (Ok $next)
           (sm_check_trace $rules $next $rest $final)
           $checked))
       (Err skipped_step))
     $from_r)))

(= (sm_check_normalize $ld $start $fuel $trace $final)
   (if (sm_trace_fits $fuel $trace)
     (sm_check_trace (sm_ld_rules $ld) $start $trace $final)
     (Err fuel_exhausted)))
