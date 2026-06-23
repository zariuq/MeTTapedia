!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
;  imp_coherence_exp1_petta.metta  --  GOAL #3 (PeTTa parity of the EXHAUSTIVE
;  CeTTa harness).  Same rules, same enumeration; PeTTa adapters = lib_he unify,
;  underscore names, !(test ...).  See imp_coherence_exp1.metta for the spec.
;    ◇ side  = `prove` (emits the derivation);  CHECK = `k_check`.
;    Coherence over ALL (Γ,φ): every Found cert is kernel-accepted with concl φ.
;  SCOPE: ⇒-fragment; atoms {A,B,C}; size≤3; |Γ|≤1; depth 3 (adequacy vs 4).
; =============================================================================

; ---------------- booleans + hyp lists --------------------------------------
(= (and_b True $y) $y)
(= (and_b False $y) False)
(= (not_b True) False)
(= (not_b False) True)
(= (h_mem $x HNil) False)
(= (h_mem $x (HCons $y $ys)) (if (== $x $y) True (h_mem $x $ys)))
(= (h_remove $x HNil) HNil)
(= (h_remove $x (HCons $y $ys))
   (if (== $x $y) (h_remove $x $ys) (HCons $y (h_remove $x $ys))))
(= (h_union HNil $ys) $ys)
(= (h_union (HCons $x $xs) $ys) (HCons $x (h_union $xs $ys)))
(= (h_append HNil $ys) $ys)
(= (h_append (HCons $x $xs) $ys) (HCons $x (h_append $xs $ys)))
(= (h_subset HNil $ys) True)
(= (h_subset (HCons $x $xs) $ys) (and_b (h_mem $x $ys) (h_subset $xs $ys)))

(= (atoms) (HCons (Atom A) (HCons (Atom B) (HCons (Atom C) HNil))))
(= (cands $ctx) (h_append (atoms) $ctx))

; ============ CHECK SIDE: trusted witness validator =========================
(= (k_check (CAssume $p)) (Ok (Seq (HCons $p HNil) $p)))
(= (k_check (CDisch $p $c))
   (let $r (k_check $c)
     (unify $r (Ok (Seq $g $q))
       (Ok (Seq (h_remove $p $g) (Imp $p $q)))
       $r)))
(= (k_check (CMP $c1 $c2))
   (let $r1 (k_check $c1)
     (let $r2 (k_check $c2)
       (unify $r1 (Ok (Seq $g1 (Imp $p $q)))
         (unify $r2 (Ok (Seq $g2 $p2))
           (if (== $p $p2) (Ok (Seq (h_union $g1 $g2) $q)) (Err mp_antecedent_mismatch))
           $r2)
         $r1))))
(= (concl (Ok (Seq $g $c))) $c)
(= (concl (Err $e)) (NoConcl $e))

; ============ ◇ SIDE: exhaustive depth-bounded search, EMITS a cert ==========
(= (prove Z $ctx $phi)
   (if (h_mem $phi $ctx) (Found (CAssume $phi)) NoProof))
(= (prove (S $d) $ctx $phi)
   (if (h_mem $phi $ctx)
       (Found (CAssume $phi))
       (try_intro (S $d) $ctx $phi)))
(= (try_intro (S $d) $ctx (Atom $x)) (mp_scan $d $ctx (Atom $x) (cands $ctx)))
(= (try_intro (S $d) $ctx (Imp $a $b))
   (let $r (prove $d (HCons $a $ctx) $b)
     (unify $r (Found $c)
        (Found (CDisch $a $c))
        (mp_scan $d $ctx (Imp $a $b) (cands $ctx)))))
(= (mp_scan $d $ctx $phi HNil) NoProof)
(= (mp_scan $d $ctx $phi (HCons $c $cs))
   (let $r1 (prove $d $ctx (Imp $c $phi))
     (unify $r1 (Found $c1)
        (let $r2 (prove $d $ctx $c)
          (unify $r2 (Found $c2)
             (Found (CMP $c1 $c2))
             (mp_scan $d $ctx $phi $cs)))
        (mp_scan $d $ctx $phi $cs))))
(= (is_found (Found $c)) True)
(= (is_found NoProof) False)

; ============ ENUMERATION =====================================================
(= (imps_from $a HNil) HNil)
(= (imps_from $a (HCons $b $bs)) (HCons (Imp $a $b) (imps_from $a $bs)))
(= (imp_pairs HNil $bs) HNil)
(= (imp_pairs (HCons $a $as) $bs) (h_append (imps_from $a $bs) (imp_pairs $as $bs)))
(= (formulas3) (h_append (atoms) (imp_pairs (atoms) (atoms))))
(= (singletons HNil) HNil)
(= (singletons (HCons $f $fs)) (HCons (HCons $f HNil) (singletons $fs)))
(= (contexts1) (HCons HNil (singletons (formulas3))))
(= (pairs_for $g HNil) HNil)
(= (pairs_for $g (HCons $phi $phis)) (HCons (Pr $g $phi) (pairs_for $g $phis)))
(= (all_pairs HNil $phis) HNil)
(= (all_pairs (HCons $g $gs) $phis) (h_append (pairs_for $g $phis) (all_pairs $gs $phis)))
(= (PAIRS) (all_pairs (contexts1) (formulas3)))
(= (D) (S (S Z)))   ; depth 2 — complete for size≤3 goals; adequacy checks 2 vs 3

; ============ AUDIT + ADEQUACY ===============================================
(= (check_found NoProof $g $phi) OK)
(= (check_found (Found $c) $g $phi)
   (let $kc (k_check $c)
     (unify $kc (Ok (Seq $gg $cc))
        (if (and_b (== $cc $phi) (h_subset $gg $g)) OK (BAD_unsound $g $phi $cc))
        (BAD_rejected $g $phi))))
(= (audit $d HNil) HNil)
(= (audit $d (HCons (Pr $g $phi) $rest))
   (let $r (check_found (prove $d $g $phi) $g $phi)
     (if (== $r OK) (audit $d $rest) (HCons $r (audit $d $rest)))))
(= (found_vec $d HNil) HNil)
(= (found_vec $d (HCons (Pr $g $phi) $rest))
   (HCons (is_found (prove $d $g $phi)) (found_vec $d $rest)))
(= (found_stable $d $pairs)
   (== (found_vec $d $pairs) (found_vec (S $d) $pairs)))

; =============================== TESTS =======================================
(= (coh $d $ctx $phi)
   (let $r (prove $d $ctx $phi) (unify $r (Found $c) (Yes (concl (k_check $c))) No)))
!(test (coh (D) HNil (Imp (Atom A) (Atom A))) (Yes (Imp (Atom A) (Atom A))))
!(test (coh (D) HNil (Imp (Atom A) (Imp (Atom B) (Atom A))))
              (Yes (Imp (Atom A) (Imp (Atom B) (Atom A)))))
!(test (coh (D) (HCons (Imp (Atom A) (Atom B)) (HCons (Atom A) HNil)) (Atom B))
              (Yes (Atom B)))
!(test (coh (D) HNil (Imp (Atom A) (Atom B))) No)
!(test (coh (D) HNil (Atom B)) No)

; exhaustive terminal (criteria 2+3 audit empty; criterion 4 adequacy stable)
!(test (audit (D) (PAIRS)) HNil)
!(test (found_stable (D) (PAIRS)) True)
