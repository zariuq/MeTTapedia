!(import! &self /home/aimama/aihub/hyperon/PeTTa/lib/lib_he)

; =============================================================================
; provenance_tree_v0.metta
;
; One checked proof trace, two readouts:
;   * Boolean axiom ledger: which trusted axioms/rules occur?
;   * WM-PLN-style evidence: a truth-value/evidence projection.
;
; This file deliberately does NOT mint theoremhood.  Provenance projections are
; evidence about an already checked proof trace, never a replacement for checking.
; =============================================================================

(= (memb $x Nil) False)
(= (memb $x (Cons $y $ys)) (if (== $x $y) True (memb $x $ys)))
(= (lmerge Nil $ys) $ys)
(= (lmerge (Cons $x $xs) $ys) (if (memb $x $ys) (lmerge $xs $ys) (Cons $x (lmerge $xs $ys))))

(= (prov-ledger (PLeaf $ax)) (Cons $ax Nil))
(= (prov-ledger (PStep $rule PNil)) (Cons $rule Nil))
(= (prov-ledger (PStep $rule (PCons $p $rest)))
   (lmerge (Cons $rule Nil) (lmerge (prov-ledger $p) (prov-ledger-list $rest))))
(= (prov-ledger-list PNil) Nil)
(= (prov-ledger-list (PCons $p $rest))
   (lmerge (prov-ledger $p) (prov-ledger-list $rest)))

(= (min2 $x $y) (if (< $x $y) $x $y))
(= (tv-and (TV $s1 $c1) (TV $s2 $c2)) (TV (min2 $s1 $s2) (min2 $c1 $c2)))
(= (tv-of-axiom ax-1) (TV 95 99))
(= (tv-of-axiom ax-2) (TV 93 99))
(= (tv-of-axiom ax-mp) (TV 98 99))
(= (tv-of-axiom dtest) (TV 80 90))

(= (prov-tv (PLeaf $ax)) (tv-of-axiom $ax))
(= (prov-tv (PStep $rule PNil)) (tv-of-axiom $rule))
(= (prov-tv (PStep $rule (PCons $p $rest)))
   (tv-and (tv-of-axiom $rule) (tv-and (prov-tv $p) (prov-tv-list $rest))))
(= (prov-tv-list PNil) (TV 100 100))
(= (prov-tv-list (PCons $p $rest)) (tv-and (prov-tv $p) (prov-tv-list $rest)))

(= (prov->wm $trace $theorem)
   (WMEvidence (prov-tv $trace) (KernelTrace $trace) $theorem))
(= (wm-mints-theorem $wm) False)

; A compact provenance tree for the Metamath id proof:
;   final mp combines
;     D  from ax-1
;     C  from mp(B from ax-1, A from ax-2)
(= (id-prov-tree)
   (PStep ax-mp
     (PCons (PLeaf ax-1)
       (PCons
         (PStep ax-mp
           (PCons (PLeaf ax-1)
             (PCons (PLeaf ax-2) PNil)))
         PNil))))

(= (id-theorem) (wi (Var ph) (Var ph)))

!(test (memb ax-1 (prov-ledger (id-prov-tree))) True)
!(test (memb ax-2 (prov-ledger (id-prov-tree))) True)
!(test (memb ax-mp (prov-ledger (id-prov-tree))) True)
!(test (memb dtest (prov-ledger (id-prov-tree))) False)

; Boolean projection and WM projection read the same source tree.
!(test (prov-tv (id-prov-tree)) (TV 93 99))
!(test
   (prov->wm (id-prov-tree) (id-theorem))
   (WMEvidence (TV 93 99) (KernelTrace (id-prov-tree)) (wi (Var ph) (Var ph))))

; Evidence cannot mint a theorem.
!(test (wm-mints-theorem (prov->wm (id-prov-tree) (id-theorem))) False)
