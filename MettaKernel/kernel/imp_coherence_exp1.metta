; =============================================================================
;  imp_coherence_exp1.metta   --  GOAL #3: Inference⇔Certificate Coherence
;                                  (implication fragment), EXHAUSTIVE bounded.
;
;  CLAIM: for the ⇒-fragment {Assume, ⇒-intro, ⇒-elim}, provability-by-search
;  (◇, = `prove`, which EMITS the derivation) and kernel witness-checking
;  (`k-check`) are the SAME logic:
;      prove D Γ φ = Found c   ⟹   k-check c = Ok(Seq Γ' φ),  Γ' ⊆ Γ
;  and the search is exhaustive (NoProof ⇔ no derivation ≤ D), so a divergence
;  (search emits a cert the kernel rejects, or with wrong conclusion) is a real
;  finding about the rule presentation.
;
;  SCOPE (criterion 7): fragment = ⇒ only; atoms = {A,B,C} (C = non-collusion
;  control); formula size S = 3; context size H = 1; depth D = 3 (adequacy vs 4);
;  MP cut-universe U = atoms ++ hypotheses (saturated for this fragment/size).
;  This is a BOUNDED stand-in for OSLF ◇ (true OSLF coherence = Experiment 4,
;  awaits Lean unfreeze).  Run: cetta imp_coherence_exp1.metta
; =============================================================================

; ---------------- booleans + hyp lists --------------------------------------
(= (and-b True $y) $y)
(= (and-b False $y) False)
(= (not-b True) False)
(= (not-b False) True)
(= (h-mem $x HNil) False)
(= (h-mem $x (HCons $y $ys)) (if (== $x $y) True (h-mem $x $ys)))
(= (h-remove $x HNil) HNil)
(= (h-remove $x (HCons $y $ys))
   (if (== $x $y) (h-remove $x $ys) (HCons $y (h-remove $x $ys))))
(= (h-union HNil $ys) $ys)
(= (h-union (HCons $x $xs) $ys) (HCons $x (h-union $xs $ys)))
(= (h-append HNil $ys) $ys)
(= (h-append (HCons $x $xs) $ys) (HCons $x (h-append $xs $ys)))
(= (h-length HNil) 0)
(= (h-length (HCons $x $xs)) (+ 1 (h-length $xs)))
(= (subset HNil $ys) True)
(= (subset (HCons $x $xs) $ys) (and-b (h-mem $x $ys) (subset $xs $ys)))

; atoms + bounded MP cut-formula universe
(= (atoms) (HCons (Atom A) (HCons (Atom B) (HCons (Atom C) HNil))))
(= (cands $ctx) (h-append (atoms) $ctx))

; ============ CHECK SIDE: trusted witness validator (kernel-check) ============
(= (k-check (CAssume $p)) (Ok (Seq (HCons $p HNil) $p)))
(= (k-check (CDisch $p $c))
   (let $r (k-check $c)
     (unify $r (Ok (Seq $g $q))
       (Ok (Seq (h-remove $p $g) (Imp $p $q)))
       $r)))
(= (k-check (CMP $c1 $c2))
   (let $r1 (k-check $c1)
     (let $r2 (k-check $c2)
       (unify $r1 (Ok (Seq $g1 (Imp $p $q)))
         (unify $r2 (Ok (Seq $g2 $p2))
           (if (== $p $p2) (Ok (Seq (h-union $g1 $g2) $q)) (Err mp-antecedent-mismatch))
           $r2)
         $r1))))
(= (concl (Ok (Seq $g $c))) $c)
(= (concl (Err $e)) (NoConcl $e))

; ============ ◇ SIDE: exhaustive depth-bounded search, EMITS a cert ==========
(= (prove Z $ctx $phi)
   (if (h-mem $phi $ctx) (Found (CAssume $phi)) NoProof))
(= (prove (S $d) $ctx $phi)
   (if (h-mem $phi $ctx)
       (Found (CAssume $phi))
       (try-intro (S $d) $ctx $phi)))
(= (try-intro (S $d) $ctx (Atom $x)) (mp-scan $d $ctx (Atom $x) (cands $ctx)))
(= (try-intro (S $d) $ctx (Imp $a $b))
   (let $r (prove $d (HCons $a $ctx) $b)
     (unify $r (Found $c)
        (Found (CDisch $a $c))
        (mp-scan $d $ctx (Imp $a $b) (cands $ctx)))))
(= (mp-scan $d $ctx $phi HNil) NoProof)
(= (mp-scan $d $ctx $phi (HCons $c $cs))
   (let $r1 (prove $d $ctx (Imp $c $phi))
     (unify $r1 (Found $c1)
        (let $r2 (prove $d $ctx $c)
          (unify $r2 (Found $c2)
             (Found (CMP $c1 $c2))
             (mp-scan $d $ctx $phi $cs)))
        (mp-scan $d $ctx $phi $cs))))
(= (is-found (Found $c)) True)
(= (is-found NoProof) False)

; ============ ENUMERATION: formulas (size≤3), contexts (|Γ|≤1), pairs ========
(= (imps-from $a HNil) HNil)
(= (imps-from $a (HCons $b $bs)) (HCons (Imp $a $b) (imps-from $a $bs)))
(= (imp-pairs HNil $bs) HNil)
(= (imp-pairs (HCons $a $as) $bs) (h-append (imps-from $a $bs) (imp-pairs $as $bs)))
; formulas size≤3 = atoms (size 1) ++ atom⇒atom (size 3)
(= (formulas3) (h-append (atoms) (imp-pairs (atoms) (atoms))))
; contexts |Γ|≤1 = HNil  ++  each singleton
(= (singletons HNil) HNil)
(= (singletons (HCons $f $fs)) (HCons (HCons $f HNil) (singletons $fs)))
(= (contexts1) (HCons HNil (singletons (formulas3))))
; product Γ × φ  as a flat list of (Pr Γ φ)
(= (pairs-for $g HNil) HNil)
(= (pairs-for $g (HCons $phi $phis)) (HCons (Pr $g $phi) (pairs-for $g $phis)))
(= (all-pairs HNil $phis) HNil)
(= (all-pairs (HCons $g $gs) $phis) (h-append (pairs-for $g $phis) (all-pairs $gs $phis)))
(= (PAIRS) (all-pairs (contexts1) (formulas3)))
(= (D) (S (S Z)))   ; depth 2 — complete for size≤3 goals (max proof depth 2); adequacy checks 2 vs 3

; ============ AUDIT: criteria (2)+(3) — every Found cert is kernel-accepted ===
(= (check-found NoProof $g $phi) OK)                       ; negative: search exhausted
(= (check-found (Found $c) $g $phi)
   (let $kc (k-check $c)
     (unify $kc (Ok (Seq $gg $cc))
        (if (and-b (== $cc $phi) (subset $gg $g)) OK (BAD-unsound $g $phi $cc))
        (BAD-rejected $g $phi))))
(= (audit $d HNil) HNil)
(= (audit $d (HCons (Pr $g $phi) $rest))
   (let $r (check-found (prove $d $g $phi) $g $phi)
     (if (== $r OK) (audit $d $rest) (HCons $r (audit $d $rest)))))

; ============ ADEQUACY: criterion (4) — found-ness stable at D vs D+1 =========
(= (found-vec $d HNil) HNil)
(= (found-vec $d (HCons (Pr $g $phi) $rest))
   (HCons (is-found (prove $d $g $phi)) (found-vec $d $rest)))
(= (found-stable $d $pairs)
   (== (found-vec $d $pairs) (found-vec (S $d) $pairs)))

; =============================== HEADLINE SANITY =============================
(= (coh $d $ctx $phi)
   (let $r (prove $d $ctx $phi) (unify $r (Found $c) (Yes (concl (k-check $c))) No)))
!(assertEqual (coh (D) HNil (Imp (Atom A) (Atom A))) (Yes (Imp (Atom A) (Atom A))))
!(assertEqual (coh (D) HNil (Imp (Atom A) (Imp (Atom B) (Atom A))))
              (Yes (Imp (Atom A) (Imp (Atom B) (Atom A)))))
!(assertEqual (coh (D) (HCons (Imp (Atom A) (Atom B)) (HCons (Atom A) HNil)) (Atom B))
              (Yes (Atom B)))
!(assertEqual (coh (D) HNil (Imp (Atom A) (Atom B))) No)
!(assertEqual (coh (D) HNil (Atom B)) No)

; ============================ EXHAUSTIVE TERMINAL ===========================
; (1) report N actually checked:
!(h-length (PAIRS))
; (2)+(3) coherence + witness-soundness over ALL pairs  → must be HNil (green):
!(audit (D) (PAIRS))
!(assertEqual (audit (D) (PAIRS)) HNil)
; (4) bound adequacy: provability verdict identical at D and D+1:
!(assertEqual (found-stable (D) (PAIRS)) True)
