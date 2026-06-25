; =============================================================================
; mettarho_opcorr_shadow_v1.metta
;
; MeTTa2rho OPERATIONAL-CORRESPONDENCE SHADOW v1 — a bounded operational shadow of
; knotted-topoi's Prop/Obligation `ob:opcorr`: the desugaring of a GSLT into core
; rho has a transition system bisimilar to the GSLT's rewrite system, with each
; rewrite at location l firing as a rendezvous on the location channel c(l)=quote(l).
; Lifts the conv/~/<> shadows off hand-given LTSs onto a REAL language definition.
;
; GENUINE GSLT (not a toy process): Peano addition as a 2-rule term-rewriting
; system --   A(Z,y)      => y            (add-z)
;             A(S x, y)   => S(A(x,y))    (add-s)
; This has NESTED redexes at DISTINCT locations (A(S z, A(z,z)) has a head redex
; AND an inner redex), so the location-channel discipline c(l)=quote(l) and its
; INJECTIVITY (knotted-topoi rem. "freshness by quoting") are load-bearing.
;
; HONEST SCOPE (v1 seed, no overclaim -- the ocoherence wording lesson):
;   * `rw` is the GSLT rewrite LTS (term side), located, the INDEPENDENT REFERENCE.
;   * `dsg` desugars a term to a rho process modelled as a location-channel-
;     ANNOTATED tree (each node carries c(l); this is the part of the desugaring
;     `ob:opcorr` actually rests on: the channel assignment, knotted-topoi App+App.A).
;   * `dfire` is the rho-side ∂T-transition: it reads the channel OFF the annotation
;     and finds redexes on the desugared structure -- it never calls `rw` or `chan`,
;     so the correspondence is NOT tautological; a wrong/colliding channel breaks it.
;   * `opc-corr t` = the two transition systems agree (FORWARD+BACKWARD via list eq);
;     `opc-injective` = the desugared channels are pairwise distinct (no two redexes
;     collapse -- the a|a vs a failure); `opc-bisim` = bounded bisimulation.
;   The full persistent-receive rendezvous EXECUTION in rho is the scaling step
;   (Codex's RhoCompiler/rhometta + the extended rho profile); v1 is the bounded,
;   channel-level correspondence.  run_mettarho_opcorr_gate.sh injects desugaring
;   breaks (channel collision; wrong location; dropped re-emit) and confirms red.
; =============================================================================

; ---------- list utility (transitions Tx; redexes Rx; channels Cx) ------------
(= (rapp RNil $ys) $ys)
(= (rapp (RCons $x $xs) $ys) (RCons $x (rapp $xs $ys)))
(= (tapp TNil $ys) $ys)
(= (tapp (TCons $x $xs) $ys) (TCons $x (tapp $xs $ys)))

; ---------- location paths (root PNil, append a step at the end) --------------
(= (psnoc PNil $s) (PStep $s PNil))
(= (psnoc (PStep $h $t) $s) (PStep $h (psnoc $t $s)))

; ---------- GSLT rewrite LTS (TERM side -- the independent reference) ----------
; rw t -> list of (RW loc t') ; loc = path to the redex, t' = the WHOLE term rewritten
(= (rw $t) (rw-at PNil $t))
(= (rw-at $loc Z) RNil)
(= (rw-at $loc (S $x)) (wrapS (rw-at (psnoc $loc S1) $x)))
(= (rw-at $loc (A $x $y))
   (rapp (hredex $loc (A $x $y))
     (rapp (wrapA1 $y (rw-at (psnoc $loc A1) $x))
           (wrapA2 $x (rw-at (psnoc $loc A2) $y)))))
; head redex of an A-node (non-overlapping on the first argument Z / S / A)
(= (hredex $loc (A Z $y)) (RCons (RW $loc $y) RNil))                          ; add(z,y) => y
(= (hredex $loc (A (S $x) $y)) (RCons (RW $loc (S (A $x $y))) RNil))          ; add(s x,y) => s(add x y)
(= (hredex $loc (A (A $a $b) $y)) RNil)                                       ; first arg unreduced: no head redex
; wrap child redex results back into the parent term
(= (wrapS RNil) RNil)
(= (wrapS (RCons (RW $l $r) $rest)) (RCons (RW $l (S $r)) (wrapS $rest)))
(= (wrapA1 $y RNil) RNil)
(= (wrapA1 $y (RCons (RW $l $r) $rest)) (RCons (RW $l (A $r $y)) (wrapA1 $y $rest)))
(= (wrapA2 $x RNil) RNil)
(= (wrapA2 $x (RCons (RW $l $r) $rest)) (RCons (RW $l (A $x $r)) (wrapA2 $x $rest)))

; ---------- the desugaring: location-channel annotation (rho side) ------------
(= (chan $loc) (Chan $loc))                       ; c(l) = quote(l), injective
(= (dsg $t) (dsg-at PNil $t))
(= (dsg-at $loc Z) (DZ (chan $loc)))
(= (dsg-at $loc (S $x)) (DS (chan $loc) (dsg-at (psnoc $loc S1) $x)))
(= (dsg-at $loc (A $x $y)) (DA (chan $loc) (dsg-at (psnoc $loc A1) $x) (dsg-at (psnoc $loc A2) $y)))
(= (undsg (DZ $c)) Z)
(= (undsg (DS $c $d)) (S (undsg $d)))
(= (undsg (DA $c $d1 $d2)) (A (undsg $d1) (undsg $d2)))

; ---------- rho-side ∂T-transitions: read the channel OFF the annotation -------
; dfire d -> list of (Tr c t') ; c is the DESUGARED channel at the redex node,
;            t' the resulting TERM.  Never calls rw or chan -- genuinely the rho side.
(= (dfire (DZ $c)) TNil)
(= (dfire (DS $c $d)) (twrapS (dfire $d)))
(= (dfire (DA $c $d1 $d2))
   (tapp (dhead (DA $c $d1 $d2))
     (tapp (twrapA1 (undsg $d2) (dfire $d1))
           (twrapA2 (undsg $d1) (dfire $d2)))))
(= (dhead (DA $c (DZ $cz) $dy)) (TCons (Tr $c (undsg $dy)) TNil))                       ; add(z,y) => y, on channel $c
(= (dhead (DA $c (DS $cs $dx) $dy)) (TCons (Tr $c (S (A (undsg $dx) (undsg $dy)))) TNil)); add(s x,y) => s(add x y)
(= (dhead (DA $c (DA $ca $da $db) $dy)) TNil)
(= (twrapS TNil) TNil)
(= (twrapS (TCons (Tr $c $r) $rest)) (TCons (Tr $c (S $r)) (twrapS $rest)))
(= (twrapA1 $y TNil) TNil)
(= (twrapA1 $y (TCons (Tr $c $r) $rest)) (TCons (Tr $c (A $r $y)) (twrapA1 $y $rest)))
(= (twrapA2 $x TNil) TNil)
(= (twrapA2 $x (TCons (Tr $c $r) $rest)) (TCons (Tr $c (A $x $r)) (twrapA2 $x $rest)))

; ---------- the correspondence (compare rho side to the term-side reference) ---
(= (rmap-chan RNil) TNil)
(= (rmap-chan (RCons (RW $l $r) $rest)) (TCons (Tr (chan $l) $r) (rmap-chan $rest)))
(= (opc-corr $t) (== (dfire (dsg $t)) (rmap-chan (rw $t))))     ; FORWARD+BACKWARD via list equality

; channel-injectivity of the desugared transitions (the load-bearing teeth)
(= (chans-of TNil) KNil)
(= (chans-of (TCons (Tr $c $r) $rest)) (KCons $c (chans-of $rest)))
(= (mem-c $c KNil) False)
(= (mem-c $c (KCons $d $rest)) (if (== $c $d) True (mem-c $c $rest)))
(= (all-distinct KNil) True)
(= (all-distinct (KCons $c $rest)) (if (mem-c $c $rest) False (all-distinct $rest)))
(= (opc-injective $trs) (all-distinct (chans-of $trs)))

; bounded bisimulation of the two transition systems over reachable terms
(= (opc-bisim $n $t)
   (if (== $n 0) True (if (opc-corr $t) (bisim-kids $n (rw $t)) False)))
(= (bisim-kids $n RNil) True)
(= (bisim-kids $n (RCons (RW $l $t') $rest))
   (if (opc-bisim (- $n 1) $t') (bisim-kids $n $rest) False))

; ---------- a deliberately WRONG desugaring (constant channel) for negatives ---
(= (dsg-bad $t) (dsg-bad-go $t))
(= (dsg-bad-go Z) (DZ (Chan collide)))
(= (dsg-bad-go (S $x)) (DS (Chan collide) (dsg-bad-go $x)))
(= (dsg-bad-go (A $x $y)) (DA (Chan collide) (dsg-bad-go $x) (dsg-bad-go $y)))

; ---------- example terms -----------------------------------------------------
(= (t-one)   (A Z (S Z)))                          ; add(z, s z)            -- 1 redex
(= (t-two)   (A (S Z) (A Z Z)))                    ; add(s z, add(z,z))     -- 2 redexes, distinct locations
(= (t-multi) (A (S (S Z)) (S Z)))                  ; add(s s z, s z)        -- reduces over several steps
(= (step1-multi) (S (A (S Z) (S Z))))
(= (step2-multi) (S (S (A Z (S Z)))))
(= (nf-multi)    (S (S (S Z))))

; =============================================================================
; (i) FORWARD + BACKWARD: the desugared ∂T-transitions correspond exactly to the
;     GSLT rewrites, each on its location channel c(l)=quote(l).
; =============================================================================
!(assertEqual (opc-corr (t-one)) True)
!(assertEqual (opc-corr (t-two)) True)
!(assertEqual (opc-corr (t-multi)) True)
; the explicit single-step witness: add(z, s z) fires on c(root) to (s z)
!(assertEqual (dfire (dsg (t-one))) (TCons (Tr (Chan PNil) (S Z)) TNil))
; the two-redex witness: head on c(root), inner on c(root.A2), distinct channels + results
!(assertEqual (dfire (dsg (t-two)))
   (TCons (Tr (Chan PNil) (S (A Z (A Z Z))))
     (TCons (Tr (Chan (PStep A2 PNil)) (A (S Z) Z)) TNil)))

; =============================================================================
; (ii) INJECTIVITY (the teeth): distinct redex locations get distinct channels;
;      a collapsing desugaring is detected.
; =============================================================================
!(assertEqual (opc-injective (dfire (dsg (t-two)))) True)             ; distinct channels
!(assertEqual (opc-injective (dfire (dsg-bad (t-two)))) False)        ; collapsed channels -> caught
; and the wrong (collapsing) desugaring does NOT correspond to the GSLT rewrites
!(assertEqual (== (dfire (dsg-bad (t-two))) (rmap-chan (rw (t-two)))) False)
!(assertEqual (== (dfire (dsg-bad (t-one))) (rmap-chan (rw (t-one)))) False)

; =============================================================================
; (iii) BOUNDED BISIMULATION over reachable terms (the two LTSs agree all the way
;       down to normal form).
; =============================================================================
!(assertEqual (opc-bisim 8 (t-one)) True)
!(assertEqual (opc-bisim 8 (t-two)) True)
!(assertEqual (opc-bisim 8 (t-multi)) True)
; sanity: the GSLT actually computes -- add(s s z, s z) normalises.
!(assertEqual (rw (A (S (S Z)) (S Z)))
   (RCons (RW PNil (S (A (S Z) (S Z)))) RNil))
!(assertEqual (rw (step1-multi))
   (RCons (RW (PStep S1 PNil) (step2-multi)) RNil))
!(assertEqual (rw (step2-multi))
   (RCons (RW (PStep S1 (PStep S1 PNil)) (nf-multi)) RNil))
!(assertEqual (rw (nf-multi)) RNil)
!(assertEqual (opc-corr (step1-multi)) True)
!(assertEqual (opc-corr (step2-multi)) True)
!(assertEqual (opc-corr (nf-multi)) True)
