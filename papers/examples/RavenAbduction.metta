;; RavenAbduction.metta — abduction as "hypothesize the best explanation of the data"
;; ----------------------------------------------------------------------------
;; Runnable on Hyperon Experimental:   metta RavenAbduction.metta
;; (also runs under PeTTa; the NARS truth functions below mirror
;;  hyperon/PeTTa/lib/lib_nars.metta exactly.)
;;
;; Companion to RavenAsymmetricInduction.{lean,metta}.  Induction *learns* the
;; conditionals; abduction *uses* them to hypothesize which species explains an
;; observed bird.  Key point — base-rate dilution:
;;   * one common feature ("black") under-determines the explanation;
;;   * a discriminating feature ("croaks") decides it.
;;
;; KB ("which bird is this?"), rules cause --> effect with (stv freq conf):
;;   Raven --> Black  (0.99, 0.9)     Raven --> Croaks (0.90, 0.9)
;;   Crow  --> Black  (0.95, 0.9)     Crow  --> Caws   (0.90, 0.9)   [Crow croaks: 0.01]
;; base rates among birds (priors):  P(Crow) = 0.10,  P(Raven) = 0.02
;; ----------------------------------------------------------------------------

;; ====================================================================
;; Part 1 — the ATOMIC NARS abduction rule  (from lib_nars.metta)
;;   {a --> c, b --> c}  |-  b --> a       (NARS abduction, shared predicate c)
;;   conclusion frequency = f(b-->c); confidence = w2c(f1*c1*c2)  (low)
;; ====================================================================
(= (Truth_w2c $w) (/ $w (+ $w 1.0)))
(= (Truth_Abduction (stv $f1 $c1) (stv $f2 $c2))
   (stv $f2 (Truth_w2c (* (* $f1 $c1) $c2))))

;; observe "thisBird --> Black (1.0, 0.9)" and abduce the species:
!(Truth_Abduction (stv 0.99 0.9) (stv 1.0 0.9))   ; thisBird --> Raven
!(Truth_Abduction (stv 0.95 0.9) (stv 1.0 0.9))   ; thisBird --> Crow
;; -> both return frequency 1.0 with similar moderate confidence: the atomic
;;    rule GENERATES the hypothesis but does NOT rank by base rate.  Ranking
;;    competing explanations needs the prior (Part 2).

;; ====================================================================
;; Part 2 — BEST EXPLANATION = posterior  (prior x likelihood)
;;   score(h | features) = prior(h) * product_i likelihood(feature_i | h)
;;   normalization cancels in comparisons; bigger score = better explanation.
;; ====================================================================
(= (score-black $prior $likeBlack) (* $prior $likeBlack))
(= (score-black-croak $prior $likeBlack $likeCroak) (* (* $prior $likeBlack) $likeCroak))

;; Stage 1 — data: "black" only.
!(score-black 0.02 0.99)   ; Raven -> 0.0198
!(score-black 0.10 0.95)   ; Crow  -> 0.095    => Crow wins (base-rate dilution)

;; Stage 2 — data: "black" AND "croaks".   P(Croak|Raven)=0.9, P(Croak|Crow)=0.01
!(score-black-croak 0.02 0.99 0.9)    ; Raven -> 0.01782
!(score-black-croak 0.10 0.95 0.01)   ; Crow  -> 0.00095  => Raven wins (discriminating feature)
