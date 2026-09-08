;; ============================================================
;;  06 · SCHRÖDINGER'S PICNIC
;;  Discriminator: lazy gradual-dependent world branching
;; ============================================================
;;
;;  Question this instrument asks:
;;    A plan's type depends on evidence not yet available (the
;;    weather).  Several elaboration worlds are held open.  As evidence
;;    arrives, what may be pruned, and by whom?  Three laws are tested:
;;
;;    (1) more evidence never invalidates an already-justified COMMON
;;        behavior;
;;    (2) unknown is never treated as false;
;;    (3) pruning happens only when the OBSERVER cannot distinguish
;;        the removed worlds.
;;
;;  Candidate semantics: are these laws native (modal locks, gradual
;;  precision in the type theory) or an elaborator-layer convention?
;;  This file lets you watch the laws operate, so you can decide where
;;  they have to live.
;; ============================================================

;; --- the open worlds ---------------------------------------------------
(= (worlds) (superpose (sunny rainy)))

;; --- behaviors and where they are justified -----------------------------
(= (justified bring-food sunny) True)
(= (justified bring-food rainy) True)
(= (justified umbrella   rainy) True)
(= (justified umbrella   sunny) False)
(= (justified sunscreen  sunny) True)
(= (justified sunscreen  rainy) False)

;; a behavior is COMMON if justified in every open world
(= (common $b $ws) (== (collapse (justified-in $b $ws)) (collapse (all-true $ws))))
(= (justified-in $b $ws) (let $w (superpose $ws) (justified $b $w)))
(= (all-true $ws) (let $w (superpose $ws) True))

;; --- evidence arrives incrementally -------------------------------------
;;  stage 0: nothing known.  stage 1: clouds seen (compatible with both).
;;  stage 2: rain felt (rules out sunny).
(= (open-worlds 0) (sunny rainy))
(= (open-worlds 1) (sunny rainy))        ; clouds do not decide
(= (open-worlds 2) (rainy))

!(println! "--- law (1): common behavior survives every stage ---")
!(println! (stage0 bring-food (common bring-food (open-worlds 0))))
!(println! (stage1 bring-food (common bring-food (open-worlds 1))))
!(println! (stage2 bring-food (common bring-food (open-worlds 2))))
!(println! "--- a NON-common behavior only becomes common when worlds narrow ---")
!(println! (stage0 umbrella (common umbrella (open-worlds 0))))
!(println! (stage2 umbrella (common umbrella (open-worlds 2))))

;; --- law (2): three-valued answers; unknown is not false ----------------
(= (answer $q $ws)
   (let $vals (collapse (let $w (superpose $ws) (justified $q $w)))
     (case $vals
       (((True True) yes)
        ((False False) no)
        ((True) yes)
        ((False) no)
        ($_ unknown)))))

!(println! "--- law (2): is an umbrella justified? (stage 0 / 1 / 2) ---")
!(println! ((answer umbrella (open-worlds 0)) (answer umbrella (open-worlds 1)) (answer umbrella (open-worlds 2))))
!(println! "  (note: stage 0 says unknown, never no)")

;; --- law (3): pruning is observer-relative ---------------------------
;;  An observer is a list of behaviors it cares about.  Two worlds are
;;  indistinguishable for an observer iff every cared-for behavior has
;;  the same justification in both.
(= (view $obs $w) (collapse (let $b (superpose $obs) (justified $b $w))))
(= (indistinguishable $obs $w1 $w2) (== (view $obs $w1) (view $obs $w2)))
(= (may-prune-for $obs)
   (if (indistinguishable $obs sunny rainy)
       (PRUNE-ALLOWED keep-one-representative)
       (PRUNE-FORBIDDEN worlds-differ-for-this-observer)))

!(println! "--- law (3): may the elaborator prune sunny/rainy to one world? ---")
!(println! (caterer     (may-prune-for (bring-food))))
!(println! (picnic-goer (may-prune-for (bring-food umbrella sunscreen))))

;; Reading: the three laws held without any special construct: worlds
;; were a superposition, evidence was a filter, observers were lists.
;; Prime's choice: keep this an elaborator convention (cheap, but
;; nothing stops a rule from treating unknown as false), or make the
;; observer index and the monotone-evidence lock part of the type
;; discipline (costlier, but law (2) becomes unviolable by construction).
