; Prime Motivation 04: a finite proof article as an automaton.
; Dialect: Hyperon Experimental MeTTa.
;
; The ordinary recognizer exposes the control skeleton shared by finite
; automata and proof schedulers.  Prime/NIK replaces symbolic trust with exact
; guest-rule evidence and can authorize deterministic dispatch once per revision.
;
; Lean anchors:
;   Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation.Builder
;   Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation.
;     Builder.finish?_closed_sound
;   Mettapedia.GSLT.LanguageDef.NIKGSLT.Family.
;     acceptance_implies_certified

(= (proof-step start hyp-A) have-A)
(= (proof-step have-A hyp-A-implies-B) have-implication)
(= (proof-step have-implication mp) have-B)
(= (proof-step have-B end) accepted)

(= (proof-run $state Nil) $state)
(= (proof-run $state (Cons $token $rest))
   (proof-run (proof-step $state $token) $rest))

(= (proof-accepted accepted) True)
(= (proof-accepted start) False)
(= (proof-accepted have-A) False)
(= (proof-accepted have-implication) False)
(= (proof-accepted have-B) False)

(= (check-article $tokens)
   (proof-accepted (proof-run start $tokens)))

!(assertEqual
  (check-article
    (Cons hyp-A
      (Cons hyp-A-implies-B
        (Cons mp (Cons end Nil)))))
  True)

!(assertEqual
  (check-article
    (Cons hyp-A (Cons hyp-A-implies-B (Cons mp Nil))))
  False)
