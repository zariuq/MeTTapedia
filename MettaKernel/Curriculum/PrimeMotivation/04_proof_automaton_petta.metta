; Prime Motivation 04: a finite proof article as an automaton.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: check the shape of a tiny modus-ponens article.  The
; automaton expects a hypothesis A, a hypothesis A-implies-B, an MP step, and
; an end marker.  This is deliberately a recognizer, not a proof kernel.
;
; Prime/NIK payoff: the same control pattern scales to exact rule selection
; and chronological proof-node admission.  Accepted nodes carry their
; invariant as they are constructed; finish checks the selected root and
; target rather than replaying the accumulated article.  A deterministic
; transition table can additionally receive the prepared-selector license.
; Lean anchors:
;   Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation.Builder
;   Mettapedia.GSLT.LanguageDef.ChronologicalArticleCompilation.
;     Builder.finish?_closed_sound
;   Mettapedia.GSLT.LanguageDef.NIKGSLT.Family.
;     acceptance_implies_certified
;   Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation.
;     runCompiled_eq_runSource_of_compile?
;
; The later NIK lesson must replace these symbolic transitions with the guest
; kernel's actual rule evidence; the automaton motivates the architecture.

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

!(test
  (check-article
    (Cons hyp-A
      (Cons hyp-A-implies-B
        (Cons mp (Cons end Nil)))))
  True)

; Negative control: an unfinished article is not accepted.
!(test
  (check-article
    (Cons hyp-A (Cons hyp-A-implies-B (Cons mp Nil))))
  False)
