; Prime Motivation 06: a language-indexed structural syntax promotion.
; Dialect: Hyperon Experimental MeTTa.
;
; This is the same ordinary transformer as 06_language_promotion_petta.metta.
; Its explicit None cases are the code that an indexed route removes: the
; source and target languages constrain which structural program can exist.
;
; Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.variables_are_fixed
;   Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel.
;     constructor_translation_is_nontrivial
;   Mettapedia.Languages.MeTTa.Prime.InternalDataTransport.
;     transport_commutes_with_opening
;   Mettapedia.Languages.MeTTa.Prime.LanguageOperationSyntax.
;     no_reverse_gslt_operation_has_syntax

(= (promote (Var $name)) (Some (Var $name)))
(= (promote (ZeroAtom $name)) (Some (PrimeAtom $name)))
(= (promote (ZeroApp $head $argument))
   (promote-app $head (promote $argument)))
(= (promote (Foreign $payload)) None)
(= (promote (PrimeAtom $name)) None)
(= (promote (PrimeApp $head $argument)) None)

(= (promote-app $head None) None)
(= (promote-app $head (Some $argument))
   (Some (PrimeApp $head $argument)))

!(assertEqual (promote (Var x)) (Some (Var x)))
!(assertEqual
  (promote (ZeroApp f (ZeroApp g (ZeroAtom a))))
  (Some (PrimeApp f (PrimeApp g (PrimeAtom a)))))
!(assertEqual (promote (Foreign opaque)) None)
!(assertEqual (promote (PrimeAtom already-prime)) None)
