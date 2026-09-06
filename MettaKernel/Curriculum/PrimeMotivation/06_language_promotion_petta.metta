; Prime Motivation 06: a language-indexed structural syntax promotion.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: promote a small Zero-flavoured syntax tree into a
; Prime-flavoured tree.  Variables are fixed, constructors are changed, and
; unsupported or already-Prime inputs are rejected by explicit equations.
; Nothing in untyped MeTTa prevents calling this transformer in the wrong
; direction, so every such case needs a defensive branch.
;
; Prime/MTT payoff: the route has source and target language indices.  Binder-
; safe structural transport is proved once, and the nonexistent Prime-to-Zero
; route is uninhabited rather than represented by another runtime case.  Lean
; anchors:
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

!(test (promote (Var x)) (Some (Var x)))
!(test
  (promote (ZeroApp f (ZeroApp g (ZeroAtom a))))
  (Some (PrimeApp f (PrimeApp g (PrimeAtom a)))))
!(test (promote (Foreign opaque)) None)
!(test (promote (PrimeAtom already-prime)) None)
