; Prime Motivation 01: deterministic finite automaton.
; Dialect: Hyperon Experimental MeTTa.
;
; This is the same ordinary algorithm as 01_dfa_petta.metta.  Prime keeps the
; dialect tag explicit when quoting source, while the prospective optimization
; depends on the checked transition-table shape rather than on a silent parser
; default.
;
; Lean anchors:
;   Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core.modeFits
;   Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation.
;     runCompiled_eq_runSource_of_compile?
;   Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

(= (dfa-step q0 zero) q1)
(= (dfa-step q0 one) q0)
(= (dfa-step q1 zero) q1)
(= (dfa-step q1 one) q2)
(= (dfa-step q2 zero) q1)
(= (dfa-step q2 one) q0)

(= (dfa-run $state Nil) $state)
(= (dfa-run $state (Cons $symbol $rest))
   (dfa-run (dfa-step $state $symbol) $rest))

(= (dfa-accepting q0) False)
(= (dfa-accepting q1) False)
(= (dfa-accepting q2) True)

(= (ends-in-01 $word) (dfa-accepting (dfa-run q0 $word)))

!(assertEqual (dfa-run q0 (Cons one (Cons zero (Cons one Nil)))) q2)
!(assertEqual (ends-in-01 (Cons one (Cons zero (Cons one Nil)))) True)
!(assertEqual (ends-in-01 (Cons zero (Cons one (Cons one Nil)))) False)
!(assertEqual (ends-in-01 Nil) False)
