; Prime Motivation 01: deterministic finite automaton.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: recognize binary words ending in 01.  Each transition is
; written as a separate MeTTa equation, and dfa-run recursively dispatches
; over the current state and next symbol.
;
; Current friction: the source text alone does not certify that dfa-step is
; total and single-valued.  A general evaluator must retain the possibility of
; no answer or several answers even though this table is a function.
;
; Prime payoff: infer or check a deterministic grade for
;   delta : State -> Symbol -> State
; and authorize an exact prepared selector once.  The evaluator may then select
; one transition directly without changing the result.  Lean anchors:
;   Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core.modeFits
;   Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation.
;     runCompiled_eq_runSource_of_compile?
;   Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation.
;     runAdmittedOrSource_eq_instantiate_of_compileEquation?
;
; The optimization is shape-licensed: overlapping or missing transitions must
; fail admission and continue through ordinary MeTTa evaluation.

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

!(test (dfa-run q0 (Cons one (Cons zero (Cons one Nil)))) q2)
!(test (ends-in-01 (Cons one (Cons zero (Cons one Nil)))) True)
!(test (ends-in-01 (Cons zero (Cons one (Cons one Nil)))) False)
!(test (ends-in-01 Nil) False)
