; =============================================================================
; evaluator_ground_recursion_invariant.metta
;
; ONE canonical evaluator-invariant test for the proof-kernel runtime.
;
; INVARIANT: a ground query that recurses through `let`/bind into the SAME
;   equation head must yield the result the operational semantics mandates —
;   it must NOT be silently dropped.  Here `infer` on a nested `Pi` telescope
;   recursively calls `infer` (under an extended context) on a sub-term that is
;   itself a `Pi`, i.e. recursion under the same head from inside a `let` body.
;
; ORACLE: the expected normal form `(Srt kind)` is exactly what the Lean-verified
;   MOPS engine (LeaTTa) produces, and Hyperon and PeTTa agree.  This test pins
;   that cross-engine result as the standing invariant; any engine that drops it
;   (default CeTTa once returned no result for this shape — a bind-mode bug that
;   preserved internal rule variables for ground queries, since fixed in CeTTa
;   eval.c) regresses against the spec and fails here.
;
; The two checks below guard BOTH failure directions:
;   (1) positive — deep recursive inference must reach `(Srt kind)` (no dropped
;       result / under-generation, the original bug);
;   (2) negative — a malformed domain must still be rejected as `Bad`, so a fix
;       to (1) must not make `infer` spuriously produce results (over-generation).
; =============================================================================

!(import! &self kernel_binding_waist_v1)

; Public capture-avoiding `shift`/`subst` traversal comes from the shared binding
; waist.  This file tests evaluator recursion, not binding traversal.

(= (nf (Var $k)) (Var $k))
(= (nf (Srt $s)) (Srt $s))
(= (nf (Pi $A $B)) (Pi (nf $A) (nf $B)))
(= (nf (Bad $e)) (Bad $e))

(= (ctx-nth $i CtxNil) (Bad var-out-of-range))
(= (ctx-nth $i (CtxCons $h $t)) (if (== $i 0) $h (ctx-nth (- $i 1) $t)))
(= (ctx-type $i $ctx) (shift (+ $i 1) 0 (ctx-nth $i $ctx)))

(= (pts-rule $sA $sB)
   (unify $sA (Srt type)
     (unify $sB (Srt type) (Srt type)
       (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
     (unify $sA (Srt kind)
       (unify $sB (Srt type) (Srt kind)
         (unify $sB (Srt kind) (Srt kind) (Bad pi-bad-codomain)))
       (Bad pi-domain-not-type))))

(= (infer $ctx (Srt type)) (Srt kind))
(= (infer $ctx (Srt kind)) (Bad kind-is-topsort))
(= (infer $ctx (Bad $e)) (Bad $e))
(= (infer $ctx (Var $i)) (ctx-type $i $ctx))

; Direct recursive equation under the SAME head — the shape under test.
(= (infer $ctx (Pi $A $B))
   (let $sA (nf (infer $ctx $A))
     (let $sB (nf (infer (CtxCons $A $ctx) $B))
       (pts-rule $sA $sB))))

(= (id-ty-expanded)
   (Pi (Srt type) (Pi (Var 0) (Pi (Var 1) (Srt type)))))

; (1) positive: deep recursive inference reaches the spec normal form (Srt kind).
!(assertEqual (subst 0 (Con z) (Var 1)) (Var 0))
!(assertEqual (subst 0 (Var 0) (Lam (Srt type) (Var 1))) (Lam (Srt type) (Var 1)))
!(assertEqual (shift 1 0 (Lam (Srt type) (Var 0))) (Lam (Srt type) (Var 0)))
!(assertEqual (shift 1 0 (Lam (Srt type) (Var 1))) (Lam (Srt type) (Var 2)))
!(assertEqual
   (nf (infer CtxNil (id-ty-expanded)))
   (Srt kind))

; (2) negative: a malformed domain (kind, not a type) is still rejected as Bad —
;     the evaluator must discriminate, not blanket-produce a result.
!(assertEqual
   (infer CtxNil (Pi (Srt kind) (Srt type)))
   (Bad pi-domain-not-type))
