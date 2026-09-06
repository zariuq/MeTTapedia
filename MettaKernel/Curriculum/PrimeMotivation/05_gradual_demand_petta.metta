; Prime Motivation 05: validate only when the operation demands evidence.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: preview accepts a payload without validating it; commit
; explicitly compares the payload against the expected shape.  This manual
; mode split preserves the useful untyped path, but it does not package a
; suspended check, cache its result, or retain structured blame.
;
; Prime payoff: CheckedPlan carries the pending obligation separately from
; raw execution.  No demand contributes no checking work; the first demand
; contributes one unit and caches evidence or blame; later observations reuse
; the cache.  Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.NativeCanary.
;     rejected_check_does_not_gate_raw_execution
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.
;     executionWorkSpanWithDemand_ne_withoutDemand
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.
;     cachedValue_zero_work_one_observation
;
; Thus laziness is useful here as a semantic boundary: evidence is demanded
; by commit, not speculatively computed merely because a checker exists.

(= (bit-list-eq Nil Nil) True)
(= (bit-list-eq Nil (Cons $right $rights)) False)
(= (bit-list-eq (Cons $left $lefts) Nil) False)
(= (bit-list-eq (Cons zero $lefts) (Cons zero $rights))
   (bit-list-eq $lefts $rights))
(= (bit-list-eq (Cons one $lefts) (Cons one $rights))
   (bit-list-eq $lefts $rights))
(= (bit-list-eq (Cons zero $lefts) (Cons one $rights)) False)
(= (bit-list-eq (Cons one $lefts) (Cons zero $rights)) False)

(= (finish-commit True $payload) (Committed $payload))
(= (finish-commit False $payload) Rejected)

(= (use-payload preview $payload $expected) (Preview $payload))
(= (use-payload commit $payload $expected)
   (finish-commit (bit-list-eq $payload $expected) $payload))

!(test
  (use-payload preview (Cons zero Nil) (Cons one Nil))
  (Preview (Cons zero Nil)))
!(test
  (use-payload commit (Cons zero (Cons one Nil))
                      (Cons zero (Cons one Nil)))
  (Committed (Cons zero (Cons one Nil))))
!(test
  (use-payload commit (Cons zero Nil) (Cons one Nil))
  Rejected)
