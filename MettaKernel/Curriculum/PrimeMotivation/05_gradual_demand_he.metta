; Prime Motivation 05: validate only when the operation demands evidence.
; Dialect: Hyperon Experimental MeTTa.
;
; This is the same ordinary algorithm as 05_gradual_demand_petta.metta.
; Preview deliberately does not inspect the expected shape.  Prime turns that
; convention into a source-preserving CheckedPlan with a suspended, cached
; check and theorem-backed demand cost.
;
; Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.
;     demandCheck_evaluationCount
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.
;     demandWorkSpan_eq_unit
;   Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan.CheckedPlan.
;     cachedValue_zero_work_one_observation

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

!(assertEqual
  (use-payload preview (Cons zero Nil) (Cons one Nil))
  (Preview (Cons zero Nil)))
!(assertEqual
  (use-payload commit (Cons zero (Cons one Nil))
                      (Cons zero (Cons one Nil)))
  (Committed (Cons zero (Cons one Nil))))
!(assertEqual
  (use-payload commit (Cons zero Nil) (Cons one Nil))
  Rejected)
