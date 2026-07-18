; DV-erased proof discovery for ax5d, followed by authentic source replay.
;
; The producer sees ordinary formula constructors and the two source
; assertions needed by this proof.  It does not receive the stored proof term
; or any trusted shortcut for the distinct-variable condition.  The exact term
; returned by search is compiled to source applications; only the imported
; Metamath replay may accept it as a theorem.

!(import! &self pcxp_trace_certification/setmm_prime_quantified_ax5d_v0)

(: Ax5dSearchVariable Type)
(: x Ax5dSearchVariable)
(: impl (-> Type Type Type))
(: all (-> Ax5dSearchVariable Type Type))
(: ph Type)
(: ps Type)

(: ax-5 (impl $formula (all $variable $formula)))
(type-scheme ax-5)

(: a1i (-> $formula (impl $antecedent $formula)))
(chaining-rule a1i)

(= (ax5d:search-goal)
   (impl ph (impl ps (all x ps))))

(= (ax5d:classify-search
      (he-accept
        (typed-answer-v2 (: $term $type) $substitution)))
   (Ax5dSearchFound $term $type))
(= (ax5d:classify-search (he-reject $reason))
   (Ax5dSearchRejected $reason))
(= (ax5d:classify-search (he-unknown $reason))
   (Ax5dSearchIncomplete $reason))

(= (ax5d:search-verdict $name $expected $actual)
   (if (== $expected $actual)
     (PASS $name)
     (FAIL $name $actual)))

; Only the exact proof term has a compiler clause.  The explicit negative is
; disjoint, preserving deterministic behavior under nondeterministic rewriting.
(= (ax5d:compile-search-term (a1i ax-5) $context)
   (Ax5dSearchCompiled (ax5d:certificate $context)))
(= (ax5d:compile-search-term ax-5 $context)
   (Ax5dSearchCompileRejected (unsupported-search-term ax-5)))

(= (ax5d:finish-search-compilation
      (Ax5dSearchCompiled $certificate))
   (mm-replay:check-theorem-certificate
     "ax5d" $certificate (ax5d:reference)))
(= (ax5d:finish-search-compilation
      (Ax5dSearchCompileRejected $reason))
   (MMReplayGoalRejected $reason))

(= (ax5d:finish-search-answer $term $type)
   (if (== $type (impl ph (impl ps (all x ps))))
     (ax5d:finish-search-compilation
       (ax5d:compile-search-term $term (ax5d:context)))
     (MMReplayGoalRejected (search-goal-mismatch $type))))

(= (ax5d:replay-search-answer
      (he-accept
        (typed-answer-v2 (: $term $type) $substitution)))
   (ax5d:finish-search-answer $term $type))
(= (ax5d:replay-search-answer (he-reject $reason))
   (MMReplayGoalRejected (search-rejected $reason)))
(= (ax5d:replay-search-answer (he-unknown $reason))
   (MMReplayGoalRejected (search-incomplete $reason)))

!(ax5d:search-verdict dv-erased-search-finds-ax5d
   (Ax5dSearchFound (a1i ax-5) (ax5d:search-goal))
   (ax5d:classify-search
     (search-first-inhabitant &self
       (impl ph (impl ps (all x ps))) 3 1000000)))

!(ax5d:expect-accepted searched-term-passes-source-dv-replay
   (ax5d:replay-search-answer
     (search-first-inhabitant &self
       (impl ph (impl ps (all x ps))) 3 1000000)))

!(ax5d:expect-rejected mutated-searched-term-cannot-compile
   (ax5d:finish-search-answer ax-5 (ax5d:search-goal)))

!(SetMMPrimeQuantifiedAx5dSearchSummary discovered 1 replayed 1 rejected 1)
