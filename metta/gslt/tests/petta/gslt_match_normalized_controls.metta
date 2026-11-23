(= (normalized:check $label $value $expected) (println! ($label (== $value $expected))))

!(normalized:check normalized-prefix
  (gslt:normalized:strip-prefix (LCons 1 LNil) (LCons 1 (LCons 0 LNil)))
  (Some (LCons 0 LNil)))
!(normalized:check normalized-wrong-prefix
  (gslt:normalized:strip-prefix (LCons 1 LNil) (LCons 2 (LCons 0 LNil))) None)
!(normalized:check normalized-long-prefix
  (gslt:normalized:strip-prefix (LCons 1 (LCons 0 LNil)) (LCons 1 LNil)) None)
!(normalized:check normalized-index
  (gslt:normalized:at (LCons a (LCons b LNil)) 1) (Some b))
!(normalized:check normalized-invalid-index
  (gslt:normalized:at (LCons a LNil) 2) None)

!(normalized:check normalized-duplicate-occurrences
  (gslt:normalized:derive
    (MNormal (LCons (LCons (Observe (LCons 0 LNil) (MKey A 0)) LNil) LNil)
      (LCons (MInstance (LCons 1 LNil) (At LNil 0) 0)
        (LCons (MInstance (LCons 1 LNil) (At LNil 1) 0) LNil)))
    (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)))
  (MFinished (LCons (MGoal (At (LCons 1 LNil) 0) LNil)
    (LCons (MGoal (At (LCons 1 LNil) 1) LNil) LNil)) 1))

!(normalized:check normalized-displaced-activations
  (gslt:normalized:derive
    (MNormal (LCons (LCons (Observe (LCons 0 LNil) (MKey A 0)) LNil) LNil)
      (LCons (MInstance (LCons 1 LNil) (At LNil 0) 0)
        (LCons (MInstance (LCons 2 LNil) (At LNil 1) 0) LNil)))
    (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)))
  (MFinished (LCons (MGoal (At (LCons 1 LNil) 0) LNil)
    (LCons (MGoal (At (LCons 2 LNil) 1)
      (LCons (Observe (LCons 2 (LCons 0 LNil)) (MKey A 0)) LNil)) LNil)) 2))

!(normalized:check normalized-conflicting-key
  (gslt:normalized:derive
    (MNormal (LCons (LCons (Observe LNil (MKey A 0)) LNil) LNil)
      (LCons (MInstance LNil (At LNil 0) 0) LNil))
    (Observe LNil (MKey B 0)))
  (MFinished LNil 1))

!(normalized:check normalized-invalid-control
  (gslt:normalized:derive
    (MNormal LNil (LCons (MInstance LNil (At LNil 0) 4) LNil))
    (Observe LNil (MKey A 0)))
  (MFinished LNil 1))

!(normalized:check normalized-empty-control
  (gslt:normalized:derive
    (MNormal (LCons LNil LNil)
      (LCons (MInstance (LCons 2 LNil) (At (LCons 3 LNil) 7) 0) LNil))
    (Observe LNil (MKey A 0)))
  (MFinished (LCons (MGoal (At (LCons 2 (LCons 3 LNil)) 7) LNil) LNil) 1))

!(normalized:check normalized-common-prefix
  (gslt:normalized:common-prefix (LCons 1 (LCons 0 LNil)) (LCons 1 (LCons 2 LNil)))
  (LCons 1 LNil))
!(normalized:check normalized-common-prefix-mismatch
  (gslt:normalized:common-prefix (LCons 1 LNil) (LCons 2 LNil)) LNil)
!(normalized:check normalized-overlap-ignores-key
  (gslt:normalized:overlaps
    (MGoal (At LNil 0) (LCons (Observe (LCons 1 LNil) (MKey A 0)) LNil))
    (MGoal (At LNil 1) (LCons (Observe (LCons 1 LNil) (MKey B 0)) LNil))) True)
!(normalized:check normalized-disjoint-positions
  (gslt:normalized:overlaps
    (MGoal (At LNil 0) (LCons (Observe (LCons 1 LNil) (MKey A 0)) LNil))
    (MGoal (At LNil 1) (LCons (Observe (LCons 2 LNil) (MKey A 0)) LNil))) False)

!(normalized:check normalized-intern-ordered-origins
  (gslt:normalized:normalize
    (LCons (MGoal (At (LCons 1 LNil) 0)
      (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil))
      (LCons (MGoal (At (LCons 2 LNil) 0)
        (LCons (Observe (LCons 2 (LCons 0 LNil)) (MKey A 0)) LNil))
        (LCons (MGoal (At (LCons 1 LNil) 1)
          (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil)) LNil))))
  (MNormal (LCons (LCons (Observe (LCons 0 LNil) (MKey A 0)) LNil) LNil)
    (LCons (MInstance (LCons 1 LNil) (At LNil 0) 0)
      (LCons (MInstance (LCons 2 LNil) (At LNil 0) 0)
        (LCons (MInstance (LCons 1 LNil) (At LNil 1) 0) LNil)))))

!(let $normal
    (gslt:normalized:normalize
      (LCons (MGoal (At (LCons 1 LNil) 0)
        (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil))
        (LCons (MGoal (At (LCons 1 LNil) 1)
          (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil)) LNil)))
  (normalized:check normalized-expanded-roundtrip (gslt:normalized:expand $normal)
    (LCons (MGoal (At (LCons 1 LNil) 0)
    (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil))
    (LCons (MGoal (At (LCons 1 LNil) 1)
      (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0)) LNil)) LNil))))

!(normalized:check normalized-wrong-cache-offset
  (gslt:normalized:lookup (MActivation 0 (LCons 2 LNil))
    (LCons (MCache (MActivation 0 (LCons 1 LNil)) (Some LNil)) LNil)) None)

!(normalized:check normalized-full-run-duplicates
  (gslt:normalized:top
    (LCons (PApp f (LCons (FVar x) LNil))
      (LCons (PApp f (LCons (FVar x) LNil)) LNil))
    (PApp f (LCons (PApp a LNil) LNil)))
  (MatchRun (LCons (Found LNil 0 (LCons (Binding x (PApp a LNil)) LNil))
    (LCons (Found LNil 1 (LCons (Binding x (PApp a LNil)) LNil)) LNil)) 2 4))

!(normalized:check normalized-full-run-nonlinear-refusal
  (gslt:normalized:top
    (LCons (PApp f (LCons (FVar x) (LCons (FVar x) LNil))) LNil)
    (PApp f (LCons (PApp a LNil) (LCons (PApp b LNil) LNil))))
  (MatchRun LNil 3 8))

!(normalized:check normalized-canonical-wire-duplicates
  (gslt:normalized:top
    (LCons (PApp "f" (LCons (FVar "x") LNil))
      (LCons (PApp "f" (LCons (FVar "x") LNil)) LNil))
    (PApp "f" (LCons (PApp "a" LNil) LNil)))
  (MatchRun (LCons (Found LNil 0 (LCons (Binding "x" (PApp "a" LNil)) LNil))
    (LCons (Found LNil 1 (LCons (Binding "x" (PApp "a" LNil)) LNil)) LNil)) 2 4))

!(normalized:check normalized-canonical-wire-nonlinear-refusal
  (gslt:normalized:top
    (LCons (PApp "f" (LCons (FVar "x") (LCons (FVar "x") LNil))) LNil)
    (PApp "f" (LCons (PApp "a" LNil) (LCons (PApp "b" LNil) LNil))))
  (MatchRun LNil 3 8))

!(let $normal
    (gslt:normalized:normalize
      (LCons (MGoal (At (LCons 1 LNil) 0)
        (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0))
          (LCons (Observe (LCons 1 (LCons 1 LNil)) (MKey B 0)) LNil)))
        (LCons (MGoal (At (LCons 2 LNil) 0)
          (LCons (Observe (LCons 2 (LCons 0 LNil)) (MKey A 0))
            (LCons (Observe (LCons 2 (LCons 1 LNil)) (MKey B 0)) LNil)))
          (LCons (MGoal (At (LCons 1 LNil) 1)
            (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0))
              (LCons (Observe (LCons 1 (LCons 1 LNil)) (MKey B 0)) LNil))) LNil))))
  (normalized:check normalized-counted-interleaved-execution
    (gslt:normalized:execute
      (LCons (Observe (LCons 1 (LCons 0 LNil)) (MKey A 0))
        (LCons (Observe (LCons 1 (LCons 1 LNil)) (MKey B 0))
          (LCons (Observe (LCons 2 (LCons 0 LNil)) (MKey A 0))
            (LCons (Observe (LCons 2 (LCons 1 LNil)) (MKey B 0)) LNil)))) $normal)
    (MExecuted (MNormal (LCons LNil LNil)
      (LCons (MInstance (LCons 1 LNil) (At LNil 0) 0)
        (LCons (MInstance (LCons 2 LNil) (At LNil 0) 0)
          (LCons (MInstance (LCons 1 LNil) (At LNil 1) 0) LNil)))) 8)))

; The existing canonical guarded-row controls run through the normalized entry.
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-missing-guard" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) LNil (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-missing-guard" (== $actual (quote LNil)))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-duplicate-guard-witnesses" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ignored" LNil) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ready" LNil) LNil)))) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-duplicate-guard-witnesses" (== $actual (quote (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) LNil))))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-ordered-dependent-branches" LNil LNil LNil (LCons (RewriteRule "chain" LNil (LCons (RelationQuery "first" (LCons (FVar "x") LNil)) (LCons (RelationQuery "next" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil)) (PApp "start" LNil) (PApp "out" (LCons (FVar "y") LNil))) LNil)) (LCons (ProviderRow "first" (LCons (PApp "b" LNil) LNil)) (LCons (ProviderRow "first" (LCons (PApp "a" LNil) LNil)) (LCons (ProviderRow "next" (LCons (PApp "a" LNil) (LCons (PApp "c" LNil) LNil))) (LCons (ProviderRow "next" (LCons (PApp "b" LNil) (LCons (PApp "d" LNil) LNil))) (LCons (ProviderRow "next" (LCons (PApp "b" LNil) (LCons (PApp "d" LNil) LNil))) LNil))))) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-ordered-dependent-branches" (== $actual (quote (LCons (PApp "out" (LCons (PApp "d" LNil) LNil)) (LCons (PApp "out" (LCons (PApp "d" LNil) LNil)) (LCons (PApp "out" (LCons (PApp "c" LNil) LNil)) LNil))))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-failed-suffix-removes-branches" LNil LNil LNil (LCons (RewriteRule "suffix" LNil (LCons (RelationQuery "ready" LNil) (LCons (RelationQuery "missing" LNil) LNil)) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ready" LNil) LNil)) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-failed-suffix-removes-branches" (== $actual (quote LNil)))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-repeated-query-variable-conflict" LNil LNil LNil (LCons (RewriteRule "same" LNil (LCons (RelationQuery "pair" (LCons (FVar "x") (LCons (FVar "x") LNil))) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "pair" (LCons (PApp "a" LNil) (LCons (PApp "b" LNil) LNil))) LNil) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-repeated-query-variable-conflict" (== $actual (quote LNil)))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-opaque-prebound-variable" LNil LNil LNil (LCons (RewriteRule "literal" LNil (LCons (RelationQuery "payload" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil) (PApp "wrap" (LCons (FVar "x") LNil)) (FVar "y")) LNil)) (LCons (ProviderRow "payload" (LCons (FVar "inside") (LCons (PApp "kept" LNil) LNil))) (LCons (ProviderRow "payload" (LCons (PApp "inside" LNil) (LCons (PApp "discarded" LNil) LNil))) LNil)) (PApp "wrap" (LCons (FVar "inside") LNil)))
  (println! (NormalizedDispatchControl "top-conditional-opaque-prebound-variable" (== $actual (quote (LCons (PApp "kept" LNil) LNil))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-two-equal-builtin-witnesses" LNil LNil LNil (LCons (RewriteRule "equal" LNil (LCons (RelationQuery "eq" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil) (PApp "pair" (LCons (FVar "x") (LCons (FVar "y") LNil))) (PApp "done" LNil)) LNil)) LNil (PApp "pair" (LCons (PApp "a" LNil) (LCons (PApp "a" LNil) LNil))))
  (println! (NormalizedDispatchControl "top-conditional-two-equal-builtin-witnesses" (== $actual (quote (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) LNil)))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-builtins-before-provider-witness" LNil LNil LNil (LCons (RewriteRule "witness" LNil (LCons (RelationQuery "eq" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil) (PApp "start" LNil) (PApp "out" (LCons (FVar "x") (LCons (FVar "y") LNil)))) LNil)) (LCons (ProviderRow "eq" (LCons (PApp "p" LNil) (LCons (PApp "q" LNil) LNil))) LNil) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-builtins-before-provider-witness" (== $actual (quote (LCons (PApp "out" (LCons (FVar "x") (LCons (FVar "x") LNil))) (LCons (PApp "out" (LCons (FVar "y") (LCons (FVar "y") LNil))) (LCons (PApp "out" (LCons (PApp "p" LNil) (LCons (PApp "q" LNil) LNil))) LNil))))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-duplicate-rules-times-guard-witnesses" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil))) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ready" LNil) LNil)) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-duplicate-rules-times-guard-witnesses" (== $actual (quote (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) (LCons (PApp "done" LNil) LNil)))))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-provider-arity-refusal" LNil LNil LNil (LCons (RewriteRule "arity" LNil (LCons (RelationQuery "one" (LCons (FVar "x") LNil)) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "one" LNil) (LCons (ProviderRow "one" (LCons (PApp "a" LNil) (LCons (PApp "b" LNil) LNil))) LNil)) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-provider-arity-refusal" (== $actual (quote LNil)))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-child-match-grants-no-permission" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "ready" LNil) LNil) (PApp "wrap" (LCons (PApp "start" LNil) LNil)))
  (println! (NormalizedDispatchControl "top-conditional-child-match-grants-no-permission" (== $actual (quote LNil)))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-premise-free-parity" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "start" LNil) (PApp "a" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "start" LNil) (PApp "b" LNil)) LNil))) (LCons (ProviderRow "irrelevant" (LCons (PApp "anything" LNil) LNil)) LNil) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "top-conditional-premise-free-parity" (== $actual (quote (LCons (PApp "a" LNil) (LCons (PApp "b" LNil) LNil)))))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-duplicate-guard-witnesses" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ignored" LNil) (LCons (ProviderRow "ready" LNil) (LCons (ProviderRow "ready" LNil) LNil)))) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "refuse-top-matched-observation-0" (== (== $actual (quote (LCons (PApp "done" LNil) LNil))) False))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-ordered-dependent-branches" LNil LNil LNil (LCons (RewriteRule "chain" LNil (LCons (RelationQuery "first" (LCons (FVar "x") LNil)) (LCons (RelationQuery "next" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil)) (PApp "start" LNil) (PApp "out" (LCons (FVar "y") LNil))) LNil)) (LCons (ProviderRow "first" (LCons (PApp "b" LNil) LNil)) (LCons (ProviderRow "first" (LCons (PApp "a" LNil) LNil)) (LCons (ProviderRow "next" (LCons (PApp "a" LNil) (LCons (PApp "c" LNil) LNil))) (LCons (ProviderRow "next" (LCons (PApp "b" LNil) (LCons (PApp "d" LNil) LNil))) (LCons (ProviderRow "next" (LCons (PApp "b" LNil) (LCons (PApp "d" LNil) LNil))) LNil))))) (PApp "start" LNil))
  (println! (NormalizedDispatchControl "refuse-top-matched-observation-1" (== (== $actual (quote (LCons (PApp "out" (LCons (PApp "c" LNil) LNil)) (LCons (PApp "out" (LCons (PApp "d" LNil) LNil)) (LCons (PApp "out" (LCons (PApp "d" LNil) LNil)) LNil))))) False))))
!(let $actual (gslt:normalized:language-root-reducts (GSLTLanguageDefWireV1 "conditional-child-match-grants-no-permission" LNil LNil LNil (LCons (RewriteRule "guard" LNil (LCons (RelationQuery "ready" LNil) LNil) (PApp "start" LNil) (PApp "done" LNil)) LNil)) (LCons (ProviderRow "ready" LNil) LNil) (PApp "wrap" (LCons (PApp "start" LNil) LNil)))
  (println! (NormalizedDispatchControl "refuse-top-matched-observation-2" (== (== $actual (quote (LCons (PApp "wrap" (LCons (PApp "done" LNil) LNil)) LNil))) False))))

!(let $actual
    (gslt:normalized:language-top
      (GSLTLanguageDefWireV1 "metadata-match-only" (Types opaque) (Terms retained)
        (Equations opaque)
        (LCons (RewriteRule "duplicate" (Context opaque) LNil
            (PApp "f" (LCons (FVar "x") LNil)) (PApp "done" LNil))
          (LCons (RewriteRule "duplicate" (Context opaque) LNil
              (PApp "f" (LCons (FVar "x") LNil)) (PApp "done" LNil)) LNil)))
      (PApp "f" (LCons (PApp "a" LNil) LNil)))
  (println! (NormalizedDispatchControl "matcher-retains-opaque-metadata-and-occurrences"
    (== $actual (quote (MatchRun
      (LCons (Found LNil 0 (LCons (Binding "x" (PApp "a" LNil)) LNil))
        (LCons (Found LNil 1 (LCons (Binding "x" (PApp "a" LNil)) LNil)) LNil)) 2 4))))))

!(let $actual
    (gslt:normalized:language-root-reducts
      (GSLTLanguageDefWireV1 "nonlinear" LNil LNil LNil
        (LCons (RewriteRule "same" LNil LNil
          (PApp "pair" (LCons (FVar "x") (LCons (FVar "x") LNil)))
          (PApp "done" LNil)) LNil)) LNil
      (PApp "pair" (LCons (PApp "a" LNil) (LCons (PApp "b" LNil) LNil))))
  (println! (NormalizedDispatchControl "nonlinear-structural-candidate-is-refused"
    (== $actual (quote LNil)))))

!(let $actual
    (gslt:normalized:language-root-reducts
      (GSLTLanguageDefWireV1 "duplicate-rows" (Types retained) (Terms retained) LNil
        (LCons (RewriteRule "same" (Context retained) LNil
            (PApp "f" (LCons (FVar "x") LNil)) (FVar "x"))
          (LCons (RewriteRule "same" (Context retained) LNil
              (PApp "f" (LCons (FVar "x") LNil)) (FVar "x")) LNil))) LNil
      (PApp "f" (LCons (PApp "a" LNil) LNil)))
  (println! (NormalizedDispatchControl "duplicate-rows-survive-shared-dispatch"
    (== $actual (quote (LCons (PApp "a" LNil) (LCons (PApp "a" LNil) LNil)))))))
