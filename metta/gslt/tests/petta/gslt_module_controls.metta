; Generated from complete-row module assembly and canonical contextual execution.
!(let $actual (gslt:module:assemble "Assembled" LNil)
  (println! (ModuleExecutionControl "assemble-empty" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  LNil)
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
 LNil))))
  (println! (ModuleExecutionControl "assemble-split-core" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "First"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Last"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 LNil))))))
  (println! (ModuleExecutionControl "assemble-empty-between-fragments" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "First"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "First"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))
 LNil))))
  (println! (ModuleExecutionControl "assemble-duplicate-physical-rows" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Left"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Right"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))
 LNil)))
  (println! (ModuleExecutionControl "assemble-staged-assembly" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Syntax"
  (LCons (TypeDecl "Term" CarrierAst) LNil)
  (LCons (GrammarRule "Start" "Term" LNil (LCons (SyntaxTerminal "start") LNil) EvalNone) LNil)
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "contextual-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
 LNil)))))
  (println! (ModuleExecutionControl "assemble-signature-retained" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  (LCons (TypeDecl "Term" CarrierAst) LNil)
  (LCons (GrammarRule "Start" "Term" LNil (LCons (SyntaxTerminal "start") LNil) EvalNone) LNil)
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Other"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Other"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))
 LNil)))
  (println! (ModuleExecutionControl "assemble-local-names-do-not-override" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil)))))
))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 LNil))))
  (println! (ModuleExecutionControl "assemble-all-empty" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled"
  LNil
  LNil
  LNil
  LNil)
))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-recursive-witness-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)))) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-duplicate-wrapper-occurrences" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil) MatchBottomUp LNil 3 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-missing-recursive-witness" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 LNil) MatchBottomUp LNil 3 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-missing-context-permission" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (RelationQuery "allow" (LCons (FVar "x") LNil)) (LCons (Congruence (FVar "x") (FVar "y")) LNil)) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil))) MatchBottomUp (LCons (ProviderRow "allow" (LCons (PApp "Start" LNil) LNil)) (LCons (ProviderRow "allow" (LCons (PApp "Start" LNil) LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-guard-and-recursion-cross-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp LNil 1 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-exhausted-recursive-depth" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-freshness-witness-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil))) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-freshness-retains-duplicate-wrapper-occurrences" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "atom") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-nonfresh-recursive-witness-refused" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 LNil) MatchBottomUp LNil 3 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-freshness-does-not-authorize-context" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) (LCons (RelationQuery "name" (LCons (FVar "atom") LNil)) LNil)) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (FVar "actual") LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-freshness-before-query-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (RelationQuery "name" (LCons (FVar "atom") LNil)) (LCons (Freshness "atom" (FVar "subject")) LNil)) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchBottomUp (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (FVar "actual") LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchBottomUp-query-before-freshness-refuses-recursive-witness" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-recursive-witness-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)))) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-duplicate-wrapper-occurrences" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil) MatchTopDown LNil 3 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-missing-recursive-witness" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 LNil) MatchTopDown LNil 3 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-missing-context-permission" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (RelationQuery "allow" (LCons (FVar "x") LNil)) (LCons (Congruence (FVar "x") (FVar "y")) LNil)) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil))) MatchTopDown (LCons (ProviderRow "allow" (LCons (PApp "Start" LNil) LNil)) (LCons (ProviderRow "allow" (LCons (PApp "Start" LNil) LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-guard-and-recursion-cross-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown LNil 1 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-exhausted-recursive-depth" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-freshness-witness-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil))) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-freshness-retains-duplicate-wrapper-occurrences" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "atom") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-nonfresh-recursive-witness-refused" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) LNil) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil)))
 LNil) MatchTopDown LNil 3 (PApp "Box" (LCons (PApp "Fresh" (LCons (PApp "Pair" (LCons (FVar "other") (LCons (FVar "other") LNil))) LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-freshness-does-not-authorize-context" (== $actual (quote LNil)))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (Freshness "atom" (FVar "subject")) (LCons (RelationQuery "name" (LCons (FVar "atom") LNil)) LNil)) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (FVar "actual") LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-freshness-before-query-crosses-fragments" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Accepted" LNil) LNil)) LNil)))))))
!(let $actual (gslt:module:reducts "Assembled" (LCons (GSLTLanguageDefWireV1 "freshness-controls"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "fresh" LNil (LCons (RelationQuery "name" (LCons (FVar "atom") LNil)) (LCons (Freshness "atom" (FVar "subject")) LNil)) (PApp "Fresh" (LCons (FVar "subject") LNil)) (PApp "Accepted" LNil)) LNil))
 (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))
 LNil)) MatchTopDown (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) (LCons (ProviderRow "name" (LCons (FVar "actual") LNil)) LNil)) 2 (PApp "Box" (LCons (PApp "Fresh" (LCons (FVar "actual") LNil)) LNil)))
  (println! (ModuleExecutionControl "MatchTopDown-query-before-freshness-refuses-recursive-witness" (== $actual (quote LNil)))))
!(let $actual (gslt:module:assemble "Assembled" (LCons BrokenFragment LNil))
  (println! (ModuleExecutionControl "malformed-fragment-0" (== $actual (quote None)))))
!(let $actual (gslt:module:assemble "Assembled" BrokenTail)
  (println! (ModuleExecutionControl "malformed-fragment-1" (== $actual (quote None)))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "MissingField" LNil LNil LNil) LNil))
  (println! (ModuleExecutionControl "malformed-fragment-2" (== $actual (quote None)))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Empty"
  LNil
  LNil
  LNil
  LNil)
 (LCons BrokenFragment LNil)))
  (println! (ModuleExecutionControl "malformed-fragment-3" (== $actual (quote None)))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Left" (LCons first-type LNil) (LCons first-syntax LNil) (LCons same-equation LNil) (LCons first-rewrite LNil)) (LCons (GSLTLanguageDefWireV1 "Right" (LCons second-type LNil) (LCons second-syntax LNil) (LCons same-equation LNil) (LCons second-rewrite LNil)) LNil)))
  (println! (ModuleExecutionControl "opaque-all-row-families" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled" (LCons first-type (LCons second-type LNil)) (LCons first-syntax (LCons second-syntax LNil)) (LCons same-equation (LCons same-equation LNil)) (LCons first-rewrite (LCons second-rewrite LNil)))))))))
!(let $actual (gslt:module:assemble "Assembled" (LCons (GSLTLanguageDefWireV1 "Left" (LCons first-type LNil) (LCons first-syntax LNil) (LCons same-equation LNil) (LCons first-rewrite LNil)) (LCons (GSLTLanguageDefWireV1 "Left" (LCons first-type LNil) (LCons first-syntax LNil) (LCons same-equation LNil) (LCons first-rewrite LNil)) LNil)))
  (println! (ModuleExecutionControl "opaque-duplicate-equation-occurrences" (== $actual (quote (Some (GSLTLanguageDefWireV1 "Assembled" (LCons first-type (LCons first-type LNil)) (LCons first-syntax (LCons first-syntax LNil)) (LCons same-equation (LCons same-equation LNil)) (LCons first-rewrite (LCons first-rewrite LNil)))))))))
!(let $actual (gslt:module:join CoherentOriginV1 LNil LNil)
  (println! (ModuleExecutionControl "CoherentOriginV1-empty" (== $actual (quote (Some LNil))))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-diamond" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-same-fragment-twice" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))))))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil)) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))))
  (println! (ModuleExecutionControl "CoherentOriginV1-first-seen-order" (== $actual (quote (Some (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-duplicate-within-fragment" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Other" "shared" SharedBody) LNil))
  (println! (ModuleExecutionControl "CoherentOriginV1-label-collision" (== $actual (quote None)))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Shared" "shared" ChangedBody) LNil))
  (println! (ModuleExecutionControl "CoherentOriginV1-shared-body-conflict" (== $actual (quote None)))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Shared" "renamed" SharedBody) LNil))
  (println! (ModuleExecutionControl "CoherentOriginV1-distinct-view-at-shared-origin" (== $actual (quote None)))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Shared" "shared" ChangedBody) LNil))))
  (println! (ModuleExecutionControl "CoherentOriginV1-late-conflict" (== $actual (quote None)))))
!(let $actual (gslt:module:join StructuralOriginViewV1 LNil LNil)
  (println! (ModuleExecutionControl "StructuralOriginViewV1-empty" (== $actual (quote (Some LNil))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-diamond" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-same-fragment-twice" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil)) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-first-seen-order" (== $actual (quote (Some (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil))) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-duplicate-within-fragment" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) (LCons (ModuleEntry "Right" "right" RightBody) LNil)))))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Other" "shared" SharedBody) LNil))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-label-collision" (== $actual (quote None)))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Shared" "shared" ChangedBody) LNil))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-shared-body-conflict" (== $actual (quote None)))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons (ModuleEntry "Shared" "renamed" SharedBody) LNil))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-distinct-view-at-shared-origin" (== $actual (quote (Some (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Shared" "renamed" SharedBody) LNil))))))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Left" "left" LeftBody) LNil)) (LCons (ModuleEntry "Right" "right" RightBody) (LCons (ModuleEntry "Shared" "shared" SharedBody) (LCons (ModuleEntry "Shared" "shared" ChangedBody) LNil))))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-late-conflict" (== $actual (quote None)))))
!(let $actual (gslt:module:join OtherContract LNil LNil)
  (println! (ModuleExecutionControl "unknown-contract" (== $actual (quote None)))))
!(let $actual (gslt:module:join CoherentOriginV1 (LCons BrokenEntry LNil) LNil)
  (println! (ModuleExecutionControl "malformed-entry" (== $actual (quote None)))))
!(let $actual (gslt:module:join CoherentOriginV1 LNil BrokenTail)
  (println! (ModuleExecutionControl "malformed-tail" (== $actual (quote None)))))
!(let $actual (gslt:module:join StructuralOriginViewV1 (LCons (ModuleEntry "Shared" "shared" SharedBody) LNil) (LCons BrokenEntry LNil))
  (println! (ModuleExecutionControl "malformed-late-entry" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-diamond-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-repeated-import-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "OtherWrapper" "second-wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-distinct-identities-retain-body-rules" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-missing-context-permission-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-missing-child-witness-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil LNil)) LNil))) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-late-conflict-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "OtherOrigin" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-label-collision-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "renamed-children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchBottomUp-shared-origin-view-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-diamond-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-repeated-import-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "OtherWrapper" "second-wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-distinct-identities-retain-body-rules" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-missing-context-permission-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-missing-child-witness-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil LNil)) LNil))) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-late-conflict-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "OtherOrigin" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-label-collision-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "renamed-children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "CoherentOriginV1-MatchTopDown-shared-origin-view-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-diamond-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-repeated-import-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "OtherWrapper" "second-wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-distinct-identities-retain-body-rules" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-missing-context-permission-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-missing-child-witness-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil LNil)) LNil))) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-late-conflict-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "OtherOrigin" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-label-collision-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "renamed-children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchBottomUp LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchBottomUp-shared-origin-view-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-diamond-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-repeated-import-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "OtherWrapper" "second-wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-distinct-identities-retain-body-rules" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-missing-context-permission-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-missing-child-witness-after-join" (== $actual (quote LNil)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Right" "empty" (GSLTLanguageDefWireV1 "Empty" LNil LNil LNil LNil)) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil LNil)) LNil))) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-late-conflict-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "OtherOrigin" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-label-collision-refuses-execution" (== $actual (quote None)))))
!(let $actual (gslt:module:import-reducts StructuralOriginViewV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) (LCons (ModuleEntry "Left" "wrapper" (GSLTLanguageDefWireV1 "Wrapper" LNil LNil LNil (LCons (RewriteRule "box-step" LNil (LCons (Congruence (FVar "x") (FVar "y")) LNil) (PApp "Box" (LCons (FVar "x") LNil)) (PApp "Box" (LCons (FVar "y") LNil))) LNil))) LNil)) (LCons (ModuleEntry "Shared" "renamed-children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) MatchTopDown LNil 2 (PApp "Box" (LCons (PApp "Start" LNil) LNil)))
  (println! (ModuleExecutionControl "StructuralOriginViewV1-MatchTopDown-shared-origin-view-execution" (== $actual (quote (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Final" LNil) LNil)) (LCons (PApp "Box" (LCons (PApp "Middle" LNil) LNil)) LNil)))))))))))
!(let $actual (gslt:module:bodies (LCons (ModuleEntry "Opaque" "opaque" (+ 2 3)) LNil))
  (println! (ModuleExecutionControl "import-body-remains-opaque" (== $actual (quote (LCons (+ 2 3) LNil))))))
!(let $actual (gslt:module:import-reducts CoherentOriginV1 "Assembled" (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) (LCons (RewriteRule "second" LNil LNil (PApp "Start" LNil) (PApp "Final" LNil)) (LCons (RewriteRule "first" LNil LNil (PApp "Start" LNil) (PApp "Middle" LNil)) LNil))))) LNil) (LCons (ModuleEntry "Shared" "children" (GSLTLanguageDefWireV1 "Children" LNil LNil LNil LNil)) LNil) (+ 2 3) (+ 2 3) (+ 2 3) (+ 2 3))
  (println! (ModuleExecutionControl "import-conflict-does-not-evaluate-strategy-or-subject" (== $actual (quote None)))))
