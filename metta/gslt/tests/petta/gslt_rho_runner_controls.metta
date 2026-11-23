; Expected traces are the Lean iteration of LexCanonical.lexCanon and the first completed
; receipt of GeneralRho.DepthOne.plan, on the same processes.
!(let $actual (rho:run (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) LNil)) RNone) 5 1000)
  (println! (RhoRunControl "received-code-runs" (== $actual (quote (RhoTrace (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) RNone) (LCons (PApp "PZero" LNil) LNil)) RhoQuiescent))))))
!(let $actual (rho:run (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) LNil))) RNone) 5 1000)
  (println! (RhoRunControl "two-step-relay" (== $actual (quote (RhoTrace (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) LNil))) RNone) (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) RNone) (LCons (PApp "PZero" LNil) LNil))) RhoQuiescent))))))
!(let $actual (rho:run (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil)))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) LNil))) RNone) 5 1000)
  (println! (RhoRunControl "race-picks-one" (== $actual (quote (RhoTrace (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil)))) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) RNone) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil)))) LNil))) LNil)) RhoQuiescent))))))
!(let $actual (rho:run (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)) (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) LNil)) RNone)) LNil))) 5 1000)
  (println! (RhoRunControl "guarded-is-quiescent" (== $actual (quote (RhoTrace (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) RNone)) LNil))) LNil) RhoQuiescent))))))
!(let $actual (rho:run (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) LNil))) RNone) 1 1000)
  (println! (RhoRunControl "fuel-bounds-the-run" (== $actual (quote (RhoTrace (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) LNil))) RNone) (LCons (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) RNone) LNil)) RhoFuelSpent))))))

; Retained single-COMM searches use the public program driver for construction.
; These controls inspect the retained value, not only its receipt prefix.
(: rho:control:begin (-> Atom Atom %Undefined%))
(= (rho:control:begin $plan $process)
   (case $plan
     (((RhoPlan $environment $permissions $bound $expected $rules)
       (let $canonical (rho:lex:canonical $process)
         (let $observation
           (gslt:program:execute $environment $permissions $bound $expected $canonical $rules 0)
           (RhoSearch $canonical $observation)))))))
(= (rho:control:process (RhoSearch $process $observation)) $process)
(= (rho:control:observation (RhoSearch $process $observation)) $observation)
(= (rho:control:status (ProgramPublication $receipts $status)) $status)
(= (rho:control:has-jobs (ProgramObservation LNil $receipts)) false)
(= (rho:control:has-jobs (ProgramObservation (LCons $job $rest) $receipts)) true)
(= (rho:control:plan) (RhoPlan (PremiseEnvironment (LCons (GrammarTypingV1 "PZero" "Proc" LNil) (LCons (GrammarTypingV1 "PDrop" "Proc" (LCons (TermSimple "n" (TBase "Name")) LNil)) (LCons (GrammarTypingV1 "NQuote" "Name" (LCons (TermSimple "p" (TBase "Proc")) LNil)) (LCons (GrammarTypingV1 "PPar" "Proc" (LCons (TermSimple "ps" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)) (LCons (GrammarTypingV1 "POutput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermSimple "q" (TBase "Proc")) LNil))) (LCons (GrammarTypingV1 "PInput" "Proc" (LCons (TermSimple "n" (TBase "Name")) (LCons (TermAbstraction BNone "p" (TArrow (TBase "Name") (TBase "Proc"))) LNil))) LNil)))))) (LCons (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) LNil) (LCons (PremiseSpecification 0 (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil)))) LNil) (PremiseProvider LNil LNil) (PremiseReflection (LCons (ReflectivePresentation "RhoCommSubstitution" "Proc" "Name" "NQuote" "PDrop" "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" "PZero" "QuoteDrop" QuoteClosed) LNil) (LCons (ReflectiveRule "RhoCommReflective" "Comm" "RhoCommSubstitution" "RhoCommSubstitution") LNil)) LNil) (OperationalPermissions PermissionYes PermissionNo LNil PermissionNo PermissionNo LNil) LNil (TBase "Proc") (LCons (RuleJobDeclaration 0 (ScopedRewriteRuleV1 "Comm" (LCons (TypeBinding "n" (TBase "Name")) (LCons (TypeBinding "p" (TBase "Proc")) (LCons (TypeBinding "q" (TBase "Proc")) (LCons (TypeBinding "rest" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Proc"))) LNil)))) LNil (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "PInput" (LCons (FVar "n") (LCons (PLam BNone (FVar "p")) LNil))) (LCons (PApp "POutput" (LCons (FVar "n") (LCons (FVar "q") LNil))) LNil)) (RSome "rest")) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PSubst (FVar "p") (PApp "NQuote" (LCons (FVar "q") LNil))) LNil) (RSome "rest")) (RuleBindingSome (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))))) (RuleBindingPlan (RuleBindingSpec (LCons (RuleDependency "n" LNil) (LCons (RuleDependency "p" (LCons (TBase "Name") LNil)) (LCons (RuleDependency "q" LNil) (LCons (RuleDependency "rest" LNil) LNil)))) (LCons (RuleOccurrence "p" RuleLeft (LCons 0 (LCons 1 (LCons 0 LNil))) (LCons (Var 0) LNil)) (LCons (RuleOccurrence "p" RuleRight (LCons 0 (LCons 0 LNil)) (LCons (Var 0) LNil)) LNil))) BindingAuthored)) LNil)))
(= (rho:control:process-fixture) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) LNil)) RNone))
!(println! (RhoSearchControl "zero-budget-keeps-whole-search" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let $same (rho:run:resume-search $start 0) (== $same $start)))))
!(println! (RhoSearchControl "split-budget-matches-sum" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let* (($once (rho:run:resume-search $start 2))
                  ($twice (rho:run:resume-search $once 5))
                  ($together (rho:run:resume-search $start 7)))
           (== $twice $together)))))
!(println! (RhoSearchControl "zero-budget-keeps-pending-jobs" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let $observation (rho:control:observation $start)
           (rho:control:has-jobs $observation)))))
!(println! (RhoSearchControl "empty-pending-is-not-complete" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let* (($observation (rho:control:observation $start))
                  ($publication (gslt:program:publication $observation)))
           (== (rho:control:status $publication) ProgramPublicationPending)))))
!(println! (RhoSearchControl "resume-preserves-process" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let $resumed (rho:run:resume-search $start 7)
           (== (rho:control:process $resumed) (rho:control:process $start))))))
!(println! (RhoSearchControl "resume-advances-retained-frames" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let $resumed (rho:run:resume-search $start 7)
           (== (== $resumed $start) false)))))
!(println! (RhoSearchControl "complete-search-keeps-step-receipt" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let* (($resumed (rho:run:resume-search $start 1000))
                  ($observation (rho:control:observation $resumed))
                  ($publication (gslt:program:publication $observation)))
           (case $publication
             (((ProgramPublication (LCons $receipt $rest) ProgramPublicationComplete) true)
              ($anything false)))))))
!(println! (RhoSearchControl "settled-empty-is-complete" (let* (($plan (rho:control:plan))
         ($process (rho:control:process-fixture))
         ($start (rho:control:begin $plan $process)))
(let* (($zero (rho:control:begin $plan (PApp "PZero" LNil)))
                  ($resumed (rho:run:resume-search $zero 1000))
                  ($observation (rho:control:observation $resumed))
                  ($publication (gslt:program:publication $observation)))
           (== $publication (quote (ProgramPublication LNil ProgramPublicationComplete)))))))

; Retained multi-COMM process. Matcher budget stays on resume-process.
; These controls use the authored process operations and do not change
; RhoRunControl or RhoSearchControl.
(= (rho:control:two-step) (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PLam BNone (PApp "PDrop" (LCons (Var 0) LNil))) LNil))) (LCons (PApp "PInput" (LCons (PApp "NQuote" (LCons (PApp "POutput" (LCons (PApp "NQuote" (LCons (PApp "PZero" LNil) LNil)) (LCons (PApp "PZero" LNil) LNil))) LNil)) (LCons (PLam BNone (PApp "PZero" LNil)) LNil))) LNil))) RNone))
(= (rho:control:process-phase (RhoProcess $history (RhoLive $search))) process-live)
(= (rho:control:process-phase (RhoProcess $history (RhoDone $process))) process-done)
(= (rho:control:process-phase (RhoProcess $history RhoCancelled)) process-cancelled)
(= (rho:control:process-status (RhoProcess $history (RhoLive (RhoSearch $process $observation))))
   (rho:control:status (gslt:program:publication $observation)))
(= (rho:control:count LNil) 0)
(= (rho:control:count (LCons $head $tail)) (+ 1 (rho:control:count $tail)))
(= (rho:control:commits (RhoProcess $history $phase)) $history)
(= (rho:control:live-publication (RhoProcess $history (RhoLive (RhoSearch $process $observation))))
   (gslt:program:publication $observation))
(= (rho:control:receipt (ProgramPublication (LCons $receipt $rest) $status)) $receipt)
!(println! (RhoProcessControl "zero-budget-is-pending" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process)))
   (if (== (rho:control:process-phase $start) process-live)
     (if (== (rho:control:process-status $start) ProgramPublicationPending)
       (if (== (rho:control:count (rho:control:commits $start)) 0) true false)
       false)
     false))))
!(println! (RhoProcessControl "partial-prefix-not-quiescent" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($paused (rho:run:resume-process $start 1)))
   (if (== (rho:control:process-phase $paused) process-live)
     (if (== (rho:control:process-status $paused) ProgramPublicationPending)
       (if (== (== $paused $start) false) true false)
       false)
     false))))
!(println! (RhoProcessControl "two-communication-suffix" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($trace (rho:run $plan $process 5 1000))
        ($start (rho:run:begin $plan $process))
        ($paused (rho:run:resume-process $start 1))
        ($ready (rho:run:resume-process $start 1000))
        ($first (rho:run:commit $plan $ready))
        ($held (rho:run:resume-process $first 0))
        ($next (rho:run:resume-process $first 1000))
        ($second (rho:run:commit $plan $next))
        ($settled (rho:run:resume-process $second 1000))
        ($done (rho:run:commit $plan $settled)))
   (case $trace
     (((RhoTrace (LCons $s1 (LCons $s2 (LCons $s3 LNil))) RhoQuiescent)
       (case (rho:control:commits $second)
         (((LCons (RhoCommit $b1 $r1 $a1) (LCons (RhoCommit $b2 $r2 $a2) LNil))
           (case $done
             (((RhoProcess $doneHistory (RhoDone $doneProcess))
               (if (== (rho:control:process-status $paused) ProgramPublicationPending) (if (== (== $paused $start) false) (if (== (rho:control:process-phase $first) process-live) (if (== (rho:control:process-status $first) ProgramPublicationPending) (if (== (rho:control:count (rho:control:commits $first)) 1) (if (== $held $first) (if (== (== $next $first) false) (if (== (rho:control:count (rho:control:commits $second)) 2) (if (== $b1 $s1) (if (== $a1 $s2) (if (== $b2 $s2) (if (== $a2 $s3) (if (== $doneHistory (rho:control:commits $second)) (if (== $doneProcess $s3) true false) false) false) false) false) false) false) false) false) false) false) false) false) false))
              ($other false))))
          ($other false))))
      ($other false))))))
!(println! (RhoProcessControl "advance-does-not-replay" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($ready (rho:run:resume-process $start 1000))
        ($first (rho:run:commit $plan $ready))
        ($again (rho:run:advance $plan $ready 2)))
   (== $again $first))))
!(println! (RhoProcessControl "cancel-keeps-history" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($ready (rho:run:resume-process $start 1000))
        ($first (rho:run:commit $plan $ready))
        ($cancelled (rho:run:cancel $first)))
   (if (== (rho:control:process-phase $cancelled) process-cancelled)
     (if (== (rho:control:commits $cancelled) (rho:control:commits $first))
       (if (== (rho:run:commit $plan $cancelled) $cancelled)
         (if (== (rho:run:advance $plan $cancelled 3) $cancelled) true false)
         false)
       false)
     false))))
!(println! (RhoProcessControl "selected-candidate-commits" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($ready (rho:run:resume-process $start 1000))
        ($publication (rho:control:live-publication $ready))
        ($receipt (rho:control:receipt $publication))
        ($first (rho:run:commit $plan $ready))
        ($accepted (rho:run:commit-candidate $plan $ready $receipt)))
   (== $accepted $first))))
!(println! (RhoProcessControl "foreign-candidate-refused" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($ready (rho:run:resume-process $start 1000))
        ($foreign (rho:run:commit-candidate $plan $ready ForeignReceipt)))
   (== $foreign $ready))))
!(println! (RhoProcessControl "stale-candidate-refused" (let* (($plan (rho:control:plan))
        ($process (rho:control:two-step))
        ($start (rho:run:begin $plan $process))
        ($ready (rho:run:resume-process $start 1000))
        ($publication (rho:control:live-publication $ready))
        ($receipt (rho:control:receipt $publication))
        ($first (rho:run:commit $plan $ready))
        ($stale (rho:run:commit-candidate $plan $first $receipt)))
   (== $stale $first))))
!(println! (RhoProcessControl "distinct-receipts-stay-distinct" (let* (($zero (PApp "PZero" LNil))
        ($left (RhoCommit $zero receipt-left $zero))
        ($right (RhoCommit $zero receipt-right $zero))
        ($once (rho:run:append-commit LNil $left))
        ($history (rho:run:append-commit $once $right)))
   (if (== (== $left $right) false)
     (if (== (rho:control:count $history) 2)
       (case $history
         (((LCons $first (LCons $second LNil))
           (if (== $first $left) (if (== $second $right) true false) false))
          ($other false)))
       false)
     false))))

(=
  (rho:control:independent)
  (let*
    (($zero (PApp "PZero" LNil))
      ($name (PApp "NQuote" (LCons $zero LNil)))
      ($other (PApp "NQuote" (LCons (PApp "POutput" (LCons $name (LCons $zero LNil))) LNil))))
    (PCollection
      "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag"
      (LCons
        (PApp "PInput" (LCons $name (LCons (PLam BNone $zero) LNil)))
        (LCons
          (PApp "POutput" (LCons $name (LCons $zero LNil)))
          (LCons
            (PApp "PInput" (LCons $other (LCons (PLam BNone $zero) LNil)))
            (LCons (PApp "POutput" (LCons $other (LCons $zero LNil))) LNil))))
      RNone)))
(= (rho:control:second (ProgramPublication (LCons $first (LCons $second $rest)) $status)) $second)
(= (rho:control:live-state (RhoProcess $history (RhoLive (RhoSearch $process $observation)))) $process)
!(println!
  (RhoPublicationControl
    "head-policy-agrees"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed2 (let* (($computed1 (rho:control:independent))) (rho:run:begin $plan $computed1))))
            (rho:run:resume-process $computed2 1000)))
        ($head (let* (($computed3 (rho:control:live-publication $ready))) (rho:control:receipt $computed3))))
      (== (rho:run:commit-published $plan $ready $head) (rho:run:commit-candidate $plan $ready $head)))))
!(println!
  (RhoPublicationControl
    "nonhead-receipt-selectable"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed5 (let* (($computed4 (rho:control:independent))) (rho:run:begin $plan $computed4))))
            (rho:run:resume-process $computed5 1000)))
        ($second (let* (($computed6 (rho:control:live-publication $ready))) (rho:control:second $computed6)))
        ($selected (rho:run:commit-published $plan $ready $second)))
      (if
        (== (let* (($computed7 (rho:control:commits $selected))) (rho:control:count $computed7)) 1)
        (== (rho:run:commit-candidate $plan $ready $second) $ready)
        false))))
!(println!
  (RhoPublicationControl
    "independent-diamond-keeps-different-histories"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed9 (let* (($computed8 (rho:control:independent))) (rho:run:begin $plan $computed8))))
            (rho:run:resume-process $computed9 1000)))
        ($pub (rho:control:live-publication $ready))
        ($one
          (let*
            (($computed10 (rho:control:receipt $pub)))
            (rho:run:commit-published $plan $ready $computed10)))
        ($two
          (let* (($computed11 (rho:control:second $pub))) (rho:run:commit-published $plan $ready $computed11)))
        ($ab (let* (($computed12 (rho:run:resume-process $one 1000))) (rho:run:commit $plan $computed12)))
        ($ba (let* (($computed13 (rho:run:resume-process $two 1000))) (rho:run:commit $plan $computed13))))
      (if
        (== (rho:control:live-state $ab) (rho:control:live-state $ba))
        (if
          (== (let* (($computed14 (rho:control:commits $ab))) (rho:control:count $computed14)) 2)
          (if
            (== (let* (($computed15 (rho:control:commits $ba))) (rho:control:count $computed15)) 2)
            (== (== (rho:control:commits $ab) (rho:control:commits $ba)) false)
            false)
          false)
        false))))
!(println!
  (RhoPublicationControl
    "foreign-receipt-refused"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed17 (let* (($computed16 (rho:control:independent))) (rho:run:begin $plan $computed16))))
            (rho:run:resume-process $computed17 1000))))
      (== (rho:run:commit-published $plan $ready ForeignReceipt) $ready))))
!(println!
  (RhoPublicationControl
    "stale-source-receipt-refused"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed19 (let* (($computed18 (rho:control:independent))) (rho:run:begin $plan $computed18))))
            (rho:run:resume-process $computed19 1000)))
        ($receipt
          (let* (($computed20 (rho:control:live-publication $ready))) (rho:control:receipt $computed20)))
        ($next (rho:run:commit-published $plan $ready $receipt)))
      (== (rho:run:commit-published $plan $next $receipt) $next))))
!(println!
  (RhoPublicationControl
    "cancelled-cannot-commit"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed22 (let* (($computed21 (rho:control:independent))) (rho:run:begin $plan $computed21))))
            (rho:run:resume-process $computed22 1000)))
        ($receipt
          (let* (($computed23 (rho:control:live-publication $ready))) (rho:control:receipt $computed23)))
        ($cancelled (rho:run:cancel $ready)))
      (== (rho:run:commit-published $plan $cancelled $receipt) $cancelled))))
!(println!
  (RhoPublicationControl
    "pending-cannot-commit"
    (let*
      (($plan (rho:control:plan))
        ($pending (let* (($computed24 (rho:control:independent))) (rho:run:begin $plan $computed24))))
      (== (rho:run:commit-published $plan $pending ForeignReceipt) $pending))))
!(println!
  (RhoPublicationControl
    "whole-receipt-not-value-membership"
    (if
      (rho:run:contains-receipt (Receipt first same-value) (LCons (Receipt second same-value) LNil))
      false
      true)))
(=
  (rho:control:cells)
  (LCons
    (RhoCell 0 (RhoLiveCell (LCons input LNil)))
    (LCons
      (RhoCell 1 (RhoLiveCell (LCons output LNil)))
      (LCons
        (RhoCell 3 (RhoLiveCell (LCons input LNil)))
        (LCons (RhoCell 4 (RhoLiveCell (LCons output LNil))) LNil)))))
(=
  (rho:control:cell-proposal $input $output $result)
  (RhoProposal
    (LCons
      (RhoCell $input (RhoLiveCell (LCons input LNil)))
      (LCons (RhoCell $output (RhoLiveCell (LCons output LNil))) (LCons (RhoCell $result RhoFresh) LNil)))
    (LCons
      (RhoCell $input RhoSpent)
      (LCons (RhoCell $output RhoSpent) (LCons (RhoCell $result (RhoLiveCell LNil)) LNil)))))
(= (rho:control:accepted-cells (RhoCellsAccepted $cells)) $cells)
!(println!
  (RhoCellControl
    "missing-is-fresh"
    (== (let* (($computed25 (rho:control:cells))) (rho:run:cell-read $computed25 2)) RhoFresh)))
!(println!
  (RhoCellControl
    "valid-proposal-accepted"
    (case
      (let*
        (($computed26 (rho:control:cells)) ($computed27 (rho:control:cell-proposal 0 1 2)))
        (rho:run:commit-cells $computed26 $computed27))
      (((RhoCellsAccepted $cells)
         (if
           (== (rho:run:cell-read $cells 0) RhoSpent)
           (if
             (== (rho:run:cell-read $cells 1) RhoSpent)
             (== (rho:run:cell-read $cells 2) (RhoLiveCell LNil))
             false)
           false))
        ($other false)))))
!(println!
  (RhoCellControl
    "replay-refused"
    (let*
      (($proposal (rho:control:cell-proposal 0 1 2))
        ($once
          (let*
            (($computed29
               (let* (($computed28 (rho:control:cells))) (rho:run:commit-cells $computed28 $proposal)))
)
            (rho:control:accepted-cells $computed29))))
      (== (rho:run:commit-cells $once $proposal) (RhoCellsRefused $once)))))
!(println!
  (RhoCellControl
    "independent-update-stays-valid"
    (let*
      (($once
         (let*
           (($computed32
              (let*
                (($computed30 (rho:control:cells)) ($computed31 (rho:control:cell-proposal 0 1 2)))
                (rho:run:commit-cells $computed30 $computed31)))
)
           (rho:control:accepted-cells $computed32)))
        ($both
          (let* (($computed33 (rho:control:cell-proposal 3 4 5))) (rho:run:commit-cells $once $computed33))))
      (case $both (((RhoCellsAccepted $cells) (== (rho:run:cell-read $cells 3) RhoSpent)) ($other false))))))
!(println!
  (RhoCellControl
    "competing-update-refused"
    (let
      $once
      (let*
        (($computed36
           (let*
             (($computed34 (rho:control:cells)) ($computed35 (rho:control:cell-proposal 0 1 2)))
             (rho:run:commit-cells $computed34 $computed35)))
)
        (rho:control:accepted-cells $computed36))
      (==
        (let* (($computed37 (rho:control:cell-proposal 0 4 5))) (rho:run:commit-cells $once $computed37))
        (RhoCellsRefused $once)))))
!(println!
  (RhoCellControl
    "spent-result-cannot-be-reallocated"
    (let
      $once
      (let*
        (($computed40
           (let*
             (($computed38 (rho:control:cells)) ($computed39 (rho:control:cell-proposal 0 1 2)))
             (rho:run:commit-cells $computed38 $computed39)))
)
        (rho:control:accepted-cells $computed40))
      (==
        (let* (($computed41 (rho:control:cell-proposal 3 4 0))) (rho:run:commit-cells $once $computed41))
        (RhoCellsRefused $once)))))
!(println!
  (RhoCellControl
    "equal-values-distinct-occurrences"
    (let
      $once
      (let*
        (($computed44
           (let*
             (($computed42 (rho:control:cells)) ($computed43 (rho:control:cell-proposal 0 1 2)))
             (rho:run:commit-cells $computed42 $computed43)))
)
        (rho:control:accepted-cells $computed44))
      (if
        (== (rho:run:cell-read $once 0) RhoSpent)
        (== (rho:run:cell-read $once 3) (RhoLiveCell (LCons input LNil)))
        false))))
!(println!
  (RhoCellControl
    "allocation-read-is-validated"
    (let*
      (($cells (rho:control:cells)) ($occupied (LCons (RhoCell 2 (RhoLiveCell LNil)) $cells)))
      (==
        (let* (($computed45 (rho:control:cell-proposal 0 1 2))) (rho:run:commit-cells $occupied $computed45))
        (RhoCellsRefused $occupied)))))
(=
  (rho:control:duplicate-process)
  (let*
    (($zero (PApp "PZero" LNil))
      ($name (PApp "NQuote" (LCons $zero LNil)))
      ($input (PApp "PInput" (LCons $name (LCons (PLam BNone $zero) LNil))))
      ($output (PApp "POutput" (LCons $name (LCons $zero LNil)))))
    (PCollection
      "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag"
      (LCons $input (LCons $output (LCons $input (LCons $output LNil))))
      RNone)))
(= (rho:control:released (ProgramPublication $receipts $status)) $receipts)
!(println!
  (RhoPublicationControl
    "duplicate-syntax-keeps-four-distinct-matches"
    (let*
      (($plan (rho:control:plan))
        ($ready
          (let*
            (($computed47
               (let* (($computed46 (rho:control:duplicate-process))) (rho:run:begin $plan $computed46)))
)
            (rho:run:resume-process $computed47 1000)))
        ($pub (rho:control:live-publication $ready))
        ($first (rho:control:receipt $pub))
        ($second (rho:control:second $pub))
        ($a (rho:run:commit-published $plan $ready $first))
        ($b (rho:run:commit-published $plan $ready $second)))
      (if
        (== (let* (($computed48 (rho:control:released $pub))) (rho:control:count $computed48)) 4)
        (if
          (== (rho:control:live-state $a) (rho:control:live-state $b))
          (== (== (rho:control:commits $a) (rho:control:commits $b)) false)
          false)
        false))))
