; Exact ordered occurrences, independent declaration choices and permission refusals.

!(let $actual
  (gslt:sites:generate LNil LNil
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionYes PermissionYes LNil)
    LNil (TArrow (TBase "Expr") (TBase "Expr")) (PLam BNone (Var 0)))
  (println! (TypedSitesControl "lambda-retains-exact-bound-sort"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole (PLam BNone (Var 0)) LNil
        (TArrow (TBase "Expr") (TBase "Expr")) LNil)
      (LCons (RuleJobSite (LCons 0 LNil) (ContextLam BNone ContextHole) (Var 0)
        (LCons (TBase "Expr") LNil) (TBase "Expr")
        (LCons (TypingLambda (TBase "Expr")) LNil)) LNil)))))))

!(let $actual
  (gslt:sites:generate LNil LNil
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionNo PermissionYes LNil)
    LNil (TArrow (TBase "Expr") (TBase "Expr")) (PLam BNone (Var 0)))
  (println! (TypedSitesControl "lambda-permission-refuses-only-descent"
    (== $actual (quote (LCons (RuleJobSite LNil ContextHole (PLam BNone (Var 0)) LNil
      (TArrow (TBase "Expr") (TBase "Expr")) LNil) LNil))))))

!(let $actual
  (gslt:sites:generate LNil LNil
    (OperationalPermissions PermissionNo PermissionYes LNil PermissionYes PermissionYes LNil)
    LNil (TArrow (TBase "Expr") (TBase "Expr")) (PLam BNone (Var 0)))
  (println! (TypedSitesControl "disabled-permission-refuses-root" (== $actual LNil))))

!(let $actual
  (gslt:sites:generate LNil LNil
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionYes PermissionYes LNil)
    LNil (TArrow (TBase "Expr") (TBase "Other")) (PLam BNone (Var 0)))
  (println! (TypedSitesControl "wrong-bound-sort-refuses-root" (== $actual LNil))))

!(let $actual
  (gslt:sites:generate LNil LNil
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionYes PermissionYes LNil)
    LNil (TArrow (TMultiBinder (TBase "Name")) (TBase "Name"))
    (PMultiLam 2 (LCons "x" (LCons "y" LNil)) (Var 1)))
  (println! (TypedSitesControl "multiple-binders-retain-arity-sorts-and-display"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole (PMultiLam 2 (LCons "x" (LCons "y" LNil)) (Var 1)) LNil
        (TArrow (TMultiBinder (TBase "Name")) (TBase "Name")) LNil)
      (LCons (RuleJobSite (LCons 0 LNil) (ContextMultiLam 2 (LCons "x" (LCons "y" LNil)) ContextHole)
        (Var 1) (LCons (TBase "Name") (LCons (TBase "Name") LNil)) (TBase "Name")
        (LCons (TypingMultiLambda 2 (TBase "Name")) LNil)) LNil)))))))

!(let $actual (gslt:sites:cross-rules
  (LCons DeclarationA (LCons DeclarationA LNil))
  (LCons SiteA (LCons SiteA LNil)) 0)
  (println! (TypedSitesControl "cross-product-keeps-duplicate-occurrences"
    (== $actual (quote
      (LCons (RuleJob 0 DeclarationA SiteA)
      (LCons (RuleJob 0 DeclarationA SiteA)
      (LCons (RuleJob 1 DeclarationA SiteA)
      (LCons (RuleJob 1 DeclarationA SiteA) LNil)))))))))

!(let $actual
  (gslt:sites:generate
    (LCons (GrammarTypingV1 "id" "Expr" (LCons (TermSimple "x" (TBase "Expr")) LNil))
      (LCons (GrammarTypingV1 "id" "Expr" (LCons (TermSimple "x" (TBase "Expr")) LNil)) LNil))
    (LCons (Binding "v" (TBase "Expr")) LNil)
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionNo PermissionNo LNil)
    LNil (TBase "Expr") (PApp "id" (LCons (FVar "v") LNil)))
  (println! (TypedSitesControl "overloaded-declarations-retain-both-typing-witnesses"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole (PApp "id" (LCons (FVar "v") LNil)) LNil (TBase "Expr") LNil)
      (LCons (RuleJobSite (LCons 0 LNil) (ContextApp "id" LNil ContextHole LNil)
        (FVar "v") LNil (TBase "Expr") (LCons (TypingApplication 0 0) LNil))
      (LCons (RuleJobSite (LCons 0 LNil) (ContextApp "id" LNil ContextHole LNil)
        (FVar "v") LNil (TBase "Expr") (LCons (TypingApplication 1 0) LNil)) LNil))))))))

!(let $actual
  (gslt:sites:generate
    (LCons (GrammarTypingV1 "id" "Expr" (LCons (TermSimple "x" (TBase "Expr")) LNil)) LNil)
    (LCons (Binding "v" (TBase "Expr")) LNil)
    (OperationalPermissions PermissionYes PermissionNo (LCons (TermSlot "other" 0) LNil) PermissionNo PermissionNo LNil)
    LNil (TBase "Expr") (PApp "id" (LCons (FVar "v") LNil)))
  (println! (TypedSitesControl "unlicensed-argument-refuses-descent"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole (PApp "id" (LCons (FVar "v") LNil)) LNil (TBase "Expr") LNil) LNil))))))

!(let $actual
  (gslt:sites:generate LNil (LCons (Binding "v" (TBase "Expr")) LNil)
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionNo PermissionNo
      (LCons "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" LNil))
    LNil (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Expr"))
    (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (FVar "v") (LCons (FVar "v") LNil)) RNone))
  (println! (TypedSitesControl "hashbag-duplicates-retain-physical-positions"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole
        (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (FVar "v") (LCons (FVar "v") LNil)) RNone)
        LNil (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Expr")) LNil)
      (LCons (RuleJobSite (LCons 0 LNil)
        (ContextCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" LNil ContextHole (LCons (FVar "v") LNil) RNone)
        (FVar "v") LNil (TBase "Expr")
        (LCons (TypingDirectCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag") LNil))
      (LCons (RuleJobSite (LCons 1 LNil)
        (ContextCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (FVar "v") LNil) ContextHole LNil RNone)
        (FVar "v") LNil (TBase "Expr")
        (LCons (TypingDirectCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag") LNil)) LNil))))))))

!(let $actual
  (gslt:sites:generate
    (LCons (GrammarTypingV1 "Bag" "BagExpr"
      (LCons (TermSimple "xs" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Expr"))) LNil))
    (LCons (GrammarTypingV1 "OtherBag" "BagExpr"
      (LCons (TermSimple "xs" (TCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (TBase "Expr"))) LNil)) LNil))
    (LCons (Binding "v" (TBase "Expr")) LNil)
    (OperationalPermissions PermissionYes PermissionYes LNil PermissionNo PermissionNo
      (LCons "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" LNil))
    LNil (TBase "BagExpr")
    (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (FVar "v") LNil) RNone))
  (println! (TypedSitesControl "authored-collection-alternatives-stay-ordered"
    (== $actual (quote
      (LCons (RuleJobSite LNil ContextHole
        (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" (LCons (FVar "v") LNil) RNone)
        LNil (TBase "BagExpr") LNil)
      (LCons (RuleJobSite (LCons 0 LNil)
        (ContextCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" LNil ContextHole LNil RNone)
        (FVar "v") LNil (TBase "Expr") (LCons (TypingAuthoredCollection 0) LNil))
      (LCons (RuleJobSite (LCons 0 LNil)
        (ContextCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" LNil ContextHole LNil RNone)
        (FVar "v") LNil (TBase "Expr") (LCons (TypingAuthoredCollection 1) LNil)) LNil))))))))
