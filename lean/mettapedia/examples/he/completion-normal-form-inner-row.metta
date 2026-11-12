(: CompletionNil (CompletionList $a))
(: CompletionWrap (-> Number CompletionW))
(: (CompletionWrap 1) CompletionFoo)
(: CompletionCons (-> $a (CompletionList $a) (CompletionList $a)))

!(CompletionCons (CompletionWrap 1) CompletionNil)
