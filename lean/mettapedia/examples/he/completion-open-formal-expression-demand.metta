(: CompletionExprBox (-> Number Expression))
(: completion-number (-> Number))
(= (completion-number) 7)
(: CompletionCoupled (-> $t $t CompletionResult))

!(CompletionCoupled (CompletionExprBox 1) (CompletionExprBox (completion-number)))
