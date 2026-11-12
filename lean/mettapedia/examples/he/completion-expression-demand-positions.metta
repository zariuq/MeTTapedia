(: CompletionExprBox (-> Number Expression))
(: completion-number (-> Number))
(= (completion-number) 7)
(: CompletionCoupled (-> $t $t CompletionResult))

!(CompletionCoupled (CompletionExprBox (completion-number)) (CompletionExprBox (completion-number)))
