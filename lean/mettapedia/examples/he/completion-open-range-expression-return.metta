(: CompletionExprBox (-> Number Expression))
(: completion-number (-> Number))
(= (completion-number) 7)
(: completion-return-id (-> $t $t))
(= (completion-return-id $value) $value)

!(completion-return-id (CompletionExprBox (completion-number)))
