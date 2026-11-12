(: CompletionExprBox (-> Number Expression))
(: CompletionData (-> Number CompletionDataType))
(: CompletionCoupled (-> $t $t CompletionResult))

!(CompletionCoupled (CompletionExprBox 1) (CompletionData 7))
