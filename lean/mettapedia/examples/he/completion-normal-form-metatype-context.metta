(: CompletionExpressionWitness Expression)
(: CompletionData (-> Number CompletionDataType))
(: CompletionCoupled (-> $t $t CompletionResult))
(: CompletionUse (-> CompletionResult Number))
(= (CompletionUse $value) 7)

!(CompletionUse (CompletionCoupled CompletionExpressionWitness (CompletionData 7)))
