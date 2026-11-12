(: AssertedBox (-> Number AssertedRange))
(: (AssertedBox "wrong-field") AssertedRange)
(: asserted-body (-> AssertedRange))
(= (asserted-body) (AssertedBox "wrong-field"))

!(get-type (AssertedBox "wrong-field"))
!(asserted-body)
