(: CachedGuardBox (-> Number CachedGuardRange))
(: cached-guard-body (-> %Undefined% CachedGuardRange))
(= (cached-guard-body $value) (CachedGuardBox $value))

!(cached-guard-body 7)
!(add-atom &self (: (CachedGuardBox "wrong-field") CachedGuardRange))
!(cached-guard-body "wrong-field")
