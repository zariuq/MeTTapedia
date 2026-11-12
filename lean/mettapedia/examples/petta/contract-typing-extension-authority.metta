; Authored type-query alternatives remain part of each relational guard.
(= (get-type $value) Number)
(: authority-inner (-> Number Number))
(= (authority-inner $value) $value)
(: authority-outer (-> Number Number))
(= (authority-outer $value) (authority-inner $value))
!(collapse (get-type 1))
!(collapse (authority-inner 1))
!(collapse (authority-outer 1))
