; Calibration fixture for MainlineTypeQueryEnumeration and MainlineTypeQueryModes.
; These are source-engine queries, not an implementation of a type checker.
(: a A)
(: b B)
(: f (-> A C))
(: wildcard (-> %Undefined% C))
!(get-type (f a))
!(get-type (f b))
!(get-type (wildcard 3))
!(get-type 3)
!(get-type (f a a))
(: repeated A)
(: repeated A)
!(get-type (f repeated))
