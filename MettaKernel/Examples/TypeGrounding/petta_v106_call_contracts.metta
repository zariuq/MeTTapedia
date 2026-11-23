; External-oracle controls for PeTTa v1.0.6's translated call contracts.
(: takes-number (-> Number Bool))
(= (takes-number $value) true)
!(collapse (takes-number 3))
!(collapse (takes-number "bad"))

(: wrong-result (-> Number))
(= (wrong-result) "bad")
!(collapse (wrong-result))

(: as-data (-> Atom Atom))
(= (as-data $value) $value)
!(as-data (+ 1 2))
