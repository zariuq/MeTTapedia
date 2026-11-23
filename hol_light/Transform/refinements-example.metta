!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "Mettapedia/hol_light/Transform/refinements.holr")))
    ((hol:sequent (hol:theorem $k "TC_SEPARATES_UNION")) (hol:sequent (hol:theorem $k "TC_ANSWER_OBSERVER_CAN_FORGET"))))
