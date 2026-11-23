!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "Mettapedia/hol_light/Transform/admission.holr")))
    ((hol:sequent (hol:theorem $k "TC_PREPARED_IS_SEMANTIC")) (hol:sequent (hol:theorem $k "TC_RELAXED_PERMISSION_CAN_BREAK_INVARIANT"))))
