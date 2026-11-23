!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "Mettapedia/hol_light/Transform/runs-admission.holr")))
    ((hol:sequent (hol:theorem $k "TC_PREPARED_IS_SEMANTIC")) (hol:sequent (hol:theorem $k "TC_RUN_PULLBACK_CONS"))))
