!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "parallel.holr")))
    ((hol:sequent (hol:theorem $k "TC_PAR_STORE_ASSOC")) (hol:sequent (hol:theorem $k "TC_PAR_TAKE_DESTROYS_CONTEXT"))))
