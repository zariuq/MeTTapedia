!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "parallel-traces.holr")))
    ((hol:sequent (hol:theorem $k "TC_TRACE_OBSERVER_DESCENT")) (hol:sequent (hol:theorem $k "TC_TRACE_EQUAL_ENDPOINTS_DISTINCT"))))
