!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "parallel-domains.holr")))
    ((hol:sequent (hol:theorem $k "TC_PREPARED_WORD_TARGET_APPEND")) (hol:sequent (hol:theorem $k "TC_PREPARED_WORD_DOMAIN_APPEND"))))
