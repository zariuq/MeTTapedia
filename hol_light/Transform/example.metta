!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "Mettapedia/hol_light/Transform/core.holr")))
    ((hol:sequent (hol:theorem $k "TC_SOUND_COMPOSE")) (hol:sequent (hol:theorem $k "TC_FRESH_TARGET_NOT_SAME_TARGET"))))
