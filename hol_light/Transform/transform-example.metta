!(import! &self holkernel)
!(let* (($k (hol:kernel standard))
        ($_ (hol:replay $k "Mettapedia/hol_light/Transform/transform.holr")))
    ((hol:sequent (hol:theorem $k "TC_SOUND_COMPOSE")) (hol:sequent (hol:theorem $k "TC_OBSERVER_CAN_FORGET_ENDPOINT"))))
