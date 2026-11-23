; Calibration fixture: transitivity retains its two source hypotheses.
; Standard-policy acceptance and a hypothesis-free conclusion are separate.
!(import! &self holkernel)

(= (relative-trans-service:check $certificate)
  (let $kernel (hol:kernel standard)
    (case (hol:replay $kernel $certificate)
      (((hol:accepted $records $roots)
         (let $theorem (hol:theorem $kernel "RELATIVE_TRANS")
           (RelativeTransService
             (hol:accepted $records $roots)
             (SourceSequent (hol:text $theorem))
             (StandardPolicy (hol:standard $theorem)))))
       ($other $other)))))
