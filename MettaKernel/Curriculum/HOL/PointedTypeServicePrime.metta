; Calibration fixture: retrieve both laws of a natively checked pointed type.
; The certificate retains the witness DAG and the actual type-definition step.
; This is kernel-service access; typed transport into a hol: space is separate.
!(import! &self holkernel)

(= (pointed-type-service:check $certificate)
  (let $kernel (hol:kernel standard)
    (case (hol:replay $kernel $certificate)
      (((hol:accepted $records $roots)
         (PointedTypeService
           (hol:accepted $records $roots)
           (hol:standard (hol:theorem $kernel "POINTED_ABS_REP"))
           (hol:standard (hol:theorem $kernel "POINTED_REP_ABS"))))
       ($other $other)))))
