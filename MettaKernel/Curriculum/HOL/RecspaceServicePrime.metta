; Calibration fixture: opaque access to natively checked recursive-space facts.
; The certificate supplies the labelled primitive proof DAG. This module uses
; the kernel service; it does not transport type definitions into a hol: space.
!(import! &self holkernel)

(= (recspace-service:check $certificate)
  (let $kernel (hol:kernel standard)
    (case (hol:replay $kernel $certificate)
      (((hol:accepted $records $roots)
         (RecspaceService
           (hol:accepted $records $roots)
           (hol:standard (hol:theorem $kernel "CONSTR_BOT"))
           (hol:standard (hol:theorem $kernel "CONSTR_INJ"))
           (hol:standard (hol:theorem $kernel "CONSTR_IND"))
           (hol:standard (hol:theorem $kernel "CONSTR_REC"))))
       ($other $other)))))
