; A valid constructor's structural range and its whole-value annotation differ.
(: AscribedRangeBox (-> Number ActualBoxRange))
(: (AscribedRangeBox 1) ClaimedBoxRange)
(: use-actual-box (-> ActualBoxRange ActualBoxRange))
(= (use-actual-box $value) $value)
(: use-claimed-box (-> ClaimedBoxRange ClaimedBoxRange))
(= (use-claimed-box $value) $value)
(: make-ascribed-box (-> ActualBoxRange))
(= (make-ascribed-box) (AscribedRangeBox 1))
!(get-type (AscribedRangeBox 1))
!(use-actual-box (AscribedRangeBox 1))
!(use-actual-box (make-ascribed-box))
; Keep the deliberate type error last: the file runner stops after an error.
!(use-claimed-box (AscribedRangeBox 1))
