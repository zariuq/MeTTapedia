; A structural match rejected by the caller's constraints takes the else
; branch and retains the original caller bindings. Expected: (Else A).
!(function
  (chain (unify $x A Bound Refused) $first
    (chain (unify $x B Wrong Else) $branch
      (return ($branch $x)))))

; Without the conflicting caller constraint the same match succeeds.
; Expected: (Then B).
!(function
  (chain (unify $x B Then Wrong) $branch
    (return ($branch $x))))
