; Calibration fixture: initializer-effect-on-clash
!(let $s (new-space)
   (let $answers (collapse (let expected (let $_ (add-atom $s (seen)) actual) unreachable))
     (let $seen (collapse (match $s (seen) yes))
       (result $answers $seen))))
