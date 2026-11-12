!(let $s (new-space)
  (let $answer (collapse (let False (add-atom $s (touched)) (quote impossible)))
    (let $rows (collapse (match $s (touched) t))
      (quote ($answer $rows)))))
