!(bind! &jobs (new-space))
!(add-atom &jobs (exec first (,) (O (+ (unresolved $outside)))))
!(select 100 (search-policy (control FIFO (resources MM2) (budget 100000))) &jobs)
!(collapse (get-atoms &jobs))
