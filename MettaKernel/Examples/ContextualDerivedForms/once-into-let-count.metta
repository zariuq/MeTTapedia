; Regression: the take and destination write succeed; the count must reach let.
!(bind! &q (new-space))
!(bind! &out (new-space))
!(let $ignored (add-atom &q (job a)) (empty))
!(let $n (once (transform &q (take (job $j)) (done $j) &out)) (observed $n))
!(collapse (match &out (done $j) $j))
