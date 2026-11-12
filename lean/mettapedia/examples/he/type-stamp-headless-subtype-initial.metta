; A headless row present before admission is caught by the fresh open-row flag.
(: h H)
(: a N)
(: b S)
(:< Unrelated Top)
($row-head (H N) (H S))
!(let $warm (new-state (h a))
   (let $target (new-state (h b))
     (change-state! $target (h a))))
