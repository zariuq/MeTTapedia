; A newly added headless row can change the full subtype query.
(: h H)
(: a N)
(: b S)
(:< Unrelated Top)
!(let $warm (new-state (h a))
   (let $target (new-state (h b))
     (let $added (add-atom &self ($row-head (H N) (H S)))
       (change-state! $target (h a)))))
