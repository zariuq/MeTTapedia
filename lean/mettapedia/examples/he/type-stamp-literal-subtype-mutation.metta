; A literal subtype insertion already advances the declaration revision.
(: h H)
(: a N)
(: b S)
(:< Unrelated Top)
!(let $warm (new-state (h a))
   (let $target (new-state (h b))
     (let $added (add-atom &self (:< (H N) (H S)))
       (change-state! $target (h a)))))
