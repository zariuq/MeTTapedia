(sat 1 7)
(sat 1 7)
(sat 1 8)

(= (present $tag $node)
  (not (== (collapse (once (match &self (sat $tag $node) t))) ())))

!(let $tag 1 (let $node 7 (collapse (once (match &self (sat $tag $node) t)))))
!(let $tag 1 (let $node 9 (collapse (once (match &self (sat $tag $node) t)))))
!(let $node $shared (let $shared 7
  (collapse (once (match &self (sat 1 $node) t)))))
!(collapse (let $node 7
  (let $packet (collapse (once (match &self (sat 1 $node) t))) (quote ($node $packet)))))
!(present 1 7)
!(present 1 9)
