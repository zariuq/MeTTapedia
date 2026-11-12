(sat 1 7)
(sat 1 7)
(sat 1 8)

!(let $saved kept (let $packet (collapse (once (match &self (sat 1 7) true))) (Pair $saved $packet)))
!(let $saved kept (let $packet (collapse (once (match &self (sat 1 9) true))) (Pair $saved $packet)))
!(collapse (match &self (sat 1 7) true))
!(let $ignored (println! prefix) (let $saved kept (let $packet (collapse (once (match &self (sat 1 7) true))) (Pair $saved $packet))))
