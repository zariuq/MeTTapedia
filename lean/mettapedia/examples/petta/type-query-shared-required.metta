; A bound query refines a shared variable before reading its next subject.
(: Number Type)
!(collapse (let ($x String) (get-type (1 $x)) $x))

; A genuinely fresh query followed by a separate match is a different program.
!(collapse (let $types (get-type (1 $x)) (let ($x String) $types $x)))
