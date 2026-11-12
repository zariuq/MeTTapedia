; Distinct anonymous occurrences versus repeated named occurrences.
!(let $parsed (parse "(Pair $_ $_)")
   (let (Pair $a $b) $parsed (== $a $b)))
!(let $parsed (parse "(Pair $x $x)")
   (let (Pair $a $b) $parsed (== $a $b)))
