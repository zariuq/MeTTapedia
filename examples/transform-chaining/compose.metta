; Compose two supplied relations and retain the intermediate value and both receipts.
!(bind! &facts (new-space))
!(add-atom &facts (edge mother alice bob l1 mother-proof report))
!(add-atom &facts (edge mother alice bob l2 mother-proof report))
!(add-atom &facts (edge father bob carol r1 father-proof certain))
!(add-atom &facts (edge father dana carol bad wrong-proof certain))
!(add-atom &facts (edge rail east hub l3 rail-proof timetable))
!(add-atom &facts (edge ferry hub west r2 ferry-proof schedule))

(= (compose $r $s $x $z)
   (transform &facts (, (read (edge $r $x $y $i $p $a))
                         (read (edge $s $y $z $j $q $b)))
      (witness $x $y $z $i $j $p $q $a $b)))

(= (ordinary $r $s $x $z)
   (match &facts (, (edge $r $x $y $i $p $a)
                    (edge $s $y $z $j $q $b))
      (witness $x $y $z $i $j $p $q $a $b)))

!(reset-runtime-stats!)
!(prepared-family (collapse (compose mother father alice carol)))
!(ordinary-family (collapse (ordinary mother father alice carol)))
!(first-family (once (compose mother father alice carol)))
!(prepared-route (collapse (compose rail ferry east west)))
!(ordinary-route (collapse (ordinary rail ferry east west)))
!(reversed (collapse (compose father mother alice carol)))

; A composed relation can supply either argument of the same operation.
!(bind! &relations (new-space))
!(transform &facts (read (edge $r $x $y $i $p $a))
   (holds $r $x $y (leaf $i $p $a)) &relations)
!(add-atom &relations (holds bus west pier (leaf r3 bus-proof schedule)))
(= (derive $r $s)
   (transform &relations (, (read (holds $r $x $m $p)) (read (holds $s $m $z $q)))
     (holds (then $r $s) $x $z (via $m $p $q)) &relations))
!(derive rail ferry)
!(derive (then rail ferry) bus)
!(nested (collapse (match &relations (holds (then (then rail ferry) bus) east pier $p) $p)))

