; Independent commits may exchange order. A guard can prevent that exchange
; even when the two commits consume different resources.
!(import! &self (library lib_transform))

(= (rc:view $board) (sort-atom (collapse (match $board $row $row))))
(= (rc:move $board $id)
   (collapse (transform $board (take (Pending $id $value)) (Done $id $value) $board)))

!(bind! &rc-ab (new-space))
!(bind! &rc-ba (new-space))
!(add-atom &rc-ab (Pending a same))
!(add-atom &rc-ab (Pending b same))
!(add-atom &rc-ba (Pending a same))
!(add-atom &rc-ba (Pending b same))
!(rc:move &rc-ab a)
!(rc:move &rc-ab b)
!(rc:move &rc-ba b)
!(rc:move &rc-ba a)
!(println! (IndependentOrdersAgree (== (rc:view &rc-ab) (rc:view &rc-ba))))
!(println! (BothOriginsRetained (== (rc:view &rc-ab) ((Done a same) (Done b same)))))

; The two events have the same visible label but different origins.
(= (rc:exchange ($first $second)) ($second $first))
!(println! (ExchangedOrigins (rc:exchange ((Event 0 copy) (Event 1 copy)))))

(= (rc:observe $board)
   (collapse (transform $board
     (, (take (Pending observe)) (absent (Blocked))) (Observed) $board)))
(= (rc:block $board)
   (collapse (transform $board (take (Pending block)) (Blocked) $board)))

!(bind! &rc-before (new-space))
!(bind! &rc-after (new-space))
!(add-atom &rc-before (Pending observe))
!(add-atom &rc-before (Pending block))
!(add-atom &rc-after (Pending observe))
!(add-atom &rc-after (Pending block))
!(rc:observe &rc-before)
!(rc:block &rc-before)
!(rc:block &rc-after)
!(rc:observe &rc-after)
!(println! (GuardedOrderDiffers (not (== (rc:view &rc-before) (rc:view &rc-after)))))
!(println! (RefusalKeepsPending
   (== (collapse (match &rc-after (Pending observe) still-pending)) (still-pending))))

; A replay has no Pending resource to consume and cannot publish another row.
!(println! (ReplayRefused (== (rc:move &rc-ab a) ())))
!(println! (ReplayKeepsResult (== (rc:view &rc-ab) ((Done a same) (Done b same)))))
