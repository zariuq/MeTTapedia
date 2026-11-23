; Radó two-state table: native PeTTa driver smoke checks.
; Run/At/Cell encode ordered tape data; Next requests one table step.
; The recursive driver returns data when no equation answers.
; Source table: Mettapedia.Languages.TuringMachine.ClassicMachines.busyBeaver2.
!(println! "BEGIN table driver")
(= (Next (Run QZero (At $l SZero (Cell $c $r)))) (Run (QSucc QZero) (At (Cell (SSucc SZero) $l) $c $r)))
(= (Next (Run QZero (At $l SZero Empty))) (Run (QSucc QZero) (At (Cell (SSucc SZero) $l) SZero Empty)))
(= (Next (Run QZero (At (Cell $c $l) (SSucc SZero) $r))) (Run (QSucc QZero) (At $l $c (Cell (SSucc SZero) $r))))
(= (Next (Run QZero (At Empty (SSucc SZero) $r))) (Run (QSucc QZero) (At Empty SZero (Cell (SSucc SZero) $r))))
(= (Next (Run (QSucc QZero) (At (Cell $c $l) SZero $r))) (Run QZero (At $l $c (Cell (SSucc SZero) $r))))
(= (Next (Run (QSucc QZero) (At Empty SZero $r))) (Run QZero (At Empty SZero (Cell (SSucc SZero) $r))))
(= (Next (Run (QSucc QZero) (At $l (SSucc SZero) (Cell $c $r)))) (Run (QSucc (QSucc QZero)) (At (Cell (SSucc SZero) $l) $c $r)))
(= (Next (Run (QSucc QZero) (At $l (SSucc SZero) Empty))) (Run (QSucc (QSucc QZero)) (At (Cell (SSucc SZero) $l) SZero Empty)))
(= (Execute $c) (case (collapse (Next $c)) ((() $c) (($n) (Execute $n)))))
!(println! (Execute (Run QZero (At Empty SZero Empty))))
!(test (Execute (Run QZero (At Empty SZero Empty))) (Run (QSucc (QSucc QZero)) (At (Cell (SSucc SZero) (Cell (SSucc SZero) Empty)) (SSucc SZero) (Cell (SSucc SZero) Empty))))
!(test (Execute (Run QZero (At Empty (SSucc (SSucc SZero)) Empty))) (Run QZero (At Empty (SSucc (SSucc SZero)) Empty)))
!(println! "END table driver")
