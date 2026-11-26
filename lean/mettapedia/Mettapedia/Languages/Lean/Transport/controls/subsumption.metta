; Controls for the instance matcher: each prints (control NAME ok/FAILED).
(= (ctl $c_name $c_got $c_want) (println! (control $c_name (if (== $c_got $c_want) ok (FAILED (got $c_got) (want $c_want))))))
; add_comm's statement is no pattern for add_left_comm's: v_n would need two values
!(ctl repeated-variable
      (subsume:match (app Eq ((app Nat ()) (app Nat.add ((var v_n) (var v_m))) (app Nat.add ((var v_m) (var v_n)))))
                (app Eq ((app Nat ()) (app Nat.add ((var v_n) (app Nat.add ((var v_m) (var v_k))))) (app Nat.add ((var v_m) (app Nat.add ((var v_n) (var v_k)))))))
                (v_n v_m) () 0)
      Fail)
; a renaming is an instance
!(ctl renaming
      (subsume:match (app Eq ((app Nat ()) (app Nat.add ((var v_n) (var v_m))) (app Nat.add ((var v_m) (var v_n)))))
                (app Eq ((app Nat ()) (app Nat.add ((var v_a) (var v_b))) (app Nat.add ((var v_b) (var v_a)))))
                (v_n v_m) () 0)
      ((v_m (var v_b)) (v_n (var v_a))))
; a variable cannot stand for something that names a binder of the statement
!(ctl capture (subsume:match (lam x (app Nat ()) (app f ((dbv 0) (var v_n)))) (lam y (app Nat ()) (app f ((dbv 0) (dbv 0)))) (v_n) () 0) Fail)
; nor can a binder of one kind stand for another
!(ctl binder-kind (subsume:match (lam x (app Nat ()) (app f ())) (pi x (app Nat ()) (app f ())) () () 0) Fail)

!(ctl local-argument
      (subsume:complete-binders ((term count (app Nat ())))
        ((term available (app Nat ()))) (count) ())
      ((count (var available))))
!(ctl absent-instance
      (subsume:complete-binders ((term instance (app Decidable ((var p)))))
        ((term p (app Prop ()))) (instance p) ((p (var p))))
      Fail)
!(ctl recover-dependent-type
      (let $sig (subsume:propagate-binder-types
         ((type carrier lzero) (term value (var carrier)))
         ((term n (app Nat ()))) (carrier value) ((value (var n))))
         (subsume:lookup carrier $sig))
      (app Nat ()))
