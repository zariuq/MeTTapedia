;; Generated recursion interfaces; statements come from checked Lean declarations.
(LeanWfRecursion
  Nat.gcd
  (Method measure)
  (ProofArguments ())
  (Implementation Nat.gcd._unary)
  (Relation Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.functionBridge)
  (Equations ((Nat.gcd.eq_1 Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.equation0)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Decreases)
        (SourceProofs (_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary._proof_1))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ())))))

(LeanRecursionSourceType Nat.gcd (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.measure
  (Type (arrow (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ())))
  (Value
    (lam
      v_x
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (app
        PSigma.casesOn
        ((app Nat ())
          (lam v_m (app Nat ()) (app Nat ()))
          (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
          (var v_x)
          (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.relation
  (Type
    (arrow
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (arrow (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (prop))))
  (Value
    (lam
      v_a
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (lam
        v_x1
        (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
        (app
          Nat.le
          ((app
              Nat.succ
              ((app
                  PSigma.casesOn
                  ((app Nat ())
                    (lam v_m (app Nat ()) (app Nat ()))
                    (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                    (var v_a)
                    (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
            (app
              PSigma.casesOn
              ((app Nat ())
                (lam v_m (app Nat ()) (app Nat ()))
                (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                (var v_x1)
                (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.recipe
  (Type
    (pi
      v__x
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (arrow
        (pi
          v_y
          (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
          (arrow
            (app
              Nat.le
              ((app
                  Nat.succ
                  ((app
                      PSigma.casesOn
                      ((app Nat ())
                        (lam v_m (app Nat ()) (app Nat ()))
                        (lam v_x2 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                        (var v_y)
                        (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                (app
                  PSigma.casesOn
                  ((app Nat ())
                    (lam v_m (app Nat ()) (app Nat ()))
                    (lam v_x2 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                    (var v__x)
                    (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
            (app Nat ())))
        (app Nat ()))))
  (Value
    (lam
      v__x
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (lam
        v_a
        (pi
          v_y
          (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
          (arrow
            (app
              Nat.le
              ((app
                  Nat.succ
                  ((app
                      PSigma.casesOn
                      ((app Nat ())
                        (lam v_m (app Nat ()) (app Nat ()))
                        (lam v_x2 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                        (var v_y)
                        (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                (app
                  PSigma.casesOn
                  ((app Nat ())
                    (lam v_m (app Nat ()) (app Nat ()))
                    (lam v_x2 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                    (var v__x)
                    (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
            (app Nat ())))
        (app
          PSigma.casesOn
          ((app Nat ())
            (lam v_m (app Nat ()) (app Nat ()))
            (lam
              v_x2
              (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
              (arrow
                (pi
                  v_y
                  (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                  (arrow
                    (app
                      Nat.le
                      ((app
                          Nat.succ
                          ((app
                              PSigma.casesOn
                              ((app Nat ())
                                (lam v_m (app Nat ()) (app Nat ()))
                                (lam v_x4 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                                (var v_y)
                                (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                        (app
                          PSigma.casesOn
                          ((app Nat ())
                            (lam v_m (app Nat ()) (app Nat ()))
                            (lam v_x4 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                            (var v_x2)
                            (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                    (app Nat ())))
                (app Nat ())))
            (var v__x)
            (lam
              v_m
              (app Nat ())
              (lam
                v_n
                (app Nat ())
                (lam
                  v_x4
                  (pi
                    v_y
                    (app PSigma ((app Nat ()) (lam v_x4 (app Nat ()) (app Nat ()))))
                    (arrow
                      (app
                        Nat.le
                        ((app
                            Nat.succ
                            ((app
                                PSigma.casesOn
                                ((app Nat ())
                                  (lam v_x5 (app Nat ()) (app Nat ()))
                                  (lam
                                    v_x5
                                    (app PSigma ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ()))))
                                    (app Nat ()))
                                  (var v_y)
                                  (lam v_x5 (app Nat ()) (lam v_x6 (app Nat ()) (var v_x5)))))))
                          (app
                            PSigma.casesOn
                            ((app Nat ())
                              (lam v_x5 (app Nat ()) (app Nat ()))
                              (lam v_x5 (app PSigma ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ())))) (app Nat ()))
                              (app PSigma.mk ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                              (lam v_x5 (app Nat ()) (lam v_x6 (app Nat ()) (var v_x5)))))))
                      (app Nat ())))
                  (app
                    dite
                    ((app Nat ())
                      (app Eq ((app Nat ()) (var v_m) (num 0)))
                      (app instDecidableEqNat ((var v_m) (num 0)))
                      (lam v_h (app Eq ((app Nat ()) (var v_m) (num 0))) (var v_n))
                      (lam
                        v_h
                        (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
                        (apv
                          (var v_x4)
                          ((app
                              PSigma.mk
                              ((app Nat ())
                                (lam v_x6 (app Nat ()) (app Nat ()))
                                (app Nat.mod ((var v_n) (var v_m)))
                                (var v_m)))
                            (proof)))))))))
            (var v_a)))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.wellFounded
  (app
    WellFounded
    ((app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (lam
        v_a
        (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
        (lam
          v_x1
          (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
          (app
            Nat.le
            ((app
                Nat.succ
                ((app
                    PSigma.casesOn
                    ((app Nat ())
                      (lam v_m (app Nat ()) (app Nat ()))
                      (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                      (var v_a)
                      (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
              (app
                PSigma.casesOn
                ((app Nat ())
                  (lam v_m (app Nat ()) (app Nat ()))
                  (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                  (var v_x1)
                  (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.bridge
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.accessible ((var v_m) (var v_n)))
          (app Nat.gcd ((var v_m) (var v_n)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.functionBridge
  (app
    Eq
    ((arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))
      (lam
        v_m
        (app Nat ())
        (lam
          v_n
          (app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.accessible ((var v_m) (var v_n)))))
      (lam v_m (app Nat ()) (lam v_n (app Nat ()) (app Nat.gcd ((var v_m) (var v_n)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.gcd.eq_1
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.gcd ((var v_m) (var v_n)))
          (app
            ite
            ((app Nat ())
              (app Eq ((app Nat ()) (var v_m) (num 0)))
              (app instDecidableEqNat ((var v_m) (num 0)))
              (var v_n)
              (app Nat.gcd ((app Nat.mod ((var v_n) (var v_m))) (var v_m)))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.equation0
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.accessible ((var v_m) (var v_n)))
          (app
            ite
            ((app Nat ())
              (app Eq ((app Nat ()) (var v_m) (num 0)))
              (app instDecidableEqNat ((var v_m) (num 0)))
              (var v_n)
              (app
                Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.accessible
                ((app Nat.mod ((var v_n) (var v_m))) (var v_m)))))))))
  (Axioms (Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Current
  (Type
    (pi
      v_m
      (app Nat ())
      (arrow
        (app Nat ())
        (arrow
          (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
          (app PSigma ((app Nat ()) (lam v_x1 (app Nat ()) (app Nat ()))))))))
  (Value
    (lam
      v_m
      (app Nat ())
      (lam
        v_n
        (app Nat ())
        (lam
          v_h
          (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
          (app PSigma.mk ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())) (var v_m) (var v_n))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Argument
  (Type
    (pi
      v_m
      (app Nat ())
      (arrow
        (app Nat ())
        (arrow
          (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
          (app PSigma ((app Nat ()) (lam v_x1 (app Nat ()) (app Nat ()))))))))
  (Value
    (lam
      v_m
      (app Nat ())
      (lam
        v_n
        (app Nat ())
        (lam
          v_h
          (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
          (app
            PSigma.mk
            ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())) (app Nat.mod ((var v_n) (var v_m))) (var v_m))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.Gcd.call0Decreases
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (arrow
        (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
        (app
          Nat.le
          ((app
              Nat.succ
              ((app
                  PSigma.casesOn
                  ((app Nat ())
                    (lam v_x2 (app Nat ()) (app Nat ()))
                    (lam v__x (app PSigma ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())))) (app Nat ()))
                    (app
                      PSigma.mk
                      ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())) (app Nat.mod ((var v_n) (var v_m))) (var v_m)))
                    (lam v_x2 (app Nat ()) (lam v_x3 (app Nat ()) (var v_x2)))))))
            (app
              PSigma.casesOn
              ((app Nat ())
                (lam v_x2 (app Nat ()) (app Nat ()))
                (lam v__x (app PSigma ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())))) (app Nat ()))
                (app PSigma.mk ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                (lam v_x2 (app Nat ()) (lam v_x3 (app Nat ()) (var v_x2))))))))))
  (Axioms ()))

(LeanWfRecursion
  List.mergeSort
  (Method measure)
  (ProofArguments ())
  (Implementation List.mergeSort._unary)
  (Relation Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.functionBridge)
  (Equations
    ((List.mergeSort.eq_1 Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation0)
      (List.mergeSort.eq_2 Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation1)
      (List.mergeSort.eq_3 Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation2)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Decreases)
        (SourceProofs (_private.Init.Data.List.Sort.Basic.0.List.mergeSort._unary._proof_4))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ()))
      (call
        (Current Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Current)
        (Argument Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Decreases)
        (SourceProofs (_private.Init.Data.List.Sort.Basic.0.List.mergeSort._unary._proof_5))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ())))))

(LeanRecursionSourceType
  List.mergeSort
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (arrow
      (app List ((var v_u945)))
      (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.measure
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (app Nat ()))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_x
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (app
          PSigma.casesOn
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
            (lam
              v__x
              (app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
              (app Nat ()))
            (var v_x)
            (lam
              v_xs
              (app List ((var v_u945)))
              (lam
                v_le
                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                (app List.length ((var v_u945) (var v_xs)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.relation
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (arrow
          (app
            PSigma
            ((app List ((var v_u945)))
              (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
          (prop)))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (lam
          v_x2
          (app
            PSigma
            ((app List ((var v_u945)))
              (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
          (app
            Nat.le
            ((app
                Nat.succ
                ((app
                    PSigma.casesOn
                    ((app List ((var v_u945)))
                      (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (lam
                        v__x
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (app Nat ()))
                      (var v_a)
                      (lam
                        v_xs
                        (app List ((var v_u945)))
                        (lam
                          v_le
                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                          (app List.length ((var v_u945) (var v_xs)))))))))
              (app
                PSigma.casesOn
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                  (lam
                    v__x
                    (app
                      PSigma
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                    (app Nat ()))
                  (var v_x2)
                  (lam
                    v_xs
                    (app List ((var v_u945)))
                    (lam
                      v_le
                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                      (app List.length ((var v_u945) (var v_xs))))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.recipe
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v__x
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (arrow
          (pi
            v_y
            (app
              PSigma
              ((app List ((var v_u945)))
                (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
            (arrow
              (app
                Nat.le
                ((app
                    Nat.succ
                    ((app
                        PSigma.casesOn
                        ((app List ((var v_u945)))
                          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                          (lam
                            v_x3
                            (app
                              PSigma
                              ((app List ((var v_u945)))
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                            (app Nat ()))
                          (var v_y)
                          (lam
                            v_xs
                            (app List ((var v_u945)))
                            (lam
                              v_le
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                              (app List.length ((var v_u945) (var v_xs)))))))))
                  (app
                    PSigma.casesOn
                    ((app List ((var v_u945)))
                      (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (lam
                        v_x3
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (app Nat ()))
                      (var v__x)
                      (lam
                        v_xs
                        (app List ((var v_u945)))
                        (lam
                          v_le
                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                          (app List.length ((var v_u945) (var v_xs)))))))))
              (app List ((var v_u945)))))
          (app List ((var v_u945)))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v__x
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (lam
          v_a
          (pi
            v_y
            (app
              PSigma
              ((app List ((var v_u945)))
                (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
            (arrow
              (app
                Nat.le
                ((app
                    Nat.succ
                    ((app
                        PSigma.casesOn
                        ((app List ((var v_u945)))
                          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                          (lam
                            v_x3
                            (app
                              PSigma
                              ((app List ((var v_u945)))
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                            (app Nat ()))
                          (var v_y)
                          (lam
                            v_xs
                            (app List ((var v_u945)))
                            (lam
                              v_le
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                              (app List.length ((var v_u945) (var v_xs)))))))))
                  (app
                    PSigma.casesOn
                    ((app List ((var v_u945)))
                      (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (lam
                        v_x3
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (app Nat ()))
                      (var v__x)
                      (lam
                        v_xs
                        (app List ((var v_u945)))
                        (lam
                          v_le
                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                          (app List.length ((var v_u945) (var v_xs)))))))))
              (app List ((var v_u945)))))
          (app
            PSigma.casesOn
            ((app List ((var v_u945)))
              (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
              (lam
                v_x3
                (app
                  PSigma
                  ((app List ((var v_u945)))
                    (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                (arrow
                  (pi
                    v_y
                    (app
                      PSigma
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                    (arrow
                      (app
                        Nat.le
                        ((app
                            Nat.succ
                            ((app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                  (lam
                                    v_x5
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_xs
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                    (app Nat ()))
                                  (var v_y)
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (lam
                                      v_le
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                      (app List.length ((var v_u945) (var v_xs)))))))))
                          (app
                            PSigma.casesOn
                            ((app List ((var v_u945)))
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                              (lam
                                v_x5
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_xs
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                (app Nat ()))
                              (var v_x3)
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (lam
                                  v_le
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                  (app List.length ((var v_u945) (var v_xs)))))))))
                      (app List ((var v_u945)))))
                  (app List ((var v_u945)))))
              (var v__x)
              (lam
                v_xs
                (app List ((var v_u945)))
                (lam
                  v_le
                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                  (lam
                    v_x5
                    (pi
                      v_y
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_x5 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (arrow
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app
                                  PSigma.casesOn
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x6
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                    (lam
                                      v_x6
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x6
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                      (app Nat ()))
                                    (var v_y)
                                    (lam
                                      v_x6
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x7
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                        (app List.length ((var v_u945) (var v_x6)))))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam
                                  v_x6
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                (lam
                                  v_x6
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x6
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (app Nat ()))
                                (app
                                  PSigma.mk
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                    (var v_xs)
                                    (var v_le)))
                                (lam
                                  v_x6
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x7
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                    (app List.length ((var v_u945) (var v_x6)))))))))
                        (app List ((var v_u945)))))
                    (app
                      _private.Init.Data.List.Sort.Basic.0.List.mergeSort.match_1
                      ((var v_u945)
                        (lam
                          v_x
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (arrow
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                (arrow
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (lam
                                                v_x9
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x9
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                (app Nat ()))
                                              (var v_y)
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x10
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                  (app List.length ((var v_u945) (var v_x9)))))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                            (app Nat ()))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (var v_x)
                                              (var v_x7)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                              (app List.length ((var v_u945) (var v_x9)))))))))
                                  (app List ((var v_u945)))))
                              (app List ((var v_u945))))))
                        (var v_xs)
                        (var v_le)
                        (lam
                          v_x
                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                          (lam
                            v_x7
                            (pi
                              v_y
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x7
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                              (arrow
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (lam
                                              v_x8
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x8
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                              (app Nat ()))
                                            (var v_y)
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                (app List.length ((var v_u945) (var v_x8)))))))))
                                    (app
                                      PSigma.casesOn
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x8
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                        (lam
                                          v_x8
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                          (app Nat ()))
                                        (app
                                          PSigma.mk
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (app List.nil ((var v_u945)))
                                            (var v_x)))
                                        (lam
                                          v_x8
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x9
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                            (app List.length ((var v_u945) (var v_x8)))))))))
                                (app List ((var v_u945)))))
                            (app List.nil ((var v_u945)))))
                        (lam
                          v_x6
                          (var v_u945)
                          (lam
                            v_x
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (lam
                              v_x8
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                (arrow
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (lam
                                                v_x9
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x9
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                (app Nat ()))
                                              (var v_y)
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x10
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                  (app List.length ((var v_u945) (var v_x9)))))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                            (app Nat ()))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (app List.cons ((var v_u945) (var v_x6) (app List.nil ((var v_u945)))))
                                              (var v_x)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                              (app List.length ((var v_u945) (var v_x9)))))))))
                                  (app List ((var v_u945)))))
                              (app List.cons ((var v_u945) (var v_x6) (app List.nil ((var v_u945))))))))
                        (lam
                          v_x6
                          (var v_u945)
                          (lam
                            v_b
                            (var v_u945)
                            (lam
                              v_x8
                              (app List ((var v_u945)))
                              (lam
                                v_x9
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                (lam
                                  v_x
                                  (pi
                                    v_y
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                    (arrow
                                      (app
                                        Nat.le
                                        ((app
                                            Nat.succ
                                            ((app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                    (app Nat ()))
                                                  (var v_y)
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                      (app List.length ((var v_u945) (var v_x11)))))))))
                                          (app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (lam
                                                v_x11
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x11
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                (app Nat ()))
                                              (app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_x6)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_x8)))))
                                                  (var v_x9)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                  (app List.length ((var v_u945) (var v_x11)))))))))
                                      (app List ((var v_u945)))))
                                  (apv
                                    (lam
                                      v_lr
                                      (app
                                        Prod
                                        ((app
                                            Subtype
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_l
                                                (app List ((var v_u945)))
                                                (app
                                                  Eq
                                                  ((app Nat ())
                                                    (app List.length ((var v_u945) (var v_l)))
                                                    (app
                                                      Nat.div
                                                      ((app
                                                          Nat.add
                                                          ((app
                                                              List.length
                                                              ((var v_u945)
                                                                (app
                                                                  List.cons
                                                                  ((var v_u945)
                                                                    (var v_x6)
                                                                    (app
                                                                      List.cons
                                                                      ((var v_u945) (var v_b) (var v_x8)))))))
                                                            (num 1)))
                                                        (num 2))))))))
                                          (app
                                            Subtype
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_l
                                                (app List ((var v_u945)))
                                                (app
                                                  Eq
                                                  ((app Nat ())
                                                    (app List.length ((var v_u945) (var v_l)))
                                                    (app
                                                      Nat.div
                                                      ((app
                                                          List.length
                                                          ((var v_u945)
                                                            (app
                                                              List.cons
                                                              ((var v_u945)
                                                                (var v_x6)
                                                                (app List.cons ((var v_u945) (var v_b) (var v_x8)))))))
                                                        (num 2))))))))))
                                      (app
                                        List.merge
                                        ((var v_u945)
                                          (apv
                                            (var v_x)
                                            ((app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    Subtype.val
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  Nat.add
                                                                  ((app
                                                                      List.length
                                                                      ((var v_u945)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945)
                                                                            (var v_x6)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945) (var v_b) (var v_x8)))))))
                                                                    (num 1)))
                                                                (num 2))))))
                                                      (app
                                                        Prod.fst
                                                        ((app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          Nat.add
                                                                          ((app
                                                                              List.length
                                                                              ((var v_u945)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x6)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_b)
                                                                                        (var v_x8)))))))
                                                                            (num 1)))
                                                                        (num 2))))))))
                                                          (app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_x6)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_b)
                                                                                    (var v_x8)))))))
                                                                        (num 2))))))))
                                                          (var v_lr)))))
                                                  (var v_x9)))
                                              (proof)))
                                          (apv
                                            (var v_x)
                                            ((app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    Subtype.val
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  List.length
                                                                  ((var v_u945)
                                                                    (app
                                                                      List.cons
                                                                      ((var v_u945)
                                                                        (var v_x6)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945) (var v_b) (var v_x8)))))))
                                                                (num 2))))))
                                                      (app
                                                        Prod.snd
                                                        ((app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          Nat.add
                                                                          ((app
                                                                              List.length
                                                                              ((var v_u945)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x6)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_b)
                                                                                        (var v_x8)))))))
                                                                            (num 1)))
                                                                        (num 2))))))))
                                                          (app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_x6)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_b)
                                                                                    (var v_x8)))))))
                                                                        (num 2))))))))
                                                          (var v_lr)))))
                                                  (var v_x9)))
                                              (proof)))
                                          (var v_x9))))
                                    ((app
                                        List.MergeSort.Internal.splitInTwo
                                        ((var v_u945)
                                          (app
                                            List.length
                                            ((var v_u945)
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_x6)
                                                  (app List.cons ((var v_u945) (var v_b) (var v_x8)))))))
                                          (app
                                            Subtype.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_l
                                                (app List ((var v_u945)))
                                                (app
                                                  Eq
                                                  ((app Nat ())
                                                    (app List.length ((var v_u945) (var v_l)))
                                                    (app
                                                      List.length
                                                      ((var v_u945)
                                                        (app
                                                          List.cons
                                                          ((var v_u945)
                                                            (var v_x6)
                                                            (app List.cons ((var v_u945) (var v_b) (var v_x8))))))))))
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_x6)
                                                  (app List.cons ((var v_u945) (var v_b) (var v_x8)))))
                                              (proof))))))))))))
                        (var v_x5))))))
              (var v_a))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.wellFounded
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (app
      WellFounded
      ((app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (lam
          v_a
          (app
            PSigma
            ((app List ((var v_u945)))
              (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
          (lam
            v_x2
            (app
              PSigma
              ((app List ((var v_u945)))
                (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
            (app
              Nat.le
              ((app
                  Nat.succ
                  ((app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945)))
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                          (app Nat ()))
                        (var v_a)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_le
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (app List.length ((var v_u945) (var v_xs)))))))))
                (app
                  PSigma.casesOn
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                    (lam
                      v__x
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (app Nat ()))
                    (var v_x2)
                    (lam
                      v_xs
                      (app List ((var v_u945)))
                      (lam
                        v_le
                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                        (app List.length ((var v_u945) (var v_xs))))))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.bridge
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
              ((var v_u945) (var v_xs) (var v_le)))
            (app List.mergeSort ((var v_u945) (var v_xs) (var v_le))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.functionBridge
  (app
    Eq
    ((pi
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (arrow
          (app List ((var v_u945)))
          (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945))))))
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
              ((var v_u945) (var v_xs) (var v_le))))))
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app List.mergeSort ((var v_u945) (var v_xs) (var v_le))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.mergeSort.eq_1
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (app
        Eq
        ((app List ((var v_u945)))
          (app List.mergeSort ((var v_u945) (app List.nil ((var v_u945))) (var v_x)))
          (app List.nil ((var v_u945)))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.mergeSort.eq_2
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_a
        (var v_u945)
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              List.mergeSort
              ((var v_u945) (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945))))) (var v_x)))
            (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.mergeSort.eq_3
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_a
        (var v_u945)
        (pi
          v_b
          (var v_u945)
          (pi
            v_xs
            (app List ((var v_u945)))
            (app
              Eq
              ((app List ((var v_u945)))
                (app
                  List.mergeSort
                  ((var v_u945)
                    (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                    (var v_x)))
                (app
                  List.merge
                  ((var v_u945)
                    (app
                      List.mergeSort
                      ((var v_u945)
                        (app
                          Subtype.val
                          ((app List ((var v_u945)))
                            (lam
                              v_l
                              (app List ((var v_u945)))
                              (app
                                Eq
                                ((app Nat ())
                                  (app List.length ((var v_u945) (var v_l)))
                                  (app
                                    Nat.div
                                    ((app
                                        Nat.add
                                        ((app
                                            List.length
                                            ((var v_u945)
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_a)
                                                  (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                          (num 1)))
                                      (num 2))))))
                            (app
                              Prod.fst
                              ((app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                Nat.add
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_a)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                  (num 1)))
                                              (num 2))))))))
                                (app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                              (num 2))))))))
                                (app
                                  List.MergeSort.Internal.splitInTwo
                                  ((var v_u945)
                                    (app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (app
                                      Subtype.mk
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_l
                                          (app List ((var v_u945)))
                                          (app
                                            Eq
                                            ((app Nat ())
                                              (app List.length ((var v_u945) (var v_l)))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                        (app
                                          List.cons
                                          ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                        (proof)))))))))
                        (var v_x)))
                    (app
                      List.mergeSort
                      ((var v_u945)
                        (app
                          Subtype.val
                          ((app List ((var v_u945)))
                            (lam
                              v_l
                              (app List ((var v_u945)))
                              (app
                                Eq
                                ((app Nat ())
                                  (app List.length ((var v_u945) (var v_l)))
                                  (app
                                    Nat.div
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (num 2))))))
                            (app
                              Prod.snd
                              ((app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                Nat.add
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_a)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                  (num 1)))
                                              (num 2))))))))
                                (app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                              (num 2))))))))
                                (app
                                  List.MergeSort.Internal.splitInTwo
                                  ((var v_u945)
                                    (app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (app
                                      Subtype.mk
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_l
                                          (app List ((var v_u945)))
                                          (app
                                            Eq
                                            ((app Nat ())
                                              (app List.length ((var v_u945) (var v_l)))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                        (app
                                          List.cons
                                          ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                        (proof)))))))))
                        (var v_x)))
                    (var v_x))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation0
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (app
        Eq
        ((app List ((var v_u945)))
          (app
            Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
            ((var v_u945) (app List.nil ((var v_u945))) (var v_x)))
          (app List.nil ((var v_u945)))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation1
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_a
        (var v_u945)
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
              ((var v_u945) (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945))))) (var v_x)))
            (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.equation2
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_x
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_a
        (var v_u945)
        (pi
          v_b
          (var v_u945)
          (pi
            v_xs
            (app List ((var v_u945)))
            (app
              Eq
              ((app List ((var v_u945)))
                (app
                  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
                  ((var v_u945)
                    (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                    (var v_x)))
                (app
                  List.merge
                  ((var v_u945)
                    (app
                      Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
                      ((var v_u945)
                        (app
                          Subtype.val
                          ((app List ((var v_u945)))
                            (lam
                              v_l
                              (app List ((var v_u945)))
                              (app
                                Eq
                                ((app Nat ())
                                  (app List.length ((var v_u945) (var v_l)))
                                  (app
                                    Nat.div
                                    ((app
                                        Nat.add
                                        ((app
                                            List.length
                                            ((var v_u945)
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_a)
                                                  (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                          (num 1)))
                                      (num 2))))))
                            (app
                              Prod.fst
                              ((app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                Nat.add
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_a)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                  (num 1)))
                                              (num 2))))))))
                                (app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                              (num 2))))))))
                                (app
                                  List.MergeSort.Internal.splitInTwo
                                  ((var v_u945)
                                    (app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (app
                                      Subtype.mk
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_l
                                          (app List ((var v_u945)))
                                          (app
                                            Eq
                                            ((app Nat ())
                                              (app List.length ((var v_u945) (var v_l)))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                        (app
                                          List.cons
                                          ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                        (proof)))))))))
                        (var v_x)))
                    (app
                      Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.accessible
                      ((var v_u945)
                        (app
                          Subtype.val
                          ((app List ((var v_u945)))
                            (lam
                              v_l
                              (app List ((var v_u945)))
                              (app
                                Eq
                                ((app Nat ())
                                  (app List.length ((var v_u945) (var v_l)))
                                  (app
                                    Nat.div
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (num 2))))))
                            (app
                              Prod.snd
                              ((app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                Nat.add
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_a)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                  (num 1)))
                                              (num 2))))))))
                                (app
                                  Subtype
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                              (num 2))))))))
                                (app
                                  List.MergeSort.Internal.splitInTwo
                                  ((var v_u945)
                                    (app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (app
                                      Subtype.mk
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_l
                                          (app List ((var v_u945)))
                                          (app
                                            Eq
                                            ((app Nat ())
                                              (app List.length ((var v_u945) (var v_l)))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                        (app
                                          List.cons
                                          ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                        (proof)))))))))
                        (var v_x)))
                    (var v_x))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Current
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (var v_u945)
        (arrow
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (arrow
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (var v_u945)
        (lam
          v_b
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma.mk
                ((app List ((var v_u945)))
                  (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                  (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                  (var v_le))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Argument
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (var v_u945)
        (arrow
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (arrow
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (var v_u945)
        (lam
          v_b
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (apv
                (lam
                  v_lr
                  (app
                    Prod
                    ((app
                        Subtype
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      Nat.add
                                      ((app
                                          List.length
                                          ((var v_u945)
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_a)
                                                (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                        (num 1)))
                                    (num 2))))))))
                      (app
                        Subtype
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (num 2))))))))))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (app
                        Subtype.val
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      Nat.add
                                      ((app
                                          List.length
                                          ((var v_u945)
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_a)
                                                (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                        (num 1)))
                                    (num 2))))))
                          (app
                            Prod.fst
                            ((app
                                Subtype
                                ((app List ((var v_u945)))
                                  (lam
                                    v_l
                                    (app List ((var v_u945)))
                                    (app
                                      Eq
                                      ((app Nat ())
                                        (app List.length ((var v_u945) (var v_l)))
                                        (app
                                          Nat.div
                                          ((app
                                              Nat.add
                                              ((app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                (num 1)))
                                            (num 2))))))))
                              (app
                                Subtype
                                ((app List ((var v_u945)))
                                  (lam
                                    v_l
                                    (app List ((var v_u945)))
                                    (app
                                      Eq
                                      ((app Nat ())
                                        (app List.length ((var v_u945) (var v_l)))
                                        (app
                                          Nat.div
                                          ((app
                                              List.length
                                              ((var v_u945)
                                                (app
                                                  List.cons
                                                  ((var v_u945)
                                                    (var v_a)
                                                    (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                            (num 2))))))))
                              (var v_lr)))))
                      (var v_le))))
                ((app
                    List.MergeSort.Internal.splitInTwo
                    ((var v_u945)
                      (app
                        List.length
                        ((var v_u945)
                          (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                      (app
                        Subtype.mk
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  List.length
                                  ((var v_u945)
                                    (app
                                      List.cons
                                      ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                          (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                          (proof))))))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call0Decreases
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_a
      (var v_u945)
      (pi
        v_b
        (var v_u945)
        (pi
          v_xs
          (app List ((var v_u945)))
          (pi
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (apv
              (lam
                v_lr
                (app
                  Prod
                  ((app
                      Subtype
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                Nat.div
                                ((app
                                    Nat.add
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (num 1)))
                                  (num 2))))))))
                    (app
                      Subtype
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                Nat.div
                                ((app
                                    List.length
                                    ((var v_u945)
                                      (app
                                        List.cons
                                        ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                  (num 2))))))))))
                (app
                  Nat.le
                  ((app
                      Nat.succ
                      ((app
                          PSigma.casesOn
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (lam
                              v__x
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x6
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                              (app Nat ()))
                            (app
                              PSigma.mk
                              ((app List ((var v_u945)))
                                (lam
                                  v_x6
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                (app
                                  Subtype.val
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                Nat.add
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_a)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                  (num 1)))
                                              (num 2))))))
                                    (app
                                      Prod.fst
                                      ((app
                                          Subtype
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_l
                                              (app List ((var v_u945)))
                                              (app
                                                Eq
                                                ((app Nat ())
                                                  (app List.length ((var v_u945) (var v_l)))
                                                  (app
                                                    Nat.div
                                                    ((app
                                                        Nat.add
                                                        ((app
                                                            List.length
                                                            ((var v_u945)
                                                              (app
                                                                List.cons
                                                                ((var v_u945)
                                                                  (var v_a)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945) (var v_b) (var v_xs)))))))
                                                          (num 1)))
                                                      (num 2))))))))
                                        (app
                                          Subtype
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_l
                                              (app List ((var v_u945)))
                                              (app
                                                Eq
                                                ((app Nat ())
                                                  (app List.length ((var v_u945) (var v_l)))
                                                  (app
                                                    Nat.div
                                                    ((app
                                                        List.length
                                                        ((var v_u945)
                                                          (app
                                                            List.cons
                                                            ((var v_u945)
                                                              (var v_a)
                                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                      (num 2))))))))
                                        (var v_lr)))))
                                (var v_le)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                (app List.length ((var v_u945) (var v_x6)))))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945)))
                              (lam
                                v_x6
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                          (app Nat ()))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                            (var v_le)))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (app List.length ((var v_u945) (var v_x6))))))))))
              ((app
                  List.MergeSort.Internal.splitInTwo
                  ((var v_u945)
                    (app
                      List.length
                      ((var v_u945)
                        (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                    (app
                      Subtype.mk
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                List.length
                                ((var v_u945)
                                  (app
                                    List.cons
                                    ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                        (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                        (proof))))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Current
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (var v_u945)
        (arrow
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (arrow
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (var v_u945)
        (lam
          v_b
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma.mk
                ((app List ((var v_u945)))
                  (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                  (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                  (var v_le))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Argument
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (var v_u945)
        (arrow
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (arrow
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (var v_u945)
        (lam
          v_b
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (apv
                (lam
                  v_lr
                  (app
                    Prod
                    ((app
                        Subtype
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      Nat.add
                                      ((app
                                          List.length
                                          ((var v_u945)
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_a)
                                                (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                        (num 1)))
                                    (num 2))))))))
                      (app
                        Subtype
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (num 2))))))))))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (app
                        Subtype.val
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  Nat.div
                                  ((app
                                      List.length
                                      ((var v_u945)
                                        (app
                                          List.cons
                                          ((var v_u945)
                                            (var v_a)
                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                    (num 2))))))
                          (app
                            Prod.snd
                            ((app
                                Subtype
                                ((app List ((var v_u945)))
                                  (lam
                                    v_l
                                    (app List ((var v_u945)))
                                    (app
                                      Eq
                                      ((app Nat ())
                                        (app List.length ((var v_u945) (var v_l)))
                                        (app
                                          Nat.div
                                          ((app
                                              Nat.add
                                              ((app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                (num 1)))
                                            (num 2))))))))
                              (app
                                Subtype
                                ((app List ((var v_u945)))
                                  (lam
                                    v_l
                                    (app List ((var v_u945)))
                                    (app
                                      Eq
                                      ((app Nat ())
                                        (app List.length ((var v_u945) (var v_l)))
                                        (app
                                          Nat.div
                                          ((app
                                              List.length
                                              ((var v_u945)
                                                (app
                                                  List.cons
                                                  ((var v_u945)
                                                    (var v_a)
                                                    (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                            (num 2))))))))
                              (var v_lr)))))
                      (var v_le))))
                ((app
                    List.MergeSort.Internal.splitInTwo
                    ((var v_u945)
                      (app
                        List.length
                        ((var v_u945)
                          (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                      (app
                        Subtype.mk
                        ((app List ((var v_u945)))
                          (lam
                            v_l
                            (app List ((var v_u945)))
                            (app
                              Eq
                              ((app Nat ())
                                (app List.length ((var v_u945) (var v_l)))
                                (app
                                  List.length
                                  ((var v_u945)
                                    (app
                                      List.cons
                                      ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                          (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                          (proof))))))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MergeSort.call1Decreases
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_a
      (var v_u945)
      (pi
        v_b
        (var v_u945)
        (pi
          v_xs
          (app List ((var v_u945)))
          (pi
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (apv
              (lam
                v_lr
                (app
                  Prod
                  ((app
                      Subtype
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                Nat.div
                                ((app
                                    Nat.add
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (num 1)))
                                  (num 2))))))))
                    (app
                      Subtype
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                Nat.div
                                ((app
                                    List.length
                                    ((var v_u945)
                                      (app
                                        List.cons
                                        ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                  (num 2))))))))))
                (app
                  Nat.le
                  ((app
                      Nat.succ
                      ((app
                          PSigma.casesOn
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (lam
                              v__x
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x6
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                              (app Nat ()))
                            (app
                              PSigma.mk
                              ((app List ((var v_u945)))
                                (lam
                                  v_x6
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                (app
                                  Subtype.val
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_l
                                      (app List ((var v_u945)))
                                      (app
                                        Eq
                                        ((app Nat ())
                                          (app List.length ((var v_u945) (var v_l)))
                                          (app
                                            Nat.div
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_a)
                                                      (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                              (num 2))))))
                                    (app
                                      Prod.snd
                                      ((app
                                          Subtype
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_l
                                              (app List ((var v_u945)))
                                              (app
                                                Eq
                                                ((app Nat ())
                                                  (app List.length ((var v_u945) (var v_l)))
                                                  (app
                                                    Nat.div
                                                    ((app
                                                        Nat.add
                                                        ((app
                                                            List.length
                                                            ((var v_u945)
                                                              (app
                                                                List.cons
                                                                ((var v_u945)
                                                                  (var v_a)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945) (var v_b) (var v_xs)))))))
                                                          (num 1)))
                                                      (num 2))))))))
                                        (app
                                          Subtype
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_l
                                              (app List ((var v_u945)))
                                              (app
                                                Eq
                                                ((app Nat ())
                                                  (app List.length ((var v_u945) (var v_l)))
                                                  (app
                                                    Nat.div
                                                    ((app
                                                        List.length
                                                        ((var v_u945)
                                                          (app
                                                            List.cons
                                                            ((var v_u945)
                                                              (var v_a)
                                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                      (num 2))))))))
                                        (var v_lr)))))
                                (var v_le)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                (app List.length ((var v_u945) (var v_x6)))))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945)))
                              (lam
                                v_x6
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                          (app Nat ()))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                            (var v_le)))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (app List.length ((var v_u945) (var v_x6))))))))))
              ((app
                  List.MergeSort.Internal.splitInTwo
                  ((var v_u945)
                    (app
                      List.length
                      ((var v_u945)
                        (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                    (app
                      Subtype.mk
                      ((app List ((var v_u945)))
                        (lam
                          v_l
                          (app List ((var v_u945)))
                          (app
                            Eq
                            ((app Nat ())
                              (app List.length ((var v_u945) (var v_l)))
                              (app
                                List.length
                                ((var v_u945)
                                  (app
                                    List.cons
                                    ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                        (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                        (proof))))))))))))
  (Axioms (propext Quot.sound)))

(LeanWfRecursion
  Nat.primeFactorsList
  (Method measure)
  (ProofArguments ())
  (Implementation Nat.primeFactorsList)
  (Relation Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.functionBridge)
  (Equations
    ((Nat.primeFactorsList.eq_1 Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation0)
      (Nat.primeFactorsList.eq_2 Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation1)
      (Nat.primeFactorsList.eq_3 Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation2)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Decreases)
        (SourceProofs (Nat.primeFactorsList._proof_1))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ())))))

(LeanRecursionSourceType Nat.primeFactorsList (arrow (app Nat ()) (app List ((app Nat ())))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.measure
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value (lam v_x (app Nat ()) (var v_x))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.relation
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (prop))))
  (Value (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.recipe
  (Type
    (pi
      v_a
      (app Nat ())
      (arrow
        (pi v_y (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_a))) (app List ((app Nat ())))))
        (app List ((app Nat ()))))))
  (Value
    (lam
      v_a
      (app Nat ())
      (lam
        v_x1
        (pi v_y (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_a))) (app List ((app Nat ())))))
        (app
          Nat.primeFactorsList.match_1
          ((lam
              v_x
              (app Nat ())
              (arrow
                (pi
                  v_y
                  (app Nat ())
                  (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_x))) (app List ((app Nat ())))))
                (app List ((app Nat ())))))
            (var v_a)
            (lam
              v__
              (app PUnit ())
              (lam
                v_x
                (pi
                  v_y
                  (app Nat ())
                  (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 0))) (app List ((app Nat ())))))
                (app List.nil ((app Nat ())))))
            (lam
              v__
              (app PUnit ())
              (lam
                v_x
                (pi
                  v_y
                  (app Nat ())
                  (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 1))) (app List ((app Nat ())))))
                (app List.nil ((app Nat ())))))
            (lam
              v_k
              (app Nat ())
              (lam
                v_x
                (pi
                  v_y
                  (app Nat ())
                  (arrow
                    (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((app Nat.succ ((var v_k)))))))
                    (app List ((app Nat ())))))
                (apv
                  (lam
                    v_m
                    (app Nat ())
                    (app
                      List.cons
                      ((app Nat ())
                        (var v_m)
                        (apv (var v_x) ((app Nat.div ((app Nat.add ((var v_k) (num 2))) (var v_m))) (proof))))))
                  ((app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))))))
            (var v_x1)))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.wellFounded
  (app
    WellFounded
    ((app Nat ()) (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.bridge
  (app
    Eq
    ((arrow (app Nat ()) (app List ((app Nat ()))))
      (lam
        v_x
        (app Nat ())
        (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible ((var v_x))))
      (lam v_a (app Nat ()) (app Nat.primeFactorsList ((var v_a))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.functionBridge
  (app
    Eq
    ((arrow (app Nat ()) (app List ((app Nat ()))))
      (lam
        v_x
        (app Nat ())
        (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible ((var v_x))))
      (lam v_a (app Nat ()) (app Nat.primeFactorsList ((var v_a))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Nat.primeFactorsList.eq_1
  (app Eq ((app List ((app Nat ()))) (app Nat.primeFactorsList ((num 0))) (app List.nil ((app Nat ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Nat.primeFactorsList.eq_2
  (app Eq ((app List ((app Nat ()))) (app Nat.primeFactorsList ((num 1))) (app List.nil ((app Nat ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Nat.primeFactorsList.eq_3
  (pi
    v_k
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app Nat.primeFactorsList ((app Nat.succ ((app Nat.succ ((var v_k)))))))
        (app
          List.cons
          ((app Nat ())
            (app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))
            (app
              Nat.primeFactorsList
              ((app
                  Nat.div
                  ((app Nat.add ((var v_k) (num 2))) (app Nat.minFac ((app Nat.add ((var v_k) (num 2))))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation0
  (app
    Eq
    ((app List ((app Nat ())))
      (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible ((num 0)))
      (app List.nil ((app Nat ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation1
  (app
    Eq
    ((app List ((app Nat ())))
      (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible ((num 1)))
      (app List.nil ((app Nat ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.equation2
  (pi
    v_k
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app
          Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible
          ((app Nat.succ ((app Nat.succ ((var v_k)))))))
        (app
          List.cons
          ((app Nat ())
            (app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))
            (app
              Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.accessible
              ((app
                  Nat.div
                  ((app Nat.add ((var v_k) (num 2))) (app Nat.minFac ((app Nat.add ((var v_k) (num 2))))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Current
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value (lam v_k (app Nat ()) (app Nat.succ ((app Nat.succ ((var v_k))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Argument
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value
    (lam
      v_k
      (app Nat ())
      (apv
        (lam v_m (app Nat ()) (app Nat.div ((app Nat.add ((var v_k) (num 2))) (var v_m))))
        ((app Nat.minFac ((app Nat.add ((var v_k) (num 2))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.PrimeFactorsList.call0Decreases
  (pi
    v_k
    (app Nat ())
    (apv
      (lam
        v_m
        (app Nat ())
        (app
          Nat.le
          ((app Nat.succ ((app Nat.div ((app Nat.add ((var v_k) (num 2))) (var v_m)))))
            (app Nat.succ ((app Nat.succ ((var v_k))))))))
      ((app Nat.minFac ((app Nat.add ((var v_k) (num 2))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanWfRecursion
  Nat.minFacAux
  (Method measure)
  (ProofArguments ())
  (Implementation Nat.minFacAux)
  (Relation Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.functionBridge)
  (Equations ((Nat.minFacAux.eq_1 Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.equation0)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Decreases)
        (SourceProofs (Nat.minFacAux._proof_1))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ())))))

(LeanRecursionSourceType Nat.minFacAux (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.measure
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam v_x (app Nat ()) (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_x)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.relation
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (prop)))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_a
        (app Nat ())
        (lam
          v_x2
          (app Nat ())
          (app
            Nat.le
            ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_a)))))
              (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_x2))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.recipe
  (Type
    (pi
      v_n
      (app Nat ())
      (pi
        v_a
        (app Nat ())
        (arrow
          (pi
            v_y
            (app Nat ())
            (arrow
              (app
                Nat.le
                ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_y)))))
                  (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_a)))))
              (app Nat ())))
          (app Nat ())))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_a
        (app Nat ())
        (lam
          v_x2
          (pi
            v_y
            (app Nat ())
            (arrow
              (app
                Nat.le
                ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_y)))))
                  (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_a)))))
              (app Nat ())))
          (apv
            (lam
              v_k
              (app Nat ())
              (app
                dite
                ((app Nat ())
                  (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                  (app Nat.decLt ((var v_n) (app Nat.mul ((var v_k) (var v_k)))))
                  (lam v_h (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (var v_n))
                  (lam
                    v_h
                    (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
                    (app
                      dite
                      ((app Nat ())
                        (app
                          Exists
                          ((app Nat ())
                            (lam
                              v_c
                              (app Nat ())
                              (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                        (app Nat.decidable_dvd ((var v_k) (var v_n)))
                        (lam
                          v_x5
                          (app
                            Exists
                            ((app Nat ())
                              (lam
                                v_c
                                (app Nat ())
                                (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                          (var v_k))
                        (lam
                          v_x5
                          (arrow
                            (app
                              Exists
                              ((app Nat ())
                                (lam
                                  v_c
                                  (app Nat ())
                                  (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                            (app False ()))
                          (apv (var v_x2) ((app Nat.add ((var v_k) (num 2))) (proof))))))))))
            ((var v_a))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.wellFounded
  (pi
    v_n
    (app Nat ())
    (app
      WellFounded
      ((app Nat ())
        (lam
          v_a
          (app Nat ())
          (lam
            v_x2
            (app Nat ())
            (app
              Nat.le
              ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_a)))))
                (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_x2))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.bridge
  (pi
    v_n
    (app Nat ())
    (app
      Eq
      ((arrow (app Nat ()) (app Nat ()))
        (lam
          v_x
          (app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible ((var v_n) (var v_x))))
        (lam v_a (app Nat ()) (app Nat.minFacAux ((var v_n) (var v_a)))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.functionBridge
  (app
    Eq
    ((arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))
      (lam
        v_n
        (app Nat ())
        (lam
          v_x
          (app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible ((var v_n) (var v_x)))))
      (lam v_n (app Nat ()) (lam v_a (app Nat ()) (app Nat.minFacAux ((var v_n) (var v_a)))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Nat.minFacAux.eq_1
  (pi
    v_n
    (app Nat ())
    (pi
      v_x
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.minFacAux ((var v_n) (var v_x)))
          (app
            ite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_x) (var v_x)))))
              (app Nat.decLt ((var v_n) (app Nat.mul ((var v_x) (var v_x)))))
              (var v_n)
              (app
                ite
                ((app Nat ())
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_x) (var v_c))))))))
                  (app Nat.decidable_dvd ((var v_x) (var v_n)))
                  (var v_x)
                  (app Nat.minFacAux ((var v_n) (app Nat.add ((var v_x) (num 2)))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.equation0
  (pi
    v_n
    (app Nat ())
    (pi
      v_x
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible ((var v_n) (var v_x)))
          (app
            ite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_x) (var v_x)))))
              (app Nat.decLt ((var v_n) (app Nat.mul ((var v_x) (var v_x)))))
              (var v_n)
              (app
                ite
                ((app Nat ())
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_x) (var v_c))))))))
                  (app Nat.decidable_dvd ((var v_x) (var v_n)))
                  (var v_x)
                  (app
                    Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible
                    ((var v_n) (app Nat.add ((var v_x) (num 2)))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Current
  (Type
    (pi
      v_n
      (app Nat ())
      (pi
        v_a
        (app Nat ())
        (apv
          (lam
            v_k
            (app Nat ())
            (arrow
              (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
              (arrow
                (arrow
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                  (app False ()))
                (app Nat ()))))
          ((var v_a))))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_a
        (app Nat ())
        (apv
          (lam
            v_k
            (app Nat ())
            (lam
              v_h
              (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
              (lam
                v_x4
                (arrow
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                  (app False ()))
                (var v_a))))
          ((var v_a)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Argument
  (Type
    (pi
      v_n
      (app Nat ())
      (pi
        v_a
        (app Nat ())
        (apv
          (lam
            v_k
            (app Nat ())
            (arrow
              (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
              (arrow
                (arrow
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                  (app False ()))
                (app Nat ()))))
          ((var v_a))))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_a
        (app Nat ())
        (apv
          (lam
            v_k
            (app Nat ())
            (lam
              v_h
              (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
              (lam
                v_x4
                (arrow
                  (app
                    Exists
                    ((app Nat ())
                      (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                  (app False ()))
                (app Nat.add ((var v_k) (num 2))))))
          ((var v_a)))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.call0Decreases
  (pi
    v_n
    (app Nat ())
    (pi
      v_a
      (app Nat ())
      (apv
        (lam
          v_k
          (app Nat ())
          (arrow
            (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (app False ()))
            (arrow
              (arrow
                (app
                  Exists
                  ((app Nat ())
                    (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                (app False ()))
              (app
                Nat.le
                ((app
                    Nat.succ
                    ((app
                        Nat.sub
                        ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (app Nat.add ((var v_k) (num 2)))))))
                  (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_a))))))))
        ((var v_a)))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanWfRecursion
  Nat.div.go
  (Method structural-natural)
  (ProofArguments (1 4))
  (Implementation Nat.div.go)
  (Relation Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.functionBridge)
  (Equations ((Nat.div.go.eq_1 Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.equation0)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Decreases)
        (SourceProofs (Nat.lt_succ_self Nat.div_rec_fuel_lemma))
        (SourceCall (Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Source))
        (SourceEquation (Nat.div.go.eq_1))
        (ProofUses
          ((1
              (Proposition Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof1Proposition)
              (Evidence ())
              (ForwardedCondition (v_hy)))
            (4
              (Proposition Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof4Proposition)
              (Evidence (Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof4Evidence))
              (ForwardedCondition ()))))))))

(LeanRecursionSourceType
  Nat.div.go
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_fuel
        (app Nat ())
        (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel))) (app Nat ())))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.measure
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value (lam v_n (app Nat ()) (var v_n))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.relation
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (prop))))
  (Value (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.recipe
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_n
          (app Nat ())
          (arrow
            (pi
              v_m
              (app Nat ())
              (arrow
                (app Nat.le ((app Nat.succ ((var v_m))) (var v_n)))
                (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_m))) (app Nat ())))))
            (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_n))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_n
          (app Nat ())
          (lam
            v_previous
            (pi
              v_m
              (app Nat ())
              (arrow
                (app Nat.le ((app Nat.succ ((var v_m))) (var v_n)))
                (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_m))) (app Nat ())))))
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_n)))
                (app
                  Mettapedia.Languages.Lean.Recursion.AccessibleNatBrec.recipe
                  ((lam
                      v_fuel
                      (app Nat ())
                      (pi
                        v_x7
                        (app Nat ())
                        (arrow (app Nat.le ((app Nat.succ ((var v_x7))) (var v_fuel))) (app Nat ()))))
                    (lam
                      v_fuel
                      (app Nat ())
                      (lam
                        v_f
                        (app
                          Nat.rec
                          ((lam v_t (app Nat ()) (sort (lvl 1)))
                            (app PUnit ())
                            (lam
                              v_x7
                              (app Nat ())
                              (lam
                                v_n_ih
                                (sort (lvl 1))
                                (app
                                  PProd
                                  ((pi
                                      v_x9
                                      (app Nat ())
                                      (arrow (app Nat.le ((app Nat.succ ((var v_x9))) (var v_x7))) (app Nat ())))
                                    (var v_n_ih)))))
                            (var v_fuel)))
                        (lam
                          v_x8
                          (app Nat ())
                          (lam
                            v_x9
                            (app Nat.le ((app Nat.succ ((var v_x8))) (var v_fuel)))
                            (app Nat.div.go._f ((var v_y) (proof) (var v_fuel) (var v_f) (var v_x8) (proof)))))))
                    (var v_n)
                    (var v_previous)
                    (var v_x)
                    (proof)))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.wellFounded
  (app
    WellFounded
    ((app Nat ()) (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.bridge
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_fuel
        (app Nat ())
        (pi
          v_x
          (app Nat ())
          (pi
            v_hfuel
            (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
            (app
              Eq
              ((app Nat ())
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible
                  ((var v_y) (proof) (var v_fuel) (var v_x) (proof)))
                (app Nat.div.go ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.functionBridge
  (app
    Eq
    ((pi
        v_y
        (app Nat ())
        (arrow
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (pi
            v_fuel
            (app Nat ())
            (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel))) (app Nat ()))))))
      (lam
        v_y
        (app Nat ())
        (lam
          v_hy
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (lam
            v_fuel
            (app Nat ())
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible
                  ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))
      (lam
        v_y
        (app Nat ())
        (lam
          v_hy
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (lam
            v_fuel
            (app Nat ())
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
                (app Nat.div.go ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.div.go.eq_1
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (pi
            v_hfuel_2
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (app
              Eq
              ((app Nat ())
                (app Nat.div.go ((var v_y) (proof) (app Nat.succ ((var v_fuel_2))) (var v_x) (proof)))
                (app
                  dite
                  ((app Nat ())
                    (app Nat.le ((var v_y) (var v_x)))
                    (app Nat.decLe ((var v_y) (var v_x)))
                    (lam
                      v_h
                      (app Nat.le ((var v_y) (var v_x)))
                      (app
                        Nat.add
                        ((app Nat.div.go ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof)))
                          (num 1))))
                    (lam v_x5 (arrow (app Nat.le ((var v_y) (var v_x))) (app False ())) (num 0)))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.equation0
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (pi
            v_hfuel_2
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (app
              Eq
              ((app Nat ())
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible
                  ((var v_y) (proof) (app Nat.succ ((var v_fuel_2))) (var v_x) (proof)))
                (app
                  dite
                  ((app Nat ())
                    (app Nat.le ((var v_y) (var v_x)))
                    (app Nat.decLe ((var v_y) (var v_x)))
                    (lam
                      v_h
                      (app Nat.le ((var v_y) (var v_x)))
                      (app
                        Nat.add
                        ((app
                            Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible
                            ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof)))
                          (num 1))))
                    (lam v_x5 (arrow (app Nat.le ((var v_y) (var v_x))) (app False ())) (num 0)))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Current
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam v_h (app Nat.le ((var v_y) (var v_x))) (app Nat.succ ((var v_fuel_2)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Argument
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam v_h (app Nat.le ((var v_y) (var v_x))) (var v_fuel_2)))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Decreases
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (arrow
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (arrow
              (app Nat.le ((var v_y) (var v_x)))
              (app Nat.le ((app Nat.succ ((var v_fuel_2))) (app Nat.succ ((var v_fuel_2)))))))))))
  (Axioms ()))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Source
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam
                v_h
                (app Nat.le ((var v_y) (var v_x)))
                (app Nat.div.go ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof)))))))))))

(LeanRecursionTheorem
  Nat.lt_succ_self
  (pi v_n (app Nat ()) (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.succ ((var v_n))))))
  (Axioms ()))

(LeanRecursionTheorem
  Nat.div_rec_fuel_lemma
  (pi
    v_x
    (app Nat ())
    (pi
      v_y
      (app Nat ())
      (pi
        v_fuel
        (app Nat ())
        (arrow
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (arrow
            (app Nat.le ((var v_y) (var v_x)))
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.add ((var v_fuel) (num 1)))))
              (app Nat.le ((app Nat.succ ((app Nat.sub ((var v_x) (var v_y))))) (var v_fuel)))))))))
  (Axioms ()))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof1Proposition
  (Type (arrow (app Nat ()) (prop)))
  (Value (lam v_y (app Nat ()) (app Nat.le ((app Nat.succ ((num 0))) (var v_y))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof4Proposition
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (prop)))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_x
        (app Nat ())
        (lam
          v_fuel_2
          (app Nat ())
          (app Nat.le ((app Nat.succ ((app Nat.sub ((var v_x) (var v_y))))) (var v_fuel_2))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.call0Proof4Evidence
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (arrow
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (arrow
              (app Nat.le ((var v_y) (var v_x)))
              (app Nat.le ((app Nat.succ ((app Nat.sub ((var v_x) (var v_y))))) (var v_fuel_2)))))))))
  (Axioms ()))

(LeanWfRecursion
  Nat.modCore.go
  (Method structural-natural)
  (ProofArguments (1 4))
  (Implementation Nat.modCore.go)
  (Relation Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.relation)
  (Measure (Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.measure))
  (Recipe Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.functionBridge)
  (Equations ((Nat.modCore.go.eq_1 Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.equation0)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Decreases)
        (SourceProofs (Nat.lt_succ_self Nat.div_rec_fuel_lemma))
        (SourceCall (Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Source))
        (SourceEquation (Nat.modCore.go.eq_1))
        (ProofUses
          ((1
              (Proposition Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof1Proposition)
              (Evidence ())
              (ForwardedCondition (v_hy)))
            (4
              (Proposition Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof4Proposition)
              (Evidence (Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof4Evidence))
              (ForwardedCondition ()))))))))

(LeanRecursionSourceType
  Nat.modCore.go
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_fuel
        (app Nat ())
        (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel))) (app Nat ())))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.measure
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value (lam v_n (app Nat ()) (var v_n))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.relation
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (prop))))
  (Value (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.recipe
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_n
          (app Nat ())
          (arrow
            (pi
              v_m
              (app Nat ())
              (arrow
                (app Nat.le ((app Nat.succ ((var v_m))) (var v_n)))
                (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_m))) (app Nat ())))))
            (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_n))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_n
          (app Nat ())
          (lam
            v_previous
            (pi
              v_m
              (app Nat ())
              (arrow
                (app Nat.le ((app Nat.succ ((var v_m))) (var v_n)))
                (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_m))) (app Nat ())))))
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_n)))
                (app
                  Mettapedia.Languages.Lean.Recursion.AccessibleNatBrec.recipe
                  ((lam
                      v_fuel
                      (app Nat ())
                      (pi
                        v_x7
                        (app Nat ())
                        (arrow (app Nat.le ((app Nat.succ ((var v_x7))) (var v_fuel))) (app Nat ()))))
                    (lam
                      v_fuel
                      (app Nat ())
                      (lam
                        v_f
                        (app
                          Nat.rec
                          ((lam v_t (app Nat ()) (sort (lvl 1)))
                            (app PUnit ())
                            (lam
                              v_x7
                              (app Nat ())
                              (lam
                                v_n_ih
                                (sort (lvl 1))
                                (app
                                  PProd
                                  ((pi
                                      v_x9
                                      (app Nat ())
                                      (arrow (app Nat.le ((app Nat.succ ((var v_x9))) (var v_x7))) (app Nat ())))
                                    (var v_n_ih)))))
                            (var v_fuel)))
                        (lam
                          v_x8
                          (app Nat ())
                          (lam
                            v_x9
                            (app Nat.le ((app Nat.succ ((var v_x8))) (var v_fuel)))
                            (app Nat.modCore.go._f ((var v_y) (proof) (var v_fuel) (var v_f) (var v_x8) (proof)))))))
                    (var v_n)
                    (var v_previous)
                    (var v_x)
                    (proof)))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.wellFounded
  (app
    WellFounded
    ((app Nat ()) (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.le ((app Nat.succ ((var v_a))) (var v_x1)))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.bridge
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_fuel
        (app Nat ())
        (pi
          v_x
          (app Nat ())
          (pi
            v_hfuel
            (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
            (app
              Eq
              ((app Nat ())
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible
                  ((var v_y) (proof) (var v_fuel) (var v_x) (proof)))
                (app Nat.modCore.go ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.functionBridge
  (app
    Eq
    ((pi
        v_y
        (app Nat ())
        (arrow
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (pi
            v_fuel
            (app Nat ())
            (pi v_x (app Nat ()) (arrow (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel))) (app Nat ()))))))
      (lam
        v_y
        (app Nat ())
        (lam
          v_hy
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (lam
            v_fuel
            (app Nat ())
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible
                  ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))
      (lam
        v_y
        (app Nat ())
        (lam
          v_hy
          (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
          (lam
            v_fuel
            (app Nat ())
            (lam
              v_x
              (app Nat ())
              (lam
                v_hfuel
                (app Nat.le ((app Nat.succ ((var v_x))) (var v_fuel)))
                (app Nat.modCore.go ((var v_y) (proof) (var v_fuel) (var v_x) (proof))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.modCore.go.eq_1
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (pi
            v_hfuel_2
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (app
              Eq
              ((app Nat ())
                (app Nat.modCore.go ((var v_y) (proof) (app Nat.succ ((var v_fuel_2))) (var v_x) (proof)))
                (app
                  dite
                  ((app Nat ())
                    (app Nat.le ((var v_y) (var v_x)))
                    (app Nat.decLe ((var v_y) (var v_x)))
                    (lam
                      v_h
                      (app Nat.le ((var v_y) (var v_x)))
                      (app
                        Nat.modCore.go
                        ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof))))
                    (lam v_x5 (arrow (app Nat.le ((var v_y) (var v_x))) (app False ())) (var v_x)))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.equation0
  (pi
    v_y
    (app Nat ())
    (pi
      v_hy
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (pi
            v_hfuel_2
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (app
              Eq
              ((app Nat ())
                (app
                  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible
                  ((var v_y) (proof) (app Nat.succ ((var v_fuel_2))) (var v_x) (proof)))
                (app
                  dite
                  ((app Nat ())
                    (app Nat.le ((var v_y) (var v_x)))
                    (app Nat.decLe ((var v_y) (var v_x)))
                    (lam
                      v_h
                      (app Nat.le ((var v_y) (var v_x)))
                      (app
                        Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible
                        ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof))))
                    (lam v_x5 (arrow (app Nat.le ((var v_y) (var v_x))) (app False ())) (var v_x)))))))))))
  (Axioms (Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Current
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam v_h (app Nat.le ((var v_y) (var v_x))) (app Nat.succ ((var v_fuel_2)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Argument
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam v_h (app Nat.le ((var v_y) (var v_x))) (var v_fuel_2)))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Decreases
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (arrow
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (arrow
              (app Nat.le ((var v_y) (var v_x)))
              (app Nat.le ((app Nat.succ ((var v_fuel_2))) (app Nat.succ ((var v_fuel_2)))))))))))
  (Axioms ()))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Source
  (Type
    (pi
      v_y
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (pi
          v_x
          (app Nat ())
          (pi
            v_fuel_2
            (app Nat ())
            (arrow
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (arrow (app Nat.le ((var v_y) (var v_x))) (app Nat ()))))))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_hy
        (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
        (lam
          v_x
          (app Nat ())
          (lam
            v_fuel_2
            (app Nat ())
            (lam
              v_hfuel_2
              (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
              (lam
                v_h
                (app Nat.le ((var v_y) (var v_x)))
                (app
                  Nat.modCore.go
                  ((var v_y) (proof) (var v_fuel_2) (app Nat.sub ((var v_x) (var v_y))) (proof)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof1Proposition
  (Type (arrow (app Nat ()) (prop)))
  (Value (lam v_y (app Nat ()) (app Nat.le ((app Nat.succ ((num 0))) (var v_y))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof4Proposition
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (prop)))))
  (Value
    (lam
      v_y
      (app Nat ())
      (lam
        v_x
        (app Nat ())
        (lam
          v_fuel_2
          (app Nat ())
          (app Nat.le ((app Nat.succ ((app Nat.sub ((var v_x) (var v_y))))) (var v_fuel_2))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.call0Proof4Evidence
  (pi
    v_y
    (app Nat ())
    (arrow
      (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
      (pi
        v_x
        (app Nat ())
        (pi
          v_fuel_2
          (app Nat ())
          (arrow
            (app Nat.le ((app Nat.succ ((var v_x))) (app Nat.succ ((var v_fuel_2)))))
            (arrow
              (app Nat.le ((var v_y) (var v_x)))
              (app Nat.le ((app Nat.succ ((app Nat.sub ((var v_x) (var v_y))))) (var v_fuel_2)))))))))
  (Axioms ()))

(LeanWfRecursion
  List.merge
  (Method well-founded-relation)
  (ProofArguments ())
  (Implementation List.merge._unary)
  (Relation Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.relation)
  (Measure ())
  (Recipe Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.recipe)
  (WellFounded Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.wellFounded)
  (Accessible Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.functionBridge)
  (Equations
    ((List.merge.eq_1 Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation0)
      (List.merge.eq_2 Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation1)
      (List.merge.eq_3 Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation2)))
  (Calls
    ((call
        (Current Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Current)
        (Argument Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Decreases)
        (SourceProofs (_private.Init.Data.List.Sort.Basic.0.List.merge._unary._proof_2))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ()))
      (call
        (Current Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Current)
        (Argument Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Argument)
        (ConditionsAndDecrease Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Decreases)
        (Proof Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Decreases)
        (SourceProofs (_private.Init.Data.List.Sort.Basic.0.List.merge._unary._proof_3))
        (SourceCall ())
        (SourceEquation ())
        (ProofUses ())))))

(LeanRecursionSourceType
  List.merge
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (arrow
      (app List ((var v_u945)))
      (arrow
        (app List ((var v_u945)))
        (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.relation
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
        (arrow
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (prop)))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
        (lam
          v_x2
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (app
            Prod.Lex
            ((app List ((var v_u945)))
              (app List ((var v_u945)))
              (lam
                v_x3
                (app List ((var v_u945)))
                (lam
                  v_x4
                  (app List ((var v_u945)))
                  (app
                    Nat.le
                    ((app
                        Nat.succ
                        ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x3)))))
                      (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
              (lam
                v_x3
                (app List ((var v_u945)))
                (lam
                  v_x4
                  (app List ((var v_u945)))
                  (app
                    Nat.le
                    ((app
                        Nat.succ
                        ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x3)))))
                      (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
              (app
                PSigma.casesOn
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                  (lam
                    v__x
                    (app
                      PSigma
                      ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                  (var v_a)
                  (lam
                    v_xs
                    (app List ((var v_u945)))
                    (lam
                      v_ys
                      (app List ((var v_u945)))
                      (app Prod.mk ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
              (app
                PSigma.casesOn
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                  (lam
                    v__x
                    (app
                      PSigma
                      ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                  (var v_x2)
                  (lam
                    v_xs
                    (app List ((var v_u945)))
                    (lam
                      v_ys
                      (app List ((var v_u945)))
                      (app
                        Prod.mk
                        ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys))))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.recipe
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v__x
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (arrow
            (pi
              v_y
              (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
              (arrow
                (app
                  Prod.Lex
                  ((app List ((var v_u945)))
                    (app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x4
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x4
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v_x3
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (var v_y)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_ys
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v_x3
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (var v__x)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_ys
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))
                (app List ((var v_u945)))))
            (app List ((var v_u945))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v__x
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (lam
            v_a
            (pi
              v_y
              (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
              (arrow
                (app
                  Prod.Lex
                  ((app List ((var v_u945)))
                    (app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x5
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x5)))))))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x5
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x5)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v_x4
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (var v_y)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_ys
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v_x4
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (var v__x)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_ys
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))
                (app List ((var v_u945)))))
            (app
              PSigma.casesOn
              ((app List ((var v_u945)))
                (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                (lam
                  v_x4
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                  (arrow
                    (pi
                      v_y
                      (app
                        PSigma
                        ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                      (arrow
                        (app
                          Prod.Lex
                          ((app List ((var v_u945)))
                            (app List ((var v_u945)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                (lam
                                  v_x6
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                (var v_y)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_ys
                                    (app List ((var v_u945)))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                (lam
                                  v_x6
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                (var v_x4)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_ys
                                    (app List ((var v_u945)))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))
                        (app List ((var v_u945)))))
                    (app List ((var v_u945)))))
                (var v__x)
                (lam
                  v_xs
                  (app List ((var v_u945)))
                  (lam
                    v_ys
                    (app List ((var v_u945)))
                    (lam
                      v_x6
                      (pi
                        v_y
                        (app
                          PSigma
                          ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                        (arrow
                          (app
                            Prod.Lex
                            ((app List ((var v_u945)))
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (lam
                                  v_x8
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (lam
                                  v_x8
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                              (app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                  (lam
                                    v_x7
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                  (var v_y)
                                  (lam
                                    v_x7
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (app
                                        Prod.mk
                                        ((app List ((var v_u945))) (app List ((var v_u945))) (var v_x7) (var v_x8)))))))
                              (app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                  (lam
                                    v_x7
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                  (app
                                    PSigma.mk
                                    ((app List ((var v_u945)))
                                      (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                      (var v_xs)
                                      (var v_ys)))
                                  (lam
                                    v_x7
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (app
                                        Prod.mk
                                        ((app List ((var v_u945)))
                                          (app List ((var v_u945)))
                                          (var v_x7)
                                          (var v_x8)))))))))
                          (app List ((var v_u945)))))
                      (app
                        _private.Init.Data.List.Sort.Basic.0.List.merge.match_1
                        ((var v_u945)
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (lam
                              v_x8
                              (app List ((var v_u945)))
                              (arrow
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (arrow
                                    (app
                                      Prod.Lex
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x11
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x10)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x11)))))))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x11
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x10)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x11)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v_x10
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (var v_y)
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x10)
                                                    (var v_x11)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v_x10
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (var v_x7)
                                                (var v_x8)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x10)
                                                    (var v_x11)))))))))
                                    (app List ((var v_u945)))))
                                (app List ((var v_u945))))))
                          (var v_xs)
                          (var v_ys)
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (lam
                              v_x
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                                (arrow
                                  (app
                                    Prod.Lex
                                    ((app List ((var v_u945)))
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (var v_y)
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                              (app List.nil ((var v_u945)))
                                              (var v_x7)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))))
                                  (app List ((var v_u945)))))
                              (var v_x7)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (lam
                              v_x
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                                (arrow
                                  (app
                                    Prod.Lex
                                    ((app List ((var v_u945)))
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (var v_y)
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                              (var v_x7)
                                              (app List.nil ((var v_u945)))))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))))
                                  (app List ((var v_u945)))))
                              (var v_x7)))
                          (lam
                            v_x
                            (var v_u945)
                            (lam
                              v_x8
                              (app List ((var v_u945)))
                              (lam
                                v_y
                                (var v_u945)
                                (lam
                                  v_x10
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x11
                                    (pi
                                      v_x11
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))))
                                      (arrow
                                        (app
                                          Prod.Lex
                                          ((app List ((var v_u945)))
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x12
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x13
                                                (app List ((var v_u945)))
                                                (app
                                                  Nat.le
                                                  ((app
                                                      Nat.succ
                                                      ((app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x12)))))
                                                    (app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x13)))))))
                                            (lam
                                              v_x12
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x13
                                                (app List ((var v_u945)))
                                                (app
                                                  Nat.le
                                                  ((app
                                                      Nat.succ
                                                      ((app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x12)))))
                                                    (app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x13)))))))
                                            (app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (lam
                                                  v_x12
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                (var v_x11)
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Prod.mk
                                                      ((app List ((var v_u945)))
                                                        (app List ((var v_u945)))
                                                        (var v_x12)
                                                        (var v_x13)))))))
                                            (app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (lam
                                                  v_x12
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                (app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (app List.cons ((var v_u945) (var v_x) (var v_x8)))
                                                    (app List.cons ((var v_u945) (var v_y) (var v_x10)))))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Prod.mk
                                                      ((app List ((var v_u945)))
                                                        (app List ((var v_u945)))
                                                        (var v_x12)
                                                        (var v_x13)))))))))
                                        (app List ((var v_u945)))))
                                    (app
                                      dite
                                      ((app List ((var v_u945)))
                                        (app
                                          Eq
                                          ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                        (app
                                          instDecidableEqBool
                                          ((apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                        (lam
                                          v_h
                                          (app
                                            Eq
                                            ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_x)
                                              (apv
                                                (var v_x11)
                                                ((app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (var v_x8)
                                                      (app List.cons ((var v_u945) (var v_y) (var v_x10)))))
                                                  (proof))))))
                                        (lam
                                          v_h
                                          (arrow
                                            (app
                                              Eq
                                              ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                            (app False ()))
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_y)
                                              (apv
                                                (var v_x11)
                                                ((app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (app List.cons ((var v_u945) (var v_x) (var v_x8)))
                                                      (var v_x10)))
                                                  (proof)))))))))))))
                          (var v_x6))))))
                (var v_a)))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.wellFounded
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (app
      WellFounded
      ((app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
        (lam
          v_a
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (lam
            v_x2
            (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
            (app
              Prod.Lex
              ((app List ((var v_u945)))
                (app List ((var v_u945)))
                (lam
                  v_x3
                  (app List ((var v_u945)))
                  (lam
                    v_x4
                    (app List ((var v_u945)))
                    (app
                      Nat.le
                      ((app
                          Nat.succ
                          ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x3)))))
                        (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
                (lam
                  v_x3
                  (app List ((var v_u945)))
                  (lam
                    v_x4
                    (app List ((var v_u945)))
                    (app
                      Nat.le
                      ((app
                          Nat.succ
                          ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x3)))))
                        (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x4)))))))
                (app
                  PSigma.casesOn
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                    (lam
                      v__x
                      (app
                        PSigma
                        ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                    (var v_a)
                    (lam
                      v_xs
                      (app List ((var v_u945)))
                      (lam
                        v_ys
                        (app List ((var v_u945)))
                        (app Prod.mk ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                (app
                  PSigma.casesOn
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                    (lam
                      v__x
                      (app
                        PSigma
                        ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                    (var v_x2)
                    (lam
                      v_xs
                      (app List ((var v_u945)))
                      (lam
                        v_ys
                        (app List ((var v_u945)))
                        (app
                          Prod.mk
                          ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys))))))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.bridge
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                ((var v_u945) (var v_xs) (var v_ys) (var v_le)))
              (app List.merge ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.functionBridge
  (app
    Eq
    ((pi
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (arrow
          (app List ((var v_u945)))
          (arrow
            (app List ((var v_u945)))
            (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945)))))))
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_ys
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_ys
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app List.merge ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.merge.eq_1
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_ys
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app List.merge ((var v_u945) (app List.nil ((var v_u945))) (var v_ys) (var v_le)))
            (var v_ys))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.merge.eq_2
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (arrow
          (arrow (app Eq ((app List ((var v_u945))) (var v_xs) (app List.nil ((var v_u945))))) (app False ()))
          (app
            Eq
            ((app List ((var v_u945)))
              (app List.merge ((var v_u945) (var v_xs) (app List.nil ((var v_u945))) (var v_le)))
              (var v_xs)))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  List.merge.eq_3
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_x
        (var v_u945)
        (pi
          v_xs_2
          (app List ((var v_u945)))
          (pi
            v_y
            (var v_u945)
            (pi
              v_ys_2
              (app List ((var v_u945)))
              (app
                Eq
                ((app List ((var v_u945)))
                  (app
                    List.merge
                    ((var v_u945)
                      (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                      (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                      (var v_le)))
                  (app
                    ite
                    ((app List ((var v_u945)))
                      (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                      (app instDecidableEqBool ((apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                      (app
                        List.cons
                        ((var v_u945)
                          (var v_x)
                          (app
                            List.merge
                            ((var v_u945)
                              (var v_xs_2)
                              (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                              (var v_le)))))
                      (app
                        List.cons
                        ((var v_u945)
                          (var v_y)
                          (app
                            List.merge
                            ((var v_u945)
                              (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                              (var v_ys_2)
                              (var v_le)))))))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation0
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_ys
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
              ((var v_u945) (app List.nil ((var v_u945))) (var v_ys) (var v_le)))
            (var v_ys))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation1
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (arrow
          (arrow (app Eq ((app List ((var v_u945))) (var v_xs) (app List.nil ((var v_u945))))) (app False ()))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                ((var v_u945) (var v_xs) (app List.nil ((var v_u945))) (var v_le)))
              (var v_xs)))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.equation2
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_x
        (var v_u945)
        (pi
          v_xs_2
          (app List ((var v_u945)))
          (pi
            v_y
            (var v_u945)
            (pi
              v_ys_2
              (app List ((var v_u945)))
              (app
                Eq
                ((app List ((var v_u945)))
                  (app
                    Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                    ((var v_u945)
                      (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                      (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                      (var v_le)))
                  (app
                    ite
                    ((app List ((var v_u945)))
                      (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                      (app instDecidableEqBool ((apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                      (app
                        List.cons
                        ((var v_u945)
                          (var v_x)
                          (app
                            Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                            ((var v_u945)
                              (var v_xs_2)
                              (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                              (var v_le)))))
                      (app
                        List.cons
                        ((var v_u945)
                          (var v_y)
                          (app
                            Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.accessible
                            ((var v_u945)
                              (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                              (var v_ys_2)
                              (var v_le)))))))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Current
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_x
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (pi
              v_y
              (var v_u945)
              (arrow
                (app List ((var v_u945)))
                (arrow
                  (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v_x
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_y
              (var v_u945)
              (lam
                v_ys
                (app List ((var v_u945)))
                (lam
                  v_h
                  (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                      (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                      (app List.cons ((var v_u945) (var v_y) (var v_ys))))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Argument
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_x
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (pi
              v_y
              (var v_u945)
              (arrow
                (app List ((var v_u945)))
                (arrow
                  (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v_x
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_y
              (var v_u945)
              (lam
                v_ys
                (app List ((var v_u945)))
                (lam
                  v_h
                  (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                      (var v_xs)
                      (app List.cons ((var v_u945) (var v_y) (var v_ys))))))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call0Decreases
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_x
        (var v_u945)
        (pi
          v_xs
          (app List ((var v_u945)))
          (pi
            v_y
            (var v_u945)
            (pi
              v_ys
              (app List ((var v_u945)))
              (arrow
                (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                (app
                  Prod.Lex
                  ((app List ((var v_u945)))
                    (app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x7
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x7
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                            (var v_xs)
                            (app List.cons ((var v_u945) (var v_y) (var v_ys)))))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_x6) (var v_x7)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                            (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                            (app List.cons ((var v_u945) (var v_y) (var v_ys)))))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_x6) (var v_x7))))))))))))))))
  (Axioms (propext)))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Current
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_x
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (pi
              v_y
              (var v_u945)
              (arrow
                (app List ((var v_u945)))
                (arrow
                  (arrow
                    (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                    (app False ()))
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v_x
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_y
              (var v_u945)
              (lam
                v_ys
                (app List ((var v_u945)))
                (lam
                  v_h
                  (arrow
                    (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                    (app False ()))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                      (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                      (app List.cons ((var v_u945) (var v_y) (var v_ys))))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Argument
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_x
          (var v_u945)
          (arrow
            (app List ((var v_u945)))
            (pi
              v_y
              (var v_u945)
              (arrow
                (app List ((var v_u945)))
                (arrow
                  (arrow
                    (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                    (app False ()))
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v_x
          (var v_u945)
          (lam
            v_xs
            (app List ((var v_u945)))
            (lam
              v_y
              (var v_u945)
              (lam
                v_ys
                (app List ((var v_u945)))
                (lam
                  v_h
                  (arrow
                    (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                    (app False ()))
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                      (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                      (var v_ys))))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.RelationalCore.Merge.call1Decreases
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_x
        (var v_u945)
        (pi
          v_xs
          (app List ((var v_u945)))
          (pi
            v_y
            (var v_u945)
            (pi
              v_ys
              (app List ((var v_u945)))
              (arrow
                (arrow
                  (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                  (app False ()))
                (app
                  Prod.Lex
                  ((app List ((var v_u945)))
                    (app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x7
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam
                        v_x7
                        (app List ((var v_u945)))
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                            (app List._sizeOf_1 ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                            (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                            (var v_ys)))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_x6) (var v_x7)))))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                            (app List.cons ((var v_u945) (var v_x) (var v_xs)))
                            (app List.cons ((var v_u945) (var v_y) (var v_ys)))))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Prod.mk
                              ((app List ((var v_u945))) (app List ((var v_u945))) (var v_x6) (var v_x7))))))))))))))))
  (Axioms (propext)))

(LeanRecursionWrapper
  Nat.div
  (Accessible Mettapedia.Languages.Lean.Recursion.Core.Div.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.Core.Div.bridge)
  (Dependencies (Nat.div.go))
  (Equations ((Nat.div.eq_1 Mettapedia.Languages.Lean.Recursion.Core.Div.equation0))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.Core.Div.accessible
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_x
      (app Nat ())
      (lam
        v_y
        (app Nat ())
        (app
          dite
          ((app Nat ())
            (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
            (app Nat.decLt ((num 0) (var v_y)))
            (lam
              v_hy
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app
                Mettapedia.Languages.Lean.Recursion.StructuralCore.DivGo.accessible
                ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
            (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (num 0))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.Div.bridge
  (app
    Eq
    ((arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))
      (lam
        v_x
        (app Nat ())
        (lam v_y (app Nat ()) (app Mettapedia.Languages.Lean.Recursion.Core.Div.accessible ((var v_x) (var v_y)))))
      (lam v_x (app Nat ()) (lam v_y (app Nat ()) (app Nat.div ((var v_x) (var v_y)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.div.eq_1
  (pi
    v_x
    (app Nat ())
    (pi
      v_y
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.div ((var v_x) (var v_y)))
          (app
            dite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app Nat.decLt ((num 0) (var v_y)))
              (lam
                v_hy
                (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
                (app Nat.div.go ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
              (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (num 0))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.Div.equation0
  (pi
    v_x
    (app Nat ())
    (pi
      v_y
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.Core.Div.accessible ((var v_x) (var v_y)))
          (app
            dite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app Nat.decLt ((num 0) (var v_y)))
              (lam
                v_hy
                (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
                (app Nat.div.go ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
              (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (num 0))))))))
  (Axioms (Quot.sound)))

(LeanRecursionWrapper
  Nat.modCore
  (Accessible Mettapedia.Languages.Lean.Recursion.Core.ModCore.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.Core.ModCore.bridge)
  (Dependencies (Nat.modCore.go))
  (Equations ((Nat.modCore.eq_1 Mettapedia.Languages.Lean.Recursion.Core.ModCore.equation0))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.Core.ModCore.accessible
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_x
      (app Nat ())
      (lam
        v_y
        (app Nat ())
        (app
          dite
          ((app Nat ())
            (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
            (app Nat.decLt ((num 0) (var v_y)))
            (lam
              v_hy
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app
                Mettapedia.Languages.Lean.Recursion.StructuralCore.ModGo.accessible
                ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
            (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (var v_x))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.ModCore.bridge
  (app
    Eq
    ((arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))
      (lam
        v_x
        (app Nat ())
        (lam v_y (app Nat ()) (app Mettapedia.Languages.Lean.Recursion.Core.ModCore.accessible ((var v_x) (var v_y)))))
      (lam v_x (app Nat ()) (lam v_y (app Nat ()) (app Nat.modCore ((var v_x) (var v_y)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.modCore.eq_1
  (pi
    v_x
    (app Nat ())
    (pi
      v_y
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.modCore ((var v_x) (var v_y)))
          (app
            dite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app Nat.decLt ((num 0) (var v_y)))
              (lam
                v_hy
                (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
                (app Nat.modCore.go ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
              (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (var v_x))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.ModCore.equation0
  (pi
    v_x
    (app Nat ())
    (pi
      v_y
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.Core.ModCore.accessible ((var v_x) (var v_y)))
          (app
            dite
            ((app Nat ())
              (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
              (app Nat.decLt ((num 0) (var v_y)))
              (lam
                v_hy
                (app Nat.le ((app Nat.succ ((num 0))) (var v_y)))
                (app Nat.modCore.go ((var v_y) (proof) (app Nat.succ ((var v_x))) (var v_x) (proof))))
              (lam v_x2 (arrow (app Nat.le ((app Nat.succ ((num 0))) (var v_y))) (app False ())) (var v_x))))))))
  (Axioms (Quot.sound)))

(LeanRecursionWrapper
  Nat.mod
  (Accessible Mettapedia.Languages.Lean.Recursion.Core.Mod.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.Core.Mod.bridge)
  (Dependencies (Nat.modCore))
  (Equations
    ((Nat.mod.eq_1 Mettapedia.Languages.Lean.Recursion.Core.Mod.equation0)
      (Nat.mod.eq_2 Mettapedia.Languages.Lean.Recursion.Core.Mod.equation1))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.Core.Mod.accessible
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_x
      (app Nat ())
      (lam
        v_x1
        (app Nat ())
        (app
          Nat.mod.match_1
          ((lam v_x2 (app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())))
            (var v_x)
            (var v_x1)
            (lam v_x2 (app Nat ()) (num 0))
            (lam
              v_n
              (app Nat ())
              (lam
                v_x3
                (app Nat ())
                (lam
                  v_h
                  (app Eq ((app Nat ()) (var v_n) (app Nat.succ ((var v_x3)))))
                  (lam
                    v_m
                    (app Nat ())
                    (app
                      ite
                      ((app Nat ())
                        (app Nat.le ((var v_m) (var v_n)))
                        (app Nat.decLe ((var v_m) (var v_n)))
                        (app Mettapedia.Languages.Lean.Recursion.Core.ModCore.accessible ((var v_n) (var v_m)))
                        (var v_n)))))))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.Mod.bridge
  (app
    Eq
    ((arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))
      (lam
        v_x
        (app Nat ())
        (lam v_x1 (app Nat ()) (app Mettapedia.Languages.Lean.Recursion.Core.Mod.accessible ((var v_x) (var v_x1)))))
      (lam v_a (app Nat ()) (lam v_x1 (app Nat ()) (app Nat.mod ((var v_a) (var v_x1)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.mod.eq_1
  (pi v_x (app Nat ()) (app Eq ((app Nat ()) (app Nat.mod ((num 0) (var v_x))) (num 0))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.Mod.equation0
  (pi
    v_x
    (app Nat ())
    (app Eq ((app Nat ()) (app Mettapedia.Languages.Lean.Recursion.Core.Mod.accessible ((num 0) (var v_x))) (num 0))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Nat.mod.eq_2
  (pi
    v_x
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.mod ((app Nat.succ ((var v_n))) (var v_x)))
          (app
            ite
            ((app Nat ())
              (app Nat.le ((var v_x) (app Nat.succ ((var v_n)))))
              (app Nat.decLe ((var v_x) (app Nat.succ ((var v_n)))))
              (app Nat.modCore ((app Nat.succ ((var v_n))) (var v_x)))
              (app Nat.succ ((var v_n)))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.Mod.equation1
  (pi
    v_x
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.Core.Mod.accessible ((app Nat.succ ((var v_n))) (var v_x)))
          (app
            ite
            ((app Nat ())
              (app Nat.le ((var v_x) (app Nat.succ ((var v_n)))))
              (app Nat.decLe ((var v_x) (app Nat.succ ((var v_n)))))
              (app Nat.modCore ((app Nat.succ ((var v_n))) (var v_x)))
              (app Nat.succ ((var v_n)))))))))
  (Axioms (Quot.sound)))

(LeanRecursionWrapper
  Nat.minFac
  (Accessible Mettapedia.Languages.Lean.Recursion.Core.MinFac.accessible)
  (Bridge Mettapedia.Languages.Lean.Recursion.Core.MinFac.bridge)
  (Dependencies (Nat.minFacAux))
  (Equations ((Nat.minFac.eq_1 Mettapedia.Languages.Lean.Recursion.Core.MinFac.equation0))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.Core.MinFac.accessible
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value
    (lam
      v_n
      (app Nat ())
      (app
        ite
        ((app Nat ())
          (app
            Exists
            ((app Nat ()) (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((num 2) (var v_c))))))))
          (app Nat.decidable_dvd ((num 2) (var v_n)))
          (num 2)
          (app Mettapedia.Languages.Lean.Recursion.MeasuredCore.MinFacAux.accessible ((var v_n) (num 3))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.MinFac.bridge
  (app
    Eq
    ((arrow (app Nat ()) (app Nat ()))
      (lam v_n (app Nat ()) (app Mettapedia.Languages.Lean.Recursion.Core.MinFac.accessible ((var v_n))))
      (lam v_n (app Nat ()) (app Nat.minFac ((var v_n))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Nat.minFac.eq_1
  (pi
    v_n
    (app Nat ())
    (app
      Eq
      ((app Nat ())
        (app Nat.minFac ((var v_n)))
        (app
          ite
          ((app Nat ())
            (app
              Exists
              ((app Nat ()) (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((num 2) (var v_c))))))))
            (app Nat.decidable_dvd ((num 2) (var v_n)))
            (num 2)
            (app Nat.minFacAux ((var v_n) (num 3))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.Core.MinFac.equation0
  (pi
    v_n
    (app Nat ())
    (app
      Eq
      ((app Nat ())
        (app Mettapedia.Languages.Lean.Recursion.Core.MinFac.accessible ((var v_n)))
        (app
          ite
          ((app Nat ())
            (app
              Exists
              ((app Nat ()) (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((num 2) (var v_c))))))))
            (app Nat.decidable_dvd ((num 2) (var v_n)))
            (num 2)
            (app Nat.minFacAux ((var v_n) (num 3))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanFuelRecursion
  Nat.gcd
  (Fuel Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel)
  (Equations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel_succ))
  (SourceFuel Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel)
  (SourceFuelEquations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel_case0))
  (Adequate Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.adequate)
  (Budget Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.budget)
  (BudgetAdequate Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.budgetAdequate)
  (Reading Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.reading)
  (Bridge Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.bridge))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel
  (Type (arrow (app Nat ()) (arrow (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))))
  (Value
    (lam
      v_a
      (app Nat ())
      (lam
        v_x
        (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
        (app
          Mettapedia.Languages.Lean.Recursion.AccessibleRecipe.fuel
          ((app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
            (lam v_y (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
            (lam
              v_x2
              (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
              (app
                PSigma.casesOn
                ((app Nat ())
                  (lam v_m (app Nat ()) (app Nat ()))
                  (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                  (var v_x2)
                  (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m))))))
            (lam
              v__x
              (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
              (lam
                v_x3
                (pi
                  v_y
                  (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                  (arrow
                    (app
                      Nat.le
                      ((app
                          Nat.succ
                          ((app
                              PSigma.casesOn
                              ((app Nat ())
                                (lam v_m (app Nat ()) (app Nat ()))
                                (lam v_x4 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                                (var v_y)
                                (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                        (app
                          PSigma.casesOn
                          ((app Nat ())
                            (lam v_m (app Nat ()) (app Nat ()))
                            (lam v_x4 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                            (var v__x)
                            (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                    (app Nat ())))
                (app
                  PSigma.casesOn
                  ((app Nat ())
                    (lam v_m (app Nat ()) (app Nat ()))
                    (lam
                      v_x4
                      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                      (arrow
                        (pi
                          v_y
                          (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                          (arrow
                            (app
                              Nat.le
                              ((app
                                  Nat.succ
                                  ((app
                                      PSigma.casesOn
                                      ((app Nat ())
                                        (lam v_m (app Nat ()) (app Nat ()))
                                        (lam
                                          v_x6
                                          (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                                          (app Nat ()))
                                        (var v_y)
                                        (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                                (app
                                  PSigma.casesOn
                                  ((app Nat ())
                                    (lam v_m (app Nat ()) (app Nat ()))
                                    (lam
                                      v_x6
                                      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                                      (app Nat ()))
                                    (var v_x4)
                                    (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                            (app Nat ())))
                        (app Nat ())))
                    (var v__x)
                    (lam
                      v_m
                      (app Nat ())
                      (lam
                        v_n
                        (app Nat ())
                        (lam
                          v_x6
                          (pi
                            v_y
                            (app PSigma ((app Nat ()) (lam v_x6 (app Nat ()) (app Nat ()))))
                            (arrow
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        PSigma.casesOn
                                        ((app Nat ())
                                          (lam v_x7 (app Nat ()) (app Nat ()))
                                          (lam
                                            v_x7
                                            (app PSigma ((app Nat ()) (lam v_x7 (app Nat ()) (app Nat ()))))
                                            (app Nat ()))
                                          (var v_y)
                                          (lam v_x7 (app Nat ()) (lam v_x8 (app Nat ()) (var v_x7)))))))
                                  (app
                                    PSigma.casesOn
                                    ((app Nat ())
                                      (lam v_x7 (app Nat ()) (app Nat ()))
                                      (lam
                                        v_x7
                                        (app PSigma ((app Nat ()) (lam v_x7 (app Nat ()) (app Nat ()))))
                                        (app Nat ()))
                                      (app
                                        PSigma.mk
                                        ((app Nat ()) (lam v_x7 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                                      (lam v_x7 (app Nat ()) (lam v_x8 (app Nat ()) (var v_x7)))))))
                              (app Nat ())))
                          (app
                            dite
                            ((app Nat ())
                              (app Eq ((app Nat ()) (var v_m) (num 0)))
                              (app instDecidableEqNat ((var v_m) (num 0)))
                              (lam v_h (app Eq ((app Nat ()) (var v_m) (num 0))) (var v_n))
                              (lam
                                v_h
                                (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
                                (apv
                                  (var v_x6)
                                  ((app
                                      PSigma.mk
                                      ((app Nat ())
                                        (lam v_x8 (app Nat ()) (app Nat ()))
                                        (app Nat.mod ((var v_n) (var v_m)))
                                        (var v_m)))
                                    (proof)))))))))
                    (var v_x3)))))
            (lam v_state (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat.zero ()))
            (var v_a)
            (var v_x)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))))
  (Value
    (lam
      v_fuel
      (app Nat ())
      (lam
        v_m
        (app Nat ())
        (lam
          v_n
          (app Nat ())
          (app
            Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel
            ((var v_fuel) (app PSigma.mk ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())) (var v_m) (var v_n))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.budget
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value (lam v_m (app Nat ()) (lam v_n (app Nat ()) (app Nat.succ ((var v_m)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.reading
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_m
      (app Nat ())
      (lam
        v_n
        (app Nat ())
        (app
          Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
          ((app Nat.succ ((var v_m))) (var v_m) (var v_n)))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel_zero
  (pi
    v_state
    (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
    (app
      Eq
      ((app Nat ())
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel ((num 0) (var v_state)))
        (app Nat.zero ()))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_state
      (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel ((app Nat.succ ((var v_fuel))) (var v_state)))
          (app
            PSigma.casesOn
            ((app Nat ())
              (lam v_m (app Nat ()) (app Nat ()))
              (lam
                v__x
                (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                (arrow
                  (pi
                    v_y
                    (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                    (arrow
                      (app
                        Nat.le
                        ((app
                            Nat.succ
                            ((app
                                PSigma.casesOn
                                ((app Nat ())
                                  (lam v_m (app Nat ()) (app Nat ()))
                                  (lam
                                    v_x4
                                    (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                                    (app Nat ()))
                                  (var v_y)
                                  (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                          (app
                            PSigma.casesOn
                            ((app Nat ())
                              (lam v_m (app Nat ()) (app Nat ()))
                              (lam v_x4 (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                              (var v__x)
                              (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                      (app Nat ())))
                  (app Nat ())))
              (var v_state)
              (lam
                v_m
                (app Nat ())
                (lam
                  v_n
                  (app Nat ())
                  (lam
                    v_a
                    (pi
                      v_y
                      (app PSigma ((app Nat ()) (lam v_x4 (app Nat ()) (app Nat ()))))
                      (arrow
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app
                                  PSigma.casesOn
                                  ((app Nat ())
                                    (lam v_x5 (app Nat ()) (app Nat ()))
                                    (lam
                                      v__x
                                      (app PSigma ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ()))))
                                      (app Nat ()))
                                    (var v_y)
                                    (lam v_x5 (app Nat ()) (lam v_x6 (app Nat ()) (var v_x5)))))))
                            (app
                              PSigma.casesOn
                              ((app Nat ())
                                (lam v_x5 (app Nat ()) (app Nat ()))
                                (lam v__x (app PSigma ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ())))) (app Nat ()))
                                (app PSigma.mk ((app Nat ()) (lam v_x5 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                                (lam v_x5 (app Nat ()) (lam v_x6 (app Nat ()) (var v_x5)))))))
                        (app Nat ())))
                    (app
                      dite
                      ((app Nat ())
                        (app Eq ((app Nat ()) (var v_m) (num 0)))
                        (app instDecidableEqNat ((var v_m) (num 0)))
                        (lam v_h (app Eq ((app Nat ()) (var v_m) (num 0))) (var v_n))
                        (lam
                          v_h
                          (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
                          (apv
                            (var v_a)
                            ((app
                                PSigma.mk
                                ((app Nat ())
                                  (lam v_x6 (app Nat ()) (app Nat ()))
                                  (app Nat.mod ((var v_n) (var v_m)))
                                  (var v_m)))
                              (proof)))))))))
              (lam
                v_smaller
                (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ()))))
                (lam
                  v_decrease
                  (app
                    Nat.le
                    ((app
                        Nat.succ
                        ((app
                            PSigma.casesOn
                            ((app Nat ())
                              (lam v_m (app Nat ()) (app Nat ()))
                              (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                              (var v_smaller)
                              (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                      (app
                        PSigma.casesOn
                        ((app Nat ())
                          (lam v_m (app Nat ()) (app Nat ()))
                          (lam v__x (app PSigma ((app Nat ()) (lam v_m (app Nat ()) (app Nat ())))) (app Nat ()))
                          (var v_state)
                          (lam v_m (app Nat ()) (lam v_n (app Nat ()) (var v_m)))))))
                  (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel ((var v_fuel) (var v_smaller)))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_m
      (app Nat ())
      (pi
        v_n
        (app Nat ())
        (app
          Eq
          ((app Nat ())
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
              ((app Nat.succ ((var v_fuel))) (var v_m) (var v_n)))
            (app
              dite
              ((app Nat ())
                (app Eq ((app Nat ()) (var v_m) (num 0)))
                (app instDecidableEqNat ((var v_m) (num 0)))
                (lam v_h (app Eq ((app Nat ()) (var v_m) (num 0))) (var v_n))
                (lam
                  v_h
                  (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
                    ((var v_fuel) (app Nat.mod ((var v_n) (var v_m))) (var v_m)))))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.adequate
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (pi
        v_fuel
        (app Nat ())
        (arrow
          (app
            Nat.le
            ((app
                Nat.succ
                ((app
                    PSigma.casesOn
                    ((app Nat ())
                      (lam v_x3 (app Nat ()) (app Nat ()))
                      (lam v__x (app PSigma ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())))) (app Nat ()))
                      (app PSigma.mk ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                      (lam v_x3 (app Nat ()) (lam v_x4 (app Nat ()) (var v_x3)))))))
              (var v_fuel)))
          (app
            Eq
            ((app Nat ())
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.fuel
                ((var v_fuel) (app PSigma.mk ((app Nat ()) (lam v_x3 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))))
              (app Nat.gcd ((var v_m) (var v_n)))))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.budgetAdequate
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Nat.le
        ((app
            Nat.succ
            ((app
                PSigma.casesOn
                ((app Nat ())
                  (lam v_x2 (app Nat ()) (app Nat ()))
                  (lam v__x (app PSigma ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())))) (app Nat ()))
                  (app PSigma.mk ((app Nat ()) (lam v_x2 (app Nat ()) (app Nat ())) (var v_m) (var v_n)))
                  (lam v_x2 (app Nat ()) (lam v_x3 (app Nat ()) (var v_x2)))))))
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.budget ((var v_m) (var v_n)))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.bridge
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.gcd ((var v_m) (var v_n)))
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.reading ((var v_m) (var v_n)))))))
  (Axioms (Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel_zero
  (pi
    v_m
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel ((num 0) (var v_m) (var v_n)))
          (app Nat.zero ())))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel_case0
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_m
      (app Nat ())
      (pi
        v_n
        (app Nat ())
        (app
          Eq
          ((app Nat ())
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
              ((app Nat.succ ((var v_fuel))) (var v_m) (var v_n)))
            (app
              dite
              ((app Nat ())
                (app Eq ((app Nat ()) (var v_m) (num 0)))
                (app instDecidableEqNat ((var v_m) (num 0)))
                (lam v_h (app Eq ((app Nat ()) (var v_m) (num 0))) (var v_n))
                (lam
                  v_h
                  (arrow (app Eq ((app Nat ()) (var v_m) (num 0))) (app False ()))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.Gcd.sourceFuel
                    ((var v_fuel) (app Nat.mod ((var v_n) (var v_m))) (var v_m)))))))))))
  (Axioms ()))

(LeanFuelRecursion
  List.mergeSort
  (Fuel Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel)
  (Equations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel_succ))
  (SourceFuel Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel)
  (SourceFuelEquations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case0
      Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case1
      Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case2))
  (Adequate Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.adequate)
  (Budget Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.budget)
  (BudgetAdequate Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.budgetAdequate)
  (Reading Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.reading)
  (Bridge Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.bridge))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app Nat ())
        (arrow
          (app
            PSigma
            ((app List ((var v_u945)))
              (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
          (app List ((var v_u945)))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_a
        (app Nat ())
        (lam
          v_x
          (app
            PSigma
            ((app List ((var v_u945)))
              (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
          (app
            Mettapedia.Languages.Lean.Recursion.AccessibleRecipe.fuel
            ((app
                PSigma
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
              (lam
                v_y
                (app
                  PSigma
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                (app List ((var v_u945))))
              (lam
                v_x3
                (app
                  PSigma
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                (app
                  PSigma.casesOn
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                    (lam
                      v__x
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (app Nat ()))
                    (var v_x3)
                    (lam
                      v_xs
                      (app List ((var v_u945)))
                      (lam
                        v_le
                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                        (app List.length ((var v_u945) (var v_xs))))))))
              (lam
                v__x
                (app
                  PSigma
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                (lam
                  v_x4
                  (pi
                    v_y
                    (app
                      PSigma
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                    (arrow
                      (app
                        Nat.le
                        ((app
                            Nat.succ
                            ((app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                  (lam
                                    v_x5
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_xs
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                    (app Nat ()))
                                  (var v_y)
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (lam
                                      v_le
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                      (app List.length ((var v_u945) (var v_xs)))))))))
                          (app
                            PSigma.casesOn
                            ((app List ((var v_u945)))
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                              (lam
                                v_x5
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_xs
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                (app Nat ()))
                              (var v__x)
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (lam
                                  v_le
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                  (app List.length ((var v_u945) (var v_xs)))))))))
                      (app List ((var v_u945)))))
                  (app
                    PSigma.casesOn
                    ((app List ((var v_u945)))
                      (lam v_x5 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                      (lam
                        v_x5
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_x5
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (arrow
                          (pi
                            v_y
                            (app
                              PSigma
                              ((app List ((var v_u945)))
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                            (arrow
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_xs
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (lam
                                            v_x7
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_xs
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                            (app Nat ()))
                                          (var v_y)
                                          (lam
                                            v_xs
                                            (app List ((var v_u945)))
                                            (lam
                                              v_le
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                              (app List.length ((var v_u945) (var v_xs)))))))))
                                  (app
                                    PSigma.casesOn
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_xs
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (lam
                                        v_x7
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_xs
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (app Nat ()))
                                      (var v_x5)
                                      (lam
                                        v_xs
                                        (app List ((var v_u945)))
                                        (lam
                                          v_le
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                          (app List.length ((var v_u945) (var v_xs)))))))))
                              (app List ((var v_u945)))))
                          (app List ((var v_u945)))))
                      (var v__x)
                      (lam
                        v_xs
                        (app List ((var v_u945)))
                        (lam
                          v_le
                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                          (lam
                            v_x7
                            (pi
                              v_y
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x7
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                              (arrow
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (lam
                                              v_x8
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x8
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                              (app Nat ()))
                                            (var v_y)
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x9
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                (app List.length ((var v_u945) (var v_x8)))))))))
                                    (app
                                      PSigma.casesOn
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x8
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                        (lam
                                          v_x8
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                          (app Nat ()))
                                        (app
                                          PSigma.mk
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x8
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (var v_xs)
                                            (var v_le)))
                                        (lam
                                          v_x8
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x9
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                            (app List.length ((var v_u945) (var v_x8)))))))))
                                (app List ((var v_u945)))))
                            (app
                              _private.Init.Data.List.Sort.Basic.0.List.mergeSort.match_1
                              ((var v_u945)
                                (lam
                                  v_x8
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x9
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                    (arrow
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (arrow
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    PSigma.casesOn
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (lam
                                                        v_x11
                                                        (app
                                                          PSigma
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x11
                                                              (app List ((var v_u945)))
                                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                        (app Nat ()))
                                                      (var v_y)
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (lam
                                                          v_x12
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                          (app List.length ((var v_u945) (var v_x11)))))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                    (app Nat ()))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (var v_x8)
                                                      (var v_x9)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                      (app List.length ((var v_u945) (var v_x11)))))))))
                                          (app List ((var v_u945)))))
                                      (app List ((var v_u945))))))
                                (var v_xs)
                                (var v_le)
                                (lam
                                  v_x8
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                  (lam
                                    v_x9
                                    (pi
                                      v_y
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                      (arrow
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  PSigma.casesOn
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x10
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (lam
                                                      v_x10
                                                      (app
                                                        PSigma
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x10
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                      (app Nat ()))
                                                    (var v_y)
                                                    (lam
                                                      v_x10
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                        (app List.length ((var v_u945) (var v_x10)))))))))
                                            (app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x10
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (lam
                                                  v_x10
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x10
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                  (app Nat ()))
                                                (app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x10
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (app List.nil ((var v_u945)))
                                                    (var v_x8)))
                                                (lam
                                                  v_x10
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x11
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                    (app List.length ((var v_u945) (var v_x10)))))))))
                                        (app List ((var v_u945)))))
                                    (app List.nil ((var v_u945)))))
                                (lam
                                  v_x8
                                  (var v_u945)
                                  (lam
                                    v_x9
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                    (lam
                                      v_x10
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (arrow
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    PSigma.casesOn
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (lam
                                                        v_x11
                                                        (app
                                                          PSigma
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x11
                                                              (app List ((var v_u945)))
                                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                        (app Nat ()))
                                                      (var v_y)
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (lam
                                                          v_x12
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                          (app List.length ((var v_u945) (var v_x11)))))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                    (app Nat ()))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (app
                                                        List.cons
                                                        ((var v_u945) (var v_x8) (app List.nil ((var v_u945)))))
                                                      (var v_x9)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                      (app List.length ((var v_u945) (var v_x11)))))))))
                                          (app List ((var v_u945)))))
                                      (app List.cons ((var v_u945) (var v_x8) (app List.nil ((var v_u945))))))))
                                (lam
                                  v_x8
                                  (var v_u945)
                                  (lam
                                    v_b
                                    (var v_u945)
                                    (lam
                                      v_x10
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x11
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                        (lam
                                          v_x12
                                          (pi
                                            v_y
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                            (arrow
                                              (app
                                                Nat.le
                                                ((app
                                                    Nat.succ
                                                    ((app
                                                        PSigma.casesOn
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x13
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (lam
                                                            v_x13
                                                            (app
                                                              PSigma
                                                              ((app List ((var v_u945)))
                                                                (lam
                                                                  v_x13
                                                                  (app List ((var v_u945)))
                                                                  (arrow
                                                                    (var v_u945)
                                                                    (arrow (var v_u945) (app Bool ()))))))
                                                            (app Nat ()))
                                                          (var v_y)
                                                          (lam
                                                            v_x13
                                                            (app List ((var v_u945)))
                                                            (lam
                                                              v_x14
                                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                              (app List.length ((var v_u945) (var v_x13)))))))))
                                                  (app
                                                    PSigma.casesOn
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x13
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (lam
                                                        v_x13
                                                        (app
                                                          PSigma
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x13
                                                              (app List ((var v_u945)))
                                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                        (app Nat ()))
                                                      (app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x13
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (app
                                                            List.cons
                                                            ((var v_u945)
                                                              (var v_x8)
                                                              (app List.cons ((var v_u945) (var v_b) (var v_x10)))))
                                                          (var v_x11)))
                                                      (lam
                                                        v_x13
                                                        (app List ((var v_u945)))
                                                        (lam
                                                          v_x14
                                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                          (app List.length ((var v_u945) (var v_x13)))))))))
                                              (app List ((var v_u945)))))
                                          (apv
                                            (lam
                                              v_lr
                                              (app
                                                Prod
                                                ((app
                                                    Subtype
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  Nat.add
                                                                  ((app
                                                                      List.length
                                                                      ((var v_u945)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945)
                                                                            (var v_x8)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945) (var v_b) (var v_x10)))))))
                                                                    (num 1)))
                                                                (num 2))))))))
                                                  (app
                                                    Subtype
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  List.length
                                                                  ((var v_u945)
                                                                    (app
                                                                      List.cons
                                                                      ((var v_u945)
                                                                        (var v_x8)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945) (var v_b) (var v_x10)))))))
                                                                (num 2))))))))))
                                              (app
                                                List.merge
                                                ((var v_u945)
                                                  (apv
                                                    (var v_x12)
                                                    ((app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x14
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (app
                                                            Subtype.val
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          Nat.add
                                                                          ((app
                                                                              List.length
                                                                              ((var v_u945)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x8)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_b)
                                                                                        (var v_x10)))))))
                                                                            (num 1)))
                                                                        (num 2))))))
                                                              (app
                                                                Prod.fst
                                                                ((app
                                                                    Subtype
                                                                    ((app List ((var v_u945)))
                                                                      (lam
                                                                        v_l
                                                                        (app List ((var v_u945)))
                                                                        (app
                                                                          Eq
                                                                          ((app Nat ())
                                                                            (app List.length ((var v_u945) (var v_l)))
                                                                            (app
                                                                              Nat.div
                                                                              ((app
                                                                                  Nat.add
                                                                                  ((app
                                                                                      List.length
                                                                                      ((var v_u945)
                                                                                        (app
                                                                                          List.cons
                                                                                          ((var v_u945)
                                                                                            (var v_x8)
                                                                                            (app
                                                                                              List.cons
                                                                                              ((var v_u945)
                                                                                                (var v_b)
                                                                                                (var v_x10)))))))
                                                                                    (num 1)))
                                                                                (num 2))))))))
                                                                  (app
                                                                    Subtype
                                                                    ((app List ((var v_u945)))
                                                                      (lam
                                                                        v_l
                                                                        (app List ((var v_u945)))
                                                                        (app
                                                                          Eq
                                                                          ((app Nat ())
                                                                            (app List.length ((var v_u945) (var v_l)))
                                                                            (app
                                                                              Nat.div
                                                                              ((app
                                                                                  List.length
                                                                                  ((var v_u945)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_x8)
                                                                                        (app
                                                                                          List.cons
                                                                                          ((var v_u945)
                                                                                            (var v_b)
                                                                                            (var v_x10)))))))
                                                                                (num 2))))))))
                                                                  (var v_lr)))))
                                                          (var v_x11)))
                                                      (proof)))
                                                  (apv
                                                    (var v_x12)
                                                    ((app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x14
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (app
                                                            Subtype.val
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_x8)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_b)
                                                                                    (var v_x10)))))))
                                                                        (num 2))))))
                                                              (app
                                                                Prod.snd
                                                                ((app
                                                                    Subtype
                                                                    ((app List ((var v_u945)))
                                                                      (lam
                                                                        v_l
                                                                        (app List ((var v_u945)))
                                                                        (app
                                                                          Eq
                                                                          ((app Nat ())
                                                                            (app List.length ((var v_u945) (var v_l)))
                                                                            (app
                                                                              Nat.div
                                                                              ((app
                                                                                  Nat.add
                                                                                  ((app
                                                                                      List.length
                                                                                      ((var v_u945)
                                                                                        (app
                                                                                          List.cons
                                                                                          ((var v_u945)
                                                                                            (var v_x8)
                                                                                            (app
                                                                                              List.cons
                                                                                              ((var v_u945)
                                                                                                (var v_b)
                                                                                                (var v_x10)))))))
                                                                                    (num 1)))
                                                                                (num 2))))))))
                                                                  (app
                                                                    Subtype
                                                                    ((app List ((var v_u945)))
                                                                      (lam
                                                                        v_l
                                                                        (app List ((var v_u945)))
                                                                        (app
                                                                          Eq
                                                                          ((app Nat ())
                                                                            (app List.length ((var v_u945) (var v_l)))
                                                                            (app
                                                                              Nat.div
                                                                              ((app
                                                                                  List.length
                                                                                  ((var v_u945)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_x8)
                                                                                        (app
                                                                                          List.cons
                                                                                          ((var v_u945)
                                                                                            (var v_b)
                                                                                            (var v_x10)))))))
                                                                                (num 2))))))))
                                                                  (var v_lr)))))
                                                          (var v_x11)))
                                                      (proof)))
                                                  (var v_x11))))
                                            ((app
                                                List.MergeSort.Internal.splitInTwo
                                                ((var v_u945)
                                                  (app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_x8)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_x10)))))))
                                                  (app
                                                    Subtype.mk
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              List.length
                                                              ((var v_u945)
                                                                (app
                                                                  List.cons
                                                                  ((var v_u945)
                                                                    (var v_x8)
                                                                    (app
                                                                      List.cons
                                                                      ((var v_u945) (var v_b) (var v_x10))))))))))
                                                      (app
                                                        List.cons
                                                        ((var v_u945)
                                                          (var v_x8)
                                                          (app List.cons ((var v_u945) (var v_b) (var v_x10)))))
                                                      (proof))))))))))))
                                (var v_x7))))))
                      (var v_x4)))))
              (lam
                v_state
                (app
                  PSigma
                  ((app List ((var v_u945)))
                    (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                (app List.nil ((var v_u945))))
              (var v_a)
              (var v_x))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
  (Type
    (arrow
      (app Nat ())
      (pi
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (arrow
          (app List ((var v_u945)))
          (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945))))))))
  (Value
    (lam
      v_fuel
      (app Nat ())
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel
              ((var v_u945)
                (var v_fuel)
                (app
                  PSigma.mk
                  ((app List ((var v_u945)))
                    (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                    (var v_xs)
                    (var v_le)))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.budget
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow (app List ((var v_u945))) (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app Nat ())))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_xs
        (app List ((var v_u945)))
        (lam
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app Nat.succ ((app List.length ((var v_u945) (var v_xs))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.reading
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app List ((var v_u945)))
        (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945)))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_xs
        (app List ((var v_u945)))
        (lam
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
            ((app Nat.succ ((app List.length ((var v_u945) (var v_xs))))) (var v_u945) (var v_xs) (var v_le))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel_zero
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_state
      (app
        PSigma
        ((app List ((var v_u945)))
          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
      (app
        Eq
        ((app List ((var v_u945)))
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel ((var v_u945) (num 0) (var v_state)))
          (app List.nil ((var v_u945)))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel_succ
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_fuel
      (app Nat ())
      (pi
        v_state
        (app
          PSigma
          ((app List ((var v_u945)))
            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel
              ((var v_u945) (app Nat.succ ((var v_fuel))) (var v_state)))
            (app
              PSigma.casesOn
              ((app List ((var v_u945)))
                (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                (lam
                  v__x
                  (app
                    PSigma
                    ((app List ((var v_u945)))
                      (lam v_x (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                  (arrow
                    (pi
                      v_y
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (arrow
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app
                                  PSigma.casesOn
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_xs
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                    (lam
                                      v_x5
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_xs
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                      (app Nat ()))
                                    (var v_y)
                                    (lam
                                      v_xs
                                      (app List ((var v_u945)))
                                      (lam
                                        v_le
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                        (app List.length ((var v_u945) (var v_xs)))))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                (lam
                                  v_x5
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_xs
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (app Nat ()))
                                (var v__x)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_le
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                    (app List.length ((var v_u945) (var v_xs)))))))))
                        (app List ((var v_u945)))))
                    (app List ((var v_u945)))))
                (var v_state)
                (lam
                  v_xs
                  (app List ((var v_u945)))
                  (lam
                    v_le
                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                    (lam
                      v_a
                      (pi
                        v_y
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_x5
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (arrow
                          (app
                            Nat.le
                            ((app
                                Nat.succ
                                ((app
                                    PSigma.casesOn
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x6
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (lam
                                        v__x
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x6
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (app Nat ()))
                                      (var v_y)
                                      (lam
                                        v_x6
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x7
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                          (app List.length ((var v_u945) (var v_x6)))))))))
                              (app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x6
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                  (lam
                                    v__x
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x6
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                    (app Nat ()))
                                  (app
                                    PSigma.mk
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (var v_xs)
                                      (var v_le)))
                                  (lam
                                    v_x6
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x7
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                      (app List.length ((var v_u945) (var v_x6)))))))))
                          (app List ((var v_u945)))))
                      (app
                        _private.Init.Data.List.Sort.Basic.0.List.mergeSort.match_1
                        ((var v_u945)
                          (lam
                            v_x
                            (app List ((var v_u945)))
                            (lam
                              v_x7
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                              (arrow
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x8
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (arrow
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (lam
                                                  v__x
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x9
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                  (app Nat ()))
                                                (var v_y)
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x10
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                    (app List.length ((var v_u945) (var v_x9)))))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x9
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                              (app Nat ()))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (var v_x)
                                                (var v_x7)))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                (app List.length ((var v_u945) (var v_x9)))))))))
                                    (app List ((var v_u945)))))
                                (app List ((var v_u945))))))
                          (var v_xs)
                          (var v_le)
                          (lam
                            v_x
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (lam
                              v_x7
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x7
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                (arrow
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (lam
                                                v__x
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x8
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                (app Nat ()))
                                              (var v_y)
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                  (app List.length ((var v_u945) (var v_x8)))))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x8
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (lam
                                            v__x
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x8
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                            (app Nat ()))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (app List.nil ((var v_u945)))
                                              (var v_x)))
                                          (lam
                                            v_x8
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x9
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                              (app List.length ((var v_u945) (var v_x8)))))))))
                                  (app List ((var v_u945)))))
                              (app List.nil ((var v_u945)))))
                          (lam
                            v_x6
                            (var v_u945)
                            (lam
                              v_x
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                              (lam
                                v_x8
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x8
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (arrow
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (lam
                                                  v__x
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x9
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                  (app Nat ()))
                                                (var v_y)
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x10
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                    (app List.length ((var v_u945) (var v_x9)))))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x9
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                              (app Nat ()))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (app List.cons ((var v_u945) (var v_x6) (app List.nil ((var v_u945)))))
                                                (var v_x)))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                (app List.length ((var v_u945) (var v_x9)))))))))
                                    (app List ((var v_u945)))))
                                (app List.cons ((var v_u945) (var v_x6) (app List.nil ((var v_u945))))))))
                          (lam
                            v_x6
                            (var v_u945)
                            (lam
                              v_b
                              (var v_u945)
                              (lam
                                v_x8
                                (app List ((var v_u945)))
                                (lam
                                  v_x9
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                  (lam
                                    v_x
                                    (pi
                                      v_y
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                      (arrow
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  PSigma.casesOn
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x11
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (lam
                                                      v__x
                                                      (app
                                                        PSigma
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x11
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                      (app Nat ()))
                                                    (var v_y)
                                                    (lam
                                                      v_x11
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x12
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                        (app List.length ((var v_u945) (var v_x11)))))))))
                                            (app
                                              PSigma.casesOn
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x11
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (lam
                                                  v__x
                                                  (app
                                                    PSigma
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                                  (app Nat ()))
                                                (app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_x6)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_x8)))))
                                                    (var v_x9)))
                                                (lam
                                                  v_x11
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x12
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                                    (app List.length ((var v_u945) (var v_x11)))))))))
                                        (app List ((var v_u945)))))
                                    (apv
                                      (lam
                                        v_lr
                                        (app
                                          Prod
                                          ((app
                                              Subtype
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_l
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Eq
                                                    ((app Nat ())
                                                      (app List.length ((var v_u945) (var v_l)))
                                                      (app
                                                        Nat.div
                                                        ((app
                                                            Nat.add
                                                            ((app
                                                                List.length
                                                                ((var v_u945)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945)
                                                                      (var v_x6)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945) (var v_b) (var v_x8)))))))
                                                              (num 1)))
                                                          (num 2))))))))
                                            (app
                                              Subtype
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_l
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Eq
                                                    ((app Nat ())
                                                      (app List.length ((var v_u945) (var v_l)))
                                                      (app
                                                        Nat.div
                                                        ((app
                                                            List.length
                                                            ((var v_u945)
                                                              (app
                                                                List.cons
                                                                ((var v_u945)
                                                                  (var v_x6)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945) (var v_b) (var v_x8)))))))
                                                          (num 2))))))))))
                                        (app
                                          List.merge
                                          ((var v_u945)
                                            (apv
                                              (var v_x)
                                              ((app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (app
                                                      Subtype.val
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_l
                                                          (app List ((var v_u945)))
                                                          (app
                                                            Eq
                                                            ((app Nat ())
                                                              (app List.length ((var v_u945) (var v_l)))
                                                              (app
                                                                Nat.div
                                                                ((app
                                                                    Nat.add
                                                                    ((app
                                                                        List.length
                                                                        ((var v_u945)
                                                                          (app
                                                                            List.cons
                                                                            ((var v_u945)
                                                                              (var v_x6)
                                                                              (app
                                                                                List.cons
                                                                                ((var v_u945) (var v_b) (var v_x8)))))))
                                                                      (num 1)))
                                                                  (num 2))))))
                                                        (app
                                                          Prod.fst
                                                          ((app
                                                              Subtype
                                                              ((app List ((var v_u945)))
                                                                (lam
                                                                  v_l
                                                                  (app List ((var v_u945)))
                                                                  (app
                                                                    Eq
                                                                    ((app Nat ())
                                                                      (app List.length ((var v_u945) (var v_l)))
                                                                      (app
                                                                        Nat.div
                                                                        ((app
                                                                            Nat.add
                                                                            ((app
                                                                                List.length
                                                                                ((var v_u945)
                                                                                  (app
                                                                                    List.cons
                                                                                    ((var v_u945)
                                                                                      (var v_x6)
                                                                                      (app
                                                                                        List.cons
                                                                                        ((var v_u945)
                                                                                          (var v_b)
                                                                                          (var v_x8)))))))
                                                                              (num 1)))
                                                                          (num 2))))))))
                                                            (app
                                                              Subtype
                                                              ((app List ((var v_u945)))
                                                                (lam
                                                                  v_l
                                                                  (app List ((var v_u945)))
                                                                  (app
                                                                    Eq
                                                                    ((app Nat ())
                                                                      (app List.length ((var v_u945) (var v_l)))
                                                                      (app
                                                                        Nat.div
                                                                        ((app
                                                                            List.length
                                                                            ((var v_u945)
                                                                              (app
                                                                                List.cons
                                                                                ((var v_u945)
                                                                                  (var v_x6)
                                                                                  (app
                                                                                    List.cons
                                                                                    ((var v_u945)
                                                                                      (var v_b)
                                                                                      (var v_x8)))))))
                                                                          (num 2))))))))
                                                            (var v_lr)))))
                                                    (var v_x9)))
                                                (proof)))
                                            (apv
                                              (var v_x)
                                              ((app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (app
                                                      Subtype.val
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_l
                                                          (app List ((var v_u945)))
                                                          (app
                                                            Eq
                                                            ((app Nat ())
                                                              (app List.length ((var v_u945) (var v_l)))
                                                              (app
                                                                Nat.div
                                                                ((app
                                                                    List.length
                                                                    ((var v_u945)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945)
                                                                          (var v_x6)
                                                                          (app
                                                                            List.cons
                                                                            ((var v_u945) (var v_b) (var v_x8)))))))
                                                                  (num 2))))))
                                                        (app
                                                          Prod.snd
                                                          ((app
                                                              Subtype
                                                              ((app List ((var v_u945)))
                                                                (lam
                                                                  v_l
                                                                  (app List ((var v_u945)))
                                                                  (app
                                                                    Eq
                                                                    ((app Nat ())
                                                                      (app List.length ((var v_u945) (var v_l)))
                                                                      (app
                                                                        Nat.div
                                                                        ((app
                                                                            Nat.add
                                                                            ((app
                                                                                List.length
                                                                                ((var v_u945)
                                                                                  (app
                                                                                    List.cons
                                                                                    ((var v_u945)
                                                                                      (var v_x6)
                                                                                      (app
                                                                                        List.cons
                                                                                        ((var v_u945)
                                                                                          (var v_b)
                                                                                          (var v_x8)))))))
                                                                              (num 1)))
                                                                          (num 2))))))))
                                                            (app
                                                              Subtype
                                                              ((app List ((var v_u945)))
                                                                (lam
                                                                  v_l
                                                                  (app List ((var v_u945)))
                                                                  (app
                                                                    Eq
                                                                    ((app Nat ())
                                                                      (app List.length ((var v_u945) (var v_l)))
                                                                      (app
                                                                        Nat.div
                                                                        ((app
                                                                            List.length
                                                                            ((var v_u945)
                                                                              (app
                                                                                List.cons
                                                                                ((var v_u945)
                                                                                  (var v_x6)
                                                                                  (app
                                                                                    List.cons
                                                                                    ((var v_u945)
                                                                                      (var v_b)
                                                                                      (var v_x8)))))))
                                                                          (num 2))))))))
                                                            (var v_lr)))))
                                                    (var v_x9)))
                                                (proof)))
                                            (var v_x9))))
                                      ((app
                                          List.MergeSort.Internal.splitInTwo
                                          ((var v_u945)
                                            (app
                                              List.length
                                              ((var v_u945)
                                                (app
                                                  List.cons
                                                  ((var v_u945)
                                                    (var v_x6)
                                                    (app List.cons ((var v_u945) (var v_b) (var v_x8)))))))
                                            (app
                                              Subtype.mk
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_l
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Eq
                                                    ((app Nat ())
                                                      (app List.length ((var v_u945) (var v_l)))
                                                      (app
                                                        List.length
                                                        ((var v_u945)
                                                          (app
                                                            List.cons
                                                            ((var v_u945)
                                                              (var v_x6)
                                                              (app List.cons ((var v_u945) (var v_b) (var v_x8))))))))))
                                                (app
                                                  List.cons
                                                  ((var v_u945)
                                                    (var v_x6)
                                                    (app List.cons ((var v_u945) (var v_b) (var v_x8)))))
                                                (proof))))))))))))
                          (var v_a))))))
                (lam
                  v_smaller
                  (app
                    PSigma
                    ((app List ((var v_u945)))
                      (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                  (lam
                    v_decrease
                    (app
                      Nat.le
                      ((app
                          Nat.succ
                          ((app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                (lam
                                  v__x
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_xs
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (app Nat ()))
                                (var v_smaller)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_le
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                    (app List.length ((var v_u945) (var v_xs)))))))))
                        (app
                          PSigma.casesOn
                          ((app List ((var v_u945)))
                            (lam v_xs (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (lam
                              v__x
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                              (app Nat ()))
                            (var v_state)
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (lam
                                v_le
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                                (app List.length ((var v_u945) (var v_xs)))))))))
                    (app
                      Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel
                      ((var v_u945) (var v_fuel) (var v_smaller))))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_xs
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                ((app Nat.succ ((var v_fuel))) (var v_u945) (var v_xs) (var v_le)))
              (app
                List.rec
                ((var v_u945)
                  (lam
                    v_x
                    (app List ((var v_u945)))
                    (arrow
                      (pi
                        v_y
                        (app
                          PSigma
                          ((app List ((var v_u945)))
                            (lam
                              v_x5
                              (app List ((var v_u945)))
                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                        (arrow
                          (app
                            Nat.le
                            ((app
                                Nat.succ
                                ((app
                                    List.length
                                    ((var v_u945)
                                      (app
                                        PSigma.fst
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x6
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (var v_y)))))))
                              (app
                                List.length
                                ((var v_u945)
                                  (app
                                    PSigma.fst
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x6
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (app
                                        PSigma.mk
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x6
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (var v_x)
                                          (var v_le)))))))))
                          (app List ((var v_u945)))))
                      (app List ((var v_u945)))))
                  (lam
                    v_x
                    (pi
                      v_y
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (arrow
                        (app
                          Nat.le
                          ((app
                              Nat.succ
                              ((app
                                  List.length
                                  ((var v_u945)
                                    (app
                                      PSigma.fst
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x5
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                        (var v_y)))))))
                            (app
                              List.length
                              ((var v_u945)
                                (app
                                  PSigma.fst
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x5
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                    (app
                                      PSigma.mk
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                        (app List.nil ((var v_u945)))
                                        (var v_le)))))))))
                        (app List ((var v_u945)))))
                    (app List.nil ((var v_u945))))
                  (lam
                    v_head
                    (var v_u945)
                    (lam
                      v_tail
                      (app List ((var v_u945)))
                      (lam
                        v_tail_ih
                        (arrow
                          (pi
                            v_y
                            (app
                              PSigma
                              ((app List ((var v_u945)))
                                (lam
                                  v_x6
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                            (arrow
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            PSigma.fst
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x7
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (var v_y)))))))
                                  (app
                                    List.length
                                    ((var v_u945)
                                      (app
                                        PSigma.fst
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x7
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (var v_tail)
                                              (var v_le)))))))))
                              (app List ((var v_u945)))))
                          (app List ((var v_u945))))
                        (lam
                          v_x
                          (pi
                            v_y
                            (app
                              PSigma
                              ((app List ((var v_u945)))
                                (lam
                                  v_x7
                                  (app List ((var v_u945)))
                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                            (arrow
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            PSigma.fst
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x8
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (var v_y)))))))
                                  (app
                                    List.length
                                    ((var v_u945)
                                      (app
                                        PSigma.fst
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_x8
                                            (app List ((var v_u945)))
                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam
                                                v_x
                                                (app List ((var v_u945)))
                                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                              (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                              (var v_le)))))))))
                              (app List ((var v_u945)))))
                          (app
                            List.rec
                            ((var v_u945)
                              (lam
                                v_x8
                                (app List ((var v_u945)))
                                (arrow
                                  (pi
                                    v_y
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam
                                          v_x9
                                          (app List ((var v_u945)))
                                          (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                    (arrow
                                      (app
                                        Nat.le
                                        ((app
                                            Nat.succ
                                            ((app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    PSigma.fst
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x10
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (var v_y)))))))
                                          (app
                                            List.length
                                            ((var v_u945)
                                              (app
                                                PSigma.fst
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x10
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x10
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (app List.cons ((var v_u945) (var v_head) (var v_x8)))
                                                      (var v_le)))))))))
                                      (app List ((var v_u945)))))
                                  (app List ((var v_u945)))))
                              (lam
                                v_x8
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x8
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                  (arrow
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              List.length
                                              ((var v_u945)
                                                (app
                                                  PSigma.fst
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x9
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (var v_y)))))))
                                        (app
                                          List.length
                                          ((var v_u945)
                                            (app
                                              PSigma.fst
                                              ((app List ((var v_u945)))
                                                (lam
                                                  v_x9
                                                  (app List ((var v_u945)))
                                                  (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                (app
                                                  PSigma.mk
                                                  ((app List ((var v_u945)))
                                                    (lam
                                                      v_x9
                                                      (app List ((var v_u945)))
                                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                    (app
                                                      List.cons
                                                      ((var v_u945) (var v_head) (app List.nil ((var v_u945)))))
                                                    (var v_le)))))))))
                                    (app List ((var v_u945)))))
                                (app List.cons ((var v_u945) (var v_head) (app List.nil ((var v_u945))))))
                              (lam
                                v_x8
                                (var v_u945)
                                (lam
                                  v_x9
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x10
                                    (arrow
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (arrow
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        PSigma.fst
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x11
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (var v_y)))))))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    PSigma.fst
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x11
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x11
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (app List.cons ((var v_u945) (var v_head) (var v_x9)))
                                                          (var v_le)))))))))
                                          (app List ((var v_u945)))))
                                      (app List ((var v_u945))))
                                    (lam
                                      v_x11
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam
                                              v_x11
                                              (app List ((var v_u945)))
                                              (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                                        (arrow
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List.length
                                                    ((var v_u945)
                                                      (app
                                                        PSigma.fst
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x12
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (var v_y)))))))
                                              (app
                                                List.length
                                                ((var v_u945)
                                                  (app
                                                    PSigma.fst
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_x12
                                                        (app List ((var v_u945)))
                                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                      (app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x12
                                                            (app List ((var v_u945)))
                                                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                          (app
                                                            List.cons
                                                            ((var v_u945)
                                                              (var v_head)
                                                              (app List.cons ((var v_u945) (var v_x8) (var v_x9)))))
                                                          (var v_le)))))))))
                                          (app List ((var v_u945)))))
                                      (app
                                        List.merge
                                        ((var v_u945)
                                          (apv
                                            (var v_x11)
                                            ((app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    Subtype.val
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  Nat.add
                                                                  ((app
                                                                      List.length
                                                                      ((var v_u945)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945)
                                                                            (var v_head)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945) (var v_x8) (var v_x9)))))))
                                                                    (num 1)))
                                                                (num 2))))))
                                                      (app
                                                        Prod.fst
                                                        ((app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          Nat.add
                                                                          ((app
                                                                              List.length
                                                                              ((var v_u945)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_head)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_x8)
                                                                                        (var v_x9)))))))
                                                                            (num 1)))
                                                                        (num 2))))))))
                                                          (app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_head)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x8)
                                                                                    (var v_x9)))))))
                                                                        (num 2))))))))
                                                          (app
                                                            List.MergeSort.Internal.splitInTwo
                                                            ((var v_u945)
                                                              (app
                                                                List.length
                                                                ((var v_u945)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945)
                                                                      (var v_head)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945) (var v_x8) (var v_x9)))))))
                                                              (app
                                                                Subtype.mk
                                                                ((app List ((var v_u945)))
                                                                  (lam
                                                                    v_l
                                                                    (app List ((var v_u945)))
                                                                    (app
                                                                      Eq
                                                                      ((app Nat ())
                                                                        (app List.length ((var v_u945) (var v_l)))
                                                                        (app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_head)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x8)
                                                                                    (var v_x9))))))))))
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945)
                                                                      (var v_head)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945) (var v_x8) (var v_x9)))))
                                                                  (proof)))))))))
                                                  (var v_le)))
                                              (proof)))
                                          (apv
                                            (var v_x11)
                                            ((app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                                  (app
                                                    Subtype.val
                                                    ((app List ((var v_u945)))
                                                      (lam
                                                        v_l
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Eq
                                                          ((app Nat ())
                                                            (app List.length ((var v_u945) (var v_l)))
                                                            (app
                                                              Nat.div
                                                              ((app
                                                                  List.length
                                                                  ((var v_u945)
                                                                    (app
                                                                      List.cons
                                                                      ((var v_u945)
                                                                        (var v_head)
                                                                        (app
                                                                          List.cons
                                                                          ((var v_u945) (var v_x8) (var v_x9)))))))
                                                                (num 2))))))
                                                      (app
                                                        Prod.snd
                                                        ((app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          Nat.add
                                                                          ((app
                                                                              List.length
                                                                              ((var v_u945)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_head)
                                                                                    (app
                                                                                      List.cons
                                                                                      ((var v_u945)
                                                                                        (var v_x8)
                                                                                        (var v_x9)))))))
                                                                            (num 1)))
                                                                        (num 2))))))))
                                                          (app
                                                            Subtype
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_l
                                                                (app List ((var v_u945)))
                                                                (app
                                                                  Eq
                                                                  ((app Nat ())
                                                                    (app List.length ((var v_u945) (var v_l)))
                                                                    (app
                                                                      Nat.div
                                                                      ((app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_head)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x8)
                                                                                    (var v_x9)))))))
                                                                        (num 2))))))))
                                                          (app
                                                            List.MergeSort.Internal.splitInTwo
                                                            ((var v_u945)
                                                              (app
                                                                List.length
                                                                ((var v_u945)
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945)
                                                                      (var v_head)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945) (var v_x8) (var v_x9)))))))
                                                              (app
                                                                Subtype.mk
                                                                ((app List ((var v_u945)))
                                                                  (lam
                                                                    v_l
                                                                    (app List ((var v_u945)))
                                                                    (app
                                                                      Eq
                                                                      ((app Nat ())
                                                                        (app List.length ((var v_u945) (var v_l)))
                                                                        (app
                                                                          List.length
                                                                          ((var v_u945)
                                                                            (app
                                                                              List.cons
                                                                              ((var v_u945)
                                                                                (var v_head)
                                                                                (app
                                                                                  List.cons
                                                                                  ((var v_u945)
                                                                                    (var v_x8)
                                                                                    (var v_x9))))))))))
                                                                  (app
                                                                    List.cons
                                                                    ((var v_u945)
                                                                      (var v_head)
                                                                      (app
                                                                        List.cons
                                                                        ((var v_u945) (var v_x8) (var v_x9)))))
                                                                  (proof)))))))))
                                                  (var v_le)))
                                              (proof)))
                                          (var v_le)))))))
                              (var v_tail)
                              (var v_x)))))))
                  (var v_xs)
                  (lam
                    v_smaller
                    (app
                      PSigma
                      ((app List ((var v_u945)))
                        (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                    (lam
                      v_decrease
                      (app
                        Nat.le
                        ((app
                            Nat.succ
                            ((app
                                List.length
                                ((var v_u945)
                                  (app
                                    PSigma.fst
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x5
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (var v_smaller)))))))
                          (app
                            List.length
                            ((var v_u945)
                              (app
                                PSigma.fst
                                ((app List ((var v_u945)))
                                  (lam
                                    v_x5
                                    (app List ((var v_u945)))
                                    (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                  (app
                                    PSigma.mk
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_x5
                                        (app List ((var v_u945)))
                                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                      (var v_xs)
                                      (var v_le)))))))))
                      (app
                        Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                        ((var v_fuel)
                          (var v_u945)
                          (app
                            PSigma.fst
                            ((app List ((var v_u945)))
                              (lam
                                v_x6
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                              (var v_smaller)))
                          (lam
                            v_a
                            (var v_u945)
                            (lam
                              v_x7
                              (var v_u945)
                              (apv
                                (app
                                  PSigma.snd
                                  ((app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                                    (var v_smaller)))
                                ((var v_a) (var v_x7)))))))))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.adequate
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_fuel
          (app Nat ())
          (arrow
            (app
              Nat.le
              ((app
                  Nat.succ
                  ((app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (lam
                          v__x
                          (app
                            PSigma
                            ((app List ((var v_u945)))
                              (lam
                                v_x4
                                (app List ((var v_u945)))
                                (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                          (app Nat ()))
                        (app
                          PSigma.mk
                          ((app List ((var v_u945)))
                            (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                            (var v_xs)
                            (var v_le)))
                        (lam
                          v_x4
                          (app List ((var v_u945)))
                          (lam
                            v_x5
                            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                            (app List.length ((var v_u945) (var v_x4)))))))))
                (var v_fuel)))
            (app
              Eq
              ((app List ((var v_u945)))
                (app
                  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.fuel
                  ((var v_u945)
                    (var v_fuel)
                    (app
                      PSigma.mk
                      ((app List ((var v_u945)))
                        (lam v_x4 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (var v_xs)
                        (var v_le)))))
                (app List.mergeSort ((var v_u945) (var v_xs) (var v_le))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.budgetAdequate
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Nat.le
          ((app
              Nat.succ
              ((app
                  PSigma.casesOn
                  ((app List ((var v_u945)))
                    (lam v_x3 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                    (lam
                      v__x
                      (app
                        PSigma
                        ((app List ((var v_u945)))
                          (lam v_x3 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))))
                      (app Nat ()))
                    (app
                      PSigma.mk
                      ((app List ((var v_u945)))
                        (lam v_x3 (app List ((var v_u945))) (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))))
                        (var v_xs)
                        (var v_le)))
                    (lam
                      v_x3
                      (app List ((var v_u945)))
                      (lam
                        v_x4
                        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
                        (app List.length ((var v_u945) (var v_x3)))))))))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.budget
              ((var v_u945) (var v_xs) (var v_le))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.bridge
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app List.mergeSort ((var v_u945) (var v_xs) (var v_le)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.reading
              ((var v_u945) (var v_xs) (var v_le))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_zero
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
              ((num 0) (var v_u945) (var v_xs) (var v_le)))
            (app List.nil ((var v_u945))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case0
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_x
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
              ((app Nat.succ ((var v_fuel))) (var v_u945) (app List.nil ((var v_u945))) (var v_x)))
            (app List.nil ((var v_u945))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case1
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_x
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_a
          (var v_u945)
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                ((app Nat.succ ((var v_fuel)))
                  (var v_u945)
                  (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945)))))
                  (var v_x)))
              (app List.cons ((var v_u945) (var v_a) (app List.nil ((var v_u945)))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel_case2
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_x
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_a
          (var v_u945)
          (pi
            v_b
            (var v_u945)
            (pi
              v_xs
              (app List ((var v_u945)))
              (app
                Eq
                ((app List ((var v_u945)))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                    ((app Nat.succ ((var v_fuel)))
                      (var v_u945)
                      (app List.cons ((var v_u945) (var v_a) (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                      (var v_x)))
                  (app
                    List.merge
                    ((var v_u945)
                      (app
                        Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                        ((var v_fuel)
                          (var v_u945)
                          (app
                            Subtype.val
                            ((app List ((var v_u945)))
                              (lam
                                v_l
                                (app List ((var v_u945)))
                                (app
                                  Eq
                                  ((app Nat ())
                                    (app List.length ((var v_u945) (var v_l)))
                                    (app
                                      Nat.div
                                      ((app
                                          Nat.add
                                          ((app
                                              List.length
                                              ((var v_u945)
                                                (app
                                                  List.cons
                                                  ((var v_u945)
                                                    (var v_a)
                                                    (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                            (num 1)))
                                        (num 2))))))
                              (app
                                Prod.fst
                                ((app
                                    Subtype
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_l
                                        (app List ((var v_u945)))
                                        (app
                                          Eq
                                          ((app Nat ())
                                            (app List.length ((var v_u945) (var v_l)))
                                            (app
                                              Nat.div
                                              ((app
                                                  Nat.add
                                                  ((app
                                                      List.length
                                                      ((var v_u945)
                                                        (app
                                                          List.cons
                                                          ((var v_u945)
                                                            (var v_a)
                                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                    (num 1)))
                                                (num 2))))))))
                                  (app
                                    Subtype
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_l
                                        (app List ((var v_u945)))
                                        (app
                                          Eq
                                          ((app Nat ())
                                            (app List.length ((var v_u945) (var v_l)))
                                            (app
                                              Nat.div
                                              ((app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                (num 2))))))))
                                  (app
                                    List.MergeSort.Internal.splitInTwo
                                    ((var v_u945)
                                      (app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (app
                                        Subtype.mk
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_l
                                            (app List ((var v_u945)))
                                            (app
                                              Eq
                                              ((app Nat ())
                                                (app List.length ((var v_u945) (var v_l)))
                                                (app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                          (proof)))))))))
                          (var v_x)))
                      (app
                        Mettapedia.Languages.Lean.Recursion.FuelCore.MergeSort.sourceFuel
                        ((var v_fuel)
                          (var v_u945)
                          (app
                            Subtype.val
                            ((app List ((var v_u945)))
                              (lam
                                v_l
                                (app List ((var v_u945)))
                                (app
                                  Eq
                                  ((app Nat ())
                                    (app List.length ((var v_u945) (var v_l)))
                                    (app
                                      Nat.div
                                      ((app
                                          List.length
                                          ((var v_u945)
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_a)
                                                (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                        (num 2))))))
                              (app
                                Prod.snd
                                ((app
                                    Subtype
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_l
                                        (app List ((var v_u945)))
                                        (app
                                          Eq
                                          ((app Nat ())
                                            (app List.length ((var v_u945) (var v_l)))
                                            (app
                                              Nat.div
                                              ((app
                                                  Nat.add
                                                  ((app
                                                      List.length
                                                      ((var v_u945)
                                                        (app
                                                          List.cons
                                                          ((var v_u945)
                                                            (var v_a)
                                                            (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                    (num 1)))
                                                (num 2))))))))
                                  (app
                                    Subtype
                                    ((app List ((var v_u945)))
                                      (lam
                                        v_l
                                        (app List ((var v_u945)))
                                        (app
                                          Eq
                                          ((app Nat ())
                                            (app List.length ((var v_u945) (var v_l)))
                                            (app
                                              Nat.div
                                              ((app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                                (num 2))))))))
                                  (app
                                    List.MergeSort.Internal.splitInTwo
                                    ((var v_u945)
                                      (app
                                        List.length
                                        ((var v_u945)
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))))
                                      (app
                                        Subtype.mk
                                        ((app List ((var v_u945)))
                                          (lam
                                            v_l
                                            (app List ((var v_u945)))
                                            (app
                                              Eq
                                              ((app Nat ())
                                                (app List.length ((var v_u945) (var v_l)))
                                                (app
                                                  List.length
                                                  ((var v_u945)
                                                    (app
                                                      List.cons
                                                      ((var v_u945)
                                                        (var v_a)
                                                        (app List.cons ((var v_u945) (var v_b) (var v_xs))))))))))
                                          (app
                                            List.cons
                                            ((var v_u945)
                                              (var v_a)
                                              (app List.cons ((var v_u945) (var v_b) (var v_xs)))))
                                          (proof)))))))))
                          (var v_x)))
                      (var v_x)))))))))))
  (Axioms (propext Quot.sound)))

(LeanFuelRecursion
  Nat.primeFactorsList
  (Fuel Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel)
  (Equations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel_succ))
  (SourceFuel Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel)
  (SourceFuelEquations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case0
      Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case1
      Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case2))
  (Adequate Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.adequate)
  (Budget Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.budget)
  (BudgetAdequate Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.budgetAdequate)
  (Reading Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.reading)
  (Bridge Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.bridge))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app List ((app Nat ()))))))
  (Value
    (lam
      v_a
      (app Nat ())
      (lam
        v_x
        (app Nat ())
        (app
          Mettapedia.Languages.Lean.Recursion.AccessibleRecipe.fuel
          ((app Nat ())
            (lam v_y (app Nat ()) (app List ((app Nat ()))))
            (lam v_x2 (app Nat ()) (var v_x2))
            (lam
              v_x2
              (app Nat ())
              (lam
                v_x3
                (pi
                  v_y
                  (app Nat ())
                  (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_x2))) (app List ((app Nat ())))))
                (app
                  Nat.primeFactorsList.match_1
                  ((lam
                      v_x4
                      (app Nat ())
                      (arrow
                        (pi
                          v_y
                          (app Nat ())
                          (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_x4))) (app List ((app Nat ())))))
                        (app List ((app Nat ())))))
                    (var v_x2)
                    (lam
                      v__
                      (app PUnit ())
                      (lam
                        v_x5
                        (pi
                          v_y
                          (app Nat ())
                          (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 0))) (app List ((app Nat ())))))
                        (app List.nil ((app Nat ())))))
                    (lam
                      v__
                      (app PUnit ())
                      (lam
                        v_x5
                        (pi
                          v_y
                          (app Nat ())
                          (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 1))) (app List ((app Nat ())))))
                        (app List.nil ((app Nat ())))))
                    (lam
                      v_k
                      (app Nat ())
                      (lam
                        v_x5
                        (pi
                          v_y
                          (app Nat ())
                          (arrow
                            (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((app Nat.succ ((var v_k)))))))
                            (app List ((app Nat ())))))
                        (apv
                          (lam
                            v_m
                            (app Nat ())
                            (app
                              List.cons
                              ((app Nat ())
                                (var v_m)
                                (apv
                                  (var v_x5)
                                  ((app Nat.div ((app Nat.add ((var v_k) (num 2))) (var v_m))) (proof))))))
                          ((app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))))))
                    (var v_x3)))))
            (lam v_state (app Nat ()) (app List.nil ((app Nat ()))))
            (var v_a)
            (var v_x)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app List ((app Nat ()))))))
  (Value
    (lam
      v_fuel
      (app Nat ())
      (lam
        v_state
        (app Nat ())
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel ((var v_fuel) (var v_state)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.budget
  (Type (arrow (app Nat ()) (app Nat ())))
  (Value (lam v_state (app Nat ()) (app Nat.succ ((var v_state))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.reading
  (Type (arrow (app Nat ()) (app List ((app Nat ())))))
  (Value
    (lam
      v_state
      (app Nat ())
      (app
        Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
        ((app Nat.succ ((var v_state))) (var v_state))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel_zero
  (pi
    v_state
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel ((num 0) (var v_state)))
        (app List.nil ((app Nat ()))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Eq
        ((app List ((app Nat ())))
          (app
            Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel
            ((app Nat.succ ((var v_fuel))) (var v_state)))
          (app
            Nat.primeFactorsList.match_1
            ((lam
                v_x
                (app Nat ())
                (arrow
                  (pi
                    v_y
                    (app Nat ())
                    (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_x))) (app List ((app Nat ())))))
                  (app List ((app Nat ())))))
              (var v_state)
              (lam
                v__
                (app PUnit ())
                (lam
                  v_x
                  (pi
                    v_y
                    (app Nat ())
                    (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 0))) (app List ((app Nat ())))))
                  (app List.nil ((app Nat ())))))
              (lam
                v__
                (app PUnit ())
                (lam
                  v_x
                  (pi
                    v_y
                    (app Nat ())
                    (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 1))) (app List ((app Nat ())))))
                  (app List.nil ((app Nat ())))))
              (lam
                v_k
                (app Nat ())
                (lam
                  v_x
                  (pi
                    v_y
                    (app Nat ())
                    (arrow
                      (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((app Nat.succ ((var v_k)))))))
                      (app List ((app Nat ())))))
                  (apv
                    (lam
                      v_m
                      (app Nat ())
                      (app
                        List.cons
                        ((app Nat ())
                          (var v_m)
                          (apv (var v_x) ((app Nat.div ((app Nat.add ((var v_k) (num 2))) (var v_m))) (proof))))))
                    ((app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))))))
              (lam
                v_smaller
                (app Nat ())
                (lam
                  v_decrease
                  (app Nat.le ((app Nat.succ ((var v_smaller))) (var v_state)))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel
                    ((var v_fuel) (var v_smaller)))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Eq
        ((app List ((app Nat ())))
          (app
            Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
            ((app Nat.succ ((var v_fuel))) (var v_state)))
          (app
            Nat.rec
            ((lam
                v_x
                (app Nat ())
                (arrow
                  (pi
                    v_y
                    (app Nat ())
                    (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_x))) (app List ((app Nat ())))))
                  (app List ((app Nat ())))))
              (lam
                v_x
                (pi
                  v_y
                  (app Nat ())
                  (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 0))) (app List ((app Nat ())))))
                (app List.nil ((app Nat ()))))
              (lam
                v_n
                (app Nat ())
                (lam
                  v_n_ih
                  (arrow
                    (pi
                      v_y
                      (app Nat ())
                      (arrow (app Nat.le ((app Nat.succ ((var v_y))) (var v_n))) (app List ((app Nat ())))))
                    (app List ((app Nat ()))))
                  (lam
                    v_x
                    (pi
                      v_y
                      (app Nat ())
                      (arrow
                        (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((var v_n)))))
                        (app List ((app Nat ())))))
                    (app
                      Nat.rec
                      ((lam
                          v_x5
                          (app Nat ())
                          (arrow
                            (pi
                              v_y
                              (app Nat ())
                              (arrow
                                (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((var v_x5)))))
                                (app List ((app Nat ())))))
                            (app List ((app Nat ())))))
                        (lam
                          v_x5
                          (pi
                            v_y
                            (app Nat ())
                            (arrow (app Nat.le ((app Nat.succ ((var v_y))) (num 1))) (app List ((app Nat ())))))
                          (app List.nil ((app Nat ()))))
                        (lam
                          v_x5
                          (app Nat ())
                          (lam
                            v_x6
                            (arrow
                              (pi
                                v_y
                                (app Nat ())
                                (arrow
                                  (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((var v_x5)))))
                                  (app List ((app Nat ())))))
                              (app List ((app Nat ()))))
                            (lam
                              v_x7
                              (pi
                                v_y
                                (app Nat ())
                                (arrow
                                  (app Nat.le ((app Nat.succ ((var v_y))) (app Nat.succ ((app Nat.succ ((var v_x5)))))))
                                  (app List ((app Nat ())))))
                              (app
                                List.cons
                                ((app Nat ())
                                  (app Nat.minFac ((app Nat.add ((var v_x5) (num 2)))))
                                  (apv
                                    (var v_x7)
                                    ((app
                                        Nat.div
                                        ((app Nat.add ((var v_x5) (num 2)))
                                          (app Nat.minFac ((app Nat.add ((var v_x5) (num 2)))))))
                                      (proof))))))))
                        (var v_n)
                        (var v_x))))))
              (var v_state)
              (lam
                v_smaller
                (app Nat ())
                (lam
                  v_decrease
                  (app Nat.le ((app Nat.succ ((var v_smaller))) (var v_state)))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
                    ((var v_fuel) (var v_smaller)))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.adequate
  (pi
    v_state
    (app Nat ())
    (pi
      v_fuel
      (app Nat ())
      (arrow
        (app Nat.le ((app Nat.succ ((var v_state))) (var v_fuel)))
        (app
          Eq
          ((app List ((app Nat ())))
            (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.fuel ((var v_fuel) (var v_state)))
            (app Nat.primeFactorsList ((var v_state))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.budgetAdequate
  (pi
    v_state
    (app Nat ())
    (app
      Nat.le
      ((app Nat.succ ((var v_state)))
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.budget ((var v_state))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.bridge
  (pi
    v_state
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app Nat.primeFactorsList ((var v_state)))
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.reading ((var v_state))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_zero
  (pi
    v_state
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel ((num 0) (var v_state)))
        (app List.nil ((app Nat ()))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case0
  (pi
    v_fuel
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app
          Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
          ((app Nat.succ ((var v_fuel))) (num 0)))
        (app List.nil ((app Nat ()))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case1
  (pi
    v_fuel
    (app Nat ())
    (app
      Eq
      ((app List ((app Nat ())))
        (app
          Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
          ((app Nat.succ ((var v_fuel))) (num 1)))
        (app List.nil ((app Nat ()))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel_case2
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_k
      (app Nat ())
      (app
        Eq
        ((app List ((app Nat ())))
          (app
            Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
            ((app Nat.succ ((var v_fuel))) (app Nat.succ ((app Nat.succ ((var v_k)))))))
          (app
            List.cons
            ((app Nat ())
              (app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.PrimeFactorsList.sourceFuel
                ((var v_fuel)
                  (app
                    Nat.div
                    ((app Nat.add ((var v_k) (num 2))) (app Nat.minFac ((app Nat.add ((var v_k) (num 2)))))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanFuelRecursion
  Nat.minFacAux
  (Fuel Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel)
  (Equations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel_succ))
  (SourceFuel Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel)
  (SourceFuelEquations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel_case0))
  (Adequate Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.adequate)
  (Budget Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.budget)
  (BudgetAdequate Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.budgetAdequate)
  (Reading Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.reading)
  (Bridge Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.bridge))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_a
        (app Nat ())
        (lam
          v_x
          (app Nat ())
          (app
            Mettapedia.Languages.Lean.Recursion.AccessibleRecipe.fuel
            ((app Nat ())
              (lam v_y (app Nat ()) (app Nat ()))
              (lam v_x3 (app Nat ()) (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_x3))))
              (lam
                v_x3
                (app Nat ())
                (lam
                  v_x4
                  (pi
                    v_y
                    (app Nat ())
                    (arrow
                      (app
                        Nat.le
                        ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_y)))))
                          (app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_x3)))))
                      (app Nat ())))
                  (apv
                    (lam
                      v_k
                      (app Nat ())
                      (app
                        dite
                        ((app Nat ())
                          (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                          (app Nat.decLt ((var v_n) (app Nat.mul ((var v_k) (var v_k)))))
                          (lam
                            v_h
                            (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                            (var v_n))
                          (lam
                            v_h
                            (arrow
                              (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                              (app False ()))
                            (app
                              dite
                              ((app Nat ())
                                (app
                                  Exists
                                  ((app Nat ())
                                    (lam
                                      v_c
                                      (app Nat ())
                                      (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                                (app Nat.decidable_dvd ((var v_k) (var v_n)))
                                (lam
                                  v_x7
                                  (app
                                    Exists
                                    ((app Nat ())
                                      (lam
                                        v_c
                                        (app Nat ())
                                        (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                                  (var v_k))
                                (lam
                                  v_x7
                                  (arrow
                                    (app
                                      Exists
                                      ((app Nat ())
                                        (lam
                                          v_c
                                          (app Nat ())
                                          (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                                    (app False ()))
                                  (apv (var v_x4) ((app Nat.add ((var v_k) (num 2))) (proof))))))))))
                    ((var v_x3)))))
              (lam v_state (app Nat ()) (app Nat.zero ()))
              (var v_a)
              (var v_x))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ())))))
  (Value
    (lam
      v_fuel
      (app Nat ())
      (lam
        v_n
        (app Nat ())
        (lam
          v_state
          (app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel ((var v_n) (var v_fuel) (var v_state))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.budget
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value (lam v_n (app Nat ()) (lam v_state (app Nat ()) (app Nat.add ((var v_n) (num 3)))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.reading
  (Type (arrow (app Nat ()) (arrow (app Nat ()) (app Nat ()))))
  (Value
    (lam
      v_n
      (app Nat ())
      (lam
        v_state
        (app Nat ())
        (app
          Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
          ((app Nat.add ((var v_n) (num 3))) (var v_n) (var v_state)))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel_zero
  (pi
    v_n
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel ((var v_n) (num 0) (var v_state)))
          (app Nat.zero ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel_succ
  (pi
    v_n
    (app Nat ())
    (pi
      v_fuel
      (app Nat ())
      (pi
        v_state
        (app Nat ())
        (app
          Eq
          ((app Nat ())
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel
              ((var v_n) (app Nat.succ ((var v_fuel))) (var v_state)))
            (apv
              (lam
                v_k
                (app Nat ())
                (app
                  dite
                  ((app Nat ())
                    (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                    (app Nat.decLt ((var v_n) (app Nat.mul ((var v_k) (var v_k)))))
                    (lam v_h (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k))))) (var v_n))
                    (lam
                      v_h
                      (arrow
                        (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_k) (var v_k)))))
                        (app False ()))
                      (app
                        dite
                        ((app Nat ())
                          (app
                            Exists
                            ((app Nat ())
                              (lam
                                v_c
                                (app Nat ())
                                (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                          (app Nat.decidable_dvd ((var v_k) (var v_n)))
                          (lam
                            v_x5
                            (app
                              Exists
                              ((app Nat ())
                                (lam
                                  v_c
                                  (app Nat ())
                                  (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                            (var v_k))
                          (lam
                            v_x5
                            (arrow
                              (app
                                Exists
                                ((app Nat ())
                                  (lam
                                    v_c
                                    (app Nat ())
                                    (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_k) (var v_c))))))))
                              (app False ()))
                            (app
                              Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel
                              ((var v_n) (var v_fuel) (app Nat.add ((var v_k) (num 2))))))))))))
              ((var v_state))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (pi
        v_state
        (app Nat ())
        (app
          Eq
          ((app Nat ())
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
              ((app Nat.succ ((var v_fuel))) (var v_n) (var v_state)))
            (app
              dite
              ((app Nat ())
                (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_state) (var v_state)))))
                (app Nat.decLt ((var v_n) (app Nat.mul ((var v_state) (var v_state)))))
                (lam
                  v_h
                  (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_state) (var v_state)))))
                  (var v_n))
                (lam
                  v_h
                  (arrow
                    (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_state) (var v_state)))))
                    (app False ()))
                  (app
                    dite
                    ((app Nat ())
                      (app
                        Exists
                        ((app Nat ())
                          (lam
                            v_c
                            (app Nat ())
                            (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_state) (var v_c))))))))
                      (app Nat.decidable_dvd ((var v_state) (var v_n)))
                      (lam
                        v_x4
                        (app
                          Exists
                          ((app Nat ())
                            (lam
                              v_c
                              (app Nat ())
                              (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_state) (var v_c))))))))
                        (var v_state))
                      (lam
                        v_x4
                        (arrow
                          (app
                            Exists
                            ((app Nat ())
                              (lam
                                v_c
                                (app Nat ())
                                (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_state) (var v_c))))))))
                          (app False ()))
                        (app
                          Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
                          ((var v_fuel) (var v_n) (app Nat.add ((var v_state) (num 2))))))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.adequate
  (pi
    v_n
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (pi
        v_fuel
        (app Nat ())
        (arrow
          (app
            Nat.le
            ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_state)))))
              (var v_fuel)))
          (app
            Eq
            ((app Nat ())
              (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.fuel ((var v_n) (var v_fuel) (var v_state)))
              (app Nat.minFacAux ((var v_n) (var v_state)))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.budgetAdequate
  (pi
    v_n
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Nat.le
        ((app Nat.succ ((app Nat.sub ((app Nat.add ((app Nat.sqrt ((var v_n))) (num 2))) (var v_state)))))
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.budget ((var v_n) (var v_state)))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.bridge
  (pi
    v_n
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Nat.minFacAux ((var v_n) (var v_state)))
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.reading ((var v_n) (var v_state)))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel_zero
  (pi
    v_n
    (app Nat ())
    (pi
      v_state
      (app Nat ())
      (app
        Eq
        ((app Nat ())
          (app Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel ((num 0) (var v_n) (var v_state)))
          (app Nat.zero ())))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel_case0
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_n
      (app Nat ())
      (pi
        v_x
        (app Nat ())
        (app
          Eq
          ((app Nat ())
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
              ((app Nat.succ ((var v_fuel))) (var v_n) (var v_x)))
            (app
              dite
              ((app Nat ())
                (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_x) (var v_x)))))
                (app Nat.decLt ((var v_n) (app Nat.mul ((var v_x) (var v_x)))))
                (lam v_h (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_x) (var v_x))))) (var v_n))
                (lam
                  v_h
                  (arrow (app Nat.le ((app Nat.succ ((var v_n))) (app Nat.mul ((var v_x) (var v_x))))) (app False ()))
                  (app
                    dite
                    ((app Nat ())
                      (app
                        Exists
                        ((app Nat ())
                          (lam v_c (app Nat ()) (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_x) (var v_c))))))))
                      (app Nat.decidable_dvd ((var v_x) (var v_n)))
                      (lam
                        v_x4
                        (app
                          Exists
                          ((app Nat ())
                            (lam
                              v_c
                              (app Nat ())
                              (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_x) (var v_c))))))))
                        (var v_x))
                      (lam
                        v_x4
                        (arrow
                          (app
                            Exists
                            ((app Nat ())
                              (lam
                                v_c
                                (app Nat ())
                                (app Eq ((app Nat ()) (var v_n) (app Nat.mul ((var v_x) (var v_c))))))))
                          (app False ()))
                        (app
                          Mettapedia.Languages.Lean.Recursion.FuelCore.MinFacAux.sourceFuel
                          ((var v_fuel) (var v_n) (app Nat.add ((var v_x) (num 2))))))))))))))))
  (Axioms (propext Classical.choice Quot.sound)))

(LeanFuelRecursion
  List.merge
  (Fuel Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel)
  (Equations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel_succ))
  (SourceFuel Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel)
  (SourceFuelEquations
    (Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_zero
      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case0
      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case1.branch0
      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case1.branch1
      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case3))
  (Adequate Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.adequate)
  (Budget Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.budget)
  (BudgetAdequate Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.budgetAdequate)
  (Reading Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.reading)
  (Bridge Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.bridge))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (arrow
          (app Nat ())
          (arrow
            (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
            (app List ((var v_u945))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (lam
          v_a
          (app Nat ())
          (lam
            v_x
            (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
            (app
              Mettapedia.Languages.Lean.Recursion.RelationFuel.fuel
              ((app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                (lam
                  v_y
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                  (app List ((var v_u945))))
                (lam
                  v_x4
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                  (lam
                    v_x5
                    (app
                      PSigma
                      ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                    (app
                      Prod.Lex
                      ((app List ((var v_u945)))
                        (app List ((var v_u945)))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Nat.le
                              ((app
                                  Nat.succ
                                  ((app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                (app
                                  List._sizeOf_1
                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                        (lam
                          v_x6
                          (app List ((var v_u945)))
                          (lam
                            v_x7
                            (app List ((var v_u945)))
                            (app
                              Nat.le
                              ((app
                                  Nat.succ
                                  ((app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                (app
                                  List._sizeOf_1
                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                        (app
                          PSigma.casesOn
                          ((app List ((var v_u945)))
                            (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                            (lam
                              v__x
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                            (var v_x4)
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (lam
                                v_ys
                                (app List ((var v_u945)))
                                (app
                                  Prod.mk
                                  ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                        (app
                          PSigma.casesOn
                          ((app List ((var v_u945)))
                            (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                            (lam
                              v__x
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                            (var v_x5)
                            (lam
                              v_xs
                              (app List ((var v_u945)))
                              (lam
                                v_ys
                                (app List ((var v_u945)))
                                (app
                                  Prod.mk
                                  ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))))
                (lam
                  v__x
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                  (lam
                    v_x5
                    (pi
                      v_y
                      (app
                        PSigma
                        ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                      (arrow
                        (app
                          Prod.Lex
                          ((app List ((var v_u945)))
                            (app List ((var v_u945)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                (lam
                                  v_x6
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                (var v_y)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_ys
                                    (app List ((var v_u945)))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                            (app
                              PSigma.casesOn
                              ((app List ((var v_u945)))
                                (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                (lam
                                  v_x6
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                (var v__x)
                                (lam
                                  v_xs
                                  (app List ((var v_u945)))
                                  (lam
                                    v_ys
                                    (app List ((var v_u945)))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))
                        (app List ((var v_u945)))))
                    (app
                      PSigma.casesOn
                      ((app List ((var v_u945)))
                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                        (lam
                          v_x6
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                          (arrow
                            (pi
                              v_y
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                              (arrow
                                (app
                                  Prod.Lex
                                  ((app List ((var v_u945)))
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))))
                                    (lam
                                      v_x8
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))))
                                    (app
                                      PSigma.casesOn
                                      ((app List ((var v_u945)))
                                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                        (lam
                                          v_x8
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                        (var v_y)
                                        (lam
                                          v_xs
                                          (app List ((var v_u945)))
                                          (lam
                                            v_ys
                                            (app List ((var v_u945)))
                                            (app
                                              Prod.mk
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (var v_xs)
                                                (var v_ys)))))))
                                    (app
                                      PSigma.casesOn
                                      ((app List ((var v_u945)))
                                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                        (lam
                                          v_x8
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                          (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                        (var v_x6)
                                        (lam
                                          v_xs
                                          (app List ((var v_u945)))
                                          (lam
                                            v_ys
                                            (app List ((var v_u945)))
                                            (app
                                              Prod.mk
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (var v_xs)
                                                (var v_ys)))))))))
                                (app List ((var v_u945)))))
                            (app List ((var v_u945)))))
                        (var v__x)
                        (lam
                          v_xs
                          (app List ((var v_u945)))
                          (lam
                            v_ys
                            (app List ((var v_u945)))
                            (lam
                              v_x8
                              (pi
                                v_y
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                                (arrow
                                  (app
                                    Prod.Lex
                                    ((app List ((var v_u945)))
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x10
                                          (app List ((var v_u945)))
                                          (app
                                            Nat.le
                                            ((app
                                                Nat.succ
                                                ((app
                                                    List._sizeOf_1
                                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))
                                              (app
                                                List._sizeOf_1
                                                ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (var v_y)
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))
                                      (app
                                        PSigma.casesOn
                                        ((app List ((var v_u945)))
                                          (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (lam
                                            v_x9
                                            (app
                                              PSigma
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                          (app
                                            PSigma.mk
                                            ((app List ((var v_u945)))
                                              (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                              (var v_xs)
                                              (var v_ys)))
                                          (lam
                                            v_x9
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x10
                                              (app List ((var v_u945)))
                                              (app
                                                Prod.mk
                                                ((app List ((var v_u945)))
                                                  (app List ((var v_u945)))
                                                  (var v_x9)
                                                  (var v_x10)))))))))
                                  (app List ((var v_u945)))))
                              (app
                                _private.Init.Data.List.Sort.Basic.0.List.merge.match_1
                                ((var v_u945)
                                  (lam
                                    v_x9
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x10
                                      (app List ((var v_u945)))
                                      (arrow
                                        (pi
                                          v_y
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))))
                                          (arrow
                                            (app
                                              Prod.Lex
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_x12)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x13)))))))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_x12)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x13)))))))
                                                (app
                                                  PSigma.casesOn
                                                  ((app List ((var v_u945)))
                                                    (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (lam
                                                      v_x12
                                                      (app
                                                        PSigma
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x12
                                                            (app List ((var v_u945)))
                                                            (app List ((var v_u945))))))
                                                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                    (var v_y)
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x13
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Prod.mk
                                                          ((app List ((var v_u945)))
                                                            (app List ((var v_u945)))
                                                            (var v_x12)
                                                            (var v_x13)))))))
                                                (app
                                                  PSigma.casesOn
                                                  ((app List ((var v_u945)))
                                                    (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (lam
                                                      v_x12
                                                      (app
                                                        PSigma
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x12
                                                            (app List ((var v_u945)))
                                                            (app List ((var v_u945))))))
                                                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                    (app
                                                      PSigma.mk
                                                      ((app List ((var v_u945)))
                                                        (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_x9)
                                                        (var v_x10)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x13
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Prod.mk
                                                          ((app List ((var v_u945)))
                                                            (app List ((var v_u945)))
                                                            (var v_x12)
                                                            (var v_x13)))))))))
                                            (app List ((var v_u945)))))
                                        (app List ((var v_u945))))))
                                  (var v_xs)
                                  (var v_ys)
                                  (lam
                                    v_x9
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x10
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                        (arrow
                                          (app
                                            Prod.Lex
                                            ((app List ((var v_u945)))
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x11)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x12)))))))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x11)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x12)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (var v_y)
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x11)
                                                          (var v_x12)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (app List.nil ((var v_u945)))
                                                      (var v_x9)))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x11)
                                                          (var v_x12)))))))))
                                          (app List ((var v_u945)))))
                                      (var v_x9)))
                                  (lam
                                    v_x9
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x10
                                      (pi
                                        v_y
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                        (arrow
                                          (app
                                            Prod.Lex
                                            ((app List ((var v_u945)))
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x11)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x12)))))))
                                              (lam
                                                v_x11
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x12
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x11)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x12)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (var v_y)
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x11)
                                                          (var v_x12)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v_x11
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x11
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (var v_x9)
                                                      (app List.nil ((var v_u945)))))
                                                  (lam
                                                    v_x11
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x12
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x11)
                                                          (var v_x12)))))))))
                                          (app List ((var v_u945)))))
                                      (var v_x9)))
                                  (lam
                                    v_x9
                                    (var v_u945)
                                    (lam
                                      v_x10
                                      (app List ((var v_u945)))
                                      (lam
                                        v_y
                                        (var v_u945)
                                        (lam
                                          v_x12
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x13
                                            (pi
                                              v_x13
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (arrow
                                                (app
                                                  Prod.Lex
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x14
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x15
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Nat.le
                                                          ((app
                                                              Nat.succ
                                                              ((app
                                                                  List._sizeOf_1
                                                                  ((var v_u945)
                                                                    (app instSizeOfDefault ((var v_u945)))
                                                                    (var v_x14)))))
                                                            (app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_x15)))))))
                                                    (lam
                                                      v_x14
                                                      (app List ((var v_u945)))
                                                      (lam
                                                        v_x15
                                                        (app List ((var v_u945)))
                                                        (app
                                                          Nat.le
                                                          ((app
                                                              Nat.succ
                                                              ((app
                                                                  List._sizeOf_1
                                                                  ((var v_u945)
                                                                    (app instSizeOfDefault ((var v_u945)))
                                                                    (var v_x14)))))
                                                            (app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_x15)))))))
                                                    (app
                                                      PSigma.casesOn
                                                      ((app List ((var v_u945)))
                                                        (lam v_x14 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (lam
                                                          v_x14
                                                          (app
                                                            PSigma
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_x14
                                                                (app List ((var v_u945)))
                                                                (app List ((var v_u945))))))
                                                          (app
                                                            Prod
                                                            ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                        (var v_x13)
                                                        (lam
                                                          v_x14
                                                          (app List ((var v_u945)))
                                                          (lam
                                                            v_x15
                                                            (app List ((var v_u945)))
                                                            (app
                                                              Prod.mk
                                                              ((app List ((var v_u945)))
                                                                (app List ((var v_u945)))
                                                                (var v_x14)
                                                                (var v_x15)))))))
                                                    (app
                                                      PSigma.casesOn
                                                      ((app List ((var v_u945)))
                                                        (lam v_x14 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (lam
                                                          v_x14
                                                          (app
                                                            PSigma
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_x14
                                                                (app List ((var v_u945)))
                                                                (app List ((var v_u945))))))
                                                          (app
                                                            Prod
                                                            ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                        (app
                                                          PSigma.mk
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x14
                                                              (app List ((var v_u945)))
                                                              (app List ((var v_u945))))
                                                            (app List.cons ((var v_u945) (var v_x9) (var v_x10)))
                                                            (app List.cons ((var v_u945) (var v_y) (var v_x12)))))
                                                        (lam
                                                          v_x14
                                                          (app List ((var v_u945)))
                                                          (lam
                                                            v_x15
                                                            (app List ((var v_u945)))
                                                            (app
                                                              Prod.mk
                                                              ((app List ((var v_u945)))
                                                                (app List ((var v_u945)))
                                                                (var v_x14)
                                                                (var v_x15)))))))))
                                                (app List ((var v_u945)))))
                                            (app
                                              dite
                                              ((app List ((var v_u945)))
                                                (app
                                                  Eq
                                                  ((app Bool ())
                                                    (apv (var v_le) ((var v_x9) (var v_y)))
                                                    (app Bool.true ())))
                                                (app
                                                  instDecidableEqBool
                                                  ((apv (var v_le) ((var v_x9) (var v_y))) (app Bool.true ())))
                                                (lam
                                                  v_h
                                                  (app
                                                    Eq
                                                    ((app Bool ())
                                                      (apv (var v_le) ((var v_x9) (var v_y)))
                                                      (app Bool.true ())))
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_x9)
                                                      (apv
                                                        (var v_x13)
                                                        ((app
                                                            PSigma.mk
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_x15
                                                                (app List ((var v_u945)))
                                                                (app List ((var v_u945))))
                                                              (var v_x10)
                                                              (app List.cons ((var v_u945) (var v_y) (var v_x12)))))
                                                          (proof))))))
                                                (lam
                                                  v_h
                                                  (arrow
                                                    (app
                                                      Eq
                                                      ((app Bool ())
                                                        (apv (var v_le) ((var v_x9) (var v_y)))
                                                        (app Bool.true ())))
                                                    (app False ()))
                                                  (app
                                                    List.cons
                                                    ((var v_u945)
                                                      (var v_y)
                                                      (apv
                                                        (var v_x13)
                                                        ((app
                                                            PSigma.mk
                                                            ((app List ((var v_u945)))
                                                              (lam
                                                                v_x15
                                                                (app List ((var v_u945)))
                                                                (app List ((var v_u945))))
                                                              (app List.cons ((var v_u945) (var v_x9) (var v_x10)))
                                                              (var v_x12)))
                                                          (proof)))))))))))))
                                  (var v_x8))))))
                        (var v_x5)))))
                (lam
                  v_state
                  (app
                    PSigma
                    ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                  (app List.nil ((var v_u945))))
                (var v_a)
                (var v_x)))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
  (Type
    (arrow
      (app Nat ())
      (pi
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (arrow
          (app List ((var v_u945)))
          (arrow
            (app List ((var v_u945)))
            (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945)))))))))
  (Value
    (lam
      v_fuel
      (app Nat ())
      (lam
        v_u945
        (sort (lsucc (lvl l_u_1)))
        (lam
          v_xs
          (app List ((var v_u945)))
          (lam
            v_ys
            (app List ((var v_u945)))
            (lam
              v_le
              (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
                ((var v_u945)
                  (var v_le)
                  (var v_fuel)
                  (app
                    PSigma.mk
                    ((app List ((var v_u945)))
                      (lam v_x5 (app List ((var v_u945))) (app List ((var v_u945))))
                      (var v_xs)
                      (var v_ys))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.budget
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app List ((var v_u945)))
        (arrow
          (app List ((var v_u945)))
          (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app Nat ()))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_xs
        (app List ((var v_u945)))
        (lam
          v_ys
          (app List ((var v_u945)))
          (lam
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Nat.succ
              ((app
                  Nat.add
                  ((app List.length ((var v_u945) (var v_xs))) (app List.length ((var v_u945) (var v_ys)))))))))))))

(LeanRecursionDefinition
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.reading
  (Type
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (arrow
        (app List ((var v_u945)))
        (arrow
          (app List ((var v_u945)))
          (arrow (arrow (var v_u945) (arrow (var v_u945) (app Bool ()))) (app List ((var v_u945))))))))
  (Value
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_xs
        (app List ((var v_u945)))
        (lam
          v_ys
          (app List ((var v_u945)))
          (lam
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
              ((app
                  Nat.succ
                  ((app
                      Nat.add
                      ((app List.length ((var v_u945) (var v_xs))) (app List.length ((var v_u945) (var v_ys)))))))
                (var v_u945)
                (var v_xs)
                (var v_ys)
                (var v_le)))))))))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel_zero
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_state
        (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
              ((var v_u945) (var v_le) (num 0) (var v_state)))
            (app List.nil ((var v_u945))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel_succ
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_le
      (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
      (pi
        v_fuel
        (app Nat ())
        (pi
          v_state
          (app PSigma ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
                ((var v_u945) (var v_le) (app Nat.succ ((var v_fuel))) (var v_state)))
              (app
                PSigma.casesOn
                ((app List ((var v_u945)))
                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                  (lam
                    v__x
                    (app
                      PSigma
                      ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                    (arrow
                      (pi
                        v_y
                        (app
                          PSigma
                          ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                        (arrow
                          (app
                            Prod.Lex
                            ((app List ((var v_u945)))
                              (app List ((var v_u945)))
                              (lam
                                v_a
                                (app List ((var v_u945)))
                                (lam
                                  v_x7
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                              (lam
                                v_a
                                (app List ((var v_u945)))
                                (lam
                                  v_x7
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                              (app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                  (lam
                                    v_x6
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                  (var v_y)
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (lam
                                      v_ys
                                      (app List ((var v_u945)))
                                      (app
                                        Prod.mk
                                        ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                              (app
                                PSigma.casesOn
                                ((app List ((var v_u945)))
                                  (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                                  (lam
                                    v_x6
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                  (var v__x)
                                  (lam
                                    v_xs
                                    (app List ((var v_u945)))
                                    (lam
                                      v_ys
                                      (app List ((var v_u945)))
                                      (app
                                        Prod.mk
                                        ((app List ((var v_u945)))
                                          (app List ((var v_u945)))
                                          (var v_xs)
                                          (var v_ys)))))))))
                          (app List ((var v_u945)))))
                      (app List ((var v_u945)))))
                  (var v_state)
                  (lam
                    v_xs
                    (app List ((var v_u945)))
                    (lam
                      v_ys
                      (app List ((var v_u945)))
                      (lam
                        v_a
                        (pi
                          v_y
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (arrow
                            (app
                              Prod.Lex
                              ((app List ((var v_u945)))
                                (app List ((var v_u945)))
                                (lam
                                  v_a
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x8
                                    (app List ((var v_u945)))
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                        (app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                                (lam
                                  v_a
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x8
                                    (app List ((var v_u945)))
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                        (app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                                (app
                                  PSigma.casesOn
                                  ((app List ((var v_u945)))
                                    (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (lam
                                      v__x
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))))
                                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                    (var v_y)
                                    (lam
                                      v_x7
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x8
                                        (app List ((var v_u945)))
                                        (app
                                          Prod.mk
                                          ((app List ((var v_u945)))
                                            (app List ((var v_u945)))
                                            (var v_x7)
                                            (var v_x8)))))))
                                (app
                                  PSigma.casesOn
                                  ((app List ((var v_u945)))
                                    (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (lam
                                      v__x
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))))
                                      (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                    (app
                                      PSigma.mk
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (var v_xs)
                                        (var v_ys)))
                                    (lam
                                      v_x7
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x8
                                        (app List ((var v_u945)))
                                        (app
                                          Prod.mk
                                          ((app List ((var v_u945)))
                                            (app List ((var v_u945)))
                                            (var v_x7)
                                            (var v_x8)))))))))
                            (app List ((var v_u945)))))
                        (app
                          _private.Init.Data.List.Sort.Basic.0.List.merge.match_1
                          ((var v_u945)
                            (lam
                              v_x7
                              (app List ((var v_u945)))
                              (lam
                                v_x8
                                (app List ((var v_u945)))
                                (arrow
                                  (pi
                                    v_y
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (arrow
                                      (app
                                        Prod.Lex
                                        ((app List ((var v_u945)))
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x11
                                              (app List ((var v_u945)))
                                              (app
                                                Nat.le
                                                ((app
                                                    Nat.succ
                                                    ((app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x10)))))
                                                  (app
                                                    List._sizeOf_1
                                                    ((var v_u945)
                                                      (app instSizeOfDefault ((var v_u945)))
                                                      (var v_x11)))))))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x11
                                              (app List ((var v_u945)))
                                              (app
                                                Nat.le
                                                ((app
                                                    Nat.succ
                                                    ((app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x10)))))
                                                  (app
                                                    List._sizeOf_1
                                                    ((var v_u945)
                                                      (app instSizeOfDefault ((var v_u945)))
                                                      (var v_x11)))))))
                                          (app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                              (lam
                                                v__x
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                                (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                              (var v_y)
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x11
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Prod.mk
                                                    ((app List ((var v_u945)))
                                                      (app List ((var v_u945)))
                                                      (var v_x10)
                                                      (var v_x11)))))))
                                          (app
                                            PSigma.casesOn
                                            ((app List ((var v_u945)))
                                              (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                              (lam
                                                v__x
                                                (app
                                                  PSigma
                                                  ((app List ((var v_u945)))
                                                    (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                                (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app
                                                PSigma.mk
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (var v_x7)
                                                  (var v_x8)))
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x11
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Prod.mk
                                                    ((app List ((var v_u945)))
                                                      (app List ((var v_u945)))
                                                      (var v_x10)
                                                      (var v_x11)))))))))
                                      (app List ((var v_u945)))))
                                  (app List ((var v_u945))))))
                            (var v_xs)
                            (var v_ys)
                            (lam
                              v_x7
                              (app List ((var v_u945)))
                              (lam
                                v_x
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (arrow
                                    (app
                                      Prod.Lex
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x9
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x9)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                        (lam
                                          v_x9
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x9)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (var v_y)
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x9)
                                                    (var v_x10)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (app List.nil ((var v_u945)))
                                                (var v_x7)))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x9)
                                                    (var v_x10)))))))))
                                    (app List ((var v_u945)))))
                                (var v_x7)))
                            (lam
                              v_x7
                              (app List ((var v_u945)))
                              (lam
                                v_x
                                (pi
                                  v_y
                                  (app
                                    PSigma
                                    ((app List ((var v_u945)))
                                      (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                                  (arrow
                                    (app
                                      Prod.Lex
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (lam
                                          v_x9
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x9)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                        (lam
                                          v_x9
                                          (app List ((var v_u945)))
                                          (lam
                                            v_x10
                                            (app List ((var v_u945)))
                                            (app
                                              Nat.le
                                              ((app
                                                  Nat.succ
                                                  ((app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x9)))))
                                                (app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (var v_y)
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x9)
                                                    (var v_x10)))))))
                                        (app
                                          PSigma.casesOn
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (lam
                                              v__x
                                              (app
                                                PSigma
                                                ((app List ((var v_u945)))
                                                  (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                              (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (var v_x7)
                                                (app List.nil ((var v_u945)))))
                                            (lam
                                              v_x9
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x10
                                                (app List ((var v_u945)))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (var v_x9)
                                                    (var v_x10)))))))))
                                    (app List ((var v_u945)))))
                                (var v_x7)))
                            (lam
                              v_x
                              (var v_u945)
                              (lam
                                v_x8
                                (app List ((var v_u945)))
                                (lam
                                  v_y
                                  (var v_u945)
                                  (lam
                                    v_x10
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x11
                                      (pi
                                        v_x11
                                        (app
                                          PSigma
                                          ((app List ((var v_u945)))
                                            (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))))
                                        (arrow
                                          (app
                                            Prod.Lex
                                            ((app List ((var v_u945)))
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x12
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x13
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x12)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x13)))))))
                                              (lam
                                                v_x12
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_x13
                                                  (app List ((var v_u945)))
                                                  (app
                                                    Nat.le
                                                    ((app
                                                        Nat.succ
                                                        ((app
                                                            List._sizeOf_1
                                                            ((var v_u945)
                                                              (app instSizeOfDefault ((var v_u945)))
                                                              (var v_x12)))))
                                                      (app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_x13)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v__x
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x12
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (var v_x11)
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x13
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x12)
                                                          (var v_x13)))))))
                                              (app
                                                PSigma.casesOn
                                                ((app List ((var v_u945)))
                                                  (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (lam
                                                    v__x
                                                    (app
                                                      PSigma
                                                      ((app List ((var v_u945)))
                                                        (lam
                                                          v_x12
                                                          (app List ((var v_u945)))
                                                          (app List ((var v_u945))))))
                                                    (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (app List.cons ((var v_u945) (var v_x) (var v_x8)))
                                                      (app List.cons ((var v_u945) (var v_y) (var v_x10)))))
                                                  (lam
                                                    v_x12
                                                    (app List ((var v_u945)))
                                                    (lam
                                                      v_x13
                                                      (app List ((var v_u945)))
                                                      (app
                                                        Prod.mk
                                                        ((app List ((var v_u945)))
                                                          (app List ((var v_u945)))
                                                          (var v_x12)
                                                          (var v_x13)))))))))
                                          (app List ((var v_u945)))))
                                      (app
                                        dite
                                        ((app List ((var v_u945)))
                                          (app
                                            Eq
                                            ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                          (app
                                            instDecidableEqBool
                                            ((apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                          (lam
                                            v_h
                                            (app
                                              Eq
                                              ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_x)
                                                (apv
                                                  (var v_x11)
                                                  ((app
                                                      PSigma.mk
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_x8)
                                                        (app List.cons ((var v_u945) (var v_y) (var v_x10)))))
                                                    (proof))))))
                                          (lam
                                            v_h
                                            (arrow
                                              (app
                                                Eq
                                                ((app Bool ())
                                                  (apv (var v_le) ((var v_x) (var v_y)))
                                                  (app Bool.true ())))
                                              (app False ()))
                                            (app
                                              List.cons
                                              ((var v_u945)
                                                (var v_y)
                                                (apv
                                                  (var v_x11)
                                                  ((app
                                                      PSigma.mk
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app List.cons ((var v_u945) (var v_x) (var v_x8)))
                                                        (var v_x10)))
                                                    (proof)))))))))))))
                            (var v_a))))))
                  (lam
                    v_smaller
                    (app
                      PSigma
                      ((app List ((var v_u945))) (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                    (lam
                      v_decrease
                      (app
                        Prod.Lex
                        ((app List ((var v_u945)))
                          (app List ((var v_u945)))
                          (lam
                            v_a
                            (app List ((var v_u945)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                  (app
                                    List._sizeOf_1
                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))))
                          (lam
                            v_a
                            (app List ((var v_u945)))
                            (lam
                              v_x6
                              (app List ((var v_u945)))
                              (app
                                Nat.le
                                ((app
                                    Nat.succ
                                    ((app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                  (app
                                    List._sizeOf_1
                                    ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x6)))))))
                          (app
                            PSigma.casesOn
                            ((app List ((var v_u945)))
                              (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                              (lam
                                v__x
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                              (var v_smaller)
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (lam
                                  v_ys
                                  (app List ((var v_u945)))
                                  (app
                                    Prod.mk
                                    ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))
                          (app
                            PSigma.casesOn
                            ((app List ((var v_u945)))
                              (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))
                              (lam
                                v__x
                                (app
                                  PSigma
                                  ((app List ((var v_u945)))
                                    (lam v_xs (app List ((var v_u945))) (app List ((var v_u945))))))
                                (app Prod ((app List ((var v_u945))) (app List ((var v_u945))))))
                              (var v_state)
                              (lam
                                v_xs
                                (app List ((var v_u945)))
                                (lam
                                  v_ys
                                  (app List ((var v_u945)))
                                  (app
                                    Prod.mk
                                    ((app List ((var v_u945))) (app List ((var v_u945))) (var v_xs) (var v_ys)))))))))
                      (app
                        Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
                        ((var v_u945) (var v_le) (var v_fuel) (var v_smaller)))))))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_succ
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_xs
        (app List ((var v_u945)))
        (pi
          v_ys
          (app List ((var v_u945)))
          (pi
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Eq
              ((app List ((var v_u945)))
                (app
                  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                  ((app Nat.succ ((var v_fuel))) (var v_u945) (var v_xs) (var v_ys) (var v_le)))
                (app
                  List.rec
                  ((var v_u945)
                    (lam
                      v_x
                      (app List ((var v_u945)))
                      (arrow
                        (pi
                          v_y
                          (app
                            PSigma
                            ((app List ((var v_u945))) (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))))
                          (arrow
                            (app
                              Prod.Lex
                              ((app List ((var v_u945)))
                                (app List ((var v_u945)))
                                (lam
                                  v_a
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x8
                                    (app List ((var v_u945)))
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                        (app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                                (lam
                                  v_a
                                  (app List ((var v_u945)))
                                  (lam
                                    v_x8
                                    (app List ((var v_u945)))
                                    (app
                                      Nat.le
                                      ((app
                                          Nat.succ
                                          ((app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                        (app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x8)))))))
                                (app
                                  Prod.mk
                                  ((app List ((var v_u945)))
                                    (app List ((var v_u945)))
                                    (app
                                      PSigma.fst
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (var v_y)))
                                    (app
                                      PSigma.snd
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (var v_y)))))
                                (app
                                  Prod.mk
                                  ((app List ((var v_u945)))
                                    (app List ((var v_u945)))
                                    (app
                                      PSigma.fst
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (app
                                          PSigma.mk
                                          ((app List ((var v_u945)))
                                            (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_x)
                                            (var v_ys)))))
                                    (app
                                      PSigma.snd
                                      ((app List ((var v_u945)))
                                        (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (app
                                          PSigma.mk
                                          ((app List ((var v_u945)))
                                            (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_x)
                                            (var v_ys)))))))))
                            (app List ((var v_u945)))))
                        (app List ((var v_u945)))))
                    (lam
                      v_x
                      (pi
                        v_y
                        (app
                          PSigma
                          ((app List ((var v_u945))) (lam v_x5 (app List ((var v_u945))) (app List ((var v_u945))))))
                        (arrow
                          (app
                            Prod.Lex
                            ((app List ((var v_u945)))
                              (app List ((var v_u945)))
                              (lam
                                v_a
                                (app List ((var v_u945)))
                                (lam
                                  v_x7
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                              (lam
                                v_a
                                (app List ((var v_u945)))
                                (lam
                                  v_x7
                                  (app List ((var v_u945)))
                                  (app
                                    Nat.le
                                    ((app
                                        Nat.succ
                                        ((app
                                            List._sizeOf_1
                                            ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                      (app
                                        List._sizeOf_1
                                        ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                              (app
                                Prod.mk
                                ((app List ((var v_u945)))
                                  (app List ((var v_u945)))
                                  (app
                                    PSigma.fst
                                    ((app List ((var v_u945)))
                                      (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                      (var v_y)))
                                  (app
                                    PSigma.snd
                                    ((app List ((var v_u945)))
                                      (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                      (var v_y)))))
                              (app
                                Prod.mk
                                ((app List ((var v_u945)))
                                  (app List ((var v_u945)))
                                  (app
                                    PSigma.fst
                                    ((app List ((var v_u945)))
                                      (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                      (app
                                        PSigma.mk
                                        ((app List ((var v_u945)))
                                          (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (app List.nil ((var v_u945)))
                                          (var v_ys)))))
                                  (app
                                    PSigma.snd
                                    ((app List ((var v_u945)))
                                      (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                      (app
                                        PSigma.mk
                                        ((app List ((var v_u945)))
                                          (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                          (app List.nil ((var v_u945)))
                                          (var v_ys)))))))))
                          (app List ((var v_u945)))))
                      (var v_ys))
                    (lam
                      v_head
                      (var v_u945)
                      (lam
                        v_tail
                        (app List ((var v_u945)))
                        (lam
                          v_tail_ih
                          (arrow
                            (pi
                              v_y
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))))
                              (arrow
                                (app
                                  Prod.Lex
                                  ((app List ((var v_u945)))
                                    (app List ((var v_u945)))
                                    (lam
                                      v_a
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))))
                                    (lam
                                      v_a
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x9
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x9)))))))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (app
                                          PSigma.fst
                                          ((app List ((var v_u945)))
                                            (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_y)))
                                        (app
                                          PSigma.snd
                                          ((app List ((var v_u945)))
                                            (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_y)))))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (app
                                          PSigma.fst
                                          ((app List ((var v_u945)))
                                            (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (var v_tail)
                                                (var v_ys)))))
                                        (app
                                          PSigma.snd
                                          ((app List ((var v_u945)))
                                            (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (var v_tail)
                                                (var v_ys)))))))))
                                (app List ((var v_u945)))))
                            (app List ((var v_u945))))
                          (lam
                            v_x
                            (pi
                              v_y
                              (app
                                PSigma
                                ((app List ((var v_u945)))
                                  (lam v_x8 (app List ((var v_u945))) (app List ((var v_u945))))))
                              (arrow
                                (app
                                  Prod.Lex
                                  ((app List ((var v_u945)))
                                    (app List ((var v_u945)))
                                    (lam
                                      v_a
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x10
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                    (lam
                                      v_a
                                      (app List ((var v_u945)))
                                      (lam
                                        v_x10
                                        (app List ((var v_u945)))
                                        (app
                                          Nat.le
                                          ((app
                                              Nat.succ
                                              ((app
                                                  List._sizeOf_1
                                                  ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                            (app
                                              List._sizeOf_1
                                              ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x10)))))))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (app
                                          PSigma.fst
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_y)))
                                        (app
                                          PSigma.snd
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (var v_y)))))
                                    (app
                                      Prod.mk
                                      ((app List ((var v_u945)))
                                        (app List ((var v_u945)))
                                        (app
                                          PSigma.fst
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                (var v_ys)))))
                                        (app
                                          PSigma.snd
                                          ((app List ((var v_u945)))
                                            (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                            (app
                                              PSigma.mk
                                              ((app List ((var v_u945)))
                                                (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))
                                                (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                (var v_ys)))))))))
                                (app List ((var v_u945)))))
                            (app
                              List.rec
                              ((var v_u945)
                                (lam
                                  v_x9
                                  (app List ((var v_u945)))
                                  (arrow
                                    (pi
                                      v_y
                                      (app
                                        PSigma
                                        ((app List ((var v_u945)))
                                          (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))))
                                      (arrow
                                        (app
                                          Prod.Lex
                                          ((app List ((var v_u945)))
                                            (app List ((var v_u945)))
                                            (lam
                                              v_a
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x12
                                                (app List ((var v_u945)))
                                                (app
                                                  Nat.le
                                                  ((app
                                                      Nat.succ
                                                      ((app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_a)))))
                                                    (app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x12)))))))
                                            (lam
                                              v_a
                                              (app List ((var v_u945)))
                                              (lam
                                                v_x12
                                                (app List ((var v_u945)))
                                                (app
                                                  Nat.le
                                                  ((app
                                                      Nat.succ
                                                      ((app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_a)))))
                                                    (app
                                                      List._sizeOf_1
                                                      ((var v_u945)
                                                        (app instSizeOfDefault ((var v_u945)))
                                                        (var v_x12)))))))
                                            (app
                                              Prod.mk
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (app
                                                  PSigma.fst
                                                  ((app List ((var v_u945)))
                                                    (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (var v_y)))
                                                (app
                                                  PSigma.snd
                                                  ((app List ((var v_u945)))
                                                    (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (var v_y)))))
                                            (app
                                              Prod.mk
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (app
                                                  PSigma.fst
                                                  ((app List ((var v_u945)))
                                                    (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (app
                                                      PSigma.mk
                                                      ((app List ((var v_u945)))
                                                        (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                        (var v_x9)))))
                                                (app
                                                  PSigma.snd
                                                  ((app List ((var v_u945)))
                                                    (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                    (app
                                                      PSigma.mk
                                                      ((app List ((var v_u945)))
                                                        (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                        (var v_x9)))))))))
                                        (app List ((var v_u945)))))
                                    (app List ((var v_u945)))))
                                (lam
                                  v_x9
                                  (pi
                                    v_y
                                    (app
                                      PSigma
                                      ((app List ((var v_u945)))
                                        (lam v_x9 (app List ((var v_u945))) (app List ((var v_u945))))))
                                    (arrow
                                      (app
                                        Prod.Lex
                                        ((app List ((var v_u945)))
                                          (app List ((var v_u945)))
                                          (lam
                                            v_a
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x11
                                              (app List ((var v_u945)))
                                              (app
                                                Nat.le
                                                ((app
                                                    Nat.succ
                                                    ((app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_a)))))
                                                  (app
                                                    List._sizeOf_1
                                                    ((var v_u945)
                                                      (app instSizeOfDefault ((var v_u945)))
                                                      (var v_x11)))))))
                                          (lam
                                            v_a
                                            (app List ((var v_u945)))
                                            (lam
                                              v_x11
                                              (app List ((var v_u945)))
                                              (app
                                                Nat.le
                                                ((app
                                                    Nat.succ
                                                    ((app
                                                        List._sizeOf_1
                                                        ((var v_u945)
                                                          (app instSizeOfDefault ((var v_u945)))
                                                          (var v_a)))))
                                                  (app
                                                    List._sizeOf_1
                                                    ((var v_u945)
                                                      (app instSizeOfDefault ((var v_u945)))
                                                      (var v_x11)))))))
                                          (app
                                            Prod.mk
                                            ((app List ((var v_u945)))
                                              (app List ((var v_u945)))
                                              (app
                                                PSigma.fst
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (var v_y)))
                                              (app
                                                PSigma.snd
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (var v_y)))))
                                          (app
                                            Prod.mk
                                            ((app List ((var v_u945)))
                                              (app List ((var v_u945)))
                                              (app
                                                PSigma.fst
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                      (app List.nil ((var v_u945)))))))
                                              (app
                                                PSigma.snd
                                                ((app List ((var v_u945)))
                                                  (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                  (app
                                                    PSigma.mk
                                                    ((app List ((var v_u945)))
                                                      (lam v_x10 (app List ((var v_u945))) (app List ((var v_u945))))
                                                      (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                      (app List.nil ((var v_u945)))))))))))
                                      (app List ((var v_u945)))))
                                  (app List.cons ((var v_u945) (var v_head) (var v_tail))))
                                (lam
                                  v_x9
                                  (var v_u945)
                                  (lam
                                    v_x10
                                    (app List ((var v_u945)))
                                    (lam
                                      v_x11
                                      (arrow
                                        (pi
                                          v_y
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam v_x11 (app List ((var v_u945))) (app List ((var v_u945))))))
                                          (arrow
                                            (app
                                              Prod.Lex
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_a
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_a)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x13)))))))
                                                (lam
                                                  v_a
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x13
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_a)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x13)))))))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (app
                                                      PSigma.fst
                                                      ((app List ((var v_u945)))
                                                        (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_y)))
                                                    (app
                                                      PSigma.snd
                                                      ((app List ((var v_u945)))
                                                        (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_y)))))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (app
                                                      PSigma.fst
                                                      ((app List ((var v_u945)))
                                                        (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app
                                                          PSigma.mk
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x12
                                                              (app List ((var v_u945)))
                                                              (app List ((var v_u945))))
                                                            (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                            (var v_x10)))))
                                                    (app
                                                      PSigma.snd
                                                      ((app List ((var v_u945)))
                                                        (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app
                                                          PSigma.mk
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x12
                                                              (app List ((var v_u945)))
                                                              (app List ((var v_u945))))
                                                            (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                            (var v_x10)))))))))
                                            (app List ((var v_u945)))))
                                        (app List ((var v_u945))))
                                      (lam
                                        v_x12
                                        (pi
                                          v_y
                                          (app
                                            PSigma
                                            ((app List ((var v_u945)))
                                              (lam v_x12 (app List ((var v_u945))) (app List ((var v_u945))))))
                                          (arrow
                                            (app
                                              Prod.Lex
                                              ((app List ((var v_u945)))
                                                (app List ((var v_u945)))
                                                (lam
                                                  v_a
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x14
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_a)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x14)))))))
                                                (lam
                                                  v_a
                                                  (app List ((var v_u945)))
                                                  (lam
                                                    v_x14
                                                    (app List ((var v_u945)))
                                                    (app
                                                      Nat.le
                                                      ((app
                                                          Nat.succ
                                                          ((app
                                                              List._sizeOf_1
                                                              ((var v_u945)
                                                                (app instSizeOfDefault ((var v_u945)))
                                                                (var v_a)))))
                                                        (app
                                                          List._sizeOf_1
                                                          ((var v_u945)
                                                            (app instSizeOfDefault ((var v_u945)))
                                                            (var v_x14)))))))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (app
                                                      PSigma.fst
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_y)))
                                                    (app
                                                      PSigma.snd
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (var v_y)))))
                                                (app
                                                  Prod.mk
                                                  ((app List ((var v_u945)))
                                                    (app List ((var v_u945)))
                                                    (app
                                                      PSigma.fst
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app
                                                          PSigma.mk
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x13
                                                              (app List ((var v_u945)))
                                                              (app List ((var v_u945))))
                                                            (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                            (app List.cons ((var v_u945) (var v_x9) (var v_x10)))))))
                                                    (app
                                                      PSigma.snd
                                                      ((app List ((var v_u945)))
                                                        (lam v_x13 (app List ((var v_u945))) (app List ((var v_u945))))
                                                        (app
                                                          PSigma.mk
                                                          ((app List ((var v_u945)))
                                                            (lam
                                                              v_x13
                                                              (app List ((var v_u945)))
                                                              (app List ((var v_u945))))
                                                            (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                            (app
                                                              List.cons
                                                              ((var v_u945) (var v_x9) (var v_x10)))))))))))
                                            (app List ((var v_u945)))))
                                        (app
                                          dite
                                          ((app List ((var v_u945)))
                                            (app
                                              Eq
                                              ((app Bool ())
                                                (apv (var v_le) ((var v_head) (var v_x9)))
                                                (app Bool.true ())))
                                            (app
                                              instDecidableEqBool
                                              ((apv (var v_le) ((var v_head) (var v_x9))) (app Bool.true ())))
                                            (lam
                                              v_h
                                              (app
                                                Eq
                                                ((app Bool ())
                                                  (apv (var v_le) ((var v_head) (var v_x9)))
                                                  (app Bool.true ())))
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_head)
                                                  (apv
                                                    (var v_x12)
                                                    ((app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x14
                                                            (app List ((var v_u945)))
                                                            (app List ((var v_u945))))
                                                          (var v_tail)
                                                          (app List.cons ((var v_u945) (var v_x9) (var v_x10)))))
                                                      (proof))))))
                                            (lam
                                              v_h
                                              (arrow
                                                (app
                                                  Eq
                                                  ((app Bool ())
                                                    (apv (var v_le) ((var v_head) (var v_x9)))
                                                    (app Bool.true ())))
                                                (app False ()))
                                              (app
                                                List.cons
                                                ((var v_u945)
                                                  (var v_x9)
                                                  (apv
                                                    (var v_x12)
                                                    ((app
                                                        PSigma.mk
                                                        ((app List ((var v_u945)))
                                                          (lam
                                                            v_x14
                                                            (app List ((var v_u945)))
                                                            (app List ((var v_u945))))
                                                          (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                                                          (var v_x10)))
                                                      (proof))))))))))))
                                (var v_ys)
                                (var v_x)))))))
                    (var v_xs)
                    (lam
                      v_smaller
                      (app
                        PSigma
                        ((app List ((var v_u945))) (lam v_x5 (app List ((var v_u945))) (app List ((var v_u945))))))
                      (lam
                        v_decrease
                        (app
                          Prod.Lex
                          ((app List ((var v_u945)))
                            (app List ((var v_u945)))
                            (lam
                              v_a
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (lam
                              v_a
                              (app List ((var v_u945)))
                              (lam
                                v_x7
                                (app List ((var v_u945)))
                                (app
                                  Nat.le
                                  ((app
                                      Nat.succ
                                      ((app
                                          List._sizeOf_1
                                          ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_a)))))
                                    (app
                                      List._sizeOf_1
                                      ((var v_u945) (app instSizeOfDefault ((var v_u945))) (var v_x7)))))))
                            (app
                              Prod.mk
                              ((app List ((var v_u945)))
                                (app List ((var v_u945)))
                                (app
                                  PSigma.fst
                                  ((app List ((var v_u945)))
                                    (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (var v_smaller)))
                                (app
                                  PSigma.snd
                                  ((app List ((var v_u945)))
                                    (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (var v_smaller)))))
                            (app
                              Prod.mk
                              ((app List ((var v_u945)))
                                (app List ((var v_u945)))
                                (app
                                  PSigma.fst
                                  ((app List ((var v_u945)))
                                    (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (app
                                      PSigma.mk
                                      ((app List ((var v_u945)))
                                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (var v_xs)
                                        (var v_ys)))))
                                (app
                                  PSigma.snd
                                  ((app List ((var v_u945)))
                                    (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                    (app
                                      PSigma.mk
                                      ((app List ((var v_u945)))
                                        (lam v_x6 (app List ((var v_u945))) (app List ((var v_u945))))
                                        (var v_xs)
                                        (var v_ys)))))))))
                        (app
                          Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                          ((var v_fuel)
                            (var v_u945)
                            (app
                              PSigma.fst
                              ((app List ((var v_u945)))
                                (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                (var v_smaller)))
                            (app
                              PSigma.snd
                              ((app List ((var v_u945)))
                                (lam v_x7 (app List ((var v_u945))) (app List ((var v_u945))))
                                (var v_smaller)))
                            (var v_le))))))))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.adequate
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (pi
            v_fuel
            (app Nat ())
            (arrow
              (app
                Nat.le
                ((app
                    Nat.succ
                    ((app
                        Mettapedia.Languages.Lean.Recursion.MergeRank.rank
                        ((var v_u945)
                          (app
                            PSigma.mk
                            ((app List ((var v_u945)))
                              (lam v_x5 (app List ((var v_u945))) (app List ((var v_u945))))
                              (var v_xs)
                              (var v_ys)))))))
                  (var v_fuel)))
              (app
                Eq
                ((app List ((var v_u945)))
                  (app
                    Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.fuel
                    ((var v_u945)
                      (var v_le)
                      (var v_fuel)
                      (app
                        PSigma.mk
                        ((app List ((var v_u945)))
                          (lam v_x5 (app List ((var v_u945))) (app List ((var v_u945))))
                          (var v_xs)
                          (var v_ys)))))
                  (app List.merge ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.budgetAdequate
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Nat.le
            ((app
                Nat.succ
                ((app
                    Mettapedia.Languages.Lean.Recursion.MergeRank.rank
                    ((var v_u945)
                      (app
                        PSigma.mk
                        ((app List ((var v_u945)))
                          (lam v_x4 (app List ((var v_u945))) (app List ((var v_u945))))
                          (var v_xs)
                          (var v_ys)))))))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.budget
                ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))))
  (Axioms ()))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.bridge
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Eq
            ((app List ((var v_u945)))
              (app List.merge ((var v_u945) (var v_xs) (var v_ys) (var v_le)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.reading
                ((var v_u945) (var v_xs) (var v_ys) (var v_le)))))))))
  (Axioms (propext Quot.sound)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_zero
  (pi
    v_u945
    (sort (lsucc (lvl l_u_1)))
    (pi
      v_xs
      (app List ((var v_u945)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                ((num 0) (var v_u945) (var v_xs) (var v_ys) (var v_le)))
              (app List.nil ((var v_u945)))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case0
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_ys
        (app List ((var v_u945)))
        (pi
          v_le
          (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
          (app
            Eq
            ((app List ((var v_u945)))
              (app
                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                ((app Nat.succ ((var v_fuel))) (var v_u945) (app List.nil ((var v_u945))) (var v_ys) (var v_le)))
              (var v_ys)))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case1.branch0
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (app
          Eq
          ((app List ((var v_u945)))
            (app
              Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
              ((app Nat.succ ((var v_fuel)))
                (var v_u945)
                (app List.nil ((var v_u945)))
                (app List.nil ((var v_u945)))
                (var v_le)))
            (app List.nil ((var v_u945))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case1.branch1
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_head
        (var v_u945)
        (pi
          v_tail
          (app List ((var v_u945)))
          (pi
            v_le
            (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
            (app
              Eq
              ((app List ((var v_u945)))
                (app
                  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                  ((app Nat.succ ((var v_fuel)))
                    (var v_u945)
                    (app List.cons ((var v_u945) (var v_head) (var v_tail)))
                    (app List.nil ((var v_u945)))
                    (var v_le)))
                (app List.cons ((var v_u945) (var v_head) (var v_tail))))))))))
  (Axioms (propext)))

(LeanRecursionTheorem
  Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel_case3
  (pi
    v_fuel
    (app Nat ())
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_le
        (arrow (var v_u945) (arrow (var v_u945) (app Bool ())))
        (pi
          v_x
          (var v_u945)
          (pi
            v_xs_2
            (app List ((var v_u945)))
            (pi
              v_y
              (var v_u945)
              (pi
                v_ys_2
                (app List ((var v_u945)))
                (app
                  Eq
                  ((app List ((var v_u945)))
                    (app
                      Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                      ((app Nat.succ ((var v_fuel)))
                        (var v_u945)
                        (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                        (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                        (var v_le)))
                    (app
                      dite
                      ((app List ((var v_u945)))
                        (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                        (app instDecidableEqBool ((apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                        (lam
                          v_h
                          (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                          (app
                            List.cons
                            ((var v_u945)
                              (var v_x)
                              (app
                                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                                ((var v_fuel)
                                  (var v_u945)
                                  (var v_xs_2)
                                  (app List.cons ((var v_u945) (var v_y) (var v_ys_2)))
                                  (var v_le))))))
                        (lam
                          v_h
                          (arrow
                            (app Eq ((app Bool ()) (apv (var v_le) ((var v_x) (var v_y))) (app Bool.true ())))
                            (app False ()))
                          (app
                            List.cons
                            ((var v_u945)
                              (var v_y)
                              (app
                                Mettapedia.Languages.Lean.Recursion.FuelCore.Merge.sourceFuel
                                ((var v_fuel)
                                  (var v_u945)
                                  (app List.cons ((var v_u945) (var v_x) (var v_xs_2)))
                                  (var v_ys_2)
                                  (var v_le)))))))))))))))))
  (Axioms (propext)))

(LeanProofArgumentFunction
  Multiset.foldr
  (SourceType
    (pi
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (pi
        v_u946
        (sort (lsucc (lvl l_v)))
        (pi
          v_f
          (arrow (var v_u945) (arrow (var v_u946) (var v_u946)))
          (arrow
            (app LeftCommutative ((var v_u945) (var v_u946) (var v_f)))
            (arrow
              (var v_u946)
              (arrow
                (app
                  Quot
                  ((app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam v_x4 (app List ((var v_u945))) (app List.Perm ((var v_u945) (var v_a) (var v_x4)))))))
                (var v_u946))))))))
  (Body
    (lam
      v_u945
      (sort (lsucc (lvl l_u_1)))
      (lam
        v_u946
        (sort (lsucc (lvl l_v)))
        (lam
          v_f
          (arrow (var v_u945) (arrow (var v_u946) (var v_u946)))
          (lam
            v_inst
            (app LeftCommutative ((var v_u945) (var v_u946) (var v_f)))
            (lam
              v_b
              (var v_u946)
              (lam
                v_s
                (app
                  Quot
                  ((app List ((var v_u945)))
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam v_x6 (app List ((var v_u945))) (app List.Perm ((var v_u945) (var v_a) (var v_x6)))))))
                (app
                  Quot.liftOn
                  ((app List ((var v_u945)))
                    (var v_u946)
                    (lam
                      v_a
                      (app List ((var v_u945)))
                      (lam v_x7 (app List ((var v_u945))) (app List.Perm ((var v_u945) (var v_a) (var v_x7)))))
                    (var v_s)
                    (lam
                      v_l
                      (app List ((var v_u945)))
                      (app List.foldr ((var v_u945) (var v_u946) (var v_f) (var v_b) (var v_l))))
                    (proof))))))))))
  (Arguments
    ((argument
        3
        (Proposition
          (lam
            v_u945
            (sort (lsucc (lvl l_u_1)))
            (lam
              v_u946
              (sort (lsucc (lvl l_v)))
              (lam
                v_f
                (arrow (var v_u945) (arrow (var v_u946) (var v_u946)))
                (app LeftCommutative ((var v_u945) (var v_u946) (var v_f)))))))
        (Uses (("application-function" "application-function" "application-argument")))))))

(LeanProofArgumentFunction
  Quot.liftOn
  (SourceType
    (pi
      v_u945
      (sort (lvl l_u))
      (pi
        v_u946
        (sort (lvl l_v))
        (pi
          v_r
          (arrow (var v_u945) (arrow (var v_u945) (prop)))
          (arrow
            (app Quot ((var v_u945) (var v_r)))
            (pi
              v_f
              (arrow (var v_u945) (var v_u946))
              (arrow
                (pi
                  v_a
                  (var v_u945)
                  (pi
                    v_b
                    (var v_u945)
                    (arrow
                      (apv (var v_r) ((var v_a) (var v_b)))
                      (app Eq ((var v_u946) (apv (var v_f) ((var v_a))) (apv (var v_f) ((var v_b))))))))
                (var v_u946))))))))
  (Body
    (lam
      v_u945
      (sort (lvl l_u))
      (lam
        v_u946
        (sort (lvl l_v))
        (lam
          v_r
          (arrow (var v_u945) (arrow (var v_u945) (prop)))
          (lam
            v_q
            (app Quot ((var v_u945) (var v_r)))
            (lam
              v_f
              (arrow (var v_u945) (var v_u946))
              (lam
                v_c
                (pi
                  v_a
                  (var v_u945)
                  (pi
                    v_b
                    (var v_u945)
                    (arrow
                      (apv (var v_r) ((var v_a) (var v_b)))
                      (app Eq ((var v_u946) (apv (var v_f) ((var v_a))) (apv (var v_f) ((var v_b))))))))
                (app Quot.lift ((var v_u945) (var v_r) (var v_u946) (var v_f) (proof) (var v_q))))))))))
  (Arguments
    ((argument
        5
        (Proposition
          (lam
            v_u945
            (sort (lvl l_u))
            (lam
              v_u946
              (sort (lvl l_v))
              (lam
                v_r
                (arrow (var v_u945) (arrow (var v_u945) (prop)))
                (lam
                  v_f
                  (arrow (var v_u945) (var v_u946))
                  (pi
                    v_a
                    (var v_u945)
                    (pi
                      v_b
                      (var v_u945)
                      (arrow
                        (apv (var v_r) ((var v_a) (var v_b)))
                        (app Eq ((var v_u946) (apv (var v_f) ((var v_a))) (apv (var v_f) ((var v_b)))))))))))))
        (Uses (("application-argument")))))))

(LeanProofArgumentFunction
  decidable_of_decidable_of_iff
  (SourceType
    (pi
      v_p
      (prop)
      (pi
        v_q
        (prop)
        (arrow (app Decidable ((var v_p))) (arrow (app Iff ((var v_p) (var v_q))) (app Decidable ((var v_q))))))))
  (Body
    (lam
      v_p
      (prop)
      (lam
        v_q
        (prop)
        (lam
          v_inst
          (app Decidable ((var v_p)))
          (lam
            v_h
            (app Iff ((var v_p) (var v_q)))
            (app
              dite
              ((app Decidable ((var v_q)))
                (var v_p)
                (var v_inst)
                (lam v_hp (var v_p) (app Decidable.isTrue ((var v_q) (proof))))
                (lam v_hp (arrow (var v_p) (app False ())) (app Decidable.isFalse ((var v_q) (proof)))))))))))
  (Arguments
    ((argument
        3
        (Proposition (lam v_p (prop) (lam v_q (prop) (app Iff ((var v_p) (var v_q))))))
        (Uses (("application-argument")))))))

(LeanProofArgumentFunction
  decidable_of_iff
  (SourceType
    (pi
      v_b
      (prop)
      (pi
        v_a
        (prop)
        (arrow (app Iff ((var v_a) (var v_b))) (arrow (app Decidable ((var v_a))) (app Decidable ((var v_b))))))))
  (Body
    (lam
      v_b
      (prop)
      (lam
        v_a
        (prop)
        (lam
          v_h
          (app Iff ((var v_a) (var v_b)))
          (lam
            v_inst
            (app Decidable ((var v_a)))
            (app decidable_of_decidable_of_iff ((var v_a) (var v_b) (var v_inst) (proof))))))))
  (Arguments
    ((argument
        2
        (Proposition (lam v_b (prop) (lam v_a (prop) (app Iff ((var v_a) (var v_b))))))
        (Uses (("application-function" "application-argument")))))))

(LeanProofArgumentFunction
  decidable_of_iff'
  (SourceType
    (pi
      v_a
      (prop)
      (pi
        v_b
        (prop)
        (arrow (app Iff ((var v_a) (var v_b))) (arrow (app Decidable ((var v_b))) (app Decidable ((var v_a))))))))
  (Body
    (lam
      v_a
      (prop)
      (lam
        v_b
        (prop)
        (lam
          v_h
          (app Iff ((var v_a) (var v_b)))
          (lam
            v_inst
            (app Decidable ((var v_b)))
            (app decidable_of_decidable_of_iff ((var v_b) (var v_a) (var v_inst) (proof))))))))
  (Arguments
    ((argument
        2
        (Proposition (lam v_a (prop) (lam v_b (prop) (app Iff ((var v_a) (var v_b))))))
        (Uses (("application-function" "application-argument")))))))
