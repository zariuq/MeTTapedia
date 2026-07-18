; Generated from actual E and Vampire TSTP equality proofs.
; E normalizes the step as rw; Vampire exposes it as superposition.
; Both derive the same child, direction, position, and final refutation.
!(import! &self lib_atp)

!(bind! &external-equality-kbo (ATP.KBO 1 1 () (b a p ATP.Eq)))
!(bind! &external-equality ((ATP.Pos (ATP.Eq a b))))
!(bind! &external-target ((ATP.Neg (p b))))
!(bind! &external-child ((ATP.Neg (p a))))

!(assertEqual
  (atp:kbo:config-valid &external-equality-kbo)
  True)
!(assertEqual
  (atp:kbo:greater &external-equality-kbo b a)
  True)
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target (ATP.Subst ())
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p b)) (ATP.Position (1))
    &external-equality-kbo &external-child)
  True)
!(assertEqual
  (atp:resolution:check-step
    &external-child ((ATP.Pos (p a))) (ATP.Subst ())
    (ATP.Neg (p a)) (ATP.Pos (p a)) ())
  True)

; Reversing the certified equality direction violates KBO.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target (ATP.Subst ())
    (ATP.Pos (ATP.Eq a b)) ATP.LeftToRight
    (ATP.Neg (p b)) (ATP.Position (1))
    &external-equality-kbo &external-child)
  False)
; A changed child is not the supplied-position replacement.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target (ATP.Subst ())
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p b)) (ATP.Position (1))
    &external-equality-kbo ((ATP.Neg (forged))))
  False)
; A changed position is rejected.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target (ATP.Subst ())
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p b)) (ATP.Position (2))
    &external-equality-kbo &external-child)
  False)
; A reversed precedence cannot justify the observed orientation.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target (ATP.Subst ())
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p b)) (ATP.Position (1))
    (ATP.KBO 1 1 () (a b p ATP.Eq)) &external-child)
  False)
; Cyclic substitution evidence fails before replay.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality &external-target
    (ATP.Subst ((ATP.Bind x (ATP.Var y)) (ATP.Bind y (ATP.Var x))))
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p b)) (ATP.Position (1))
    &external-equality-kbo &external-child)
  False)
; An original variable target position is forbidden.
!(assertEqual
  (atp:superposition:check-unit-step
    &external-equality ((ATP.Neg (p (ATP.Var x))))
    (ATP.Subst ((ATP.Bind x b)))
    (ATP.Pos (ATP.Eq a b)) ATP.RightToLeft
    (ATP.Neg (p (ATP.Var x))) (ATP.Position (1))
    &external-equality-kbo &external-child)
  False)

; Reconstruct an ordinary proof term for Prime's unchanged checker.
!(bind! &external-equality-kb (new-space))
!(add-atom &external-equality-kb (: Obj Type))
!(add-atom &external-equality-kb (: a Obj))
!(add-atom &external-equality-kb (: b Obj))
!(add-atom &external-equality-kb (: EqT (-> Obj Obj Type)))
!(add-atom &external-equality-kb (: Pred (-> Obj Type)))
!(add-atom &external-equality-kb (: eq-proof (EqT a b)))
!(add-atom &external-equality-kb (: fact-proof (Pred a)))
!(add-atom &external-equality-kb
  (: equality-substitution
    (-> (EqT $left $right) (Pred $left) (Pred $right))))
!(assertEqual
  (check-type &external-equality-kb
    (equality-substitution eq-proof fact-proof)
    (Pred b) 100000)
  (he-accept (exact (Pred b))))

!(println!
  (SetMMPrimeExternalEqualityReplaySummary
    equality_transport 2 11 11 0))
