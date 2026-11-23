; Controls of equation_kernel_primitives_v0.metta. Load after
; equation_kernel_v0.metta and equation_kernel_primitives_v0.metta.
(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))

(= (pr:inc $a) (ek:expr (ek:cons (ek:sym "inc") (ek:cons $a ek:nil))))
(= (pr:succ $a) (ek:expr (ek:cons (ek:sym "S") (ek:cons $a ek:nil))))
(= (pr:pair $a $b) (ek:expr (ek:cons (ek:sym "pair") (ek:cons $a (ek:cons $b ek:nil)))))
(= (pr:program)
   (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (pr:inc (ek:var "x")) (ek:cons (pr:succ (ek:var "x")) ek:nil)))) ek:nil))
(= (pr:cite) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (pr:inc (ek:var "x")) (ek:cons (pr:succ (ek:var "x")) ek:nil)))) 0))

!(ek:control ctl-match-binds
   (ek:match (pr:inc (ek:var "x")) (pr:inc (ek:sym "Z")) ek:nil)
   (ek:some (ek:cons (ek:bind "x" (ek:sym "Z")) ek:nil)))
!(ek:control ctl-match-repeated-variable
   (ek:match (pr:pair (ek:var "x") (ek:var "x")) (pr:pair (ek:sym "Z") (ek:sym "Z")) ek:nil)
   (ek:some (ek:cons (ek:bind "x" (ek:sym "Z")) ek:nil)))
!(ek:control ctl-match-refuses-unequal-repeat
   (ek:match (pr:pair (ek:var "x") (ek:var "x")) (pr:pair (ek:sym "Z") (ek:sym "W")) ek:nil)
   ek:none)
!(ek:control ctl-match-target-variable-is-constant
   (ek:match (pr:inc (ek:sym "A")) (pr:inc (ek:var "z")) ek:nil)
   ek:none)
!(ek:control ctl-mstep-computes-bindings
   (ek:mstep-claim (pr:program) (ek:some (ek:claim (pr:inc (pr:inc (ek:sym "Z"))) (pr:inc (pr:inc (ek:sym "Z")))))
                   (pr:cite) (ek:cons 1 ek:nil) ek:nil)
   (ek:some (ek:claim (pr:inc (pr:inc (ek:sym "Z"))) (pr:inc (pr:succ (ek:sym "Z"))))))
!(ek:control ctl-mstep-refuses-forged-extra
   (ek:mstep-claim (pr:program) (ek:some (ek:claim (pr:succ (ek:sym "Z")) (pr:succ (ek:sym "Z"))))
                   (pr:cite) ek:nil ek:nil)
   ek:none)
!(ek:control ctl-intern-equal-atoms (== (ek:intern (pr:inc (ek:sym "Z"))) (ek:intern (pr:inc (ek:sym "Z")))) True)
!(ek:control ctl-intern-distinct-atoms (== (ek:intern (pr:inc (ek:sym "Z"))) (ek:intern (pr:succ (ek:sym "Z")))) False)
!(ek:control ctl-intern-reads-back (ek:interned (ek:intern (pr:succ (ek:sym "Z")))) (ek:some (pr:succ (ek:sym "Z"))))
!(bind! &pr-copies (new-space))
!(add-atom &pr-copies (eq coin heads))
!(add-atom &pr-copies (eq coin heads))
!(add-atom &pr-copies (eq coin tails))
!(ek:control ctl-stored-copies-heads (ek:stored-copies &pr-copies (eq coin heads)) 2)
!(ek:control ctl-stored-copies-tails (ek:stored-copies &pr-copies (eq coin tails)) 1)
!(ek:control ctl-fresh-var-first (ek:fresh-var "y" 0 (ek:cons "y" ek:nil)) (ek:var (ek:name "y" 0)))
!(ek:control ctl-fresh-var-skips (ek:fresh-var "y" 0 (ek:cons (ek:name "y" 0) (ek:cons (ek:name "y" 1) ek:nil))) (ek:var (ek:name "y" 2)))
