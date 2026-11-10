; Generate checked arithmetic branch evidence and a mismatched witness control.
; Load families, terms, generate.metta and interpret.metta before this file.
!(import! &self fs)
!(import! &self system)

(= (divisor-proposition $d $n)
   (app Exists ((app Nat ())
     (lam witness (app Nat ())
       (app Eq ((app Nat ()) (num $n) (app Nat.mul ((num $d) (var witness)))))))))
(= (divisor-control $d $n $expected)
   (let* (($P (divisor-proposition $d $n)) ($yes (decide-prop $P)))
     (if (== $yes $expected)
         (format-args "Theorem Test_divides_{}_{} : 0 {}e {}.\nexact {}.\nQed.\n"
           ($d $n (if $yes ":" "/:") (render $P ()) (if $yes (prove-prop $P) (refute-prop $P))))
         (let $_error (system:write stderr "numeral control: incorrect divisibility decision\n")
           (system:exit 1)))))

!(let ($positive $negative) (system:args)
   (let $_positive
     (fs:write $positive (join "\n"
       (map-atom ((2 360 True) (3 91 False) (3 99 True) (0 0 True) (0 8 False)
                  (137 274 True) (137 275 False) (1 100000 True)) $triple
         (let ($d $n $expected) $triple (divisor-control $d $n $expected)))))
     (fs:write $negative
       (format-args "Opaque Lean_Exists_Prop Lean_Eq_Prop LeanNum Lean_Nat_mul.\nTheorem Test_wrong_divisibility_witness : 0 :e {}.\nexact {}.\nQed.\n"
         ((render (divisor-proposition 2 5) ()) (prove-prop (divisor-proposition 2 4)))))))
