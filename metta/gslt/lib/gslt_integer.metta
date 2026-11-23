; Exact nonnegative integer division using doubling and subtraction.
; Each recursive call doubles the positive divisor. No floating conversion
; or external constraint solver is used.
(: gslt:integer:divmod (-> Number Number %Undefined%))
(= (gslt:integer:divmod $number $divisor)
   (if (< $number 0) (IntegerDivisionFault NegativeDividend)
     (if (> $divisor 0)
       (gslt:integer:divmod-positive $number $divisor)
       (IntegerDivisionFault NonpositiveDivisor))))

(: gslt:integer:divmod-positive (-> Number Number %Undefined%))
(= (gslt:integer:divmod-positive $number $divisor)
   (if (< $number $divisor) (IntegerDivmod 0 $number)
     (case (gslt:integer:divmod-positive $number (+ $divisor $divisor))
       (((IntegerDivmod $quotient $remainder)
         (let $twice (+ $quotient $quotient)
           (if (< $remainder $divisor)
             (IntegerDivmod $twice $remainder)
             (IntegerDivmod (+ $twice 1) (- $remainder $divisor)))))))))
