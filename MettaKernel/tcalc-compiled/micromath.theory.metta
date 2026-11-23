; Micromath (M. Olšák) as a transform theory, in the form tcalc's flat path compiles:
; one board constructor EQ whose four fields are names; a theorem (EQ out f x y) says
; out(a,b) = f(x(a,b), y(a,b)). Names 0 and 1 are the projections X and Y.

(= (theory-prefix) mm)
(= (theory-header) "micromath_tcalc.h")
(= (theory-leaf-header) "micromath_leaf.h")
(= (theory-table) MmTable)
(= (theory-body) MmBody)
(= (theory-board) EQ)
(= (theory-fields) (out f x y))
(= (theory-names) (X Y))
(= (theory-max-slot) 16777216)

; Rules: (rule name (kept premises) conclusion). Holes are the remaining symbols.
(= (theory-rules)
   ((rule proj1 () (EQ x X x a))
    (rule proj2 () (EQ a Y x a))
    (rule refl () (EQ a a X Y))
    (rule sub1 ((EQ x t u w) (EQ u1 u a b) (EQ w1 w a b) (EQ x1 x a b)) (EQ x1 t u1 w1))
    (rule sub2 ((EQ x t u w) (EQ u1 u a b) (EQ w1 w a b) (EQ x1 t u1 w1)) (EQ x1 x a b))
    (rule def () (EQ x1 t u w))))

; The slot interface: entry points and how their arguments reach the rule.
;   (keeps rule)               the arguments name the slots of the kept premises, then the destination
;   (inputs rule holes)        the arguments give these holes, then the destination
;   (fresh rule hole holes)    as inputs, and the hole is a new name defined from existing ones
(= (theory-entries)
   ((entry mm_proj1 (inputs proj1 (x a)))
    (entry mm_proj2 (inputs proj2 (x a)))
    (entry mm_refl (inputs refl (a)))
    (entry mm_sub1 (keeps sub1))
    (entry mm_sub2 (keeps sub2))
    (entry mm_new_def (fresh def x1 (t u w)))))

; An unset slot reads as this rule's conclusion at these holes.
(= (theory-unset) (proj1 ((x X) (a X))))
