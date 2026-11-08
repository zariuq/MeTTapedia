; Workloads for the scaling checks: Egal documents whose checking work should
; grow linearly with their size N.
;
;   cetta --lang petta scaling.metta KIND N OUT
;
;   decls     N independent definitions, each with a theorem about it
;   notation  N infix notations, each defined and used in a theorem
;   shared    one lemma, cited N times in the proof of one theorem
;
; N = 0 gives the empty document: the cost of reading the signature alone,
; which the checks subtract before comparing sizes.

!(import! &self fs)
!(import! &self str)
!(import! &self system)

(= (range-from $i $n) (if (>= $i $n) () (cons-atom $i (range-from (+ $i 1) $n))))

(= (decl-text $k)
   (format-args "Definition scd{} : set -> set := fun x => x.
Theorem sct{} : forall x, scd{} x = x.
let x. reflexivity.
Qed.
" ($k $k $k)))

(= (notation-text $k)
   (format-args "Definition scf{} : set -> set -> set := fun x y => x.
Infix scop{} 500 left := scf{}.
Theorem scn{} : forall x y, x scop{} y = x.
let x y. reflexivity.
Qed.
" ($k $k $k $k $k)))

(= (shared-claim $k)
   (format-args "claim C{}: x = x.
{} exact scl x. {}
" ($k "{" "}")))
(= (shared-text $n)
   (if (== $n 0) ""
       (format-args "Theorem scl : forall x, x = x.
let x. reflexivity.
Qed.
Theorem scs : forall x, x = x.
let x.
{}exact C{}.
Qed.
" ((str:join "" (map-atom (range-from 0 $n) $k (shared-claim $k))) (- $n 1)))))

(= (workload $kind $n)
   (case $kind
     ((decls (str:join "" (map-atom (range-from 0 $n) $k (decl-text $k))))
      (notation (str:join "" (map-atom (range-from 0 $n) $k (notation-text $k))))
      (shared (shared-text $n)))))

; The size arrives as a symbol on the command line.
!(let ($kind $size $out) (system:args)
   (fs:write $out (workload $kind (str:string->number (str:symbol->string $size)))))
