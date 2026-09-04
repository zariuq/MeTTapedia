; Closed completed-call occurrences for the selected mainline PeTTa reference.
; Each result is `(case-name successful-branch-count)` so the conformance
; driver can compare it with the independently executed Lean judgment.

; The primitive number clause cuts before ordinary annotations, and the
; `%Undefined%` branch is available only when no candidate exists.
(: 3 Grounded)
!(primitive-number-type (if (== (get-type 3) Number) 1 0))
!(primitive-annotation-cut (if (== (get-type 3) Grounded) 1 0))
!(primitive-no-undefined (if (== (get-type 3) %Undefined%) 1 0))
!(unknown-type-fallback
  (if (== (get-type cg_ref_unknown_symbol) %Undefined%) 1 0))

(: cg_ref_exact (-> Number Number))
(= (cg_ref_exact $x) $x)
!(exact-number (size-atom (collapse (cg_ref_exact 3))))
!(wrong-input (size-atom (collapse (cg_ref_exact "bad"))))

(: cg_ref_wrong_result (-> Number Number))
(= (cg_ref_wrong_result $x) "bad")
!(wrong-result (size-atom (collapse (cg_ref_wrong_result 3))))

(: cg_ref_meta (-> Grounded Number))
(= (cg_ref_meta $x) $x)
!(metatype-fallback (size-atom (collapse (cg_ref_meta 3))))

; The ordinary Expression output guard makes this case fail if the Atom input
; is evaluated to 5 instead of being passed as the raw source expression.
(: cg_ref_raw (-> Atom Expression))
(= (cg_ref_raw $x) $x)
!(raw-atom (size-atom (collapse (cg_ref_raw (+ 2 3)))))

(: cg_ref_unchecked (-> %Undefined% Number))
(= (cg_ref_unchecked $x) $x)
!(unchecked-input (size-atom (collapse (cg_ref_unchecked (+ 2 3)))))

(: cg_ref_hole (-> _ Number))
(= (cg_ref_hole $x) $x)
!(hole-input (size-atom (collapse (cg_ref_hole (+ 2 3)))))

; Exact typing and metatyping both prove Grounded for this registered atom.
; The committed soft cut must therefore produce one branch rather than two.
(: cg_ref_dual_atom Grounded)
(= (cg_ref_dual_atom) cg_ref_dual_atom)
(: cg_ref_softcut (-> Grounded Number))
(= (cg_ref_softcut $x) 3)
!(exact-softcut-single
  (size-atom (collapse (cg_ref_softcut cg_ref_dual_atom))))

(: cg_ref_two (-> Number Number))
(: cg_ref_two (-> Grounded Number))
(= (cg_ref_two $x) $x)
!(two-overloads (size-atom (collapse (cg_ref_two 3))))

(: cg_ref_duplicate (-> Number Number))
(: cg_ref_duplicate (-> Number Number))
(= (cg_ref_duplicate $x) $x)
!(duplicate-chain (size-atom (collapse (cg_ref_duplicate 3))))

(: cg_ref_outputs (-> Atom))
(: cg_ref_outputs (-> %Undefined%))
(: cg_ref_outputs (-> _))
(= (cg_ref_outputs) "bad")
!(unchecked-outputs (size-atom (collapse (cg_ref_outputs))))

; The selected reference recompiles existing callers transactionally when an
; arrow declaration is added or removed.
(= (cg_ref_dynamic_target $x) $x)
(= (cg_ref_dynamic_caller $x) (cg_ref_dynamic_target $x))
!(revision-before-add
  (size-atom (collapse (cg_ref_dynamic_caller "bad"))))
!(add-atom &self (: cg_ref_dynamic_target (-> Number Number)))
!(revision-after-add
  (size-atom (collapse (cg_ref_dynamic_caller "bad"))))
!(revision-number-after-add
  (size-atom (collapse (cg_ref_dynamic_caller 3))))
!(remove-atom &self (: cg_ref_dynamic_target (-> Number Number)))
!(revision-after-remove
  (size-atom (collapse (cg_ref_dynamic_caller "bad"))))

; The same closed guard decisions apply in a separately owned program.
!(add-atom &cg_ref_space (: cg_ref_owned (-> Number Number)))
!(add-atom &cg_ref_space (= (cg_ref_owned $x) $x))
!(owned-number
  (size-atom (collapse (eval (cg_ref_owned 3) &cg_ref_space))))
!(owned-wrong
  (size-atom (collapse (eval (cg_ref_owned "bad") &cg_ref_space))))
