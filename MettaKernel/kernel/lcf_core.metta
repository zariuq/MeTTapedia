; ============================================================================
; LCFCore -- a tiny LCF/HOL proof kernel as a MeTTa GSLT (runnable in CeTTa)
;
; A theorem is a sequent  (Thm <hyps> <concl>)  with hyps an HCons/HNil list of
; Prop.  The primitive inference rules below are the ONLY producers of (Thm ...).
; (Names are h-/tm- prefixed and the list uses HCons/HNil so nothing collides with
;  CeTTa/--he stdlib builtins such as Cons/Nil/union, which evaluate nondetermin-
;  istically and would break the kernel's required determinism.)
;
; GSLT signature (documentation; the runnable kernel stays untyped -- a separate
; Lean spec carries the typed version):
;   Ty   ::= bool | num
;   Tm   ::= (Var name Ty) | (Cst name Ty) | (App Tm Tm) | (Lam name Ty Tm)
;   Prop ::= (PVar name) | (Eq Tm Tm) | (Imp Prop Prop)
;   hyps ::= HNil | (HCons Prop hyps)        -- a list (set-dedup is a refinement)
;   Thm  ::= (Thm hyps Prop)                 -- the sequent  hyps |- concl
;
; TRUST MODEL (honest): MeTTa is untyped, so a (Thm ...) literal could be FORGED by
; writing it directly. Soundness rests on (a) only these rule equations producing
; Thm, and (b) each rule being sound -- which is why the trusted core is tiny +
; audited (a separate Lean reference spec will PROVE the rules sound).
;
; Run:  /home/aimama/aihub/hyperon/CeTTa/cetta lcf_core.metta
; ============================================================================

; ---- hypothesis lists (HCons/HNil of Prop) ---------------------------------
(= (hyp-remove $x HNil) HNil)
(= (hyp-remove $x (HCons $y $ys)) (if (== $x $y) (hyp-remove $x $ys) (HCons $y (hyp-remove $x $ys))))
(= (hyp-union HNil $ys) $ys)
(= (hyp-union (HCons $x $xs) $ys) (HCons $x (hyp-union $xs $ys)))

; ---- capture-permitting substitution (sound for closed u; SF-style) --------
(= (tm-subst $x $u (Var $y $T)) (if (== $x $y) $u (Var $y $T)))
(= (tm-subst $x $u (Cst $c $T)) (Cst $c $T))
(= (tm-subst $x $u (App $f $a)) (App (tm-subst $x $u $f) (tm-subst $x $u $a)))
(= (tm-subst $x $u (Lam $y $T $b)) (if (== $x $y) (Lam $y $T $b) (Lam $y $T (tm-subst $x $u $b))))

; ---- the TRUSTED kernel: the primitive inference rules ---------------------
(= (refl $t) (Thm HNil (Eq $t $t)))                            ; REFL  |- t=t
(= (assume $p) (Thm (HCons $p HNil) $p))                       ; ASSUME  p|-p
(= (disch $p (Thm $G $q)) (Thm (hyp-remove $p $G) (Imp $p $q))); DISCH
(= (mp (Thm $G1 (Imp $p $q)) (Thm $G2 $p2))                    ; MP (antecedent must match)
   (if (== $p $p2) (Thm (hyp-union $G1 $G2) $q) (mp-mismatch $p $p2)))
(= (beta_conv (App (Lam $x $T $b) $u))                         ; BETA_CONV
   (Thm HNil (Eq (App (Lam $x $T $b) $u) (tm-subst $x $u $b))))
(= (trans (Thm $G1 (Eq $a $b)) (Thm $G2 (Eq $b2 $c)))          ; TRANS (middle must match)
   (if (== $b $b2) (Thm (hyp-union $G1 $G2) (Eq $a $c)) (trans-mismatch $b $b2)))

; ============================================================================
; HOL06 curriculum derivations, reproduced + self-checked
; ============================================================================
!(assertEqual (refl (Var x num)) (Thm HNil (Eq (Var x num) (Var x num))))
!(assertEqual (disch (PVar p) (assume (PVar p))) (Thm HNil (Imp (PVar p) (PVar p))))
!(assertEqual
   (beta_conv (App (Lam x num (Var x num)) (Var y num)))
   (Thm HNil (Eq (App (Lam x num (Var x num)) (Var y num)) (Var y num))))
!(assertEqual
   (mp (assume (Imp (PVar p) (PVar q))) (assume (PVar p)))
   (Thm (HCons (Imp (PVar p) (PVar q)) (HCons (PVar p) HNil)) (PVar q)))
!(assertEqual
   (trans (refl (Var a num)) (refl (Var a num)))
   (Thm HNil (Eq (Var a num) (Var a num))))

; ============================================================================
; TRUST BOUNDARY: an invalid step does NOT mint a theorem
; ============================================================================
!(assertEqual
   (mp (assume (Imp (PVar p) (PVar q))) (assume (PVar r)))
   (mp-mismatch (PVar p) (PVar r)))

; ============================================================================
; DEMO: the minted theorems (illustrative -- prints the actual Thm objects)
; ============================================================================
!(refl (Var x num))                                          ; |- x = x
!(disch (PVar p) (assume (PVar p)))                          ; |- p => p
!(beta_conv (App (Lam x num (Var x num)) (Var y num)))       ; |- (\x.x) y = y
!(mp (assume (Imp (PVar p) (PVar q))) (assume (PVar r)))     ; r =/= p : NOT a theorem
