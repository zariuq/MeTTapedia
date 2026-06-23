; ============================================================================
; LCFCore (PeTTa edition) -- a tiny LCF/HOL proof kernel as a MeTTa GSLT.
; Identical logic to lcf_core.metta, but every helper is given an underscore
; m_-prefixed name (m_union/m_remove/m_subst) so it does NOT collide with a
; SWI-Prolog builtin predicate -- in particular `union` collides with the static
; lists:union/3, which aborts PeTTa.  (Hyphens are Prolog operators, so the CeTTa
; names hyp-union/tm-subst cannot be reused here either.)
;
; A theorem is a sequent  (Thm <hyps> <concl>)  with hyps an HCons/HNil list of
; Prop.  The primitive inference rules below are the ONLY producers of (Thm ...).
;
; TRUST MODEL (honest): MeTTa is untyped, so a (Thm ...) literal could be FORGED.
; Soundness rests on (a) only these rule equations producing Thm, and (b) each
; rule being sound -- which is why the trusted core is tiny + audited.
;
; Run:  cd /home/aimama/aihub/hyperon/PeTTa && ./run.sh \
;         /home/aimama/aihub/Mettapedia/MettaKernel/kernel/lcf_core_petta.metta --silent
; ============================================================================

; ---- hypothesis lists (HCons/HNil of Prop) ---------------------------------
(= (m_remove $x HNil) HNil)
(= (m_remove $x (HCons $y $ys)) (if (== $x $y) (m_remove $x $ys) (HCons $y (m_remove $x $ys))))
(= (m_union HNil $ys) $ys)
(= (m_union (HCons $x $xs) $ys) (HCons $x (m_union $xs $ys)))

; ---- capture-permitting substitution (sound for closed u; SF-style) --------
(= (m_subst $x $u (Var $y $T)) (if (== $x $y) $u (Var $y $T)))
(= (m_subst $x $u (Cst $c $T)) (Cst $c $T))
(= (m_subst $x $u (App $f $a)) (App (m_subst $x $u $f) (m_subst $x $u $a)))
(= (m_subst $x $u (Lam $y $T $b)) (if (== $x $y) (Lam $y $T $b) (Lam $y $T (m_subst $x $u $b))))

; ---- the TRUSTED kernel: the primitive inference rules ---------------------
(= (refl $t) (Thm HNil (Eq $t $t)))
(= (assume $p) (Thm (HCons $p HNil) $p))
(= (disch $p (Thm $G $q)) (Thm (m_remove $p $G) (Imp $p $q)))
(= (mp (Thm $G1 (Imp $p $q)) (Thm $G2 $p2))
   (if (== $p $p2) (Thm (m_union $G1 $G2) $q) (mp-mismatch $p $p2)))
(= (beta_conv (App (Lam $x $T $b) $u))
   (Thm HNil (Eq (App (Lam $x $T $b) $u) (m_subst $x $u $b))))
(= (trans (Thm $G1 (Eq $a $b)) (Thm $G2 (Eq $b2 $c)))
   (if (== $b $b2) (Thm (m_union $G1 $G2) (Eq $a $c)) (trans-mismatch $b $b2)))

; ---- HOL06 derivations, self-checked ---------------------------------------
!(test (refl (Var x num)) (Thm HNil (Eq (Var x num) (Var x num))))
!(test (disch (PVar p) (assume (PVar p))) (Thm HNil (Imp (PVar p) (PVar p))))
!(test
   (beta_conv (App (Lam x num (Var x num)) (Var y num)))
   (Thm HNil (Eq (App (Lam x num (Var x num)) (Var y num)) (Var y num))))
!(test
   (mp (assume (Imp (PVar p) (PVar q))) (assume (PVar p)))
   (Thm (HCons (Imp (PVar p) (PVar q)) (HCons (PVar p) HNil)) (PVar q)))
!(test
   (trans (refl (Var a num)) (refl (Var a num)))
   (Thm HNil (Eq (Var a num) (Var a num))))

; ---- trust boundary: an invalid step does NOT mint a theorem ---------------
!(test
   (mp (assume (Imp (PVar p) (PVar q))) (assume (PVar r)))
   (mp-mismatch (PVar p) (PVar r)))
