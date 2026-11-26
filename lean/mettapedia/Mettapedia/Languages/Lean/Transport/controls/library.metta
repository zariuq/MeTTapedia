; Controls for the library: matching a fragment at a proof node, the citation it gives, the lemma
; written for Lean, and exact rewriting.  Each prints (control NAME ok/FAILED).
(= (ctl $c_name $c_got $c_want) (println! (control $c_name (if (== $c_got $c_want) ok (FAILED (got $c_got) (want $c_want))))))

; a fragment's holes take what stands there, in order; another head does not fit
!(ctl match-holes
      (lib:mt (pcite f ((hole term) (app c ()))) (pcite f ((app a ()) (app c ()))) 0 () (ma () () ()))
      (ma ((hv term (app a ()) () none)) () ()))
!(ctl match-other-head (lib:mt (pcite f ((hole term))) (pcite g ((app a ()))) 0 () (ma () () ())) Fail)
; a hole of a proof's kind does not take a term
!(ctl match-kind (lib:mt (pcite f ((hole proof))) (pcite f ((app a ()))) 0 () (ma () () ())) Fail)
; under a binder of the fragment, a hole keeps that binder (its value is a function of it)
!(ctl match-under-binder
      (lib:mt (plam _ (app Nat ()) (pcite f ((hole term)))) (plam x (app Nat ()) (pcite f ((dbv 0)))) 0 () (ma () () ()))
      (ma ((hv term (dbv 0) ((bd plam x (app Nat ()))) none)) () ()))
; a reference outside the fragment is a parameter: one value everywhere, never a binder of the fragment
!(ctl free-consistent
      (lib:mt (pcite f ((dbv 0) (dbv 0))) (pcite f ((app a ()) (app a ()))) 0 () (ma () () ()))
      (ma () ((fv 0 (app a ()))) ()))
!(ctl free-differs (lib:mt (pcite f ((dbv 0) (dbv 0))) (pcite f ((app a ()) (app b ()))) 0 () (ma () () ())) Fail)
!(ctl free-captures
      (lib:mt (plam _ (app Nat ()) (pcite f ((dbv 1)))) (plam x (app Nat ()) (pcite f ((dbv 0)))) 0 () (ma () () ()))
      Fail)

; the citation: a hole under a binder is passed as a function of it
(LibLemma lemma_ctl (plam _ (app Nat ()) (pcite f ((hole term)))))
!(ctl citation-abstracts
      (lib:citation lemma_ctl (ma ((hv term (app g ((dbv 0))) ((bd plam x (app Nat ()))) none)) () ()))
      (pcite lemma_ctl ((lam x (app Nat ()) (app g ((dbv 0)))))))
; the lemma as Lean is given it: the hole a parameter applied to the bound variable
!(ctl emit-higher-order
      (let $e (lib:emit lemma_ctl (plam _ (app Nat ()) (pcite f ((hole term)))))
        (collapse (match &self (MinedLemma lemma_ctl $l $v) ($l $v))))
      ((() (plam m_2 (pi v_1 (app Nat ()) (proof)) (plam v_1 (app Nat ()) (pcite f ((apv (var m_2) ((var v_1))))))))))
; an outside reference applied to arguments is a function of that many arguments
!(ctl emit-free-applied
      (let $e (lib:emit lemma_fa (pcite f ((dbh 0 ((app a ()))))))
        (collapse (match &self (MinedLemma lemma_fa $l $v) ($l $v))))
      ((() (plam f_1 (pi a_1 (proof) (proof)) (pcite f ((phyp f_1 ((app a ())))))))))
; a binder's type that names an outside reference: the reference is a parameter before the hole
; whose type names it
!(ctl emit-free-first
      (let $e (lib:emit lemma_ff (plam _ (dbv 0) (hole term)))
        (collapse (match &self (MinedLemma lemma_ff $l $v) ($l $v))))
      ((() (plam f_2 (proof) (plam m_3 (pi v_1 (var f_2) (proof)) (plam v_1 (var f_2) (apv (var m_3) ((var v_1)))))))))
; a level hole is a universe parameter
!(ctl emit-level
      (let $e (lib:emit lemma_lvl (pcite f ((level (hole level)) (hole term))))
        (collapse (match &self (MinedLemma lemma_lvl $l $v) ($l $v))))
      (((u_1) (plam m_2 (proof) (pcite f ((level (lvl u_1)) (var m_2)))))))

; exact savings: a citation's two nodes and a level argument per universe; a binder above a hole
; costs its abstraction
!(ctl saving-plain (lib:saving (pcite f ((app a ()) (app b ()) (hole term))) 5) 3)
!(ctl saving-binder (lib:saving (plam _ (sort (lvl l_u)) (hole proof)) 4) 0)

; exact rewriting cites where it is smaller and leaves a proof where it is not
!(lib:add-lemma lemma_big (pcite big ((app a ((app b ((app c ()))))) (hole term))))
!(ctl rewrite-cites
      (let (pr $s $r) (lib:best (pcite big ((app a ((app b ((app c ()))))) (app d ())))) $r)
      (pcite lemma_big ((app d ()))))
!(ctl rewrite-leaves (let (pr $s $r) (lib:best (pcite small ((app d ())))) $r) (pcite small ((app d ()))))

; the decision: a fragment with many expected uses becomes a lemma, one seen once does not
(LibPosterior 0.5 10)
(LibCandidate "1111111111aaaa" (pcite f1 ((app a ((app b ((app c ()))))) (hole term))) 7 30 1.0)
(LibCandidate "2222222222bbbb" (pcite f2 ((app a ((app b ((app c ()))))) (hole term))) 7 1 0.001)
!(let $x (lib:choose 100)
   (let $ns (collapse (match &self (LibLemma $n $t) $n))
     (ctl choose-by-utility (pr (term:member-of lemma_1111111111 $ns) (term:member-of lemma_2222222222 $ns)) (pr True False))))

; a refused lemma stated again from its occurrences: two holes with one value in every occurrence are
; one parameter; a hole with one closed value is written in; a hole whose values never reach the
; fragment's binder is a parameter of no binder; and a hole that does reach it stays a function of it
(TransportProof ctl_t1 (pcite rf ((app a ()) (app a ()) (app c ()))))
(TransportProof ctl_t2 (pcite rf ((app b ()) (app b ()) (app c ()))))
(TransportProof ctl_t3 (plam x (app Nat ()) (pcite rg ((app a ()) (dbv 0)))))
(TransportProof ctl_t4 (plam x (app Nat ()) (pcite rg ((app b ()) (app s ((dbv 0)))))))
!(lib:add-lemma lemma_rf (pcite rf ((hole term) (hole term) (hole term))))
!(lib:add-lemma lemma_rg (plam _ (app Nat ()) (pcite rg ((hole term) (hole term)))))
(MinedRefused lemma_rf)
(MinedRefused lemma_rg)
!(lib:refine-refused (ctl_t1 ctl_t2 ctl_t3 ctl_t4))
!(ctl refine-shares-and-fills (collapse (match &self (LibLemma lemma_rfr $p) $p))
      ((pcite rf ((hole term 1 none) (hole term 1 none) (app c ())))))
!(ctl refine-strengthens (collapse (match &self (LibLemma lemma_rgr $p) $p))
      ((plam _ (app Nat ()) (pcite rg ((hole term 1 none) (hole term 2 all))))))
; the stated-again lemma: one parameter for the shared holes, cited where both hold one value only
!(ctl refine-emits
      (let $e (lib:emit lemma_rfr (pcite rf ((hole term 1 none) (hole term 1 none) (app c ()))))
        (collapse (match &self (MinedLemma lemma_rfr $l $v) $v)))
      ((plam s_1 (proof) (pcite rf ((var s_1) (var s_1) (app c ()))))))
!(ctl refine-cites (let (pr $s $r) (lib:best (pcite rf ((app d ()) (app d ()) (app c ())))) $r) (pcite lemma_rfr ((app d ()))))
!(ctl refine-shared-mismatch (lib:mt (pcite rf ((hole term 1 none) (hole term 1 none) (app c ()))) (pcite rf ((app d ()) (app e ()) (app c ()))) 0 () (ma () () ())) Fail)
