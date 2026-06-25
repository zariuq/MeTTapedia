; =============================================================================
; kernel_binding_abtg_replay_v1.metta
;
; ABT Binding Engine v1, client replay oracle.
;
; Imports the shared binding waist directly and proves the public fast path
; (`shift` / `subst` / Args / Cases) agrees with the generic `bind-shift` /
; `bind-subst` traversal on every current term/container shape.  Direct import is
; intentional: LeaTTa does not treat wrapper imports as re-exports, and indexed
; routing is now proven separately by `run_binding_mutation_gate.sh`.
; =============================================================================

!(import! &self kernel_binding_waist_v1)
!(import! &self kernel_binding_decl_v1)

; ---------- replay samples ----------------------------------------------------
(= (bind-sample-app) (App (Lam (Con nat) (Var 1)) (Var 0)))
(= (bind-sample-pi)  (Pi (Con nat) (App (Con vec) (Var 0))))
(= (bind-sample-lam) (Lam (Con nat) (App (Var 0) (Var 1))))
(= (bind-sample-args) (ArgsCons (Var 0) (ArgsCons (Lam (Con nat) (Var 1)) ArgsNil)))
(= (bind-sample-cases) (Cases (Case z (Var 0)) (Cases (Case s (Lam (Con nat) (Var 1))) CasesNil)))
(= (bind-sample-indg)
   (IndG nat (bind-sample-args) (Lam (Con nat) (Con nat))
     (bind-sample-cases) (ArgsCons (Var 0) ArgsNil) (Var 0)))

; Tiny PLFA-style context lookup oracle: de Bruijn indices are only meaningful
; inside a context, and out-of-scope variables reject.
(= (plfa-lookup $i PLCtxNil) (Bad plfa-out-of-scope))
(= (plfa-lookup $i (PLCtxCons $h $t))
   (if (== $i 0)
     $h
     (if (> $i 0) (plfa-lookup (- $i 1) $t) (Bad bad-plfa-index))))

; Atomic and binder capture behaviour, with explicit expected values.
!(assertEqual (bind-shift 1 0 (Var 0)) (Var 1))
!(assertEqual (bind-shift 1 0 (Lam (Con nat) (Var 0))) (Lam (Con nat) (Var 0)))
!(assertEqual (bind-shift 1 0 (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 2)))
!(assertEqual (bind-subst 0 (Var 0) (Lam (Con nat) (Var 1))) (Lam (Con nat) (Var 1)))
!(assertEqual (bind-subst 0 (Con z) (Var 2)) (Var 1))
!(assertEqual (plfa-lookup 0 (PLCtxCons nat PLCtxNil)) nat)
!(assertEqual (plfa-lookup 2 (PLCtxCons nat (PLCtxCons bool PLCtxNil))) (Bad plfa-out-of-scope))

; Replay against the live clauses on each current term shape.
!(assertEqual (bind-shift 1 0 (bind-sample-app)) (shift 1 0 (bind-sample-app)))
!(assertEqual (bind-shift 1 0 (bind-sample-pi))  (shift 1 0 (bind-sample-pi)))
!(assertEqual (bind-shift 1 0 (bind-sample-lam)) (shift 1 0 (bind-sample-lam)))
!(assertEqual (bind-subst 0 (Con z) (bind-sample-app)) (subst 0 (Con z) (bind-sample-app)))
!(assertEqual (bind-subst 0 (Con z) (bind-sample-pi))  (subst 0 (Con z) (bind-sample-pi)))
!(assertEqual (bind-subst 0 (Con z) (bind-sample-lam)) (subst 0 (Con z) (bind-sample-lam)))

; Replay for the non-term containers used by IndG.
!(assertEqual
  (bind-shift-cases 1 0 (bind-sample-cases))
  (Cases (Case z (Var 1)) (Cases (Case s (Lam (Con nat) (Var 2))) CasesNil)))
!(assertEqual (bind-shift-args 1 0 (bind-sample-args)) (shift-args 1 0 (bind-sample-args)))
!(assertEqual (bind-subst-args 0 (Con z) (bind-sample-args)) (subst-args 0 (Con z) (bind-sample-args)))
!(assertEqual (bind-shift-cases 1 0 (bind-sample-cases)) (shift-cases 1 0 (bind-sample-cases)))
!(assertEqual (bind-subst-cases 0 (Con z) (bind-sample-cases)) (subst-cases 0 (Con z) (bind-sample-cases)))

; Whole IndG replay: params, motive, cases, indices, and scrutinee all traverse.
!(assertEqual (bind-shift 1 0 (bind-sample-indg)) (shift 1 0 (bind-sample-indg)))
!(assertEqual (bind-subst 0 (Con z) (bind-sample-indg)) (subst 0 (Con z) (bind-sample-indg)))

; Hosted LanguageDef BindingDecl replay: Pi/Lam/forall/exists/comprehension/
; DISCH-style declarations are table data over the same binding waist.
!(assertEqual (binding-decl-admitted (BindPi domain codomain)) True)
!(assertEqual (binding-decl-admitted (BindPi body body)) False)
!(assertEqual
  (binding-decl-admitted
    (BindFields (BCons (BField body 1) (BCons (BField body 0) BNil))))
  False)
!(assertEqual (binding-decl-depth (BindPi domain codomain) domain) 0)
!(assertEqual (binding-decl-depth (BindPi domain codomain) codomain) 1)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField ty 0) (BCons (BField body 1) BNil)))
    body)
  1)
!(assertEqual (binding-decl-depth (Bind1 forallBody) forallBody) 1)
!(assertEqual (binding-decl-depth (Bind1 existsBody) existsBody) 1)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField predicate 1) (BCons (BField carrier 0) BNil)))
    predicate)
  1)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField left 0) (BCons (BField right 2) BNil)))
    right)
  2)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField left 0) (BCons (BField right 3) BNil)))
    right)
  3)
!(assertEqual
  (binding-decl-depth
    (BindFields (BCons (BField body 1) BNil))
    ty)
  (Bad undeclared-binding-field))
!(assertEqual (binding-decl-depth (Bind1 body) ty) (Bad undeclared-binding-field))
!(assertEqual (binding-shift-under-depth 1 0 2 (Var 1)) (Var 1))
!(assertEqual (binding-shift-under-depth 1 0 3 (Var 2)) (Var 2))
!(assertEqual (binding-shift-under-depth 1 0 3 (Var 3)) (Var 4))
!(assertEqual (binding-subst-under-depth 0 (Con z) 2 (Var 2)) (Con z))
!(assertEqual (binding-subst-under-depth 0 (Var 0) 2 (Var 2)) (Var 2))
!(assertEqual (binding-subst-under-depth 0 (Con z) 3 (Var 3)) (Con z))
!(assertEqual (binding-subst-under-depth 0 (Var 0) 3 (Var 3)) (Var 3))
!(assertEqual (binding-subst-under-depth 0 (Var 1) 4 (Var 4)) (Var 5))

; PLFA-style sigma-law pressure tests, as concrete kernel replays:
; identity at a nested binder boundary and one fusion/commutation witness.
!(assertEqual
  (binding-subst-under-depth 0 (Var 0) 3 (App (Var 3) (Var 2)))
  (App (Var 3) (Var 2)))
!(assertEqual
  (binding-subst-under-depth
    0 (Con z) 3
    (binding-subst-under-depth 0 (Var 0) 3 (Var 3)))
  (binding-subst-under-depth 0 (Con z) 3 (Var 3)))
!(assertEqual
  (binding-shift-under-depth
    1 0 3
    (binding-subst-under-depth 0 (Con z) 3 (Var 2)))
  (binding-subst-under-depth
    0 (Con z) 3
    (binding-shift-under-depth 1 0 3 (Var 2))))
