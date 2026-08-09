; ============================================================================
; lf_recognizer_v0.metta
;
; The self-contained runnable twin of the verified Lean LF recognizer
; (Mettapedia/GSLT/LanguageDef/LF.lean).  No imports: every rule is local, so the
; recognizer runs identically on CeTTa and on the Lean-verified LeaTTa engine --
; the invariant the correspondence theorem `recognize ts = <lf-recognize> ts`
; rests on.  The kernel-check wiring lives in the bridge that imports this file.
;
; Source anchors: LF concrete syntax and lambda-Pi terms are the HHP/Dedukti
; logical-framework vocabulary; arrow lowers to non-dependent Pi by the Dedukti
; convention.  Name resolution lowers binders to de Bruijn indices using the
; same binding sources cross-referenced by the BIND-* rows.
;
; Implementation notes, not source claims: total fuel, fail-closed parse errors,
; and a finite recursive-descent grammar for the covered LF syntax.
;
; A total, fail-closed recursive-descent recognizer for the standard-LF (Lambdapi)
; syntax, lowering a token stream to the kernel's de Bruijn AST
; (Con / Var / Lam / Pi / App / Srt) with named→de-Bruijn scope resolution.
;
; Concrete grammar (stratified; precedence is structural):
;   Term  → Pi | Lam | Arrow
;   Pi    → Π  id : App . Term
;   Lam   → λ id : App . Term
;   Arrow → App → Term | App        (arrow = non-dependent Pi: pi a (lf-shift b))
;   App   → App Atom | Atom          (left associative)
;   Atom  → ( Term ) | id | Type
; Tokens: Π  λ  →  :  .  LP  RP  Type  (Lex lf-id <name>)
; ============================================================================

; ---------- de Bruijn shift (mirrors Lean `LF.shift`, clause-for-clause) -----
; lift every free variable index >= c by one; binders raise the cutoff.
(= (lf-shift $c (Var $k)) (if (< $k $c) (Var $k) (Var (+ $k 1))))
(= (lf-shift $c (Srt $s)) (Srt $s))
(= (lf-shift $c (Con $x)) (Con $x))
(= (lf-shift $c (Pi $A $B)) (Pi (lf-shift $c $A) (lf-shift (+ $c 1) $B)))
(= (lf-shift $c (Lam $A $b)) (Lam (lf-shift $c $A) (lf-shift (+ $c 1) $b)))
(= (lf-shift $c (App $f $a)) (App (lf-shift $c $f) (lf-shift $c $a)))

; ---------- name context: named identifier → de Bruijn index ---------------
; head of ctx = innermost binder.  (Idx k) for a bound name, NF for free.
(= (lf-ctxidx Nil $s) NF)
(= (lf-ctxidx (Cons $h $t) $s)
   (if (== $h $s)
       (Idx 0)
       (case (lf-ctxidx $t $s)
         ((NF NF)
          ((Idx $k) (Idx (+ $k 1)))))))

; bound name → (Var i), free name → (Con name)
(= (lf-resolve $ctx $s)
   (case (lf-ctxidx $ctx $s)
     (((Idx $k) (Var $k))
      (NF (Con $s)))))

; ---------- recursive-descent recognizer ------------------------------------
; results: (P term rest-tokens) on success, (PErr reason) on failure.
; `$f` is fuel (a structural bound); every recursive call consumes it.

; Term → Pi | Lam | Arrow
(= (lf-term $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case $toks
         (((Cons Π (Cons (Lex lf-id $x) (Cons : $rest)))
            (case (lf-app (- $f 1) $ctx $rest)
              (((P $A (Cons . $r2))
                 (case (lf-term (- $f 1) (Cons $x $ctx) $r2)
                   (((P $B $r3) (P (Pi $A $B) $r3))
                    ($e $e))))
               ($_ (PErr pi-malformed)))))
          ((Cons λ (Cons (Lex lf-id $x) (Cons : $rest)))
            (case (lf-app (- $f 1) $ctx $rest)
              (((P $A (Cons . $r2))
                 (case (lf-term (- $f 1) (Cons $x $ctx) $r2)
                   (((P $b $r3) (P (Lam $A $b) $r3))
                    ($e $e))))
               ($_ (PErr lam-malformed)))))
          ($_ (lf-arrow $f $ctx $toks))))))

; Arrow → App → Term | App     (A → B lowers to Pi A (lf-shift 0 B))
(= (lf-arrow $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (lf-app (- $f 1) $ctx $toks)
         (((P $a (Cons → $rest))
            (case (lf-term (- $f 1) $ctx $rest)
              (((P $b $r2) (P (Pi $a (lf-shift 0 $b)) $r2))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

; App → App Atom | Atom     (one atom, then left-fold trailing atoms)
(= (lf-app $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (lf-atom (- $f 1) $ctx $toks)
         (((P $a0 $r0) (lf-appmore (- $f 1) $ctx $a0 $r0))
          ($e $e)))))

(= (lf-appmore $f $ctx $acc $toks)
   (if (<= $f 0)
       (P $acc $toks)
       (case (lf-atom (- $f 1) $ctx $toks)
         (((P $a $rest) (lf-appmore (- $f 1) $ctx (App $acc $a) $rest))
          ($_ (P $acc $toks))))))

; Atom → ( Term ) | Type | id
(= (lf-atom $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case $toks
         (((Cons LP $rest)
            (case (lf-term (- $f 1) $ctx $rest)
              (((P $t (Cons RP $r2)) (P $t $r2))
               ($_ (PErr paren-malformed)))))
          ((Cons Type $rest) (P (Srt type) $rest))
          ((Cons (Lex lf-id $s) $rest) (P (lf-resolve $ctx $s) $rest))
          ($_ (PErr atom-expected))))))

; ---------- top-level recognizer: closed term, all tokens consumed ----------
(= (lf-recognize $toks)
   (case (lf-term 64 Nil $toks)
     (((P $t Nil) (Ok $t))
      ((P $t $rest) (Err (extra-tokens $rest)))
      ((PErr $e) (Err $e))
      ($_ (Err recognize-failed)))))

; ---------- example source token streams -----------------------------------
(= (tk-rfl-z) (Cons (Lex lf-id rfl) (Cons (Lex lf-id z) Nil)))
(= (tk-eqn-z-z)
   (Cons (Lex lf-id eqn) (Cons (Lex lf-id z) (Cons (Lex lf-id z) Nil))))
(= (tk-eqn-z-sz)
   (Cons (Lex lf-id eqn) (Cons (Lex lf-id z)
     (Cons LP (Cons (Lex lf-id s) (Cons (Lex lf-id z) (Cons RP Nil)))))))
(= (tk-id-nat)
   (Cons λ (Cons (Lex lf-id x) (Cons : (Cons (Lex lf-id nat)
     (Cons . (Cons (Lex lf-id x) Nil)))))))
(= (tk-nat-arr-nat)
   (Cons (Lex lf-id nat) (Cons → (Cons (Lex lf-id nat) Nil))))
(= (tk-idapp-z)
   (Cons LP (Cons λ (Cons (Lex lf-id x) (Cons : (Cons (Lex lf-id nat)
     (Cons . (Cons (Lex lf-id x) (Cons RP (Cons (Lex lf-id z) Nil))))))))))
(= (tk-pi-a-arr)
   (Cons Π (Cons (Lex lf-id A) (Cons : (Cons Type (Cons .
     (Cons LP (Cons (Lex lf-id A) (Cons → (Cons (Lex lf-id A) (Cons RP Nil)))))))))))
(= (tk-malformed) (Cons LP (Cons . Nil)))

; ---------- recognizer unit checks (identical result on CeTTa and LeaTTa) ----
!(assertEqual (lf-recognize (tk-rfl-z)) (Ok (App (Con rfl) (Con z))))
!(assertEqual (lf-recognize (tk-eqn-z-z))
   (Ok (App (App (Con eqn) (Con z)) (Con z))))
!(assertEqual (lf-recognize (tk-eqn-z-sz))
   (Ok (App (App (Con eqn) (Con z)) (App (Con s) (Con z)))))
!(assertEqual (lf-recognize (tk-id-nat))
   (Ok (Lam (Con nat) (Var 0))))
!(assertEqual (lf-recognize (tk-nat-arr-nat))
   (Ok (Pi (Con nat) (Con nat))))
!(assertEqual (lf-recognize (tk-idapp-z))
   (Ok (App (Lam (Con nat) (Var 0)) (Con z))))
; Π A : Type . (A → A)  ==  Pi (Srt type) (Pi (Var 0) (lf-shift 0 (Var 0)))
;                          ==  Pi (Srt type) (Pi (Var 0) (Var 1))
!(assertEqual (lf-recognize (tk-pi-a-arr))
   (Ok (Pi (Srt type) (Pi (Var 0) (Var 1)))))
; a parse failure is reported, not silently dropped
!(assertEqual (lf-recognize (tk-malformed)) (Err paren-malformed))
