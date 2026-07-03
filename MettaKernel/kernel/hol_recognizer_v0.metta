; ============================================================================
; hol_recognizer_v0.metta
;
; Runnable twin of the Lean HOL/STT `hol-core-g` recognizer
; (Mettapedia/GSLT/LanguageDef/HOL.lean).
;
; Source anchors: HOL/STT terms are hosted as LF signatures in the HHP style and
; follow the Assaf-Burel HOL-to-Dedukti translation boundary: surface parsing
; lowers to LF constants/terms, then the LF kernel checks the result.  Binding
; and lambda lowering cross-reference the BIND-* rows.
;
; Implementation notes, not source claims: fuel-bounded finite grammar,
; fail-closed parser/elaborator, and covered HOL-core-g connectives only.
;
; A total, fail-closed, fuel-bounded recursive-descent recognizer for the
; `hol-core-g` surface grammar:
;   Term -> Bind | Iff
;   Bind -> ∀ id . Term | ∃ id . Term | λ id . Term
;   Iff  -> Imp ⇔ Iff | Imp
;   Imp  -> Disj ⇒ Imp | Disj
;   Disj -> Conj ∨ Disj | Conj
;   Conj -> Eq ∧ Conj | Eq
;   Eq   -> Neg = Eq | Neg
;   Neg  -> ¬ Neg | App
;   App  -> App Atom | Atom
;   Atom -> LP Term RP | (Lex hol-id name)
;
; Output is the LF kernel AST shape (Con / Var / Lam / App) used by
; `kernel_signature_lf_v0.metta`.  The implication connective lowers to the
; checked HOL fragment's `imp` constant; other HOL connectives lower to named
; constants that the imported kernel may accept or reject depending on the
; signature.
; ============================================================================

; ---------- list/name helpers ------------------------------------------------
(= (hol-ctxidx Nil $s) NF)
(= (hol-ctxidx (Cons $h $t) $s)
   (if (== $h $s)
       (Idx 0)
       (case (hol-ctxidx $t $s)
         ((NF NF)
          ((Idx $k) (Idx (+ $k 1)))))))

(= (hol-resolve $ctx $s)
   (case (hol-ctxidx $ctx $s)
     (((Idx $k) (Var $k))
      (NF (Con $s)))))

; ---------- kernel-AST constructors -----------------------------------------
(= (hol-binder-ty) (Con o))
(= (hol-mk-unary $name $t) (App (Con $name) $t))
(= (hol-mk-binary $name $a $b) (App (App (Con $name) $a) $b))
(= (hol-mk-all $body) (App (Con all) (Lam (hol-binder-ty) $body)))
(= (hol-mk-ex $body) (App (Con ex) (Lam (hol-binder-ty) $body)))
(= (hol-mk-lam $body) (Lam (hol-binder-ty) $body))
(= (hol-mk-iff $a $b) (hol-mk-binary iff $a $b))
(= (hol-mk-imp $a $b) (hol-mk-binary imp $a $b))
(= (hol-mk-or $a $b) (hol-mk-binary or $a $b))
(= (hol-mk-and $a $b) (hol-mk-binary and $a $b))
(= (hol-mk-eq $a $b) (hol-mk-binary eq $a $b))
(= (hol-mk-not $t) (hol-mk-unary not $t))

; ---------- recursive-descent recognizer ------------------------------------
; Results: (P term rest-tokens) on success, (PErr reason) on failure.

(= (hol-term $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case $toks
         (((Cons ∀ (Cons (Lex hol-id $x) (Cons . $rest)))
            (case (hol-term (- $f 1) (Cons $x $ctx) $rest)
              (((P $body $r) (P (hol-mk-all $body) $r))
               ($e $e))))
          ((Cons ∃ (Cons (Lex hol-id $x) (Cons . $rest)))
            (case (hol-term (- $f 1) (Cons $x $ctx) $rest)
              (((P $body $r) (P (hol-mk-ex $body) $r))
               ($e $e))))
          ((Cons λ (Cons (Lex hol-id $x) (Cons . $rest)))
            (case (hol-term (- $f 1) (Cons $x $ctx) $rest)
              (((P $body $r) (P (hol-mk-lam $body) $r))
               ($e $e))))
          ($_ (hol-iff $f $ctx $toks))))))

(= (hol-iff $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-imp (- $f 1) $ctx $toks)
         (((P $a (Cons ⇔ $rest))
            (case (hol-iff (- $f 1) $ctx $rest)
              (((P $b $r) (P (hol-mk-iff $a $b) $r))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

(= (hol-imp $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-disj (- $f 1) $ctx $toks)
         (((P $a (Cons ⇒ $rest))
            (case (hol-imp (- $f 1) $ctx $rest)
              (((P $b $r) (P (hol-mk-imp $a $b) $r))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

(= (hol-disj $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-conj (- $f 1) $ctx $toks)
         (((P $a (Cons ∨ $rest))
            (case (hol-disj (- $f 1) $ctx $rest)
              (((P $b $r) (P (hol-mk-or $a $b) $r))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

(= (hol-conj $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-eq (- $f 1) $ctx $toks)
         (((P $a (Cons ∧ $rest))
            (case (hol-conj (- $f 1) $ctx $rest)
              (((P $b $r) (P (hol-mk-and $a $b) $r))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

(= (hol-eq $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-neg (- $f 1) $ctx $toks)
         (((P $a (Cons = $rest))
            (case (hol-eq (- $f 1) $ctx $rest)
              (((P $b $r) (P (hol-mk-eq $a $b) $r))
               ($e $e))))
          ((P $a $rest) (P $a $rest))
          ($e $e)))))

(= (hol-neg $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case $toks
         (((Cons ¬ $rest)
            (case (hol-neg (- $f 1) $ctx $rest)
              (((P $t $r) (P (hol-mk-not $t) $r))
               ($e $e))))
          ($_ (hol-app $f $ctx $toks))))))

(= (hol-app $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case (hol-atom (- $f 1) $ctx $toks)
         (((P $a0 $r0) (hol-appmore (- $f 1) $ctx $a0 $r0))
          ($e $e)))))

(= (hol-appmore $f $ctx $acc $toks)
   (if (<= $f 0)
       (P $acc $toks)
       (case (hol-atom (- $f 1) $ctx $toks)
         (((P $a $rest) (hol-appmore (- $f 1) $ctx (App $acc $a) $rest))
          ($_ (P $acc $toks))))))

(= (hol-atom $f $ctx $toks)
   (if (<= $f 0)
       (PErr no-fuel)
       (case $toks
         (((Cons LP $rest)
            (case (hol-term (- $f 1) $ctx $rest)
              (((P $t (Cons RP $r2)) (P $t $r2))
               ($_ (PErr paren-malformed)))))
          ((Cons (Lex hol-id $s) $rest) (P (hol-resolve $ctx $s) $rest))
          ($_ (PErr atom-expected))))))

(= (hol-recognize $toks)
   (case (hol-term 128 Nil $toks)
     (((P $t Nil) (Ok $t))
      ((P $t $rest) (Err (extra-tokens $rest)))
      ((PErr $e) (Err $e))
      ($_ (Err recognize-failed)))))

; ---------- proof-fragment elaboration for the existing LF kernel ------------
; `hol-core-g` lambdas are syntactically unannotated.  The checked implication
; fragment has enough surface shape to elaborate lambdas immediately under
; `impI A B` to the LF kernel proof domain `prf A`; all final acceptance remains
; with the imported kernel.

(= (hol-elab-proof $t) (hol-elab-proof-f 128 $t))
(= (hol-elab-proof-f $f $t)
   (if (<= $f 0)
       (Err no-elab-fuel)
       (case $t
         (((App (App (App (Con impI) $A) $B) (Lam $D $body))
            (case (hol-elab-proof-f (- $f 1) $body)
              (((Ok $body0)
                 (Ok (App (App (App (Con impI) $A) $B)
                          (Lam (App (Con prf) $A) $body0))))
               ((Err $e) (Err $e)))))
          ((App $x $y)
            (case (hol-elab-proof-f (- $f 1) $x)
              (((Ok $x0)
                 (case (hol-elab-proof-f (- $f 1) $y)
                   (((Ok $y0) (Ok (App $x0 $y0)))
                    ((Err $e) (Err $e)))))
               ((Err $e) (Err $e)))))
          ((Lam $A $b)
            (case (hol-elab-proof-f (- $f 1) $b)
              (((Ok $b0) (Ok (Lam $A $b0)))
               ((Err $e) (Err $e)))))
          ((Pi $A $B)
            (case (hol-elab-proof-f (- $f 1) $A)
              (((Ok $A0)
                 (case (hol-elab-proof-f (- $f 1) $B)
                   (((Ok $B0) (Ok (Pi $A0 $B0)))
                    ((Err $e) (Err $e)))))
               ((Err $e) (Err $e)))))
          ($_ (Ok $t))))))

(= (hol-recognize-proof $toks)
   (case (hol-recognize $toks)
     (((Ok $raw) (hol-elab-proof $raw))
      ((Err $e) (Err $e)))))

; ---------- example surface token streams -----------------------------------
(= (hol-append Nil $ys) $ys)
(= (hol-append (Cons $x $xs) $ys) (Cons $x (hol-append $xs $ys)))
(= (hol-id-toks $x) (Cons (Lex hol-id $x) Nil))
(= (hol-par $xs) (Cons LP (hol-append $xs (Cons RP Nil))))
(= (hol-imp-toks $a $b) (hol-append $a (Cons ⇒ $b)))
(= (hol-lam-toks $x $body)
   (Cons λ (Cons (Lex hol-id $x) (Cons . $body))))

(= (ht-hall-imp)
   (Cons ∀ (Cons (Lex hol-id x) (Cons .
     (Cons (Lex hol-id p) (Cons ⇒ (Cons (Lex hol-id q) Nil)))))))
(= (ht-and-or)
   (Cons (Lex hol-id p) (Cons ∧ (Cons (Lex hol-id q)
     (Cons ∨ (Cons (Lex hol-id r) Nil))))))
(= (ht-nested-all)
   (Cons ∀ (Cons (Lex hol-id x) (Cons .
     (Cons ∀ (Cons (Lex hol-id y) (Cons . (Cons (Lex hol-id p) Nil))))))))
(= (ht-lam-app)
   (Cons λ (Cons (Lex hol-id x) (Cons .
     (Cons (Lex hol-id f) (Cons (Lex hol-id x) Nil))))))
(= (ht-malformed) (Cons LP (Cons ⇒ Nil)))

(= (ht-self-imp) (hol-imp-toks (hol-id-toks A) (hol-id-toks A)))
(= (ht-a-imp-b) (hol-imp-toks (hol-id-toks A) (hol-id-toks B)))
(= (ht-k-theorem)
   (hol-imp-toks (hol-id-toks A)
     (hol-imp-toks (hol-id-toks B) (hol-id-toks A))))
(= (ht-self-imp-proof)
   (hol-append (hol-id-toks impI)
     (hol-append (hol-id-toks A)
       (hol-append (hol-id-toks A)
         (hol-par (hol-lam-toks h (hol-id-toks h)))))))
(= (ht-k-proof)
   (hol-append (hol-id-toks impI)
     (hol-append (hol-id-toks A)
       (hol-append (hol-par (hol-imp-toks (hol-id-toks B) (hol-id-toks A)))
         (hol-par
           (hol-lam-toks hA
             (hol-append (hol-id-toks impI)
               (hol-append (hol-id-toks B)
                 (hol-append (hol-id-toks A)
                   (hol-par (hol-lam-toks hB (hol-id-toks hA))))))))))))
(= (ht-bad-a-imp-b-proof)
   (hol-append (hol-id-toks impI)
     (hol-append (hol-id-toks A)
       (hol-append (hol-id-toks B)
         (hol-par (hol-lam-toks h (hol-id-toks h)))))))
(= (ht-mp-theorem)
   (hol-imp-toks (hol-par (ht-a-imp-b)) (ht-a-imp-b)))
(= (ht-mp-theorem-proof)
   (hol-append (hol-id-toks impI)
     (hol-append (hol-par (ht-a-imp-b))
       (hol-append (hol-par (ht-a-imp-b))
         (hol-par
           (hol-lam-toks hAB
             (hol-append (hol-id-toks impI)
               (hol-append (hol-id-toks A)
                 (hol-append (hol-id-toks B)
                   (hol-par
                     (hol-lam-toks hA
                       (hol-append (hol-id-toks impE)
                         (hol-append (hol-id-toks A)
                           (hol-append (hol-id-toks B)
                              (hol-append (hol-id-toks hAB) (hol-id-toks hA))))))))))))))))

; ---------- recognizer unit checks ------------------------------------------
!(assertEqual (hol-recognize (ht-hall-imp))
   (Ok (App (Con all)
            (Lam (Con o) (App (App (Con imp) (Con p)) (Con q))))))
!(assertEqual (hol-recognize (ht-and-or))
   (Ok (App (App (Con or)
                 (App (App (Con and) (Con p)) (Con q)))
            (Con r))))
!(assertEqual (hol-recognize (ht-nested-all))
   (Ok (App (Con all) (Lam (Con o)
        (App (Con all) (Lam (Con o) (Con p)))))))
!(assertEqual (hol-recognize (ht-lam-app))
   (Ok (Lam (Con o) (App (Con f) (Var 0)))))
!(assertEqual (hol-recognize (ht-malformed)) (Err paren-malformed))
!(assertEqual (hol-recognize (ht-self-imp))
   (Ok (App (App (Con imp) (Con A)) (Con A))))
!(assertEqual (hol-recognize-proof (ht-self-imp-proof))
   (Ok (App (App (App (Con impI) (Con A)) (Con A))
            (Lam (App (Con prf) (Con A)) (Var 0)))))
