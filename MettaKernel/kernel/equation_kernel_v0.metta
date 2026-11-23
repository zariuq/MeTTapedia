; =============================================================================
; equation_kernel_v0.metta
;
; Tier-0 kernel for equation application over atoms, in two styles.
;
;   de Bruijn:  (ek:check program certificate claim) -> True / False
;   LCF:        theorems sealed with their theory, minted only by the rules
;               ek:lcf-refl, ek:lcf-step, ek:lcf-congr, ek:lcf-trans and the
;               checked ek:lcf-weaken; recording (ek:rec-*, eks:rec-*) emits
;               the certificate; ek:mint checks a certificate and seals its
;               claim. Written against the proposed seal operators
;               (new-seal, seal, unseal), emulated today.
;
; The judgment is `source ->* target`: finitely many applications of stored
; equations (= l r) of a program, each replacing an instance of l by the same
; instance of r at a position. Programs are multisets: an equation is cited
; by content and by the index of one of its equal stored copies.
;
; The checker computes; it never searches. A certificate supplies every
; choice (stored copy, position, bindings); the checker applies the
; bindings, compares atoms, walks positions and counts copies.
;
; Common core used: equations with constructor patterns, if, ==, and integer
; +, -, <, and case with a final catch-all. The sealed section also uses
; let*, new-state and the seal operators. No type declarations, quote, match,
; unify or superpose. Companion files:
;   equation_kernel_space_v0.metta       certificates and recording logs as
;                                        atoms of a space (each call carries
;                                        one row, not the certificate)
;   equation_kernel_registry_v0.metta    emulation of the proposed seal
;                                        operators (load before this file)
;   equation_kernel_primitives_v0.metta  emulations of proposed primitives
; Lean reference: Mettapedia.Languages.MeTTa.EquationKernel.
;
; Object atoms are data (the Lean encoder is the reference):
;   (ek:sym "name") (ek:var "name") (ek:int "decimal") (ek:str "text")
;   (ek:bool "True"|"False") (ek:gnd "type" "data") (ek:expr list)
; Lists: ek:nil | (ek:cons head tail). Symbol and variable names are strings,
; so no object symbol is ever evaluated by the host. Integers are canonical
; decimal strings, so every engine reads every integer; the kernel never
; computes with them.
;
; Certificate rows:
;   (ek:refl atom)
;   (ek:step prior (ek:cite equation copy) path bindings)
;   (ek:congr left inner right)
;   (ek:trans first second)
; Bindings: list of (ek:bind "name" atom). Paths: list of argument indices.
; Certificate: (ek:cert rows root). Claim: (ek:claim source target).
; =============================================================================

; ---------- options and lists ------------------------------------------------
(= (ek:append ek:nil $ys) $ys)
(= (ek:append (ek:cons $x $xs) $ys) (ek:cons $x (ek:append $xs $ys)))

(= (ek:nth ek:nil $i) ek:none)
(= (ek:nth (ek:cons $x $xs) $i)
   (if (== $i 0) (ek:some $x) (ek:nth $xs (- $i 1))))

(= (ek:set ek:nil $i $v) ek:nil)
(= (ek:set (ek:cons $x $xs) $i $v)
   (if (== $i 0) (ek:cons $v $xs) (ek:cons $x (ek:set $xs (- $i 1) $v))))

(= (ek:count-from $e ek:nil $n) $n)
(= (ek:count-from $e (ek:cons $x $xs) $n)
   (if (== $e $x) (ek:count-from $e $xs (+ $n 1)) (ek:count-from $e $xs $n)))

(= (ek:member $x ek:nil) False)
(= (ek:member $x (ek:cons $y $ys)) (if (== $x $y) True (ek:member $x $ys)))

; ---------- substitution -----------------------------------------------------
(= (ek:lookup $name ek:nil) ek:none)
(= (ek:lookup $name (ek:cons (ek:bind $key $value) $rest))
   (if (== $name $key) (ek:some $value) (ek:lookup $name $rest)))

(= (ek:subst $s (ek:var $name)) (ek:subst-var (ek:lookup $name $s) $name))
(= (ek:subst-var ek:none $name) (ek:var $name))
(= (ek:subst-var (ek:some $value) $name) $value)
(= (ek:subst $s (ek:sym $n)) (ek:sym $n))
(= (ek:subst $s (ek:int $n)) (ek:int $n))
(= (ek:subst $s (ek:str $n)) (ek:str $n))
(= (ek:subst $s (ek:bool $n)) (ek:bool $n))
(= (ek:subst $s (ek:gnd $t $d)) (ek:gnd $t $d))
(= (ek:subst $s (ek:expr $xs)) (ek:expr (ek:subst-list $s $xs)))
(= (ek:subst-list $s ek:nil) ek:nil)
(= (ek:subst-list $s (ek:cons $x $xs))
   (ek:cons (ek:subst $s $x) (ek:subst-list $s $xs)))

; ---------- positions --------------------------------------------------------
(= (ek:at $a ek:nil) (ek:some $a))
(= (ek:at (ek:expr $xs) (ek:cons $i $p)) (ek:at-child (ek:nth $xs $i) $p))
(= (ek:at (ek:sym $n) (ek:cons $i $p)) ek:none)
(= (ek:at (ek:var $n) (ek:cons $i $p)) ek:none)
(= (ek:at (ek:int $n) (ek:cons $i $p)) ek:none)
(= (ek:at (ek:str $n) (ek:cons $i $p)) ek:none)
(= (ek:at (ek:bool $n) (ek:cons $i $p)) ek:none)
(= (ek:at (ek:gnd $t $d) (ek:cons $i $p)) ek:none)
(= (ek:at-child ek:none $p) ek:none)
(= (ek:at-child (ek:some $x) $p) (ek:at $x $p))

(= (ek:replace $a ek:nil $new) (ek:some $new))
(= (ek:replace (ek:expr $xs) (ek:cons $i $p) $new)
   (ek:replace-child $xs $i (ek:nth $xs $i) $p $new))
(= (ek:replace (ek:sym $n) (ek:cons $i $p) $new) ek:none)
(= (ek:replace (ek:var $n) (ek:cons $i $p) $new) ek:none)
(= (ek:replace (ek:int $n) (ek:cons $i $p) $new) ek:none)
(= (ek:replace (ek:str $n) (ek:cons $i $p) $new) ek:none)
(= (ek:replace (ek:bool $n) (ek:cons $i $p) $new) ek:none)
(= (ek:replace (ek:gnd $t $d) (ek:cons $i $p) $new) ek:none)
(= (ek:replace-child $xs $i ek:none $p $new) ek:none)
(= (ek:replace-child $xs $i (ek:some $x) $p $new)
   (ek:replace-wrap $xs $i (ek:replace $x $p $new)))
(= (ek:replace-wrap $xs $i ek:none) ek:none)
(= (ek:replace-wrap $xs $i (ek:some $y)) (ek:some (ek:expr (ek:set $xs $i $y))))

; ---------- equations --------------------------------------------------------
(= (ek:sides (ek:expr $xs)) (ek:sides-list $xs))
(= (ek:sides (ek:sym $n)) ek:none)
(= (ek:sides (ek:var $n)) ek:none)
(= (ek:sides (ek:int $n)) ek:none)
(= (ek:sides (ek:str $n)) ek:none)
(= (ek:sides (ek:bool $n)) ek:none)
(= (ek:sides (ek:gnd $t $d)) ek:none)
(= (ek:sides-list ek:nil) ek:none)
(= (ek:sides-list (ek:cons $h ek:nil)) ek:none)
(= (ek:sides-list (ek:cons $h (ek:cons $l ek:nil))) ek:none)
(= (ek:sides-list (ek:cons $h (ek:cons $l (ek:cons $r ek:nil))))
   (if (== $h (ek:sym "=")) (ek:some (ek:pair $l $r)) ek:none))
(= (ek:sides-list (ek:cons $h (ek:cons $l (ek:cons $r (ek:cons $x $more))))) ek:none)

; ---------- the four kernel rules, as claim computations ---------------------
; A rule's premises arrive as (ek:some claim) or ek:none; its conclusion is
; (ek:some claim) or ek:none. The same functions serve both kernel styles.

(= (ek:refl-claim $a) (ek:some (ek:claim $a $a)))

(= (ek:step-claim $program ek:none $cite $path $bindings) ek:none)
(= (ek:step-claim $program (ek:some (ek:claim $source $current)) (ek:cite $e $k) $path $bindings)
   (ek:step-sides $program $source $current $e $k $path $bindings (ek:sides $e)))
(= (ek:step-sides $program $source $current $e $k $path $bindings ek:none) ek:none)
(= (ek:step-sides $program $source $current $e $k $path $bindings (ek:some (ek:pair $l $r)))
   (if (< $k 0)
       ek:none
       (if (< $k (ek:count-from $e $program 0))
           (if (== (ek:at $current $path) (ek:some (ek:subst $bindings $l)))
               (ek:step-next $source (ek:replace $current $path (ek:subst $bindings $r)))
               ek:none)
           ek:none)))
(= (ek:step-next $source ek:none) ek:none)
(= (ek:step-next $source (ek:some $next)) (ek:some (ek:claim $source $next)))

(= (ek:congr-claim $left ek:none $right) ek:none)
(= (ek:congr-claim $left (ek:some (ek:claim $a $b)) $right)
   (ek:some (ek:claim (ek:expr (ek:append $left (ek:cons $a $right)))
                      (ek:expr (ek:append $left (ek:cons $b $right))))))

(= (ek:trans-claim ek:none $second) ek:none)
(= (ek:trans-claim (ek:some $first) ek:none) ek:none)
(= (ek:trans-claim (ek:some (ek:claim $a $b)) (ek:some (ek:claim $b2 $c)))
   (if (== $b $b2) (ek:some (ek:claim $a $c)) ek:none))

; ---------- de Bruijn style: checking certificate rows ----------------------
; The table holds the claims of rows 0 .. n-1, newest first.
(= (ek:table-get $table $n $j)
   (if (< $j 0) ek:none (if (< $j $n) (ek:nth $table (- (- $n 1) $j)) ek:none)))

; A row that is not one of the four row terms refuses.
(= (ek:row-claim $program $table $n $row)
   (case $row
     (((ek:refl $a) (ek:refl-claim $a))
      ((ek:step $prior $cite $path $bindings)
       (ek:step-claim $program (ek:table-get $table $n $prior) $cite $path $bindings))
      ((ek:congr $left $inner $right)
       (ek:congr-claim $left (ek:table-get $table $n $inner) $right))
      ((ek:trans $first $second)
       (ek:trans-claim (ek:table-get $table $n $first) (ek:table-get $table $n $second)))
      ($other ek:none))))

(= (ek:check-rows $program $table $n ek:nil) (ek:some (ek:table $table $n)))
(= (ek:check-rows $program $table $n (ek:cons $row $rows))
   (ek:check-rows-next $program $table $n $rows (ek:row-claim $program $table $n $row)))
(= (ek:check-rows-next $program $table $n $rows ek:none) ek:none)
(= (ek:check-rows-next $program $table $n $rows (ek:some $claim))
   (ek:check-rows $program (ek:cons $claim $table) (+ $n 1) $rows))

(= (ek:check $program (ek:cert $rows $root) $claim)
   (ek:check-final (ek:check-rows $program ek:nil 0 $rows) $root $claim))
(= (ek:check-final ek:none $root $claim) False)
(= (ek:check-final (ek:some (ek:table $table $n)) $root $claim)
   (== (ek:table-get $table $n $root) (ek:some $claim)))

; ---------- hygiene: fresh instances -----------------------------------------
; A step row is fresh when every variable that occurs only on the right side
; of its equation is bound to a distinct variable absent from the claim it
; extends. The core judgment does not need this; it audits a producer's
; renaming apart.
(= (ek:vars (ek:var $n) $acc) (ek:cons $n $acc))
(= (ek:vars (ek:sym $n) $acc) $acc)
(= (ek:vars (ek:int $n) $acc) $acc)
(= (ek:vars (ek:str $n) $acc) $acc)
(= (ek:vars (ek:bool $n) $acc) $acc)
(= (ek:vars (ek:gnd $t $d) $acc) $acc)
(= (ek:vars (ek:expr $xs) $acc) (ek:vars-list $xs $acc))
(= (ek:vars-list ek:nil $acc) $acc)
(= (ek:vars-list (ek:cons $x $xs) $acc) (ek:vars $x (ek:vars-list $xs $acc)))

(= (ek:right-only ek:nil $left $acc) $acc)
(= (ek:right-only (ek:cons $n $ns) $left $acc)
   (if (ek:member $n $left) (ek:right-only $ns $left $acc) (ek:right-only $ns $left (ek:cons $n $acc))))

(= (ek:fresh-names ek:nil $scope $bindings) True)
(= (ek:fresh-names (ek:cons $n $ns) $scope $bindings)
   (ek:fresh-name (ek:lookup $n $bindings) $ns $scope $bindings))
(= (ek:fresh-name ek:none $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:var $fresh)) $ns $scope $bindings)
   (if (ek:member $fresh $scope) False (ek:fresh-names $ns $scope $bindings)))
(= (ek:fresh-name (ek:some (ek:sym $x)) $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:int $x)) $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:str $x)) $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:bool $x)) $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:gnd $t $d)) $ns $scope $bindings) False)
(= (ek:fresh-name (ek:some (ek:expr $x)) $ns $scope $bindings) False)

; Distinct right-only names must get distinct values.
(= (ek:distinct ek:nil $all $bindings) True)
(= (ek:distinct (ek:cons $n $ns) $all $bindings)
   (if (ek:distinct-from $n $all $bindings) (ek:distinct $ns $all $bindings) False))
(= (ek:distinct-from $n ek:nil $bindings) True)
(= (ek:distinct-from $n (ek:cons $m $ms) $bindings)
   (if (== $n $m)
       (ek:distinct-from $n $ms $bindings)
       (if (== (ek:lookup $n $bindings) (ek:lookup $m $bindings))
           False
           (ek:distinct-from $n $ms $bindings))))

(= (ek:fresh-step $source $current $bindings ek:none) False)
(= (ek:fresh-step $source $current $bindings (ek:some (ek:pair $l $r)))
   (ek:fresh-step-names (ek:right-only (ek:vars $r ek:nil) (ek:vars $l ek:nil) ek:nil)
                        (ek:vars $source (ek:vars $current ek:nil)) $bindings))
(= (ek:fresh-step-names $names $scope $bindings)
   (if (ek:fresh-names $names $scope $bindings) (ek:distinct $names $names $bindings) False))

(= (ek:row-fresh $table $n (ek:refl $a)) True)
(= (ek:row-fresh $table $n (ek:congr $left $inner $right)) True)
(= (ek:row-fresh $table $n (ek:trans $first $second)) True)
(= (ek:row-fresh $table $n (ek:step $prior (ek:cite $e $k) $path $bindings))
   (ek:row-fresh-at (ek:table-get $table $n $prior) $e $bindings))
(= (ek:row-fresh-at ek:none $e $bindings) False)
(= (ek:row-fresh-at (ek:some (ek:claim $source $current)) $e $bindings)
   (ek:fresh-step $source $current $bindings (ek:sides $e)))

(= (ek:fresh-rows $program $table $n ek:nil) True)
(= (ek:fresh-rows $program $table $n (ek:cons $row $rows))
   (ek:fresh-rows-next $program $table $n $row $rows (ek:row-claim $program $table $n $row)))
(= (ek:fresh-rows-next $program $table $n $row $rows ek:none) False)
(= (ek:fresh-rows-next $program $table $n $row $rows (ek:some $claim))
   (if (ek:row-fresh $table $n $row)
       (ek:fresh-rows $program (ek:cons $claim $table) (+ $n 1) $rows)
       False))

(= (ek:check-hygienic $program (ek:cert $rows $root) $claim)
   (if (ek:check $program (ek:cert $rows $root) $claim)
       (ek:fresh-rows $program ek:nil 0 $rows)
       False))

; ---------- LCF style: sealed theorems ---------------------------------------
; Written against the proposed seal primitive: (new-seal NICK), (seal S V),
; (unseal S X), (sealer-of S), (unsealer-of S); unseal gives no result for a
; value of another brand. equation_kernel_registry_v0.metta emulates these
; operators today; a native implementation replaces that file and leaves this
; section unchanged.
;
; A theorem is a value sealed by the kernel's seal, holding
;   (ek:thm THEORY CLAIM ORIGIN)
; THEORY is the program every step cites (a list of equation atoms), CLAIM is
; (ek:claim source target), ORIGIN is ek:unrecorded or (ek:origin SESSION ROW).
;
; Theory scoping. ek:lcf-step cites the premise's own theory; ek:lcf-congr
; keeps it; ek:lcf-trans requires equal theories; ek:lcf-weaken moves a
; theorem to a theory containing its own (as multisets), checked. A theorem
; is never combined across theories without that explicit, checked weakening
; (Lean: SealedTheorem in EquationKernel.Sealed).
;
; Mint authority. Only the rule functions below seal, each in the same
; equation that computes its conclusion from unsealed premises and rule data:
; ek:lcf-refl, ek:lcf-step, ek:lcf-congr, ek:lcf-trans, ek:lcf-weaken,
; ek:mint (after ek:check accepts), and the recorded forms ek:rec-* and
; eks:rec-* (equation_kernel_space_v0.metta). No function takes a conclusion
; and seals it. Reading uses the unsealer facet only.
;
; What waits for the native seal and frozen modules: today the capability
; cells below are reachable by their tokens and by matching these equations'
; bodies, and the emulated seal and its registry are data; the leak controls
; pin each case. Theory scoping and the absence of mint helpers hold now.

!(bind! &ek-sealer-cell (new-state ek:no-seal))
!(bind! &ek-unsealer-cell (new-state ek:no-seal))
!(change-state! &ek-sealer-cell (new-seal ek-theorem))
!(change-state! &ek-unsealer-cell (unsealer-of (get-state &ek-sealer-cell)))

; Reading a theorem: its content, or ek:none for anything else.
(= (ek:theorem-content $t)
   (case (collapse (unseal (get-state &ek-unsealer-cell) $t))
     ((((ek:thm $theory $claim $origin)) (ek:some (ek:thm $theory $claim $origin)))
      ($other ek:none))))
(= (ek:lcf-claim $t)
   (case (ek:theorem-content $t) (((ek:some (ek:thm $theory $claim $origin)) (ek:some $claim)) ($other ek:none))))
(= (ek:lcf-theory $t)
   (case (ek:theorem-content $t) (((ek:some (ek:thm $theory $claim $origin)) (ek:some $theory)) ($other ek:none))))

; Multiset inclusion of theories: every equation occurs at least as often.
(= (ek:included $small $large) (ek:included-from $small $small $large))
(= (ek:included-from ek:nil $small $large) True)
(= (ek:included-from (ek:cons $e $rest) $small $large)
   (if (< (ek:count-from $e $large 0) (ek:count-from $e $small 0))
       False
       (ek:included-from $rest $small $large)))

(= (ek:lcf-refl $theory $a)
   (seal (get-state &ek-sealer-cell) (ek:thm $theory (ek:claim $a $a) ek:unrecorded)))

(= (ek:lcf-step $t $cite $path $bindings)
   (case (ek:theorem-content $t)
     (((ek:some (ek:thm $theory $claim $origin))
       (case (ek:step-claim $theory (ek:some $claim) $cite $path $bindings)
         (((ek:some $next) (seal (get-state &ek-sealer-cell) (ek:thm $theory $next ek:unrecorded)))
          ($none ek:refused))))
      ($other ek:refused))))

(= (ek:lcf-congr $left $t $right)
   (case (ek:theorem-content $t)
     (((ek:some (ek:thm $theory $claim $origin))
       (case (ek:congr-claim $left (ek:some $claim) $right)
         (((ek:some $next) (seal (get-state &ek-sealer-cell) (ek:thm $theory $next ek:unrecorded)))
          ($none ek:refused))))
      ($other ek:refused))))

(= (ek:lcf-trans $t $u)
   (case (ek:theorem-content $t)
     (((ek:some (ek:thm $theory $first $origin))
       (case (ek:theorem-content $u)
         (((ek:some (ek:thm $theory2 $second $origin2))
           (if (== $theory $theory2)
               (case (ek:trans-claim (ek:some $first) (ek:some $second))
                 (((ek:some $joined) (seal (get-state &ek-sealer-cell) (ek:thm $theory $joined ek:unrecorded)))
                  ($none ek:refused)))
               ek:refused))
          ($other ek:refused))))
      ($other ek:refused))))

(= (ek:lcf-weaken $t $larger)
   (case (ek:theorem-content $t)
     (((ek:some (ek:thm $theory $claim $origin))
       (if (ek:included $theory $larger)
           (seal (get-state &ek-sealer-cell) (ek:thm $larger $claim ek:unrecorded))
           ek:refused))
      ($other ek:refused))))

; Minting: the checker accepts the certificate under the theory, then the
; claim is sealed under that theory.
(= (ek:mint $theory $certificate $claim)
   (if (ek:check $theory $certificate $claim)
       (seal (get-state &ek-sealer-cell) (ek:thm $theory $claim ek:unrecorded))
       ek:refused))

; ---------- LCF with recording -----------------------------------------------
; A recording session has a fresh name and one theory. Its state
;   (ek:rec SESSION THEORY LOG COUNT)
; holds the rows so far, newest first. Each recorded rule returns
; (ek:recorded STATE THEOREM). A recorded rule accepts only premises recorded
; in the same session and theory, cites them by their rows, and refuses
; otherwise; a refused rule returns the state unchanged. The log, reversed,
; is the certificate. A forged state cannot make a theorem false, since every
; theorem is computed from sealed premises; at worst the certificate it
; yields does not check.
!(bind! &ek-sessions (new-state 0))

(= (ek:fresh-session)
   (let $n (get-state &ek-sessions)
     (let $advanced (change-state! &ek-sessions (+ $n 1)) (ek:session $n))))

(= (ek:rec-open $theory) (let $session (ek:fresh-session) (ek:rec $session $theory ek:nil 0)))

; The row of a premise recorded in this session and theory, or ek:none.
(= (ek:session-row $session $theory $count $t)
   (case (ek:theorem-content $t)
     (((ek:some (ek:thm $theory2 $claim (ek:origin $session2 $row)))
       (if (== $session $session2)
           (if (== $theory $theory2)
               (if (< $row $count) (ek:some (ek:pair $row $claim)) ek:none)
               ek:none)
           ek:none))
      ($other ek:none))))

(= (ek:rec-refl (ek:rec $session $theory $log $count) $a)
   (let $next (+ $count 1)
     (ek:recorded (ek:rec $session $theory (ek:cons (ek:refl $a) $log) $next)
                  (seal (get-state &ek-sealer-cell)
                        (ek:thm $theory (ek:claim $a $a) (ek:origin $session $count))))))

(= (ek:rec-step (ek:rec $session $theory $log $count) $t $cite $path $bindings)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim))
       (case (ek:step-claim $theory (ek:some $claim) $cite $path $bindings)
         (((ek:some $next-claim)
           (let $next (+ $count 1)
             (ek:recorded (ek:rec $session $theory (ek:cons (ek:step $row $cite $path $bindings) $log) $next)
                          (seal (get-state &ek-sealer-cell)
                                (ek:thm $theory $next-claim (ek:origin $session $count))))))
          ($none (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))
      ($other (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))

(= (ek:rec-congr (ek:rec $session $theory $log $count) $left $t $right)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim))
       (case (ek:congr-claim $left (ek:some $claim) $right)
         (((ek:some $next-claim)
           (let $next (+ $count 1)
             (ek:recorded (ek:rec $session $theory (ek:cons (ek:congr $left $row $right) $log) $next)
                          (seal (get-state &ek-sealer-cell)
                                (ek:thm $theory $next-claim (ek:origin $session $count))))))
          ($none (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))
      ($other (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))

(= (ek:rec-trans (ek:rec $session $theory $log $count) $t $u)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $first))
       (case (ek:session-row $session $theory $count $u)
         (((ek:some (ek:pair $row2 $second))
           (case (ek:trans-claim (ek:some $first) (ek:some $second))
             (((ek:some $joined)
               (let $next (+ $count 1)
                 (ek:recorded (ek:rec $session $theory (ek:cons (ek:trans $row $row2) $log) $next)
                              (seal (get-state &ek-sealer-cell)
                                    (ek:thm $theory $joined (ek:origin $session $count))))))
              ($none (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))
          ($other (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))
      ($other (ek:recorded (ek:rec $session $theory $log $count) ek:refused)))))

(= (ek:reverse-onto ek:nil $acc) $acc)
(= (ek:reverse-onto (ek:cons $x $xs) $acc) (ek:reverse-onto $xs (ek:cons $x $acc)))

; The certificate of a recorded theorem of this session.
(= (ek:rec-certificate (ek:rec $session $theory $log $count) $t)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim)) (ek:cert (ek:reverse-onto $log ek:nil) $row))
      ($other ek:refused))))
