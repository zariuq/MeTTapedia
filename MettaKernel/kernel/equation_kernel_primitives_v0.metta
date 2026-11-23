; =============================================================================
; equation_kernel_primitives_v0.metta
;
; Library emulations of primitives proposed for MeTTa, written over the
; encoded atoms of equation_kernel_v0.metta. Load after that file. They are
; prototypes for discussion; none is needed by ek:check.
;
;   matching that returns its substitution as data   ek:match, ek:mstep
;   sites given as patterns (unique hole variable)    ek:cstep-claim
;   content-addressed atom identity                   ek:intern, ek:interned
;   membership with multiplicity                      ek:count-from (kernel),
;                                                     ek:stored-copies
;   positional subatom access and replacement         ek:at, ek:replace (kernel)
;   fresh variables                                    ek:fresh-var
;   sealing                                            new-seal, seal, unseal
;                                                      (equation_kernel_registry_v0)
; =============================================================================

; ---------- matching that returns its substitution as data -------------------
; One-way matching: variables of the pattern are bound, variables of the
; target are constants. Bindings are threaded as data.
(= (ek:match (ek:var $x) $t $b) (ek:match-var (ek:lookup $x $b) $x $t $b))
(= (ek:match-var ek:none $x $t $b) (ek:some (ek:cons (ek:bind $x $t) $b)))
(= (ek:match-var (ek:some $v) $x $t $b) (if (== $v $t) (ek:some $b) ek:none))
(= (ek:match (ek:sym $n) $t $b) (if (== (ek:sym $n) $t) (ek:some $b) ek:none))
(= (ek:match (ek:int $n) $t $b) (if (== (ek:int $n) $t) (ek:some $b) ek:none))
(= (ek:match (ek:str $n) $t $b) (if (== (ek:str $n) $t) (ek:some $b) ek:none))
(= (ek:match (ek:bool $n) $t $b) (if (== (ek:bool $n) $t) (ek:some $b) ek:none))
(= (ek:match (ek:gnd $k $d) $t $b) (if (== (ek:gnd $k $d) $t) (ek:some $b) ek:none))
(= (ek:match (ek:expr $ps) $t $b) (ek:match-expr $ps $t $b))
(= (ek:match-expr $ps (ek:expr $ts) $b) (ek:match-list $ps $ts $b))
(= (ek:match-expr $ps (ek:sym $n) $b) ek:none)
(= (ek:match-expr $ps (ek:var $n) $b) ek:none)
(= (ek:match-expr $ps (ek:int $n) $b) ek:none)
(= (ek:match-expr $ps (ek:str $n) $b) ek:none)
(= (ek:match-expr $ps (ek:bool $n) $b) ek:none)
(= (ek:match-expr $ps (ek:gnd $k $d) $b) ek:none)
(= (ek:match-list ek:nil ek:nil $b) (ek:some $b))
(= (ek:match-list ek:nil (ek:cons $t $ts) $b) ek:none)
(= (ek:match-list (ek:cons $p $ps) ek:nil $b) ek:none)
(= (ek:match-list (ek:cons $p $ps) (ek:cons $t $ts) $b)
   (ek:match-list-next $ps $ts (ek:match $p $t $b)))
(= (ek:match-list-next $ps $ts ek:none) ek:none)
(= (ek:match-list-next $ps $ts (ek:some $b)) (ek:match-list $ps $ts $b))

; A compressed step supplies only the bindings of right-only variables; the
; left-side bindings are computed by matching. The claim is then computed by
; ek:step-claim, which checks the instance again, so the matcher is not
; trusted: a wrong matcher can only cause refusals.
(= (ek:mstep-claim $program ek:none $cite $path $extra) ek:none)
(= (ek:mstep-claim $program (ek:some (ek:claim $source $current)) (ek:cite $e $k) $path $extra)
   (ek:mstep-sides $program (ek:some (ek:claim $source $current)) (ek:cite $e $k) $path $extra
                   (ek:sides $e) (ek:at $current $path)))
(= (ek:mstep-sides $program $prior $cite $path $extra ek:none $focus) ek:none)
(= (ek:mstep-sides $program $prior $cite $path $extra (ek:some (ek:pair $l $r)) ek:none) ek:none)
(= (ek:mstep-sides $program $prior $cite $path $extra (ek:some (ek:pair $l $r)) (ek:some $focus))
   (ek:mstep-bound $program $prior $cite $path $extra (ek:match $l $focus ek:nil)))
(= (ek:mstep-bound $program $prior $cite $path $extra ek:none) ek:none)
(= (ek:mstep-bound $program $prior $cite $path $extra (ek:some $matched))
   (ek:step-claim $program $prior $cite $path (ek:append $matched $extra)))

; ---------- sites given as patterns -----------------------------------------
; The site is a pattern over the current atom in which the hole variable
; occurs once; its other variables stand for kept parts. Matching the
; pattern binds the hole to the subatom, so the substitution carries the
; position. The checker substitutes back and compares, so neither matcher is
; trusted. Lean reference: contextClaim? in EquationKernel.Matching.
(= (ek:cstep-claim $program ek:none $cite $pattern $hole $extra) ek:none)
(= (ek:cstep-claim $program (ek:some (ek:claim $source $current)) (ek:cite $e $k) $pattern $hole $extra)
   (ek:cstep-sides $program $source $current $e $k $pattern $hole $extra (ek:sides $e)))
(= (ek:cstep-sides $program $source $current $e $k $pattern $hole $extra ek:none) ek:none)
(= (ek:cstep-sides $program $source $current $e $k $pattern $hole $extra (ek:some (ek:pair $l $r)))
   (if (== (ek:count-from $hole (ek:vars $pattern ek:nil) 0) 1)
       (if (< $k 0)
           ek:none
           (if (< $k (ek:count-from $e $program 0))
               (ek:cstep-around $source $current $l $r $pattern $hole $extra (ek:match $pattern $current ek:nil))
               ek:none))
       ek:none))
(= (ek:cstep-around $source $current $l $r $pattern $hole $extra ek:none) ek:none)
(= (ek:cstep-around $source $current $l $r $pattern $hole $extra (ek:some $around))
   (ek:cstep-focus $source $current $l $r $pattern $hole $extra $around (ek:lookup $hole $around)))
(= (ek:cstep-focus $source $current $l $r $pattern $hole $extra $around ek:none) ek:none)
(= (ek:cstep-focus $source $current $l $r $pattern $hole $extra $around (ek:some $focus))
   (ek:cstep-inner $source $current $l $r $pattern $hole $extra $around (ek:match $l $focus ek:nil)))
(= (ek:cstep-inner $source $current $l $r $pattern $hole $extra $around ek:none) ek:none)
(= (ek:cstep-inner $source $current $l $r $pattern $hole $extra $around (ek:some $inner))
   (ek:cstep-check $source $current $pattern $hole $around
                   (ek:subst (ek:append $inner $extra) $l) (ek:subst (ek:append $inner $extra) $r)))
(= (ek:cstep-check $source $current $pattern $hole $around $lhs $rhs)
   (if (== (ek:subst (ek:cons (ek:bind $hole $lhs) $around) $pattern) $current)
       (ek:some (ek:claim $source (ek:subst (ek:cons (ek:bind $hole $rhs) $around) $pattern)))
       ek:none))

; ---------- content-addressed atom identity ----------------------------------
; Interning: equal atoms get equal identifiers, distinct atoms distinct ones.
; A certificate may cite (ek:interned id) instead of a whole equation; the
; checker reads the atom back from the table.
!(bind! &ek-atoms (new-space))
!(bind! &ek-atom-count (new-state 0))
(= (ek:intern $atom) (ek:intern-found $atom (ek:only-answer (collapse (match &ek-atoms (ek:id $n $atom) $n)))))
(= (ek:intern-found $atom (ek:some $n)) $n)
(= (ek:intern-found $atom ek:none)
   (let $n (get-state &ek-atom-count)
     (let $advanced (change-state! &ek-atom-count (+ $n 1))
       (let $added (add-atom &ek-atoms (ek:id $n $atom)) $n))))
(= (ek:interned $n) (ek:only-answer (collapse (match &ek-atoms (ek:id $n $atom) $atom))))
(= (ek:only-answer $answers)
   (if (== $answers ()) ek:none (ek:only-answer-first (decons-atom $answers))))
(= (ek:only-answer-first ($first $rest)) (if (== $rest ()) (ek:some $first) ek:none))

; ---------- membership with multiplicity --------------------------------------
; Copies of an atom stored in a space, counted by a query.
(= (ek:stored-copies $space $atom) (ek:length-of (collapse (match $space $atom $atom)) 0))
(= (ek:length-of $answers $n)
   (if (== $answers ()) $n (ek:length-rest (decons-atom $answers) $n)))
(= (ek:length-rest ($first $rest) $n) (ek:length-of $rest (+ $n 1)))

; ---------- fresh variables ---------------------------------------------------
; The first name (ek:name base k), k = index, index + 1, ..., that does not
; occur in a scope list. String concatenation is not in the common core, so
; the emulation builds structured names; the checker compares names with ==.
(= (ek:fresh-var $base $index $scope)
   (if (ek:member (ek:name $base $index) $scope)
       (ek:fresh-var $base (+ $index 1) $scope)
       (ek:var (ek:name $base $index))))
