; =============================================================================
; equation_kernel_space_v0.metta
;
; The de Bruijn checker of equation_kernel_v0.metta with the certificate held
; as atoms of a space instead of one nested term. Load after
; equation_kernel_v0.metta. Lean model: EquationKernel.SpaceCheck
; (spaceCheck_sound, spaceCheck_complete, spaceCheck_table_restored,
; spaceCheck_retry).
;
; Certificate atoms, for a certificate named id with n rows:
;   (ek:size id n)  (ek:root id r)  (ek:row id 0 row0) ... (ek:row id n-1 rowN)
; Each fact is read as the unique answer of its query; a missing or repeated
; fact refuses.
;
; Claims are recorded in the table space &eks-table, shared by every
; invocation and writable by other code. An invocation
;   - takes a fresh invocation number and tags its entries (ek:claim-at inv i c);
;   - writes row i only after finding no entry for (inv, i), so every entry
;     it reads under its number is its own;
;   - reads a premise only below the current row, and the root only below n;
;   - removes every entry of its number when it finishes, accepted or not.
; Whatever the table holds, acceptance means that the pure checker accepts the
; certificate read from the facts under the given theory; stale names,
; earlier theories, failed runs and injected entries can only cause refusal.
;
; Each call carries one row and one claim, not the whole certificate: in HE
; and CeTTa a call's cost grows with the size of its arguments.
; =============================================================================

; At most one answer of a query.
(= (eks:only $answers)
   (if (== $answers ()) ek:none (eks:only-first (decons-atom $answers))))
(= (eks:only-first ($first $rest)) (if (== $rest ()) (ek:some $first) ek:none))

(= (eks:row $space $id $i) (eks:only (collapse (match $space (ek:row $id $i $row) $row))))
(= (eks:size $space $id) (eks:only (collapse (match $space (ek:size $id $n) $n))))
(= (eks:root $space $id) (eks:only (collapse (match $space (ek:root $id $r) $r))))

!(bind! &eks-table (new-space))
!(bind! &eks-invocations (new-state 0))

(= (eks:fresh-invocation)
   (let $n (get-state &eks-invocations)
     (let $advanced (change-state! &eks-invocations (+ $n 1)) $n)))

(= (eks:claims-at $inv $j) (collapse (match &eks-table (ek:claim-at $inv $j $claim) $claim)))
; A premise or the root: only below the current row, as the unique entry.
(= (eks:claim $inv $current $j)
   (if (< $j 0) ek:none (if (< $j $current) (eks:only (eks:claims-at $inv $j)) ek:none)))

; The four rules, through bounded lookups. A row that is not a row term
; refuses.
(= (eks:row-claim $program $inv $current $row)
   (case $row
     (((ek:refl $a) (ek:refl-claim $a))
      ((ek:step $prior $cite $path $bindings)
       (ek:step-claim $program (eks:claim $inv $current $prior) $cite $path $bindings))
      ((ek:congr $left $inner $right)
       (ek:congr-claim $left (eks:claim $inv $current $inner) $right))
      ((ek:trans $first $second)
       (ek:trans-claim (eks:claim $inv $current $first) (eks:claim $inv $current $second)))
      ($other ek:none))))

; Check rows i .. n-1; True when every row has a claim.
(= (eks:loop $program $space $id $inv $i $n)
   (if (== $i $n) True (eks:loop-row $program $space $id $inv $i $n (eks:row $space $id $i))))
(= (eks:loop-row $program $space $id $inv $i $n ek:none) False)
(= (eks:loop-row $program $space $id $inv $i $n (ek:some $row))
   (eks:loop-claim $program $space $id $inv $i $n (eks:row-claim $program $inv $i $row)))
(= (eks:loop-claim $program $space $id $inv $i $n ek:none) False)
(= (eks:loop-claim $program $space $id $inv $i $n (ek:some $claim))
   (if (== (eks:claims-at $inv $i) ())
       (let $added (add-atom &eks-table (ek:claim-at $inv $i $claim))
         (eks:loop $program $space $id $inv (+ $i 1) $n))
       False))

(= (eks:check $program $space $id $claim)
   (eks:check-sized $program $space $id $claim (eks:size $space $id) (eks:root $space $id)))
(= (eks:check-sized $program $space $id $claim ek:none $root) False)
(= (eks:check-sized $program $space $id $claim (ek:some $n) ek:none) False)
(= (eks:check-sized $program $space $id $claim (ek:some $n) (ek:some $root))
   (if (< $root 0)
       False
       (if (< $root $n)
           (let $inv (eks:fresh-invocation)
             (eks:finish $inv
               (if (eks:loop $program $space $id $inv 0 $n)
                   (== (eks:claim $inv $n $root) (ek:some $claim))
                   False)))
           False)))

; The verdict is computed before the invocation's entries are removed.
(= (eks:finish $inv $verdict) (let $cleaned (eks:cleanup $inv) $verdict))
(= (eks:cleanup $inv)
   (eks:remove-all (collapse (match &eks-table (ek:claim-at $inv $j $c) (ek:claim-at $inv $j $c)))))
(= (eks:remove-all $atoms) (if (== $atoms ()) done (eks:remove-first (decons-atom $atoms))))
(= (eks:remove-first ($first $rest)) (let $removed (remove-atom &eks-table $first) (eks:remove-all $rest)))

; ---------- LCF recording into a space ----------------------------------------
; A recording session writes each rule application as a row atom
; (ek:row SESSION i row) of a space; its state is
;   (eks:rec SPACE SESSION THEORY COUNT)
; and each recorded rule returns (eks:recorded STATE THEOREM). Sessions get
; fresh names (ek:fresh-session), so rows of different sessions never share
; a name. A recorded rule accepts only premises recorded in the same session
; and theory and refuses otherwise. (eks:rec-close STATE THEOREM) writes the
; size and root atoms and returns the session's name, under which eks:check
; checks the rows: the log is the space form of the certificate.
(= (eks:rec-open $space $theory)
   (let $session (ek:fresh-session) (eks:rec $space $session $theory 0)))

(= (eks:rec-refl (eks:rec $space $session $theory $count) $a)
   (let $next (+ $count 1)
     (let $added (add-atom $space (ek:row $session $count (ek:refl $a)))
       (eks:recorded (eks:rec $space $session $theory $next)
                     (seal (get-state &ek-sealer-cell)
                           (ek:thm $theory (ek:claim $a $a) (ek:origin $session $count)))))))

(= (eks:rec-step (eks:rec $space $session $theory $count) $t $cite $path $bindings)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim))
       (case (ek:step-claim $theory (ek:some $claim) $cite $path $bindings)
         (((ek:some $next-claim)
           (let $next (+ $count 1)
             (let $added (add-atom $space (ek:row $session $count (ek:step $row $cite $path $bindings)))
               (eks:recorded (eks:rec $space $session $theory $next)
                             (seal (get-state &ek-sealer-cell)
                                   (ek:thm $theory $next-claim (ek:origin $session $count)))))))
          ($none (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))
      ($other (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))

(= (eks:rec-congr (eks:rec $space $session $theory $count) $left $t $right)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim))
       (case (ek:congr-claim $left (ek:some $claim) $right)
         (((ek:some $next-claim)
           (let $next (+ $count 1)
             (let $added (add-atom $space (ek:row $session $count (ek:congr $left $row $right)))
               (eks:recorded (eks:rec $space $session $theory $next)
                             (seal (get-state &ek-sealer-cell)
                                   (ek:thm $theory $next-claim (ek:origin $session $count)))))))
          ($none (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))
      ($other (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))

(= (eks:rec-trans (eks:rec $space $session $theory $count) $t $u)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $first))
       (case (ek:session-row $session $theory $count $u)
         (((ek:some (ek:pair $row2 $second))
           (case (ek:trans-claim (ek:some $first) (ek:some $second))
             (((ek:some $joined)
               (let $next (+ $count 1)
                 (let $added (add-atom $space (ek:row $session $count (ek:trans $row $row2)))
                   (eks:recorded (eks:rec $space $session $theory $next)
                                 (seal (get-state &ek-sealer-cell)
                                       (ek:thm $theory $joined (ek:origin $session $count)))))))
              ($none (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))
          ($other (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))
      ($other (eks:recorded (eks:rec $space $session $theory $count) ek:refused)))))

; Close a session at a theorem of it; returns the name to check, or ek:refused.
(= (eks:rec-close (eks:rec $space $session $theory $count) $t)
   (case (ek:session-row $session $theory $count $t)
     (((ek:some (ek:pair $row $claim))
       (let $sized (add-atom $space (ek:size $session $count))
         (let $rooted (add-atom $space (ek:root $session $row)) $session)))
      ($other ek:refused))))

; Minting from a certificate held in a space.
(= (eks:mint $theory $space $id $claim)
   (if (eks:check $theory $space $id $claim)
       (seal (get-state &ek-sealer-cell) (ek:thm $theory $claim ek:unrecorded))
       ek:refused))
