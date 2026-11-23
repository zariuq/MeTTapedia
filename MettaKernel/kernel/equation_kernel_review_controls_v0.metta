; =============================================================================
; equation_kernel_review_controls_v0.metta
;
; The probes of the 2026-10-15 review of the equation kernel, as controls
; that pass when the repaired kernel refuses what it must. Load after
; equation_kernel_registry_v0.metta, equation_kernel_v0.metta and
; equation_kernel_space_v0.metta. Expected values follow the Lean examples
; SpaceScenarios (EquationKernel.SpaceCheck) and SealedScenarios
; (EquationKernel.Sealed). Facts and stored atoms are written as literal
; data, because PeTTa stores atoms without evaluating them.
; =============================================================================

(= (ek:control $name $value $expected) (if (== $value $expected) (ek:pass $name) (ek:FAIL $name $value)))

; ---------- the cache and theory probes ----------------------------------------
!(bind! &audit-second (new-space))
(ek:size same-id 2)
(ek:root same-id 1)
(ek:row same-id 0 (ek:refl (ek:sym "A")))
(ek:row same-id 1 (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))
!(ek:control ctl-review-valid-pure (ek:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:cert (ek:cons (ek:refl (ek:sym "A")) (ek:cons (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) ek:nil)) 1) (ek:claim (ek:sym "A") (ek:sym "B"))) True)
!(ek:control ctl-review-prime-cache (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self same-id (ek:claim (ek:sym "A") (ek:sym "B"))) True)
!(add-atom &audit-second (ek:size same-id 0))
!(add-atom &audit-second (ek:root same-id 1))
!(ek:control ctl-review-pure-empty (ek:check ek:nil (ek:cert ek:nil 1) (ek:claim (ek:sym "A") (ek:sym "B"))) False)
; The reviewed false acceptance, now refused.
!(ek:control ctl-review-space-empty-after-other-theory (eks:check ek:nil &audit-second same-id (ek:claim (ek:sym "A") (ek:sym "B"))) False)
!(ek:control ctl-review-pure-other-theory (ek:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) ek:nil) (ek:cert (ek:cons (ek:refl (ek:sym "A")) (ek:cons (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) ek:nil)) 1) (ek:claim (ek:sym "A") (ek:sym "B"))) False)
!(ek:control ctl-review-pure-cross-theory (ek:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) ek:nil) (ek:cert (ek:cons (ek:refl (ek:sym "A")) (ek:cons (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) (ek:cons (ek:step 1 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) 0) ek:nil ek:nil) ek:nil))) 2) (ek:claim (ek:sym "A") (ek:sym "C"))) False)
; The same mixing in the current interface: the step cites the premise's own theory.
!(ek:control ctl-review-lcf-cross-theory (let $t (ek:lcf-step (ek:lcf-refl (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:sym "A")) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) (ek:lcf-claim (ek:lcf-step $t (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) 0) ek:nil ek:nil))) ek:none)
!(ek:control ctl-review-lcf-cross-theory-trans (ek:lcf-claim (ek:lcf-trans (ek:lcf-step (ek:lcf-refl (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:sym "A")) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil) (ek:lcf-step (ek:lcf-refl (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) ek:nil) (ek:sym "B")) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) 0) ek:nil ek:nil))) ek:none)
; ---------- the public mint probe -----------------------------------------------
!(ek:control ctl-review-public-mint-helper (ek:lcf-claim (ek:lcf-from (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))) ek:no-row)) ek:none)
!(ek:control ctl-review-old-recording-helper (ek:lcf-claim (ek:rec-emit (ek:rec ek:nil 0) (ek:refl (ek:sym "A")) (ek:some (ek:claim (ek:sym "A") (ek:sym "forged"))))) ek:none)
; ---------- the reader-domain probe ----------------------------------------------
; Integers travel as canonical decimal strings, which every engine reads.
!(ek:control ctl-review-big-integers-distinct (== (ek:int "9223372036854775808") (ek:int "9223372036854775809")) False)
!(ek:control ctl-review-big-integer-fact (ek:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:expr (ek:cons (ek:sym "big") ek:nil)) (ek:cons (ek:int "9223372036854775808") ek:nil)))) ek:nil) (ek:cert (ek:cons (ek:refl (ek:expr (ek:cons (ek:sym "big") ek:nil))) (ek:cons (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:expr (ek:cons (ek:sym "big") ek:nil)) (ek:cons (ek:int "9223372036854775808") ek:nil)))) 0) ek:nil ek:nil) ek:nil)) 1) (ek:claim (ek:expr (ek:cons (ek:sym "big") ek:nil)) (ek:int "9223372036854775808"))) True)
; ---------- the space checker: names, bounds, injection, retry -----------------
; Two certificates under one name refuse.
(ek:size dup-id 2)
(ek:root dup-id 1)
(ek:row dup-id 0 (ek:refl (ek:sym "A")))
(ek:row dup-id 1 (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))
(ek:size dup-id 2)
(ek:root dup-id 1)
(ek:row dup-id 0 (ek:refl (ek:sym "A")))
(ek:row dup-id 1 (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))
!(ek:control ctl-review-repeated-name (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self dup-id (ek:claim (ek:sym "A") (ek:sym "B"))) False)
; A root at the size refuses.
(ek:size forward-root 1)
(ek:root forward-root 1)
(ek:row forward-root 0 (ek:refl (ek:sym "A")))
!(ek:control ctl-review-forward-root (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self forward-root (ek:claim (ek:sym "A") (ek:sym "A"))) False)
; A premise at or past its row refuses, even with an entry injected for it.
(ek:size forward-premise 2)
(ek:root forward-premise 0)
(ek:row forward-premise 0 (ek:step 1 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))
(ek:row forward-premise 1 (ek:refl (ek:sym "A")))
!(ek:control ctl-review-forward-premise (let $next (get-state &eks-invocations) (let $added (add-atom &eks-table (ek:claim-at $next 1 (ek:claim (ek:sym "A") (ek:sym "A")))) (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self forward-premise (ek:claim (ek:sym "A") (ek:sym "B"))))) False)
; An entry injected for the next invocation causes refusal, not acceptance;
; the refused invocation removes it, so the retry is accepted.
(ek:size injected 2)
(ek:root injected 1)
(ek:row injected 0 (ek:refl (ek:sym "A")))
(ek:row injected 1 (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))
!(ek:control ctl-review-injected-entry (let $next (get-state &eks-invocations) (let $added (add-atom &eks-table (ek:claim-at $next 1 (ek:claim (ek:sym "A") (ek:sym "B")))) (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self injected (ek:claim (ek:sym "A") (ek:sym "B"))))) False)
!(ek:control ctl-review-retry-after-injection (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self injected (ek:claim (ek:sym "A") (ek:sym "B"))) True)
; An injected claim cannot stand in for a missing row.
(ek:size missing-row 2)
(ek:root missing-row 1)
(ek:row missing-row 0 (ek:refl (ek:sym "A")))
!(ek:control ctl-review-injected-missing-row (let $next (get-state &eks-invocations) (let $added (add-atom &eks-table (ek:claim-at $next 1 (ek:claim (ek:sym "A") (ek:sym "B")))) (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self missing-row (ek:claim (ek:sym "A") (ek:sym "B"))))) False)
; A failed invocation, then a retry with a corrected certificate.
(ek:size retry-bad 2)
(ek:root retry-bad 1)
(ek:row retry-bad 0 (ek:refl (ek:sym "A")))
(ek:row retry-bad 1 (ek:step 0 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 1) ek:nil ek:nil))
!(ek:control ctl-review-failed-invocation (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self retry-bad (ek:claim (ek:sym "A") (ek:sym "B"))) False)
!(ek:control ctl-review-retry (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self same-id (ek:claim (ek:sym "A") (ek:sym "B"))) True)
; A row that is not a row term refuses.
(ek:size malformed 1)
(ek:root malformed 0)
(ek:row malformed 0 (ek:not-a-row (ek:sym "A")))
!(ek:control ctl-review-malformed-row (eks:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) &self malformed (ek:claim (ek:sym "A") (ek:sym "A"))) False)
!(ek:control ctl-review-malformed-row-pure (ek:check (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:cert (ek:cons (ek:not-a-row (ek:sym "A")) ek:nil) 0) (ek:claim (ek:sym "A") (ek:sym "A"))) False)
; Every invocation removed its entries.
!(ek:control ctl-review-table-clean (collapse (match &eks-table (ek:claim-at $i $j $c) $i)) ())
; ---------- recording sessions -------------------------------------------------
!(ek:control ctl-review-cross-session (let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:sym "A"))) ((ek:recorded $o1 $u1) (ek:rec-refl (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:sym "A"))) ((ek:recorded $s2 $t2) (ek:rec-step $s1 $u1 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))) $t2) ek:refused)
!(ek:control ctl-review-cross-session-certificate (let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:sym "A"))) ((ek:recorded $o1 $u1) (ek:rec-refl (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:sym "A")))) (ek:rec-certificate $s1 $u1)) ek:refused)
!(ek:control ctl-review-unrecorded-premise (let* (((ek:recorded $s1 $t1) (ek:rec-step (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:lcf-refl (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil) (ek:sym "A")) (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) 0) ek:nil ek:nil))) $t1) ek:refused)
!(ek:control ctl-review-recorded-foreign-step (let* (((ek:recorded $s1 $t1) (ek:rec-refl (ek:rec-open (ek:cons (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "A") (ek:cons (ek:sym "B") ek:nil)))) ek:nil)) (ek:sym "A"))) ((ek:recorded $s2 $t2) (ek:rec-step $s1 $t1 (ek:cite (ek:expr (ek:cons (ek:sym "=") (ek:cons (ek:sym "B") (ek:cons (ek:sym "C") ek:nil)))) 0) ek:nil ek:nil))) $t2) ek:refused)
