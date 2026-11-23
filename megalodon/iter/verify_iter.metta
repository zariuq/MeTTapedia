;; ============================================================================
;; Iter Architecture MeTTa + Megalodon Verification Suite Runner
;;
;; Run from the MeTTapedia repository root:
;;   cetta --lang petta megalodon/iter/verify_iter.metta
;;
;; 1. Verifies all five Megalodon formalization modules against the standard
;;    Egal preamble (megalodon/ramsey36/preamble.mgs) via CeTTa's native
;;    Megalodon kernel (library megalodon), mechanically auditing every verdict:
;;      verified, 0 document axioms, 0 admitted, 0 aby, 0 dependent,
;;      0 unfinished, 0 out-of-budget.
;; 2. Cross-checks the executable MeTTa cadence model (Module 2) and upstream
;;    extensions model (Module 5: configurable window buckets, resource caps,
;;    skill indexing hygiene, and LLM_BACKUP_MODEL fallback dispatch).
;; ============================================================================

!(import! &self (library megalodon))
!(import! &self (library system))

(= (iter-verify:preamble)
   ("megalodon/ramsey36/preamble.mgs"))

(= (iter-verify:fail $msg)
   (let $_ (println! (IterVerifyFailed $msg))
     (system:exit 1)))

(= (iter-verify:assert-true $label $cond)
   (if $cond
       (Ok $label)
       (iter-verify:fail (AssertionFailed $label))))

(= (iter-verify:assert-eq $label $got $want)
   (if (== $got $want)
       (Ok $label)
       (iter-verify:fail (EqMismatch $label (got $got) (want $want)))))

(= (iter-verify:check-mg $path $expected_count)
   (let $doc (mg:check-document (iter-verify:preamble) $path ())
     (case $doc
       (((Megalodon.document $theory $authority verified
            (summary (theorems $nt) (checked $nc) (verified $nv)
                     (admitted 0) (aby 0) (dependent 0)
                     (unfinished 0) (out-of-budget 0)
                     (document-axioms 0) (aby-steps-tried 0) (aby-steps-proved 0))
            $entries)
         (if (and (== $nt $nc) (and (== $nt $nv) (== $nt $expected_count)))
             (let $_ (println! (MegalodonVerified $path (theorems $nv) (document-axioms 0) (admitted 0) (aby 0)))
               $nv)
             (iter-verify:fail (CountMismatch $path $expected_count $nt $nc $nv))))
        ($other (iter-verify:fail (DocumentNotVerified $path $other)))))))

;; ----------------------------------------------------------------------------
;; Executable MeTTa cross-check of the Module 2 multi-step cadence theorems
;; Mirrors cad_step / cad_run in megalodon/iter/02_experience_hygiene.mg
;; ----------------------------------------------------------------------------

(= (iter-cad:bucket20 $n)
   (floor-math (/ $n 20)))

(= (iter-cad:step $policy $k (Cad $n $b $c))
   (let* (($cb (iter-cad:bucket20 $n))
          ($fired (> $cb $b))
          ($b1 (if $fired $cb $b))
          ($c1 (if $fired (+ $c 1) $c))
          ($trimmed (>= $n 100))
          ($n2 (if $trimmed (- 80 $k) $n))
          ($b2 (if $trimmed
                   (if (== $policy pre-strip)
                       (iter-cad:bucket20 80)
                       (iter-cad:bucket20 (- 80 $k)))
                   $b1)))
     (Cad (+ $n2 1) $b2 $c1)))

(= (iter-cad:run $policy $k $st $t)
   (if (<= $t 0)
       $st
       (iter-cad:run $policy $k (iter-cad:step $policy $k $st) (- $t 1))))

(= (iter-verify:check-cadence-crosscheck)
   (let* (;; Original pre-strip: uniformly 1 cleanup per closed (20+k)-step cycle for ALL 0<=k<=80
          ($_ (iter-verify:assert-eq "pre-strip-k0"  (iter-cad:run pre-strip  0 (Cad 81 4 0)  20) (Cad 81 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k1"  (iter-cad:run pre-strip  1 (Cad 80 4 0)  21) (Cad 80 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k5"  (iter-cad:run pre-strip  5 (Cad 76 4 0)  25) (Cad 76 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k20" (iter-cad:run pre-strip 20 (Cad 61 4 0)  40) (Cad 61 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k45" (iter-cad:run pre-strip 45 (Cad 36 4 0)  65) (Cad 36 4 1)))
          ($_ (iter-verify:assert-eq "pre-strip-k80" (iter-cad:run pre-strip 80 (Cad  1 4 0) 100) (Cad  1 4 1)))
          ;; Post-strip: 1 cleanup/cycle for k=0, 2 cleanups/cycle for 1<=k<=20
          ($_ (iter-verify:assert-eq "post-strip-k0"  (iter-cad:run post-strip  0 (Cad 81 4 0) 20) (Cad 81 4 1)))
          ($_ (iter-verify:assert-eq "post-strip-k1"  (iter-cad:run post-strip  1 (Cad 80 3 0) 21) (Cad 80 3 2)))
          ($_ (iter-verify:assert-eq "post-strip-k5"  (iter-cad:run post-strip  5 (Cad 76 3 0) 25) (Cad 76 3 2)))
          ($_ (iter-verify:assert-eq "post-strip-k20" (iter-cad:run post-strip 20 (Cad 61 3 0) 40) (Cad 61 3 2)))
          ;; Startup delay: uncleaned loaded history at L0=80 with k=0 has 0 cleanups across [80..99]
          ($_ (iter-verify:assert-eq "startup-delay-pre"  (iter-cad:run pre-strip  0 (Cad 80 4 0) 20) (Cad 100 4 0)))
          ($_ (iter-verify:assert-eq "startup-delay-post" (iter-cad:run post-strip 0 (Cad 80 4 0) 20) (Cad 100 4 0))))
     (println! (MeTTaCadenceCrossCheckPass (checks 12)))))

;; ----------------------------------------------------------------------------
;; Executable MeTTa cross-check of Module 5 upstream extension theorems
;; Mirrors cfg_interval, bucket_gen, cap_active/cap_omitted, skill_index_desc,
;; and backup_dispatch in megalodon/iter/05_upstream_extensions.mg
;; ----------------------------------------------------------------------------

(= (iter-ext:bucket $M $R $L)
   (floor-math (/ $L (- $M $R))))

(= (iter-ext:cap-active $N $C)
   (if (<= $C $N) $C $N))

(= (iter-ext:cap-omitted $N $C)
   (if (<= $C $N) (- $N $C) 0))

(= (iter-ext:backup-dispatch $primary $backup $p_ok $p_ref $p_res $p_err $b_ok $b_res)
   (let $has_backup (and (not (== $backup "")) (not (== $backup $primary)))
     (if $p_ok
         (if (and $p_ref $has_backup)
             (if $b_ok (Out $backup $b_res 2) (Out $backup BackupErr 2))
             (Out $primary $p_res 1))
         (if $has_backup
             (if $b_ok (Out $backup $b_res 2) (Out $primary $p_err 2))
             (Out $primary $p_err 1)))))

(= (iter-verify:check-upstream-crosscheck)
   (let* (;; Parametric configurable window: bucket(M) = bucket(R) + 1 even when (M-R) does not divide R
          ($_ (iter-verify:assert-eq "cfg-bucket-100-80" (iter-ext:bucket 100 80 100) (+ (iter-ext:bucket 100 80 80) 1)))
          ($_ (iter-verify:assert-eq "cfg-bucket-53-30"  (iter-ext:bucket 53 30 53)   (+ (iter-ext:bucket 53 30 30) 1)))
          ($_ (iter-verify:assert-eq "cfg-bucket-10-7"   (iter-ext:bucket 10 7 10)    (+ (iter-ext:bucket 10 7 7) 1)))
          ($_ (iter-verify:assert-true "cfg-sentinel-neg1" (< -1 (iter-ext:bucket 53 30 0))))
          ;; Resource cap conservation and omitted characterization
          ($_ (iter-verify:assert-eq "cap-under-active"  (iter-ext:cap-active 12 30) 12))
          ($_ (iter-verify:assert-eq "cap-under-omitted" (iter-ext:cap-omitted 12 30) 0))
          ($_ (iter-verify:assert-eq "cap-over-active"   (iter-ext:cap-active 37 30) 30))
          ($_ (iter-verify:assert-eq "cap-over-omitted"  (iter-ext:cap-omitted 37 30) 7))
          ;; LLM_BACKUP_MODEL fallback dispatch state machine
          ($_ (iter-verify:assert-eq "backup-unset-refusal"
                (iter-ext:backup-dispatch "p" "" True True RefusalResp PrimErr True BackupResp)
                (Out "p" RefusalResp 1)))
          ($_ (iter-verify:assert-eq "backup-same-model"
                (iter-ext:backup-dispatch "p" "p" False False RefusalResp PrimErr True BackupResp)
                (Out "p" PrimErr 1)))
          ($_ (iter-verify:assert-eq "backup-valid-primary"
                (iter-ext:backup-dispatch "p" "b" True False GoodResp PrimErr True BackupResp)
                (Out "p" GoodResp 1)))
          ($_ (iter-verify:assert-eq "backup-on-refusal"
                (iter-ext:backup-dispatch "p" "b" True True RefusalResp PrimErr True BackupResp)
                (Out "b" BackupResp 2)))
          ($_ (iter-verify:assert-eq "backup-on-primary-error"
                (iter-ext:backup-dispatch "p" "b" False False RefusalResp PrimErr True BackupResp)
                (Out "b" BackupResp 2)))
          ($_ (iter-verify:assert-eq "backup-double-error-preserves-primary"
                (iter-ext:backup-dispatch "p" "b" False False RefusalResp PrimErr False BackupResp)
                (Out "p" PrimErr 2))))
     (println! (MeTTaUpstreamCrossCheckPass (checks 14)))))

(= (iter-verify:main)
   (let* (($n1 (iter-verify:check-mg "megalodon/iter/01_nal_truth.mg" 63))
          ($n2 (iter-verify:check-mg "megalodon/iter/02_experience_hygiene.mg" 117))
          ($n3 (iter-verify:check-mg "megalodon/iter/03_loop_state_machine.mg" 46))
          ($n4 (iter-verify:check-mg "megalodon/iter/04_data_boundaries.mg" 48))
          ($n5 (iter-verify:check-mg "megalodon/iter/05_upstream_extensions.mg" 47))
          ($total (+ (+ (+ $n1 $n2) (+ $n3 $n4)) $n5))
          ($_ (iter-verify:assert-true "grand-total-321" (== $total 321)))
          ($_ (iter-verify:check-cadence-crosscheck))
          ($_ (iter-verify:check-upstream-crosscheck)))
     (println! (IterVerificationSuitePass
                 (megalodon-modules 5)
                 (theorems $total)
                 (cadence-crosschecks 12)
                 (upstream-crosschecks 14)
                 (document-axioms 0)
                 (admitted 0)
                 (aby 0)))))

!(iter-verify:main)
