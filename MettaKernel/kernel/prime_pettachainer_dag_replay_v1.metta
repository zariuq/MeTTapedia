; =============================================================================
; prime_pettachainer_dag_replay_v1.metta
;
; Replay a proof DAG emitted by the real PeTTaChainer forward proof store.
; The producer and this adapter are untrusted.  Authority comes only from the
; admitted rule package and the unchanged generic DAG checker.
; =============================================================================

!(import! &self prime_package_identity_v1)

; ---------- The small PLN-shaped checking package --------------------------
(= (ppd-A) (PApp "ppd.A" LNil))
(= (ppd-B) (PApp "ppd.B" LNil))
(= (ppd-Edge $left $right)
   (PApp "ppd.Edge" (pmcp-l2 $left $right)))
(= (ppd-Path $left $right)
   (PApp "ppd.Path" (pmcp-l2 $left $right)))
(= (ppd-Reach $left $right)
   (PApp "ppd.Reach" (pmcp-l2 $left $right)))
(= (ppd-Witness $left $right)
   (PApp "ppd.Witness" (pmcp-l2 $left $right)))
(= (ppd-Derives $formula)
   (PApp "ppd.Derives" (pmcp-l1 $formula)))

(= (ppd-rule-edge-ab)
   (GRule "ppd.edge-ab" LNil LNil
     (ppd-Derives (ppd-Edge (ppd-A) (ppd-B)))))
(= (ppd-rule-edge-to-path)
   (GRule "ppd.edge-to-path"
     (pmcp-l2 (Formal "left" 0) (Formal "right" 0))
     (pmcp-l1
       (ppd-Derives
         (ppd-Edge (FVar "left") (FVar "right"))))
     (ppd-Derives
       (ppd-Path (FVar "left") (FVar "right")))))
(= (ppd-rule-edge-to-reach)
   (GRule "ppd.edge-to-reach"
     (pmcp-l2 (Formal "left" 0) (Formal "right" 0))
     (pmcp-l1
       (ppd-Derives
         (ppd-Edge (FVar "left") (FVar "right"))))
     (ppd-Derives
       (ppd-Reach (FVar "left") (FVar "right")))))
(= (ppd-rule-path-reach-witness)
   (GRule "ppd.path-reach-witness"
     (pmcp-l2 (Formal "left" 0) (Formal "right" 0))
     (pmcp-l2
       (ppd-Derives
         (ppd-Path (FVar "left") (FVar "right")))
       (ppd-Derives
         (ppd-Reach (FVar "left") (FVar "right"))))
     (ppd-Derives
       (ppd-Witness (FVar "left") (FVar "right")))))

(= (ppd-rules)
   (pmcp-l4
     (ppd-rule-edge-ab)
     (ppd-rule-edge-to-path)
     (ppd-rule-edge-to-reach)
     (ppd-rule-path-reach-witness)))
(= (ppd-package) (pmcp-package-v1 (ppd-rules) LNil))
(= (ppd-cache)
   (case (pmcp-project-package (ppd-package))
     (((PMCPProjected $presentation) $presentation)
      ($_ PPDInvalidCache))))
(= (ppd-goal)
   (ppd-Derives (ppd-Witness (ppd-A) (ppd-B))))
(= (ppd-wrong-goal)
   (ppd-Derives (ppd-Path (ppd-A) (ppd-B))))

; ---------- Exact producer artifact ----------------------------------------
(= (ppd-id-edge-ab) (PeTTaProofNodeIdV1 edgeAB))
(= (ppd-id-edge-to-path)
   (PeTTaProofNodeIdV1 (edgeToPath edgeAB)))
(= (ppd-id-edge-to-reach)
   (PeTTaProofNodeIdV1 (edgeToReach edgeAB)))
(= (ppd-id-root)
   (PeTTaProofNodeIdV1
     (pathReachWitness
       (rule-proof conjunction
         (edgeToPath edgeAB) (edgeToReach edgeAB)))))

(= (ppd-ref $id) (PeTTaProofRefV1 $id))
(= (ppd-node-edge-ab)
   (PeTTaProofNodeV1
     (ppd-id-edge-ab) (PeTTaProofLeafV1 edgeAB) PCDNil))
(= (ppd-node-edge-to-path)
   (PeTTaProofNodeV1
     (ppd-id-edge-to-path)
     (PeTTaProofRuleV1 edgeToPath)
     (PCDCons (ppd-ref (ppd-id-edge-ab)) PCDNil)))
(= (ppd-node-edge-to-reach)
   (PeTTaProofNodeV1
     (ppd-id-edge-to-reach)
     (PeTTaProofRuleV1 edgeToReach)
     (PCDCons (ppd-ref (ppd-id-edge-ab)) PCDNil)))
(= (ppd-node-root)
   (PeTTaProofNodeV1
     (ppd-id-root)
     (PeTTaProofRuleV1 pathReachWitness)
     (PCDCons
       (ppd-ref (ppd-id-edge-to-path))
       (PCDCons (ppd-ref (ppd-id-edge-to-reach)) PCDNil))))

(= (ppd-canonical-nodes)
   (PCDCons (ppd-node-edge-ab)
     (PCDCons (ppd-node-edge-to-path)
       (PCDCons (ppd-node-edge-to-reach)
         (PCDCons (ppd-node-root) PCDNil)))))
(= (ppd-canonical-dag)
   (PeTTaProofDAGV1
     "pettachainer-forward-proof-v1"
     (ppd-ref (ppd-id-root))
     (ppd-canonical-nodes)))

; ---------- Fail-closed adapter to the generic DAG format -----------------
(= (ppd-map-refs $refs)
   (case $refs
     ((PCDNil (PPDRefsOK DrNil))
      ((PCDCons (PeTTaProofRefV1 $id) $rest)
        (case (ppd-map-refs $rest)
          (((PPDRefsOK $mapped)
            (PPDRefsOK (DrCons $id $mapped)))
           ($_ PPDAdapterRejected))))
      ($_ PPDAdapterRejected))))

(= (ppd-adapt-node $node)
   (case $node
     (((PeTTaProofNodeV1
          (PeTTaProofNodeIdV1 edgeAB)
          (PeTTaProofLeafV1 edgeAB) $children)
        (case (ppd-map-refs $children)
          (((PPDRefsOK $refs)
            (PPDNodeOK
              (GDNode (ppd-id-edge-ab)
                (GRuleInst "ppd.edge-ab" LNil) $refs)))
           ($_ PPDAdapterRejected))))
      ((PeTTaProofNodeV1
          (PeTTaProofNodeIdV1 (edgeToPath edgeAB))
          (PeTTaProofRuleV1 edgeToPath) $children)
        (case (ppd-map-refs $children)
          (((PPDRefsOK $refs)
            (PPDNodeOK
              (GDNode (ppd-id-edge-to-path)
                (GRuleInst "ppd.edge-to-path"
                  (pmcp-l2 (ppd-A) (ppd-B)))
                $refs)))
           ($_ PPDAdapterRejected))))
      ((PeTTaProofNodeV1
          (PeTTaProofNodeIdV1
            (edgeToReach edgeAB))
          (PeTTaProofRuleV1 edgeToReach) $children)
        (case (ppd-map-refs $children)
          (((PPDRefsOK $refs)
            (PPDNodeOK
              (GDNode (ppd-id-edge-to-reach)
                (GRuleInst "ppd.edge-to-reach"
                  (pmcp-l2 (ppd-A) (ppd-B)))
                $refs)))
           ($_ PPDAdapterRejected))))
      ((PeTTaProofNodeV1
          (PeTTaProofNodeIdV1
            (pathReachWitness
              (rule-proof conjunction
                (edgeToPath edgeAB) (edgeToReach edgeAB))))
          (PeTTaProofRuleV1 pathReachWitness) $children)
        (case (ppd-map-refs $children)
          (((PPDRefsOK $refs)
            (PPDNodeOK
              (GDNode (ppd-id-root)
                (GRuleInst "ppd.path-reach-witness"
                  (pmcp-l2 (ppd-A) (ppd-B)))
                $refs)))
           ($_ PPDAdapterRejected))))
      ($_ PPDAdapterRejected))))

(= (ppd-adapt-nodes $nodes)
   (case $nodes
     ((PCDNil (PPDNodesOK DnNil))
      ((PCDCons $node $rest)
        (case (ppd-adapt-node $node)
          (((PPDNodeOK $mapped-node)
            (case (ppd-adapt-nodes $rest)
              (((PPDNodesOK $mapped-rest)
                (PPDNodesOK (DnCons $mapped-node $mapped-rest)))
               ($_ PPDAdapterRejected))))
           ($_ PPDAdapterRejected))))
      ($_ PPDAdapterRejected))))

(= (ppd-adapt-dag $dag)
   (case $dag
     (((PeTTaProofDAGV1
          "pettachainer-forward-proof-v1"
          (PeTTaProofRefV1 $root-id) $nodes)
        (case (ppd-adapt-nodes $nodes)
          (((PPDNodesOK $mapped)
            (PPDAdaptedDAGV1 $root-id $mapped))
           ($_ PPDAdapterRejected))))
      ($_ PPDAdapterRejected))))

(= (ppd-check-with-package $package $dag $goal)
   (case (ppi-admit $package
           (case (pmcp-project-package $package)
             (((PMCPProjected $presentation) $presentation)
              ($_ PPDInvalidCache))))
     (((PrimePackageAdmissionV1 $identity $handle $stored $cache)
        (if (== $stored $package)
          (if (== $identity (ppi-package-identity $package))
            (case (ppd-adapt-dag $dag)
              (((PPDAdaptedDAGV1 $root-id $nodes)
                (gic-check-dag $cache $goal $root-id $nodes))
               ($_ False)))
            False)
          False))
      ($_ False))))
(= (ppd-replay $dag $goal)
   (ppd-check-with-package (ppd-package) $dag $goal))

; ---------- Authenticated subject and certificate -------------------------
(= (ppd-dag-digest $dag) (sha256 (repr $dag)))
(= (ppd-subject-material $package $dag $goal)
   (PrimePeTTaDAGSubjectMaterialV1
     "prime-pettachainer-dag-subject-v1"
     (ppi-package-identity $package)
     "prime"
     (PeTTaProofArtifactIdentityV1
       "pettachainer-forward-proof-v1" (ppd-dag-digest $dag))
     $goal))
(= (ppd-make-subject $package $dag $goal)
   (let $material (ppd-subject-material $package $dag $goal)
     (let $digest (sha256 (repr $material))
       (PrimePeTTaDAGSubjectRefV1
         $material $digest (SubjectLocalHandleV1 $digest)))))
(= (ppd-subject-valid $package $dag $goal $subject)
   (let $expected (ppd-make-subject $package $dag $goal)
     (== $subject $expected)))

(= (ppd-certificate-material $package $dag $goal)
   (PrimePeTTaDAGCertificateMaterialV1
     "prime-pettachainer-dag-certificate-v1"
     (ppd-make-subject $package $dag $goal)
     $dag $goal))
(= (ppd-make-certificate $package $dag $goal)
   (let $material (ppd-certificate-material $package $dag $goal)
     (PrimePeTTaDAGCertificateV1
       $material (sha256 (repr $material)))))
(= (ppd-certificate-valid-with-package $package $certificate)
   (case $certificate
     (((PrimePeTTaDAGCertificateV1
          (PrimePeTTaDAGCertificateMaterialV1
            "prime-pettachainer-dag-certificate-v1"
            $subject $dag $goal)
          $digest)
        (let $material (ppd-certificate-material $package $dag $goal)
          (if (== $digest (sha256 (repr $material)))
            (if (==
                  (PrimePeTTaDAGCertificateMaterialV1
                    "prime-pettachainer-dag-certificate-v1"
                    $subject $dag $goal)
                  $material)
              (if (ppd-subject-valid $package $dag $goal $subject)
                (ppd-check-with-package $package $dag $goal)
                False)
              False)
            False)))
      ($_ False))))
(= (ppd-certificate-valid $certificate)
   (ppd-certificate-valid-with-package (ppd-package) $certificate))
(= (ppd-canonical-certificate)
   (ppd-make-certificate
     (ppd-package) (ppd-canonical-dag) (ppd-goal)))
(= (ppd-certificate-bytes $certificate)
   (case $certificate
     (($resolved (repr $resolved)))))
(= (ppd-certificate-valid-bytes $bytes)
   (case (parse $bytes)
     (((Error $term $reason) False)
      ($parsed
        (if (== (repr $parsed) $bytes)
          (ppd-certificate-valid $parsed)
          False)))))

; ---------- Independent graph and authority mutations ---------------------
(= (ppd-root-with-children $children)
   (PeTTaProofNodeV1
     (ppd-id-root) (PeTTaProofRuleV1 pathReachWitness) $children))
(= (ppd-dag-with-nodes $root $nodes)
   (PeTTaProofDAGV1
     "pettachainer-forward-proof-v1" (ppd-ref $root) $nodes))

(= (ppd-missing-child-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-edge-ab)
       (PCDCons (ppd-node-edge-to-path)
         (PCDCons (ppd-node-edge-to-reach)
           (PCDCons
             (ppd-root-with-children
               (PCDCons
                 (ppd-ref (PeTTaProofNodeIdV1 missingProof))
                 (PCDCons (ppd-ref (ppd-id-edge-to-reach)) PCDNil)))
             PCDNil))))))
(= (ppd-swapped-children-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-edge-ab)
       (PCDCons (ppd-node-edge-to-path)
         (PCDCons (ppd-node-edge-to-reach)
           (PCDCons
             (ppd-root-with-children
               (PCDCons (ppd-ref (ppd-id-edge-to-reach))
                 (PCDCons (ppd-ref (ppd-id-edge-to-path)) PCDNil)))
             PCDNil))))))
(= (ppd-duplicate-id-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-edge-ab)
       (PCDCons (ppd-node-edge-ab)
         (PCDCons (ppd-node-edge-to-path)
           (PCDCons (ppd-node-edge-to-reach)
             (PCDCons (ppd-node-root) PCDNil)))))))
(= (ppd-forward-reference-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-root) (ppd-canonical-nodes))))
(= (ppd-cycle-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-edge-ab)
       (PCDCons (ppd-node-edge-to-path)
         (PCDCons (ppd-node-edge-to-reach)
           (PCDCons
             (ppd-root-with-children
               (PCDCons (ppd-ref (ppd-id-root))
                 (PCDCons (ppd-ref (ppd-id-edge-to-reach)) PCDNil)))
             PCDNil))))))
(= (ppd-mutated-rule-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons (ppd-node-edge-ab)
       (PCDCons
         (PeTTaProofNodeV1
           (ppd-id-edge-to-path)
           (PeTTaProofRuleV1 inventedRule)
           (PCDCons (ppd-ref (ppd-id-edge-ab)) PCDNil))
         (PCDCons (ppd-node-edge-to-reach)
           (PCDCons (ppd-node-root) PCDNil))))))
(= (ppd-wrong-root-dag)
   (ppd-dag-with-nodes (ppd-id-edge-to-path) (ppd-canonical-nodes)))
(= (ppd-extra-leaf-child-dag)
   (ppd-dag-with-nodes (ppd-id-root)
     (PCDCons
       (PeTTaProofNodeV1
         (ppd-id-edge-ab) (PeTTaProofLeafV1 edgeAB)
         (PCDCons (ppd-ref (ppd-id-edge-to-reach)) PCDNil))
       (PCDCons (ppd-node-edge-to-path)
         (PCDCons (ppd-node-edge-to-reach)
           (PCDCons (ppd-node-root) PCDNil))))))

(= (ppd-mutated-package)
   (pmcp-package-v1
     (pmcp-l4
       (ppd-rule-edge-ab)
       (ppd-rule-edge-to-path)
       (ppd-rule-edge-to-reach)
       (GRule "ppd.path-reach-witness"
         (pmcp-l2 (Formal "left" 0) (Formal "right" 0))
         (pmcp-l2
           (ppd-Derives
             (ppd-Path (FVar "left") (FVar "right")))
           (ppd-Derives
             (ppd-Reach (FVar "left") (FVar "right"))))
         (ppd-Derives
           (ppd-Edge (FVar "left") (FVar "right")))))
     LNil))

(= (ppd-forged-certificate-digest)
   (case (ppd-canonical-certificate)
     (((PrimePeTTaDAGCertificateV1 $material $digest)
        (PrimePeTTaDAGCertificateV1
          $material
          "0000000000000000000000000000000000000000000000000000000000000000")))))

; Evidence annotates an independently replayable certificate.  Its numerical
; value is never inspected by the proof checker and cannot repair a bad DAG.
(= (ppd-evidence-envelope $dag $goal $evidence)
   (PrimePLNEvidenceEnvelopeV1
     $evidence
     (ppd-make-certificate (ppd-package) $dag $goal)))
(= (ppd-evidence-envelope-valid $envelope)
   (case $envelope
     (((PrimePLNEvidenceEnvelopeV1
          (STV $strength $confidence) $certificate)
        (ppd-certificate-valid $certificate))
      ($_ False))))

; Universal positive claims require certified-complete coverage.  May
; witnesses remain usable under incomplete exploration, but the certificate
; itself must still replay.
(= (ppd-verdict-valid $verdict)
   (case $verdict
     (((PrimeDAGVerdictV1
          Must Complete Established $evidence $certificate)
        (ppd-certificate-valid $certificate))
      ((PrimeDAGVerdictV1
          May $coverage Established $evidence $certificate)
        (ppd-certificate-valid $certificate))
      ($_ False))))
(= (ppd-canonical-must-verdict)
   (PrimeDAGVerdictV1
     Must Complete Established (STV 1.0 1.0)
     (ppd-canonical-certificate)))
(= (ppd-forged-completeness-verdict)
   (PrimeDAGVerdictV1
     Must Complete Established (STV 1.0 1.0)
     (ppd-make-certificate
       (ppd-package) (ppd-mutated-rule-dag) (ppd-goal))))
(= (ppd-heuristic-must-verdict)
   (PrimeDAGVerdictV1
     Must HeuristicPruned Established (STV 1.0 1.0)
     (ppd-canonical-certificate)))
(= (ppd-incomplete-established-verdict)
   (PrimeDAGVerdictV1
     Must ResourceIncomplete Established (STV 1.0 1.0)
     (ppd-canonical-certificate)))

; A support claim is certified only by enough replayable witnesses.  The
; statistical annotation remains ledger data and contributes no witnesses.
(= (ppd-certificate-list-count PCDNil) 0)
(= (ppd-certificate-list-count (PCDCons $certificate $rest))
   (+ 1 (ppd-certificate-list-count $rest)))
(= (ppd-certificate-list-valid PCDNil) True)
(= (ppd-certificate-list-valid (PCDCons $certificate $rest))
   (if (ppd-certificate-valid $certificate)
     (ppd-certificate-list-valid $rest)
     False))
(= (ppd-support-claim-valid $claim)
   (case $claim
     (((PrimePatternSupportClaimV1
          $pattern $minimum $witnesses $statistics)
        (if (ppd-certificate-list-valid $witnesses)
          (<= $minimum (ppd-certificate-list-count $witnesses))
          False))
      ($_ False))))
(= (ppd-supported-pattern-claim)
   (PrimePatternSupportClaimV1
     (PathAndReach A B) 1
     (PCDCons (ppd-canonical-certificate) PCDNil)
     (STV 1.0 1.0)))
(= (ppd-unsupported-plausible-pattern-claim)
   (PrimePatternSupportClaimV1
     (PathAndReach A B) 2
     (PCDCons (ppd-canonical-certificate) PCDNil)
     (STV 0.999 0.999)))

; Structural metrics record the concrete benefit of the shared DAG.  Tree
; occurrences intentionally re-expand shared nodes; stored nodes do not.
(= (ppd-node-count PCDNil) 0)
(= (ppd-node-count (PCDCons $node $rest))
   (+ 1 (ppd-node-count $rest)))
(= (ppd-ref-count PCDNil) 0)
(= (ppd-ref-count (PCDCons $ref $rest))
   (+ 1 (ppd-ref-count $rest)))
(= (ppd-node-children
      (PeTTaProofNodeV1 $id $kind $children))
   $children)
(= (ppd-edge-count PCDNil) 0)
(= (ppd-edge-count (PCDCons $node $rest))
   (+ (ppd-ref-count (ppd-node-children $node))
      (ppd-edge-count $rest)))
(= (ppd-find-node $nodes $target)
   (case $nodes
     ((PCDNil PPDNoNode)
      ((PCDCons
          (PeTTaProofNodeV1 $id $kind $children) $rest)
        (if (== $id $target)
          (PPDFoundNode
            (PeTTaProofNodeV1 $id $kind $children))
          (ppd-find-node $rest $target)))
      ($_ PPDNoNode))))
(= (ppd-tree-occurrences-refs PCDNil $nodes) 0)
(= (ppd-tree-occurrences-refs
      (PCDCons (PeTTaProofRefV1 $id) $rest) $nodes)
   (+ (ppd-tree-occurrences-ref $id $nodes)
      (ppd-tree-occurrences-refs $rest $nodes)))
(= (ppd-tree-occurrences-ref $id $nodes)
   (case (ppd-find-node $nodes $id)
     (((PPDFoundNode $node)
        (+ 1
          (ppd-tree-occurrences-refs
            (ppd-node-children $node) $nodes)))
      ($_ 0))))
(= (ppd-canonical-metrics)
   (let $nodes (ppd-canonical-nodes)
     (let $node-count (ppd-node-count $nodes)
       (let $edge-count (ppd-edge-count $nodes)
         (PrimePeTTaChainerDAGMetricsV1
           $node-count
           $edge-count
           (- $edge-count (- $node-count 1))
           (ppd-tree-occurrences-ref (ppd-id-root) $nodes)
           "5/4")))))

; ---------- Positive and falsifying gates ----------------------------------
!(assertEqual (pmcp-package-valid (ppd-package)) True)
!(assertEqual (ppd-replay (ppd-canonical-dag) (ppd-goal)) True)
!(assertEqual (ppd-certificate-valid (ppd-canonical-certificate)) True)
!(assertEqual (ppd-replay (ppd-canonical-dag) (ppd-wrong-goal)) False)
!(assertEqual (ppd-replay (ppd-missing-child-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-swapped-children-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-duplicate-id-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-forward-reference-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-cycle-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-mutated-rule-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-wrong-root-dag) (ppd-goal)) False)
!(assertEqual (ppd-replay (ppd-extra-leaf-child-dag) (ppd-goal)) False)
!(assertEqual
   (ppd-certificate-valid-with-package
     (ppd-mutated-package) (ppd-canonical-certificate))
   False)
!(assertEqual
   (ppd-certificate-valid (ppd-forged-certificate-digest))
   False)
!(assertEqual
   (== (ppd-dag-digest (ppd-canonical-dag))
       (ppd-dag-digest (ppd-swapped-children-dag)))
   False)
!(assertEqual
   (ppd-evidence-envelope-valid
     (ppd-evidence-envelope
       (ppd-canonical-dag) (ppd-goal) (STV 1.0 1.0)))
   True)
!(assertEqual
   (ppd-evidence-envelope-valid
     (ppd-evidence-envelope
       (ppd-mutated-rule-dag) (ppd-goal) (STV 1.0 1.0)))
   False)
!(assertEqual
   (ppd-support-claim-valid (ppd-supported-pattern-claim))
   True)
!(assertEqual
   (ppd-support-claim-valid
     (ppd-unsupported-plausible-pattern-claim))
   False)
!(assertEqual
   (ppd-canonical-metrics)
   (PrimePeTTaChainerDAGMetricsV1 4 4 1 5 "5/4"))
!(assertEqual
   (ppd-certificate-valid-bytes
     (ppd-certificate-bytes (ppd-canonical-certificate)))
   True)
!(assertEqual
   (ppd-certificate-valid-bytes "(PrimePeTTaDAGCertificateV1")
   False)
!(assertEqual
   (ppd-certificate-valid-bytes
     (str:concat " "
       (ppd-certificate-bytes (ppd-canonical-certificate))))
   False)
!(assertEqual
   (ppd-verdict-valid (ppd-canonical-must-verdict))
   True)
!(assertEqual
   (ppd-verdict-valid (ppd-forged-completeness-verdict))
   False)
!(assertEqual
   (ppd-verdict-valid (ppd-heuristic-must-verdict))
   False)
!(assertEqual
   (ppd-verdict-valid (ppd-incomplete-established-verdict))
   False)

!(println! "PRIME_PETTACHAINER_DAG_BEGIN")
!(println! (ppd-canonical-dag))
!(println! "PRIME_PETTACHAINER_DAG_END")
!(println! "PRIME_PETTACHAINER_DAG_DIGEST_BEGIN")
!(println! (ppd-dag-digest (ppd-canonical-dag)))
!(println! "PRIME_PETTACHAINER_DAG_DIGEST_END")
!(println! "PRIME_PETTACHAINER_CERTIFICATE_BEGIN")
!(println! (ppd-certificate-bytes (ppd-canonical-certificate)))
!(println! "PRIME_PETTACHAINER_CERTIFICATE_END")
!(println! (ppd-canonical-metrics))
!(println! (PrimePeTTaChainerDAGReplaySummaryV1 27 27 0))
