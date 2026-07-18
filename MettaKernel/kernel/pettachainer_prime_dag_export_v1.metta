; A real PeTTaChainer producer fixture.  This file is loaded with its import
; root set to PeTTaChainer's own metta directory; it does not implement or
; imitate chaining.  The emitted proof-store nodes are untrusted input to the
; Prime replay fixture.

!(import! &self petta_chainer)
!(import! &self logic_configs/pln)

; The exporter is an untrusted adapter over PeTTaChainer's public proof-term
; representation.  Node identities are the proof subterms themselves, so
; repeated subproofs share one node after structural deduplication.
(= (pcd-is-rule-proof $proof)
   (if (is-expr $proof)
     (== (car-atom $proof) rule-proof)
     false))

(= (pcd-rule-name $proof)
   (car-atom (cdr-atom $proof)))

(= (pcd-rule-children $proof)
   (cdr-atom (cdr-atom $proof)))

; PeTTaChainer's forward proof store represents an applied rule as
; (rule-name proof-arguments ...).  A nested (rule-proof conjunction ...)
; is only the bundle used when a rule has several premises.
(= (pcd-is-rule-application $proof)
   (if (is-expr $proof)
     (not (pcd-is-rule-proof $proof))
     false))

(= (pcd-application-name $proof)
   (car-atom $proof))

(= (pcd-application-children $proof)
   (cdr-atom $proof))

(= (pcd-normalize-single-child $only)
   (if (pcd-is-rule-proof $only)
     (if (== (pcd-rule-name $only) conjunction)
       (pcd-rule-children $only)
       (cons $only ()))
     (cons $only ())))

(= (pcd-normalize-children $children)
   (if (== $children ())
     ()
     (if (== (cdr-atom $children) ())
       (pcd-normalize-single-child (car-atom $children))
       $children)))

(= (pcd-node-id $proof)
   (PeTTaProofNodeIdV1 $proof))

(= (pcd-child-refs ()) PCDNil)
(= (pcd-child-refs (cons $child $rest))
   (PCDCons
     (PeTTaProofRefV1 (pcd-node-id $child))
     (pcd-child-refs $rest)))

(= (pcd-native-child-nodes ()) ())
(= (pcd-native-child-nodes (cons $child $rest))
   (append
     (pcd-native-nodes $child)
     (pcd-native-child-nodes $rest)))

(= (pcd-native-nodes $proof)
   (if (pcd-is-rule-application $proof)
     (let $children
       (pcd-normalize-children (pcd-application-children $proof))
       (append
         (pcd-native-child-nodes $children)
         (cons
           (PeTTaProofNodeV1
             (pcd-node-id $proof)
             (PeTTaProofRuleV1 (pcd-application-name $proof))
             (pcd-child-refs $children))
           ())))
     (cons
       (PeTTaProofNodeV1
         (pcd-node-id $proof)
         (PeTTaProofLeafV1 $proof)
         PCDNil)
       ())))

(= (pcd-encode-node-list ()) PCDNil)
(= (pcd-encode-node-list (cons $node $rest))
   (PCDCons $node (pcd-encode-node-list $rest)))

(= (pcd-export-dag $proof)
   (PeTTaProofDAGV1
     "pettachainer-forward-proof-v1"
     (PeTTaProofRefV1 (pcd-node-id $proof))
     (pcd-encode-node-list
       (list_to_set (pcd-native-nodes $proof)))))

!(compileadd primeDagKb
   (: edgeAB (Edge A B) (STV 1.0 1.0)))
!(compileadd primeDagKb
   (: edgeToPath
      (Implication
        (Premises (Edge $x $y))
        (Conclusions (Path $x $y)))
      (STV 1.0 1.0)))
!(compileadd primeDagKb
   (: edgeToReach
      (Implication
        (Premises (Edge $x $y))
        (Conclusions (Reach $x $y)))
      (STV 1.0 1.0)))
!(compileadd primeDagKb
   (: pathReachWitness
      (Implication
        (Premises (Path $x $y) (Reach $x $y))
        (Conclusions (Witness $x $y)))
      (STV 1.0 1.0)))

!(forward-chain 50 primeDagKb)

!(println! "PETTACHAINER_PRIME_RESULT_BEGIN")
!(println!
   (collapse
     (match &kb
       ((Witness A B) (primeDagKb MAIN Nil) $proof $tv)
       (PeTTaForwardProofV1 $proof $tv))))
!(println! "PETTACHAINER_PRIME_RESULT_END")
!(println! "PETTACHAINER_PRIME_DAG_BEGIN")
!(let $dags
   (collapse
     (match &kb
       ((Witness A B) (primeDagKb MAIN Nil) $proof $tv)
       (pcd-export-dag (externalize-proof-structure $proof))))
   (println! (car-atom $dags)))
!(println! "PETTACHAINER_PRIME_DAG_END")
!(println! (PeTTaChainerPrimeProducerSummaryV1 1 1 0))
