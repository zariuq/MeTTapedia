!(import! &self metamath_native_source_calculus_v0)

(= (mm-native-suite:swap-first-two
      (GProof $rule
        (PrCons $first (PrCons $second $rest))))
   (GProof $rule
     (PrCons $second (PrCons $first $rest))))

(= (mm-native-suite:drop-last-child
      (GProof $rule $children))
   (GProof $rule (mm-native-suite:drop-last $children)))

(= (mm-native-suite:drop-last (PrCons $last PrNil)) PrNil)
(= (mm-native-suite:drop-last
      (PrCons $head (PrCons $next $rest)))
   (PrCons $head
     (mm-native-suite:drop-last (PrCons $next $rest))))

(= (mm-native-suite:wrong-source-goal
      (PApp "__metamath.SourceProves"
        (LCons $identity (LCons $formula LNil))))
   (PApp "__metamath.SourceProves"
     (LCons
       (PApp "__metamath.SourceIdentity"
         (LCons
           (PApp "__metamath.String"
             (LCons (PApp "different-source" LNil) LNil))
           (LCons
             (PApp "__metamath.String"
               (LCons (PApp "different-digest" LNil) LNil))
             LNil)))
       (LCons $formula LNil))))

(= (mm-native-suite:run $result)
   (case $result
     (((MMNativeSourceSlice $source $goal $proof $label)
       (MMNativeSourceSuite
         (gslt-source-check-v1 $source $goal $proof)
         (gslt-source-check-v1 $source $goal
           (mm-native-suite:swap-first-two $proof))
         (gslt-source-check-v1 $source $goal
           (mm-native-suite:drop-last-child $proof))
         (gslt-source-check-v1 $source
           (mm-native-suite:wrong-source-goal $goal) $proof)))
      ($error $error))))
