; Build the shared runtime and prepared matcher with the showcase tool.
; Datalog computes demand; the MeTTa adapter preserves selected seed order
; and multiplicity before invoking the MeTTa CHR controller.
!(import! &self lang)

(= (compiler:select-seeds $needed LNil) LNil)
(= (compiler:select-seeds $needed (LCons (CompilerSeed $node $goal) $tail))
   (let $rest (compiler:select-seeds $needed $tail)
     (if (> (size-atom (collapse (match $needed (Need $node) present))) 0)
       (LCons $goal $rest) $rest)))

(= (compiler:value $value)
   (case (gslt:chr:decode-integer $value)
     (((Some $number) $number) (None (compiler:scalar $value)))))
(= (compiler:constraints LNil) ())
(= (compiler:constraints (LCons $head $tail))
   (let* (($decoded (compiler:constraint $head))
          ($rest (compiler:constraints $tail)))
     (cons-atom $decoded $rest)))

!(let* (($needed (new-space))
        ($demand (lang:run (lang:load Datalog) &self $needed (SourceFile "demand.dl"))))
   (case $demand
     (((LangCompleteV1 $facts)
        (let* (($begun (compiler:begin $needed))
               ($done (gslt:chr:advance 10000 20 $begun))
               ($part (gslt:chr:advance 25 20 $begun))
               ($again (gslt:chr:advance 9975 20 $part)))
          (let $_ (println! (DemandedNodes (collapse (match $needed (Need $node) $node))))
            (let $_ (println! (ExactResume (== $done $again)))
              (case (gslt:chr:result $done)
                (((ChrResult $phase
                    (PCollection "Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag" $store RNone)
                    $history $receipts)
                  (println! (SpecializedProgram $phase (compiler:constraints $store)
                    (HistoryEntries (gslt:automata:length $history)))))))))))
      ($other (println! (DemandNotComplete $other))))))
