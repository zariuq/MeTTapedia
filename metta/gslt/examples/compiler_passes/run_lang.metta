; Both passes through the public lang library: Datalog computes demand,
; then ordinary ground CHR source folds the demanded part of the dataflow
; program. Seeds keep the program's order and multiplicity. Dataflow names
; are strings; the CHR package reads them directly as guest atom names.
!(import! &self lang)

(= (compiler:needed $needed $node)
   (> (size-atom (collapse (match $needed (Need $node) present))) 0))
(= (compiler:seed $needed $row)
   (case $row
     (((Add $node $left $right)
        (if (compiler:needed $needed $node)
          (Seed (add $node $left $right)) Skip))
      ((Constant $node $value)
        (if (compiler:needed $needed $node) (Seed (constant $node $value)) Skip))
      ((Input $node)
        (if (compiler:needed $needed $node) (Seed (input $node)) Skip))
      ($other Skip))))
(= (compiler:post $work $needed $rows)
   (case $rows
     ((() Posted)
      ((cons $row $rest)
        (case (compiler:seed $needed $row)
          (((Seed $constraint) (let $_ (add-atom $work $constraint) (compiler:post $work $needed $rest)))
           (Skip (compiler:post $work $needed $rest))))))))
(= (compiler:finish $pending $left)
   (if (== $left 0) Exhausted
     (let $next (lang:resume $pending 1000)
       (case $next
         (((LangCompleteV1 $store) $next)
          ((LangPendingV1 $cursor) (compiler:finish $pending (- $left 1)))
          ($other $other))))))

!(let* (($needed (new-space))
        ($demand (lang:run (lang:load Datalog) &self $needed (SourceFile "demand.dl")))
        ($program (collapse (get-atoms &self)))
        ($work (new-space))
        ($_ (compiler:post $work $needed $program))
        ($private (lang:eval (lang:load CHR) $work (SourceFile "constant_fold.chr")))
        ($resumed (new-space))
        ($_ (compiler:post $resumed $needed $program))
        ($pending (lang:run (lang:load CHR) $resumed $resumed 0 (SourceFile "constant_fold.chr")))
        ($stepped (compiler:finish $pending 100000))
        ($folded (lang:run (lang:load CHR) $work (SourceFile "constant_fold.chr"))))
   (case ($demand $folded)
     ((((LangCompleteV1 $facts) (LangCompleteV1 $store))
        (let* (($_ (println! (DemandedNodes (collapse (match $needed (Need $node) $node)))))
               ($_ (println! (PrivateAgrees (== $private $folded))))
               ($_ (println! (ResumedAgrees (== $stepped $folded))))
               ($_ (println! (ResumedSpace (collapse (get-atoms $resumed))))))
          (println! (SpecializedProgram (collapse (get-atoms $work))))))
      ($other (println! (ShowcaseNotComplete $other))))))
