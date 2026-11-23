(= (equation-context:check $name $actual $expected)
   (println! (EquationContextControl $name (== $actual $expected))))

(= (equation-context:control $name)
   (let* (($a (PApp "a" LNil))
          ($b (PApp "b" LNil))
          ($c (PApp "c" LNil))
          ($children (LCons $a (LCons $a LNil)))
          ($subject (PApp "pair" $children))
          ($outb (PApp "out" (LCons $b LNil)))
          ($outc (PApp "out" (LCons $c LNil)))
          ($equations (LCons
            (Equation "choose-out" LNil
              (LCons (RelationQuery "choose" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil)
              (FVar "x") (PApp "out" (LCons (FVar "y") LNil))) LNil))
          ($rows (LCons (ProviderRow "choose" (LCons $a (LCons $b LNil)))
            (LCons (ProviderRow "choose" (LCons $a (LCons $b LNil)))
              (LCons (ProviderRow "choose" (LCons $a (LCons $c LNil))) LNil))))
          ($initial (LCons (Binding "x" $a) LNil))
          ($finalb (LCons (Binding "y" $b) $initial))
          ($finalc (LCons (Binding "y" $c) $initial))
          ($atomicb (EqInstance 0 EqForward $initial (LCons 1 LNil) $finalb $outb))
          ($atomicc (EqInstance 0 EqForward $initial (LCons 2 LNil) $finalc $outc))
          ($firstWhole (PApp "pair" (LCons $a (LCons $outb LNil))))
          ($secondWhole (PApp "pair" (LCons $outc (LCons $outb LNil))))
          ($first (EqAt (LCons 1 LNil) $atomicb $firstWhole))
          ($second (EqAt (LCons 0 LNil) $atomicc $secondWhole)))
     (case $name
       ((split-first
         (equation-context:check $name (gslt:equation-context:split 0 $children)
           (Some (EqSite LNil $a (LCons $a LNil)))))
        (split-second
         (equation-context:check $name (gslt:equation-context:split 1 $children)
           (Some (EqSite (LCons $a LNil) $a LNil))))
        (split-future
         (equation-context:check $name (gslt:equation-context:split 2 $children) None))
        (focus-root
         (equation-context:check $name (gslt:equation-context:focus LNil $subject) (Some $subject)))
        (focus-first
         (equation-context:check $name (gslt:equation-context:focus (LCons 0 LNil) $subject) (Some $a)))
        (focus-second
         (equation-context:check $name (gslt:equation-context:focus (LCons 1 LNil) $subject) (Some $a)))
        (focus-future
         (equation-context:check $name (gslt:equation-context:focus (LCons 2 LNil) $subject) None))
        (focus-below-leaf
         (equation-context:check $name (gslt:equation-context:focus (LCons 1 (LCons 0 LNil)) $subject) None))
        (replace-first
         (equation-context:check $name (gslt:equation-context:replace (LCons 0 LNil) $subject $outb)
           (Some (PApp "pair" (LCons $outb (LCons $a LNil))))))
        (replace-second
         (equation-context:check $name (gslt:equation-context:replace (LCons 1 LNil) $subject $outb)
           (Some $firstWhole)))
        (replace-future
         (equation-context:check $name (gslt:equation-context:replace (LCons 2 LNil) $subject $outb) None))
        (positioned-receipt
         (equation-context:check $name (gslt:equation-context:validate $equations $rows $subject $first)
           (Some $firstWhole)))
        (wrong-sibling-whole
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $subject
             (EqAt (LCons 1 LNil) $atomicb (PApp "pair" (LCons $outb (LCons $a LNil))))) None))
        (future-site
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $subject (EqAt (LCons 2 LNil) $atomicb $firstWhole)) None))
        (forged-local-target
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $subject
             (EqAt (LCons 1 LNil)
               (EqInstance 0 EqForward $initial (LCons 1 LNil) $finalb $outc)
               (PApp "pair" (LCons $a (LCons $outc LNil))))) None))
        (empty-path
         (equation-context:check $name (gslt:equation-context:replay $equations $rows $subject LNil) (Some $subject)))
        (two-step-path
         (equation-context:check $name
           (gslt:equation-context:replay $equations $rows $subject (LCons $first (LCons $second LNil)))
           (Some $secondWhole)))
        (wrong-preceding-endpoint
         (equation-context:check $name
           (gslt:equation-context:replay $equations $rows $subject (LCons $second (LCons $first LNil))) None))
        (malformed-receipt
         (equation-context:check $name (gslt:equation-context:validate $equations $rows $subject Forged) None))
        (malformed-path
         (equation-context:check $name (gslt:equation-context:replay $equations $rows $subject Forged) None))))))

!(equation-context:control split-first)
!(equation-context:control split-second)
!(equation-context:control split-future)
!(equation-context:control focus-root)
!(equation-context:control focus-first)
!(equation-context:control focus-second)
!(equation-context:control focus-future)
!(equation-context:control focus-below-leaf)
!(equation-context:control replace-first)
!(equation-context:control replace-second)
!(equation-context:control replace-future)
!(equation-context:control positioned-receipt)
!(equation-context:control wrong-sibling-whole)
!(equation-context:control future-site)
!(equation-context:control forged-local-target)
!(equation-context:control empty-path)
!(equation-context:control two-step-path)
!(equation-context:control wrong-preceding-endpoint)
!(equation-context:control malformed-receipt)
!(equation-context:control malformed-path)

(= (equation-modulo:control $name)
   (let* (($a (PApp "a" LNil))
          ($b (PApp "b" LNil))
          ($c (PApp "c" LNil))
          ($d (PApp "d" LNil))
          ($equations (LCons (Equation "ab" LNil LNil $a $b)
            (LCons (Equation "cd" LNil LNil $c $d) LNil)))
          ($rule (RewriteRule "bc" RetainedContext LNil $b $c))
          ($rewrites (LCons $rule (LCons $rule LNil)))
          ($language (GSLTLanguageDefWireV1 "modulo" RetainedTypes RetainedTerms $equations $rewrites))
          ($view (GSLTLanguageDefWireV1 "modulo" RetainedTypes RetainedTerms LNil $rewrites))
          ($before (LCons (EqAt LNil (EqInstance 0 EqForward LNil LNil LNil $b) $b) LNil))
          ($after (LCons (EqAt LNil (EqInstance 1 EqForward LNil LNil LNil $d) $d) LNil))
          ($expected (LCons $d (LCons $d LNil))))
     (case $name
       ((modulo-view-metadata
         (equation-context:check $name (gslt:equation-context:directed-view $language) $view))
        (modulo-view-malformed
         (equation-context:check $name (gslt:equation-context:directed-view Forged) None))
        (modulo-top-duplicates
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language LNil 1 $a $before $after) $expected))
        (modulo-bottom-duplicates
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchBottomUp $language LNil 1 $a $before $after) $expected))
        (modulo-after-result-filter
         (equation-context:check $name
           (gslt:equation-context:after-results $equations LNil $after (LCons $c (LCons $c (LCons $b LNil)))) $expected))
        (modulo-no-equation-permission
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown
             (GSLTLanguageDefWireV1 "modulo" RetainedTypes RetainedTerms $equations LNil)
             LNil 1 $a $before LNil) LNil))
        (modulo-before-future-row
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language LNil 1 $a
             (LCons (EqAt LNil (EqInstance 2 EqForward LNil LNil LNil $b) $b) LNil) $after) LNil))
        (modulo-after-forged-target
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language LNil 1 $a $before
             (LCons (EqAt LNil (EqInstance 1 EqForward LNil LNil LNil $d) $a) LNil)) LNil))
        (modulo-unauthorized-child
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language LNil 1
             (PApp "pair" (LCons $a LNil))
             (LCons (EqAt (LCons 0 LNil) (EqInstance 0 EqForward LNil LNil LNil $b)
               (PApp "pair" (LCons $b LNil))) LNil) LNil) LNil))
        (modulo-zero-depth
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language LNil 0 $a $before $after) LNil))
        (modulo-malformed-language
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown Forged LNil 1 $a $before $after) LNil))))))

!(equation-modulo:control modulo-view-metadata)
!(equation-modulo:control modulo-view-malformed)
!(equation-modulo:control modulo-top-duplicates)
!(equation-modulo:control modulo-bottom-duplicates)
!(equation-modulo:control modulo-after-result-filter)
!(equation-modulo:control modulo-no-equation-permission)
!(equation-modulo:control modulo-before-future-row)
!(equation-modulo:control modulo-after-forged-target)
!(equation-modulo:control modulo-unauthorized-child)
!(equation-modulo:control modulo-zero-depth)
!(equation-modulo:control modulo-malformed-language)

; A checked reversal retains the original oriented conditional witness.
; The equation discards x, so reverse matching alone cannot recover x=a.
(= (equation-signed:control $name)
   (let* (($a (PApp "a" LNil))
          ($b (PApp "b" LNil))
          ($c (PApp "c" LNil))
          ($d (PApp "d" LNil))
          ($predecessor (PApp "drop" (LCons $a (LCons $b LNil))))
          ($forged (PApp "drop" (LCons $c (LCons $b LNil))))
          ($equation (Equation "discard-left" LNil
            (LCons (RelationQuery "allowed" (LCons (FVar "y") LNil)) LNil)
            (PApp "drop" (LCons (FVar "x") (LCons (FVar "y") LNil))) (FVar "y")))
          ($equations (LCons $equation LNil))
          ($rows (LCons (ProviderRow "allowed" (LCons $b LNil))
            (LCons (ProviderRow "allowed" (LCons $b LNil))
              (LCons (ProviderRow "allowed" (LCons $c LNil)) LNil))))
          ($seed (LCons (Binding "y" $b) (LCons (Binding "x" $a) LNil)))
          ($atomic (EqInstance 0 EqForward $seed (LCons 0 LNil) $seed $b))
          ($original (EqAt LNil $atomic $b))
          ($previous (EqPrevious $predecessor $original))
          ($nextPredecessor (PApp "drop" (LCons $d (LCons $c LNil))))
          ($nextSeed (LCons (Binding "y" $c) (LCons (Binding "x" $d) LNil)))
          ($nextOriginal (EqAt LNil (EqInstance 0 EqForward $nextSeed (LCons 0 LNil) $nextSeed $c) $c))
          ($after (LCons (EqPrevious $nextPredecessor $nextOriginal) LNil))
          ($rule (RewriteRule "drop-to-c" RetainedContext LNil $predecessor $c))
          ($language (GSLTLanguageDefWireV1 "signed" RetainedTypes RetainedTerms $equations
            (LCons $rule (LCons $rule LNil))))
          ($expected (LCons $nextPredecessor (LCons $nextPredecessor LNil))))
     (case $name
       ((signed-original-forward
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $predecessor $original) (Some $b)))
        (signed-query-occurrence
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b
             (EqPrevious $predecessor (EqAt LNil (EqInstance 0 EqForward $seed (LCons 1 LNil) $seed $b) $b)))
           (Some $predecessor)))
        (signed-previous-discarded
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b $previous) (Some $predecessor)))
        (signed-reverse-matching-loses-discarded
         (let* (($reverseSeed (LCons (Binding "y" $b) LNil))
                ($unrecovered (PApp "drop" (LCons (FVar "x") (LCons $b LNil)))))
           (equation-context:check $name
             (gslt:equation:apply-row 0 EqReverse $equation $rows $b)
             (LCons (EqInstance 0 EqReverse $reverseSeed (LCons 0 LNil) $reverseSeed $unrecovered)
               (LCons (EqInstance 0 EqReverse $reverseSeed (LCons 1 LNil) $reverseSeed $unrecovered) LNil)))))
        (signed-roundtrip
         (equation-context:check $name
           (gslt:equation-context:replay $equations $rows $predecessor (LCons $original (LCons $previous LNil)))
           (Some $predecessor)))
        (signed-opposite-roundtrip
         (equation-context:check $name
           (gslt:equation-context:replay $equations $rows $b (LCons $previous (LCons $original LNil))) (Some $b)))
        (signed-forged-predecessor
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b (EqPrevious $forged $original)) None))
        (signed-wrong-current-endpoint
         (equation-context:check $name (gslt:equation-context:validate $equations $rows $c $previous) None))
        (signed-forged-atomic-target
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $c
             (EqPrevious $predecessor (EqAt LNil (EqInstance 0 EqForward $seed (LCons 0 LNil) $seed $c) $c))) None))
        (signed-forged-whole-target
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $c (EqPrevious $predecessor (EqAt LNil $atomic $c))) None))
        (signed-future-query-choice
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b
             (EqPrevious $predecessor (EqAt LNil (EqInstance 0 EqForward $seed (LCons 2 LNil) $seed $b) $b))) None))
        (signed-missing-provider
         (equation-context:check $name (gslt:equation-context:validate $equations LNil $b $previous) None))
        (signed-malformed-original
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b (EqPrevious $predecessor Forged)) None))
        (signed-nested-previous
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b (EqPrevious $predecessor $previous)) None))
        (signed-future-equation
         (equation-context:check $name
           (gslt:equation-context:validate $equations $rows $b
             (EqPrevious $predecessor (EqAt LNil (EqInstance 1 EqForward $seed (LCons 0 LNil) $seed $b) $b))) None))
        (signed-frontier-top
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language $rows 1 $b (LCons $previous LNil) $after) $expected))
        (signed-frontier-bottom
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchBottomUp $language $rows 1 $b (LCons $previous LNil) $after) $expected))
        (signed-after-filter
         (equation-context:check $name
           (gslt:equation-context:after-results $equations $rows $after (LCons $c (LCons $b (LCons $c LNil)))) $expected))
        (signed-wrong-predecessor-frontier
         (equation-context:check $name
           (gslt:equation-context:witnessed-reducts MatchTopDown $language $rows 1 $b
             (LCons (EqPrevious $forged $original) LNil) $after) LNil))))))

!(equation-signed:control signed-original-forward)
!(equation-signed:control signed-query-occurrence)
!(equation-signed:control signed-previous-discarded)
!(equation-signed:control signed-reverse-matching-loses-discarded)
!(equation-signed:control signed-roundtrip)
!(equation-signed:control signed-opposite-roundtrip)
!(equation-signed:control signed-forged-predecessor)
!(equation-signed:control signed-wrong-current-endpoint)
!(equation-signed:control signed-forged-atomic-target)
!(equation-signed:control signed-forged-whole-target)
!(equation-signed:control signed-future-query-choice)
!(equation-signed:control signed-missing-provider)
!(equation-signed:control signed-malformed-original)
!(equation-signed:control signed-nested-previous)
!(equation-signed:control signed-future-equation)
!(equation-signed:control signed-frontier-top)
!(equation-signed:control signed-frontier-bottom)
!(equation-signed:control signed-after-filter)
!(equation-signed:control signed-wrong-predecessor-frontier)

(= (equation-acquisition:check $name $actual $expected)
   (println! (EquationAcquisitionControl $name (== $actual $expected))))

(= (equation-acquisition:control $name)
   (let* (($a (PApp "a" LNil)) ($b (PApp "b" LNil)) ($c (PApp "c" LNil))
          ($outb (PApp "out" (LCons $b LNil))) ($outc (PApp "out" (LCons $c LNil)))
          ($pair (PApp "pair" (LCons $a (LCons $a LNil))))
          ($firstWhole (PApp "pair" (LCons $a (LCons $outb LNil))))
          ($secondWhole (PApp "pair" (LCons $outc (LCons $outb LNil))))
          ($row (Equation "choose-out" LNil
            (LCons (RelationQuery "choose" (LCons (FVar "x") (LCons (FVar "y") LNil))) LNil)
            (FVar "x") (PApp "out" (LCons (FVar "y") LNil))))
          ($equations (LCons $row LNil))
          ($rows (LCons (ProviderRow "choose" (LCons $a (LCons $b LNil)))
            (LCons (ProviderRow "choose" (LCons $a (LCons $b LNil)))
              (LCons (ProviderRow "choose" (LCons $a (LCons $c LNil))) LNil))))
          ($seed (LCons (Binding "x" $a) LNil))
          ($finalb (LCons (Binding "y" $b) $seed)) ($finalc (LCons (Binding "y" $c) $seed))
          ($atomic0 (EqInstance 0 EqForward $seed (LCons 0 LNil) $finalb $outb))
          ($atomic1 (EqInstance 0 EqForward $seed (LCons 1 LNil) $finalb $outb))
          ($atomic2 (EqInstance 0 EqForward $seed (LCons 2 LNil) $finalc $outc))
          ($root0 (EqAt LNil $atomic0 $outb)) ($root1 (EqAt LNil $atomic1 $outb))
          ($root2 (EqAt LNil $atomic2 $outc))
          ($first (EqAt (LCons 1 LNil) $atomic0 $firstWhole))
          ($second (EqAt (LCons 0 LNil) $atomic2 $secondWhole))
          ($discardRow (Equation "discard-left" LNil
            (LCons (RelationQuery "allowed" (LCons (FVar "y") LNil)) LNil)
            (PApp "drop" (LCons (FVar "x") (LCons (FVar "y") LNil))) (FVar "y")))
          ($discardEquations (LCons $discardRow LNil))
          ($discardRows (LCons (ProviderRow "allowed" (LCons $b LNil))
            (LCons (ProviderRow "allowed" (LCons $b LNil)) LNil)))
          ($predecessor (PApp "drop" (LCons $a (LCons $b LNil))))
          ($discardSeed (LCons (Binding "y" $b) (LCons (Binding "x" $a) LNil)))
          ($discardAtomic (EqInstance 0 EqForward $discardSeed (LCons 0 LNil) $discardSeed $b))
          ($discardReceipt (EqAt LNil $discardAtomic $b))
          ($previousReceipt (EqPrevious $predecessor $discardReceipt)))
     (case $name
       ((frontier-query-duplicates
         (equation-acquisition:check $name (gslt:equation-context:frontier $equations $rows $a)
           (LCons $root0 (LCons $root1 (LCons $root2 LNil)))))
        (frontier-preorder-positions
         (equation-acquisition:check $name (gslt:equation-context:frontier $equations $rows $pair)
           (LCons (EqAt (LCons 0 LNil) $atomic0 (PApp "pair" (LCons $outb (LCons $a LNil))))
             (LCons (EqAt (LCons 0 LNil) $atomic1 (PApp "pair" (LCons $outb (LCons $a LNil))))
               (LCons (EqAt (LCons 0 LNil) $atomic2 (PApp "pair" (LCons $outc (LCons $a LNil))))
                 (LCons $first
                   (LCons (EqAt (LCons 1 LNil) $atomic1 $firstWhole)
                     (LCons (EqAt (LCons 1 LNil) $atomic2 (PApp "pair" (LCons $a (LCons $outc LNil)))) LNil))))))))
        (frontier-empty
         (equation-acquisition:check $name (gslt:equation-context:frontier LNil LNil $pair) LNil))
        (frontier-declaration-duplicates
         (equation-acquisition:check $name
           (gslt:equation-context:frontier (LCons $row $equations) $rows $a)
           (LCons $root0 (LCons $root1 (LCons $root2
             (LCons (EqAt LNil (EqInstance 1 EqForward $seed (LCons 0 LNil) $finalb $outb) $outb)
               (LCons (EqAt LNil (EqInstance 1 EqForward $seed (LCons 1 LNil) $finalb $outb) $outb)
                 (LCons (EqAt LNil (EqInstance 1 EqForward $seed (LCons 2 LNil) $finalc $outc) $outc) LNil))))))))
        (first-query-branch
         (equation-acquisition:check $name
           (gslt:equation-context:find-target (LCons $root0 (LCons $root1 (LCons $root2 LNil))) $outb) (Some $root0)))
        (distinct-query-branch
         (equation-acquisition:check $name
           (gslt:equation-context:find-target (LCons $root0 (LCons $root1 (LCons $root2 LNil))) $outc) (Some $root2)))
        (absent-target
         (equation-acquisition:check $name
           (gslt:equation-context:find-target (LCons $root0 (LCons $root1 LNil)) $c) None))
        (signed-forward
         (equation-acquisition:check $name (gslt:equation-context:find-signed $equations $rows $a $outb) (Some $root0)))
        (signed-original-predecessor
         (equation-acquisition:check $name
           (gslt:equation-context:find-signed $discardEquations $discardRows $b $predecessor) (Some $previousReceipt)))
        (signed-absent-edge
         (equation-acquisition:check $name (gslt:equation-context:find-signed $discardEquations $discardRows $b $c) None))
        (empty-path-reflexivity
         (equation-acquisition:check $name (gslt:equation-context:acquire-path $equations $rows $a LNil) (Some LNil)))
        (one-edge-path
         (equation-acquisition:check $name
           (gslt:equation-context:acquire-path $equations $rows $a (LCons $outb LNil)) (Some (LCons $root0 LNil))))
        (contextual-two-edge-path
         (equation-acquisition:check $name
           (gslt:equation-context:acquire-path $equations $rows $pair (LCons $firstWhole (LCons $secondWhole LNil)))
           (Some (LCons $first (LCons $second LNil)))))
        (conditional-previous-roundtrip
         (equation-acquisition:check $name
           (gslt:equation-context:acquire-path $discardEquations $discardRows $predecessor (LCons $b (LCons $predecessor LNil)))
           (Some (LCons $discardReceipt (LCons $previousReceipt LNil)))))
        (failed-later-edge
         (equation-acquisition:check $name
           (gslt:equation-context:acquire-path $equations $rows $a (LCons $outb (LCons $c LNil))) None))
        (unsupported-single-edge
         (equation-acquisition:check $name (gslt:equation-context:acquire-path $equations $rows $a (LCons $c LNil)) None))
        (future-context-position
         (equation-acquisition:check $name
           (gslt:equation-context:lift (LCons 2 LNil) $pair (LCons $atomic0 LNil)) LNil))
        (conditional-predecessor-refused
         (equation-acquisition:check $name
           (gslt:equation-context:find-signed $discardEquations $discardRows $b
             (PApp "drop" (LCons $a (LCons $c LNil)))) None))
        (unlicensed-sibling-change
         (equation-acquisition:check $name
           (gslt:equation-context:acquire-path $equations $rows $pair
             (LCons (PApp "pair" (LCons $c (LCons $outb LNil))) LNil)) None))
        (unsupported-reflexive-edge
         (equation-acquisition:check $name (gslt:equation-context:acquire-path $equations $rows $a (LCons $a LNil)) None))))))

!(equation-acquisition:control frontier-query-duplicates)
!(equation-acquisition:control frontier-preorder-positions)
!(equation-acquisition:control frontier-empty)
!(equation-acquisition:control frontier-declaration-duplicates)
!(equation-acquisition:control first-query-branch)
!(equation-acquisition:control distinct-query-branch)
!(equation-acquisition:control absent-target)
!(equation-acquisition:control signed-forward)
!(equation-acquisition:control signed-original-predecessor)
!(equation-acquisition:control signed-absent-edge)
!(equation-acquisition:control empty-path-reflexivity)
!(equation-acquisition:control one-edge-path)
!(equation-acquisition:control contextual-two-edge-path)
!(equation-acquisition:control conditional-previous-roundtrip)
!(equation-acquisition:control failed-later-edge)
!(equation-acquisition:control unsupported-single-edge)
!(equation-acquisition:control future-context-position)
!(equation-acquisition:control conditional-predecessor-refused)
!(equation-acquisition:control unlicensed-sibling-change)
!(equation-acquisition:control unsupported-reflexive-edge)

(= (equation-acquired-frontier:check $name $actual $expected)
   (println! (EquationContextControl $name (== $actual $expected))))

(= (equation-acquired-frontier:control $name)
   (let* (($a (PApp "a" LNil)) ($b (PApp "b" LNil))
          ($c (PApp "c" LNil)) ($d (PApp "d" LNil)) ($e (PApp "e" LNil))
          ($equations (LCons (Equation "ab" LNil LNil $a $b)
            (LCons (Equation "cd" LNil LNil $c $d) LNil)))
          ($rule (RewriteRule "bc" RetainedContext LNil $b $c))
          ($rewrites (LCons $rule (LCons $rule LNil)))
          ($language (GSLTLanguageDefWireV1 "acquired" RetainedTypes RetainedTerms $equations $rewrites))
          ($before (LCons $b LNil)) ($after (LCons $d LNil))
          ($expected (LCons $d (LCons $d LNil)))
          ($predecessor (PApp "drop" (LCons $a (LCons $b LNil))))
          ($nextPredecessor (PApp "drop" (LCons $d (LCons $c LNil))))
          ($conditional (Equation "discard-left" LNil
            (LCons (RelationQuery "allowed" (LCons (FVar "y") LNil)) LNil)
            (PApp "drop" (LCons (FVar "x") (LCons (FVar "y") LNil))) (FVar "y")))
          ($conditionalEquations (LCons $conditional LNil))
          ($rows (LCons (ProviderRow "allowed" (LCons $b LNil))
            (LCons (ProviderRow "allowed" (LCons $b LNil))
              (LCons (ProviderRow "allowed" (LCons $c LNil)) LNil))))
          ($conditionalRule (RewriteRule "drop-to-c" RetainedContext LNil $predecessor $c))
          ($conditionalLanguage (GSLTLanguageDefWireV1 "conditional-acquired" RetainedTypes RetainedTerms
            $conditionalEquations (LCons $conditionalRule (LCons $conditionalRule LNil))))
          ($conditionalBefore (LCons $predecessor LNil)) ($conditionalAfter (LCons $nextPredecessor LNil))
          ($conditionalExpected (LCons $nextPredecessor (LCons $nextPredecessor LNil))))
     (case $name
       ((acquired-replay-empty
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-replay $equations LNil $a LNil) (Some $a)))
        (acquired-replay-one-edge
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-replay $equations LNil $a $before) (Some $b)))
        (acquired-replay-missing-edge
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-replay $equations LNil $a (LCons $c LNil)) None))
        (acquired-after-duplicates
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-after-results $equations LNil $after
             (LCons $c (LCons $c (LCons $b LNil)))) $expected))
        (acquired-after-empty-trace-identity
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-after-results $equations LNil LNil
             (LCons $c (LCons $c (LCons $b LNil)))) (LCons $c (LCons $c (LCons $b LNil)))))
        (acquired-modulo-top-duplicates
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1 $a $before $after) $expected))
        (acquired-modulo-bottom-duplicates
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchBottomUp $language LNil 1 $a $before $after) $expected))
        (acquired-no-equation-permission
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown
             (GSLTLanguageDefWireV1 "acquired" RetainedTypes RetainedTerms $equations LNil)
             LNil 1 $a $before LNil) LNil))
        (acquired-missing-before-edge
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1 $a
             (LCons $c LNil) $after) LNil))
        (acquired-failed-later-before-edge
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1 $a
             (LCons $b (LCons $c LNil)) $after) LNil))
        (acquired-missing-after-edge
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1 $a $before
             (LCons $e LNil)) LNil))
        (acquired-continuation-per-contractum
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown
             (GSLTLanguageDefWireV1 "fork" RetainedTypes RetainedTerms $equations
               (LCons $rule (LCons (RewriteRule "be" RetainedContext LNil $b $e) LNil)))
             LNil 1 $a $before $after) (LCons $d LNil)))
        (acquired-zero-depth
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 0 $a $before $after) LNil))
        (acquired-unauthorized-directed-child
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1
             (PApp "pair" (LCons $a LNil)) (LCons (PApp "pair" (LCons $b LNil)) LNil) LNil) LNil))
        (acquired-unsupported-reflexive-adjacency
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $language LNil 1 $a
             (LCons $a LNil) $after) LNil))
        (acquired-malformed-language
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown Forged LNil 1 $a $before $after) LNil))
        (acquired-conditional-previous-top
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $conditionalLanguage $rows 1 $b
             $conditionalBefore $conditionalAfter) $conditionalExpected))
        (acquired-conditional-previous-bottom
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchBottomUp $conditionalLanguage $rows 1 $b
             $conditionalBefore $conditionalAfter) $conditionalExpected))
        (acquired-conditional-missing-provider
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $conditionalLanguage LNil 1 $b
             $conditionalBefore $conditionalAfter) LNil))
        (acquired-conditional-wrong-predecessor
         (equation-acquired-frontier:check $name
           (gslt:equation-context:acquired-witnessed-reducts MatchTopDown $conditionalLanguage $rows 1 $b
             (LCons (PApp "drop" (LCons $a (LCons $c LNil))) LNil) $conditionalAfter) LNil))))))

!(equation-acquired-frontier:control acquired-replay-empty)
!(equation-acquired-frontier:control acquired-replay-one-edge)
!(equation-acquired-frontier:control acquired-replay-missing-edge)
!(equation-acquired-frontier:control acquired-after-duplicates)
!(equation-acquired-frontier:control acquired-after-empty-trace-identity)
!(equation-acquired-frontier:control acquired-modulo-top-duplicates)
!(equation-acquired-frontier:control acquired-modulo-bottom-duplicates)
!(equation-acquired-frontier:control acquired-no-equation-permission)
!(equation-acquired-frontier:control acquired-missing-before-edge)
!(equation-acquired-frontier:control acquired-failed-later-before-edge)
!(equation-acquired-frontier:control acquired-missing-after-edge)
!(equation-acquired-frontier:control acquired-continuation-per-contractum)
!(equation-acquired-frontier:control acquired-zero-depth)
!(equation-acquired-frontier:control acquired-unauthorized-directed-child)
!(equation-acquired-frontier:control acquired-unsupported-reflexive-adjacency)
!(equation-acquired-frontier:control acquired-malformed-language)
!(equation-acquired-frontier:control acquired-conditional-previous-top)
!(equation-acquired-frontier:control acquired-conditional-previous-bottom)
!(equation-acquired-frontier:control acquired-conditional-missing-provider)
!(equation-acquired-frontier:control acquired-conditional-wrong-predecessor)
