; Many-sorted first-order modules use the canonical LanguageDef wire and the
; existing GRuleV1 / Pattern certificate carrier. This backend has no object
; binders, definitions or computational providers. It retains the full source
; wire, assigns indices in declaration order, and validates every generated
; declaration with the MM0 kernel before returning a compilation.
; Load data.metta, kernel.generated.metta, service.metta and mmu.metta first.

(: mm0:module:list (-> Atom %Undefined%))
(= (mm0:module:list $values)
   (case $values
     ((LNil (Some (MM0:L ())))
      ((LCons $first $rest)
       (case (mm0:module:list $rest)
         (((Some $tail) (let $result (mm0:list-cons $first $tail) (Some $result)))
          ($bad None))))
      ($bad None))))

(: mm0:module:member (-> Atom Atom %Undefined%))
(= (mm0:module:member $name $values)
   (case $values
     ((LNil False)
      ((LCons $first $rest)
       (if (== $first $name) True (mm0:module:member $name $rest)))
      ($bad False))))

; Portable upstream artifacts use separate generated name namespaces. The
; compilation retains the complete authored wire, including display names and
; notation. The Lean authoring printer exposes that richer notation directly.
(: mm0:module:artifact-name (-> Atom Number %Undefined%))
(= (mm0:module:artifact-name $kind $index)
   (str:concat "mm0__" (str:concat $kind (str:concat "_" (str:number->string $index)))))

(: mm0:module:expression-text (-> Atom %Undefined%))
(= (mm0:module:expression-text $expression)
   (mm0:module:spine-text $expression ""))
(: mm0:module:spine-text (-> Atom Atom %Undefined%))
(= (mm0:module:spine-text $expression $arguments)
   (case $expression
     (((MM0:Var $index)
       (if (== $arguments "") (let $name (mm0:module:artifact-name "arg" $index) (Some $name)) None))
      ((MM0:Term $index)
       (let $name (mm0:module:artifact-name "term" $index)
         (let $text (str:concat "(" (str:concat $name (str:concat $arguments ")"))) (Some $text))))
      ((MM0:App $function $argument)
       (case (mm0:module:expression-text $argument)
         (((Some $text)
           (let $more (str:concat " " (str:concat $text $arguments))
             (mm0:module:spine-text $function $more)))
          ($bad None))))
      ($bad None))))

(: mm0:module:expressions-text (-> Atom %Undefined%))
(= (mm0:module:expressions-text (MM0:L $values))
   (case $values
     ((() (Some ""))
      ((cons $first $rest)
       (case ((mm0:module:expression-text $first) (mm0:module:expressions-text (MM0:L $rest)))
         ((((Some $head) (Some $tail))
           (let $text (if (== $tail "") $head (str:concat $head (str:concat " " $tail))) (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:context-text (-> Atom Number %Undefined%))
(= (mm0:module:context-text (MM0:L $binders) $index)
   (case $binders
     ((() (Some ""))
      ((cons (MM0:L (MM0:Regular $sort (MM0:L ()))) $rest)
       (case (mm0:module:context-text (MM0:L $rest) (+ $index 1))
         (((Some $tail)
           (let* (($name (mm0:module:artifact-name "arg" $index))
                  ($type (mm0:module:artifact-name "sort" $sort))
                  ($text (str:concat " (" (str:concat $name (str:concat ": " (str:concat $type ")"))))))
             (let $result (str:concat $text $tail) (Some $result))))
          ($bad None))))
      ($bad None))))

(: mm0:module:statements-text (-> Atom Atom %Undefined%))
(= (mm0:module:statements-text (MM0:L $hypotheses) $conclusion)
   (case $hypotheses
     ((() (case (mm0:module:expression-text $conclusion)
             (((Some $text) (let $result (str:concat "$ " (str:concat $text " $")) (Some $result)))
              ($bad None))))
      ((cons $first $rest)
       (case ((mm0:module:expression-text $first)
              (mm0:module:statements-text (MM0:L $rest) $conclusion))
         ((((Some $head) (Some $tail))
           (let $text (str:concat "$ " (str:concat $head (str:concat " $ > " $tail))) (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:assertion-text (-> Atom Atom Atom %Undefined%))
(= (mm0:module:assertion-text $kind $name $declaration)
   (case $declaration
     (((MM0:L (MM0:Theorem $arguments $hypotheses $conclusion))
       (case ((mm0:module:context-text $arguments 0)
              (mm0:module:statements-text $hypotheses $conclusion))
         ((((Some $context) (Some $statements))
           (let $text (str:concat $kind (str:concat " " (str:concat $name
             (str:concat $context (str:concat ": " $statements))))) (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:sorts-text (-> Atom %Undefined%))
(= (mm0:module:sorts-text (MM0:L $sorts))
   (case $sorts
     ((() (Some ""))
      ((cons (MM0:L ($index (MM0:L (MM0:Sort False True $provable False)))) $rest)
       (case (mm0:module:sorts-text (MM0:L $rest))
         (((Some $tail)
           (let* (($name (mm0:module:artifact-name "sort" $index))
                  ($prefix (if $provable "strict provable sort " "strict sort "))
                  ($text (str:concat $prefix (str:concat $name (str:concat ";\n" $tail)))))
             (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:terms-text (-> Atom %Undefined%))
(= (mm0:module:terms-text (MM0:L $terms))
   (case $terms
     ((() (Some ""))
      ((cons (MM0:L ($index (MM0:L (MM0:TermDecl $arguments $sort (MM0:L ()))))) $rest)
       (case ((mm0:module:context-text $arguments 0) (mm0:module:terms-text (MM0:L $rest)))
         ((((Some $context) (Some $tail))
           (let* (($name (mm0:module:artifact-name "term" $index))
                  ($type (mm0:module:artifact-name "sort" $sort))
                  ($text (str:concat "term " (str:concat $name (str:concat $context
                    (str:concat ": " (str:concat $type (str:concat ";\n" $tail))))))))
             (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:axioms-text (-> Atom %Undefined%))
(= (mm0:module:axioms-text (MM0:L $axioms))
   (case $axioms
     ((() (Some ""))
      ((cons (MM0:L ($index $declaration)) $rest)
       (let $name (mm0:module:artifact-name "rule" $index)
         (case ((mm0:module:assertion-text "axiom" $name $declaration)
                (mm0:module:axioms-text (MM0:L $rest)))
           ((((Some $head) (Some $tail))
             (let $text (str:concat $head (str:concat ";\n" $tail)) (Some $text)))
            ($bad None)))))
      ($bad None))))

(: mm0:module:proof-text (-> Atom %Undefined%))
(= (mm0:module:proof-text $proof)
   (case $proof
     (((MM0:L (MM0:Hyp $index))
       (let $name (mm0:module:artifact-name "hyp" $index) (Some $name)))
      ((MM0:L (MM0:TheoremApp $index (MM0:L $arguments) $children))
       (case ((mm0:module:proof-arguments $arguments) (mm0:module:proofs-text $children))
         ((((Some $formals) (Some $premises))
           (let* (($name (mm0:module:artifact-name "rule" $index))
                  ($text (str:concat "(! " (str:concat $name (str:concat $formals (str:concat $premises ")"))))))
             (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:proof-arguments (-> Atom %Undefined%))
(= (mm0:module:proof-arguments $arguments)
   (case $arguments
     ((() (Some ""))
      ((cons $first $rest)
       (case ((mm0:module:expression-text $first) (mm0:module:proof-arguments $rest))
         ((((Some $head) (Some $tail))
           (let $text (str:concat " $ " (str:concat $head (str:concat " $" $tail))) (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:proofs-text (-> Atom %Undefined%))
(= (mm0:module:proofs-text (MM0:L $proofs))
   (case $proofs
     ((() (Some ""))
      ((cons $first $rest)
       (case ((mm0:module:proof-text $first) (mm0:module:proofs-text (MM0:L $rest)))
         ((((Some $head) (Some $tail))
           (let $text (str:concat " " (str:concat $head $tail)) (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:hypotheses-text (-> Atom Number %Undefined%))
(= (mm0:module:hypotheses-text (MM0:L $hypotheses) $index)
   (case $hypotheses
     ((() (Some ""))
      ((cons $first $rest)
       (case ((mm0:module:expression-text $first) (mm0:module:hypotheses-text (MM0:L $rest) (+ $index 1)))
         ((((Some $head) (Some $tail))
           (let* (($name (mm0:module:artifact-name "hyp" $index))
                  ($text (str:concat " (" (str:concat $name (str:concat ": $ "
                    (str:concat $head (str:concat " $)" $tail)))))))
             (Some $text)))
          ($bad None))))
      ($bad None))))

(: mm0:module:artifacts (-> Atom Atom Atom %Undefined%))
(= (mm0:module:artifacts $compilation $goal $certificate)
   (case $compilation
     (((Some (MM0:CompiledModule $source $spec $commands
         (MM0:L (MM0:Theory (MM0:L $sorts) (MM0:L $terms) $defs (MM0:L $rules)))
         $sortNames $termNames $ruleNames))
       (case ((mm0:module:row $goal $sortNames $termNames)
              (mm0:module:proof $certificate $termNames $ruleNames))
         ((((Some (MM0:ModuleRow $name (MM0:L (MM0:Theorem $context $hypotheses $claim)) $formals)) (Some $root))
           (let* (($sortRows (reverse $sorts)) ($termRows (reverse $terms)) ($ruleRows (reverse $rules)))
             (case ((mm0:module:sorts-text (MM0:L $sortRows))
                    (mm0:module:terms-text (MM0:L $termRows))
                    (mm0:module:axioms-text (MM0:L $ruleRows))
                    (mm0:module:assertion-text "theorem" "checked_goal"
                      (MM0:L (MM0:Theorem $context $hypotheses $claim)))
                    (mm0:module:context-text $context 0)
                    (mm0:module:hypotheses-text $hypotheses 0)
                    (mm0:module:expression-text $claim)
                    (mm0:module:proof-text $root))
               ((((Some $sortText) (Some $termText) (Some $axiomText) (Some $goalText)
                   (Some $contextText) (Some $hypothesisText) (Some $claimText) (Some $proofText))
                 (let* (($base (str:concat "delimiter $ ( ) $;\n" (str:concat $sortText (str:concat $termText $axiomText))))
                        ($specification (str:concat $base (str:concat $goalText ";\n")))
                        ($proofFile (str:concat $base (str:concat "pub theorem checked_goal"
                          (str:concat $contextText (str:concat $hypothesisText (str:concat ": $ "
                            (str:concat $claimText (str:concat " $ =\n  '" (str:concat $proofText ";\n"))))))))))
                   (Some (MM0:ModuleArtifacts $specification $proofFile))))
                ($bad None)))))
          ($bad None))))
      ($bad None))))

(: mm0:module:declared (-> Atom Atom %Undefined%))
(= (mm0:module:declared $values $names)
   (case $values
     ((LNil True)
      ((LCons $first $rest)
       (case (mm0:mmu:lookup $names $first)
         (((Some $index) (mm0:module:declared $rest $names)) ($bad False))))
      ($bad False))))

(: mm0:module:carrier (-> Atom %Undefined%))
(= (mm0:module:carrier $carrier)
   (is-member $carrier (CarrierAst CarrierTokenLabel CarrierTokenRaw
     CarrierTokenProof CarrierTokenPath CarrierBuiltinInt CarrierBuiltinString CarrierBuiltinBool)))

(: mm0:module:compile (-> Atom %Undefined%))
(= (mm0:module:compile $source)
   (case $source
     (((GSLTInferenceTheoryWireV1
         (GSLTLanguageDefWireV1 $name $types $constructors LNil LNil)
         $exports $judgments $rules)
       (let $cache (new-space)
         (let $reset (change-state! mm0-inference-cache $cache)
           (case (mm0:module:types $types $judgments 0
                   (MM0:ModuleBuild (MM0:L ()) (MM0:L ()) (MM0:L ())
                     (MM0:L ()) (MM0:L ()) (MM0:L ()) (MM0:L ()) (MM0:L ())))
             (((Some $typed)
               (case (mm0:module:constructors $constructors 0 $typed)
                 (((Some $terms)
                   (case (mm0:module:rules $rules 0 $terms)
                     (((Some $built) (mm0:module:finish-build $source $exports $judgments $built))
                      ($bad None))))
                  ($bad None))))
              ($bad None))))))
      ($unsupported None))))

(: mm0:module:types (-> Atom Atom Number Atom %Undefined%))
(= (mm0:module:types $types $judgments $index $build)
   (case ($types $build)
     (((LNil $ready) (Some $ready))
      (((LCons (TypeDecl $name $carrier) $rest)
        (MM0:ModuleBuild $sorts $terms $thms $sortNames $termNames $ruleNames $spec $commands))
       (if (and (== (get-type $name) String) (mm0:module:carrier $carrier))
         (if (== (mm0:mmu:lookup $sortNames $name) None)
           (let* (($provable (mm0:module:member $name $judgments))
                  ($info (MM0:L (MM0:Sort False True $provable False)))
                  ($nextSorts (mm0:list-cons (MM0:L ($index $info)) $sorts))
                  ($nextNames (mm0:mmu:bind $sortNames $name $index))
                  ($nextSpec (mm0:list-cons (MM0:L (MM0:SpecSort $index $info)) $spec))
                  ($nextCommands (mm0:list-cons
                    (MM0:L (MM0:ProofDeclaration False (MM0:L (MM0:AdmitSort $index $info)))) $commands)))
             (mm0:module:types $rest $judgments (+ $index 1)
               (MM0:ModuleBuild $nextSorts $terms $thms $nextNames $termNames $ruleNames
                 $nextSpec $nextCommands)))
           None)
         None))
      ($bad None))))

; Contexts use regular variables with empty dependency sets. Source formal
; names are numbered once, in their authored order, and checked for duplicates.
(: mm0:module:context (-> Atom Atom Atom Number Atom Atom %Undefined%))
(= (mm0:module:context $formals $types $sortNames $index $names $context)
   (case ($formals $types)
     (((LNil LNil) (Some (MM0:ModuleContext $names $context)))
      (((LCons (Formal $name 0) $rest) (LCons (TBase $sort) $more))
       (if (and (== (get-type $name) String) (== (mm0:mmu:lookup $names $name) None))
         (case (mm0:mmu:lookup $sortNames $sort)
           (((Some $sortIndex)
             (let $bound (mm0:mmu:bind $names $name $index)
               (case (mm0:module:context $rest $more $sortNames (+ $index 1) $bound $context)
                 (((Some (MM0:ModuleContext $all $tail))
                   (let $result (mm0:list-cons (MM0:L (MM0:Regular $sortIndex (MM0:L ()))) $tail)
                     (Some (MM0:ModuleContext $all $result))))
                  ($bad None)))))
            ($bad None)))
         None))
      ($bad None))))

(: mm0:module:parameters (-> Atom Atom %Undefined%))
(= (mm0:module:parameters $parameters $sortNames)
   (case $parameters
     ((LNil (Some (MM0:L ())))
      ((LCons (TermSimple $name (TBase $sort)) $rest)
       (case ((mm0:mmu:lookup $sortNames $sort) (mm0:module:parameters $rest $sortNames))
         ((((Some $index) (Some $tail))
           (let $result (mm0:list-cons (MM0:L (MM0:Regular $index (MM0:L ()))) $tail)
             (Some $result)))
          ($bad None))))
      ($bad None))))

(: mm0:module:constructors (-> Atom Number Atom %Undefined%))
(= (mm0:module:constructors $constructors $index $build)
   (case ($constructors $build)
     (((LNil $ready) (Some $ready))
      (((LCons (GrammarRule $name $sort $parameters $notation EvalNone) $rest)
        (MM0:ModuleBuild $sorts $terms $thms $sortNames $termNames $ruleNames $spec $commands))
       (if (and (== (get-type $name) String) (== (mm0:mmu:lookup $termNames $name) None))
         (case ((mm0:mmu:lookup $sortNames $sort) (mm0:module:parameters $parameters $sortNames))
           ((((Some $sortIndex) (Some $context))
             (let $declaration (MM0:L (MM0:TermDecl $context $sortIndex (MM0:L ())))
               (if (mm0:form-term $sorts $declaration)
                 (let* (($nextTerms (mm0:list-cons (MM0:L ($index $declaration)) $terms))
                        ($nextNames (mm0:mmu:bind $termNames $name $index))
                        ($nextSpec (mm0:list-cons (MM0:L (MM0:SpecTerm $index $declaration)) $spec))
                        ($nextCommands (mm0:list-cons
                          (MM0:L (MM0:ProofDeclaration False (MM0:L (MM0:AdmitTerm $index $declaration))))
                          $commands)))
                   (mm0:module:constructors $rest (+ $index 1)
                     (MM0:ModuleBuild $sorts $nextTerms $thms $sortNames $nextNames $ruleNames
                       $nextSpec $nextCommands)))
                 None)))
            ($bad None)))
         None))
      ($bad None))))

; Only the first-order Pattern fragment is translated. A free variable must
; be a declared formal; open-certificate variables are explicitly indexed.
(: mm0:module:expression (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:module:expression $pattern $termNames $formals $open)
   (case $pattern
     (((FVar $name)
       (case (mm0:mmu:lookup $formals $name)
         (((Some $index) (Some (MM0:Var $index))) ($bad None))))
      ((Var $index)
       (if (and $open (mm0:module:natural $index))
         (Some (MM0:Var $index)) None))
      ((PApp $name $arguments)
       (case (mm0:mmu:lookup $termNames $name)
         (((Some $index)
           (mm0:module:apply $arguments $termNames $formals $open (MM0:Term $index)))
          ($bad None))))
      ($unsupported None))))

(: mm0:module:apply (-> Atom Atom Atom Atom Atom %Undefined%))
(= (mm0:module:apply $arguments $termNames $formals $open $function)
   (case $arguments
     ((LNil (Some $function))
      ((LCons $argument $rest)
       (case (mm0:module:expression $argument $termNames $formals $open)
         (((Some $value)
           (mm0:module:apply $rest $termNames $formals $open (MM0:App $function $value)))
          ($bad None))))
      ($bad None))))

(: mm0:module:expressions (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:module:expressions $patterns $termNames $formals $open)
   (case $patterns
     ((LNil (Some (MM0:L ())))
      ((LCons $first $rest)
       (case ((mm0:module:expression $first $termNames $formals $open)
              (mm0:module:expressions $rest $termNames $formals $open))
         ((((Some $head) (Some $tail))
           (let $result (mm0:list-cons $head $tail) (Some $result)))
          ($bad None))))
      ($bad None))))

(: mm0:module:row (-> Atom Atom Atom %Undefined%))
(= (mm0:module:row $row $sortNames $termNames)
   (case $row
     (((SortedRuleV1 (GRuleV1 $name $formals $premises $conclusion LNil) $types)
       (case (mm0:module:context $formals $types $sortNames 0 (MM0:L ()) (MM0:L ()))
         (((Some (MM0:ModuleContext $names $context))
           (case ((mm0:module:expressions $premises $termNames $names False)
                  (mm0:module:expression $conclusion $termNames $names False))
             ((((Some $hypotheses) (Some $claim))
               (Some (MM0:ModuleRow $name (MM0:L (MM0:Theorem $context $hypotheses $claim)) $names)))
              ($bad None))))
          ($bad None))))
      ($bad None))))

(: mm0:module:rules (-> Atom Number Atom %Undefined%))
(= (mm0:module:rules $rules $index $build)
   (case ($rules $build)
     (((LNil $ready) (Some $ready))
      (((LCons $first $rest)
        (MM0:ModuleBuild $sorts $terms $thms $sortNames $termNames $ruleNames $spec $commands))
       (case (mm0:module:row $first $sortNames $termNames)
         (((Some (MM0:ModuleRow $name $declaration $formals))
           (if (and (== (get-type $name) String) (== (mm0:mmu:lookup $ruleNames $name) None))
             (if (mm0:form-theorem $sorts $terms $declaration)
               (let* (($nextTheorems (mm0:list-cons (MM0:L ($index $declaration)) $thms))
                      ($nextNames (mm0:mmu:bind $ruleNames $name $index))
                      ($nextSpec (mm0:list-cons (MM0:L (MM0:SpecAxiom $index $declaration)) $spec))
                      ($nextCommands (mm0:list-cons
                        (MM0:L (MM0:ProofDeclaration False (MM0:L (MM0:AdmitAxiom $index $declaration))))
                        $commands)))
                 (mm0:module:rules $rest (+ $index 1)
                   (MM0:ModuleBuild $sorts $terms $nextTheorems $sortNames $termNames $nextNames
                     $nextSpec $nextCommands)))
               None)
             None))
          ($bad None))))
      ($bad None))))

(: mm0:module:finish-build (-> Atom Atom Atom Atom %Undefined%))
(= (mm0:module:finish-build $source $exports $judgments $build)
   (case $build
     (((MM0:ModuleBuild $sorts $terms $thms $sortNames $termNames $ruleNames
         (MM0:L $reversedSpec) (MM0:L $reversedCommands))
       (if (and (mm0:module:declared $exports $sortNames) (mm0:module:declared $judgments $sortNames))
         (let* (($spec (reverse $reversedSpec)) ($commands (reverse $reversedCommands)))
           (Some (MM0:CompiledModule $source (MM0:L $spec) (MM0:L $commands)
             (MM0:L (MM0:Theory $sorts $terms (MM0:L ()) $thms)) $sortNames $termNames $ruleNames)))
         None))
      ($bad None))))

; The open extension adds a hypothesis occurrence to the existing GProof
; carrier. Children retain their ordered PrNil / PrCons representation.
(: mm0:module:proof (-> Atom Atom Atom %Undefined%))
(= (mm0:module:proof $proof $termNames $ruleNames)
   (case $proof
     (((GOpenHyp $index)
       (if (mm0:module:natural $index)
         (Some (MM0:L (MM0:Hyp $index))) None))
      ((GProof (GRuleInst $name $arguments) $children)
       (case ((mm0:mmu:lookup $ruleNames $name)
              (mm0:module:expressions $arguments $termNames (MM0:L ()) True)
              (mm0:module:proofs $children $termNames $ruleNames))
         ((((Some $index) (Some $values) (Some $premises))
           (Some (MM0:L (MM0:TheoremApp $index $values $premises))))
          ($bad None))))
      ($bad None))))

; The physical certificate codec has natural indices, rather than arbitrary
; Number values. Decimal fractions, signs and nonnumeric atoms are refused.
(: mm0:module:natural (-> Atom %Undefined%))
(= (mm0:module:natural $value)
   (if (== (get-type $value) Number)
     (let $text (str:number->string $value) (str:all-in? digit $text)) False))

(: mm0:module:proofs (-> Atom Atom Atom %Undefined%))
(= (mm0:module:proofs $children $termNames $ruleNames)
   (case $children
     ((PrNil (Some (MM0:L ())))
      ((PrCons $first $rest)
       (case ((mm0:module:proof $first $termNames $ruleNames)
              (mm0:module:proofs $rest $termNames $ruleNames))
         ((((Some $head) (Some $tail))
           (let $result (mm0:list-cons $head $tail) (Some $result)))
          ($bad None))))
      ($bad None))))

(: mm0:module:submit-all (-> Atom %Undefined%))
(= (mm0:module:submit-all (MM0:L $commands))
   (case $commands
     ((() True)
      ((cons $first $rest)
       (if (mm0:submit $first) (mm0:module:submit-all (MM0:L $rest)) False))
      ($bad False))))

; A proof is submitted only after the independently supplied goal is appended
; to the specification. Unknown rules and malformed encodings are refused.
(: mm0:module:check (-> Atom Atom Atom %Undefined%))
(= (mm0:module:check $compilation $goal $certificate)
   (case $compilation
     (((Some (MM0:CompiledModule $source $spec $commands
         (MM0:L (MM0:Theory $sorts $terms $defs (MM0:L $theorems))) $sortNames $termNames $ruleNames))
       (let* (($formed (mm0:module:row $goal $sortNames $termNames))
              ($evidence (mm0:module:proof $certificate $termNames $ruleNames)))
        (case ($formed $evidence)
         ((((Some (MM0:ModuleRow $name $declaration $formals)) (Some $root))
           (let* (($index (size-atom $theorems))
                  ($expected (mm0:list-append $spec (MM0:L ((MM0:L (MM0:SpecTheorem $index $declaration))))))
                  ($command (MM0:L (MM0:ProofDeclaration False
                    (MM0:L (MM0:AdmitTheorem $index $declaration (MM0:L ()) $root))))))
             (if (mm0:start $expected)
               (if (mm0:module:submit-all $commands)
                 (if (mm0:submit $command) (mm0:finish) False) False)
               False)))
          ($bad False)))))
      ($bad False))))
