; Join independently parsed MM0 declarations to the MMU and MMB resolvers and
; the same checked session. Public authorization comes from the MM0 source.
(: mm0:native:sort-name (-> Atom Number %Undefined%))
(= (mm0:native:sort-name $sorts $index)
   (case $sorts
     (((MM0SortEntriesConsV1 (MM0SortEntryV1 $name $flags $position) $rest)
       (if (== $index 0) (mm0:mmu:source-name $name)
         (mm0:native:sort-name $rest (- $index 1))))
      ($bad None))))

(: mm0:native:term-name (-> Atom Number %Undefined%))
(= (mm0:native:term-name $declarations $index)
   (case $declarations
     (((MM0DeclarationEntriesConsV1 (MM0TermEntryV1 $name $signature $position $source) $rest)
       (if (== $index 0) (mm0:mmu:source-name $name)
         (mm0:native:term-name $rest (- $index 1))))
      ((MM0DeclarationEntriesConsV1 (MM0AssertionEntryV1 $kind $name $signature $position $source) $rest)
       (mm0:native:term-name $rest $index))
      ($bad None))))

(: mm0:native:assertion-name (-> Atom Number %Undefined%))
(= (mm0:native:assertion-name $declarations $index)
   (case $declarations
     (((MM0DeclarationEntriesConsV1 (MM0TermEntryV1 $name $signature $position $source) $rest)
       (mm0:native:assertion-name $rest $index))
      ((MM0DeclarationEntriesConsV1 (MM0AssertionEntryV1 $kind $name $signature $position $source) $rest)
       (if (== $index 0) (mm0:mmu:source-name $name)
         (mm0:native:assertion-name $rest (- $index 1))))
      ($bad None))))

(: mm0:native:public-entry (-> Atom Atom Atom %Undefined%))
(= (mm0:native:public-entry $entry $sorts $declarations)
   (case $entry
     (((MM0:L (MM0:SpecSort $index $info))
       (let $name (mm0:native:sort-name $sorts $index)
         (mm0:native:named-entry $name MM0:MMUSort $index $entry)))
      ((MM0:L (MM0:SpecTerm $index $signature))
       (let $name (mm0:native:term-name $declarations $index)
         (mm0:native:named-entry $name MM0:MMUTerm $index $entry)))
      ((MM0:L (MM0:SpecDefinition $index $signature $body))
       (let $name (mm0:native:term-name $declarations $index)
         (mm0:native:named-entry $name MM0:MMUDefinition $index $entry)))
      ((MM0:L (MM0:SpecAxiom $index $signature))
       (let $name (mm0:native:assertion-name $declarations $index)
         (mm0:native:named-entry $name MM0:MMUAxiom $index $entry)))
      ((MM0:L (MM0:SpecTheorem $index $signature))
       (let $name (mm0:native:assertion-name $declarations $index)
         (mm0:native:named-entry $name MM0:MMUTheorem $index $entry)))
      ($bad None))))

(: mm0:native:named-entry (-> Atom Atom Number Atom %Undefined%))
(= (mm0:native:named-entry $name $kind $index $entry)
   (case $name
     (((Some $text) (Some (MM0:MMUPublic $text $kind $index $entry)))
      ($bad None))))

(: mm0:native:public-slots (-> Atom Atom Atom %Undefined%))
(= (mm0:native:public-slots $pending $sorts $declarations)
   (case (mm0:list-view $pending)
     ((List:Nil (Some (MM0:L ())))
      ((List:Cons $entry $rest)
       (let* (($head (mm0:native:public-entry $entry $sorts $declarations))
              ($tail (mm0:native:public-slots $rest $sorts $declarations)))
         (case ($head $tail)
           ((((Some $first) (Some $after))
             (let $result (mm0:list-cons $first $after) (Some $result)))
            ($bad None)))))
      ($bad None))))

(: mm0:native:prepare-mm0 (-> Atom %Undefined%))
(= (mm0:native:prepare-mm0 $path)
   (case (mm0:includes:elaborate-file $path)
     (((Some (MM0:IncludedEnvironment $file $digest $ast
        (MM0SourceStateV1 (MM0TextualEnvironmentV1 $sorts $declarations) $notation) $history $provenance))
       (let* (($state (MM0SourceStateV1 (MM0TextualEnvironmentV1 $sorts $declarations) $notation))
              ($pending (mm0:text:specification $state)))
         (case $pending
           (((Some $specification)
             (case (mm0:native:public-slots $specification $sorts $declarations)
               (((Some $public)
                 (Some (MM0:NativeSpecification $file $specification $public
                   (MM0:IncludedEnvironment $file $digest $ast $state $history $provenance))))
                ($bad None))))
            ($bad None)))))
      ($bad None))))

(: mm0:native:check-files (-> Atom Atom %Undefined%))
(= (mm0:native:check-files $specificationPath $proofPath)
   (mm0:native:check-files-profile MM0:MMURustStrict $specificationPath $proofPath))

(: mm0:native:check-files-profile (-> Atom Atom Atom %Undefined%))
(= (mm0:native:check-files-profile $profile $specificationPath $proofPath)
   (mm0:native:check-files-profile-fuel $profile 1000000 $specificationPath $proofPath))

(: mm0:native:check-files-profile-fuel (-> Atom Number Atom Atom %Undefined%))
(= (mm0:native:check-files-profile-fuel $profile $fuel $specificationPath $proofPath)
   (case (mm0:native:prepare-mm0 $specificationPath)
     (((Some $prepared) (mm0:native:check-prepared-fuel $profile $fuel $prepared $proofPath))
      ($bad (MM0:NativeFrontendRefused MM0:MM0Source)))))

; Logical projection retains the source history. Profiles which do not
; interpret its I/O obligations must refuse them before starting a session.
(: mm0:native:history-has-io (-> Atom %Undefined%))
(= (mm0:native:history-has-io $history)
   (case $history
     ((MM0SourceHistoryNilV1 False)
      ((MM0SourceHistoryConsV1 $first $rest)
       (case $first
         (((MM0StringDirectiveV1 $position $direction $expression $profile) True)
          ($other (mm0:native:history-has-io $rest)))))
      ($bad True))))
(: mm0:native:source-has-io (-> Atom %Undefined%))
(= (mm0:native:source-has-io $source)
   (case $source
     (((MM0:IncludedEnvironment $file $digest $ast $state $history $provenance)
       (mm0:native:history-has-io $history))
      ($bad True))))

(: mm0:native:check-prepared (-> Atom Atom Atom %Undefined%))
(= (mm0:native:check-prepared $profile
     (MM0:NativeSpecification $path $specification $public $source) $proofPath)
   (mm0:native:check-prepared-fuel $profile 1000000
     (MM0:NativeSpecification $path $specification $public $source) $proofPath))

(: mm0:native:check-prepared-fuel (-> Atom Number Atom Atom %Undefined%))
(= (mm0:native:check-prepared-fuel $profile $fuel
     (MM0:NativeSpecification $path $specification $public $source) $proofPath)
   (if (if (== $profile MM0:MMUHaskellString) False
         (mm0:native:source-has-io $source))
     (MM0:NativeFrontendRefused MM0:StringIOProfile)
     (let $resolved
       (if (== $profile MM0:MMUHaskellString)
         (mm0:string-io:resolve-file
           (MM0:NativeSpecification $path $specification $public $source) $proofPath)
         (mm0:mmu:resolve-file-profile $profile $public $proofPath))
       (case $resolved
         (((Some $program)
           (mm0:native:check-resolved-fuel $profile $fuel
             (MM0:NativeSpecification $path $specification $public $source) $program))
          ($bad (MM0:NativeFrontendRefused MM0:MMUSource)))))))

(: mm0:native:check-binary-files (-> Atom Atom %Undefined%))
(= (mm0:native:check-binary-files $specificationPath $proofPath)
   (case (mm0:native:prepare-mm0 $specificationPath)
     (((Some $prepared) (mm0:native:check-binary-prepared $prepared $proofPath))
      ($bad (MM0:NativeFrontendRefused MM0:MM0Source)))))

(: mm0:native:check-binary-prepared (-> Atom Atom %Undefined%))
(= (mm0:native:check-binary-prepared
     (MM0:NativeSpecification $path $specification $public $source) $proofPath)
   (if (mm0:native:source-has-io $source)
     (MM0:NativeFrontendRefused MM0:StringIOProfile)
     (case (mm0:mmb:resolve-file $public $proofPath)
       (((Some $resolved)
         (mm0:native:check-resolved MM0:MMBBinaryV1
           (MM0:NativeSpecification $path $specification $public $source) $resolved))
        ($bad (MM0:NativeFrontendRefused MM0:MMBSource))))))

(: mm0:native:submit-resolved (-> Atom %Undefined%))
(= (mm0:native:submit-resolved $resolved)
   (case $resolved
     (((MM0:MMUProgram $profile $state $commands $extensions $source)
       (mm0:mmu:submit-commands $commands))
      ((MM0:MMBProgram MM0:MMBBinaryV1 $state $commands $source)
       (mm0:mmu:submit-commands $commands))
      ($bad False))))

; Both input formats submit their retained commands through one session driver.
(: mm0:native:check-resolved (-> Atom Atom Atom %Undefined%))
(= (mm0:native:check-resolved $profile
     (MM0:NativeSpecification $path $specification $public $source) $resolved)
   (mm0:native:check-resolved-fuel $profile 1000000
     (MM0:NativeSpecification $path $specification $public $source) $resolved))

(: mm0:native:check-resolved-fuel (-> Atom Number Atom Atom %Undefined%))
(= (mm0:native:check-resolved-fuel $profile $fuel
     (MM0:NativeSpecification $path $specification $public $source) $resolved)
   (let* (($started (mm0:start $specification))
          ($submitted (mm0:native:submit-resolved $resolved))
          ($finished (mm0:finish))
          ($accepted (and $started (and $submitted $finished)))
          ($kernelReceipt (MM0:NativeReceipt $profile $accepted $started $submitted $finished
            (MM0:NativeSpecification $path $specification $public $source) $resolved)))
     (if (== $profile MM0:MMUHaskellString)
       (let* (($effects (mm0:string-io:finish $kernelReceipt $fuel))
              ($verdict (mm0:string-io:verdict $effects)))
         (MM0:NativeStringReceipt $profile $verdict $kernelReceipt $effects))
       $kernelReceipt)))

(: mm0:native:verdict (-> Atom %Undefined%))
(= (mm0:native:verdict $receipt)
   (case $receipt
     (((MM0:NativeReceipt $profile $accepted $started $submitted $finished $specification $proof)
       $accepted)
      ((MM0:NativeStringReceipt MM0:MMUHaskellString $accepted $kernel $effects) $accepted)
      ((MM0:NativeFrontendRefused $stage) False)
      ($bad (MM0:UnexpectedNativeResult $bad)))))

(: mm0:native:string-effects (-> Atom %Undefined%))
(= (mm0:native:string-effects $receipt)
   (case $receipt
     (((MM0:NativeStringReceipt MM0:MMUHaskellString $accepted $kernel $effects) $effects)
      ($other None))))

(: mm0:native:verify-files (-> Atom Atom %Undefined%))
(= (mm0:native:verify-files $specificationPath $proofPath)
   (mm0:native:verify-files-profile MM0:MMURustStrict $specificationPath $proofPath))

(: mm0:native:verify-files-profile (-> Atom Atom Atom %Undefined%))
(= (mm0:native:verify-files-profile $profile $specificationPath $proofPath)
   (let $receipt (mm0:native:check-files-profile $profile $specificationPath $proofPath)
     (mm0:native:verdict $receipt)))

(: mm0:native:verify-files-profile-fuel (-> Atom Number Atom Atom %Undefined%))
(= (mm0:native:verify-files-profile-fuel $profile $fuel $specificationPath $proofPath)
   (let $receipt (mm0:native:check-files-profile-fuel $profile $fuel $specificationPath $proofPath)
     (mm0:native:verdict $receipt)))

(: mm0:native:verify-binary-files (-> Atom Atom %Undefined%))
(= (mm0:native:verify-binary-files $specificationPath $proofPath)
   (let $receipt (mm0:native:check-binary-files $specificationPath $proofPath)
     (mm0:native:verdict $receipt)))
