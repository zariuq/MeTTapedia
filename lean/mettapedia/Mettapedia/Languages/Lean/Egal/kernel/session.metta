; The Lean reading as a live kernel theory.
;
; The document that check.sh hands to the two checkers is assembled here from
; the same files in the same order and checked once, in process, by the
; Megalodon kernel of CeTTa.  What it builds is a theory: every definition
; and theorem of the reading is then a kernel object, found by its name in
; the source text.
;
;   (egal:open PREAMBLE ROOT WORK)  assemble ROOT's document in WORK and check
;                                   it after the signature PREAMBLE; answers
;                                   (LeanSession VERDICT SUMMARY)
;   (egal:open-parts PREAMBLE ROOT WORK PARTS)
;                                   the same for a target's document: the
;                                   ROOT-relative files PARTS, in the order
;                                   check-target.sh reads them
;   (egal:theory)                   the theory of the open session
;   (egal:id NAME)                  the kernel's name of the declaration whose
;                                   source name is NAME
;   (egal:arity NAME)               the arguments it takes as a function of the
;                                   logic
;   (egal:known NAME)               the theorem named NAME
;   (egal:proposition NAME)         what it states
;
; Import megalodon, fs and str first.

; The files of the document, in checking order.  A library that the function
; document already embeds is not read a second time.
(= (egal:parts-before-functions)
   ("Library/Conversion.mg" "Library/Quotients.mg" "Library/EquivalenceClosure.mg"
    "Library/RankedRecursion.mg" "LeanInEgal.mg" "Library/Typing.mg" "Library/QuotientTyping.mg"
    "Library/Digits.mg" "generated/LeanFamilies.mg" "Library/EqFacts.mg" "Library/QuotientProofs.mg"
    "FamilyFacts.mg" "Numerals.mg" "Decidable.mg" "Library/NumeralDecisions.mg"
    "Library/AlgebraicStructures.mg" "Library/NatAlgebra.mg" "Library/Propositions.mg"))
(= (egal:parts-after-functions)
   ("Library/DecideFacts.mg" "Library/NatAdd.mg" "Library/NatMul.mg" "Library/NatSub.mg"
    "Library/NatDecide.mg" "Library/NatDiv.mg"))
(= (egal:path $root $relative) (format-args "{}/{}" ($root $relative)))
(= (egal:embedded $functions $relative)
   (case (str:find $functions (format-args "(** Embedded proof support: {} **)\n" ($relative)))
     (((TextNotFound $_) False) ($_ True))))
(= (egal:texts $root $relatives)
   (if (== $relatives ()) ()
       (cons-atom (fs:read-text (egal:path $root (car-atom $relatives)))
                  (egal:texts $root (cdr-atom $relatives)))))
(= (egal:not-embedded $functions $relatives)
   (if (== $relatives ()) ()
       (if (egal:embedded $functions (car-atom $relatives))
           (egal:not-embedded $functions (cdr-atom $relatives))
           (cons-atom (car-atom $relatives) (egal:not-embedded $functions (cdr-atom $relatives))))))
(= (egal:document-text $root)
   (let* (($functions (fs:read-text (egal:path $root "generated/LeanFunctions.mg")))
          ($before (str:join "" (egal:texts $root (egal:parts-before-functions))))
          ($after (str:join "" (egal:texts $root (egal:not-embedded $functions (egal:parts-after-functions)))))
          ($computations (fs:read-text (egal:path $root "generated/LeanComputations.mg"))))
     (str:join "" ($before $functions $after $computations))))

; A document's text, written to DOCUMENT and checked after PREAMBLE; its theory
; is the session's.
(= (egal:open-text $preamble $document $text)
   (let* (($_written (fs:write $document $text))
          ($result (mg:check-document ($preamble) $document ((theory egal)))))
     (case $result
       (((Megalodon.document $theory $authority $verdict $summary $entries)
         (let $_kept (add-atom &self (LeanSessionTheory $theory))
           (LeanSession $verdict $summary)))
        ($other $other)))))
(= (egal:open $preamble $root $work)
   (egal:open-text $preamble (format-args "{}/lean-document.mg" ($work)) (egal:document-text $root)))
(= (egal:open-parts $preamble $root $work $parts)
   (egal:open-text $preamble (format-args "{}/target-document.mg" ($work)) (str:join "" (egal:texts $root $parts))))
(= (egal:theory) (match &self (LeanSessionTheory $theory) $theory))

; Names.  The kernel names a declaration by its content; the source name is a
; key that finds it.  Each answer is kept, with the declaration's type.
; A declaration is (KIND ID TYPE-OR-STATEMENT PROVENANCE ..): its provenance
; (source, also, origin) varies, so it is read by position.
(= (egal:declared $declaration)
   (let* (($kind (car-atom $declaration))
          ($id (car-atom (cdr-atom $declaration)))
          ($third (car-atom (cdr-atom (cdr-atom $declaration)))))
     (if (or (== $kind Megalodon.definition) (== $kind Megalodon.parameter))
         (LeanDeclared $id $third)
         (LeanDeclared $id (Tp.prop)))))
(= (egal:found $found $source)
   (case $found
     (((Megalodon.found) (Error (LeanName $source) (LeanSession "no declaration has this source name")))
      ($_ (egal:declared (car-atom (cdr-atom $found)))))))
(= (egal:declaration $source)
   (let $kept (collapse (match &self (LeanKernelName $source $declared) $declared))
     (if (== $kept ())
         (let $declared (egal:found (mg:lookup (egal:theory) $source) $source)
           (let $_kept (add-atom &self (LeanKernelName $source $declared)) $declared))
         (car-atom $kept))))
(= (egal:id $source)
   (case (egal:declaration $source) (((LeanDeclared $id $type) $id) ($other $other))))
; How many arguments the declaration takes as a function of the logic (a set
; takes none: applying a set is the set-theoretic application ap).
(= (egal:arrows $type) (case $type (((Tp.arr $a $b) (+ 1 (egal:arrows $b))) ($_ 0))))
(= (egal:arity $source)
   (case (egal:declaration $source) (((LeanDeclared $id $type) (egal:arrows $type)) ($other 0))))
(= (egal:known $source) (mg:known (egal:theory) (egal:id $source)))
(= (egal:proposition $source) (mg:proposition (egal:known $source)))
