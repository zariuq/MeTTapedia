; The Lean reading as a live kernel theory.
;
; The document that check.sh hands to the two checkers is assembled here from
; the same files in the same order and checked once, in process, by the
; Megalodon kernel of CeTTa.  What it builds is a theory: every definition
; and theorem of the reading is then a kernel object, found by its name in
; the source text.
;
;   (lean:open PREAMBLE ROOT WORK)  assemble ROOT's document in WORK and check
;                                   it after the signature PREAMBLE; answers
;                                   (LeanSession VERDICT SUMMARY)
;   (lean:theory)                   the theory of the open session
;   (lean:id NAME)                  the kernel's name of the declaration whose
;                                   source name is NAME
;   (lean:arity NAME)               the arguments it takes as a function of the
;                                   logic
;   (lean:known NAME)               the theorem named NAME
;   (lean:proposition NAME)         what it states
;
; Import megalodon, fs and str first.

; The files of the document, in checking order.  A library that the function
; document already embeds is not read a second time.
(= (lean:parts-before-functions)
   ("Library/Conversion.mg" "Library/Quotients.mg" "Library/EquivalenceClosure.mg"
    "Library/RankedRecursion.mg" "LeanInEgal.mg" "Library/Typing.mg" "Library/QuotientTyping.mg"
    "Library/Digits.mg" "generated/LeanFamilies.mg" "Library/EqFacts.mg" "Library/QuotientProofs.mg"
    "FamilyFacts.mg" "Numerals.mg" "Decidable.mg" "Library/NumeralDecisions.mg"
    "Library/AlgebraicStructures.mg" "Library/NatAlgebra.mg" "Library/Propositions.mg"))
(= (lean:parts-after-functions)
   ("Library/DecideFacts.mg" "Library/NatAdd.mg" "Library/NatMul.mg" "Library/NatSub.mg"
    "Library/NatDecide.mg" "Library/NatDiv.mg"))
(= (lean:path $root $relative) (format-args "{}/{}" ($root $relative)))
(= (lean:embedded $functions $relative)
   (case (str:find $functions (format-args "(** Embedded proof support: {} **)\n" ($relative)))
     (((TextNotFound $_) False) ($_ True))))
(= (lean:texts $root $relatives)
   (if (== $relatives ()) ()
       (cons-atom (fs:read-text (lean:path $root (car-atom $relatives)))
                  (lean:texts $root (cdr-atom $relatives)))))
(= (lean:not-embedded $functions $relatives)
   (if (== $relatives ()) ()
       (if (lean:embedded $functions (car-atom $relatives))
           (lean:not-embedded $functions (cdr-atom $relatives))
           (cons-atom (car-atom $relatives) (lean:not-embedded $functions (cdr-atom $relatives))))))
(= (lean:document-text $root)
   (let* (($functions (fs:read-text (lean:path $root "generated/LeanFunctions.mg")))
          ($before (str:join "" (lean:texts $root (lean:parts-before-functions))))
          ($after (str:join "" (lean:texts $root (lean:not-embedded $functions (lean:parts-after-functions)))))
          ($computations (fs:read-text (lean:path $root "generated/LeanComputations.mg"))))
     (str:join "" ($before $functions $after $computations))))

(= (lean:open $preamble $root $work)
   (let* (($document (format-args "{}/lean-document.mg" ($work)))
          ($_written (fs:write $document (lean:document-text $root)))
          ($result (mg:check-document ($preamble) $document ((theory egal)))))
     (case $result
       (((Megalodon.document $theory $authority $verdict $summary $entries)
         (let $_kept (add-atom &self (LeanSessionTheory $theory))
           (LeanSession $verdict $summary)))
        ($other $other)))))
(= (lean:theory) (match &self (LeanSessionTheory $theory) $theory))

; Names.  The kernel names a declaration by its content; the source name is a
; key that finds it.  Each answer is kept, with the declaration's type.
; A declaration is (KIND ID TYPE-OR-STATEMENT PROVENANCE ..): its provenance
; (source, also, origin) varies, so it is read by position.
(= (lean:declared $declaration)
   (let* (($kind (car-atom $declaration))
          ($id (car-atom (cdr-atom $declaration)))
          ($third (car-atom (cdr-atom (cdr-atom $declaration)))))
     (if (or (== $kind Megalodon.definition) (== $kind Megalodon.parameter))
         (LeanDeclared $id $third)
         (LeanDeclared $id (Tp.prop)))))
(= (lean:found $found $source)
   (case $found
     (((Megalodon.found) (Error (LeanName $source) (LeanSession "no declaration has this source name")))
      ($_ (lean:declared (car-atom (cdr-atom $found)))))))
(= (lean:declaration $source)
   (let $kept (collapse (match &self (LeanKernelName $source $declared) $declared))
     (if (== $kept ())
         (let $declared (lean:found (mg:lookup (lean:theory) $source) $source)
           (let $_kept (add-atom &self (LeanKernelName $source $declared)) $declared))
         (car-atom $kept))))
(= (lean:id $source)
   (case (lean:declaration $source) (((LeanDeclared $id $type) $id) ($other $other))))
; How many arguments the declaration takes as a function of the logic (a set
; takes none: applying a set is the set-theoretic application ap).
(= (lean:arrows $type) (case $type (((Tp.arr $a $b) (+ 1 (lean:arrows $b))) ($_ 0))))
(= (lean:arity $source)
   (case (lean:declaration $source) (((LeanDeclared $id $type) (lean:arrows $type)) ($other 0))))
(= (lean:known $source) (mg:known (lean:theory) (lean:id $source)))
(= (lean:proposition $source) (mg:proposition (lean:known $source)))
