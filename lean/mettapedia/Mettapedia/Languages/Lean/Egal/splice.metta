; Typing lemmas proved in Egal by hand.
;
;   cetta --lang petta splice.metta facts DIR OUT        writes (TypingProof Lean_X) for each DIR/Lean_X_In.mgproof
;                                                         and (LemmaProof Lean_X) for each DIR/Lean_X_proof.mgproof
;   cetta --lang petta splice.metta splice DIR FILE...   replaces each line "PROOF-FILE NAME" with DIR/NAME.mgproof
;
; The statements are generated from the functions' declared types, and from
; the statements of the theorems that Lean's proof terms cite; only the proofs
; are written by hand, in proofs/functions/.  A marker without its proof file
; is an error (exit status 1).

!(import! &self fs)
!(import! &self str)
!(import! &self system)

(= (append-lists $xs $ys) (if (== $xs ()) $ys (cons-atom (car-atom $xs) (append-lists (cdr-atom $xs) $ys))))

; The names of a directory's entries.
(= (entries $owner $acc)
   (case (fs:next-entry $owner)
     (((fs:entry $name $kind $i) (entries $owner (cons-atom $name $acc)))
      ($_ (let $closed (fs:close $owner) $acc)))))

; Names in byte order (insertion sort).
(= (insert-name $x $ys)
   (if (== $ys ()) ($x)
       (if (< (str:compare $x (car-atom $ys)) 0) (cons-atom $x $ys)
           (cons-atom (car-atom $ys) (insert-name $x (cdr-atom $ys))))))
(= (sort-names $xs) (if (== $xs ()) () (insert-name (car-atom $xs) (sort-names (cdr-atom $xs)))))

(= (proof-names $names)
   (if (== $names ()) ()
       (let* (($n (car-atom $names)) ($rest (proof-names (cdr-atom $names))))
         (if (str:ends-with $n "_In.mgproof")
             (cons-atom (str:byte-slice $n 0 (- (str:byte-length $n) 11)) $rest)
             $rest))))
(= (lemma-names $names)
   (if (== $names ()) ()
       (let* (($n (car-atom $names)) ($rest (lemma-names (cdr-atom $names))))
         (if (str:ends-with $n "_proof.mgproof")
             (cons-atom (str:byte-slice $n 0 (- (str:byte-length $n) 14)) $rest)
             $rest))))

(= (write-facts $dir $out)
   (let* (($all (entries (fs:open-directory $dir) ()))
          ($names (sort-names (proof-names $all))) ($lemmas (sort-names (lemma-names $all))))
     (fs:write $out (str:join "" (append-lists (fact-lines "TypingProof" $names) (fact-lines "LemmaProof" $lemmas))))))
(= (fact-lines $kind $ns)
   (if (== $ns ()) ()
       (cons-atom (format-args "({} {})\n" ($kind (car-atom $ns))) (fact-lines $kind (cdr-atom $ns)))))

; Each marker line is replaced by its proof, without its final newlines.
(= (strip-newlines $t)
   (if (str:ends-with $t "\n") (strip-newlines (str:byte-slice $t 0 (- (str:byte-length $t) 1))) $t))
(= (spliced $dir $lines)
   (if (== $lines ()) ()
       (let* (($l (car-atom $lines)) ($rest (spliced $dir (cdr-atom $lines))))
         (if (str:starts-with $l "PROOF-FILE ")
             (let* (($name (car-atom (cdr-atom (str:split-whitespace $l))))
                    ($path (format-args "{}/{}.mgproof" ($dir $name))))
               (if (fs:exists $path) (cons-atom (strip-newlines (fs:read-text $path)) $rest)
                   (let $_e (system:write stderr (format-args "splice: no proof file for {}\n" ($name))) (system:exit 1))))
             (cons-atom $l $rest)))))
(= (splice-file $dir $path)
   (fs:write $path (str:join "\n" (spliced $dir (str:split "\n" (fs:read-text $path))))))
(= (splice-all $dir $paths)
   (if (== $paths ()) () (let $done (splice-file $dir (car-atom $paths)) (splice-all $dir (cdr-atom $paths)))))

!(let* (($args (system:args)) ($mode (car-atom $args)) ($dir (car-atom (cdr-atom $args))) ($rest (cdr-atom (cdr-atom $args))))
   (if (== (format-args "{}" ($mode)) "facts") (write-facts $dir (car-atom $rest))
   (if (== (format-args "{}" ($mode)) "splice") (splice-all $dir $rest)
       (let $_e (system:write stderr "usage: splice.metta facts DIR OUT | splice DIR FILE...\n") (system:exit 1)))))
