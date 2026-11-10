; The evidence of a carried Lean development, one row per manifest constant,
; and the qualification of each expected test.
;
;   cetta --lang petta DECLS/terms.metta DECLS/families.metta evidence.metta \
;         EVIDENCE.tsv QUALIFICATION.tsv SUMMARY.txt DECLS GEN
;
; DECLS is artifacts/lean-declarations/TARGET (terms.metta and families.metta,
; read as the programs before this one; manifest.tsv; display-exclusions.tsv);
; GEN holds the generated Families.mg, Functions.mg, Theorems.mg,
; Computations.mg, Skipped.txt and Outcomes.tsv.
;
; Each constant gets one evidence kind:
;
;   interpretation         read into Egal: a family, a constructor, a recursor, a
;                          case analysis, a projection, or a function whose Lean
;                          equation theorems are proved from its reading
;   target-reconstruction  a theorem whose statement is read from Lean and proved
;                          in Egal
;   unfolded               reducible, or an instance whose projections Lean
;                          unfolds; read through its body where it is used
;   expanded               a matcher, read by its definition at each use
;   replaced               no confusion and injectivity, proved for the family in Egal
;   not-needed             no read definition, equation, theorem or test uses it;
;                          the detail says what it is
;   display-excluded       a derived display instance
;   refused                a named refusal; the detail says why and which tests it
;                          leaves unqualified
;
; The tests are those of Outcomes.tsv.  A joined test's dependencies are every
; definition and theorem of the generated document that its Egal theorem
; reaches through the names their statements and proofs use, transitively;
; each belongs to the Lean constant whose Egal name is its longest prefix.  The
; test is qualified when every constant it depends on has interpretation
; evidence (or is unfolded or expanded); otherwise it is unqualified, with the
; constants that make it so.  The joined tests must be exactly those with a
; theorem.  A missing input or a disagreement is an error (exit status 1).

!(import! &self fs)
!(import! &self str)
!(import! &self re)
!(import! &self system)

; ---- lists and text ----
(= (append-lists $xs $ys) (if (== $xs ()) $ys (cons-atom (car-atom $xs) (append-lists (cdr-atom $xs) $ys))))
(= (len-of $xs) (if (== $xs ()) 0 (+ 1 (len-of (cdr-atom $xs)))))
(= (nth-of $xs $k) (if (== $k 0) (car-atom $xs) (nth-of (cdr-atom $xs) (- $k 1))))
(= (in-list $x $xs) (if (== $xs ()) False (if (== (car-atom $xs) $x) True (in-list $x (cdr-atom $xs)))))
; PeTTa reads the symbols True and False as its truth values.
(= (str-of $x) (if (== $x False) "False" (if (== $x True) "True" (format-args "{}" ($x)))))
(= (insert-str $x $ys)
   (if (== $ys ()) ($x)
       (if (< (str:compare $x (car-atom $ys)) 0) (cons-atom $x $ys) (cons-atom (car-atom $ys) (insert-str $x (cdr-atom $ys))))))
(= (sort-strs $xs) (if (== $xs ()) () (insert-str (car-atom $xs) (sort-strs (cdr-atom $xs)))))
(= (insert-num $x $ys)
   (if (== $ys ()) ($x) (if (< $x (car-atom $ys)) (cons-atom $x $ys) (cons-atom (car-atom $ys) (insert-num $x (cdr-atom $ys))))))
(= (sort-nums $xs) (if (== $xs ()) () (insert-num (car-atom $xs) (sort-nums (cdr-atom $xs)))))
(= (dedup $xs $seen)
   (if (== $xs ()) ()
       (if (in-list (car-atom $xs) $seen) (dedup (cdr-atom $xs) $seen)
           (cons-atom (car-atom $xs) (dedup (cdr-atom $xs) (cons-atom (car-atom $xs) $seen))))))
(= (tsv-rows $path)
   (if (fs:exists $path) (cdr-atom (nonempty (fs:read-lines $path))) ()))
(= (nonempty $ls) (if (== $ls ()) () (if (== (car-atom $ls) "") (nonempty (cdr-atom $ls)) (cons-atom (car-atom $ls) (nonempty (cdr-atom $ls))))))
(= (fields $line) (str:split "\t" $line))
(= (identifier-text $x)
   (if (== (get-type $x) String) (str-of $x)
       (let $_error (system:write stderr (format-args "evidence: non-text identifier {}\n" ($x)))
         (system:exit 1))))
(= (join-comma $xs) (str:join "," (map-atom $xs $x (identifier-text $x))))

; ---- the declarations, as string-keyed facts ----
; add-atom stores its argument as written: values are computed first.
(= (source-obligations $c $thms)
   (let $sources (collapse (match &self (LeanSourceEquations $c $qs) $qs))
     (dedup (append-lists $thms (if (== $sources ()) () (car-atom $sources))) ())))
(= (put2 $tag $a $b) (let* (($x (str-of $a)) ($y $b)) (add-atom &self ($tag $x $y))))
(= (put1 $tag $a) (let $x (str-of $a) (add-atom &self ($tag $x))))
(= (load-facts)
   (let* (($a (collapse (match &self (EgalName $c $e) (put2 EgalS $c (str-of $e)))))
          ($b (collapse (match &self (LeanFunction $c $thms)
                (put2 FnS $c (map-atom (source-obligations $c $thms) $q (str-of $q))))))
          ($c1 (collapse (match &self (LeanEquation $c $bs $T $l $r) (put1 EqS $c))))
          ($d (collapse (match &self (LeanMatcher $c $bs $body) (put1 MatcherS $c))))
          ($f (collapse (match &self (LeanCasesOn $c $F) (put2 CasesS $c (str-of $F)))))
          ($g (collapse (match &self (LeanProjection $c $S $k $i $np) (put1 ProjS $c))))
          ($h (collapse (match &self (LeanTheorem $c $P) (put1 ThmS $c))))
          ($i (collapse (match &self (LeanReducible $c) (put1 RedS $c))))
          ($j (collapse (match &self (LeanInstance $c) (put1 InstS $c))))
          ($k (collapse (match &self (LeanFunctionRefused $c $why) (put2 RefFnS $c (str-of $why)))))
          ($primitives (collapse (match &self (LeanIntrinsic $c $kind $bs $R)
            (let $_kind (put2 PrimS $c (str-of $kind))
              (put2 PrimRequiredS $c (map-atom (source-obligations $c ()) $q (str-of $q)))))))
          ($primitiveLaws (collapse (match &self (LeanPrimitiveLaw $c $law) (put2 PrimLawS $c (str-of $law)))))
          ($profiles (collapse (match &self (LeanUniverseProfile $c $kind $levels) (put2 ProfileS $c (str-of $kind)))))
          ($l (collapse (match &self (LeanAdmitted $c $u) (put1 FamS $c))))
          ($m (collapse (match &self (LeanFamily (Family $F $ps $is $srt $cs) $u $el $n) (put1 FamS $F))))
          ($o (collapse (match &self (LeanFamily (Family $F $ps $is $srt (constructors $cs)) $u $el $n)
                 (map-atom $cs $entry (put1 CtorS (car-atom (car-atom (cdr-atom $entry)))))))))
     ok))

(= (egal-of $c) (let $es (collapse (match &self (EgalS $c $e) $e)) (if (== $es ()) "" (car-atom $es))))
(= (has $q) (if (== (collapse (match &self $q True)) ()) False True))

; Constants the reading uses: every constant applied in a read equation,
; matcher, theorem statement, test, or family field.
(= (app-heads $t)
   (if (== (get-metatype $t) Expression)
       (if (== $t ()) ()
           (let $rest (app-heads-list $t)
             (if (== (car-atom $t) app)
                 (let $h (car-atom (cdr-atom $t)) (if (== (get-metatype $h) Symbol) (cons-atom (str-of $h) $rest) $rest))
                 $rest)))
       ()))
(= (app-heads-list $ts) (if (== $ts ()) () (append-lists (app-heads (car-atom $ts)) (app-heads-list (cdr-atom $ts)))))
(= (load-read)
   (let* (($ts (append-lists (collapse (match &self (LeanEquation $c $bs $T $l $r) ($bs $T $l $r)))
                (append-lists (collapse (match &self (LeanMatcher $c $bs $body) ($bs $body)))
                (append-lists (collapse (match &self (LeanTheorem $c $P) ($P)))
                (append-lists (collapse (match &self (LeanComputation $i $t $ty) ($t $ty)))
                (append-lists (collapse (match &self (LeanFamily $x $u $el $n) ($x)))
                              (collapse (match &self (LeanAdmitted $c $u) ($u)))))))))
          ($hs (app-heads-list $ts)))
     (map-atom $hs $h (if (has (ReadS $h)) () (add-atom &self (ReadS $h))))))

; ---- the generated document ----
(= (name-after $line $k)
   (let $rest (str:byte-slice $line $k (str:byte-length $line))
     (let $m (re:find (re:compile "^[A-Za-z0-9_]+") $rest)
       (case $m (((re:match $a $b $caps) (str:byte-slice $rest $a $b)) ($_ ""))))))
(= (defined-name $line)
   (if (str:starts-with $line "Definition ") (name-after $line 11)
       (if (str:starts-with $line "Theorem ") (name-after $line 8) "")))
(= (load-defined $gen)
   (map-atom ("Families.mg" "Functions.mg" "Theorems.mg") $f
     (map-atom (fs:read-lines (format-args "{}/{}" ($gen $f))) $l
       (let $n (defined-name $l) (if (== $n "") () (add-atom &self (Defined $n)))))))
(= (is-defined $e) (if (== $e "") False (has (Defined $e))))

; External implementations remain reachable even when a source contract is
; missing. Otherwise omitting a contract would erase the dependency itself.
(= (load-primitive-names)
   (collapse (match &self (PrimS $c $kind)
     (let $name (egal-of $c)
       (if (== $name "") () (if (is-defined $name) () (add-atom &self (Defined $name))))))))
(= (load-primitive-refs)
   (collapse (match &self (PrimS $c $kind)
     (let* (($name (egal-of $c)) ($contract (str:concat $name "_source_type"))
            ($_type (if (is-defined $contract) (add-atom &self (Ref $name $contract)) ())))
       (collapse (match &self (PrimLawS $c $law)
         (let $target (egal-of $law)
           (if (is-defined $target) (add-atom &self (Ref $name $target)) ()))))))))
(= (primitive-evidence $c)
   (let* (($name (egal-of $c)) ($contract (str:concat $name "_source_type"))
          ($kind (car-atom (collapse (match &self (PrimS $c $kind) $kind))))
          ($laws (collapse (match &self (PrimLawS $c $law) $law)))
          ($required (car-atom (collapse (match &self (PrimRequiredS $c $qs) $qs))))
          ($unproved (unproved-list (append-lists $laws $required))))
     (if (not (is-defined $contract)) (ev refused $name "quotient primitive source typing contract missing")
     (if (not (== (len-of $laws) (if (== $kind "type") 0 1)))
         (ev refused $name "quotient primitive kernel-law inventory incomplete or ambiguous")
     (if (not (== $unproved ())) (ev refused $name "quotient primitive source law contract missing")
         (ev interpretation $name "Type-carrier quotient profile; source typing and kernel-law contracts proved"))))))

(= (load-skipped $gen)
   (map-atom (fs:read-lines (format-args "{}/Skipped.txt" ($gen))) $l
     (let $t (str:trim $l)
       (if (or (str:starts-with $t "function ") (str:starts-with $t "theorem "))
           (let* (($sp (str:find $t " ")) ($rest (str:byte-slice $t (+ $sp 1) (str:byte-length $t)))
                  ($k (str:find $rest ": ")))
             (if (< $k 0) ()
                 (let* (($c (str:byte-slice $rest 0 $k)) ($w (str:byte-slice $rest (+ $k 2) (str:byte-length $rest))))
                   (add-atom &self (SkipS $c $w)))))
           ()))))
(= (skip-reason $c $default)
   (let $ws (collapse (match &self (SkipS $c $w) $w)) (if (== $ws ()) $default (car-atom $ws))))

; The references of the document: each definition or theorem, from its line
; to the next one's, uses the defined names its text mentions.
(= (ident-pattern) (re:compile "[A-Za-z_][A-Za-z0-9_]*"))
(= (spans-text $ms $text)
   (case $ms
     ((LNil ())
      ((LCons (re:match $a $b $caps) $rest) (cons-atom (str:byte-slice $text $a $b) (spans-text $rest $text))))))
(= (idents $text) (case (re:find-all (ident-pattern) $text) (((re:matches $ms) (spans-text $ms $text)) ($_ ()))))
(= (add-refs $node $lines)
   (map-atom (idents (str:join " " $lines)) $i
     (if (== $i $node) () (if (has (Defined $i)) (if (has (Ref $node $i)) () (add-atom &self (Ref $node $i))) ()))))
; An Opaque or Transparent directive ends a block and belongs to none.
(= (directive $l) (or (str:starts-with $l "Opaque ") (str:starts-with $l "Transparent ")))
(= (scan-blocks $lines $node $acc)
   (if (== $lines ()) (if (== $node "") () (add-refs $node $acc))
       (let* (($l (car-atom $lines)) ($n (defined-name $l)))
         (if (directive $l)
             (let $done (if (== $node "") () (add-refs $node $acc)) (scan-blocks (cdr-atom $lines) "" ()))
         (if (== $n "") (scan-blocks (cdr-atom $lines) $node (cons-atom $l $acc))
             (let $done (if (== $node "") () (add-refs $node $acc))
               (scan-blocks (cdr-atom $lines) $n ($l))))))))
(= (load-refs $gen)
   (map-atom ("Families.mg" "Functions.mg" "Theorems.mg" "Computations.mg") $f
     (scan-blocks (fs:read-lines (format-args "{}/{}" ($gen $f))) "" ())))
; Required source equations are semantic dependencies of a fuel reading,
; even when its computation proof only cites the fuel bridge.
(= (load-source-obligation-refs)
   (collapse (match &self (LeanSourceEquations $c $qs)
     (let $owner (egal-of (str-of $c))
       (map-atom $qs $q
         (let $required (egal-of (str-of $q))
           (if (and (is-defined $owner) (is-defined $required))
               (if (has (Ref $owner $required)) () (add-atom &self (Ref $owner $required))) ())))))))
(= (load-test-names $gen)
   (map-atom (fs:read-lines (format-args "{}/Computations.mg" ($gen))) $l
     (let $n (defined-name $l) (if (== $n "") () (add-atom &self (Defined $n))))))

; Everything a test's theorem reaches, recorded as (Seen root name).
(= (reach $root $todo)
   (if (== $todo ()) ok
       (let $n (car-atom $todo)
         (if (has (Seen $root $n)) (reach $root (cdr-atom $todo))
             (let $_a (add-atom &self (Seen $root $n))
               (reach $root (append-lists (collapse (match &self (Ref $n $m) $m)) (cdr-atom $todo))))))))

; The constant a defined name belongs to: the longest Egal name it begins with.
(= (owner-of $name)
   (let $memo (collapse (match &self (OwnerS $name $c) $c))
     (if (not (== $memo ())) (car-atom $memo)
         (let* (($parts (str:split "_" $name)) ($c (owner-prefix $parts (len-of $parts))) ($_a (add-atom &self (OwnerS $name $c))))
           $c))))
(= (owner-prefix $parts $k)
   (if (< $k 2) None
       (let* (($p (str:join "_" (take-k $parts $k))) ($cs (collapse (match &self (EgalS $c $p) $c))))
         (if (== $cs ()) (owner-prefix $parts (- $k 1)) (car-atom $cs)))))
(= (take-k $xs $k) (if (or (== $k 0) (== $xs ())) () (cons-atom (car-atom $xs) (take-k (cdr-atom $xs) (- $k 1)))))
(= (owners $names)
   (if (== $names ()) ()
       (let $o (owner-of (car-atom $names)) (if (== $o None) (owners (cdr-atom $names)) (cons-atom $o (owners (cdr-atom $names)))))))

(= (test-name $i) (if (< $i 10) (format-args "Lean_test_0{}" ($i)) (format-args "Lean_test_{}" ($i))))

; ---- classification ----
(= (unused-ev)
   (ev not-needed "" "no read definition, equation, theorem or test uses it; Lean reaches it through type classes whose instances are unfolded, or through display and panic messages"))
(= (helper-reasons)
   (("\\.(brecOn|below)(_\\d+)?(\\.go|\\.eq)?$|\\._f$|\\._unsafe_rec$|\\._sunfold$|\\.eq_def$|\\.splitter$|\\.match_\\d+\\.eq_\\d+$|\\.go$"
     "Lean's compilation of recursion and matching; the reading takes each function from its equation theorems and each matcher from its definition")
    ("\\.(recOn|elim|ctorElim|ctorElimType|ctorIdx)$|\\._sparseCasesOn_\\d+$|\\._flat_ctor$"
     "an eliminator Lean derives from the recursor; the reading uses the recursor")
    ("sizeOf" "Lean's size measure for termination; not part of the development's meaning")
    ("\\._proof_\\d+$" "a proof inside a definition; proofs are irrelevant in the interpretation (0)")))
(= (helper-ev $c $rs)
   (if (== $rs ()) None
       (let ($p $why) (car-atom $rs)
         (if (re:is-match (re:compile $p) $c) (ev not-needed "" $why) (helper-ev $c (cdr-atom $rs))))))
(= (short $c) (re:replace-literal (re:compile "^_private\\.[A-Za-z0-9_.]*?\\.0\\.") $c ""))
(= (family-of-rec $c)
   (let $parts (str:split "." $c) (if (< (len-of $parts) 2) $c (str:join "." (take-k $parts (- (len-of $parts) 1))))))
(= (unproved-eqns $c)
   (let $qs (car-atom (collapse (match &self (FnS $c $thms) $thms))) (unproved-list $qs)))
(= (unproved-list $qs)
   (if (== $qs ()) ()
       (let $rest (unproved-list (cdr-atom $qs))
         (if (is-defined (egal-of (car-atom $qs))) $rest (cons-atom (car-atom $qs) $rest)))))
(= (profile-detail $c)
   (if (has (ProfileS $c $kind)) "; restricted to the declared Type universe profile" ""))

(= (classify $c $kind $role)
   (let $e (egal-of $c)
     (let $dw (collapse (match &self (DisplayS $c $w) $w))
     (if (not (== $dw ())) (ev display-excluded "" (car-atom $dw))
     (if (has (PrimS $c $primitiveKind)) (primitive-evidence $c)
     ; Source equations prove the function interpretation even when their
     ; target proof was supplied through the theorem-reconstruction path.
     (if (and (== $kind "theorem") (and (has (ThmS $c)) (not (has (EqS $c)))))
         (if (is-defined $e) (ev target-reconstruction $e "statement read from Lean, proved in Egal")
             (ev refused $e (skip-reason $c "statement read, not proved here yet")))
     (if (== $c "And") (ev interpretation "" "read as Egal's conjunction in statements")
     (if (== $c "Or") (ev interpretation "" "read as Egal's disjunction in statements")
     (if (== $kind "inductive")
         (if (is-defined $e) (ev interpretation $e "family")
             (if (has (ReadS $c)) (ev refused $e "family used by the reading but not read") (unused-ev)))
     (if (== $kind "constructor")
         (if (is-defined (str:concat $e "_node")) (ev interpretation (str:concat $e "_node") "constructor")
         (if (is-defined (str:concat $e "_b_node")) (ev interpretation (str:concat $e "_b_node") "constructor of a nested block, read with the block")
             (if (has (ReadS $c)) (ev refused $e "constructor of a family not read") (unused-ev))))
     (if (== $kind "recursor")
         (let $fe (egal-of (family-of-rec $c))
           (if (is-defined (str:concat $fe "_prec")) (ev interpretation (str:concat $fe "_prec") "the recursor of a family of propositions")
           (if (is-defined (str:concat $fe "_rec")) (ev interpretation (str:concat $fe "_rec") "the family's recursor, with its computation rules")
           (if (is-defined (str:concat $fe "_b_rec")) (ev interpretation (str:concat $fe "_b_rec") "the recursor of the family's nested block")
               (if (has (ReadS $c)) (ev refused "" "recursor of a family not read") (unused-ev))))))
     (if (is-defined (str:concat $e "_canon"))
         (ev refused $e "decision procedure read by its type (the canonical element of Decidable p), not yet from its definition")
     (let $cf (collapse (match &self (CasesS $c $F) $F))
     (if (not (== $cf ()))
         (let $fe (egal-of (car-atom $cf))
           (if (is-defined (str:concat $fe "_casesOn"))
               (ev interpretation (str:concat $fe "_casesOn") "case analysis read as the family's case eliminator")
               (ev interpretation (if (is-defined (str:concat $fe "_rec")) (str:concat $fe "_rec") (str:concat $fe "_b_rec"))
                   "case analysis read as the recursor with the minors as methods")))
     (if (has (ProjS $c))
         (if (is-defined $e) (ev interpretation $e "projection") (ev refused $e "projection not read"))
     (if (has (FnS $c $any))
         (if (not (is-defined $e)) (ev refused $e (skip-reason $c "function not read"))
             (let $un (unproved-eqns $c)
               (if (== $un ()) (ev interpretation $e
                 (str:concat "function read from its equation theorems; Lean's equations proved" (profile-detail $c)))
                   (ev refused $e (str:concat "function read, but not all of Lean's equation theorems are proved from the reading: "
                                    (str:join ", " (map-atom $un $q (short $q))))))))
     (let $rw (collapse (match &self (RefFnS $c $w) $w))
     (if (not (== $rw ())) (ev refused $e (car-atom $rw))
     (if (has (EqS $c))
         (if (is-defined $e) (ev interpretation $e "Lean's equation theorem, proved from the reading")
             (ev refused $e "equation theorem not proved from the reading"))
     (if (has (MatcherS $c)) (ev expanded "" "matcher, read by its definition at each use")
     (if (re:is-match (re:compile "\\.(noConfusion|noConfusionType|inj|injEq)$") $c)
         (ev replaced "" "no confusion and injectivity are proved for the family in Egal (_noconf, _inj)")
     (if (has (InstS $c)) (ev unfolded "" "instance: Lean unfolds it where it is used, and the reading reads the result")
     (if (has (RedS $c)) (ev unfolded "" "reducible definition: Lean unfolds it where it is used, and the reading reads the result")
     (let $hv (helper-ev $c (helper-reasons))
       (if (not (== $hv None)) $hv
           (if (== $kind "theorem") (ev not-needed "" "a theorem Lean's proofs use; the theorems are reconstructed in Egal, not transported")
               (ev not-needed "" "no read definition, equation, theorem or test uses it")))))))))))))))))))))))))))

(= (ev-kind $v) (case $v (((ev $k $e $d) $k))))
(= (qualifying $k) (or (== $k interpretation) (or (== $k unfolded) (== $k expanded))))

; ---- rows: the manifest's, display instances, and the constants the reading adds ----
(= (manifest-rows $decls)
   (let $hdr (fields (car-atom (fs:read-lines (format-args "{}/manifest.tsv" ($decls)))))
     (map-atom (tsv-rows (format-args "{}/manifest.tsv" ($decls))) $l
       (let $fs (fields $l) (row (nth-of $fs (col $hdr "constant" 0)) (nth-of $fs (col $hdr "role" 0)) (nth-of $fs (col $hdr "kind" 0)))))))
(= (col $hdr $name $i) (if (== (car-atom $hdr) $name) $i (col (cdr-atom $hdr) $name (+ $i 1))))
(= (row-c $r) (case $r (((row $c $role $kind) $c))))
(= (extra-rows $listed)
   (let* (($disp (sort-strs (filter-out (collapse (match &self (DisplayS $c $w) $c)) $listed)))
          ($drows (map-atom $disp $c (row $c "display" "definition")))
          ($listed2 (append-lists $listed $disp))
          ($eg (sort-strs (filter-out (dedup (collapse (match &self (EgalS $c $e) $c)) ()) $listed2))))
     (append-lists $drows
       (map-atom $eg $c (row $c "reading"
         (if (or (has (ThmS $c)) (has (EqS $c))) "theorem"
             (if (has (FamS $c)) "inductive" (if (has (CtorS $c)) "constructor" "definition"))))))))
(= (filter-out $xs $ys)
   (if (== $xs ()) () (if (in-list (car-atom $xs) $ys) (filter-out (cdr-atom $xs) $ys) (cons-atom (car-atom $xs) (filter-out (cdr-atom $xs) $ys)))))

; ---- tests ----
(= (outcome-rows $gen)
   (map-atom (tsv-rows (format-args "{}/Outcomes.tsv" ($gen))) $l
     (let $fs (fields $l) (oc (str:string->number (nth-of $fs 0)) (nth-of $fs 1) (if (< (len-of $fs) 3) "" (nth-of $fs 2))))))
(= (joined-ids $ocs) (if (== $ocs ()) () (case (car-atom $ocs) (((oc $i $o $w) (if (== $o "joined") (cons-atom $i (joined-ids (cdr-atom $ocs))) (joined-ids (cdr-atom $ocs))))))))
(= (theorem-ids $gen)
   (let $ls (fs:read-lines (format-args "{}/Computations.mg" ($gen))) (theorem-ids-of $ls)))
(= (theorem-ids-of $ls)
   (if (== $ls ()) ()
       (let* (($l (car-atom $ls)) ($rest (theorem-ids-of (cdr-atom $ls))))
         (if (str:starts-with $l "Theorem Lean_test_")
             (let $ws (str:split-whitespace $l)
               (if (== (nth-of $ws 2) ":")
                   (let $d (str:byte-slice (nth-of $ws 1) 10 (str:byte-length (nth-of $ws 1)))
                     (if (str:is-all-in digit $d) (cons-atom (str:string->number $d) $rest) $rest))
                   $rest))
             $rest))))

; The constants a joined test depends on, each once.
(= (test-deps $i)
   (let* (($root (test-name $i)) ($_r (reach $root ($root)))
          ($os (owners (collapse (match &self (Seen $root $n) $n))))
          ($_d (map-atom $os $o (if (has (DepS $i $o)) () (add-atom &self (DepS $i $o))))))
     (collapse (match &self (DepS $i $o) $o))))

(= (main $out-ev $out-q $out-s $decls $gen)
   (let* (($f (load-facts)) ($r (load-read))
          ($dd (map-atom (tsv-rows (format-args "{}/display-exclusions.tsv" ($decls))) $l
                 (let* (($fs (fields $l)) ($c (nth-of $fs 0)) ($w (nth-of $fs 1))) (add-atom &self (DisplayS $c $w)))))
          ($df (load-defined $gen)) ($primitiveNames (load-primitive-names))
          ($tn (load-test-names $gen)) ($sk (load-skipped $gen)) ($rf (load-refs $gen))
          ($primitiveRefs (load-primitive-refs))
          ($sourceRefs (load-source-obligation-refs))
          ($rows0 (if (fs:exists (format-args "{}/manifest.tsv" ($decls))) (manifest-rows $decls) ()))
          ($rows (append-lists $rows0 (extra-rows (map-atom $rows0 $x (row-c $x)))))
          ($evs (map-atom $rows $x (case $x (((row $c $role $kind) (let $v (classify $c $kind $role) (let $_a (add-atom &self (EvS $c $v)) ($c $v))))))))
          ($ocs (outcome-rows $gen))
          ($joined (sort-nums (joined-ids $ocs))) ($thms (sort-nums (theorem-ids $gen))))
     (if (not (== $joined $thms))
         (let $_e (system:write stderr (format-args "evidence: tests with a theorem {} and joined tests {} of Outcomes.tsv differ\n" ($thms $joined)))
           (system:exit 1))
     (let* (($deps (map-atom $joined $i ($i (test-deps $i))))
            ($bad (map-atom $deps $d (case $d ((($i $cs) ($i (sort-strs (bad-of $cs $evs))))))))
            ($evtext (ev-lines $rows $evs $bad))
            ($qtext (q-lines $ocs $deps $bad))
            ($w1 (fs:write $out-ev (str:concat "constant\trole\tkind\tevidence\tegal\tdetail\n" $evtext)))
            ($w2 (fs:write $out-q (str:concat "test\tstatus\tconstants\tunresolved\treason\n" $qtext)))
            ($nq (count-bad $bad 0))
            ($absent (dedup (absent-of (deps-all $deps) $evs) ())))
       (fs:write $out-s
         (str:concat
           (format-args "evidence: {}; {} constants\ntests: {} expected; {} joined ({} qualified, {} unqualified), {} refused\n"
             ((kind-counts $evs $absent) (len-of $rows)
              (len-of $ocs) (len-of $joined) (- (len-of $joined) $nq) $nq (- (len-of $ocs) (len-of $joined))))
           (if (== $absent ()) ""
               (format-args "used by tests but absent from the manifest: {}\n" ((str:join ", " (sort-strs $absent)))))))))))

(= (ev-of $c $evs) (let $vs (collapse (match &self (EvS $c $v) $v)) (if (== $vs ()) None (car-atom $vs))))
(= (bad-of $cs $evs)
   (if (== $cs ()) ()
       (let* (($c (car-atom $cs)) ($v (ev-of $c $evs)) ($rest (bad-of (cdr-atom $cs) $evs)))
         (if (== $v None) (cons-atom $c $rest) (if (qualifying (ev-kind $v)) $rest (cons-atom $c $rest))))))
(= (deps-all $deps) (if (== $deps ()) () (case (car-atom $deps) ((($i $cs) (append-lists $cs (deps-all (cdr-atom $deps))))))))
(= (absent-of $cs $evs)
   (if (== $cs ()) () (if (== (ev-of (car-atom $cs) $evs) None) (cons-atom (car-atom $cs) (absent-of (cdr-atom $cs) $evs)) (absent-of (cdr-atom $cs) $evs))))
(= (count-bad $bad $n) (if (== $bad ()) $n (case (car-atom $bad) ((($i $cs) (count-bad (cdr-atom $bad) (if (== $cs ()) $n (+ $n 1))))))))
(= (blamed $c $bad)
   (if (== $bad ()) () (case (car-atom $bad) ((($i $cs) (if (in-list $c $cs) (cons-atom $i (blamed $c (cdr-atom $bad))) (blamed $c (cdr-atom $bad))))))))
(= (ev-lines $rows $evs $bad)
   (if (== $rows ()) ""
       (case (car-atom $rows)
         (((row $c $role $kind)
           (case (ev-of $c $evs)
             (((ev $k $e $d)
               (let* (($b (sort-nums (blamed $c $bad)))
                      ($d2 (if (== $b ()) $d (format-args "{}; leaves tests {} unqualified" ($d (join-comma (map-atom $b $x (str-of $x))))))))
                 (str:concat (format-args "{}\t{}\t{}\t{}\t{}\t{}\n" ($c $role $kind $k $e $d2)) (ev-lines (cdr-atom $rows) $evs $bad)))))))))))
(= (deps-of $i $deps) (if (== $deps ()) () (case (car-atom $deps) ((($j $cs) (if (== $j $i) $cs (deps-of $i (cdr-atom $deps))))))))
(= (q-lines $ocs $deps $bad)
   (str:join "" (map-atom (sort-ocs $ocs) $o
     (case $o
       (((oc $i $out $w)
         (if (== $out "joined")
             (let $b (deps-of $i $bad)
               (format-args "{}\t{}\t{}\t{}\t\n" ($i (if (== $b ()) "qualified" "unqualified") (len-of (deps-of $i $deps)) (join-comma $b))))
             (format-args "{}\trefused\t0\t\t{}\n" ($i $w)))))))))
(= (oc-id $o) (case $o (((oc $i $out $w) $i))))
(= (insert-oc $x $ys)
   (if (== $ys ()) ($x) (if (< (oc-id $x) (oc-id (car-atom $ys))) (cons-atom $x $ys) (cons-atom (car-atom $ys) (insert-oc $x (cdr-atom $ys))))))
(= (sort-ocs $xs) (if (== $xs ()) () (insert-oc (car-atom $xs) (sort-ocs (cdr-atom $xs)))))

; Kinds by count, most first; equal counts in order of first appearance.
(= (kind-counts $evs $absent)
   (let* (($ks (append-lists (map-atom $evs $p (let ($c $v) $p (ev-kind $v))) (map-atom $absent $a absent)))
          ($order (dedup $ks ()))
          ($pairs (map-atom $order $k ($k (count-of $k $ks 0))))
          ($sorted (sort-pairs $pairs)))
     (str:join ", " (map-atom $sorted $p (let ($k $n) $p (format-args "{} {}" ($n $k)))))))
(= (count-of $k $ks $n) (if (== $ks ()) $n (count-of $k (cdr-atom $ks) (if (== (car-atom $ks) $k) (+ $n 1) $n))))
(= (insert-pair $x $ys)
   (if (== $ys ()) ($x)
       (let (($k $n) ($k2 $n2)) ($x (car-atom $ys))
         (if (> $n $n2) (cons-atom $x $ys) (cons-atom (car-atom $ys) (insert-pair $x (cdr-atom $ys)))))))
(= (sort-pairs $xs) (if (== $xs ()) () (insert-pair-stable (car-atom $xs) (sort-pairs (cdr-atom $xs)))))
; Stable: an earlier pair goes before later ones of the same count.
(= (insert-pair-stable $x $ys)
   (if (== $ys ()) ($x)
       (let (($k $n) ($k2 $n2)) ($x (car-atom $ys))
         (if (>= $n $n2) (cons-atom $x $ys) (cons-atom (car-atom $ys) (insert-pair-stable $x (cdr-atom $ys)))))))

(= (missing-inputs $gen)
   (let $need (map-atom ("Families.mg" "Functions.mg" "Theorems.mg" "Computations.mg" "Skipped.txt" "Outcomes.tsv") $f
                (format-args "{}/{}" ($gen $f)))
     (missing-of $need)))
(= (missing-of $ps)
   (if (== $ps ()) () (if (fs:exists (car-atom $ps)) (missing-of (cdr-atom $ps)) (cons-atom (car-atom $ps) (missing-of (cdr-atom $ps))))))

!(let* (($oe (system:arg 0)) ($oq (system:arg 1)) ($os (system:arg 2)) ($decls (system:arg 3)) ($gen (system:arg 4))
        ($gone (missing-inputs $gen)))
   (if (== $gone ()) (main $oe $oq $os $decls $gen)
       (let $_e (system:write stderr (format-args "evidence: missing input {}\n" ((car-atom $gone)))) (system:exit 1))))
