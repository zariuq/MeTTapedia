; Compile a flat, keep-only transform theory into a Cesta unit that implements its
; slot interface. Run on CeTTa's PeTTa lane after the theory file:
;   cetta --lang petta --no-results THEORY.metta emit_MODE.metta tcalc_compile.metta > OUT
; where MODE is header (the table type and leaf prototypes, plain C), leaf (the leaves,
; one per kept-premise entry: each decides its rule on a table passed in, with no globals
; and no calls, so its machine code can be proved on its own) or main (the runtime and
; the entry points, which call the leaves).
;
; The class compiled here is the one tcalc's flat path handles: a single board
; constructor whose fields are names; premises are kept (never taken); every hole of
; a conclusion is bound by a premise field, an input, or a fresh name. Each rule becomes
; straight-line code: repeated holes become field comparisons, the conclusion becomes
; field reads. The data layout is chosen here too: theorem bodies are stored by value in
; their slots, and when the unset-slot reading is all zero names, zero-filled slots stand
; for it and no presence flags are kept.

; ---- small list and text helpers ----------------------------------------------------
(= (lb) "{")
(= (rb) "}")

(= (tc-position $x $xs $i)
   (if (== $xs ()) -1
       (if (== (car-atom $xs) $x) $i (tc-position $x (cdr-atom $xs) (+ $i 1)))))

(= (tc-len $xs) (if (== $xs ()) 0 (+ 1 (tc-len (cdr-atom $xs)))))

(= (tc-rev-onto $xs $acc)
   (if (== $xs ()) $acc (tc-rev-onto (cdr-atom $xs) (cons-atom (car-atom $xs) $acc))))
(= (tc-rev $xs) (tc-rev-onto $xs ()))

(= (tc-join $sep $xs)
   (if (== $xs ()) ""
       (if (== (cdr-atom $xs) ()) (car-atom $xs)
           (format-args "{}{}{}" ((car-atom $xs) $sep (tc-join $sep (cdr-atom $xs)))))))

(= (tc-lookup $h $env)
   (if (== $env ()) none
       (let (bind $k $v) (car-atom $env)
         (if (== $k $h) $v (tc-lookup $h (cdr-atom $env))))))

(= (find-rule $name $rules)
   (if (== $rules ()) none
       (let (rule $n $keeps $make) (car-atom $rules)
         (if (== $n $name) (car-atom $rules) (find-rule $name (cdr-atom $rules))))))

; ---- compiling patterns --------------------------------------------------------------
; A name constant compiles to its number; names are minted in the order declared.
(= (tc-constant $a) (tc-position $a (theory-names) 0))

; Walk one premise's fields. The first occurrence of a hole binds it to the field; a
; later occurrence, or a constant, becomes a guard that refuses the firing.
(= (walk-fields $i $args $fields $env $guards)
   (if (== $args ()) (tc-state $env $guards)
       (let* (($a (car-atom $args))
              ($here (format-args "p{}->{}" ($i (car-atom $fields))))
              ($c (tc-constant $a)))
         (if (>= $c 0)
             (walk-fields $i (cdr-atom $args) (cdr-atom $fields) $env
                          (cons-atom (format-args "{} != {}" ($here $c)) $guards))
             (let $prev (tc-lookup $a $env)
               (if (== $prev none)
                   (walk-fields $i (cdr-atom $args) (cdr-atom $fields)
                                (cons-atom (bind $a $here) $env) $guards)
                   (walk-fields $i (cdr-atom $args) (cdr-atom $fields) $env
                                (cons-atom (format-args "{} != {}" ($here $prev)) $guards))))))))

(= (walk-premises $i $premises $env $guards)
   (if (== $premises ()) (tc-state $env $guards)
       (let (tc-state $env2 $guards2)
            (walk-fields $i (cdr-atom (car-atom $premises)) (theory-fields) $env $guards)
         (walk-premises (+ $i 1) (cdr-atom $premises) $env2 $guards2))))

; A conclusion field: a constant, or the expression its hole is bound to.
(= (field-expr $a $env)
   (let $c (tc-constant $a)
     (if (>= $c 0) (format-args "{}" ($c)) (tc-lookup $a $env))))

(= (field-exprs $args $env)
   (if (== $args ()) ()
       (cons-atom (field-expr (car-atom $args) $env) (field-exprs (cdr-atom $args) $env))))

; The conclusion's fields, as the arguments of put. They are read before put runs, so a
; table that grows inside put never invalidates a premise being read.
(= (tc-body $make $env) (tc-join ", " (field-exprs (cdr-atom $make) $env)))

; Inputs bind holes to the parameters i0, i1, ...
(= (bind-inputs $holes $i $env)
   (if (== $holes ()) $env
       (bind-inputs (cdr-atom $holes) (+ $i 1)
                    (cons-atom (bind (car-atom $holes) (format-args "i{}" ($i))) $env))))

(= (tc-args $prefix $n $i)
   (if (== $i $n) () (cons-atom (format-args "{}{}" ($prefix $i)) (tc-args $prefix $n (+ $i 1)))))

(= (tc-params $prefix $n $i)
   (if (== $i $n) ()
       (cons-atom (format-args "uint64_t {}{}" ($prefix $i)) (tc-params $prefix $n (+ $i 1)))))

(= (input-checks $n $i)
   (if (== $i $n) ()
       (cons-atom (format-args "i{} > last" ($i)) (input-checks $n (+ $i 1)))))

; ---- emitting entries ----------------------------------------------------------------
; Emitters return the lines they produce; the unit prints them in order at the end.
(= (tc-append $xs $ys)
   (if (== $xs ()) $ys (cons-atom (car-atom $xs) (tc-append (cdr-atom $xs) $ys))))

; The unit is printed once, as raw text: the lines joined by newlines, made an atom so
; that println! does not quote it.
(= (print-unit $xs) (println! (atom_concat (tc-join "\n" $xs) "")))

; A premise is read through the table passed in; past the table it is the unset body.
; The table's base, size and unset body are loaded once, so each choice is a select
; rather than a branch.
(= (slot-reads $n $i)
   (if (== $i $n) ()
       (cons-atom (format-args "*p{} = k{} < n ? &sl[k{}] : u" ($i $i $i))
                  (slot-reads $n (+ $i 1)))))

; The guards are combined with |, so they compile to one test rather than a chain.
(= (paren-all $gs)
   (if (== $gs ()) () (cons-atom (format-args "({})" ((car-atom $gs))) (paren-all (cdr-atom $gs)))))
(= (guard-lines $guards)
   (if (== $guards ()) ()
       ((format-args "    if ({})" ((tc-join " | " (paren-all (tc-rev $guards))))) "        return 0;")))

(= (leaf-signature $name $k)
   (format-args "uint64_t {}_leaf({} *t, {}, uint64_t dest)" ($name (theory-table) (tc-join ", " (tc-params "k" $k 0)))))

(= (keeps-count $r) (let (rule $n $keeps $make) (find-rule $r (theory-rules)) (tc-len $keeps)))

; A leaf decides its rule on table t: 0 refused, 1 fired (slot dest written), 2 the rule
; fires but dest is past the table (nothing written). The conclusion is built from the
; premises before the store, so a destination that is also a premise is read first.
(= (leaf-lines (entry $name (keeps $r)))
   (let (rule $n $keeps $make) (find-rule $r (theory-rules))
     (let* (($k (tc-len $keeps))
            ((tc-state $env $guards) (walk-premises 0 $keeps () ())))
       (tc-append
         ((format-args "{} {}" ((leaf-signature $name $k) (lb)))
          (format-args "    {} *sl = t->slot;" ((theory-body)))
          "    uint64_t n = t->nslot;"
          (format-args "    const {} *u = &t->unset;" ((theory-body)))
          (format-args "    const {} {};" ((theory-body) (tc-join ", " (slot-reads $k 0)))))
         (tc-append (guard-lines $guards)
           ("    if (dest >= n)"
            "        return 2;"
            (format-args "    sl[dest] = ({}){}{}{};" ((theory-body) (lb) (tc-body $make $env) (rb)))
            "    return 1;"
            (rb) ""))))))
(= (leaf-lines (entry $name (inputs $r $holes))) ())
(= (leaf-lines (entry $name (fresh $r $hole $holes))) ())

(= (leaves-lines $es)
   (if (== $es ()) () (tc-append (leaf-lines (car-atom $es)) (leaves-lines (cdr-atom $es)))))

(= (leaf-prototypes $es)
   (if (== $es ()) ()
       (let $rest (leaf-prototypes (cdr-atom $es))
         (let (entry $name $how) (car-atom $es)
           (if (== (car-atom $how) keeps)
               (cons-atom (format-args "{};" ((leaf-signature $name (keeps-count (car-atom (cdr-atom $how)))))) $rest)
               $rest)))))

(= (leaf-names $es)
   (if (== $es ()) ()
       (let $rest (leaf-names (cdr-atom $es))
         (let (entry $name $how) (car-atom $es)
           (if (== (car-atom $how) keeps) (cons-atom (format-args "{}_leaf" ($name)) $rest) $rest)))))

(= (fire-names $es)
   (if (== $es ()) ()
       (let $rest (fire-names (cdr-atom $es))
         (let (entry $name $how) (car-atom $es)
           (if (== (car-atom $how) keeps) (cons-atom (format-args "{}_fire" ($name)) $rest) $rest)))))

; The entry point fires the leaf on the theorem table; when the destination is past the
; table it grows the table and fires again (the premises read the same: new slots are
; unset). fire passes the table, so the checked entry handles names only.
(= (entry-lines (entry $name (keeps $r)))
   (let* (($k (keeps-count $r))
          ($ks (tc-join ", " (tc-args "k" $k 0))))
     ((format-args "static uint64_t {}_fire({}, uint64_t dest) {}" ($name (tc-join ", " (tc-params "k" $k 0)) (lb)))
      (format-args "    return {}_leaf(&{}_table, {}, dest);" ($name (theory-prefix) $ks))
      (rb)
      ""
      (format-args "bool {}({}, uint64_t dest) {}" ($name (tc-join ", " (tc-params "k" $k 0)) (lb)))
      (format-args "    uint64_t r = {}_fire({}, dest);" ($name $ks))
      "    if (r != 2)"
      "        return r == 1;"
      (format-args "    if (!{}_grow(dest))" ((theory-prefix)))
      "        return false;"
      (format-args "    return {}_fire({}, dest) == 1;" ($name $ks))
      (rb) "")))

(= (entry-lines (entry $name (inputs $r $holes)))
   (let (rule $n $keeps $make) (find-rule $r (theory-rules))
     ((format-args "bool {}({}, uint64_t dest) {}" ($name (tc-join ", " (tc-params "i" (tc-len $holes) 0)) (lb)))
      (format-args "    return {}_put(dest, {});" ((theory-prefix) (tc-body $make (bind-inputs $holes 0 ()))))
      (rb) "")))

; A fresh hole: the given names must exist already. Every refusal comes before any
; effect: the slot is made writable before the new name is minted, so a firing that
; fails never spends a name.
(= (entry-lines (entry $name (fresh $r $hole $holes)))
   (let (rule $n $keeps $make) (find-rule $r (theory-rules))
     (let $env (cons-atom (bind $hole "fresh") (bind-inputs $holes 0 ()))
       ((format-args "uint64_t {}({}, uint64_t dest) {}" ($name (tc-join ", " (tc-params "i" (tc-len $holes) 0)) (lb)))
        (format-args "    uint64_t last = {}_last_name();" ((theory-prefix)))
        (format-args "    if ({} || last == UINT64_MAX)" ((tc-join " || " (input-checks (tc-len $holes) 0))))
        "        return 0;"
        (format-args "    if (!{}_reserve(dest))" ((theory-prefix)))
        "        return 0;"
        (format-args "    uint64_t fresh = {}_fresh_name();" ((theory-prefix)))
        (format-args "    {}_store(dest, {});" ((theory-prefix) (tc-body $make $env)))
        "    return fresh;"
        (rb) ""))))

(= (entries-lines $es)
   (if (== $es ()) () (tc-append (entry-lines (car-atom $es)) (entries-lines (cdr-atom $es)))))

; ---- the unset reading, decided now ----------------------------------------------------
(= (unset-env $pairs)
   (if (== $pairs ()) ()
       (let ($h $v) (car-atom $pairs)
         (cons-atom (bind $h (format-args "{}" ((tc-constant $v)))) (unset-env (cdr-atom $pairs))))))

(= (unset-fields)
   (let ($r $pairs) (theory-unset)
     (let (rule $n $keeps $make) (find-rule $r (theory-rules))
       (field-exprs (cdr-atom $make) (unset-env $pairs)))))

(= (all-zero $xs)
   (if (== $xs ()) True (if (== (car-atom $xs) "0") (all-zero (cdr-atom $xs)) False)))

; ---- admission: the class this compiler handles --------------------------------------
; A theory outside the class is refused, never compiled approximately. The class: one board
; constructor whose fields are names, so every board is ground, flat and first-order; every
; premise and conclusion is that constructor applied to holes and named constants; premises
; are kept; every hole of a conclusion is bound by a premise field, an input, or the fresh
; name. Guards compare names by identity, which is exact on ground boards.
(= (tc-symbol $a) (== (get-metatype $a) Symbol))

(= (all-symbols $xs)
   (if (== $xs ()) True (if (tc-symbol (car-atom $xs)) (all-symbols (cdr-atom $xs)) False)))

(= (board-ok $t)
   (if (== (get-metatype $t) Expression)
       (if (== $t ()) False
           (if (== (car-atom $t) (theory-board))
               (if (== (tc-len (cdr-atom $t)) (tc-len (theory-fields))) (all-symbols (cdr-atom $t)) False)
               False))
       False))

(= (boards-ok $ts)
   (if (== $ts ()) True (if (board-ok (car-atom $ts)) (boards-ok (cdr-atom $ts)) False)))

(= (holes-of $args)
   (if (== $args ()) ()
       (let $rest (holes-of (cdr-atom $args))
         (if (>= (tc-constant (car-atom $args)) 0) $rest (cons-atom (car-atom $args) $rest)))))

(= (premise-holes $ps)
   (if (== $ps ()) () (tc-append (holes-of (cdr-atom (car-atom $ps))) (premise-holes (cdr-atom $ps)))))

(= (all-in $xs $set)
   (if (== $xs ()) True
       (if (>= (tc-position (car-atom $xs) $set 0) 0) (all-in (cdr-atom $xs) $set) False)))

(= (refuse $fmt $args) ((format-args (format-args "#error {}" ($fmt)) $args)))

(= (rule-errors (rule $n $keeps $make))
   (if (boards-ok (cons-atom $make $keeps)) ()
       (refuse "rule {}: every premise and the conclusion must be ({} ...) over {} holes or named constants"
               ($n (theory-board) (tc-len (theory-fields))))))

(= (entry-errors (entry $name (keeps $r)))
   (let $rule (find-rule $r (theory-rules))
     (if (== $rule none) (refuse "entry {}: no rule {}" ($name $r))
         (let (rule $n $keeps $make) $rule
           (if (== $keeps ()) (refuse "entry {}: keeps rule {}, which has no premises" ($name $r))
               (if (all-in (holes-of (cdr-atom $make)) (premise-holes $keeps)) ()
                   (refuse "entry {}: a conclusion hole of rule {} is bound by no premise" ($name $r))))))))

(= (entry-errors (entry $name (inputs $r $holes)))
   (let $rule (find-rule $r (theory-rules))
     (if (== $rule none) (refuse "entry {}: no rule {}" ($name $r))
         (let (rule $n $keeps $make) $rule
           (if (== $keeps ()) 
               (if (all-symbols $holes)
                   (if (all-in (holes-of (cdr-atom $make)) $holes) ()
                       (refuse "entry {}: a conclusion hole of rule {} is not an input" ($name $r)))
                   (refuse "entry {}: inputs must be holes" ($name)))
               (refuse "entry {}: rule {} has premises; use keeps" ($name $r)))))))

(= (entry-errors (entry $name (fresh $r $hole $holes)))
   (let $rule (find-rule $r (theory-rules))
     (if (== $rule none) (refuse "entry {}: no rule {}" ($name $r))
         (let (rule $n $keeps $make) $rule
           (if (== $keeps ())
               (if (>= (tc-position $hole $holes 0) 0)
                   (refuse "entry {}: the fresh hole {} is also an input" ($name $hole))
                   (if (all-in (holes-of (cdr-atom $make)) (cons-atom $hole $holes)) ()
                       (refuse "entry {}: a conclusion hole of rule {} is neither an input nor fresh" ($name $r))))
               (refuse "entry {}: rule {} has premises; a fresh entry takes inputs only" ($name $r)))))))

(= (rules-errors $rs)
   (if (== $rs ()) () (tc-append (rule-errors (car-atom $rs)) (rules-errors (cdr-atom $rs)))))
(= (entries-errors $es)
   (if (== $es ()) () (tc-append (entry-errors (car-atom $es)) (entries-errors (cdr-atom $es)))))

; The data layout is decided only for an admitted theory.
(= (theory-errors)
   (let $e (tc-append (rules-errors (theory-rules)) (entries-errors (theory-entries)))
     (if (== $e ())
         (if (== (theory-names) ())
             (refuse "a theory with no declared constants needs another name-exhaustion sentinel" ())
             (if (== (all-zero (unset-fields)) False)
                 (refuse "the unset reading is not all zero names; presence flags are not generated yet" ())
                 ()))
         $e)))

; A refused theory still compiles to a unit: one whose C is only the reasons, so the build
; stops with them.
(= (refused-unit $errors)
   (tc-append ("(cesta native-c/1 compact-c/2" " (unit" "  (native \"")
              (tc-append $errors ("\")))"))))

; ---- the unit ------------------------------------------------------------------------
(= (field-params $fs)
   (if (== $fs ()) () (cons-atom (format-args "uint64_t {}" ((car-atom $fs))) (field-params (cdr-atom $fs)))))
(= (field-checks $fs)
   (if (== $fs ()) () (cons-atom (format-args "{} > last" ((car-atom $fs))) (field-checks (cdr-atom $fs)))))

; The names 0 .. last are in use; the declared constants come first. last is the count
; of names minus one, so the full range of names can be minted, as in Micromath's kernel.
(= (runtime-lines $p $b $unset $params $fields)
   ("(cesta native-c/1 compact-c/2"
    " (unit"
    (format-args "  (include \"{}\")" ((theory-leaf-header)))
    "  (include \"stdlib.h\")"
    "  (ownership (check-all)"
    (format-args "    (unchecked ({}_grow {}_reserve {}_store {}_last_name {}_fresh_name {}_init {})" ($p $p $p $p $p $p (tc-join " " (fire-names (theory-entries)))))
    "      (obligation \"The theorem table and the name counter of the compiled theory: every subscript is below the table size and the table is grown only by grow.\"))"
    (format-args "    (unchecked {}_ref (returns-static)" ($p))
    "      (obligation \"Returns the body in slot s of the table, or the table's unset body past it; every caller reads it before its next call that can grow the table.\"))"
    (format-args "{})" ((foreign-lines (leaf-names (theory-entries)))))
    "  (native \""
    "/* Generated by tcalc_compile.metta from the theory file. Do not edit. */"
    (format-args "#define {}_MAX_SLOT ((uint64_t){}u)" ($p (theory-max-slot)))
    ""
    "/* Theorem bodies by slot, stored by value. Unset slots are zero-filled with the unset"
    "   body, which is all zero names (decided when the theory was compiled). */"
    (format-args "static {} {}_table;" ((theory-table) $p))
    (format-args "static uint64_t {}_last;" ($p))
    ""
    (format-args "static const {} *{}_ref(uint64_t s) {}" ($b $p (lb)))
    (format-args "    return s < {}_table.nslot ? &{}_table.slot[s] : &{}_table.unset;" ($p $p $p))
    (rb)
    ""
    "/* Makes slot s writable; false past the slot bound or when the table cannot grow. */"
    (format-args "static bool {}_grow(uint64_t s) {}" ($p (lb)))
    (format-args "    if (s >= {}_MAX_SLOT)" ($p))
    "        return false;"
    (format-args "    uint64_t m = {}_table.nslot ? {}_table.nslot : 1024;" ($p $p))
    "    while (m <= s)"
    "        m *= 2;"
    (format-args "    {} *g = realloc({}_table.slot, m * sizeof *g);" ($b $p))
    "    if (!g)"
    "        return false;"
    (format-args "    for (uint64_t i = {}_table.nslot; i < m; i++)" ($p))
    (format-args "        g[i] = {}_table.unset;" ($p))
    (format-args "    {}_table.slot = g;" ($p))
    (format-args "    {}_table.nslot = m;" ($p))
    "    return true;"
    (rb)
    ""
    (format-args "static bool {}_reserve(uint64_t s) {} return s < {}_table.nslot || {}_grow(s); {}" ($p (lb) $p $p (rb)))
    ""
    "/* Requires a successful reserve of s. */"
    (format-args "static void {}_store(uint64_t s, {}) {}" ($p $params (lb)))
    (format-args "    {}_table.slot[s] = ({}){}{}{};" ($p $b (lb) $fields (rb)))
    (rb)
    ""
    (format-args "static bool {}_put(uint64_t s, {}) {}" ($p $params (lb)))
    (format-args "    if (!{}_reserve(s))" ($p))
    "        return false;"
    (format-args "    {}_store(s, {});" ($p $fields))
    "    return true;"
    (rb)
    ""
    (format-args "static uint64_t {}_last_name(void) {} return {}_last; {}" ($p (lb) $p (rb)))
    ""
    "/* Requires last_name() < UINT64_MAX. */"
    (format-args "static uint64_t {}_fresh_name(void) {} return ++{}_last; {}" ($p (lb) $p (rb)))
    ""
    (format-args "bool {}_init(void) {}" ($p (lb)))
    (format-args "    free({}_table.slot);" ($p))
    (format-args "    {}_table.slot = NULL;" ($p))
    (format-args "    {}_table.nslot = 0;" ($p))
    (format-args "    {}_table.unset = ({}){}{}{};" ($p $b (lb) $unset (rb)))
    (format-args "    {}_last = {};" ($p (- (tc-len (theory-names)) 1)))
    "    return true;"
    (rb)
    ""
    "/* 0 when every name is in use (0 is a declared constant, never minted). */"
    (format-args "uint64_t {}_new_opaque(void) {} return {}_last_name() == UINT64_MAX ? 0 : {}_fresh_name(); {}" ($p (lb) $p $p (rb)))
    ""
    "/* Trusted: posts a theorem directly; every field must name a name in use. */"
    (format-args "bool {}_set({}, uint64_t dest) {}" ($p $params (lb)))
    (format-args "    uint64_t last = {}_last_name();" ($p))
    (format-args "    if ({})" ((tc-join " || " (field-checks (theory-fields)))))
    "        return false;"
    (format-args "    return {}_put(dest, {});" ($p $fields))
    (rb)
    ""
    (format-args "{} {}_get(uint64_t slot) {} return *{}_ref(slot); {}" ($b $p (lb) $p (rb)))
    ""))

; Each leaf is declared foreign to the main unit: its contract is the leaf unit's.
(= (foreign-decls $names)
   (if (== $names ()) ()
       (cons-atom (format-args "    (foreign {} (obligation \"Decides its rule on a table whose slot array holds nslot bodies; writes only slot dest, and only when dest < nslot.\"))" ((car-atom $names)))
                  (foreign-decls (cdr-atom $names)))))
(= (foreign-lines $names) (tc-join "\n" (foreign-decls $names)))

(= (header-lines)
   ("#pragma once"
    "/* Generated by tcalc_compile.metta from the theory file. Do not edit. */"
    (format-args "#include \"{}\"" ((theory-header)))
    ""
    "/* The theorem table: bodies by slot, and the body an unset slot reads as. */"
    (format-args "typedef struct {} {} *slot; uint64_t nslot; {} unset; {} {};" ((lb) (theory-body) (theory-body) (rb) (theory-table)))
    ""
    "/* Leaves: 0 refused, 1 fired (slot dest written), 2 the rule fires but dest is past"
    "   the table (nothing written). */"))

(= (leaf-unit-lines)
   (tc-append
     ("(cesta native-c/1 compact-c/2"
      " (unit"
      (format-args "  (include \"{}\")" ((theory-leaf-header)))
      "  (ownership (check-all)"
      (format-args "    (unchecked ({})" ((tc-join " " (leaf-names (theory-entries)))))
      "      (obligation \"Given a table whose slot array holds nslot bodies, each leaf reads its premises through bounds-checked references and writes only slot dest, and only when dest < nslot. The machine code of a leaf is the subject of its proof.\")))"
      "  (native \""
      "/* Generated by tcalc_compile.metta from the theory file. Do not edit. */"
      "")
     (tc-append (leaves-lines (theory-entries)) ("\")))"))))

(= (unit-lines)
   (let $errors (theory-errors)
     (if (== $errors ())
         (let* (($p (theory-prefix)) ($b (theory-body))
                ($unset (tc-join ", " (unset-fields)))
                ($params (tc-join ", " (field-params (theory-fields))))
                ($fields (tc-join ", " (theory-fields))))
           (if (== (tc-emit) header)
               (tc-append (header-lines) (leaf-prototypes (theory-entries)))
               (if (== (tc-emit) leaf)
                   (leaf-unit-lines)
                   (tc-append (runtime-lines $p $b $unset $params $fields)
                              (tc-append (entries-lines (theory-entries)) ("\")))"))))))
         (if (== (tc-emit) header) $errors (refused-unit $errors)))))

!(print-unit (unit-lines))
