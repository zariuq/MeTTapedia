; Wrap long lines of generated Megalodon text at 200 characters.
;
;   cetta --lang petta wrap.metta FILE.mg...
;
; Breaks only at spaces, never inside a token; a continuation line is
; indented by four spaces and never starts with a character Megalodon reads
; as a bullet (-, +, *).  Megalodon does not depend on line breaks otherwise.

!(import! &self fs)
!(import! &self str)
!(import! &self system)

(= (width) 200)

(= (trim-line-end $line)
   (let $n (str:byte-length $line)
     (if (== $n 0) $line
         (let $last (str:byte-slice $line (- $n 1) $n)
           (if (or (== $last " ") (or (== $last "\t") (== $last "\r")))
               (trim-line-end (str:byte-slice $line 0 (- $n 1))) $line)))))

(= (append-lists $xs $ys) (if (== $xs ()) $ys (cons-atom (car-atom $xs) (append-lists (cdr-atom $xs) $ys))))

; A break may follow a space at position i (from width - 1 down to 21) when
; the next character starts a token that is not a bullet.
(= (good-next $c)
   (not (or (== $c "-") (or (== $c "+") (or (== $c "*") (or (== $c " ") (== $c "")))))))

; ASCII text: characters are bytes.
(= (cut-at $line $i)
   (if (<= $i 20) -1
       (if (and (== (str:byte-slice $line $i (+ $i 1)) " ") (good-next (str:byte-slice $line (+ $i 1) (+ $i 2))))
           $i (cut-at $line (- $i 1)))))
(= (wrap-ascii $line $acc)
   (if (<= (str:byte-length $line) (width)) (append-lists $acc ($line))
       (let $cut (cut-at $line (- (width) 1))
         (if (< $cut 0) (append-lists $acc ($line))
             (wrap-ascii (str:concat "    " (str:byte-slice $line (+ $cut 1) (str:byte-length $line)))
                         (append-lists $acc ((str:byte-slice $line 0 $cut))))))))

; Other text: characters are codepoints.
(= (nth-of $xs $k) (if (== $xs ()) "" (if (== $k 0) (car-atom $xs) (nth-of (cdr-atom $xs) (- $k 1)))))
(= (take-of $xs $k) (if (or (== $k 0) (== $xs ())) () (cons-atom (car-atom $xs) (take-of (cdr-atom $xs) (- $k 1)))))
(= (drop-of $xs $k) (if (or (== $k 0) (== $xs ())) $xs (drop-of (cdr-atom $xs) (- $k 1))))
(= (len-of $xs) (if (== $xs ()) 0 (+ 1 (len-of (cdr-atom $xs)))))
(= (cut-at-cps $cs $i)
   (if (<= $i 20) -1
       (if (and (== (nth-of $cs $i) " ") (good-next (nth-of $cs (+ $i 1)))) $i (cut-at-cps $cs (- $i 1)))))
(= (wrap-cps $cs $acc)
   (if (<= (len-of $cs) (width)) (append-lists $acc ((str:from-codepoints $cs)))
       (let $cut (cut-at-cps $cs (- (width) 1))
         (if (< $cut 0) (append-lists $acc ((str:from-codepoints $cs)))
             (wrap-cps (append-lists (" " " " " " " ") (drop-of $cs (+ $cut 1)))
                       (append-lists $acc ((str:from-codepoints (take-of $cs $cut)))))))))

(= (wrap-line $line)
   (let $clean (trim-line-end $line)
     (if (str:is-all-in ascii $clean) (wrap-ascii $clean ()) (wrap-cps (str:codepoints $clean) ()))))
(= (wrap-lines $lines)
   (if (== $lines ()) () (append-lists (wrap-line (car-atom $lines)) (wrap-lines (cdr-atom $lines)))))
(= (wrap-file $path)
   (fs:write $path (str:join "\n" (wrap-lines (str:split "\n" (fs:read-text $path))))))
(= (wrap-all $paths)
   (if (== $paths ()) () (let $done (wrap-file (car-atom $paths)) (wrap-all (cdr-atom $paths)))))

!(wrap-all (system:args))
