; The mailbox of the draft's sealed4 example, written with spaces as values and rules as
; attenuation: no facet, no new-region, no rights. Spaces are created fresh and handed to
; code as arguments; a program holds only the spaces it is given.
!(import! &self interaction)

; A client receives the spaces it may use as arguments.
(= (client-post $m $l) (transform $m () (add-atom $m (post $l))))
(= (client-read $m) (collapse (transform $m (read (letter $x)) (saw $x))))
(= (client-take $m) (collapse (transform $m (take (letter $x)) (stolen $x))))
(= (client-take-post $m) (collapse (transform $m (take (post $x)) (intercepted $x))))
; A location that no source binds and no scope supplies is not formed.
(= (client-ambient) (transform $s (take (letter $x)) (ambient $x)))

; The owner forwards every post at the mailbox m into its store n.
(= (forward $m $n) (whenever (transform $m (take (post $x)) (add-atom $n $x))))
(= (owner-receive $n) (collapse (transform $n (take (letter $x)) (got $x))))

; Read-only access: the asker posts (ask PATTERN TAG) at its own space q; the owner answers.
(= (serve-reads $q $n)
   (whenever (transform $q (, (take (ask $p $tag)) (read $n $p)) (add-atom $q (reply $tag $p)))))
(= (ask-owner $q $p $tag) (transform $q () (add-atom $q (ask $p $tag))))
(= (take-reply $q $tag) (collapse (transform $q (take (reply $tag $v)) (answer $v))))

; 1. The mailbox. The client posts; reading or taking a letter at its handle finds none; the
;    ambient take is not formed; the owner receives hello, then from-client, then nothing.
!(let* (($n (new-space))
        ($m (new-space))
        ($f (forward $m $n))
        ($h (transform $n () (add-atom $n (letter hello))))
        ($p (client-post $m (letter from-client)))
        ($r (client-read $m))
        ($t (client-take $m))
        ($a (collapse (client-ambient)))
        ($g1 (owner-receive $n))
        ($g2 (owner-receive $n))
        ($g3 (owner-receive $n)))
   (mailbox $r $t $a $g1 $g2 $g3))

; 2. One mailbox name shared by two clients is a full space for both: the second takes the
;    first's post before the owner's forwarder runs, and the owner receives nothing.
!(let* (($n (new-space))
        ($m (new-space))
        ($p (client-post $m (letter from-one)))
        ($s (client-take-post $m))
        ($f (forward $m $n))
        ($g (owner-receive $n)))
   (shared-mailbox $s $g))

; 3. One fresh mailbox per client. The second client is handed only its own mailbox, so it
;    finds nothing to take, and the owner receives the first client's letter.
!(let* (($n (new-space))
        ($m1 (new-space))
        ($m2 (new-space))
        ($p (client-post $m1 (letter from-one)))
        ($s (client-take-post $m2))
        ($f1 (forward $m1 $n))
        ($f2 (forward $m2 $n))
        ($g (owner-receive $n)))
   (separate-mailboxes $s $g))

; 4. Read-only by asking the owner: the answer arrives as data and the row stays.
!(let* (($n (new-space))
        ($q (new-space))
        ($s (serve-reads $q $n))
        ($h (transform $n () (add-atom $n (letter hello))))
        ($a (ask-owner $q (letter $x) t1))
        ($r (take-reply $q t1))
        ($still (collapse (transform $n (read (letter $y)) (still $y)))))
   (read-only $r $still))

; 5. The answer is a copy: the owner takes the row before the asker collects the answer.
!(let* (($n (new-space))
        ($q (new-space))
        ($s (serve-reads $q $n))
        ($h (transform $n () (add-atom $n (letter hello))))
        ($a (ask-owner $q (letter $x) t2))
        ($o (owner-receive $n))
        ($r (take-reply $q t2))
        ($left (collapse (transform $n (read (letter $z)) (left $z)))))
   (stale-answer $o $r $left))
