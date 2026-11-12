(step 1)
(step 2)
(p 0 0)

(= (close-domain $out)
   (let $fresh
     (size-atom (collapse (match (quote &self) (step $x)
       (match (quote &self) (p $u $v)
         (let $payload (quote (p $x $u))
           (if (== (collapse (match $out $payload true)) ())
             (add-atom $out $payload) (empty)))))))
     (if (== $fresh 0) true (close-domain $out))))
(= (close-domain 7) unreachable)

(= (iterate-renamed $destination)
   (let $delta
     (size-atom (collapse (match (quote &self) (step $x)
       (match (quote &self) (p $u $v)
         (let $local-row (quote (p $x $u))
           (if (== (collapse (match $destination $local-row true)) ())
             (add-atom $destination $local-row) (empty)))))))
     (if (== $delta 0) true (iterate-renamed $destination))))

!(let $destination &self (iterate-renamed $destination))
!(collapse (match &self (p $u $v) (quote ($u $v))))
!(let $out &self (close-domain $out))
!(collapse (match &self (p $u $v) (quote ($u $v))))
