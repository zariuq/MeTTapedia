; Prime Motivation 02: response validation before dependent protocols.
; Dialect: Hyperon Experimental MeTTa.
;
; This ordinary version explicitly checks ticket, declared size, and actual
; payload size.  Prime's dependent interaction type can make the two size
; mismatch cases uninhabited while preserving this raw program as the gradual
; fallback.
;
; Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.
;     indexedProtocolTy
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.
;     one_request_rejects_two_field_response
;   Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation.
;     rejected_blame_does_not_gate_raw_execution

(= (nat-eq Z Z) True)
(= (nat-eq Z (S $n)) False)
(= (nat-eq (S $n) Z) False)
(= (nat-eq (S $m) (S $n)) (nat-eq $m $n))

(= (bool-and True True) True)
(= (bool-and True False) False)
(= (bool-and False True) False)
(= (bool-and False False) False)

(= (ticket-eq ticket-7 ticket-7) True)
(= (ticket-eq ticket-7 ticket-8) False)

(= (payload-count Nil) Z)
(= (payload-count (Cons $payload $rest)) (S (payload-count $rest)))

(= (validation-result True) Accepted)
(= (validation-result False) Rejected)

(= (validate-response
      (Request $expected-ticket $expected-count)
      (Response $actual-ticket $declared-count $payloads))
   (validation-result
     (bool-and
       (ticket-eq $expected-ticket $actual-ticket)
       (bool-and
         (nat-eq $expected-count $declared-count)
         (nat-eq $declared-count (payload-count $payloads))))))

!(assertEqual
  (validate-response
    (Request ticket-7 (S (S Z)))
    (Response ticket-7 (S (S Z)) (Cons datum-a (Cons datum-b Nil))))
  Accepted)

!(assertEqual
  (validate-response
    (Request ticket-7 (S Z))
    (Response ticket-7 (S (S Z)) (Cons datum-a (Cons datum-b Nil))))
  Rejected)

!(assertEqual
  (validate-response
    (Request ticket-7 (S Z))
    (Response ticket-8 (S Z) (Cons datum-a Nil)))
  Rejected)
