; Prime Motivation 02: response validation before dependent protocols.
; Dialect: PeTTa.  Run with PeTTa run.sh and --silent.
;
; Ordinary program: validate that a reply uses the requested ticket, declares
; the requested payload count, and actually contains that many payloads.
; Every defensive check is useful in untyped MeTTa and remains executable.
;
; Prime payoff: index the continuation by the received count:
;   (count : Nat) -> Comp-rho(request count, response count)
;                    x SizedResponse count
; The ticket/count agreement then shapes the protocol itself.  The wrong-size
; response is uninhabited, so its defensive branch can be deleted rather than
; merely optimized.  Lean anchors:
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.
;     indexedProtocolTy
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation.
;     one_request_rejects_two_field_response
;   Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam.
;     unknownCommPlan_raw_reachable
;
; Unknown or rejected typing evidence does not disable this ordinary program.

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

!(test
  (validate-response
    (Request ticket-7 (S (S Z)))
    (Response ticket-7 (S (S Z)) (Cons datum-a (Cons datum-b Nil))))
  Accepted)

!(test
  (validate-response
    (Request ticket-7 (S Z))
    (Response ticket-7 (S (S Z)) (Cons datum-a (Cons datum-b Nil))))
  Rejected)

!(test
  (validate-response
    (Request ticket-7 (S Z))
    (Response ticket-8 (S Z) (Cons datum-a Nil)))
  Rejected)
