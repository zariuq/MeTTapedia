; VerifiedMeTTa 04: match/query.

(verified-answer (N (S (S Z))))

!(assertEqualToResult
  (match &self (verified-answer $answer) $answer)
  ((N (S (S Z)))))

!(assertEqualToResult
  (match &self (missing-answer $answer) $answer)
  ())
