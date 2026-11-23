!(import! &self stable_top_k.metta)

; A mathematical library is data. Indices record source order, scores are
; integers, and payloads may contain statements or proof-strategy syntax.
(candidate-rows
  (RankCons (0 8 premise-a)
    (RankCons (1 -3 premise-b)
      (RankCons (2 8 premise-c)
        (RankCons (3 1 premise-d)
          (RankCons (4 100 later-theorem) RankNil))))))

; Only earlier entries are eligible. Stable ties keep premise-a before c.
!(match &self (candidate-rows $rows) (rank:select 4 3 $rows))
!(match &self (candidate-rows $rows) (rank:select 4 0 $rows))

; The implementation itself is inspectable without running it.
!(match &self (= (rank:select $before $budget $rows) $body)
   (Implementation $body))

; Code-shaped mathematical data stays data when read from the library.
(inert-rows (RankCons (0 1 (println! this-is-data)) RankNil))
!(match &self (inert-rows $rows) (rank:select 1 1 $rows))
