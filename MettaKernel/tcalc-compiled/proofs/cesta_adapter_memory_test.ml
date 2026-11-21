let ORDINARY_ADAPTER_RIP_MEMORY_VALUE_TEST = prove
 (`!pc stackpointer (s47:x86state) (s52:x86state).
    read (memory :> bytes64
      (word_add (word_sub stackpointer (word 120)) (word 32))) s47 = word 0 /\
    read RIP s52 =
      (if ~(((word_zx:int64->int64) ((word_zx:int64->int64)
        ((word_zx:int64->int64)
          (read (memory :> bytes64
            (word_add (word_sub stackpointer (word 120)) (word 32))) s47)))) =
        word 0)
       then word (pc + 1181) else word (pc + 1176))
    ==> read RIP s52 = word (pc + 1176)`,
  REPEAT STRIP_TAC THEN ordinary_adapter_normalize_state THEN
  ASM_REWRITE_TAC[WORD_ZX_0]);;
