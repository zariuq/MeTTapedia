(* Bounded ordinary-row packing and capacity-preserving output contracts.
   These definitions and their arithmetic lemma do not depend on a linked ELF. *)

needs "../../Mettapedia/MettaKernel/tcalc-compiled/proofs/ordinary_flat.ml";;

let ordinary_pack_span_valid = new_definition
 `ordinary_pack_span_valid (a:int64) (xs:int32 list) <=>
    LENGTH xs < 2 EXP 61 /\
    (LENGTH xs = 0 \/ ~(a = word 0)) /\
    word_and a (word 3) = word 0 /\
    val a + 4 * LENGTH xs <= 2 EXP 64`;;

let ordinary_pack_offsets_valid = new_definition
 `ordinary_pack_offsets_valid (source:int32 list) (offsets:int32 list) <=>
    ALL (\offset. val offset + 4 <= LENGTH source) offsets`;;

let ORDINARY_PACK_OFFSETS_VALID = prove
 (`!source offsets.
    ordinary_pack_offsets_valid source offsets <=>
    ALL (\offset. val offset <= LENGTH source /\
                  4 <= LENGTH source - val offset) offsets`,
  REWRITE_TAC[ordinary_pack_offsets_valid;
    ARITH_RULE `!n offset. offset + 4 <= n <=>
                           offset <= n /\ 4 <= n - offset`]);;

let ordinary_pack_shape_valid = new_definition
 `ordinary_pack_shape_valid (offsets:int32 list) (constants:int32 list)
      (fields:int32 list) (rows:int32 list) <=>
    LENGTH offsets <= 24 /\ LENGTH constants <= 32 /\
    4 * LENGTH offsets + LENGTH constants <= LENGTH fields /\
    LENGTH offsets + 1 <= LENGTH rows`;;

let ordinary_pack_result_fields = new_definition
 `ordinary_pack_result_fields (source:int32 list) (offsets:int32 list)
      (constants:int32 list) (fields:int32 list) =
    APPEND
      (ordinary_fields
        (ordinary_arena_rows source (MAP (\offset. val offset) offsets)) constants)
      (ordinary_drop (4 * LENGTH offsets + LENGTH constants) fields)`;;

let ordinary_pack_result_rows = new_definition
 `ordinary_pack_result_rows (source:int32 list) (offsets:int32 list)
      (rows:int32 list) =
    APPEND
      (ordinary_rows
        (ordinary_arena_rows source (MAP (\offset. val offset) offsets)))
      (ordinary_drop (LENGTH offsets + 1) rows)`;;

let ordinary_pack_rejects = new_definition
 `ordinary_pack_rejects (source:int32 list) (offsets:int32 list)
      (constants:int32 list) (fields:int32 list) (rows:int32 list) <=>
    ~(ordinary_pack_shape_valid offsets constants fields rows) \/
    ~(ordinary_pack_offsets_valid source offsets)`;;

