import Mettapedia.OSLF.MeTTaIL.PatternCodeComputable
import Mettapedia.OSLF.MeTTaIL.PatternLexOrder
import Mettapedia.Computability.ComputableLists

/-!
# The lexicographic order of patterns is computable on codes

The serialization of a pattern is computed from its code (`serCode`, `serCode_patternCode`): the strings inside a
code are lists of character codes in the standard list code, and the parts' serializations are joined as `ser` joins
them. The comparison of serializations is a left fold (`lexLe_eq_foldl`), and the strict order of lists of numbers is
its negation reversed (`decide_lt_eq_lexLe`). So the order of patterns (`PatternLe`), sorting by it and the least of
a list of sorted candidates are computable on codes (`sortCode_computable`, `leastCode_computable`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.PatternLexOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-! ## Comparing lists of numbers -/

/-- One step of the comparison, the left list's next number against the right list: once decided, it stays. -/
def lexStep (state : Option Bool × List ℕ) (left : ℕ) : Option Bool × List ℕ :=
  match state with
  | (some decided, rest) => (some decided, rest)
  | (none, []) => (some false, [])
  | (none, right :: rest) => if left < right then (some true, rest) else if left = right then (none, rest)
      else (some false, rest)

theorem foldl_lexStep_decided (decided : Bool) :
    ∀ (lefts rest : List ℕ), lefts.foldl lexStep (some decided, rest) = (some decided, rest)
  | [], _ => rfl
  | _ :: lefts, rest => foldl_lexStep_decided decided lefts rest

/-- **The comparison is a left fold.** -/
theorem lexLe_eq_foldl : ∀ lefts rights : List ℕ, lexLe lefts rights = (lefts.foldl lexStep (none, rights)).1.getD true
  | [], _ => rfl
  | _ :: _, [] => by simp [lexLe, List.foldl_cons, lexStep, foldl_lexStep_decided]
  | left :: lefts, right :: rights => by
      rw [List.foldl_cons]
      by_cases less : left < right
      · simp [lexLe, lexStep, less, foldl_lexStep_decided]
      · by_cases same : left = right
        · subst same
          simp [lexLe, lexStep, lexLe_eq_foldl lefts rights]
        · simp [lexLe, lexStep, less, same, foldl_lexStep_decided]

theorem lexStep_primrec : Primrec₂ lexStep := by
  have undecided : Primrec fun input : (Option Bool × List ℕ) × ℕ => (input.1.2.head?, input.1.2.tail) :=
    Primrec.pair (Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst))
  have compared : Primrec₂ fun (input : (Option Bool × List ℕ) × ℕ) (right : ℕ) =>
      ((if input.2 < right then (some true, input.1.2.tail) else if input.2 = right then (none, input.1.2.tail)
        else (some false, input.1.2.tail)) : Option Bool × List ℕ) := by
    have tail : Primrec fun pair : ((Option Bool × List ℕ) × ℕ) × ℕ => pair.1.1.2.tail :=
      Primrec.list_tail.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec.ite (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.pair (Primrec.const (some true)) tail)
      (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.pair (Primrec.const none) tail) (Primrec.pair (Primrec.const (some false)) tail))
  have whenUndecided := Primrec.option_casesOn (o := fun input : (Option Bool × List ℕ) × ℕ => input.1.2.head?)
    (f := fun _ => ((some false, []) : Option Bool × List ℕ)) (g := fun input right =>
      ((if input.2 < right then (some true, input.1.2.tail) else if input.2 = right then (none, input.1.2.tail)
        else (some false, input.1.2.tail)) : Option Bool × List ℕ))
    (Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const _) compared
  have cased := Primrec.option_casesOn (o := fun input : (Option Bool × List ℕ) × ℕ => input.1.1)
    (f := fun input => Option.casesOn (motive := fun _ => Option Bool × List ℕ) input.1.2.head? (some false, [])
      fun right => ((if input.2 < right then (some true, input.1.2.tail) else if input.2 = right then
        (none, input.1.2.tail) else (some false, input.1.2.tail)) : Option Bool × List ℕ))
    (g := fun input decided => ((some decided, input.1.2) : Option Bool × List ℕ))
    (Primrec.fst.comp Primrec.fst) whenUndecided
    (Primrec.pair (Primrec.option_some.comp Primrec.snd) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  refine cased.of_eq fun input => ?_
  rcases input with ⟨⟨_ | decided, _ | ⟨right, rest⟩⟩, left⟩ <;> simp [lexStep]

/-- **The comparison of lists of numbers is primitive recursive.** -/
theorem lexLe_primrec : Primrec₂ lexLe :=
  (Primrec.option_getD.comp (Primrec.fst.comp (Primrec.list_foldl Primrec.fst
    (Primrec.pair (Primrec.const none) Primrec.snd) (lexStep_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)) (Primrec.const true)).of_eq fun input => by
    rw [lexLe_eq_foldl]

/-- **The strict order of lists of numbers is the comparison reversed, failing.** -/
theorem lt_iff_lexLe : ∀ lefts rights : List ℕ, lefts < rights ↔ lexLe rights lefts = false
  | [], [] => by simp [lexLe]
  | [], _ :: _ => by simp [lexLe]
  | _ :: _, [] => by simp [lexLe]
  | left :: lefts, right :: rights => by
      rw [List.cons_lt_cons_iff, lt_iff_lexLe lefts rights]
      rcases Nat.lt_trichotomy left right with less | rfl | more
      · simp [lexLe, less, Nat.not_lt.mpr less.le, Nat.ne_of_gt less]
      · simp [lexLe]
      · simp [lexLe, more, Nat.not_lt.mpr more.le, Nat.ne_of_gt more]

theorem decide_lt_eq_lexLe (lefts rights : List ℕ) : decide (lefts < rights) = !lexLe rights lefts := by
  cases compared : lexLe rights lefts <;> simp [lt_iff_lexLe, compared]

/-- The serialization of a list is the serializations of its members, joined. -/
theorem serList_eq_flatMap : ∀ patterns : List Pattern, serList patterns = patterns.flatMap ser
  | [] => rfl
  | pattern :: patterns => by rw [serList, serList_eq_flatMap patterns, List.flatMap_cons]

/-! ## Strings in codes -/

theorem charListCode_eq_encode : ∀ characters : List Char,
    PatternCode.charListCode characters = Encodable.encode (characters.map Char.toNat)
  | [] => rfl
  | character :: characters => by
      simp [PatternCode.charListCode, charListCode_eq_encode characters, Encodable.encode_list_cons]

theorem stringListCode_eq_encode : ∀ strings : List String,
    PatternCode.stringListCode strings = Encodable.encode (strings.map PatternCode.stringCode)
  | [] => rfl
  | string :: strings => by
      simp [PatternCode.stringListCode, stringListCode_eq_encode strings, Encodable.encode_list_cons]

/-- The serialization of the string with a code. -/
def serStringCode (code : ℕ) : List ℕ :=
  (Denumerable.ofNat (List ℕ) code).length :: Denumerable.ofNat (List ℕ) code

/-- The serialization of the optional string with a code. -/
def serOptStringCode (code : ℕ) : List ℕ :=
  if code.unpair.1 = 0 then [0] else 1 :: serStringCode code.unpair.2

/-- The serialization of the list of strings with a code. -/
def serStringListCode (code : ℕ) : List ℕ :=
  (Denumerable.ofNat (List ℕ) code).length :: (Denumerable.ofNat (List ℕ) code).flatMap serStringCode

theorem serStringCode_stringCode (string : String) :
    serStringCode (PatternCode.stringCode string) = serString string := by
  simp [serStringCode, PatternCode.stringCode, charListCode_eq_encode, serString, String.length_toList]

theorem serOptStringCode_optionStringCode (string : Option String) :
    serOptStringCode (PatternCode.optionStringCode string) = serOptString string := by
  cases string <;> simp [serOptStringCode, PatternCode.optionStringCode, serOptString, serStringCode_stringCode]

theorem serStringListCode_stringListCode (strings : List String) :
    serStringListCode (PatternCode.stringListCode strings) = serStringList strings := by
  simp [serStringListCode, stringListCode_eq_encode, serStringList, List.flatMap_map, serStringCode_stringCode]

theorem serStringCode_primrec : Primrec serStringCode :=
  Primrec.list_cons.comp (Primrec.list_length.comp (Primrec.ofNat (List ℕ))) (Primrec.ofNat (List ℕ))

theorem serOptStringCode_primrec : Primrec serOptStringCode :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)) (Primrec.const [0])
    (Primrec.list_cons.comp (Primrec.const 1) (serStringCode_primrec.comp (Primrec.snd.comp Primrec.unpair)))

theorem serStringListCode_primrec : Primrec serStringListCode :=
  Primrec.list_cons.comp (Primrec.list_length.comp (Primrec.ofNat (List ℕ)))
    (Primrec.list_flatMap (Primrec.ofNat (List ℕ)) (serStringCode_primrec.comp Primrec.snd).to₂)

/-! ## The serialization on codes -/

/-- The serialization at a node, from its code and the codes of its parts' serializations. -/
def serCombine (_ code : ℕ) (values : List ℕ) : ℕ :=
  let parts := values.map (Denumerable.ofNat (List ℕ))
  Encodable.encode <|
    if code.unpair.1 = 0 then [0, code.unpair.2]
    else if code.unpair.1 = 1 then 1 :: serStringCode code.unpair.2
    else if code.unpair.1 = 2 then
      2 :: serStringCode code.unpair.2.unpair.1 ++ parts.length :: parts.flatten
    else if code.unpair.1 = 3 then 3 :: serOptStringCode code.unpair.2.unpair.1 ++ parts.headI
    else if code.unpair.1 = 4 then
      4 :: code.unpair.2.unpair.1 :: serStringListCode code.unpair.2.unpair.2.unpair.1 ++ parts.headI
    else if code.unpair.1 = 5 then 5 :: parts.headI ++ parts.getD 1 []
    else 6 :: code.unpair.2.unpair.1 :: parts.length :: parts.flatten ++ serOptStringCode code.unpair.2.unpair.2.unpair.2

/-- The calls of the serialization: the parts. -/
def serCalls (_ code : ℕ) : List ℕ := (partsCode code).map (Nat.pair 0)

/-- **The serialization on codes**, as the code of the list of numbers. -/
def serCode (code : ℕ) : ℕ := structural serCalls serCombine 0 code

private theorem collectionCode_eq (kind : CollType) : PatternCode.collectionCode kind = collectionTag kind := by
  cases kind <;> rfl

theorem serCode_patternCode (pattern : Pattern) :
    serCode (patternCode pattern) = Encodable.encode (ser pattern) := by
  refine structural_patternCode (value := fun _ pattern => Encodable.encode (ser pattern))
    (fun _ pattern => (parts pattern).map fun part => (0, part)) ?_ ?_ ?_ 0 pattern
  · intro _ pattern
    simp only [List.map_map, Function.comp_def]
    cases pattern with
    | bvar index => simp [serCombine, patternCode, ser]
    | fvar name => simp [serCombine, patternCode, ser, serStringCode_stringCode]
    | apply label arguments =>
        simp [serCombine, patternCode, ser, parts, serStringCode_stringCode, serList_eq_flatMap,
          Function.comp_def, Denumerable.ofNat_encode, List.flatMap_def]
    | lambda binder body =>
        simp [serCombine, patternCode, ser, parts, serOptStringCode_optionStringCode]
    | multiLambda arity binders body =>
        simp [serCombine, patternCode, ser, parts, serStringListCode_stringListCode]
    | subst body replacement => simp [serCombine, patternCode, ser, parts]
    | collection kind elements rest =>
        simp [serCombine, patternCode, ser, parts, serList_eq_flatMap, serOptStringCode_optionStringCode,
          collectionCode_eq, Function.comp_def, Denumerable.ofNat_encode, List.flatMap_def]
  · intro _ pattern
    simp [serCalls, partsCode_patternCode, Function.comp_def]
  · intro _ pattern call member
    simp only [List.mem_map] at member
    obtain ⟨part, inParts, rfl⟩ := member
    exact patternCode_lt_of_mem_parts inParts

theorem serCode_computable : Computable serCode := by
  have calls : Computable₂ serCalls :=
    (Primrec.list_map (partsCode_primrec.comp Primrec.snd) (Primrec₂.natPair.comp (Primrec.const 0)
      Primrec.snd).to₂).to_comp
  have combine : Computable fun input : ℕ × ℕ × List ℕ => serCombine input.1 input.2.1 input.2.2 := by
    have primitive : Primrec fun input : ℕ × ℕ × List ℕ => serCombine input.1 input.2.1 input.2.2 := by
      have code : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1 := Primrec.fst.comp Primrec.snd
      have parts : Primrec fun input : ℕ × ℕ × List ℕ => input.2.2.map (Denumerable.ofNat (List ℕ)) :=
        Primrec.list_map (Primrec.snd.comp Primrec.snd) ((Primrec.ofNat (List ℕ)).comp Primrec.snd).to₂
      have tagged : ∀ value : ℕ, PrimrecPred fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.1 = value :=
        fun value => Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp code)) (Primrec.const value)
      have payload : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.2 :=
        Primrec.snd.comp (Primrec.unpair.comp code)
      have first : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.2.unpair.1 :=
        Primrec.fst.comp (Primrec.unpair.comp payload)
      have second : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.2.unpair.2 :=
        Primrec.snd.comp (Primrec.unpair.comp payload)
      have third : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.2.unpair.2.unpair.1 :=
        Primrec.fst.comp (Primrec.unpair.comp second)
      have fourth : Primrec fun input : ℕ × ℕ × List ℕ => input.2.1.unpair.2.unpair.2.unpair.2 :=
        Primrec.snd.comp (Primrec.unpair.comp second)
      have cons : ∀ {head : ℕ × ℕ × List ℕ → ℕ} {tail : ℕ × ℕ × List ℕ → List ℕ}, Primrec head → Primrec tail →
          Primrec fun input => head input :: tail input :=
        fun headPrimitive tailPrimitive => Primrec.list_cons.comp headPrimitive tailPrimitive
      have append : ∀ {left right : ℕ × ℕ × List ℕ → List ℕ}, Primrec left → Primrec right →
          Primrec fun input => left input ++ right input :=
        fun leftPrimitive rightPrimitive => Primrec.list_append.comp leftPrimitive rightPrimitive
      have count : Primrec fun input : ℕ × ℕ × List ℕ => (input.2.2.map (Denumerable.ofNat (List ℕ))).length :=
        Primrec.list_length.comp parts
      have joined : Primrec fun input : ℕ × ℕ × List ℕ => (input.2.2.map (Denumerable.ofNat (List ℕ))).flatten :=
        Primrec.list_flatten.comp parts
      have head : Primrec fun input : ℕ × ℕ × List ℕ => (input.2.2.map (Denumerable.ofNat (List ℕ))).headI :=
        Primrec.list_headI.comp parts
      have second' : Primrec fun input : ℕ × ℕ × List ℕ =>
          (input.2.2.map (Denumerable.ofNat (List ℕ))).getD 1 [] :=
        (Primrec.list_getD []).comp parts (Primrec.const 1)
      have chosen := Primrec.ite (tagged 0) (cons (Primrec.const 0) (cons payload (Primrec.const [])))
        (Primrec.ite (tagged 1) (cons (Primrec.const 1) (serStringCode_primrec.comp payload))
        (Primrec.ite (tagged 2) (cons (Primrec.const 2) (append (serStringCode_primrec.comp first)
          (cons count joined)))
        (Primrec.ite (tagged 3) (cons (Primrec.const 3) (append (serOptStringCode_primrec.comp first) head))
        (Primrec.ite (tagged 4) (cons (Primrec.const 4) (cons first (append (serStringListCode_primrec.comp third)
          head)))
        (Primrec.ite (tagged 5) (cons (Primrec.const 5) (append head second'))
          (cons (Primrec.const 6) (cons first (cons count (append joined
            (serOptStringCode_primrec.comp fourth))))))))))
      exact (Primrec.encode.comp chosen).of_eq fun input => by simp only [serCombine]; rfl
    exact primitive.to_comp
  exact (structural_computable calls combine).comp (Computable.const 0) Computable.id

/-- The serialization of the pattern with a code. -/
def serOf (code : ℕ) : List ℕ := Denumerable.ofNat (List ℕ) (serCode code)

theorem serOf_patternCode (pattern : Pattern) : serOf (patternCode pattern) = ser pattern := by
  rw [serOf, serCode_patternCode, Denumerable.ofNat_encode]

theorem serOf_computable : Computable serOf := (Primrec.ofNat (List ℕ)).to_comp.comp serCode_computable

/-! ## Sorting and choosing on codes -/

/-- The order of patterns, on codes. -/
def leCode (left right : ℕ) : Bool := lexLe (serOf left) (serOf right)

theorem leCode_computable : Computable₂ leCode :=
  lexLe_primrec.to_comp.comp (serOf_computable.comp Computable.fst) (serOf_computable.comp Computable.snd)

/-- Insert into a sorted list of codes. -/
def insertCode (code : ℕ) (codes : List ℕ) : List ℕ :=
  codes.takeWhile (fun other => !leCode code other) ++ code :: codes.drop (codes.takeWhile fun other => !leCode code other).length

/-- **Sorting codes** by the order of their patterns. -/
def sortCode (codes : List ℕ) : List ℕ := codes.foldr insertCode []

theorem dropWhile_eq_drop {β : Type*} (test : β → Bool) :
    ∀ members : List β, members.dropWhile test = members.drop (members.takeWhile test).length
  | [] => rfl
  | member :: members => by
      rw [List.dropWhile_cons, List.takeWhile_cons]
      cases test member
      · rfl
      · simp [dropWhile_eq_drop test members]

theorem insertCode_eq (code : ℕ) (codes : List ℕ) :
    insertCode code codes = codes.orderedInsert (fun left right => leCode left right = true) code := by
  rw [List.orderedInsert_eq_take_drop, insertCode]
  congr 2
  · funext other
    simp
  · rw [← dropWhile_eq_drop]
    congr 1
    funext other
    simp

theorem sortCode_eq (codes : List ℕ) :
    sortCode codes = codes.insertionSort (fun left right => leCode left right = true) := by
  induction codes with
  | nil => rfl
  | cons code codes recurse => rw [sortCode, List.foldr_cons, ← sortCode, recurse, insertCode_eq]; rfl

/-- **Sorting on codes tracks sorting patterns** by their order. -/
theorem sortCode_patternCode (patterns : List Pattern) :
    sortCode (patterns.map patternCode) = (patterns.insertionSort PatternLe).map patternCode := by
  rw [sortCode_eq]
  refine (List.map_insertionSort (r := PatternLe) (s := fun left right : ℕ => leCode left right = true)
    patternCode patterns fun left _ right _ => ?_).symm
  simp [leCode, serOf_patternCode, PatternLe]

theorem takeWhile_eq_foldr {β : Type*} (test : β → Bool) :
    ∀ members : List β, members.takeWhile test = members.foldr (fun member kept => if test member then member :: kept else []) []
  | [] => rfl
  | member :: members => by
      rw [List.takeWhile_cons, List.foldr_cons, takeWhile_eq_foldr test members]

theorem insertCode_computable : Computable₂ insertCode := by
  have kept : Computable fun input : ℕ × List ℕ => input.2.takeWhile fun other => !leCode input.1 other := by
    have folded := Computable.list_foldr' (members := fun input : ℕ × List ℕ => input.2)
      (start := fun _ => ([] : List ℕ))
      (combine := fun input member kept => if !leCode input.1 member then member :: kept else [])
      Computable.snd (Computable.const [])
      ((Computable.cond ((Primrec.not.to_comp).comp (leCode_computable.comp
          (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)))
        ((Primrec.list_cons.to_comp).comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
        (Computable.const [])).of_eq fun input => by
          cases hTested : !leCode input.1.1 input.2.1 <;> simp)
    exact folded.of_eq fun input => (takeWhile_eq_foldr _ input.2).symm
  exact (Primrec.list_append.to_comp).comp kept ((Primrec.list_cons.to_comp).comp Computable.fst
    ((Primrec.list_drop.to_comp).comp (Primrec.list_length.to_comp.comp kept) Computable.snd))

theorem sortCode_computable : Computable sortCode :=
  Computable.list_foldr' (members := id) (start := fun _ => ([] : List ℕ))
    (combine := fun _ code sorted => insertCode code sorted) Computable.id (Computable.const [])
    (insertCode_computable.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))

/-- The serialization of a list of codes. -/
def serListOf (codes : List ℕ) : List ℕ := codes.flatMap serOf

theorem serListOf_patternCode (patterns : List Pattern) : serListOf (patterns.map patternCode) = serList patterns := by
  rw [serListOf, List.flatMap_map, serList_eq_flatMap]
  congr 1
  funext pattern
  exact serOf_patternCode pattern

theorem serListOf_computable : Computable serListOf :=
  Computable.list_flatMap' Computable.id (serOf_computable.comp Computable.snd)

/-- **The least candidate, on codes**: compared by serializations, the first of the least kept. -/
def leastCode : List (List ℕ) → List ℕ
  | [] => []
  | first :: rest => rest.foldl (fun best next => if !lexLe (serListOf best) (serListOf next) then next else best) first


/-- One comparison of the least candidate so far against the next. -/
def leastStep (best next : List ℕ) : List ℕ :=
  if !lexLe (serListOf best) (serListOf next) then next else best

theorem leastCode_eq (candidates : List (List ℕ)) :
    leastCode candidates = candidates.tail.foldl leastStep candidates.headI := by
  cases candidates <;> rfl

theorem leastCode_computable : Computable leastCode := by
  have step : Computable fun input : List (List ℕ) × List ℕ × List ℕ => leastStep input.2.1 input.2.2 := by
    have compared : Computable fun input : List (List ℕ) × List ℕ × List ℕ =>
        !lexLe (serListOf input.2.1) (serListOf input.2.2) :=
      (Primrec.not.to_comp).comp (lexLe_primrec.to_comp.comp
        (serListOf_computable.comp (Computable.fst.comp Computable.snd))
        (serListOf_computable.comp (Computable.snd.comp Computable.snd)))
    refine (Computable.cond compared (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)).of_eq fun input => ?_
    simp only [leastStep]
    cases !lexLe (serListOf input.2.1) (serListOf input.2.2) <;> rfl
  have folded := Computable.list_foldl' (members := fun candidates : List (List ℕ) => candidates.tail)
    (start := fun candidates => candidates.headI) (combine := fun _ best next => leastStep best next)
    (Primrec.list_tail.to_comp) (Primrec.list_headI.to_comp) step
  exact folded.of_eq fun candidates => (leastCode_eq candidates).symm

end Mettapedia.OSLF.MeTTaIL.PatternLexOrder
