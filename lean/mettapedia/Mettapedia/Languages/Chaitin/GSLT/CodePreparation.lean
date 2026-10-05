import Mettapedia.Languages.Chaitin.GSLT.TuringAdequacy
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Effective preparation of actual Lisp evaluator terms

The framework's structural pattern numbering is used throughout. Binary
numerals, tape lists, quotation, and the fixed interpreter context all have
primitive-recursive code constructors. No execution or eventual output is
used to prepare a program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT.CodePreparation

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.PatternCode

def nodeCode (name : String) (arguments : List Nat) : Nat :=
  Nat.pair 2 (Nat.pair (stringCode name)
    (arguments.foldr (fun first rest => Nat.succ (Nat.pair first rest)) 0))

theorem nodeCode_primrec (name : String) : Primrec (nodeCode name) := by
  have step : Primrec₂ fun (_ : List Nat) (pair : Nat × Nat) =>
      Nat.succ (Nat.pair pair.1 pair.2) :=
    Primrec₂.mk (Primrec.succ.comp (Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
  exact Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.const _)
      (Primrec.list_foldr Primrec.id (Primrec.const 0) step))

theorem patternListCode_map (patterns : List Pattern) :
    patternListCode patterns =
      (patterns.map patternCode).foldr (fun first rest => Nat.succ (Nat.pair first rest)) 0 := by
  induction patterns <;> simp [patternListCode, *]

theorem nodeCode_map (name : String) (arguments : List Pattern) :
    nodeCode name (arguments.map patternCode) = patternCode (.apply name arguments) := by
  simp only [nodeCode, patternCode, patternListCode_map]

def positiveCode (number : Nat) : Nat :=
  match (number : Num) with
  | .zero => patternCode (encodePositive .one)
  | .pos value => patternCode (encodePositive value)

private theorem numCast_positive (number : PosNum) :
    ((number : Nat) : Num) = .pos number := by
  simpa only [Num.ofNat'_eq] using PosNum.of_to_nat' number

theorem positiveCode_rec (number : Nat) :
    positiveCode number = if number ≤ 1 then nodeCode "One" [] else
      nodeCode (if number % 2 = 0 then "Bit0" else "Bit1") [positiveCode (number / 2)] := by
  generalize converted : (number : Num) = binary
  have original : number = (binary : Nat) := by
    rw [← converted]
    exact (Num.to_of_nat number).symm
  subst number
  cases binary with
  | zero => rfl
  | pos value =>
      cases value with
      | one => rfl
      | bit0 value =>
          have positive := PosNum.to_nat_pos value
          have quotient : ((value : Nat) + value) / 2 = value := by omega
          have remainder : ((value : Nat) + value) % 2 = 0 := by omega
          have large : ¬ ((value : Nat) + value ≤ 1) := by omega
          rw [positiveCode, converted]
          simp only [Num.cast_pos, positiveCode, numCast_positive, encodePositive, patternCode, patternListCode,
            PosNum.cast_bit0, if_neg large, quotient, remainder, ↓reduceIte, nodeCode,
            List.foldr_cons, List.foldr_nil]
      | bit1 value =>
          have positive := PosNum.to_nat_pos value
          have quotient : ((value : Nat) + value + 1) / 2 = value := by omega
          have remainder : ((value : Nat) + value + 1) % 2 = 1 := by omega
          have large : ¬ ((value : Nat) + value + 1 ≤ 1) := by omega
          rw [positiveCode, converted]
          simp only [Num.cast_pos, positiveCode, numCast_positive, encodePositive, patternCode, patternListCode,
            PosNum.cast_bit1, if_neg large, quotient, remainder, Nat.one_ne_zero, ↓reduceIte,
            nodeCode, List.foldr_cons, List.foldr_nil]

theorem nodeCode_one_primrec (name : String) :
    Primrec fun value : Nat => nodeCode name [value] :=
  (nodeCode_primrec name).comp (Primrec.list_cons.comp Primrec.id (Primrec.const []))

theorem nodeCode_two_primrec (name : String) :
    Primrec₂ fun first rest : Nat => nodeCode name [first, rest] :=
  Primrec₂.mk ((nodeCode_primrec name).comp
    (Primrec.list_cons.comp Primrec.fst
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))

/-- Strong recursion only queries the already prepared code at `n / 2`.
It performs no simulated machine execution. -/
theorem positiveCode_primrec : Primrec positiveCode := by
  let step : Unit → List Nat → Option Nat := fun _ previous => some
    (if previous.length ≤ 1 then nodeCode "One" [] else
      if previous.length % 2 = 0 then nodeCode "Bit0" [previous[previous.length / 2]?.getD 0]
      else nodeCode "Bit1" [previous[previous.length / 2]?.getD 0])
  have length : Primrec fun input : Unit × List Nat => input.2.length :=
    Primrec.list_length.comp Primrec.snd
  have selected : Primrec fun input : Unit × List Nat =>
      input.2[input.2.length / 2]?.getD 0 :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_div.comp length (Primrec.const 2)))
      (Primrec.const 0)
  have stepEffective : Primrec₂ step := Primrec₂.mk
    (Primrec.option_some.comp
      (Primrec.ite (Primrec.nat_le.comp length (Primrec.const 1)) (Primrec.const _)
        (Primrec.ite
          (Primrec.eq.comp (Primrec.nat_mod.comp length (Primrec.const 2)) (Primrec.const 0))
          ((nodeCode_one_primrec "Bit0").comp selected)
          ((nodeCode_one_primrec "Bit1").comp selected))))
  have strong : Primrec₂ fun (_ : Unit) number => positiveCode number := by
    apply Primrec.nat_strong_rec (fun (_ : Unit) number => positiveCode number) stepEffective
    intro _ number
    simp only [step, List.length_map, List.length_range]
    by_cases small : number ≤ 1
    · rw [if_pos small, positiveCode_rec, if_pos small]
    · have smaller : number / 2 < number := Nat.div_lt_self (by omega) (by omega)
      rw [if_neg small, positiveCode_rec, if_neg small]
      by_cases even : number % 2 = 0 <;> simp [smaller, even]
  exact strong.comp (Primrec.const ()) Primrec.id

def naturalCode (number : Nat) : Nat := patternCode (encodeNat number)

theorem naturalCode_eq (number : Nat) :
    naturalCode number = if number = 0 then nodeCode "Zero" [] else
      nodeCode "Positive" [positiveCode number] := by
  cases converted : (number : Num) with
  | zero =>
      have zero : number = 0 := by
        have same := congrArg (fun n : Num => (n : Nat)) converted
        simpa only [Num.to_of_nat, Num.cast_zero'] using same
      subst number
      rfl
  | pos positive =>
      have nonzero : number ≠ 0 := by
        intro zero
        subst number
        contradiction
      simp only [naturalCode, encodeNat, converted, encodeNumber, patternCode, patternListCode,
        if_neg nonzero, positiveCode, nodeCode, List.foldr_cons, List.foldr_nil]

theorem naturalCode_primrec : Primrec naturalCode :=
  (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const (nodeCode "Zero" []))
    ((nodeCode_one_primrec "Positive").comp positiveCode_primrec)).of_eq
      fun number => (naturalCode_eq number).symm

def numberCode (number : Nat) : Nat := nodeCode "Number" [naturalCode number]

theorem numberCode_primrec : Primrec numberCode :=
  (nodeCode_one_primrec "Number").comp naturalCode_primrec

theorem numberCode_eq (number : Nat) : numberCode number = patternCode (encode (.number number)) := by
  simp only [numberCode, encode, patternCode, patternListCode, nodeCode, naturalCode,
    List.foldr_cons, List.foldr_nil]

def valuesCode (values : List Nat) : Nat :=
  values.foldr (fun first rest => nodeCode "Cons" [first, rest]) (nodeCode "Nil" [])

theorem valuesCode_primrec : Primrec valuesCode := by
  have step : Primrec₂ fun (_ : List Nat) (pair : Nat × Nat) => nodeCode "Cons" [pair.1, pair.2] :=
    Primrec₂.mk ((nodeCode_two_primrec "Cons").comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr Primrec.id (Primrec.const _) step

theorem valuesCode_eq (expressions : List SExpr) :
    valuesCode (expressions.map (fun expression => patternCode (encode expression))) =
      patternCode (encodeValues expressions) := by
  induction expressions with
  | nil => simp only [List.map_nil, valuesCode, List.foldr_nil, encodeValues,
      patternCode, patternListCode, nodeCode]
  | cons first rest recurse =>
      simp only [List.map_cons, valuesCode, List.foldr_cons] at recurse ⊢
      rw [recurse]
      simp only [encodeValues, patternCode, patternListCode, nodeCode, List.foldr_cons,
        List.foldr_nil]

def listCode (values : List Nat) : Nat := nodeCode "List" [valuesCode values]

theorem listCode_primrec : Primrec listCode :=
  (nodeCode_one_primrec "List").comp valuesCode_primrec

theorem listCode_eq (expressions : List SExpr) :
    listCode (expressions.map (fun expression => patternCode (encode expression))) =
      patternCode (encode (.list expressions)) := by
  rw [listCode, valuesCode_eq]
  simp only [encode, patternCode, patternListCode, nodeCode, List.foldr_cons, List.foldr_nil]

def cellsCode (cells : List Nat) : Nat :=
  listCode (cells.map numberCode)

theorem cellsCode_primrec : Primrec cellsCode :=
  listCode_primrec.comp (Primrec.list_map Primrec.id (numberCode_primrec.comp₂ Primrec₂.right))

theorem cellsCode_eq (cells : List Nat) :
    cellsCode cells = patternCode (encode (TuringPrograms.encodeCells cells)) := by
  rw [cellsCode, TuringPrograms.encodeCells, ← listCode_eq, List.map_map]
  congr 1
  exact List.map_congr_left fun number _ => numberCode_eq number

def configurationCode (data : Nat × (List Nat × (Nat × List Nat))) : Nat :=
  listCode [numberCode data.1, cellsCode data.2.1, numberCode data.2.2.1, cellsCode data.2.2.2]

theorem configurationCode_primrec : Primrec configurationCode := by
  have state := numberCode_primrec.comp
    (Primrec.fst (α := Nat) (β := List Nat × (Nat × List Nat)))
  have leftCells := cellsCode_primrec.comp (Primrec.fst.comp
    (Primrec.snd (α := Nat) (β := List Nat × (Nat × List Nat))))
  have scanned := numberCode_primrec.comp (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd (α := Nat) (β := List Nat × (Nat × List Nat)))))
  have rightCells := cellsCode_primrec.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd (α := Nat) (β := List Nat × (Nat × List Nat)))))
  exact listCode_primrec.comp
    (Primrec.list_cons.comp state (Primrec.list_cons.comp leftCells
      (Primrec.list_cons.comp scanned (Primrec.list_cons.comp rightCells (Primrec.const [])))))

theorem configurationCode_eq (data : Nat × (List Nat × (Nat × List Nat))) :
    configurationCode data = patternCode (encode (TuringPrograms.encodeConfiguration
      ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩)) := by
  simpa only [configurationCode, numberCode_eq, cellsCode_eq, List.map_cons, List.map_nil,
    TuringPrograms.encodeConfiguration] using listCode_eq
      [SExpr.number data.1, TuringPrograms.encodeCells data.2.1,
        SExpr.number data.2.2.1, TuringPrograms.encodeCells data.2.2.2]

def quoteCode (expression : Nat) : Nat :=
  listCode [patternCode (encode (.symbol "'")), expression]

theorem quoteCode_primrec : Primrec quoteCode :=
  listCode_primrec.comp (Primrec.list_cons.comp (Primrec.const _)
    (Primrec.list_cons.comp Primrec.id (Primrec.const [])))

theorem quoteCode_eq (expression : SExpr) :
    quoteCode (patternCode (encode expression)) = patternCode (encode (Expressions.quote expression)) := by
  simpa only [quoteCode, Expressions.quote, Expressions.call, List.map_cons, List.map_nil] using
    listCode_eq [SExpr.symbol "'", expression]

def letCode (name : String) (value body : Nat) : Nat :=
  listCode [quoteCode (listCode [patternCode (encode (.symbol "lambda")),
    listCode [patternCode (encode (.symbol name))], body]), value]

theorem letCode_primrec (name : String) : Primrec₂ (letCode name) := by
  have lambda : Primrec fun pair : Nat × Nat =>
      listCode [patternCode (encode (.symbol "lambda")),
        listCode [patternCode (encode (.symbol name))], pair.2] :=
    listCode_primrec.comp (Primrec.list_cons.comp (Primrec.const _)
      (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp Primrec.snd (Primrec.const []))))
  exact Primrec₂.mk (listCode_primrec.comp
    (Primrec.list_cons.comp (quoteCode_primrec.comp lambda)
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))))

theorem letCode_eq (name : String) (value body : SExpr) :
    letCode name (patternCode (encode value)) (patternCode (encode body)) =
      patternCode (encode (Expressions.letValue name value body)) := by
  have parameters := listCode_eq [SExpr.symbol name]
  have lambda := listCode_eq [SExpr.symbol "lambda", .list [.symbol name], body]
  have quoted := quoteCode_eq (Expressions.lambda [name] body)
  have applied := listCode_eq [Expressions.quotedLambda [name] body, value]
  simp only [List.map_cons, List.map_nil] at parameters lambda applied
  simp only [Expressions.lambda, List.map_cons, List.map_nil] at quoted
  rw [letCode, parameters, lambda, quoted]
  exact applied

def programCode (source : TuringMachine.Machine) (configuration : Nat) : Nat :=
  letCode "find-row" (patternCode (encode TuringPrograms.lookupProgram))
    (letCode "move-row" (patternCode (encode TuringPrograms.transitionProgram))
      (letCode "run-table" (patternCode (encode TuringPrograms.loopProgram))
        (listCode [patternCode (encode (.symbol "run-table")),
          quoteCode (patternCode (encode (TuringPrograms.encodeTable source.transitions))),
          quoteCode configuration])))

theorem programCode_primrec (source : TuringMachine.Machine) : Primrec (programCode source) :=
  (letCode_primrec "find-row").comp (Primrec.const _)
    ((letCode_primrec "move-row").comp (Primrec.const _)
      ((letCode_primrec "run-table").comp (Primrec.const _)
        (listCode_primrec.comp (Primrec.list_cons.comp (Primrec.const _)
          (Primrec.list_cons.comp (Primrec.const _)
            (Primrec.list_cons.comp quoteCode_primrec (Primrec.const [])))))))

theorem programCode_eq (source : TuringMachine.Machine) (configuration : TuringMachine.Configuration) :
    programCode source (patternCode (encode (TuringPrograms.encodeConfiguration configuration))) =
      patternCode (encode (TuringPrograms.machineProgram source configuration)) := by
  rw [programCode, quoteCode_eq, quoteCode_eq,
    show listCode [patternCode (encode (.symbol "run-table")),
      patternCode (encode (Expressions.quote (TuringPrograms.encodeTable source.transitions))),
      patternCode (encode (Expressions.quote (TuringPrograms.encodeConfiguration configuration)))] =
        patternCode (encode (Expressions.call "run-table"
          [Expressions.quote (TuringPrograms.encodeTable source.transitions),
            Expressions.quote (TuringPrograms.encodeConfiguration configuration)])) by
      simpa only [Expressions.call, List.map_cons, List.map_nil] using
        listCode_eq [SExpr.symbol "run-table",
          Expressions.quote (TuringPrograms.encodeTable source.transitions),
          Expressions.quote (TuringPrograms.encodeConfiguration configuration)],
    letCode_eq, letCode_eq, letCode_eq]
  simp only [TuringPrograms.machineProgram, TuringPrograms.interpreterProgram]

def startCode (expression : Nat) : Nat := nodeCode "Eval"
  [expression, patternCode (encodeEnvironment cleanEnvironment), patternCode (encodeContinuation .done)]

theorem startCode_primrec : Primrec startCode :=
  (nodeCode_primrec "Eval").comp (Primrec.list_cons.comp Primrec.id
    (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp (Primrec.const _) (Primrec.const []))))

theorem startCode_eq (expression : SExpr) :
    startCode (patternCode (encode expression)) = patternCode (start expression) := by
  simpa only [startCode, start, encodeConfiguration, List.map_cons, List.map_nil] using
    nodeCode_map "Eval" [encode expression, encodeEnvironment cleanEnvironment, encodeContinuation .done]

def rawInputCode (source : TuringMachine.Machine) (raw : Nat) : Nat :=
  startCode (programCode source
    (configurationCode (Denumerable.ofNat (Nat × (List Nat × (Nat × List Nat))) raw)))

theorem rawInputCode_primrec (source : TuringMachine.Machine) : Primrec (rawInputCode source) :=
  startCode_primrec.comp ((programCode_primrec source).comp
    (configurationCode_primrec.comp (Primrec.ofNat _)))

theorem rawInputCode_eq (source : TuringMachine.Machine) (configuration : TuringMachine.Configuration) :
    rawInputCode source (TuringMachine.InputEncoding.configurationCode configuration) =
      patternCode (start (TuringPrograms.machineProgram source configuration)) := by
  unfold rawInputCode
  rw [TuringMachine.InputEncoding.configurationCode, Denumerable.ofNat_encode, configurationCode_eq]
  change startCode (programCode source
    (patternCode (encode (TuringPrograms.encodeConfiguration configuration)))) = _
  rw [programCode_eq, startCode_eq]

/-- Primitive-recursive preparation of the actual generated-language term,
under the framework's existing structural numbering. -/
theorem universal_input_code_primrec :
    Primrec fun index : Nat => patternCode (start (TuringInterpreter.universalProgram index 0)) := by
  have prepared : Primrec fun index : Nat => rawInputCode TuringMachine.UniversalTable.machine
      (TuringMachine.InputEncoding.configurationCode (TuringMachine.UniversalTable.inputConfiguration index 0)) :=
    (rawInputCode_primrec TuringMachine.UniversalTable.machine).comp
      TuringMachine.UniversalTable.input_code_primrec
  exact prepared.of_eq fun index => rawInputCode_eq TuringMachine.UniversalTable.machine
    (TuringMachine.UniversalTable.inputConfiguration index 0)

/-- Codes of terms that can reach a successful returned value. A blocked
effect request is not included merely because it has no pure-core reduct. -/
def ReturningCode (code : Nat) : Prop :=
  ∃ pattern, patternCode pattern = code ∧
    ∃ value, theory.MultiStep pattern (result value)

theorem returningCode_pattern (pattern : Pattern) :
    ReturningCode (patternCode pattern) ↔ ∃ value, theory.MultiStep pattern (result value) := by
  constructor
  · rintro ⟨other, same, returned⟩
    cases patternCode_injective same
    exact returned
  · exact fun returned => ⟨pattern, rfl, returned⟩

theorem returningCode_not_computable : ¬ ComputablePred ReturningCode := by
  intro decided
  apply universal_halting_not_computable
  obtain ⟨decidable, computable⟩ := decided
  have prepared : ComputablePred fun index : Nat =>
      ReturningCode (patternCode (start (TuringInterpreter.universalProgram index 0))) :=
    ⟨fun index => decidable _, computable.comp universal_input_code_primrec.to_comp⟩
  exact prepared.of_eq fun index => returningCode_pattern _

end Mettapedia.Languages.Chaitin.GSLT.CodePreparation
