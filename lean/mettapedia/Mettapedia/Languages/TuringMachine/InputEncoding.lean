import Mettapedia.Languages.TuringMachine.PartrecBridge
import Mettapedia.Computability.KolmogorovComplexity.SelfDelimitingCode
import Mettapedia.OSLF.MeTTaIL.UnaryNumeralCode

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.InputEncoding

open Turing Turing.ToPartrec

private def bitSymbol (digit : Nat) : PartrecToTM2.Γ' :=
  if digit = 1 then .bit1 else .bit0

private theorem trPosNum_digits (number : PosNum) :
    PartrecToTM2.trPosNum number = (Nat.digits 2 (number : Nat)).map bitSymbol := by
  induction number with
  | one =>
      change [PartrecToTM2.Γ'.bit1] = (Nat.digits 2 1).map bitSymbol
      rw [Nat.digits_eq_cons_digits_div (by omega) (by omega)]
      rfl
  | bit0 number induction =>
      rw [PosNum.cast_bit0, Nat.digits_eq_cons_digits_div (by omega) (by
        have := PosNum.to_nat_pos number
        omega)]
      have quotient : ((number : Nat) + number) / 2 = number := by omega
      have remainder : ((number : Nat) + number) % 2 = 0 := by omega
      rw [quotient, remainder, List.map_cons, ← induction]
      rfl
  | bit1 number induction =>
      rw [PosNum.cast_bit1, Nat.digits_eq_cons_digits_div (by omega) (by omega)]
      have quotient : ((number : Nat) + number + 1) / 2 = number := by omega
      have remainder : ((number : Nat) + number + 1) % 2 = 1 := by omega
      rw [quotient, remainder, List.map_cons, ← induction]
      rfl

private theorem trNum_digits (number : Num) :
    PartrecToTM2.trNum number = (Nat.digits 2 (number : Nat)).map bitSymbol := by
  cases number with
  | zero => simp [PartrecToTM2.trNum]
  | pos number => exact trPosNum_digits number

theorem trNat_digits (number : Nat) :
    PartrecToTM2.trNat number = (Nat.digits 2 number).map bitSymbol := by
  simpa only [PartrecToTM2.trNat, Num.to_of_nat] using trNum_digits (number : Num)

theorem coded_trNat_primrec (code : PartrecToTM2.Γ' → Nat) :
    Primrec fun number => (PartrecToTM2.trNat number).map code := by
  have digit : Primrec fun n => code (bitSymbol n) := by
    apply (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
      (Primrec.const (code .bit1)) (Primrec.const (code .bit0))).of_eq
    intro n
    by_cases h : n = 1 <;> simp [bitSymbol, h]
  exact (Primrec.list_map KolmogorovComplexity.digitsTwo_primrec
    (digit.comp₂ Primrec₂.right)).of_eq fun n => by
      rw [trNat_digits, List.map_map]
      rfl

theorem coded_trList_primrec (code : PartrecToTM2.Γ' → Nat) :
    Primrec fun input : List Nat => (PartrecToTM2.trList input).map code := by
  have step : Primrec₂ fun (_ : List Nat) (pair : Nat × List Nat) =>
      (PartrecToTM2.trNat pair.1).map code ++ code .cons :: pair.2 :=
    Primrec₂.mk (Primrec.list_append.comp
      ((coded_trNat_primrec code).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const (code .cons))
        (Primrec.snd.comp Primrec.snd)))
  have folded : Primrec fun input : List Nat =>
      input.foldr (fun n tail => (PartrecToTM2.trNat n).map code ++ code .cons :: tail) [] :=
    Primrec.list_foldr Primrec.id (Primrec.const []) step
  apply folded.of_eq
  intro input
  induction input with
  | nil => rfl
  | cons head tail induction => simp [PartrecToTM2.trList, induction]

/-- A cell with a symbol on the main stack and no symbols on the others. -/
def cell (bottom : Bool) (symbol : PartrecToTM2.Γ') : PartrecBridge.Alphabet :=
  (bottom, Function.update (fun _ => none) .main (some symbol))

def emptyBottom : PartrecBridge.Alphabet := (true, fun _ => none)

theorem coded_tapeInput (code : PartrecBridge.Alphabet → Nat) (input : List Nat) :
    (PartrecBridge.tapeInput input).map code =
      (((PartrecToTM2.trList input).map (fun symbol => code (cell true symbol))).reverse.head?
        |>.getD (code emptyBottom)) ::
      (((PartrecToTM2.trList input).map (fun symbol => code (cell false symbol))).reverse.tail) := by
  change List.map code
    (let records : List PartrecBridge.Alphabet :=
      (PartrecToTM2.trList input).reverse.map (cell false)
     (true, records.headI.2) :: records.tail) = _
  rw [← List.map_reverse, ← List.map_reverse]
  generalize (PartrecToTM2.trList input).reverse = symbols
  cases symbols with
  | nil => rfl
  | cons head tail =>
      dsimp only
      simp only [List.map_cons, List.headI_cons, List.tail_cons, List.head?_cons,
        Option.getD_some]
      change code (cell true head) :: (tail.map (cell false)).map code = _
      rw [List.map_map]
      rfl

theorem coded_tapeInput_primrec (code : PartrecBridge.Alphabet → Nat) :
    Primrec fun input : List Nat => (PartrecBridge.tapeInput input).map code := by
  have bottom : Primrec fun input : List Nat =>
      ((PartrecToTM2.trList input).map (fun symbol => code (cell true symbol))).reverse :=
    Primrec.list_reverse.comp (coded_trList_primrec _)
  have rest : Primrec fun input : List Nat =>
      ((PartrecToTM2.trList input).map (fun symbol => code (cell false symbol))).reverse :=
    Primrec.list_reverse.comp (coded_trList_primrec _)
  exact (Primrec.list_cons.comp
    (Primrec.option_getD.comp (Primrec.list_head?.comp bottom) (Primrec.const (code emptyBottom)))
    (Primrec.list_tail.comp rest)).of_eq fun input => (coded_tapeInput code input).symm

/-- A primitive-recursive code of raw configurations, including both half-tapes. -/
def configurationCode (configuration : Configuration) : Nat :=
  Encodable.encode (configuration.state, (configuration.left,
    (configuration.scanned, configuration.right)))

theorem inputConfiguration_code_primrec (program : Code) :
    Primrec fun input : List Nat => configurationCode (PartrecBridge.inputConfiguration program input) := by
  let := PartrecBridge.initialLabels program
  let := FiniteControl.controlInhabited (TM1to0.tr PartrecBridge.tapeProgram)
    (PartrecBridge.support program) (PartrecBridge.supported program)
  let symbol := (PartrecBridge.encoding program).symbol
  have codedInput : Primrec fun input : List Nat => (PartrecBridge.tapeInput input).map symbol :=
    coded_tapeInput_primrec symbol
  have head : Primrec fun input : List Nat => ((PartrecBridge.tapeInput input).map symbol).headI :=
    Primrec.list_headI.comp codedInput
  have tail : Primrec fun input : List Nat => ((PartrecBridge.tapeInput input).map symbol).tail :=
    Primrec.list_tail.comp codedInput
  apply (Primrec.encode.comp ((Primrec.const (PartrecBridge.inputConfiguration program []).state).pair ((Primrec.const ([] : List Nat)).pair
    (head.pair tail)))).of_eq
  intro input
  unfold configurationCode PartrecBridge.inputConfiguration FinitePostCompiler.initial
  rw [symbol.headI_map, List.map_tail]
  rfl

/-- A raw configuration code determines all four components. -/
theorem configurationCode_injective : Function.Injective configurationCode := by
  intro first second same
  have components :
      (first.state, (first.left, (first.scanned, first.right))) =
      (second.state, (second.left, (second.scanned, second.right))) :=
    Encodable.encode_injective same
  cases first
  cases second
  simp only [Prod.mk.injEq] at components
  rcases components with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- The structural code of a half-tape is primitive recursive. -/
theorem cellsTerm_code_primrec :
    Primrec fun symbols : List Nat =>
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (cellsTerm symbols) := by
  open Mettapedia.OSLF.MeTTaIL.PatternCode in
  have step : Primrec₂ fun (_ : List Nat) (pair : Nat × Nat) =>
      Nat.pair 2 (Nat.pair (stringCode "Cell")
        (Nat.succ (Nat.pair (unaryCode "SZero" "SSucc" pair.1)
          (Nat.succ (Nat.pair pair.2 0))))) :=
    Primrec₂.mk (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const _)
        (Primrec.succ.comp (Primrec₂.natPair.comp
          ((unaryCode_primrec "SZero" "SSucc").comp (Primrec.fst.comp Primrec.snd))
          (Primrec.succ.comp (Primrec₂.natPair.comp
            (Primrec.snd.comp Primrec.snd) (Primrec.const 0)))))))
  open Mettapedia.OSLF.MeTTaIL.PatternCode in
  apply (Primrec.list_foldr Primrec.id (Primrec.const (patternCode emptyCells)) step).of_eq
  intro symbols
  induction symbols with
  | nil => rfl
  | cons head tail induction =>
      simp only [id_eq, List.foldr_cons] at induction ⊢
      rw [induction]
      rfl

/-- The shared pattern code of a configuration term is effective on its data. -/
theorem configurationPatternCode_primrec :
    Primrec fun data : Nat × (List Nat × (Nat × List Nat)) =>
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (Configuration.mk data.1 data.2.1 data.2.2.1 data.2.2.2).term := by
  open Mettapedia.OSLF.MeTTaIL.PatternCode in
  have state : Primrec fun data : Nat × (List Nat × (Nat × List Nat)) =>
      unaryCode "QZero" "QSucc" data.1 :=
    (unaryCode_primrec _ _).comp Primrec.fst
  have leftCells : Primrec fun data : Nat × (List Nat × (Nat × List Nat)) =>
      patternCode (cellsTerm data.2.1) :=
    cellsTerm_code_primrec.comp (Primrec.fst.comp Primrec.snd)
  have scanned : Primrec fun data : Nat × (List Nat × (Nat × List Nat)) =>
      unaryCode "SZero" "SSucc" data.2.2.1 :=
    (unaryCode_primrec _ _).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have rightCells : Primrec fun data : Nat × (List Nat × (Nat × List Nat)) =>
      patternCode (cellsTerm data.2.2.2) :=
    cellsTerm_code_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have cons : ∀ {first rest : (Nat × (List Nat × (Nat × List Nat))) → Nat},
      Primrec first → Primrec rest →
      Primrec fun data => Nat.succ (Nat.pair (first data) (rest data)) :=
    fun first rest => Primrec.succ.comp (Primrec₂.natPair.comp first rest)
  have applyNode : ∀ {arguments : (Nat × (List Nat × (Nat × List Nat))) → Nat},
      (label : String) → Primrec arguments →
      Primrec fun data => Nat.pair 2 (Nat.pair (stringCode label) (arguments data)) :=
    fun label arguments => Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const (stringCode label)) arguments)
  exact applyNode "Run" (cons state (cons
    (applyNode "At" (cons leftCells (cons scanned (cons rightCells (Primrec.const 0)))))
    (Primrec.const 0)))

/-- Prepared input terms have primitive-recursive shared pattern codes. -/
theorem inputConfiguration_patternCode_primrec (program : Code) :
    Primrec fun input : List Nat => Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
      (PartrecBridge.inputConfiguration program input).term := by
  apply (configurationPatternCode_primrec.comp
    ((Primrec.ofNat (Nat × (List Nat × (Nat × List Nat)))).comp
      (inputConfiguration_code_primrec program))).of_eq
  intro input
  rw [configurationCode, Denumerable.ofNat_encode]

end Mettapedia.Languages.TuringMachine.InputEncoding
