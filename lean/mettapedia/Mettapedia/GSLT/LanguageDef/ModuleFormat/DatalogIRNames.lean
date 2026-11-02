import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoin
import Mathlib.Tactic.IntervalCases
import Std.Data.String.ToNat

/-! Compiler-generated names distinguish pools, logical variables and every
anonymous occurrence, including different argument positions in one clause. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Names

inductive Role where
  | relation (index : Nat)
  | literal (index : Nat)
  | logical (name : String)
  | anonymous (position argument : Nat)
  deriving DecidableEq, Repr

def encode : Role → String
  | .relation index => Join.relationSlot index
  | .literal index => Join.literalSlot index
  | .logical name => Join.logicalVariable name
  | .anonymous position argument => Join.anonymousVariable position argument

private theorem digit_ne_separator (digit : Nat) (small : digit < 10) : Nat.digitChar digit ≠ ':' := by
  interval_cases digit <;> decide

private theorem repr_no_separator (number : Nat) : ':' ∉ number.repr.toList := by
  induction number using Nat.strong_induction_on with
  | h number ih =>
    by_cases small : number < 10
    · rw [Nat.repr_of_lt small]
      simp only [String.toList_singleton,List.mem_singleton]
      exact Ne.symm (digit_ne_separator number small)
    · rw [Nat.repr_of_ge (by omega),String.toList_append]
      intro present
      rcases List.mem_append.mp present with before | last
      · exact ih (number / 10) (Nat.div_lt_self (by omega) (by omega)) before
      · simp only [String.toList_singleton,List.mem_singleton] at last
        exact digit_ne_separator (number % 10) (Nat.mod_lt _ (by omega)) last.symm

theorem anonymous_injective {position argument otherPosition otherArgument : Nat}
    (same : Join.anonymousVariable position argument = Join.anonymousVariable otherPosition otherArgument) :
    position = otherPosition ∧ argument = otherArgument := by
  simp only [Join.anonymousVariable,String.append_assoc] at same
  have suffix := (String.append_right_inj "anonymous:").mp same
  have characters := congrArg String.toList suffix
  simp only [String.toList_append] at characters
  have before := congrArg (List.takeWhile (fun character => character != ':')) characters
  have take (number : Nat) : ∀ character ∈ (toString number).toList, (character != ':') = true := by
    intro character member
    have different : character ≠ ':' := by intro same; exact repr_no_separator number (same ▸ member)
    simp [different]
  simp only [show ":".toList = [':'] from rfl,List.singleton_append,
    List.takeWhile_append_of_pos (take position),List.takeWhile_append_of_pos (take otherPosition),
    List.takeWhile_cons_of_neg (a := ':') (p := fun character : Char => character != ':') (by decide),List.append_nil] at before
  have first : position = otherPosition := Nat.repr_injective (String.toList_inj.mp before)
  subst otherPosition
  have second := (String.append_right_inj (toString position ++ ":")).mp
    (by simpa only [String.append_assoc] using suffix)
  exact ⟨rfl,Nat.repr_injective second⟩

theorem encode_injective : Function.Injective encode := by
  intro first second same
  cases first with
  | relation index =>
    cases second with
    | relation other =>
      have eq := (String.append_right_inj "pool:relation:").mp same
      exact congrArg Role.relation (Nat.repr_injective eq)
    | literal other =>
      have tag := congrArg (fun text => (text.toList.drop 5).head?) same
      simp [encode,Join.relationSlot,Join.literalSlot,String.toList_append] at tag
    | logical name =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.relationSlot,Join.logicalVariable,String.toList_append] at tag
    | anonymous p i =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.relationSlot,Join.anonymousVariable,String.toList_append] at tag
  | literal index =>
    cases second with
    | relation other =>
      have tag := congrArg (fun text => (text.toList.drop 5).head?) same
      simp [encode,Join.relationSlot,Join.literalSlot,String.toList_append] at tag
    | literal other =>
      have eq := (String.append_right_inj "pool:literal:").mp same
      exact congrArg Role.literal (Nat.repr_injective eq)
    | logical name =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.literalSlot,Join.logicalVariable,String.toList_append] at tag
    | anonymous p i =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.literalSlot,Join.anonymousVariable,String.toList_append] at tag
  | logical name =>
    cases second with
    | relation other =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.relationSlot,Join.logicalVariable,String.toList_append] at tag
    | literal other =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.literalSlot,Join.logicalVariable,String.toList_append] at tag
    | logical other => exact congrArg Role.logical ((String.append_right_inj "variable:").mp same)
    | anonymous p i =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.logicalVariable,Join.anonymousVariable,String.toList_append] at tag
  | anonymous position argument =>
    cases second with
    | relation other =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.relationSlot,Join.anonymousVariable,String.toList_append] at tag
    | literal other =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.literalSlot,Join.anonymousVariable,String.toList_append] at tag
    | logical name =>
      have tag := congrArg (fun text => text.toList.head?) same
      simp [encode,Join.logicalVariable,Join.anonymousVariable,String.toList_append] at tag
    | anonymous otherPosition otherArgument =>
      obtain ⟨rfl,rfl⟩ := anonymous_injective same
      rfl

#print axioms anonymous_injective
#print axioms encode_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Names
