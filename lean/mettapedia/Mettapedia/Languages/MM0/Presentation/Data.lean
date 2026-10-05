import Mettapedia.Languages.MM0.Kernel.Term
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalData

/-! # MM0 preterms as constructor data for shared equation programs -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation

open Kernel
open Mettapedia.GSLT.LanguageDef

def encode : Preterm → DeterministicEquations.Term
  | .var index => .expr [.sym "MM0:Var", DeterministicEquations.natural index]
  | .term index => .expr [.sym "MM0:Term", DeterministicEquations.natural index]
  | .app function argument => .expr [.sym "MM0:App", encode function, encode argument]

def decode : DeterministicEquations.Term → Option Preterm
  | .expr [.sym "MM0:Var", index] => (DeterministicEquations.natural? index).map Preterm.var
  | .expr [.sym "MM0:Term", index] => (DeterministicEquations.natural? index).map Preterm.term
  | .expr [.sym "MM0:App", function, argument] => do
      let function' ← decode function
      let argument' ← decode argument
      pure (.app function' argument')
  | _ => none

@[simp] theorem decode_encode (term : Preterm) : decode (encode term) = some term := by
  induction term with
  | var index => simp [encode, decode]
  | term index => simp [encode, decode]
  | app function argument first second => simp [encode, decode, first, second]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa using decoded

def constructorHeads : List String := ["MM0:Var", "MM0:Term", "MM0:App"]

/-- Guest tags cannot be interpreted as functions or primitives. -/
structure DataSeparated (P : DeterministicEquations.Program) (H : DeterministicEquations.Host) : Prop where
  undefined : ∀ head ∈ constructorHeads, P.defines head = false
  unhandled : ∀ head ∈ constructorHeads, ∀ arguments, H.primitive head arguments = .unhandled

theorem encoded_passive {P : DeterministicEquations.Program} {H : DeterministicEquations.Host}
    (separated : DataSeparated P H) (term : Preterm) :
    DeterministicEquations.PassiveData P H (encode term) := by
  induction term with
  | var index =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro argument member
        have same := List.mem_singleton.mp member
        subst argument
        exact DeterministicEquations.natural_passive _ _ _
  | term index =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro argument member
        have same := List.mem_singleton.mp member
        subst argument
        exact DeterministicEquations.natural_passive _ _ _
  | app function argument first second =>
      apply DeterministicEquations.PassiveData.node
      · simp [DeterministicEquations.Special]
      · exact separated.undefined _ (by simp [constructorHeads])
      · exact separated.unhandled _ (by simp [constructorHeads]) _
      · intro value member
        simp at member
        rcases member with rfl | rfl
        · exact first
        · exact second

theorem encoded_evaluation {P : DeterministicEquations.Program} {H : DeterministicEquations.Host}
    (separated : DataSeparated P H) (term : Preterm) (environment : DeterministicEquations.Env) (fuel : Nat)
    (enough : sizeOf (encode term) < fuel) :
    DeterministicEquations.eval P H fuel environment (encode term) = .value (encode term) :=
  (encoded_passive separated term).eval_eq_value environment fuel enough

theorem foreign_tag_refuses : decode (.expr [.sym "Foreign:Var", DeterministicEquations.natural 0]) = none := rfl

theorem partial_application_refuses :
    decode (.expr [.sym "MM0:App", encode (.var 0)]) = none := rfl

theorem natural_index_has_no_word_bound :
    decode (encode (.var 18446744073709551616)) = some (.var 18446744073709551616) :=
  decode_encode _

end Mettapedia.Languages.MM0.Presentation
