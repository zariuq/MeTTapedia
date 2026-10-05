import Mettapedia.Languages.Chaitin.Bridges.MeTTa.WireData
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireData

/-!
# Historical Lisp program data in declaration-based Prime

The shared physical wire codec embeds Lisp values into the existing native
data signature. Exact decoding supplies the data meaning, native formation
supplies its type, and substitution/renaming preserve literal code. Lisp
variable spellings remain words inside this representation.

The declarations are opaque data constructors. Native execution of a hosted
Lisp evaluator is a separate operational comparison; native data typing does
not assert that a represented Lisp program terminates or is a valid proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.Bridges.Chaitin.Data

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation

abbrev Lisp := Mettapedia.Languages.Chaitin.SExpr

open Mettapedia.Languages.Chaitin.Bridges.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

def encode {n : Nat} (expression : Lisp) : Tower.Tm n :=
  NativeWireData.encode (WireData.encode expression)

def decode {n : Nat} (term : Tower.Tm n) : Option Lisp :=
  (NativeWireData.decode term).bind WireData.decode

@[simp] theorem decode_encode {n : Nat} (expression : Lisp) :
    decode (encode (n := n) expression) = some expression := by
  simp only [decode, encode, NativeWireData.decode_encode, Option.bind_some, WireData.decode_encode]

theorem encode_injective {n : Nat} : Function.Injective (encode (n := n)) := by
  intro first second same
  exact WireData.encode_injective (NativeWireData.encode_injective same)

theorem encode_typing {n : Nat} (context : Tower.Ctx n) (expression : Lisp) :
    FormationSensitive.Typing NativeWireData.rules context (encode expression) NativeWireData.dataType :=
  NativeWireData.encode_typing context (WireData.encode expression)

theorem encode_judgment {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation NativeWireData.rules context) (expression : Lisp) :
    FormationSensitive.Judgment NativeWireData.rules context (encode expression) NativeWireData.dataType :=
  NativeWireData.encode_judgment formed (WireData.encode expression)

@[simp] theorem subst_encode {n m : Nat} (substitution : Sub Tower.Head n m)
    (expression : Lisp) : subst substitution (encode expression) = encode expression :=
  NativeWireData.subst_encode substitution (WireData.encode expression)

@[simp] theorem rename_encode {n m : Nat} (rho : Ren n m) (expression : Lisp) :
    rename rho (encode expression) = encode expression :=
  NativeWireData.rename_encode rho (WireData.encode expression)

/-- Instantiating a surrounding binder leaves the represented guest program
unchanged; it does not perform substitution inside Lisp code. -/
theorem instantiate_preserves_program {n : Nat} (argument : Tower.Tm n) (expression : Lisp) :
    inst0 argument (encode expression) = encode expression :=
  subst_encode _ expression

/-- An actual native beta step returns the literal guest program unchanged. -/
theorem beta_returns_program {n : Nat} (argument : Tower.Tm n) (expression : Lisp) :
    StepCore NativeWireData.rules.computation (fun _ _ => False)
      (.app (.lam (encode expression)) argument) (encode expression) := by
  have step : StepCore NativeWireData.rules.computation (fun _ _ => False)
      (.app (.lam (encode expression)) argument) (inst0 argument (encode expression)) :=
    .betaPi _ _
  simpa only [instantiate_preserves_program] using step

/-- Guest environment lookup and surrounding native instantiation are
different operations, even for a single variable-looking word. -/
theorem guest_lookup_is_not_native_instantiation (argument : Tower.Tm 0) (value : Nat) :
    inst0 argument (encode (.symbol "x")) ≠
      encode (Mettapedia.Languages.Chaitin.lookup [(.symbol "x", .number value)] (.symbol "x")) := by
  rw [instantiate_preserves_program]
  have found : Mettapedia.Languages.Chaitin.lookup [(.symbol "x", .number value)] (.symbol "x") =
      .number value := rfl
  rw [found]
  intro same
  cases encode_injective same

theorem native_variable_rejected {n : Nat} (index : Fin n) :
    decode (.var index) = none := by
  simp only [decode, NativeWireData.native_variable_rejected, Option.bind_none]

theorem physical_string_rejected {n : Nat} (value : String) :
    decode (NativeWireData.encode (n := n) (.string value)) = none := by
  simp only [decode, NativeWireData.decode_encode, Option.bind_some, WireData.decode_string]

theorem numeric_word_distinct {n : Nat} (value : Nat) :
    encode (n := n) (.symbol (toString value)) ≠ encode (.number value) := by
  intro same
  cases encode_injective same

theorem closed_program_typed (expression : Lisp) :
    FormationSensitive.Judgment NativeWireData.rules .nil (encode expression) NativeWireData.dataType :=
  encode_judgment .nil expression

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.Bridges.Chaitin.Data
