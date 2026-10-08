import Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
import Mettapedia.TypeTheory.Calculi.ContextualCode.Destructuring

/-!
# Contextual code on the shared physical ABT

This adapter connects the existing contextual calculus to the signature-indexed
ABT engine. A nested quotation is an atomic owned field: opening an outer
context never traverses its payload. Abstractions have one field-local binder;
applications and the remaining computation forms have ordinary fields.

The adapter is not a new evaluator. Its opening theorem compares the calculus's
capture-avoiding substitution with the independent binder-eliminating ABT
operation. Native languages still have to supply these field-depth signatures
and qualify their syntax and ownership boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode.PhysicalABT

open Mettapedia.GSLT.LanguageDef

open Term

inductive Head where
  | sym (name : String)
  | lam
  | app
  | quote (parameters : Nat) (body : Term parameters)
  | lift
  | drop
  | matchCode {holes : Nat} (parameters : Nat) (pattern : Pat holes parameters)

def signature : Head → List Nat
  | .sym _ | .quote _ _ => []
  | .lam => [1]
  | .app | .matchCode _ _ => [0, 0]
  | .lift | .drop => [0]

def encode : {n : Nat} → Term n → SignatureIndexedABT.Term Head
  | _, .var index => .idx index.val
  | _, .sym name => .node (.sym name) .nil
  | _, .lam body => .node .lam (.cons 1 (encode body) .nil)
  | _, .app function argument =>
      .node .app (.cons 0 (encode function) (.cons 0 (encode argument) .nil))
  | _, .cquote parameters body => .node (.quote parameters body) .nil
  | _, .lift computation => .node .lift (.cons 0 (encode computation) .nil)
  | _, .drop code => .node .drop (.cons 0 (encode code) .nil)
  | _, .cmatch parameters code pattern handler =>
      .node (.matchCode parameters pattern)
        (.cons 0 (encode code) (.cons 0 (encode handler) .nil))

theorem encode_supported : ∀ {n : Nat} (term : Term n),
    SignatureIndexedABT.Term.supportedAt n (encode term) = true
  | _, .var index => by simp [encode, SignatureIndexedABT.Term.supportedAt, index.isLt]
  | _, .sym _ => rfl
  | _, .lam body => by
      simpa [encode, SignatureIndexedABT.Term.supportedAt, SignatureIndexedABT.Term.Fields.supportedAt] using
        encode_supported body
  | _, .app function argument => by
      simp [encode, SignatureIndexedABT.Term.supportedAt, SignatureIndexedABT.Term.Fields.supportedAt,
        encode_supported function, encode_supported argument]
  | _, .cquote _ _ => rfl
  | _, .lift computation => by
      simpa [encode, SignatureIndexedABT.Term.supportedAt, SignatureIndexedABT.Term.Fields.supportedAt] using
        encode_supported computation
  | _, .drop code => by
      simpa [encode, SignatureIndexedABT.Term.supportedAt, SignatureIndexedABT.Term.Fields.supportedAt] using
        encode_supported code
  | _, .cmatch _ code _ handler => by
      simp [encode, SignatureIndexedABT.Term.supportedAt, SignatureIndexedABT.Term.Fields.supportedAt,
        encode_supported code, encode_supported handler]

theorem encode_conforms : ∀ {n : Nat} (term : Term n),
    SignatureIndexedABT.Term.conforms signature (encode term) = true
  | _, .var _ => rfl
  | _, .sym _ => rfl
  | _, .lam body => by
      simp [encode, SignatureIndexedABT.Term.conforms, SignatureIndexedABT.Term.Fields.conforms,
        signature, encode_conforms body]
  | _, .app function argument => by
      simp [encode, SignatureIndexedABT.Term.conforms, SignatureIndexedABT.Term.Fields.conforms, signature,
        encode_conforms function, encode_conforms argument]
  | _, .cquote _ _ => rfl
  | _, .lift computation => by
      simp [encode, SignatureIndexedABT.Term.conforms, SignatureIndexedABT.Term.Fields.conforms,
        signature, encode_conforms computation]
  | _, .drop code => by
      simp [encode, SignatureIndexedABT.Term.conforms, SignatureIndexedABT.Term.Fields.conforms,
        signature, encode_conforms code]
  | _, .cmatch _ code _ handler => by
      simp [encode, SignatureIndexedABT.Term.conforms, SignatureIndexedABT.Term.Fields.conforms, signature,
        encode_conforms code, encode_conforms handler]

/-- A context extension that preserves every old index is invisible to the
physical encoding. The premise is vacuous only for a genuinely closed term. -/
theorem encode_rename_same : ∀ {n m : Nat} (mapping : Ren n m)
    (_same : ∀ index, (mapping index).val = index.val) (term : Term n),
    encode (term.rename mapping) = encode term
  | _, _, mapping, same, .var index => by simp [rename, encode, same index]
  | _, _, _, _, .sym _ => rfl
  | _, _, mapping, same, .lam body => by
      have lifted : ∀ index, (liftRen mapping index).val = index.val := by
        intro index
        cases index using Fin.cases with
        | zero => rfl
        | succ index => simp [same index]
      simp only [rename, encode, encode_rename_same (liftRen mapping) lifted body]
  | _, _, mapping, same, .app function argument => by
      simp only [rename, encode, encode_rename_same mapping same function,
        encode_rename_same mapping same argument]
  | _, _, _, _, .cquote _ _ => rfl
  | _, _, mapping, same, .lift computation => by
      simp only [rename, encode, encode_rename_same mapping same computation]
  | _, _, mapping, same, .drop code => by
      simp only [rename, encode, encode_rename_same mapping same code]
  | _, _, mapping, same, .cmatch _ code _ handler => by
      simp only [rename, encode, encode_rename_same mapping same code,
        encode_rename_same mapping same handler]

theorem encode_ofClosed {n : Nat} (term : Term 0) :
    encode (ofClosed (n := n) term) = encode term :=
  encode_rename_same _ (fun index => Fin.elim0 index) term

/-- Opening the first written parameter commutes with physical ABT
instantiation, including beneath local binders and beside nested quotes. -/
theorem encode_openFirst (replacement : Term 0) : ∀ {n : Nat} (body : Term (n + 1)),
    encode (openFirst replacement body) =
      SignatureIndexedABT.Term.instantiateAt n (encode replacement) (encode body)
  | n, .var index => by
      cases index using Fin.lastCases with
      | last =>
          simp only [openFirst, subst, firstParamSub, Fin.lastCases_last, encode_ofClosed]
          simp [encode, SignatureIndexedABT.Term.instantiateAt,
            SignatureIndexedABT.Term.lift_of_supported 0 n (encode replacement) (encode_supported replacement)]
      | cast index =>
          simp only [openFirst, subst, firstParamSub, Fin.lastCases_castSucc]
          simp [encode, SignatureIndexedABT.Term.instantiateAt, index.isLt]
  | _, .sym _ => rfl
  | n, .lam body => by
      simp only [openFirst, subst, liftSub_firstParamSub]
      change encode (.lam (openFirst replacement body)) = _
      simp only [encode, SignatureIndexedABT.Term.instantiateAt, SignatureIndexedABT.Term.Fields.instantiateAt,
        encode_openFirst replacement body]
  | _, .app function argument => by
      change encode (.app (openFirst replacement function) (openFirst replacement argument)) = _
      simp only [encode, SignatureIndexedABT.Term.instantiateAt, SignatureIndexedABT.Term.Fields.instantiateAt,
        Nat.add_zero, encode_openFirst replacement function, encode_openFirst replacement argument]
  | _, .cquote _ _ => rfl
  | _, .lift computation => by
      change encode (.lift (openFirst replacement computation)) = _
      simp only [encode, SignatureIndexedABT.Term.instantiateAt, SignatureIndexedABT.Term.Fields.instantiateAt,
        Nat.add_zero, encode_openFirst replacement computation]
  | _, .drop code => by
      change encode (.drop (openFirst replacement code)) = _
      simp only [encode, SignatureIndexedABT.Term.instantiateAt, SignatureIndexedABT.Term.Fields.instantiateAt,
        Nat.add_zero, encode_openFirst replacement code]
  | _, .cmatch parameters code pattern handler => by
      change encode (.cmatch parameters (openFirst replacement code) pattern
        (openFirst replacement handler)) = _
      simp only [encode, SignatureIndexedABT.Term.instantiateAt, SignatureIndexedABT.Term.Fields.instantiateAt,
        Nat.add_zero, encode_openFirst replacement code, encode_openFirst replacement handler]

/-- The native binder-eliminating operation therefore inherits the existing
close/open inverse, without substituting into a nested quotation. -/
theorem instantiate_closeSym {n : Nat} (name : String) (body : Term n) :
    SignatureIndexedABT.Term.instantiateAt n (encode (.sym name : Term 0)) (encode (closeSym name body)) =
      encode body := by
  rw [← encode_openFirst, openFirst_closeSym]

/-- Positive control: the outer parameter is opened, a local binder remains. -/
example : SignatureIndexedABT.Term.instantiateAt 0 (encode (.sym "payload" : Term 0))
    (encode (.lam (.app (.var 1) (.var 0)) : Term 1)) =
    encode (.lam (.app (.sym "payload") (.var 0)) : Term 0) := by
  rw [← encode_openFirst]
  rfl

/-- Negative control: an outer opening cannot capture the inner code's index. -/
example : SignatureIndexedABT.Term.instantiateAt 0 (encode (.sym "payload" : Term 0))
    (encode (.cquote 1 (.var 0) : Term 1)) =
    encode (.cquote 1 (.var 0) : Term 0) := rfl

end Mettapedia.TypeTheory.Calculi.ContextualCode.PhysicalABT
