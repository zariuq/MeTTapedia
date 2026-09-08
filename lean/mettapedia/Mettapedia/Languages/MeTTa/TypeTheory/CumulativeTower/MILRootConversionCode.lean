import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILHypothesis
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralConversionCode

/-!
# Executable root receipts for the native hypothesis package

Each code retains the arguments of one authored primitive or chain rule.
Decoding computes both endpoints, including every repeated metadata field
and both recursive calls in the chain result. No conversion test participates
in exact root matching. The data has no proof fields.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILRootConversionCode

open Presentation IntrinsicMILHypothesis

variable {n : Nat}

/-- Finite authored root data, before any claimed endpoints are trusted. -/
inductive Code (n : Nat) where
  | primitive (sorts primitives motive primitiveCase chainCase source target symbol : Tower.Tm n)
  | chain (sorts primitives motive primitiveCase chainCase source middle target earlier later : Tower.Tm n)
  deriving DecidableEq, Repr

/-- The source repeats exactly the metadata that the original rule repeats;
the result is the original native contraction, not an auxiliary completion. -/
def Code.endpoints : Code n → Tower.Tm n × Tower.Tm n
  | .primitive sorts primitives motive primitiveCase chainCase source target symbol =>
      (eliminateApp sorts primitives motive primitiveCase chainCase source target
        (primitiveApp sorts primitives source target symbol),
       .app (.app (.app primitiveCase source) target) symbol)
  | .chain sorts primitives motive primitiveCase chainCase source middle target earlier later =>
      (eliminateApp sorts primitives motive primitiveCase chainCase source target
        (chainApp sorts primitives source middle target earlier later),
       .app
         (.app (.app (.app (.app (.app (.app chainCase source) middle) target) earlier) later)
           (eliminateApp sorts primitives motive primitiveCase chainCase source middle earlier))
         (eliminateApp sorts primitives motive primitiveCase chainCase middle target later))

/-- Every well-scoped root code computes its endpoints. Arbitrary claimed
endpoints must still agree with this result at the enclosing checker. -/
def decode (code : Code n) : Option (Tower.Tm n × Tower.Tm n) :=
  some code.endpoints

theorem decode_sound (code : Code n) {left right : Tower.Tm n}
    (decoded : decode code = some (left, right)) :
    IntrinsicMILHypothesis.rules.computation.step left right := by
  cases code with
  | primitive sorts primitives motive primitiveCase chainCase source target symbol =>
      simp only [decode, Code.endpoints, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .declared ⟨.primitive sorts primitives motive primitiveCase chainCase source target symbol⟩
  | chain sorts primitives motive primitiveCase chainCase source middle target earlier later =>
      simp only [decode, Code.endpoints, Option.some.injEq, Prod.mk.injEq] at decoded
      rcases decoded with ⟨rfl, rfl⟩
      exact .declared
        ⟨.chain sorts primitives motive primitiveCase chainCase source middle target earlier later⟩

/-- Every original root has finite code, including all open instances. The
underlying tower has no inherited roots and this signature has no values. -/
theorem decode_complete {left right : Tower.Tm n}
    (step : IntrinsicMILHypothesis.rules.computation.step left right) :
    ∃ code : Code n, decode code = some (left, right) := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta lookup => rw [rawSignature_valueOf_none] at lookup; cases lookup
  | declared supported =>
      obtain ⟨evidence⟩ := supported
      cases evidence with
      | primitive sorts primitives motive primitiveCase chainCase source target symbol =>
          exact ⟨.primitive sorts primitives motive primitiveCase chainCase source target symbol, rfl⟩
      | chain sorts primitives motive primitiveCase chainCase source middle target earlier later =>
          exact
            ⟨.chain sorts primitives motive primitiveCase chainCase source middle target earlier later, rfl⟩

/-- Qualification for structural conversion checking over unchanged native
root computation. This does not install a different evaluation relation. -/
def decoder : StructuralConversionCode.RootDecoder IntrinsicMILHypothesis.rules.computation where
  Code := Code
  decode := decode
  sound := decode_sound
  complete := decode_complete

namespace Examples

def primitiveCode : Code 8 :=
  .primitive (.var 7) (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def chainCode : Code 10 :=
  .chain (.var 9) (.var 8) (.var 7) (.var 6) (.var 5)
    (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

/-- Decoding the open primitive schema yields its actual native step. -/
theorem primitive_decodes_and_steps :
    decode primitiveCode = some (primitiveIotaLeft, primitiveIotaRight) ∧
      IntrinsicMILHypothesis.rules.computation.step primitiveIotaLeft primitiveIotaRight :=
  ⟨rfl, decode_sound primitiveCode rfl⟩

/-- The open chain schema keeps both source programs and both recursive
eliminator calls in the decoded result. -/
theorem chain_decodes_and_steps :
    decode chainCode = some (chainIotaLeft, chainIotaRight) ∧
      IntrinsicMILHypothesis.rules.computation.step chainIotaLeft chainIotaRight :=
  ⟨rfl, decode_sound chainCode rfl⟩

def changedPrimitiveResult : Tower.Tm 8 :=
  .app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 1)

/-- A changed result cannot be attached to the same primitive receipt. -/
theorem changed_result_rejected :
    decode primitiveCode ≠ some (primitiveIotaLeft, changedPrimitiveResult) := by
  decide

def ground : Tower.Tm n := .head .legacyGround
def betaGround : Tower.Tm n := .app (.lam (.var 0)) ground

def mismatchedMetadata : Tower.Tm n :=
  eliminateApp ground ground ground (.const hypothesisName) ground ground ground
    (primitiveApp betaGround ground ground ground ground)

/-- Even convertible metadata must satisfy the original exact root pattern.
No finite receipt can authorize a root whose repeated fields differ. -/
theorem mismatched_metadata_has_no_code (target : Tower.Tm n) :
    ¬ ∃ code : Code n, decode code = some (mismatchedMetadata, target) := by
  rintro ⟨code, decoded⟩
  have step := decode_sound code decoded
  cases step with
  | inherited impossible => exact impossible.elim
  | declared supported =>
      obtain ⟨evidence⟩ := supported
      cases evidence

theorem convertible_metadata_still_requires_exact_root :
    Conv IntrinsicMILHypothesis.rules.headEq (betaGround : Tower.Tm n) ground
        IntrinsicMILHypothesis.rules.computation ∧
      ∀ target : Tower.Tm n,
        ¬ ∃ code : Code n, decode code = some (mismatchedMetadata, target) :=
  ⟨.rel _ _ (.betaPi _ _), mismatched_metadata_has_no_code⟩

end Examples

#print axioms decode_sound
#print axioms decode_complete
#print axioms decoder
#print axioms Examples.primitive_decodes_and_steps
#print axioms Examples.chain_decodes_and_steps
#print axioms Examples.changed_result_rejected
#print axioms Examples.mismatched_metadata_has_no_code
#print axioms Examples.convertible_metadata_still_requires_exact_root

end MILRootConversionCode
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
