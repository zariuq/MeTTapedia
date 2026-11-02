import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaKernel
import Mettapedia.OSLF.Syntax.CommonABTBindingSignature
import Mettapedia.OSLF.Syntax.ContextualRigidReflection

/-!
# Structural intrinsic encodings of scoped physical inference values

Physical location is a rigid outer constructor. The payload uses the common
ABT binding presentation, retaining each head, field depth and bound index.
The scope admission is exactly the existing zero-ambient-scope check.
Protected judgments and admitted requests satisfy it by their existing
source admission rules. This is a rigid data profile; contextual metavariable
assignments still range over the general calculus without specialization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValues

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open InferenceSchemaKernel (Space Value)

abbrev Head := Space ⊕ InferenceSchemaActivation.Head
abbrev base := CommonABT.Presentation.signature Head
abbrev Tree := Term base [] ()

def raw (value : Value) : SignatureIndexedABT.Term Head :=
  .node (.inl value.1) (.cons 0 (SignatureIndexedABT.mapHeads Sum.inr value.2) .nil)

def Scoped (value : Value) : Prop := SignatureIndexedABT.Term.supportedAt 0 value.2 = true

instance : DecidablePred Scoped := fun value =>
  inferInstanceAs (Decidable (SignatureIndexedABT.Term.supportedAt 0 value.2 = true))

abbrev Ready := {value : Value // Scoped value}

def checkScope? (value : Value) : Option Ready :=
  if supported : Scoped value then some ⟨value, supported⟩ else none

theorem checked_scope {value : Value} {ready : Ready} (accepted : checkScope? value = some ready) :
    ready.val = value ∧ Scoped value := by
  unfold checkScope? at accepted
  split at accepted
  · rename_i supported
    cases Option.some.inj accepted
    exact ⟨rfl, supported⟩
  · cases accepted

theorem raw_scope (value : Value) :
    SignatureIndexedABT.Term.supportedAt 0 (raw value) =
      SignatureIndexedABT.Term.supportedAt 0 value.2 := by
  simp only [raw, SignatureIndexedABT.Term.supportedAt,
    SignatureIndexedABT.Term.Fields.supportedAt, Nat.zero_add,
    SignatureIndexedABT.mapHeads_scope, Bool.and_true]

theorem raw_injective : Function.Injective raw := by
  intro first second same
  have heads := Sum.inl.inj (SignatureIndexedABT.Term.node.inj same).1
  have fields := SignatureIndexedABT.Fields.cons.inj (SignatureIndexedABT.Term.node.inj same).2
  have values := SignatureIndexedABT.mapHeads_injective Sum.inr Sum.inr_injective
    first.2 second.2 fields.2.1
  exact Prod.ext heads values

def encode (value : Ready) : Tree :=
  CommonABT.Presentation.read (raw value.val) 0 ((raw_scope value.val).trans value.property)

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have equal := CommonABT.Presentation.read_injective 0 (raw first.val) (raw second.val)
    ((raw_scope first.val).trans first.property) ((raw_scope second.val).trans second.property) same
  exact Subtype.ext (raw_injective equal)

def into {V : Type} (declaration : V → MetaArity base) (value : Ready) :
    Term (signature base declaration) [] () := Rigid.includeTerm declaration (encode value)

theorem into_injective {V : Type} (declaration : V → MetaArity base) :
    Function.Injective (into declaration) := by
  intro first second same
  exact encode_injective (Rigid.include_injective declaration _ _ same)

theorem instantiate_into {V W : Type} {source : V → MetaArity base} {target : W → MetaArity base}
    (assignment : Assignment source target) (value : Ready) :
    instantiate assignment (into source value) = into target value :=
  Rigid.instantiate_include assignment _

theorem into_support {V : Type} (declaration : V → MetaArity base) (value : Ready) :
    support (into declaration value) = [] := Rigid.support_include declaration _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedInferenceValues
