import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPurseImage

/-!
# Structural admission of the existing serialized parser image

These predicates range over the existing raw runtime datatypes. They retain
actual accepted signature witnesses, singleton literal seals and ordered purse
heads, and quotation's scope reset. Parallel layout may be an arbitrary raw
binary tree: the original parser inserts trailing nils, while normalization
removes them. A later readback therefore compares normalized configurations
instead of asserting literal parser-image closure of normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Exactly one whole checked signature Pattern supplies one literal raw atom. -/
inductive SignatureAdmitted : RawCostSig → Prop where
  | accepted {source : Pattern} (signature : TypedSignature source)
      (checked : signature? source = some signature) :
      SignatureAdmitted [literalAuthorityKey source]

inductive StackAdmitted : RawCostStack → Prop where
  | empty : StackAdmitted []
  | cons {head : RawCostSig} {tail : RawCostStack}
      (signature : SignatureAdmitted head) (rest : StackAdmitted tail) :
      StackAdmitted (head :: tail)

mutual
  inductive NameAdmitted : Nat → RawCostName → Prop where
    | bvar {depth index : Nat} (bound : index < depth) : NameAdmitted depth (.bvar index)
    | quote {depth : Nat} {code : RawCostTerm} (body : CodeAdmitted 0 code) :
        NameAdmitted depth (.quote code)

  inductive CodeAdmitted : Nat → RawCostTerm → Prop where
    | zero {depth : Nat} : CodeAdmitted depth .nil
    | drop {depth : Nat} {name : RawCostName} (image : NameAdmitted depth name) :
        CodeAdmitted depth (.drop name)
    | signed {depth : Nat} {process : RawCostProc} {authority : RawCostSig}
        (image : ProcAdmitted depth process) (signature : SignatureAdmitted authority) :
        CodeAdmitted depth (.signed process authority)
    | par {depth : Nat} {left right : RawCostTerm}
        (first : CodeAdmitted depth left) (second : CodeAdmitted depth right) :
        CodeAdmitted depth (.par left right)

  inductive ProcAdmitted : Nat → RawCostProc → Prop where
    | zero {depth : Nat} : ProcAdmitted depth .nil
    | send {depth : Nat} {location : RawCostName} {payload : RawCostTerm}
        (channel : NameAdmitted depth location) (code : CodeAdmitted depth payload) :
        ProcAdmitted depth (.send location payload)
    | recv {depth : Nat} {location : RawCostName} {body : RawCostTerm}
        (channel : NameAdmitted depth location) (code : CodeAdmitted (depth + 1) body) :
        ProcAdmitted depth (.recv location body)
    | par {depth : Nat} {left right : RawCostProc}
        (first : ProcAdmitted depth left) (second : ProcAdmitted depth right) :
        ProcAdmitted depth (.par left right)
end

/-- Configuration layout retains a single explicit funding-location index. -/
inductive ConfigAdmitted (location : RawCostName) : RawCostTerm → Prop where
  | code {term : RawCostTerm} (image : CodeAdmitted 0 term) : ConfigAdmitted location term
  | purse {stack : RawCostStack} (image : StackAdmitted stack) : ConfigAdmitted location (.purse location stack)
  | par {left right : RawCostTerm} (first : ConfigAdmitted location left)
      (second : ConfigAdmitted location right) : ConfigAdmitted location (.par left right)

theorem SignatureAdmitted.normalize_identity {signature : RawCostSig}
    (image : SignatureAdmitted signature) : signature.normalize = signature := by
  cases image
  rfl

theorem SignatureAdmitted.length_eq_one {signature : RawCostSig}
    (image : SignatureAdmitted signature) : signature.length = 1 := by
  cases image
  rfl

theorem StackAdmitted.normalize_identity {stack : RawCostStack}
    (image : StackAdmitted stack) : stack.map RawCostSig.normalize = stack := by
  induction image with
  | empty => rfl
  | cons head tail ih => simp only [List.map_cons, head.normalize_identity, ih]

/-- Ordered stack readback uses the original actual signature checker. -/
theorem StackAdmitted.readback {stack : RawCostStack} (image : StackAdmitted stack) :
    ∃ source decoded, StackImage source decoded ∧ literalEncodeStack decoded = stack := by
  induction image with
  | empty => exact ⟨_, .empty, StackImage.empty, rfl⟩
  | cons signature rest ih =>
      obtain ⟨tailSource, tail, tailImage, tailSame⟩ := ih
      cases signature with
      | @accepted source checked accepted =>
          refine ⟨.apply "$cost:apparatus-constructor:token-stack-cons" [source, tailSource],
            .cons checked.val tail, .cons checked accepted tailImage, ?_⟩
          change encodeCostSig (checked.val.map literalAuthorityKey) :: literalEncodeStack tail = _
          rw [checked.property.1, literalEncodeSig_singleton, tailSame]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax SerializationAdmission

theorem StackImage.serialized {source : Pattern} {stack : CostStack LiteralAuthority}
    (image : StackImage source stack) : StackAdmitted (literalEncodeStack stack) := by
  induction image with
  | empty => exact .empty
  | cons signature accepted tail ih =>
      change StackAdmitted (encodeCostSig (signature.val.map literalAuthorityKey) :: literalEncodeStack _)
      rw [signature.property.1, literalEncodeSig_singleton]
      exact .cons (.accepted signature accepted) ih

mutual
  theorem NameImage.serialized {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority}
      (image : NameImage depth source name) : NameAdmitted depth (literalEncodeName name) := by
    cases image with
    | bvar bound => exact .bvar bound
    | baseZeroQuote => exact .quote .zero
    | quote code => exact .quote code.serialized

  theorem CodeImage.serialized {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeImage depth source term) : CodeAdmitted depth (literalEncodeTerm term) := by
    cases image with
    | zero => exact .zero
    | drop name => exact .drop name.serialized
    | signed signature accepted process =>
        change CodeAdmitted depth (.signed (literalEncodeProc _) (encodeCostSig (signature.val.map literalAuthorityKey)))
        rw [signature.property.1, literalEncodeSig_singleton]
        exact .signed process.serialized (.accepted signature accepted)
    | collection codes => exact codes.serialized

  theorem ProcImage.serialized {depth : Nat} {source : Pattern} {process : CostProc LiteralAuthority}
      (image : ProcImage depth source process) : ProcAdmitted depth (literalEncodeProc process) := by
    cases image with
    | zero => exact .zero
    | send name code => exact .send name.serialized code.serialized
    | recv name code => exact .recv name.serialized code.serialized
    | pair first second => exact .par first.serialized second.serialized

  theorem CodeListImage.serialized {depth : Nat} {sources : List Pattern} {term : CostTerm LiteralAuthority}
      (image : CodeListImage depth sources term) : CodeAdmitted depth (literalEncodeTerm term) := by
    cases image with
    | nil => exact .zero
    | cons head tail => exact .par head.serialized tail.serialized
end

mutual
  theorem ConfigImage.serialized {location : CostName LiteralAuthority} {source : Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigImage location source term) :
      ConfigAdmitted (literalEncodeName location) (literalEncodeTerm term) := by
    cases image with
    | zero => exact .code .zero
    | drop name => exact .code (.drop name.serialized)
    | signed signature accepted process => exact .code (CodeImage.serialized (.signed signature accepted process))
    | contact code stack => exact .par code.serialized (.purse stack.serialized)
    | collection codes => exact codes.serialized

  theorem ConfigListImage.serialized {location : CostName LiteralAuthority} {sources : List Pattern}
      {term : CostTerm LiteralAuthority} (image : ConfigListImage location sources term) :
      ConfigAdmitted (literalEncodeName location) (literalEncodeTerm term) := by
    cases image with
    | nil => exact .code .zero
    | cons head tail => exact .par head.serialized tail.serialized
end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
