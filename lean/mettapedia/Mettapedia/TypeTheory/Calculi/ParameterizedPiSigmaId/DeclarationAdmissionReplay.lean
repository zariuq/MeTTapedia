import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationConversionCode
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Prefix-checked dependent declaration libraries

Each declaration is checked against its preceding source inventory, before
the name or its computation is installed. Formation and optional body evidence
use the existing structural typing checker. Conversion reuses the structural
decoder with inherited roots and actual selected delta lookup.

Admission preserves opaque assumptions as opaque entries; it does not prove
their inhabitation or consistency. Successful replay earns typing of every
selected body in the final library, for use by subject preservation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace DeclarationAdmissionReplay

open Declaration StructuralConversionCode FormationSensitive

variable {Head : Type}

abbrev ConversionCode (Head : Type) (BaseCode : Nat → Type) :=
  StructuralConversionCode.Code Head (DeclarationConversionCode.RootCode BaseCode (fun _ => Empty))

structure Certificate (Head : Type) (BaseCode : Nat → Type) where
  levelHead : Head
  formation : StructuralTypingReplay.Code Head (ConversionCode Head BaseCode) 0
  value? : Option (StructuralTypingReplay.Code Head (ConversionCode Head BaseCode) 0)

/-- This relation states source-prefix formation and body typing using the
existing judgments. It introduces no new term or typing constructors. -/
inductive Admitted (base : Rules Head) :
    List (DeclName × Entry Head) → List (DeclName × Entry Head) → Prop where
  | nil (prior : List (DeclName × Entry Head)) : Admitted base prior []
  | cons {prior : List (DeclName × Entry Head)} {item : DeclName × Entry Head}
      {later : List (DeclName × Entry Head)} {levelHead : Head}
      (fresh : (extendRules base (Signature.ofList prior)).constantType item.1 = none)
      (isUniverse : base.isUniverse levelHead)
      (formed : Typing (extendRules base (Signature.ofList prior)) .nil item.2.type (.head levelHead))
      (body : ∀ value, item.2.value? = some value →
        Typing (extendRules base (Signature.ofList prior)) .nil value item.2.type)
      (rest : Admitted base (prior ++ [item]) later) : Admitted base prior (item :: later)

section Computation

variable (base : Rules Head) [DecidableEq Head]
variable [DecidableRel base.headEq]
variable (decoder : RootDecoder base.computation)

def conversionCheck (entries : List (DeclName × Entry Head)) {n : Nat}
    (code : ConversionCode Head decoder.Code n) (left right : Tm Head n) : Bool :=
  code.check base.headEq (DeclarationConversionCode.ofList base decoder entries).decode left right

theorem conversionCheck_sound (entries : List (DeclName × Entry Head)) {n : Nat}
    {code : ConversionCode Head decoder.Code n} {left right : Tm Head n}
    (accepted : conversionCheck base decoder entries code left right = true) :
    Conv base.headEq left right (extendRules base (Signature.ofList entries)).computation :=
  StructuralConversionCode.Code.check_sound (DeclarationConversionCode.ofList base decoder entries) accepted

theorem conversion_iff_checked (entries : List (DeclName × Entry Head)) {n : Nat}
    {left right : Tm Head n} :
    Conv base.headEq left right (extendRules base (Signature.ofList entries)).computation ↔
      ∃ code, conversionCheck base decoder entries code left right = true :=
  StructuralConversionCode.Code.conversion_iff_checked (DeclarationConversionCode.ofList base decoder entries)

section Typing

variable [∀ h u, Decidable (base.headTyping h u)] [∀ h, Decidable (base.isUniverse h)]
variable [∀ u v w, Decidable (base.join u v w)] [∀ u v, Decidable (base.cumulative u v)]

local instance (entries : List (DeclName × Entry Head)) :
    ∀ h u, Decidable ((extendRules base (Signature.ofList entries)).headTyping h u) :=
  fun h u => inferInstanceAs (Decidable (base.headTyping h u))
local instance (entries : List (DeclName × Entry Head)) :
    ∀ h, Decidable ((extendRules base (Signature.ofList entries)).isUniverse h) :=
  fun h => inferInstanceAs (Decidable (base.isUniverse h))
local instance (entries : List (DeclName × Entry Head)) :
    ∀ u v w, Decidable ((extendRules base (Signature.ofList entries)).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (base.join u v w))
local instance (entries : List (DeclName × Entry Head)) :
    ∀ u v, Decidable ((extendRules base (Signature.ofList entries)).cumulative u v) :=
  fun u v => inferInstanceAs (Decidable (base.cumulative u v))

def checkTerm (entries : List (DeclName × Entry Head))
    (term type : Tm Head 0)
    (code : StructuralTypingReplay.Code Head (ConversionCode Head decoder.Code) 0) : Bool :=
  StructuralTypingReplay.check (extendRules base (Signature.ofList entries))
    (conversionCheck base decoder entries) .nil term type code

theorem checkTerm_sound (entries : List (DeclName × Entry Head))
    {term type : Tm Head 0}
    {code : StructuralTypingReplay.Code Head (ConversionCode Head decoder.Code) 0}
    (accepted : checkTerm base decoder entries term type code = true) :
    Typing (extendRules base (Signature.ofList entries)) .nil term type :=
  StructuralTypingReplay.check_sound _ _ (conversionCheck_sound base decoder entries) code accepted

theorem checkTerm_complete (entries : List (DeclName × Entry Head))
    {term type : Tm Head 0}
    (typed : Typing (extendRules base (Signature.ofList entries)) .nil term type) :
    ∃ code, checkTerm base decoder entries term type code = true :=
  StructuralTypingReplay.check_complete _ _
    (fun conversion => (conversion_iff_checked base decoder entries).mp conversion) typed

def checkValue (prior : List (DeclName × Entry Head)) (entry : Entry Head)
    (certificate : Certificate Head decoder.Code) : Bool :=
  match entry.value?, certificate.value? with
  | none, none => true
  | some value, some code => checkTerm base decoder prior value entry.type code
  | _, _ => false

def check : List (DeclName × Entry Head) → List (DeclName × Entry Head) →
    List (Certificate Head decoder.Code) → Bool
  | _, [], [] => true
  | prior, item :: later, certificate :: certificates =>
      ((extendRules base (Signature.ofList prior)).constantType item.1).isNone &&
      decide (base.isUniverse certificate.levelHead) &&
      checkTerm base decoder prior item.2.type (.head certificate.levelHead) certificate.formation &&
      checkValue base decoder prior item.2 certificate &&
      check (prior ++ [item]) later certificates
  | _, _, _ => false

/-- An aligned checked prefix can be reused while admitting the suffix at
its actual extended inventory. The equation concerns the existing checker,
not a second admission algorithm. -/
theorem check_append (prior first second : List (DeclName × Entry Head))
    (firstCertificates secondCertificates : List (Certificate Head decoder.Code))
    (aligned : first.length = firstCertificates.length) :
    check base decoder prior (first ++ second) (firstCertificates ++ secondCertificates) =
      (check base decoder prior first firstCertificates &&
        check base decoder (prior ++ first) second secondCertificates) := by
  induction first generalizing prior firstCertificates with
  | nil =>
      cases firstCertificates with
      | nil => simp [check]
      | cons certificate certificates => simp at aligned
  | cons item later ih =>
      cases firstCertificates with
      | nil => simp at aligned
      | cons certificate certificates =>
          have lengths : later.length = certificates.length := by simpa using aligned
          simp only [List.cons_append, check]
          rw [ih _ _ lengths]
          simp only [List.append_assoc, List.singleton_append, Bool.and_assoc]

theorem check_sound {prior entries : List (DeclName × Entry Head)}
    {certificates : List (Certificate Head decoder.Code)}
    (accepted : check base decoder prior entries certificates = true) :
    Admitted base prior entries := by
  induction entries generalizing prior certificates with
  | nil => exact .nil prior
  | cons item later ih =>
      cases certificates with
      | nil => simp [check] at accepted
      | cons certificate certificates =>
          simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨⟨⟨fresh, levelHead⟩, formed⟩, body⟩, rest⟩ := accepted
          refine .cons (Option.isNone_iff_eq_none.mp fresh) levelHead
            (checkTerm_sound base decoder prior formed) ?_ (ih rest)
          intro value selected
          cases evidence : certificate.value? with
          | none => simp [checkValue, selected, evidence] at body
          | some code =>
              exact checkTerm_sound base decoder prior (by
                simpa [checkValue, selected, evidence] using body)

theorem check_complete {prior entries : List (DeclName × Entry Head)}
    (admitted : Admitted base prior entries) :
    ∃ certificates, check base decoder prior entries certificates = true := by
  induction admitted with
  | nil prior => exact ⟨[], rfl⟩
  | @cons prior item later levelHead fresh isUniverse formed body rest ih =>
      obtain ⟨formation, formationChecked⟩ := checkTerm_complete base decoder prior formed
      obtain ⟨certificates, restChecked⟩ := ih
      cases selected : item.2.value? with
      | none =>
          refine ⟨⟨levelHead, formation, none⟩ :: certificates, ?_⟩
          simp [check, fresh, isUniverse, formationChecked, checkValue, selected, restChecked]
      | some value =>
          obtain ⟨code, bodyChecked⟩ := checkTerm_complete base decoder prior (body value selected)
          refine ⟨⟨levelHead, formation, some code⟩ :: certificates, ?_⟩
          simp [check, fresh, isUniverse, formationChecked, checkValue, selected, bodyChecked, restChecked]

theorem admitted_iff_checked {prior entries : List (DeclName × Entry Head)} :
    Admitted base prior entries ↔
      ∃ certificates, check base decoder prior entries certificates = true :=
  ⟨check_complete base decoder, fun ⟨_, accepted⟩ => check_sound base decoder accepted⟩

end Typing
end Computation

variable (base : Rules Head)

/-- Later declarations do not retroactively justify an earlier entry.
Every admitted formation/body can nevertheless be reused in the final
signature through its proved prefix inclusion. -/
theorem Admitted.member_typed {prior entries : List (DeclName × Entry Head)}
    (admitted : Admitted base prior entries) {item : DeclName × Entry Head}
    (member : item ∈ entries) :
    base.constantType item.1 = none ∧
      ∃ levelHead, base.isUniverse levelHead ∧
        Typing (extendRules base (Signature.ofList (prior ++ entries))) .nil item.2.type (.head levelHead) ∧
        ∀ value, item.2.value? = some value →
          Typing (extendRules base (Signature.ofList (prior ++ entries))) .nil value item.2.type := by
  induction admitted with
  | nil => cases member
  | @cons prior first later levelHead fresh isUniverse formed body rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst item
        have baseFresh : base.constantType first.1 = none := by
          cases selected : base.constantType first.1 with
          | none => rfl
          | some type => simp [extendRules, combinedType, selected] at fresh
        exact ⟨baseFresh, levelHead, isUniverse,
          formed.monoSignature (Signature.ofList_extends_append prior (first :: later)),
          fun value selected => (body value selected).monoSignature
            (Signature.ofList_extends_append prior (first :: later))⟩
      · simpa only [List.append_assoc, List.singleton_append] using ih member

theorem Admitted.selected_bodies_typed {entries : List (DeclName × Entry Head)}
    (admitted : Admitted base [] entries) (name : DeclName) (value : Tm Head 0)
    (selected : (Signature.ofList entries).valueOf? name = some value) :
    ∃ type, (extendRules base (Signature.ofList entries)).constantType name = some type ∧
      Typing (extendRules base (Signature.ofList entries)) .nil value type := by
  cases lookup : (Signature.ofList entries).entries name with
  | none => simp [Signature.valueOf?, lookup] at selected
  | some entry =>
      have valueLookup : entry.value? = some value := by
        simpa [Signature.valueOf?, lookup] using selected
      obtain ⟨fresh, levelHead, isUniverse, formed, typed⟩ :=
        admitted.member_typed base (Signature.entries_ofList_mem entries lookup)
      refine ⟨entry.type, combinedType_of_signature base _ fresh ?_, ?_⟩
      · simp [Signature.typeOf?, lookup]
      · simpa only [List.nil_append] using typed value valueLookup

#print axioms conversionCheck_sound
#print axioms conversion_iff_checked
#print axioms check_append
#print axioms check_sound
#print axioms check_complete
#print axioms admitted_iff_checked
#print axioms Admitted.member_typed
#print axioms Admitted.selected_bodies_typed

end DeclarationAdmissionReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
