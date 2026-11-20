import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Normalizer
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableConversion

/-!
# One unfolding of each executable comparison, for any reducer

The executable comparison (`ExecutableConversion.compare`, `compareNeutral`, `types`, `neutral`) takes its
reducer as a parameter. Each lemma here unfolds one call at one shape of what the reducer returned: at a
dependent function type the comparison η-expands the given terms, at a pair type it projects them, at a
universe it compares types, at an identity type it compares reflexivity proofs or else spines, and at every
other weak-head form (a neutral type, the type constant of an inductive type, a head that is not a universe)
it compares the reducer's forms of the two terms as spines. The lemmas hold for every reducer; the tower's
versions are the instances at its normalizer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion

/-- A successful computation. -/
abbrev Ok {α : Type} (computation : Option α) : Prop := ∃ result, computation = some result

/-- A term that is not a type former: no head, no dependent function or pair type, no identity type. -/
def NotFormer {Head : Type} {n : Nat} (t : Tm Head n) : Prop :=
  (∀ h, t ≠ .head h) ∧ (∀ A B, t ≠ .pi A B) ∧ (∀ A B, t ≠ .sigma A B) ∧ (∀ A a b, t ≠ .id A a b)

theorem NotFormer.of_neutral {Head : Type} {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) : NotFormer t :=
  neutral.not_former

theorem NotFormer.const {Head : Type} {n : Nat} (name : DeclName) : NotFormer (.const name : Tm Head n) :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩

section Unfold

variable {Head : Type} (R : Rules Head) [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] (red : Reducer R)
variable {n : Nat} {fuel : Nat} {Γ : Ctx Head n}

theorem compare_pi {left right type domain : Tm Head n} {body : Tm Head (n + 1)}
    {path : Reduces R type (.pi domain body)}
    (normal : red (fuel + 1) type = some ⟨.pi domain body, path⟩)
    (inner : Ok (compare R red fuel (.snoc Γ domain)
      (.app (Presentation.rename wk left) (.var 0)) (.app (Presentation.rename wk right) (.var 0)) body)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed]
  exact ⟨_, rfl⟩

theorem compare_sigma {left right type domain : Tm Head n} {body : Tm Head (n + 1)}
    {path : Reduces R type (.sigma domain body)}
    (normal : red (fuel + 1) type = some ⟨.sigma domain body, path⟩)
    (first : Ok (compare R red fuel Γ (.fst left) (.fst right) domain))
    (second : Ok (compare R red fuel Γ (.snd left) (.snd right) (inst0 (.fst left) body))) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := first
  obtain ⟨certificate', computed'⟩ := second
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem compare_universe {left right type : Tm Head n} {value : Head}
    {path : Reduces R type (.head value)} (universeHead : R.isUniverse value)
    (normal : red (fuel + 1) type = some ⟨.head value, path⟩)
    (inner : Ok (types R red fuel Γ left right)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, dif_pos universeHead, computed]
  exact ⟨_, rfl⟩

theorem compare_refl {left right type carrier first second subject subject' : Tm Head n}
    {path : Reduces R type (.id carrier first second)}
    {leftPath : Reduces R left (.refl subject)} {rightPath : Reduces R right (.refl subject')}
    (normal : red (fuel + 1) type = some ⟨.id carrier first second, path⟩)
    (leftNormal : red (fuel + 1) left = some ⟨.refl subject, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.refl subject', rightPath⟩)
    (inner : Ok (compare R red fuel Γ subject subject' carrier)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, leftNormal, rightNormal, computed]
  exact ⟨_, rfl⟩

theorem compareNeutral_of {left right type : Tm Head n} {first : Result R left} {second : Result R right}
    (leftNormal : red (fuel + 1) left = some first) (rightNormal : red (fuel + 1) right = some second)
    (inner : Ok (neutral R red fuel Γ first.val second.val)) :
    Ok (compareNeutral R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compareNeutral, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed]
  exact ⟨_, rfl⟩

/-- At a weak-head form of the type that is not a type former, terms are compared as spines. -/
theorem compare_other {left right type : Tm Head n} {normalType : Result R type}
    (shape : NotFormer normalType.val) (normal : red (fuel + 1) type = some normalType)
    (inner : Ok (compareNeutral R red fuel Γ left right type)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨code, path⟩ := normalType
  obtain ⟨notHead, notPi, notSigma, notId⟩ := shape
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases code <;> first
    | exact absurd rfl (notHead _)
    | exact absurd rfl (notPi _ _)
    | exact absurd rfl (notSigma _ _)
    | exact absurd rfl (notId _ _ _)
    | exact ⟨_, computed⟩

/-- At a head that is not a universe, terms are compared as spines. -/
theorem compare_ground {left right type : Tm Head n} {value : Head}
    {path : Reduces R type (.head value)} (notUniverse : ¬ R.isUniverse value)
    (normal : red (fuel + 1) type = some ⟨.head value, path⟩)
    (inner : Ok (compareNeutral R red fuel Γ left right type)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, dif_neg notUniverse]
  exact ⟨_, computed⟩

/-- At an identity type, terms whose forms are not reflexivity proofs are compared as spines. -/
theorem compare_id_spine {left right type carrier first second : Tm Head n}
    {path : Reduces R type (.id carrier first second)}
    {leftResult : Result R left} {rightResult : Result R right}
    (normal : red (fuel + 1) type = some ⟨.id carrier first second, path⟩)
    (leftNormal : red (fuel + 1) left = some leftResult) (rightNormal : red (fuel + 1) right = some rightResult)
    (notRefl : ∀ x, leftResult.val ≠ .refl x)
    (inner : Ok (compareNeutral R red fuel Γ left right type)) :
    Ok (compare R red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨leftCode, leftPath⟩ := leftResult
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, leftNormal, rightNormal]
  cases leftCode <;> first
    | exact absurd rfl (notRefl _)
    | exact ⟨_, computed⟩

theorem neutral_var (i : Fin n) :
    ∃ certificate, neutral R red (fuel + 1) Γ (.var i) (.var i) =
      some ⟨Ctx.lookup Γ i, certificate⟩ := by
  simp only [ExecutableConversion.neutral]
  exact ⟨_, rfl⟩

theorem neutral_const {name : DeclName} {type : Tm Head 0} (known : R.constantType name = some type) :
    ∃ certificate, neutral R red (fuel + 1) Γ (.const name) (.const name) =
      some ⟨liftClosed type, certificate⟩ := by
  refine ⟨⟨.const known⟩, ?_⟩
  simp only [ExecutableConversion.neutral, dite_true]
  split
  · rename_i type' known'
    rw [known] at known'
    cases known'
    rfl
  · rename_i known'
    rw [known] at known'
    cases known'

theorem neutral_app {function function' argument argument' functionType domain : Tm Head n}
    {body : Tm Head (n + 1)}
    {functionCertificate : Certificate R (.neutral Γ function function' functionType)}
    {path : Reduces R functionType (.pi domain body)}
    (functions : neutral R red fuel Γ function function' = some ⟨functionType, functionCertificate⟩)
    (normal : red (fuel + 1) functionType = some ⟨.pi domain body, path⟩)
    (arguments : Ok (compare R red fuel Γ argument argument' domain)) :
    ∃ certificate, neutral R red (fuel + 1) Γ (.app function argument) (.app function' argument') =
      some ⟨inst0 argument body, certificate⟩ := by
  obtain ⟨certificate, computed⟩ := arguments
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, functions, Option.bind_some, normal, computed]
  exact ⟨_, rfl⟩

theorem neutral_fst {pair pair' pairType domain : Tm Head n} {body : Tm Head (n + 1)}
    {pairCertificate : Certificate R (.neutral Γ pair pair' pairType)}
    {path : Reduces R pairType (.sigma domain body)}
    (pairs : neutral R red fuel Γ pair pair' = some ⟨pairType, pairCertificate⟩)
    (normal : red (fuel + 1) pairType = some ⟨.sigma domain body, path⟩) :
    ∃ certificate, neutral R red (fuel + 1) Γ (.fst pair) (.fst pair') = some ⟨domain, certificate⟩ := by
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, pairs, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem neutral_snd {pair pair' pairType domain : Tm Head n} {body : Tm Head (n + 1)}
    {pairCertificate : Certificate R (.neutral Γ pair pair' pairType)}
    {path : Reduces R pairType (.sigma domain body)}
    (pairs : neutral R red fuel Γ pair pair' = some ⟨pairType, pairCertificate⟩)
    (normal : red (fuel + 1) pairType = some ⟨.sigma domain body, path⟩) :
    ∃ certificate, neutral R red (fuel + 1) Γ (.snd pair) (.snd pair') =
      some ⟨inst0 (.fst pair) body, certificate⟩ := by
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, pairs, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem types_heads {left right : Tm Head n} {a b : Head}
    {leftPath : Reduces R left (.head a)} {rightPath : Reduces R right (.head b)}
    (leftNormal : red (fuel + 1) left = some ⟨.head a, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.head b, rightPath⟩) (same : HeadSame R a b) :
    Ok (types R red (fuel + 1) Γ left right) := by
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have same' : a = b ∨ R.headEq a b := same
  rw [dif_pos same']
  exact ⟨_, rfl⟩

theorem types_pi {left right domain domain' : Tm Head n} {body body' : Tm Head (n + 1)}
    {leftPath : Reduces R left (.pi domain body)} {rightPath : Reduces R right (.pi domain' body')}
    (leftNormal : red (fuel + 1) left = some ⟨.pi domain body, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.pi domain' body', rightPath⟩)
    (domains : Ok (types R red fuel Γ domain domain'))
    (bodies : Ok (types R red fuel (.snoc Γ domain) body body')) :
    Ok (types R red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := domains
  obtain ⟨certificate', computed'⟩ := bodies
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem types_sigma {left right domain domain' : Tm Head n} {body body' : Tm Head (n + 1)}
    {leftPath : Reduces R left (.sigma domain body)} {rightPath : Reduces R right (.sigma domain' body')}
    (leftNormal : red (fuel + 1) left = some ⟨.sigma domain body, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.sigma domain' body', rightPath⟩)
    (domains : Ok (types R red fuel Γ domain domain'))
    (bodies : Ok (types R red fuel (.snoc Γ domain) body body')) :
    Ok (types R red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := domains
  obtain ⟨certificate', computed'⟩ := bodies
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem types_id {left right carrier carrier' a a' b b' : Tm Head n}
    {leftPath : Reduces R left (.id carrier a b)} {rightPath : Reduces R right (.id carrier' a' b')}
    (leftNormal : red (fuel + 1) left = some ⟨.id carrier a b, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.id carrier' a' b', rightPath⟩)
    (carriers : Ok (types R red fuel Γ carrier carrier'))
    (lefts : Ok (compare R red fuel Γ a a' carrier))
    (rights : Ok (compare R red fuel Γ b b' carrier)) :
    Ok (types R red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := carriers
  obtain ⟨certificate', computed'⟩ := lefts
  obtain ⟨certificate'', computed''⟩ := rights
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed', computed'']
  exact ⟨_, rfl⟩

/-- Types whose first form is not a type former are compared as spines. -/
theorem types_other {left right : Tm Head n} {first : Result R left} {second : Result R right}
    (leftNormal : red (fuel + 1) left = some first) (rightNormal : red (fuel + 1) right = some second)
    (shape : NotFormer first.val) (inner : Ok (neutral R red fuel Γ first.val second.val)) :
    Ok (types R red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨code, path⟩ := first
  obtain ⟨notHead, notPi, notSigma, notId⟩ := shape
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases code <;> first
    | exact absurd rfl (notHead _)
    | exact absurd rfl (notPi _ _)
    | exact absurd rfl (notSigma _ _)
    | exact absurd rfl (notId _ _ _)
    | (simp only [computed]; exact ⟨_, rfl⟩)

end Unfold

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms compare_pi
#print axioms compare_sigma
#print axioms compare_universe
#print axioms compare_refl
#print axioms compareNeutral_of
#print axioms compare_other
#print axioms compare_ground
#print axioms compare_id_spine
#print axioms neutral_var
#print axioms neutral_const
#print axioms neutral_app
#print axioms neutral_fst
#print axioms neutral_snd
#print axioms types_heads
#print axioms types_pi
#print axioms types_sigma
#print axioms types_id
#print axioms types_other
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
