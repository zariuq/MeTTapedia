import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.DefinitionHistories
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.AnnotatedProgressBit

/-!
# Checked definitions over a computing two-point carrier

The base has actual negation steps, cumulative universes and formed primitive
declarations. The history names a carrier, a function carrier, an identity
function and a genuinely dependent reflexivity family. Its erasure and
conservativity are instances of the general history theorems.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace DefinitionHistories
namespace Controls

open Normalization
open Annotated Annotated.ProgressBit
open ConstantExpansion (constantNames)

theorem bit_primitiveSafety : PrimitiveSafety bitRules where
  declarations := by
    intro name type known
    by_cases hb : name = bitName
    · subst name
      have same : type = .head 0 := by simpa [bitRules, bitConstType] using known.symm
      subst type
      exact ⟨1, trivial, bit_head_typed.erase⟩
    by_cases ht : name = ttName
    · subst name
      have same : type = .const bitName := by
        simpa [bitRules, bitConstType, hb] using known.symm
      subst type
      exact ⟨0, trivial, (bit_typed .nil).erase⟩
    by_cases hf : name = ffName
    · subst name
      have same : type = .const bitName := by
        simpa [bitRules, bitConstType, hb, ht] using known.symm
      subst type
      exact ⟨0, trivial, (bit_typed .nil).erase⟩
    by_cases hn : name = notName
    · subst name
      have same : type = .pi (.const bitName) (.const bitName) := by
        simpa [bitRules, bitConstType, hb, ht, hf] using known.symm
      subst type
      exact ⟨0, trivial, not_type_typed.erase⟩
    by_cases hp : name = propName
    · subst name
      have same : type = .head 1 := by
        simpa [bitRules, bitConstType, hb, ht, hf, hn] using known.symm
      subst type
      exact ⟨2, trivial, prop_head_typed.erase⟩
    by_cases hh : name = holdsName
    · subst name
      have same : type = .pi (.const propName) (.head 0) := by
        simpa [bitRules, bitConstType, hb, ht, hf, hn, hp] using known.symm
      subst type
      exact ⟨1, trivial, holds_type_typed.erase⟩
    simp [bitRules, bitConstType, hb, ht, hf, hn, hp, hh] at known
  freshComputation := by
    intro name fresh body n left right step
    have notDistinct : notName ≠ name := by
      intro same
      subst name
      have declared := bitChurch.erase_declared declared_not
      change bitRules.constantType notName = some _ at declared
      rw [fresh] at declared
      cases declared
    have ttDistinct : ttName ≠ name := by
      intro same
      subst name
      have declared := bitChurch.erase_declared declared_tt
      change bitRules.constantType ttName = some _ at declared
      rw [fresh] at declared
      cases declared
    have ffDistinct : ffName ≠ name := by
      intro same
      subst name
      have declared := bitChurch.erase_declared declared_ff
      change bitRules.constantType ffName = some _ at declared
      rw [fresh] at declared
      cases declared
    cases step with
    | tt =>
      change bitRules.computation.step
        (unfoldTm name body (.app (.const notName) (.const ttName)))
        (unfoldTm name body (.const ffName))
      rw [unfoldTm_app, unfoldTm_const_of_ne notDistinct,
        unfoldTm_const_of_ne ttDistinct, unfoldTm_const_of_ne ffDistinct]
      exact .tt
    | ff =>
      change bitRules.computation.step
        (unfoldTm name body (.app (.const notName) (.const ffName)))
        (unfoldTm name body (.const ttName))
      rw [unfoldTm_app, unfoldTm_const_of_ne notDistinct,
        unfoldTm_const_of_ne ffDistinct, unfoldTm_const_of_ne ttDistinct]
      exact .ff

def carrier : Definition Nat := ⟨`CarrierAlias, .head 0, .const bitName⟩
def arrow : Definition Nat :=
  ⟨`FunctionAlias, .head 0, .pi (.const carrier.name) (.const carrier.name)⟩
def identity : Definition Nat := ⟨`SharedIdentity, .const arrow.name, .lam (.var 0)⟩
def diagonal : Definition Nat :=
  ⟨`DependentReflexivity,
    .pi (.const carrier.name) (.id (.const carrier.name) (.var 0) (.var 0)),
    .lam (.refl (.var 0))⟩

theorem universe_zero_formed (rules : Rules Nat)
    (headRule : rules.headTyping 0 1) (universeOne : rules.isUniverse 1) :
    IsType rules .nil (.head 0) := ⟨1, universeOne, .headType headRule⟩

theorem carrier_checked : Checked bitRules [carrier] :=
  .cons carrier .nil (by decide)
    (universe_zero_formed bitRules rfl trivial) (bit_typed .nil).erase

theorem carrier_typed {n : Nat} (context : Ctx Nat n) :
    Typed (stage bitRules [carrier]) context (.const carrier.name) (.head 0) := by
  exact withTheorem_typed_in (by decide)
    (universe_zero_formed bitRules rfl trivial) context

theorem arrow_body_typed :
    Typed (stage bitRules [carrier]) .nil arrow.body (.head 0) :=
  .piForm (carrier_typed .nil) trivial
    (carrier_typed (.snoc .nil (.const carrier.name))) trivial rfl

theorem arrow_checked : Checked bitRules [arrow, carrier] :=
  .cons arrow carrier_checked (by decide)
    (universe_zero_formed _ rfl trivial) arrow_body_typed

theorem arrow_typed {n : Nat} (context : Ctx Nat n) :
    Typed (stage bitRules [arrow, carrier]) context (.const arrow.name) (.head 0) := by
  exact withTheorem_typed_in (by decide)
    (universe_zero_formed (stage bitRules [carrier]) rfl trivial) context

theorem identity_body_typed :
    Typed (stage bitRules [arrow, carrier]) .nil identity.body identity.type := by
  have included := withTheorem_sub (R := stage bitRules [carrier])
    (name := arrow.name) (T := arrow.type) (body := arrow.body) (by decide)
  have arrowFormed := Derivable.mono included arrow_body_typed
  have bareIdentity : Typed (stage bitRules [arrow, carrier]) .nil
      (.lam (.var 0)) arrow.body := by
    exact .lamIntro arrowFormed trivial (.var 0)
  have arrowEqualsBody := withTheorem_equal_body (R := stage bitRules [carrier])
    (name := arrow.name) (by decide) (universe_zero_formed _ rfl trivial) arrow_body_typed
  exact .conv bareIdentity (.symm arrowEqualsBody) trivial

theorem identity_checked : Checked bitRules [identity, arrow, carrier] :=
  .cons identity arrow_checked (by decide) ⟨0, trivial, arrow_typed .nil⟩ identity_body_typed

theorem diagonal_type_formed :
    IsType (stage bitRules [identity, arrow, carrier]) .nil diagonal.type := by
  have carrierIncluded := (withTheorem_sub (R := stage bitRules [carrier])
    (name := arrow.name) (T := arrow.type) (body := arrow.body) (by decide)).trans
      (withTheorem_sub (R := stage bitRules [arrow, carrier])
        (name := identity.name) (T := identity.type) (body := identity.body) (by decide))
  refine ⟨0, trivial, .piForm (Derivable.mono carrierIncluded (carrier_typed .nil))
    trivial ?_ trivial rfl⟩
  exact .idForm (Derivable.mono carrierIncluded
    (carrier_typed (.snoc .nil (.const carrier.name)))) trivial (.var 0) (.var 0)

theorem diagonal_body_typed :
    Typed (stage bitRules [identity, arrow, carrier]) .nil diagonal.body diagonal.type := by
  obtain ⟨level, universeWitness, formed⟩ := diagonal_type_formed
  exact .lamIntro formed universeWitness (.reflIntro (.var 0))

theorem history_checked : Checked bitRules [diagonal, identity, arrow, carrier] :=
  .cons diagonal identity_checked (by decide) diagonal_type_formed diagonal_body_typed

theorem history_safety : PrimitiveSafety (stage bitRules [diagonal, identity, arrow, carrier]) :=
  history_checked.safety bit_primitiveSafety

/-- A named function carrier erases through the earlier carrier alias. -/
theorem arrow_reading :
    erase [diagonal, identity, arrow, carrier] (.const arrow.name : Tm Nat 0) =
      .pi (.const bitName) (.const bitName) := by decide

/-- The dependent consumer retains its actual argument in both endpoints. -/
theorem diagonal_reading :
    erase [diagonal, identity, arrow, carrier] (.const diagonal.name : Tm Nat 0) =
      .lam (.refl (.var 0)) := by decide

/-- The consumer has a varying identity family after complete erasure. -/
theorem diagonal_erased_typed :
    Typed bitRules .nil (.lam (.refl (.var 0)))
      (.pi (.const bitName) (.id (.const bitName) (.var 0) (.var 0))) := by
  have named := withTheorem_typed (R := stage bitRules [identity, arrow, carrier])
    (name := diagonal.name) (body := diagonal.body) (by decide) diagonal_type_formed
  have erased := history_checked.erase_derivation bit_primitiveSafety named
  have expandedType : erase [diagonal, identity, arrow, carrier] diagonal.type =
      .pi (.const bitName) (.id (.const bitName) (.var 0) (.var 0)) := by decide
  simpa only [erase_typing, eraseContext_nil, diagonal_reading, expandedType] using erased

/-- A body cannot justify its own declaration by using that declaration. -/
theorem self_reference_refused {Head : Type} {base : Rules Head}
    {prior : List (Definition Head)} {name : DeclName} {type : Tm Head 0}
    (fresh : (stage base prior).constantType name = none) :
    ¬ Typed (stage base prior) .nil (.const name) type := by
  intro typed
  exact typed.avoids fresh (List.mem_singleton.mpr rfl)

/-- Publishing the same name again violates the checked admission boundary. -/
theorem replacement_refused :
    (stage bitRules [carrier]).constantType carrier.name ≠ none := by decide

/-- Moving the carrier definition after its dependent arrow is not licensed. -/
theorem forward_dependency_refused : ¬ Typed bitRules .nil arrow.body arrow.type := by
  intro typed
  have fresh : bitRules.constantType carrier.name = none := by decide
  apply typed.avoids fresh
  simp [arrow, carrier, constantNames]

end Controls
end DefinitionHistories
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
