import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationHostedJudgments
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilySource
import Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist

/-!
# Checked ingress into a declaration-hosted Prime world

The fixed structural Prime presentation and an authored declaration host have
different jobs.  The former checks its exact finite raw fragment; the latter
extends the native dependent calculus with formed declarations.  This module
connects them without identifying either one with the other.

Every checked formed-typing derivation in the fixed fragment realizes to a
term in any formed declaration host by monotonicity of intrinsic typing.  The
retained checked/native graph still carries the exact structural derivation,
while the hot artifact is the corresponding host-indexed judgment.

The converse is deliberately false.  A formed declaration constructs its
constant natively in the hosted calculus, but the fixed bare presentation has
no constant rule.  The strictness theorem below makes this maximal-native
boundary explicit: a later source-generated checker extension may cover raw
declaration ingress, but native declaration construction is not reduced to
replaying the bare checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace DeclarationHostedCheckedNativeWaist

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open DeclarationAwarePatternCodec
open DeclarationAwareFormedTyping
open DeclarationHostedJudgments

noncomputable section

/-! ## Conservative checked ingress into every authored host -/

/-- The exact fixed Prime semantics realizes in any formed authored world.
The host-indexed artifact retains context formation, formation of the expected
type, and subject typing in the extended rules package. -/
def nativeRealization (host : FormationHost) :
    NativeRealization FormedTypingQuery
      (fun query => PrimeRootMeaning (encodeFormedTypingQuery query)) where
  Artifact := fun query => HostedFormedTyping host query
  realize := fun query meaning =>
    IntrinsicFormedTyping.includeHost host (meaning.2 query rfl)

/-- One fixed checked presentation, interpreted in an arbitrary authored
Prime host.  The checker remains a raw-ingress capability; the artifact is an
intrinsic judgment of the hosted calculus. -/
def checkedNativeWaist (host : FormationHost) :
    CheckedNativeWaist formedTypingExtension.target where
  Meaning := PrimeRootMeaning
  semantics := formedTypingSemanticExtension.targetSemantics
  Goal := FormedTypingQuery
  surface := encodeFormedTypingQuery
  native := nativeRealization host

/-- Raw checking is exact for the retained host-indexed ingress, including the
identical authored proof tree. -/
theorem checkRaw_iff_nonempty_hosted
    (host : FormationHost) (query : FormedTypingQuery) (raw : RawProof) :
    checkRaw formedTypingExtension.target
        (encodeFormedTypingQuery query) raw = true ↔
      Nonempty ((checkedNativeWaist host).CheckedRawProgram query raw) :=
  (checkedNativeWaist host).checkRaw_iff_nonempty query raw

/-- Realization is exactly conservative inclusion of the independently
interpreted intrinsic judgment into the selected declaration host. -/
@[simp] theorem checkedProgram_artifact
    (host : FormationHost) {query : FormedTypingQuery}
    (program : (checkedNativeWaist host).CheckedProgram query) :
    program.artifact =
      IntrinsicFormedTyping.includeHost host
        (program.evidence.2 query rfl) :=
  rfl

/-! ## A real authored-host positive control -/

/-- The existing dependent-Pi example crosses the same checked boundary into
the authored native List/identity declaration world. -/
theorem simplePi_crosses_nativeFamilyHost :
    Nonempty
      ((checkedNativeWaist NativeIndexedFamilySource.nativeFormationHost)
        |>.CheckedRawProgram
          DeclarationAwareFormedTyping.Examples.simplePiQuery
          (DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw.derived
            DeclarationAwareFormedTyping.Examples.simplePiQuery)) := by
  apply
    (checkRaw_iff_nonempty_hosted
      NativeIndexedFamilySource.nativeFormationHost
      DeclarationAwareFormedTyping.Examples.simplePiQuery
      (DeclarationAwareFormedTyping.Examples.simplePiIntrinsic.raw.derived
        DeclarationAwareFormedTyping.Examples.simplePiQuery)).mp
  exact DeclarationAwareFormedTyping.Examples.simplePi_derived_raw_accepted

/-! ## Strict maximal-native boundary -/

/-- The fixed structural fragment has no constructor for a global declaration
constant.  This is an index theorem, not a syntactic search heuristic. -/
theorem no_intrinsic_bare_constant
    (name : DeclName) (type : Tower.Tm 0) (level : LevelExpr) :
    ¬ Nonempty
      (IntrinsicFormedTyping
        { arity := 0
          context := .nil
          levels := .nil
          subject := .const name
          type := type
          level := level }) := by
  rintro ⟨evidence⟩
  cases evidence.subjectTyping

/-- Consequently the fixed generic checker cannot derive a declaration
constant merely because some external host happens to declare it. -/
theorem no_fixed_checked_constant
    (name : DeclName) (type : Tower.Tm 0) (level : LevelExpr) :
    ¬ Nonempty
      (Derivation formedTypingExtension.target
        (encodeFormedTypingQuery
          { arity := 0
            context := .nil
            levels := .nil
            subject := .const name
            type := type
            level := level })) := by
  rintro ⟨derivation⟩
  let meaning :=
    formedTypingSemanticExtension.targetSemantics.interpret derivation
  exact no_intrinsic_bare_constant name type level
    ⟨meaning.2
      { arity := 0
        context := .nil
        levels := .nil
        subject := .const name
        type := type
        level := level }
      rfl⟩

/-- Every actually formed declaration supplies a strict native inhabitant:
its constant is typed in the hosted DTT, while the fixed bare checker image is
empty at the same surface judgment.  This is the precise reason declaration
ingress must be generated from authored source or handled by a stronger native
kernel, rather than being inferred from the fixed presentation. -/
theorem declared_constant_is_strictly_native
    (host : FormationHost) {name : DeclName} {type : Tower.Tm 0}
    (declared : host.signature.typeOf? name = some type) :
    ∃ level : LevelExpr,
      Nonempty
        (HostedFormedTyping host
          { arity := 0
            context := .nil
            levels := .nil
            subject := .const name
            type := type
            level := level }) ∧
      ¬ Nonempty
        (Derivation formedTypingExtension.target
          (encodeFormedTypingQuery
            { arity := 0
              context := .nil
              levels := .nil
              subject := .const name
              type := type
              level := level })) := by
  rcases declared_constant_has_hosted_typing host declared with
    ⟨level, hosted⟩
  exact ⟨level, hosted, no_fixed_checked_constant name type level⟩

#print axioms checkedNativeWaist
#print axioms checkRaw_iff_nonempty_hosted
#print axioms checkedProgram_artifact
#print axioms simplePi_crosses_nativeFamilyHost
#print axioms no_intrinsic_bare_constant
#print axioms no_fixed_checked_constant
#print axioms declared_constant_is_strictly_native

end

end DeclarationHostedCheckedNativeWaist
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
