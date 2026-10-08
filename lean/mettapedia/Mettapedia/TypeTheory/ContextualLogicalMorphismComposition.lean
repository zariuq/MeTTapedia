import Mettapedia.TypeTheory.ContextualStrictMorphismComposition
import Mettapedia.TypeTheory.ContextualLogicalMorphism

/-!
# Identity and composition of local logical preservation

The intermediate binder family and every supplied section are transported
along the first actual comprehension equality. The second local constructor
law then acts on those values. No compatibility with whole syntax is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLogicalMorphism

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualComprehensionMorphism ContextualTelescopeMorphism
open ContextualStrictMorphismComposition
open ContextualProductComparison (selfExtend)

universe u v w w'
variable {C D E : CwfWithTerminal.{u, v, w, w'}}

theorem PiPreservation.identity (products : PiOperations C.toCwf) :
    PiPreservation (StrictCwfMorphism.identity C) products products := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains body body' bodies
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    cases eq_of_heq bodies
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains f f' a a' functions arguments
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    cases eq_of_heq functions
    cases eq_of_heq arguments
    rfl

theorem SigmaPreservation.identity (sums : SigmaOperations C.toCwf) :
    SigmaPreservation (StrictCwfMorphism.identity C) sums sums := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains a a' b b' firsts seconds
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    cases eq_of_heq firsts
    cases eq_of_heq seconds
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    cases eq_of_heq pairs
    rfl
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    change Γ = Γ' at contexts
    cases contexts
    cases eq_of_heq domains
    cases eq_of_heq codomains
    cases eq_of_heq pairs
    rfl

theorem PiPreservation.comp {first : StrictCwfMorphism C D} {second : StrictCwfMorphism D E}
    {source : PiOperations C.toCwf} {middle : PiOperations D.toCwf} {target : PiOperations E.toCwf}
    (earlier : PiPreservation first source middle) (later : PiPreservation second middle target) :
    PiPreservation (compose first second) source target := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    let midB := imageType first (context_ext first Γ A) B
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    exact (mappedType_heq second rfl firstForm).trans (later.formation contexts domains finalTypes)
  · intro Γ Γ' contexts A A' domains B B' codomains body body' bodies
    let midB := imageType first (context_ext first Γ A) B
    let midBody := imageTerm first (context_ext first Γ A) body
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have midBodies := imageTerm_heq first (context_ext first Γ A) body
    have finalBodies := (mappedTerm_heq second (context_ext first Γ A) midTypes midBodies).symm.trans bodies
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    have firstLam := earlier.abstraction rfl HEq.rfl midTypes body midBody midBodies
    exact (mappedTerm_heq second rfl firstForm firstLam).trans
      (later.abstraction contexts domains finalTypes midBody body' finalBodies)
  · intro Γ Γ' contexts A A' domains B B' codomains f f' a a' functions arguments
    let midA := first.toFamilyMorphism.mapType A
    let midB := imageType first (context_ext first Γ A) B
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    let midF := imageAtType first rfl (middle.pi midA midB) firstForm f
    have midFunctions := imageAtType_heq first rfl (middle.pi midA midB) firstForm f
    have finalFunctions := (mappedTerm_heq second rfl firstForm midFunctions).symm.trans functions
    let midArgument := first.toFamilyMorphism.mapTerm a
    have resultTypes := substituted_type_heq first rfl (context_ext first Γ A) midTypes
      (self_extension_heq first rfl HEq.rfl a midArgument HEq.rfl)
    have firstApp := earlier.application rfl HEq.rfl midTypes f midF a midArgument midFunctions HEq.rfl
    exact (mappedTerm_heq second rfl resultTypes firstApp).trans
      (later.application contexts domains finalTypes midF f' midArgument a' finalFunctions arguments)

theorem SigmaPreservation.comp {first : StrictCwfMorphism C D} {second : StrictCwfMorphism D E}
    {source : SigmaOperations C.toCwf} {middle : SigmaOperations D.toCwf}
    {target : SigmaOperations E.toCwf}
    (earlier : SigmaPreservation first source middle) (later : SigmaPreservation second middle target) :
    SigmaPreservation (compose first second) source target := by
  constructor
  · intro Γ Γ' contexts A A' domains B B' codomains
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    exact (mappedType_heq second rfl firstForm).trans (later.formation contexts domains finalTypes)
  · intro Γ Γ' contexts A A' domains B B' codomains a a' b b' firsts seconds
    let midA := first.toFamilyMorphism.mapType A
    let midB := imageType first (context_ext first Γ A) B
    let midFirst := first.toFamilyMorphism.mapTerm a
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have bodyTypes := substituted_type_heq first rfl (context_ext first Γ A) midTypes
      (self_extension_heq first rfl HEq.rfl a midFirst HEq.rfl)
    let midSecond := imageAtType first rfl (D.toCwf.tySub midB (selfExtend D.toCwf midFirst)) bodyTypes b
    have midSeconds := imageAtType_heq first rfl
      (D.toCwf.tySub midB (selfExtend D.toCwf midFirst)) bodyTypes b
    have finalSeconds := (mappedTerm_heq second rfl bodyTypes midSeconds).symm.trans seconds
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    have firstPair := earlier.pairing rfl HEq.rfl midTypes a midFirst b midSecond HEq.rfl midSeconds
    exact (mappedTerm_heq second rfl firstForm firstPair).trans
      (later.pairing contexts domains finalTypes midFirst a' midSecond b' firsts finalSeconds)
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    let midA := first.toFamilyMorphism.mapType A
    let midB := imageType first (context_ext first Γ A) B
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    let midPair := imageAtType first rfl (middle.sigma midA midB) firstForm p
    have midPairs := imageAtType_heq first rfl (middle.sigma midA midB) firstForm p
    have finalPairs := (mappedTerm_heq second rfl firstForm midPairs).symm.trans pairs
    have firstProjection := earlier.firstProjection rfl HEq.rfl midTypes p midPair midPairs
    exact (mappedTerm_heq second rfl HEq.rfl firstProjection).trans
      (later.firstProjection contexts domains finalTypes midPair p' finalPairs)
  · intro Γ Γ' contexts A A' domains B B' codomains p p' pairs
    let midA := first.toFamilyMorphism.mapType A
    let midB := imageType first (context_ext first Γ A) B
    have midTypes := imageType_heq first (context_ext first Γ A) B
    have finalTypes := (mappedType_heq second (context_ext first Γ A) midTypes).symm.trans codomains
    have firstForm := earlier.formation rfl HEq.rfl midTypes
    let midPair := imageAtType first rfl (middle.sigma midA midB) firstForm p
    have midPairs := imageAtType_heq first rfl (middle.sigma midA midB) firstForm p
    have finalPairs := (mappedTerm_heq second rfl firstForm midPairs).symm.trans pairs
    have firstProjection := earlier.firstProjection rfl HEq.rfl midTypes p midPair midPairs
    have resultTypes := substituted_type_heq first rfl (context_ext first Γ A) midTypes
      (self_extension_heq first rfl HEq.rfl _ _ firstProjection)
    have secondProjection := earlier.secondProjection rfl HEq.rfl midTypes p midPair midPairs
    exact (mappedTerm_heq second rfl resultTypes secondProjection).trans
      (later.secondProjection contexts domains finalTypes midPair p' finalPairs)

theorem LogicalPreservation.identity (products : PiOperations C.toCwf) (sums : SigmaOperations C.toCwf) :
    LogicalPreservation (StrictCwfMorphism.identity C) products products sums sums :=
  ⟨PiPreservation.identity products, SigmaPreservation.identity sums⟩

theorem LogicalPreservation.comp {first : StrictCwfMorphism C D} {second : StrictCwfMorphism D E}
    {sourcePi : PiOperations C.toCwf} {middlePi : PiOperations D.toCwf} {targetPi : PiOperations E.toCwf}
    {sourceSigma : SigmaOperations C.toCwf} {middleSigma : SigmaOperations D.toCwf}
    {targetSigma : SigmaOperations E.toCwf}
    (earlier : LogicalPreservation first sourcePi middlePi sourceSigma middleSigma)
    (later : LogicalPreservation second middlePi targetPi middleSigma targetSigma) :
    LogicalPreservation (compose first second) sourcePi targetPi sourceSigma targetSigma :=
  ⟨earlier.products.comp later.products, earlier.sums.comp later.sums⟩

end Mettapedia.TypeTheory.ContextualLogicalMorphism
