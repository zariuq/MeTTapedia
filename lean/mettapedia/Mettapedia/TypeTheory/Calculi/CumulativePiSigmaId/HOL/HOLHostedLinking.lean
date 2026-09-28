import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLReadingCompileModulo
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeGenericProofCompilerModuloLaws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HostedProfile
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism

/-!
# Hosted profiles linked by the generic compiler

A signed profile is a hosted profile over the tower together with the declared
logical signature of the generic compiler that its reading agrees with
(`SignedProfile`). For such a profile:

* **licensing** (`SignedProfile.linked_typedO`): a proof from published facts
  whose conversion articles stay inside the read terms is linked by
  `compileModulo` to the term the reading compiles, and that term is a closed
  term of the package at the decoding of the signature's representation of its
  theorem; under a reading that interprets every constant, every successful
  run of `compileModulo` is typed (`SignedProfile.linked_typedO_of_total`);
* **residual list** (`SignedProfile.assumed_link`): when some assumptions are
  published and the others are linked to assumption constants, the assumption
  constants of the link are exactly the used assumptions that are not
  published;
* **declaration compatibility** (`SignedProfile.linked_extend`): along a
  signature embedding into a second profile whose package receives a morphism
  from the first, the image of a proof links to the same term, and its typing
  transfers to the second package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FormationSensitiveHOLInterface (LogicalSignature represent)
open Mettapedia.Logic
open ConstantExpansion (constantNames)

universe u v w

/-- A hosted profile over the tower, with the declared logical signature of the
generic compiler that its reading agrees with. -/
structure SignedProfile (Base : Type u) (Const : HOL.Ty Base → Type v) extends
    HostedProfile Tower.Head Base Const where
  signature : LogicalSignature Base Const
  agrees : reading.Agrees signature

namespace SignedProfile

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The realizations of the published assumptions, the others absent. -/
def realizations (P : SignedProfile Base Const) {assumptions : List (HOL.Formula Const [])}
    (published : ∀ i : Fin assumptions.length, Option (P.Published (assumptions.get i))) :
    Fin assumptions.length → Option (Tower.Tm 0) :=
  fun i => (published i).map fun p => p.realization

/-- **Licensing.** A proof from published facts whose articles stay inside the
read terms is linked by the generic compiler to the term the reading compiles,
a closed term of the package at the decoding of the signature's representation
of its theorem. -/
theorem linked_typedO (P : SignedProfile Base Const) {assumptions : List (HOL.Formula Const [])}
    {statement : HOL.Formula Const []}
    {proof : HOL.ProofSyntaxModulo P.equations assumptions statement}
    (articles : P.reading.ArticlesRead P.equations proof)
    (published : ∀ i : Fin assumptions.length, P.Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : P.reading.compile proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    HOLNativeGenericProofCompiler.Modulo.compileModulo P.signature proof (fun i => Fin.elim0 i)
        (fun i => (published i).realization) = some term ∧
      ∃ code, represent P.signature statement = some code ∧
        Typed P.reading.rules .nil term (P.reading.holdsOf code) := by
  obtain ⟨code, hcode, typed⟩ := P.toHostedProfile.linked_typedO articles published compiled
  exact ⟨P.agrees.compile_compileModulo proof _ _ compiled, code,
    P.agrees.term_represent hcode, typed⟩

/-- **Licensing under a total reading.** Every successful link of the generic
compiler against published facts is typed. -/
theorem linked_typedO_of_total (P : SignedProfile Base Const) (total : P.reading.Total)
    {assumptions : List (HOL.Formula Const [])} {statement : HOL.Formula Const []}
    (proof : HOL.ProofSyntaxModulo P.equations assumptions statement)
    (published : ∀ i : Fin assumptions.length, P.Published (assumptions.get i)) {term : Tower.Tm 0}
    (linked : HOLNativeGenericProofCompiler.Modulo.compileModulo P.signature proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    ∃ code, represent P.signature statement = some code ∧
      Typed P.reading.rules .nil term (P.reading.holdsOf code) := by
  rw [P.agrees.compileModulo_eq total] at linked
  exact (P.linked_typedO (HOLReading.ArticlesRead.of_total total proof) published linked).2

/-- **Residual assumptions.** Link the published assumptions to their
realizations and the others to distinct assumption constants that are fresh
for the signature and the realizations: the assumption constants of the link
are exactly the used assumptions that are not published. -/
theorem assumed_link (P : SignedProfile Base Const) {assumptions : List (HOL.Formula Const [])}
    {statement : HOL.Formula Const []}
    (proof : HOL.ProofSyntaxModulo P.equations assumptions statement)
    (published : ∀ i : Fin assumptions.length, Option (P.Published (assumptions.get i)))
    (names : Fin assumptions.length → DeclName) (distinct : Function.Injective names)
    (freshSymbols : ∀ i, ¬ P.signature.SymbolName (names i))
    (freshRealizations : ∀ i j (p : P.Published (assumptions.get j)), published j = some p →
      names i ∉ constantNames p.realization)
    {out : Tower.Tm 0}
    (linked : HOLNativeGenericProofCompiler.Modulo.compileModulo P.signature proof (fun i => Fin.elim0 i)
      (HOLNativeGenericProofCompiler.Modulo.linkHyps (P.realizations published) names) = some out)
    (i : Fin assumptions.length) :
    names i ∈ constantNames out ↔ proof.usesHyp i = true ∧ published i = none := by
  have iff := HOLNativeGenericProofCompiler.Modulo.assumed_link P.signature proof (fun i => Fin.elim0 i) (P.realizations published)
    names distinct freshSymbols (fun _ j => Fin.elim0 j)
    (fun i j r hr => by
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hr
      exact freshRealizations i j p hp)
    linked i
  rw [iff]
  unfold realizations
  cases published i <;> simp

/-- **Declaration compatibility.** Along a signature embedding into a second
profile that lists the image of every equation, and whose package receives a
morphism from the first, the image of a proof from published facts links to the
same term, which is typed in the second package. -/
theorem linked_extend (P : SignedProfile Base Const) {Const' : HOL.Ty Base → Type w}
    (P' : SignedProfile Base Const')
    (embedding : HOLNativeGenericProofCompiler.Modulo.SignatureEmbedding P.signature P'.signature)
    (listed : ∀ equation ∈ P.equations, HOL.DefiningEquation.mapConst embedding.map equation ∈
      P'.equations)
    (morphism : P.reading.rules.Morphism P'.reading.rules (fun head => head))
    {assumptions : List (HOL.Formula Const [])} {statement : HOL.Formula Const []}
    {proof : HOL.ProofSyntaxModulo P.equations assumptions statement}
    (articles : P.reading.ArticlesRead P.equations proof)
    (published : ∀ i : Fin assumptions.length, P.Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : P.reading.compile proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    HOLNativeGenericProofCompiler.Modulo.compileModulo P'.signature (proof.mapConst embedding.map listed) (fun i => Fin.elim0 i)
        (fun i => (published (i.cast (by simp))).realization) = some term ∧
      ∃ code, represent P.signature statement = some code ∧
        Typed P'.reading.rules .nil term (P.reading.holdsOf code) := by
  obtain ⟨linked, code, represented, typed⟩ := P.linked_typedO articles published compiled
  refine ⟨?_, code, represented, typed.of_morphism morphism⟩
  rw [HOLNativeGenericProofCompiler.Modulo.compileModulo_mapConst embedding listed proof]
  exact linked

end SignedProfile

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
