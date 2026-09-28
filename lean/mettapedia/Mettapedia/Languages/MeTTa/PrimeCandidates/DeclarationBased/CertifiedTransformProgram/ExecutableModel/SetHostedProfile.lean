import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SetReading
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLHostedLinking

/-!
# The set profile as a hosted profile

The set profile read in the object package (`setReading`) is a hosted profile
(`setHostedProfile`):

* the laws of the reading are `setReading_laws`;
* the universe of motives is the universe of level one;
* the identity eliminator is `id:eliminate` at carriers of the lowest universe
  (`setIdentity`);
* the defining equations of addition and of the iterated power set are realized
  by root steps of the executable package (`setReading_realizes`);
* the admitted inductive sort is `num`, with `zero` and `suc`, read as the
  declared numbers with their recursor `num-rec` (`numInductive`);
* no source assumption is tracked.

With the signature of the generic compiler it is a signed profile
(`setSignedProfile`).

The facts the fixed-profile linking publishes are facts of the generic carrier,
realized by the same terms: reflexivity by `λx. refl x`, substitution by the
identity eliminator at the code motive, and induction on the numbers by the
recursor at the code motive (`realization_reflexivity`,
`realization_substitution`, `realization_induction`); the induction principle of
`numInductive` is the profile's `num-ind` (`numInductive_formula`).

**The set profile with `Falsum` defined** (`definedHostedProfile`,
`definedSignedProfile`) reads `Falsum` by its name in the package that publishes
the definition, with the same motives, identity eliminator and numbers, and the
equations `SetProfile.definedEquations`. The definition is one of its published
facts, realized by reflexivity through the δ-step (`falsumDefinition_published`).
The set profile embeds in it (`definedEmbedding`, `sourceEquations_listed`), and
its package receives the object package (`objectRules_defined`), so every proof
the set profile links from its published facts links to the same term in the
profile with the definition, typed in the package with the definition
(`linked_defined`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open Package (jName numRecName)
open SetProfile (SetBase SetConst numTy)

namespace CodeModel

/-- The universe of level one holds the motives of eliminators into proofs. -/
theorem setMotives : setReading.MotiveUniverse where
  exists_universe := ⟨.sort (.succ Tower.zero), .sort _, .sort Tower.zero, fun _ => Nat.zero_le _,
    _, .sorts _ _, fun _ => Nat.le_of_eq (Nat.max_self _)⟩

/-- `id:eliminate` is the identity eliminator of the object package. -/
def setIdentity : setReading.IdentityEliminator where
  name := jName
  typed := fun hA hx hM hd hy he => j_typedO hA hx hM hd hy he

/-- The constructors of `num`: `zero` and `suc`, with their names in the package. -/
def numCtors : List (HOL.InductiveCtor SetConst SetBase.num × DeclName) :=
  [(⟨[], .zero⟩, zeroN), (⟨[none], .suc⟩, sucN)]

/-- The numbers, an admitted inductive sort of the set profile. -/
def numInductive : HOLReading.AdmittedInductive SetBase SetConst where
  sort := .num
  ctors := numCtors
  typeName := numN
  recName := numRecName

theorem numInductive_nativeCtors : numInductive.nativeCtors setReading = ctors := rfl

theorem numInductive_laws : numInductive.Laws setReading where
  sort := rfl
  ctor := by
    intro c mem
    change c ∈ numCtors at mem
    rcases List.mem_cons.mp mem with rfl | mem
    · rfl
    · rcases List.mem_cons.mp mem with rfl | mem
      · rfl
      · exact absurd mem List.not_mem_nil
  recursor := numRecConst_typedO

/-- The induction principle of `numInductive` is the profile's `num-ind`. -/
theorem numInductive_formula : numInductive.inductionFormula = SetProfile.inductionAxiom := rfl

/-- **The set profile is a hosted profile.** Every field is a fact about the
object package; none is assumed. -/
def setHostedProfile : HostedProfile Tower.Head SetBase SetConst where
  reading := setReading
  laws := setReading_laws
  motives := setMotives
  identity := setIdentity
  equations := SetProfile.sourceEquations
  realizes := setReading_realizes
  inductives := [numInductive]
  inductiveLaws := by
    intro I mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact numInductive_laws
  assumptions := []

/-- The set profile with the signature of the generic compiler. -/
noncomputable def setSignedProfile : SignedProfile SetBase SetConst where
  toHostedProfile := setHostedProfile
  signature := SetProfile.signature
  agrees := by
    refine ⟨rfl, fun _ => rfl, fun _ => rfl, fun c t found => ?_⟩
    cases c <;> simp only [setHostedProfile, setReading, setConstant, reduceCtorEq,
      Option.some.injEq] at found <;> subst found <;> rfl

theorem numInductive_mem : numInductive ∈ setHostedProfile.inductives := List.mem_singleton_self _

/-! ## The fixed-profile facts, as facts of the generic carrier -/

theorem realization_reflexivity (τ : HOL.Ty SetBase) :
    (HostedProfile.Published.reflexivity (P := setHostedProfile) τ).realization =
      IdentityEquality.Realizations.reflRealization := rfl

theorem realization_substitution (τ : HOL.Ty SetBase) :
    (HostedProfile.Published.substitution (P := setHostedProfile) τ).realization =
      IdentityEquality.Carriers.substRealizationAt τ := by
  change setReading.substRealization jName τ = _
  unfold HOLReading.substRealization IdentityEquality.Carriers.substRealizationAt
  rw [setReading_carrierAt]
  rfl

theorem realization_induction :
    (HostedProfile.Published.induction numInductive_mem).realization =
      IdentityEquality.Realizations.inductionRealization := rfl

/-- The substitution formula of the generic carrier is the fixed profile's. -/
theorem substitutionFormula_eq (τ : HOL.Ty SetBase) :
    (HOL.substitutionFormula τ : HOL.Formula SetConst []) = IdentityEquality.Carriers.substitution τ :=
  rfl

/-- The reflexivity formula of the generic carrier is the fixed profile's. -/
theorem reflexivityFormula_eq (τ : HOL.Ty SetBase) :
    (HOL.reflexivityFormula τ : HOL.Formula SetConst []) =
      FormationSensitiveHOLIdentityEquality.reflexivity τ :=
  rfl

/-! ## The set profile with `Falsum` defined -/

/-- The universe of level one holds the motives in the package with the
definition too. -/
theorem definedMotives : definedReading.MotiveUniverse := ⟨setMotives.exists_universe⟩

/-- `id:eliminate` is the identity eliminator of the package with the
definition. -/
def definedIdentity : definedReading.IdentityEliminator where
  name := jName
  typed := by
    intro n Γ A x M d y e hA hx hM hd hy he
    have mor : SubstMor definedReading.rules jTelescope Γ
        (consSub e (consSub y (consSub d (consSub M (consSub x (consSub A
          fun i => Fin.elim0 i)))))) := by
      intro i
      refine Fin.cases he (fun i => ?_) i
      refine Fin.cases hy (fun i => ?_) i
      refine Fin.cases hd (fun i => ?_) i
      refine Fin.cases hM (fun i => ?_) i
      refine Fin.cases hx (fun i => ?_) i
      refine Fin.cases hA (fun i => ?_) i
      exact i.elim0
    exact (typed_defined jSpine_typedO).substitute mor

theorem numInductive_defined : numInductive.Laws definedReading where
  sort := rfl
  ctor := by
    intro c mem
    change c ∈ numCtors at mem
    rcases List.mem_cons.mp mem with rfl | mem
    · rfl
    · rcases List.mem_cons.mp mem with rfl | mem
      · rfl
      · exact absurd mem List.not_mem_nil
  recursor := typed_defined numRecConst_typedO

/-- **The set profile with `Falsum` defined is a hosted profile.** -/
def definedHostedProfile : HostedProfile Tower.Head SetBase SetConst where
  reading := definedReading
  laws := definedReading_laws
  motives := definedMotives
  identity := definedIdentity
  equations := SetProfile.definedEquations
  realizes := definedReading_realizes
  inductives := [numInductive]
  inductiveLaws := by
    intro I mem
    simp only [List.mem_singleton] at mem
    subst mem
    exact numInductive_defined
  assumptions := []

/-- The reading with the definition reads the symbols of the chart with the rule
of `Falsum`, `Falsum` by its name. -/
theorem definedReading_agrees : definedReading.Agrees SetProfile.definedSignature where
  implication := rfl
  universal _ := rfl
  equality _ := rfl
  constant c t found := by
    cases c <;> simp only [definedReading, definedConstant, setConstant, reduceCtorEq,
      Option.some.injEq] at found <;> subst found <;> rfl

/-- The set profile with `Falsum` defined, with the signature of the generic
compiler that carries the rule of `Falsum`. -/
noncomputable def definedSignedProfile : SignedProfile SetBase SetConst where
  toHostedProfile := definedHostedProfile
  signature := SetProfile.definedSignature
  agrees := definedReading_agrees

/-- **The definition of `Falsum` is a published fact** of the profile with the
definition, realized by reflexivity at `Falsum` through its δ-step. -/
theorem falsumDefinition_published :
    ∃ code, definedReading.term SetProfile.falsumEquation.closedFormula = some code ∧
      Typed definedRules .nil
        (HostedProfile.Published.definingEquation (P := definedHostedProfile)
          SetProfile.falsumEquation_mem).realization
        (programCodes.holdsOf code) := by
  obtain ⟨code, read, typed⟩ :=
    (HostedProfile.Published.definingEquation (P := definedHostedProfile)
      SetProfile.falsumEquation_mem).typed
  exact ⟨code, read, definedReading_rules ▸ typed⟩

/-- The symbols of the set profile, in the chart with the rule of `Falsum`. -/
def definedEmbedding :
    HOLNativeGenericProofCompiler.Modulo.SignatureEmbedding SetProfile.signature
      SetProfile.definedSignature where
  map := fun c => c
  constant _ := rfl
  implication := rfl
  universal _ := rfl
  equality _ := rfl

/-- The equations of `add` and `pow` are equations of the profile with the
definition. -/
theorem sourceEquations_listed : ∀ equation ∈ SetProfile.sourceEquations,
    HOL.DefiningEquation.mapConst (fun c => c) equation ∈ SetProfile.definedEquations := by
  intro equation listed
  simp only [SetProfile.sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))
  · exact .tail _ (.tail _ (.tail _ (.head _)))
  · exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- **The definition of `Falsum` is compatible with the set profile's proofs.** A
proof from facts the set profile publishes, whose conversion articles stay inside
the read terms, links in the profile with the definition to the term the set
profile links, and that term is typed in the package with the definition at the
decoding of the code of its theorem. -/
theorem linked_defined {assumptions : List (HOL.Formula SetConst [])}
    {statement : HOL.Formula SetConst []}
    {proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement}
    (articles : setReading.ArticlesRead SetProfile.sourceEquations proof)
    (published : ∀ i : Fin assumptions.length, setSignedProfile.Published (assumptions.get i))
    {term : Tower.Tm 0}
    (compiled : setReading.compile proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.definedSignature
        (proof.mapConst (fun c => c) sourceEquations_listed) (fun i => Fin.elim0 i)
        (fun i => (published (i.cast (by simp))).realization) = some term ∧
      ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature statement =
          some code ∧ Typed definedRules .nil term (programCodes.holdsOf code) := by
  obtain ⟨linked, code, represented, typed⟩ := SignedProfile.linked_extend setSignedProfile
    definedSignedProfile definedEmbedding sourceEquations_listed
    (definedReading_rules ▸ objectRules_defined) articles published compiled
  exact ⟨linked, code, represented, definedReading_rules ▸ typed⟩

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
