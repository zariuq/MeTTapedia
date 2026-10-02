import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchFundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationForms

/-!
# The weak-head forms of the object package's annotated types

* **The conditions** of `CTypeEq.formsMatch_sub` at the object package: a type whose erasure
  is neutral takes no head step, since the erasure is a weak-head normal form under the
  package's root shape (`objectHeadReduction_neutralNormal`); the numbers are the only
  inductive type, read with the tag of numbers (`objectRigid_inductiveNumbers`).
* **The rigid types `set` and `prop` are adequate** (`constAdequateAt_set`,
  `constAdequateAt_prop`).
* **Equal types in weak-head form match within adequate constants**
  (`objectChurch_formsMatch_within`): for every equation derivable within a set of adequate
  constants, over a context formed within them. In particular a neutral type is equal there to
  no type former and not to the numbers (`objectChurch_neutral_not_former_within`,
  `objectChurch_neutral_not_num_within`).
* **The adequacy of all constants** (`objectChurch_constAdequate_of`) follows from that of
  `Power`, `pow`, `num-rec`, `transportCert`, `composeCert`, `returnIter`, `sucStep`, the
  decoder, implication and the equations `eq@A`; the other constants are adequate.
* **With every constant adequate**: the facts about the weak-head forms
  (`objectChurch_formFacts`), the injectivity and no-confusion of the type formers
  (`objectChurch_formerFacts`), coherence of annotations
  (`objectChurch_coherence_of_constAdequate`) and preservation of root steps
  (`objectChurch_rootPreserving_of_constAdequate`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName)
open Mettapedia.Logic

namespace CodeModel

/-! ## The conditions -/

/-- **Neutral types take no head step**: the erasure of a type whose erasure is neutral is a
weak-head normal form under the object package's root shape. -/
theorem objectHeadReduction_neutralNormal : objectHeadReduction.NeutralNormal objectRoles :=
  fun neutral u => CWhStepR.not_of_whnf (Neutral.whnf objectShape neutral) u

/-- **The numbers are the only inductive type**, read with the tag of numbers. -/
theorem objectRigid_inductiveNumbers :
    objectRigid.InductiveNumbers objectRoles objectChurchReading := by
  intro T ctors role
  obtain ⟨rfl, -⟩ := objectRoles_inductive role
  refine ⟨rfl, ?_⟩
  rw [objectChurchReading_num]
  exact Ideal.mem_principal_tag.2 rfl

/-! ## The rigid types -/

/-- **`set` is adequate**: the sets are an adequate type of `U₀`. -/
theorem constAdequateAt_set : ConstAdequateAt objectChurchReading objectHeadReduction setN :=
  ConstAdequateAt.of_adequate (objectChurch_declared (c := setN) (T := Package.U0) (by decide) rfl)
    ((adequateType_typeAt (.base .set) (.nil : CCtx Tower.Head 0)).adequate ConvRules.objectLevels
      objectChurch_soundnessFacts (.sort Tower.zero))

/-- **`prop` is adequate**: the proposition codes are an adequate type of `U₀`. -/
theorem constAdequateAt_prop : ConstAdequateAt objectChurchReading objectHeadReduction propN :=
  ConstAdequateAt.of_adequate (objectChurch_declared (c := propN) (T := Package.U0) (by decide) rfl)
    ((adequateType_typeAt .prop (.nil : CCtx Tower.Head 0)).adequate ConvRules.objectLevels
      objectChurch_soundnessFacts (.sort Tower.zero))

/-! ## Within adequate constants -/

section Within

variable {allowed : DeclName → Bool}
  (consts : ∀ {c : DeclName}, allowed c = true →
    ConstAdequateAt objectChurchReading objectHeadReduction c)
  {n : Nat} {Γ : CCtx Tower.Head n}

include consts in
/-- **Equal types in weak-head form match, within adequate constants**: for every equation of
types derivable within a set of adequate constants, over a context formed within them. -/
theorem objectChurch_formsMatch_within {A B : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A B)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ)
    (formA : IsTypeForm objectRoles A.erase) (formB : IsTypeForm objectRoles B.erase) :
    CFormsMatch objectChurch objectRoles Γ A B :=
  CTypeEq.formsMatch_sub ConvRules.objectLevels objectChurchReading_valid objectRigid_groundHeads
    objectRules_groundHeadEq objectHeadReduction_decoderStuck ChurchRules.restrict_sub
    (fun declared => consts (ChurchRules.restrict_declared declared).1)
    objectHeadReduction_neutralNormal objectRigid_inductiveNumbers equal formed formA formB

include consts in
/-- **A neutral type is equal to no type former, within adequate constants.** -/
theorem objectChurch_neutral_not_former_within {A B : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A B)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ) (neutral : Neutral objectRoles A.erase)
    (former : CFormer B) : False :=
  equal.neutral_not_former_sub ConvRules.objectLevels objectChurchReading_valid
    objectRigid_groundHeads objectRules_groundHeadEq objectHeadReduction_decoderStuck
    ChurchRules.restrict_sub (fun declared => consts (ChurchRules.restrict_declared declared).1)
    objectHeadReduction_neutralNormal formed neutral former

include consts in
/-- **A neutral type is not equal to the numbers, within adequate constants.** -/
theorem objectChurch_neutral_not_num_within {A : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A cnum)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ) (neutral : Neutral objectRoles A.erase) :
    False :=
  equal.neutral_not_inductive_sub ConvRules.objectLevels objectChurchReading_valid
    objectRigid_groundHeads objectRules_groundHeadEq objectHeadReduction_decoderStuck
    ChurchRules.restrict_sub (fun declared => consts (ChurchRules.restrict_declared declared).1)
    objectHeadReduction_neutralNormal objectRigid_inductiveNumbers formed neutral objectRoles_num

end Within

/-! ## The adequacy of all constants -/

/-- **Every constant of the object package is adequate** once `Power`, `pow`, `num-rec`,
`transportCert`, `composeCert`, `returnIter`, `sucStep`, the decoder, implication and the
equations `eq@A` are: the numbers, their constructors, addition, the sets, the proposition
codes, the identity eliminator, `eqAt`, `sucMove`, `keepCert`, the iterator and the
quantifiers `all@A` are adequate. -/
theorem objectChurch_constAdequate_of
    (power : ConstAdequateAt objectChurchReading objectHeadReduction powerN)
    (pow : ConstAdequateAt objectChurchReading objectHeadReduction powN)
    (numRec : ConstAdequateAt objectChurchReading objectHeadReduction numRecName)
    (transport : ConstAdequateAt objectChurchReading objectHeadReduction transportName)
    (compose : ConstAdequateAt objectChurchReading objectHeadReduction composeName)
    (returnIter : ConstAdequateAt objectChurchReading objectHeadReduction returnIterName)
    (sucStep : ConstAdequateAt objectChurchReading objectHeadReduction sucStepName)
    (holds : ConstAdequateAt objectChurchReading objectHeadReduction holdsN)
    (imp : ConstAdequateAt objectChurchReading objectHeadReduction impN)
    (eq : ∀ type, ConstAdequateAt objectChurchReading objectHeadReduction (SetProfile.eqName type)) :
    ConstAdequate objectChurchReading objectHeadReduction := by
  intro c D u declared
  have fixed : ∀ p ∈ fixedDecls, ConstAdequateAt objectChurchReading objectHeadReduction p.1 := by
    simp only [fixedDecls, declarations, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨constAdequateAt_prop, holds, imp, constAdequateAt_num, constAdequateAt_set,
      constAdequateAt_zero, constAdequateAt_suc, constAdequateAt_add, power, pow, numRec,
      constAdequateAt_j, constAdequateAt_eqAt, constAdequateAt_sucMove', constAdequateAt_keep,
      transport, compose, constAdequateAt_iter, returnIter, sucStep⟩
  have key : ConstAdequateAt objectChurchReading objectHeadReduction c := by
    rw [objectChurch_constantType] at declared
    unfold elabDeclarations at declared
    cases hT : objectRules.constantType c with
    | none => rw [hT] at declared; cases declared
    | some T =>
        rcases objectRules_constantType_cases hT with ⟨type, rfl, -⟩ | ⟨type, rfl, -⟩ | hmem
        · exact constAdequateAt_all type
        · exact eq type
        · exact fixed _ hmem
  exact key declared

/-! ## With every constant adequate -/

section Adequate

variable (consts : ConstAdequate objectChurchReading objectHeadReduction)

include consts in
/-- **The facts about the weak-head forms of the object package's annotated types**, with
every constant adequate. -/
theorem objectChurch_formFacts : CFormFacts objectChurch objectRoles :=
  CFormFacts.of_constAdequate ConvRules.objectLevels objectChurchReading_valid
    objectRigid_groundHeads objectRules_groundHeadEq objectHeadReduction_decoderStuck
    objectHeadReduction_neutralNormal objectRigid_inductiveNumbers consts

include consts in
/-- **The injectivity and no-confusion of the object package's annotated type formers**,
with every constant adequate. -/
theorem objectChurch_formerFacts : CFormerFacts objectChurch :=
  (objectChurch_formFacts consts).formers

include consts in
/-- **Coherence of annotations for the object package**, with every constant adequate: two
annotated terms with one erasure, typed at one type, are equal at it. -/
theorem objectChurch_coherence_of_constAdequate {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed objectChurch Γ) {t t' A : CTm Tower.Head n}
    (typing : CTyped objectChurch Γ t A) (typing' : CTyped objectChurch Γ t' A)
    (same : t.erase = t'.erase) : CEqual objectChurch Γ t t' A :=
  objectChurch_coherence (objectChurch_formerFacts consts) formed typing typing' same

include consts in
/-- **The object package's root steps preserve types**, with every constant adequate. -/
theorem objectChurch_rootPreserving_of_constAdequate : CRootPreserving objectChurch :=
  objectChurch_rootPreserving (objectChurch_formerFacts consts)

end Adequate

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
