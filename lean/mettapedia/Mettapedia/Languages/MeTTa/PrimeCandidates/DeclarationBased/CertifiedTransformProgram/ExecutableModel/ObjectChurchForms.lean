import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchFundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationForms

/-!
# The weak-head forms of the annotated types of packages containing the object package

Every statement here is about a package containing the object package (`ObjectExtension`),
the object package itself among them, unless it names the object package.

* **The conditions** of `CTypeEq.formsMatch_sub` hold in every extension: a type whose erasure
  is neutral takes no head step (`ObjectExtension.neutralNormal`), and the inductive types are
  read with their datatype's tag (`ObjectExtension.rigid_inductivesRead`).
* **The rigid types `set` and `prop` are adequate** (`constAdequateAt_set`,
  `constAdequateAt_prop`).
* **Equal types in weak-head form match within adequate constants**
  (`ObjectExtension.formsMatch_within`): for every equation derivable in the object package
  within a set of adequate constants, over a context formed within them. In particular a
  neutral type is equal there to no type former and not to the numbers
  (`ObjectExtension.neutral_not_former_within`, `ObjectExtension.neutral_not_num_within`).
* **The adequacy of the object package's constants** (`ObjectExtension.objectConsts_adequate_of`)
  follows from that of `Power`, `pow`, `num-rec`, `transportCert`, `composeCert`, `returnIter`,
  `sucStep`, the decoder, implication and the equations `eq@A`; the other constants are
  adequate.
* **With every constant adequate**: the facts about the weak-head forms
  (`ObjectExtension.formFacts`) and the injectivity and no-confusion of the type formers
  (`ObjectExtension.formerFacts`); for the object package, coherence of annotations
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

variable (X : ObjectExtension)

/-! ## The rigid types -/

/-- **`set` is adequate**: the sets are an adequate type of `U₀`. -/
theorem constAdequateAt_set : ConstAdequateAt X.reading X.head setN :=
  ConstAdequateAt.of_adequate
    (X.sub.constantType (objectChurch_declared (c := setN) (T := Package.U0) (by decide) rfl))
    ((adequateType_typeAt X (.base .set) (.nil : CCtx Tower.Head 0)).adequate X.levels
      X.soundnessFacts (X.sort Tower.zero))

/-- **`prop` is adequate**: the proposition codes are an adequate type of `U₀`. -/
theorem constAdequateAt_prop : ConstAdequateAt X.reading X.head propN :=
  ConstAdequateAt.of_adequate
    (X.sub.constantType (objectChurch_declared (c := propN) (T := Package.U0) (by decide) rfl))
    ((adequateType_typeAt X .prop (.nil : CCtx Tower.Head 0)).adequate X.levels
      X.soundnessFacts (X.sort Tower.zero))

/-! ## Within adequate constants -/

section Within

variable {X} {allowed : DeclName → Bool}
  (consts : ∀ {c : DeclName}, allowed c = true → ConstAdequateAt X.reading X.head c)
  {n : Nat} {Γ : CCtx Tower.Head n}

include consts in
/-- **Equal types in weak-head form match, within adequate constants**: for every equation of
types derivable in the object package within a set of constants adequate in the extension, over
a context formed within them. -/
theorem ObjectExtension.formsMatch_within {A B : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A B)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ)
    (formA : IsTypeForm X.roles A.erase) (formB : IsTypeForm X.roles B.erase) :
    CFormsMatch X.church X.roles Γ A B :=
  CTypeEq.formsMatch_sub X.levels X.valid X.groundHeads X.groundHeadEq X.decoderStuck
    (ChurchRules.restrict_sub.trans X.sub)
    (fun declared => consts (ChurchRules.restrict_declared declared).1)
    X.neutralNormal X.rigid_inductivesRead equal formed formA formB

include consts in
/-- **A neutral type is equal to no type former, within adequate constants.** -/
theorem ObjectExtension.neutral_not_former_within {A B : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A B)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ) (neutral : Neutral X.roles A.erase)
    (former : CFormer B) : False :=
  equal.neutral_not_former_sub X.levels X.valid X.groundHeads X.groundHeadEq X.decoderStuck
    (ChurchRules.restrict_sub.trans X.sub)
    (fun declared => consts (ChurchRules.restrict_declared declared).1)
    X.neutralNormal formed neutral former

include consts in
/-- **A neutral type is not equal to the numbers, within adequate constants.** -/
theorem ObjectExtension.neutral_not_num_within {A : CTm Tower.Head n}
    (equal : CTypeEq (objectChurch.restrict allowed) Γ A cnum)
    (formed : CCtxFormed (objectChurch.restrict allowed) Γ) (neutral : Neutral X.roles A.erase) :
    False :=
  equal.neutral_not_inductive_sub X.levels X.valid X.groundHeads X.groundHeadEq X.decoderStuck
    (ChurchRules.restrict_sub.trans X.sub)
    (fun declared => consts (ChurchRules.restrict_declared declared).1)
    X.neutralNormal X.rigid_inductivesRead formed neutral
    ((X.roles_object (by decide)).trans objectRoles_num)

end Within

/-! ## The adequacy of the object package's constants -/

/-- **Every constant of the object package is adequate in an extension** once `Power`, `pow`,
`num-rec`, `transportCert`, `composeCert`, `returnIter`, `sucStep`, the decoder, implication and
the equations `eq@A` are: the numbers, their constructors, addition, the sets, the proposition
codes, the identity eliminator, `eqAt`, `sucMove`, `keepCert`, the iterator and the
quantifiers `all@A` are adequate. -/
theorem ObjectExtension.objectConsts_adequate_of
    (power : ConstAdequateAt X.reading X.head powerN)
    (pow : ConstAdequateAt X.reading X.head powN)
    (numRec : ConstAdequateAt X.reading X.head numRecName)
    (transport : ConstAdequateAt X.reading X.head transportName)
    (compose : ConstAdequateAt X.reading X.head composeName)
    (returnIter : ConstAdequateAt X.reading X.head returnIterName)
    (sucStep : ConstAdequateAt X.reading X.head sucStepName)
    (holds : ConstAdequateAt X.reading X.head holdsN)
    (imp : ConstAdequateAt X.reading X.head impN)
    (eq : ∀ type, ConstAdequateAt X.reading X.head (SetProfile.eqName type)) :
    ∀ {c : DeclName} {D : CTm Tower.Head 0}, objectChurch.constantType c = some D →
      ConstAdequateAt X.reading X.head c := by
  intro c D declared
  show ConstAdequateAt X.reading X.head c
  have fixed : ∀ p ∈ fixedDecls, ConstAdequateAt X.reading X.head p.1 := by
    simp only [fixedDecls, declarations, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨constAdequateAt_prop X, holds, imp, constAdequateAt_num X, constAdequateAt_set X,
      constAdequateAt_zero X, constAdequateAt_suc X, constAdequateAt_add X, power, pow, numRec,
      constAdequateAt_j X, constAdequateAt_eqAt X, constAdequateAt_sucMove' X,
      constAdequateAt_keep X, transport, compose, constAdequateAt_iter X, returnIter, sucStep⟩
  rw [objectChurch_constantType] at declared
  unfold elabDeclarations at declared
  cases hT : objectRules.constantType c with
  | none => rw [hT] at declared; cases declared
  | some T =>
      rcases objectRules_constantType_cases hT with ⟨type, rfl, -⟩ | ⟨type, rfl, -⟩ | hmem
      · exact (constAdequateAt_all X type : ConstAdequateAt X.reading X.head _)
      · exact (eq type : ConstAdequateAt X.reading X.head _)
      · exact (fixed _ hmem : ConstAdequateAt X.reading X.head (c, T).1)

/-! ## With every constant adequate -/

section Adequate

variable {X} (consts : ConstAdequate X.reading X.head)

include consts in
/-- **The facts about the weak-head forms of an extension's annotated types**, with every
constant adequate. -/
theorem ObjectExtension.formFacts : CFormFacts X.church X.roles :=
  CFormFacts.of_constAdequate X.levels X.valid X.groundHeads X.groundHeadEq X.decoderStuck
    X.neutralNormal X.rigid_inductivesRead consts

include consts in
/-- **The injectivity and no-confusion of an extension's annotated type formers**, with every
constant adequate. -/
theorem ObjectExtension.formerFacts : CFormerFacts X.church :=
  (ObjectExtension.formFacts consts).formers

end Adequate

section ObjectAdequate

variable (consts : ConstAdequate objectChurchReading objectHeadReduction)

include consts in
/-- **Coherence of annotations for the object package**, with every constant adequate: two
annotated terms with one erasure, typed at one type, are equal at it. -/
theorem objectChurch_coherence_of_constAdequate {n : Nat} {Γ : CCtx Tower.Head n}
    (formed : CCtxFormed objectChurch Γ) {t t' A : CTm Tower.Head n}
    (typing : CTyped objectChurch Γ t A) (typing' : CTyped objectChurch Γ t' A)
    (same : t.erase = t'.erase) : CEqual objectChurch Γ t t' A :=
  objectChurch_coherence (ObjectExtension.formerFacts (X := objectExtension) consts) formed typing
    typing' same

include consts in
/-- **The object package's root steps preserve types**, with every constant adequate. -/
theorem objectChurch_rootPreserving_of_constAdequate : CRootPreserving objectChurch :=
  objectChurch_rootPreserving (ObjectExtension.formerFacts (X := objectExtension) consts)

end ObjectAdequate

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
