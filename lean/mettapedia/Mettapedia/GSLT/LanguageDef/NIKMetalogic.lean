import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Data.Finset.Max
import Mettapedia.GSLT.LanguageDef.NIKIndexedOperational
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClone

/-!
# The metalogic carried by NIK authorities

NIK's primitive judgment retains a certificate accepted by a selected
authority.  It does not determine hypothetical consequence.  This module
separates that replay waist from optional consequence and comprehension
structure, and records the exact bridges that are available when the extra
laws are supplied.
-/

namespace Mettapedia.GSLT.LanguageDef.NIKMetalogic

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed

universe uSignature uHom uSentence uKind uClaim uCertificate uFormula uEvidence
  uSourceEvidence uMiddleEvidence uTargetEvidence uContext uSubstitution
  uArtifact uProof

/-! ## Pi-institutions -/

/-- A Pi-institution presents consequence directly, without choosing models.
Sentence translation is covariant, and every signature carries a Tarski
closure operator compatible with translation. -/
structure PiInstitution (Signature : Type uSignature)
    [CategoryTheory.Category.{uHom} Signature] where
  sentence : CategoryTheory.Functor Signature (Type (max uSentence 0))
  consequence : (signature : Signature) →
    ClosureOperator (Set (sentence.obj signature))
  translation : ∀ {source target : Signature} (map : source ⟶ target)
      (premises : Set (sentence.obj source)),
    Set.image (sentence.map map) (consequence source premises) ⊆
      consequence target (Set.image (sentence.map map) premises)

namespace PiInstitution

variable {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution Signature)

/-- The consequence judgment induced by closure membership. -/
def Derives (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (conclusion : institution.sentence.obj signature) : Prop :=
  conclusion ∈ institution.consequence signature premises

/-- Every premise is derivable. -/
theorem derives_of_mem (signature : Signature)
    {premises : Set (institution.sentence.obj signature)}
    {formula : institution.sentence.obj signature}
    (member : formula ∈ premises) :
    institution.Derives signature premises formula :=
  institution.consequence signature |>.le_closure premises member

/-- Consequence is monotone in its hypotheses. -/
theorem derives_mono (signature : Signature)
    {source target : Set (institution.sentence.obj signature)}
    (subset : source ⊆ target)
    {formula : institution.sentence.obj signature}
    (derives : institution.Derives signature source formula) :
    institution.Derives signature target formula :=
  institution.consequence signature |>.monotone subset derives

/-- Cutting a whole layer of already-derived premises is idempotence of the
closure operator. -/
theorem derives_cut (signature : Signature)
    {premises : Set (institution.sentence.obj signature)}
    {formula : institution.sentence.obj signature}
    (derives : institution.Derives signature
      (institution.consequence signature premises) formula) :
    institution.Derives signature premises formula := by
  change formula ∈ institution.consequence signature
    (institution.consequence signature premises) at derives
  change formula ∈ institution.consequence signature premises
  rw [← (institution.consequence signature).idempotent premises]
  exact derives

/-- The theorem set is consequence from no local hypotheses. -/
def theorems (signature : Signature) :
    Set (institution.sentence.obj signature) :=
  institution.consequence signature ∅

/-- Signature translation preserves theorems. -/
theorem map_theorem {source target : Signature} (map : source ⟶ target)
    {formula : institution.sentence.obj source}
    (theoremhood : formula ∈ institution.theorems source) :
    institution.sentence.map map formula ∈ institution.theorems target := by
  have transported := institution.translation map ∅
    (Set.mem_image_of_mem (institution.sentence.map map) theoremhood)
  simpa [theorems] using transported

/-- A theory is a consequence-closed set of sentences. -/
def Theory (signature : Signature) :=
  { formulas : Set (institution.sentence.obj signature) //
    institution.consequence signature formulas = formulas }

/-! ### Signature-changing comorphisms -/

/-- A signature-changing comorphism of Pi-institutions in the
Fiadeiro--Sernadas direction: signatures and sentences map covariantly, and
translated consequence is preserved.  Source and target signature categories
may differ; the later `Hom` is the useful vertical specialization over one
fixed signature category. -/
structure Comorphism
    {SourceSignature TargetSignature : Type uSignature}
    [CategoryTheory.Category.{uHom} SourceSignature]
    [CategoryTheory.Category.{uHom} TargetSignature]
    (source : PiInstitution.{uSignature, uHom, uSentence} SourceSignature)
    (target : PiInstitution.{uSignature, uHom, uSentence} TargetSignature) where
  mapSignature : CategoryTheory.Functor SourceSignature TargetSignature
  mapSentence : ∀ signature, source.sentence.obj signature →
    target.sentence.obj (mapSignature.obj signature)
  mapSentence_natural : ∀ {sourceSignature targetSignature}
      (translation : sourceSignature ⟶ targetSignature)
      (formula : source.sentence.obj sourceSignature),
    target.sentence.map (mapSignature.map translation)
        (mapSentence sourceSignature formula) =
      mapSentence targetSignature (source.sentence.map translation formula)
  preserves : ∀ (signature : SourceSignature)
      (premises : Set (source.sentence.obj signature))
      (formula : source.sentence.obj signature),
    formula ∈ source.consequence signature premises →
      mapSentence signature formula ∈
        target.consequence (mapSignature.obj signature)
          (Set.image (mapSentence signature) premises)

namespace Comorphism

def identity
    {Signature : Type uSignature}
    [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Comorphism institution institution where
  mapSignature :=
    { obj := id
      map := fun translation => translation
      map_id := by intro signature; rfl
      map_comp := by intro source target last earlier later; rfl }
  mapSentence := fun _ formula => formula
  mapSentence_natural := by intro source target translation formula; rfl
  preserves := by
    intro signature premises formula derives
    simp only [id, Set.image_id']
    convert derives using 1 <;> rfl

def comp
    {FirstSignature MiddleSignature LastSignature : Type uSignature}
    [CategoryTheory.Category.{uHom} FirstSignature]
    [CategoryTheory.Category.{uHom} MiddleSignature]
    [CategoryTheory.Category.{uHom} LastSignature]
    {first : PiInstitution.{uSignature, uHom, uSentence} FirstSignature}
    {middle : PiInstitution.{uSignature, uHom, uSentence} MiddleSignature}
    {last : PiInstitution.{uSignature, uHom, uSentence} LastSignature}
    (earlier : Comorphism first middle) (later : Comorphism middle last) :
    Comorphism first last where
  mapSignature := CategoryTheory.Functor.comp earlier.mapSignature
    later.mapSignature
  mapSentence := fun signature formula =>
    later.mapSentence (earlier.mapSignature.obj signature)
      (earlier.mapSentence signature formula)
  mapSentence_natural := by
    intro sourceSignature targetSignature translation formula
    change last.sentence.map
        (later.mapSignature.map (earlier.mapSignature.map translation))
        (later.mapSentence (earlier.mapSignature.obj sourceSignature)
          (earlier.mapSentence sourceSignature formula)) = _
    rw [later.mapSentence_natural, earlier.mapSentence_natural]
  preserves := by
    intro signature premises formula derives
    have firstDerives := earlier.preserves signature premises formula derives
    have lastDerives := later.preserves (earlier.mapSignature.obj signature)
      (Set.image (earlier.mapSentence signature) premises)
      (earlier.mapSentence signature formula) firstDerives
    rw [Set.image_image] at lastDerives
    change later.mapSentence (earlier.mapSignature.obj signature)
        (earlier.mapSentence signature formula) ∈
      last.consequence
        (later.mapSignature.obj (earlier.mapSignature.obj signature))
        (Set.image
          (fun sourceFormula =>
            later.mapSentence (earlier.mapSignature.obj signature)
              (earlier.mapSentence signature sourceFormula)) premises)
    exact lastDerives

end Comorphism

/-! ### Morphisms over a fixed signature category -/

/-- A morphism of Pi-institutions over the same signature category.  Sentence
translation is natural, and derivability is preserved after translating every
hypothesis.  More general morphisms may also change the signature category;
this vertical category is the exact part needed for comparing consequence
layers over one NIK authority diagram. -/
structure Hom
    (source target : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  mapSentence : source.sentence ⟶ target.sentence
  preserves : ∀ (signature : Signature)
      (premises : Set (source.sentence.obj signature))
      (formula : source.sentence.obj signature),
    formula ∈ source.consequence signature premises →
      mapSentence.app signature formula ∈
        target.consequence signature
          (Set.image (mapSentence.app signature) premises)

namespace Hom

variable {source middle target :
  PiInstitution.{uSignature, uHom, uSentence} Signature}

def identity (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Hom institution institution where
  mapSentence := CategoryTheory.NatTrans.id institution.sentence
  preserves := by
    intro signature premises formula derives
    simpa using derives

def comp (earlier : Hom source middle) (later : Hom middle target) :
    Hom source target where
  mapSentence := CategoryTheory.CategoryStruct.comp earlier.mapSentence
    later.mapSentence
  preserves := by
    intro signature premises formula derives
    have first := earlier.preserves signature premises formula derives
    have second := later.preserves signature
      (Set.image (earlier.mapSentence.app signature) premises)
      (earlier.mapSentence.app signature formula) first
    have imageComposition :
        Set.image (later.mapSentence.app signature)
            (Set.image (earlier.mapSentence.app signature) premises) =
          Set.image
            ((CategoryTheory.CategoryStruct.comp earlier.mapSentence
              later.mapSentence).app signature) premises := by
      ext translated
      constructor
      · rintro ⟨middleFormula, ⟨sourceFormula, member, rfl⟩, rfl⟩
        exact ⟨sourceFormula, member, rfl⟩
      · rintro ⟨sourceFormula, member, rfl⟩
        exact ⟨earlier.mapSentence.app signature sourceFormula,
          ⟨sourceFormula, member, rfl⟩, rfl⟩
    rw [imageComposition] at second
    exact second

@[ext]
theorem ext {left right : Hom source target}
    (mapSentenceEqual : left.mapSentence = right.mapSentence) :
    left = right := by
  cases left
  cases right
  cases mapSentenceEqual
  rfl

end Hom

instance instQuiverPiInstitution :
    Quiver (PiInstitution.{uSignature, uHom, uSentence} Signature) where
  Hom := Hom

instance instCategoryPiInstitution :
    CategoryTheory.Category
      (PiInstitution.{uSignature, uHom, uSentence} Signature) where
  id := Hom.identity
  comp := Hom.comp
  id_comp morphism := by
    apply Hom.ext
    exact CategoryTheory.Category.id_comp morphism.mapSentence
  comp_id morphism := by
    apply Hom.ext
    exact CategoryTheory.Category.comp_id morphism.mapSentence
  assoc first second third := by
    apply Hom.ext
    exact CategoryTheory.Category.assoc first.mapSentence second.mapSentence
      third.mapSentence

/-! ### The category of closed theories -/

/-- A closed theory retains both its signature and its consequence-closed
set of sentences. -/
structure TheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  signature : Signature
  theory : institution.Theory signature

/-- The theory generated by an arbitrary axiom set is its consequence
closure. -/
def generatedTheory
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (axioms : Set (institution.sentence.obj signature)) :
    TheoryObject institution where
  signature := signature
  theory := ⟨institution.consequence signature axioms,
    (institution.consequence signature).idempotent axioms⟩

@[simp]
theorem mem_generatedTheory_iff
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (axioms : Set (institution.sentence.obj signature))
    (formula : institution.sentence.obj signature) :
    formula ∈ (generatedTheory institution signature axioms).theory.1 ↔
      formula ∈ institution.consequence signature axioms :=
  Iff.rfl

/-- A theory morphism translates the signature and sends every source theorem
to a target theorem. -/
structure TheoryHom
    {institution : PiInstitution.{uSignature, uHom, uSentence} Signature}
    (source target : TheoryObject institution) where
  mapSignature : source.signature ⟶ target.signature
  preserves : ∀ {formula}, formula ∈ source.theory.1 →
    institution.sentence.map mapSignature formula ∈ target.theory.1

namespace TheoryHom

variable {institution :
  PiInstitution.{uSignature, uHom, uSentence} Signature}
  {first middle last : TheoryObject institution}

def identity (theory : TheoryObject institution) : TheoryHom theory theory where
  mapSignature := CategoryTheory.CategoryStruct.id theory.signature
  preserves := by
    intro formula theoremhood
    simpa using theoremhood

def comp (earlier : TheoryHom first middle) (later : TheoryHom middle last) :
    TheoryHom first last where
  mapSignature := CategoryTheory.CategoryStruct.comp earlier.mapSignature
    later.mapSignature
  preserves := by
    intro formula theoremhood
    have middleTheorem := earlier.preserves theoremhood
    have lastTheorem := later.preserves middleTheorem
    simpa using lastTheorem

@[ext]
theorem ext {source target : TheoryObject institution}
    {left right : TheoryHom source target}
    (mapEqual : left.mapSignature = right.mapSignature) : left = right := by
  cases left
  cases right
  cases mapEqual
  rfl

end TheoryHom

instance instQuiverTheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    Quiver (TheoryObject institution) where
  Hom := TheoryHom

instance instCategoryTheoryObject
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Category (TheoryObject institution) where
  id := TheoryHom.identity
  comp := TheoryHom.comp
  id_comp morphism := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.id_comp morphism.mapSignature
  comp_id morphism := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.comp_id morphism.mapSignature
  assoc first second third := by
    apply TheoryHom.ext
    exact CategoryTheory.Category.assoc first.mapSignature second.mapSignature
      third.mapSignature

/-- Sentences indexed by the category of closed theories. -/
def theorySentence (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory := institution.sentence.obj theory.signature
  map translation := institution.sentence.map translation.mapSignature
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro formula
    exact institution.sentence.map_id_apply theory.signature formula
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro formula
    exact institution.sentence.map_comp_apply earlier.mapSignature
      later.mapSignature formula

/-! ### The proof-projection nucleus of a Meseguer proof calculus -/

/-- Proof objects functorial in closed theories, whose projection has exactly
each theory's theorem set as image.  This is the proof-to-sentence nucleus of
Meseguer's proof-calculus account.  Models and satisfaction are not part of
it, and richer proof structures may replace the present Type-valued functor. -/
structure ProofCalculus
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) where
  proof : CategoryTheory.Functor (TheoryObject institution) (Type uSentence)
  projection : proof ⟶ theorySentence institution
  theorem_image : ∀ (theory : TheoryObject institution)
      (formula : institution.sentence.obj theory.signature),
    (∃ evidence : proof.obj theory,
      projection.app theory evidence = formula) ↔
        formula ∈ theory.theory.1

namespace ProofCalculus

variable {institution :
  PiInstitution.{uSignature, uHom, uSentence} Signature}

/-- The canonical thin proof functor has exactly one proof-irrelevant object
for each theorem of each closed theory. -/
def thinProofFunctor (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory := { formula : institution.sentence.obj theory.signature //
    formula ∈ theory.theory.1 }
  map translation := TypeCat.ofHom fun theoremObject =>
    ⟨institution.sentence.map translation.mapSignature theoremObject.1,
      translation.preserves theoremObject.2⟩
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro theoremObject
    apply Subtype.ext
    exact institution.sentence.map_id_apply theory.signature theoremObject.1
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro theoremObject
    apply Subtype.ext
    exact institution.sentence.map_comp_apply earlier.mapSignature
      later.mapSignature theoremObject.1

/-- Every Pi-institution admits a canonical thin proof-calculus nucleus. -/
def thin (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    ProofCalculus institution where
  proof := thinProofFunctor institution
  projection :=
    { app := fun _ => TypeCat.ofHom Subtype.val
      naturality := by intro source target translation; rfl }
  theorem_image := by
    intro theory formula
    constructor
    · rintro ⟨proof, projected⟩
      simpa [thinProofFunctor] using projected ▸ proof.2
    · intro theoremhood
      exact ⟨⟨formula, theoremhood⟩, rfl⟩

/-- A proof-relevant presentation with the same theorem image as the thin
calculus.  The Boolean tag is retained by theory translation but erased by
the proof-to-sentence projection. -/
def taggedProofFunctor (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    CategoryTheory.Functor (TheoryObject institution) (Type uSentence) where
  obj theory :=
    { formula : institution.sentence.obj theory.signature //
      formula ∈ theory.theory.1 } × Bool
  map translation := TypeCat.ofHom fun proof =>
    (⟨institution.sentence.map translation.mapSignature proof.1.1,
      translation.preserves proof.1.2⟩, proof.2)
  map_id theory := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro proof
    apply Prod.ext
    · apply Subtype.ext
      exact institution.sentence.map_id_apply theory.signature proof.1.1
    · rfl
  map_comp earlier later := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro proof
    apply Prod.ext
    · apply Subtype.ext
      exact institution.sentence.map_comp_apply earlier.mapSignature
        later.mapSignature proof.1.1
    · rfl

/-- The theorem-image law permits genuinely proof-relevant fibres; it does
not identify a logic with its thin closure presentation. -/
def tagged (institution :
    PiInstitution.{uSignature, uHom, uSentence} Signature) :
    ProofCalculus institution where
  proof := taggedProofFunctor institution
  projection :=
    { app := fun _ => TypeCat.ofHom fun proof => proof.1.1
      naturality := by intro source target translation; rfl }
  theorem_image := by
    intro theory formula
    constructor
    · rintro ⟨proof, projected⟩
      simpa [taggedProofFunctor] using projected ▸ proof.1.2
    · intro theoremhood
      exact ⟨(⟨formula, theoremhood⟩, false), rfl⟩

/-- Positive proof relevance can coexist with the exact same theorem image:
the tagged calculus has two proofs of every theorem that project to the same
sentence. -/
theorem tagged_projection_not_injective
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ¬ Function.Injective ((tagged institution).projection.app theory) := by
  intro injective
  let falseProof : (tagged institution).proof.obj theory :=
    (⟨formula, theoremhood⟩, false)
  let trueProof : (tagged institution).proof.obj theory :=
    (⟨formula, theoremhood⟩, true)
  have equalProofs : falseProof = trueProof := injective rfl
  have equalTags := congrArg Prod.snd equalProofs
  change false = true at equalTags
  cases equalTags

/-- The theorem-image law turns theoremhood back into an actual proof object;
this direction is exactly what a raw proof projection without adequacy lacks. -/
theorem proof_of_theorem (calculus : ProofCalculus institution)
    (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ∃ evidence : calculus.proof.obj theory,
      calculus.projection.app theory evidence = formula :=
  (calculus.theorem_image theory formula).mpr theoremhood

/-- A theory with a theorem cannot have an empty proof fibre in any adequate
proof calculus.  This is the negative boundary supplied by the image law. -/
theorem theorem_forbids_empty_proof_fibre
    (calculus : ProofCalculus institution) (theory : TheoryObject institution)
    (formula : institution.sentence.obj theory.signature)
    (theoremhood : formula ∈ theory.theory.1) :
    ¬ IsEmpty (calculus.proof.obj theory) := by
  intro emptyProofs
  obtain ⟨evidence, projected⟩ :=
    calculus.proof_of_theorem theory formula theoremhood
  exact emptyProofs.false evidence

end ProofCalculus

/-! ### Proof fibres with retained composition equations -/

/-- A proof fibre over one closed theory upgraded from a set of closed proofs
to a multisorted clone.  Its operations are proofs from ordered contexts,
projections retain hypothesis occurrences, and clone substitution is proof
composition.  The theorem-image law concerns only the nullary operations. -/
structure CloneProofFibre
    (theory : TheoryObject institution) where
  proof : MultiSortedClone.{uSentence, uProof}
    (institution.sentence.obj theory.signature)
  theorem_image : ∀ formula,
    Nonempty (proof.Hom [] formula) ↔ formula ∈ theory.theory.1

/-- Consequence relative to a closed theory: the theory is available as a
fixed collection of global hypotheses while `premises` remains local. -/
noncomputable def relativeClosure
    (theory : TheoryObject institution) :
    ClosureOperator (Set (institution.sentence.obj theory.signature)) :=
  ClosureOperator.mk'
    (fun premises => institution.consequence theory.signature
      (theory.theory.1 ∪ premises))
    (by
      intro source target subset
      exact (institution.consequence theory.signature).monotone
        (Set.union_subset_union_right _ subset))
    (by
      intro premises formula member
      exact (institution.consequence theory.signature).le_closure _
        (Set.mem_union_right _ member))
    (by
      intro premises formula twice
      have narrowed := (institution.consequence theory.signature).monotone
        (show theory.theory.1 ∪
              institution.consequence theory.signature
                (theory.theory.1 ∪ premises) ⊆
            institution.consequence theory.signature
              (theory.theory.1 ∪ premises) by
          intro hypothesis member
          rcases member with theoryMember | derived
          · exact (institution.consequence theory.signature).le_closure _
              (Set.mem_union_left _ theoryMember)
          · exact derived)
        twice
      simpa only [(institution.consequence theory.signature).idempotent]
        using narrowed)

@[simp]
theorem relativeClosure_empty
    (theory : TheoryObject institution) :
    institution.relativeClosure theory ∅ = theory.theory.1 := by
  change institution.consequence theory.signature
      (theory.theory.1 ∪ ∅) = theory.theory.1
  simpa using theory.theory.2

/-- Thin evidence for a closure operator forms a genuine multisorted clone.
The equations hold because every inhabited proof fibre is subsingleton; this
is the proof-irrelevant cartesian boundary, not a reconstruction of native
proof identity. -/
noncomputable def thinCloneOfClosure
    {Formula : Type uFormula}
    (closure : ClosureOperator (Set Formula)) :
    MultiSortedClone Formula where
  Hom context goal := PLift (goal ∈ closure { formula | formula ∈ context })
  project := fun {context} index =>
    ⟨closure.le_closure _ (List.get_mem context index)⟩
  substitute := by
    intro sourceContext targetContext output operation environment
    refine ⟨?_⟩
    have twice : output ∈ closure
        (closure { formula | formula ∈ targetContext }) :=
      closure.monotone (fun hypothesis member => by
        obtain ⟨index, indexEq⟩ := List.get_of_mem member
        exact indexEq ▸ (environment index).down) operation.down
    simpa only [closure.idempotent] using twice
  substitute_project := by
    intro sourceContext targetContext environment index
    exact Subsingleton.elim _ _
  substitute_projects := by
    intro context output operation
    exact Subsingleton.elim _ _
  substitute_assoc := by
    intro firstContext secondContext thirdContext output operation first second
    exact Subsingleton.elim _ _

/-- Every Pi-institution has a canonical proof-irrelevant clone fibre over
each closed theory.  Its nullary operations are exactly that theory's
theorems. -/
noncomputable def CloneProofFibre.thin
    (theory : TheoryObject institution) :
    CloneProofFibre.{uSignature, uHom, uSentence, 0} institution theory where
  proof := thinCloneOfClosure (institution.relativeClosure theory)
  theorem_image := by
    intro formula
    change Nonempty (PLift
        (formula ∈ institution.relativeClosure theory
          { sentence | sentence ∈ ([] : List
            (institution.sentence.obj theory.signature)) })) ↔ _
    simp only [List.not_mem_nil, Set.setOf_false, relativeClosure_empty]
    constructor
    · rintro ⟨proof⟩
      exact proof.down
    · intro theoremhood
      exact ⟨⟨theoremhood⟩⟩

end PiInstitution

namespace CertificateGSLTCloneCanary

open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- The concrete CertificateGSLT clone retains premise occurrence identity: two
equal formulas at different context positions give different projection
proofs.  Thus the clone upgrade is genuinely proof relevant and is not the
thin closure construction above. -/
theorem repeated_assumption_occurrences_distinct
    (object : CertificateGSLT.Object)
    (formula : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    (CertificateGSLT.derivationClone object).project
        (context := [formula, formula]) (0 : Fin 2) ≠
      (CertificateGSLT.derivationClone object).project
        (context := [formula, formula]) (1 : Fin 2) := by
  intro equalProofs
  have equalIndices : (0 : Fin 2) = (1 : Fin 2) := by
    injection equalProofs
  omega

end CertificateGSLTCloneCanary

/-! ## The least closure extending a raw theorem set -/

/-- Add a fixed raw theorem set to every premise set.  This is the least
Tarski closure with exactly those theorems at the empty context. -/
def theoremClosure {Sentence : Type uSentence} (theorems : Set Sentence) :
    ClosureOperator (Set Sentence) where
  toFun premises := premises ∪ theorems
  monotone' := by
    intro source target subset formula member
    rcases member with member | theoremhood
    · exact Or.inl (subset member)
    · exact Or.inr theoremhood
  le_closure' premises := Set.subset_union_left
  idempotent' premises := by
    ext formula
    constructor
    · rintro ((member | theoremhood) | theoremhood)
      · exact Or.inl member
      · exact Or.inr theoremhood
      · exact Or.inr theoremhood
    · intro member
      exact Or.inl member

@[simp]
theorem theoremClosure_apply {Sentence : Type uSentence}
    (theorems premises : Set Sentence) :
    theoremClosure theorems premises = premises ∪ theorems :=
  rfl

@[simp]
theorem theoremClosure_empty {Sentence : Type uSentence}
    (theorems : Set Sentence) :
    theoremClosure theorems ∅ = theorems := by
  change ∅ ∪ theorems = theorems
  exact Set.empty_union theorems

/-- `theoremClosure` is pointwise below every closure having the requested
empty-context theorems. -/
theorem theoremClosure_minimal {Sentence : Type uSentence}
    (theorems : Set Sentence) (closure : ClosureOperator (Set Sentence))
    (contains : theorems ⊆ closure ∅) (premises : Set Sentence) :
    theoremClosure theorems premises ⊆ closure premises := by
  intro formula member
  rcases member with premise | theoremhood
  · exact closure.le_closure premises premise
  · exact closure.monotone (Set.empty_subset premises) (contains theoremhood)

/-! ## Raw checker authority does not determine consequence -/

/-- Consequence added to each authority fibre, with the empty-context theorem
set fixed to exactly the authority's certified scope.  No transport between
authorities is presumed at this local level. -/
structure LocalConsequenceExtension {Kind : Type uKind}
    (family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind) where
  consequence : (kind : Kind) →
    ClosureOperator (Set (family.Claim kind))
  empty_eq_certified : ∀ kind,
    consequence kind ∅ = { claim | family.Certified kind claim }

/-- Three sentences suffice to separate theorem replay from hypothetical
consequence. -/
inductive SeparationSentence where
  | theorem
  | antecedent
  | consequent
deriving DecidableEq

namespace SeparationSentence

/-- A checker whose exact certified scope contains only `theorem`. -/
def checker : Checker SeparationSentence Unit where
  check claim _ := decide (claim = .theorem)

theorem checker_authority : checker.Authority (· = .theorem) where
  sound := by
    intro claim certificate accepted
    simpa [checker] using accepted
  complete := by
    intro claim theoremhood
    subst claim
    exact ⟨(), by simp [checker]⟩

/-- The raw NIK family shared by both incompatible consequence extensions. -/
def family : AuthorityFamily Unit where
  Claim := fun _ => SeparationSentence
  Certificate := fun _ => Unit
  checker := fun _ => checker
  Certified := fun _ claim => claim = .theorem
  Meaning := fun _ claim => claim = .theorem
  projection := fun _ => checker_authority.toProjection

/-- The minimal extension has no hypothetical rule beyond premise and theorem
inclusion. -/
def minimalClosure : ClosureOperator (Set SeparationSentence) :=
  theoremClosure { .theorem }

/-- One application of the hypothetical rule `antecedent ⊢ consequent`, while
retaining premises and the raw theorem. -/
def ruleStep (premises : Set SeparationSentence) : Set SeparationSentence :=
  premises ∪ { .theorem } ∪
    { formula | .antecedent ∈ premises ∧ formula = .consequent }

/-- Add the nontrivial hypothetical rule `antecedent ⊢ consequent`. -/
def ruleClosure : ClosureOperator (Set SeparationSentence) where
  toFun := ruleStep
  monotone' := by
    intro source target subset formula member
    simp only [ruleStep, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_setOf_eq] at member ⊢
    rcases member with (member | theoremhood) | generated
    · exact Or.inl (Or.inl (subset member))
    · exact Or.inl (Or.inr theoremhood)
    · exact Or.inr ⟨subset generated.1, generated.2⟩
  le_closure' premises := by
    intro formula member
    exact Or.inl (Or.inl member)
  idempotent' premises := by
    ext formula
    have antecedent_ne_theorem :
        SeparationSentence.antecedent ≠ SeparationSentence.theorem := by
      decide
    have antecedent_ne_consequent :
        SeparationSentence.antecedent ≠ SeparationSentence.consequent := by
      decide
    simp only [ruleStep, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    aesop

def minimalExtension : LocalConsequenceExtension family where
  consequence := fun _ => minimalClosure
  empty_eq_certified := by
    intro kind
    cases kind
    ext claim
    change claim ∈ theoremClosure { .theorem } ∅ ↔ claim = .theorem
    rw [theoremClosure_empty]
    change claim = SeparationSentence.theorem ↔
      claim = SeparationSentence.theorem
    exact Iff.rfl

def ruleExtension : LocalConsequenceExtension family where
  consequence := fun _ => ruleClosure
  empty_eq_certified := by
    intro kind
    cases kind
    ext claim
    change claim ∈ ruleStep ∅ ↔ claim = .theorem
    change ((False ∨ claim = SeparationSentence.theorem) ∨
      (False ∧ claim = SeparationSentence.consequent)) ↔
        claim = SeparationSentence.theorem
    tauto

/-- Both extensions agree on the raw empty-context theorem set. -/
theorem extensions_agree_on_theorems :
    minimalExtension.consequence () ∅ =
      ruleExtension.consequence () ∅ := by
  rw [minimalExtension.empty_eq_certified, ruleExtension.empty_eq_certified]

/-- The nontrivial rule belongs only to the richer extension. -/
theorem consequent_not_in_minimal_antecedent :
    SeparationSentence.consequent ∉
      minimalExtension.consequence () { SeparationSentence.antecedent } := by
  change SeparationSentence.consequent ∉
    theoremClosure { SeparationSentence.theorem } { SeparationSentence.antecedent }
  change SeparationSentence.consequent ∉
    ({ SeparationSentence.antecedent } ∪ { SeparationSentence.theorem } :
    Set SeparationSentence)
  simp

theorem consequent_in_rule_antecedent :
    SeparationSentence.consequent ∈
      ruleExtension.consequence () { SeparationSentence.antecedent } := by
  change SeparationSentence.consequent ∈
    ruleStep { SeparationSentence.antecedent }
  simp [ruleStep]

theorem minimalClosure_ne_ruleClosure : minimalClosure ≠ ruleClosure := by
  intro equalClosures
  have equalAtAntecedent := congrArg
    (fun closure : ClosureOperator (Set SeparationSentence) =>
      closure { SeparationSentence.antecedent }) equalClosures
  have generated : SeparationSentence.consequent ∈
      ruleClosure { SeparationSentence.antecedent } := by
    change SeparationSentence.consequent ∈
      ruleStep { SeparationSentence.antecedent }
    simp [ruleStep]
  have minimalMembership : SeparationSentence.consequent ∈
      minimalClosure { SeparationSentence.antecedent } := by
    rw [equalAtAntecedent]
    exact generated
  change SeparationSentence.consequent ∈
    theoremClosure { SeparationSentence.theorem }
      { SeparationSentence.antecedent } at minimalMembership
  change SeparationSentence.consequent ∈
    ({ SeparationSentence.antecedent } ∪ { SeparationSentence.theorem } :
      Set SeparationSentence) at minimalMembership
  simp at minimalMembership

/-- A raw authority and its exact theorem fibre do not reconstruct a unique
hypothetical consequence operator. -/
theorem rawNIK_does_not_determine_consequence :
    minimalExtension ≠ ruleExtension := by
  intro equalExtensions
  apply minimalClosure_ne_ruleClosure
  exact congrArg (fun extension => extension.consequence ()) equalExtensions

end SeparationSentence

/-! ## Proof-relevant evidence doctrines and proof-erased consequence -/

/-- A proof-relevant hypothetical judgment over sets of formulas.  `substitute`
is simultaneous cut: a derivation from `intermediate` hypotheses can be
instantiated by derivations of every intermediate hypothesis from `ambient`
hypotheses. -/
structure SetEvidenceDoctrine (Formula : Type uFormula) where
  Evidence : Set Formula → Formula → Type uEvidence
  assumption : ∀ {premises : Set Formula} {formula : Formula},
    formula ∈ premises → Evidence premises formula
  weakening : ∀ {source target : Set Formula} {formula : Formula},
    source ⊆ target → Evidence source formula → Evidence target formula
  substitute : ∀ {ambient intermediate : Set Formula} {formula : Formula},
    Evidence intermediate formula →
      (∀ hypothesis, hypothesis ∈ intermediate → Evidence ambient hypothesis) →
        Evidence ambient formula

namespace SetEvidenceDoctrine

variable {Formula : Type uFormula}
    (doctrine : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)

/-- Proof erasure retains only inhabitation of the evidence fibre. -/
def Provable (premises : Set Formula) (formula : Formula) : Prop :=
  Nonempty (doctrine.Evidence premises formula)

/-- Every proof-relevant set-evidence doctrine induces a Tarski closure.
Simultaneous evidence substitution supplies idempotence. -/
noncomputable def consequence : ClosureOperator (Set Formula) :=
  ClosureOperator.mk'
    (fun premises => { formula | doctrine.Provable premises formula })
    (by
      intro source target subset formula provable
      obtain ⟨evidence⟩ := provable
      exact ⟨doctrine.weakening subset evidence⟩)
    (by
      intro premises formula member
      exact ⟨doctrine.assumption member⟩)
    (by
      intro premises formula twiceProvable
      obtain ⟨outerEvidence⟩ := twiceProvable
      refine ⟨doctrine.substitute outerEvidence ?_⟩
      intro hypothesis hypothesisProvable
      exact Classical.choice hypothesisProvable)

@[simp]
theorem mem_consequence_iff (premises : Set Formula) (formula : Formula) :
    formula ∈ doctrine.consequence premises ↔
      Nonempty (doctrine.Evidence premises formula) :=
  Iff.rfl

theorem provable_mono {source target : Set Formula} (subset : source ⊆ target)
    {formula : Formula} :
    doctrine.Provable source formula → doctrine.Provable target formula := by
  rintro ⟨evidence⟩
  exact ⟨doctrine.weakening subset evidence⟩

/-- A proof-preserving morphism between evidence doctrines on the same
formula language. -/
structure Hom
    (source : SetEvidenceDoctrine.{uFormula, uSourceEvidence} Formula)
    (target : SetEvidenceDoctrine.{uFormula, uTargetEvidence} Formula) where
  map : ∀ {premises formula}, source.Evidence premises formula →
    target.Evidence premises formula
  map_assumption : ∀ {premises formula}
      (member : formula ∈ premises),
    map (source.assumption member) = target.assumption member
  map_weakening : ∀ {sourcePremises targetPremises formula}
      (subset : sourcePremises ⊆ targetPremises)
      (evidence : source.Evidence sourcePremises formula),
    map (source.weakening subset evidence) =
      target.weakening subset (map evidence)
  map_substitute : ∀ {ambient intermediate formula}
      (evidence : source.Evidence intermediate formula)
      (substitutions : ∀ hypothesis, hypothesis ∈ intermediate →
        source.Evidence ambient hypothesis),
    map (source.substitute evidence substitutions) =
      target.substitute (map evidence)
        (fun hypothesis member => map (substitutions hypothesis member))

namespace Hom

variable {source middle target :
  SetEvidenceDoctrine.{uFormula, uEvidence} Formula}

def identity (doctrine : SetEvidenceDoctrine.{uFormula, uEvidence} Formula) :
    Hom doctrine doctrine where
  map evidence := evidence
  map_assumption _ := rfl
  map_weakening _ _ := rfl
  map_substitute _ _ := rfl

def comp
    {source : SetEvidenceDoctrine.{uFormula, uSourceEvidence} Formula}
    {middle : SetEvidenceDoctrine.{uFormula, uMiddleEvidence} Formula}
    {target : SetEvidenceDoctrine.{uFormula, uTargetEvidence} Formula}
    (earlier : Hom source middle) (later : Hom middle target) :
    Hom source target where
  map evidence := later.map (earlier.map evidence)
  map_assumption member := by
    rw [earlier.map_assumption, later.map_assumption]
  map_weakening subset evidence := by
    rw [earlier.map_weakening, later.map_weakening]
  map_substitute evidence substitutions := by
    rw [earlier.map_substitute, later.map_substitute]

@[ext]
theorem ext
    {source : SetEvidenceDoctrine.{uFormula, uSourceEvidence} Formula}
    {target : SetEvidenceDoctrine.{uFormula, uTargetEvidence} Formula}
    {left right : Hom source target}
    (mapEqual : @left.map = @right.map) : left = right := by
  cases left
  cases right
  cases mapEqual
  rfl

end Hom

instance instQuiverSetEvidenceDoctrine :
    Quiver (SetEvidenceDoctrine.{uFormula, uEvidence} Formula) where
  Hom := Hom

instance instCategorySetEvidenceDoctrine :
    CategoryTheory.Category
      (SetEvidenceDoctrine.{uFormula, uEvidence} Formula) where
  id := Hom.identity
  comp := Hom.comp
  id_comp morphism := by apply Hom.ext; rfl
  comp_id morphism := by apply Hom.ext; rfl
  assoc first second third := by apply Hom.ext; rfl

/-- Thin evidence associated with one Tarski closure operator. -/
noncomputable def thinOfClosure (closure : ClosureOperator (Set Formula)) :
    SetEvidenceDoctrine.{uFormula, 0} Formula where
  Evidence premises formula := PLift (formula ∈ closure premises)
  assumption member := ⟨closure.le_closure _ member⟩
  weakening subset evidence := ⟨closure.monotone subset evidence.down⟩
  substitute := by
    intro ambient intermediate formula evidence substitutions
    refine ⟨?_⟩
    have twice : formula ∈ closure (closure ambient) :=
      closure.monotone
        (fun hypothesis member =>
          (substitutions hypothesis member).down)
        evidence.down
    simpa only [closure.idempotent] using twice

theorem thinOfClosure_subsingleton
    (closure : ClosureOperator (Set Formula))
    (premises : Set Formula) (formula : Formula) :
    Subsingleton
      ((thinOfClosure closure).Evidence
        premises formula) where
  allEq left right := by
    cases left
    cases right
    congr

/-- A morphism between closure operators is pointwise preservation of
derivability. -/
structure ClosureHom (source target : ClosureOperator (Set Formula)) : Type where
  preserves : ∀ premises, source premises ⊆ target premises

namespace ClosureHom

@[ext]
theorem ext {source target : ClosureOperator (Set Formula)}
    {left right : ClosureHom source target} : left = right := by
  cases left
  cases right
  rfl

instance instSubsingleton {source target : ClosureOperator (Set Formula)} :
    Subsingleton (ClosureHom source target) where
  allEq _ _ := ext

def identity (closure : ClosureOperator (Set Formula)) :
    ClosureHom closure closure where
  preserves _ := Set.Subset.rfl

def comp {first middle last : ClosureOperator (Set Formula)}
    (earlier : ClosureHom first middle) (later : ClosureHom middle last) :
    ClosureHom first last where
  preserves premises := Set.Subset.trans (earlier.preserves premises)
    (later.preserves premises)

end ClosureHom

instance instQuiverClosureOperator :
    Quiver (ClosureOperator (Set Formula)) where
  Hom := ClosureHom

instance instCategoryClosureOperator :
    CategoryTheory.Category (ClosureOperator (Set Formula)) where
  id := ClosureHom.identity
  comp := ClosureHom.comp
  id_comp _ := ClosureHom.ext
  comp_id _ := ClosureHom.ext
  assoc _ _ _ := ClosureHom.ext

/-- Erase proof identity while retaining its induced closure operator. -/
noncomputable def proofErasure :
    CategoryTheory.Functor
      (SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
      (ClosureOperator (Set Formula)) where
  obj doctrine := doctrine.consequence
  map morphism :=
    { preserves := by
        intro premises formula provable
        obtain ⟨evidence⟩ := provable
        exact ⟨morphism.map evidence⟩ }
  map_id _ := ClosureHom.ext
  map_comp _ _ := ClosureHom.ext

/-- Closure preservation lifts canonically to a morphism between thin proof
presentations. -/
noncomputable def thinEmbedding :
    CategoryTheory.Functor
      (ClosureOperator (Set Formula))
      (SetEvidenceDoctrine.{uFormula, 0} Formula) where
  obj := thinOfClosure
  map morphism :=
    { map := fun evidence => ⟨morphism.preserves _ evidence.down⟩
      map_assumption := by
        intro premises formula member
        exact (thinOfClosure_subsingleton _ premises formula).elim _ _
      map_weakening := by
        intro sourcePremises targetPremises formula subset evidence
        exact (thinOfClosure_subsingleton _ targetPremises formula).elim _ _
      map_substitute := by
        intro ambient intermediate formula evidence substitutions
        exact (thinOfClosure_subsingleton _ ambient formula).elim _ _ }
  map_id closure := by
    apply Hom.ext
    funext premises formula evidence
    exact (thinOfClosure_subsingleton closure premises formula).elim _ _
  map_comp earlier later := by
    apply Hom.ext
    funext premises formula evidence
    exact (thinOfClosure_subsingleton _ premises formula).elim _ _

/-- Every morphism into a thin presentation is uniquely determined by its
proof-erased consequence action. -/
theorem hom_thin_subsingleton
    (source : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
    (target : ClosureOperator (Set Formula)) :
    Subsingleton (Hom source (thinOfClosure target)) where
  allEq left right := by
    apply Hom.ext
    funext premises formula evidence
    exact (thinOfClosure_subsingleton target premises formula).elim _ _

/-- Proof erasure and thin evidence satisfy the defining hom-set equivalence
of a reflection.  This is the exact sense in which proof erasure is left
adjoint to the thin embedding, without claiming that proof presentations are
equivalent. -/
noncomputable def homToThinEquiv
    (source : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
    (target : ClosureOperator (Set Formula)) :
    Hom source (thinOfClosure target) ≃
      ClosureHom source.consequence target where
  toFun morphism :=
    { preserves := by
        intro premises formula provable
        obtain ⟨evidence⟩ := provable
        exact (morphism.map evidence).down }
  invFun closureMap :=
    { map := fun evidence =>
        ⟨closureMap.preserves _ ⟨evidence⟩⟩
      map_assumption := by
        intro premises formula member
        exact (thinOfClosure_subsingleton target premises formula).elim _ _
      map_weakening := by
        intro sourcePremises targetPremises formula subset evidence
        exact (thinOfClosure_subsingleton target targetPremises formula).elim _ _
      map_substitute := by
        intro ambient intermediate formula evidence substitutions
        exact (thinOfClosure_subsingleton target ambient formula).elim _ _ }
  left_inv morphism := by
    apply Hom.ext
    funext premises formula evidence
    exact (thinOfClosure_subsingleton target premises formula).elim _ _
  right_inv closureMap := by
    cases closureMap
    rfl

/-- Thin evidence erases back to exactly the closure from which it was
constructed. -/
theorem thinOfClosure_consequence
    (closure : ClosureOperator (Set Formula)) :
    (thinOfClosure closure).consequence = closure := by
  apply ClosureOperator.ext
  intro premises
  ext formula
  change Nonempty (PLift (formula ∈ closure premises)) ↔
    formula ∈ closure premises
  constructor
  · rintro ⟨evidence⟩
    exact evidence.down
  · intro derives
    exact ⟨⟨derives⟩⟩

/-- The thin embedding is fully faithful: a proof-preserving map between
thin presentations contains exactly one closure-preservation map. -/
noncomputable def thinEmbeddingFullyFaithful :
    (thinEmbedding (Formula := Formula)).FullyFaithful where
  preimage morphism :=
    { preserves := by
        intro premises formula derives
        exact (morphism.map ⟨derives⟩).down }
  map_preimage morphism :=
    (hom_thin_subsingleton _ _).elim _ _
  preimage_map morphism := ClosureHom.ext

/-- Proof erasure is left adjoint to the thin-evidence embedding.  This is
the categorical comparison with proof-irrelevant Pi-institutional closure;
the unit need not be invertible when proof identity carries information. -/
noncomputable def proofErasureThinAdjunction :
    proofErasure (Formula := Formula) ⊣ thinEmbedding (Formula := Formula) :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun source target => (homToThinEquiv source target).symm
      homEquiv_naturality_left_symm := by
        intro source' source target earlier later
        exact ClosureHom.ext
      homEquiv_naturality_right := by
        intro source target target' earlier later
        exact (hom_thin_subsingleton source target').elim _ _ }

end SetEvidenceDoctrine

/-- Proof-relevant consequence indexed covariantly by a signature category.
The evidence map is the exact extra law needed to make proof-erased closure
compatible with sentence translation. -/
structure IndexedSetEvidenceDoctrine
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (sentence : CategoryTheory.Functor Signature (Type (max uSentence 0))) where
  fibre : (signature : Signature) →
    SetEvidenceDoctrine.{uSentence, uEvidence} (sentence.obj signature)
  mapEvidence : ∀ {source target : Signature} (map : source ⟶ target)
      {premises : Set (sentence.obj source)} {formula : sentence.obj source},
    (fibre source).Evidence premises formula →
      (fibre target).Evidence (Set.image (sentence.map map) premises)
        (sentence.map map formula)

namespace IndexedSetEvidenceDoctrine

variable {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    {sentence : CategoryTheory.Functor Signature (Type (max uSentence 0))}
    (doctrine : IndexedSetEvidenceDoctrine.{uSignature, uHom, uSentence,
      uEvidence} sentence)

/-- Proof erasure of an indexed evidence doctrine is a Pi-institution. -/
noncomputable def toPiInstitution : PiInstitution Signature where
  sentence := sentence
  consequence := fun signature => (doctrine.fibre signature).consequence
  translation := by
    intro source target map premises formula member
    obtain ⟨sourceFormula, sourceEvidence, rfl⟩ := member
    obtain ⟨evidence⟩ := sourceEvidence
    exact ⟨doctrine.mapEvidence map evidence⟩

@[simp]
theorem toPiInstitution_consequence (signature : Signature) :
    (doctrine.toPiInstitution.consequence signature) =
      (doctrine.fibre signature).consequence :=
  rfl

end IndexedSetEvidenceDoctrine

/-! ### The converse thin evidence construction -/

/-- A Pi-institution supplies proof-irrelevant evidence by retaining only
closure membership. -/
def PiInstitution.ThinEvidence
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (formula : institution.sentence.obj signature) : Type :=
  PLift (institution.Derives signature premises formula)

/-- The canonical evidence presentation of a Pi-institution is fibrewise
subsingleton.  Thus non-discrete proof objects are not required by the
definition of a logic based on closure. -/
theorem PiInstitution.thinEvidence_subsingleton
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (premises : Set (institution.sentence.obj signature))
    (formula : institution.sentence.obj signature) :
    Subsingleton (institution.ThinEvidence signature premises formula) where
  allEq left right := by
    cases left
    cases right
    congr

/-- Every Pi-institution has a canonical thin proof-relevant presentation.
Its substitution operation is precisely monotonicity followed by closure
idempotence. -/
noncomputable def PiInstitution.toThinEvidenceDoctrine
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature) :
    IndexedSetEvidenceDoctrine institution.sentence where
  fibre signature :=
    { Evidence := institution.ThinEvidence signature
      assumption := by
        intro premises formula member
        exact ⟨institution.derives_of_mem signature member⟩
      weakening := by
        intro source target formula subset evidence
        exact ⟨institution.derives_mono signature subset evidence.down⟩
      substitute := by
        intro ambient intermediate formula evidence substitutions
        refine ⟨institution.derives_cut signature ?_⟩
        exact institution.derives_mono signature
          (fun hypothesis member => (substitutions hypothesis member).down)
          evidence.down }
  mapEvidence := by
    intro source target map premises formula evidence
    exact ⟨institution.translation map premises
      (Set.mem_image_of_mem (institution.sentence.map map) evidence.down)⟩

/-- Proof erasure after the thin construction recovers the original closure
operator exactly. -/
theorem PiInstitution.thinEvidence_closure_roundtrip
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature) :
    ((institution.toThinEvidenceDoctrine.fibre signature).consequence) =
      institution.consequence signature := by
  apply ClosureOperator.ext
  intro premises
  ext formula
  change Nonempty (PLift
    (institution.Derives signature premises formula)) ↔
      institution.Derives signature premises formula
  constructor
  · rintro ⟨evidence⟩
    exact evidence.down
  · intro derives
    exact ⟨⟨derives⟩⟩

/-! ### Exact proof-erasure comparison -/

/-- The unit from retained evidence to its thin proof-erased reflection. -/
def SetEvidenceDoctrine.toThinReflection
    {Formula : Type uFormula}
    (doctrine : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
    {premises : Set Formula} {formula : Formula}
    (evidence : doctrine.Evidence premises formula) :
    PLift (Nonempty (doctrine.Evidence premises formula)) :=
  ⟨⟨evidence⟩⟩

/-- The thin reflection is proof-irrelevant in every judgment fibre. -/
theorem SetEvidenceDoctrine.thinReflection_subsingleton
    {Formula : Type uFormula}
    (doctrine : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
    (premises : Set Formula) (formula : Formula) :
    Subsingleton
      (PLift (Nonempty (doctrine.Evidence premises formula))) := by
  infer_instance

/-- Proof erasure is faithful at one judgment exactly when the original
evidence fibre was already thin.  This is the exact obstruction to upgrading
the closure-level retraction into an equivalence of proof presentations. -/
theorem SetEvidenceDoctrine.toThinReflection_injective_iff_subsingleton
    {Formula : Type uFormula}
    (doctrine : SetEvidenceDoctrine.{uFormula, uEvidence} Formula)
    (premises : Set Formula) (formula : Formula) :
    Function.Injective
        (doctrine.toThinReflection (premises := premises) (formula := formula))
      ↔ Subsingleton (doctrine.Evidence premises formula) := by
  constructor
  · intro injective
    exact
      { allEq := by
          intro left right
          apply injective
          exact Subsingleton.elim _ _ }
  · intro subsingleton left right _
    exact subsingleton.elim left right

/-! ### What set-based consequence forgets -/

/-- Read a list context through its underlying set of formulas. -/
def PiInstitution.DerivesList
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (context : List (institution.sentence.obj signature))
    (formula : institution.sentence.obj signature) : Prop :=
  institution.Derives signature { hypothesis | hypothesis ∈ context } formula

/-- List presentations with the same support become indistinguishable after
passing to ordinary set-based Pi-institutional consequence. -/
theorem PiInstitution.derivesList_iff_of_mem_iff
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    {left right : List (institution.sentence.obj signature)}
    (sameSupport : ∀ formula, formula ∈ left ↔ formula ∈ right)
    (conclusion : institution.sentence.obj signature) :
    institution.DerivesList signature left conclusion ↔
      institution.DerivesList signature right conclusion := by
  have setsEqual :
      ({ formula | formula ∈ left } :
        Set (institution.sentence.obj signature)) =
      { formula | formula ∈ right } := by
    ext formula
    exact sameSupport formula
  rw [DerivesList, DerivesList, setsEqual]

/-- Ordinary Pi-institutional consequence forgets the order of two adjacent
hypotheses. -/
theorem PiInstitution.derivesList_swap
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (left right conclusion : institution.sentence.obj signature)
    (context : List (institution.sentence.obj signature)) :
    institution.DerivesList signature (left :: right :: context) conclusion ↔
      institution.DerivesList signature (right :: left :: context) conclusion := by
  apply institution.derivesList_iff_of_mem_iff signature _ conclusion
  intro formula
  simp only [List.mem_cons]
  tauto

/-- Ordinary Pi-institutional consequence also forgets duplicate hypotheses. -/
theorem PiInstitution.derivesList_contract
    {Signature : Type uSignature} [CategoryTheory.Category.{uHom} Signature]
    (institution : PiInstitution.{uSignature, uHom, uSentence} Signature)
    (signature : Signature)
    (repeated conclusion : institution.sentence.obj signature)
    (context : List (institution.sentence.obj signature)) :
    institution.DerivesList signature
        (repeated :: repeated :: context) conclusion ↔
      institution.DerivesList signature (repeated :: context) conclusion := by
  apply institution.derivesList_iff_of_mem_iff signature _ conclusion
  intro formula
  simp only [List.mem_cons]
  tauto

/-! ### Proof relevance is not recovered by closure -/

/-- Premise membership as a thin evidence doctrine. -/
def premiseEvidenceDoctrine (Formula : Type uFormula) :
    SetEvidenceDoctrine.{uFormula, 0} Formula where
  Evidence premises formula := PLift (formula ∈ premises)
  assumption member := ⟨member⟩
  weakening subset evidence := ⟨subset evidence.down⟩
  substitute evidence substitutions :=
    substitutions _ evidence.down

/-- The same provability relation with an additional retained Boolean proof
tag. -/
def taggedPremiseEvidenceDoctrine (Formula : Type uFormula) :
    SetEvidenceDoctrine.{uFormula, 0} Formula where
  Evidence premises formula := PLift (formula ∈ premises) × Bool
  assumption member := ⟨⟨member⟩, false⟩
  weakening subset evidence := ⟨⟨subset evidence.1.down⟩, evidence.2⟩
  substitute evidence substitutions := by
    obtain ⟨mapped, _⟩ := substitutions _ evidence.1.down
    exact ⟨mapped, evidence.2⟩

/-- Both proof presentations erase to the identity closure. -/
theorem premise_and_tagged_closure_agree (Formula : Type uFormula) :
    (premiseEvidenceDoctrine Formula).consequence =
      (taggedPremiseEvidenceDoctrine Formula).consequence := by
  apply ClosureOperator.ext
  intro premises
  ext formula
  change Nonempty (PLift (formula ∈ premises)) ↔
    Nonempty (PLift (formula ∈ premises) × Bool)
  constructor
  · rintro ⟨evidence⟩
    exact ⟨⟨evidence, false⟩⟩
  · rintro ⟨evidence, tag⟩
    exact ⟨evidence⟩

/-- The tagged presentation retains two distinct evidence objects for one
judgment, so equal closure does not recover proof relevance. -/
theorem taggedPremiseEvidence_not_subsingleton :
    ¬ Subsingleton
      ((taggedPremiseEvidenceDoctrine Unit).Evidence {()} ()) := by
  intro subsingleton
  let falseEvidence :
      (taggedPremiseEvidenceDoctrine Unit).Evidence {()} () :=
    ⟨⟨by simp⟩, false⟩
  let trueEvidence :
      (taggedPremiseEvidenceDoctrine Unit).Evidence {()} () :=
    ⟨⟨by simp⟩, true⟩
  have equalEvidence : falseEvidence = trueEvidence :=
    subsingleton.elim _ _
  have equalTags := congrArg Prod.snd equalEvidence
  change false = true at equalTags
  cases equalTags

/-- The tagged proof presentation supplies the negative witness: the closure
round trip is exact, but the unit to thin evidence identifies its two proof
tags. -/
theorem taggedPremise_toThinReflection_not_injective :
    ¬ Function.Injective
      ((taggedPremiseEvidenceDoctrine Unit).toThinReflection
        (premises := {()}) (formula := ())) := by
  intro injective
  have subsingleton :=
    ((taggedPremiseEvidenceDoctrine Unit)
      |>.toThinReflection_injective_iff_subsingleton {()} ()).mp injective
  exact taggedPremiseEvidence_not_subsingleton subsingleton

/-! ### Set consequence is optional guest structure -/

/-- An exact realization of list-indexed NIK evidence by a set-indexed
doctrine.  Such a realization forgets order and multiplicity by construction. -/
structure ListEvidenceRealization
    {Kind : Type uKind}
    (family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    (presentation : InternalJudgment.HypotheticalPresentation family)
    (kind : Kind)
    (doctrine : SetEvidenceDoctrine (presentation.Formula kind)) where
  toSet : ∀ {context goal},
    InternalJudgment.HypotheticalEvidence family presentation kind context goal →
      doctrine.Evidence { formula | formula ∈ context } goal
  fromSet : ∀ {context goal},
    doctrine.Evidence { formula | formula ∈ context } goal →
      InternalJudgment.HypotheticalEvidence family presentation kind context goal

/-- The live authority accepting exactly empty contexts cannot be represented
by a monotone set-evidence doctrine.  Hence ordinary Tarskian consequence is
not a theorem of the raw NIK waist. -/
theorem emptyContext_has_no_setEvidence_realization
    (doctrine : SetEvidenceDoctrine.{0, uEvidence} Unit) :
    ¬ Nonempty (ListEvidenceRealization
      InternalJudgmentCanary.emptyContextFamily
      InternalJudgmentCanary.emptyContextPresentation () doctrine) := by
  rintro ⟨realization⟩
  have source : InternalJudgment.HypotheticalEvidence
      InternalJudgmentCanary.emptyContextFamily
      InternalJudgmentCanary.emptyContextPresentation () [] () :=
    ⟨(), rfl⟩
  have sourceSet := realization.toSet source
  have subset : ({ formula | formula ∈ ([] : List Unit) } : Set Unit) ⊆
      { formula | formula ∈ [()] } := by
    simp
  have targetSet := doctrine.weakening subset sourceSet
  have target := realization.fromSet (context := [()]) targetSet
  have impossible := target.property
  simp [InternalJudgment.Checks,
    InternalJudgmentCanary.emptyContextPresentation,
    InternalJudgmentCanary.emptyContextFamily,
    InternalJudgmentCanary.emptyContextChecker] at impossible

/-! ## A neutral contextual evidence doctrine -/

/-- A guest-chosen category of contexts and substitutions. -/
structure ContextBase where
  Context : Type uContext
  category : CategoryTheory.Category.{uSubstitution} Context

instance ContextBase.instCategory (base : ContextBase) :
    CategoryTheory.Category base.Context :=
  base.category

/-- A substitution is a morphism of the guest's context category. -/
abbrev ContextBase.Substitution (base : ContextBase)
    (source target : base.Context) :=
  @Quiver.Hom base.Context
    base.category.toCategoryStruct.toQuiver source target

def ContextBase.identity (base : ContextBase) (context : base.Context) :
    base.Substitution context context :=
  @CategoryTheory.CategoryStruct.id base.Context
    base.category.toCategoryStruct context

def ContextBase.comp (base : ContextBase)
    {first second third : base.Context}
    (earlier : base.Substitution first second)
    (later : base.Substitution second third) :
    base.Substitution first third :=
  @CategoryTheory.CategoryStruct.comp base.Context
    base.category.toCategoryStruct first second third earlier later

/-- A functor between guest context categories, written without hiding either
category in global typeclass inference. -/
structure ContextMap (source target : ContextBase) where
  obj : source.Context → target.Context
  map : ∀ {left right}, source.Substitution left right →
    target.Substitution (obj left) (obj right)
  map_id : ∀ context, map (source.identity context) =
    target.identity (obj context)
  map_comp : ∀ {first second third}
      (earlier : source.Substitution first second)
      (later : source.Substitution second third),
    map (source.comp earlier later) = target.comp (map earlier) (map later)

def ContextMap.identity (base : ContextBase) : ContextMap base base where
  obj := id
  map := id
  map_id _ := rfl
  map_comp _ _ := rfl

def ContextMap.comp {first second third : ContextBase}
    (earlier : ContextMap first second) (later : ContextMap second third) :
    ContextMap first third where
  obj := later.obj ∘ earlier.obj
  map substitution := later.map (earlier.map substitution)
  map_id context := by
    change later.map (earlier.map (first.identity context)) =
      third.identity (later.obj (earlier.obj context))
    rw [earlier.map_id, later.map_id]
  map_comp earlierSubstitution laterSubstitution := by
    change later.map (earlier.map
        (first.comp earlierSubstitution laterSubstitution)) = _
    rw [earlier.map_comp, later.map_comp]
    rfl

/-- One guest's contextual judgment.  Claims and accepted proof objects
reindex contravariantly along substitutions.  The projection law says that
reindexing a proof also reindexes the claim it proves.  No weakening,
exchange, contraction, comprehension, or dependent type former is assumed. -/
structure ContextualEvidenceFibre where
  base : ContextBase.{uContext, uSubstitution}
  Claim : base.Context → Type uClaim
  Accepted : (context : base.Context) → Type uEvidence
  claimOf : ∀ {context}, Accepted context → Claim context
  reindexClaim : ∀ {source target : base.Context},
    base.Substitution source target →
    Claim target → Claim source
  reindexAccepted : ∀ {source target : base.Context},
    base.Substitution source target →
    Accepted target → Accepted source
  claimOf_reindex : ∀ {source target : base.Context}
      (substitution : base.Substitution source target)
      (accepted : Accepted target),
    claimOf (reindexAccepted substitution accepted) =
      reindexClaim substitution (claimOf accepted)
  reindexClaim_id : ∀ (context : base.Context) (claim : Claim context),
    reindexClaim (base.identity context) claim = claim
  reindexClaim_comp : ∀ {first second third : base.Context}
      (earlier : base.Substitution first second)
      (later : base.Substitution second third)
      (claim : Claim third),
    reindexClaim (base.comp earlier later) claim =
      reindexClaim earlier (reindexClaim later claim)
  reindexAccepted_id : ∀ (context : base.Context)
      (accepted : Accepted context),
    reindexAccepted (base.identity context) accepted =
      accepted
  reindexAccepted_comp : ∀ {first second third : base.Context}
      (earlier : base.Substitution first second)
      (later : base.Substitution second third)
      (accepted : Accepted third),
    reindexAccepted (base.comp earlier later) accepted =
      reindexAccepted earlier (reindexAccepted later accepted)

namespace ContextualEvidenceFibre

variable (fibre : ContextualEvidenceFibre)

/-- Evidence for a claim in a context is the retained fibre of the
proof-to-claim projection. -/
def Evidence (context : fibre.base.Context) (claim : fibre.Claim context) :=
  { accepted : fibre.Accepted context // fibre.claimOf accepted = claim }

/-- Contravariant substitution of a contextual claim. -/
def reindexEvidence {source target : fibre.base.Context}
    (substitution : fibre.base.Substitution source target)
    {claim : fibre.Claim target}
    (evidence : fibre.Evidence target claim) :
    fibre.Evidence source (fibre.reindexClaim substitution claim) :=
  ⟨fibre.reindexAccepted substitution evidence.1,
    fibre.claimOf_reindex substitution evidence.1 |>.trans
      (congrArg (fibre.reindexClaim substitution) evidence.2)⟩

end ContextualEvidenceFibre

/-- A translation between contextual guest judgments.  Authority transport is
covariant through `mapContext`; substitution remains contravariant inside each
fibre.  The last two fields are the interchange laws between those axes. -/
structure ContextualTranslation
    (source target : ContextualEvidenceFibre) where
  mapContext : ContextMap source.base target.base
  mapClaim : ∀ {context}, source.Claim context →
    target.Claim (mapContext.obj context)
  mapAccepted : ∀ {context}, source.Accepted context →
    target.Accepted (mapContext.obj context)
  projection_commutes : ∀ {context} (accepted : source.Accepted context),
    target.claimOf (mapAccepted accepted) = mapClaim (source.claimOf accepted)
  claim_substitution_interchange : ∀ {sourceContext targetContext}
      (substitution : source.base.Substitution sourceContext targetContext)
      (claim : source.Claim targetContext),
    target.reindexClaim (mapContext.map substitution) (mapClaim claim) =
      mapClaim (source.reindexClaim substitution claim)
  accepted_substitution_interchange : ∀ {sourceContext targetContext}
      (substitution : source.base.Substitution sourceContext targetContext)
      (accepted : source.Accepted targetContext),
    target.reindexAccepted (mapContext.map substitution)
        (mapAccepted accepted) =
      mapAccepted (source.reindexAccepted substitution accepted)

namespace ContextualTranslation

variable {source target : ContextualEvidenceFibre}
    (translation : ContextualTranslation source target)

/-- Identity translation of one contextual guest judgment. -/
def identity (source : ContextualEvidenceFibre) :
    ContextualTranslation source source where
  mapContext := ContextMap.identity source.base
  mapClaim := id
  mapAccepted := id
  projection_commutes _ := rfl
  claim_substitution_interchange _ _ := rfl
  accepted_substitution_interchange _ _ := rfl

/-- Composition of contextual translations preserves both the authority and
substitution axes. -/
def comp {first middle last : ContextualEvidenceFibre}
    (earlier : ContextualTranslation first middle)
    (later : ContextualTranslation middle last) :
    ContextualTranslation first last where
  mapContext := ContextMap.comp earlier.mapContext later.mapContext
  mapClaim claim := later.mapClaim (earlier.mapClaim claim)
  mapAccepted accepted := later.mapAccepted (earlier.mapAccepted accepted)
  projection_commutes accepted := by
    change last.claimOf (later.mapAccepted (earlier.mapAccepted accepted)) = _
    exact (later.projection_commutes (earlier.mapAccepted accepted)).trans
      (congrArg later.mapClaim (earlier.projection_commutes accepted))
  claim_substitution_interchange substitution claim := by
    change last.reindexClaim
      (later.mapContext.map (earlier.mapContext.map substitution))
      (later.mapClaim (earlier.mapClaim claim)) = _
    exact (later.claim_substitution_interchange
      (earlier.mapContext.map substitution) (earlier.mapClaim claim)).trans
      (congrArg later.mapClaim
        (earlier.claim_substitution_interchange substitution claim))
  accepted_substitution_interchange substitution accepted := by
    change last.reindexAccepted
      (later.mapContext.map (earlier.mapContext.map substitution))
      (later.mapAccepted (earlier.mapAccepted accepted)) = _
    exact (later.accepted_substitution_interchange
      (earlier.mapContext.map substitution)
      (earlier.mapAccepted accepted)).trans
      (congrArg later.mapAccepted
        (earlier.accepted_substitution_interchange substitution accepted))

/-- Map evidence along the authority axis while retaining its mapped claim. -/
def mapEvidence {context : source.base.Context}
    {claim : source.Claim context}
    (evidence : source.Evidence context claim) :
    target.Evidence (translation.mapContext.obj context)
      (translation.mapClaim claim) :=
  ⟨translation.mapAccepted evidence.1,
    translation.projection_commutes evidence.1 |>.trans
      (congrArg translation.mapClaim evidence.2)⟩

/-- Authority translation commutes with substitution on claims. -/
theorem mapClaim_reindex
    {sourceContext targetContext : source.base.Context}
    (substitution : source.base.Substitution sourceContext targetContext)
    (claim : source.Claim targetContext) :
    target.reindexClaim (translation.mapContext.map substitution)
        (translation.mapClaim claim) =
      translation.mapClaim (source.reindexClaim substitution claim) :=
  translation.claim_substitution_interchange substitution claim

/-- Authority translation commutes with substitution on retained evidence. -/
theorem mapAccepted_reindex
    {sourceContext targetContext : source.base.Context}
    (substitution : source.base.Substitution sourceContext targetContext)
    (accepted : source.Accepted targetContext) :
    target.reindexAccepted (translation.mapContext.map substitution)
        (translation.mapAccepted accepted) =
      translation.mapAccepted (source.reindexAccepted substitution accepted) :=
  translation.accepted_substitution_interchange substitution accepted

end ContextualTranslation

/-- A strict authority-indexed contextual doctrine.  Typed translation alone
does not earn the word `action`: identity and composition of the entire
claim-and-evidence translation are retained as explicit laws. -/
structure ContextualAuthorityDoctrine
    (Index : Type uKind) [CategoryTheory.Category.{uHom} Index] where
  fibre : Index → ContextualEvidenceFibre.{uContext, uSubstitution,
    uClaim, uEvidence}
  transport : ∀ {source target : Index}, (source ⟶ target) →
    ContextualTranslation.{uContext, uSubstitution, uClaim, uEvidence,
      uContext, uSubstitution, uClaim, uEvidence}
      (fibre source) (fibre target)
  transport_id : ∀ (kind : Index),
    transport (CategoryTheory.CategoryStruct.id kind) =
      ContextualTranslation.identity (fibre kind)
  transport_comp : ∀ {first second third : Index}
      (earlier : first ⟶ second) (later : second ⟶ third),
    transport (CategoryTheory.CategoryStruct.comp earlier later) =
      ContextualTranslation.comp (transport earlier) (transport later)

/-! ### A structural set-context guest -/

namespace StructuralContextGuest

private theorem pliftProp_subsingleton (proposition : Prop) :
    Subsingleton (PLift proposition) where
  allEq left right := by
    cases left
    cases right
    congr

/-- A structural context is a set of available formulas. -/
structure Context (Formula : Type uFormula) where
  formulas : Set Formula

/-- Substitution points from a larger ambient context to the smaller context
whose derivation is being weakened. -/
def Hom {Formula : Type uFormula}
    (source target : Context Formula) : Type :=
  PLift (target.formulas ⊆ source.formulas)

instance {Formula : Type uFormula} : Quiver (Context Formula) where
  Hom := Hom

instance {Formula : Type uFormula} (source target : Context Formula) :
    Subsingleton (source ⟶ target) where
  allEq left right := by
    change Hom source target at left right
    exact (pliftProp_subsingleton _).elim left right

instance {Formula : Type uFormula} :
    CategoryTheory.Category.{0} (Context Formula) where
  id := fun _ => ⟨Set.Subset.rfl⟩
  comp earlier later := ⟨Set.Subset.trans later.down earlier.down⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

def base (Formula : Type uFormula) : ContextBase.{uFormula, 0} where
  Context := Context Formula
  category := inferInstance

/-- Thin consequence evidence over structural contexts.  Reverse-inclusion
morphisms act by weakening. -/
noncomputable def fibre {Formula : Type uFormula}
    (closure : ClosureOperator (Set Formula)) :
    ContextualEvidenceFibre.{uFormula, uFormula, uFormula, 0} where
  base := base Formula
  Claim := fun _ => Formula
  Accepted := fun context =>
    Sigma fun formula => PLift (formula ∈ closure context.formulas)
  claimOf := Sigma.fst
  reindexClaim := fun _ claim => claim
  reindexAccepted := by
    intro source target substitution accepted
    exact ⟨accepted.1, ⟨closure.monotone substitution.down accepted.2.down⟩⟩
  claimOf_reindex := by intro source target substitution accepted; rfl
  reindexClaim_id := by intro context claim; rfl
  reindexClaim_comp := by intro first second third earlier later claim; rfl
  reindexAccepted_id := by
    intro context accepted
    apply Sigma.ext rfl
    exact heq_of_eq ((pliftProp_subsingleton _).elim _ _)
  reindexAccepted_comp := by
    intro first second third earlier later accepted
    apply Sigma.ext rfl
    exact heq_of_eq ((pliftProp_subsingleton _).elim _ _)

/-- Closure inclusion gives an authority translation whose context map is the
identity.  Its interchange with weakening follows from thin proof identity. -/
noncomputable def translation {Formula : Type uFormula}
    {source target : ClosureOperator (Set Formula)}
    (map : SetEvidenceDoctrine.ClosureHom source target) :
    ContextualTranslation (fibre source) (fibre target) where
  mapContext := ContextMap.identity (base Formula)
  mapClaim := id
  mapAccepted := fun accepted =>
    ⟨accepted.1, ⟨map.preserves _ accepted.2.down⟩⟩
  projection_commutes := by intro context accepted; rfl
  claim_substitution_interchange := by
    intro sourceContext targetContext substitution claim
    rfl
  accepted_substitution_interchange := by
    intro sourceContext targetContext substitution accepted
    rcases accepted with ⟨formula, proof⟩
    apply Sigma.ext rfl
    exact heq_of_eq ((pliftProp_subsingleton _).elim _ _)

def small : Context Bool := ⟨{true}⟩
def large : Context Bool := ⟨{true, false}⟩

def includeSmallInLarge : large ⟶ small := by
  refine ⟨?_⟩
  intro formula member
  simp [small] at member
  simp [large, member]

noncomputable def smallEvidence :
    (fibre (theoremClosure (∅ : Set Bool))).Accepted small :=
  ⟨true, ⟨by simp [theoremClosure_apply, small]⟩⟩

/-- Positive structural witness: evidence from `{true}` weakens into the
larger context `{true,false}`. -/
theorem weakening_preserves_evidence :
    Nonempty ((fibre (theoremClosure (∅ : Set Bool))).Evidence large true) := by
  let transported :=
    (fibre (theoremClosure (∅ : Set Bool))).reindexAccepted
      includeSmallInLarge smallEvidence
  exact ⟨⟨transported, rfl⟩⟩

end StructuralContextGuest

/-! ### An occurrence-preserving resource guest -/

namespace ResourceContextGuest

/-- Only the number of resource occurrences is fixed here; a morphism below
must biject their positions. -/
structure Context where
  slots : Nat
deriving DecidableEq

/-- A resource substitution is a permutation/bijection of occurrences.  It
can exchange slots but cannot silently copy or discard one. -/
def Hom (source target : Context) : Type :=
  Fin target.slots ≃ Fin source.slots

instance : Quiver Context where
  Hom := Hom

instance : CategoryTheory.Category.{0} Context where
  id := fun context => Equiv.refl (Fin context.slots)
  comp earlier later := later.trans earlier
  id_comp morphism := by apply Equiv.ext; intro index; rfl
  comp_id morphism := by apply Equiv.ext; intro index; rfl
  assoc first second third := by apply Equiv.ext; intro index; rfl

def base : ContextBase.{0, 0} where
  Context := Context
  category := inferInstance

/-- Evidence is one retained resource occurrence. -/
def fibre : ContextualEvidenceFibre.{0, 0, 0, 0} where
  base := base
  Claim := fun _ => Unit
  Accepted := fun context => Fin context.slots
  claimOf := fun _ => ()
  reindexClaim := fun _ claim => claim
  reindexAccepted := by
    intro source target substitution accepted
    change Hom source target at substitution
    exact substitution.toFun accepted
  claimOf_reindex := by intro source target substitution accepted; rfl
  reindexClaim_id := by intro context claim; rfl
  reindexClaim_comp := by intro first second third earlier later claim; rfl
  reindexAccepted_id := by intro context accepted; rfl
  reindexAccepted_comp := by
    intro first second third earlier later accepted
    rfl

/-- A second authority over the same resource contexts retains an additional
provenance tag while leaving occurrence transport unchanged. -/
def taggedFibre : ContextualEvidenceFibre.{0, 0, 0, 0} where
  base := base
  Claim := fun _ => Unit
  Accepted := fun context => Fin context.slots × Bool
  claimOf := fun _ => ()
  reindexClaim := fun _ claim => claim
  reindexAccepted := by
    intro source target substitution accepted
    change Hom source target at substitution
    exact (substitution.toFun accepted.1, accepted.2)
  claimOf_reindex := by intro source target substitution accepted; rfl
  reindexClaim_id := by intro context claim; rfl
  reindexClaim_comp := by intro first second third earlier later claim; rfl
  reindexAccepted_id := by intro context accepted; rfl
  reindexAccepted_comp := by
    intro first second third earlier later accepted
    rfl

/-- Authority enrichment commutes with every occurrence-preserving resource
substitution. -/
def taggingTranslation : ContextualTranslation fibre taggedFibre where
  mapContext := ContextMap.identity base
  mapClaim := id
  mapAccepted := fun occurrence => (occurrence, false)
  projection_commutes := by intro context occurrence; rfl
  claim_substitution_interchange := by
    intro source target substitution claim
    rfl
  accepted_substitution_interchange := by
    intro source target substitution occurrence
    rfl

def two : Context := ⟨2⟩
def one : Context := ⟨1⟩

def swap : two ⟶ two := Equiv.swap (0 : Fin 2) (1 : Fin 2)

/-- Positive resource witness: the guest admits a genuine exchange of two
distinct occurrences. -/
theorem swap_moves_first_occurrence :
    fibre.reindexAccepted swap (0 : Fin 2) = (1 : Fin 2) := by
  change swap.toFun (0 : Fin 2) = (1 : Fin 2)
  simp [swap]

/-- Positive two-axis witness: tag enrichment and the nontrivial resource
swap commute. -/
theorem tagging_commutes_with_swap :
    taggedFibre.reindexAccepted swap
        (taggingTranslation.mapAccepted (0 : Fin 2)) =
      taggingTranslation.mapAccepted
        (fibre.reindexAccepted swap (0 : Fin 2)) :=
  taggingTranslation.mapAccepted_reindex swap (0 : Fin 2)

/-- Negative authority witness: forward enrichment deliberately does not
cover evidence carrying the other provenance tag. -/
theorem tagging_not_surjective_at_two :
    ¬ Function.Surjective
      (fun occurrence : fibre.Accepted two =>
        (taggingTranslation.mapAccepted occurrence :
          taggedFibre.Accepted two)) := by
  intro surjective
  obtain ⟨occurrence, equality⟩ :=
    surjective ((0 : Fin 2), true)
  have tagEquality := congrArg Prod.snd equality
  change false = true at tagEquality
  cases tagEquality

/-- Negative resource witness: no substitution duplicates one occurrence into
two. -/
theorem no_resource_duplication :
    ¬ Nonempty (one ⟶ two) := by
  rintro ⟨bijection⟩
  have cardinality := Fintype.card_congr bijection
  change 2 = 1 at cardinality
  omega

/-- Negative resource witness: no substitution discards one of two
occurrences either. -/
theorem no_resource_discard :
    ¬ Nonempty (two ⟶ one) := by
  rintro ⟨bijection⟩
  have cardinality := Fintype.card_congr bijection
  change 1 = 2 at cardinality
  omega

end ResourceContextGuest

/-! ## Terminal-base comprehension obstruction -/

/-- The part of CwF comprehension that remains after specializing the context
category to the terminal category.  Its generic-variable equation says that
the sole pairing map sends the generic term to every supplied term. -/
structure TerminalBaseComprehension
    (Ty : Type uFormula) (Tm : Ty → Type uEvidence) where
  generic : (type : Ty) → Tm type
  generic_after_unique_pair : ∀ (type : Ty) (term : Tm type),
    generic type = term

/-- Terminal-base comprehension forces every term fibre to be a subsingleton. -/
theorem terminalCwF_term_fibre_subsingleton
    {Ty : Type uFormula} {Tm : Ty → Type uEvidence}
    (comprehension : TerminalBaseComprehension Ty Tm) (type : Ty) :
    Subsingleton (Tm type) where
  allEq left right :=
    (comprehension.generic_after_unique_pair type left).symm.trans
      (comprehension.generic_after_unique_pair type right)

/-- Singleton term fibres give a positive terminal-base comprehension model. -/
def unitTerminalBaseComprehension (Ty : Type uFormula) :
    TerminalBaseComprehension Ty (fun _ => Unit) where
  generic _ := ()
  generic_after_unique_pair _ term := Subsingleton.elim () term

/-- A multiply inhabited term fibre rules out terminal-base comprehension. -/
theorem boolTerms_have_no_terminalBaseComprehension :
    ¬ Nonempty (TerminalBaseComprehension Unit (fun _ => Bool)) := by
  rintro ⟨comprehension⟩
  have subsingleton := terminalCwF_term_fibre_subsingleton comprehension ()
  have impossible : false = true := subsingleton.elim _ _
  cases impossible

/-- An empty term fibre also rules out terminal-base comprehension because a
generic variable would have to inhabit it. -/
theorem emptyTerms_have_no_terminalBaseComprehension :
    ¬ Nonempty (TerminalBaseComprehension Unit (fun _ => Empty)) := by
  rintro ⟨comprehension⟩
  exact nomatch comprehension.generic ()

/-! ## Exact replay transport versus semantic transport -/

/-- The Boolean-replay part of a checker translation, without separately
stored certified-scope or guest-meaning obligations. -/
structure ExactReplayTranslation
    {Kind : Type uKind}
    (family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind)
    (source target : Kind) where
  mapClaim : family.Claim source → family.Claim target
  mapCertificate : family.Certificate source → family.Certificate target
  check_commutes : ∀ claim certificate,
    (family.checker target).check (mapClaim claim) (mapCertificate certificate) =
      (family.checker source).check claim certificate

/-- Exact replay plus exact source and target authority makes certified-scope
preservation derivable; it need not be stored as independent data. -/
theorem ExactReplayTranslation.certified_preserved
    {Kind : Type uKind}
    {family : AuthorityFamily.{uKind, uClaim, uCertificate} Kind}
    {source target : Kind}
    (translation : ExactReplayTranslation family source target)
    {claim : family.Claim source}
    (certified : family.Certified source claim) :
    family.Certified target (translation.mapClaim claim) := by
  obtain ⟨certificate, accepted⟩ :=
    (family.projection source).authority.complete claim certified
  apply (family.projection target).authority.sound
    (translation.mapClaim claim) (translation.mapCertificate certificate)
  rw [translation.check_commutes]
  exact accepted

namespace MeaningGapCanary

/-- Both fibres replay exactly the Boolean truth claim.  The source projects
that scope into a deliberately broader meaning; the target does not. -/
def family : AuthorityFamily Bool where
  Claim := fun _ => Bool
  Certificate := fun _ => Unit
  checker := fun _ => { check := fun claim _ => claim }
  Certified := fun _ claim => claim = true
  Meaning
    | false => fun _ => True
    | true => fun claim => claim = true
  projection := by
    intro kind
    cases kind with
    | false =>
        exact
          { authority :=
              { sound := by
                  intro claim certificate accepted
                  simpa using accepted
                complete := by
                  intro claim certified
                  exact ⟨(), by simpa using certified⟩ }
            project := by intro claim certified; trivial }
    | true =>
        exact
          { authority :=
              { sound := by
                  intro claim certificate accepted
                  simpa using accepted
                complete := by
                  intro claim certified
                  exact ⟨(), by simpa using certified⟩ }
            project := by intro claim certified; exact certified }

def replayTranslation : ExactReplayTranslation family false true where
  mapClaim := id
  mapCertificate := id
  check_commutes := by intro claim certificate; rfl

/-- Certified scope transports, but preservation of the broader authored
`Meaning` predicate is genuinely extra structure. -/
theorem replay_does_not_determine_meaning_preservation :
    ¬ ∀ claim, family.Meaning false claim →
      family.Meaning true (replayTranslation.mapClaim claim) := by
  intro preservation
  have impossible := preservation false trivial
  simp [family, replayTranslation] at impossible

end MeaningGapCanary

/-! ## A finite meta-authority for checker refinement -/

namespace RefinementMetaAuthority

/-- A small executable checker interface used as the object language of the
meta-authority.  Both inputs are finite, so refinement can be checked by four
explicit rows. -/
structure BinaryChecker where
  run : Bool → Bool → Bool

/-- The meta-level claim is one-way acceptance preservation. -/
structure Claim where
  source : BinaryChecker
  target : BinaryChecker

/-- Authored meaning is extensional refinement, independently of the
certificate format and replay function. -/
def Refines (claim : Claim) : Prop :=
  ∀ input certificate,
    claim.source.run input certificate = true →
      claim.target.run input certificate = true

/-- One retained Boolean result for each point of the finite input space. -/
structure Certificate where
  ff : Bool
  ft : Bool
  tf : Bool
  tt : Bool
deriving DecidableEq

/-- Boolean implication for one source/target acceptance row. -/
def row (source target : Bool) : Bool := !source || target

theorem row_eq_true_iff (source target : Bool) :
    row source target = true ↔ (source = true → target = true) := by
  cases source <;> cases target <;> simp [row]

/-- A certificate is valid when every retained row is the row recomputed from
the two checkers and that row establishes acceptance preservation. -/
def CellValid (retained source target : Bool) : Prop :=
  retained = row source target ∧ retained = true

def ValidCertificate (claim : Claim) (certificate : Certificate) : Prop :=
  CellValid certificate.ff
      (claim.source.run false false) (claim.target.run false false) ∧
    CellValid certificate.ft
      (claim.source.run false true) (claim.target.run false true) ∧
    CellValid certificate.tf
      (claim.source.run true false) (claim.target.run true false) ∧
    CellValid certificate.tt
      (claim.source.run true true) (claim.target.run true true)

instance (claim : Claim) (certificate : Certificate) :
    Decidable (ValidCertificate claim certificate) := by
  unfold ValidCertificate CellValid
  infer_instance

/-- Replay is a finite truth-table computation.  It does not call `Refines`
or identify semantic meaning with acceptance by definition. -/
def checker : Checker Claim Certificate where
  check claim certificate := decide (ValidCertificate claim certificate)

theorem checker_sound : checker.Sound Refines := by
  intro claim certificate accepted
  have valid : ValidCertificate claim certificate :=
    of_decide_eq_true accepted
  intro input evidence sourceAccepted
  cases input <;> cases evidence
  · exact (row_eq_true_iff _ _).mp
      (valid.1.1.symm.trans valid.1.2) sourceAccepted
  · exact (row_eq_true_iff _ _).mp
      (valid.2.1.1.symm.trans valid.2.1.2) sourceAccepted
  · exact (row_eq_true_iff _ _).mp
      (valid.2.2.1.1.symm.trans valid.2.2.1.2) sourceAccepted
  · exact (row_eq_true_iff _ _).mp
      (valid.2.2.2.1.symm.trans valid.2.2.2.2) sourceAccepted

def computedCertificate (claim : Claim) : Certificate where
  ff := row (claim.source.run false false) (claim.target.run false false)
  ft := row (claim.source.run false true) (claim.target.run false true)
  tf := row (claim.source.run true false) (claim.target.run true false)
  tt := row (claim.source.run true true) (claim.target.run true true)

theorem computedCertificate_valid (claim : Claim) (refines : Refines claim) :
    ValidCertificate claim (computedCertificate claim) := by
  exact ⟨⟨rfl, (row_eq_true_iff _ _).mpr (refines false false)⟩,
    ⟨rfl, (row_eq_true_iff _ _).mpr (refines false true)⟩,
    ⟨rfl, (row_eq_true_iff _ _).mpr (refines true false)⟩,
    ⟨rfl, (row_eq_true_iff _ _).mpr (refines true true)⟩⟩

theorem checker_complete : checker.CertificateComplete Refines := by
  intro claim refines
  refine ⟨computedCertificate claim, ?_⟩
  change decide (ValidCertificate claim (computedCertificate claim)) = true
  exact decide_eq_true (computedCertificate_valid claim refines)

/-- The finite meta-checker is exact for the independently stated extensional
refinement relation. -/
theorem checker_authority : checker.Authority Refines where
  sound := checker_sound
  complete := checker_complete

/-- The refinement checker is itself an ordinary NIK authority and can be
hosted without changing the raw NIK waist. -/
def family : AuthorityFamily Unit where
  Claim := fun _ => Claim
  Certificate := fun _ => Certificate
  checker := fun _ => checker
  Certified := fun _ => Refines
  Meaning := fun _ => Refines
  projection := fun _ => checker_authority.toProjection

def identityClaim (implementation : BinaryChecker) : Claim where
  source := implementation
  target := implementation

theorem identity_refines (implementation : BinaryChecker) :
    Refines (identityClaim implementation) := by
  intro input certificate accepted
  exact accepted

/-- Positive witness: the computed four-row certificate for an identity
refinement is accepted. -/
theorem identity_certificate_accepted (implementation : BinaryChecker) :
    checker.check (identityClaim implementation)
        (computedCertificate (identityClaim implementation)) = true :=
  by
    change decide (ValidCertificate (identityClaim implementation)
      (computedCertificate (identityClaim implementation))) = true
    exact decide_eq_true
      (computedCertificate_valid _ (identity_refines implementation))

def alwaysAccept : BinaryChecker where
  run := fun _ _ => true

def conjunction : BinaryChecker where
  run := fun input certificate => input && certificate

def badClaim : Claim where
  source := alwaysAccept
  target := conjunction

/-- Negative semantic witness: an always-accepting source cannot refine the
conjunctive target. -/
theorem badClaim_not_refines : ¬ Refines badClaim := by
  intro refines
  have impossible := refines false false rfl
  simp [badClaim, conjunction] at impossible

/-- Negative certificate witness: no forged truth table can make the bad
refinement pass. -/
theorem badClaim_has_no_accepted_certificate :
    ¬ ∃ certificate, checker.check badClaim certificate = true := by
  intro accepted
  exact badClaim_not_refines
    ((checker_authority.meaning_iff_exists_certificate badClaim).mpr accepted)

end RefinementMetaAuthority

/-! ## Native proof objects and exact certificate boundaries

An authority may replay traces, retain native proof terms, or recompute local
judgments.  These are independent capabilities.  In particular, merely
decoding every accepted certificate to *some* native proof does not show that
the certificate format has exactly the guest's proof relevance: an ignored
tag can survive in the certificate fibre.  The invariant below is therefore a
claim-indexed equivalence of fibres. -/

/-- A guest's native proof objects and independently stated judgment. -/
structure NativeProofSystem (Claim : Type uClaim) where
  ProofObject : Type uProof
  Judges : ProofObject → Claim → Prop

/-- An executable decision procedure whose accepted Boolean is equivalent to
an independently stated binary relation.  Guests use this for conversion,
typing, or any other deterministic judgment their native kernel recomputes. -/
structure DecidedRelation (Carrier : Type uClaim)
    (relation : Carrier → Carrier → Prop) where
  decide : Carrier → Carrier → Bool
  correct : ∀ left right, decide left right = true ↔ relation left right

/-- Native proofs of one particular claim. -/
def NativeProofSystem.ProofFibre {Claim : Type uClaim}
    (guest : NativeProofSystem.{uClaim, uProof} Claim) (claim : Claim) :=
  { proof : guest.ProofObject // guest.Judges proof claim }

/-- Certificates accepted for one particular claim. -/
def AcceptedCertificateFibre
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (claim : Claim) :=
  { certificate : Certificate // checker.check claim certificate = true }

/-- Exact preservation of proof relevance at the primary certificate
boundary.  The equivalence is fibrewise because the same raw proof syntax may
prove different claims in an extrinsic guest. -/
structure CertificateEquivalence
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (guest : NativeProofSystem.{uClaim, uProof} Claim) where
  fibreEquiv : ∀ claim,
    AcceptedCertificateFibre checker claim ≃ guest.ProofFibre claim

namespace CertificateEquivalence

variable {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {guest : NativeProofSystem.{uClaim, uProof} Claim}

/-- Exact proof-fibre preservation implies exact authority for native
theoremhood, understood as inhabitation of the guest proof fibre. -/
theorem authority (boundary : CertificateEquivalence checker guest) :
    checker.Authority (fun claim => Nonempty (guest.ProofFibre claim)) where
  sound := by
    intro claim certificate accepted
    exact ⟨CertificateEquivalence.fibreEquiv boundary claim
      ⟨certificate, accepted⟩⟩
  complete := by
    intro claim proof
    rcases proof with ⟨nativeProof⟩
    let accepted :=
      (CertificateEquivalence.fibreEquiv boundary claim).symm nativeProof
    exact ⟨accepted.1, accepted.2⟩

/-- Encode one judged native proof as accepted primary evidence. -/
def acceptedOfNative (boundary : CertificateEquivalence checker guest)
    {claim : Claim} (proof : guest.ProofFibre claim) :
    AcceptedCertificateFibre checker claim :=
  (boundary.fibreEquiv claim).symm proof

/-- Decode accepted primary evidence without erasing its proof identity. -/
def nativeOfAccepted (boundary : CertificateEquivalence checker guest)
    {claim : Claim}
    (accepted : AcceptedCertificateFibre checker claim) :
    guest.ProofFibre claim :=
  boundary.fibreEquiv claim accepted

end CertificateEquivalence

/-- The weaker decode-only condition.  It is useful for audit formats, but is
not a primary certificate-boundary theorem because distinct accepted
certificates may decode to the same native proof. -/
structure DecodableCertificateBoundary
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (guest : NativeProofSystem.{uClaim, uProof} Claim) where
  encode : guest.ProofObject → Certificate
  decode : Certificate → Option guest.ProofObject
  decode_encode : ∀ proof, decode (encode proof) = some proof
  faithful : ∀ claim proof,
    checker.check claim (encode proof) = true ↔ guest.Judges proof claim
  accepted_decodes : ∀ claim certificate,
    checker.check claim certificate = true →
      ∃ proof, decode certificate = some proof ∧ guest.Judges proof claim

/-- A native kernel computes whether a native proof object has the claimed
judgment.  Its certificate language is the guest proof language itself. -/
structure NativeProofKernel
    {Claim : Type uClaim}
    (guest : NativeProofSystem.{uClaim, uProof} Claim) where
  decide : Claim → guest.ProofObject → Bool
  correct : ∀ claim proof,
    decide claim proof = true ↔ guest.Judges proof claim

namespace NativeProofKernel

variable {Claim : Type uClaim}
    {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (kernel : NativeProofKernel guest)

/-- The computing kernel as an ordinary NIK checker. -/
def toChecker : Checker Claim guest.ProofObject where
  check := kernel.decide

/-- Direct native checking preserves the complete proof fibre, not merely
the existence of some proof. -/
def certificateEquivalence :
    CertificateEquivalence kernel.toChecker guest where
  fibreEquiv claim :=
    { toFun := fun accepted =>
        ⟨accepted.1, (kernel.correct claim accepted.1).mp accepted.2⟩
      invFun := fun proof =>
        ⟨proof.1, (kernel.correct claim proof.1).mpr proof.2⟩
      left_inv := by intro accepted; cases accepted; rfl
      right_inv := by intro proof; cases proof; rfl }

/-- A computing native proof kernel is an exact NIK authority for the
inhabited native judgment. -/
theorem authority :
    kernel.toChecker.Authority
      (fun claim => Nonempty (guest.ProofFibre claim)) :=
  CertificateEquivalence.authority kernel.certificateEquivalence

end NativeProofKernel

/-! ### A strict counterexample to decode-only parity -/

namespace CertificateBoundaryCanary

def guest : NativeProofSystem Unit where
  ProofObject := Unit
  Judges := fun _ _ => True

/-- The Boolean tag is accepted but has no native proof-level meaning. -/
def decoratedChecker : Checker Unit (Unit × Bool) where
  check := fun _ _ => true

/-- The weaker encode/decode/no-finer shape accepts this decorated format:
both tags decode to the same native proof. -/
def decodable : DecodableCertificateBoundary decoratedChecker guest where
  encode proof := (proof, false)
  decode certificate := some certificate.1
  decode_encode proof := by cases proof; rfl
  faithful claim proof := by simp [decoratedChecker, guest]
  accepted_decodes claim certificate accepted := by
    exact ⟨(), by simp [guest]⟩

/-- The extra accepted tag makes exact proof-fibre parity impossible. -/
theorem no_certificateEquivalence :
    ¬ Nonempty (CertificateEquivalence decoratedChecker guest) := by
  rintro ⟨boundary⟩
  let left : AcceptedCertificateFibre decoratedChecker () :=
    ⟨((), false), rfl⟩
  let right : AcceptedCertificateFibre decoratedChecker () :=
    ⟨((), true), rfl⟩
  have sameNative : boundary.fibreEquiv () left =
      boundary.fibreEquiv () right := by
    apply Subtype.ext
    change ((): Unit) = ()
    rfl
  have sameAccepted : left = right :=
    (boundary.fibreEquiv ()).injective sameNative
  have false_eq_true := congrArg (fun accepted => accepted.1.2) sameAccepted
  exact Bool.false_ne_true false_eq_true

/-- Positive and negative witnesses together show that decode-only parity is
strictly weaker than proof-fibre equivalence. -/
theorem decodable_but_not_exact :
    Nonempty (DecodableCertificateBoundary decoratedChecker guest) ∧
      ¬ Nonempty (CertificateEquivalence decoratedChecker guest) :=
  ⟨⟨decodable⟩, no_certificateEquivalence⟩

end CertificateBoundaryCanary

/-! ### Theorem decision and proof relevance are orthogonal -/

namespace DecisionProofCanary

def meaning (_claim : Unit) : Prop := True

def decisionKernel : Checker.DecisionKernel Unit meaning where
  decide := fun _ => true
  correct := by intro claim; simp [meaning]

/-- The direct theoremhood decision in this canary is genuinely computable;
the later loss of proof relevance is therefore independent of any
noncomputability issue. -/
theorem decisionKernel_computable :
    Computable decisionKernel.decide := by
  exact Computable.const true

/-- The native guest deliberately retains two different proof objects for its
single theorem. -/
def guest : NativeProofSystem Unit where
  ProofObject := Bool
  Judges := fun _ _ => True

/-- Positive witness: theoremhood is directly decidable with a trivial
certificate. -/
theorem decision_authority :
    decisionKernel.toChecker.Authority meaning :=
  decisionKernel.authority

/-- Negative witness: the trivial decision certificate cannot retain the
guest's two native proof objects.  Deciding theoremhood therefore does not by
itself provide proof-fibre parity. -/
theorem decision_does_not_retain_native_proofs :
    ¬ Nonempty (CertificateEquivalence decisionKernel.toChecker guest) := by
  rintro ⟨boundary⟩
  let falseProof : guest.ProofFibre () := ⟨false, trivial⟩
  let trueProof : guest.ProofFibre () := ⟨true, trivial⟩
  have sameAccepted :
      (boundary.fibreEquiv ()).symm falseProof =
        (boundary.fibreEquiv ()).symm trueProof := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have sameProof : falseProof = trueProof :=
    (boundary.fibreEquiv ()).symm.injective sameAccepted
  have false_eq_true := congrArg (fun proof => proof.1) sameProof
  exact Bool.false_ne_true false_eq_true

end DecisionProofCanary

/-! ### The native-calculus boundary has two independent axes

Direct computation and retention of native proof objects answer different
questions.  A computable decision kernel can erase a non-thin proof fibre,
while a computable certificate boundary can recognize a semidecidable
judgment for which no computable direct decision exists.  The conjunction
below is the negative guard against choosing one universal calculus face for
all guests. -/

/-- There is no valid identification of "computes theoremhood directly" with
"retains the guest's exact proof objects", nor of computable boundary replay
with computable direct decision.  Guest structure must select these two
capabilities independently. -/
theorem native_calculus_faces_are_independent :
    (Computable DecisionProofCanary.decisionKernel.decide ∧
      ¬ Nonempty
        (CertificateEquivalence
          DecisionProofCanary.decisionKernel.toChecker
          DecisionProofCanary.guest)) ∧
    ((∃ checker : Checker Nat.Partrec.Code Nat,
        Computable (fun input : Nat.Partrec.Code × Nat =>
          checker.check input.1 input.2) ∧
        checker.Sound Checker.HaltingMeaning ∧
        checker.CertificateComplete Checker.HaltingMeaning) ∧
      ¬ ∃ kernel : Checker.DecisionKernel Nat.Partrec.Code
          Checker.HaltingMeaning,
        Computable kernel.decide) := by
  exact
    ⟨⟨DecisionProofCanary.decisionKernel_computable,
        DecisionProofCanary.decision_does_not_retain_native_proofs⟩,
      Checker.computable_certificate_authority_without_computable_decision⟩

/-! ### Native proof composition through a clone -/

/-! #### Operational derivations as an optional native proof algebra

The raw NIK waist does not impose a clone.  A guest whose admitted operations
are unary state transitions can nevertheless obtain one canonically: a native
derivation is either an already-admitted seed, a selected premise occurrence,
or one more retained transition.  Substitution plugs derivations into premise
occurrences; it never replays or revalidates their interiors. -/

/-- Proof-relevant derivations generated by admitted seeds and unary
operational steps.  This is an optional cartesian guest above raw NIK, not
structure imposed on resource-sensitive authorities. -/
inductive OperationalDerivation
    {State : Type uFormula}
    (Step : State → State → Type uEvidence)
    (Seed : State → Type uProof) :
    List State → State → Type (max uFormula uEvidence uProof) where
  | assumption {context : List State}
      (index : Fin context.length) :
      OperationalDerivation Step Seed context (context.get index)
  | admittedSeed {context : List State} {target : State}
      (evidence : Seed target) :
      OperationalDerivation Step Seed context target
  | advance {context : List State} {source target : State}
      (prior : OperationalDerivation Step Seed context source)
      (step : Step source target) :
      OperationalDerivation Step Seed context target

namespace OperationalDerivation

/-- Plug a shared environment of native derivations into every open premise.
Admitted seeds and steps are retained directly. -/
def bind
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {sourceContext targetContext : List State} {target : State}
    (derivation : OperationalDerivation Step Seed sourceContext target)
    (environment : (index : Fin sourceContext.length) →
      OperationalDerivation Step Seed targetContext
        (sourceContext.get index)) :
    OperationalDerivation Step Seed targetContext target :=
  match derivation with
  | .assumption index => environment index
  | .admittedSeed evidence => .admittedSeed evidence
  | .advance prior step => .advance (bind prior environment) step

@[simp] theorem bind_assumption
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {sourceContext targetContext : List State}
    (environment : (index : Fin sourceContext.length) →
      OperationalDerivation Step Seed targetContext
        (sourceContext.get index))
    (index : Fin sourceContext.length) :
    bind (.assumption index) environment = environment index :=
  rfl

@[simp] theorem bind_assumptions
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {context : List State} {target : State}
    (derivation : OperationalDerivation Step Seed context target) :
    bind derivation (fun index => .assumption index) = derivation := by
  induction derivation with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp [bind, inductionHypothesis]

@[simp] theorem bind_assoc
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {firstContext secondContext thirdContext : List State}
    {target : State}
    (derivation : OperationalDerivation Step Seed firstContext target)
    (first : (index : Fin firstContext.length) →
      OperationalDerivation Step Seed secondContext
        (firstContext.get index))
    (second : (index : Fin secondContext.length) →
      OperationalDerivation Step Seed thirdContext
        (secondContext.get index)) :
    bind (bind derivation first) second =
      bind derivation (fun index => bind (first index) second) := by
  induction derivation with
  | assumption => rfl
  | admittedSeed => rfl
  | advance prior step inductionHypothesis =>
      simp [bind, inductionHypothesis]

/-- Semantic soundness is paid once for seeds and step constructors, then
flows through every composed native derivation without consulting a checker. -/
theorem sound
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {Meaning : State → Prop}
    (seedSound : ∀ {claim}, Seed claim → Meaning claim)
    (stepSound : ∀ {source target}, Step source target →
      Meaning source → Meaning target)
    {context : List State} {target : State}
    (derivation : OperationalDerivation Step Seed context target)
    (premises : ∀ index : Fin context.length,
      Meaning (context.get index)) :
    Meaning target := by
  induction derivation with
  | assumption index => exact premises index
  | admittedSeed evidence => exact seedSound evidence
  | advance prior step inductionHypothesis =>
      exact stepSound step inductionHypothesis

end OperationalDerivation

/-- The native substitution algebra of an operational guest. -/
def operationalDerivationClone
    {State : Type uFormula}
    (Step : State → State → Type uEvidence)
    (Seed : State → Type uProof) :
    MultiSortedClone.{uFormula, max uFormula uEvidence uProof} State where
  Hom := OperationalDerivation Step Seed
  project := .assumption
  substitute := OperationalDerivation.bind
  substitute_project := by intros; rfl
  substitute_projects := OperationalDerivation.bind_assumptions
  substitute_assoc := OperationalDerivation.bind_assoc

/-- One retained operational rule, with its endpoints indexed in the type. -/
structure OperationalRule
    {State : Type uFormula}
    (Step : State → State → Type uEvidence) where
  source : State
  target : State
  step : Step source target

/-- Uniform raw proof objects for a clone: a closed operation retains its
output judgment as part of the raw object. -/
def cloneNativeProofSystem {Sorts : Type uFormula}
    (clone : MultiSortedClone.{uFormula, uEvidence} Sorts) :
    NativeProofSystem.{uFormula, max uFormula uEvidence} Sorts where
  ProofObject := Sigma fun output => clone.Hom [] output
  Judges := fun proof output => proof.1 = output

/-- Closed clone operations are exactly the judged native proof fibre. -/
def closedProofFibreEquiv {Sorts : Type uFormula}
    (clone : MultiSortedClone.{uFormula, uEvidence} Sorts) (output : Sorts) :
    clone.Hom [] output ≃ (cloneNativeProofSystem clone).ProofFibre output where
  toFun proof := ⟨⟨output, proof⟩, rfl⟩
  invFun proof := proof.2 ▸ proof.1.2
  left_inv proof := rfl
  right_inv proof := by
    rcases proof with ⟨⟨actualOutput, proof⟩, equality⟩
    cases equality
    rfl

/-- An intrinsically typed clone proof needs only have its retained output
index compared with the submitted claim; the derivation itself is already a
native proof object, not a replay trace. -/
def cloneNativeProofKernel {Sorts : Type uFormula} [DecidableEq Sorts]
    (clone : MultiSortedClone.{uFormula, uEvidence} Sorts) :
    NativeProofKernel (cloneNativeProofSystem clone) where
  decide output proof := decide (proof.1 = output)
  correct output proof := by
    change decide (proof.1 = output) = true ↔ proof.1 = output
    exact decide_eq_true_iff

/-- A structure-preserving map between proof-relevant clones over the same
judgment sorts.  Unlike agreement only on closed theorems, it preserves
hypotheses and simultaneous substitution. -/
structure CloneHom {Sorts : Type uFormula}
    (source target : MultiSortedClone.{uFormula, uEvidence} Sorts) where
  map : {context : List Sorts} → {output : Sorts} →
    source.Hom context output → target.Hom context output
  map_project : ∀ {context : List Sorts}
      (index : Fin context.length),
    map (source.project index) = target.project index
  map_substitute : ∀ {sourceContext targetContext : List Sorts}
      {output : Sorts} (operation : source.Hom sourceContext output)
      (environment : (index : Fin sourceContext.length) →
        source.Hom targetContext (sourceContext.get index)),
    map (source.substitute operation environment) =
      target.substitute (map operation) (fun index => map (environment index))

/-- An exact clone equivalence retains the open proof fibres and their
substitution algebra in both directions. -/
structure CloneEquivalence {Sorts : Type uFormula}
    (source target : MultiSortedClone.{uFormula, uEvidence} Sorts) where
  toHom : CloneHom source target
  invHom : CloneHom target source
  left_inv : ∀ {context : List Sorts} {output : Sorts}
      (operation : source.Hom context output),
    invHom.map (toHom.map operation) = operation
  right_inv : ∀ {context : List Sorts} {output : Sorts}
      (operation : target.Hom context output),
    toHom.map (invHom.map operation) = operation

/-! ### The common admission algebra

Proof rules, validated language transformations, compiled plans, and verified
optimizations have different payloads but the same trusted shape: an operation
between semantic fibres together with a preservation theorem.  The theorem is
retained when the operation is admitted; executing `run` does not invoke a
checker and does not consume an emitted certificate.

The fibres are explicit objects rather than a single coarse predicate.  This
is what lets a cost-decreasing optimization target a strictly smaller cost
fibre, while an exact semantic transformation remains inside one observation
fibre. -/

/-- A carrier together with the semantic invariant selecting its admissible
fibre. -/
structure AdmissionObject where
  Carrier : Type uArtifact
  Meaning : Carrier → Prop

/-- A retained operation whose admission proof says that it maps one semantic
fibre into another.  There is deliberately no certificate field: optional
emission is an observation of an admitted run, not an input to execution. -/
structure AdmissionHom (source target : AdmissionObject.{uArtifact}) where
  run : source.Carrier → target.Carrier
  preserves : ∀ value, source.Meaning value → target.Meaning (run value)

namespace AdmissionHom

@[ext]
theorem ext {source target : AdmissionObject.{uArtifact}}
    {first second : AdmissionHom source target}
    (run : first.run = second.run) : first = second := by
  cases first
  cases second
  cases run
  rfl

/-- Identity is admitted without changing either the object or its meaning. -/
def id (object : AdmissionObject.{uArtifact}) : AdmissionHom object object where
  run := _root_.id
  preserves := fun _ meaningful => meaningful

/-- Admitted operations compose in execution order, and their retained
preservation proofs compose at admission time. -/
def comp {first middle last : AdmissionObject.{uArtifact}}
    (earlier : AdmissionHom first middle)
    (later : AdmissionHom middle last) : AdmissionHom first last where
  run := later.run ∘ earlier.run
  preserves := fun value meaningful =>
    later.preserves _ (earlier.preserves value meaningful)

@[simp]
theorem id_run (object : AdmissionObject.{uArtifact}) (value : object.Carrier) :
    (id object).run value = value :=
  rfl

@[simp]
theorem comp_run {first middle last : AdmissionObject.{uArtifact}}
    (earlier : AdmissionHom first middle)
    (later : AdmissionHom middle last) (value : first.Carrier) :
    (comp earlier later).run value = later.run (earlier.run value) :=
  rfl

end AdmissionHom

/-- Meaning-preserving admission arrows form a category.  Category
composition records admission-time proof composition; evaluating a morphism
still applies only its `run` function. -/
instance : CategoryTheory.Category.{uArtifact} AdmissionObject.{uArtifact} where
  Hom := AdmissionHom
  id := AdmissionHom.id
  comp earlier later := AdmissionHom.comp earlier later
  id_comp morphism := by ext; rfl
  comp_id morphism := by ext; rfl
  assoc first second third := by ext; rfl

/-- Optional evidence exposed about an admitted execution.  Neither the
artifact type nor the observer occurs in `AdmissionHom.run`. -/
structure AdmissionEmission
    {source target : AdmissionObject.{uArtifact}}
    (operation : source ⟶ target) where
  Artifact : Type uProof
  emit : source.Carrier → target.Carrier → Artifact

namespace AdmissionCanary

/-- A nonidentity admitted endomorphism: successor preserves the positive
natural-number fibre. -/
def positiveNaturals : AdmissionObject where
  Carrier := Nat
  Meaning := fun value => value ≠ 0

def successor : positiveNaturals ⟶ positiveNaturals where
  run := Nat.succ
  preserves := fun _ _ => Nat.succ_ne_zero _

theorem successor_is_nonidentity :
    successor.run (1 : Nat) ≠
      (AdmissionHom.id positiveNaturals).run (1 : Nat) := by
  intro equality
  change Nat.succ 1 = 1 at equality
  cases equality

/-- Boolean truth is a proper semantic fibre. -/
def trueBooleans : AdmissionObject where
  Carrier := Bool
  Meaning := fun value => value = true

/-- Negative witness: arbitrary callbacks do not become admitted merely by
having the right function type.  Negation leaves the truth fibre. -/
theorem no_negation_admission :
    ¬ ∃ operation : trueBooleans ⟶ trueBooleans,
        operation.run = Bool.not := by
  rintro ⟨operation, run⟩
  have preserved := operation.preserves true rfl
  rw [run] at preserved
  simp [trueBooleans] at preserved

/-- Two optional observers may expose entirely different artifacts for the
same operation. -/
def unitEmission : AdmissionEmission successor where
  Artifact := Unit
  emit := fun _ _ => ()

def resultEmission : AdmissionEmission successor where
  Artifact := Nat
  emit := fun _ result => result

/-- Changing an emission observer cannot change execution. -/
theorem emission_does_not_control_execution
    (value : positiveNaturals.Carrier) :
    successor.run value = successor.run value ∧
      unitEmission.emit value (successor.run value) = () ∧
      resultEmission.emit value (successor.run value) = Nat.succ value := by
  simp [successor, unitEmission, resultEmission]

end AdmissionCanary

/-! ### Exact limits and bounded optimality for admitted optimizations

The common admission algebra says when a retained transformation preserves its
semantic invariant.  It does not make semantic applicability decidable, nor
does it choose a globally best costed transformation.  The negative witnesses
below isolate those two additional demands.  The positive finite-fragment
theorem then states exactly what finite enumeration does buy.

The reachability and dead-code results are computability statements.  The
`Computable` hypotheses are essential: classically chosen Boolean
characteristic functions would make bare set-theoretic nonexistence false. -/

namespace OptimizationLimits

/-- A total, computable, two-sided analysis of a semantic property of partial
recursive programs. -/
structure ExactComputableAnalysis
    (property : Nat.Partrec.Code → Prop) where
  decide : Nat.Partrec.Code → Bool
  correct : ∀ program, decide program = true ↔ property program
  computable : Computable decide

/-- The two control points needed for the reachability reduction. -/
inductive ProgramPoint where
  | entry
  | halted
  deriving DecidableEq, Repr

/-- Semantic control-flow reachability for a partial program.  Reflexive
reachability is always present; reaching the halt point from the entry point
is exactly termination of the encoded program on input zero. -/
def Reaches (program : Nat.Partrec.Code) : ProgramPoint → ProgramPoint → Prop
  | source, target =>
      source = target ∨
        (source = .entry ∧ target = .halted ∧
          Checker.HaltingMeaning program)

/-- The program's halt point is reachable from its entry point. -/
def HaltPointReachable (program : Nat.Partrec.Code) : Prop :=
  Reaches program .entry .halted

theorem haltPointReachable_iff (program : Nat.Partrec.Code) :
    HaltPointReachable program ↔ Checker.HaltingMeaning program := by
  simp [HaltPointReachable, Reaches]

/-- No total computable analysis exactly decides reachability of the halt
point for every partial-recursive program. -/
theorem NoCompleteReachabilityAnalysis :
    ¬ Nonempty (ExactComputableAnalysis HaltPointReachable) := by
  rintro ⟨analysis⟩
  apply Checker.no_computableDecisionKernel_for_halting
  refine ⟨
    { decide := analysis.decide
      correct := fun program =>
        (analysis.correct program).trans (haltPointReachable_iff program) },
    analysis.computable⟩

/-- Reachability remains exactly semidecidable by finite execution budgets:
accepted budgets are sound, and every reachable halt point has some accepted
budget.  This is the positive boundary counterpart to the absence of a total
computable decision. -/
def reachabilityBudgetAuthority :
    Checker.haltingTrustBoundaryChecker.Authority HaltPointReachable where
  sound := by
    intro program budget accepted
    exact (haltPointReachable_iff program).mpr
      (Checker.haltingTrustBoundaryChecker_sound program budget accepted)
  complete := by
    intro program reachable
    exact Checker.haltingTrustBoundaryChecker_complete program
      ((haltPointReachable_iff program).mp reachable)

/-- A block guarded by termination is dead exactly when the halt point is not
reachable. -/
def HaltBlockDead (program : Nat.Partrec.Code) : Prop :=
  ¬ HaltPointReachable program

/-- An exact computable dead-code eliminator would decide nontermination and,
by Boolean complementation, termination. -/
theorem NoCompleteDeadCodeEliminator :
    ¬ Nonempty (ExactComputableAnalysis HaltBlockDead) := by
  rintro ⟨analysis⟩
  apply Checker.no_computableDecisionKernel_for_halting
  let kernel : Checker.DecisionKernel Nat.Partrec.Code Checker.HaltingMeaning :=
    { decide := fun program => !(analysis.decide program)
      correct := by
        intro program
        constructor
        · intro accepted
          by_contra doesNotHalt
          have dead : HaltBlockDead program := by
            exact fun reachable =>
              doesNotHalt ((haltPointReachable_iff program).mp reachable)
          have markedDead : analysis.decide program = true :=
            (analysis.correct program).mpr dead
          simp [markedDead] at accepted
        · intro halts
          have reachable : HaltPointReachable program :=
            (haltPointReachable_iff program).mpr halts
          cases marked : analysis.decide program with
          | false => simp
          | true =>
              have dead : HaltBlockDead program :=
                (analysis.correct program).mp marked
              exact (dead reachable).elim }
  refine ⟨kernel, ?_⟩
  simpa [kernel, Function.comp_def] using
    (Primrec.not.to_comp.comp analysis.computable)

/-- A property-directed optimizer is an admitted transformation plus an exact
computable recognizer for the programs to which the specialization applies.
The retained transformation itself contains no certificate or replay path. -/
def propertyProgramObject (property : Nat.Partrec.Code → Prop) :
    AdmissionObject where
  Carrier := Nat.Partrec.Code
  Meaning := property

structure PropertyDirectedOptimizer
    (property : Nat.Partrec.Code → Prop) where
  optimize : propertyProgramObject property ⟶ propertyProgramObject property
  applicability : ExactComputableAnalysis property

/-- Admission of a transformation does not make an undecidable semantic
applicability condition decidable. -/
theorem NoCompletePropertyDirectedOptimizer :
    ¬ Nonempty (PropertyDirectedOptimizer HaltPointReachable) := by
  rintro ⟨optimizer⟩
  exact NoCompleteReachabilityAnalysis ⟨optimizer.applicability⟩

/-- A meaning-preserving admitted transformation equipped with an external
natural-valued cost model.  The cost model measures execution; it is not an
input to `operation.run`. -/
structure CostedAdmission
    (source target : AdmissionObject.{uArtifact}) where
  operation : source ⟶ target
  cost : source.Carrier → Nat

/-- Total cost of one admitted compiler on an explicitly bounded input
fragment. -/
def fragmentCost
    {source target : AdmissionObject.{uArtifact}}
    (compiler : CostedAdmission source target)
    (fragment : Finset source.Carrier) : Nat :=
  ∑ input ∈ fragment, compiler.cost input

/-- One compiler is pointwise optimal in a family when it costs no more than
every family member on every semantically admitted source value. -/
def PointwiseOptimal
    {source target : AdmissionObject.{uArtifact}} {index : Type*}
    (family : index → CostedAdmission source target) (chosen : index) : Prop :=
  ∀ candidate input, source.Meaning input →
    (family chosen).cost input ≤ (family candidate).cost input

/-- A concrete nonidentity admitted compiler family with an indefinitely
advancing optimization frontier.  Every member runs successor on the positive
natural fibre; index `n` gives zero cost below threshold `n` and unit cost
elsewhere. -/
def thresholdCost (threshold input : Nat) : Nat :=
  if input < threshold then 0 else 1

def thresholdCompiler (threshold : Nat) :
    CostedAdmission AdmissionCanary.positiveNaturals
      AdmissionCanary.positiveNaturals where
  operation := AdmissionCanary.successor
  cost := thresholdCost threshold

/-- The infinite threshold family has no pointwise optimal member: candidate
`n + 2` strictly improves candidate `n` at the admitted input `n + 1`.
Consequently, invariant-preserving admission alone cannot supply a universal
optimal compiler theorem. -/
theorem NoUniversalOptimalCompiler :
    ¬ ∃ chosen : Nat, PointwiseOptimal thresholdCompiler chosen := by
  rintro ⟨chosen, optimal⟩
  have meaningful :
      AdmissionCanary.positiveNaturals.Meaning (chosen + 1) := by
    change chosen + 1 ≠ 0
    omega
  have comparison := optimal (chosen + 2) (chosen + 1) meaningful
  have chosenCost :
      (thresholdCompiler chosen).cost (chosen + 1) = 1 := by
    simp only [thresholdCompiler, thresholdCost]
    split
    · rename_i impossible
      omega
    · rfl
  have laterCost :
      (thresholdCompiler (chosen + 2)).cost (chosen + 1) = 0 := by
    simp only [thresholdCompiler, thresholdCost]
    split
    · rfl
    · rename_i impossible
      omega
  rw [chosenCost, laterCost] at comparison
  omega

/-- Finite candidate enumeration and a finite input fragment always admit a
minimum-total-cost admitted compiler.  This is the precise positive result:
soundness is universal because every candidate is an `AdmissionHom`, while
optimality is asserted only for the explicitly bounded candidate and input
sets. -/
theorem FiniteFragmentOptimalCompilation
    {source target : AdmissionObject.{uArtifact}}
    {index : Type*} [Fintype index] [Nonempty index]
    (family : index → CostedAdmission source target)
    (fragment : Finset source.Carrier) :
    ∃ chosen : index, ∀ candidate : index,
      fragmentCost (family chosen) fragment ≤
        fragmentCost (family candidate) fragment := by
  classical
  obtain ⟨chosen, _, minimal⟩ :=
    Finset.exists_min_image Finset.univ
      (fun candidate => fragmentCost (family candidate) fragment)
      Finset.univ_nonempty
  exact ⟨chosen, fun candidate => minimal candidate (Finset.mem_univ candidate)⟩

/-- A two-candidate, two-input positive canary.  It exercises the bounded
optimality theorem on nonidentity admitted transformations rather than on an
empty family. -/
theorem finiteThresholdFragment_has_optimal_compiler :
    ∃ chosen : Fin 2, ∀ candidate : Fin 2,
      fragmentCost (thresholdCompiler chosen.val) ({1, 2} : Finset Nat) ≤
        fragmentCost (thresholdCompiler candidate.val) ({1, 2} : Finset Nat) :=
  FiniteFragmentOptimalCompilation
    (family := fun chosen : Fin 2 => thresholdCompiler chosen.val)
    (fragment := ({1, 2} : Finset Nat))

/-- Audit bundle for the optimization boundary.  Exact global reachability,
dead-code, property-directed applicability, and universal pointwise
optimality all fail in the exhibited computable families; exact boundary
checking and finite-fragment optimal selection remain positively available.
Keeping both sides in one theorem prevents the impossibility results from
being misread as a barrier to certified specialization. -/
theorem impossibility_ladder_and_bounded_frontier :
    (¬ Nonempty (ExactComputableAnalysis HaltPointReachable)) ∧
    Checker.haltingTrustBoundaryChecker.Authority HaltPointReachable ∧
    (¬ Nonempty (ExactComputableAnalysis HaltBlockDead)) ∧
    (¬ Nonempty (PropertyDirectedOptimizer HaltPointReachable)) ∧
    (¬ ∃ chosen : Nat, PointwiseOptimal thresholdCompiler chosen) ∧
    (∃ chosen : Fin 2, ∀ candidate : Fin 2,
      fragmentCost (thresholdCompiler chosen.val) ({1, 2} : Finset Nat) ≤
        fragmentCost (thresholdCompiler candidate.val)
          ({1, 2} : Finset Nat)) := by
  exact
    ⟨NoCompleteReachabilityAnalysis,
      reachabilityBudgetAuthority,
      NoCompleteDeadCodeEliminator,
      NoCompletePropertyDirectedOptimizer,
      NoUniversalOptimalCompiler,
      finiteThresholdFragment_has_optimal_compiler⟩

end OptimizationLimits

/-- Admitted proof operations with their semantic preservation law.  The
clone operation is retained, rather than replaced by an opaque callback. -/
structure AdmittedCloneRules {Sorts : Type uFormula}
    (clone : MultiSortedClone.{uFormula, uEvidence} Sorts)
    (Meaning : Sorts → Prop) where
  Rule : Type uProof
  premises : Rule → List Sorts
  conclusion : Rule → Sorts
  operation : (rule : Rule) → clone.Hom (premises rule) (conclusion rule)
  preserves : ∀ (rule : Rule),
    (∀ index : Fin (premises rule).length,
      Meaning ((premises rule).get index)) →
    Meaning (conclusion rule)

/-- Apply one admitted operation to closed native proof objects.  This is
proof substitution, not replay of the proofs' construction histories. -/
def AdmittedCloneRules.applyClosed
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule)
    (proofs : (index : Fin (rules.premises rule).length) →
      clone.Hom [] ((rules.premises rule).get index)) :
    clone.Hom [] (rules.conclusion rule) :=
  clone.substitute (rules.operation rule) proofs

/-- The one-step flow theorem: once an operation is admitted as
truth-preserving, applying it to meaningful premise proofs produces a
meaningful conclusion with no further semantic recheck. -/
theorem AdmittedCloneRules.applyClosed_sound
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule)
    (_proofs : (index : Fin (rules.premises rule).length) →
      clone.Hom [] ((rules.premises rule).get index))
    (premisesMeaning : ∀ index : Fin (rules.premises rule).length,
      Meaning ((rules.premises rule).get index)) :
    Meaning (rules.conclusion rule) :=
  rules.preserves rule premisesMeaning

/-- The semantic admission object of the closed premise environment for one
clone rule.  The dependent function type retains the exact premise claims and
their occurrence indices. -/
def AdmittedCloneRules.closedPremiseObject
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule) : AdmissionObject where
  Carrier := (index : Fin (rules.premises rule).length) →
    clone.Hom [] ((rules.premises rule).get index)
  Meaning := fun _ => ∀ index : Fin (rules.premises rule).length,
    Meaning ((rules.premises rule).get index)

/-- The semantic admission object of the closed conclusion-proof fibre. -/
def AdmittedCloneRules.closedConclusionObject
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule) : AdmissionObject where
  Carrier := clone.Hom [] (rules.conclusion rule)
  Meaning := fun _ => Meaning (rules.conclusion rule)

/-- Every admitted clone rule is an arrow in the common admission algebra.
Its execution is native proof substitution; `applyClosed_sound` is retained
as the admission proof rather than rerun as a checker. -/
def AdmittedCloneRules.toAdmissionHom
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule) :
    rules.closedPremiseObject rule ⟶ rules.closedConclusionObject rule where
  run := rules.applyClosed rule
  preserves := fun proofs premisesMeaning =>
    rules.applyClosed_sound rule proofs premisesMeaning

@[simp]
theorem AdmittedCloneRules.toAdmissionHom_run
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (rules : AdmittedCloneRules.{uFormula, uEvidence, uProof} clone Meaning)
    (rule : rules.Rule)
    (proofs : (index : Fin (rules.premises rule).length) →
      clone.Hom [] ((rules.premises rule).get index)) :
    (rules.toAdmissionHom rule).run proofs = rules.applyClosed rule proofs :=
  rfl

/-- A semantic interpretation of all closed proof objects of a clone.  For a
presented calculus this is established by induction over its native
derivations; it is not supplied by the raw NIK waist. -/
structure SoundClone
    {Sorts : Type uFormula}
    (clone : MultiSortedClone.{uFormula, uEvidence} Sorts)
    (Meaning : Sorts → Prop) where
  closed_sound : ∀ {claim}, clone.Hom [] claim → Meaning claim

/-- Every semantically preserving operational relation gives an admitted
one-premise rule family over its native derivation clone. -/
def operationalAdmittedRules
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {Meaning : State → Prop}
    (stepSound : ∀ {source target}, Step source target →
      Meaning source → Meaning target) :
    AdmittedCloneRules
      (operationalDerivationClone Step Seed) Meaning where
  Rule := OperationalRule Step
  premises rule := [rule.source]
  conclusion rule := rule.target
  operation rule := by
    let prior : OperationalDerivation Step Seed [rule.source] rule.source :=
      @OperationalDerivation.assumption State Step Seed [rule.source]
        (0 : Fin 1)
    exact .advance prior rule.step
  preserves := by
    intro rule premiseMeaning
    exact stepSound rule.step (premiseMeaning (0 : Fin 1))

/-- The entire operational clone is sound once its seed and one-step laws are
admitted.  No checker invocation occurs in this induction. -/
def operationalSoundClone
    {State : Type uFormula}
    {Step : State → State → Type uEvidence}
    {Seed : State → Type uProof}
    {Meaning : State → Prop}
    (seedSound : ∀ {claim}, Seed claim → Meaning claim)
    (stepSound : ∀ {source target}, Step source target →
      Meaning source → Meaning target) :
    SoundClone (operationalDerivationClone Step Seed) Meaning where
  closed_sound := by
    intro claim proof
    change OperationalDerivation Step Seed [] claim at proof
    exact @OperationalDerivation.sound State Step Seed Meaning
      seedSound stepSound [] claim proof
      (fun impossible => Fin.elim0 impossible)

/-- CertificateGSLT's actual open-derivation clone is semantically sound whenever
the admitted presentation rules are sound.  This is the concrete native
proof-object flow theorem: semantic validity follows by induction over the
typed derivation, not by replaying a separate trace language. -/
def CertificateGSLTCloneCanary.soundClone
    (object : CertificateGSLT.Object)
    (Meaning : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleApplication
        object.presentation ruleInstance premises conclusion →
      (∀ premise ∈ premises, Meaning premise) → Meaning conclusion) :
    SoundClone (CertificateGSLT.derivationClone object) Meaning where
  closed_sound proof :=
    CertificateGSLT.OpenDerivation.sound_of_ruleApplications Meaning ruleSound
      (by simp) proof

/-- CertificateGSLT's native open-derivation clone has a direct computing checker:
the retained conclusion index is compared with the submitted claim while the
derivation remains the certificate. -/
def CertificateGSLTCloneCanary.nativeKernel
    (object : CertificateGSLT.Object) :
    NativeProofKernel
      (cloneNativeProofSystem (CertificateGSLT.derivationClone object)) :=
  cloneNativeProofKernel (CertificateGSLT.derivationClone object)

/-- Consequently the direct CertificateGSLT checker preserves the entire native
closed-derivation fibre. -/
def CertificateGSLTCloneCanary.certificateEquivalence
    (object : CertificateGSLT.Object) :
    CertificateEquivalence
      (CertificateGSLTCloneCanary.nativeKernel object).toChecker
      (cloneNativeProofSystem (CertificateGSLT.derivationClone object)) :=
  (CertificateGSLTCloneCanary.nativeKernel object).certificateEquivalence

/-- Under a primary certificate boundary, a closed native clone proof is
promoted to accepted NIK evidence without replaying its construction tree. -/
theorem closedCloneProof_hasAcceptedCertificate
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Certificate : Type uCertificate}
    {checker : Checker Sorts Certificate}
    (boundary : CertificateEquivalence checker
      (cloneNativeProofSystem clone))
    {claim : Sorts} (proof : clone.Hom [] claim) :
    ∃ certificate, checker.check claim certificate = true := by
  let nativeProof := (closedProofFibreEquiv clone claim) proof
  let accepted := boundary.acceptedOfNative nativeProof
  exact ⟨accepted.1, accepted.2⟩

/-- A sound clone and a primary certificate boundary jointly give both
native acceptance and semantic meaning for every closed proof object. -/
theorem closedCloneProof_flows_without_recheck
    {Sorts : Type uFormula}
    {clone : MultiSortedClone.{uFormula, uEvidence} Sorts}
    {Meaning : Sorts → Prop}
    (semantics : SoundClone clone Meaning)
    {Certificate : Type uCertificate}
    {checker : Checker Sorts Certificate}
    (boundary : CertificateEquivalence checker
      (cloneNativeProofSystem clone))
    {claim : Sorts} (proof : clone.Hom [] claim) :
    (∃ certificate, checker.check claim certificate = true) ∧ Meaning claim :=
  ⟨closedCloneProof_hasAcceptedCertificate boundary proof,
    semantics.closed_sound proof⟩

/-- Concrete end-to-end witness for the proof-object tier: a closed
CertificateGSLT derivation is accepted by its direct native checker and denotes a
meaningful conclusion whenever the authored rules preserve that meaning.
No auxiliary micro-trace is introduced. -/
theorem CertificateGSLTCloneCanary.native_derivation_flows
    (object : CertificateGSLT.Object)
    (Meaning : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ruleSound : ∀ ruleInstance premises conclusion,
      Mettapedia.GSLT.LanguageDef.InferenceChecker.RuleApplication
        object.presentation ruleInstance premises conclusion →
      (∀ premise ∈ premises, Meaning premise) → Meaning conclusion)
    {claim : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (proof : (CertificateGSLT.derivationClone object).Hom [] claim) :
    (∃ certificate,
      (CertificateGSLTCloneCanary.nativeKernel object).toChecker.check
        claim certificate = true) ∧ Meaning claim :=
  closedCloneProof_flows_without_recheck
    (CertificateGSLTCloneCanary.soundClone object Meaning ruleSound)
    (CertificateGSLTCloneCanary.certificateEquivalence object) proof

/-! ## Theory, authority contract, and realization -/

/-- Authored claims, independently declared proof scope, and semantic
meaning, presented separately from a certificate format or checker.
Extensional equality of `Scope` and `Meaning` is permitted.  This dependency
direction expresses the intended construction discipline, but cannot prove
the provenance of an arbitrary instance; the canary below makes that limit
explicit. -/
structure TheoryFamily (Kind : Type uKind) where
  Signature : Type uSignature
  signatureOf : Kind → Signature
  Claim : Kind → Type uClaim
  Scope : (kind : Kind) → Claim kind → Prop
  Meaning : (kind : Kind) → Claim kind → Prop
  scope_sound : ∀ kind claim, Scope kind claim → Meaning kind claim

/-! ### Construction order is not a provenance theorem -/

namespace TheoryFamilyCanary

/-- A previously available checker whose accepted image can be used to
define a later theory's scope and meaning. -/
def priorChecker : Checker Bool Unit where
  check claim _certificate := claim

/-- This is a well-typed theory family even though both predicates are
defined from a checker.  Consequently, `TheoryFamily` alone must not be sold
as a proof of checker-independent semantics. -/
def checkerDefinedTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ claim => ∃ certificate, priorChecker.check claim certificate = true
  Meaning := fun _ claim => ∃ certificate, priorChecker.check claim certificate = true
  scope_sound := fun _ _ proof => proof

/-- Definitional witness for the constructional limitation: this theory's
meaning predicate is exactly the prior checker's accepted image. -/
theorem checkerDefinedTheory_meaning_iff_accepted (claim : Bool) :
    checkerDefinedTheory.Meaning () claim ↔
      ∃ certificate, priorChecker.check claim certificate = true :=
  Iff.rfl

/-- The canary is not vacuous: the checker-derived theory still rejects a
concrete false claim. -/
theorem false_not_meaning : ¬ checkerDefinedTheory.Meaning () false := by
  simp [checkerDefinedTheory, priorChecker]

end TheoryFamilyCanary

/-- An exact replay contract for a theory's independently declared scope. -/
structure AuthorityContract {Kind : Type uKind}
    (theory : TheoryFamily Kind) where
  Certificate : Kind → Type uCertificate
  checker : (kind : Kind) → Checker (theory.Claim kind) (Certificate kind)
  scopeAuthority : (kind : Kind) →
    (checker kind).Authority (theory.Scope kind)

/-- Exact scope authority projects soundly to the theory's separately
authored meaning. -/
def AuthorityContract.projection
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (contract : AuthorityContract theory) (kind : Kind) :
    (contract.checker kind).AuthorityProjection
      (theory.Scope kind) (theory.Meaning kind) where
  authority := contract.scopeAuthority kind
  project := theory.scope_sound kind

/-- Recombining the first two factors recovers the live NIK authority-family
interface exactly. -/
def AuthorityContract.toAuthorityFamily
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (contract : AuthorityContract theory) :
    AuthorityFamily Kind where
  Claim := theory.Claim
  Certificate := contract.Certificate
  checker := contract.checker
  Certified := theory.Scope
  Meaning := theory.Meaning
  projection := contract.projection

/-! ### Native evidence discipline over an authored theory -/

/-- A theory-indexed native proof discipline.  `scope_iff_proof` is the
Meseguer-style theorem-image law: the independently authored scope is exactly
the image of the proof-to-claim relation. -/
structure EvidenceDiscipline
    {Kind : Type uKind} (theory : TheoryFamily Kind) where
  ProofObject : Kind → Type uProof
  Proves : (kind : Kind) → ProofObject kind → theory.Claim kind → Prop
  scope_iff_proof : ∀ kind claim,
    theory.Scope kind claim ↔
      ∃ proof, Proves kind proof claim

/-- The native proof system selected by one theory fibre. -/
def EvidenceDiscipline.proofSystem
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (discipline : EvidenceDiscipline theory)
    (kind : Kind) : NativeProofSystem (theory.Claim kind) where
  ProofObject := discipline.ProofObject kind
  Judges := discipline.Proves kind

/-- A primary proof-carrying authority is exact at the level of native proof
fibres.  Audit/trace authorities may intentionally omit this stronger field. -/
structure ProofCarryingAuthority
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (discipline : EvidenceDiscipline theory) where
  Certificate : Kind → Type uCertificate
  checker : (kind : Kind) → Checker (theory.Claim kind) (Certificate kind)
  certificateBoundary : ∀ kind,
    CertificateEquivalence (checker kind) (discipline.proofSystem kind)

namespace ProofCarryingAuthority

variable {Kind : Type uKind} {theory : TheoryFamily Kind}
    {discipline : EvidenceDiscipline theory}
    (authority : ProofCarryingAuthority discipline)

/-- Fibre equivalence plus the independent theorem-image law derives exact
scope authority.  Neither scope nor meaning is defined by checker replay. -/
theorem scopeAuthority (kind : Kind) :
    (authority.checker kind).Authority (theory.Scope kind) where
  sound := by
    intro claim certificate accepted
    have proofExists :
        ∃ proof, discipline.Proves kind proof claim := by
      let native :=
        (authority.certificateBoundary kind).nativeOfAccepted
          ⟨certificate, accepted⟩
      exact ⟨native.1, native.2⟩
    exact (discipline.scope_iff_proof kind claim).mpr proofExists
  complete := by
    intro claim inScope
    obtain ⟨proof, proves⟩ :=
      (discipline.scope_iff_proof kind claim).mp inScope
    let accepted :=
      (authority.certificateBoundary kind).acceptedOfNative ⟨proof, proves⟩
    exact ⟨accepted.1, accepted.2⟩

/-- Forget native proof-fibre identity only after deriving the ordinary
authority contract. -/
def toAuthorityContract : AuthorityContract theory where
  Certificate := authority.Certificate
  checker := authority.checker
  scopeAuthority := authority.scopeAuthority

end ProofCarryingAuthority

/-- A selected artifact and its native replay observation, with the exact
commuting equation required to realize one abstract authority checker. -/
structure AuthorityRealization
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (contract : AuthorityContract theory)
    (kind : Kind) (Artifact : Type uArtifact) where
  artifact : Artifact
  replay : Artifact → theory.Claim kind → contract.Certificate kind → Bool
  adequate : ∀ claim certificate,
    replay artifact claim certificate =
      (contract.checker kind).check claim certificate

namespace AuthorityRealization

variable {Kind : Type uKind} {theory : TheoryFamily Kind}
    {contract : AuthorityContract theory}
    {kind : Kind} {Artifact : Type uArtifact}

/-- A realized authority is a genuine instance of the generic certified
realization interface, with Boolean replay functions as its observation. -/
def toGSLTRealization
    (realization : AuthorityRealization contract kind Artifact) :
    Mettapedia.GSLT.SimpleRealization Unit Artifact
      (theory.Claim kind → contract.Certificate kind → Bool) where
  compile _ _ := realization.artifact
  observeSource _ _ := (contract.checker kind).check
  observeArtifact _ := realization.replay
  adequate _ _ := funext fun claim => funext fun certificate =>
    realization.adequate claim certificate

/-- The compiled artifact replays the abstract checker exactly. -/
theorem compiled_artifact_replays_checker
    (realization : AuthorityRealization contract kind Artifact)
    (claim : theory.Claim kind) (certificate : contract.Certificate kind) :
    realization.replay
        (realization.toGSLTRealization.compile () ()) claim certificate =
      (contract.checker kind).check claim certificate :=
  by
    change realization.replay realization.artifact claim certificate = _
    exact realization.adequate claim certificate

end AuthorityRealization

/-- An artifact candidate before adequacy is proved.  Sharing an artifact type
or even the same artifact value is intentionally insufficient. -/
structure UncheckedAuthorityArtifact
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    (contract : AuthorityContract theory)
    (kind : Kind) (Artifact : Type uArtifact) where
  artifact : Artifact
  replay : Artifact → theory.Claim kind → contract.Certificate kind → Bool

def UncheckedAuthorityArtifact.Adequate
    {Kind : Type uKind} {theory : TheoryFamily Kind}
    {contract : AuthorityContract theory}
    {kind : Kind} {Artifact : Type uArtifact}
    (candidate : UncheckedAuthorityArtifact contract kind Artifact) : Prop :=
  ∀ claim certificate, candidate.replay candidate.artifact claim certificate =
    (contract.checker kind).check claim certificate

namespace RealizationCanary

def theory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ claim => claim = true
  Meaning := fun _ claim => claim = true
  scope_sound := fun _ _ inScope => inScope

/-- A distinct semantic theory over the very same signature assignment. -/
def oppositeTheory : TheoryFamily Unit where
  Signature := Unit
  signatureOf := fun _ => ()
  Claim := fun _ => Bool
  Scope := fun _ claim => claim = false
  Meaning := fun _ claim => claim = false
  scope_sound := fun _ _ inScope => inScope

/-- Sharing a language signature does not identify semantic theories. -/
theorem signature_overlap_does_not_determine_meaning :
    theory.signatureOf () = oppositeTheory.signatureOf () ∧
      ∃ claim, theory.Meaning () claim ∧
        ¬ oppositeTheory.Meaning () claim := by
  refine ⟨rfl, true, rfl, ?_⟩
  simp [oppositeTheory]

def checker : Checker Bool Unit where
  check claim _ := claim

theorem checker_authority : checker.Authority (· = true) where
  sound := by intro claim certificate accepted; simpa [checker] using accepted
  complete := by
    intro claim meaningful
    exact ⟨(), by simpa [checker] using meaningful⟩

def contract : AuthorityContract theory where
  Certificate := fun _ => Unit
  checker := fun _ => checker
  scopeAuthority := fun _ => checker_authority

/-- The same Boolean claim checker with a retained proof tag. -/
def taggedChecker : Checker Bool Bool where
  check claim _ := claim

theorem taggedChecker_authority : taggedChecker.Authority (· = true) where
  sound := by
    intro claim certificate accepted
    simpa [taggedChecker] using accepted
  complete := by
    intro claim meaningful
    exact ⟨false, by simpa [taggedChecker] using meaningful⟩

/-- The same semantic theory may use a proof-relevant certificate format. -/
def taggedContract : AuthorityContract theory where
  Certificate := fun _ => Bool
  checker := fun _ => taggedChecker
  scopeAuthority := fun _ => taggedChecker_authority

/-- One semantic theory does not determine a certificate format: these two
exact authorities have respectively thin and non-thin certificate fibres. -/
theorem one_theory_supports_distinct_certificate_fibres :
    Subsingleton (contract.Certificate ()) ∧
      ¬ Subsingleton (taggedContract.Certificate ()) := by
  constructor
  · change Subsingleton Unit
    infer_instance
  · intro subsingleton
    change Subsingleton Bool at subsingleton
    have impossible : false = true := subsingleton.elim _ _
    cases impossible

def good : UncheckedAuthorityArtifact contract () Unit where
  artifact := ()
  replay := fun _ claim _ => claim

def bad : UncheckedAuthorityArtifact contract () Unit where
  artifact := ()
  replay := fun _ claim _ => !claim

theorem good_adequate : good.Adequate := by
  intro claim certificate
  rfl

theorem bad_not_adequate : ¬ bad.Adequate := by
  intro adequate
  have contradiction := adequate true ()
  simp [bad, contract, checker] at contradiction

/-- The same artifact carrier and value can support an adequate or an
inadequate replay interpretation.  Artifact overlap is therefore strictly
weaker than realization. -/
theorem artifact_overlap_does_not_determine_adequacy :
    good.artifact = bad.artifact ∧ good.Adequate ∧ ¬ bad.Adequate :=
  ⟨rfl, good_adequate, bad_not_adequate⟩

end RealizationCanary

/-! ## Stratified bootstrap authorities

Checker fidelity, source adequacy, native refinement, and consistency are
different contract claims.  A bootstrap authority at level `n` may only state
contracts about a target selected from `Fin n`; therefore no claim can name
its own host level.  This is a stratification discipline, not a theorem that
any layer proves its own consistency. -/

/-- Independent kinds of checker and realization contracts. -/
inductive BootstrapContractKind where
  | sourceSound
  | scopeComplete
  | sourceAdequate
  | wireCorrect
  | providerRefines
  | nativeRefines
  | resourceHonest
  | catalogBinds
  | modelSound
  | lowerConsistency
  deriving DecidableEq, Repr

/-- A contract checked at `hostLevel` whose subject lives at a strictly lower
level.  The statement family may use a different language at every level. -/
structure LowerContract (Statement : Nat → Type uClaim) (hostLevel : Nat) where
  targetLevel : Fin hostLevel
  kind : BootstrapContractKind
  statement : Statement targetLevel.val

namespace LowerContract

variable {Statement : Nat → Type uClaim} {hostLevel : Nat}

/-- Every well-formed contract targets a strictly lower level. -/
theorem target_lt_host (claim : LowerContract Statement hostLevel) :
    claim.targetLevel.val < hostLevel :=
  claim.targetLevel.isLt

/-- A stratified contract cannot target the level at which it is checked. -/
theorem target_ne_host (claim : LowerContract Statement hostLevel) :
    claim.targetLevel.val ≠ hostLevel :=
  Nat.ne_of_lt claim.target_lt_host

/-- Two meta-levels cannot certify each other in a cycle. -/
theorem no_two_level_cycle {first second : Nat}
    (firstChecksSecond : second < first)
    (secondChecksFirst : first < second) : False :=
  (Nat.not_lt_of_ge (Nat.le_of_lt firstChecksSecond)) secondChecksFirst

/-- There are no meta-contracts at level zero. -/
theorem levelZero_empty : IsEmpty (LowerContract Statement 0) where
  false claim := Fin.elim0 claim.targetLevel

/-- A contract may be transported to the next higher checker level without
changing its subject or contract kind. -/
def lift (claim : LowerContract Statement hostLevel) :
    LowerContract Statement (hostLevel + 1) where
  targetLevel := claim.targetLevel.castSucc
  kind := claim.kind
  statement := claim.statement

@[simp] theorem lift_targetLevel (claim : LowerContract Statement hostLevel) :
    claim.lift.targetLevel.val = claim.targetLevel.val :=
  rfl

@[simp] theorem lift_kind (claim : LowerContract Statement hostLevel) :
    claim.lift.kind = claim.kind :=
  rfl

end LowerContract

/-- One meta-authority layer with independently declared scope and meaning. -/
structure BootstrapLayer
    (Statement : Nat → Type uClaim) (hostLevel : Nat) where
  Certificate : Type uCertificate
  Scope : LowerContract Statement hostLevel → Prop
  Meaning : LowerContract Statement hostLevel → Prop
  scope_sound : ∀ claim, Scope claim → Meaning claim
  checker : Checker (LowerContract Statement hostLevel) Certificate
  scopeAuthority : checker.Authority Scope

/-- Repackage one bootstrap layer through the generic
theory/authority/realization factorization. -/
def BootstrapLayer.toTheoryFamily
    {Statement : Nat → Type uClaim} {hostLevel : Nat}
    (layer : BootstrapLayer.{uClaim, uCertificate} Statement hostLevel) :
    TheoryFamily Unit where
  Signature := Nat
  signatureOf := fun _ => hostLevel
  Claim := fun _ => LowerContract Statement hostLevel
  Scope := fun _ => layer.Scope
  Meaning := fun _ => layer.Meaning
  scope_sound := fun _ => layer.scope_sound

/-- The checker half of a bootstrap layer is an ordinary NIK authority
contract over its independently built theory. -/
def BootstrapLayer.toAuthorityContract
    {Statement : Nat → Type uClaim} {hostLevel : Nat}
    (layer : BootstrapLayer.{uClaim, uCertificate} Statement hostLevel) :
    AuthorityContract layer.toTheoryFamily where
  Certificate := fun _ => layer.Certificate
  checker := fun _ => layer.checker
  scopeAuthority := fun _ => layer.scopeAuthority

/-- An unbounded tower supplies a common certificate language and checker at
every successor level.  Layer `n+1` may discuss any level at most `n`, never
itself. -/
structure BootstrapTower (Statement : Nat → Type uClaim)
    (Certificate : Type uCertificate) where
  layer : (level : Nat) → BootstrapLayer Statement (level + 1)
  certificate_eq : ∀ level, (layer level).Certificate = Certificate

/-- The tower index enforces strict descent for every hosted claim. -/
theorem BootstrapTower.every_claim_targets_lower
    {Statement : Nat → Type uClaim} {Certificate : Type uCertificate}
    (_tower : BootstrapTower Statement Certificate)
    (level : Nat)
    (claim : LowerContract Statement (level + 1)) :
    claim.targetLevel.val < level + 1 :=
  claim.target_lt_host

/-! ### A concrete non-circular level tower

The finite Boolean refinement authority supplies an actual meta-authority at
every successor level.  It checks only `nativeRefines`; the other contract
kinds are rejected until separate authorities are supplied. -/

namespace RefinementBootstrapTower

def Statement : Nat → Type := fun _ => RefinementMetaAuthority.Claim

def Meaning {hostLevel : Nat} (claim : LowerContract Statement hostLevel) : Prop :=
  match claim.kind with
  | .nativeRefines => RefinementMetaAuthority.Refines claim.statement
  | _ => False

def checker {hostLevel : Nat} :
    Checker (LowerContract Statement hostLevel)
      RefinementMetaAuthority.Certificate where
  check claim certificate :=
    match claim.kind with
    | .nativeRefines =>
        RefinementMetaAuthority.checker.check claim.statement certificate
    | _ => false

theorem checker_sound {hostLevel : Nat} : checker.Sound (@Meaning hostLevel) := by
  intro claim certificate accepted
  cases kindEquality : claim.kind <;>
    simp [checker, Meaning, kindEquality] at accepted ⊢
  exact RefinementMetaAuthority.checker_sound
    claim.statement certificate accepted

theorem checker_complete {hostLevel : Nat} :
    checker.CertificateComplete (@Meaning hostLevel) := by
  intro claim meaningful
  cases kindEquality : claim.kind <;>
    simp [Meaning, kindEquality] at meaningful
  obtain ⟨certificate, accepted⟩ :=
    RefinementMetaAuthority.checker_complete claim.statement meaningful
  exact ⟨certificate, by simpa [checker, kindEquality] using accepted⟩

theorem checker_authority {hostLevel : Nat} :
    checker.Authority (@Meaning hostLevel) where
  sound := checker_sound
  complete := checker_complete

def layer (level : Nat) : BootstrapLayer Statement (level + 1) where
  Certificate := RefinementMetaAuthority.Certificate
  Scope := Meaning
  Meaning := Meaning
  scope_sound := fun _ inScope => inScope
  checker := checker
  scopeAuthority := checker_authority

/-- A concrete infinite tower of finite refinement meta-authorities. -/
def tower : BootstrapTower Statement RefinementMetaAuthority.Certificate where
  layer := layer
  certificate_eq := fun _ => rfl

def levelOneIdentityClaim
    (implementation : RefinementMetaAuthority.BinaryChecker) :
    LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .nativeRefines
  statement := RefinementMetaAuthority.identityClaim implementation

/-- Positive witness: level one checks a genuine refinement contract about
the level-zero implementation. -/
theorem levelOne_identity_accepted
    (implementation : RefinementMetaAuthority.BinaryChecker) :
    checker.check (levelOneIdentityClaim implementation)
      (RefinementMetaAuthority.computedCertificate
        (RefinementMetaAuthority.identityClaim implementation)) = true :=
  RefinementMetaAuthority.identity_certificate_accepted implementation

def levelOneBadClaim : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .nativeRefines
  statement := RefinementMetaAuthority.badClaim

/-- Negative witness: stratification does not make a false lower-level
refinement certifiable. -/
theorem levelOne_bad_has_no_certificate :
    ¬ ∃ certificate, checker.check levelOneBadClaim certificate = true :=
  RefinementMetaAuthority.badClaim_has_no_accepted_certificate

def unsupportedSourceSoundClaim : LowerContract Statement 1 where
  targetLevel := ⟨0, by decide⟩
  kind := .sourceSound
  statement := RefinementMetaAuthority.identityClaim
    RefinementMetaAuthority.alwaysAccept

/-- Fail-closed witness: a refinement checker cannot impersonate a source
soundness authority merely because both claims inhabit the same tower. -/
theorem unsupported_kind_rejected (certificate) :
    checker.check unsupportedSourceSoundClaim certificate = false :=
  rfl

end RefinementBootstrapTower

/-! ## Consequence over an authority diagram -/

/-- A Pi-institutional consequence layer whose sentence functor is exactly the
live NIK claim functor.  This is additional structure over an authority
diagram, not a reconstruction from its raw checker fields. -/
structure AuthorityConsequenceExtension
    {Index : Type uKind} [CategoryTheory.Category.{uHom} Index]
    (diagram : NIKGSLT.Indexed.AuthorityDiagram.{uKind, uClaim,
      uCertificate, uHom} Index) where
  evidence : IndexedSetEvidenceDoctrine.{uKind, uHom,
    max uClaim uCertificate, uEvidence} diagram.claimFunctor
  empty_eq_certified : ∀ kind,
    (evidence.fibre kind).consequence ∅ =
      { claim | diagram.family.Certified kind claim.down }

namespace AuthorityConsequenceExtension

variable {Index : Type uKind} [CategoryTheory.Category.{uHom} Index]
    {diagram : NIKGSLT.Indexed.AuthorityDiagram.{uKind, uClaim,
      uCertificate, uHom} Index}
    (extension : AuthorityConsequenceExtension diagram)

/-- Forgetting evidence but retaining hypothetical closure produces the
Pi-institutional view of a suitably extended NIK diagram. -/
noncomputable def toPiInstitution : PiInstitution Index :=
  extension.evidence.toPiInstitution

/-- The Pi-institutional theorem set is exactly native certified scope when
the extension records the required adequacy law. -/
theorem theorems_eq_certified (kind : Index) :
    extension.toPiInstitution.theorems kind =
      { claim | diagram.family.Certified kind claim.down } :=
  extension.empty_eq_certified kind

end AuthorityConsequenceExtension

/-! ## The exact refinement functor -/

namespace AuthorityDiagram

variable {Index : Type uKind} [CategoryTheory.Category.{uHom} Index]
    (diagram : Mettapedia.GSLT.LanguageDef.NIKGSLT.Indexed.AuthorityDiagram.{uKind, uClaim,
      uCertificate, uHom} Index)

/-! ### The accepted-evidence fibres are discrete -/

/-- A vertical arrow between two accepted judgments over the same authority
is an arrow whose underlying authority route is the identity. -/
def VerticalHom (kind : Index)
    (source target : diagram.acceptedFunctor.obj kind) :=
  { arrow :
      diagram.acceptedObject kind source ⟶
        diagram.acceptedObject kind target //
    diagram.acceptedProjection.map arrow =
      CategoryTheory.CategoryStruct.id kind }

/-- A vertical accepted-evidence arrow can exist only between equal retained
claim-certificate pairs. -/
theorem eq_of_verticalHom (kind : Index)
    {source target : diagram.acceptedFunctor.obj kind}
    (arrow : VerticalHom diagram kind source target) :
    source = target := by
  have mappedEvidence := arrow.val.property
  have baseIdentity : arrow.val.val =
      CategoryTheory.CategoryStruct.id kind := arrow.property
  rw [baseIdentity] at mappedEvidence
  exact
    (diagram.acceptedFunctor.map_id_apply kind source).symm.trans
      mappedEvidence

/-- Equal accepted evidence has the identity vertical arrow. -/
def verticalHomOfEq (kind : Index)
    {source target : diagram.acceptedFunctor.obj kind}
    (equalEvidence : source = target) :
    VerticalHom diagram kind source target := by
  subst target
  refine ⟨CategoryTheory.CategoryStruct.id _, ?_⟩
  exact diagram.acceptedProjection.map_id _

/-- The fibrewise hom is inhabited exactly at equality. -/
theorem nonempty_verticalHom_iff_eq (kind : Index)
    (source target : diagram.acceptedFunctor.obj kind) :
    Nonempty (VerticalHom diagram kind source target) ↔ source = target := by
  constructor
  · rintro ⟨arrow⟩
    exact eq_of_verticalHom diagram kind arrow
  · intro equalEvidence
    exact ⟨verticalHomOfEq diagram kind equalEvidence⟩

/-- Vertical arrows are unique, completing the concrete discreteness
characterization of each accepted-evidence fibre. -/
theorem verticalHom_subsingleton (kind : Index)
    (source target : diagram.acceptedFunctor.obj kind) :
    Subsingleton (VerticalHom diagram kind source target) where
  allEq left right := by
    apply Subtype.ext
    apply CategoryTheory.CategoryOfElements.ext diagram.acceptedFunctor
    exact left.property.trans right.property.symm

/-- Total category of authority-indexed claims. -/
abbrev ClaimTotal := (diagram.claimFunctor).Elements

/-- Accepted evidence refines its retained claim.  This is the
Mellies--Zeilberger refinement functor; the separate projection to `Index`
only remembers which authority owns the judgment. -/
def evidenceRefinement :
    CategoryTheory.Functor
      (NIKGSLT.Indexed.AuthorityDiagram.AcceptedTotal diagram)
      (ClaimTotal diagram) :=
  CategoryTheory.CategoryOfElements.map diagram.evidenceToClaim

@[simp]
theorem evidenceRefinement_obj_claim
    (object : NIKGSLT.Indexed.AuthorityDiagram.AcceptedTotal diagram) :
    (evidenceRefinement diagram |>.obj object).2 = ULift.up object.2.claim :=
  rfl

/-- Refinement erasure and the accepted-evidence projection name the same
authority. -/
theorem evidenceRefinement_comp_claimProjection :
    CategoryTheory.Functor.comp (evidenceRefinement diagram)
        (CategoryTheory.CategoryOfElements.π diagram.claimFunctor) =
      diagram.acceptedProjection :=
  rfl

/-- Erasure is faithful: a morphism of accepted judgments is already
determined by its underlying authority route.  This does not make erasure
full or recover certificates from claims. -/
instance evidenceRefinement_faithful :
    (evidenceRefinement diagram).Faithful where
  map_injective := by
    intro source target left right equalMaps
    apply CategoryTheory.CategoryOfElements.ext diagram.acceptedFunctor
    have baseEq := congrArg
      (fun morphism => morphism.val) equalMaps
    simpa [evidenceRefinement, CategoryTheory.CategoryOfElements.map] using baseEq

/-- Certificate erasure is not full whenever an authority route relates the
retained claims but its evidence action misses the chosen target
certificate.  Thus fullness would be a substantive proof-reconstruction
property, not a consequence of the NIK waist. -/
theorem evidenceRefinement_not_full_of_missing_evidence
    {source target : Index} (route : source ⟶ target)
    (sourceEvidence : diagram.acceptedFunctor.obj source)
    (targetEvidence : diagram.acceptedFunctor.obj target)
    (sameClaim : diagram.claimFunctor.map route
        (ULift.up sourceEvidence.claim) =
      ULift.up targetEvidence.claim)
    (missingEvidence : diagram.acceptedFunctor.map route sourceEvidence ≠
      targetEvidence) :
    ¬ CategoryTheory.Functor.Full (evidenceRefinement diagram) := by
  intro fullness
  let sourceObject :
      NIKGSLT.Indexed.AuthorityDiagram.AcceptedTotal diagram :=
    ⟨source, sourceEvidence⟩
  let targetObject :
      NIKGSLT.Indexed.AuthorityDiagram.AcceptedTotal diagram :=
    ⟨target, targetEvidence⟩
  let claimArrow :
      (evidenceRefinement diagram).obj sourceObject ⟶
        (evidenceRefinement diagram).obj targetObject :=
    CategoryTheory.CategoryOfElements.homMk _ _ route sameClaim
  letI : CategoryTheory.Functor.Full (evidenceRefinement diagram) := fullness
  obtain ⟨evidenceArrow, mappedArrow⟩ :=
    (evidenceRefinement diagram).map_surjective claimArrow
  have baseEquality : evidenceArrow.val = route := by
    have underlyingEquality := congrArg
      (fun arrow => arrow.val) mappedArrow
    simpa [evidenceRefinement, CategoryTheory.CategoryOfElements.map,
      claimArrow] using underlyingEquality
  apply missingEvidence
  rw [← baseEquality]
  exact evidenceArrow.property

end AuthorityDiagram

/-! ### A concrete non-full refinement canary -/

namespace RefinementCanary

abbrev Index := CategoryTheory.Discrete Unit

/-- One claim with two independently retained proof tags. -/
def checker : Checker Unit Bool where
  check _ _ := true

theorem checker_authority : checker.Authority (fun _ => True) where
  sound := by intro claim certificate accepted; trivial
  complete := by intro claim certified; exact ⟨false, rfl⟩

def family : AuthorityFamily Index :=
  { Claim := fun _ => Unit
    Certificate := fun _ => Bool
    checker := fun _ => checker
    Certified := fun _ _ => True
    Meaning := fun _ _ => True
    projection := fun _ => checker_authority.toProjection }

/-- The authority base is deliberately trivial; all nontriviality is in the
two retained certificates for its sole claim. -/
def diagram : NIKGSLT.Indexed.AuthorityDiagram Index where
  family := family
  transport := by
    intro source target route
    exact
      { mapClaim := id
        mapCertificate := id
        check_commutes := by intro claim certificate; rfl
        certified_preserved := by intro claim certified; exact certified
        meaning_preserved := by intro claim meaningful; exact meaningful }
  mapClaim_id := by intro kind claim; rfl
  mapCertificate_id := by intro kind certificate; rfl
  mapClaim_comp := by intro first second third left right claim; rfl
  mapCertificate_comp := by
    intro first second third left right certificate
    rfl

def kind : Index := CategoryTheory.Discrete.mk ()

def falseEvidence : diagram.acceptedFunctor.obj kind where
  claim := ()
  certificate := false
  accepted := rfl

def trueEvidence : diagram.acceptedFunctor.obj kind where
  claim := ()
  certificate := true
  accepted := rfl

theorem identity_misses_trueEvidence :
    diagram.acceptedFunctor.map (CategoryTheory.CategoryStruct.id kind)
        falseEvidence ≠ trueEvidence := by
  intro mapped
  have sourceEqualsTarget : falseEvidence = trueEvidence :=
    (diagram.acceptedFunctor.map_id_apply kind falseEvidence).symm.trans mapped
  have tagsEqual := congrArg InternalJudgment.Accepted.certificate
    sourceEqualsTarget
  change false = true at tagsEqual
  cases tagsEqual

/-- Forgetting certificates is faithful but not full even over a one-object
authority base: the claim identity cannot reconstruct the other proof tag. -/
theorem refinement_faithful_and_not_full :
    CategoryTheory.Functor.Faithful
        (AuthorityDiagram.evidenceRefinement diagram) ∧
      ¬ CategoryTheory.Functor.Full
        (AuthorityDiagram.evidenceRefinement diagram) := by
  constructor
  · infer_instance
  · exact AuthorityDiagram.evidenceRefinement_not_full_of_missing_evidence
      diagram (CategoryTheory.CategoryStruct.id kind) falseEvidence trueEvidence
      (by rfl)
      identity_misses_trueEvidence

end RefinementCanary

/-! ## Axiom audit -/

#print axioms SeparationSentence.rawNIK_does_not_determine_consequence
#print axioms PiInstitution.Comorphism.comp
#print axioms PiInstitution.TheoryHom.comp
#print axioms PiInstitution.ProofCalculus.tagged_projection_not_injective
#print axioms PiInstitution.ProofCalculus.theorem_forbids_empty_proof_fibre
#print axioms PiInstitution.relativeClosure_empty
#print axioms CertificateGSLTCloneCanary.repeated_assumption_occurrences_distinct
#print axioms SetEvidenceDoctrine.thinOfClosure_consequence
#print axioms SetEvidenceDoctrine.proofErasureThinAdjunction
#print axioms PiInstitution.thinEvidence_closure_roundtrip
#print axioms emptyContext_has_no_setEvidence_realization
#print axioms ContextualTranslation.mapAccepted_reindex
#print axioms StructuralContextGuest.weakening_preserves_evidence
#print axioms ResourceContextGuest.tagging_commutes_with_swap
#print axioms ResourceContextGuest.tagging_not_surjective_at_two
#print axioms ResourceContextGuest.no_resource_duplication
#print axioms terminalCwF_term_fibre_subsingleton
#print axioms MeaningGapCanary.replay_does_not_determine_meaning_preservation
#print axioms RefinementMetaAuthority.checker_authority
#print axioms RefinementMetaAuthority.badClaim_has_no_accepted_certificate
#print axioms CertificateBoundaryCanary.decodable_but_not_exact
#print axioms DecisionProofCanary.decisionKernel_computable
#print axioms DecisionProofCanary.decision_does_not_retain_native_proofs
#print axioms native_calculus_faces_are_independent
#print axioms NativeProofKernel.certificateEquivalence
#print axioms OperationalDerivation.bind_assumptions
#print axioms OperationalDerivation.bind_assoc
#print axioms OperationalDerivation.sound
#print axioms operationalDerivationClone
#print axioms operationalAdmittedRules
#print axioms operationalSoundClone
#print axioms AdmissionCanary.successor_is_nonidentity
#print axioms AdmissionCanary.no_negation_admission
#print axioms AdmissionCanary.emission_does_not_control_execution
#print axioms OptimizationLimits.haltPointReachable_iff
#print axioms OptimizationLimits.NoCompleteReachabilityAnalysis
#print axioms OptimizationLimits.reachabilityBudgetAuthority
#print axioms OptimizationLimits.NoCompleteDeadCodeEliminator
#print axioms OptimizationLimits.NoCompletePropertyDirectedOptimizer
#print axioms OptimizationLimits.NoUniversalOptimalCompiler
#print axioms OptimizationLimits.FiniteFragmentOptimalCompilation
#print axioms OptimizationLimits.finiteThresholdFragment_has_optimal_compiler
#print axioms OptimizationLimits.impossibility_ladder_and_bounded_frontier
#print axioms AdmittedCloneRules.toAdmissionHom_run
#print axioms CertificateGSLTCloneCanary.soundClone
#print axioms CertificateGSLTCloneCanary.native_derivation_flows
#print axioms ProofCarryingAuthority.scopeAuthority
#print axioms TheoryFamilyCanary.false_not_meaning
#print axioms LowerContract.no_two_level_cycle
#print axioms RefinementBootstrapTower.levelOne_identity_accepted
#print axioms RefinementBootstrapTower.levelOne_bad_has_no_certificate
#print axioms RefinementBootstrapTower.unsupported_kind_rejected
#print axioms AuthorityRealization.compiled_artifact_replays_checker
#print axioms RealizationCanary.signature_overlap_does_not_determine_meaning
#print axioms RealizationCanary.one_theory_supports_distinct_certificate_fibres
#print axioms RealizationCanary.artifact_overlap_does_not_determine_adequacy
#print axioms AuthorityConsequenceExtension.theorems_eq_certified
#print axioms AuthorityDiagram.nonempty_verticalHom_iff_eq
#print axioms AuthorityDiagram.evidenceRefinement_comp_claimProjection
#print axioms RefinementCanary.refinement_faithful_and_not_full

end Mettapedia.GSLT.LanguageDef.NIKMetalogic
