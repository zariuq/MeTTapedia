import Mettapedia.TypeTheory.IndexedPolynomial
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalInternalLanguage
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IndexedFamilyDeclaration
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ConversionCoherence
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.ProofRelevantSubstitutionCoherence

/-!
# Native indexed-family semantics for Prime

This module connects the reusable indexed-polynomial theory to Prime's
existing proof-relevant relational semantics.  It does not define inductive
families in terms of Prime, and it does not install a runtime representation.
The dependency is intentionally one-way:

1. `Mettapedia.TypeTheory.IndexedPolynomial` gives the general mathematics;
2. this module selects its polynomial List as a running Prime hypothesis;
3. Prime's `Rel` lifts through that List without losing derivation evidence;
4. functional graphs recover ordinary `map` by exact fibrewise equivalence.

The declaration-aware syntactic realization is a separate layer below this
semantic seam.  Consequently changing Prime's authored notation or runtime
representation cannot change what strictly-positive indexed families mean.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeIndexedFamilies

open Mettapedia.TypeTheory.IndexedPolynomial

namespace Semantic

universe u

abbrev PrimeRel := RelationalInternalLanguage.Semantic.Rel

/-- The current native-list semantic hypothesis is the polynomial fixed point,
not the Church encoding used by the polymorphism canary. -/
abbrev List (Element : Type u) : Type u :=
  ListExample.ListP Element

abbrev nil {Element : Type u} : List Element :=
  ListExample.nil

abbrev cons {Element : Type u} (head : Element) (tail : List Element) :
    List Element :=
  ListExample.cons head tail

noncomputable abbrev map {Source Target : Type u}
    (function : Source → Target) : List Source → List Target :=
  ListExample.map function

/-- Lift a Prime proof-relevant relation through native Lists.  Evidence is
the full pointwise derivation spine, so branching multiplicity survives. -/
noncomputable def mapRel {Source Target : Type u}
    (relation : PrimeRel Source Target) : PrimeRel (List Source) (List Target)
    where
  evidence source target :=
    ListExample.mapRel relation.evidence source target

/-- Prime's companion/graph evidence is definitionally the equality witness
used by the abstract list relator. -/
def graphEvidenceEquiv {Source Target : Type u}
    (function : Source → Target) (source : Source) (target : Target) :
    (RelationalInternalLanguage.Semantic.Rel.graph function).evidence
        source target ≃
      ListExample.Graph.{u, u, u} function source target :=
  Equiv.refl _

/-- The decisive seam: relational map of a functional graph is exactly the
graph of native map, including evidence fibres rather than only support. -/
noncomputable def mapRel_graph_equiv_graph_map
    {Source Target : Type u} (function : Source → Target)
    (source : List Source) (target : List Target) :
    (mapRel (RelationalInternalLanguage.Semantic.Rel.graph function)).evidence
        source target ≃
      (RelationalInternalLanguage.Semantic.Rel.graph (map function)).evidence
        source target :=
  ListExample.mapRel_graph_equiv_graph_map function source target

/-- Native polynomial Lists have the expected no-junk/no-confusion model. -/
noncomputable def listRepresentation (Element : Type u) :
    List Element ≃ _root_.List Element :=
  ListExample.equivList Element

/-! ## Evidence controls at the Prime seam -/

def branchingRelation : PrimeRel Unit Unit where
  evidence := ListExample.branchingRelation

/-- Two derivations at one element become two distinct native-list relational
map derivations. -/
theorem branching_mapRel_not_subsingleton :
    ¬ Subsingleton
      ((mapRel branchingRelation).evidence
        ListExample.singletonUnit ListExample.singletonUnit) :=
  ListExample.branching_mapRel_not_subsingleton

def impossibleRelation : PrimeRel Unit Unit where
  evidence := ListExample.impossibleRelation

/-- Relational lifting cannot synthesize a list derivation when the element
fibre is empty. -/
theorem impossible_singleton_mapRel_isEmpty :
    IsEmpty
      ((mapRel impossibleRelation).evidence
        ListExample.singletonUnit ListExample.singletonUnit) :=
  ListExample.impossible_singleton_mapRel_isEmpty

end Semantic

/-! ## Declaration-aware intrinsic hypothesis

The following syntax is the running Prime realization of the abstract List.
It is deliberately expressed through the common declaration-aware tower:
family, constructors, and eliminator are global declarations; constructor
computation is licensed by structurally stable root rules.  The raw signature
is not called checked authority until its formation and subject-reduction
obligations have been proved below.
-/

namespace Intrinsic

open Presentation
open Presentation.SchemaElaboration
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily
open Presentation.ConversionCoherence

def elementLevel : LevelExpr := .param 0
def motiveLevel : LevelExpr := .param 1

def listName : DeclName := `Prime.List
def nilName : DeclName := `Prime.List.nil
def consName : DeclName := `Prime.List.cons
def eliminateName : DeclName := `Prime.List.eliminate
def identityEliminateName : DeclName := `Prime.Id.eliminate

def listApp (element : Tower.Tm n) : Tower.Tm n :=
  .app (.const listName) element

@[simp] theorem rename_listApp (renameMap : Ren n m)
    (element : Tower.Tm n) :
    Presentation.rename renameMap (listApp element) =
      listApp (Presentation.rename renameMap element) := rfl

@[simp] theorem subst_listApp (substitution : Sub Tower.Head n m)
    (element : Tower.Tm n) :
    Presentation.subst substitution (listApp element) =
      listApp (Presentation.subst substitution element) := rfl

def nilApp (element : Tower.Tm n) : Tower.Tm n :=
  .app (.const nilName) element

def consApp (element head tail : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.const consName) element) head) tail

def eliminateApp (element motive nilCase consCase list : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app (.const eliminateName) element)
          motive)
        nilCase)
      consCase)
    list

/-- Apply identity elimination with a fixed left endpoint. -/
def identityEliminateApp
    (element point motive reflCase endpoint equality : Tower.Tm n) :
    Tower.Tm n :=
  .app
    (.app
      (.app
        (.app
          (.app
            (.app (.const identityEliminateName) element)
            point)
          motive)
        reflCase)
      endpoint)
    equality

@[simp] theorem rename_identityEliminateApp (renameMap : Ren n m)
    (element point motive reflCase endpoint equality : Tower.Tm n) :
    Presentation.rename renameMap
        (identityEliminateApp element point motive reflCase endpoint equality) =
      identityEliminateApp
        (Presentation.rename renameMap element)
        (Presentation.rename renameMap point)
        (Presentation.rename renameMap motive)
        (Presentation.rename renameMap reflCase)
        (Presentation.rename renameMap endpoint)
        (Presentation.rename renameMap equality) :=
  rfl

@[simp] theorem subst_identityEliminateApp
    (substitution : Sub Tower.Head n m)
    (element point motive reflCase endpoint equality : Tower.Tm n) :
    Presentation.subst substitution
        (identityEliminateApp element point motive reflCase endpoint equality) =
      identityEliminateApp
        (Presentation.subst substitution element)
        (Presentation.subst substitution point)
        (Presentation.subst substitution motive)
        (Presentation.subst substitution reflCase)
        (Presentation.subst substitution endpoint)
        (Presentation.subst substitution equality) :=
  rfl

/-- `List : Π (A : U α), U α`. -/
def listType : Tower.Tm 0 :=
  .pi (sortTm elementLevel) (sortTm elementLevel)

/-- `nil : Π (A : U α), List A`. -/
def nilType : Tower.Tm 0 :=
  .pi (sortTm elementLevel) (listApp (.var 0))

/-- The portion of the `cons` type below its element-type binder. -/
def consBodyType : Tower.Tm 1 :=
  .pi (.var 0)
    (.pi (listApp (.var 1)) (listApp (.var 2)))

/-- `cons : Π A, A → List A → List A`. -/
def consType : Tower.Tm 0 :=
  .pi (sortTm elementLevel) consBodyType

/-- Motives may depend on the eliminated list and live in an independent
universe: `Π (xs : List A), U ρ`. -/
def motiveType : Tower.Tm 1 :=
  .pi (listApp (.var 0)) (sortTm motiveLevel)

/-- In context `A,P`, the nil branch has type `P (nil A)`. -/
def nilCaseType : Tower.Tm 2 :=
  .app (.var 0) (nilApp (.var 1))

/-- In context `A,P,z`, the cons branch has type
`Π a xs, P xs → P (cons A a xs)`. -/
def consCaseType : Tower.Tm 3 :=
  .pi (.var 2)
    (.pi (listApp (.var 3))
      (.pi (.app (.var 3) (.var 0))
        (.app (.var 4) (consApp (.var 5) (.var 2) (.var 1)))))

/-- In context `A,P,z,s`, elimination returns `Π xs, P xs`. -/
def eliminateResultType : Tower.Tm 4 :=
  .pi (listApp (.var 3)) (.app (.var 3) (.var 0))

/-- The genuinely dependent List eliminator. -/
def eliminateType : Tower.Tm 0 :=
  .pi (sortTm elementLevel)
    (.pi motiveType
      (.pi nilCaseType
        (.pi consCaseType eliminateResultType)))

/-! Identity is already a primitive family former with reflexivity in the
shared syntax.  Its dependent eliminator is an instance of the same indexed
family mechanism as List, not an unrelated postulate. -/

/-- In context `A,x`, an identity motive ranges over the right endpoint and
its equality witness. -/
def identityMotiveType : Tower.Tm 2 :=
  .pi (.var 1)
    (.pi (.id (.var 2) (.var 1) (.var 0)) (sortTm motiveLevel))

/-- In context `A,x,P`, the reflexivity branch is `P x (refl x)`. -/
def identityReflCaseType : Tower.Tm 3 :=
  .app (.app (.var 0) (.var 1)) (.refl (.var 1))

/-- In context `A,x,P,d`, path induction yields every endpoint and equality
witness in the motive. -/
def identityEliminateResultType : Tower.Tm 4 :=
  .pi (.var 3)
    (.pi (.id (.var 4) (.var 3) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)))

/-- Fixed-left-endpoint Martin-Löf identity elimination (`J`). -/
def identityEliminateType : Tower.Tm 0 :=
  .pi (sortTm elementLevel)
    (.pi (.var 0)
      (.pi identityMotiveType
        (.pi identityReflCaseType identityEliminateResultType)))

/-! ### Iota computation -/

/-- Constructor computation for the native dependent List eliminator.  The
rules are schematic in every ambient telescope and retain all authored
arguments. -/
inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | nil (element motive nilCase consCase : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp element motive nilCase consCase (nilApp element))
        nilCase
  | cons (element motive nilCase consCase head tail : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp element motive nilCase consCase
          (consApp element head tail))
        (.app
          (.app
            (.app consCase head)
            tail)
          (eliminateApp element motive nilCase consCase tail))
  | identity (element point motive reflCase : Tower.Tm n) :
      IotaEvidence n
        (identityEliminateApp element point motive reflCase point
          (.refl point))
        reflCase

def IotaEvidence.rename {left right : Tower.Tm n}
    (step : IotaEvidence n left right) (renameMap : Ren n m) :
    IotaEvidence m (Presentation.rename renameMap left)
      (Presentation.rename renameMap right) := by
  cases step with
  | nil => exact .nil _ _ _ _
  | cons => exact .cons _ _ _ _ _ _
  | identity => exact .identity _ _ _ _

def IotaEvidence.substitute {left right : Tower.Tm n}
    (step : IotaEvidence n left right) (substitution : Sub Tower.Head n m) :
    IotaEvidence m (Presentation.subst substitution left)
      (Presentation.subst substitution right) := by
  cases step with
  | nil => exact .nil _ _ _ _
  | cons => exact .cons _ _ _ _ _ _
  | identity => exact .identity _ _ _ _

/-- The unindexed data retained by an iota receipt.  Endpoints are computed
from this code; keeping the code separate makes coherence of informative
receipts reducible to ordinary equality rather than proof irrelevance. -/
inductive IotaEvidenceCode (n : Nat) where
  | nil (element motive nilCase consCase : Tower.Tm n)
  | cons (element motive nilCase consCase head tail : Tower.Tm n)
  | identity (element point motive reflCase : Tower.Tm n)
  deriving DecidableEq

def IotaEvidence.code :
    {left right : Tower.Tm n} →
      IotaEvidence n left right → IotaEvidenceCode n
  | _, _, .nil element motive nilCase consCase =>
      .nil element motive nilCase consCase
  | _, _, .cons element motive nilCase consCase head tail =>
      .cons element motive nilCase consCase head tail
  | _, _, .identity element point motive reflCase =>
      .identity element point motive reflCase

/-- Receipt codes are complete: equal retained constructor data determines
heterogeneously equal evidence, including its computed endpoints. -/
theorem IotaEvidence.heq_of_code_eq
    {left₁ right₁ left₂ right₂ : Tower.Tm n}
    {first : IotaEvidence n left₁ right₁}
    {second : IotaEvidence n left₂ right₂}
    (encoded : first.code = second.code) : HEq first second := by
  cases first <;> cases second <;>
    simp_all [IotaEvidence.code]
  case nil.nil =>
    rcases encoded with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  case cons.cons =>
    rcases encoded with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl
  case identity.identity =>
    rcases encoded with ⟨rfl, rfl, rfl, rfl⟩
    rfl

def proofRelevantIotaComputation :
    ProofRelevantRootComputation Tower.Head where
  Evidence := IotaEvidence _
  rename := by
    intro n m renameMap left right step
    exact IotaEvidence.rename step renameMap
  substitute := by
    intro n m substitution left right step
    exact IotaEvidence.substitute step substitution

/-- The authored List and identity computation receipts are stable under
identity and composite substitutions.  In particular, the `J` computation
rule is not merely available at closed terms: it is natural in its ambient
context, as required of a dependent eliminator. -/
def proofRelevantIotaSubstitutionCoherent :
    proofRelevantIotaComputation.SubstitutionCoherent where
  substitute_ids := by
    intro n left right evidence
    apply IotaEvidence.heq_of_code_eq
    cases evidence <;>
      simp [IotaEvidence.code, proofRelevantIotaComputation,
        IotaEvidence.substitute]
  substitute_comp := by
    intro n m k later earlier left right evidence
    apply IotaEvidence.heq_of_code_eq
    cases evidence <;>
      simp [IotaEvidence.code, proofRelevantIotaComputation,
        IotaEvidence.substitute]

/-- Definitional conversion sees only support; execution and authority retain
the full `IotaEvidence` receipt above. -/
def iotaComputation : RootComputation Tower.Head :=
  proofRelevantIotaComputation.support

def declarations : List (DeclName × Entry Tower.Head) :=
  [(listName, { type := listType }),
   (nilName, { type := nilType }),
   (consName, { type := consType }),
   (eliminateName, { type := eliminateType }),
   (identityEliminateName, { type := identityEliminateType })]

/-- Raw declaration data plus iota computation.  Authority consumers must use
the later checked package, not this unvalidated carrier. -/
def rawSignature : Signature Tower.Head where
  entries := (Signature.ofList declarations).entries
  computation := iotaComputation

abbrev rules : Rules Tower.Head :=
  extendRules Tower.rules rawSignature

/-- Native iota equations never rewrite a dependent-function constructor or
a universe head at the root.  They act only on fully applied eliminators;
computation inside Pi components remains available through congruence. -/
def rootPiHeadNeutral : RootPiHeadNeutral rules where
  pi := by
    intro n domain codomain target rootStep
    cases rootStep with
    | inherited inherited => exact inherited.elim
    | declared declared =>
        rcases declared with ⟨evidence⟩
        cases evidence
  head := by
    intro n source target rootStep
    cases rootStep with
    | inherited inherited => exact inherited.elim
    | declared declared =>
        rcases declared with ⟨evidence⟩
        cases evidence

/-- For the native declaration calculus, beta/iota Church--Rosser is now the
only remaining premise needed to obtain Pi injectivity and Pi/head
disjointness. -/
def piConversionBoundaryOfChurchRosser
    (churchRosser : ConversionCoherence.ChurchRosser rules) :
    PiConversionBoundary rules :=
  ConversionCoherence.piConversionBoundaryOfChurchRosser
    rootPiHeadNeutral churchRosser

@[simp] theorem typeOf_list :
    rawSignature.typeOf? listName = some listType := by
  simp [rawSignature, declarations, listName, nilName, consName, eliminateName,
    listType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_nil :
    rawSignature.typeOf? nilName = some nilType := by
  simp [rawSignature, declarations, listName, nilName, consName, eliminateName,
    nilType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_cons :
    rawSignature.typeOf? consName = some consType := by
  simp [rawSignature, declarations, listName, nilName, consName, eliminateName,
    consType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_eliminate :
    rawSignature.typeOf? eliminateName = some eliminateType := by
  simp [rawSignature, declarations, listName, nilName, consName, eliminateName,
    identityEliminateName,
    eliminateType, Signature.ofList, Signature.insert, Signature.typeOf?]

@[simp] theorem typeOf_identityEliminate :
    rawSignature.typeOf? identityEliminateName =
      some identityEliminateType := by
  simp [rawSignature, declarations, listName, nilName, consName, eliminateName,
    identityEliminateName, identityEliminateType, Signature.ofList,
    Signature.insert, Signature.typeOf?]

/-! ### Declaration formation -/

abbrev HasType {n : Nat} :=
  @Presentation.HasType Tower.Head rules n

theorem listConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const listName) (liftClosed listType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature listName = some listType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_list

theorem nilConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const nilName) (liftClosed nilType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature nilName = some nilType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_nil

theorem consConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const consName) (liftClosed consType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature consName = some consType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_cons

theorem eliminateConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const eliminateName) (liftClosed eliminateType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature eliminateName = some eliminateType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_eliminate

theorem identityEliminateConstant_hasType {context : Tower.Ctx n} :
    HasType context (.const identityEliminateName)
      (liftClosed identityEliminateType) := by
  apply Presentation.HasType.const
  change combinedType Tower.rules rawSignature identityEliminateName =
    some identityEliminateType
  apply combinedType_of_signature
  · rfl
  · exact typeOf_identityEliminate

/-- Applying the intrinsic family former to a formed element type produces a
type in that element universe. -/
theorem listApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel)) :
    HasType context (listApp element) (sortTm elementLevel) := by
  have application := Presentation.HasType.appElim
    (listConstant_hasType (context := context)) elementTyping
  simpa [listType, listApp, liftClosed, sortTm, Presentation.rename,
    Presentation.inst0, Presentation.subst] using application

/-- The intrinsic nullary constructor produces a native list. -/
theorem nilApp_hasType {context : Tower.Ctx n} {element : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel)) :
    HasType context (nilApp element) (listApp element) := by
  have application := Presentation.HasType.appElim
    (nilConstant_hasType (context := context)) elementTyping
  simpa [nilType, nilApp, listApp, liftClosed, sortTm, Presentation.rename,
    Presentation.inst0, Presentation.subst, Presentation.subst0,
    Presentation.liftRen, Presentation.liftSub] using application

@[simp] theorem inst0_lifted_closed_binder
    (element : Tower.Tm n) :
    Presentation.inst0 element
        (Presentation.rename
          (liftRen (Fin.elim0 : Ren 0 n))
          (.var 0 : Tower.Tm 1)) =
      element := by
  rfl

@[simp] theorem rename_lifted_closed_binder :
    Presentation.rename
        (liftRen (Fin.elim0 : Ren 0 n))
        (.var 0 : Tower.Tm 1) =
      (.var 0 : Tower.Tm (n + 1)) := by
  rfl

/-- The intrinsic binary constructor preserves its element-indexed list
fibre. -/
theorem consApp_hasType {context : Tower.Ctx n}
    {element head tail : Tower.Tm n}
    (elementTyping : HasType context element (sortTm elementLevel))
    (headTyping : HasType context head element)
    (tailTyping : HasType context tail (listApp element)) :
    HasType context (consApp element head tail) (listApp element) := by
  have consBodyAsArrows :
      consBodyType =
        arrow (.var 0)
          (arrow (listApp (.var 0)) (listApp (.var 0))) := by
    decide
  have first := Presentation.HasType.appElim
    (consConstant_hasType (context := context)) elementTyping
  have firstNormalized :
      HasType context (.app (.const consName) element)
        (arrow element
          (arrow (listApp element) (listApp element))) := by
    simpa [consType, consBodyAsArrows, liftClosed, Presentation.inst0,
      Presentation.subst0] using first
  have second := Presentation.HasType.appElim firstNormalized headTyping
  have secondNormalized :
      HasType context (.app (.app (.const consName) element) head)
        (arrow (listApp element) (listApp element)) := by
    simpa only [inst0_rename_wk] using second
  have third := Presentation.HasType.appElim secondNormalized tailTyping
  simpa only [consApp, arrow, inst0_rename_wk] using third

/-- Applying a dependent List motive yields a type in the motive universe. -/
theorem motiveApp_hasType {context : Tower.Ctx n}
    {element motive list : Tower.Tm n}
    (motiveTyping : HasType context motive
      (.pi (listApp element) (sortTm motiveLevel)))
    (listTyping : HasType context list (listApp element)) :
    HasType context (.app motive list) (sortTm motiveLevel) := by
  have application := Presentation.HasType.appElim motiveTyping listTyping
  simpa [sortTm, Presentation.inst0, Presentation.subst] using application

def listDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) (.succ elementLevel)

/-- The native family former itself has a formed declaration type. -/
theorem listType_hasType :
    HasType (.nil : Tower.Ctx 0) listType
      (sortTm listDeclarationLevel) := by
  unfold listType listDeclarationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact .sorts (.succ elementLevel) (.succ elementLevel)

def nilDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) elementLevel

/-- The nullary constructor has a formed declaration type. -/
theorem nilType_hasType :
    HasType (.nil : Tower.Ctx 0) nilType
      (sortTm nilDeclarationLevel) := by
  unfold nilType nilDeclarationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply listApp_hasType
    exact Presentation.HasType.var 0
  · exact .sort elementLevel
  · exact .sorts (.succ elementLevel) elementLevel

/-- Below the element-type binder, both constructor arguments and the result
remain in the element universe. -/
def consBodyLevel : LevelExpr :=
  .max elementLevel (.max elementLevel elementLevel)

theorem consBodyType_hasType :
    HasType (.snoc (.nil : Tower.Ctx 0) (sortTm elementLevel))
      consBodyType (sortTm consBodyLevel) := by
  unfold consBodyType consBodyLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 0
  · exact .sort elementLevel
  · apply Presentation.HasType.piForm
    · apply listApp_hasType
      exact Presentation.HasType.var 1
    · exact .sort elementLevel
    · apply listApp_hasType
      exact Presentation.HasType.var 2
    · exact .sort elementLevel
    · exact .sorts elementLevel elementLevel
  · exact .sort (.max elementLevel elementLevel)
  · exact .sorts elementLevel (.max elementLevel elementLevel)

def consDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) consBodyLevel

/-- The binary constructor has a formed declaration type. -/
theorem consType_hasType :
    HasType (.nil : Tower.Ctx 0) consType
      (sortTm consDeclarationLevel) := by
  unfold consType consDeclarationLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · exact consBodyType_hasType
  · exact .sort consBodyLevel
  · exact .sorts (.succ elementLevel) consBodyLevel

/-! ### Dependent eliminator formation -/

def contextA : Tower.Ctx 1 :=
  .snoc .nil (sortTm elementLevel)

def contextAP : Tower.Ctx 2 :=
  .snoc contextA motiveType

def contextAPZ : Tower.Ctx 3 :=
  .snoc contextAP nilCaseType

def contextAPZS : Tower.Ctx 4 :=
  .snoc contextAPZ consCaseType

def motiveTypeLevel : LevelExpr :=
  .max elementLevel (.succ motiveLevel)

/-- A List motive is a dependent family over the native List fibre. -/
theorem motiveType_hasType :
    HasType contextA motiveType (sortTm motiveTypeLevel) := by
  unfold contextA motiveType motiveTypeLevel
  apply Presentation.HasType.piForm
  · apply listApp_hasType
    exact Presentation.HasType.var 0
  · exact .sort elementLevel
  · exact .headType (.sort motiveLevel)
  · exact .sort (.succ motiveLevel)
  · exact .sorts elementLevel (.succ motiveLevel)

/-- The nil branch is itself a type in the motive universe. -/
theorem nilCaseType_hasType :
    HasType contextAP nilCaseType (sortTm motiveLevel) := by
  unfold contextAP nilCaseType
  apply motiveApp_hasType
  · exact Presentation.HasType.var 0
  · apply nilApp_hasType
    exact Presentation.HasType.var 1

def consCaseInnerLevel : LevelExpr :=
  .max motiveLevel motiveLevel

def consCaseTailLevel : LevelExpr :=
  .max elementLevel consCaseInnerLevel

def consCaseLevel : LevelExpr :=
  .max elementLevel consCaseTailLevel

/-- The step branch is a dependent function over the head, tail, and the
recursive hypothesis.  The result mentions the constructor applied to the
same head and tail, so this is genuine dependent elimination. -/
theorem consCaseType_hasType :
    HasType contextAPZ consCaseType (sortTm consCaseLevel) := by
  unfold consCaseType consCaseLevel consCaseTailLevel consCaseInnerLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 2
  · exact .sort elementLevel
  · apply Presentation.HasType.piForm
    · apply listApp_hasType
      exact Presentation.HasType.var 3
    · exact .sort elementLevel
    · apply Presentation.HasType.piForm
      · apply motiveApp_hasType
        · exact Presentation.HasType.var 3
        · exact Presentation.HasType.var 0
      · exact .sort motiveLevel
      · apply motiveApp_hasType
        · exact Presentation.HasType.var 4
        · apply consApp_hasType
          · exact Presentation.HasType.var 5
          · exact Presentation.HasType.var 2
          · exact Presentation.HasType.var 1
      · exact .sort motiveLevel
      · exact .sorts motiveLevel motiveLevel
    · exact .sort (.max motiveLevel motiveLevel)
    · exact .sorts elementLevel (.max motiveLevel motiveLevel)
  · exact .sort (.max elementLevel (.max motiveLevel motiveLevel))
  · exact .sorts elementLevel
      (.max elementLevel (.max motiveLevel motiveLevel))

def eliminateResultLevel : LevelExpr :=
  .max elementLevel motiveLevel

/-- Once all branches are supplied, the eliminator returns a dependent
function over the eliminated list. -/
theorem eliminateResultType_hasType :
    HasType contextAPZS eliminateResultType
      (sortTm eliminateResultLevel) := by
  unfold contextAPZS eliminateResultType eliminateResultLevel
  apply Presentation.HasType.piForm
  · apply listApp_hasType
    exact Presentation.HasType.var 3
  · exact .sort elementLevel
  · apply motiveApp_hasType
    · exact Presentation.HasType.var 3
    · exact Presentation.HasType.var 0
  · exact .sort motiveLevel
  · exact .sorts elementLevel motiveLevel

def eliminateAfterConsLevel : LevelExpr :=
  .max consCaseLevel eliminateResultLevel

def eliminateAfterNilLevel : LevelExpr :=
  .max motiveLevel eliminateAfterConsLevel

def eliminateAfterMotiveLevel : LevelExpr :=
  .max motiveTypeLevel eliminateAfterNilLevel

def eliminateDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) eliminateAfterMotiveLevel

/-- The complete dependent eliminator has a formed closed declaration type.
This is the intrinsic property that the Church canary lacks: native List is
characterized by constructors, dependent use, and both computation rules. -/
theorem eliminateType_hasType :
    HasType (.nil : Tower.Ctx 0) eliminateType
      (sortTm eliminateDeclarationLevel) := by
  unfold eliminateType eliminateDeclarationLevel eliminateAfterMotiveLevel
    eliminateAfterNilLevel eliminateAfterConsLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply Presentation.HasType.piForm
    · exact motiveType_hasType
    · exact .sort motiveTypeLevel
    · apply Presentation.HasType.piForm
      · exact nilCaseType_hasType
      · exact .sort motiveLevel
      · apply Presentation.HasType.piForm
        · exact consCaseType_hasType
        · exact .sort consCaseLevel
        · exact eliminateResultType_hasType
        · exact .sort eliminateResultLevel
        · exact .sorts consCaseLevel eliminateResultLevel
      · exact .sort (.max consCaseLevel eliminateResultLevel)
      · exact .sorts motiveLevel
          (.max consCaseLevel eliminateResultLevel)
    · exact .sort
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel))
    · exact .sorts motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel))
  · exact .sort
      (.max motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel)))
  · exact .sorts (.succ elementLevel)
      (.max motiveTypeLevel
        (.max motiveLevel (.max consCaseLevel eliminateResultLevel)))

/-! ### Identity elimination as an indexed-family instance -/

def contextAX : Tower.Ctx 2 :=
  .snoc contextA (.var 0)

def contextAXP : Tower.Ctx 3 :=
  .snoc contextAX identityMotiveType

def contextAXPD : Tower.Ctx 4 :=
  .snoc contextAXP identityReflCaseType

def identityMotiveInnerLevel : LevelExpr :=
  .max elementLevel (.succ motiveLevel)

def identityMotiveLevel : LevelExpr :=
  .max elementLevel identityMotiveInnerLevel

/-- The path-induction motive is formed over the endpoint and equality
witness indices. -/
theorem identityMotiveType_hasType :
    HasType contextAX identityMotiveType
      (sortTm identityMotiveLevel) := by
  unfold contextAX identityMotiveType identityMotiveLevel
    identityMotiveInnerLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 1
  · exact .sort elementLevel
  · apply Presentation.HasType.piForm
    · apply Presentation.HasType.idForm
      · exact Presentation.HasType.var 2
      · exact .sort elementLevel
      · exact Presentation.HasType.var 1
      · exact Presentation.HasType.var 0
    · exact .sort elementLevel
    · exact .headType (.sort motiveLevel)
    · exact .sort (.succ motiveLevel)
    · exact .sorts elementLevel (.succ motiveLevel)
  · exact .sort (.max elementLevel (.succ motiveLevel))
  · exact .sorts elementLevel
      (.max elementLevel (.succ motiveLevel))

/-- The reflexivity method inhabits the motive specialized to the diagonal
endpoint and reflexivity witness. -/
theorem identityReflCaseType_hasType :
    HasType contextAXP identityReflCaseType (sortTm motiveLevel) := by
  have motiveLookup :
      Ctx.lookup contextAXP 0 =
        (.pi (.var 2)
          (.pi (.id (.var 3) (.var 2) (.var 0))
            (sortTm motiveLevel)) : Tower.Tm 3) := by
    decide
  have motiveTyping :
      HasType contextAXP (.var 0)
        (.pi (.var 2)
          (.pi (.id (.var 3) (.var 2) (.var 0))
            (sortTm motiveLevel))) := by
    simpa only [motiveLookup] using
      (Presentation.HasType.var (R := rules) (Γ := contextAXP) 0)
  have pointTyping : HasType contextAXP (.var 1) (.var 2) := by
    exact Presentation.HasType.var 1
  have motiveAtPoint :=
    Presentation.HasType.appElim motiveTyping pointTyping
  have motiveAtPointType :
      Presentation.inst0 (.var 1 : Tower.Tm 3)
          (.pi (.id (.var 3) (.var 2) (.var 0))
            (sortTm motiveLevel)) =
        (.pi (.id (.var 2) (.var 1) (.var 1))
          (sortTm motiveLevel) : Tower.Tm 3) := by
    decide
  have motiveAtPointNormalized :
      HasType contextAXP (.app (.var 0) (.var 1))
        (.pi (.id (.var 2) (.var 1) (.var 1))
          (sortTm motiveLevel)) := by
    simpa only [motiveAtPointType] using motiveAtPoint
  have reflexivity :
      HasType contextAXP (.refl (.var 1))
        (.id (.var 2) (.var 1) (.var 1)) :=
    Presentation.HasType.reflIntro pointTyping
  have result := Presentation.HasType.appElim
    motiveAtPointNormalized reflexivity
  simpa [identityReflCaseType, sortTm, Presentation.inst0,
    Presentation.subst] using result

def contextAXPDY : Tower.Ctx 5 :=
  .snoc contextAXPD (.var 3)

def contextAXPDYQ : Tower.Ctx 6 :=
  .snoc contextAXPDY (.id (.var 4) (.var 3) (.var 0))

def identityEliminateResultLevel : LevelExpr :=
  .max elementLevel (.max elementLevel motiveLevel)

/-- Path induction returns the motive at the supplied endpoint and equality
witness. -/
theorem identityEliminateResultType_hasType :
    HasType contextAXPD identityEliminateResultType
      (sortTm identityEliminateResultLevel) := by
  unfold identityEliminateResultType identityEliminateResultLevel
  apply Presentation.HasType.piForm
  · exact Presentation.HasType.var 3
  · exact .sort elementLevel
  · apply Presentation.HasType.piForm
    · apply Presentation.HasType.idForm
      · exact Presentation.HasType.var 4
      · exact .sort elementLevel
      · exact Presentation.HasType.var 3
      · exact Presentation.HasType.var 0
    · exact .sort elementLevel
    · have motiveLookup :
          Ctx.lookup contextAXPDYQ 3 =
            (.pi (.var 5)
              (.pi (.id (.var 6) (.var 5) (.var 0))
                (sortTm motiveLevel)) : Tower.Tm 6) := by
        decide
      have motiveTyping :
          HasType contextAXPDYQ (.var 3)
            (.pi (.var 5)
              (.pi (.id (.var 6) (.var 5) (.var 0))
                (sortTm motiveLevel))) := by
        simpa only [motiveLookup] using
          (Presentation.HasType.var (R := rules) (Γ := contextAXPDYQ) 3)
      have endpointTyping :
          HasType contextAXPDYQ (.var 1) (.var 5) := by
        exact Presentation.HasType.var 1
      have first := Presentation.HasType.appElim motiveTyping endpointTyping
      have firstType :
          Presentation.inst0 (.var 1 : Tower.Tm 6)
              (.pi (.id (.var 6) (.var 5) (.var 0))
                (sortTm motiveLevel)) =
            (.pi (.id (.var 5) (.var 4) (.var 1))
              (sortTm motiveLevel) : Tower.Tm 6) := by
        decide
      have firstNormalized :
          HasType contextAXPDYQ (.app (.var 3) (.var 1))
            (.pi (.id (.var 5) (.var 4) (.var 1))
              (sortTm motiveLevel)) := by
        simpa only [firstType] using first
      have equalityTyping :
          HasType contextAXPDYQ (.var 0)
            (.id (.var 5) (.var 4) (.var 1)) := by
        exact Presentation.HasType.var 0
      have result := Presentation.HasType.appElim
        firstNormalized equalityTyping
      simpa [contextAXPDYQ, contextAXPDY, sortTm, Presentation.inst0,
        Presentation.subst] using result
    · exact .sort motiveLevel
    · exact .sorts elementLevel motiveLevel
  · exact .sort (.max elementLevel motiveLevel)
  · exact .sorts elementLevel (.max elementLevel motiveLevel)

def identityAfterReflLevel : LevelExpr :=
  .max motiveLevel identityEliminateResultLevel

def identityAfterMotiveLevel : LevelExpr :=
  .max identityMotiveLevel identityAfterReflLevel

def identityAfterPointLevel : LevelExpr :=
  .max elementLevel identityAfterMotiveLevel

def identityEliminateDeclarationLevel : LevelExpr :=
  .max (.succ elementLevel) identityAfterPointLevel

/-- The fixed-left-endpoint identity eliminator is a formed declaration.
Together with `IotaEvidence.identity`, this places both `J` and its reflexivity
computation rule in the same declaration-aware mechanism as native List. -/
theorem identityEliminateType_hasType :
    HasType (.nil : Tower.Ctx 0) identityEliminateType
      (sortTm identityEliminateDeclarationLevel) := by
  unfold identityEliminateType identityEliminateDeclarationLevel
    identityAfterPointLevel identityAfterMotiveLevel identityAfterReflLevel
  apply Presentation.HasType.piForm
  · exact .headType (.sort elementLevel)
  · exact .sort (.succ elementLevel)
  · apply Presentation.HasType.piForm
    · exact Presentation.HasType.var 0
    · exact .sort elementLevel
    · apply Presentation.HasType.piForm
      · exact identityMotiveType_hasType
      · exact .sort identityMotiveLevel
      · apply Presentation.HasType.piForm
        · exact identityReflCaseType_hasType
        · exact .sort motiveLevel
        · exact identityEliminateResultType_hasType
        · exact .sort identityEliminateResultLevel
        · exact .sorts motiveLevel identityEliminateResultLevel
      · exact .sort identityAfterReflLevel
      · exact .sorts identityMotiveLevel identityAfterReflLevel
    · exact .sort identityAfterMotiveLevel
    · exact .sorts elementLevel identityAfterMotiveLevel
  · exact .sort identityAfterPointLevel
  · exact .sorts (.succ elementLevel) identityAfterPointLevel

/-! ### Canonical typed computation schemas

The raw iota family is closed under every syntactic substitution, including
ill-typed ones, because conversion must be a relation on raw terms.  Its
authoritative source is therefore a typed schema in the declaration
telescope.  Ambient well-typed instances are obtained from these schemas by
typed substitution; raw support is only their operational readout.
-/

/-- The native List eliminator after its four parameters have been supplied
in the declaration telescope `A, P, z, s`. -/
def eliminateAtParameters : Tower.Tm 4 :=
  .app
    (.app
      (.app
        (.app (.const eliminateName) (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

/-- Its dependent result type in that telescope. -/
def eliminateAtParametersType : Tower.Tm 4 :=
  .pi (listApp (.var 3)) (.app (.var 3) (.var 0))

/-- Supplying the declaration telescope to the eliminator yields the expected
dependent function over Lists. -/
theorem eliminateAtParameters_hasType :
    HasType contextAPZS eliminateAtParameters eliminateAtParametersType := by
  have elementTyping :
      HasType contextAPZS (.var 3) (sortTm elementLevel) := by
    exact Presentation.HasType.var 3
  have motiveTyping :
      HasType contextAPZS (.var 2)
        (.pi (listApp (.var 3)) (sortTm motiveLevel)) := by
    exact Presentation.HasType.var 2
  have nilCaseTyping :
      HasType contextAPZS (.var 1)
        (.app (.var 2) (nilApp (.var 3))) := by
    exact Presentation.HasType.var 1
  have consCaseTyping :
      HasType contextAPZS (.var 0)
        (Presentation.rename wk consCaseType) := by
    exact Presentation.HasType.var 0
  have afterElement := Presentation.HasType.appElim
    (eliminateConstant_hasType (context := contextAPZS)) elementTyping
  have afterMotive := Presentation.HasType.appElim afterElement motiveTyping
  have afterNil := Presentation.HasType.appElim afterMotive nilCaseTyping
  have afterCons := Presentation.HasType.appElim afterNil consCaseTyping
  convert afterCons using 1 <;> decide

/-- A native iota receipt retains the rule witness as data in addition to the
common judgment fibre.  Its propositional declaration-step view is derived
below by support erasure. -/
abbrev TypedIotaReceipt (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type :=
  ProofRelevantStepReceipt Tower.rules rawSignature
    proofRelevantIotaComputation context left right type

/-- Logical declaration computation is the support readout of a native iota
receipt. -/
def TypedIotaReceipt.toDeclaredReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (receipt : TypedIotaReceipt context left right type) :
    DeclaredStepReceipt Tower.rules rawSignature context left right type :=
  ProofRelevantStepReceipt.toDeclaredReceipt receipt rfl

/-- Typed substitution acts on the full receipt, including its proof-relevant
rule witness. -/
def TypedIotaReceipt.substitute
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {left right type : Tower.Tm n} (substitution : Sub Tower.Head n m)
    (receipt : TypedIotaReceipt sourceContext left right type)
    (typed : CtxMor rules sourceContext targetContext substitution) :
    TypedIotaReceipt targetContext (Presentation.subst substitution left)
      (Presentation.subst substitution right)
      (Presentation.subst substitution type) :=
  ProofRelevantStepReceipt.substitute substitution receipt typed

/-- The exact typed-substitution image of one native iota schema. -/
abbrev TypedIotaReceipt.InstanceAt
    {sourceContext : Tower.Ctx n}
    {sourceLeft sourceRight sourceType : Tower.Tm n}
    (schema : TypedIotaReceipt sourceContext sourceLeft sourceRight sourceType)
    (targetContext : Tower.Ctx m)
    (left right type : Tower.Tm m) : Type :=
  ProofRelevantStepReceipt.InstanceAt schema targetContext left right type

def TypedIotaReceipt.InstanceAt.toReceipt
    {sourceContext : Tower.Ctx n}
    {sourceLeft sourceRight sourceType : Tower.Tm n}
    {schema : TypedIotaReceipt sourceContext sourceLeft sourceRight sourceType}
    {targetContext : Tower.Ctx m} {left right type : Tower.Tm m}
    (occurrence : schema.InstanceAt targetContext left right type) :
    TypedIotaReceipt targetContext left right type :=
  ProofRelevantStepReceipt.InstanceAt.toReceipt occurrence

def TypedIotaReceipt.identityInstance
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (schema : TypedIotaReceipt context left right type) :
    schema.InstanceAt context left right type :=
  ProofRelevantStepReceipt.identityInstance schema

def nilIotaLeft : Tower.Tm 4 :=
  .app eliminateAtParameters (nilApp (.var 3))

def nilIotaRight : Tower.Tm 4 := .var 1

def nilIotaResultType : Tower.Tm 4 :=
  .app (.var 2) (nilApp (.var 3))

/-- The nil equation is a typed transition in the exact declaration
telescope, not merely an equality between raw endpoints. -/
def nilIotaReceipt :
    TypedIotaReceipt contextAPZS
      nilIotaLeft nilIotaRight nilIotaResultType where
  sourceTyping := by
    have elementTyping :
        HasType contextAPZS (.var 3) (sortTm elementLevel) := by
      exact Presentation.HasType.var 3
    have listTyping := nilApp_hasType elementTyping
    have result := Presentation.HasType.appElim
      eliminateAtParameters_hasType listTyping
    convert result using 1 <;> decide
  targetTyping := by
    exact Presentation.HasType.var 1
  evidence := .nil (.var 3) (.var 2) (.var 1) (.var 0)

/-- Extend the List declaration telescope by a constructor head. -/
def contextAPZSHead : Tower.Ctx 5 :=
  .snoc contextAPZS (.var 3)

/-- Extend it once more by a constructor tail. -/
def contextAPZSHeadTail : Tower.Ctx 6 :=
  .snoc contextAPZSHead (listApp (.var 4))

def eliminateAtConsParameters : Tower.Tm 6 :=
  Presentation.rename wk (Presentation.rename wk eliminateAtParameters)

def eliminateAtConsParametersType : Tower.Tm 6 :=
  .pi (listApp (.var 5)) (.app (.var 5) (.var 0))

theorem eliminateAtConsParameters_hasType :
    HasType contextAPZSHeadTail eliminateAtConsParameters
      eliminateAtConsParametersType := by
  have afterHead := eliminateAtParameters_hasType.weaken
    (extension := (.var 3 : Tower.Tm 4))
  have weakened := afterHead.weaken
    (extension := listApp (.var 4 : Tower.Tm 5))
  unfold contextAPZSHeadTail contextAPZSHead
  convert weakened using 1 <;> decide

def consIotaLeft : Tower.Tm 6 :=
  .app eliminateAtConsParameters
    (consApp (.var 5) (.var 1) (.var 0))

def consIotaRight : Tower.Tm 6 :=
  .app
    (.app
      (.app (.var 2) (.var 1))
      (.var 0))
    (.app eliminateAtConsParameters (.var 0))

def consIotaResultType : Tower.Tm 6 :=
  .app (.var 4) (consApp (.var 5) (.var 1) (.var 0))

/-- The cons equation retains the head, tail, recursive-result derivation,
and common dependent result type. -/
def consIotaReceipt :
    TypedIotaReceipt contextAPZSHeadTail
      consIotaLeft consIotaRight consIotaResultType where
  sourceTyping := by
    have elementTyping :
        HasType contextAPZSHeadTail (.var 5) (sortTm elementLevel) := by
      exact Presentation.HasType.var 5
    have headTyping :
        HasType contextAPZSHeadTail (.var 1) (.var 5) := by
      exact Presentation.HasType.var 1
    have tailTyping :
        HasType contextAPZSHeadTail (.var 0) (listApp (.var 5)) := by
      exact Presentation.HasType.var 0
    have listTyping := consApp_hasType elementTyping headTyping tailTyping
    have result := Presentation.HasType.appElim
      eliminateAtConsParameters_hasType listTyping
    convert result using 1 <;> decide
  targetTyping := by
    have headTyping :
        HasType contextAPZSHeadTail (.var 1) (.var 5) := by
      exact Presentation.HasType.var 1
    have tailTyping :
        HasType contextAPZSHeadTail (.var 0) (listApp (.var 5)) := by
      exact Presentation.HasType.var 0
    have consCaseTyping :
        HasType contextAPZSHeadTail (.var 2)
          (Presentation.rename wk
            (Presentation.rename wk
              (Presentation.rename wk consCaseType))) := by
      exact Presentation.HasType.var 2
    have recursiveTyping := Presentation.HasType.appElim
      eliminateAtConsParameters_hasType tailTyping
    have afterHead := Presentation.HasType.appElim consCaseTyping headTyping
    have afterTail := Presentation.HasType.appElim afterHead tailTyping
    have result := Presentation.HasType.appElim afterTail recursiveTyping
    convert result using 1 <;> decide
  evidence :=
    .cons (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

/-- The identity eliminator after `A, x, P, d` have been supplied. -/
def identityEliminateAtParameters : Tower.Tm 4 :=
  .app
    (.app
      (.app
        (.app (.const identityEliminateName) (.var 3))
        (.var 2))
      (.var 1))
    (.var 0)

def identityEliminateAtParametersType : Tower.Tm 4 :=
  .pi (.var 3)
    (.pi (.id (.var 4) (.var 3) (.var 0))
      (.app (.app (.var 3) (.var 1)) (.var 0)))

theorem identityEliminateAtParameters_hasType :
    HasType contextAXPD identityEliminateAtParameters
      identityEliminateAtParametersType := by
  have elementTyping :
      HasType contextAXPD (.var 3) (sortTm elementLevel) := by
    exact Presentation.HasType.var 3
  have pointTyping : HasType contextAXPD (.var 2) (.var 3) := by
    exact Presentation.HasType.var 2
  have motiveTyping :
      HasType contextAXPD (.var 1)
        (Presentation.rename wk (Presentation.rename wk identityMotiveType)) := by
    exact Presentation.HasType.var 1
  have reflCaseTyping :
      HasType contextAXPD (.var 0)
        (Presentation.rename wk identityReflCaseType) := by
    exact Presentation.HasType.var 0
  have afterElement := Presentation.HasType.appElim
    (identityEliminateConstant_hasType (context := contextAXPD)) elementTyping
  have afterPoint := Presentation.HasType.appElim afterElement pointTyping
  have afterMotive := Presentation.HasType.appElim afterPoint motiveTyping
  have afterRefl := Presentation.HasType.appElim afterMotive reflCaseTyping
  convert afterRefl using 1 <;> decide

def identityIotaLeft : Tower.Tm 4 :=
  .app
    (.app identityEliminateAtParameters (.var 2))
    (.refl (.var 2))

def identityIotaRight : Tower.Tm 4 := .var 0

def identityIotaResultType : Tower.Tm 4 :=
  .app (.app (.var 1) (.var 2)) (.refl (.var 2))

/-- `J` computes on reflexivity in the same typed-schema discipline as the
two List equations. -/
def identityIotaReceipt :
    TypedIotaReceipt contextAXPD
      identityIotaLeft identityIotaRight identityIotaResultType where
  sourceTyping := by
    have pointTyping : HasType contextAXPD (.var 2) (.var 3) := by
      exact Presentation.HasType.var 2
    have equalityTyping :
        HasType contextAXPD (.refl (.var 2))
          (.id (.var 3) (.var 2) (.var 2)) :=
      Presentation.HasType.reflIntro pointTyping
    have afterPoint := Presentation.HasType.appElim
      identityEliminateAtParameters_hasType pointTyping
    have result := Presentation.HasType.appElim afterPoint equalityTyping
    convert result using 1 <;> decide
  targetTyping := by
    exact Presentation.HasType.var 0
  evidence := .identity (.var 3) (.var 2) (.var 1) (.var 0)

/-! ### The exact proof-carrying iota image -/

/-- The named fragment generated by typed substitutions of the three
canonical schemas.  This is an executable-authority image, not a claim that
all declaratively typed raw redexes have already been inverted into it. -/
inductive TypedIotaInstance (context : Tower.Ctx n)
    (left right type : Tower.Tm n) : Type where
  | nil (occurrence :
      nilIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type
  | cons (occurrence :
      consIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type
  | identity (occurrence :
      identityIotaReceipt.InstanceAt context left right type) :
      TypedIotaInstance context left right type

/-- Every recognized instance reconstructs both endpoint typings and its
proof-relevant rule receipt. -/
def TypedIotaInstance.toReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    TypedIotaReceipt context left right type := by
  cases occurrence with
  | nil schemaInstance => exact schemaInstance.toReceipt
  | cons schemaInstance => exact schemaInstance.toReceipt
  | identity schemaInstance => exact schemaInstance.toReceipt

def TypedIotaInstance.toDeclaredReceipt
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    DeclaredStepReceipt Tower.rules rawSignature context left right type :=
  occurrence.toReceipt.toDeclaredReceipt

/-- Subject preservation is structural on the exact proof-carrying image. -/
def TypedIotaInstance.targetTyping
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    HasType context right type :=
  occurrence.toReceipt.targetTyping

/-- A typed iota instance at its principal result, followed by the exact
directed conversion/cumulativity adjustment used by the displayed judgment.
Keeping this adjustment explicit is essential: full subject reduction asks
for the target at the displayed type, whereas exact schema recognition owns
the principal type. -/
structure TypedIotaInstance.Adjusted (context : Tower.Ctx n)
    (left right displayedType : Tower.Tm n) : Type where
  principalType : Tower.Tm n
  principal : TypedIotaInstance context left right principalType
  adjustment : TypeAdjustment rules principalType displayedType

/-- Exact fragment membership embeds into adjusted membership by the
reflexive adjustment. -/
def TypedIotaInstance.asAdjusted
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedIotaInstance context left right type) :
    TypedIotaInstance.Adjusted context left right type where
  principalType := type
  principal := occurrence
  adjustment := .refl type

/-- An adjusted occurrence reconstructs a complete receipt at the displayed
type without erasing its principal schema instance. -/
def TypedIotaInstance.Adjusted.toReceipt
    {context : Tower.Ctx n} {left right displayedType : Tower.Tm n}
    (occurrence : TypedIotaInstance.Adjusted context left right displayedType) :
    TypedIotaReceipt context left right displayedType :=
  let principalReceipt := occurrence.principal.toReceipt
  { sourceTyping := principalReceipt.sourceTyping.adjust occurrence.adjustment
    targetTyping := principalReceipt.targetTyping.adjust occurrence.adjustment
    evidence := principalReceipt.evidence }

/-- In particular, an adjusted occurrence retains target typing at the exact
displayed judgment. -/
def TypedIotaInstance.Adjusted.targetTyping
    {context : Tower.Ctx n} {left right displayedType : Tower.Tm n}
    (occurrence : TypedIotaInstance.Adjusted context left right displayedType) :
    HasType context right displayedType :=
  occurrence.toReceipt.targetTyping

/-- Positive control: a canonical nil computation is recognized exactly and
therefore also in the adjustment-closed subject-reduction image. -/
def canonicalNilInstance :
    TypedIotaInstance contextAPZS
      nilIotaLeft nilIotaRight nilIotaResultType :=
  .nil nilIotaReceipt.identityInstance

def canonicalNilAdjusted :
    TypedIotaInstance.Adjusted contextAPZS
      nilIotaLeft nilIotaRight nilIotaResultType :=
  canonicalNilInstance.asAdjusted

def canonicalConsInstance :
    TypedIotaInstance contextAPZSHeadTail
      consIotaLeft consIotaRight consIotaResultType :=
  .cons consIotaReceipt.identityInstance

def canonicalConsAdjusted :
    TypedIotaInstance.Adjusted contextAPZSHeadTail
      consIotaLeft consIotaRight consIotaResultType :=
  canonicalConsInstance.asAdjusted

def canonicalIdentityInstance :
    TypedIotaInstance contextAXPD
      identityIotaLeft identityIotaRight identityIotaResultType :=
  .identity identityIotaReceipt.identityInstance

def canonicalIdentityAdjusted :
    TypedIotaInstance.Adjusted contextAXPD
      identityIotaLeft identityIotaRight identityIotaResultType :=
  canonicalIdentityInstance.asAdjusted

/-- The remaining coverage theorem required for full raw-signature
authority: every raw iota edge from a typed source must be reconstructible as
a typed substitution instance at a principal type, followed by the actual
display adjustment.  Exact instances remain the smaller executable fragment
above; this stronger relation is the subject-reduction boundary. -/
abbrev TypedIotaCoverage : Prop :=
  ∀ {n : Nat} {context : Tower.Ctx n} {left right type : Tower.Tm n},
    IotaEvidence n left right →
    HasType context left type →
      Nonempty (TypedIotaInstance.Adjusted context left right type)

/-- Exactly the partial application spines whose Pi typings are inspected by
the native List and identity computation authority.  Naming this image keeps
the conversion obligation fragment-scoped: unrelated Prime functions and
guest calculi are not silently pulled into the theorem. -/
inductive NativeFunctionSpine : (n : Nat) → Tower.Tm n → Prop where
  | eliminateConstant :
      NativeFunctionSpine n (.const eliminateName)
  | eliminateElement (element : Tower.Tm n) :
      NativeFunctionSpine n (.app (.const eliminateName) element)
  | eliminateMotive (element motive : Tower.Tm n) :
      NativeFunctionSpine n
        (.app (.app (.const eliminateName) element) motive)
  | eliminateNilCase (element motive nilCase : Tower.Tm n) :
      NativeFunctionSpine n
        (.app (.app (.app (.const eliminateName) element) motive) nilCase)
  | eliminateConsCase
      (element motive nilCase consCase : Tower.Tm n) :
      NativeFunctionSpine n
        (.app
          (.app (.app (.app (.const eliminateName) element) motive) nilCase)
          consCase)
  | consConstant : NativeFunctionSpine n (.const consName)
  | consElement (element : Tower.Tm n) :
      NativeFunctionSpine n (.app (.const consName) element)
  | consHead (element head : Tower.Tm n) :
      NativeFunctionSpine n
        (.app (.app (.const consName) element) head)
  | identityConstant :
      NativeFunctionSpine n (.const identityEliminateName)
  | identityElement (element : Tower.Tm n) :
      NativeFunctionSpine n
        (.app (.const identityEliminateName) element)
  | identityPoint (element point : Tower.Tm n) :
      NativeFunctionSpine n
        (.app (.app (.const identityEliminateName) element) point)
  | identityMotive (element point motive : Tower.Tm n) :
      NativeFunctionSpine n
        (.app
          (.app (.app (.const identityEliminateName) element) point)
          motive)
  | identityReflCase
      (element point motive reflCase : Tower.Tm n) :
      NativeFunctionSpine n
        (.app
          (.app
            (.app (.app (.const identityEliminateName) element) point)
            motive)
          reflCase)
  | identityEndpoint
      (element point motive reflCase endpoint : Tower.Tm n) :
      NativeFunctionSpine n
        (.app
          (.app
            (.app
              (.app (.app (.const identityEliminateName) element) point)
              motive)
            reflCase)
          endpoint)

abbrev NativeSpineAlignment : Prop :=
  PiTypingAlignmentOn (Head := Tower.Head) rules NativeFunctionSpine

/-! ### Deriving spine alignment from conversion constructor laws -/

/-- The constant base of the List-eliminator spine needs only functional
declaration lookup and the generic Pi conversion boundary. -/
private theorem eliminateConstantPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.const eliminateName) (.pi domain₁ codomain₁))
    (second : HasType context (.const eliminateName) (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.constantPiAlignment boundary first second

private theorem eliminateElementPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.app (.const eliminateName) element)
      (.pi domain₁ codomain₁))
    (second : HasType context (.app (.const eliminateName) element)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      eliminateConstantPiAlignment boundary firstFunction secondFunction)
    first second

private theorem eliminateMotivePiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element motive : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app (.app (.const eliminateName) element) motive)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app (.app (.const eliminateName) element) motive)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      eliminateElementPiAlignment boundary firstFunction secondFunction)
    first second

private theorem eliminateNilCasePiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element motive nilCase : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app (.app (.app (.const eliminateName) element) motive) nilCase)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app (.app (.app (.const eliminateName) element) motive) nilCase)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      eliminateMotivePiAlignment boundary firstFunction secondFunction)
    first second

private theorem eliminateConsCasePiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {element motive nilCase consCase : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app
        (.app (.app (.app (.const eliminateName) element) motive) nilCase)
        consCase)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app
        (.app (.app (.app (.const eliminateName) element) motive) nilCase)
        consCase)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      eliminateNilCasePiAlignment boundary firstFunction secondFunction)
    first second

private theorem consConstantPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.const consName) (.pi domain₁ codomain₁))
    (second : HasType context (.const consName) (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.constantPiAlignment boundary first second

private theorem consElementPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.app (.const consName) element)
      (.pi domain₁ codomain₁))
    (second : HasType context (.app (.const consName) element)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      consConstantPiAlignment boundary firstFunction secondFunction)
    first second

private theorem consHeadPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element head : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app (.app (.const consName) element) head)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app (.app (.const consName) element) head)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      consElementPiAlignment boundary firstFunction secondFunction)
    first second

private theorem identityConstantPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.const identityEliminateName)
      (.pi domain₁ codomain₁))
    (second : HasType context (.const identityEliminateName)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.constantPiAlignment boundary first second

private theorem identityElementPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context (.app (.const identityEliminateName) element)
      (.pi domain₁ codomain₁))
    (second : HasType context (.app (.const identityEliminateName) element)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      identityConstantPiAlignment boundary firstFunction secondFunction)
    first second

private theorem identityPointPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element point : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app (.app (.const identityEliminateName) element) point)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app (.app (.const identityEliminateName) element) point)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      identityElementPiAlignment boundary firstFunction secondFunction)
    first second

private theorem identityMotivePiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n} {element point motive : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app
        (.app (.app (.const identityEliminateName) element) point)
        motive)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app
        (.app (.app (.const identityEliminateName) element) point)
        motive)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      identityPointPiAlignment boundary firstFunction secondFunction)
    first second

private theorem identityReflCasePiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {element point motive reflCase : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app
        (.app
          (.app (.app (.const identityEliminateName) element) point)
          motive)
        reflCase)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app
        (.app
          (.app (.app (.const identityEliminateName) element) point)
          motive)
        reflCase)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      identityMotivePiAlignment boundary firstFunction secondFunction)
    first second

private theorem identityEndpointPiAlignment
    (boundary : PiConversionBoundary rules)
    {context : Tower.Ctx n}
    {element point motive reflCase endpoint : Tower.Tm n}
    {domain₁ domain₂ : Tower.Tm n}
    {codomain₁ codomain₂ : Tower.Tm (n + 1)}
    (first : HasType context
      (.app
        (.app
          (.app
            (.app (.app (.const identityEliminateName) element) point)
            motive)
          reflCase)
        endpoint)
      (.pi domain₁ codomain₁))
    (second : HasType context
      (.app
        (.app
          (.app
            (.app (.app (.const identityEliminateName) element) point)
            motive)
          reflCase)
        endpoint)
      (.pi domain₂ codomain₂)) :
    Conv rules.headEq domain₁ domain₂ rules.computation ∧
      Conv rules.headEq codomain₁ codomain₂ rules.computation :=
  Presentation.HasType.applicationPiAlignment boundary
    (fun firstFunction secondFunction =>
      identityReflCasePiAlignment boundary firstFunction secondFunction)
    first second

/-- The complete native-spine typing-alignment obligation follows from the
strictly smaller conversion boundary.  The proof is structural on the named
spines: constants use functional declaration lookup, and each partial
application propagates alignment by generic application generation. -/
def nativeSpineAlignmentOfPiConversionBoundary
    (boundary : PiConversionBoundary rules) : NativeSpineAlignment where
  align := by
    intro n context term domain₁ domain₂ codomain₁ codomain₂ recognized
      first second
    cases recognized with
    | eliminateConstant =>
        exact eliminateConstantPiAlignment boundary first second
    | eliminateElement element =>
        exact eliminateElementPiAlignment boundary first second
    | eliminateMotive element motive =>
        exact eliminateMotivePiAlignment boundary first second
    | eliminateNilCase element motive nilCase =>
        exact eliminateNilCasePiAlignment boundary first second
    | eliminateConsCase element motive nilCase consCase =>
        exact eliminateConsCasePiAlignment boundary first second
    | consConstant =>
        exact consConstantPiAlignment boundary first second
    | consElement element =>
        exact consElementPiAlignment boundary first second
    | consHead element head =>
        exact consHeadPiAlignment boundary first second
    | identityConstant =>
        exact identityConstantPiAlignment boundary first second
    | identityElement element =>
        exact identityElementPiAlignment boundary first second
    | identityPoint element point =>
        exact identityPointPiAlignment boundary first second
    | identityMotive element point motive =>
        exact identityMotivePiAlignment boundary first second
    | identityReflCase element point motive reflCase =>
        exact identityReflCasePiAlignment boundary first second
    | identityEndpoint element point motive reflCase endpoint =>
        exact identityEndpointPiAlignment boundary first second

/-! ### Reconstruction from fragment conversion coherence -/

/-- The unique substitution out of the empty declaration telescope. -/
def emptySchemaSubstitution : Sub Tower.Head 0 n :=
  fun index => Fin.elim0 index

/-- Successive prefixes of the native List declaration telescope.  Naming
them exposes the standard relationship between repeated `inst0` and context
comprehension, rather than relying on a large reducibility computation. -/
def elementSchemaSubstitution (element : Tower.Tm n) : Sub Tower.Head 1 n :=
  consSub element emptySchemaSubstitution

@[simp] theorem elementSchemaSubstitution_zero
    (element : Tower.Tm n) :
    elementSchemaSubstitution element (0 : Fin 1) = element := by
  rfl

def motiveSchemaSubstitution (element motive : Tower.Tm n) :
    Sub Tower.Head 2 n :=
  consSub motive (elementSchemaSubstitution element)

def nilCaseSchemaSubstitution (element motive nilCase : Tower.Tm n) :
    Sub Tower.Head 3 n :=
  consSub nilCase (motiveSchemaSubstitution element motive)

/-- The simultaneous substitution represented by a nil-iota occurrence.
The newest declaration variable is the constructor branch, so the nesting of
`consSub` follows the declaration telescope rather than surface argument
order. -/
def nilSchemaSubstitution
    (element motive nilCase consCase : Tower.Tm n) :
    Sub Tower.Head 4 n :=
  consSub consCase (nilCaseSchemaSubstitution element motive nilCase)

/-- The simultaneous substitution represented by the identity-iota schema
telescope `A,x,P,d`.  It shares only the structural context-comprehension
operation with List; its mathematical role is the parameterization of `J`. -/
def identitySchemaSubstitution
    (element point motive reflCase : Tower.Tm n) :
    Sub Tower.Head 4 n :=
  consSub reflCase
    (consSub motive
      (consSub point
        (consSub element emptySchemaSubstitution)))

@[simp] theorem motiveSchemaSubstitution_one
    (element motive : Tower.Tm n) :
    motiveSchemaSubstitution element motive (1 : Fin 2) = element := by
  rfl

@[simp] theorem nilSchemaSubstitution_two
    (element motive nilCase consCase : Tower.Tm n) :
    nilSchemaSubstitution element motive nilCase consCase (2 : Fin 4) =
      motive := by
  rfl

@[simp] theorem nilSchemaSubstitution_three
    (element motive nilCase consCase : Tower.Tm n) :
    nilSchemaSubstitution element motive nilCase consCase (3 : Fin 4) =
      element := by
  rfl

@[simp] theorem identitySchemaSubstitution_one
    (element point motive reflCase : Tower.Tm n) :
    identitySchemaSubstitution element point motive reflCase (1 : Fin 4) =
      motive := by
  rfl

@[simp] theorem identitySchemaSubstitution_two
    (element point motive reflCase : Tower.Tm n) :
    identitySchemaSubstitution element point motive reflCase (2 : Fin 4) =
      point := by
  rfl

@[simp] theorem identitySchemaSubstitution_three
    (element point motive reflCase : Tower.Tm n) :
    identitySchemaSubstitution element point motive reflCase (3 : Fin 4) =
      element := by
  rfl

@[simp] theorem subst_motiveType_elementSchema
    (element : Tower.Tm n) :
  Presentation.subst (elementSchemaSubstitution element) motiveType =
      .pi (listApp element) (sortTm motiveLevel) := by
  simp [elementSchemaSubstitution, motiveType, listApp, sortTm,
    Presentation.subst]

@[simp] theorem subst_nilCaseType_motiveSchema
    (element motive : Tower.Tm n) :
  Presentation.subst (motiveSchemaSubstitution element motive) nilCaseType =
      .app motive (nilApp element) := by
  simp [motiveSchemaSubstitution, elementSchemaSubstitution,
    nilCaseType, nilApp, Presentation.subst]
  exact motiveSchemaSubstitution_one element motive

@[simp] theorem subst_nilIotaResult_nilSchema
    (element motive nilCase consCase : Tower.Tm n) :
    Presentation.subst
        (nilSchemaSubstitution element motive nilCase consCase)
        nilIotaResultType =
      .app motive (nilApp element) := by
  simp [nilSchemaSubstitution, nilCaseSchemaSubstitution,
    motiveSchemaSubstitution, elementSchemaSubstitution,
    nilIotaResultType, nilApp, Presentation.subst]
  exact ⟨nilSchemaSubstitution_two element motive nilCase consCase,
    nilSchemaSubstitution_three element motive nilCase consCase⟩

/-- Substituting the four List-eliminator parameters exposes its canonical
dependent function type.  Keeping this equality named avoids re-running a
large de Bruijn reduction at every constructor computation. -/
@[simp] theorem subst_eliminateResult_nilSchema
    (element motive nilCase consCase : Tower.Tm n) :
    Presentation.subst
        (nilSchemaSubstitution element motive nilCase consCase)
        eliminateResultType =
      .pi (listApp element)
        (.app (Presentation.rename wk motive) (.var 0)) := by
  simp [nilSchemaSubstitution, nilCaseSchemaSubstitution,
    motiveSchemaSubstitution, elementSchemaSubstitution,
    eliminateResultType, listApp, Presentation.subst]
  exact ⟨nilSchemaSubstitution_three element motive nilCase consCase,
    congrArg (Presentation.rename wk)
      (nilSchemaSubstitution_two element motive nilCase consCase)⟩

/-- Substitution of `A,x,P,d` exposes the canonical two-argument result of
path induction before the endpoint and equality witness are supplied. -/
@[simp] theorem subst_identityEliminateResult_identitySchema
    (element point motive reflCase : Tower.Tm n) :
    Presentation.subst
        (identitySchemaSubstitution element point motive reflCase)
        identityEliminateResultType =
      .pi element
        (.pi
          (.id (Presentation.rename wk element)
            (Presentation.rename wk point) (.var 0))
          (.app
            (.app
              (Presentation.rename wk (Presentation.rename wk motive))
              (.var 1))
            (.var 0))) := by
  simp [identitySchemaSubstitution, identityEliminateResultType,
    Presentation.subst]
  refine ⟨identitySchemaSubstitution_three element point motive reflCase,
    ⟨?_, ?_⟩⟩
  · exact ⟨
      congrArg (Presentation.rename wk)
        (identitySchemaSubstitution_three element point motive reflCase),
      congrArg (Presentation.rename wk)
        (identitySchemaSubstitution_two element point motive reflCase)⟩
  · refine ⟨?_, rfl⟩
    change Presentation.rename wk
        (Presentation.rename wk
          (identitySchemaSubstitution element point motive reflCase 1)) =
      Presentation.rename (fun index => wk (wk index)) motive
    rw [identitySchemaSubstitution_one]
    exact Presentation.rename_comp wk wk motive

/-- Repeated opening of a lifted closed two-variable body agrees with the
simultaneous context-comprehension substitution. -/
theorem instantiateTwo_eq_subst
    (element motive : Tower.Tm n) (body : Tower.Tm 2) :
    Presentation.subst (subst0 motive)
        (Presentation.subst (liftSub (subst0 element))
          (Presentation.rename (liftRen (liftRen Fin.elim0)) body)) =
      Presentation.subst (motiveSchemaSubstitution element motive) body := by
  simp only [Presentation.subst_rename, Presentation.subst_comp]
  apply Presentation.subst_ext
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) prior
    change Presentation.inst0 motive (Presentation.rename wk element) = element
    exact Presentation.inst0_rename_wk motive element

/-- Three repeated dependent applications agree with substitution by the
`A,P,z` prefix of the declaration telescope. -/
theorem instantiateThree_eq_subst
    (element motive nilCase : Tower.Tm n) (body : Tower.Tm 3) :
    Presentation.subst (subst0 nilCase)
        (Presentation.subst (liftSub (subst0 motive))
          (Presentation.subst (liftSub (liftSub (subst0 element)))
            (Presentation.rename
              (liftRen (liftRen (liftRen Fin.elim0))) body))) =
      Presentation.subst
        (nilCaseSchemaSubstitution element motive nilCase) body := by
  simp only [Presentation.subst_rename, Presentation.subst_comp]
  apply Presentation.subst_ext
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · refine Fin.cases ?_ (fun earlier => ?_) prior
    · change Presentation.inst0 nilCase (Presentation.rename wk motive) = motive
      exact Presentation.inst0_rename_wk nilCase motive
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) earlier
      change _ = element
      have motiveCancels :
          Presentation.subst (subst0 motive)
              (Presentation.rename wk element) = element :=
        Presentation.inst0_rename_wk motive element
      calc
        _ = Presentation.subst (subst0 nilCase)
              (Presentation.subst (liftSub (subst0 motive))
                (Presentation.rename wk (Presentation.rename wk element))) := by
              exact (Presentation.subst_comp
                (subst0 nilCase) (liftSub (subst0 motive))
                (Presentation.rename wk (Presentation.rename wk element))).symm
        _ = Presentation.subst (subst0 nilCase)
              (Presentation.rename wk
                (Presentation.subst (subst0 motive)
                  (Presentation.rename wk element))) := by
              rw [Presentation.subst_liftSub_wk]
        _ = Presentation.subst (subst0 nilCase)
              (Presentation.rename wk element) := by
              rw [motiveCancels]
        _ = element := Presentation.inst0_rename_wk nilCase element

/-- Four repeated dependent applications agree with substitution by the
complete `A,P,z,s` List eliminator telescope. -/
theorem instantiateFour_eq_subst
    (element motive nilCase consCase : Tower.Tm n) (body : Tower.Tm 4) :
    Presentation.subst (subst0 consCase)
        (Presentation.subst (liftSub (subst0 nilCase))
          (Presentation.subst (liftSub (liftSub (subst0 motive)))
            (Presentation.subst
              (liftSub (liftSub (liftSub (subst0 element))))
              (Presentation.rename
                (liftRen (liftRen (liftRen (liftRen Fin.elim0)))) body)))) =
      Presentation.subst
        (nilSchemaSubstitution element motive nilCase consCase) body := by
  simp only [Presentation.subst_rename, Presentation.subst_comp]
  apply Presentation.subst_ext
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · refine Fin.cases ?_ (fun earlier => ?_) prior
    · change Presentation.inst0 consCase
        (Presentation.rename wk nilCase) = nilCase
      exact Presentation.inst0_rename_wk consCase nilCase
    · refine Fin.cases ?_ (fun oldest => ?_) earlier
      · change _ = motive
        have nilCancels :
            Presentation.subst (subst0 nilCase)
                (Presentation.rename wk motive) = motive :=
          Presentation.inst0_rename_wk nilCase motive
        calc
          _ = Presentation.subst (subst0 consCase)
                (Presentation.subst (liftSub (subst0 nilCase))
                  (Presentation.rename wk (Presentation.rename wk motive))) := by
                exact (Presentation.subst_comp
                  (subst0 consCase) (liftSub (subst0 nilCase))
                  (Presentation.rename wk
                    (Presentation.rename wk motive))).symm
          _ = Presentation.subst (subst0 consCase)
                (Presentation.rename wk
                  (Presentation.subst (subst0 nilCase)
                    (Presentation.rename wk motive))) := by
                rw [Presentation.subst_liftSub_wk]
          _ = Presentation.subst (subst0 consCase)
                (Presentation.rename wk motive) := by rw [nilCancels]
          _ = motive := Presentation.inst0_rename_wk consCase motive
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) oldest
        change _ = element
        have motiveCancels :
            Presentation.subst (subst0 motive)
                (Presentation.rename wk element) = element :=
          Presentation.inst0_rename_wk motive element
        have nilCancels :
            Presentation.subst (subst0 nilCase)
                (Presentation.rename wk element) = element :=
          Presentation.inst0_rename_wk nilCase element
        rw [← Presentation.subst_comp, ← Presentation.subst_comp]
        change Presentation.subst (subst0 consCase)
          (Presentation.subst (liftSub (subst0 nilCase))
            (Presentation.subst (liftSub (liftSub (subst0 motive)))
              (Presentation.rename wk
                (Presentation.rename wk
                  (Presentation.rename wk element))))) = element
        simp only [Presentation.subst_liftSub_wk, motiveCancels,
          nilCancels]
        exact Presentation.inst0_rename_wk consCase element

/-- The reusable inversion result for a fully applied List eliminator.  It
recovers the typed declaration substitution, the eliminated List argument,
and the directed adjustment from the principal dependent result.  Constructor
specific reconstruction below consumes this one common theorem. -/
structure EliminatorApplicationTyping
    (context : Tower.Ctx n)
    (element motive nilCase consCase list displayedType : Tower.Tm n) : Prop where
  parametersTyped :
    CtxMor rules contextAPZS context
      (nilSchemaSubstitution element motive nilCase consCase)
  listTyped : HasType context list (listApp element)
  adjustment : TypeAdjustment rules (.app motive list) displayedType

/-- Inversion of the common eliminator spine, independently of which List
constructor supplied its final argument. -/
theorem eliminateApplicationTyping
    (alignment : NativeSpineAlignment)
    {context : Tower.Ctx n}
    {element motive nilCase consCase list type : Tower.Tm n}
    (sourceTyping : HasType context
      (eliminateApp element motive nilCase consCase list) type) :
    EliminatorApplicationTyping context element motive nilCase consCase
      list type := by
  rcases sourceTyping.appGeneration with
    ⟨_, _, afterConsObserved, _, _⟩
  rcases afterConsObserved.appGeneration with
    ⟨_, _, afterNilObserved, _, _⟩
  rcases afterNilObserved.appGeneration with
    ⟨_, _, afterMotiveObserved, _, _⟩
  rcases afterMotiveObserved.appGeneration with
    ⟨_, _, afterElementObserved, _, _⟩
  have first := HasType.appAgainstPrincipalOn alignment
    NativeFunctionSpine.eliminateConstant
    (eliminateConstant_hasType (context := context)) afterElementObserved
  have second := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.eliminateElement element) first.2.1
    afterMotiveObserved
  have third := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.eliminateMotive element motive) second.2.1
    afterNilObserved
  have fourth := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.eliminateNilCase element motive nilCase) third.2.1
    afterConsObserved
  let emptySub : Sub Tower.Head 0 n := emptySchemaSubstitution
  let elementSub : Sub Tower.Head 1 n := elementSchemaSubstitution element
  let motiveSub : Sub Tower.Head 2 n :=
    motiveSchemaSubstitution element motive
  let nilCaseSub : Sub Tower.Head 3 n :=
    nilCaseSchemaSubstitution element motive nilCase
  let schemaSub : Sub Tower.Head 4 n :=
    nilSchemaSubstitution element motive nilCase consCase
  have afterBranchesPrincipal :
      HasType context
        (.app
          (.app
            (.app
              (.app (.const eliminateName) element)
              motive)
            nilCase)
          consCase)
        (.pi (listApp element)
          (.app (Presentation.rename wk motive) (.var 0))) := by
    rw [← subst_eliminateResult_nilSchema]
    rw [← instantiateFour_eq_subst element motive nilCase consCase
      eliminateResultType]
    exact fourth.2.1
  have fifth := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.eliminateConsCase
      element motive nilCase consCase)
    afterBranchesPrincipal sourceTyping
  have emptyTyped :
      CtxMor rules (.nil : Tower.Ctx 0) context emptySub := by
    intro index
    exact Fin.elim0 index
  have elementTyped : CtxMor rules contextA context elementSub := by
    apply CtxMor.extend emptyTyped
    convert first.1 using 1
    simp [emptySub, sortTm, Presentation.subst, Presentation.rename]
  have motiveTyped : CtxMor rules contextAP context motiveSub := by
    apply CtxMor.extend elementTyped
    simpa [elementSub, motiveSub, contextAP, motiveType, listApp, sortTm,
      eliminateType, liftClosed, Presentation.inst0, Presentation.subst,
      Presentation.subst0, Presentation.rename, Presentation.liftSub,
      Presentation.liftRen] using second.1
  have nilCaseTyped : CtxMor rules contextAPZ context nilCaseSub := by
    apply CtxMor.extend motiveTyped
    change HasType context nilCase
      (Presentation.subst
        (motiveSchemaSubstitution element motive) nilCaseType)
    rw [← instantiateTwo_eq_subst element motive nilCaseType]
    exact third.1
  have schemaTyped : CtxMor rules contextAPZS context schemaSub := by
    apply CtxMor.extend nilCaseTyped
    change HasType context consCase
      (Presentation.subst
        (nilCaseSchemaSubstitution element motive nilCase) consCaseType)
    rw [← instantiateThree_eq_subst element motive nilCase consCaseType]
    exact fourth.1
  have finalAdjustment : TypeAdjustment rules (.app motive list) type := by
    have motiveCancels :
        Presentation.subst (subst0 list)
            (Presentation.rename wk motive) = motive :=
      Presentation.inst0_rename_wk list motive
    simpa [Presentation.inst0, Presentation.subst,
      Presentation.subst0, motiveCancels] using fifth.2.2
  exact
    { parametersTyped := schemaTyped
      listTyped := fifth.1
      adjustment := finalAdjustment }

/-- A typed nil-iota source determines the exact canonical schema instance
plus the directed adjustment from its principal result to the displayed
type, provided the fragment has earned dependent-function typing coherence. -/
theorem nilAdjustedOfTyping
    (alignment : NativeSpineAlignment)
    {context : Tower.Ctx n} {element motive nilCase consCase type : Tower.Tm n}
    (sourceTyping : HasType context
      (eliminateApp element motive nilCase consCase (nilApp element)) type) :
    Nonempty
      (TypedIotaInstance.Adjusted context
        (eliminateApp element motive nilCase consCase (nilApp element))
        nilCase type) := by
  have recovered := eliminateApplicationTyping alignment sourceTyping
  let occurrence : nilIotaReceipt.InstanceAt context
      (eliminateApp element motive nilCase consCase (nilApp element))
      nilCase (.app motive (nilApp element)) :=
    { substitution := nilSchemaSubstitution element motive nilCase consCase
      typed := recovered.parametersTyped
      sourceEquation := by rfl
      targetEquation := by rfl
      typeEquation := by rfl }
  refine ⟨
    { principalType := .app motive (nilApp element)
      principal := .nil occurrence
      adjustment := recovered.adjustment }⟩

/-- Exact constructor-argument typings recovered from a typed `cons` spine.
The result is deliberately propositional: executable authorities retain the
original derivations in their Type-valued receipts instead of extracting
them from declarative support. -/
structure ConsApplicationTyping
    (context : Tower.Ctx n) (element head tail : Tower.Tm n) : Prop where
  headTyped : HasType context head element
  tailTyped : HasType context tail (listApp element)

theorem consApplicationTyping
    (alignment : NativeSpineAlignment)
    {context : Tower.Ctx n} {element head tail : Tower.Tm n}
    (typing : HasType context (consApp element head tail)
      (listApp element)) :
    ConsApplicationTyping context element head tail := by
  rcases typing.appGeneration with
    ⟨_, _, afterHeadObserved, _, _⟩
  rcases afterHeadObserved.appGeneration with
    ⟨_, _, afterElementObserved, _, _⟩
  have first := HasType.appAgainstPrincipalOn alignment
    NativeFunctionSpine.consConstant
    (consConstant_hasType (context := context)) afterElementObserved
  have second := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.consElement element) first.2.1 afterHeadObserved
  have third := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.consHead element head) second.2.1 typing
  have tailTyped : HasType context tail (listApp element) := by
    have normalized := third.1
    rw [instantiateTwo_eq_subst element head (listApp (.var 1))] at normalized
    change HasType context tail
      (listApp (motiveSchemaSubstitution element head (1 : Fin 2))) at normalized
    rw [motiveSchemaSubstitution_one] at normalized
    exact normalized
  exact
    { headTyped := second.1
      tailTyped := tailTyped }

/-- Simultaneous substitution for the complete cons-iota schema telescope
`A,P,z,s,head,tail`. -/
def consSchemaSubstitution
    (element motive nilCase consCase head tail : Tower.Tm n) :
    Sub Tower.Head 6 n :=
  consSub tail
    (consSub head
      (nilSchemaSubstitution element motive nilCase consCase))

/-- A typed cons-iota source reconstructs the six-variable canonical schema
and retains the adjustment from `P (cons A head tail)` to the displayed type. -/
theorem consAdjustedOfTyping
    (alignment : NativeSpineAlignment)
    {context : Tower.Ctx n}
    {element motive nilCase consCase head tail type : Tower.Tm n}
    (sourceTyping : HasType context
      (eliminateApp element motive nilCase consCase
        (consApp element head tail)) type) :
    Nonempty
      (TypedIotaInstance.Adjusted context
        (eliminateApp element motive nilCase consCase
          (consApp element head tail))
        (.app (.app (.app consCase head) tail)
          (eliminateApp element motive nilCase consCase tail))
        type) := by
  have recovered := eliminateApplicationTyping alignment sourceTyping
  have constructorArguments :=
    consApplicationTyping alignment recovered.listTyped
  let parameterSub : Sub Tower.Head 4 n :=
    nilSchemaSubstitution element motive nilCase consCase
  let headSub : Sub Tower.Head 5 n := consSub head parameterSub
  let schemaSub : Sub Tower.Head 6 n := consSub tail headSub
  have parameterElement : parameterSub (3 : Fin 4) = element := by
    exact nilSchemaSubstitution_three element motive nilCase consCase
  have headSubTyped : CtxMor rules contextAPZSHead context headSub := by
    apply CtxMor.extend recovered.parametersTyped
    change HasType context head (parameterSub (3 : Fin 4))
    rw [parameterElement]
    exact constructorArguments.headTyped
  have headSubElement : headSub (4 : Fin 5) = element := by
    change parameterSub (3 : Fin 4) = element
    exact parameterElement
  have schemaTyped : CtxMor rules contextAPZSHeadTail context schemaSub := by
    apply CtxMor.extend headSubTyped
    change HasType context tail (listApp (headSub (4 : Fin 5)))
    rw [headSubElement]
    exact constructorArguments.tailTyped
  let occurrence : consIotaReceipt.InstanceAt context
      (eliminateApp element motive nilCase consCase
        (consApp element head tail))
      (.app (.app (.app consCase head) tail)
        (eliminateApp element motive nilCase consCase tail))
      (.app motive (consApp element head tail)) :=
    { substitution := schemaSub
      typed := schemaTyped
      sourceEquation := by rfl
      targetEquation := by rfl
      typeEquation := by rfl }
  refine ⟨
    { principalType := .app motive (consApp element head tail)
      principal := .cons occurrence
      adjustment := recovered.adjustment }⟩

/-- A typed reflexivity redex for `J` reconstructs the canonical
`A,x,P,d` schema and the displayed-type adjustment.  Thus identity
elimination and both List equations cross the same proof-carrying boundary. -/
theorem identityAdjustedOfTyping
    (alignment : NativeSpineAlignment)
    {context : Tower.Ctx n}
    {element point motive reflCase type : Tower.Tm n}
    (sourceTyping : HasType context
      (identityEliminateApp element point motive reflCase point
        (.refl point)) type) :
    Nonempty
      (TypedIotaInstance.Adjusted context
        (identityEliminateApp element point motive reflCase point
          (.refl point))
        reflCase type) := by
  rcases sourceTyping.appGeneration with
    ⟨_, _, afterEndpointObserved, _, _⟩
  rcases afterEndpointObserved.appGeneration with
    ⟨_, _, afterReflCaseObserved, _, _⟩
  rcases afterReflCaseObserved.appGeneration with
    ⟨_, _, afterMotiveObserved, _, _⟩
  rcases afterMotiveObserved.appGeneration with
    ⟨_, _, afterPointObserved, _, _⟩
  rcases afterPointObserved.appGeneration with
    ⟨_, _, afterElementObserved, _, _⟩
  have first := HasType.appAgainstPrincipalOn alignment
    NativeFunctionSpine.identityConstant
    (identityEliminateConstant_hasType (context := context))
    afterElementObserved
  have second := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.identityElement element) first.2.1
    afterPointObserved
  have third := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.identityPoint element point) second.2.1
    afterMotiveObserved
  have fourth := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.identityMotive element point motive) third.2.1
    afterReflCaseObserved
  let emptySub : Sub Tower.Head 0 n := emptySchemaSubstitution
  let elementSub : Sub Tower.Head 1 n := elementSchemaSubstitution element
  let pointSub : Sub Tower.Head 2 n :=
    motiveSchemaSubstitution element point
  let motiveSub : Sub Tower.Head 3 n :=
    nilCaseSchemaSubstitution element point motive
  let schemaSub : Sub Tower.Head 4 n :=
    identitySchemaSubstitution element point motive reflCase
  have afterMethodsPrincipal :
      HasType context
        (.app
          (.app
            (.app
              (.app (.const identityEliminateName) element)
              point)
            motive)
          reflCase)
        (.pi element
          (.pi
            (.id (Presentation.rename wk element)
              (Presentation.rename wk point) (.var 0))
            (.app
              (.app
                (Presentation.rename wk (Presentation.rename wk motive))
              (.var 1))
              (.var 0)))) := by
    rw [← subst_identityEliminateResult_identitySchema
      element point motive reflCase]
    have identityParameters := instantiateFour_eq_subst
      element point motive reflCase identityEliminateResultType
    change _ = Presentation.subst
      (identitySchemaSubstitution element point motive reflCase)
      identityEliminateResultType at identityParameters
    rw [← identityParameters]
    exact fourth.2.1
  have fifth := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.identityReflCase
      element point motive reflCase)
    afterMethodsPrincipal afterEndpointObserved
  have elementCancels :
      Presentation.subst (subst0 point)
          (Presentation.rename wk element) = element :=
    Presentation.inst0_rename_wk point element
  have pointCancels :
      Presentation.subst (subst0 point)
          (Presentation.rename wk point) = point :=
    Presentation.inst0_rename_wk point point
  have motiveLiftCancels :
      Presentation.subst (liftSub (subst0 point))
          (Presentation.rename (fun index => wk (wk index)) motive) =
        Presentation.rename wk motive := by
    rw [← Presentation.rename_comp]
    rw [Presentation.subst_liftSub_wk]
    exact congrArg (Presentation.rename wk)
      (Presentation.inst0_rename_wk point motive)
  have pointLift :
      liftSub (subst0 point) (1 : Fin (n + 2)) =
        Presentation.rename wk point := by
    rfl
  have afterEndpointPrincipal :
      HasType context
        (.app
          (.app
            (.app
              (.app
                (.app (.const identityEliminateName) element)
                point)
              motive)
            reflCase)
          point)
        (.pi (.id element point point)
          (.app
            (.app (Presentation.rename wk motive)
              (Presentation.rename wk point))
            (.var 0))) := by
    simpa [Presentation.inst0, Presentation.subst,
      Presentation.subst0, elementCancels, pointCancels,
      motiveLiftCancels, pointLift] using fifth.2.1
  have sixth := HasType.appAgainstPrincipalOn alignment
    (NativeFunctionSpine.identityEndpoint
      element point motive reflCase point)
    afterEndpointPrincipal sourceTyping
  have emptyTyped :
      CtxMor rules (.nil : Tower.Ctx 0) context emptySub := by
    intro index
    exact Fin.elim0 index
  have elementTyped : CtxMor rules contextA context elementSub := by
    apply CtxMor.extend emptyTyped
    convert first.1 using 1
    simp [emptySub, sortTm, Presentation.subst, Presentation.rename]
  have pointTyped : CtxMor rules contextAX context pointSub := by
    apply CtxMor.extend elementTyped
    simpa [elementSub, pointSub, Presentation.inst0,
      Presentation.subst, Presentation.subst0, Presentation.rename,
      Presentation.liftSub, Presentation.liftRen] using second.1
  have motiveTyped : CtxMor rules contextAXP context motiveSub := by
    apply CtxMor.extend pointTyped
    change HasType context motive
      (Presentation.subst
        (motiveSchemaSubstitution element point) identityMotiveType)
    rw [← instantiateTwo_eq_subst element point identityMotiveType]
    exact third.1
  have schemaTyped : CtxMor rules contextAXPD context schemaSub := by
    apply CtxMor.extend motiveTyped
    change HasType context reflCase
      (Presentation.subst
        (nilCaseSchemaSubstitution element point motive)
        identityReflCaseType)
    rw [← instantiateThree_eq_subst element point motive
      identityReflCaseType]
    exact fourth.1
  let occurrence : identityIotaReceipt.InstanceAt context
      (identityEliminateApp element point motive reflCase point
        (.refl point))
      reflCase
      (.app (.app motive point) (.refl point)) :=
    { substitution := schemaSub
      typed := schemaTyped
      sourceEquation := by rfl
      targetEquation := by rfl
      typeEquation := by rfl }
  have finalAdjustment :
      TypeAdjustment rules (.app (.app motive point) (.refl point)) type := by
    have motiveCancels :
        Presentation.subst (subst0 (.refl point))
            (Presentation.rename wk motive) = motive :=
      Presentation.inst0_rename_wk (.refl point) motive
    have pointCancels' :
        Presentation.subst (subst0 (.refl point))
            (Presentation.rename wk point) = point :=
      Presentation.inst0_rename_wk (.refl point) point
    simpa [Presentation.inst0, Presentation.subst,
      Presentation.subst0, motiveCancels, pointCancels'] using sixth.2.2
  refine ⟨
    { principalType := .app (.app motive point) (.refl point)
      principal := .identity occurrence
      adjustment := finalAdjustment }⟩

/-- Fragment typing alignment is sufficient for adjustment-closed iota
coverage.  All three constructors are reconstructed as typed schema
instances; no raw support witness is promoted without its parameter typings. -/
theorem typedIotaCoverageOfNativeSpineAlignment
    (alignment : NativeSpineAlignment) : TypedIotaCoverage := by
  intro n context left right type evidence sourceTyping
  cases evidence with
  | nil element motive nilCase consCase =>
      exact nilAdjustedOfTyping alignment sourceTyping
  | cons element motive nilCase consCase head tail =>
      exact consAdjustedOfTyping alignment sourceTyping
  | identity element point motive reflCase =>
      exact identityAdjustedOfTyping alignment sourceTyping

/-- Pi constructor separation in conversion implies the complete native
spine alignment above and hence all three typed iota coverage cases. -/
theorem typedIotaCoverageOfPiConversionBoundary
    (boundary : PiConversionBoundary rules) : TypedIotaCoverage :=
  typedIotaCoverageOfNativeSpineAlignment
    (nativeSpineAlignmentOfPiConversionBoundary boundary)

/-- A beta/iota Church--Rosser theorem now closes typed iota coverage without
any further typing-generation or schema-specific premise. -/
theorem typedIotaCoverageOfChurchRosser
    (churchRosser : ConversionCoherence.ChurchRosser rules) :
    TypedIotaCoverage :=
  typedIotaCoverageOfPiConversionBoundary
    (piConversionBoundaryOfChurchRosser churchRosser)

/-- Global Pi coherence remains a sufficient—but no longer required—route
to native iota coverage. -/
theorem typedIotaCoverageOfPiCoherence
    (coherence : PiTypingCoherence rules) : TypedIotaCoverage :=
  typedIotaCoverageOfNativeSpineAlignment
    (coherence.toAlignmentOn NativeFunctionSpine)

/-! ### Raw-support negative control -/

def undeclaredElementName : DeclName := `Prime.UndeclaredElement

def undeclaredElement : Tower.Tm 0 := .const undeclaredElementName

def untypedNilLeft : Tower.Tm 0 :=
  eliminateApp undeclaredElement undeclaredElement undeclaredElement
    undeclaredElement (nilApp undeclaredElement)

/-- The schema relation is intentionally defined on raw syntax, so it has an
edge even when its element parameter is an undeclared constant. -/
def untypedNilEvidence :
    IotaEvidence 0
      untypedNilLeft
      undeclaredElement :=
  .nil undeclaredElement undeclaredElement undeclaredElement undeclaredElement

/-- The undeclared parameter has no type in the native declaration calculus.
Thus raw support alone cannot be promoted to a typed computation receipt. -/
theorem undeclaredElement_not_hasType (type : Tower.Tm 0) :
    ¬ HasType (.nil : Tower.Ctx 0) undeclaredElement type := by
  have missing : rules.constantType undeclaredElementName = none := by
    simp [undeclaredElementName, rules, extendRules, combinedType, Tower.rules,
      rawSignature, declarations, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, listName, nilName, consName,
      eliminateName, identityEliminateName]
  exact Presentation.HasType.constantImpossibleWhenMissing missing

/-- Inverting just the visible nil application is enough to show that the
whole raw redex cannot have a displayed type: its undeclared element argument
would itself need a typing derivation. -/
theorem untypedNilLeft_not_hasType (type : Tower.Tm 0) :
    ¬ HasType (.nil : Tower.Ctx 0) untypedNilLeft type := by
  intro sourceTyping
  rcases sourceTyping.appGeneration with
    ⟨_domain, _codomain, _functionTyping, listTyping, _adjustment⟩
  have nilTyping :
      HasType (.nil : Tower.Ctx 0)
        (.app (.const nilName) undeclaredElement) _domain := by
    simpa [untypedNilLeft, nilApp, eliminateApp] using listTyping
  rcases nilTyping.appGeneration with
    ⟨elementType, _nilCodomain, _nilTyping, elementTyping, _nilAdjustment⟩
  exact undeclaredElement_not_hasType elementType elementTyping

/-- Negative control for the authoritative image: raw iota support with an
ill-typed parameter cannot acquire an adjusted typed-instance receipt. -/
theorem untypedNil_not_adjusted (type : Tower.Tm 0) :
    TypedIotaInstance.Adjusted (.nil : Tower.Ctx 0)
      untypedNilLeft undeclaredElement type → False := by
  intro occurrence
  exact untypedNilLeft_not_hasType type occurrence.toReceipt.sourceTyping

/-- Both facts are present at once: a raw equation witness exists, while the
parameter required by its typed schema is unavailable. -/
theorem raw_iota_support_does_not_imply_typed_parameters :
    Nonempty
        (IotaEvidence 0
          untypedNilLeft
          undeclaredElement) ∧
      ¬ HasType (.nil : Tower.Ctx 0) undeclaredElement
        (sortTm elementLevel) :=
  ⟨⟨untypedNilEvidence⟩, undeclaredElement_not_hasType _⟩

/-! ### The proved formation boundary -/

@[simp] theorem rawSignature_valueOf_none (name : DeclName) :
    rawSignature.valueOf? name = none := by
  by_cases isList : name = listName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty]
  by_cases isNil : name = nilName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList]
  by_cases isCons : name = consName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList, isNil]
  by_cases isEliminate : name = eliminateName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList, isNil, isCons]
  by_cases isIdentity : name = identityEliminateName
  · subst name
    simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList, isNil, isCons, isEliminate]
  · simp [rawSignature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList, isNil, isCons,
      isEliminate, isIdentity]

/-- Every declared type in the native List signature is formed.  This is one
of the obligations of checked authority, stated independently so later
subject-reduction work cannot be confused with formation progress. -/
theorem rawSignature_types_formed {name : DeclName} {type : Tower.Tm 0}
    (lookup : rawSignature.typeOf? name = some type) :
    ∃ level : Tower.Head,
      Tower.rules.isUniverse level ∧
      HasType (.nil : Tower.Ctx 0) type (.head level) := by
  by_cases isList : name = listName
  · subst name
    have typeEquality : type = listType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort listDeclarationLevel, .sort listDeclarationLevel,
      listType_hasType⟩
  by_cases isNil : name = nilName
  · subst name
    have typeEquality : type = nilType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort nilDeclarationLevel, .sort nilDeclarationLevel,
      nilType_hasType⟩
  by_cases isCons : name = consName
  · subst name
    have typeEquality : type = consType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort consDeclarationLevel, .sort consDeclarationLevel,
      consType_hasType⟩
  by_cases isEliminate : name = eliminateName
  · subst name
    have typeEquality : type = eliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort eliminateDeclarationLevel, .sort eliminateDeclarationLevel,
      eliminateType_hasType⟩
  by_cases isIdentity : name = identityEliminateName
  · subst name
    have typeEquality : type = identityEliminateType := by
      simpa using lookup.symm
    subst type
    exact ⟨.sort identityEliminateDeclarationLevel,
      .sort identityEliminateDeclarationLevel,
      identityEliminateType_hasType⟩
  · simp [rawSignature, declarations, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, isList, isNil, isCons,
      isEliminate, isIdentity] at lookup

/-- The native declarations are fresh relative to the undecorated tower. -/
theorem rawSignature_fresh {name : DeclName} {entry : Entry Tower.Head}
    (_lookup : rawSignature.entries name = some entry) :
    Tower.rules.constantType name = none :=
  rfl

/-- The formation/freshness/value portion of `Signature.WellFormed` is fully
discharged.  Constructor ι-preservation remains a separate theorem
obligation; no checked-authority package is exported before it is proved. -/
def rawSignature_formed : rawSignature.Formed Tower.rules where
  fresh := rawSignature_fresh
  types := rawSignature_types_formed
  values := by
    intro name type value _typeLookup valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [rawSignature_valueOf_none] at valueLookup
    cases valueLookup

/-! ### Native List as an indexed-family declaration

The generic declaration interface is instantiated here by the actual Prime
syntax, not by the external polynomial model.  Positivity therefore talks
about the same constants and de Bruijn binders used by typing and iota
receipts. -/

/-- An exact unary occurrence `List A`; the element index must not itself
mention the family being declared. -/
def listFamilyApplication (element : Tower.Tm n)
    (elementFree : FreeOf listName element) :
    FamilyApplication listName 1 (listApp element) :=
  .intro [element] rfl (by
    intro argument membership
    simp only [List.mem_singleton] at membership
    subst argument
    exact elementFree) rfl

/-- `nil : Π A, List A` ends in the family and has only a family-free
parameter field. -/
def nilConstructorPositive : ConstructorType listName 1 nilType := by
  unfold nilType
  exact .field (.free (.head _))
    (.result (listFamilyApplication (.var 0) (.var 0)))

/-- `cons : Π A, A → List A → List A` has one recursive field, in a
strictly positive position, and returns the same unary family. -/
def consConstructorPositive : ConstructorType listName 1 consType := by
  unfold consType consBodyType
  exact .field (.free (.head _))
    (.field (.free (.var 0))
      (.field
        (.recursive (listFamilyApplication (.var 1) (.var 1)))
        (.result (listFamilyApplication (.var 2) (.var 2)))))

def nilConstructorSpec :
    ConstructorSpec rawSignature listName 1 where
  name := nilName
  type := nilType
  declared := typeOf_nil
  positive := nilConstructorPositive

def consConstructorSpec :
    ConstructorSpec rawSignature listName 1 where
  name := consName
  type := consType
  declared := typeOf_cons
  positive := consConstructorPositive

def listConstructors :
    List (ConstructorSpec rawSignature listName 1) :=
  [nilConstructorSpec, consConstructorSpec]

def listEliminatorSpec : EliminatorSpec rawSignature where
  name := eliminateName
  type := eliminateType
  declared := typeOf_eliminate

def nilIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 4 where
  context := contextAPZS
  left := nilIotaLeft
  right := nilIotaRight
  type := nilIotaResultType
  receipt := nilIotaReceipt

def consIotaSchema :
    IotaSchema Tower.rules rawSignature proofRelevantIotaComputation 6 where
  context := contextAPZSHeadTail
  left := consIotaLeft
  right := consIotaRight
  type := consIotaResultType
  receipt := consIotaReceipt

def eliminateAtParameters_applicationHead :
    ApplicationHead eliminateName eliminateAtParameters :=
  .app (.app (.app (.app .const)))

noncomputable def eliminateAtConsParameters_applicationHead :
    ApplicationHead eliminateName eliminateAtConsParameters := by
  unfold eliminateAtConsParameters
  exact (eliminateAtParameters_applicationHead.rename wk).rename wk

def nilApp_constantOccurrence (element : Tower.Tm n) :
    ConstantOccurrence nilName (nilApp element) :=
  .appFunction .here

def consApp_constantOccurrence (element head tail : Tower.Tm n) :
    ConstantOccurrence consName (consApp element head tail) :=
  .appFunction (.appFunction (.appFunction .here))

def nilIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (listConstructors.map ConstructorSpec.name) listEliminatorSpec.name where
  constructorName := nilName
  constructorDeclared := by
    simp [listConstructors, nilConstructorSpec]
  arity := 4
  schema := nilIotaSchema
  eliminatorHead := .app eliminateAtParameters_applicationHead
  constructorOccurrence := .appArgument (nilApp_constantOccurrence (.var 3))

noncomputable def consIotaClause :
    IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (listConstructors.map ConstructorSpec.name) listEliminatorSpec.name where
  constructorName := consName
  constructorDeclared := by
    simp [listConstructors, nilConstructorSpec, consConstructorSpec]
  arity := 6
  schema := consIotaSchema
  eliminatorHead := .app eliminateAtConsParameters_applicationHead
  constructorOccurrence :=
    .appArgument (consApp_constantOccurrence (.var 5) (.var 1) (.var 0))

noncomputable def listIotaClauses :
    List (IotaClause Tower.rules rawSignature proofRelevantIotaComputation
      (listConstructors.map ConstructorSpec.name) listEliminatorSpec.name) :=
  [nilIotaClause, consIotaClause]

/-- Prime's native List is a formed, strictly-positive declaration candidate.
The signature also carries `J`; accordingly these two schemas are explicitly
the List-specific part of its computation relation, not an exhaustiveness
claim about the whole signature. -/
noncomputable def listCandidate : Candidate Tower.rules where
  signature := rawSignature
  formed := rawSignature_formed
  computation := proofRelevantIotaComputation
  computationSupport := rfl
  familyName := listName
  familyParameterCount := 1
  familyIndexCount := 0
  familyType := listType
  familyDeclared := typeOf_list
  constructors := listConstructors
  constructorNamesNodup := by
    change [nilName, consName].Nodup
    decide
  familyNotConstructor := by
    intro constructor membership
    simp only [listConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  eliminator := listEliminatorSpec
  eliminatorNotFamily := by decide
  eliminatorNotConstructor := by
    intro constructor membership
    simp only [listConstructors, List.mem_cons, List.not_mem_nil, or_false]
      at membership
    rcases membership with rfl | rfl <;> decide
  iotaClauses := listIotaClauses
  constructorsComputed := by
    intro constructorName membership
    simp [listConstructors, nilConstructorSpec, consConstructorSpec] at membership
    rcases membership with rfl | rfl <;>
      simp [listIotaClauses, nilIotaClause, consIotaClause]

/-- Native negative control: an occurrence of `List` in a function domain is
not strictly positive, even though its index is family-free. -/
theorem listInFunctionDomain_not_strictlyPositive :
    StrictlyPositive listName 1
      (.pi (listApp (.var 0 : Tower.Tm 1)) (.var 0)) → False :=
  recursivePiDomain_not_strictlyPositive
    (listFamilyApplication (.var 0) (.var 0)) (.var 0)

/-! ### Exact computational-authority boundary -/

/-- The proof-relevant datum still needed to make every authored iota
instance preserve its displayed type. -/
abbrev IotaPreservation : Type :=
  DeclaredPreservationFamily Tower.rules rawSignature

/-- Exact typed-schema coverage is sufficient for full preservation of the
raw iota support relation.  This theorem isolates the remaining metatheoretic
work: inversion must reconstruct one of the three typed schema images from
an arbitrary declarative typing of an iota source. -/
def iotaPreservationOfCoverage (coverage : TypedIotaCoverage) :
    IotaPreservation := by
  intro n context type left right step sourceTyping
  exact ⟨by
    rcases step.down with ⟨evidence⟩
    have covered := coverage (n := n) (context := context)
      (left := left) (right := right) (type := type)
      evidence sourceTyping.down
    rcases covered with ⟨occurrence⟩
    exact occurrence.targetTyping⟩

/-- The native signature has no inherited root computation and no delta
values.  Consequently neither branch contributes a hidden preservation
obligation. -/
def remainingRootPreservation :
    RemainingRootPreservation Tower.rules rawSignature where
  inherited := by
    intro n context left right type inherited sourceTyping
    exact inherited.elim
  delta := by
    intro n context name value type unfolding sourceTyping
    rw [rawSignature_valueOf_none] at unfolding
    cases unfolding

/-- An iota-preservation family is sufficient to construct the complete
well-formed signature.  Formation, freshness, and value obligations have
already been discharged above. -/
def wellFormedOfIotaPreservation (preserves : IotaPreservation) :
    rawSignature.WellFormed Tower.rules :=
  rawSignature_formed.withPreservation
    (declaredPreservesOfFamily preserves)

/-- The generic declaration-authority obligation reduces to alignment on the
explicit native function-spine image, rather than three declaration-specific
preservation assumptions or a whole-calculus checker. -/
def iotaPreservationOfNativeSpineAlignment
    (alignment : NativeSpineAlignment) : IotaPreservation :=
  iotaPreservationOfCoverage
    (typedIotaCoverageOfNativeSpineAlignment alignment)

def wellFormedOfNativeSpineAlignment
    (alignment : NativeSpineAlignment) :
    rawSignature.WellFormed Tower.rules :=
  wellFormedOfIotaPreservation
    (iotaPreservationOfNativeSpineAlignment alignment)

/-- Checked native declaration authority follows directly from Pi
constructor separation.  Confluence or normalization may establish that
boundary, but neither is embedded in this interface. -/
def iotaPreservationOfPiConversionBoundary
    (boundary : PiConversionBoundary rules) : IotaPreservation :=
  iotaPreservationOfCoverage
    (typedIotaCoverageOfPiConversionBoundary boundary)

def wellFormedOfPiConversionBoundary
    (boundary : PiConversionBoundary rules) :
    rawSignature.WellFormed Tower.rules :=
  wellFormedOfIotaPreservation
    (iotaPreservationOfPiConversionBoundary boundary)

/-- The native signature becomes checked authority as soon as its beta/iota
conversion relation earns Church--Rosser.  Root constructor neutrality and
all typing reconstruction obligations are already discharged. -/
def wellFormedOfChurchRosser
    (churchRosser : ConversionCoherence.ChurchRosser rules) :
    rawSignature.WellFormed Tower.rules :=
  wellFormedOfPiConversionBoundary
    (piConversionBoundaryOfChurchRosser churchRosser)

/-- Whole-calculus Pi coherence is a conservative sufficient route to the
smaller native-spine obligation. -/
def iotaPreservationOfPiCoherence
    (coherence : PiTypingCoherence rules) : IotaPreservation :=
  iotaPreservationOfNativeSpineAlignment
    (coherence.toAlignmentOn NativeFunctionSpine)

def wellFormedOfPiCoherence
    (coherence : PiTypingCoherence rules) :
    rawSignature.WellFormed Tower.rules :=
  wellFormedOfIotaPreservation (iotaPreservationOfPiCoherence coherence)

/-- There are no unnamed side conditions: checked signature authority is
equivalent to inhabiting the one genuine iota-preservation family. -/
theorem wellFormed_iff_iotaPreservation_inhabited :
    Nonempty (rawSignature.WellFormed Tower.rules) ↔
      Nonempty IotaPreservation := by
  constructor
  · rintro ⟨wellFormed⟩
    exact
      ⟨Presentation.Declaration.ComputationAuthority.Signature.WellFormed.declaredPreservationFamily
        wellFormed⟩
  · rintro ⟨preserves⟩
    exact ⟨wellFormedOfIotaPreservation preserves⟩

/-- Once iota preservation is supplied, every native combined root step
preserves typing. -/
def combinedRootPreservesOfIota (preserves : IotaPreservation) :
    ∀ {n : Nat} {context : Tower.Ctx n}
        {left right type : Tower.Tm n},
      rules.computation.step left right →
      HasType context left type → HasType context right type :=
  Presentation.Declaration.ComputationAuthority.Signature.WellFormed.combinedRootPreserves
    (wellFormedOfIotaPreservation preserves) remainingRootPreservation

theorem iota_nil {element motive nilCase consCase : Tower.Tm n} :
    rules.computation.step
      (eliminateApp element motive nilCase consCase (nilApp element))
      nilCase :=
  RootStep.declared ⟨.nil element motive nilCase consCase⟩

theorem iota_cons {element motive nilCase consCase head tail : Tower.Tm n} :
    rules.computation.step
      (eliminateApp element motive nilCase consCase
        (consApp element head tail))
      (.app (.app (.app consCase head) tail)
        (eliminateApp element motive nilCase consCase tail)) :=
  RootStep.declared
    ⟨.cons element motive nilCase consCase head tail⟩

theorem iota_identity {element point motive reflCase : Tower.Tm n} :
    rules.computation.step
      (identityEliminateApp element point motive reflCase point
        (.refl point))
      reflCase :=
  RootStep.declared ⟨.identity element point motive reflCase⟩

/-- The native identity eliminator is an inhabited Martin-Löf-style
capability: it is declared at its dependent type, computes on reflexivity,
and its proof-relevant computation receipts commute with substitution. -/
theorem martinLofIdentityEliminationContract
    {element point motive reflCase : Tower.Tm n} :
    rawSignature.typeOf? identityEliminateName =
        some identityEliminateType ∧
      proofRelevantIotaComputation.SubstitutionCoherent ∧
      rules.computation.step
        (identityEliminateApp element point motive reflCase point
          (.refl point))
        reflCase :=
  ⟨typeOf_identityEliminate,
    proofRelevantIotaSubstitutionCoherent,
    iota_identity⟩

/-! ### Axiom audit -/

#print axioms eliminateAtParameters_hasType
#print axioms rawSignature_formed
#print axioms nilConstructorPositive
#print axioms consConstructorPositive
#print axioms listCandidate
#print axioms listInFunctionDomain_not_strictlyPositive
#print axioms nilIotaReceipt
#print axioms consIotaReceipt
#print axioms identityIotaReceipt
#print axioms IotaEvidence.heq_of_code_eq
#print axioms proofRelevantIotaSubstitutionCoherent
#print axioms martinLofIdentityEliminationContract
#print axioms TypedIotaReceipt.InstanceAt.toReceipt
#print axioms TypedIotaInstance.targetTyping
#print axioms TypedIotaInstance.Adjusted.toReceipt
#print axioms canonicalNilAdjusted
#print axioms canonicalConsAdjusted
#print axioms canonicalIdentityAdjusted
#print axioms rootPiHeadNeutral
#print axioms piConversionBoundaryOfChurchRosser
#print axioms nativeSpineAlignmentOfPiConversionBoundary
#print axioms typedIotaCoverageOfNativeSpineAlignment
#print axioms typedIotaCoverageOfPiConversionBoundary
#print axioms typedIotaCoverageOfChurchRosser
#print axioms typedIotaCoverageOfPiCoherence
#print axioms wellFormedOfNativeSpineAlignment
#print axioms wellFormedOfPiConversionBoundary
#print axioms wellFormedOfChurchRosser
#print axioms wellFormedOfPiCoherence
#print axioms iotaPreservationOfCoverage
#print axioms raw_iota_support_does_not_imply_typed_parameters
#print axioms untypedNil_not_adjusted
#print axioms wellFormed_iff_iotaPreservation_inhabited

end Intrinsic

end NativeIndexedFamilies
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
