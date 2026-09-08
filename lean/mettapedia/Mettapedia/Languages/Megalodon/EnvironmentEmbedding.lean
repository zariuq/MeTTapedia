import Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-!
# Namespace-preserving Megalodon environment embeddings

A theory extension is not safely modeled by appending declarations to a raw
`Environment`: a formerly opaque name may acquire a definition, changing
fuel-bounded delta normalization and even invalidating a previously accepted
proof.  This module instead uses an injective source-name embedding whose image
has exactly the source lookups.  The target may contain arbitrary declarations
outside that image.

The first rung deliberately fixes the primitive table.  Transport of primitive
and base-type indices requires a separate indexed embedding and is not inferred
from name transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.EnvironmentEmbedding

open Mettapedia.GSLT.LanguageDef.NIKTheoryProfileView
open Mettapedia.Languages.Megalodon.MathdataKernel
open Mettapedia.Languages.Megalodon.NIKNativeProof
open Mettapedia.Languages.Megalodon.SelectedTheoryProfile

/-! ## Renaming the material presentation -/

/-- Rename global term names in a Mathdata term.  Bound variables, primitive
indices, and type structure are retained exactly. -/
def renameTm (rename : Name -> Name) : Tm -> Tm
  | .db index => .db index
  | .named name => .named (rename name)
  | .prim index => .prim index
  | .app function argument =>
      .app (renameTm rename function) (renameTm rename argument)
  | .lam type body => .lam type (renameTm rename body)
  | .imp domain codomain =>
      .imp (renameTm rename domain) (renameTm rename codomain)
  | .all type body => .all type (renameTm rename body)
  | .typeApp function type => .typeApp (renameTm rename function) type
  | .typeLam body => .typeLam (renameTm rename body)
  | .typeAll body => .typeAll (renameTm rename body)

/-- Rename all global names carried by a native Megalodon proof term. -/
def renamePf (rename : Name -> Name) : Pf -> Pf
  | .gpa name => .gpa (rename name)
  | .hyp index => .hyp index
  | .known name => .known (rename name)
  | .termApp function argument =>
      .termApp (renamePf rename function) (renameTm rename argument)
  | .proofApp function argument =>
      .proofApp (renamePf rename function) (renamePf rename argument)
  | .proofLam proposition body =>
      .proofLam (renameTm rename proposition) (renamePf rename body)
  | .termLam type body => .termLam type (renamePf rename body)
  | .typeApp function type => .typeApp (renamePf rename function) type
  | .typeLam body => .typeLam (renamePf rename body)

def renameTermDecl (rename : Name -> Name) (declaration : TermDecl) : TermDecl :=
  { name := rename declaration.name
    type := declaration.type
    definition := declaration.definition.map (renameTm rename) }

def renameKnownDecl (rename : Name -> Name) (declaration : KnownDecl) : KnownDecl :=
  { name := rename declaration.name
    proposition := renameTm rename declaration.proposition }

/-- Rename the globally addressed declarations of a complete environment. -/
def renameEnvironment (rename : Name -> Name)
    (environment : Environment) : Environment where
  primitives := environment.primitives
  terms := environment.terms.map (renameTermDecl rename)
  known := environment.known.map (renameKnownDecl rename)

theorem lookupTermList?_rename {rename : Name -> Name}
    (nameInjective : Function.Injective rename)
    (declarations : List TermDecl) (name : Name) :
    lookupTermList? (declarations.map (renameTermDecl rename))
        (rename name) =
      (lookupTermList? declarations name).map (renameTermDecl rename) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations declarationsIH =>
      by_cases sameName : declaration.name = name
      · subst name
        simp [lookupTermList?, renameTermDecl]
      · have renamedDifferent : rename declaration.name ≠ rename name := by
          intro equalRenaming
          exact sameName (nameInjective equalRenaming)
        simp [lookupTermList?, renameTermDecl, sameName, renamedDifferent,
          declarationsIH]

theorem lookupKnownList?_rename {rename : Name -> Name}
    (nameInjective : Function.Injective rename)
    (declarations : List KnownDecl) (name : Name) :
    lookupKnownList? (declarations.map (renameKnownDecl rename))
        (rename name) =
      (lookupKnownList? declarations name).map (renameTm rename) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations declarationsIH =>
      by_cases sameName : declaration.name = name
      · subst name
        simp [lookupKnownList?, renameKnownDecl]
      · have renamedDifferent : rename declaration.name ≠ rename name := by
          intro equalRenaming
          exact sameName (nameInjective equalRenaming)
        simp [lookupKnownList?, renameKnownDecl, sameName, renamedDifferent,
          declarationsIH]

@[simp] theorem renameTm_identity (term : Tm) :
    renameTm id term = term := by
  induction term <;> simp [renameTm, *]

@[simp] theorem renamePf_identity (proof : Pf) :
    renamePf id proof = proof := by
  induction proof <;> simp [renamePf, renameTm_identity, *]

theorem renameTm_comp (first second : Name -> Name) (term : Tm) :
    renameTm second (renameTm first term) =
      renameTm (second ∘ first) term := by
  induction term <;> simp [renameTm, Function.comp_apply, *]

theorem renamePf_comp (first second : Name -> Name) (proof : Pf) :
    renamePf second (renamePf first proof) =
      renamePf (second ∘ first) proof := by
  induction proof <;>
    simp [renamePf, renameTm_comp, Function.comp_apply, *]

/-- An injective global-name map induces an injective map on complete terms. -/
theorem renameTm_injective {rename : Name -> Name}
    (nameInjective : Function.Injective rename) :
    Function.Injective (renameTm rename) := by
  intro left
  induction left with
  | db index =>
      intro right
      cases right <;> simp [renameTm]
  | named name =>
      intro right
      cases right <;> simp [renameTm, nameInjective.eq_iff]
  | prim index =>
      intro right
      cases right <;> simp [renameTm]
  | app function argument functionIH argumentIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case app otherFunction otherArgument =>
        exact congrArg₂ Tm.app
          (functionIH equalRenaming.1) (argumentIH equalRenaming.2)
  | lam type body bodyIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case lam otherType otherBody =>
        exact congrArg₂ Tm.lam equalRenaming.1
          (bodyIH equalRenaming.2)
  | imp domain codomain domainIH codomainIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case imp otherDomain otherCodomain =>
        exact congrArg₂ Tm.imp
          (domainIH equalRenaming.1) (codomainIH equalRenaming.2)
  | all type body bodyIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case all otherType otherBody =>
        exact congrArg₂ Tm.all equalRenaming.1
          (bodyIH equalRenaming.2)
  | typeApp function type functionIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case typeApp otherFunction otherType =>
        exact congrArg₂ Tm.typeApp
          (functionIH equalRenaming.1) equalRenaming.2
  | typeLam body bodyIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case typeLam otherBody =>
        exact congrArg Tm.typeLam (bodyIH equalRenaming)
  | typeAll body bodyIH =>
      intro right equalRenaming
      cases right <;> simp [renameTm] at equalRenaming
      case typeAll otherBody =>
        exact congrArg Tm.typeAll (bodyIH equalRenaming)

/-! ## Commutation with binder operations -/

theorem renameTm_shift (rename : Name -> Name) (cutoff amount : Nat)
    (term : Tm) :
    renameTm rename (Tm.shift cutoff amount term) =
      Tm.shift cutoff amount (renameTm rename term) := by
  induction term generalizing cutoff <;> simp [renameTm, Tm.shift, *]
  all_goals split <;> rfl

theorem renameTm_typeShift (rename : Name -> Name) (cutoff amount : Nat)
    (term : Tm) :
    renameTm rename (Tm.typeShift cutoff amount term) =
      Tm.typeShift cutoff amount (renameTm rename term) := by
  induction term generalizing cutoff <;> simp [renameTm, Tm.typeShift, *]

theorem renameTm_instantiateAt (rename : Name -> Name) (depth : Nat)
    (replacement body : Tm) :
    renameTm rename (Tm.instantiateAt depth replacement body) =
      Tm.instantiateAt depth (renameTm rename replacement)
        (renameTm rename body) := by
  induction body generalizing depth with
  | db index =>
      by_cases below : index < depth
      · simp [Tm.instantiateAt, renameTm, below]
      · by_cases equal : index = depth
        · simp [Tm.instantiateAt, renameTm, equal, renameTm_shift]
        · simp [Tm.instantiateAt, renameTm, below, equal]
  | named => simp [Tm.instantiateAt, renameTm]
  | prim => simp [Tm.instantiateAt, renameTm]
  | app function argument functionIH argumentIH =>
      simp [Tm.instantiateAt, renameTm, functionIH, argumentIH]
  | lam type body bodyIH =>
      simp [Tm.instantiateAt, renameTm, bodyIH]
  | imp domain codomain domainIH codomainIH =>
      simp [Tm.instantiateAt, renameTm, domainIH, codomainIH]
  | all type body bodyIH =>
      simp [Tm.instantiateAt, renameTm, bodyIH]
  | typeApp function type functionIH =>
      simp [Tm.instantiateAt, renameTm, functionIH]
  | typeLam body bodyIH =>
      simp [Tm.instantiateAt, renameTm, bodyIH]
  | typeAll body bodyIH =>
      simp [Tm.instantiateAt, renameTm, bodyIH]

@[simp] theorem renameTm_instantiate (rename : Name -> Name)
    (replacement body : Tm) :
    renameTm rename (Tm.instantiate replacement body) =
      Tm.instantiate (renameTm rename replacement) (renameTm rename body) := by
  exact renameTm_instantiateAt rename 0 replacement body

theorem renameTm_typeInstantiateAt (rename : Name -> Name) (depth : Nat)
    (replacement : Tp) (term : Tm) :
    renameTm rename (Tm.typeInstantiateAt depth replacement term) =
      Tm.typeInstantiateAt depth replacement (renameTm rename term) := by
  induction term generalizing depth <;>
    simp [renameTm, Tm.typeInstantiateAt, *]

@[simp] theorem renameTm_typeInstantiate (rename : Name -> Name)
    (replacement : Tp) (term : Tm) :
    renameTm rename (Tm.typeInstantiate replacement term) =
      Tm.typeInstantiate replacement (renameTm rename term) := by
  exact renameTm_typeInstantiateAt rename 0 replacement term

theorem renameTm_dropAt? (rename : Name -> Name) (cutoff : Nat) (term : Tm) :
    (Tm.dropAt? cutoff term).map (renameTm rename) =
      Tm.dropAt? cutoff (renameTm rename term) := by
  induction term generalizing cutoff with
  | db index =>
      by_cases below : index < cutoff
      · simp [Tm.dropAt?, renameTm, below]
      · by_cases equal : index = cutoff
        · simp [Tm.dropAt?, renameTm, equal]
        · simp [Tm.dropAt?, renameTm, below, equal]
  | named => simp [Tm.dropAt?, renameTm]
  | prim => simp [Tm.dropAt?, renameTm]
  | app function argument functionIH argumentIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← functionIH cutoff, ← argumentIH cutoff]
      cases Tm.dropAt? cutoff function <;>
        cases Tm.dropAt? cutoff argument <;> rfl
  | lam type body bodyIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.dropAt? (cutoff + 1) body <;> rfl
  | imp domain codomain domainIH codomainIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← domainIH cutoff, ← codomainIH cutoff]
      cases Tm.dropAt? cutoff domain <;>
        cases Tm.dropAt? cutoff codomain <;> rfl
  | all type body bodyIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.dropAt? (cutoff + 1) body <;> rfl
  | typeApp function type functionIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← functionIH cutoff]
      cases Tm.dropAt? cutoff function <;> rfl
  | typeLam body bodyIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← bodyIH cutoff]
      cases Tm.dropAt? cutoff body <;> rfl
  | typeAll body bodyIH =>
      simp only [Tm.dropAt?, renameTm]
      rw [← bodyIH cutoff]
      cases Tm.dropAt? cutoff body <;> rfl

theorem renameTm_typeDropAt? (rename : Name -> Name) (cutoff : Nat)
    (term : Tm) :
    (Tm.typeDropAt? cutoff term).map (renameTm rename) =
      Tm.typeDropAt? cutoff (renameTm rename term) := by
  induction term generalizing cutoff with
  | db => simp [Tm.typeDropAt?, renameTm]
  | named => simp [Tm.typeDropAt?, renameTm]
  | prim => simp [Tm.typeDropAt?, renameTm]
  | app function argument functionIH argumentIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← functionIH cutoff, ← argumentIH cutoff]
      cases Tm.typeDropAt? cutoff function <;>
        cases Tm.typeDropAt? cutoff argument <;> rfl
  | lam type body bodyIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← bodyIH cutoff]
      cases Tp.dropAt? cutoff type <;>
        cases Tm.typeDropAt? cutoff body <;> rfl
  | imp domain codomain domainIH codomainIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← domainIH cutoff, ← codomainIH cutoff]
      cases Tm.typeDropAt? cutoff domain <;>
        cases Tm.typeDropAt? cutoff codomain <;> rfl
  | all type body bodyIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← bodyIH cutoff]
      cases Tp.dropAt? cutoff type <;>
        cases Tm.typeDropAt? cutoff body <;> rfl
  | typeApp function type functionIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← functionIH cutoff]
      cases Tm.typeDropAt? cutoff function <;>
        cases Tp.dropAt? cutoff type <;> rfl
  | typeLam body bodyIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.typeDropAt? (cutoff + 1) body <;> rfl
  | typeAll body bodyIH =>
      simp only [Tm.typeDropAt?, renameTm]
      rw [← bodyIH (cutoff + 1)]
      cases Tm.typeDropAt? (cutoff + 1) body <;> rfl

/-! ## Commutation with beta/eta normalization -/

/-- Rename the term component of one normalization pass result. -/
def renamePass (rename : Name -> Name) (result : Tm × Bool) : Tm × Bool :=
  (renameTm rename result.1, result.2)

theorem normalizeOne_rename (rename : Name -> Name) (term : Tm) :
    Tm.normalizeOne (renameTm rename term) =
      renamePass rename (Tm.normalizeOne term) := by
  induction term with
  | db => rfl
  | named => rfl
  | prim => rfl
  | app function argument functionIH argumentIH =>
      cases functionPass : Tm.normalizeOne function with
      | mk functionResult functionStable =>
          cases argumentPass : Tm.normalizeOne argument with
          | mk argumentResult argumentStable =>
              have mappedFunction := functionIH
              have mappedArgument := argumentIH
              rw [functionPass] at mappedFunction
              rw [argumentPass] at mappedArgument
              cases functionResult <;>
                simp [Tm.normalizeOne, renameTm, renamePass,
                  functionPass, argumentPass, mappedFunction, mappedArgument,
                  renameTm_instantiate]
  | lam type body bodyIH =>
      cases bodyPass : Tm.normalizeOne body with
      | mk bodyResult bodyStable =>
          have mappedBody := bodyIH
          rw [bodyPass] at mappedBody
          cases bodyResult <;>
            simp [Tm.normalizeOne, renameTm, renamePass, bodyPass, mappedBody]
          case app function argument =>
            cases argument <;> try rfl
            case db index =>
              cases index with
              | zero =>
                  have dropCommutes := renameTm_dropAt? rename 0 function
                  simp only [renameTm]
                  rw [← dropCommutes]
                  cases Tm.dropAt? 0 function <;> rfl
              | succ index => rfl
  | imp domain codomain domainIH codomainIH =>
      simp [Tm.normalizeOne, renameTm, renamePass, domainIH, codomainIH]
  | all type body bodyIH =>
      simp [Tm.normalizeOne, renameTm, renamePass, bodyIH]
  | typeApp function type functionIH =>
      cases functionPass : Tm.normalizeOne function with
      | mk functionResult functionStable =>
          have mappedFunction := functionIH
          rw [functionPass] at mappedFunction
          cases functionResult <;>
            simp [Tm.normalizeOne, renameTm, renamePass, functionPass,
              mappedFunction, renameTm_typeInstantiate]
  | typeLam body bodyIH =>
      cases bodyPass : Tm.normalizeOne body with
      | mk bodyResult bodyStable =>
          have mappedBody := bodyIH
          rw [bodyPass] at mappedBody
          cases bodyResult <;>
            simp [Tm.normalizeOne, renameTm, renamePass, bodyPass, mappedBody]
          case typeApp function type =>
            cases type <;> try rfl
            case var index =>
              cases index with
              | zero =>
                  have dropCommutes := renameTm_typeDropAt? rename 0 function
                  change
                    (match Tm.typeDropAt? 0 (renameTm rename function) with
                      | some contracted => (contracted, false)
                      | none =>
                          (.typeLam (.typeApp (renameTm rename function)
                            (.var 0)), bodyStable)) =
                    renamePass rename
                      (match Tm.typeDropAt? 0 function with
                        | some contracted => (contracted, false)
                        | none =>
                            (.typeLam (.typeApp function (.var 0)), bodyStable))
                  rw [← dropCommutes]
                  cases Tm.typeDropAt? 0 function <;> rfl
              | succ index => rfl
  | typeAll body bodyIH =>
      simp [Tm.normalizeOne, renameTm, renamePass, bodyIH]

theorem normalize_rename (rename : Name -> Name) (fuel : Nat) (term : Tm) :
    Tm.normalize fuel (renameTm rename term) =
      (Tm.normalize fuel term).map (renameTm rename) := by
  induction fuel generalizing term with
  | zero =>
      unfold Tm.normalize
      rw [normalizeOne_rename]
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable
          · simp [renamePass]
          · simp [renamePass]
  | succ fuel fuelIH =>
      unfold Tm.normalize
      rw [normalizeOne_rename]
      cases pass : Tm.normalizeOne term with
      | mk result stable =>
          cases stable
          · simp [renamePass, fuelIH]
          · simp [renamePass]

/-! ## Declaration-aware environment embeddings -/

/-- A source environment embedded into a reserved namespace of a target.

Exact lookup agreement includes absence: a target declaration may be added
outside the image, but not at the translation of a source name that was opaque.
This is what makes fuel-bounded delta conversion stable for arbitrary source
claims, including rejected ones. -/
structure Embedding (source target : Environment) where
  mapName : Name -> Name
  name_injective : Function.Injective mapName
  primitives_eq : target.primitives = source.primitives
  lookupTerm_commutes : forall name,
    target.lookupTerm? (mapName name) =
      (source.lookupTerm? name).map (renameTermDecl mapName)
  lookupKnown_commutes : forall name,
    target.lookupKnown? (mapName name) =
      (source.lookupKnown? name).map (renameTm mapName)

namespace Embedding

variable {source middle target : Environment}

/-! ## Canonical environment renaming -/

/-- Injective renaming of a whole environment is the canonical nontrivial
environment embedding. -/
def ofRenaming (environment : Environment) (rename : Name -> Name)
    (nameInjective : Function.Injective rename) :
    Embedding environment (renameEnvironment rename environment) where
  mapName := rename
  name_injective := nameInjective
  primitives_eq := rfl
  lookupTerm_commutes := by
    intro name
    exact lookupTermList?_rename nameInjective environment.terms name
  lookupKnown_commutes := by
    intro name
    exact lookupKnownList?_rename nameInjective environment.known name

/-! ## Computation and typing commute with an environment embedding -/

/-- Exact lookup agreement, including absence, makes delta normalization
equivariant under global-name transport at every fuel bound. -/
theorem deltaNormalize_rename (embedding : Embedding source target)
    (fuel : Nat) (term : Tm) :
    deltaNormalize target fuel (renameTm embedding.mapName term) =
      (deltaNormalize source fuel term).map
        (renameTm embedding.mapName) := by
  induction fuel generalizing term with
  | zero =>
      induction term with
      | db => simp [renameTm, deltaNormalize]
      | named name =>
          simp only [renameTm, deltaNormalize]
          rw [embedding.lookupTerm_commutes]
          cases lookup : source.lookupTerm? name with
          | none => rfl
          | some declaration =>
              cases declaration with
              | mk declarationName declarationType definition =>
                  cases definition <;> rfl
      | prim => simp [renameTm, deltaNormalize]
      | app function argument functionIH argumentIH =>
          simp only [renameTm, deltaNormalize]
          rw [functionIH, argumentIH]
          cases deltaNormalize source 0 function <;>
            cases deltaNormalize source 0 argument <;> rfl
      | lam type body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | imp domain codomain domainIH codomainIH =>
          simp only [renameTm, deltaNormalize]
          rw [domainIH, codomainIH]
          cases deltaNormalize source 0 domain <;>
            cases deltaNormalize source 0 codomain <;> rfl
      | all type body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | typeApp function type functionIH =>
          simp only [renameTm, deltaNormalize]
          rw [functionIH]
          cases deltaNormalize source 0 function <;> rfl
      | typeLam body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
      | typeAll body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source 0 body <;> rfl
  | succ fuel fuelIH =>
      induction term with
      | db => simp [renameTm, deltaNormalize]
      | named name =>
          simp only [renameTm, deltaNormalize]
          rw [embedding.lookupTerm_commutes]
          cases lookup : source.lookupTerm? name with
          | none => rfl
          | some declaration =>
              cases declaration with
              | mk declarationName declarationType definition =>
                  cases definition with
                  | none => rfl
                  | some definition =>
                      simpa [renameTermDecl] using fuelIH definition
      | prim => simp [renameTm, deltaNormalize]
      | app function argument functionIH argumentIH =>
          simp only [renameTm, deltaNormalize]
          rw [functionIH, argumentIH]
          cases deltaNormalize source (fuel + 1) function <;>
            cases deltaNormalize source (fuel + 1) argument <;> rfl
      | lam type body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | imp domain codomain domainIH codomainIH =>
          simp only [renameTm, deltaNormalize]
          rw [domainIH, codomainIH]
          cases deltaNormalize source (fuel + 1) domain <;>
            cases deltaNormalize source (fuel + 1) codomain <;> rfl
      | all type body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | typeApp function type functionIH =>
          simp only [renameTm, deltaNormalize]
          rw [functionIH]
          cases deltaNormalize source (fuel + 1) function <;> rfl
      | typeLam body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl
      | typeAll body bodyIH =>
          simp only [renameTm, deltaNormalize]
          rw [bodyIH]
          cases deltaNormalize source (fuel + 1) body <;> rfl

/-- Full beta/eta/delta normalization commutes with an embedding, including
resource failure. -/
theorem normalize_rename (embedding : Embedding source target)
    (fuel : Nat) (term : Tm) :
    MathdataKernel.normalize target fuel
        (renameTm embedding.mapName term) =
      (MathdataKernel.normalize source fuel term).map
        (renameTm embedding.mapName) := by
  unfold MathdataKernel.normalize
  rw [embedding.deltaNormalize_rename]
  cases normalized : deltaNormalize source fuel term with
  | none => rfl
  | some deltaNormal =>
      simpa using
        Mettapedia.Languages.Megalodon.EnvironmentEmbedding.normalize_rename
          embedding.mapName fuel deltaNormal

/-- Type synthesis is invariant under a declaration-preserving name
embedding.  Primitive indices are unchanged in this first rung. -/
theorem inferTerm_rename (embedding : Embedding source target)
    (typeDepth : Nat) (termContext : List Tp) (term : Tm) :
    inferTerm target typeDepth termContext
        (renameTm embedding.mapName term) =
      inferTerm source typeDepth termContext term := by
  induction term generalizing typeDepth termContext with
  | db index => rfl
  | named name =>
      simp only [renameTm, inferTerm]
      rw [embedding.lookupTerm_commutes]
      cases lookup : source.lookupTerm? name with
      | none => rfl
      | some declaration =>
          cases declaration
          rfl
  | prim index =>
      simp [renameTm, inferTerm, embedding.primitives_eq]
  | app function argument functionIH argumentIH =>
      simp only [renameTm, inferTerm]
      rw [functionIH, argumentIH]
  | lam type body bodyIH =>
      simp only [renameTm, inferTerm]
      split <;> simp_all
  | imp domain codomain domainIH codomainIH =>
      simp only [renameTm, inferTerm]
      rw [domainIH, codomainIH]
  | all type body bodyIH =>
      simp only [renameTm, inferTerm]
      split <;> simp_all
  | typeApp function type functionIH =>
      simp only [renameTm, inferTerm]
      rw [functionIH]
  | typeLam body bodyIH =>
      simp only [renameTm, inferTerm]
      rw [bodyIH]
  | typeAll body bodyIH => rfl

/-- Proposition formation is invariant under the same embedding. -/
theorem checkProposition_rename (embedding : Embedding source target)
    (typeDepth : Nat) (termContext : List Tp) (proposition : Tm) :
    checkProposition target typeDepth termContext
        (renameTm embedding.mapName proposition) =
      checkProposition source typeDepth termContext proposition := by
  induction proposition generalizing typeDepth termContext with
  | typeAll body bodyIH =>
      simp only [renameTm, checkProposition]
      exact bodyIH (typeDepth + 1) []
  | db index =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.db index))
  | named name =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.named name))
  | prim index =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.prim index))
  | app function argument functionIH argumentIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext
          (.app function argument))
  | lam type body bodyIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.lam type body))
  | imp domain codomain domainIH codomainIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext
          (.imp domain codomain))
  | all type body bodyIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.all type body))
  | typeApp function type functionIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext
          (.typeApp function type))
  | typeLam body bodyIH =>
      simp only [renameTm, checkProposition]
      exact congrArg (fun result : Option Tp => decide (result = some .prop))
        (embedding.inferTerm_rename typeDepth termContext (.typeLam body))

/-- Renaming global names commutes with the proof-context shift introduced by
a term binder. -/
theorem map_rename_shift (rename : Name -> Name) (proofContext : List Tm) :
    (proofContext.map (renameTm rename)).map (Tm.shift 0 1) =
      (proofContext.map (Tm.shift 0 1)).map (renameTm rename) := by
  simp only [List.map_map, List.map_inj_left]
  intro proposition membership
  exact (renameTm_shift rename 0 1 proposition).symm

/-- Native proof synthesis commutes exactly with the environment embedding.
The source proof context is renamed pointwise; term-context types remain
unchanged in the fixed-primitive first rung. -/
theorem inferProof_rename (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) :
    inferProof target fuel typeDepth termContext
        (proofContext.map (renameTm embedding.mapName))
        (renamePf embedding.mapName proof) =
      (inferProof source fuel typeDepth termContext proofContext proof).map
        (renameTm embedding.mapName) := by
  induction proof generalizing typeDepth termContext proofContext with
  | gpa name => rfl
  | hyp index =>
      simp [renamePf, inferProof]
  | known name =>
      simp only [renamePf, inferProof]
      rw [embedding.lookupKnown_commutes]
      cases lookup : source.lookupKnown? name with
      | none => rfl
      | some proposition =>
          simpa using embedding.normalize_rename fuel proposition
  | termApp function argument functionIH =>
      simp only [renamePf, inferProof]
      rw [functionIH, embedding.inferTerm_rename,
        embedding.deltaNormalize_rename]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try simp [renameTm]
          case all domain body =>
            cases actualLookup :
                inferTerm source typeDepth termContext argument with
            | none => simp
            | some actualType =>
                by_cases sameType : actualType = domain
                · subst actualType
                  simp
                  cases argumentResult :
                      deltaNormalize source fuel argument with
                  | none => simp
                  | some normalizedArgument =>
                      simp only [Option.map_some, Option.bind_some]
                      rw [← renameTm_instantiate]
                      simpa using embedding.normalize_rename fuel
                        (Tm.instantiate normalizedArgument body)
                · simp [sameType]
  | proofApp function argument functionIH argumentIH =>
      simp only [renamePf, inferProof]
      rw [functionIH, argumentIH]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try simp [renameTm]
          case imp domain codomain =>
            cases argumentResult :
                inferProof source fuel typeDepth termContext proofContext argument with
            | none => simp
            | some actual =>
                by_cases sameProposition : actual = domain
                · subst actual
                  simp
                · have renamedDifferent :
                      renameTm embedding.mapName actual ≠
                        renameTm embedding.mapName domain := by
                    intro equalRenaming
                    exact sameProposition
                      (renameTm_injective embedding.name_injective equalRenaming)
                  simp [sameProposition, renamedDifferent]
  | proofLam proposition body bodyIH =>
      simp only [renamePf, inferProof]
      rw [embedding.inferTerm_rename, embedding.normalize_rename]
      cases propositionType : inferTerm source typeDepth termContext proposition with
      | none => rfl
      | some type =>
          by_cases isProp : type = .prop
          · subst type
            cases normalization : MathdataKernel.normalize source fuel proposition with
            | none => rfl
            | some normalized =>
                simp only [Option.map_some]
                have mappedBody :=
                  bodyIH typeDepth termContext (normalized :: proofContext)
                simp only [List.map_cons] at mappedBody
                simp [mappedBody]
                cases bodyResult : inferProof source fuel typeDepth termContext
                    (normalized :: proofContext) body <;> rfl
          · simp [isProp]
  | termLam type body bodyIH =>
      simp only [renamePf, inferProof]
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => simp
      | true =>
          rw [map_rename_shift]
          rw [bodyIH]
          cases bodyResult : inferProof source fuel typeDepth
              (type :: termContext) (proofContext.map (Tm.shift 0 1)) body <;>
            rfl
  | typeApp function type functionIH =>
      simp only [renamePf, inferProof]
      rw [functionIH]
      cases functionResult :
          inferProof source fuel typeDepth termContext proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try rfl
          case typeAll body =>
            simp [renameTm, renameTm_typeInstantiate]
  | typeLam body bodyIH =>
      cases termContext with
      | nil =>
          cases proofContext with
          | nil =>
              simp only [renamePf, List.map_nil, inferProof,
                List.isEmpty_nil, Bool.true_and, ↓reduceIte]
              have mappedBody := bodyIH (typeDepth + 1) [] []
              simp only [List.map_nil] at mappedBody
              rw [mappedBody]
              cases bodyResult : inferProof source fuel (typeDepth + 1)
                  [] [] body <;> rfl
          | cons proposition proofContext =>
              simp [renamePf, inferProof]
      | cons type termContext =>
          simp [renamePf, inferProof]

/-- Checking against an already-normalized proposition is exactly preserved.
Injectivity is essential in the rejecting direction: without it, two distinct
source propositions could collapse after renaming. -/
theorem checkNormalizedProof_rename (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    checkNormalizedProof target fuel typeDepth termContext
        (proofContext.map (renameTm embedding.mapName))
        (renamePf embedding.mapName proof)
        (renameTm embedding.mapName proposition) =
      checkNormalizedProof source fuel typeDepth termContext proofContext
        proof proposition := by
  unfold checkNormalizedProof
  rw [embedding.inferProof_rename]
  cases proofResult :
      inferProof source fuel typeDepth termContext proofContext proof with
  | none => rfl
  | some inferred =>
      by_cases sameProposition : inferred = proposition
      · subst inferred
        simp
      · have renamedDifferent :
            renameTm embedding.mapName inferred ≠
              renameTm embedding.mapName proposition := by
          intro equalRenaming
          exact sameProposition
            (renameTm_injective embedding.name_injective equalRenaming)
        simp [sameProposition, renamedDifferent]

/-- Source-level proof checking, including normalization failure, commutes
exactly with the environment embedding. -/
theorem checkProof_rename (embedding : Embedding source target)
    (fuel typeDepth : Nat) (termContext : List Tp)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    checkProof target fuel typeDepth termContext
        (proofContext.map (renameTm embedding.mapName))
        (renamePf embedding.mapName proof)
        (renameTm embedding.mapName proposition) =
      checkProof source fuel typeDepth termContext proofContext proof
        proposition := by
  unfold checkProof
  rw [embedding.normalize_rename]
  cases normalization : MathdataKernel.normalize source fuel proposition with
  | none => rfl
  | some normalized =>
      exact embedding.checkNormalizedProof_rename fuel typeDepth termContext
        proofContext proof normalized

/-! ## Induced selected-theory and NIK views -/

/-- Transport the environment-local part of a selected Megalodon query. -/
def mapProfileClaim (embedding : Embedding source target)
    (claim : ProfileClaim) : ProfileClaim where
  fuel := claim.fuel
  typeDepth := claim.typeDepth
  termContext := claim.termContext
  proofContext := claim.proofContext.map (renameTm embedding.mapName)
  proposition := renameTm embedding.mapName claim.proposition

@[simp] theorem mapProfileClaim_fuel (embedding : Embedding source target)
    (claim : ProfileClaim) :
    (embedding.mapProfileClaim claim).fuel = claim.fuel :=
  rfl

@[simp] theorem mapProfileClaim_proposition
    (embedding : Embedding source target) (claim : ProfileClaim) :
    (embedding.mapProfileClaim claim).proposition =
      renameTm embedding.mapName claim.proposition :=
  rfl

/-- A declaration-bearing environment embedding induces an exact
proof-carrying NIK theory-profile view. -/
def authorityView (embedding : Embedding source target) :
    AuthorityView contract source target where
  mapClaim := embedding.mapProfileClaim
  mapCertificate := renamePf embedding.mapName
  check_commutes := by
    intro claim proof
    change
      checkProof target claim.fuel claim.typeDepth claim.termContext
          (claim.proofContext.map (renameTm embedding.mapName))
          (renamePf embedding.mapName proof)
          (renameTm embedding.mapName claim.proposition) =
        checkProof source claim.fuel claim.typeDepth claim.termContext
          claim.proofContext proof claim.proposition
    exact embedding.checkProof_rename claim.fuel claim.typeDepth
      claim.termContext claim.proofContext proof claim.proposition
  meaning_preserved := by
    intro claim theoremhood
    change ProfileClaim at claim
    change NativeTheoremScope source claim at theoremhood
    change NativeTheoremScope target (embedding.mapProfileClaim claim)
    unfold NativeTheoremScope at theoremhood ⊢
    obtain ⟨proof, judged⟩ := theoremhood
    refine ⟨renamePf embedding.mapName proof, ?_⟩
    unfold Judges at judged ⊢
    simp only [attach, mapProfileClaim] at judged ⊢
    obtain ⟨normal, propositionNormalizes, proofSynthesizes⟩ := judged
    refine ⟨renameTm embedding.mapName normal, ?_, ?_⟩
    · rw [embedding.normalize_rename, propositionNormalizes]
      rfl
    · rw [embedding.inferProof_rename, proofSynthesizes]
      rfl

/-- The semantic claim translation obtained after checker exactness has
established scope preservation. -/
def theoryView (embedding : Embedding source target) :
    TheoryView theory source target :=
  embedding.authorityView.toTheoryView

/-- The same theorem mechanically supplies NIK's covered operational
translation, including target-step lifting on translated states. -/
def operationalView (embedding : Embedding source target) :=
  embedding.authorityView.toCoveredTranslation

@[simp] theorem authorityView_mapClaim (embedding : Embedding source target)
    (claim : ProfileClaim) :
    embedding.authorityView.mapClaim claim = embedding.mapProfileClaim claim :=
  rfl

@[simp] theorem authorityView_mapCertificate
    (embedding : Embedding source target) (proof : Pf) :
    embedding.authorityView.mapCertificate proof =
      renamePf embedding.mapName proof :=
  rfl

def identity (environment : Environment) : Embedding environment environment where
  mapName := id
  name_injective := Function.injective_id
  primitives_eq := rfl
  lookupTerm_commutes := by
    intro name
    cases lookup : environment.lookupTerm? name <;>
      simp [lookup, renameTermDecl]
    case some declaration =>
      cases declaration with
      | mk name type definition =>
          cases definition <;> simp
  lookupKnown_commutes := by
    intro name
    cases lookup : environment.lookupKnown? name <;>
      simp [lookup, renameTm_identity]

def comp (earlier : Embedding source middle)
    (later : Embedding middle target) : Embedding source target where
  mapName := later.mapName ∘ earlier.mapName
  name_injective := later.name_injective.comp earlier.name_injective
  primitives_eq := later.primitives_eq.trans earlier.primitives_eq
  lookupTerm_commutes := by
    intro name
    change target.lookupTerm? (later.mapName (earlier.mapName name)) = _
    rw [later.lookupTerm_commutes, earlier.lookupTerm_commutes]
    cases lookup : source.lookupTerm? name with
    | none => simp
    | some declaration =>
        cases declaration with
        | mk declarationName declarationType definition =>
            cases definition <;>
              simp [renameTermDecl, renameTm_comp, Function.comp_apply]
  lookupKnown_commutes := by
    intro name
    change target.lookupKnown? (later.mapName (earlier.mapName name)) = _
    rw [later.lookupKnown_commutes, earlier.lookupKnown_commutes]
    cases lookup : source.lookupKnown? name with
    | none => simp
    | some proposition =>
        simp [renameTm_comp]

/-- Claim transport respects composition of declaration-bearing embeddings. -/
theorem mapProfileClaim_comp (earlier : Embedding source middle)
    (later : Embedding middle target) (claim : ProfileClaim) :
    (comp earlier later).mapProfileClaim claim =
      later.mapProfileClaim (earlier.mapProfileClaim claim) := by
  cases claim
  simp [mapProfileClaim, comp, List.map_map, renameTm_comp,
    Function.comp_apply]

/-- Native proof-object transport obeys the same composition law. -/
theorem renamePf_comp_embedding (earlier : Embedding source middle)
    (later : Embedding middle target) (proof : Pf) :
    renamePf (comp earlier later).mapName proof =
      renamePf later.mapName (renamePf earlier.mapName proof) := by
  simpa [comp] using
    (renamePf_comp earlier.mapName later.mapName proof).symm

/-- Identity environment transport is observationally the identity on local
claims. -/
theorem mapProfileClaim_identity (environment : Environment)
    (claim : ProfileClaim) :
    (identity environment).mapProfileClaim claim = claim := by
  have renameIdentity : renameTm id = id :=
    funext renameTm_identity
  cases claim
  simp [mapProfileClaim, identity, renameIdentity]

end Embedding

/-! ## Nontrivial extension and shadowing canaries -/

namespace Canary

/-- Reserve an explicit namespace for imported source declarations. -/
def prefixName (name : Name) : Name :=
  "source/" ++ name

theorem prefixName_injective : Function.Injective prefixName := by
  intro first second equalNames
  exact (String.append_right_inj "source/").mp equalNames

theorem prefixName_ne_empty (name : Name) : prefixName name ≠ "" := by
  intro emptyName
  have equalLengths := congrArg String.length emptyName
  simp [prefixName] at equalLengths

def outsideDeclaration : TermDecl :=
  { name := "", type := .prop }

/-- The target contains the renamed source theory and a genuinely new
declaration outside the reserved image. -/
def extendedEnvironment : Environment :=
  { primitives := definitionConversionEnvironment.primitives
    terms := outsideDeclaration ::
      definitionConversionEnvironment.terms.map
        (renameTermDecl prefixName)
    known := definitionConversionEnvironment.known.map
      (renameKnownDecl prefixName) }

/-- The unrelated target declaration does not perturb any imported lookup. -/
def namespacedEmbedding :
    Embedding definitionConversionEnvironment extendedEnvironment where
  mapName := prefixName
  name_injective := prefixName_injective
  primitives_eq := rfl
  lookupTerm_commutes := by
    intro name
    have outsideImage : ("" : Name) ≠ prefixName name :=
      (prefixName_ne_empty name).symm
    simp [extendedEnvironment, outsideDeclaration, Environment.lookupTerm?,
      lookupTermList?, outsideImage,
      lookupTermList?_rename prefixName_injective]
  lookupKnown_commutes := by
    intro name
    exact lookupKnownList?_rename prefixName_injective
      definitionConversionEnvironment.known name

/-- Positive control: the target really has authority absent from the source
namespace, without changing replay of imported evidence. -/
theorem extended_has_outside_declaration :
    extendedEnvironment.lookupTerm? "" = some outsideDeclaration := by
  rfl

/-- Positive control: the real definition-sensitive theorem and its native
proof replay exactly after namespace transport. -/
theorem namespaced_definition_profile_accepts :
    (contract.checker extendedEnvironment).check
        (namespacedEmbedding.mapProfileClaim definitionClaim)
        (renamePf prefixName definitionConversionProof) = true := by
  change
    checkProof extendedEnvironment definitionClaim.fuel
      definitionClaim.typeDepth definitionClaim.termContext
      (definitionClaim.proofContext.map
        (renameTm namespacedEmbedding.mapName))
      (renamePf namespacedEmbedding.mapName definitionConversionProof)
      (renameTm namespacedEmbedding.mapName definitionClaim.proposition) = true
  rw [namespacedEmbedding.checkProof_rename]
  exact definition_profile_accepts

/-- A naïve prepend can shadow an existing opaque declaration. -/
def shadowingEnvironment : Environment :=
  { opaqueIdentityEnvironment with
    terms :=
      { name := "idp", type := .arr .prop .prop,
        definition := some (.lam .prop (.db 0)) } ::
        opaqueIdentityEnvironment.terms }

/-- Negative control: the same source claim/proof changes from rejection to
acceptance after the shadowing prepend.  Raw declaration-list growth is not a
theory morphism. -/
theorem shadowing_changes_replay :
    checkProof shadowingEnvironment 16 0 [] []
        definitionConversionProof definitionConversionGoal = true := by
  simp [shadowingEnvironment, opaqueIdentityEnvironment, checkProof,
    checkNormalizedProof, definitionConversionProof, definitionConversionGoal,
    definitionConversionDomain, inferProof, inferTerm,
    MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?, Tm.instantiate,
    Tm.instantiateAt, Tm.shift]

/-- Consequently no identity-on-names environment embedding can certify that
shadowing prepend: its required exact lookup square is false at `idp`. -/
theorem no_identity_embedding_for_shadowing :
    ¬ (exists embedding :
        Embedding opaqueIdentityEnvironment shadowingEnvironment,
      forall name, embedding.mapName name = name) := by
  rintro ⟨embedding, identityNames⟩
  have lookupAgreement := embedding.lookupTerm_commutes "idp"
  rw [identityNames "idp"] at lookupAgreement
  simp [shadowingEnvironment, opaqueIdentityEnvironment,
    Environment.lookupTerm?, lookupTermList?, renameTermDecl] at lookupAgreement

#print axioms namespaced_definition_profile_accepts
#print axioms shadowing_changes_replay
#print axioms no_identity_embedding_for_shadowing
#print axioms Embedding.checkProof_rename
#print axioms Embedding.authorityView
#print axioms Embedding.mapProfileClaim_comp

end Canary

end Mettapedia.Languages.Megalodon.EnvironmentEmbedding
