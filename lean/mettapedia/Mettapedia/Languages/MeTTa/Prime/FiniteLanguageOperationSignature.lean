import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Data.List.OfFn
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec

/-!
# Finite authored language-operation signatures

A validated language package contains finitely many named language codes and
finitely many primitive language-changing routes.  This module turns precisely
that authored data into:

* a quiver whose paths are the freely composed route programs;
* a functor into validated GSLT language definitions;
* ordinary declaration-aware Prime syntax for codes and routes; and
* an executable, syntax-directed route recognizer.

There is no separate composition tree: route programs are Mathlib
`Quiver.Path`s.  The syntax recognizer is defined solely from the finite
authored names and endpoints; semantic GSLT morphisms enter only through the
separate structural interpretation.
-/

namespace Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSpec
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution

/-- The four names shared by every finite language-operation presentation. -/
structure CoreNames where
  languageType : DeclName
  routeType : DeclName
  identity : DeclName
  compose : DeclName
deriving DecidableEq, Repr

/-- A finite, named presentation of validated languages and primitive routes.

The route table is endpoint-indexed by its `source` and `target` functions.
Each route is also supplied with its already validated structural GSLT
morphism.  `declaredNamesNodup` is the executable no-shadowing boundary between
the four shared names, language constants, and primitive-route constants. -/
structure Signature where
  Language : Type
  languageCount : Nat
  routeCount : Nat
  names : CoreNames
  languageIndex : Fin languageCount ≃ Language
  languageName : Language ↪ DeclName
  routeName : Fin routeCount ↪ DeclName
  source : Fin routeCount → Language
  target : Fin routeCount → Language
  presentation : Language → ValidatedLanguageDef
  routeMorphism : ∀ route,
    StructuralMorphism (presentation (source route)) (presentation (target route))
  declaredNamesNodup :
    ([names.languageType, names.routeType, names.identity, names.compose] ++
      List.ofFn (fun index => languageName (languageIndex index)) ++
      List.ofFn routeName).Nodup

namespace Signature

abbrev Route (signature : Signature) := Fin signature.routeCount

instance languageDecidableEq (signature : Signature) :
    DecidableEq signature.Language :=
  signature.languageIndex.symm.decidableEq

/-- Primitive arrows are exactly entries of the authored route table. -/
inductive Generator (signature : Signature) :
    signature.Language → signature.Language → Type
  | named (route : signature.Route) :
      Generator signature (signature.source route) (signature.target route)

instance operationQuiver (signature : Signature) : Quiver signature.Language where
  Hom := signature.Generator

/-- Freely composed route programs. -/
abbrev Program (signature : Signature)
    (source target : signature.Language) := Quiver.Path source target

def identityProgram (signature : Signature) (language : signature.Language) :
    signature.Program language language :=
  .nil

def namedProgram (signature : Signature) (route : signature.Route) :
    signature.Program (signature.source route) (signature.target route) :=
  Quiver.Hom.toPath (.named route)

/-- The authored primitive routes as a prefunctor into validated GSLT
languages. -/
def structuralPrefunctor (signature : Signature) :
    signature.Language ⥤q ValidatedLanguageDef where
  obj := signature.presentation
  map
    | .named route => signature.routeMorphism route

/-- The structural interpretation of a route program is supplied by the free
path-category lift, rather than by another recursive interpreter. -/
def structuralInterpretation (signature : Signature) :
    Paths signature.Language ⥤ ValidatedLanguageDef :=
  Paths.lift signature.structuralPrefunctor

@[simp]
theorem structuralInterpretation_named (signature : Signature)
    (route : signature.Route) :
    signature.structuralInterpretation.map (signature.namedProgram route) =
      signature.routeMorphism route := by
  rfl

/-! ## Generic closed Prime syntax -/

def languageType (signature : Signature) : PureTm n :=
  .const signature.names.languageType

def languageTerm (signature : Signature)
    (language : signature.Language) : PureTm n :=
  .const (signature.languageName language)

def routeType (signature : Signature) (source target : PureTm n) : PureTm n :=
  .app (.app (.const signature.names.routeType) source) target

def routeTypeFormer (signature : Signature) : PureTm 0 :=
  .pi signature.languageType (.pi signature.languageType .u0)

def identityType (signature : Signature) : PureTm 0 :=
  .pi signature.languageType
    (signature.routeType (.var 0) (.var 0))

def composeType (signature : Signature) : PureTm 0 :=
  .pi signature.languageType
    (.pi signature.languageType
      (.pi signature.languageType
        (.pi (signature.routeType (.var 2) (.var 1))
          (.pi (signature.routeType (.var 2) (.var 1))
            (signature.routeType (.var 4) (.var 2))))))

def coreSpecs (signature : Signature) : List DeclSpec :=
  [{ name := signature.names.languageType, type := .u0 },
   { name := signature.names.routeType, type := signature.routeTypeFormer },
   { name := signature.names.identity, type := signature.identityType },
   { name := signature.names.compose, type := signature.composeType }]

def languageSpec (signature : Signature)
    (language : signature.Language) : DeclSpec :=
  { name := signature.languageName language
    type := signature.languageType }

def routeSpec (signature : Signature) (route : signature.Route) : DeclSpec :=
  { name := signature.routeName route
    type := signature.routeType
      (signature.languageTerm (signature.source route))
      (signature.languageTerm (signature.target route)) }

def operationSpecs (signature : Signature) : List DeclSpec :=
  signature.coreSpecs ++
    List.ofFn (fun index =>
      signature.languageSpec (signature.languageIndex index)) ++
    List.ofFn signature.routeSpec

def operationDeclEnv (signature : Signature) : DeclEnv :=
  envOfSpecs signature.operationSpecs

def identityTerm (signature : Signature)
    (language : signature.Language) : PureTm 0 :=
  .app (.const signature.names.identity) (signature.languageTerm language)

def composeTerm (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : PureTm 0) : PureTm 0 :=
  .app
    (.app
      (.app
        (.app
          (.app (.const signature.names.compose)
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last))
      earlier)
    later

def routeTerm (signature : Signature) (route : signature.Route) : PureTm 0 :=
  .const (signature.routeName route)

/-- Compile a route path into closed Prime syntax. -/
def encodeProgram (signature : Signature) {source target : signature.Language} :
    signature.Program source target → PureTm 0
  | .nil => signature.identityTerm source
  | .cons prior generator =>
      match generator with
      | .named route =>
          signature.composeTerm source (signature.source route)
            (signature.target route) (signature.encodeProgram prior)
            (signature.routeTerm route)

/-! ## Finite name decoding -/

/-- Executable inverse search for a finite injectively named family. -/
def decodeIndex? {α : Type} [DecidableEq α] :
    {count : Nat} → (Fin count → α) → α → Option (Fin count)
  | 0, _, _ => none
  | _ + 1, names, name =>
      if names 0 = name then some 0
      else
        (decodeIndex? (fun index => names index.succ) name).map Fin.succ

@[simp]
theorem decodeIndex_encode {α : Type} [DecidableEq α]
    {count : Nat} (names : Fin count → α)
    (injective : Function.Injective names) (index : Fin count) :
    decodeIndex? names (names index) = some index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp [decodeIndex?]
      · intro prior
        have different : names 0 ≠ names prior.succ := by
          intro equal
          have indexEqual : (0 : Fin (count + 1)) = prior.succ :=
            injective equal
          have valueEqual : 0 = prior.val + 1 := congrArg Fin.val indexEqual
          exact (Nat.zero_ne_add_one prior.val) valueEqual
        have tailInjective :
            Function.Injective (fun i : Fin count => names i.succ) :=
          fun _ _ equal => Fin.ext (Nat.add_right_cancel
            (congrArg Fin.val (injective equal)))
        simp [decodeIndex?, different,
          inductionHypothesis (fun i : Fin count => names i.succ)
            tailInjective prior]

theorem decodeIndex_eq_some {α : Type} [DecidableEq α]
    {count : Nat} (names : Fin count → α) (name : α) (index : Fin count)
    (accepted : decodeIndex? names name = some index) :
    names index = name := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      by_cases firstMatches : names 0 = name
      · rw [decodeIndex?, if_pos firstMatches] at accepted
        cases accepted
        exact firstMatches
      · rw [decodeIndex?, if_neg firstMatches] at accepted
        cases tailAccepted :
            decodeIndex? (fun i : Fin count => names i.succ) name with
        | none => simp [tailAccepted] at accepted
        | some tailIndex =>
            rw [tailAccepted] at accepted
            cases accepted
            exact inductionHypothesis
              (fun i : Fin count => names i.succ) tailIndex tailAccepted

def decodeLanguageName? (signature : Signature) (name : DeclName) :
    Option signature.Language :=
  (decodeIndex?
    (fun index => signature.languageName (signature.languageIndex index))
    name).map signature.languageIndex

def decodeRouteName? (signature : Signature) (name : DeclName) :
    Option signature.Route :=
  decodeIndex? signature.routeName name

@[simp]
theorem decodeLanguageName_languageName (signature : Signature)
    (language : signature.Language) :
    signature.decodeLanguageName? (signature.languageName language) =
      some language := by
  unfold decodeLanguageName?
  have decoded := decodeIndex_encode
    (fun index => signature.languageName (signature.languageIndex index))
    (signature.languageName.injective.comp signature.languageIndex.injective)
    (signature.languageIndex.symm language)
  simpa using congrArg (Option.map signature.languageIndex) decoded

@[simp]
theorem decodeRouteName_routeName (signature : Signature)
    (route : signature.Route) :
    signature.decodeRouteName? (signature.routeName route) = some route :=
  decodeIndex_encode signature.routeName signature.routeName.injective route

def decodeLanguageTerm? (signature : Signature) :
    PureTm 0 → Option signature.Language
  | .const name => signature.decodeLanguageName? name
  | _ => none

@[simp]
theorem decodeLanguageTerm_languageTerm (signature : Signature)
    (language : signature.Language) :
    signature.decodeLanguageTerm? (signature.languageTerm language) =
      some language := by
  simp [decodeLanguageTerm?, languageTerm]

theorem decodeLanguageTerm_eq_some (signature : Signature)
    {term : PureTm 0} {language : signature.Language}
    (accepted : signature.decodeLanguageTerm? term = some language) :
    term = signature.languageTerm language := by
  cases term with
  | const name =>
      unfold decodeLanguageTerm? at accepted
      unfold decodeLanguageName? at accepted
      cases decodedIndex : decodeIndex?
          (fun index => signature.languageName (signature.languageIndex index))
          name with
      | none => simp [decodedIndex] at accepted
      | some index =>
          simp [decodedIndex] at accepted
          subst language
          exact congrArg PureTm.const
            (decodeIndex_eq_some
              (fun index => signature.languageName
                (signature.languageIndex index))
              name index decodedIndex).symm
  | _ => simp [decodeLanguageTerm?] at accepted

/-- A recovered route program with intrinsically indexed endpoints. -/
structure DecodedProgram (signature : Signature) where
  source : signature.Language
  target : signature.Language
  program : signature.Program source target

/-- Transport a path across checked endpoint equalities. -/
def reindexProgram (signature : Signature)
    {source target newSource newTarget : signature.Language}
    (sourceEq : source = newSource) (targetEq : target = newTarget) :
    signature.Program source target → signature.Program newSource newTarget := by
  subst newSource
  subst newTarget
  exact id

def composeDecoded? (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : signature.DecodedProgram) :
    Option signature.DecodedProgram :=
  if earlierSource : earlier.source = first then
    if earlierTarget : earlier.target = middle then
      if laterSource : later.source = middle then
        if laterTarget : later.target = last then
          some
            { source := first
              target := last
              program := Quiver.Path.comp
                (signature.reindexProgram earlierSource earlierTarget
                  earlier.program)
                (signature.reindexProgram laterSource laterTarget
                  later.program) }
        else none
      else none
    else none
  else none

/-- Syntax-directed recognition of the finite Prime route fragment. -/
def decodeProgram? (signature : Signature) :
    PureTm 0 → Option signature.DecodedProgram
  | .app (.const name) languageTerm =>
      if name = signature.names.identity then
        (signature.decodeLanguageTerm? languageTerm).map fun language =>
          { source := language
            target := language
            program := signature.identityProgram language }
      else none
  | .const name =>
      (signature.decodeRouteName? name).map fun route =>
        { source := signature.source route
          target := signature.target route
          program := signature.namedProgram route }
  | .app
      (.app
        (.app
          (.app
            (.app (.const name) firstTerm)
            middleTerm)
          lastTerm)
        earlierTerm)
      laterTerm =>
      if name = signature.names.compose then
        match signature.decodeLanguageTerm? firstTerm,
            signature.decodeLanguageTerm? middleTerm,
            signature.decodeLanguageTerm? lastTerm,
            signature.decodeProgram? earlierTerm,
            signature.decodeProgram? laterTerm with
        | some first, some middle, some last, some earlier, some later =>
            signature.composeDecoded? first middle last earlier later
        | _, _, _, _, _ => none
      else none
  | _ => none
termination_by term => term

@[simp]
theorem composeDecoded_programs (signature : Signature)
    {first middle last : signature.Language}
    (earlier : signature.Program first middle)
    (later : signature.Program middle last) :
    signature.composeDecoded? first middle last
        { source := first, target := middle, program := earlier }
        { source := middle, target := last, program := later } =
      some
        { source := first
          target := last
          program := Quiver.Path.comp earlier later } := by
  simp [composeDecoded?, reindexProgram]

/-- Encoding followed by independent recognition recovers every route path. -/
@[simp]
theorem decodeProgram_encodeProgram (signature : Signature)
    {source target : signature.Language}
    (program : signature.Program source target) :
    signature.decodeProgram? (signature.encodeProgram program) =
      some { source := source, target := target, program := program } := by
  induction program with
  | nil =>
      simp [encodeProgram, identityTerm, decodeProgram?, identityProgram]
  | cons prior generator inductionHypothesis =>
      cases generator with
      | named route =>
          simp [encodeProgram, composeTerm, routeTerm, decodeProgram?,
            inductionHypothesis, composeDecoded_programs, namedProgram]

/-- A composition term cannot disguise a disagreement between the recovered
target of its first route and the written middle endpoint. -/
theorem decodeProgram_compose_rejects_earlier_target
    (signature : Signature)
    {first actualMiddle writtenMiddle last : signature.Language}
    (earlier : signature.Program first actualMiddle)
    (later : signature.Program writtenMiddle last)
    (different : actualMiddle ≠ writtenMiddle) :
    signature.decodeProgram?
      (signature.composeTerm first writtenMiddle last
        (signature.encodeProgram earlier) (signature.encodeProgram later)) =
      none := by
  simp only [composeTerm, decodeProgram?]
  simp [decodeProgram_encodeProgram, composeDecoded?, different]

/-! ## Generated declarations and exact typing -/

@[simp]
theorem operationSpecs_names (signature : Signature) :
    signature.operationSpecs.map DeclSpec.name =
      [signature.names.languageType, signature.names.routeType,
        signature.names.identity, signature.names.compose] ++
      List.ofFn (fun index =>
        signature.languageName (signature.languageIndex index)) ++
      List.ofFn signature.routeName := by
  simp [operationSpecs, coreSpecs, languageSpec, routeSpec, Function.comp_def]

theorem languageSpec_mem (signature : Signature)
    (language : signature.Language) :
    signature.languageSpec language ∈ signature.operationSpecs := by
  simp only [operationSpecs, List.mem_append]
  exact Or.inl (Or.inr (List.mem_ofFn.mpr
    ⟨signature.languageIndex.symm language,
      congrArg signature.languageSpec
        (signature.languageIndex.apply_symm_apply language)⟩))

theorem routeSpec_mem (signature : Signature) (route : signature.Route) :
    signature.routeSpec route ∈ signature.operationSpecs := by
  simp [operationSpecs, List.mem_ofFn]

theorem operationSpecs_value_none (signature : Signature)
    {specification : DeclSpec}
    (membership : specification ∈ signature.operationSpecs) :
    specification.value? = none := by
  have everySpecification :
      ∀ entry ∈ signature.operationSpecs, entry.value? = none := by
    simp [operationSpecs, coreSpecs, languageSpec, routeSpec]
    intro entry generated
    rcases generated with ⟨language, rfl⟩ | ⟨route, rfl⟩ <;> rfl
  exact everySpecification specification membership

theorem operationSpecs_signatureWellFormed (signature : Signature) :
    SignatureWellFormed signature.operationSpecs where
  noShadowing := by
    simpa only [operationSpecs_names] using signature.declaredNamesNodup
  obligations := by
    constructor
    · intro specification membership value valueEquation
      rw [signature.operationSpecs_value_none membership] at valueEquation
      simp at valueEquation
    · intro specification membership value valueEquation
      rw [signature.operationSpecs_value_none membership] at valueEquation
      simp at valueEquation

@[simp]
theorem typeOf_languageType (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.languageType =
      some .u0 := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.languageType, type := .u0 })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_routeType (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.routeType =
      some signature.routeTypeFormer := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.routeType, type := signature.routeTypeFormer })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_identity (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.identity =
      some signature.identityType := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.identity, type := signature.identityType })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_compose (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.compose =
      some signature.composeType := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.compose, type := signature.composeType })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_languageName (signature : Signature)
    (language : signature.Language) :
    typeOf? signature.operationDeclEnv (signature.languageName language) =
      some signature.languageType := by
  simpa [operationDeclEnv, languageSpec] using
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      signature.operationSpecs_signatureWellFormed.noShadowing
      (signature.languageSpec_mem language)

@[simp]
theorem typeOf_routeName (signature : Signature) (route : signature.Route) :
    typeOf? signature.operationDeclEnv (signature.routeName route) =
      some (signature.routeType
        (signature.languageTerm (signature.source route))
        (signature.languageTerm (signature.target route))) := by
  simpa [operationDeclEnv, routeSpec] using
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      signature.operationSpecs_signatureWellFormed.noShadowing
      (signature.routeSpec_mem route)

theorem hasType_languageTerm (signature : Signature)
    (language : signature.Language) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.languageTerm language) signature.languageType :=
  hasType_const_from_lookup
    (E := signature.operationDeclEnv) (Γ := .nil)
    (c := signature.languageName language) (A0 := signature.languageType)
    (signature.typeOf_languageName language)

theorem hasType_identityTerm (signature : Signature)
    (language : signature.Language) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.identityTerm language)
      (signature.routeType (signature.languageTerm language)
        (signature.languageTerm language)) := by
  unfold identityTerm
  simpa [identityType, routeType, languageType, inst0, subst, rename,
    liftRen] using
    (HasTypeDecl.app_elim
      (hasType_const_from_lookup (E := signature.operationDeclEnv)
        (Γ := .nil) (c := signature.names.identity)
        (A0 := signature.identityType) signature.typeOf_identity)
      (signature.hasType_languageTerm language))

theorem hasType_routeTerm (signature : Signature) (route : signature.Route) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.routeTerm route)
      (signature.routeType
        (signature.languageTerm (signature.source route))
        (signature.languageTerm (signature.target route))) :=
  hasType_const_from_lookup
    (E := signature.operationDeclEnv) (Γ := .nil)
    (c := signature.routeName route)
    (A0 := signature.routeType
      (signature.languageTerm (signature.source route))
      (signature.languageTerm (signature.target route)))
    (signature.typeOf_routeName route)

private def instantiatePiCodomain (type argument : PureTm n) : PureTm n :=
  match type with
  | .pi _ codomain => inst0 argument codomain
  | other => other

private theorem instantiatePiCodomain_composeType (signature : Signature)
    (first middle last : signature.Language) :
    instantiatePiCodomain
        (instantiatePiCodomain
          (instantiatePiCodomain signature.composeType
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last) =
      .pi
        (signature.routeType (signature.languageTerm first)
          (signature.languageTerm middle))
        (.pi
          (liftClosed (signature.routeType (signature.languageTerm middle)
            (signature.languageTerm last)))
          (liftClosed (signature.routeType (signature.languageTerm first)
            (signature.languageTerm last)))) := by
  rfl

theorem hasType_composeTerm (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : PureTm 0)
    (earlierTyped : HasTypeDecl signature.operationDeclEnv .nil earlier
      (signature.routeType (signature.languageTerm first)
        (signature.languageTerm middle)))
    (laterTyped : HasTypeDecl signature.operationDeclEnv .nil later
      (signature.routeType (signature.languageTerm middle)
        (signature.languageTerm last))) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.composeTerm first middle last earlier later)
      (signature.routeType (signature.languageTerm first)
        (signature.languageTerm last)) := by
  let firstTerm : PureTm 0 := signature.languageTerm first
  let middleTerm : PureTm 0 := signature.languageTerm middle
  let lastTerm : PureTm 0 := signature.languageTerm last
  have composeTyped : HasTypeDecl signature.operationDeclEnv .nil
      (.const signature.names.compose) signature.composeType :=
    hasType_const_from_lookup
      (E := signature.operationDeclEnv) (Γ := .nil)
      (c := signature.names.compose) (A0 := signature.composeType)
      signature.typeOf_compose
  have languagesApplied :=
    HasTypeDecl.app_elim
      (HasTypeDecl.app_elim
        (HasTypeDecl.app_elim composeTyped
          (signature.hasType_languageTerm first))
        (signature.hasType_languageTerm middle))
      (signature.hasType_languageTerm last)
  have languagesApplied' : HasTypeDecl signature.operationDeclEnv .nil
      (.app
        (.app
          (.app (.const signature.names.compose) firstTerm)
          middleTerm)
        lastTerm)
      (.pi (signature.routeType firstTerm middleTerm)
        (.pi (liftClosed (signature.routeType middleTerm lastTerm))
          (liftClosed (signature.routeType firstTerm lastTerm)))) := by
    change HasTypeDecl signature.operationDeclEnv .nil
      (.app
        (.app
          (.app (.const signature.names.compose)
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last))
      (instantiatePiCodomain
        (instantiatePiCodomain
          (instantiatePiCodomain signature.composeType
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last)) at languagesApplied
    rw [instantiatePiCodomain_composeType] at languagesApplied
    simpa [firstTerm, middleTerm, lastTerm] using languagesApplied
  have earlierApplied := HasTypeDecl.app_elim languagesApplied' earlierTyped
  have laterApplied := HasTypeDecl.app_elim earlierApplied laterTyped
  simpa [composeTerm, firstTerm, middleTerm, lastTerm, inst0, subst,
    subst_liftClosed, liftClosed_zero] using laterApplied

/-- Every generated route program has its exact dependent route type. -/
theorem encodeProgram_typed (signature : Signature)
    {source target : signature.Language}
    (program : signature.Program source target) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.encodeProgram program)
      (signature.routeType (signature.languageTerm source)
        (signature.languageTerm target)) := by
  induction program with
  | nil => exact signature.hasType_identityTerm source
  | cons prior generator inductionHypothesis =>
      cases generator with
      | named route =>
          exact signature.hasType_composeTerm source
            (signature.source route) (signature.target route)
            (signature.encodeProgram prior) (signature.routeTerm route)
            inductionHypothesis (signature.hasType_routeTerm route)

/-- The finite syntax recognizer accepts only well-typed route programs. -/
theorem decodeProgram_typed (signature : Signature)
    (term : PureTm 0) (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    HasTypeDecl signature.operationDeclEnv .nil term
      (signature.routeType (signature.languageTerm decoded.source)
        (signature.languageTerm decoded.target)) := by
  fun_induction signature.decodeProgram? term generalizing decoded with
  | case1 languageTerm =>
      cases decodedLanguage : signature.decodeLanguageTerm? languageTerm with
      | none => simp [decodedLanguage] at accepted
      | some language =>
          have languageTermEq :=
            signature.decodeLanguageTerm_eq_some decodedLanguage
          simp [decodedLanguage] at accepted
          subst languageTerm
          subst decoded
          exact signature.hasType_identityTerm language
  | case2 _ _ _ => simp at accepted
  | case3 name =>
      cases routeDecoded : signature.decodeRouteName? name with
      | none => simp [routeDecoded] at accepted
      | some route =>
          have nameEq : name = signature.routeName route :=
            (decodeIndex_eq_some signature.routeName name route routeDecoded).symm
          subst name
          simp at accepted
          subst decoded
          exact signature.hasType_routeTerm route
  | case4 firstTerm middleTerm lastTerm earlierTerm laterTerm
      first middle last earlier later laterDecoded earlierDecoded
      lastDecoded middleDecoded firstDecoded earlierIH laterIH =>
      have firstTermEq := signature.decodeLanguageTerm_eq_some firstDecoded
      have middleTermEq := signature.decodeLanguageTerm_eq_some middleDecoded
      have lastTermEq := signature.decodeLanguageTerm_eq_some lastDecoded
      subst firstTerm
      subst middleTerm
      subst lastTerm
      have earlierTyped := earlierIH earlier earlierDecoded
      have laterTyped := laterIH later laterDecoded
      unfold composeDecoded? at accepted
      split_ifs at accepted with earlierSource earlierTarget laterSource laterTarget
      · simp [earlierSource, earlierTarget] at earlierTyped
        simp [laterSource, laterTarget] at laterTyped
        cases accepted
        exact signature.hasType_composeTerm first middle last
          earlierTerm laterTerm earlierTyped laterTyped
  | case5 _ _ _ _ _ _ _ _ => simp at accepted
  | case6 _ _ _ _ _ _ _ => simp at accepted
  | case7 _ _ _ _ => simp at accepted

/-- A closed Prime term accepted by an independently generated finite route
signature. -/
structure RecognizedOperation (signature : Signature) where
  term : PureTm 0
  decoded : signature.DecodedProgram
  recognized : signature.decodeProgram? term = some decoded

namespace RecognizedOperation

theorem wellTyped {signature : Signature}
    (operation : signature.RecognizedOperation) :
    HasTypeDecl signature.operationDeclEnv .nil operation.term
      (signature.routeType
        (signature.languageTerm operation.decoded.source)
        (signature.languageTerm operation.decoded.target)) :=
  signature.decodeProgram_typed operation.term operation.decoded
    operation.recognized

def structuralRoute {signature : Signature}
    (operation : signature.RecognizedOperation) :
    signature.presentation operation.decoded.source ⟶
      signature.presentation operation.decoded.target :=
  signature.structuralInterpretation.map operation.decoded.program

end RecognizedOperation

end Signature

end Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature
