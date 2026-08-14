import Mettapedia.Languages.MeTTa.Prime.DataFibration
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# The first HE-to-Prime Data translation kernel

This module states the first dialect delta at the type-and-elaboration level.
HE's `Atom` parameter convention is translated to Prime's explicit `Data _`
domain, while `Atom` in ordinary value position becomes the inert top.  The
translation has an exact image characterization and preserves whether an
argument is held or evaluated.

The syntax map is hygienic by construction: it translates constructor heads
only.  Bound indices and free metavariable names are fixed pointwise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Type translation and its exact image -/

inductive HEType where
  | atom
  | named (name : String)
  | arrow (domain codomain : HEType)
  deriving DecidableEq, Repr

inductive PrimeType where
  | dynamic
  | atomTop
  | named (name : String)
  | data (payload : Option PrimeType)
  | arrow (domain codomain : PrimeType)
  deriving Repr

/-- One structural translation with an explicit domain-position flag. -/
def translate (domainPosition : Bool) : HEType → PrimeType
  | .atom => if domainPosition then .data none else .atomTop
  | .named name => .named name
  | .arrow domain codomain =>
      .arrow (translate true domain) (translate false codomain)

/-- Value-position translation. -/
def translateType : HEType → PrimeType := translate false

/-- Export the domain action as a separately testable kernel function. -/
def translateDomain : HEType → PrimeType
  := translate true

@[simp] theorem translateType_atom : translateType .atom = .atomTop := rfl

@[simp] theorem translateDomain_atom :
    translateDomain .atom = .data none := rfl

@[simp] theorem translateType_arrow (domain codomain : HEType) :
    translateType (.arrow domain codomain) =
      .arrow (translateDomain domain) (translateType codomain) := rfl

/-- One structural partial inverse with an explicit domain-position flag. -/
def untranslate (domainPosition : Bool) : PrimeType → Option HEType
  | .atomTop => if domainPosition then none else some .atom
  | .named name => some (.named name)
  | .data none => if domainPosition then some .atom else none
  | .data (some _) => none
  | .arrow domain codomain => do
      let heDomain ← untranslate true domain
      let heCodomain ← untranslate false codomain
      pure (.arrow heDomain heCodomain)
  | .dynamic => none

/-- Partial inverse on the exact image of value-position translation. -/
def untranslateType : PrimeType → Option HEType := untranslate false

/-- Partial inverse on the exact image of domain translation. -/
def untranslateDomain : PrimeType → Option HEType := untranslate true

@[simp] theorem untranslate_translate (domainPosition : Bool) (type : HEType) :
    untranslate domainPosition (translate domainPosition type) = some type := by
  induction type generalizing domainPosition with
  | atom => cases domainPosition <;> rfl
  | named name => cases domainPosition <;> rfl
  | arrow domain codomain domainIH codomainIH =>
      simp [translate, untranslate, domainIH, codomainIH]

@[simp] theorem untranslate_translate_type (type : HEType) :
    untranslateType (translateType type) = some type :=
  untranslate_translate false type

@[simp] theorem untranslate_translate_domain (type : HEType) :
    untranslateDomain (translateDomain type) = some type :=
  untranslate_translate true type

def InTranslationImage (type : PrimeType) : Prop :=
  ∃ source, translateType source = type

/-- Exact-image round trip: no Prime type outside the authored HE projection
is silently claimed to have an HE preimage. -/
theorem translate_untranslate_of_image {type : PrimeType}
    (inImage : InTranslationImage type) :
    Option.map translateType (untranslateType type) = some type := by
  rcases inImage with ⟨source, rfl⟩
  simp

theorem dynamic_has_no_he_preimage :
    ¬ InTranslationImage .dynamic := by
  rintro ⟨source, equal⟩
  have roundtrip := untranslate_translate_type source
  rw [equal] at roundtrip
  cases roundtrip

/-! ## Call-site elaboration -/

inductive RawTerm where
  | symbol (name : String)
  | application (head : String) (arguments : List RawTerm)

inductive ElaboratedArgument where
  | evaluated (term : RawTerm)
  | held (term : RawTerm)

/-- Frozen HE domain convention, stated independently. -/
def elaborateHE (domain : HEType) (argument : RawTerm) : ElaboratedArgument :=
  match domain with
  | .atom => .held argument
  | _ => .evaluated argument

/-- Prime elaboration reads evaluation control from the explicit Data
modality, never from the top type. -/
def elaboratePrime (domain : PrimeType)
    (argument : RawTerm) : ElaboratedArgument :=
  match domain with
  | .data _ => .held argument
  | _ => .evaluated argument

/-- The first translation delta preserves call sites exactly: translating
the signature supplies the quotation that HE previously inserted implicitly. -/
theorem first_delta_preserves_elaboration
    (domain : HEType) (argument : RawTerm) :
    elaboratePrime (translateDomain domain) argument =
      elaborateHE domain argument := by
  cases domain <;> rfl

theorem atom_domain_inserts_hold (argument : RawTerm) :
    elaboratePrime (translateDomain .atom) argument = .held argument := rfl

theorem atom_top_does_not_hold (argument : RawTerm) :
    elaboratePrime .atomTop argument = .evaluated argument := rfl

/-! ## Constructor-only hygienic syntax transport -/

mutual
  /-- Translate language constructor heads while retaining binding structure,
  display metadata, free metavariable names, and collection shape. -/
  def mapPattern (mapHead : String → String) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply head arguments => .apply (mapHead head) (mapPatternList mapHead arguments)
    | .lambda name body => .lambda name (mapPattern mapHead body)
    | .multiLambda arity names body =>
        .multiLambda arity names (mapPattern mapHead body)
    | .subst body replacement =>
        .subst (mapPattern mapHead body) (mapPattern mapHead replacement)
    | .collection kind elements rest =>
        .collection kind (mapPatternList mapHead elements) rest

  def mapPatternList (mapHead : String → String) : List Pattern → List Pattern
    | [] => []
    | term :: rest => mapPattern mapHead term :: mapPatternList mapHead rest
end

@[simp] theorem mapPatternList_eq_map (mapHead : String → String)
    (terms : List Pattern) :
    mapPatternList mapHead terms = terms.map (mapPattern mapHead) := by
  induction terms with
  | nil => rfl
  | cons term rest inductionHypothesis =>
      simp [mapPatternList, inductionHypothesis]

@[simp] theorem mapPattern_bvar (mapHead : String → String) (index : Nat) :
    mapPattern mapHead (.bvar index) = .bvar index := rfl

@[simp] theorem mapPattern_fvar (mapHead : String → String) (name : String) :
    mapPattern mapHead (.fvar name) = .fvar name := rfl

/-- The most local capture-avoidance law: a language translation cannot
rename either kind of variable. -/
theorem variables_are_fixed (mapHead : String → String) :
    (∀ index, mapPattern mapHead (.bvar index) = .bvar index) ∧
      (∀ name, mapPattern mapHead (.fvar name) = .fvar name) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-! ### Full contextual hygiene

Fixing variable constructors is necessary but not sufficient for hygienic
language change.  The transport must also commute with the locally nameless
operations that implement contextual opening, abstraction, lifting, and
binder-eliminating substitution.  The following equations state that stronger
criterion against the canonical MeTTaIL operations. -/

theorem mapPattern_openBVar (mapHead : String → String) (index : Nat)
    (replacement body : Pattern) :
    mapPattern mapHead (openBVar index replacement body) =
      openBVar index (mapPattern mapHead replacement) (mapPattern mapHead body) := by
  induction body using Pattern.inductionOn generalizing index with
  | hbvar variableIndex =>
      by_cases equal : variableIndex = index <;>
        simp [openBVar, mapPattern, equal]
  | hfvar name => simp [openBVar, mapPattern]
  | happly head arguments inductionHypothesis =>
      simp only [openBVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (mapHead head))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership index
  | hlambda name body inductionHypothesis =>
      simp [openBVar, mapPattern, inductionHypothesis]
  | hmultiLambda arity names body inductionHypothesis =>
      simp [openBVar, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [openBVar, mapPattern, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [openBVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun translatedElements =>
        Pattern.collection kind translatedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership index

theorem mapPattern_closeFVar (mapHead : String → String) (index : Nat)
    (name : String) (body : Pattern) :
    mapPattern mapHead (closeFVar index name body) =
      closeFVar index name (mapPattern mapHead body) := by
  induction body using Pattern.inductionOn generalizing index with
  | hbvar variableIndex => simp [closeFVar, mapPattern]
  | hfvar variableName =>
      by_cases equal : variableName = name <;>
        simp [closeFVar, mapPattern, equal]
  | happly head arguments inductionHypothesis =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (mapHead head))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership index
  | hlambda binder body inductionHypothesis =>
      simp [closeFVar, mapPattern, inductionHypothesis]
  | hmultiLambda arity names body inductionHypothesis =>
      simp [closeFVar, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [closeFVar, mapPattern, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [closeFVar, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun translatedElements =>
        Pattern.collection kind translatedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership index

theorem mapPattern_liftBVars (mapHead : String → String) (cutoff shift : Nat)
    (body : Pattern) :
    mapPattern mapHead (liftBVars cutoff shift body) =
      liftBVars cutoff shift (mapPattern mapHead body) := by
  induction body using Pattern.inductionOn generalizing cutoff with
  | hbvar variableIndex =>
      by_cases shifted : cutoff ≤ variableIndex <;>
        simp [liftBVars, mapPattern, shifted]
  | hfvar name => simp [liftBVars, mapPattern]
  | happly head arguments inductionHypothesis =>
      simp only [liftBVars, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (mapHead head))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership cutoff
  | hlambda name body inductionHypothesis =>
      simp [liftBVars, mapPattern, inductionHypothesis]
  | hmultiLambda arity names body inductionHypothesis =>
      simp [liftBVars, mapPattern, inductionHypothesis]
  | hsubst body replacement bodyIH replacementIH =>
      simp [liftBVars, mapPattern, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [liftBVars, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun translatedElements =>
        Pattern.collection kind translatedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership cutoff

theorem mapPattern_instantiateBVarAt (mapHead : String → String)
    (depth : Nat) (replacement body : Pattern) :
    mapPattern mapHead (instantiateBVarAt depth replacement body) =
      instantiateBVarAt depth (mapPattern mapHead replacement)
        (mapPattern mapHead body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar variableIndex =>
      simp only [instantiateBVarAt, mapPattern]
      split <;> try rfl
      split <;> try rfl
      exact mapPattern_liftBVars mapHead 0 depth replacement
  | hfvar name => simp [instantiateBVarAt, mapPattern]
  | happly head arguments inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (Pattern.apply (mapHead head))
      apply List.map_congr_left
      intro argument membership
      simpa only [Function.comp_apply] using
        inductionHypothesis argument membership depth
  | hlambda name body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hmultiLambda arity names body inductionHypothesis =>
      simp [instantiateBVarAt, mapPattern, inductionHypothesis]
  | hsubst body nestedReplacement bodyIH replacementIH =>
      simp [instantiateBVarAt, mapPattern, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [instantiateBVarAt, mapPattern, mapPatternList_eq_map, List.map_map]
      apply congrArg (fun translatedElements =>
        Pattern.collection kind translatedElements rest)
      apply List.map_congr_left
      intro element membership
      simpa only [Function.comp_apply] using
        inductionHypothesis element membership depth

theorem mapPattern_instantiateBVar (mapHead : String → String)
    (replacement body : Pattern) :
    mapPattern mapHead (instantiateBVar replacement body) =
      instantiateBVar (mapPattern mapHead replacement) (mapPattern mapHead body) :=
  mapPattern_instantiateBVarAt mapHead 0 replacement body

theorem free_names_preserved (mapHead : String → String) (term : Pattern) :
    (mapPattern mapHead term).freeFvarNames = term.freeFvarNames := by
  induction term using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly head arguments inductionHypothesis =>
      simp only [mapPattern, Pattern.freeFvarNames]
      induction arguments with
      | nil => rfl
      | cons argument rest restIH =>
          simp only [mapPatternList, List.flatMap_cons]
          rw [inductionHypothesis argument (by simp)]
          apply congrArg₂ (· ++ ·) rfl
          apply restIH
          intro term membership
          exact inductionHypothesis term (by simp [membership])
  | hlambda name body inductionHypothesis =>
      simpa [mapPattern, Pattern.freeFvarNames] using inductionHypothesis
  | hmultiLambda arity names body inductionHypothesis =>
      simpa [mapPattern, Pattern.freeFvarNames] using inductionHypothesis
  | hsubst body replacement bodyIH replacementIH =>
      simp [mapPattern, Pattern.freeFvarNames, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [mapPattern, Pattern.freeFvarNames]
      apply congrArg₂ (· ++ ·) ?_ rfl
      induction elements with
      | nil => rfl
      | cons element tail tailIH =>
          simp only [mapPatternList, List.flatMap_cons]
          rw [inductionHypothesis element (by simp)]
          apply congrArg₂ (· ++ ·) rfl
          apply tailIH
          intro term membership
          exact inductionHypothesis term (by simp [membership])

theorem wellScoped_preserved (mapHead : String → String)
    (depth : Nat) (term : Pattern) :
    (mapPattern mapHead term).isWellScopedAt depth =
      term.isWellScopedAt depth := by
  induction term using Pattern.inductionOn generalizing depth with
  | hbvar => rfl
  | hfvar => rfl
  | happly head arguments inductionHypothesis =>
      simp only [mapPattern, Pattern.isWellScopedAt]
      induction arguments with
      | nil => rfl
      | cons argument rest restIH =>
          simp only [mapPatternList, Pattern.isWellScopedListAt]
          rw [inductionHypothesis argument (by simp) depth]
          rw [restIH]
          intro term membership anyDepth
          exact inductionHypothesis term (by simp [membership]) anyDepth
  | hlambda name body inductionHypothesis =>
      simpa [mapPattern, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + 1)
  | hmultiLambda arity names body inductionHypothesis =>
      simpa [mapPattern, Pattern.isWellScopedAt] using
        inductionHypothesis (depth + arity)
  | hsubst body replacement bodyIH replacementIH =>
      simp [mapPattern, Pattern.isWellScopedAt, bodyIH, replacementIH]
  | hcollection kind elements rest inductionHypothesis =>
      simp only [mapPattern, Pattern.isWellScopedAt]
      induction elements with
      | nil => rfl
      | cons element tail tailIH =>
          simp only [mapPatternList, Pattern.isWellScopedListAt]
          rw [inductionHypothesis element (by simp) depth]
          rw [tailIH]
          intro term membership anyDepth
          exact inductionHypothesis term (by simp [membership]) anyDepth

theorem closed_translation_remains_closed (mapHead : String → String)
    {term : Pattern} (closed : term.isWellScoped = true) :
    (mapPattern mapHead term).isWellScoped = true := by
  simpa [Pattern.isWellScoped, wellScoped_preserved] using closed

/-! ## Context-indexed open code and controls -/

/-- Open code whose free metavariable names are authorized by an explicit
context.  Bound variables remain governed by locally nameless scope. -/
def ContextualCode (context : List String) :=
  { term : Pattern //
    ∀ name ∈ term.freeFvarNames, name ∈ context }

/-- Constructor-only language change transports open code in the same
context; no weakening, renaming, or capture premise is needed. -/
def mapContextualCode (mapHead : String → String) {context : List String} :
    ContextualCode context → ContextualCode context
  | ⟨term, authorized⟩ => ⟨mapPattern mapHead term, by
      intro name membership
      rw [free_names_preserved] at membership
      exact authorized name membership⟩

@[simp] theorem mapContextualCode_term (mapHead : String → String)
    {context : List String} (code : ContextualCode context) :
    (mapContextualCode mapHead code).1 = mapPattern mapHead code.1 := rfl

/-- Positive canary: genuinely open code under a binder is representable in
the one-name context. -/
def openCodeCanary : ContextualCode ["external"] :=
  ⟨.lambda none
      (.apply "Source" [.bvar 0, .fvar "external"]), by
    intro name membership
    simpa [Pattern.freeFvarNames] using membership⟩

def renameSourceToTarget (head : String) : String :=
  if head = "Source" then "Target" else head

/-- Positive cross-language hygiene canary: the constructor changes while the
free name and bound index remain in place. -/
theorem open_code_translation_canary :
    (mapContextualCode renameSourceToTarget openCodeCanary).1 =
      .lambda none
        (.apply "Target" [.bvar 0, .fvar "external"]) := by
  rfl

/-- Negative control: hygiene does not mean that translation is the identity
on language constructors. -/
theorem constructor_translation_is_nontrivial :
    mapPattern renameSourceToTarget
        (.apply "Source" [.fvar "external"]) ≠
      .apply "Source" [.fvar "external"] := by
  decide

/-- The same nontrivial translation still commutes with contextual opening. -/
theorem nontrivial_translation_commutes_with_opening :
    mapPattern renameSourceToTarget
        (openBVar 0 (.fvar "external")
          (.apply "Source" [.bvar 0])) =
      openBVar 0 (mapPattern renameSourceToTarget (.fvar "external"))
        (mapPattern renameSourceToTarget
          (.apply "Source" [.bvar 0])) :=
  mapPattern_openBVar renameSourceToTarget 0 (.fvar "external")
    (.apply "Source" [.bvar 0])

end Mettapedia.Languages.MeTTa.Prime.DataTranslationKernel
