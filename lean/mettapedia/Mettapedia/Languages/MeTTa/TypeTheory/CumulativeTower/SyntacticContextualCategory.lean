import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature

/-!
# The declaration-aware syntactic contextual category

The generic Prime presentation already has raw telescopes, a proof-carrying
context-formation judgment, typed simultaneous substitutions, and exact
substitution/comprehension laws.  This module packages those existing objects
as one syntactic contextual category.  It does not introduce a second term
grammar or typing relation.

Only well-formed telescopes are objects.  An arrow `Delta ⟶ Gamma` is a
simultaneous substitution for the variables of `Gamma` by terms in `Delta`,
together with its `CtxMor` typing proof.  This contravariant orientation is the
one used by reindexing in categories with families.

The category and terminal-object laws hold before quotienting.  The later
semantic-CwF theorem must still choose the equality notion for types and
terms; nothing here prejudges that boundary.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace SyntacticContextual

open CategoryTheory

/-- A raw telescope together with its declaration-aware formation proof. -/
structure FormedContext (rules : Rules Head) where
  arity : Nat
  context : Ctx Head arity
  wellFormed : Declaration.ContextWellFormed rules context

/-- A context arrow is exactly an existing typed simultaneous substitution.
The raw substitution points from the target telescope into the source
telescope because syntax is reindexed contravariantly. -/
structure ContextHom {rules : Rules Head}
    (source target : FormedContext rules) where
  substitution : Sub Head target.arity source.arity
  typed : CtxMor rules target.context source.context substitution

@[ext] theorem ContextHom.ext {rules : Rules Head}
    {source target : FormedContext rules}
    {left right : ContextHom source target}
    (equalSubstitutions : left.substitution = right.substitution) :
    left = right := by
  cases left
  cases right
  cases equalSubstitutions
  rfl

/-- The declaration-aware contexts and typed substitutions form a category.
Composition reuses `CtxMor.comp`; no typing derivation is reconstructed. -/
instance formedContextCategory (rules : Rules Head) :
    Category (FormedContext rules) where
  Hom := ContextHom
  id context :=
    { substitution := ids
      typed := CtxMor.identity rules context.context }
  comp earlier later :=
    { substitution := subComp earlier.substitution later.substitution
      typed := CtxMor.comp later.typed earlier.typed }
  id_comp morphism := by
    apply ContextHom.ext
    exact subComp_ids_left morphism.substitution
  comp_id morphism := by
    apply ContextHom.ext
    exact subComp_ids_right morphism.substitution
  assoc first second third := by
    apply ContextHom.ext
    exact (subComp_assoc first.substitution second.substitution
      third.substitution).symm

/-! ## Functorial transport between presentations -/

/-- Map every component of a simultaneous substitution along a universe-head
map. -/
abbrev mapSubHeads (map : HeadOne → HeadTwo) (substitution : Sub HeadOne n m) :
    Sub HeadTwo n m :=
  fun index => (substitution index).mapHead map

@[simp] theorem mapSubHeads_ids (map : HeadOne → HeadTwo) :
    mapSubHeads map (ids (Head := HeadOne) (n := n)) = ids := by
  rfl

/-- Head mapping preserves substitution composition. -/
theorem mapSubHeads_subComp (map : HeadOne → HeadTwo)
    (earlier : Sub HeadOne m k) (later : Sub HeadOne n m) :
    mapSubHeads map (subComp earlier later) =
      subComp (mapSubHeads map earlier) (mapSubHeads map later) := by
  funext index
  exact Tm.mapHead_subst map earlier (later index)

/-- Transport one formed context along a constructor-preserving presentation
morphism. -/
def FormedContext.mapHead {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    (context : FormedContext sourceRules) : FormedContext targetRules where
  arity := context.arity
  context := context.context.mapHead map
  wellFormed := context.wellFormed.mapHead morphism

/-- Typed substitutions transport componentwise along a presentation
morphism. -/
def ContextHom.mapHead {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (presentationMorphism : sourceRules.Morphism targetRules map)
    {source target : FormedContext sourceRules}
    (contextMorphism : source ⟶ target) :
    source.mapHead presentationMorphism ⟶
      target.mapHead presentationMorphism where
  substitution := mapSubHeads map contextMorphism.substitution
  typed := by
    intro index
    dsimp only [FormedContext.mapHead, mapSubHeads]
    have transported :=
      (contextMorphism.typed index).mapHead presentationMorphism
    simpa only [Ctx.lookup_mapHead, Tm.mapHead_subst] using transported

/-- Every presentation morphism induces a functor on its declaration-aware
syntactic context category. -/
def rulesMorphismFunctor {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map) :
    FormedContext sourceRules ⥤ FormedContext targetRules where
  obj context := context.mapHead morphism
  map contextMorphism := contextMorphism.mapHead morphism
  map_id context := by
    apply ContextHom.ext
    exact mapSubHeads_ids map
  map_comp earlier later := by
    apply ContextHom.ext
    exact mapSubHeads_subComp map earlier.substitution later.substitution

/-- The empty telescope as a well-formed context object. -/
def emptyContext (rules : Rules Head) : FormedContext rules where
  arity := 0
  context := .nil
  wellFormed := .nil

/-- The unique raw substitution from any context into the empty telescope. -/
def toEmpty {rules : Rules Head} (source : FormedContext rules) :
    source ⟶ emptyContext rules where
  substitution := Fin.elim0
  typed := fun index => Fin.elim0 index

/-- There is exactly one context arrow into the empty telescope. -/
theorem toEmpty_unique {rules : Rules Head} (source : FormedContext rules)
    (morphism : source ⟶ emptyContext rules) :
    morphism = toEmpty source := by
  apply ContextHom.ext
  funext index
  exact Fin.elim0 index

/-- Constructive terminality of the empty telescope: every hom-set into it
has exactly one inhabitant.  This is the terminal universal property without
introducing a choice-based selected limit object. -/
@[reducible] def emptyTerminalUniversal (rules : Rules Head) :
    ∀ source : FormedContext rules, Unique (source ⟶ emptyContext rules) :=
  fun source =>
    { default := toEmpty source
      uniq := fun morphism => toEmpty_unique source morphism }

/-- Naturality of the terminal arrow. -/
@[simp] theorem comp_toEmpty {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    morphism ≫ toEmpty target = toEmpty source :=
  toEmpty_unique source _

/-! ## The reindexed family of well-formed types and terms -/

/-- A type over a formed context, including the universe in which its
formation was checked.  The level is retained because cumulativity may offer
more than one formation derivation for the same raw term. -/
structure TypeOver {rules : Rules Head} (context : FormedContext rules) where
  code : Tm Head context.arity
  level : Head
  isUniverse : rules.isUniverse level
  formed : HasType rules context.context code (.head level)

@[ext] theorem TypeOver.ext {rules : Rules Head}
    {context : FormedContext rules} {left right : TypeOver context}
    (equalCodes : left.code = right.code)
    (equalLevels : left.level = right.level) :
    left = right := by
  cases left
  cases right
  cases equalCodes
  cases equalLevels
  rfl

/-- Transport a formed type along a presentation morphism. -/
def TypeOver.mapHead {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {context : FormedContext sourceRules} (type : TypeOver context) :
    TypeOver (context.mapHead morphism) where
  code := type.code.mapHead map
  level := map type.level
  isUniverse := morphism.isUniverse type.isUniverse
  formed := type.formed.mapHead morphism

/-- Reindex a formed type along a typed context substitution. -/
def TypeOver.reindex {rules : Rules Head}
    {source target : FormedContext rules} (type : TypeOver target)
    (morphism : source ⟶ target) : TypeOver source where
  code := subst morphism.substitution type.code
  level := type.level
  isUniverse := type.isUniverse
  formed := by
    simpa only [Presentation.subst] using
      type.formed.substitute morphism.typed

@[simp] theorem TypeOver.reindex_id {rules : Rules Head}
    {context : FormedContext rules} (type : TypeOver context) :
    type.reindex (𝟙 context) = type := by
  apply TypeOver.ext
  · exact subst_ids type.code
  · rfl

@[simp] theorem TypeOver.reindex_comp {rules : Rules Head}
    {source middle target : FormedContext rules}
    (type : TypeOver target) (earlier : source ⟶ middle)
    (later : middle ⟶ target) :
    type.reindex (earlier ≫ later) =
      (type.reindex later).reindex earlier := by
  apply TypeOver.ext
  · exact (subst_subComp earlier.substitution later.substitution
      type.code).symm
  · rfl

/-- Changing a presentation commutes with reindexing a formed type. -/
theorem TypeOver.mapHead_reindex {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (presentationMorphism : sourceRules.Morphism targetRules map)
    {source target : FormedContext sourceRules} (type : TypeOver target)
    (contextMorphism : source ⟶ target) :
    (type.reindex contextMorphism).mapHead presentationMorphism =
      (type.mapHead presentationMorphism).reindex
        (contextMorphism.mapHead presentationMorphism) := by
  apply TypeOver.ext
  · exact Tm.mapHead_subst map contextMorphism.substitution type.code
  · rfl

/-- A term is raw syntax together with a derivation at one formed type. -/
structure Term {rules : Rules Head} (context : FormedContext rules)
    (type : TypeOver context) where
  code : Tm Head context.arity
  typed : HasType rules context.context code type.code

@[ext] theorem Term.ext {rules : Rules Head}
    {context : FormedContext rules} {type : TypeOver context}
    {left right : Term context type} (equalCodes : left.code = right.code) :
    left = right := by
  cases left
  cases right
  cases equalCodes
  rfl

/-- Transport a term across equality of its formed type. -/
def Term.cast {rules : Rules Head} {context : FormedContext rules}
    {source target : TypeOver context} (equalTypes : source = target)
    (term : Term context source) : Term context target :=
  equalTypes ▸ term

@[simp] theorem Term.cast_code {rules : Rules Head}
    {context : FormedContext rules} {source target : TypeOver context}
    (equalTypes : source = target) (term : Term context source) :
    (term.cast equalTypes).code = term.code := by
  cases equalTypes
  rfl

/-- Equality of dependent type indices plus equality of retained raw syntax
determines equality of proof-carrying terms. -/
theorem Term.heq_of_type_eq_of_code_eq {rules : Rules Head}
    {context : FormedContext rules} {source target : TypeOver context}
    (equalTypes : source = target) (left : Term context source)
    (right : Term context target) (equalCodes : left.code = right.code) :
    HEq left right := by
  cases equalTypes
  exact heq_of_eq (Term.ext equalCodes)

/-- Typed term substitution is inherited directly from `HasType.substitute`. -/
def Term.reindex {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    Term source (type.reindex morphism) where
  code := subst morphism.substitution term.code
  typed := term.typed.substitute morphism.typed

/-- Transport a typed term along a presentation morphism. -/
def Term.mapHead {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (morphism : sourceRules.Morphism targetRules map)
    {context : FormedContext sourceRules} {type : TypeOver context}
    (term : Term context type) :
    Term (context.mapHead morphism) (type.mapHead morphism) where
  code := term.code.mapHead map
  typed := term.typed.mapHead morphism

/-- Term reindexing by identity is the same dependent term. -/
theorem Term.reindex_id {rules : Rules Head}
    {context : FormedContext rules} {type : TypeOver context}
    (term : Term context type) :
    HEq (term.reindex (𝟙 context)) term := by
  exact Term.heq_of_type_eq_of_code_eq (TypeOver.reindex_id type)
    (term.reindex (𝟙 context)) term (subst_ids term.code)

/-- Term reindexing respects categorical composition. -/
theorem Term.reindex_comp {rules : Rules Head}
    {source middle target : FormedContext rules} {type : TypeOver target}
    (term : Term target type) (earlier : source ⟶ middle)
    (later : middle ⟶ target) :
    HEq (term.reindex (earlier ≫ later))
      ((term.reindex later).reindex earlier) := by
  exact Term.heq_of_type_eq_of_code_eq
    (TypeOver.reindex_comp type earlier later)
    (term.reindex (earlier ≫ later))
    ((term.reindex later).reindex earlier)
    ((subst_subComp earlier.substitution later.substitution term.code).symm)

/-- Changing a presentation commutes with reindexing a typed term. -/
theorem Term.mapHead_reindex {sourceRules : Rules HeadOne}
    {targetRules : Rules HeadTwo} {map : HeadOne → HeadTwo}
    (presentationMorphism : sourceRules.Morphism targetRules map)
    {source target : FormedContext sourceRules} {type : TypeOver target}
    (term : Term target type) (contextMorphism : source ⟶ target) :
    HEq ((term.reindex contextMorphism).mapHead presentationMorphism)
      ((term.mapHead presentationMorphism).reindex
        (contextMorphism.mapHead presentationMorphism)) := by
  exact Term.heq_of_type_eq_of_code_eq
    (TypeOver.mapHead_reindex presentationMorphism type contextMorphism)
    ((term.reindex contextMorphism).mapHead presentationMorphism)
    ((term.mapHead presentationMorphism).reindex
      (contextMorphism.mapHead presentationMorphism))
    (Tm.mapHead_subst map contextMorphism.substitution term.code)

/-! ## Context comprehension -/

/-- Extend a formed telescope by a formed type. -/
def extendContext {rules : Rules Head} (context : FormedContext rules)
    (type : TypeOver context) : FormedContext rules where
  arity := context.arity + 1
  context := .snoc context.context type.code
  wellFormed := .snoc context.wellFormed type.formed type.isUniverse

/-- The de Bruijn index introduced by context comprehension. -/
def newestIndex {rules : Rules Head} (context : FormedContext rules)
    (type : TypeOver context) : Fin (extendContext context type).arity :=
  ⟨0, Nat.zero_lt_succ context.arity⟩

/-- The weakening projection from a context extension. -/
def projectionHom {rules : Rules Head} (context : FormedContext rules)
    (type : TypeOver context) : extendContext context type ⟶ context where
  substitution := projection
  typed := CtxMor.projectionTyped rules context.context type.code

/-- The newest variable in a context extension. -/
def newestVariable {rules : Rules Head} (context : FormedContext rules)
    (type : TypeOver context) :
    Term (extendContext context type) (type.reindex (projectionHom context type))
    where
  code := .var (newestIndex context type)
  typed := by
    change HasType rules (.snoc context.context type.code) (.var 0)
      (subst projection type.code)
    rw [subst_projection]
    exact HasType.var 0

/-- Pair a context substitution with a term in its reindexed fibre. -/
def extendHom {rules : Rules Head} {source target : FormedContext rules}
    {type : TypeOver target} (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) :
    source ⟶ extendContext target type where
  substitution := consSub term.code morphism.substitution
  typed := CtxMor.extend morphism.typed term.typed

/-- First comprehension beta law: projecting a paired substitution recovers
its base substitution. -/
@[simp] theorem extendHom_projection {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) :
    extendHom morphism term ≫ projectionHom target type = morphism := by
  apply ContextHom.ext
  exact subComp_consSub_projection term.code morphism.substitution

/-- The type of the newest variable after a paired substitution is exactly
the type of the paired term. -/
theorem newestVariable_extendHom_type {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) :
    (type.reindex (projectionHom target type)).reindex
        (extendHom morphism term) =
      type.reindex morphism := by
  rw [← TypeOver.reindex_comp]
  simp

/-- Second comprehension beta law: substituting a paired environment into
the newest variable recovers the paired term. -/
@[simp] theorem newestVariable_extendHom {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) :
    Term.cast (newestVariable_extendHom_type morphism term)
        ((newestVariable target type).reindex (extendHom morphism term)) =
      term := by
  apply Term.ext
  rw [Term.cast_code]
  rfl

/-- Reindex the newest variable of an arbitrary comprehension arrow into the
fibre expected over its projected base. -/
def pulledNewest {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ extendContext target type) :
    Term source (type.reindex (morphism ≫ projectionHom target type)) :=
  Term.cast
    (TypeOver.reindex_comp type morphism (projectionHom target type)).symm
    ((newestVariable target type).reindex morphism)

/-- Context-comprehension eta: every arrow into an extension is recovered by
its projection and newest component. -/
theorem extendHom_eta {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ extendContext target type) :
    extendHom (morphism ≫ projectionHom target type)
        (pulledNewest morphism) = morphism := by
  apply ContextHom.ext
  have newestCode :
      (pulledNewest morphism).code =
        morphism.substitution (newestIndex target type) := by
    rw [pulledNewest, Term.cast_code]
    rfl
  have projected :
      subComp morphism.substitution projection =
        (fun index => morphism.substitution index.succ) := by
    funext index
    rfl
  change consSub (pulledNewest morphism).code
      (subComp morphism.substitution projection) = morphism.substitution
  rw [newestCode, projected]
  exact consSub_eta morphism.substitution

/-- Pairing retains the selected term component: two terms with distinct raw
codes induce distinct arrows over the same base substitution. -/
theorem extendHom_ne_of_term_code_ne {rules : Rules Head}
    {source target : FormedContext rules} {type : TypeOver target}
    (morphism : source ⟶ target)
    {left right : Term source (type.reindex morphism)}
    (different : left.code ≠ right.code) :
    extendHom morphism left ≠ extendHom morphism right := by
  intro equalArrows
  have equalSubstitutions := congrArg ContextHom.substitution equalArrows
  have equalNewest := congrFun equalSubstitutions (0 : Fin (target.arity + 1))
  exact different equalNewest

/-! ## Concrete nondegenerate Tower witnesses -/

namespace TowerExamples

/-- The formed empty context for the cumulative Tower presentation. -/
abbrev empty : FormedContext Tower.rules := emptyContext Tower.rules

/-- `U₁` as a formed type over the empty context. -/
def universeOne : TypeOver empty where
  code := sortTm (.succ Tower.zero)
  level := .sort (.succ (.succ Tower.zero))
  isUniverse := .sort (.succ (.succ Tower.zero))
  formed := .headType (.sort (.succ Tower.zero))

/-- `U₀` is one term of `U₁`. -/
def universeZero : Term empty universeOne where
  code := sortTm Tower.zero
  typed := .headType (.sort Tower.zero)

/-- The opaque legacy ground type is another term of `U₁`, obtained by
its native `U₀` formation followed by cumulative lifting. -/
def legacyGround : Term empty universeOne where
  code := .head .legacyGround
  typed := .cumul (.headType .legacyGround) (by
    intro _valuation
    exact Nat.zero_le _)

/-- Turn a closed term of `U₁` into a section of its comprehension. -/
def sectionHom (term : Term empty universeOne) :
    empty ⟶ extendContext empty universeOne :=
  extendHom (𝟙 empty)
    (Term.cast (TypeOver.reindex_id universeOne).symm term)

/-- Negative control: the syntactic contextual category retains which term a
section selected; cumulativity does not collapse `U₀` and the legacy ground
head into one arrow. -/
theorem universeZero_section_ne_legacyGround_section :
    sectionHom universeZero ≠ sectionHom legacyGround := by
  apply extendHom_ne_of_term_code_ne
  intro equalCodes
  have equalHeads :
      Tower.Head.sort Tower.zero = Tower.Head.legacyGround :=
    Tm.head.inj equalCodes
  cases equalHeads

end TowerExamples

/-! ## Positive and negative boundary witnesses -/

/-- Positive: the categorical identity is the pre-existing identity
substitution, including its typing evidence. -/
@[simp] theorem identity_substitution {rules : Rules Head}
    (context : FormedContext rules) :
    (CategoryStruct.id context : ContextHom context context).substitution =
      ids :=
  rfl

/-- Negative: the terminal arrow cannot secretly contain a term.  Its raw
environment has empty domain, independently of the source telescope. -/
theorem toEmpty_has_no_component {rules : Rules Head}
    (_source : FormedContext rules) :
    IsEmpty (Fin (emptyContext rules).arity) := by
  exact ⟨Fin.elim0⟩

/-! ## Axiom audit -/

#print axioms formedContextCategory
#print axioms ContextHom.mapHead
#print axioms rulesMorphismFunctor
#print axioms emptyTerminalUniversal
#print axioms comp_toEmpty
#print axioms toEmpty_unique
#print axioms TypeOver.reindex_comp
#print axioms TypeOver.mapHead_reindex
#print axioms Term.cast
#print axioms Term.cast_code
#print axioms Term.reindex
#print axioms Term.reindex_comp
#print axioms Term.mapHead_reindex
#print axioms extendHom_projection
#print axioms projectionHom
#print axioms newestIndex
#print axioms newestVariable
#print axioms extendHom
#print axioms newestVariable_extendHom_type
#print axioms newestVariable_extendHom
#print axioms pulledNewest
#print axioms extendHom_eta
#print axioms extendHom_ne_of_term_code_ne
#print axioms TowerExamples.universeOne
#print axioms TowerExamples.universeZero
#print axioms TowerExamples.legacyGround
#print axioms TowerExamples.sectionHom
#print axioms TowerExamples.universeZero_section_ne_legacyGround_section

end SyntacticContextual
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
