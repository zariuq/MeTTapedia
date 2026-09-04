import Mettapedia.GSLT.LanguageDef.StructuralCoproduct
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# The extensional category of validated language definitions

`LanguageDefSymbolMap` is intentionally total on strings, while a language
uses only finitely many declared symbols.  Raw equality of total symbol
functions therefore observes irrelevant values and prevents ordinary tagged
unions from satisfying categorical uniqueness.  This module quotients
structural morphisms by equality of their action on every declaration of the
source `LanguageDef`.  Composition respects that equality because structural
morphisms carry declared symbols to declared symbols.

This is a category of validated declaration data.  A colimit proved here is
therefore a colimit for declaration-preserving maps; it does not by itself say
that an operational or model-theoretic semantics preserves that colimit.  Such
a semantic claim requires a separately defined interpretation functor and a
preservation theorem.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

/-- Two structural maps are operationally indistinguishable when they map
every declaration of the source to the same target declaration. -/
structure Equivalent {source target : ValidatedLanguageDef}
    (first second : StructuralMorphism source target) : Prop where
  types : ∀ (declaration : TypeDecl),
    List.Mem declaration source.language.types →
    mapTypeDecl first.symbols declaration =
      mapTypeDecl second.symbols declaration
  terms : ∀ declaration, List.Mem declaration source.language.terms →
    mapGrammarRule first.symbols declaration =
      mapGrammarRule second.symbols declaration
  equations : ∀ declaration,
    List.Mem declaration source.language.equations →
    mapEquation first.symbols declaration =
      mapEquation second.symbols declaration
  rewrites : ∀ declaration,
    List.Mem declaration source.language.rewrites →
    mapRewriteRule first.symbols declaration =
      mapRewriteRule second.symbols declaration

namespace Equivalent

theorem refl {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    Equivalent morphism morphism where
  types := by intros; rfl
  terms := by intros; rfl
  equations := by intros; rfl
  rewrites := by intros; rfl

theorem symm {source target : ValidatedLanguageDef}
    {first second : StructuralMorphism source target}
    (equivalent : Equivalent first second) : Equivalent second first where
  types declaration membership := (equivalent.types declaration membership).symm
  terms declaration membership := (equivalent.terms declaration membership).symm
  equations declaration membership :=
    (equivalent.equations declaration membership).symm
  rewrites declaration membership :=
    (equivalent.rewrites declaration membership).symm

theorem trans {source target : ValidatedLanguageDef}
    {first second third : StructuralMorphism source target}
    (left : Equivalent first second) (right : Equivalent second third) :
    Equivalent first third where
  types declaration membership :=
    (left.types declaration membership).trans
      (right.types declaration membership)
  terms declaration membership :=
    (left.terms declaration membership).trans
      (right.terms declaration membership)
  equations declaration membership :=
    (left.equations declaration membership).trans
      (right.equations declaration membership)
  rewrites declaration membership :=
    (left.rewrites declaration membership).trans
      (right.rewrites declaration membership)

theorem comp {first second third : ValidatedLanguageDef}
    {left left' : StructuralMorphism first second}
    {right right' : StructuralMorphism second third}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    Equivalent (StructuralMorphism.comp left right)
      (StructuralMorphism.comp left' right') where
  types declaration membership := by
    calc
      mapTypeDecl (StructuralMorphism.comp left right).symbols declaration =
          mapTypeDecl right.symbols (mapTypeDecl left.symbols declaration) :=
        mapTypeDecl_comp left.symbols right.symbols declaration
      _ = mapTypeDecl right.symbols (mapTypeDecl left'.symbols declaration) :=
        congrArg (mapTypeDecl right.symbols)
          (leftEquivalent.types declaration membership)
      _ = mapTypeDecl right'.symbols (mapTypeDecl left'.symbols declaration) :=
        rightEquivalent.types _ (left'.mapsTypes declaration membership)
      _ = mapTypeDecl (StructuralMorphism.comp left' right').symbols declaration :=
        (mapTypeDecl_comp left'.symbols right'.symbols declaration).symm
  terms declaration membership := by
    calc
      mapGrammarRule (StructuralMorphism.comp left right).symbols declaration =
          mapGrammarRule right.symbols (mapGrammarRule left.symbols declaration) :=
        mapGrammarRule_comp left.symbols right.symbols declaration
      _ = mapGrammarRule right.symbols
          (mapGrammarRule left'.symbols declaration) :=
        congrArg (mapGrammarRule right.symbols)
          (leftEquivalent.terms declaration membership)
      _ = mapGrammarRule right'.symbols
          (mapGrammarRule left'.symbols declaration) :=
        rightEquivalent.terms _ (left'.mapsTerms declaration membership)
      _ = mapGrammarRule (StructuralMorphism.comp left' right').symbols declaration :=
        (mapGrammarRule_comp left'.symbols right'.symbols declaration).symm
  equations declaration membership := by
    calc
      mapEquation (StructuralMorphism.comp left right).symbols declaration =
          mapEquation right.symbols (mapEquation left.symbols declaration) :=
        mapEquation_comp left.symbols right.symbols declaration
      _ = mapEquation right.symbols (mapEquation left'.symbols declaration) :=
        congrArg (mapEquation right.symbols)
          (leftEquivalent.equations declaration membership)
      _ = mapEquation right'.symbols (mapEquation left'.symbols declaration) :=
        rightEquivalent.equations _
          (left'.mapsEquations declaration membership)
      _ = mapEquation (StructuralMorphism.comp left' right').symbols declaration :=
        (mapEquation_comp left'.symbols right'.symbols declaration).symm
  rewrites declaration membership := by
    calc
      mapRewriteRule (StructuralMorphism.comp left right).symbols declaration =
          mapRewriteRule right.symbols
            (mapRewriteRule left.symbols declaration) :=
        mapRewriteRule_comp left.symbols right.symbols declaration
      _ = mapRewriteRule right.symbols
          (mapRewriteRule left'.symbols declaration) :=
        congrArg (mapRewriteRule right.symbols)
          (leftEquivalent.rewrites declaration membership)
      _ = mapRewriteRule right'.symbols
          (mapRewriteRule left'.symbols declaration) :=
        rightEquivalent.rewrites _
          (left'.mapsRewrites declaration membership)
      _ = mapRewriteRule (StructuralMorphism.comp left' right').symbols declaration :=
        (mapRewriteRule_comp left'.symbols right'.symbols declaration).symm

end Equivalent

instance structuralMorphismSetoid (source target : ValidatedLanguageDef) :
    Setoid (StructuralMorphism source target) where
  r := Equivalent
  iseqv := ⟨Equivalent.refl, Equivalent.symm, Equivalent.trans⟩

/-- Structural maps modulo equality on the exact source `LanguageDef`. -/
abbrev Arrow (source target : ValidatedLanguageDef) :=
  Quotient (structuralMorphismSetoid source target)

namespace Arrow

def ofMorphism {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) : Arrow source target :=
  Quotient.mk _ morphism

def id (language : ValidatedLanguageDef) : Arrow language language :=
  ofMorphism (StructuralMorphism.id language)

def comp {first second third : ValidatedLanguageDef}
    (left : Arrow first second) (right : Arrow second third) :
    Arrow first third :=
  Quotient.map₂ StructuralMorphism.comp
    (fun {_ _} leftEquivalent {_ _} rightEquivalent =>
      Equivalent.comp leftEquivalent rightEquivalent)
    left right

private theorem raw_id_comp {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    StructuralMorphism.comp (StructuralMorphism.id source) morphism =
      morphism := by
  apply StructuralMorphism.ext
  rfl

private theorem raw_comp_id {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    StructuralMorphism.comp morphism (StructuralMorphism.id target) =
      morphism := by
  apply StructuralMorphism.ext
  rfl

private theorem raw_assoc {first second third fourth : ValidatedLanguageDef}
    (one : StructuralMorphism first second)
    (two : StructuralMorphism second third)
    (three : StructuralMorphism third fourth) :
    StructuralMorphism.comp (StructuralMorphism.comp one two) three =
      StructuralMorphism.comp one (StructuralMorphism.comp two three) := by
  apply StructuralMorphism.ext
  rfl

end Arrow

/-- Validated language definitions and extensional structural arrows form the
category in which disjoint sums have their intended universal property. -/
instance : Category ValidatedLanguageDef where
  Hom := Arrow
  id := Arrow.id
  comp := Arrow.comp
  id_comp morphism := by
    induction morphism using Quotient.inductionOn with
    | _ representative =>
        change Arrow.ofMorphism
            (StructuralMorphism.comp (StructuralMorphism.id _) representative) =
          Arrow.ofMorphism representative
        exact congrArg Arrow.ofMorphism (Arrow.raw_id_comp representative)
  comp_id morphism := by
    induction morphism using Quotient.inductionOn with
    | _ representative =>
        change Arrow.ofMorphism
            (StructuralMorphism.comp representative (StructuralMorphism.id _)) =
          Arrow.ofMorphism representative
        exact congrArg Arrow.ofMorphism (Arrow.raw_comp_id representative)
  assoc one two three := by
    induction one using Quotient.inductionOn with
    | _ oneRepresentative =>
      induction two using Quotient.inductionOn with
      | _ twoRepresentative =>
        induction three using Quotient.inductionOn with
        | _ threeRepresentative =>
          change Arrow.ofMorphism
              (StructuralMorphism.comp
                (StructuralMorphism.comp oneRepresentative twoRepresentative)
                threeRepresentative) =
            Arrow.ofMorphism
              (StructuralMorphism.comp oneRepresentative
                (StructuralMorphism.comp twoRepresentative threeRepresentative))
          exact congrArg Arrow.ofMorphism
            (Arrow.raw_assoc oneRepresentative twoRepresentative
              threeRepresentative)

namespace Coproduct

open Mettapedia.GSLT.LanguageDef.StructuralCoproduct

/-- Copair two functions across disjoint, injective images.  Values outside
the two images are observationally irrelevant to the source LanguageDef. -/
noncomputable def copairFunction
    (left right leftTarget rightTarget : String → String)
    (value : String) : String := by
  classical
  exact
    if leftWitness : ∃ source, left source = value then
      leftTarget (Classical.choose leftWitness)
    else if rightWitness : ∃ source, right source = value then
      rightTarget (Classical.choose rightWitness)
    else value

theorem copairFunction_left
    {left right leftTarget rightTarget : String → String}
    (leftInjective : Function.Injective left) (source : String) :
    copairFunction left right leftTarget rightTarget (left source) =
      leftTarget source := by
  classical
  unfold copairFunction
  split
  next witness =>
    have chosen : Classical.choose witness = source :=
      leftInjective (Classical.choose_spec witness)
    rw [chosen]
  next absent => exact (absent ⟨source, rfl⟩).elim

theorem copairFunction_right
    {left right leftTarget rightTarget : String → String}
    (rightInjective : Function.Injective right)
    (imagesDisjoint : ∀ leftSource rightSource,
      left leftSource ≠ right rightSource)
    (source : String) :
    copairFunction left right leftTarget rightTarget (right source) =
      rightTarget source := by
  classical
  unfold copairFunction
  split
  next leftWitness =>
    exact (imagesDisjoint (Classical.choose leftWitness) source
      (Classical.choose_spec leftWitness)).elim
  next _ =>
    split
    next rightWitness =>
      have chosen : Classical.choose rightWitness = source :=
        rightInjective (Classical.choose_spec rightWitness)
      rw [chosen]
    next absent => exact (absent ⟨source, rfl⟩).elim

/-- The unique declaration-observable symbol action induced by maps from the
two components. -/
noncomputable def copairSymbols
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (_compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) : LanguageDefSymbolMap where
  sort := copairFunction leftSymbols.sort rightSymbols.sort
    leftMap.symbols.sort rightMap.symbols.sort
  constructor := copairFunction leftSymbols.constructor rightSymbols.constructor
    leftMap.symbols.constructor rightMap.symbols.constructor
  relation := copairFunction leftSymbols.relation rightSymbols.relation
    leftMap.symbols.relation rightMap.symbols.relation
  equation := copairFunction leftSymbols.equation rightSymbols.equation
    leftMap.symbols.equation rightMap.symbols.equation
  rewrite := copairFunction leftSymbols.rewrite rightSymbols.rewrite
    leftMap.symbols.rewrite rightMap.symbols.rewrite

theorem leftSymbols_comp_copairSymbols
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) :
    LanguageDefSymbolMap.comp leftSymbols
      (copairSymbols compatible leftMap rightMap) = leftMap.symbols := by
  apply LanguageDefSymbolMap.ext
  · funext value
    exact copairFunction_left compatible.leftSymbolsInjective.sort value
  · funext value
    exact copairFunction_left compatible.leftSymbolsInjective.constructor value
  · funext value
    exact copairFunction_left compatible.leftSymbolsInjective.relation value
  · funext value
    exact copairFunction_left compatible.leftSymbolsInjective.equation value
  · funext value
    exact copairFunction_left compatible.leftSymbolsInjective.rewrite value

theorem rightSymbols_comp_copairSymbols
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) :
    LanguageDefSymbolMap.comp rightSymbols
      (copairSymbols compatible leftMap rightMap) = rightMap.symbols := by
  apply LanguageDefSymbolMap.ext
  · funext value
    exact copairFunction_right compatible.rightSymbolsInjective.sort
      compatible.symbolImagesDisjoint.sort value
  · funext value
    exact copairFunction_right compatible.rightSymbolsInjective.constructor
      compatible.symbolImagesDisjoint.constructor value
  · funext value
    exact copairFunction_right compatible.rightSymbolsInjective.relation
      compatible.symbolImagesDisjoint.relation value
  · funext value
    exact copairFunction_right compatible.rightSymbolsInjective.equation
      compatible.symbolImagesDisjoint.equation value
  · funext value
    exact copairFunction_right compatible.rightSymbolsInjective.rewrite
      compatible.symbolImagesDisjoint.rewrite value

/-- Raw mediating structural morphism.  The quotient category below removes
its arbitrary action on strings absent from the coproduct LanguageDef. -/
noncomputable def copairMorphism
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) :
    StructuralMorphism compatible.combinedLanguage target where
  symbols := copairSymbols compatible leftMap rightMap
  mapsTypes declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      rw [← mapTypeDecl_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact leftMap.mapsTypes source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      rw [← mapTypeDecl_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact rightMap.mapsTypes source sourceMember
  mapsTerms declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      rw [← mapGrammarRule_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact leftMap.mapsTerms source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      rw [← mapGrammarRule_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact rightMap.mapsTerms source sourceMember
  mapsEquations declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      rw [← mapEquation_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact leftMap.mapsEquations source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      rw [← mapEquation_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact rightMap.mapsEquations source sourceMember
  mapsRewrites declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      rw [← mapRewriteRule_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact leftMap.mapsRewrites source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      rw [← mapRewriteRule_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap]
      exact rightMap.mapsRewrites source sourceMember

theorem leftInclusion_comp_copairMorphism
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) :
    StructuralMorphism.comp compatible.leftInclusion
      (copairMorphism compatible leftMap rightMap) = leftMap := by
  apply StructuralMorphism.ext
  exact leftSymbols_comp_copairSymbols compatible leftMap rightMap

theorem rightInclusion_comp_copairMorphism
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : StructuralMorphism left target)
    (rightMap : StructuralMorphism right target) :
    StructuralMorphism.comp compatible.rightInclusion
      (copairMorphism compatible leftMap rightMap) = rightMap := by
  apply StructuralMorphism.ext
  exact rightSymbols_comp_copairSymbols compatible leftMap rightMap

theorem copairMorphism_equivalent
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {leftMap leftMap' : StructuralMorphism left target}
    {rightMap rightMap' : StructuralMorphism right target}
    (leftEquivalent : Equivalent leftMap leftMap')
    (rightEquivalent : Equivalent rightMap rightMap') :
    Equivalent (copairMorphism compatible leftMap rightMap)
      (copairMorphism compatible leftMap' rightMap') where
  types declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [copairMorphism, ← mapTypeDecl_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap,
        leftSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        leftEquivalent.types source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [copairMorphism, ← mapTypeDecl_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap,
        rightSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        rightEquivalent.types source sourceMember
  terms declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [copairMorphism, ← mapGrammarRule_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap,
        leftSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        leftEquivalent.terms source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [copairMorphism, ← mapGrammarRule_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap,
        rightSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        rightEquivalent.terms source sourceMember
  equations declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [copairMorphism, ← mapEquation_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap,
        leftSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        leftEquivalent.equations source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [copairMorphism, ← mapEquation_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap,
        rightSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        rightEquivalent.equations source sourceMember
  rewrites declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [copairMorphism, ← mapRewriteRule_comp,
        leftSymbols_comp_copairSymbols compatible leftMap rightMap,
        leftSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        leftEquivalent.rewrites source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [copairMorphism, ← mapRewriteRule_comp,
        rightSymbols_comp_copairSymbols compatible leftMap rightMap,
        rightSymbols_comp_copairSymbols compatible leftMap' rightMap'] using
        rightEquivalent.rewrites source sourceMember

theorem equivalent_of_component_equivalent
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {first second : StructuralMorphism compatible.combinedLanguage target}
    (leftEquivalent : Equivalent
      (StructuralMorphism.comp compatible.leftInclusion first)
      (StructuralMorphism.comp compatible.leftInclusion second))
    (rightEquivalent : Equivalent
      (StructuralMorphism.comp compatible.rightInclusion first)
      (StructuralMorphism.comp compatible.rightInclusion second)) :
    Equivalent first second where
  types declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [StructuralMorphism.comp, Compatibility.leftInclusion,
        mapTypeDecl_comp] using
        leftEquivalent.types source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [StructuralMorphism.comp, Compatibility.rightInclusion,
        mapTypeDecl_comp] using
        rightEquivalent.types source sourceMember
  terms declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [StructuralMorphism.comp, Compatibility.leftInclusion,
        mapGrammarRule_comp] using
        leftEquivalent.terms source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [StructuralMorphism.comp, Compatibility.rightInclusion,
        mapGrammarRule_comp] using
        rightEquivalent.terms source sourceMember
  equations declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [StructuralMorphism.comp, Compatibility.leftInclusion,
        mapEquation_comp] using
        leftEquivalent.equations source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [StructuralMorphism.comp, Compatibility.rightInclusion,
        mapEquation_comp] using
        rightEquivalent.equations source sourceMember
  rewrites declaration membership := by
    rcases List.mem_append.mp membership with leftMember | rightMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp leftMember
      simpa only [StructuralMorphism.comp, Compatibility.leftInclusion,
        mapRewriteRule_comp] using
        leftEquivalent.rewrites source sourceMember
    · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp rightMember
      simpa only [StructuralMorphism.comp, Compatibility.rightInclusion,
        mapRewriteRule_comp] using
        rightEquivalent.rewrites source sourceMember

/-- Categorical injection of the left LanguageDef. -/
def leftArrow
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    left ⟶ compatible.combinedLanguage :=
  Arrow.ofMorphism compatible.leftInclusion

/-- Categorical injection of the right LanguageDef. -/
def rightArrow
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    right ⟶ compatible.combinedLanguage :=
  Arrow.ofMorphism compatible.rightInclusion

/-- Categorical copairing of two declaration-observable structural maps. -/
noncomputable def copair
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : left ⟶ target) (rightMap : right ⟶ target) :
    compatible.combinedLanguage ⟶ target :=
  Quotient.map₂ (copairMorphism compatible)
    (fun {_ _} leftEquivalent {_ _} rightEquivalent =>
      copairMorphism_equivalent compatible leftEquivalent rightEquivalent)
    leftMap rightMap

theorem leftArrow_comp_copair
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : left ⟶ target) (rightMap : right ⟶ target) :
    leftArrow compatible ≫ copair compatible leftMap rightMap = leftMap := by
  induction leftMap using Quotient.inductionOn with
  | _ leftRepresentative =>
    induction rightMap using Quotient.inductionOn with
    | _ rightRepresentative =>
      exact congrArg Arrow.ofMorphism
        (leftInclusion_comp_copairMorphism compatible
          leftRepresentative rightRepresentative)

theorem rightArrow_comp_copair
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    (leftMap : left ⟶ target) (rightMap : right ⟶ target) :
    rightArrow compatible ≫ copair compatible leftMap rightMap = rightMap := by
  induction leftMap using Quotient.inductionOn with
  | _ leftRepresentative =>
    induction rightMap using Quotient.inductionOn with
    | _ rightRepresentative =>
      exact congrArg Arrow.ofMorphism
        (rightInclusion_comp_copairMorphism compatible
          leftRepresentative rightRepresentative)

theorem hom_ext
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right target : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right)
    {first second : compatible.combinedLanguage ⟶ target}
    (leftEquality : leftArrow compatible ≫ first =
      leftArrow compatible ≫ second)
    (rightEquality : rightArrow compatible ≫ first =
      rightArrow compatible ≫ second) : first = second := by
  induction first using Quotient.inductionOn with
  | _ firstRepresentative =>
    induction second using Quotient.inductionOn with
    | _ secondRepresentative =>
      apply Quotient.sound
      apply equivalent_of_component_equivalent compatible
      · exact Quotient.exact leftEquality
      · exact Quotient.exact rightEquality

/-- The binary cofan determined by a compatible structural sum. -/
def cofan
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    Limits.BinaryCofan left right :=
  Limits.BinaryCofan.mk (leftArrow compatible) (rightArrow compatible)

/-- A compatible structural sum is a genuine categorical coproduct in the
declaration-observational category of validated language definitions. -/
noncomputable def isColimit
    {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
    {left right : ValidatedLanguageDef}
    (compatible : Compatibility name leftSymbols rightSymbols left right) :
    Limits.IsColimit (cofan compatible) :=
  Limits.BinaryCofan.IsColimit.mk (cofan compatible)
    (fun leftMap rightMap => copair compatible leftMap rightMap)
    (fun leftMap rightMap => leftArrow_comp_copair compatible leftMap rightMap)
    (fun leftMap rightMap => rightArrow_comp_copair compatible leftMap rightMap)
    (fun leftMap rightMap _morphism leftEquality rightEquality =>
      hom_ext compatible
        (leftEquality.trans
          (leftArrow_comp_copair compatible leftMap rightMap).symm)
        (rightEquality.trans
          (rightArrow_comp_copair compatible leftMap rightMap).symm))

end Coproduct

#print axioms Equivalent.comp
#print axioms Coproduct.isColimit

end Mettapedia.GSLT.LanguageDef.StructuralLanguageDefCategory
