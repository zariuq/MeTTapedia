import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.GSLT.LanguageDef.MappedPresentationMorphism

/-!
# Complete collection metadata and equation transport

Adding an equation and renaming a constant both preserve the static
equivalence. Renaming a unit also preserves it when the declaration's unit
reference is renamed with the constructor. A stale reference passes the
ordinary declaration validator but supplies no usable collection algebra.
Its terms are not the complete structural image of the source.

The positive unit renaming transports actual typed terms and their unit law.
The negative incomplete image distinguishes a bag from a constant under all
contextual equations and admits no structural map with that symbol action.
Constructor injectivity alone cannot repair incomplete metadata.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls.EquationTransport

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.EquationSimulation
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## A law is added -/

/-- The contact theory with associativity. -/
def associative : ValidatedLanguageDef :=
  ⟨contactWith [assocLaw], contactWith_validate_eq_nil [assocLaw] (by decide) (by
    intro law membership
    obtain rfl : law = assocLaw := List.mem_singleton.mp membership
    simp [knownLaws])⟩

/-- The contact theory with associativity and commutativity. -/
def associativeCommutative : ValidatedLanguageDef :=
  ⟨contactWith [assocLaw, commLaw],
    contactWith_validate_eq_nil [assocLaw, commLaw] (by decide) (by
      intro law membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl <;> simp [knownLaws])⟩

/-- The inclusion that adds commutativity. -/
def addCommutativity : StructuralMorphism associative associativeCommutative where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration membership
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms := by
    intro rule membership
    rw [mapGrammarRule_id]
    exact membership
  mapsEquations := by
    intro equation membership
    rw [mapEquation_id]
    have listed : equation ∈ [assocLaw] := membership
    obtain rfl : equation = assocLaw := List.mem_singleton.mp listed
    exact List.Mem.head _
  mapsRewrites := by
    intro rewrite membership
    rw [mapRewriteRule_id]
    exact membership

/-- The contact theories declare no collection algebra, so there is no unit
to fix. -/
theorem addCommutativity_fixesUnits :
    FixesDeclaredUnits addCommutativity.symbols associative.language :=
  fixesDeclaredUnits_of_constructor_id _ _ fun _ => rfl

/-- **Adding a law preserves the static equivalence**, between two
presentations with authored equations. -/
theorem addCommutativity_preservesEquations : PreservesEquations base addCommutativity :=
  preservesEquations_default addCommutativity rfl addCommutativity_fixesUnits

/-- Adding a law preserves reduction at every interface. -/
theorem addCommutativity_preservesSteps : PreservesSteps base addCommutativity :=
  preservesSteps_default addCommutativity rfl addCommutativity_fixesUnits

/-! ## A bag with a declared unit -/

/-- Exchange two constructor labels and fix every other name. -/
def swapConstructors (first second : String) : LanguageDefSymbolMap where
  sort := id
  constructor := fun label =>
    if label = first then second else if label = second then first else label
  relation := id
  equation := id
  rewrite := id

/-- Exchanging two labels twice changes nothing. -/
theorem swapConstructors_involutive (first second : String) (label : String) :
    (swapConstructors first second).constructor
      ((swapConstructors first second).constructor label) = label := by
  simp only [swapConstructors]
  split_ifs <;> simp_all

/-- Exchanging two labels is injective. -/
theorem swapConstructors_injective (first second : String) :
    Function.Injective (swapConstructors first second).constructor :=
  Function.LeftInverse.injective (swapConstructors_involutive first second)

/-- The bag constructor.  Its algebra flattens nested bags and declares the
constructor labelled `Z` as its unit. -/
def bagRule : GrammarRule :=
  { label := "Par", category := "P",
    params := [.simple "ps" (.collection .hashBag (.base "P"))],
    syntaxPattern := [.nonTerminal "ps"],
    algebra? := some { flatten := true, unit := some "Z" } }

/-- A constant of the sort of the bag. -/
def constantRule (label : String) : GrammarRule :=
  { label := label, category := "P", params := [], syntaxPattern := [] }

/-- The bag with two constants under the given labels.  The bag declares the
label `Z` as its unit whatever the two labels are. -/
def bagWith (first second : String) : LanguageDef :=
  { name := "BagWithUnit"
    types := ["P"]
    terms := [bagRule, constantRule first, constantRule second]
    equations := []
    rewrites := [] }

/-- The presentation passes the declaration gate when the three labels are
distinct. -/
theorem bagWith_validate_eq_nil (first second : String)
    (distinct : (["Par", first, second] : List String).Nodup) :
    (bagWith first second).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["P"] : List String).Nodup
    decide
  · exact distinct
  · show ([] : List String).Nodup
    decide
  · intro term membership
    have listed : term ∈ [bagRule, constantRule first, constantRule second] := membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl <;> exact List.Mem.head _
  · intro term membership parameter parameterMember typeName typeMember
    have listed : term ∈ [bagRule, constantRule first, constantRule second] := membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl
    · simp only [bagRule, List.mem_cons, List.not_mem_nil, or_false] at parameterMember
      subst parameterMember
      simp only [TermParam.typeExpr, TypeExpr.baseNames, List.mem_cons, List.not_mem_nil,
        or_false] at typeMember
      subst typeMember
      exact List.Mem.head _
    · simp [constantRule] at parameterMember
    · simp [constantRule] at parameterMember
  · intro term membership
    have listed : term ∈ [bagRule, constantRule first, constantRule second] := membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · intro rewrite membership
    cases membership

/-- The bag with unit `Z` and constant `A`. -/
def bagZA : ValidatedLanguageDef := ⟨bagWith "Z" "A", bagWith_validate_eq_nil _ _ (by decide)⟩

/-- The same bag with the constant under the label `A2`. -/
def bagZA2 : ValidatedLanguageDef := ⟨bagWith "Z" "A2", bagWith_validate_eq_nil _ _ (by decide)⟩

/-- The same bag with the first constant under the label `Z2`.  The bag still
declares the label `Z` as its unit. -/
def bagZ2A : ValidatedLanguageDef := ⟨bagWith "Z2" "A", bagWith_validate_eq_nil _ _ (by decide)⟩

/-- A renaming of constructors that fixes the label of the bag carries the
bag with two constants to the bag with the renamed constants. -/
def constantRenaming (symbols : LanguageDefSymbolMap) (first second : String)
    (sortFixed : ∀ name, symbols.sort name = name)
    (bagFixed : symbols.constructor "Par" = "Par")
    (unitFixed : symbols.constructor "Z" = "Z")
    (sourceValid : (bagWith first second).validate = [])
    (targetValid :
      (bagWith (symbols.constructor first) (symbols.constructor second)).validate = []) :
    StructuralMorphism ⟨bagWith first second, sourceValid⟩
      ⟨bagWith (symbols.constructor first) (symbols.constructor second), targetValid⟩ where
  symbols := symbols
  mapsTypes := by
    intro declaration membership
    cases membership with
    | head =>
        have same : mapTypeDecl symbols (TypeDecl.plain "P") = TypeDecl.plain "P" := by
          simp [mapTypeDecl, TypeDecl.plain, sortFixed]
        rw [same]
        exact List.Mem.head _
    | tail _ inner => cases inner
  mapsTerms := by
    intro rule membership
    have listed : rule ∈ [bagRule, constantRule first, constantRule second] := membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    show mapGrammarRule symbols rule ∈
      [bagRule, constantRule (symbols.constructor first),
        constantRule (symbols.constructor second)]
    rcases listed with rfl | rfl | rfl
    · simp [mapGrammarRule, bagRule, bagFixed, sortFixed, mapTermParam, mapTypeExpr,
        StructuralMorphism.mapCollectionAlgebra, unitFixed]
    · simp [mapGrammarRule, constantRule, sortFixed]
    · simp [mapGrammarRule, constantRule, sortFixed]
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    cases membership

/-- Renaming the constant `A` to `A2`. -/
def renameConstant : StructuralMorphism bagZA bagZA2 :=
  constantRenaming (swapConstructors "A" "A2") "Z" "A" (fun _ => rfl) (by decide) (by decide) _
    (bagWith_validate_eq_nil _ _ (by decide))

/-- The complete structural image renames the unit reference as well as
its declaration. -/
def renamedUnitBag : ValidatedLanguageDef :=
  validatedImage bagZA (swapConstructors "Z" "Z2") (by decide +kernel)

/-- Renaming `Z` to `Z2` in the entire presentation, including algebra
metadata. -/
def renameUnit : StructuralMorphism bagZA renamedUnitBag :=
  structuralMapToValidatedImage bagZA (swapConstructors "Z" "Z2")
    (by decide +kernel)

/-- The sort of the bag. -/
def sortP (first second : String) : LangSort (bagWith first second) := ⟨"P", List.Mem.head _⟩

/-- The interface of the closed terms of the bag's sort. -/
abbrev closedP : Interface := closedInterface (presentation := bagZA) (sortP "Z" "A")

/-- `{Z | A}`: the bag of the unit and the constant. -/
def unitBesideA : Term bagZA.language closedP :=
  ofClosed (ClosedTerm.ofCheck
    (.collection .hashBag [.apply "Z" [], .apply "A" []] none) (by decide +kernel))

/-- `{A}`: the bag of the constant alone. -/
def singletonA : Term bagZA.language closedP :=
  ofClosed (ClosedTerm.ofCheck (.collection .hashBag [.apply "A" []] none) (by decide +kernel))

/-- `A`: the constant. -/
def constantA : Term bagZA.language closedP :=
  ofClosed (ClosedTerm.ofCheck (.apply "A" []) (by decide +kernel))

/-- The bag of the source declares its algebra, with the unit `Z` authored. -/
theorem bagZA_algebraRule :
    AlgebraRule bagZA.language bagRule .hashBag { flatten := true, unit := some "Z" } where
  authored := List.Mem.head _
  declared := rfl
  selfSorted := ⟨"ps", rfl⟩
  unitAuthored := by
    intro unit declared
    obtain rfl : "Z" = unit := Option.some.inj declared
    exact ⟨constantRule "Z", List.Mem.tail _ (List.Mem.head _), rfl, rfl, rfl⟩

/-- **In the source the bag of the unit and the constant is equivalent to the
constant**: the unit is absorbed and the singleton collapses. -/
theorem unitBesideA_equivalent :
    (termSetoid base bagZA.language closedP).r unitBesideA constantA := by
  have absorbed : (termSetoid base bagZA.language closedP).r unitBesideA singletonA :=
    Relation.EqvGen.rel _ _ (EquationContextStep.inContext .hole (Or.inr
      (DerivedInstance.unitElim (pre := []) (post := [.apply "A" []]) bagZA_algebraRule rfl
        ⟨FreeTypeContext.empty, [], unitBesideA.2.1⟩)))
  have collapsed : (termSetoid base bagZA.language closedP).r singletonA constantA :=
    Relation.EqvGen.rel _ _ (EquationContextStep.inContext .hole (Or.inr
      (DerivedInstance.singleton bagZA_algebraRule rfl
        ⟨FreeTypeContext.empty, [], singletonA.2.1⟩)))
  exact Relation.EqvGen.trans _ _ _ absorbed collapsed

/-! ### Renaming the constant -/

/-- Renaming the constant fixes the declared unit. -/
theorem renameConstant_fixesUnits :
    FixesDeclaredUnits renameConstant.symbols bagZA.language := by
  intro rule membership algebra declared unit isUnit
  have listed : rule ∈ [bagRule, constantRule "Z", constantRule "A"] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · obtain rfl : ({ flatten := true, unit := some "Z" } : CollectionAlgebra) = algebra :=
      Option.some.inj declared
    obtain rfl : "Z" = unit := Option.some.inj isUnit
    decide
  · cases declared
  · cases declared

/-- **Renaming the constant preserves the static equivalence**: the laws of
the unit are carried. -/
theorem renameConstant_preservesEquations : PreservesEquations base renameConstant :=
  preservesEquations_default renameConstant rfl renameConstant_fixesUnits

/-- In the image the bag of the unit and the renamed constant is equivalent
to the renamed constant. -/
theorem renameConstant_carries_unit_law :
    (termSetoid base bagZA2.language (closedP.map renameConstant.symbols)).r
      (Term.map renameConstant unitBesideA) (Term.map renameConstant constantA) :=
  renameConstant_preservesEquations unitBesideA_equivalent

/-- The image of the bag is the bag of `Z` and `A2`. -/
theorem renameConstant_unitBesideA :
    (Term.map renameConstant unitBesideA).1 =
      .collection .hashBag [.apply "Z" [], .apply "A2" []] none := by
  decide +kernel

/-! ### Renaming the unit -/

/-- Renaming the unit is injective on constructors and fixes the built-in
relation. -/
theorem renameUnit_injective : Function.Injective renameUnit.symbols.constructor :=
  swapConstructors_injective _ _

/-- Renaming the unit does not fix the declared unit. -/
theorem renameUnit_not_fixesUnits :
    ¬ FixesDeclaredUnits renameUnit.symbols bagZA.language := by
  intro fixes
  have fixed := fixes bagRule (List.Mem.head _) _ rfl "Z" rfl
  revert fixed
  decide

/-- A pattern that is a collection at its root. -/
def IsCollection : Pattern → Prop
  | .collection _ _ _ => True
  | _ => False

/-- A context other than the hole decides the root of what fills it. -/
theorem isCollection_fill_iff (context : OneHoleContext) (notHole : context ≠ .hole)
    (first second : Pattern) :
    IsCollection (context.fill first) ↔ IsCollection (context.fill second) := by
  cases context with
  | hole => exact absurd rfl notHole
  | apply constructor before inner after => simp [OneHoleContext.fill, IsCollection]
  | lambda binder inner => simp [OneHoleContext.fill, IsCollection]
  | multiLambda arity binders inner => simp [OneHoleContext.fill, IsCollection]
  | substBody inner replacement => simp [OneHoleContext.fill, IsCollection]
  | substReplacement body inner => simp [OneHoleContext.fill, IsCollection]
  | collection kind before inner after rest => simp [OneHoleContext.fill, IsCollection]

/-- The incomplete target declares no usable algebra: its bag still names
`Z` as its unit, while no target constructor has that label. -/
theorem bagZ2A_no_algebraRule {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} : ¬ AlgebraRule bagZ2A.language rule kind algebra := by
  intro declaration
  have listed : rule ∈ [bagRule, constantRule "Z2", constantRule "A"] := declaration.authored
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl
  · have declared := declaration.declared
    obtain rfl : ({ flatten := true, unit := some "Z" } : CollectionAlgebra) = algebra :=
      Option.some.inj declared
    obtain ⟨unitRule, unitMember, unitLabel, -, -⟩ := declaration.unitAuthored "Z" rfl
    have unitListed : unitRule ∈ [bagRule, constantRule "Z2", constantRule "A"] := unitMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at unitListed
    rcases unitListed with rfl | rfl | rfl <;> exact absurd unitLabel (by decide)
  · exact absurd declaration.declared (by simp [constantRule])
  · exact absurd declaration.declared (by simp [constantRule])

/-- In the incomplete target, an equation step relates a collection only
to a collection; no declared unit or flattening law is usable. -/
theorem bagZ2A_step_isCollection {left right : Pattern}
    (step : EquationContextStep base bagZ2A.language left right) :
    IsCollection left ↔ IsCollection right := by
  cases step with
  | inContext context generator =>
      by_cases isHole : context = .hole
      · subst isHole
        rcases generator with ⟨fuel, authored⟩ | derived
        · cases authored with
          | forward member => cases member
          | reverse member => cases member
        · cases derived with
          | bagPerm => simp [OneHoleContext.fill, IsCollection]
          | setPerm => simp [OneHoleContext.fill, IsCollection]
          | setDedup => simp [OneHoleContext.fill, IsCollection]
          | flatten declaration => exact absurd declaration bagZ2A_no_algebraRule
          | singleton declaration => exact absurd declaration bagZ2A_no_algebraRule
          | unitElim declaration => exact absurd declaration bagZ2A_no_algebraRule
          | emptyUnit declaration => exact absurd declaration bagZ2A_no_algebraRule
      · exact isCollection_fill_iff context isHole _ _

/-- Equivalent patterns in the incomplete target agree on whether their
root is a collection. -/
theorem bagZ2A_equivalent_isCollection {left right : Pattern}
    (equivalent : EquationEquiv base bagZ2A.language left right) :
    IsCollection left ↔ IsCollection right := by
  induction equivalent with
  | rel left right step => exact bagZ2A_step_isCollection step
  | refl term => exact Iff.rfl
  | symm left right _ recurse => exact recurse.symm
  | trans left middle right _ _ first second => exact first.trans second

/-- Complete unit renaming preserves every contextual equation at every
interface without fixing the unit's original name. -/
theorem renameUnit_preservesEquations : PreservesEquations base renameUnit :=
  preservesEquations_transport_default renameUnit rfl

/-- The same unit absorption law holds on the actual renamed typed terms. -/
theorem renameUnit_carries_unit_law :
    (termSetoid base renamedUnitBag.language (closedP.map renameUnit.symbols)).r
      (Term.map renameUnit unitBesideA) (Term.map renameUnit constantA) :=
  renameUnit_preservesEquations unitBesideA_equivalent

/-- The incomplete target omits the renamed unit reference, so no structural
map into it can have the intended constructor action. -/
theorem staleUnit_not_a_structuralMap
    (morphism : StructuralMorphism bagZA bagZ2A) :
    morphism.symbols ≠ swapConstructors "Z" "Z2" := by
  intro symbols
  have mapped := morphism.mapsTerms bagRule (List.Mem.head _)
  rw [symbols] at mapped
  have absent : mapGrammarRule (swapConstructors "Z" "Z2") bagRule ∉
      bagZ2A.language.terms := by decide +kernel
  exact absent mapped

/-- Retaining a stale unit reference loses the source unit law. This is an
incomplete metadata translation, not a structural morphism. -/
theorem staleUnit_unit_law_fails :
    ¬ EquationEquiv base bagZ2A.language
      (mapPattern (swapConstructors "Z" "Z2") unitBesideA.1)
      (mapPattern (swapConstructors "Z" "Z2") constantA.1) := by
  intro equivalent
  have image := bagZ2A_equivalent_isCollection equivalent
  have bag : IsCollection
      (mapPattern (swapConstructors "Z" "Z2") unitBesideA.1) := by
    change IsCollection (mapPattern (swapConstructors "Z" "Z2")
      (.collection .hashBag [.apply "Z" [], .apply "A" []] none))
    simp [mapPattern, IsCollection]
  have constant : ¬ IsCollection
      (mapPattern (swapConstructors "Z" "Z2") constantA.1) := by
    change ¬ IsCollection (mapPattern (swapConstructors "Z" "Z2") (.apply "A" []))
    simp [mapPattern, IsCollection]
  exact constant (image.mp bag)

/-- A unit may change names under a complete structural map. A stale
algebra reference instead loses the law and cannot be such a map. -/
theorem collection_unit_metadata_required :
    (¬ FixesDeclaredUnits renameUnit.symbols bagZA.language ∧
      PreservesEquations base renameUnit) ∧
    (¬ EquationEquiv base bagZ2A.language
        (mapPattern (swapConstructors "Z" "Z2") unitBesideA.1)
        (mapPattern (swapConstructors "Z" "Z2") constantA.1) ∧
      ∀ morphism : StructuralMorphism bagZA bagZ2A,
        morphism.symbols ≠ swapConstructors "Z" "Z2") :=
  ⟨⟨renameUnit_not_fixesUnits, renameUnit_preservesEquations⟩,
    ⟨staleUnit_unit_law_fails, staleUnit_not_a_structuralMap⟩⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls.EquationTransport
