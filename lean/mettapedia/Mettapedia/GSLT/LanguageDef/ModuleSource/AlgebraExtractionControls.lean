import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtraction
import Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraInterpretation

/-! # Textual controls for collection-algebra admission -/

open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

Module LiteralVariadicAssociativity {
  Theory Words() {
    Types { Item; }
    Terms {
      Word . xs:Vec(Item) |- "[" xs.*sep(",") "]" : Item;
    }
    Equations {
      (Word {(Word {x, y}), z}) == (Word {x, (Word {y, z})});
    }
  }
  theory Words()
}

Module NonunitalBinaryCollection {
  Theory Semigroup() {
    Types { Item; }
    Terms { Op . x:Item, y:Item |- "(" x ";" y ")" : Item; }
    Equations { (Op (Op x y) z) == (Op x (Op y z)); }
  }
  Theory Words(s: Semigroup) {
    s Replacements { Op => Word . xs:Vec(Item) |- "[" xs.*sep(",") "]" : Item; }
  }
  theory Words(Semigroup())
}

Module BagChangedToSet {
  Theory Bags() {
    Types { Item; }
    Terms { Bag . xs:HashBag(Item) |- "{" xs.*sep(",") "}" : Item; }
  }
  Theory Sets(b: Bags) {
    b Replacements { Bag => Set . xs:HashSet(Item) |- "{" xs.*sep(",") "}" : Item; }
  }
  theory Sets(Bags())
}

Module SourceMonoidFold {
  Theory Monoid() {
    Types { Item; }
    Terms {
      One . |- "one" : Item;
      Op . x:Item, y:Item |- "(" x ";" y ")" : Item;
    }
    Equations {
      (Op (Op x y) z) == (Op x (Op y z));
      (Op x (One)) == x;
      (Op (One) x) == x;
    }
  }
  Theory Words(m: Monoid) {
    m Replacements { Op => Word . xs:Vec(Item) |- "[" xs.*sep(",") "]" : Item; }
  }
  theory Words(Monoid())
}

#module_roundtrip LiteralVariadicAssociativity
#module_roundtrip SourceMonoidFold

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionControls

#guard match LiteralVariadicAssociativity.language with
  | .ok language => language.equations.length == 1 &&
      language.terms.all (fun rule => rule.algebra?.isNone)
  | .error _ => false

#guard match NonunitalBinaryCollection.language with
  | .error (.replaceCollectionBasis "Op" "Word") => true
  | _ => false

#guard match BagChangedToSet.language with
  | .error (.replaceTyping "Bag" "Set") => true
  | _ => false

#guard match SourceMonoidFold.language with
  | .ok language => language.equations.length == 2 &&
      ((language.terms.find? (fun rule => rule.label == "Word")).bind (·.algebra?)) ==
        some { flatten := true, unit := some "One" }
  | .error _ => false

def sourceMonoidValue : Value :=
  ((applyTheory SourceMonoidFold.library SourceMonoidFold.module ["Monoid"] []).toOption.map
    Prod.snd).getD { entries := [] }

theorem source_monoid_basis_ready : binaryFoldReady sourceMonoidValue "Op" = true := by decide

def wordOperations (_label : String) (arguments : List (List Nat)) : List Nat := arguments.flatten

theorem source_monoid_equation_inventory :
    (flattenRaw "" sourceMonoidValue).equations.map (fun row => (row.left, row.right)) =
      [(.apply "Op" [.apply "Op" [.fvar "x", .fvar "y"], .fvar "z"],
          .apply "Op" [.fvar "x", .apply "Op" [.fvar "y", .fvar "z"]]),
        (.apply "Op" [.fvar "x", .apply "One" []], .fvar "x"),
        (.apply "Op" [.apply "One" [], .fvar "x"], .fvar "x")] := by decide

/-- The actual parsed source has a noncommutative word model. Its source
equations are checked semantically, independently of the admission recognizer. -/
theorem source_monoid_word_model :
    AlgebraInterpretation.SourceEquationsHold wordOperations sourceMonoidValue := by
  intro item member row body _
  have declared : row ∈ (flattenRaw "" sourceMonoidValue).equations :=
    List.mem_filterMap.mpr ⟨item, member, by simp [body]⟩
  have pair := List.mem_map_of_mem (f := fun row : Equation => (row.left, row.right)) declared
  rw [source_monoid_equation_inventory] at pair
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at pair
  rcases pair with ⟨left, right⟩ | ⟨left, right⟩ | ⟨left, right⟩ <;>
    rw [left, right] <;>
    simp [AlgebraInterpretation.EquationHolds, AlgebraInterpretation.read?,
      wordOperations, List.append_assoc]

theorem source_monoid_has_variadic_model :
    ∃ unit : String, ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat),
      model.fold [] = wordOperations unit [] ∧
      ∀ first second, model.fold [first, second] = first ++ second := by
  obtain ⟨unit, model, empty, binary, _, _⟩ :=
    AlgebraInterpretation.collection_fold_model .vec source_monoid_word_model
      source_monoid_basis_ready (by simp) (by simp)
  exact ⟨unit, model, empty, fun first second => by
    simpa [wordOperations] using binary first second⟩

def wordReplacement? : Option Replacement := do
  let theoryRow ← SourceMonoidFold.module.theories.find? (·.name == "Words")
  match theoryRow.body with
  | .extend _ [.replacements [row]] => some row
  | _ => none

def wordReplacement : Replacement :=
  wordReplacement?.getD ⟨"", singleRule []⟩

theorem word_replacement_is_authored : wordReplacement? = some wordReplacement := by decide +kernel

def replacedWordValue : Value :=
  (replaceRow sourceMonoidValue wordReplacement).toOption.getD sourceMonoidValue

theorem actual_word_replacement_succeeds :
    replaceRow sourceMonoidValue wordReplacement = .ok replacedWordValue := by
  have checked : (replaceRow sourceMonoidValue wordReplacement).isOk = true := by decide +kernel
  unfold replacedWordValue
  generalize computed : replaceRow sourceMonoidValue wordReplacement = result at checked ⊢
  cases result with
  | error _ => cases checked
  | ok _ => rfl

def binarySourceItem : Item :=
  (sourceMonoidValue.entries.find? (·.label == (.term, "Op"))).getD
    (newItem 0 .term "" (.term (singleRule [])))

def binarySourceRule : GrammarRule :=
  match binarySourceItem.body with
  | .term rule => rule
  | _ => singleRule []

/-- The fold model is now obtained from the actual authored replacement's
success, not from a separately supplied faithfulness-check result. -/
theorem actual_word_replacement_has_fold_model :
    ∃ unit : String, ∃ model : Mettapedia.Algebra.Collections.Folds.Model (List Nat),
      model.fold [] = wordOperations unit [] ∧
      ∀ first second, model.fold [first, second] = first ++ second := by
  have selected : sourceMonoidValue.entries.find? (·.label == (.term, wordReplacement.old)) =
      some binarySourceItem := by decide +kernel
  have body : binarySourceItem.body = .term binarySourceRule := by rfl
  have source : collectionParameterKind binarySourceRule = none := by decide +kernel
  have target : wordReplacement.rule.params = [.simple "xs" (.collection .vec (.base "Item"))] := by rfl
  obtain ⟨unit, model, empty, binary, _, _⟩ :=
    AlgebraInterpretation.replacement_collection_fold_model actual_word_replacement_succeeds
      selected body source target source_monoid_word_model
  refine ⟨unit, model, empty, ?_⟩
  intro first second
  simpa [wordOperations] using binary first second

theorem word_model_does_not_erase_order :
    wordOperations "Op" [[0], [1]] ≠ wordOperations "Op" [[1], [0]] := by decide

theorem word_model_does_not_erase_multiplicity :
    wordOperations "Op" [[0], [0]] ≠ wordOperations "Op" [[0]] := by decide

def extractedWordLanguage : LanguageDef :=
  SourceMonoidFold.language.toOption.getD (LanguageDef.empty "")

def unitVector : Pattern := .collection .vec [.apply "One" []] none

def vectorLength : Pattern → Option Nat
  | .collection .vec elements none => some elements.length
  | _ => none

open WellSorted

/-- A unit value and a declared bare carrier give the same representation
both an operation-carrier fibre and a vector-data fibre. -/
theorem unit_vector_has_two_typing_fibres
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {parameter : String}
    (unitTyped : HasType language free bound (.apply "One" []) (.base rule.category))
    (declaredRule : rule ∈ language.terms)
    (shape : rule.bareParams = [.simple parameter (.collection .vec (.base rule.category))]) :
    HasType language free bound unitVector (.base rule.category) ∧
      HasType language free bound unitVector (.collection .vec (.base rule.category)) := by
  have elements : ElementsHaveType language free bound [.apply "One" []] (.base rule.category) :=
    .cons unitTyped (.nil bound (.base rule.category))
  exact ⟨.collectionConstructor declaredRule shape elements, .collection elements⟩

/-- A kind-wide unit law keeps both types but changes the vector-data
readout. Its declaration table, unit typing and carrier row are primitive
inputs, rather than an assumed normalization or observation theorem. -/
theorem untyped_unit_normalization_changes_vector_data
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} {parameter : String}
    (unitTyped : HasType language free bound (.apply "One" []) (.base rule.category))
    (declaredRule : rule ∈ language.terms)
    (shape : rule.bareParams = [.simple parameter (.collection .vec (.base rule.category))])
    (laws : Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared language = [⟨.vec, some "One"⟩]) :
    let normalized := Mettapedia.OSLF.MeTTaIL.CollectionLaws.standardForm
      (Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared language) [] unitVector
    HasType language free bound unitVector (.base rule.category) ∧
      HasType language free bound unitVector (.collection .vec (.base rule.category)) ∧
      vectorLength unitVector = some 1 ∧ vectorLength normalized = some 0 ∧
      HasType language free bound normalized (.base rule.category) ∧
      HasType language free bound normalized (.collection .vec (.base rule.category)) := by
  have computed : Mettapedia.OSLF.MeTTaIL.CollectionLaws.standardForm
      (Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared language) [] unitVector =
      .collection .vec [] none := by
    rw [laws]
    simp [Mettapedia.OSLF.MeTTaIL.CollectionLaws.standardForm,
      Mettapedia.OSLF.MeTTaIL.CollectionLaws.normalize,
      Mettapedia.OSLF.MeTTaIL.CollectionLaws.splice,
      Mettapedia.OSLF.MeTTaIL.CollectionLaws.extrude, unitVector]
  dsimp only
  rw [computed]
  have before := unit_vector_has_two_typing_fibres unitTyped declaredRule shape
  exact ⟨before.1, before.2, rfl, rfl, .collectionConstructor declaredRule shape (.nil bound (.base rule.category)),
    .collection (.nil bound (.base rule.category))⟩

/- The actual authored source supplies a concrete evaluated discriminator
for the generic theorem. Kernel compilation of the complete module is not
assumed by that theorem. -/
#guard checkHasType extractedWordLanguage (fun _ => none) [] unitVector (.base "Item") &&
  checkHasType extractedWordLanguage (fun _ => none) [] unitVector (.collection .vec (.base "Item"))

def normalizedUnitVector : Pattern := Mettapedia.OSLF.MeTTaIL.CollectionLaws.standardForm
  (Mettapedia.OSLF.MeTTaIL.CollectionLaws.declared extractedWordLanguage) [] unitVector

#guard vectorLength unitVector == some 1 && vectorLength normalizedUnitVector == some 0 &&
  checkHasType extractedWordLanguage (fun _ => none) [] normalizedUnitVector (.base "Item") &&
  checkHasType extractedWordLanguage (fun _ => none) [] normalizedUnitVector (.collection .vec (.base "Item"))

end Mettapedia.GSLT.LanguageDef.ModuleSource.AlgebraExtractionControls
