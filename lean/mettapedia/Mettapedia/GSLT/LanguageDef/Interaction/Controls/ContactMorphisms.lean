import Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
import Mettapedia.GSLT.LanguageDef.TypingInversion
import Mettapedia.GSLT.LanguageDef.ClosedTermChecker
import Mettapedia.GSLT.Core.FunctionalBisimulation
import Mettapedia.OSLF.MeTTaIL.RuleInstances

/-!
# Morphisms of interactive theories on the contact family

The law-free member of the contact family is an iGSLT whose reduction is easy
to describe: a term steps exactly when it is an input prefix facing an output
prefix across the contact, and it steps to the contact of the two bodies.

Two maps out of it show what a morphism of iGSLTs is and is not.

* The renaming that sends the constant `B` to the constant `A` and fixes every
  other symbol is a morphism from the theory to itself.  It is not the
  identity, and it is not injective on terms: it identifies `A` and `B`.  It
  preserves bisimilarity because it preserves steps and every step of an
  image is the image of a step.
* The inclusion into the same theory with one more rule, `B ⟶ A`, carries
  every declaration to a declaration and preserves the selected sort, contact
  and rule.  It is not a morphism of iGSLTs: `A` and `B` are bisimilar where
  neither moves, and are not where `B` does.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- An input prefix. -/
def input (body : Pattern) : Pattern := .apply "In" [body]

/-- An output prefix. -/
def output (body : Pattern) : Pattern := .apply "Out" [body]

/-! ## Steps of the family -/

/-- A language whose only rule is the contact rule has plain rules. -/
theorem plainRules_of_rewrites {language : LanguageDef}
    (rewrites : language.rewrites = [syncRule]) : PlainRules language := by
  intro rule membership
  rw [rewrites] at membership
  obtain rfl := List.mem_singleton.mp membership
  exact ⟨rfl, by decide +kernel⟩

/-- The contact rule fires on an input facing an output. -/
theorem sync_matches (first second : Pattern) :
    ∃ bindings ∈ matchPattern syncRule.left (join (input first) (output second)),
      applyBindings bindings syncRule.right = join first second := by
  refine ⟨[("y", second), ("x", first)], ?_, ?_⟩
  · apply matchRel_complete
    refine MatchRel.apply (MatchArgsRel.cons (hb := [("x", first)]) (tb := [("y", second)])
      (MatchRel.apply (MatchArgsRel.cons (hb := [("x", first)]) (tb := [])
        MatchRel.fvar MatchArgsRel.nil rfl) rfl)
      (MatchArgsRel.cons (hb := [("y", second)]) (tb := [])
        (MatchRel.apply (MatchArgsRel.cons (hb := [("y", second)]) (tb := [])
          MatchRel.fvar MatchArgsRel.nil rfl) rfl)
        MatchArgsRel.nil rfl)
      ?_) rfl
    rfl
  · simp [syncRule, join, applyBindings]

/-- **The reduction of a contact theory.**  A term steps exactly when it is an
input facing an output across the contact, and then to the contact of the two
bodies. -/
theorem step_iff_of_rewrites {language : LanguageDef}
    (rewrites : language.rewrites = [syncRule]) {source target : Pattern} :
    Step base language source target ↔
      ∃ first second, source = join (input first) (output second) ∧
        target = join first second := by
  constructor
  · intro step
    obtain ⟨rule, membership, bindings, rfl, rfl⟩ :=
      sides_of_step (plainRules_of_rewrites rewrites) (by
        intro rule membership
        rw [rewrites] at membership
        obtain rfl := List.mem_singleton.mp membership
        decide) step
    rw [rewrites] at membership
    obtain rfl := List.mem_singleton.mp membership
    exact ⟨applyBindings bindings (.fvar "x"), applyBindings bindings (.fvar "y"),
      by simp [syncRule, join, input, output, applyBindings],
      by simp [syncRule, join, applyBindings]⟩
  · rintro ⟨first, second, rfl, rfl⟩
    obtain ⟨bindings, matched, applied⟩ := sync_matches first second
    exact (step_iff_exists_match (plainRules_of_rewrites rewrites)).mpr
      ⟨syncRule, by rw [rewrites]; exact List.mem_singleton.mpr rfl, bindings, matched, applied⟩

/-! ## The law-free theory as an iGSLT -/

/-- The law-free presentation. -/
def barePresentation : InteractivePresentation :=
  presentation [] (by decide) (by intro law membership; cases membership)

theorem bare_executionFlowErrors_eq_nil :
    (contactWith []).executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    obtain rfl : rule = syncRule := List.mem_singleton.mp membership
    rfl
  · intro rule membership name nameMembership
    obtain rfl : rule = syncRule := List.mem_singleton.mp membership
    simp [syncRule, join, Pattern.freeFvarNames] at nameMembership ⊢
    exact nameMembership

/-- The law-free contact theory as an iGSLT. -/
def bare : IGSLT where
  presentation := barePresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := contactWith []
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            barePresentation.presentation.valid bare_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- With no law, the static equivalence of the fibre is equality. -/
theorem bare_equivalent_iff_eq {left right : barePresentation.Term} :
    (presentedEquationSetoid defaultBasePremises barePresentation).r left right ↔
      left = right :=
  presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises barePresentation
    (by decide) left right

/-- The steps of the iGSLT are the steps of the rule. -/
theorem bare_step_iff {source target : barePresentation.Term} :
    bare.toGSLT.Step source target ↔
      ∃ first second, source.1 = join (input first) (output second) ∧
        target.1 = join first second := by
  constructor
  · rintro ⟨redex, contractum, sourceEquivalent, primitive, targetEquivalent⟩
    obtain rfl := bare_equivalent_iff_eq.mp sourceEquivalent
    obtain rfl := bare_equivalent_iff_eq.mp targetEquivalent
    exact (step_iff_of_rewrites (language := contactWith []) rfl).mp primitive
  · intro shape
    exact primitiveStep_to_presentedStep (base := defaultBasePremises)
      (presentation := barePresentation)
      ((step_iff_of_rewrites (language := contactWith []) rfl).mpr shape)

/-- The typing of an input facing an output types the contact of the two
bodies, in every typing context. -/
theorem hasType_reduct {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr}
    {first second : Pattern}
    (typed : HasType (contactWith []) free bound (join (input first) (output second)) type) :
    HasType (contactWith []) free bound (join first second) type := by
  obtain ⟨rule, ruleMember, ruleLabel, sortEq, notBare, arguments⟩ := typed.apply_inv
  have ruleIsJoin : rule = terms[7] := by
    change rule ∈ terms at ruleMember
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ruleMember
    rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd ruleLabel (by decide)
  subst ruleIsJoin
  obtain ⟨inputTyped, rest⟩ := arguments.simple_cons_inv
  obtain ⟨outputTyped, -⟩ := rest.simple_cons_inv
  obtain ⟨inputRule, inputMember, inputLabel, -, -, inputArguments⟩ := inputTyped.apply_inv
  have inputIsIn : inputRule = terms[5] := by
    change inputRule ∈ terms at inputMember
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at inputMember
    rcases inputMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd inputLabel (by decide)
  subst inputIsIn
  obtain ⟨outputRule, outputMember, outputLabel, -, -, outputArguments⟩ :=
    outputTyped.apply_inv
  have outputIsOut : outputRule = terms[6] := by
    change outputRule ∈ terms at outputMember
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at outputMember
    rcases outputMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd outputLabel (by decide)
  subst outputIsOut
  obtain ⟨firstTyped, -⟩ := inputArguments.simple_cons_inv
  obtain ⟨secondTyped, -⟩ := outputArguments.simple_cons_inv
  rw [sortEq]
  exact HasType.constructor (rule := terms[7]) (List.getElem_mem (by decide)) notBare
    (.cons trivial rfl firstTyped (.cons trivial rfl secondTyped .nil))

/-- The reduct of a closed term is a closed term. -/
theorem closed_reduct {sort : LangSort (contactWith [])} {first second : Pattern}
    (closed : ClosedTermWellSorted (contactWith []) sort
      (join (input first) (output second))) :
    ClosedTermWellSorted (contactWith []) sort (join first second) := by
  obtain ⟨typed, ground, canonical, object, wellScoped⟩ := closed
  refine ⟨hasType_reduct typed, ?_, ?_, ?_, ?_⟩
  · simpa [join, input, output, Pattern.isGround, Pattern.isGroundAt,
      Pattern.isGroundListAt] using ground
  · simpa [join, input, output, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList] using canonical
  · simpa [join, input, output, isObjectPattern, isObjectPatternList] using object
  · simpa [ScopeSafe, ScopeSafeAt, join, input, output, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt] using wellScoped

/-! ## A morphism that identifies two terms -/

/-- Send the constant `B` to the constant `A`; fix everything else. -/
def collapseSymbols : LanguageDefSymbolMap where
  sort := id
  constructor := fun label => if label = "B" then "A" else label
  relation := id
  equation := id
  rewrite := id

/-- A label other than `A` and `B` is the image of itself only. -/
theorem collapse_eq_iff {original label : String} (notA : label ≠ "A")
    (notB : label ≠ "B") :
    collapseSymbols.constructor original = label ↔ original = label := by
  unfold collapseSymbols
  by_cases isB : original = "B"
  · subst isB
    simp only [if_true]
    constructor
    · intro same
      exact absurd same.symm notA
    · intro same
      exact absurd same.symm notB
  · simp [isB]

/-- A list whose image has two elements has two elements. -/
theorem map_eq_pair {α β : Type*} {function : α → β} {list : List α} {first second : β}
    (image : list.map function = [first, second]) :
    ∃ left right, list = [left, right] ∧ function left = first ∧ function right = second := by
  match list, image with
  | [left, right], image =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at image
      exact ⟨left, right, rfl, image.1, image.2⟩

/-- A list whose image has one element has one element. -/
theorem map_eq_single {α β : Type*} {function : α → β} {list : List α} {only : β}
    (image : list.map function = [only]) :
    ∃ element, list = [element] ∧ function element = only := by
  match list, image with
  | [element], image =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at image
      exact ⟨element, rfl, image⟩

/-- The renaming fixes the contact rule. -/
theorem collapse_syncRule : mapRewriteRule collapseSymbols syncRule = syncRule := by
  simp [mapRewriteRule, syncRule, join, mapPattern, mapPatternList, collapseSymbols,
    mapTypeContext, mapTypeExpr]

/-- The renaming carries every declaration of the law-free theory to one of
its declarations. -/
def collapseStructural :
    StructuralMorphism barePresentation.presentation barePresentation.presentation where
  symbols := collapseSymbols
  mapsTypes := by
    intro declaration membership
    obtain rfl : declaration = TypeDecl.plain "Proc" := List.mem_singleton.mp membership
    exact List.Mem.head _
  mapsTerms := by
    intro rule membership
    change rule ∈ terms at membership
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
    change mapGrammarRule collapseSymbols rule ∈ terms
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    obtain rfl : rewrite = syncRule := List.mem_singleton.mp membership
    change mapRewriteRule collapseSymbols syncRule ∈ [syncRule]
    rw [collapse_syncRule]
    exact List.mem_singleton.mpr rfl

/-- It preserves the selected sort, contact and rule. -/
def collapseInteractive : InteractiveMorphism barePresentation barePresentation where
  structural := collapseStructural
  mapsInteractingSort := Subtype.ext (by decide +kernel)
  mapsContactConstructor := Subtype.ext (by decide +kernel)
  mapsInteractionRewrite := Subtype.ext collapse_syncRule

/-- The renaming of an input facing an output. -/
theorem collapse_join (first second : Pattern) :
    mapPattern collapseSymbols (join (input first) (output second)) =
      join (input (mapPattern collapseSymbols first))
        (output (mapPattern collapseSymbols second)) := by
  simp [join, input, output, mapPattern, collapseSymbols]

/-- The renaming of a contact. -/
theorem collapse_contact (first second : Pattern) :
    mapPattern collapseSymbols (join first second) =
      join (mapPattern collapseSymbols first) (mapPattern collapseSymbols second) := by
  simp [join, mapPattern, collapseSymbols]

/-- A term whose renaming is an input facing an output is one. -/
theorem collapse_join_inv {pattern first' second' : Pattern}
    (image : mapPattern collapseSymbols pattern = join (input first') (output second')) :
    ∃ first second, pattern = join (input first) (output second) ∧
      mapPattern collapseSymbols first = first' ∧
        mapPattern collapseSymbols second = second' := by
  obtain ⟨label, arguments, rfl, labelImage, argumentImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp image
  obtain rfl := (collapse_eq_iff (by decide) (by decide)).mp labelImage
  obtain ⟨left, right, rfl, leftImage, rightImage⟩ := map_eq_pair argumentImages
  obtain ⟨leftLabel, leftArguments, rfl, leftLabelImage, leftImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp leftImage
  obtain rfl := (collapse_eq_iff (by decide) (by decide)).mp leftLabelImage
  obtain ⟨rightLabel, rightArguments, rfl, rightLabelImage, rightImages⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp rightImage
  obtain rfl := (collapse_eq_iff (by decide) (by decide)).mp rightLabelImage
  obtain ⟨first, rfl, firstImage⟩ := map_eq_single leftImages
  obtain ⟨second, rfl, secondImage⟩ := map_eq_single rightImages
  exact ⟨first, second, rfl, firstImage, secondImage⟩

/-- **A morphism of iGSLTs that is not injective on terms.**  The renaming
preserves steps, and every step of an image is the image of a step, so it
preserves bisimilarity. -/
def collapse : bare ⟶ bare where
  structural := collapseInteractive
  preservesBisim := by
    intro left right equivalent
    apply GSLT.bisimilar_map_of_zigzag (source := bare.toGSLT) (target := bare.toGSLT)
      (IGSLT.mapClosedTerm collapseInteractive) _ _ equivalent
    · intro source target step
      obtain ⟨first, second, sourceShape, targetShape⟩ := bare_step_iff.mp step
      apply bare_step_iff.mpr
      refine ⟨mapPattern collapseSymbols first, mapPattern collapseSymbols second, ?_, ?_⟩
      · show mapPattern collapseSymbols source.1 = _
        rw [sourceShape, collapse_join]
      · show mapPattern collapseSymbols target.1 = _
        rw [targetShape, collapse_contact]
    · intro source next step
      obtain ⟨first', second', imageShape, nextShape⟩ := bare_step_iff.mp step
      obtain ⟨first, second, sourceShape, rfl, rfl⟩ :=
        collapse_join_inv (pattern := source.1) imageShape
      have closed := source.2
      rw [sourceShape] at closed
      let reduct : barePresentation.Term := ⟨join first second, closed_reduct closed⟩
      refine ⟨reduct, ?_, ?_⟩
      · exact bare_step_iff.mpr ⟨first, second, sourceShape, rfl⟩
      · have same : IGSLT.mapClosedTerm (source := bare) (target := bare)
            collapseInteractive reduct = next := by
          apply Subtype.ext
          show mapPattern collapseSymbols (join first second) = next.1
          rw [collapse_contact, nextShape]
        rw [same]
        exact bare.toGSLT.bisimilar_refl next

/-- The two constants as closed terms. -/
def closedA : barePresentation.Term := ClosedTerm.ofCheck termA (by decide +kernel)

/-- The second constant. -/
def closedB : barePresentation.Term := ClosedTerm.ofCheck termB (by decide +kernel)

/-- The term action of the morphism is the renaming. -/
theorem collapse_mapTerm_val (term : barePresentation.Term) :
    (IGSLT.Morphism.mapTerm collapse term).1 = mapPattern collapseSymbols term.1 :=
  rfl

/-- The morphism identifies two distinct terms. -/
theorem collapse_identifies :
    closedA ≠ closedB ∧
      IGSLT.Morphism.mapTerm collapse closedA = IGSLT.Morphism.mapTerm collapse closedB := by
  constructor
  · intro same
    have patterns : termA = termB := congrArg Subtype.val same
    revert patterns
    decide
  · apply Subtype.ext
    rw [collapse_mapTerm_val, collapse_mapTerm_val]
    show mapPattern collapseSymbols termA = mapPattern collapseSymbols termB
    decide +kernel

/-- It is not the identity. -/
theorem collapse_ne_id : collapse ≠ 𝟙 bare := by
  intro same
  have symbols := congrArg
    (fun morphism : IGSLT.Morphism bare bare =>
      morphism.structural.structural.symbols.constructor "B") same
  revert symbols
  show ("A" : String) = "B" → False
  decide

/-! ## A structural map that is not a morphism -/

/-- One more rule: the constant `B` becomes the constant `A`. -/
def fireRule : RewriteRule where
  name := "Fire"
  typeContext := []
  premises := []
  left := termB
  right := termA

/-- The law-free theory with the extra rule. -/
def contactWithFire : LanguageDef :=
  { name := "Contact"
    types := ["Proc"]
    terms := terms
    equations := []
    rewrites := [syncRule, fireRule] }

theorem fireRule_validates :
    LanguageDef.validateRewrite contactWithFire fireRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [fireRule, contactWithFire, terms, termA, termB]

/-- The extended theory passes the declaration gate. -/
theorem contactWithFire_validate_eq_nil : contactWithFire.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    have cases : rewrite = syncRule ∨ rewrite = fireRule := by
      have listed : rewrite ∈ [syncRule, fireRule] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · rw [LanguageDef.validateRewrite_congr_signature (first := contactWithFire)
        (second := contactWith []) rfl rfl]
      exact syncRule_validates []
    · exact fireRule_validates

/-- The extended presentation selects the same sort, contact and rule. -/
def firePresentation : InteractivePresentation where
  presentation := ⟨contactWithFire, contactWithFire_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[7], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨syncRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

theorem fire_executionFlowErrors_eq_nil :
    contactWithFire.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    have cases : rule = syncRule ∨ rule = fireRule := by
      have listed : rule ∈ [syncRule, fireRule] := membership
      simpa using listed
    rcases cases with rfl | rfl <;> rfl
  · intro rule membership name nameMembership
    have cases : rule = syncRule ∨ rule = fireRule := by
      have listed : rule ∈ [syncRule, fireRule] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · simp [syncRule, join, Pattern.freeFvarNames] at nameMembership ⊢
      exact nameMembership
    · simp [fireRule, termA, Pattern.freeFvarNames] at nameMembership

/-- The extended theory as an iGSLT. -/
def fire : IGSLT where
  presentation := firePresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := contactWithFire
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            contactWithFire_validate_eq_nil fire_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- The inclusion: every declaration of the law-free theory is a declaration
of the extended one, and the selected sort, contact and rule are the same. -/
def inclusion : InteractiveMorphism barePresentation firePresentation where
  structural :=
    { symbols := LanguageDefSymbolMap.id
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
        cases membership
      mapsRewrites := by
        intro rewrite membership
        rw [mapRewriteRule_id]
        obtain rfl : rewrite = syncRule := List.mem_singleton.mp membership
        exact List.Mem.head _ }
  mapsInteractingSort := Subtype.ext (mapTypeDecl_id _)
  mapsContactConstructor := Subtype.ext (mapGrammarRule_id _)
  mapsInteractionRewrite := Subtype.ext (mapRewriteRule_id _)

/-- In the law-free theory neither constant moves, so they are bisimilar. -/
theorem bare_constants_bisimilar : bare.toGSLT.Bisimilar closedA closedB := by
  have stuckA : ∀ target, ¬ bare.toGSLT.Step closedA target := by
    intro target step
    obtain ⟨first, second, shape, -⟩ := bare_step_iff.mp step
    have shape' : termA = join (input first) (output second) := shape
    simp [termA, join] at shape'
  have stuckB : ∀ target, ¬ bare.toGSLT.Step closedB target := by
    intro target step
    obtain ⟨first, second, shape, -⟩ := bare_step_iff.mp step
    have shape' : termB = join (input first) (output second) := shape
    simp [termB, join] at shape'
  refine ⟨fun left right => left = closedA ∧ right = closedB, ⟨?_, ?_⟩, rfl, rfl⟩
  · rintro left right ⟨rfl, rfl⟩ next step
    exact absurd step (stuckA next)
  · rintro left right ⟨rfl, rfl⟩ next step
    exact absurd step (stuckB next)

/-- With no law, the static equivalence of the extended fibre is equality. -/
theorem fire_equivalent_iff_eq {left right : firePresentation.Term} :
    (presentedEquationSetoid defaultBasePremises firePresentation).r left right ↔
      left = right :=
  presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises firePresentation
    (by decide) left right

/-- In the extended theory `B` moves and `A` does not: they are not
bisimilar. -/
theorem fire_constants_not_bisimilar :
    ¬ fire.toGSLT.Bisimilar
      (IGSLT.mapClosedTerm (source := bare) (target := fire) inclusion closedA)
      (IGSLT.mapClosedTerm (source := bare) (target := fire) inclusion closedB) := by
  rintro ⟨relation, ⟨-, backward⟩, related⟩
  have moves : fire.toGSLT.Step
      (IGSLT.mapClosedTerm (source := bare) (target := fire) inclusion closedB)
      (IGSLT.mapClosedTerm (source := bare) (target := fire) inclusion closedA) := by
    apply primitiveStep_to_presentedStep (base := defaultBasePremises)
      (presentation := firePresentation)
    show Step defaultBasePremises contactWithFire
      (mapPattern LanguageDefSymbolMap.id termB) (mapPattern LanguageDefSymbolMap.id termA)
    rw [mapPattern_id, mapPattern_id]
    exact exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩
  obtain ⟨next, ⟨redex, contractum, sourceEquivalent, primitive, -⟩, -⟩ :=
    backward related moves
  obtain rfl := fire_equivalent_iff_eq.mp sourceEquivalent
  have primitive' : Step defaultBasePremises contactWithFire termA contractum.1 := by
    have unfolded : Step defaultBasePremises contactWithFire
        (mapPattern LanguageDefSymbolMap.id termA) contractum.1 := primitive
    rwa [mapPattern_id] at unfolded
  revert primitive'
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  have cases : rule = syncRule ∨ rule = fireRule := by
    have listed : rule ∈ [syncRule, fireRule] := membership
    simpa using listed
  rcases cases with rfl | rfl <;> decide +kernel

/-- **A structural map need not preserve behaviour.**  The inclusion carries
every declaration to a declaration and preserves the selected interaction
data, and no morphism of iGSLTs lies over it. -/
theorem inclusion_not_semantic :
    ¬ ∃ morphism : bare ⟶ fire, IGSLT.Morphism.structural morphism = inclusion := by
  rintro ⟨morphism, over⟩
  have preserved := morphism.preservesBisim bare_constants_bisimilar
  rw [over] at preserved
  exact fire_constants_not_bisimilar preserved

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
