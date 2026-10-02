import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Hosting
import Mettapedia.OSLF.Framework.PredFiniteSufficient

/-!
# Preserving reduction bisimilarity is not enough

A morphism of iGSLTs is a map of declarations that preserves the
bisimilarity of reduction on the closed interacting carrier.  A morphism of
theories preserves what every probe sees.  The second does not follow from
the first.

The witness adds two constants `X`, `Y` and three rules to the law-free
contact theory:

* `Join(In(A), Out(y)) ⟶ X` and `Join(In(B), Out(y)) ⟶ Y`: a further way
  for an input of `A`, or of `B`, to meet an output;
* `Join(X, Nil) ⟶ Nil`: only `X` can be read.

The inclusion of the contact theory preserves reduction bisimilarity.  In the
contact theory a term has at most one reduct, and the new reducts of the
image of a term appear only at its last step, where the reduct is stuck, so
the image of a term reduces exactly as long as the term does.

The inclusion does not preserve what the full probe sees.  `A` and `B` are
bisimilar over all contexts of the contact theory.  Under the image of the
context `Join(In([-]), Out(Nil))` the image of `A` reaches `X`, and the image
of `B` reaches `Y` or `Join(B, Nil)`; under the image of `Join([-], Nil)`,
`X` moves and neither of the other two does.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## The extended theory -/

/-- The constant `X`. -/
def termX : Pattern := .apply "X" []

/-- The constant `Y`. -/
def termY : Pattern := .apply "Y" []

/-- The declarations of the two new constants. -/
def markDeclarations : List GrammarRule := [
    { label := "X", category := "Proc", params := [], syntaxPattern := [] },
    { label := "Y", category := "Proc", params := [], syntaxPattern := [] }
  ]

/-- `Join(In(A), Out(y)) ⟶ X`. -/
def markARule : RewriteRule where
  name := "MarkA"
  typeContext := [("y", .base "Proc")]
  premises := []
  left := join (.apply "In" [termA]) (.apply "Out" [.fvar "y"])
  right := termX

/-- `Join(In(B), Out(y)) ⟶ Y`. -/
def markBRule : RewriteRule where
  name := "MarkB"
  typeContext := [("y", .base "Proc")]
  premises := []
  left := join (.apply "In" [termB]) (.apply "Out" [.fvar "y"])
  right := termY

/-- `Join(X, Nil) ⟶ Nil`. -/
def readRule : RewriteRule where
  name := "Read"
  typeContext := []
  premises := []
  left := join termX termNil
  right := termNil

/-- The contact theory with the marks and the rule that reads one of them. -/
def markingLanguage : LanguageDef :=
  { name := "Marking"
    types := ["Proc"]
    terms := terms ++ markDeclarations
    equations := []
    rewrites := [syncRule, markARule, markBRule, readRule] }

theorem marking_rules (rule : RewriteRule) (membership : rule ∈ markingLanguage.rewrites) :
    rule = syncRule ∨ rule = markARule ∨ rule = markBRule ∨ rule = readRule := by
  have listed : rule ∈ [syncRule, markARule, markBRule, readRule] := membership
  simpa using listed

theorem marking_rules_validate :
    ∀ rewrite ∈ markingLanguage.rewrites,
      LanguageDef.validateRewrite markingLanguage rewrite = [] := by
  intro rewrite membership
  rcases marking_rules rewrite membership with rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [syncRule, markARule, markBRule, readRule, markingLanguage, terms,
          markDeclarations, join, termA, termB, termX, termY, termNil]

theorem marking_validate_eq_nil : markingLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · exact marking_rules_validate

/-- The extended presentation selects the same sort, contact and rule. -/
def markingPresentation : InteractivePresentation where
  presentation := ⟨markingLanguage, marking_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[7], List.mem_append_left _ (List.getElem_mem (by decide))⟩
  interactionRewrite := ⟨syncRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

theorem marking_executionFlowErrors_eq_nil : markingLanguage.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    rcases marking_rules rule membership with rfl | rfl | rfl | rfl <;> rfl
  · intro rule membership name nameMembership
    rcases marking_rules rule membership with rfl | rfl | rfl | rfl
    · simp [syncRule, join, Pattern.freeFvarNames] at nameMembership ⊢
      exact nameMembership
    · simp [markARule, termX, Pattern.freeFvarNames] at nameMembership
    · simp [markBRule, termY, Pattern.freeFvarNames] at nameMembership
    · simp [readRule, termNil, Pattern.freeFvarNames] at nameMembership

/-- The extended theory as an iGSLT. -/
def marking : IGSLT where
  presentation := markingPresentation
  baseInteraction := isBaseRewrite_of_premises_eq_nil rfl
  executionProfile :=
    { relationModes := []
      admitted :=
        { lang := markingLanguage
          admitted := LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes _
            marking_validate_eq_nil marking_executionFlowErrors_eq_nil }
      exactLanguage := rfl }

/-- The inclusion of the contact theory. -/
def toMarkingInteractive : InteractiveMorphism barePresentation markingPresentation where
  structural :=
    { symbols := LanguageDefSymbolMap.id
      mapsTypes := by
        intro declaration membership
        rw [mapTypeDecl_id]
        exact membership
      mapsTerms := by
        intro rule membership
        rw [mapGrammarRule_id]
        exact List.mem_append_left _ membership
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

/-! ## The reductions of the extended theory -/

theorem marking_plainRules : PlainRules markingLanguage := by
  intro rule membership
  rcases marking_rules rule membership with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by decide +kernel⟩

/-- **The reductions of the extended theory.** -/
theorem marking_step_iff {source target : Pattern} :
    Step base markingLanguage source target ↔
      (∃ first second, source = join (input first) (output second) ∧
        target = join first second) ∨
      (∃ second, source = join (input termA) (output second) ∧ target = termX) ∨
      (∃ second, source = join (input termB) (output second) ∧ target = termY) ∨
      (source = join termX termNil ∧ target = termNil) := by
  constructor
  · intro step
    obtain ⟨rule, membership, bindings, rfl, rfl⟩ :=
      sides_of_step marking_plainRules (by
        intro rule membership
        rcases marking_rules rule membership with rfl | rfl | rfl | rfl <;> decide) step
    rcases marking_rules rule membership with rfl | rfl | rfl | rfl
    · exact .inl ⟨applyBindings bindings (.fvar "x"), applyBindings bindings (.fvar "y"),
        by simp [syncRule, join, input, output, applyBindings],
        by simp [syncRule, join, applyBindings]⟩
    · exact .inr (.inl ⟨applyBindings bindings (.fvar "y"),
        by simp [markARule, join, input, output, termA, applyBindings],
        by simp [markARule, termX, applyBindings]⟩)
    · exact .inr (.inr (.inl ⟨applyBindings bindings (.fvar "y"),
        by simp [markBRule, join, input, output, termB, applyBindings],
        by simp [markBRule, termY, applyBindings]⟩))
    · exact .inr (.inr (.inr ⟨by simp [readRule, join, termX, termNil, applyBindings],
        by simp [readRule, termNil, applyBindings]⟩))
  · rintro (⟨first, second, rfl, rfl⟩ | ⟨second, rfl, rfl⟩ | ⟨second, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨bindings, matched, applied⟩ := sync_matches first second
      exact (step_iff_exists_match marking_plainRules).mpr
        ⟨syncRule, List.Mem.head _, bindings, matched, applied⟩
    · obtain ⟨bindings, matched, -⟩ :=
        matchPattern_applyBindings_complete (pat := markARule.left) (bs := [("y", second)])
          (by decide)
      refine (step_iff_exists_match marking_plainRules).mpr
        ⟨markARule, List.Mem.tail _ (List.Mem.head _), bindings, ?_, ?_⟩
      · simpa [markARule, join, input, output, termA, applyBindings] using matched
      · simp [markARule, termX, applyBindings]
    · obtain ⟨bindings, matched, -⟩ :=
        matchPattern_applyBindings_complete (pat := markBRule.left) (bs := [("y", second)])
          (by decide)
      refine (step_iff_exists_match marking_plainRules).mpr
        ⟨markBRule, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), bindings, ?_, ?_⟩
      · simpa [markBRule, join, input, output, termB, applyBindings] using matched
      · simp [markBRule, termY, applyBindings]
    · exact (step_iff_exists_match marking_plainRules).mpr
        ⟨readRule, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          by decide +kernel⟩

theorem marking_equationFree : markingLanguage.isEquationFree = true := by decide

/-- The reductions of the iGSLT are the reductions of the patterns. -/
theorem marking_toGSLT_step_iff {source target : markingPresentation.Term} :
    marking.toGSLT.Step source target ↔ Step base markingLanguage source.1 target.1 := by
  have equal : ∀ {left right : markingPresentation.Term},
      (presentedEquationSetoid defaultBasePremises markingPresentation).r left right ↔
        left = right := fun {left right} =>
    presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises markingPresentation
      (by decide) left right
  constructor
  · rintro ⟨redex, contractum, sourceEquivalent, primitive, targetEquivalent⟩
    obtain rfl := equal.mp sourceEquivalent
    obtain rfl := equal.mp targetEquivalent
    exact primitive
  · intro primitive
    exact primitiveStep_to_presentedStep (base := defaultBasePremises)
      (presentation := markingPresentation) primitive

/-! ## The inclusion preserves reduction bisimilarity -/

/-- The image of a closed term of the contact theory. -/
abbrev image (term : barePresentation.Term) : markingPresentation.Term :=
  IGSLT.mapClosedTerm (source := bare) (target := marking) toMarkingInteractive term

theorem image_val (term : barePresentation.Term) : (image term).1 = term.1 :=
  mapPattern_id term.1

/-- A term of the contact theory does not mention `X`. -/
theorem bare_ne_read (term : barePresentation.Term) : term.1 ≠ join termX termNil := by
  intro shape
  have typed := term.2.1
  rw [shape] at typed
  obtain ⟨rule, ruleMember, ruleLabel, -, -, arguments⟩ := typed.apply_inv
  have ruleIsJoin : rule = terms[7] := by
    change rule ∈ terms at ruleMember
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ruleMember
    rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd ruleLabel (by decide)
  subst ruleIsJoin
  obtain ⟨markTyped, -⟩ := arguments.simple_cons_inv
  obtain ⟨markRule, markMember, markLabel, -⟩ := markTyped.apply_inv
  change markRule ∈ terms at markMember
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at markMember
  rcases markMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd markLabel (by decide)

/-- A reduction of the contact theory is a reduction of the image. -/
theorem image_step {source target : barePresentation.Term}
    (step : bare.toGSLT.Step source target) : marking.toGSLT.Step (image source) (image target) := by
  obtain ⟨first, second, sourceShape, targetShape⟩ := bare_step_iff.mp step
  apply marking_toGSLT_step_iff.mpr
  rw [image_val, image_val]
  exact marking_step_iff.mpr (.inl ⟨first, second, sourceShape, targetShape⟩)

/-- The image of a term that cannot move cannot move. -/
theorem image_stuck {term : barePresentation.Term}
    (stuck : ∀ next, ¬ bare.toGSLT.Step term next) (next : markingPresentation.Term) :
    ¬ marking.toGSLT.Step (image term) next := by
  intro step
  have raw := marking_toGSLT_step_iff.mp step
  rw [image_val] at raw
  have moves : ∀ first second, term.1 = join (input first) (output second) → False := by
    intro first second shape
    have closed := term.2
    rw [shape] at closed
    exact stuck ⟨join first second, closed_reduct closed⟩
      (bare_step_iff.mpr ⟨first, second, shape, rfl⟩)
  rcases marking_step_iff.mp raw with
    ⟨first, second, shape, -⟩ | ⟨second, shape, -⟩ | ⟨second, shape, -⟩ | ⟨shape, -⟩
  · exact moves first second shape
  · exact moves termA second shape
  · exact moves termB second shape
  · exact bare_ne_read term shape

/-- A term that is `X` or `Y` cannot move. -/
theorem mark_stuck {term : markingPresentation.Term} (mark : term.1 = termX ∨ term.1 = termY)
    (next : markingPresentation.Term) : ¬ marking.toGSLT.Step term next := by
  intro step
  have raw := marking_toGSLT_step_iff.mp step
  rcases mark with shape | shape <;> rw [shape] at raw <;>
    rcases marking_step_iff.mp raw with
      ⟨first, second, bad, -⟩ | ⟨second, bad, -⟩ | ⟨second, bad, -⟩ | ⟨bad, -⟩ <;>
    simp [termX, termY, join] at bad

/-- A contact whose left operand is a constant cannot move in the contact
theory. -/
theorem constant_contact_stuck {term : barePresentation.Term} {second : Pattern}
    (shape : term.1 = join termA second ∨ term.1 = join termB second)
    (next : barePresentation.Term) : ¬ bare.toGSLT.Step term next := by
  intro step
  obtain ⟨first', second', moved, -⟩ := bare_step_iff.mp step
  rcases shape with shape | shape <;> rw [shape] at moved <;>
    simp [join, input, termA, termB] at moved

/-- One reduction of the image of a term is answered by the image of a term
bisimilar to it: by an image, or by a term that cannot move. -/
theorem image_forward {left right : barePresentation.Term}
    (related : bare.toGSLT.Bisimilar left right) {next : markingPresentation.Term}
    (step : marking.toGSLT.Step (image left) next) :
    ∃ answer, marking.toGSLT.Step (image right) answer ∧
      ((∃ a b, next = image a ∧ answer = image b ∧ bare.toGSLT.Bisimilar a b) ∨
        ((∀ after, ¬ marking.toGSLT.Step next after) ∧
          ∀ after, ¬ marking.toGSLT.Step answer after)) := by
  obtain ⟨relation, ⟨forward, backward⟩, pair⟩ := related
  have raw := marking_toGSLT_step_iff.mp step
  rw [image_val] at raw
  have last : ∀ (operand second : Pattern),
      left.1 = join (input operand) (output second) →
      (operand = termA ∨ operand = termB) → (next.1 = termX ∨ next.1 = termY) →
      ∃ answer, marking.toGSLT.Step (image right) answer ∧
        ((∃ a b, next = image a ∧ answer = image b ∧ bare.toGSLT.Bisimilar a b) ∨
          ((∀ after, ¬ marking.toGSLT.Step next after) ∧
            ∀ after, ¬ marking.toGSLT.Step answer after)) := by
    intro operand second shape constant mark
    have closed := left.2
    rw [shape] at closed
    let reduct : barePresentation.Term := ⟨join operand second, closed_reduct closed⟩
    have reductStuck : ∀ after, ¬ bare.toGSLT.Step reduct after :=
      constant_contact_stuck (term := reduct) (second := second)
        (constant.elim
          (fun isA => .inl (show join operand second = join termA second by rw [isA]))
          (fun isB => .inr (show join operand second = join termB second by rw [isB])))
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward pair (bare_step_iff.mpr ⟨operand, second, shape, rfl⟩ : bare.toGSLT.Step left reduct)
    have matchedStuck : ∀ after, ¬ bare.toGSLT.Step matched after := by
      intro after moves
      obtain ⟨before, beforeStep, -⟩ := backward matchedRelated moves
      exact reductStuck before beforeStep
    exact ⟨image matched, image_step matchedStep,
      .inr ⟨mark_stuck mark, image_stuck matchedStuck⟩⟩
  rcases marking_step_iff.mp raw with
    ⟨first, second, shape, nextShape⟩ | ⟨second, shape, nextShape⟩ |
      ⟨second, shape, nextShape⟩ | ⟨shape, -⟩
  · have closed := left.2
    rw [shape] at closed
    let reduct : barePresentation.Term := ⟨join first second, closed_reduct closed⟩
    obtain ⟨matched, matchedStep, matchedRelated⟩ :=
      forward pair (bare_step_iff.mpr ⟨first, second, shape, rfl⟩ : bare.toGSLT.Step left reduct)
    refine ⟨image matched, image_step matchedStep,
      .inl ⟨reduct, matched, ?_, rfl, relation, ⟨forward, backward⟩, matchedRelated⟩⟩
    apply Subtype.ext
    rw [image_val]
    exact nextShape
  · exact last termA second shape (.inl rfl) (.inl nextShape)
  · exact last termB second shape (.inr rfl) (.inr nextShape)
  · exact absurd shape (bare_ne_read left)

/-- **The inclusion is a morphism of iGSLTs**: it preserves reduction
bisimilarity. -/
def toMarking : bare ⟶ marking where
  structural := toMarkingInteractive
  preservesBisim := by
    intro left right bisimilar
    refine ⟨fun first second =>
      (∃ a b, first = image a ∧ second = image b ∧ bare.toGSLT.Bisimilar a b) ∨
        ((∀ after, ¬ marking.toGSLT.Step first after) ∧
          ∀ after, ¬ marking.toGSLT.Step second after),
      ⟨?_, ?_⟩, .inl ⟨left, right, rfl, rfl, bisimilar⟩⟩
    · rintro first second (⟨a, b, rfl, rfl, related⟩ | ⟨stuck, -⟩) next step
      · exact image_forward related step
      · exact absurd step (stuck next)
    · rintro first second (⟨a, b, rfl, rfl, related⟩ | ⟨-, stuck⟩) next step
      · obtain ⟨answer, answerStep, answerRelated⟩ :=
          image_forward (bare.toGSLT.bisimilar_symm related) step
        refine ⟨answer, answerStep, ?_⟩
        rcases answerRelated with ⟨c, d, rfl, rfl, both⟩ | ⟨nextStuck, answerStuck⟩
        · exact .inl ⟨d, c, rfl, rfl, bare.toGSLT.bisimilar_symm both⟩
        · exact .inr ⟨answerStuck, nextStuck⟩
      · exact absurd step (stuck next)

/-! ## The inclusion does not preserve what the full probe sees -/

/-- The validated extended presentation. -/
abbrev markingValidated : ValidatedLanguageDef := markingPresentation.presentation

/-- The map of declarations of the inclusion. -/
abbrev toMarkingStructural : StructuralMorphism bareValidated markingValidated :=
  toMarkingInteractive.structural

/-- The inclusion as a map of theories. -/
def toMarkingMap :
    ContextMap (contextTheory base bareValidated) (contextTheory base markingValidated) :=
  structuralContextMap base toMarkingStructural
    (preservesEquations_of_equationFree base toMarkingStructural bare_equationFree)

theorem bare_typed_nil :
    HasType (contactWith []) FreeTypeContext.empty [] termNil (.base "Proc") :=
  .constructor (rule := terms[3]) (List.getElem_mem (by decide))
    (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil

/-- The context `Join(In([-]), Out(Nil))`. -/
def prefixContext : OneHoleContext :=
  .apply "Join" [] (.apply "In" [] .hole []) [output termNil]

/-- It is a label of the contact theory. -/
def prefixLabel : (contextTheory base bareValidated).Label proc proc :=
  labelOfOccurrence (presentation := bareValidated) (source := proc) (target := proc)
    prefixContext (label := "Nil") (arguments := [])
    (TypedAt.application (rule := terms[7]) (beforeParams := [])
      (afterParams := [.simple "right" (.base "Proc")])
      (parameter := .simple "left" (.base "Proc"))
      (List.getElem_mem (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl
        (HasType.constructor (rule := terms[5]) (List.getElem_mem (by decide))
          (by rintro ⟨name, kind, element, shape⟩; cases shape)
          (.cons trivial rfl bare_typed_nil .nil))
        (.cons trivial rfl
          (HasType.constructor (rule := terms[6]) (List.getElem_mem (by decide))
            (by rintro ⟨name, kind, element, shape⟩; cases shape)
            (.cons trivial rfl bare_typed_nil .nil)) .nil))
      rfl rfl rfl
      (TypedAt.application (rule := terms[5]) (beforeParams := []) (afterParams := [])
        (parameter := .simple "body" (.base "Proc"))
        (List.getElem_mem (by decide))
        (by rintro ⟨name, kind, element, shape⟩; cases shape)
        (.cons trivial rfl bare_typed_nil .nil) rfl rfl rfl (.here bare_typed_nil)))
    (by decide +kernel) (by decide +kernel)

/-- The context `Join([-], Nil)`. -/
def contactContext : OneHoleContext := .apply "Join" [] .hole [termNil]

/-- It is a label of the contact theory. -/
def contactLabel : (contextTheory base bareValidated).Label proc proc :=
  labelOfOccurrence (presentation := bareValidated) (source := proc) (target := proc)
    contactContext (label := "Nil") (arguments := [])
    (TypedAt.application (rule := terms[7]) (beforeParams := [])
      (afterParams := [.simple "right" (.base "Proc")])
      (parameter := .simple "left" (.base "Proc"))
      (List.getElem_mem (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl bare_typed_nil (.cons trivial rfl bare_typed_nil .nil))
      rfl rfl rfl (.here bare_typed_nil))
    (by decide +kernel) (by decide +kernel)

/-- The interface of closed processes of the extended theory, as an image. -/
abbrev markingProc : Interface := proc.map toMarkingStructural.symbols

/-- `X` as a term of the extended theory. -/
def markX : Term markingValidated.language markingProc :=
  ofClosed (presentation := markingValidated)
    (ClosedTerm.ofCheck (sort := markingPresentation.interactingLangSort) termX
      (by decide +kernel))

/-- `Nil` as a term of the extended theory. -/
def markNil : Term markingValidated.language markingProc :=
  ofClosed (presentation := markingValidated)
    (ClosedTerm.ofCheck (sort := markingPresentation.interactingLangSort) termNil
      (by decide +kernel))

/-- The reductions of the extended theory at an interface. -/
theorem marking_termStep_iff {interface : Interface}
    {term next : Term markingValidated.language interface} :
    TermStep base markingValidated.language term next ↔
      Step base markingLanguage term.1 next.1 :=
  termStep_iff_step base _ marking_equationFree term next

/-- Under the image of a label of the contact theory, a term of the extended
theory is plugged into the same one-hole context. -/
theorem apply_image_label (label : (contextTheory base bareValidated).Label proc proc)
    {context : OneHoleContext} (shape : label.shape = MultiHoleContext.ofOneHole context)
    (term : Term markingValidated.language markingProc) :
    ((contextTheory base markingValidated).apply (toMarkingMap.context label) term).1 =
      context.fill term.1 :=
  (apply_map_label base toMarkingStructural label shape term).trans
    (congrArg (fun mapped => mapped.fill term.1) (CIGSLT.mapOneHoleContext_id context))

/-- A transition labelled by the image of a label of the contact theory is a
reduction of the plugged term. -/
theorem transition_image_iff (label : (contextTheory base bareValidated).Label proc proc)
    {context : OneHoleContext} (shape : label.shape = MultiHoleContext.ofOneHole context)
    (term next : Term markingValidated.language markingProc) :
    (contextTheory base markingValidated).Transition term (toMarkingMap.context label) next ↔
      Step base markingLanguage (context.fill term.1) next.1 := by
  constructor
  · intro transition
    exact apply_image_label label shape term ▸ marking_termStep_iff.mp transition
  · intro raw
    apply marking_termStep_iff.mpr
    exact (apply_image_label label shape term).symm ▸ raw

/-- **Over the images of the contexts of the contact theory, the images of
the two constants are separated.** -/
theorem images_not_bisimilar_over_image :
    ¬ (toMarkingMap.push (contextTheory base bareValidated).fullProbe).Bisimilar (index := proc)
      (toMarkingMap.term constantA) (toMarkingMap.term constantB) := by
  rintro ⟨relation, ⟨forward, -⟩, related⟩
  have marks : (contextTheory base markingValidated).Transition (toMarkingMap.term constantA)
      (toMarkingMap.context prefixLabel) markX :=
    (transition_image_iff prefixLabel rfl (toMarkingMap.term constantA) markX).mpr
      (marking_step_iff.mpr (.inr (.inl ⟨termNil, by
        change prefixContext.fill (mapPattern LanguageDefSymbolMap.id termA) = _
        rw [mapPattern_id]
        rfl, rfl⟩)))
  obtain ⟨answer, answerStep, answerRelated⟩ := forward related (target := proc) prefixLabel marks
  have answerRaw : Step base markingLanguage (join (input termB) (output termNil)) answer.1 := by
    have raw := (transition_image_iff prefixLabel rfl (toMarkingMap.term constantB) answer).mp
      answerStep
    change Step base markingLanguage
      (prefixContext.fill (mapPattern LanguageDefSymbolMap.id termB)) answer.1 at raw
    rw [mapPattern_id] at raw
    exact raw
  have reads : (contextTheory base markingValidated).Transition markX
      (toMarkingMap.context contactLabel) markNil :=
    (transition_image_iff contactLabel rfl markX markNil).mpr
      (marking_step_iff.mpr (.inr (.inr (.inr ⟨rfl, rfl⟩))))
  obtain ⟨final, finalStep, -⟩ := forward answerRelated (target := proc) contactLabel reads
  have finalRaw : Step base markingLanguage (join answer.1 termNil) final.1 :=
    (transition_image_iff contactLabel rfl answer final).mp finalStep
  have answerShape : answer.1 = join termB termNil ∨ answer.1 = termY := by
    rcases marking_step_iff.mp answerRaw with
      ⟨first, second, shape, target⟩ | ⟨second, shape, -⟩ | ⟨second, -, target⟩ | ⟨shape, -⟩
    · have operands : termB = first ∧ termNil = second := by
        simpa [join, input, output] using shape
      rw [← operands.1, ← operands.2] at target
      exact .inl target
    · simp [join, input, output, termA, termB] at shape
    · exact .inr target
    · simp [join, input, output, termX, termB] at shape
  rcases answerShape with shape | shape <;> rw [shape] at finalRaw <;>
    rcases marking_step_iff.mp finalRaw with
      ⟨first, second, bad, -⟩ | ⟨second, bad, -⟩ | ⟨second, bad, -⟩ | ⟨bad, -⟩ <;>
    simp [join, input, output, termA, termB, termX, termY, termNil] at bad

/-- The inclusion is faithful on contexts because it is injective on terms. -/
theorem toMarking_faithful : toMarkingMap.Faithful := by
  apply (ContextMap.faithful_iff_reflectsEquations _).mpr
  intro origin first second equivalent
  have same := (termSetoid_iff_eq base _ marking_equationFree _ _).mp equivalent
  have patterns : first.1 = second.1 := by
    have raw : mapPattern LanguageDefSymbolMap.id first.1 =
        mapPattern LanguageDefSymbolMap.id second.1 := congrArg Subtype.val same
    simpa using raw
  have equal : first = second := Subtype.ext patterns
  rw [equal]

/-- Faithfulness does not imply backward transition lifting.  The inclusion is faithful, and
the image of `A` has, under the image of a context of the contact theory, a
transition that is the image of no transition of `A`. -/
theorem faithfulness_does_not_reflect :
    toMarkingMap.Faithful ∧ ¬ toMarkingMap.ReflectsTransitions := by
  refine ⟨toMarking_faithful, fun reflects => ?_⟩
  have marks : (contextTheory base markingValidated).Transition (toMarkingMap.term constantA)
      (toMarkingMap.context prefixLabel) markX :=
    (transition_image_iff prefixLabel rfl (toMarkingMap.term constantA) markX).mpr
      (marking_step_iff.mpr (.inr (.inl ⟨termNil, by
        change prefixContext.fill (mapPattern LanguageDefSymbolMap.id termA) = _
        rw [mapPattern_id]
        rfl, rfl⟩)))
  obtain ⟨next, sourceStep, equivalent⟩ := reflects prefixLabel marks
  have same := (termSetoid_iff_eq base _ marking_equationFree _ _).mp equivalent
  have nextShape : next.1 = termX := by
    have raw : termX = mapPattern LanguageDefSymbolMap.id next.1 := congrArg Subtype.val same
    rw [mapPattern_id] at raw
    exact raw.symm
  obtain ⟨first, second, -, reduct⟩ := (bare_termStep_iff).mp sourceStep
  have absurdShape : termX = join first second := nextShape.symm.trans reduct
  simp [termX, join] at absurdShape

/-- The marking inclusion is not hosting: it adds a transition under an
image context that cannot be lifted to the source. -/
theorem toMarking_not_hosting : ¬ toMarkingMap.Hosting :=
  fun hosting => faithfulness_does_not_reflect.2 hosting.reflects

/-- **Preserving reduction bisimilarity does not make a map of declarations
a morphism of theories.**  The inclusion is a morphism of iGSLTs; the two
constants are bisimilar over all contexts of the contact theory; and their
images are not bisimilar over the images of those contexts. -/
theorem reduction_bisimilarity_insufficient :
    (∃ morphism : bare ⟶ marking, IGSLT.Morphism.structural morphism = toMarkingInteractive) ∧
    (contextTheory base bareValidated).fullProbe.Bisimilar (index := proc) constantA constantB ∧
    ¬ (toMarkingMap.push (contextTheory base bareValidated).fullProbe).Bisimilar (index := proc)
      (toMarkingMap.term constantA) (toMarkingMap.term constantB) :=
  ⟨⟨toMarking, rfl⟩, constants_bisimilar, images_not_bisimilar_over_image⟩

/-- No morphism of theories lies over the inclusion. -/
theorem toMarking_not_contextMorphism :
    ¬ ∃ morphism : ContextMorphism (contextTheory base bareValidated)
        (contextTheory base markingValidated), morphism.toContextMap = toMarkingMap := by
  rintro ⟨morphism, same⟩
  have preserved := morphism.preserves_full constants_bisimilar
  rw [same] at preserved
  exact images_not_bisimilar_over_image preserved

end Mettapedia.GSLT.LanguageDef.Contexts.Controls
