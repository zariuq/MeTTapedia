import Mettapedia.GSLT.LanguageDef.Interaction.Freeness
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.EquationInvariant
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# Equations on a contact forge position

One signature, one interaction rule, and a varying list of equations.  The
contact is a binary constructor `Join`; the rule lets an input prefix and an
output prefix meet across it.  Each presentation below adds one law.

* With **associativity**, `Join(Join(A, B), C)` and `Join(A, Join(B, C))` are
  equal, and what stands to the left of the outer contact changes from
  `Join(A, B)` to `A`, which are not equal.
* With a **unit** law, `Join(Nil, A)` equals `A`: a contact appears and
  disappears around a term.
* With **idempotence**, `Join(A, A)` equals `A`: a neighbour is copied or
  deleted.
* With **associativity and commutativity**, `Join(A, B)` equals `Join(B, A)`,
  and `A` and `B` are not equal: the two sides of the contact are exchanged.

None of the terms involved can take a step, so in each case the change is
made by the equations alone.

Two further presentations locate the hypothesis of the rigidity theorem.  An
equation that never mentions `Join` but has a bare variable on one side wraps
any term, so a contact is equal to a term that is not a contact.  An equation
between closed terms headed by other constructors leaves every contact in
place while changing its operands.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-- The constructors: four constants, a wrapper, two prefixes and the
contact. -/
def terms : List GrammarRule := [
    { label := "A", category := "Proc", params := [], syntaxPattern := [] },
    { label := "B", category := "Proc", params := [], syntaxPattern := [] },
    { label := "C", category := "Proc", params := [], syntaxPattern := [] },
    { label := "Nil", category := "Proc", params := [], syntaxPattern := [] },
    { label := "Wrap", category := "Proc",
      params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] },
    { label := "In", category := "Proc",
      params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] },
    { label := "Out", category := "Proc",
      params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] },
    { label := "Join", category := "Proc",
      params := [.simple "left" (.base "Proc"), .simple "right" (.base "Proc")],
      syntaxPattern := [.nonTerminal "left", .nonTerminal "right"] }
  ]

/-- The contact of two terms. -/
def join (left right : Pattern) : Pattern := .apply "Join" [left, right]

/-- The constant `A`. -/
def termA : Pattern := .apply "A" []

/-- The constant `B`. -/
def termB : Pattern := .apply "B" []

/-- The constant `C`. -/
def termC : Pattern := .apply "C" []

/-- The constant `Nil`. -/
def termNil : Pattern := .apply "Nil" []

/-- A wrapped term. -/
def wrap (body : Pattern) : Pattern := .apply "Wrap" [body]

/-- The interaction rule: an input and an output meet across the contact. -/
def syncRule : RewriteRule where
  name := "Sync"
  typeContext := [("x", .base "Proc"), ("y", .base "Proc")]
  premises := []
  left := join (.apply "In" [.fvar "x"]) (.apply "Out" [.fvar "y"])
  right := join (.fvar "x") (.fvar "y")

/-- The presentation with a given list of laws. -/
def contactWith (laws : List Equation) : LanguageDef :=
  { name := "Contact"
    types := ["Proc"]
    terms := terms
    equations := laws
    rewrites := [syncRule] }

/-- `Join(Join(x, y), z) = Join(x, Join(y, z))`. -/
def assocLaw : Equation where
  name := "Assoc"
  typeContext := [("x", .base "Proc"), ("y", .base "Proc"), ("z", .base "Proc")]
  premises := []
  left := join (join (.fvar "x") (.fvar "y")) (.fvar "z")
  right := join (.fvar "x") (join (.fvar "y") (.fvar "z"))

/-- `Join(Nil, x) = x`. -/
def unitLaw : Equation where
  name := "Unit"
  typeContext := [("x", .base "Proc")]
  premises := []
  left := join termNil (.fvar "x")
  right := .fvar "x"

/-- `Join(x, x) = x`. -/
def idemLaw : Equation where
  name := "Idem"
  typeContext := [("x", .base "Proc")]
  premises := []
  left := join (.fvar "x") (.fvar "x")
  right := .fvar "x"

/-- `Join(x, y) = Join(y, x)`. -/
def commLaw : Equation where
  name := "Comm"
  typeContext := [("x", .base "Proc"), ("y", .base "Proc")]
  premises := []
  left := join (.fvar "x") (.fvar "y")
  right := join (.fvar "y") (.fvar "x")

/-- `Wrap(A) = B`: an equation between closed terms, away from the contact. -/
def wrapLaw : Equation where
  name := "WrapA"
  typeContext := []
  premises := []
  left := wrap termA
  right := termB

/-- `Wrap(x) = x`: an equation that never mentions the contact and has a bare
variable on one side. -/
def collapseLaw : Equation where
  name := "Collapse"
  typeContext := [("x", .base "Proc")]
  premises := []
  left := wrap (.fvar "x")
  right := .fvar "x"

/-- The laws used below. -/
def knownLaws : List Equation :=
  [assocLaw, unitLaw, idemLaw, commLaw, wrapLaw, collapseLaw]

/-! ## Validation -/

/-- Validation of a rule reads the signature only, which the laws do not
change. -/
theorem syncRule_validates (laws : List Equation) :
    LanguageDef.validateRewrite (contactWith laws) syncRule = [] := by
  rw [LanguageDef.validateRewrite_congr_signature (first := contactWith laws)
    (second := contactWith []) rfl rfl]
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [syncRule, contactWith, terms, join]

theorem knownLaws_validate (laws : List Equation) :
    ∀ law ∈ knownLaws, LanguageDef.validateEquation (contactWith laws) law = [] := by
  intro law membership
  rw [LanguageDef.validateEquation_congr_signature (first := contactWith laws)
    (second := contactWith []) rfl rfl]
  simp only [knownLaws, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [assocLaw, unitLaw, idemLaw, commLaw, wrapLaw, collapseLaw, contactWith,
          terms, join, wrap, termA, termB, termNil]

/-- Every presentation of the family with distinctly named known laws passes
the declaration gate. -/
theorem contactWith_validate_eq_nil (laws : List Equation)
    (names : (laws.map (·.name)).Nodup) (known : ∀ law ∈ laws, law ∈ knownLaws) :
    (contactWith laws).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  · show (["Proc"] : List String).Nodup
    decide
  · show (terms.map (·.label)).Nodup
    decide
  · exact names
  · show (["Sync"] : List String).Nodup
    decide
  · show ∀ term ∈ terms, term.category ∈ (["Proc"] : List String)
    decide
  · show ∀ term ∈ terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["Proc"] : List String)
    decide
  · show ∀ term ∈ terms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    decide +kernel
  · intro law membership
    exact knownLaws_validate laws law (known law membership)
  · intro rewrite membership
    obtain rfl : rewrite = syncRule := by simpa [contactWith] using membership
    exact syncRule_validates laws

/-- The interactive presentation of a member of the family: the sort of
processes, the contact `Join`, and the rule at which a prefix meets its dual. -/
def presentation (laws : List Equation)
    (names : (laws.map (·.name)).Nodup) (known : ∀ law ∈ laws, law ∈ knownLaws) :
    InteractivePresentation where
  presentation := ⟨contactWith laws, contactWith_validate_eq_nil laws names known⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[7], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨syncRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- Each member of the family is interactive. -/
theorem contactWith_isInteractive (laws : List Equation)
    (names : (laws.map (·.name)).Nodup) (known : ∀ law ∈ laws, law ∈ knownLaws) :
    IsInteractive (contactWith laws) :=
  (presentation laws names known).isInteractive (isBaseRewrite_of_premises_eq_nil rfl)

/-! ## Facts shared by the family -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- The signature has no collection and declares no collection algebra. -/
theorem contactWith_no_collections (laws : List Equation) :
    (contactWith laws).usesCollection .hashSet = false ∧
      (contactWith laws).hasAlgebraDeclarations = false := by
  constructor
  · show LanguageDef.usesCollection (contactWith []) .hashSet = false
    decide
  · show LanguageDef.hasAlgebraDeclarations (contactWith []) = false
    decide

/-- No constructor declares a unit, so every weight is admissible. -/
theorem contactWith_units (laws : List Equation) (weight : String → Nat) :
    ∀ rule ∈ (contactWith laws).terms, ∀ algebra, rule.algebra? = some algebra →
      ∀ unit, algebra.unit = some unit → weight unit = 0 := by
  intro rule membership algebra declared
  change rule ∈ terms at membership
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases declared

/-- A term built from constants, wrappers and contacts takes no step: the
rule needs an input prefix facing an output prefix at the root. -/
theorem no_step_of_no_match (laws : List Equation) {source : Pattern}
    (unmatched : matchPatternForRule (contactWith laws) syncRule source = [])
    (target : Pattern) : ¬ Step base (contactWith laws) source target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule membership
  obtain rfl : rule = syncRule := by simpa [contactWith] using membership
  exact unmatched

/-! ## Associativity re-brackets adjacency -/

/-- The associativity law, once. -/
theorem assoc_rebrackets :
    EquationEquiv base (contactWith [assocLaw])
      (join (join termA termB) termC) (join termA (join termB termC)) := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern assocLaw.left (join (join termA termB) termC),
        applyBindings bindings assocLaw.right = join termA (join termB termC) := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.forward (equation := assocLaw) (List.Mem.head _) matched
    (PremisesAt.nil bindings) applied⟩

/-- Associativity preserves the number of constructor occurrences. -/
theorem assoc_preserves_size {left right : Pattern}
    (equivalent : EquationEquiv base (contactWith [assocLaw]) left right) :
    left.weigh (fun _ => 1) = right.weigh (fun _ => 1) := by
  apply equationEquiv_weigh (fun _ => 1) _ (contactWith_no_collections _).1
    (contactWith_units _ _) _ equivalent
  · intro equation membership
    obtain rfl : equation = assocLaw := List.mem_singleton.mp membership
    exact ⟨rfl, by decide, by decide⟩
  · intro equation membership bindings
    obtain rfl : equation = assocLaw := List.mem_singleton.mp membership
    simp only [assocLaw, join, applyBindings, List.map_cons, List.map_nil, Pattern.weigh,
      Pattern.weighList]
    omega

/-- **Associativity changes what is adjacent.**  Two equal contacts whose left
operands are not equal. -/
theorem assoc_changes_adjacency :
    ∃ program environment program' environment' : Pattern,
      EquationEquiv base (contactWith [assocLaw])
          (join program environment) (join program' environment') ∧
        ¬ EquationEquiv base (contactWith [assocLaw]) program program' := by
  refine ⟨join termA termB, termC, termA, join termB termC, assoc_rebrackets, ?_⟩
  intro equivalent
  have sizes := assoc_preserves_size equivalent
  revert sizes
  decide

/-- Neither bracketing can take a step. -/
theorem assoc_no_cut_fires (target : Pattern) :
    ¬ Step base (contactWith [assocLaw]) (join (join termA termB) termC) target ∧
      ¬ Step base (contactWith [assocLaw]) (join termA (join termB termC)) target :=
  ⟨no_step_of_no_match _ (by decide +kernel) target,
    no_step_of_no_match _ (by decide +kernel) target⟩

/-! ## A unit law inserts and deletes neighbours -/

/-- The unit law, once. -/
theorem unit_deletes :
    EquationEquiv base (contactWith [unitLaw]) (join termNil termA) termA := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern unitLaw.left (join termNil termA),
        applyBindings bindings unitLaw.right = termA := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.forward (equation := unitLaw) (List.Mem.head _) matched
    (PremisesAt.nil bindings) applied⟩

/-- **A unit law forges a contact.**  A contact is equal to a term that is
not a contact. -/
theorem unit_forges_contact :
    ∃ program environment other : Pattern,
      EquationEquiv base (contactWith [unitLaw]) (join program environment) other ∧
        ∀ program' environment', other ≠ join program' environment' :=
  ⟨termNil, termA, termA, unit_deletes, by intro _ _ same; simp [termA, join] at same⟩

/-- Neither term can take a step. -/
theorem unit_no_cut_fires (target : Pattern) :
    ¬ Step base (contactWith [unitLaw]) (join termNil termA) target ∧
      ¬ Step base (contactWith [unitLaw]) termA target :=
  ⟨no_step_of_no_match _ (by decide +kernel) target,
    no_step_of_no_match _ (by decide +kernel) target⟩

/-! ## Idempotence copies neighbours -/

/-- The idempotence law, once. -/
theorem idem_deletes :
    EquationEquiv base (contactWith [idemLaw]) (join termA termA) termA := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern idemLaw.left (join termA termA),
        applyBindings bindings idemLaw.right = termA := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.forward (equation := idemLaw) (List.Mem.head _) matched
    (PremisesAt.nil bindings) applied⟩

/-- **Idempotence forges a contact.** -/
theorem idem_forges_contact :
    ∃ program environment other : Pattern,
      EquationEquiv base (contactWith [idemLaw]) (join program environment) other ∧
        ∀ program' environment', other ≠ join program' environment' :=
  ⟨termA, termA, termA, idem_deletes, by intro _ _ same; simp [termA, join] at same⟩

/-- Neither term can take a step. -/
theorem idem_no_cut_fires (target : Pattern) :
    ¬ Step base (contactWith [idemLaw]) (join termA termA) target ∧
      ¬ Step base (contactWith [idemLaw]) termA target :=
  ⟨no_step_of_no_match _ (by decide +kernel) target,
    no_step_of_no_match _ (by decide +kernel) target⟩

/-! ## Associativity with commutativity dissolves position -/

/-- The commutativity law, once. -/
theorem comm_swaps :
    EquationEquiv base (contactWith [assocLaw, commLaw])
      (join termA termB) (join termB termA) := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern commLaw.left (join termA termB),
        applyBindings bindings commLaw.right = join termB termA := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.forward (equation := commLaw)
    (List.Mem.tail _ (List.Mem.head _)) matched (PremisesAt.nil bindings) applied⟩

/-- The weight that counts occurrences of `A`. -/
def countA (label : String) : Nat := if label = "A" then 1 else 0

/-- Associativity and commutativity preserve the number of occurrences of
`A`. -/
theorem ac_preserves_countA {left right : Pattern}
    (equivalent : EquationEquiv base (contactWith [assocLaw, commLaw]) left right) :
    left.weigh countA = right.weigh countA := by
  apply equationEquiv_weigh countA _ (contactWith_no_collections _).1
    (contactWith_units _ _) _ equivalent
  · intro equation membership
    have cases : equation = assocLaw ∨ equation = commLaw := by
      have listed : equation ∈ [assocLaw, commLaw] := membership
      simpa using listed
    rcases cases with rfl | rfl <;> exact ⟨rfl, by decide, by decide⟩
  · intro equation membership bindings
    have cases : equation = assocLaw ∨ equation = commLaw := by
      have listed : equation ∈ [assocLaw, commLaw] := membership
      simpa using listed
    rcases cases with rfl | rfl <;>
      simp only [assocLaw, commLaw, join, applyBindings, List.map_cons, List.map_nil,
        Pattern.weigh, Pattern.weighList] <;>
      omega

/-- **Commutativity exchanges the two sides of the contact.**  Two equal
contacts whose left operands are not equal. -/
theorem ac_changes_adjacency :
    ∃ program environment program' environment' : Pattern,
      EquationEquiv base (contactWith [assocLaw, commLaw])
          (join program environment) (join program' environment') ∧
        ¬ EquationEquiv base (contactWith [assocLaw, commLaw]) program program' := by
  refine ⟨termA, termB, termB, termA, comm_swaps, ?_⟩
  intro equivalent
  have counts := ac_preserves_countA equivalent
  revert counts
  decide

/-- Neither order can take a step. -/
theorem ac_no_cut_fires (target : Pattern) :
    ¬ Step base (contactWith [assocLaw, commLaw]) (join termA termB) target ∧
      ¬ Step base (contactWith [assocLaw, commLaw]) (join termB termA) target :=
  ⟨no_step_of_no_match _ (by decide +kernel) target,
    no_step_of_no_match _ (by decide +kernel) target⟩

/-! ## Where the hypothesis of rigidity lies -/

/-- The presentation with the collapsing law. -/
def collapsePresentation : InteractivePresentation :=
  presentation [collapseLaw] (by decide) (by
    intro law membership
    obtain rfl := List.mem_singleton.mp membership
    simp [knownLaws])

/-- The collapsing law does not mention the contact: the presentation's
contact is free of authored equations in the sense of `ContactEquationFree`. -/
theorem collapse_contactEquationFree : ContactEquationFree collapsePresentation := by
  intro equation membership
  obtain rfl : equation = collapseLaw := List.mem_singleton.mp membership
  decide +kernel

/-- The collapsing law read from right to left wraps a contact. -/
theorem collapse_wraps :
    EquationEquiv base (contactWith [collapseLaw]) (join termA termB)
      (wrap (join termA termB)) := by
  apply equationInstance_equivalent
  obtain ⟨bindings, matched, applied⟩ :
      ∃ bindings ∈ matchPattern collapseLaw.right (join termA termB),
        applyBindings bindings collapseLaw.left = wrap (join termA termB) := by
    decide +kernel
  exact ⟨0, EquationInstanceAt.reverse (equation := collapseLaw) (List.Mem.head _) matched
    (PremisesAt.nil bindings) applied⟩

/-- **Absence of the contact from the equations is not rigidity.**  The
contact is free of authored equations, and a contact is still equal to a term
that is not a contact. -/
theorem collapse_forges_contact :
    ContactEquationFree collapsePresentation ∧
      ∃ program environment other : Pattern,
        EquationEquiv base (contactWith [collapseLaw]) (join program environment) other ∧
          ∀ program' environment', other ≠ join program' environment' :=
  ⟨collapse_contactEquationFree, termA, termB, wrap (join termA termB), collapse_wraps,
    by intro _ _ same; simp [wrap, join] at same⟩

/-- The presentation whose only law is an equation between closed terms headed
by other constructors. -/
def freePresentation : InteractivePresentation :=
  presentation [wrapLaw] (by decide) (by
    intro law membership
    obtain rfl := List.mem_singleton.mp membership
    simp [knownLaws])

/-- Its contact is rigid. -/
theorem free_rigidContact : freePresentation.RigidContact := by
  refine ⟨?_, by decide⟩
  intro equation membership
  obtain rfl : equation = wrapLaw := List.mem_singleton.mp membership
  exact ⟨⟨"Wrap", [termA], rfl, by decide⟩, ⟨"B", [], rfl, by decide⟩⟩

/-- The law acts beneath the contact. -/
theorem free_operand_changes :
    EquationEquiv base (contactWith [wrapLaw]) (join (wrap termA) termC)
      (join termB termC) := by
  have inner : EquationEquiv base (contactWith [wrapLaw]) (wrap termA) termB := by
    apply equationInstance_equivalent
    obtain ⟨bindings, matched, applied⟩ :
        ∃ bindings ∈ matchPattern wrapLaw.left (wrap termA),
          applyBindings bindings wrapLaw.right = termB := by
      decide +kernel
    exact ⟨0, EquationInstanceAt.forward (equation := wrapLaw) (List.Mem.head _) matched
      (PremisesAt.nil bindings) applied⟩
  exact equationEquiv_apply_of_forall₂ "Join"
    (.cons inner (.cons (Relation.EqvGen.refl _) .nil))

/-- **A free contact keeps its position.**  Whatever is equal to a contact in
this presentation is a contact of equal operands, side by side; the law above
shows the equivalence is not the identity. -/
theorem free_position_invariant {program environment other : Pattern}
    (equivalent : EquationEquiv base (contactWith [wrapLaw]) (join program environment)
      other) :
    ∃ program' environment', other = join program' environment' ∧
      EquationEquiv base (contactWith [wrapLaw]) program program' ∧
        EquationEquiv base (contactWith [wrapLaw]) environment environment' :=
  equationEquiv_binary_of_headed free_rigidContact.1 free_rigidContact.2 equivalent

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
