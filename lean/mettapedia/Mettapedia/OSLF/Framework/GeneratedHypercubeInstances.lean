import Mettapedia.OSLF.Framework.GeneratedHypercube
import Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-!
# Generated slot families on authored presentations

Every statement here is computed from an authored rule by the generator of
`GeneratedHypercube` and checked by the kernel.  Three presentations are run:
the rho communication rule, the WM calculus core, and a weak commutative
monoid.  Together they are the positive and negative evidence that the
derivation has content — the same function returns a full cube on one
presentation and a two-element line on another, according to what the
equations of each say about its rely parameters.

## Two places where a generated family differs from an earlier hand-written one

`ModalHypercube` states slot families for these rules in prose and types their
admissibility by hand.  Running the generator disagrees with two of them, and in
opposite directions — one is a defect of the hand-written presentation, the
other a defect of the authored rule.

* `WM_RevisionComm` is stated there with rely parameters `{W1, W2}` and three
  slots.  Its left-hand side is `Revise(W1, W2)`, whose only proper redex
  positions are the two arguments; at either one the remaining argument is the
  sole rely parameter, so the generated family has **two** slots.  The generator
  is right and the hand-written presentation is a bug — the same module applies
  the correct recipe to `revision_assoc` two entries later.

* The rho communication modality is stated there with three slots, and the
  generator gives four.  **Here the generator is right and this tree's authored
  rule is wrong.**  The source material's context for this redex carries no
  parallel remainder, this tree already delegates parallel closure to a separate
  contextual rule, and the `rest` metavariable is not even declared in the
  rule's own type context — so the generator is minting a slot for an undeclared
  variable.  `rhoComm_relyVars_not_declared` below is that defect as a theorem
  rather than a remark.  Dropping `rest` from the communication rule yields the
  source's `{n, q}`, three slots, and a centre of eight; repairing the rule is a
  change to the shared rho presentation and is not made here.
-/

namespace Mettapedia.OSLF.Framework.GeneratedHypercubeInstances

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedHypercube
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-! ## The rho communication modality

The chosen redex position is the continuation of the input, which is the
position the Hypercube development selects. -/

/-- The continuation of the input in the rho communication redex. -/
def rhoCommPos : Position := [0, 1]

/-- The chosen subterm is the input's continuation. -/
theorem rhoComm_focus :
    subtermAt rhoCommRewrite.left rhoCommPos =
      some (.lambda none (.fvar "p")) := by rfl

/-- `W_j`: the continuation keeps its own body variable to itself. -/
theorem rhoComm_hiddenVars :
    hiddenVars rhoCommRewrite.left rhoCommPos = ["p"] := by rfl

/-- `V_j`: the channel, the transmitted process, and the parallel remainder. -/
theorem rhoComm_relyVars :
    relyVars rhoCommRewrite.left rhoCommPos = ["rest", "n", "q"] := by rfl

/-- Four slots: one per rely parameter and one output. -/
theorem rhoComm_slotCount :
    slotCount rhoCommRewrite.left rhoCommPos = 4 := by rfl

/-- `K_j[t_j] = L`: the position really is a one-hole context for the
continuation. -/
theorem rhoComm_plug :
    plug rhoCommRewrite.left rhoCommPos (.lambda none (.fvar "p")) =
      some rhoCommRewrite.left := by rfl

/-- The generated center of the rho communication modality. -/
def rhoCommCenter : Finset (Fin (slotCount rhoCommRewrite.left rhoCommPos) → HSort) :=
  derivedCenter firstProjection rhoCalc rhoCommRewrite rhoCommPos

/-- No equation of the presentation constrains these slots, so the whole cube
survives: `2^4` assignments. -/
theorem rhoComm_center_card : rhoCommCenter.card = 16 := by decide

/-- The rule does not declare every rely parameter this position produces: the
parallel remainder is a free metavariable of the left-hand side and is absent
from the rule's type context.  This is the defect that makes the family four
slots wide instead of the source's three. -/
theorem rhoComm_relyVars_not_declared :
    RelyVarsDeclared rhoCommRewrite rhoCommPos = false := by rfl

/-- The WM rule, by contrast, declares all of its. -/
theorem wmEvidenceAdd_relyVars_declared :
    RelyVarsDeclared ruleEvidenceAdd [0] = true := by rfl

/-- The Barendregt face: fix the channel and the parallel remainder at `*` and
let the transmitted process and the output vary.  These are the four corners of
the lambda cube's square.  Two slots have to be pinned rather than the source's
one, because of the extra slot `rhoComm_relyVars_not_declared` identifies. -/
def rhoComm_barendregtFace :
    Finset (Fin (slotCount rhoCommRewrite.left rhoCommPos) → HSort) :=
  rhoCommCenter.filter fun σ =>
    fixSlot (relyVars rhoCommRewrite.left rhoCommPos) "n" .star σ &&
      fixSlot (relyVars rhoCommRewrite.left rhoCommPos) "rest" .star σ

theorem rhoComm_barendregtFace_card : rhoComm_barendregtFace.card = 4 := by decide

/-! ## The gate: the source's communication rule and its two-slot square

The rule above is this tree's, and it carries a parallel remainder the source's
does not.  The source's rule is the same interaction with that remainder
dropped — parallel closure is `rhoParCongRewrite`'s job, and this tree already
has it — and every one of its metavariables is declared.  Running the same
generator on it, with nothing hand-written, gives the source's family. -/

/-- The source's communication rule: the same interaction, with the parallel
remainder delegated to the contextual rule rather than carried here.  It is the
tree's rule with the rest name removed from both sides, and that is the only
difference. -/
def rhoCommPaper : RewriteRule where
  name := "Comm"
  typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)]
  premises := []
  left := .collection .hashBag [
    .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
    .apply "POutput" [.fvar "n", .fvar "q"]
  ] none
  right := .collection .hashBag [
    .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])
  ] none

/-- It differs from this tree's rule in exactly the rest name. -/
theorem rhoCommPaper_is_rhoComm_without_rest :
    rhoCommPaper.typeContext = rhoCommRewrite.typeContext ∧
      rhoCommPaper.premises = rhoCommRewrite.premises ∧
      (∃ elements : List Pattern,
        rhoCommRewrite.left = .collection .hashBag elements (some "rest") ∧
          rhoCommPaper.left = .collection .hashBag elements none) ∧
      ∃ elements : List Pattern,
        rhoCommRewrite.right = .collection .hashBag elements (some "rest") ∧
          rhoCommPaper.right = .collection .hashBag elements none :=
  ⟨rfl, rfl,
    ⟨[.apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
      .apply "POutput" [.fvar "n", .fvar "q"]], rfl, rfl⟩,
    ⟨[.subst (.fvar "p") (.apply "NQuote" [.fvar "q"])], rfl, rfl⟩⟩

/-- The same redex position: the continuation of the input. -/
def rhoCommPaperPos : Position := [0, 1]

/-- And the same focus. -/
theorem rhoCommPaper_focus :
    subtermAt rhoCommPaper.left rhoCommPaperPos =
      some (.lambda none (.fvar "p")) := by rfl

/-- **The source's two rely parameters**, generated rather than written. -/
theorem rhoCommPaper_relyVars :
    relyVars rhoCommPaper.left rhoCommPaperPos = ["n", "q"] := by rfl

/-- The continuation is hidden by the redex, as the source has it. -/
theorem rhoCommPaper_hiddenVars :
    hiddenVars rhoCommPaper.left rhoCommPaperPos = ["p"] := by rfl

/-- Three slots: one per rely parameter and one output. -/
theorem rhoCommPaper_slotCount :
    slotCount rhoCommPaper.left rhoCommPaperPos = 3 := by rfl

/-- **And no slot is minted for an undeclared variable.**  This is the defect of
the tree's rule, absent here; the two theorems together locate it exactly. -/
theorem rhoCommPaper_relyVars_declared :
    RelyVarsDeclared rhoCommPaper rhoCommPaperPos = true := by rfl

/-- The generated centre of the source's rule. -/
def rhoCommPaperCenter :
    Finset (Fin (slotCount rhoCommPaper.left rhoCommPaperPos) → HSort) :=
  derivedCenter firstProjection rhoCalc rhoCommPaper rhoCommPaperPos

/-- The whole three-cube survives: rho's equations constrain none of these
slots, and the rule's right-hand side is a substitution the sort-level
interpretation does not read, so output agreement binds nothing either. -/
theorem rhoCommPaper_center_card : rhoCommPaperCenter.card = 8 := by decide

/-- The cube is the full assignment space, not a proper subset of it. -/
theorem rhoCommPaper_center_eq_univ : rhoCommPaperCenter = Finset.univ := by decide

/-- **The gate.**  Fixing the output slot cuts the generated cube to a square:
four corners, indexed by the two rely parameters.  This is Barendregt's cube
face, obtained from the authored rule by the generator with no slot and no rule
written by hand. -/
def rhoCommPaperSquare :
    Finset (Fin (slotCount rhoCommPaper.left rhoCommPaperPos) → HSort) :=
  rhoCommPaperCenter.filter fun σ =>
    σ (outputIndex (relyVars rhoCommPaper.left rhoCommPaperPos)) == .star

theorem rhoCommPaper_square_card : rhoCommPaperSquare.card = 4 := by decide

/-- The square is a face: it is cut out by one condition, on one slot. -/
theorem rhoCommPaper_square_is_face :
    rhoCommPaperSquare =
      Finset.univ.filter fun σ =>
        σ (outputIndex (relyVars rhoCommPaper.left rhoCommPaperPos)) == .star := by
  decide

/-- **What the spurious slot costs.**  On the tree's rule a square needs *two*
conditions, because the undeclared rest name has minted a slot that carries no
information; on the source's rule one condition suffices.  The two cardinalities
are equal and the two descriptions are not, which is the difference the defect
makes. -/
theorem rhoComm_square_needs_two_conditions :
    rhoComm_barendregtFace.card = 4 ∧ rhoCommPaperSquare.card = 4 ∧
      slotCount rhoCommRewrite.left rhoCommPos =
        slotCount rhoCommPaper.left rhoCommPaperPos + 1 :=
  ⟨rhoComm_barendregtFace_card, rhoCommPaper_square_card, rfl⟩

/-! ## The WM calculus core

`WM_EvidenceAdd` confirms the earlier hand-written family; `WM_RevisionComm`
does not. -/

/-- The revision argument of `Extract(Revise(W1, W2), q)`. -/
def wmEvidenceAddPos : Position := [0]

theorem wmEvidenceAdd_relyVars :
    relyVars ruleEvidenceAdd.left wmEvidenceAddPos = ["q"] := by rfl

/-- Two slots, agreeing with the hand-written `wmEvidenceAddPres`. -/
theorem wmEvidenceAdd_slotCount :
    slotCount ruleEvidenceAdd.left wmEvidenceAddPos = 2 := by rfl

theorem wmEvidenceAdd_center_card :
    (derivedCenter firstProjection wmCoreLanguageDef ruleEvidenceAdd
      wmEvidenceAddPos).card = 4 := by decide

/-- The generated family agrees with the hand-written presentation for this
rule, on both the slot count and the center. -/
theorem wmEvidenceAdd_matches_handwritten :
    slotCount ruleEvidenceAdd.left wmEvidenceAddPos = 2 ∧
      (derivedCenter firstProjection wmCoreLanguageDef ruleEvidenceAdd
        wmEvidenceAddPos).card = (equationalCenter wmEvidenceAddPres).card :=
  ⟨wmEvidenceAdd_slotCount, by decide⟩

/-- The first argument of `Revise(W1, W2)`. -/
def wmRevisionCommPos : Position := [0]

/-- At this position the second argument is the only rely parameter. -/
theorem wmRevisionComm_relyVars :
    relyVars ruleRevisionComm.left wmRevisionCommPos = ["W2"] := by rfl

/-- The other argument position is symmetric. -/
theorem wmRevisionComm_relyVars_right :
    relyVars ruleRevisionComm.left [1] = ["W1"] := by rfl

/-- Two slots, not the three the hand-written `wmRevisionCommPres` assumes. -/
theorem wmRevisionComm_slotCount :
    slotCount ruleRevisionComm.left wmRevisionCommPos = 2 := by rfl

/-- The refutation, stated as a disagreement of slot counts: the hand-written
presentation for this rule carries three slots, the rule generates two. -/
theorem wmRevisionComm_slotCount_ne_handwritten :
    slotCount ruleRevisionComm.left wmRevisionCommPos ≠ 3 := by decide

/-- Neither does the root position carry three slots: with the whole left-hand
side as the hole there is no context, hence no rely parameter at all. -/
theorem wmRevisionComm_root_slotCount :
    slotCount ruleRevisionComm.left [] = 1 := by rfl

/-! ## A theory whose equations do collapse the cube

The WM core declares no equations, so nothing above tests the equational half
of the derivation.  A weak commutative monoid does: commutativity is stated
over the very parameters that become slots, and a rule that discards its second
factor makes the output agree with the first.  Under the first-projection
interpretation this is the book's weak monoid, and the generator returns its
line. -/

/-- `Mul(x, y)`. -/
def pMul (x y : Pattern) : Pattern := .apply "Mul" [x, y]

/-- Commutativity of the product, stated over the parameters that become
slots. -/
def mulComm : Equation where
  name := "mul_comm"
  typeContext := [("q", .base "M"), ("r", .base "M")]
  premises := []
  left := pMul (.fvar "q") (.fvar "r")
  right := pMul (.fvar "r") (.fvar "q")

/-- `Mul(Mul(q, r), z) ⇝ Mul(q, r)`: the product of a product discards its
second factor, so the modality's output is the inner product. -/
def mulDiscard : RewriteRule where
  name := "mul_discard"
  typeContext := [("q", .base "M"), ("r", .base "M"), ("z", .base "M")]
  premises := []
  left := pMul (pMul (.fvar "q") (.fvar "r")) (.fvar "z")
  right := pMul (.fvar "q") (.fvar "r")

/-- A weak commutative monoid presentation. -/
def weakMonoidLang : LanguageDef where
  name := "WeakCommutativeMonoid"
  types := ["M"]
  terms := []
  equations := [mulComm]
  rewrites := [mulDiscard]

/-- The discarded factor: the hole sits beside a context mentioning both
factors of the inner product, so both are rely parameters. -/
def weakMonoidPos : Position := [1]

theorem weakMonoid_relyVars :
    relyVars mulDiscard.left weakMonoidPos = ["q", "r"] := by rfl

/-- Three slots: the two factors and the output — the book's weak monoid
family, obtained from the rule rather than assumed. -/
theorem weakMonoid_slotCount :
    slotCount mulDiscard.left weakMonoidPos = 3 := by rfl

/-- Commutativity forces the two factor slots to agree and output agreement
forces the output to follow them, so two of the eight assignments survive. -/
theorem weakMonoid_center_card :
    (derivedCenter firstProjection weakMonoidLang mulDiscard weakMonoidPos).card
      = 2 := by decide

/-- Without the equation, four of the eight assignments survive rather than two:
output agreement still forces the output slot to follow the first factor, so the
equation is responsible for exactly the further collapse from four to two. -/
theorem weakMonoid_center_card_without_equation :
    (derivedCenter firstProjection { weakMonoidLang with equations := [] }
      mulDiscard weakMonoidPos).card = 4 := by decide

/-! ## The collapse is a property of the equation, not of its spelling

Equations are instantiated at the slots in every possible way, so renaming an
equation's bound variables cannot change the center it produces.  Here is that
invariance on the worked example: the same law written over different variable
names collapses the cube identically, and neither spelling shares a variable
name with the other. -/

/-- Commutativity again, over variables sharing no name with the rely
parameters. -/
def mulCommRenamed : Equation where
  name := "mul_comm_renamed"
  typeContext := [("xx", .base "M"), ("yy", .base "M")]
  premises := []
  left := pMul (.fvar "xx") (.fvar "yy")
  right := pMul (.fvar "yy") (.fvar "xx")

/-- The same theory under the renamed law. -/
def weakMonoidLangRenamed : LanguageDef :=
  { weakMonoidLang with equations := [mulCommRenamed] }

/-- The rely parameters are `q` and `r`; the renamed law mentions neither. -/
theorem mulCommRenamed_shares_no_name :
    (equationVars mulCommRenamed).all
      (fun x => !(relyVars mulDiscard.left weakMonoidPos).contains x) = true := by
  rfl

/-- And the center is the same. -/
theorem weakMonoid_center_card_renamed :
    (derivedCenter firstProjection weakMonoidLangRenamed mulDiscard
      weakMonoidPos).card = 2 := by decide

/-- Stated as the invariance it is: renaming the law's bound variables leaves
the generated center alone, while removing the law does not. -/
theorem weakMonoid_center_alpha_invariant :
    (derivedCenter firstProjection weakMonoidLang mulDiscard weakMonoidPos).card =
      (derivedCenter firstProjection weakMonoidLangRenamed mulDiscard
        weakMonoidPos).card ∧
      (derivedCenter firstProjection weakMonoidLang mulDiscard weakMonoidPos).card ≠
        (derivedCenter firstProjection { weakMonoidLang with equations := [] }
          mulDiscard weakMonoidPos).card := by
  constructor
  · decide
  · decide

end Mettapedia.OSLF.Framework.GeneratedHypercubeInstances
