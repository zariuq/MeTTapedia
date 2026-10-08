import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy
import Mettapedia.CategoryTheory.FiniteActionTreeFinalSemantics

/-!
# Complete canonical COMM behaviour under parallel partners

Both states and labels are actual canonical bags of closed rho primes. Each
label supplies a complete parallel partner. Its finite successor set is the
image of all addressed COMM firings, not a selected firing or an approximation
of the target inventory. Addressed receipts retain duplicate occurrences
separately. The comparison uses the established equation-saturated public
COMM presentation; RUN and a free drop rule are not part of this behaviour.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCoalgebra

open _root_.CategoryTheory
open Mettapedia.CategoryTheory
open CanonicalBag CanonicalReaction CanonicalReactionOccurrences
open LanguageDefGSLT
open LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- The full addressed receipt for one supplied parallel partner. -/
abbrev Receipt (source partner : Bag) := Firing (append source partner)

def receipts (source partner : Bag) : Finset (Receipt source partner) :=
  @Finset.univ _ (Fintype.ofFinite _)

@[simp] theorem mem_receipts (source partner : Bag) (receipt : Receipt source partner) :
    receipt ∈ receipts source partner := by
  classical
  simp [receipts]

/-- The complete canonical target image, with only equal targets identified. -/
def successors (source partner : Bag) : Finset Bag :=
  FinitePowerset.map Firing.target (receipts source partner)

theorem mem_successors_iff_firing (source partner target : Bag) :
    target ∈ successors source partner ↔
      ∃ receipt : Receipt source partner, receipt.target = target := by
  simp only [successors, FinitePowerset.mem_map, mem_receipts, true_and]

theorem mem_successors_iff_reaction (source partner target : Bag) :
    target ∈ successors source partner ↔ Reaction (append source partner) target :=
  (mem_successors_iff_firing source partner target).trans
    (reaction_iff_firing (append source partner) target).symm

theorem receipt_member (source partner : Bag) (receipt : Receipt source partner) :
    receipt.target ∈ successors source partner :=
  (mem_successors_iff_firing source partner receipt.target).2 ⟨receipt, rfl⟩

/-- Outer parallel composition is exactly addition of canonical inventories. -/
theorem fromProcess_par (source partner : RhoProcess) :
    fromProcess (ParallelContextAdequacy.par source partner) =
      append (fromProcess source) (fromProcess partner) := by
  let closed : ∀ pattern ∈ [source.1, partner.1],
      RhoClosedTermWellSorted rhoProc pattern := by
    intro pattern member
    rcases List.mem_cons.mp member with rfl | member
    · exact source.2
    · have same := List.mem_singleton.mp member
      exact same ▸ partner.2
  have presentation : ParallelContextAdequacy.par source partner =
      ofList [source.1, partner.1] closed := Subtype.ext rfl
  apply Subtype.ext
  rw [presentation, fromProcess_ofList_inventory]
  change (Canonical.bagContents [Canonical.canonicalize source.1,
    Canonical.canonicalize partner.1] : Multiset _) =
      (fromProcess source).1 + (fromProcess partner).1
  rw [fromProcess_inventory, fromProcess_inventory]
  rw [show [Canonical.canonicalize source.1, Canonical.canonicalize partner.1] =
    [Canonical.canonicalize source.1] ++ [Canonical.canonicalize partner.1] from rfl,
    Canonical.bagContents_append, Multiset.coe_add]

/-- Every supplied raw target has exactly the public COMM membership criterion. -/
theorem mem_successors_iff_public (source partner target : RhoProcess) :
    fromProcess target ∈ successors (fromProcess source) (fromProcess partner) ↔
      rhoLanguageDefGSLT.Step (ParallelContextAdequacy.par source partner) target := by
  rw [mem_successors_iff_reaction, publicStep_iff, fromProcess_par]

theorem mem_successors_iff_canonical_public (source partner target : Bag) :
    target ∈ successors source partner ↔
      rhoLanguageDefGSLT.Step
        (ParallelContextAdequacy.par (toProcess source) (toProcess partner))
        (toProcess target) := by
  simpa only [fromProcess_toProcess] using
    mem_successors_iff_public (toProcess source) (toProcess partner) (toProcess target)

/-- The actual receipt retains its selected indices and its complete public endpoint. -/
theorem receipt_public (source partner : Bag) (receipt : Receipt source partner) :
    rhoLanguageDefGSLT.Step
      (ParallelContextAdequacy.par (toProcess source) (toProcess partner))
      (toProcess receipt.target) :=
  (mem_successors_iff_canonical_public source partner receipt.target).1
    (receipt_member source partner receipt)

theorem successors_equations {source source' partner partner' : RhoProcess}
    (sourceEquation : rhoProcessEquations.r source source')
    (partnerEquation : rhoProcessEquations.r partner partner') :
    successors (fromProcess source) (fromProcess partner) =
      successors (fromProcess source') (fromProcess partner') := by
  rw [(fromProcess_eq_iff source source').2 sourceEquation,
    (fromProcess_eq_iff partner partner').2 partnerEquation]

abbrev base := PUnit
abbrev index (_ : base) := PUnit
abbrev actions (_ : base) (_ : PUnit) := Bag

/-- Labelwise finite behaviour retains the arbitrary canonical partner alphabet. -/
abbrev behavior := FiniteActionTreeCofree.behavior.{0, 0, 0, 0} base index actions

def coalgebra : Endofunctor.Coalgebra behavior where
  V _ _ := Bag
  str _ _ := ↾successors

theorem coalgebra_readout (source partner : Bag) :
    coalgebra.str PUnit.unit PUnit.unit source partner = successors source partner := rfl

/-- Whole successor sets on the actual sorted equation quotient. -/
def quotientSuccessors (source partner : Quotient rhoProcessEquations) :
    Finset (Quotient rhoProcessEquations) :=
  FinitePowerset.map quotientEquiv.symm (successors (quotientEquiv source) (quotientEquiv partner))

theorem mem_quotientSuccessors (source partner target : Quotient rhoProcessEquations) :
    target ∈ quotientSuccessors source partner ↔
      quotientEquiv target ∈ successors (quotientEquiv source) (quotientEquiv partner) := by
  rw [quotientSuccessors, FinitePowerset.mem_map]
  constructor
  · rintro ⟨bag, member, same⟩
    have bagSame : bag = quotientEquiv target := by
      simpa only [Equiv.apply_symm_apply] using congrArg quotientEquiv same
    exact bagSame ▸ member
  · intro member
    exact ⟨quotientEquiv target, member, quotientEquiv.symm_apply_apply target⟩

/-- No representative choices remain in this quotient/public comparison. -/
theorem quotient_public_readout (source partner target : RhoProcess) :
    Quotient.mk rhoProcessEquations target ∈ quotientSuccessors
        (Quotient.mk rhoProcessEquations source) (Quotient.mk rhoProcessEquations partner) ↔
      rhoLanguageDefGSLT.Step (ParallelContextAdequacy.par source partner) target := by
  rw [mem_quotientSuccessors]
  exact mem_successors_iff_public source partner target

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCoalgebra
