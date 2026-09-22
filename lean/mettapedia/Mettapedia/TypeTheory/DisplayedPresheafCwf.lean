import Mettapedia.TypeTheory.DisplayedPresheafComprehension
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualTypeReindexing

/-!
# A proof-relevant CwF of displayed presheaf families

Contexts are presheaves on one fixed syntax category. A type over a context
is a proof-relevant functor on its category of elements; a term is a natural
section. Context extension is the existing total presheaf, and substitution
is natural base change. This packages the existing constructions together
with their context-comprehension laws. It does not add dependent products,
identity elimination, universes, or authored Prime judgments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafCwf

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

universe uContext vContext uBase uIndex vIndex uEvidence

variable {Context : Type uContext} [Category.{vContext} Context]

/-- Casting a natural section along equality of displayed families does
not replace the evidence at any contextual point. -/
theorem sectionCast_value_heq
    {Index : Type uIndex} [Category.{vIndex} Index]
    {first second : Index ⥤ Type uEvidence}
    (same : first = second) (sectionValue : first.sections)
    (point : Index) :
    HEq ((same ▸ sectionValue).val point) (sectionValue.val point) := by
  cases same
  rfl

private theorem displayedMap_heq
    {base : Face.{uContext, vContext, uBase} Context}
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} base)
    {source target otherTarget : base.Elements}
    (sameTarget : target = otherTarget)
    (first : source ⟶ target) (second : source ⟶ otherTarget)
    (sameArrow : HEq first.val second.val) (evidence : family.obj source) :
    HEq (family.map first evidence) (family.map second evidence) := by
  cases sameTarget
  have same : first = second := Subtype.ext (eq_of_heq sameArrow)
  cases same
  rfl

/-- The canonical dependent last variable of a displayed total context. -/
def presheafVariable {base : Face.{uContext, vContext, uBase} Context}
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} base) :
    (reindexDisplayed (totalProjection family) family).sections where
  val point := point.2.2
  property := by
    intro source target arrow
    rcases arrow with ⟨substitution, follows⟩
    rcases source with ⟨sourceContext, ⟨sourceValue, evidence⟩⟩
    rcases target with ⟨targetContext, ⟨targetValue, targetEvidence⟩⟩
    change totalMap family substitution ⟨sourceValue, evidence⟩ =
      ⟨targetValue, targetEvidence⟩ at follows
    have firstEq : base.map substitution sourceValue = targetValue :=
      congrArg Sigma.fst follows
    have targetEq :
        (⟨targetContext, base.map substitution sourceValue⟩ : base.Elements) =
          ⟨targetContext, targetValue⟩ :=
      congrArg (fun value => (⟨targetContext, value⟩ : base.Elements)) firstEq
    have transported := displayedMap_heq family targetEq
      (CategoryOfElements.homMk _ _ substitution rfl)
      ((totalProjection family).mapElements.map ⟨substitution, follows⟩)
      (heq_of_eq rfl) evidence
    exact eq_of_heq (transported.symm.trans (Sigma.mk.inj follows).2)

/-- Pair a natural context map and a dependent term into the proof-bearing
total context, without choosing or truncating the term evidence. -/
def presheafPair
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (term : (reindexDisplayed substitution family).sections) :
    source ⟶ totalSpace family :=
  sectionLift (reindexDisplayed substitution family) term ≫
    totalReindexMap substitution family

/-- Pairing followed by weakening recovers the original natural context
map, including its action at every syntax context. -/
theorem presheafPair_weaken
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (term : (reindexDisplayed substitution family).sections) :
    presheafPair substitution family term ≫ totalProjection family =
      substitution := by
  rw [presheafPair, Category.assoc, totalReindexMap_square]
  rw [← Category.assoc, sectionLift_projection]
  simp

/-- The proof-relevant displayed presheaf families form a terminal-free CwF
over the category of presheaf contexts on one fixed syntax category. -/
def presheafCwf (Context : Type uContext) [Category.{vContext} Context] : Cwf where
  Ctx := Face.{uContext, vContext, uBase} Context
  Sub source target := source ⟶ target
  idS _ := 𝟙 _
  compS later earlier := earlier ≫ later
  id_comp _ := by simp
  comp_id _ := by simp
  comp_assoc _ _ _ := by simp [Category.assoc]
  Ty base := DisplayedFamily.{uContext, vContext, uBase, uBase} base
  tySub family substitution := reindexDisplayed substitution family
  tySub_id family := reindexDisplayed_id family
  tySub_comp family later earlier := reindexDisplayed_comp later family earlier
  Tm _ family := family.sections
  tmSub term substitution := reindexDisplayedSection substitution _ term
  tmSub_id term := by rfl
  tmSub_comp term later earlier := by
    rfl
  ext _ family := totalSpace family
  wk family := totalProjection family
  vz family := presheafVariable family
  pair substitution family term := presheafPair substitution family term
  wk_pair substitution family term := presheafPair_weaken substitution family term
  vz_pair substitution family term := by
    rfl
  pair_eta family substitution := by
    rfl

/-- A dependent family pulled back along a chosen section commutes with
base change. This is an equality of displayed families, including their
transport on contextual arrows, not only an objectwise value equation. -/
theorem dependentSectionBaseChangeFamily
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (codomain : DisplayedFamily.{uContext, vContext, uBase, uBase}
      (totalSpace domain))
    (first : domain.sections) :
    reindexDisplayed substitution
        (reindexDisplayed (sectionLift domain first) codomain) =
      reindexDisplayed
        (sectionLift (reindexDisplayed substitution domain)
          (reindexDisplayedSection substitution domain first))
        (reindexDisplayed (totalReindexMap substitution domain) codomain) := by
  calc
    _ = reindexDisplayed
        (substitution ≫ sectionLift domain first) codomain :=
      (reindexDisplayed_comp (change := sectionLift domain first)
        (originalFamily := codomain) substitution).symm
    _ = reindexDisplayed
        (sectionLift (reindexDisplayed substitution domain)
          (reindexDisplayedSection substitution domain first) ≫
          totalReindexMap substitution domain) codomain := by
      rw [reindexDisplayedSection_lift]
    _ = _ :=
      reindexDisplayed_comp
        (change := totalReindexMap substitution domain)
        (originalFamily := codomain)
        (sectionLift (reindexDisplayed substitution domain)
          (reindexDisplayedSection substitution domain first))

/-- Reindex an existing dependent witness along a presheaf-context map.
The second section is precomposed and transported across the proved
family equality; it is never regenerated by search or choice. -/
def reindexDependentSection
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (codomain : DisplayedFamily.{uContext, vContext, uBase, uBase}
      (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    (reindexDisplayed
      (sectionLift (reindexDisplayed substitution domain)
        (reindexDisplayedSection substitution domain first))
      (reindexDisplayed (totalReindexMap substitution domain) codomain)).sections :=
  (dependentSectionBaseChangeFamily substitution domain codomain first) ▸
    reindexDisplayedSection substitution _ second

/-- The canonical second witness remains the original section after
precomposition, modulo only its dependent-family transport. -/
theorem reindexDependentSection_heq
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (codomain : DisplayedFamily.{uContext, vContext, uBase, uBase}
      (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    HEq (reindexDisplayedSection substitution _ second)
      (reindexDependentSection substitution domain codomain first second) := by
  simp only [reindexDependentSection]
  exact HEq.rfl

/-- At every contextual point the transported dependent witness retains
the precomposed section's evidence, up to its indexed type cast. -/
theorem reindexDependentSection_value_heq
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{uContext, vContext, uBase, uBase} target)
    (codomain : DisplayedFamily.{uContext, vContext, uBase, uBase}
      (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections)
    (point : source.Elements) :
    HEq ((reindexDependentSection substitution domain codomain first second).val point)
      ((reindexDisplayedSection substitution _ second).val point) := by
  have cast := sectionCast_value_heq
    (dependentSectionBaseChangeFamily substitution domain codomain first)
    (reindexDisplayedSection substitution _ second) point
  simpa only [reindexDependentSection] using cast

/-- The constant singleton presheaf is the empty context of this semantic
CwF. It is not an empty carrier: every context has exactly one map to it. -/
def terminalFace (Context : Type uContext) [Category.{vContext} Context] :
    Face.{uContext, vContext, uBase} Context :=
  (Functor.const (Contextᵒᵖ)).obj PUnit

/-- A full semantic CwF, including the terminal context. -/
def presheafCwfWithTerminal (Context : Type uContext)
    [Category.{vContext} Context] : CwfWithTerminal where
  toCwf := presheafCwf Context
  empty := terminalFace Context
  toEmpty _ := {
    app _ := TypeCat.ofHom fun _ => PUnit.unit
    naturality := by intros; rfl }
  toEmpty_unique := by
    intro base substitution
    dsimp [presheafCwf, terminalFace] at base substitution ⊢
    apply NatTrans.ext
    funext context
    apply ConcreteCategory.hom_ext
    intro value
    cases substitution.app context value
    rfl

/-- The generic CwF substitution lift is the concrete evidence-retaining
base-change map of the displayed-presheaf construction. -/
theorem extensionSubstitution_eq_totalReindexMap
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} target) :
    TypeOver.extensionSubstitution
        (C := presheafCwf Context) substitution family =
      totalReindexMap substitution family := by
  rfl

/-- CwF context extension is cartesian under every natural substitution
of presheaf contexts, with proof-relevant witnesses retained. -/
theorem presheafCwf_extension_isPullback
    {source target : Face.{uContext, vContext, uBase} Context}
    (substitution : source ⟶ target)
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} target) :
    IsPullback
      ((presheafCwf Context).wk ((presheafCwf Context).tySub family substitution))
      (TypeOver.extensionSubstitution
        (C := presheafCwf Context) substitution family)
      substitution ((presheafCwf Context).wk family) := by
  rw [extensionSubstitution_eq_totalReindexMap]
  exact totalReindexMap_isPullback substitution family

/-- Weakening forgets only the evidence coordinate: two genuinely distinct
proofs can have the same base value without becoming equal in the CwF. -/
theorem weakening_forgets_distinct_evidence
    {base : Face.{uContext, vContext, uBase} Context}
    (family : DisplayedFamily.{uContext, vContext, uBase, uBase} base)
    (context : Contextᵒᵖ) (value : base.obj context)
    (first second : family.obj ⟨context, value⟩)
    (different : first ≠ second) :
    ((presheafCwf Context).wk family).app context
        (⟨value, first⟩ : (totalSpace family).obj context) =
      ((presheafCwf Context).wk family).app context
        (⟨value, second⟩ : (totalSpace family).obj context) ∧
      (⟨value, first⟩ : (totalSpace family).obj context) ≠
        ⟨value, second⟩ := by
  constructor
  · rfl
  · intro same
    exact different (eq_of_heq (Sigma.mk.inj same).2)

/-- The one-object base context for the Boolean evidence control. -/
def boolBase : Face.{0, 0, 0} (Discrete PUnit.{1}) :=
  terminalFace (Discrete PUnit.{1})

/-- A genuinely two-valued displayed family over the one-object base. -/
def boolFamily : DisplayedFamily.{0, 0, 0, 0} boolBase :=
  (Functor.const boolBase.Elements).obj Bool

/-- The inhabited syntax context of the Boolean evidence control. -/
def boolContext : (Discrete PUnit.{1})ᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- A natural section selecting the true evidence at every base point. -/
def boolTrueTerm : boolFamily.sections where
  val _ := true
  property := by
    change ∀ {source target : boolBase.Elements} (arrow : source ⟶ target),
      boolFamily.map arrow true = true
    intro source target arrow
    rfl

/-- Concrete positive control: pairing a section with the identity context
map produces the receipt carrying that section's actual Boolean evidence. -/
theorem bool_pair_carries_evidence :
    ((presheafCwf (Discrete PUnit.{1})).pair (𝟙 boolBase) boolFamily
        boolTrueTerm).app boolContext PUnit.unit =
      (⟨PUnit.unit, true⟩ : (totalSpace boolFamily).obj boolContext) := by
  rfl

/-- Concrete negative control: Boolean proof receipts remain distinct under
the semantic context extension although weakening observes the same base. -/
theorem bool_evidence_not_collapsed :
    ((presheafCwf (Discrete PUnit.{1})).wk boolFamily).app boolContext
        (⟨PUnit.unit, true⟩ : (totalSpace boolFamily).obj boolContext) =
      ((presheafCwf (Discrete PUnit.{1})).wk boolFamily).app boolContext
        (⟨PUnit.unit, false⟩ : (totalSpace boolFamily).obj boolContext) ∧
      (⟨PUnit.unit, true⟩ : (totalSpace boolFamily).obj boolContext) ≠
        ⟨PUnit.unit, false⟩ := by
  exact weakening_forgets_distinct_evidence boolFamily boolContext
    PUnit.unit (true : Bool) (false : Bool)
    (show (true : Bool) ≠ false from by decide)

#print axioms presheafVariable
#print axioms presheafPair
#print axioms presheafPair_weaken
#print axioms presheafCwf
#print axioms dependentSectionBaseChangeFamily
#print axioms reindexDependentSection_heq
#print axioms sectionCast_value_heq
#print axioms reindexDependentSection_value_heq
#print axioms presheafCwfWithTerminal
#print axioms extensionSubstitution_eq_totalReindexMap
#print axioms presheafCwf_extension_isPullback
#print axioms bool_pair_carries_evidence
#print axioms bool_evidence_not_collapsed

end Mettapedia.TypeTheory.DisplayedPresheafCwf
