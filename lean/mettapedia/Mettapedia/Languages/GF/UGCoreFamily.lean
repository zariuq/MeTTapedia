import Mettapedia.Languages.GF.UGCoreSelected
import Mettapedia.Languages.GF.WorldModelSemantics

/-!
# Family-Indexed UG Core

Strengthens the selected-core story in three ways:

1. family-indexed cores over collections of selected signatures;
2. monotonicity/refinement under family enlargement;
3. a formal trivialization criterion, plus a concrete nontrivial English/Czech
   witness for the currently selected invariant package.
-/

namespace Mettapedia.Languages.GF.UGCoreFamily

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.UGCoreSelected
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel

universe u v

/-! ## 1. Family-indexed selected cores -/

/-- Family-indexed selected-core equality: trees agree at every member
signature in the family. -/
def UGFamilyCoreEq {ι : Type u} (fam : ι → UGSignature)
    (t₁ t₂ : AbstractNode) : Prop :=
  ∀ i, UGCoreEq (fam i) t₁ t₂

theorem UGFamilyCoreEq.refl {ι : Type u} (fam : ι → UGSignature) (t : AbstractNode) :
    UGFamilyCoreEq fam t t := by
  intro i
  exact UGCoreEq.refl _ _

theorem UGFamilyCoreEq.symm {ι : Type u} (fam : ι → UGSignature)
    {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq fam t₁ t₂ → UGFamilyCoreEq fam t₂ t₁ := by
  intro h i
  exact UGCoreEq.symm _ (h i)

theorem UGFamilyCoreEq.trans {ι : Type u} (fam : ι → UGSignature)
    {t₁ t₂ t₃ : AbstractNode} :
    UGFamilyCoreEq fam t₁ t₂ → UGFamilyCoreEq fam t₂ t₃ → UGFamilyCoreEq fam t₁ t₃ := by
  intro h12 h23 i
  exact UGCoreEq.trans _ (h12 i) (h23 i)

/-- Setoid induced by a family of selected signatures. -/
def ugFamilySetoid {ι : Type u} (fam : ι → UGSignature) : Setoid AbstractNode where
  r := UGFamilyCoreEq fam
  iseqv := by
    constructor
    · exact UGFamilyCoreEq.refl fam
    · exact UGFamilyCoreEq.symm fam
    · exact UGFamilyCoreEq.trans fam

/-- `small` is a subfamily of `large` if every member signature of `small`
appears in `large`. -/
def IsSubfamily {ι : Type u} {κ : Type v}
    (small : ι → UGSignature) (large : κ → UGSignature) : Prop :=
  ∀ i, ∃ j, small i = large j

/-- Enlarging the family refines the family-indexed core relation. -/
theorem UGFamilyCoreEq.of_subfamily {ι : Type u} {κ : Type v}
    {small : ι → UGSignature} {large : κ → UGSignature}
    (hSub : IsSubfamily small large)
    {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq large t₁ t₂ → UGFamilyCoreEq small t₁ t₂ := by
  intro hLarge i
  rcases hSub i with ⟨j, hEq⟩
  simpa [hEq] using hLarge j

/-- Canonical quotient map from a larger-family core quotient to a
smaller-family core quotient. This is the precise refinement direction
supported by the family-indexed construction. -/
def quotientMap_of_subfamily {ι : Type u} {κ : Type v}
    {small : ι → UGSignature} {large : κ → UGSignature}
    (hSub : IsSubfamily small large) :
    Quotient (ugFamilySetoid large) → Quotient (ugFamilySetoid small) :=
  Quotient.lift
    (fun t => Quotient.mk (ugFamilySetoid small) t)
    (by
      intro t₁ t₂ hEq
      exact Quotient.sound (UGFamilyCoreEq.of_subfamily hSub hEq))

theorem quotientMap_of_subfamily_surjective {ι : Type u} {κ : Type v}
    {small : ι → UGSignature} {large : κ → UGSignature}
    (hSub : IsSubfamily small large) :
    Function.Surjective (quotientMap_of_subfamily hSub) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro t
  exact ⟨Quotient.mk (ugFamilySetoid large) t, rfl⟩

/-- Family obtained by adjoining a duplicate of an existing member. -/
def duplicateMemberFamily {ι : Type u}
    (fam : ι → UGSignature) (i₀ : ι) : Option ι → UGSignature
  | none => fam i₀
  | some i => fam i

/-- Adjoining a duplicate member does not change the family-indexed core
relation. This is the clean counterexample to any theorem claiming that family
growth must strictly refine the selected-family core. -/
theorem UGFamilyCoreEq_duplicateMemberFamily_iff
    {ι : Type u} (fam : ι → UGSignature) (i₀ : ι)
    {t₁ t₂ : AbstractNode} :
    UGFamilyCoreEq (duplicateMemberFamily fam i₀) t₁ t₂ ↔
      UGFamilyCoreEq fam t₁ t₂ := by
  constructor
  · intro hDup i
    exact hDup (some i)
  · intro hFam oi
    cases oi with
    | none => exact hFam i₀
    | some i => exact hFam i

/-- Quotient-level corollary: adjoining a duplicate member yields the same
family core quotient up to extensional equality of the underlying relation. -/
theorem duplicateMemberFamily_not_strict_refinement
    {ι : Type u} (fam : ι → UGSignature) (i₀ : ι) :
    ∀ t₁ t₂,
      UGFamilyCoreEq (duplicateMemberFamily fam i₀) t₁ t₂ ↔
        UGFamilyCoreEq fam t₁ t₂ := by
  intro t₁ t₂
  exact UGFamilyCoreEq_duplicateMemberFamily_iff fam i₀

/-! ## 2. Separation and trivialization criteria -/

theorem not_UGCoreEq_of_label_separates
    (sig : UGSignature) (ℓ : sig.Label) {t₁ t₂ : AbstractNode}
    (hSep : sig.observe ℓ t₁ ≠ sig.observe ℓ t₂) :
    ¬ UGCoreEq sig t₁ t₂ := by
  intro hEq
  exact hSep (hEq ℓ)

theorem not_UGFamilyCoreEq_of_member_label_separates
    {ι : Type u} (fam : ι → UGSignature) (i : ι) (ℓ : (fam i).Label)
    {t₁ t₂ : AbstractNode}
    (hSep : (fam i).observe ℓ t₁ ≠ (fam i).observe ℓ t₂) :
    ¬ UGFamilyCoreEq fam t₁ t₂ := by
  intro hEq
  exact hSep ((hEq i) ℓ)

/-- If the family core trivializes completely, then every selected observation
in every family member is constant across abstract trees. -/
theorem family_core_total_implies_selected_observation_constant
    {ι : Type u} (fam : ι → UGSignature)
    (hTotal : ∀ t₁ t₂, UGFamilyCoreEq fam t₁ t₂)
    (i : ι) (ℓ : (fam i).Label) (t₁ t₂ : AbstractNode) :
    (fam i).observe ℓ t₁ = (fam i).observe ℓ t₂ :=
  (hTotal t₁ t₂ i) ℓ

/-- Formal refutation criterion: if some selected observation in the family
genuinely distinguishes two trees, then the family core cannot be total. -/
theorem Strong_UG_fails_if_family_core_trivializes
    {ι : Type u} (fam : ι → UGSignature)
    (hSep : ∃ i, ∃ ℓ : (fam i).Label, ∃ t₁ t₂,
      (fam i).observe ℓ t₁ ≠ (fam i).observe ℓ t₂) :
    ¬ (∀ t₁ t₂, UGFamilyCoreEq fam t₁ t₂) := by
  intro hTotal
  rcases hSep with ⟨i, ℓ, t₁, t₂, hNe⟩
  exact hNe (family_core_total_implies_selected_observation_constant fam hTotal i ℓ t₁ t₂)

/-! ## 3. Concrete English/Czech selected-core nontriviality -/

abbrev useNHouseTree : AbstractNode :=
  AbstractNode.apply FunctionSig.UseN [AbstractNode.leaf "house" (.base "N")]

abbrev bareHouseTree : AbstractNode :=
  AbstractNode.leaf "house" (.base "N")

/-- `UseN(p)` reduces to `p` in the English GF language surface as well. -/
private theorem english_langReduces_UseN (p : Pattern) :
    langReduces englishGFLanguageDef (.apply "UseN" [p]) p := by
  unfold langReduces langReducesUsing
  exact .topRule useNElimRewrite
    (by simp [englishGFLanguageDef, gfRGLLanguageDef, allIdentityRewrites, allSemanticRewrites])
    [("x", p)]
    (by simp [useNElimRewrite, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
      Mettapedia.OSLF.MeTTaIL.Match.matchArgs, BEq.beq, List.length,
      Mettapedia.OSLF.MeTTaIL.Match.mergeBindings, List.filterMap])
    [("x", p)]
    (by simp [useNElimRewrite, applyPremisesWithEnv])
    (by simp [useNElimRewrite, Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
      List.find?, BEq.beq])

theorem english_useNHouse_dia_is_house :
    sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
      (.dia (.atom "is_house")) (gfAbstractToPattern useNHouseTree) := by
  refine ⟨.fvar "house", ?_, ?_⟩
  · simpa [gfAbstractToPattern, FunctionSig.UseN] using
      (english_langReduces_UseN (.fvar "house"))
  · simp [gfAtomSem_isName, sem]

theorem english_bareHouse_not_dia_is_house :
    ¬ sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
      (.dia (.atom "is_house")) (gfAbstractToPattern bareHouseTree) := by
  intro h
  rcases h with ⟨q, hR, _⟩
  have hExec := (langReducesUsing_iff_execUsing RelationEnv.empty
    englishGFLanguageDef (gfAbstractToPattern bareHouseTree) q).1 hR
  simp [bareHouseTree, langReducesExecUsing,
    rewriteWithContextWithPremisesUsing, rewriteStepWithPremisesUsing,
    RelationEnv.empty, englishGFLanguageDef, gfRGLLanguageDef,
    allIdentityRewrites, allSemanticRewrites, allTenseRewrites,
    applyRuleWithPremisesUsing, Mettapedia.OSLF.MeTTaIL.Match.matchPattern,
    applyPremisesWithEnv, useNElimRewrite, positAElimRewrite,
    useVElimRewrite, useCompElimRewrite, useN2ElimRewrite, useA2ElimRewrite,
    activePassiveRewrite, presentTenseRewrite, pastTenseRewrite,
    futureTenseRewrite] at hExec

/-! ### Alternative witness family: active/passive clause contrast -/

/-- Subject NP used in the active/passive witness pair: "the cat". -/
abbrev activeSubjCatTree : AbstractNode :=
  .apply FunctionSig.DetCN
    [.leaf "the_Det" (.base "Det"),
      .apply FunctionSig.UseN [.leaf "cat_N" (.base "N")]]

/-- Object NP used in the active/passive witness pair: "the dog". -/
abbrev activeObjDogTree : AbstractNode :=
  .apply FunctionSig.DetCN
    [.leaf "the_Det" (.base "Det"),
      .apply FunctionSig.UseN [.leaf "dog_N" (.base "N")]]

/-- Active clause witness: "the cat loves the dog". -/
abbrev activeClauseTree : AbstractNode :=
  .apply FunctionSig.PredVP
    [activeSubjCatTree,
      .apply FunctionSig.ComplSlash
        [.apply FunctionSig.SlashV2a [.leaf "love_V2" (.base "V2")],
          activeObjDogTree]]

/-- Passive clause witness: "the dog is loved". -/
abbrev passiveClauseTree : AbstractNode :=
  .apply FunctionSig.PredVP
    [activeObjDogTree,
      .apply FunctionSig.PassV2 [.leaf "love_V2" (.base "V2")]]

/-- Atomic observation naming the passive-clause witness pattern. -/
def passiveClauseAtomSem : String → Pattern → Prop
  | "is_passive_clause", p => p = gfAbstractToPattern passiveClauseTree
  | _, _ => False

theorem activeClause_pattern_ne_passiveClause_pattern :
    gfAbstractToPattern activeClauseTree ≠
      gfAbstractToPattern passiveClauseTree := by
  simp [activeClauseTree, passiveClauseTree, activeSubjCatTree, activeObjDogTree,
    FunctionSig.PredVP, FunctionSig.DetCN, FunctionSig.UseN, FunctionSig.ComplSlash,
    FunctionSig.SlashV2a, FunctionSig.PassV2]

theorem passiveClause_passiveAtom_true :
    sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
      (.atom "is_passive_clause") (gfAbstractToPattern passiveClauseTree) := by
  simp [sem, passiveClauseAtomSem]

theorem activeClause_passiveAtom_false :
    ¬ sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
      (.atom "is_passive_clause") (gfAbstractToPattern activeClauseTree) := by
  simp [sem, passiveClauseAtomSem, activeClauseTree, passiveClauseTree,
    activeSubjCatTree, activeObjDogTree, FunctionSig.PredVP, FunctionSig.DetCN,
    FunctionSig.UseN, FunctionSig.ComplSlash, FunctionSig.SlashV2a,
    FunctionSig.PassV2]

section EnglishCzechNontrivial

variable {State : Type u} [EvidenceType State] [WorldModel State Pattern]

/-- The selected English/Czech signature is nontrivial: even with the same
shared abstract machinery, the chosen OSLF observation family distinguishes
at least one genuine pair of trees. -/
theorem UGCore_nontrivial_for_EnglishCzech
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let sig :=
      englishCzechSelectedSignature W (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ∃ t₁ t₂, ¬ UGCoreEq sig t₁ t₂ := by
  dsimp
  refine ⟨useNHouseTree, bareHouseTree, ?_⟩
  intro hEq
  have hObs := hEq .englishSem
  dsimp [englishCzechSelectedSignature] at hObs
  have hPos :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) (gfAbstractToPattern useNHouseTree) :=
    english_useNHouse_dia_is_house
  have hTransferred :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) (gfAbstractToPattern bareHouseTree) := by
    rwa [hObs] at hPos
  exact english_bareHouse_not_dia_is_house hTransferred

/-- Package the English/Czech selected signature as a singleton family and
record its nontriviality at the family level. -/
theorem EnglishCzech_selected_family_has_genuine_distinction
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let fam : Unit → UGSignature := fun _ =>
      englishCzechSelectedSignature W (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ∃ i, ∃ ℓ : (fam i).Label, ∃ t₁ t₂,
      (fam i).observe ℓ t₁ ≠ (fam i).observe ℓ t₂ := by
  dsimp
  refine ⟨(), .englishSem, useNHouseTree, bareHouseTree, ?_⟩
  intro hEq
  dsimp [englishCzechSelectedSignature] at hEq
  have hPos :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) (gfAbstractToPattern useNHouseTree) :=
    english_useNHouse_dia_is_house
  have hTransferred :
      sem (langReduces englishGFLanguageDef) (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) (gfAbstractToPattern bareHouseTree) := by
    rwa [hEq] at hPos
  exact english_bareHouse_not_dia_is_house hTransferred

/-- Family-level corollary: the English/Czech selected family does not
trivialize. -/
theorem EnglishCzech_selected_family_not_total
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let fam : Unit → UGSignature := fun _ =>
      englishCzechSelectedSignature W (gfAtomSem_isName "house")
        (.dia (.atom "is_house")) Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ¬ (∀ t₁ t₂, UGFamilyCoreEq fam t₁ t₂) := by
  dsimp
  apply Strong_UG_fails_if_family_core_trivializes
  exact EnglishCzech_selected_family_has_genuine_distinction
    W Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl

/-- Parallel nontriviality witness using the active/passive clause pair rather
than the `UseN(house)` wrapper example. This is a more linguistically legible
selected-core witness for exposition, while the wrapper witness remains the
smallest reduction-theoretic endpoint. -/
theorem UGCore_nontrivial_for_EnglishCzech_activePassive
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let sig :=
      englishCzechSelectedSignature W passiveClauseAtomSem
        (.atom "is_passive_clause") Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ∃ t₁ t₂, ¬ UGCoreEq sig t₁ t₂ := by
  dsimp
  refine ⟨activeClauseTree, passiveClauseTree, ?_⟩
  intro hEq
  have hObs := hEq .englishSem
  dsimp [englishCzechSelectedSignature] at hObs
  have hPos :
      sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
        (.atom "is_passive_clause") (gfAbstractToPattern passiveClauseTree) :=
    passiveClause_passiveAtom_true
  have hTransferred :
      sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
        (.atom "is_passive_clause") (gfAbstractToPattern activeClauseTree) := by
    exact hObs.mpr hPos
  exact activeClause_passiveAtom_false hTransferred

/-- Family-level distinction using the active/passive clause pair. -/
theorem EnglishCzech_selected_family_has_activePassive_distinction
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let fam : Unit → UGSignature := fun _ =>
      englishCzechSelectedSignature W passiveClauseAtomSem
        (.atom "is_passive_clause") Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ∃ i, ∃ ℓ : (fam i).Label, ∃ t₁ t₂,
      (fam i).observe ℓ t₁ ≠ (fam i).observe ℓ t₂ := by
  dsimp
  refine ⟨(), .englishSem, activeClauseTree, passiveClauseTree, ?_⟩
  intro hEq
  dsimp [englishCzechSelectedSignature] at hEq
  have hPos :
      sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
        (.atom "is_passive_clause") (gfAbstractToPattern passiveClauseTree) :=
    passiveClause_passiveAtom_true
  have hTransferred :
      sem (langReduces englishGFLanguageDef) passiveClauseAtomSem
        (.atom "is_passive_clause") (gfAbstractToPattern activeClauseTree) := by
    exact hEq.mpr hPos
  exact activeClause_passiveAtom_false hTransferred

/-- Family-level corollary for the active/passive witness package. -/
theorem EnglishCzech_selected_family_not_total_activePassive
    (W : State)
    (Rnt : Pattern → Pattern → Prop) (Int : Mettapedia.OSLF.QuantifiedFormula2.QEvidenceAtomSem)
    (Dom : Domain2) (envScope : VarEnv2)
    (x y : String) (hne : x ≠ y)
    (φscope : QFormula2) (X : Mettapedia.CategoryTheory.PLNInstance.PLNObj)
    (env₁ env₂ : VarEnv2) (φclosed : QFormula2) (hcl : closedQF2 φclosed) :
    let fam : Unit → UGSignature := fun _ =>
      englishCzechSelectedSignature W passiveClauseAtomSem
        (.atom "is_passive_clause") Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl
    ¬ (∀ t₁ t₂, UGFamilyCoreEq fam t₁ t₂) := by
  dsimp
  apply Strong_UG_fails_if_family_core_trivializes
  exact EnglishCzech_selected_family_has_activePassive_distinction
    W Rnt Int Dom envScope x y hne φscope X env₁ env₂ φclosed hcl

end EnglishCzechNontrivial

end Mettapedia.Languages.GF.UGCoreFamily
