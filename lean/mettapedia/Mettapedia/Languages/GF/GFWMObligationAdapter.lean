import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mettapedia.Languages.GF.GFWMConnections
import Mettapedia.Logic.PLNWorldModelPureKernelBridge
import Mettapedia.Logic.PLNWorldModelCategoricalBridge

/-!
# GF → WM Obligation Adapter (Pure-Interface Aligned)

This module aligns GF transport endpoints with the same obligation surface used by
`PureJudgmentWMInterface`, without modifying Pure kernel semantics.

It provides:

1. adapters from GF syntactic transport (`GFSyntaxHom`) into
   `WMStrengthObligation` / `WMConsequenceRuleOn` under a supplied
   `PureJudgmentWMInterface`,
2. category-theoretic characterization endpoints for the GF→WM functor:
   a faithful direction (always) and non-fullness witness under
   evidence-collapse assumptions.
-/

namespace Mettapedia.Languages.GF.GFWMObligationAdapter

open CategoryTheory
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.GFWMConnections
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelPureKernelBridge
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
open Mettapedia.OSLF.MeTTaIL.Syntax

universe u v

section PureAlignedAdapters

variable {State : Type u} {Query : Type v}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- A GF syntactic transport can be consumed directly as a
`PureJudgmentWMInterface`-style WM obligation witness. -/
theorem gfSyntaxHom_to_wmStrengthObligation
    (I : PureJudgmentWMInterface State Query)
    {A B : GFSyntaxObj} (f : A ⟶ B)
    {W : State} (hW : I.side W) :
    WMStrengthObligation State Query W
      (I.encode (syntaxQuery A))
      (I.encode (syntaxQuery B)) := by
  have hstar : PureProfileTheoryStepStar (syntaxQuery A) (syntaxQuery B) := by
    rcases f with ⟨hEq⟩
    exact hEq ▸ Relation.ReflTransGen.refl
  exact I.profileStepStar_sound hW hstar

/-- Tree-pattern equality endpoint on the same pure-interface obligation surface. -/
theorem gfTreePatternEq_to_wmStrengthObligation
    (I : PureJudgmentWMInterface State Query)
    {t₁ t₂ : AbstractNode}
    (hPat : Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₁ =
      Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₂)
    {W : State} (hW : I.side W) :
    WMStrengthObligation State Query W
      (I.encode (Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₁))
      (I.encode (Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₂)) := by
  simpa [syntaxQuery] using
    (gfSyntaxHom_to_wmStrengthObligation (I := I)
      (f := syntaxHom_of_treePatternEq (hPat := hPat)) (W := W) hW)

/-- Package a GF syntactic transport as a state-indexed WM consequence rule using
the same interface surface as Pure-bridge wrappers. -/
def wmConsequenceRuleOn_of_gfSyntaxHom_viaPureInterface
    (I : PureJudgmentWMInterface State Query)
    {A B : GFSyntaxObj} (f : A ⟶ B) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode (syntaxQuery A)
  conclusion := I.encode (syntaxQuery B)
  sound := by
    intro W hW
    exact gfSyntaxHom_to_wmStrengthObligation (I := I) (f := f) (W := W) hW

/-- Tree-pattern equality packaged as a pure-interface-aligned WM consequence rule. -/
def wmConsequenceRuleOn_of_gfTreePatternEq_viaPureInterface
    (I : PureJudgmentWMInterface State Query)
    {t₁ t₂ : AbstractNode}
    (hPat : Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₁ =
      Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern t₂) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_gfSyntaxHom_viaPureInterface (I := I)
    (f := syntaxHom_of_treePatternEq (hPat := hPat))

/-- Frege-strong compositional transport packaged as a pure-interface-aligned
WM consequence rule. -/
def wmConsequenceRuleOn_of_fregeStrong_viaPureInterface
    (I : PureJudgmentWMInterface State Query)
    (f : FunctionSig) (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern =
      args₂.map Mettapedia.Languages.GF.OSLFBridge.gfAbstractToPattern) :
    WMConsequenceRuleOn State Query :=
  wmConsequenceRuleOn_of_gfTreePatternEq_viaPureInterface (I := I)
    (hPat := Mettapedia.Languages.GF.Typing.frege_strong f args₁ args₂ hargs)

end PureAlignedAdapters

section CategoricalEndpointLink

variable {State : Type u} {Query : Type v}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Unified endpoint that packages:
1) GF syntactic transport consumed as a pure-interface WM obligation, and
2) the institution+Beck-Chevalley categorical endpoint theorem.

This gives one theorem-level entry point from GF adapter obligations into the
categorical WM endpoint surface. -/
theorem gfSyntaxHom_and_institution_beckChevalley_endpoint
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (I : PureJudgmentWMInterface State Query)
    {Asyn Bsyn : GFSyntaxObj} (f : Asyn ⟶ Bsyn)
    (W : State) (φ : H.query Bobj) (hW : I.side W) :
    WMStrengthObligation State Query W
      (I.encode (syntaxQuery Asyn))
      (I.encode (syntaxQuery Bsyn))
    ∧
    EndpointStatement
      (H := H) pi1 pi2 fcat gcat W φ := by
  letI : CategoryTheory.Mono fcat := hmfcat
  letI : CategoryTheory.Mono pi2 := hmpi2
  constructor
  · exact gfSyntaxHom_to_wmStrengthObligation (I := I) (f := f) (W := W) hW
  · exact institution_beckChevalley_endpoint
      (H := H) pi1 pi2 fcat gcat hpb W φ

end CategoricalEndpointLink

section CategoryCharacterization

variable {State : Type u}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

/-- The GF syntax→WM functor is faithful (thin-domain transport is conservative). -/
instance syntaxToWMFunctor_faithful :
    CategoryTheory.Functor.Faithful (syntaxToWMFunctor (State := State)) where
  map_injective := by
    intro X Y f g _
    cases f
    cases g
    rfl

/-- If WM query-equivalence reflects pattern equality, the GF syntax→WM functor is full. -/
noncomputable def syntaxToWMFunctor_full_of_queryEq_reflects_patternEq
    (hreflect : ∀ p q : Pattern,
      WMQueryEq (State := State) (Query := Pattern) p q → p = q) :
    CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) where
  map_surjective := by
    intro A B f
    refine ⟨PLift.up (hreflect (syntaxQuery A) (syntaxQuery B) ?_), ?_⟩
    · simpa [wmQuery, syntaxQuery] using f.down
    · cases f
      rfl

/-- Positive expressivity: GF syntax transport into WM is always faithful. -/
theorem syntaxToWMFunctor_positive_faithful :
    CategoryTheory.Functor.Faithful (syntaxToWMFunctor (State := State)) := by
  infer_instance

/-- Positive expressivity criterion family:
if WM query-equivalence reflects pattern equality, GF→WM is full. -/
theorem syntaxToWMFunctor_positive_full_of_queryEq_reflects_patternEq
    (hreflect : ∀ p q : Pattern,
      WMQueryEq (State := State) (Query := Pattern) p q → p = q) :
    CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) :=
  syntaxToWMFunctor_full_of_queryEq_reflects_patternEq (State := State) hreflect

/-- Under evidence collapse (all queries observationally equal), the GF syntax→WM
functor has semantic morphisms with no syntactic preimage (non-fullness witness). -/
theorem syntaxToWMFunctor_not_full_witness_of_constant_evidence
    (hconst : ∀ W : State, ∀ p q : Pattern,
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W p =
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W q)
    {A B : GFSyntaxObj}
    (hneq : syntaxQuery A ≠ syntaxQuery B) :
    ∃ (f : (syntaxToWMFunctor (State := State)).obj A
          ⟶ (syntaxToWMFunctor (State := State)).obj B),
      ¬ ∃ g : A ⟶ B, (syntaxToWMFunctor (State := State)).map g = f := by
  refine ⟨PLift.up ?_, ?_⟩
  · intro W
    simpa [wmQuery, syntaxQuery] using hconst W (syntaxQuery A) (syntaxQuery B)
  · intro hpre
    rcases hpre with ⟨g, _⟩
    exact hneq g.down

/-- If evidence collapses all queries and two syntax objects are distinct at query-level,
the GF syntax→WM functor is not full. -/
theorem syntaxToWMFunctor_not_full_of_constant_evidence
    (hconst : ∀ W : State, ∀ p q : Pattern,
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W p =
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W q)
    {A B : GFSyntaxObj}
    (hneq : syntaxQuery A ≠ syntaxQuery B) :
    ¬ CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) := by
  intro hfull
  letI : CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) := hfull
  rcases syntaxToWMFunctor_not_full_witness_of_constant_evidence
      (State := State) hconst (A := A) (B := B) hneq with ⟨f, hno⟩
  exact hno ((CategoryTheory.Functor.map_surjective (F := syntaxToWMFunctor (State := State)) f))

/-- Negative expressivity criterion family:
if evidence collapses queries globally and syntax has a distinct query pair,
GF→WM cannot be full. -/
theorem syntaxToWMFunctor_not_full_of_constant_evidence_and_nontrivial_syntax
    (hconst : ∀ W : State, ∀ p q : Pattern,
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W p =
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W q)
    (hneq : ∃ A B : GFSyntaxObj, syntaxQuery A ≠ syntaxQuery B) :
    ¬ CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) := by
  rcases hneq with ⟨A, B, hAB⟩
  exact syntaxToWMFunctor_not_full_of_constant_evidence
    (State := State) hconst (A := A) (B := B) hAB

/-- Positive/negative expressivity split under explicit criteria:
faithful always; non-full under global evidence collapse + nontrivial syntax. -/
theorem syntaxToWMFunctor_expressivity_split_of_constant_evidence
    (hconst : ∀ W : State, ∀ p q : Pattern,
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W p =
      BinaryWorldModel.evidence (State := State) (Query := Pattern) W q)
    (hneq : ∃ A B : GFSyntaxObj, syntaxQuery A ≠ syntaxQuery B) :
    CategoryTheory.Functor.Faithful (syntaxToWMFunctor (State := State))
    ∧ ¬ CategoryTheory.Functor.Full (syntaxToWMFunctor (State := State)) := by
  constructor
  · exact syntaxToWMFunctor_positive_faithful (State := State)
  · exact syntaxToWMFunctor_not_full_of_constant_evidence_and_nontrivial_syntax
      (State := State) hconst hneq

end CategoryCharacterization

end Mettapedia.Languages.GF.GFWMObligationAdapter
