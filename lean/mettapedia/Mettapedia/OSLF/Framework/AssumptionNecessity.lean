import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
import Mettapedia.OSLF.NativeType.Construction

/-!
# Assumption-Necessity Counterexamples

Counterexamples and non-finiteness witnesses used to justify why selected
global assumptions in endpoint wrappers remain explicit.
-/

namespace Mettapedia.OSLF.Framework.AssumptionNecessity

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

abbrev AtomSem := Mettapedia.OSLF.Formula.AtomSem
abbrev OSLFFormula := Mettapedia.OSLF.Formula.OSLFFormula

/-- A fixed base pattern for explicit star-image witnesses. -/
def basePat : Pattern := .bvar 0

/-- Syntactic zero process marker used by SC nil-laws. -/
def zeroPat : Pattern := .apply "PZero" []

/-- Recursively add right-`PZero` wrappers via bag syntax. -/
def addRightZeroNest : Nat → Pattern
  | 0 => basePat
  | n + 1 => .collection .hashBag [addRightZeroNest n, zeroPat] none

/-- Depth counter for `addRightZeroNest`. -/
def rightZeroDepth : Pattern → Nat
  | .bvar 0 => 0
  | .collection .hashBag [p, .apply "PZero" []] none => rightZeroDepth p + 1
  | _ => 0

theorem rightZeroDepth_addRightZeroNest (n : Nat) :
    rightZeroDepth (addRightZeroNest n) = n := by
  induction n with
  | zero =>
      simp [addRightZeroNest, rightZeroDepth, basePat]
  | succ n ih =>
      simp [addRightZeroNest, rightZeroDepth, zeroPat, ih]

theorem addRightZeroNest_injective : Function.Injective addRightZeroNest := by
  intro n m h
  have hd : rightZeroDepth (addRightZeroNest n) = rightZeroDepth (addRightZeroNest m) :=
    congrArg rightZeroDepth h
  simpa [rightZeroDepth_addRightZeroNest] using hd

/-- Source with a direct DROP reduction to `basePat`. -/
def dropSource : Pattern := .apply "PDrop" [.apply "NQuote" [basePat]]

theorem base_sc_addRightZeroNest : ∀ n, StructuralCongruence basePat (addRightZeroNest n)
  | 0 => StructuralCongruence.refl basePat
  | n + 1 =>
      StructuralCongruence.trans basePat (addRightZeroNest n) (addRightZeroNest (n + 1))
        (base_sc_addRightZeroNest n)
        (by
          simpa [addRightZeroNest] using
            (StructuralCongruence.symm _ _
              (StructuralCongruence.par_nil_right (addRightZeroNest n))))

def dropSource_reduces_to_addRightZeroNest (n : Nat) :
    Reduces dropSource (addRightZeroNest n) :=
  Reduces.equiv
    (p' := dropSource) (q' := basePat)
    (StructuralCongruence.refl dropSource)
    (by simpa [dropSource, basePat] using (Reduces.drop (p := basePat)))
    (by simpa using base_sc_addRightZeroNest n)

theorem dropSource_coreStar_to_addRightZeroNest (n : Nat) :
    rhoCoreStarRel dropSource (addRightZeroNest n) := by
  exact ⟨ReducesStar.single (dropSource_reduces_to_addRightZeroNest n)⟩

theorem dropSource_derivedStar_to_addRightZeroNest (n : Nat) :
    rhoDerivedStarRel dropSource (addRightZeroNest n) := by
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
    (ReducesStar.single (dropSource_reduces_to_addRightZeroNest n))⟩

theorem infinite_image_rhoCoreStarRel_dropSource :
    Set.Infinite {q : Pattern | rhoCoreStarRel dropSource q} := by
  let f : Nat → Pattern := addRightZeroNest
  have hInfRange : Set.Infinite (Set.range f) :=
    Set.infinite_range_of_injective addRightZeroNest_injective
  have hSubset : Set.range f ⊆ {q : Pattern | rhoCoreStarRel dropSource q} := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact dropSource_coreStar_to_addRightZeroNest n
  exact hInfRange.mono hSubset

theorem infinite_image_rhoDerivedStarRel_dropSource :
    Set.Infinite {q : Pattern | rhoDerivedStarRel dropSource q} := by
  let f : Nat → Pattern := addRightZeroNest
  have hInfRange : Set.Infinite (Set.range f) :=
    Set.infinite_range_of_injective addRightZeroNest_injective
  have hSubset : Set.range f ⊆ {q : Pattern | rhoDerivedStarRel dropSource q} := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact dropSource_derivedStar_to_addRightZeroNest n
  exact hInfRange.mono hSubset

/-- Concrete witness: the core-star endpoint relation is not globally image-finite. -/
theorem rhoCoreStarRel_not_imageFinite :
    ∃ p : Pattern, ¬ Set.Finite {q : Pattern | rhoCoreStarRel p q} := by
  refine ⟨dropSource, ?_⟩
  exact infinite_image_rhoCoreStarRel_dropSource.not_finite

/-- Concrete witness: the derived-star endpoint relation is not globally image-finite. -/
theorem rhoDerivedStarRel_not_imageFinite :
    ∃ p : Pattern, ¬ Set.Finite {q : Pattern | rhoDerivedStarRel p q} := by
  refine ⟨dropSource, ?_⟩
  exact infinite_image_rhoDerivedStarRel_dropSource.not_finite

/-- Therefore global `hImageFinite` assumptions for star-level HM wrappers are
not automatically dischargeable for all states. -/
theorem not_global_hImageFinite_rhoCoreStarRel :
    ¬ (∀ p : Pattern, Set.Finite {q : Pattern | rhoCoreStarRel p q}) := by
  intro h
  rcases rhoCoreStarRel_not_imageFinite with ⟨p, hp⟩
  exact hp (h p)

/-- Therefore global `hImageFinite` assumptions for derived-star HM wrappers are
not automatically dischargeable for all states. -/
theorem not_global_hImageFinite_rhoDerivedStarRel :
    ¬ (∀ p : Pattern, Set.Finite {q : Pattern | rhoDerivedStarRel p q}) := by
  intro h
  rcases rhoDerivedStarRel_not_imageFinite with ⟨p, hp⟩
  exact hp (h p)

/-! ## Predecessor-Finiteness Necessity for Canonical `langReduces rhoCalc`

The ρ-calculus COMM rule erases the channel name from the reduct:
  { n!(q) | for(<-n){p} | rest } ~> { p[@q] | rest }
Variable `n` appears in the LHS but NOT in the RHS. Therefore, for a fixed
COMM target, infinitely many syntactically distinct sources (differing only
in channel name) all reduce to the same target in one step. -/

section PredFiniteNecessity

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar)
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Generic COMM source parameterized by channel. Body = `.bvar 0` (echo
    received name), sent value = `PZero`. -/
def commPredSourceGeneric (channel : Pattern) : Pattern :=
  .collection .hashBag [
    .apply "PInput" [channel, .lambda none (.bvar 0)],
    .apply "POutput" [channel, zeroPat]
  ] none

/-- Infinite family of COMM sources: channel varies via `addRightZeroNest`
    wrapped in `NQuote`. -/
def commPredSource (n : Nat) : Pattern :=
  commPredSourceGeneric (.apply "NQuote" [addRightZeroNest n])

/-- Fixed COMM target shared by every `commPredSource n`.
    Result of `openBVar 0 (NQuote PZero) (BVar 0) = NQuote PZero`. -/
def commPredTarget : Pattern :=
  .collection .hashBag [.apply "NQuote" [zeroPat]] none

/-- Extract the channel from a `commPredSourceGeneric` pattern. -/
private def commPredExtractChannel : Pattern → Pattern
  | .collection _ ((.apply "PInput" (ch :: _)) :: _) _ => ch
  | p => p

private theorem commPredExtractChannel_eq (n : Nat) :
    commPredExtractChannel (commPredSource n) =
      .apply "NQuote" [addRightZeroNest n] := by
  simp [commPredSource, commPredSourceGeneric, commPredExtractChannel]

theorem commPredSource_injective : Function.Injective commPredSource := by
  intro n m h
  have hch : commPredExtractChannel (commPredSource n) =
      commPredExtractChannel (commPredSource m) :=
    congrArg commPredExtractChannel h
  simp [commPredExtractChannel_eq] at hch
  exact addRightZeroNest_injective hch

/-- The ρ-calculus COMM rewrite rule (extracted for proof clarity). -/
private def commRule : RewriteRule where
  name := "Comm"
  typeContext := [("n", TypeExpr.name), ("p", TypeExpr.proc), ("q", TypeExpr.proc)]
  premises := []
  left := .collection .hashBag [
    .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
    .apply "POutput" [.fvar "n", .fvar "q"]
  ] (some "rest")
  right := .collection .hashBag [
    .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])
  ] (some "rest")

private theorem commRule_mem : commRule ∈ rhoCalc.rewrites := by
  simp [commRule, rhoCalc]

/-- Every `commPredSourceGeneric channel` reduces to `commPredTarget` via COMM.

    Proof strategy: construct a `DeclReducesWithPremises.topRule` witness using
    the COMM rule, explicit matching bindings, and the fact that `applyBindings`
    evaluates the `.subst` node via `openBVar`. -/
theorem commPredSourceGeneric_langReduces (channel : Pattern) :
    langReduces rhoCalc (commPredSourceGeneric channel) commPredTarget := by
  -- langReduces unfolds to DeclReducesWithPremises
  show DeclReducesWithPremises RelationEnv.empty rhoCalc
    (commPredSourceGeneric channel) commPredTarget
  -- The COMM bindings (order from matchBag: q, rest, p, n)
  let commBindings : Bindings :=
    [("q", zeroPat), ("rest", .collection .hashBag [] none),
     ("p", .bvar 0), ("n", channel)]
  apply DeclReducesWithPremises.topRule
    (r := commRule)
    (bs0 := commBindings)
    (bs := commBindings)
  -- Goal 1: commRule ∈ rhoCalc.rewrites
  · exact commRule_mem
  -- Goal 2: commBindings ∈ matchPattern commRule.left (commPredSourceGeneric channel)
  · -- matchPattern: inline commBindings and simp through bag matching
    show [("q", zeroPat), ("rest", Pattern.collection .hashBag [] none),
          ("p", Pattern.bvar 0), ("n", channel)] ∈ matchPattern
      (.collection .hashBag [
        .apply "PInput" [.fvar "n", .lambda none (.fvar "p")],
        .apply "POutput" [.fvar "n", .fvar "q"]
      ] (some "rest"))
      (commPredSourceGeneric channel)
    simp [commPredSourceGeneric, zeroPat,
      matchPattern, matchBag, matchArgs, mergeBindings]
  -- Goal 3: commBindings ∈ applyPremisesWithEnv ... commRule.premises commBindings
  --   COMM has no premises, so foldl on [] returns [seed]
  · show commBindings ∈ [commBindings]
    exact List.Mem.head _
  -- Goal 4: applyBindings commBindings commRule.right = commPredTarget
  · show applyBindings
      [("q", zeroPat), ("rest", Pattern.collection .hashBag [] none),
       ("p", Pattern.bvar 0), ("n", channel)]
      (.collection .hashBag [
        .subst (.fvar "p") (.apply "NQuote" [.fvar "q"])
      ] (some "rest")) = commPredTarget
    simp [commPredTarget, zeroPat, applyBindings, openBVar]

theorem commPredSource_langReduces (n : Nat) :
    langReduces rhoCalc (commPredSource n) commPredTarget :=
  commPredSourceGeneric_langReduces (.apply "NQuote" [addRightZeroNest n])

theorem infinite_predecessors_langReduces_rhoCalc :
    Set.Infinite {p : Pattern | langReduces rhoCalc p commPredTarget} := by
  have hInfRange : Set.Infinite (Set.range commPredSource) :=
    Set.infinite_range_of_injective commPredSource_injective
  exact hInfRange.mono (fun p hp => by
    rcases hp with ⟨n, rfl⟩
    exact commPredSource_langReduces n)

/-- Concrete witness: canonical one-step `langReduces rhoCalc` is not
    predecessor-finite. -/
theorem langReduces_rhoCalc_not_predFinite :
    ∃ p : Pattern, ¬ Set.Finite {q : Pattern | langReduces rhoCalc q p} :=
  ⟨commPredTarget, infinite_predecessors_langReduces_rhoCalc.not_finite⟩

/-- Therefore the canonical Theorem-1 predecessor-finiteness assumption cannot
    be discharged globally for `langReduces rhoCalc`. -/
theorem not_global_hPredFinite_langReduces_rhoCalc :
    ¬ (∀ p : Pattern, Set.Finite {q : Pattern | langReduces rhoCalc q p}) := by
  intro h
  exact infinite_predecessors_langReduces_rhoCalc.not_finite (h commPredTarget)

end PredFiniteNecessity

def relAll : Pattern → Pattern → Prop := fun _ _ => True
def relNone : Pattern → Pattern → Prop := fun _ _ => False

def atomAll : AtomSem := fun _ _ => True
def atomNone : AtomSem := fun _ _ => False

def witnessPat : Pattern := .bvar 0

/-- Counterexample pattern: dropping `hAtomAll` from global dia/box transfer
is unsound even when `◇⊤` holds everywhere. -/
theorem counterexample_hAtomAll_for_global_diaBox_transfer :
    ∃ (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula),
      EndpointDiaBoxFragment φ ∧
      (∀ p, Mettapedia.OSLF.Formula.sem R I (.dia .top) p) ∧
      ¬ (∀ p, Mettapedia.OSLF.Formula.sem R I φ p) := by
  refine ⟨relAll, atomNone, .atom "a", EndpointDiaBoxFragment.atom "a", ?_, ?_⟩
  · intro p
    exact ⟨p, trivial, trivial⟩
  · intro hall
    have hAt : Mettapedia.OSLF.Formula.sem relAll atomNone (.atom "a") witnessPat :=
      hall witnessPat
    simpa [atomNone] using hAt

/-- Counterexample pattern: dropping global `◇⊤` (`hDiaTopAll`) from the same
global transfer shape is unsound even when atoms are universally true. -/
theorem counterexample_hDiaTopAll_for_global_diaBox_transfer :
    ∃ (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula),
      EndpointDiaBoxFragment φ ∧
      (∀ a p, I a p) ∧
      ¬ (∀ p, Mettapedia.OSLF.Formula.sem R I φ p) := by
  refine ⟨relNone, atomAll, .dia .top,
    EndpointDiaBoxFragment.dia EndpointDiaBoxFragment.top, ?_, ?_⟩
  · intro _a _p
    trivial
  · intro hall
    have hDia : Mettapedia.OSLF.Formula.sem relNone atomAll (.dia .top) witnessPat :=
      hall witnessPat
    rcases hDia with ⟨_q, hstep, _hTop⟩
    exact hstep

def commLiftSeed : Pattern := .apply "NQuote" [basePat]

def commLiftBody : Pattern := .apply "PDrop" [.bvar 0]

def commLiftPred : Pattern → Prop := fun u => u = commLiftBody

theorem commLift_body_subst_eq_pathSem_h :
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst commLiftBody basePat =
      pathSem rhoCalc pdropArrow.toPath commLiftSeed := by
  simp [commLiftBody, commLiftSeed,
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst,
    Mettapedia.OSLF.MeTTaIL.Substitution.openBVar,
    pathSem, SortArrow.toPath, arrowSem, pdropArrow]

theorem commLift_body_subst_ne_pathSem_gcomp_h :
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst commLiftBody basePat ≠
      pathSem rhoCalc (nquoteArrow.toPath.comp pdropArrow.toPath) commLiftSeed := by
  intro h
  have hcontra : basePat = Pattern.apply "NQuote" [basePat] := by
    simpa [commLiftBody, commLiftSeed,
      Mettapedia.OSLF.MeTTaIL.Substitution.commSubst,
      Mettapedia.OSLF.MeTTaIL.Substitution.openBVar,
      pathSem, SortArrow.toPath, SortPath.comp, arrowSem,
      pdropArrow, nquoteArrow] using h
  cases hcontra

/-- Concrete necessity witness: `commDiWitnessLifting` is not derivable in full
generality from syntax alone (without an explicit lifting/package assumption). -/
theorem not_commDiWitnessLifting_rho_example :
    ¬ commDiWitnessLifting rhoCalc rhoProc commLiftSeed basePat commLiftPred := by
  intro hLift
  have hEx :=
    hLift
      (g := nquoteArrow.toPath)
      (h := pdropArrow.toPath)
      (u := commLiftBody)
      commLift_body_subst_eq_pathSem_h
      rfl
  rcases hEx with ⟨u', hu'Eq, hu'Pred⟩
  have hu' : u' = commLiftBody := hu'Pred
  subst hu'
  exact commLift_body_subst_ne_pathSem_gcomp_h hu'Eq

/-- Therefore the generic COMM/pathSem-lifting assumptions in BC transfer
lemmas cannot be dropped in full generality. -/
theorem commDiWitnessLifting_not_derivable_globally :
    ∃ (lang : LanguageDef) (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
      (seed q : Pattern) (φ : Pattern → Prop),
      ¬ commDiWitnessLifting lang s seed q φ := by
  exact ⟨rhoCalc, rhoProc, commLiftSeed, basePat, commLiftPred,
    not_commDiWitnessLifting_rho_example⟩

/-! ## M1–M4 Paper-Parity Assumption Necessity

These counterexamples justify the explicit assumptions introduced in the
paper-parity endpoints (M1–M4). -/

section PaperParityAssumptions

open Mettapedia.CategoryTheory.LambdaTheories in
/-- The `types.Nonempty` guard on Π/Σ type formation (M3) is necessary:
for empty type families, `sInf ∅ = ⊤` and `sSup ∅ = ⊥`, so `⊤ ≤ ⊥` fails
in any nontrivial Frame. -/
theorem types_nonempty_necessary_for_piSigma :
    ∃ (α : Type) (_ : Order.Frame α) (_ : Nontrivial α),
      ¬ (sInf (∅ : Set α) ≤ sSup (∅ : Set α)) := by
  refine ⟨Prop, inferInstance, ⟨⟨True, False, by simp⟩⟩, ?_⟩
  simp [sInf_empty, sSup_empty]

/-- Two distinct `ScopedConstructorPred`s witnessing that not all fragments are
closed under `ScopedReachable`. -/
theorem hClosed_necessary_for_fragment :
    ∃ (Frag : Mettapedia.OSLF.NativeType.ScopedConstructorPred rhoCalc → Prop),
      ∃ (A B : Mettapedia.OSLF.NativeType.ScopedConstructorPred rhoCalc),
        Frag A ∧
        Mettapedia.OSLF.NativeType.ScopedReachable A B ∧
        ¬ Frag B := by
  -- Define Frag that accepts only predicates with seed = basePat
  refine ⟨fun X => X.seed = basePat, ?_⟩
  -- Construct two ScopedConstructorPreds with different seeds but a morphism between them
  -- A: seed = basePat, pred = fun _ => True, sort = rhoProc
  -- B: seed = zeroPat, pred = fun _ => True, sort = rhoProc
  have hNat : ∀ seed, Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
      rhoCalc rhoProc seed (fun _ => True) := by
    intro seed _ _ g h _; trivial
  let A : Mettapedia.OSLF.NativeType.ScopedConstructorPred rhoCalc :=
    ⟨rhoProc, basePat, fun _ => True, hNat basePat⟩
  let B : Mettapedia.OSLF.NativeType.ScopedConstructorPred rhoCalc :=
    ⟨rhoProc, zeroPat, fun _ => True, hNat zeroPat⟩
  refine ⟨A, B, rfl, ?_, ?_⟩
  · -- ScopedReachable A B: need Nonempty (ScopedConstructorPredHom rhoCalc A B)
    exact ⟨{
      base := CategoryTheory.CategoryStruct.id _
      fiberLe := by
        intro U x _
        simp [Mettapedia.OSLF.NativeType.ScopedConstructorPred.toFullGrothObj,
              CategoryTheory.Subfunctor.preimage]
        trivial
    }⟩
  · -- ¬ Frag B: B.seed = zeroPat ≠ basePat
    simp [B, basePat, zeroPat]

end PaperParityAssumptions

end Mettapedia.OSLF.Framework.AssumptionNecessity
