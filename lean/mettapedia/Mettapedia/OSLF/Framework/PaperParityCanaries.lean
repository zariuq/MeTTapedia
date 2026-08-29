import Mettapedia.OSLF.CoreMain
import Mettapedia.OSLF.PresheafNativeType.PresheafSemantics

/-!
# Paper-Parity Canaries

Concrete instantiations of `coreMain_paper_parity_full_package` on two language
instances (ρ-calculus, λ-calculus) plus a negative canary showing the `hClosed`
assumption does real work.
-/

namespace Mettapedia.OSLF.Framework.PaperParityCanaries

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.PresheafNativeType
open Mettapedia.OSLF.Framework.ConstructorCategory

/-! ## Helper definitions -/

/-- Trivial atom semantics: all atoms satisfied everywhere. -/
def trivialAtomSem : Mettapedia.OSLF.Formula.AtomSem := fun _ _ => True

/-- Trivially-true predicate naturality. -/
theorem trivialPred_naturality (lang : LanguageDef) (s : LangSort lang) (seed : Pattern) :
    Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
      lang s seed (fun _ => True) := by
  intro _ _ _ _ _; trivial

/-- A concrete `ScopedConstructorPred` on any language and sort. -/
def trivialScopedPred (lang : LanguageDef) (s : LangSort lang) (seed : Pattern) :
    ScopedConstructorPred lang :=
  ⟨s, seed, fun _ => True, trivialPred_naturality lang s seed⟩

/-! ## Canary 1: ρ-calculus positive -/

/-- The paper-parity package instantiates concretely on `rhoCalc`. -/
theorem rhoCalc_paper_parity_canary :
    let A := trivialScopedPred rhoCalc rhoProc (.bvar 0)
    CoreMainPaperParityCanonicalPackage rhoCalc trivialAtomSem A (fun _ => True)
    ∧
    (∃ _ : CategoryTheory.Category.{0, 1} (FullPresheafGrothendieckObj rhoCalc), True)
    ∧
    (fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (scoped_fullGroth_base_eq_representable A) rfl = A) := by
  refine ⟨?_, ⟨fullPresheafGrothendieckCategory _, trivial⟩, scoped_full_scoped_obj_roundtrip _⟩
  exact Mettapedia.OSLF.coreMain_paper_parity_canonical_package _ _ _ _
    (by intro _ _ _ _; trivial)

/-! ## Canary 2: λ-calculus positive -/

/-- LangSort for the single λ-calculus sort. -/
def lambdaTerm : LangSort Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc :=
  ⟨"Term", List.Mem.head _⟩

/-- The paper-parity package instantiates on `lambdaCalc`. -/
theorem lambdaCalc_paper_parity_canary :
    let lang := Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
    let A := trivialScopedPred lang lambdaTerm (.bvar 0)
    CoreMainPaperParityCanonicalPackage lang trivialAtomSem A (fun _ => True)
    ∧
    (∃ _ : CategoryTheory.Category.{0, 1} (FullPresheafGrothendieckObj lang), True)
    ∧
    (fullGrothObj_to_scopedConstructorPred_at_representable
      A.toFullGrothObj A.sort A.seed A.pred A.naturality
      (scoped_fullGroth_base_eq_representable A) rfl = A) := by
  refine ⟨?_, ⟨fullPresheafGrothendieckCategory _, trivial⟩, scoped_full_scoped_obj_roundtrip _⟩
  exact Mettapedia.OSLF.coreMain_paper_parity_canonical_package _ _ _ _
    (by intro _ _ _ _; trivial)

/-! ## Canary 3: Negative (non-closed fragment)

Demonstrates that the `hClosed` hypothesis is not vacuous. -/

/-- A fragment restricted by seed value. -/
def seedRestrictedFrag (target : Pattern) :
    ScopedConstructorPred rhoCalc → Prop :=
  fun X => X.seed = target

/-- Two ScopedConstructorPreds with different seeds are reachable but the
seed-restricted fragment excludes one. -/
theorem negative_canary_nonclosed_fragment :
    let seedA := Pattern.bvar 0
    let seedB := Pattern.apply "PZero" []
    let A := trivialScopedPred rhoCalc rhoProc seedA
    let B := trivialScopedPred rhoCalc rhoProc seedB
    let Frag := seedRestrictedFrag seedA
    -- A is in the fragment
    Frag A
    ∧ -- B is reachable from A
    ScopedReachable A B
    ∧ -- But B is NOT in the fragment
    ¬ Frag B := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨{
      base := CategoryTheory.CategoryStruct.id _
      fiberLe := by
        intro U x _
        simp [ScopedConstructorPred.toFullGrothObj, CategoryTheory.Subfunctor.preimage]
        trivial
    }⟩
  · simp [seedRestrictedFrag, trivialScopedPred]

end Mettapedia.OSLF.Framework.PaperParityCanaries
