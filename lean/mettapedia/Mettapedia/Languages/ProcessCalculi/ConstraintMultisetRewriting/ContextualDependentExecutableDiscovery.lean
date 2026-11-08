import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableChecking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPiSpineDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWorklistSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecoveryBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBudget

/-!
# Eventual success of the solver's executable entry points

The dependent solver reads a store through four executable entry points: the
comparison of the two annotations of an equation, the discovery of a dependent
Π-spine from an annotation, the newest declaration of a context with its
synthesized universe, and checked recovery of a body. In the cumulative tower,
with the actual normalizer and the constructed universe choices, each eventually
succeeds and then keeps its result:

* annotations that are equal types are eventually compared successfully;
* a normal annotation with at least the requested number of leading Π binders
  eventually yields its spine;
* a context whose newest entry is normal eventually yields its newest view.

Each result is the same at every larger budget, by fuel stability of the
underlying executable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExecutableDiscovery

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion
open ContextualDependentExecutableChecking

variable {L : Type} [UniverseLevel.LevelOrder L]
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

local instance settingHeadEq (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

variable (valuation : Nat → L)

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem red_stable {n : Nat} (fuel : Nat) (term : Tm (LevelTower.Head L) n) :
    ContextualDependentConversionBudget.Keeps (red fuel term) (red (fuel + 1) term) :=
  ContextualDependentConversionBudget.normalizer_stable (LevelTower.rules L) (fun _ => none) fuel term

/-- The executable type former, with a result kept at every larger budget. -/
theorem formType_stable {Γ : Context (LevelTower.rules L)} {code : Tm (LevelTower.Head L) Γ.arity}
    (normal : Normal (LevelTower.rules L) code) (isType : IsType (LevelTower.rules L) Γ.raw code) :
    ∃ fuel result, ∀ larger, fuel ≤ larger →
      ContextualDependentPruning.formType (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger Γ code = some result := by
  obtain ⟨fuel, succeeds⟩ := formType_eventually valuation normal isType
  obtain ⟨result, computed⟩ := Option.isSome_iff_exists.mp (succeeds fuel le_rfl)
  exact ⟨fuel, result, fun _ enough =>
    ContextualDependentRecoveryBudget.formType_mono (S := TowerModel.setting valuation) TowerModel.facts
      TowerModel.roots TowerModel.heads TowerModel.algebra declared tc red red_stable computed enough⟩

omit [DecidableRel (LevelTower.rules L).cumulative] in
/-- **Annotation comparison eventually accepts equal annotations**, and keeps its result. -/
theorem compareTypes_eventually {Γ : Context (LevelTower.rules L)} (first second : TypeOver Γ)
    (equal : TypeEq (LevelTower.rules L) Γ.raw first.code second.code) :
    ∃ fuel result, ∀ larger, fuel ≤ larger →
      ContextualDependentEta.Conversion.compareTypes (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra red larger first second = some result := by
  obtain ⟨fuel, certificate, stable⟩ := types_eventually Γ.formed equal
  refine ⟨fuel, ⟨equal⟩, fun larger enough => ?_⟩
  have compared : ExecutableConversion.types (TowerModel.setting valuation).R red larger Γ.raw first.code second.code =
      some certificate := stable larger enough
  unfold ContextualDependentEta.Conversion.compareTypes
  rw [compared]
  rfl

/-- The number of leading Π binders of a code. -/
def piDepth {n : Nat} : Tm (LevelTower.Head L) n → Nat
  | .pi _ body => piDepth body + 1
  | _ => 0

/-- **Spine discovery eventually reads every normal annotation** with at least the requested
number of leading Π binders, and keeps its spine. -/
theorem discover_eventually : ∀ (count : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ),
    Normal (LevelTower.rules L) whole.code → count ≤ piDepth whole.code →
    ∃ fuel spine, ∀ larger, fuel ≤ larger →
      ContextualDependentPiSpineDiscovery.discover (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger count whole = some spine
  | 0, _, whole, _, _ => ⟨0, .stop whole, fun _ _ => rfl⟩
  | count + 1, Γ, whole, normal, deep => by
      obtain ⟨code, level, universeWitness, formed⟩ := whole
      cases code with
      | pi domain codomain =>
          have normalDomain : Normal (LevelTower.rules L) domain := fun _ step => normal _ (.congPiDom step)
          have normalCodomain : Normal (LevelTower.rules L) codomain := fun _ step => normal _ (.congPiCod step)
          obtain ⟨⟨u, hu, tDomain⟩, v, hv, tCodomain⟩ := IsType.pi_parts ⟨level, universeWitness, formed⟩
          obtain ⟨f₁, first, stable₁⟩ := formType_stable valuation normalDomain ⟨u, hu, tDomain⟩
          have tCodomain' : IsType (LevelTower.rules L) (extend Γ first.val).raw codomain := by
            change IsType (LevelTower.rules L) (.snoc Γ.raw first.val.code) codomain
            rw [first.property]
            exact ⟨v, hv, tCodomain⟩
          obtain ⟨f₂, second, stable₂⟩ := formType_stable valuation (Γ := extend Γ first.val) normalCodomain tCodomain'
          have normalSecond : Normal (LevelTower.rules L) second.val.code := by
            rw [second.property]
            exact normalCodomain
          have deepSecond : count ≤ piDepth second.val.code := by
            rw [second.property]
            simp only [piDepth] at deep
            omega
          obtain ⟨f₃, rest, stable₃⟩ := discover_eventually count second.val normalSecond deepSecond
          refine ⟨f₁ + f₂ + f₃, .bind ⟨first.val, second.val, ⟨.pi domain codomain, level, universeWitness, formed⟩,
            by rw [first.property, second.property]⟩ rest, fun larger enough => ?_⟩
          simp only [ContextualDependentPiSpineDiscovery.discover]
          exact Option.bind_eq_some_iff.mpr ⟨first, stable₁ larger (by omega),
            Option.bind_eq_some_iff.mpr ⟨second, stable₂ larger (by omega),
              Option.bind_eq_some_iff.mpr ⟨rest, stable₃ larger (by omega), rfl⟩⟩⟩
      | _ => simp [piDepth] at deep

/-- **The newest declaration is eventually read** from every context whose newest entry is
normal, and the view is kept at every larger budget. -/
theorem newestOf_eventually {n : Nat} {raw : Ctx (LevelTower.Head L) n} {code : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) (.snoc raw code)) (normal : Normal (LevelTower.rules L) code) :
    ∃ fuel, (ContextualDependentWorklist.newestOf (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red fuel ⟨n + 1, .snoc raw code, formed⟩).isSome ∧
      ∀ larger, fuel ≤ larger →
        ContextualDependentWorklist.newestOf (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
          TowerModel.heads TowerModel.algebra declared tc red larger ⟨n + 1, .snoc raw code, formed⟩ =
        ContextualDependentWorklist.newestOf (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
          TowerModel.heads TowerModel.algebra declared tc red fuel ⟨n + 1, .snoc raw code, formed⟩ := by
  have isType : IsType (LevelTower.rules L) raw code := by
    cases formed
    assumption
  obtain ⟨fuel, result, stable⟩ := formType_stable valuation (Γ := ⟨n, raw, ContextualDependentWorklist.formedPrefix (S := TowerModel.setting valuation) formed⟩)
    normal isType
  refine ⟨fuel, ?_, fun larger enough => ?_⟩
  · simp only [ContextualDependentWorklist.newestOf]
    erw [stable fuel le_rfl]
    rfl
  · simp only [ContextualDependentWorklist.newestOf]
    erw [stable larger enough, stable fuel le_rfl]

omit [DecidableRel (LevelTower.rules L).cumulative] in
/-- **The solver's conversion test eventually accepts every equal pair** of annotated terms, and keeps
its result. -/
theorem compare_total_eventually {Γ : Context (LevelTower.rules L)} (first second : TotalTerm Γ)
    (equal : (ContextualDependentEta.frames (TowerModel.setting valuation).levels).E first second) :
    ∃ fuel result, ∀ larger, fuel ≤ larger →
      ContextualDependentEta.Conversion.compare (S := TowerModel.setting valuation) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra red larger first second = some result := by
  obtain ⟨types, terms⟩ := equal
  obtain ⟨f₁, annotations, stable₁⟩ := compareTypes_eventually valuation first.1 second.1 types
  obtain ⟨f₂, certificate, stable₂⟩ := ContextualDependentExecutableConversion.compare_eventually Γ.formed terms
  refine ⟨f₁ + f₂, ⟨⟨types, terms⟩⟩, fun larger enough => ?_⟩
  have compared₁ := stable₁ larger (by omega)
  have compared₂ : ExecutableConversion.compare (TowerModel.setting valuation).R red larger Γ.raw first.2.code
      second.2.code first.1.code = some certificate := stable₂ larger (by omega)
  unfold ContextualDependentEta.Conversion.compare
  simp only [Option.bind_eq_bind]
  erw [compared₁]
  simp only [Option.bind_some]
  erw [compared₂]
  rfl

omit [DecidableRel (LevelTower.rules L).cumulative] in
/-- **The conversion scan eventually discharges every convertible equation**: at every large budget,
no equation it keeps has equal sides. -/
theorem scan_eventually {Γ : Context (LevelTower.rules L)} :
    ∀ problem : EquationStore (TotalTerm Γ), ∃ fuel, ∀ larger, fuel ≤ larger →
      ∀ equation ∈ ContextualDependentEta.Conversion.scan (S := TowerModel.setting valuation) TowerModel.facts
          TowerModel.roots TowerModel.heads TowerModel.algebra red larger problem,
        ¬ (ContextualDependentEta.frames (TowerModel.setting valuation).levels).E equation.1 equation.2
  | [] => ⟨0, fun _ _ _ member => absurd member List.not_mem_nil⟩
  | equation :: rest => by
      obtain ⟨fuel, kept⟩ := scan_eventually rest
      by_cases equal : (ContextualDependentEta.frames (TowerModel.setting valuation).levels).E equation.1 equation.2
      · obtain ⟨f, result, stable⟩ := compare_total_eventually valuation equation.1 equation.2 equal
        refine ⟨fuel + f, fun larger enough => ?_⟩
        simp only [ContextualDependentEta.Conversion.scan, stable larger (by omega)]
        exact kept larger (by omega)
      · refine ⟨fuel, fun larger enough => ?_⟩
        simp only [ContextualDependentEta.Conversion.scan]
        split
        · exact kept larger enough
        · intro other member
          rcases List.mem_cons.mp member with rfl | later
          · exact equal
          · exact kept larger enough other later

end ContextualDependentExecutableDiscovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
