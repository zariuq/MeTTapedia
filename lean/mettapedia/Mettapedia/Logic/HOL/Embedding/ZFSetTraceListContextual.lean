import Mettapedia.Logic.HOL.Embedding.ZFSetTraceContextual
import Mettapedia.Logic.HOL.Embedding.ZFSetListContextual

/-!
# Actual contextual lists with trace-coded functions

The same list sets and constructors support trace-coded mapping and dependent
elimination. Both operations are built using trace lambda/application; their
computation and pullback laws do not assume agreement with graph functions.
The separately constructed graph eliminator is then compared by application.
The semantic map equation here is a control, not a retained-proof translation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceListContextual

open ZFSetDependentProducts
open ZFSetContextualInterpretation (SetFamily Section Extension extensionSubstitution)
open ZFSetListContextual (listFamily nil cons NilCase ConsCase)
open ZFSetTraceContextual (piFamily piDecode lam app)

universe u
variable {Γ Δ : Type (u + 1)}

noncomputable abbrev FunctionFamily (a b : SetFamily Γ) : SetFamily Γ :=
  piFamily a (fun pair => b pair.1)

noncomputable def mapFunction {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) :
    Section (FunctionFamily (listFamily a) (listFamily b)) :=
  lam (fun pair => ZFSetList.map
    (piDecode a (fun point => b point.1) pair.1 (function pair.1)) pair.2)

noncomputable def map {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) (xs : Section (listFamily a)) :
    Section (listFamily b) := app (mapFunction function) xs

theorem map_at {a b : SetFamily Γ} (function : Section (FunctionFamily a b))
    (xs : Section (listFamily a)) (γ : Γ) :
    map function xs γ = ZFSetList.map
      (piDecode a (fun point => b point.1) γ (function γ)) (xs γ) :=
  congrFun (ZFSetTraceContextual.app_lam _ xs) γ

theorem map_nil {a b : SetFamily Γ} (function : Section (FunctionFamily a b)) :
    map function (nil a) = nil b := by
  funext γ
  rw [map_at]
  exact ZFSetList.map_nil _

theorem map_cons {a b : SetFamily Γ} (function : Section (FunctionFamily a b))
    (head : Section a) (tail : Section (listFamily a)) :
    map function (cons head tail) = cons (app function head) (map function tail) := by
  funext γ
  rw [map_at]
  change ZFSetList.map _ (ZFSetList.cons (head γ) (tail γ)) =
    ZFSetList.cons _ (map function tail γ)
  rw [ZFSetList.map_cons, map_at]
  rfl

noncomputable def composeFunctions {a b c : SetFamily Γ}
    (f : Section (FunctionFamily b c)) (g : Section (FunctionFamily a b)) :
    Section (FunctionFamily a c) :=
  lam (fun pair => piDecode b (fun point => c point.1) pair.1 (f pair.1)
    (piDecode a (fun point => b point.1) pair.1 (g pair.1) pair.2))

theorem map_composition {a b c : SetFamily Γ}
    (f : Section (FunctionFamily b c)) (g : Section (FunctionFamily a b))
    (xs : Section (listFamily a)) :
    map f (map g xs) = map (composeFunctions f g) xs := by
  funext γ
  rw [map_at, map_at, map_at]
  have computation := (piDecode a (fun point => c point.1) γ).apply_symm_apply
    (fun x => piDecode b (fun point => c point.1) γ (f γ)
      (piDecode a (fun point => b point.1) γ (g γ) x))
  change piDecode a (fun point => c point.1) γ (composeFunctions f g γ) = _ at computation
  rw [computation]
  exact ZFSetList.map_composition _ _ _

noncomputable def eliminator {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) :
    Section (piFamily (listFamily a) motive) :=
  lam (fun pair => ZFSetList.eliminate
    (fun xs => Elements (motive ⟨pair.1, xs⟩)) (zero pair.1) (step pair.1) pair.2)

noncomputable def eliminate {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) :
    Section (fun γ => motive ⟨γ, xs γ⟩) := app (eliminator motive zero step) xs

theorem eliminate_at {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) (γ : Γ) :
    eliminate motive zero step xs γ =
      ZFSetList.eliminate (fun ys => Elements (motive ⟨γ, ys⟩)) (zero γ) (step γ) (xs γ) :=
  congrFun (ZFSetTraceContextual.app_lam _ xs) γ

theorem eliminate_nil {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) :
    eliminate motive zero step (nil a) = zero := by
  funext γ
  rw [eliminate_at]
  exact ZFSetList.eliminate_nil _ _ _

theorem eliminate_cons {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive)
    (head : Section a) (tail : Section (listFamily a)) :
    eliminate motive zero step (cons head tail) =
      fun γ => step γ (head γ) (tail γ) (eliminate motive zero step tail γ) := by
  funext γ
  rw [eliminate_at]
  change ZFSetList.eliminate _ _ _ (ZFSetList.cons (head γ) (tail γ)) = _
  rw [ZFSetList.eliminate_cons, eliminate_at]

theorem graph_eliminator_comparison {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) :
    ZFSetTraceContextual.fromGraph (ZFSetListContextual.eliminator motive zero step) =
      eliminator motive zero step := ZFSetTraceContextual.lambda_agreement _

theorem graph_application_agreement {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) :
    eliminate motive zero step xs = ZFSetListContextual.eliminate motive zero step xs := by
  funext γ
  rw [eliminate_at, ZFSetListContextual.eliminate_at]

theorem map_substitution (θ : Δ → Γ) {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) (xs : Section (listFamily a)) :
    (fun δ => map function xs (θ δ)) =
      map (a := a ∘ θ) (b := b ∘ θ) (fun δ => function (θ δ)) (fun δ => xs (θ δ)) := rfl

theorem eliminate_substitution (θ : Δ → Γ) {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) :
    (fun δ => eliminate motive zero step xs (θ δ)) =
      eliminate (a := a ∘ θ) (motive ∘ extensionSubstitution θ (listFamily a))
        (fun δ => zero (θ δ)) (fun δ => step (θ δ)) (fun δ => xs (θ δ)) := rfl

namespace Controls

@[reducible] noncomputable def domain : SetFamily Γ := fun _ => ZFSetList.Controls.carrier

noncomputable def motive : SetFamily (Extension (listFamily (domain : SetFamily Γ))) :=
  fun pair => ZFSetList.Controls.varying pair.2

noncomputable def zero : NilCase (motive : SetFamily (Extension (listFamily (domain : SetFamily Γ)))) :=
  fun _ => ZFSetList.Controls.zero

noncomputable def step : ConsCase (motive : SetFamily (Extension (listFamily (domain : SetFamily Γ)))) :=
  fun _ => ZFSetList.Controls.step

theorem nil_result (γ : Γ) :
    (eliminate motive zero step (nil domain) γ).1 = ∅ := by
  rw [eliminate_nil]
  rfl

theorem cons_result (γ : Γ) :
    (eliminate motive zero step
      (cons (fun _ => ZFSetList.Controls.head) (nil domain)) γ).1 = ZFSet.powerset ∅ := by
  rw [eliminate_cons]
  rfl

theorem wrong_constant_result (γ : Γ) :
    (eliminate motive zero step
      (cons (fun _ => ZFSetList.Controls.head) (nil domain)) γ).1 ≠ ∅ := by
  rw [cons_result]
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [equal] at member
  exact ZFSet.notMem_empty _ member

end Controls

#print axioms map_nil
#print axioms map_cons
#print axioms map_composition
#print axioms eliminate_nil
#print axioms eliminate_cons
#print axioms graph_eliminator_comparison
#print axioms graph_application_agreement
#print axioms map_substitution
#print axioms eliminate_substitution
#print axioms Controls.nil_result
#print axioms Controls.cons_result
#print axioms Controls.wrong_constant_result

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceListContextual
