import Mettapedia.Logic.HOL.Embedding.ZFSetList

/-!
# Set-coded lists in the existing contextual model

List codes act pointwise on set families. Mapping and dependent elimination
are sections of the existing graph-product families, with their actual
application and computation laws. Context substitution is pullback, and the
constructed operations commute with it without an injectivity assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetListContextual

open ZFSetDependentProducts ZFSetContextualInterpretation

universe u

variable {Γ Δ : Type (u + 1)}

@[reducible] noncomputable def listFamily (a : SetFamily Γ) : SetFamily Γ :=
  fun γ => ZFSetList.listCode (a γ)

noncomputable def nil (a : SetFamily Γ) : Section (listFamily a) :=
  fun γ => ZFSetList.nil (a γ)

noncomputable def cons {a : SetFamily Γ} (head : Section a)
    (tail : Section (listFamily a)) : Section (listFamily a) :=
  fun γ => ZFSetList.cons (head γ) (tail γ)

noncomputable abbrev FunctionFamily (a b : SetFamily Γ) : SetFamily Γ :=
  piFamily a (fun pair => b pair.1)

/-- A map on lists is an actual contextual graph function. Its element
function is decoded from the caller's graph, not assumed to be a Lean map. -/
noncomputable def mapFunction {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) :
    Section (FunctionFamily (listFamily a) (listFamily b)) :=
  ZFSetContextualInterpretation.lam (fun pair =>
    ZFSetList.map (fun value => piDecode a (fun point => b point.1) pair.1
      (function pair.1) value) pair.2)

noncomputable def map {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) (xs : Section (listFamily a)) :
    Section (listFamily b) := ZFSetContextualInterpretation.app (mapFunction function) xs

theorem map_at {a b : SetFamily Γ} (function : Section (FunctionFamily a b))
    (xs : Section (listFamily a)) (γ : Γ) :
    map function xs γ = ZFSetList.map
      (fun value => piDecode a (fun point => b point.1) γ (function γ) value) (xs γ) :=
  congrFun (ZFSetContextualInterpretation.app_lam _ xs) γ

theorem map_nil {a b : SetFamily Γ} (function : Section (FunctionFamily a b)) :
    map function (nil a) = nil b := by
  funext γ
  rw [map_at]
  exact ZFSetList.map_nil _

theorem map_cons {a b : SetFamily Γ} (function : Section (FunctionFamily a b))
    (head : Section a) (tail : Section (listFamily a)) :
    map function (cons head tail) =
      cons (ZFSetContextualInterpretation.app function head) (map function tail) := by
  funext γ
  rw [map_at]
  change ZFSetList.map _ (ZFSetList.cons (head γ) (tail γ)) =
    ZFSetList.cons _ (map function tail γ)
  rw [ZFSetList.map_cons, map_at]
  rfl

noncomputable def composeFunctions {a b c : SetFamily Γ}
    (f : Section (FunctionFamily b c)) (g : Section (FunctionFamily a b)) :
    Section (FunctionFamily a c) :=
  ZFSetContextualInterpretation.lam (fun pair =>
    piDecode b (fun point => c point.1) pair.1 (f pair.1)
      (piDecode a (fun point => b point.1) pair.1 (g pair.1) pair.2))

theorem decode_composeFunctions {a b c : SetFamily Γ}
    (f : Section (FunctionFamily b c)) (g : Section (FunctionFamily a b)) (γ : Γ) :
    piDecode a (fun point => c point.1) γ (composeFunctions f g γ) =
      (fun x => piDecode b (fun point => c point.1) γ (f γ)
        (piDecode a (fun point => b point.1) γ (g γ) x)) :=
  (piDecode a (fun point => c point.1) γ).apply_symm_apply _

/-- Semantic map fusion takes the actual contextual graph composition as
its function input. It is independent of any compiled syntactic proof. -/
theorem map_composition {a b c : SetFamily Γ}
    (f : Section (FunctionFamily b c)) (g : Section (FunctionFamily a b))
    (xs : Section (listFamily a)) :
    map f (map g xs) = map (composeFunctions f g) xs := by
  funext γ
  rw [map_at, map_at, map_at, decode_composeFunctions]
  exact ZFSetList.map_composition _ _ _

abbrev NilCase {a : SetFamily Γ} (motive : SetFamily (Extension (listFamily a))) :=
  Section (fun γ => motive ⟨γ, ZFSetList.nil (a γ)⟩)

abbrev ConsCase {a : SetFamily Γ} (motive : SetFamily (Extension (listFamily a))) :=
  (γ : Γ) → (head : Elements (a γ)) → (tail : Elements (ZFSetList.listCode (a γ))) →
    Elements (motive ⟨γ, tail⟩) → Elements (motive ⟨γ, ZFSetList.cons head tail⟩)

noncomputable def eliminator {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) :
    Section (piFamily (listFamily a) motive) :=
  ZFSetContextualInterpretation.lam (fun pair =>
    ZFSetList.eliminate (fun xs => Elements (motive ⟨pair.1, xs⟩))
      (zero pair.1) (step pair.1) pair.2)

noncomputable def eliminate {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) :
    Section (fun γ => motive ⟨γ, xs γ⟩) :=
  ZFSetContextualInterpretation.app (eliminator motive zero step) xs

theorem eliminate_at {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) (γ : Γ) :
    eliminate motive zero step xs γ =
      ZFSetList.eliminate (fun ys => Elements (motive ⟨γ, ys⟩)) (zero γ) (step γ) (xs γ) :=
  congrFun (ZFSetContextualInterpretation.app_lam _ xs) γ

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

/-! ## Substitution acts through the same contextual operations -/

theorem listFamily_substitution (substitution : Δ → Γ) (a : SetFamily Γ) :
    listFamily a ∘ substitution = listFamily (a ∘ substitution) := rfl

theorem nil_substitution (substitution : Δ → Γ) (a : SetFamily Γ) :
    (fun δ => nil a (substitution δ)) = nil (a ∘ substitution) := rfl

theorem cons_substitution (substitution : Δ → Γ) {a : SetFamily Γ}
    (head : Section a) (tail : Section (listFamily a)) :
    (fun δ => cons head tail (substitution δ)) =
      cons (fun δ => head (substitution δ)) (fun δ => tail (substitution δ)) := rfl

theorem mapFunction_substitution (substitution : Δ → Γ) {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) :
    (fun δ => mapFunction function (substitution δ)) =
      mapFunction (a := a ∘ substitution) (b := b ∘ substitution)
        (fun δ => function (substitution δ)) := rfl

theorem map_substitution (substitution : Δ → Γ) {a b : SetFamily Γ}
    (function : Section (FunctionFamily a b)) (xs : Section (listFamily a)) :
    (fun δ => map function xs (substitution δ)) =
      map (a := a ∘ substitution) (b := b ∘ substitution)
        (fun δ => function (substitution δ)) (fun δ => xs (substitution δ)) := rfl

theorem eliminator_substitution (substitution : Δ → Γ) {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) :
    (fun δ => eliminator motive zero step (substitution δ)) =
      eliminator (a := a ∘ substitution)
        (motive ∘ extensionSubstitution substitution (listFamily a))
        (fun δ => zero (substitution δ)) (fun δ => step (substitution δ)) := rfl

theorem eliminate_substitution (substitution : Δ → Γ) {a : SetFamily Γ}
    (motive : SetFamily (Extension (listFamily a)))
    (zero : NilCase motive) (step : ConsCase motive) (xs : Section (listFamily a)) :
    (fun δ => eliminate motive zero step xs (substitution δ)) =
      eliminate (a := a ∘ substitution)
        (motive ∘ extensionSubstitution substitution (listFamily a))
        (fun δ => zero (substitution δ)) (fun δ => step (substitution δ))
        (fun δ => xs (substitution δ)) := rfl

#print axioms map_at
#print axioms map_nil
#print axioms map_cons
#print axioms decode_composeFunctions
#print axioms map_composition
#print axioms eliminate_at
#print axioms eliminate_nil
#print axioms eliminate_cons
#print axioms map_substitution
#print axioms eliminator_substitution
#print axioms eliminate_substitution

end Mettapedia.Logic.HOL.Embedding.ZFSetListContextual
