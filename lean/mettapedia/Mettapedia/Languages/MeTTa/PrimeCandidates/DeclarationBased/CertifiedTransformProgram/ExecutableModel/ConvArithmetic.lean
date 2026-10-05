import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueNumbers

/-!
# Addition and the iterated power set in the conversion model

Addition recurses on its second argument and the iterated power set on its
count, on the value side and on the realizer side alike. Both are valid terms
of their declared types (`valid_add`, `valid_pow`):

* **Addition.** A sum of numbers of two shapes has the sum of the shapes: the
  second shape with its final `zero` replaced by the first. Its realizers, by
  induction on the second shape: realizers of the second argument reaching
  neutral terms make both sums reach neutral spines; reaching `zero`, both sums
  compute to the first arguments' realizers; reaching `suc`, both compute to
  `suc` of the sums with the predecessors' realizers (`add_real`).
* **The iterated power set** returns sets, whose values are all related and
  realized by the terms the generic equality relates. By induction on the
  count's shape, both applications reach neutral spines, the sets' realizers at
  `zero`, or `Power` of shorter iterates, which the generic equality relates
  (`pow_real`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Morph)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape)
open StrongNormalization (NumShape)
open SetProfile (zeroNative sucNative)
open Package (U0 numT)

namespace CodeModel
namespace ConvRules

/-! ## Addition and the iterated power set on the realizer side -/

/-- Addition at its declared type on the realizer side. -/
theorem rules_add_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rules Γ (.const addN) (.pi numT (.pi numT numT)) :=
  Derivable.mono (stage_sub_rules _)
    (add_typed (names := [numN, addN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- The iterated power set at its declared type on the realizer side. -/
theorem rules_pow_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rules Γ (.const powN) (.pi numT (.pi setT setT)) :=
  Derivable.mono (stage_sub_rules _)
    (constT (allowed := allowedIn [numN, setN, powN]) (level := Tower.zero)
      (stage_declared (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (powType_typed (List.mem_cons_self ..) (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

/-- The sum of two terms. -/
abbrev addApp {n : Nat} (x y : Tower.Tm n) : Tower.Tm n := .app (.app (.const addN) x) y

/-- The iterated power set of a set. -/
abbrev powApp {n : Nat} (k X : Tower.Tm n) : Tower.Tm n := .app (.app (.const powN) k) X

section Typings

variable {T : RealizerSide Tower.Head ℕ} (ext : OverRules T) {n : Nat} {Δ : Tower.Ctx n}
include ext

theorem addApp_typed' {x y : Tower.Tm n} (tx : Typed T.R Δ x numT) (ty : Typed T.R Δ y numT) :
    Typed T.R Δ (addApp x y) numT :=
  .appElim (B := numT) (.appElim (B := .pi numT numT) (ext.typed rules_add_typed) tx) ty

theorem powApp_typed {k X : Tower.Tm n} (tk : Typed T.R Δ k numT) (tX : Typed T.R Δ X setT) :
    Typed T.R Δ (powApp k X) setT :=
  .appElim (B := setT) (.appElim (B := .pi setT setT) (ext.typed rules_pow_typed) tk) tX

theorem sucApp_typed' {a : Tower.Tm n} (ta : Typed T.R Δ a numT) :
    Typed T.R Δ (sucNative a) numT :=
  .appElim (B := numT) ext.suc_typed ta

theorem powerApp_typed {X : Tower.Tm n} (tX : Typed T.R Δ X setT) :
    Typed T.R Δ (.app (.const powerN) X) setT :=
  .appElim (B := setT) ext.power_typed tX

/-- Reducing the second argument of a sum. -/
theorem add_scrutinee_red {x y y' : Tower.Tm n} (tx : Typed T.R Δ x numT)
    (red : RedTm T.R T.roles Δ y y' numT) :
    RedTm T.R T.roles Δ (addApp x y) (addApp x y') numT :=
  ⟨WhRed.scrutinee (before := [x]) (after := []) ext.roles_add rfl red.red,
    addApp_typed' ext tx red.source, addApp_typed' ext tx red.target,
    .appCong (B := numT) (.refl (.appElim (B := .pi numT numT) (ext.typed rules_add_typed) tx)) red.equal⟩

/-- Reducing the count of an iterated power set. -/
theorem pow_scrutinee_red {k k' X : Tower.Tm n} (tX : Typed T.R Δ X setT)
    (red : RedTm T.R T.roles Δ k k' numT) :
    RedTm T.R T.roles Δ (powApp k X) (powApp k' X) setT :=
  ⟨WhRed.scrutinee (before := []) (after := [X]) ext.roles_pow rfl red.red,
    powApp_typed ext red.source tX, powApp_typed ext red.target tX,
    .appCong (B := setT) (.appCong (B := .pi setT setT) (.refl (ext.typed rules_pow_typed)) red.equal)
      (.refl tX)⟩

end Typings

/-- `add x zero = x` on the realizer side. -/
theorem rules_add_zero {n : Nat} (x : Tower.Tm n) :
    rules.computation.step (addApp x zeroNative) x :=
  equation_sound (equation_listed 0 (by decide) rfl) (fun _ => x)

/-- `add x (suc a) = suc (add x a)` on the realizer side. -/
theorem rules_add_suc {n : Nat} (x a : Tower.Tm n) :
    rules.computation.step (addApp x (sucNative a)) (sucNative (addApp x a)) :=
  equation_sound (equation_listed 1 (by decide) rfl) (consSub a fun _ => x)

/-- `pow zero X = X` on the realizer side. -/
theorem rules_pow_zero {n : Nat} (X : Tower.Tm n) :
    rules.computation.step (powApp zeroNative X) X :=
  equation_sound (equation_listed 2 (by decide) rfl) (fun _ => X)

/-- `pow (suc a) X = Power (pow a X)` on the realizer side. -/
theorem rules_pow_suc {n : Nat} (a X : Tower.Tm n) :
    rules.computation.step (powApp (sucNative a) X) (.app (.const powerN) (powApp a X)) :=
  equation_sound (equation_listed 3 (by decide) rfl) (consSub X fun _ => a)

section Model

variable (X : TExtension) (v : Nat → Nat) {T : RealizerSide Tower.Head ℕ}

/-- Terms reaching neutral terms are related by the realizers of every shape. -/
theorem numShapeRel_of_neRel {m : Nat} {Δ : Tower.Ctx m} {A t t' : Tower.Tm m}
    (ne : NeRel T Δ A t t') :
    ∀ sh : NumShape, NumShapeRel T numN zeroN sucN sh Δ A t t'
  | .zero => .inl ne
  | .suc _ => .inl ne
  | .star => ne

section Constants

variable (ext : OverRules T)
include ext

/-! ## Addition -/

/-- **The realizers of a sum.** Realizers of numbers of two shapes, added,
realize the sum of the shapes, by induction on the second shape. -/
theorem add_real {m r : Nat} {ξ : World (nmodel X v T).reading m}
    {Δ : Tower.Ctx r} {NP : NPack (nmodel X v T) m}
    (den : DenN (nmodel X v T) ξ numT NP) {x₀ : Tower.Tm m} {s : NumShape}
    (hx₀ : X.VShape v x₀ s) {x x' : Tower.Tm r} (rx : (NP.real x₀).rel Δ numT x x') :
    ∀ (t : NumShape) {y₀ : Tower.Tm m}, X.VShape v y₀ t → ∀ {y y' : Tower.Tm r},
      (NP.real y₀).rel Δ numT y y' →
        (NP.real (addApp x₀ y₀)).rel Δ numT (addApp x y) (addApp x' y') := by
  obtain ⟨tx, tx'⟩ := ECand.typed _ rx
  have numType : IsType T.R Δ numT := ext.numType
  -- Second arguments reaching neutral terms: both sums reach neutral spines.
  have neutralCase : ∀ {y y' : Tower.Tm r}, NeRel T Δ numT y y' →
      NeRel T Δ numT (addApp x y) (addApp x' y') := by
    intro y y' ne
    obtain ⟨w, w', r₀, r₀', nw, nw', cv⟩ := ne
    refine ⟨addApp x w, addApp x' w', (add_scrutinee_red ext tx r₀).trans (RedTm.refl
      (addApp_typed' ext tx r₀.target)), (add_scrutinee_red ext tx' r₀').trans (RedTm.refl
      (addApp_typed' ext tx' r₀'.target)),
      Neutral.stuck_single (before := [x]) (after := []) ext.roles_add rfl nw,
      Neutral.stuck_single (before := [x']) (after := []) ext.roles_add rfl nw', ?_⟩
    exact T.laws.convNe_app (B := numT)
      (T.laws.convNe_app (B := .pi numT numT) (T.laws.convNe_const addN (ext.typed rules_add_typed))
        (ECand.escape _ rx))
      (T.laws.convTm_of_convNe (.inl nw) (.inl nw') cv)
  intro t
  induction t with
  | zero =>
      intro y₀ hy₀ y y' ry
      rw [num_real X v ext den (X.hasShape_add v hx₀ hy₀)]
      rcases (num_real X v ext den hy₀ Δ numT y y').mp ry with ne | ⟨-, r₀, r₀', -⟩
      · exact numShapeRel_of_neRel (neutralCase ne) _
      have red := (add_scrutinee_red ext tx r₀).trans (RedTm.root (ext.step (rules_add_zero x))
        (addApp_typed' ext tx r₀.target) tx)
      have red' := (add_scrutinee_red ext tx' r₀').trans (RedTm.root (ext.step (rules_add_zero x'))
        (addApp_typed' ext tx' r₀'.target) tx')
      rw [← num_real X v ext den (X.hasShape_add v hx₀ hy₀)]
      have h : (NP.real (addApp x₀ y₀)).rel Δ numT x x' := by
        rw [num_real X v ext den (X.hasShape_add v hx₀ hy₀)]
        exact (num_real X v ext den hx₀ Δ numT x x').mp rx
      exact ECand.expand _ red red' h
  | suc t ih =>
      intro y₀ hy₀ y y' ry
      cases hy₀ with
      | @suc _ c _ redValue hc =>
          have shape : X.VShape v (addApp x₀ y₀) (.suc (shapeAdd s t)) :=
            X.hasShape_add v hx₀ (.suc redValue hc)
          rw [num_real X v ext den shape]
          rcases (num_real X v ext den (.suc redValue hc) Δ numT y y').mp ry with
            ne | ⟨-, b, b', r₀, r₀', cv, hb⟩
          · exact numShapeRel_of_neRel (neutralCase ne) _
          have rb := (num_real X v ext den hc Δ numT b b').mpr hb
          have sums := ih hc rb
          obtain ⟨tb, tb'⟩ := ECand.typed _ rb
          have red := (add_scrutinee_red ext tx r₀).trans (RedTm.root (ext.step (rules_add_suc x b))
            (addApp_typed' ext tx r₀.target) (sucApp_typed' ext (addApp_typed' ext tx tb)))
          have red' := (add_scrutinee_red ext tx' r₀').trans (RedTm.root (ext.step (rules_add_suc x' b'))
            (addApp_typed' ext tx' r₀'.target) (sucApp_typed' ext (addApp_typed' ext tx' tb')))
          have conv : T.E.convTm Δ (sucNative (addApp x b)) (sucNative (addApp x' b')) numT :=
            T.laws.convTm_of_convNe (.inr (.inl ⟨sucN, 1, [addApp x b], ext.roles_suc, rfl⟩))
              (.inr (.inl ⟨sucN, 1, [addApp x' b'], ext.roles_suc, rfl⟩))
              (T.laws.convNe_app (B := numT) (T.laws.convNe_const sucN ext.suc_typed)
                (ECand.escape _ sums))
          exact .inr ⟨RedTy.refl numType, addApp x b, addApp x' b', red, red',
            T.laws.convTm_expand red red' conv,
            (num_real X v ext den (X.hasShape_add v hx₀ hc) Δ numT _ _).mp sums⟩
  | star =>
      intro y₀ hy₀ y y' ry
      rw [num_real X v ext den (X.hasShape_add v hx₀ hy₀)]
      exact neutralCase ((num_real X v ext den hy₀ Δ numT y y').mp ry)

/-- The stage of the numbers and their constructors, with the sets and `Power`,
is sound for the model. -/
theorem powStage_typedSoundN : TypedSoundN powStage (nmodel X v T) :=
  stage_typedSoundN_of X v ext fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact valid_num X v ext
    · exact valid_zero X v ext
    · exact valid_suc X v ext
    · exact valid_set X v ext
    · exact valid_power X v ext

/-- **Addition is valid**: it sends numbers of two shapes to the number of the
sum of the shapes, and realizers to realizers of the sum. -/
theorem valid_add : ValidTmN (nmodel X v T) .nil (.const addN) addType := by
  have laws := nmodel_laws X v T
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN (numStage_typedSoundN X v ext)
    (addType_typed (names := [numN]) (List.mem_cons_self ..)) trivial
  refine ValidTmN.close laws (.snoc (.snoc .nil numT) numT) (C := numT) (f := .const addN)
    (validT.validTy (LevelTower.IsUniverse.sort _) ext.isUniverse_zero) partsT (ext.typed rules_add_typed)
    (fun args short => .inr (.inr ⟨addN, args, 2, .inr ⟨_, ext.roles_add⟩, short, rfl⟩))
    ⟨ValidTyN.liftClosed ((valid_num X v ext).validTy (LevelTower.IsUniverse.sort _)
      ext.isUniverse_zero) _, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨⟨-, RA, denA, hx, rx⟩, RB, denB, hy, ry⟩ := e
  change DenN (nmodel X v T) ξ numT RA at denA
  change RA.rel (σ 1) (σ' 1) at hx
  change (RA.real (σ 1)).rel Δ numT (ς 1) (ς' 1) at rx
  change DenN (nmodel X v T) ξ numT RB at denB
  change RB.rel (σ 0) (σ' 0) at hy
  change (RB.real (σ 0)).rel Δ numT (ς 0) (ς' 0) at ry
  change DenN (nmodel X v T) ξ numT P at den
  show P.rel (addApp (σ 1) (σ 0)) (addApp (σ' 1) (σ' 0)) ∧
    (P.real (addApp (σ 1) (σ 0))).rel Δ numT (addApp (ς 1) (ς 0)) (addApp (ς' 1) (ς' 0))
  obtain rfl := ValueSide.DenS.deterministic (nmodel_laws X v T).value denA den
  obtain rfl := ValueSide.DenS.deterministic (nmodel_laws X v T).value denB denA
  have hx' := hx
  have hy' := hy
  rw [num_den X v denA] at hx' hy'
  obtain ⟨s, hs, hs'⟩ := ValueSide.numIndPack_rel.mp hx'
  obtain ⟨t, ht, ht'⟩ := ValueSide.numIndPack_rel.mp hy'
  refine ⟨?_, add_real X v ext denA hs rx t ht ry⟩
  rw [num_den X v denA]
  exact ValueSide.numIndPack_rel.mpr
    ⟨shapeAdd s t, X.hasShape_add v hs ht, X.hasShape_add v hs' ht'⟩

/-! ## The iterated power set -/

/-- **The realizers of an iterated power set.** Realizers of a number of a shape
and of a set give iterated power sets related by `top`: by induction on the
shape. -/
theorem pow_real {m r : Nat} {ξ : World (nmodel X v T).reading m}
    {Δ : Tower.Ctx r} {NP : NPack (nmodel X v T) m}
    (den : DenN (nmodel X v T) ξ numT NP) {Y Y' : Tower.Tm r}
    (rX : (ECand.top T).rel Δ setT Y Y') :
    ∀ (t : NumShape) {k₀ : Tower.Tm m}, X.VShape v k₀ t → ∀ {k k' : Tower.Tm r},
      (NP.real k₀).rel Δ numT k k' →
        (ECand.top T).rel Δ setT (powApp k Y) (powApp k' Y') := by
  obtain ⟨tX, tX', cX⟩ := rX
  -- Counts reaching neutral terms: both applications reach neutral spines.
  have neutralCase : ∀ {k k' : Tower.Tm r}, NeRel T Δ numT k k' →
      (ECand.top T).rel Δ setT (powApp k Y) (powApp k' Y') := by
    intro k k' ne
    obtain ⟨w, w', r₀, r₀', nw, nw', cv⟩ := ne
    have redN := pow_scrutinee_red ext tX r₀
    have redN' := pow_scrutinee_red ext tX' r₀'
    refine ECand.expand _ redN redN' (ECand.neutral _
      (Neutral.stuck_single (before := []) (after := [Y]) ext.roles_pow rfl nw)
      (Neutral.stuck_single (before := []) (after := [Y']) ext.roles_pow rfl nw')
      redN.target redN'.target ?_)
    exact T.laws.convNe_app (B := setT)
      (T.laws.convNe_app (B := .pi setT setT) (T.laws.convNe_const powN (ext.typed rules_pow_typed))
        (T.laws.convTm_of_convNe (.inl nw) (.inl nw') cv)) cX
  intro t
  induction t with
  | zero =>
      intro k₀ hk₀ k k' rk
      rcases (num_real X v ext den hk₀ Δ numT k k').mp rk with ne | ⟨-, r₀, r₀', -⟩
      · exact neutralCase ne
      have red := (pow_scrutinee_red ext tX r₀).trans (RedTm.root (ext.step (rules_pow_zero Y))
        (powApp_typed ext r₀.target tX) tX)
      have red' := (pow_scrutinee_red ext tX' r₀').trans (RedTm.root (ext.step (rules_pow_zero Y'))
        (powApp_typed ext r₀'.target tX') tX')
      exact ECand.expand _ red red' ⟨tX, tX', cX⟩
  | suc t ih =>
      intro k₀ hk₀ k k' rk
      cases hk₀ with
      | @suc _ c _ _ hc =>
          rcases (num_real X v ext den (.suc (by assumption) hc) Δ numT k k').mp rk with
            ne | ⟨-, b, b', r₀, r₀', -, hb⟩
          · exact neutralCase ne
          have iterates := ih hc ((num_real X v ext den hc Δ numT b b').mpr hb)
          obtain ⟨ti, ti', ci⟩ := iterates
          have red := (pow_scrutinee_red ext tX r₀).trans (RedTm.root (ext.step (rules_pow_suc b Y))
            (powApp_typed ext r₀.target tX) (powerApp_typed ext ti))
          have red' := (pow_scrutinee_red ext tX' r₀').trans
            (RedTm.root (ext.step (rules_pow_suc b' Y'))
              (powApp_typed ext r₀'.target tX') (powerApp_typed ext ti'))
          exact ECand.expand _ red red' ⟨powerApp_typed ext ti, powerApp_typed ext ti',
            T.laws.convTm_of_convNe (.inl (.rigid [powApp b Y] ext.power))
              (.inl (.rigid [powApp b' Y'] ext.power))
              (T.laws.convNe_app (B := setT) (T.laws.convNe_const powerN ext.power_typed) ci)⟩
  | star =>
      intro k₀ hk₀ k k' rk
      exact neutralCase ((num_real X v ext den hk₀ Δ numT k k').mp rk)

/-- **The iterated power set is valid**: it returns sets, and its realizers are
related by the generic equality. -/
theorem valid_pow : ValidTmN (nmodel X v T) .nil (.const powN) powType := by
  have laws := nmodel_laws X v T
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN (numSetStage_typedSoundN X v ext)
    (powType_typed (names := [numN, setN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))) trivial
  refine ValidTmN.close laws (.snoc (.snoc .nil numT) setT) (C := setT) (f := .const powN)
    (validT.validTy (LevelTower.IsUniverse.sort _) ext.isUniverse_zero) partsT (ext.typed rules_pow_typed)
    (fun args short => .inr (.inr ⟨powN, args, 2, .inr ⟨_, ext.roles_pow⟩, short, rfl⟩))
    ⟨ValidTyN.liftClosed ((valid_set X v ext).validTy (LevelTower.IsUniverse.sort _)
      ext.isUniverse_zero) _, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨⟨-, RA, denA, hk, rk⟩, RB, denB, -, rX⟩ := e
  change DenN (nmodel X v T) ξ numT RA at denA
  change RA.rel (σ 1) (σ' 1) at hk
  change (RA.real (σ 1)).rel Δ numT (ς 1) (ς' 1) at rk
  change DenN (nmodel X v T) ξ setT RB at denB
  change (RB.real (σ 0)).rel Δ setT (ς 0) (ς' 0) at rX
  change DenN (nmodel X v T) ξ setT P at den
  show P.rel (powApp (σ 1) (σ 0)) (powApp (σ' 1) (σ' 0)) ∧
    (P.real (powApp (σ 1) (σ 0))).rel Δ setT (powApp (ς 1) (ς 0)) (powApp (ς' 1) (ς' 0))
  rw [set_den X v denB] at rX
  rw [set_den X v den]
  have hk' := hk
  rw [num_den X v denA] at hk'
  obtain ⟨t, ht, -⟩ := ValueSide.numIndPack_rel.mp hk'
  exact ⟨trivial, pow_real X v ext denA rX t ht rk⟩

end Constants

end Model

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
