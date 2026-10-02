import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines

/-!
# The numbers, the sets and arithmetic in the transport value model

In the transport value model on the skeleton-free value side the numbers relate
the terms with one shape, where a shape may be the daimon, and a number of a
shape is realized by the realizer side's numerals of that shape. The sets, a
rigid type, relate every two terms and are realized by every strongly
normalizing term.

* The sets are a type of the lowest universe, a leaf, realized by themselves.
* `zero` has shape zero and realizes it; `suc` sends a number of a shape to the
  successor shape, and a realizer of a shape to a realizer of the successor
  shape.
* `Power` returns sets.
* Addition recurses on its second argument, on the value side and on the
  realizer side alike: the shape of a sum is the shape of its second argument
  with the final `zero` replaced by the shape of the first, and a sum of
  realizers realizes the sum of their shapes.
* The iterated power set returns sets; its applications to realizers are
  strongly normalizing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape Daimonic)
open Package (U0 numT)

namespace CodeModel

/-! ## Arithmetic on the realizer side -/

/-- The sets do not compute in the object package. -/
theorem set_sn {n : Nat} : SN objectRules (setT : Tower.Tm n) :=
  const_sn fun _ _ role => by
    change objectRoles setN = _ at role
    rw [objectRoles_of (by decide) (by decide) (by decide) (by decide), roles_set] at role
    cases role

/-- The shape of a sum: the second shape with its final `zero` replaced by the
first. -/
def shapeAdd (s : NumShape) : NumShape → NumShape
  | .zero => s
  | .suc t => .suc (shapeAdd s t)
  | .star => .star

/-- Both arguments of a spine of two strongly normalizing arguments are strongly
normalizing. -/
private theorem two_sn {n : Nat} {x y : Tower.Tm n} (sx : SN objectRules x)
    (sy : SN objectRules y) : ∀ a ∈ [x, y], SN objectRules a := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact sx
  · exact sy

/-- **A sum of realizers realizes the sum of their shapes**, by induction on the
second shape: at `zero` its root reducts are reducts of the first realizer, and
at `suc m` successors of sums with `m`. -/
theorem numReal_add : ∀ (t : NumShape) {s : NumShape} {n : Nat} {u w : Tower.Tm n},
    (NumReal objectReflects objectNumerals s).mem u →
      (NumReal objectReflects objectNumerals t).mem w →
        (NumReal objectReflects objectNumerals (shapeAdd s t)).mem
          (.app (.app (.const addN) u) w) := by
  intro t
  induction t with
  | zero =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem objectShape _ objectRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add step with ⟨-, rfl⟩ | ⟨m, rfl, -⟩
      · exact KCand.reducts _ hu hu'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hw hw'
        cases same
  | suc t ih =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem objectShape _ objectRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add step with ⟨rfl, -⟩ | ⟨m, rfl, rfl⟩
      · cases NumReal.shape_of_zero objectReflects objectNumerals hw hw'
      · obtain ⟨_, same, hm⟩ := NumReal.shape_of_suc objectReflects objectNumerals hw hw'
        cases same
        exact NumReal.suc_mem objectReflects objectNumerals objectShape
          (ih (KCand.reducts _ hu hu') hm)
  | star =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem objectShape _ objectRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, -, hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add step with ⟨rfl, -⟩ | ⟨m, rfl, -⟩
      · cases NumReal.shape_of_zero objectReflects objectNumerals hw hw'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hw hw'
        cases same

/-- **An iterated power set of realizers is strongly normalizing**, by induction
on the shape of the number: at `zero` a root reduct is a reduct of the set, and
at `suc m` the power set of a shorter iterate. -/
theorem pow_sn : ∀ (s : NumShape) {n : Nat} {u w : Tower.Tm n},
    (NumReal objectReflects objectNumerals s).mem u → SN objectRules w →
      SN objectRules (.app (.app (.const powN) u) w) := by
  have powerStuck : ∀ arity scrutinee, objectRoles powerN = .computes arity scrutinee →
      1 < arity := by
    intro _ _ role
    rw [(objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_power]
      at role
    cases role
  intro s
  induction s with
  | zero =>
      intro n u w hu sw
      refine KCand.computingSpine_mem objectShape (KCand.sn' objectReflects) objectRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_pow step with ⟨-, rfl⟩ | ⟨m, rfl, -⟩
      · exact sw.reducts hw'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hu hu'
        cases same
  | suc s ih =>
      intro n u w hu sw
      refine KCand.computingSpine_mem objectShape (KCand.sn' objectReflects) objectRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_pow step with ⟨rfl, -⟩ | ⟨m, rfl, rfl⟩
      · cases NumReal.shape_of_zero objectReflects objectNumerals hu hu'
      · obtain ⟨_, same, hm⟩ := NumReal.shape_of_suc objectReflects objectNumerals hu hu'
        cases same
        exact SN.constSpine objectShape (args := [_]) powerStuck
          (by simpa using ih hm (sw.reducts hw'))
  | star =>
      intro n u w hu sw
      refine KCand.computingSpine_mem objectShape (KCand.sn' objectReflects) objectRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', -⟩ := ArgsStep.star_two steps
      rcases objectStep_pow step with ⟨rfl, -⟩ | ⟨m, rfl, -⟩
      · cases NumReal.shape_of_zero objectReflects objectNumerals hu hu'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc objectReflects objectNumerals hu hu'
        cases same

variable (v : Nat → Nat)

/-! ## Packs at every world -/

/-- The pack of the numbers at every world. -/
abbrev vnumD : ∀ {m : Nat}, World (vmodel v).reading m → ValueSide.Pack (vmodel v).value m :=
  fun {m} _ => ValueSide.numIndPack (vmodel v).value m

/-- The pack of the sets at every world. -/
abbrev vsetD : ∀ {m : Nat}, World (vmodel v).reading m → ValueSide.Pack (vmodel v).value m :=
  fun {m} _ => ValueSide.Pack.total (vmodel v).value m

/-- The pack of a function type between packs given at every world. -/
abbrev varrowD (D C : ∀ {m : Nat}, World (vmodel v).reading m → ValueSide.Pack (vmodel v).value m) :
    ∀ {m : Nat}, World (vmodel v).reading m → ValueSide.Pack (vmodel v).value m :=
  fun ξ => (ValueSide.PiPack.arrow ξ D C).piPack

/-! ## The sets -/

/-- The sets are rigid on the value side. -/
theorem vmodel_roles_set : (vmodel v).value.roles setN = .rigid :=
  (tmodelRoles_eq (by decide)).trans
    ((modelRoles_of (name := setN) (by decide) (by decide) (by decide) (by decide)).trans roles_set)

/-- The sets, a rigid type, at every level and world. -/
theorem vinterp_set (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ setT (vsetD v ξ) :=
  ValueSide.SInterp.rigid (args := []) .refl (vmodel_roles_set v)
    (by change setN ≠ propN; decide) (by change setN ≠ holdsN; decide)

/-- The sets are of one shape with themselves: a leaf. -/
theorem vshape_set (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ setT setT := by
  have leaf := ValueSide.Shape.of_methodForm (vmodel_valueLaws v) (vinterp_set v l ξ) .refl
    (.inr (.inr (.inr ⟨setN, [], rfl, vmodel_roles_set v, by change setN ≠ propN; decide,
      by change setN ≠ holdsN; decide⟩)))
  exact .total leaf leaf

/-- **The sets are a type of the lowest universe**: at every world they are a
leaf interpreted at the lowest level, and the constant is strongly
normalizing. -/
theorem vmodel_valid_set : ModelSN.ValidTmS (vmodel v) .nil (.const setN) U0 := by
  refine ⟨ModelSN.ValidTyS.sort (LevelTower.IsUniverse.sort _), fun {_ _ ξ σ σ' ς} _ {P} den => ?_⟩
  rw [ModelSN.DenS.sort_inv (vmodel_laws v) (LevelTower.IsUniverse.sort _) den]
  refine ⟨fun {_ ξ' ρ} _ => ?_, set_sn⟩
  exact ⟨_, vinterp_set v _ ξ', vinterp_set v _ ξ', vshape_set v _ ξ'⟩

/-! ## Interpretations of the declared types -/

/-- The numbers at every level and world. -/
theorem vinterp_num (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ numT (vnumD v ξ) :=
  ValueSide.InterpAt.num (vmodel_valueLaws v) l .refl

/-- The function type between the numbers. -/
theorem vinterp_numArrow (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ (.pi numT numT) (varrowD v (vnumD v) (vnumD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => vinterp_num v l _)
    (fun {_ _ _} _ {_} _ => vinterp_num v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The function type between the sets. -/
theorem vinterp_setArrow (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ (.pi setT setT) (varrowD v (vsetD v) (vsetD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => vinterp_set v l _)
    (fun {_ _ _} _ {_} _ => vinterp_set v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of `Power`. -/
theorem vinterp_powerType (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ (liftClosed powerType)
      (varrowD v (vsetD v) (vsetD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => vinterp_set v l _)
    (fun {_ _ _} _ {_} _ => vinterp_set v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of addition. -/
theorem vinterp_addType (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ (liftClosed addType)
      (varrowD v (vnumD v) (varrowD v (vnumD v) (vnumD v)) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => vinterp_num v l _)
    (fun {_ _ _} _ {_} _ => vinterp_numArrow v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of the iterated power set. -/
theorem vinterp_powType (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ (liftClosed powType)
      (varrowD v (vnumD v) (varrowD v (vsetD v) (vsetD v)) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => vinterp_num v l _)
    (fun {_ _ _} _ {_} _ => vinterp_setArrow v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-! ## `zero` and `suc` -/

/-- **`zero` has shape zero and realizes it.** -/
theorem vmodel_valid_zero : ModelSN.ValidTmS (vmodel v) .nil (.const zeroN) numT := by
  have shape : ∀ {m : Nat}, VShape v (.const zeroN : Tower.Tm m) .zero := HasShape.zero .refl
  refine ModelSN.ValidTmS.closed (vmodel_laws v) numT_sn (D := vnumD v)
    (fun ξ => ⟨0, vinterp_num v 0 ξ⟩)
    (fun _ => ValueSide.numIndPack_rel.mpr ⟨.zero, shape, shape⟩) (fun {_} _ {r} => ?_)
  change ((ValueSide.numIndPack (vmodel v).value _).real (.const zeroN)).mem
    (.const zeroN : Tower.Tm r)
  rw [vnumIndPack_real v shape]
  exact NumReal.zero_mem objectReflects objectNumerals objectShape

/-- **`suc` sends a number of a shape to the successor shape**, and realizers
of a shape to realizers of the successor shape. -/
theorem vmodel_valid_suc : ModelSN.ValidTmS (vmodel v) .nil (.const sucN) (.pi numT numT) := by
  refine ModelSN.ValidTmS.closed (vmodel_laws v)
    (SN.pi (RootShape.spineHeaded objectShape) numT_sn numT_sn)
    (D := varrowD v (vnumD v) (vnumD v))
    (fun ξ => ⟨0, vinterp_numArrow v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ _ _ a b _ related
    obtain ⟨s, ha, hb⟩ := ValueSide.numIndPack_rel.mp related
    exact ValueSide.numIndPack_rel.mpr ⟨.suc s, .suc .refl ha, .suc .refl hb⟩
  · show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨const_sn fun _ _ role => ?_, fun {_ ξ' ρ} _ {a} ha {_} ρr u hu => ?_⟩
    · change objectRoles sucN = _ at role
      rw [objectRoles_suc] at role
      cases role
    · obtain ⟨s, shape, -⟩ := ValueSide.numIndPack_rel.mp ha
      change ((ValueSide.numIndPack (vmodel v).value _).real a).mem u at hu
      change ((ValueSide.numIndPack (vmodel v).value _).real (.app (.const sucN) a)).mem
        (.app (.const sucN) u)
      have shape' : VShape v (.app (.const sucN) a) (.suc s) := .suc .refl shape
      rw [vnumIndPack_real v shape] at hu
      rw [vnumIndPack_real v shape']
      exact NumReal.suc_mem objectReflects objectNumerals objectShape hu

/-- **`Power` returns sets.** -/
theorem vmodel_valid_power : ModelSN.ValidTmS (vmodel v) .nil (.const powerN) powerType := by
  have rigid : objectRoles powerN = .rigid :=
    (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_power
  have stuck : ∀ arity scrutinee, objectRoles powerN = .computes arity scrutinee →
      1 < arity := by
    intro _ _ role
    rw [rigid] at role
    cases role
  refine ModelSN.ValidTmS.closed (vmodel_laws v)
    (SN.pi (RootShape.spineHeaded objectShape) set_sn set_sn)
    (D := varrowD v (vsetD v) (vsetD v))
    (fun ξ => ⟨0, vinterp_powerType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ _ _ _ _ _ _
    trivial
  · show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨const_sn fun _ _ role => ?_, fun {_ _ _} _ {_} _ {_} _ u hu => ?_⟩
    · rw [rigid] at role
      cases role
    · have sn : SN objectRules u := hu
      exact SN.constSpine objectShape (args := [u]) stuck (by simpa using sn)

/-! ## Addition and the iterated power set -/

/-- **A sum has the sum of its arguments' shapes** on the value side. -/
theorem vhasShape_add {n : Nat} {x y : Tower.Tm n} {s t : NumShape}
    (left : VShape v x s) (right : VShape v y t) :
    VShape v (.app (.app (.const addN) x) y) (shapeAdd s t) := by
  induction right with
  | zero red =>
      exact HasShape.expand
        (Relation.ReflTransGen.tail (vadd_scrutinee v x red) (vadd_zero_step v x)) left
  | suc red _ ih =>
      exact .suc (Relation.ReflTransGen.tail (vadd_scrutinee v x red) (vadd_suc_step v x _)) ih
  | star red daimonic =>
      exact .star (vadd_scrutinee v x red)
        (Daimonic.stuck (before := [x]) (after := []) tmodelRoles_add rfl daimonic)

/-- A partial application of a computing constant of arity two to one strongly
normalizing argument is strongly normalizing. -/
theorem computes2_partial_sn {c : DeclName} {scrutinee : InspectTree}
    (role : objectRoles c = .computes 2 scrutinee) {n : Nat} {u : Tower.Tm n}
    (su : SN objectRules u) : SN objectRules (.app (.const c) u) :=
  SN.constSpine objectShape (args := [u])
    (fun _ _ role' => by rw [role] at role'; cases role'; exact Nat.lt_succ_self 1)
    (by simpa using su)

/-- A computing constant of arity two is strongly normalizing. -/
theorem computes2_const_sn {c : DeclName} {scrutinee : InspectTree}
    (role : objectRoles c = .computes 2 scrutinee) {n : Nat} :
    SN objectRules (.const c : Tower.Tm n) :=
  SN.constSpine objectShape (args := [])
    (fun _ _ role' => by rw [role] at role'; cases role'; exact Nat.zero_lt_two) (by simp)

/-- **Addition sends numbers of two shapes to the number of the sum of the
shapes**, and realizers to the realizer of the sum. -/
theorem vmodel_valid_add : ModelSN.ValidTmS (vmodel v) .nil (.const addN) addType := by
  refine ModelSN.ValidTmS.closed (vmodel_laws v)
    (SN.pi (RootShape.spineHeaded objectShape) numT_sn
      (SN.pi (RootShape.spineHeaded objectShape) numT_sn numT_sn))
    (D := varrowD v (vnumD v) (varrowD v (vnumD v) (vnumD v)))
    (fun ξ => ⟨0, vinterp_addType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ ρ _ a b _ related _ _ ρ' _ c d _ related'
    obtain ⟨s, ha, hb⟩ := ValueSide.numIndPack_rel.mp related
    obtain ⟨t, hc, hd⟩ := ValueSide.numIndPack_rel.mp related'
    exact ValueSide.numIndPack_rel.mpr ⟨shapeAdd s t,
      vhasShape_add v (vshape_rename v ρ' ha) hc, vhasShape_add v (vshape_rename v ρ' hb) hd⟩
  · show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨computes2_const_sn objectRoles_add, fun {_ ξ' ρ} _ {a} ha {_} ρr u hu => ?_⟩
    show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨computes2_partial_sn objectRoles_add (KCand.sn _ hu),
      fun {_ ξ'' ρ'} _ {c} hc {_} ρr' u' hu' => ?_⟩
    obtain ⟨s, sa, -⟩ := ValueSide.numIndPack_rel.mp ha
    obtain ⟨t, sc, -⟩ := ValueSide.numIndPack_rel.mp hc
    have sa' := vshape_rename v ρ' sa
    change ((ValueSide.numIndPack (vmodel v).value _).real a).mem u at hu
    change ((ValueSide.numIndPack (vmodel v).value _).real c).mem u' at hu'
    change ((ValueSide.numIndPack (vmodel v).value _).real
      (.app (.app (.const addN) (Presentation.rename ρ' a)) c)).mem
      (.app (.app (.const addN) (Presentation.rename ρr' u)) u')
    rw [vnumIndPack_real v sa] at hu
    rw [vnumIndPack_real v sc] at hu'
    rw [vnumIndPack_real v (vhasShape_add v sa' sc)]
    exact numReal_add t (KCand.rename _ ρr' hu) hu'

/-- **The iterated power set returns sets**; its applications to realizers are
strongly normalizing. -/
theorem vmodel_valid_pow : ModelSN.ValidTmS (vmodel v) .nil (.const powN) powType := by
  refine ModelSN.ValidTmS.closed (vmodel_laws v)
    (SN.pi (RootShape.spineHeaded objectShape) numT_sn
      (SN.pi (RootShape.spineHeaded objectShape) set_sn set_sn))
    (D := varrowD v (vnumD v) (varrowD v (vsetD v) (vsetD v)))
    (fun ξ => ⟨0, vinterp_powType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    trivial
  · show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨computes2_const_sn objectRoles_pow, fun {_ ξ' ρ} _ {a} ha {_} ρr u hu => ?_⟩
    show (ValueSide.PiPack.real (V := (vmodel v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨computes2_partial_sn objectRoles_pow (KCand.sn _ hu),
      fun {_ _ _} _ {_} _ {_} ρr' u' hu' => ?_⟩
    obtain ⟨s, sa, -⟩ := ValueSide.numIndPack_rel.mp ha
    change ((ValueSide.numIndPack (vmodel v).value _).real a).mem u at hu
    rw [vnumIndPack_real v sa] at hu
    exact pow_sn s (KCand.rename _ ρr' hu) hu'

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
