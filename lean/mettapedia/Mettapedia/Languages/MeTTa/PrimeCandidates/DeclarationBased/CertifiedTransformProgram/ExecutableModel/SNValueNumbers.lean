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
open Package (U0 numT numRecName)

namespace CodeModel

namespace TExtension

variable (X : TExtension)

/-! ## Arithmetic on the realizer side -/

/-- The sets do not compute on the realizer side. -/
theorem set_sn {n : Nat} : SN X.realRules (setT : Tower.Tm n) :=
  X.const_sn fun _ _ role => by
    change X.realRoles setN = _ at role
    rw [X.realRoles_declared (c := setN) (by decide),
      objectRoles_of (by decide) (by decide) (by decide) (by decide), roles_set] at role
    cases role

end TExtension

/-- The shape of a sum: the second shape with its final `zero` replaced by the
first. -/
def shapeAdd (s : NumShape) : NumShape → NumShape
  | .zero => s
  | .suc t => .suc (shapeAdd s t)
  | .star => .star

/-- Both arguments of a spine of two strongly normalizing arguments are strongly
normalizing. -/
private theorem two_sn {R : Rules Tower.Head} {n : Nat} {x y : Tower.Tm n} (sx : SN R x)
    (sy : SN R y) : ∀ a ∈ [x, y], SN R a := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact sx
  · exact sy

namespace TExtension

variable (X : TExtension)

/-- **A sum of realizers realizes the sum of their shapes**, by induction on the
second shape: at `zero` its root reducts are reducts of the first realizer, and
at `suc m` successors of sums with `m`. -/
theorem numReal_add : ∀ (t : NumShape) {s : NumShape} {n : Nat} {u w : Tower.Tm n},
    (NumReal X.realReflects X.realNumerals s).mem u →
      (NumReal X.realReflects X.realNumerals t).mem w →
        (NumReal X.realReflects X.realNumerals (shapeAdd s t)).mem
          (.app (.app (.const addN) u) w) := by
  intro t
  induction t with
  | zero =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem X.realShape _ X.realRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add (X.realStep_declared (by decide) step) with ⟨-, rfl⟩ | ⟨m, rfl, -⟩
      · exact KCand.reducts _ hu hu'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hw hw'
        cases same
  | suc t ih =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem X.realShape _ X.realRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add (X.realStep_declared (by decide) step) with ⟨rfl, -⟩ | ⟨m, rfl, rfl⟩
      · cases NumReal.shape_of_zero X.realReflects X.realNumerals hw hw'
      · obtain ⟨_, same, hm⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hw hw'
        cases same
        exact NumReal.suc_mem X.realReflects X.realNumerals X.realShape
          (ih (KCand.reducts _ hu hu') hm)
  | star =>
      intro s n u w hu hw
      refine KCand.computingSpine_mem X.realShape _ X.realRoles_add (args := [u, w]) rfl
        (two_sn (KCand.sn _ hu) (KCand.sn _ hw)) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, -, hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_add (X.realStep_declared (by decide) step) with ⟨rfl, -⟩ | ⟨m, rfl, -⟩
      · cases NumReal.shape_of_zero X.realReflects X.realNumerals hw hw'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hw hw'
        cases same

/-- **An iterated power set of realizers is strongly normalizing**, by induction
on the shape of the number: at `zero` a root reduct is a reduct of the set, and
at `suc m` the power set of a shorter iterate. -/
theorem pow_sn : ∀ (s : NumShape) {n : Nat} {u w : Tower.Tm n},
    (NumReal X.realReflects X.realNumerals s).mem u → SN X.realRules w →
      SN X.realRules (.app (.app (.const powN) u) w) := by
  have powerStuck : ∀ arity scrutinee, X.realRoles powerN = .computes arity scrutinee →
      1 < arity := by
    intro _ _ role
    rw [X.realRoles_declared (c := powerN) (by decide),
      (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_power] at role
    cases role
  intro s
  induction s with
  | zero =>
      intro n u w hu sw
      refine KCand.computingSpine_mem X.realShape (KCand.sn' X.realReflects) X.realRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_pow (X.realStep_declared (by decide) step) with ⟨-, rfl⟩ | ⟨m, rfl, -⟩
      · exact sw.reducts hw'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hu hu'
        cases same
  | suc s ih =>
      intro n u w hu sw
      refine KCand.computingSpine_mem X.realShape (KCand.sn' X.realReflects) X.realRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', hw'⟩ := ArgsStep.star_two steps
      rcases objectStep_pow (X.realStep_declared (by decide) step) with ⟨rfl, -⟩ | ⟨m, rfl, rfl⟩
      · cases NumReal.shape_of_zero X.realReflects X.realNumerals hu hu'
      · obtain ⟨_, same, hm⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hu hu'
        cases same
        exact SN.constSpine X.realShape (args := [_]) powerStuck
          (by simpa using ih hm (sw.reducts hw'))
  | star =>
      intro n u w hu sw
      refine KCand.computingSpine_mem X.realShape (KCand.sn' X.realReflects) X.realRoles_pow
        (args := [u, w]) rfl (two_sn (KCand.sn _ hu) sw) fun args' steps r step => ?_
      obtain ⟨u', w', rfl, hu', -⟩ := ArgsStep.star_two steps
      rcases objectStep_pow (X.realStep_declared (by decide) step) with ⟨rfl, -⟩ | ⟨m, rfl, -⟩
      · cases NumReal.shape_of_zero X.realReflects X.realNumerals hu hu'
      · obtain ⟨_, same, _⟩ := NumReal.shape_of_suc X.realReflects X.realNumerals hu hu'
        cases same

variable (v : Nat → Nat)

/-! ## Packs at every world -/

/-- The pack of the numbers at every world. -/
abbrev numD : ∀ {m : Nat}, World (X.model v).reading m → ValueSide.Pack (X.model v).value m :=
  fun {m} _ => ValueSide.numIndPack (X.model v).value m

/-- The pack of the sets at every world. -/
abbrev setD : ∀ {m : Nat}, World (X.model v).reading m → ValueSide.Pack (X.model v).value m :=
  fun {m} _ => ValueSide.Pack.total (X.model v).value m

/-- The pack of a function type between packs given at every world. -/
abbrev arrowD (D C : ∀ {m : Nat}, World (X.model v).reading m → ValueSide.Pack (X.model v).value m) :
    ∀ {m : Nat}, World (X.model v).reading m → ValueSide.Pack (X.model v).value m :=
  fun ξ => (ValueSide.PiPack.arrow ξ D C).piPack

/-! ## The sets -/

/-- The sets are rigid on the value side. -/
theorem roles_set_rigid : (X.model v).value.roles setN = .rigid :=
  X.extends_.setRigid

/-- The sets, a rigid type, at every level and world. -/
theorem interp_set (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ setT (X.setD v ξ) :=
  ValueSide.SInterp.rigid (args := []) .refl (X.roles_set_rigid v)
    (by change setN ≠ propN; decide) (by change setN ≠ holdsN; decide)

/-- The sets are of one shape with themselves: a leaf. -/
theorem shape_set (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.Shape (X.model v).value (ValueSide.InterpAt (X.model v).value l) .pair ξ setT setT := by
  have leaf := ValueSide.Shape.of_methodForm (X.valueLaws v) (X.interp_set v l ξ) .refl
    (.inr (.inr (.inr ⟨setN, [], rfl, X.roles_set_rigid v, by change setN ≠ propN; decide,
      by change setN ≠ holdsN; decide⟩)))
  exact .total leaf leaf

/-- **The sets are a type of the lowest universe**: at every world they are a
leaf interpreted at the lowest level, and the constant is strongly
normalizing. -/
theorem valid_set : ModelSN.ValidTmS (X.model v) .nil (.const setN) U0 := by
  refine ⟨ModelSN.ValidTyS.sort (LevelTower.IsUniverse.sort _), fun {_ _ ξ σ σ' ς} _ {P} den => ?_⟩
  rw [ModelSN.DenS.sort_inv (X.laws v) (LevelTower.IsUniverse.sort _) den]
  refine ⟨fun {_ ξ' ρ} _ => ?_, X.set_sn⟩
  exact ⟨_, X.interp_set v _ ξ', X.interp_set v _ ξ', X.shape_set v _ ξ'⟩

/-! ## Interpretations of the declared types -/

/-- The numbers at every level and world. -/
theorem interp_num (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ numT (X.numD v ξ) :=
  ValueSide.InterpAt.num (X.valueLaws v) l .refl

/-- The function type between the numbers. -/
theorem interp_numArrow (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ (.pi numT numT) (X.arrowD v (X.numD v) (X.numD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => X.interp_num v l _)
    (fun {_ _ _} _ {_} _ => X.interp_num v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The function type between the sets. -/
theorem interp_setArrow (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ (.pi setT setT) (X.arrowD v (X.setD v) (X.setD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => X.interp_set v l _)
    (fun {_ _ _} _ {_} _ => X.interp_set v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of `Power`. -/
theorem interp_powerType (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ (liftClosed powerType)
      (X.arrowD v (X.setD v) (X.setD v) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => X.interp_set v l _)
    (fun {_ _ _} _ {_} _ => X.interp_set v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of addition. -/
theorem interp_addType (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ (liftClosed addType)
      (X.arrowD v (X.numD v) (X.arrowD v (X.numD v) (X.numD v)) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => X.interp_num v l _)
    (fun {_ _ _} _ {_} _ => X.interp_numArrow v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The declared type of the iterated power set. -/
theorem interp_powType (l : Nat) {n : Nat} (ξ : World (X.model v).reading n) :
    ValueSide.InterpAt (X.model v).value l ξ (liftClosed powType)
      (X.arrowD v (X.numD v) (X.arrowD v (X.setD v) (X.setD v)) ξ) :=
  ValueSide.SInterp.pi .refl _ (fun {_ _ _} _ => X.interp_num v l _)
    (fun {_ _ _} _ {_} _ => X.interp_setArrow v l _) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-! ## `zero` and `suc` -/

/-- The numbers are a simple inductive type in the model of every extension: `zero` without
fields and `suc` with one recursive field, and the recursor computes by their rules on both
sides. -/
theorem num_inductiveIn : ModelSN.InductiveIn (X.model v) numN numRecName ctors where
  role := X.extends_.num
  recRole := X.extends_.numRec
  iota := fun h => X.step v (tmodelListedAt X.roles v 0 (by decide)) h
  realRole := X.realRoles_num
  realDeclared := X.realDeclared
  realRecRole := X.realRoles_numRec
  realIota := fun step =>
    objectStep_entry (listed 0 (by decide)) (by decide) (X.realStep_declared (by decide) step)

/-- The stage of the numbers is sound for the model of every extension. -/
theorem numStage_soundS : ModelSN.TypedSoundS (stage (allowedIn [numN])) (X.model v) :=
  X.stage_soundS_of v (names := [numN]) (by decide) fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    obtain rfl := Option.some.inj declared
    exact X.valid_num v

/-- **`zero` has shape zero and realizes it**: the clause of a constructor of a simple
inductive type (`ModelSN.ValidTmS.inductiveCtor`), without fields. -/
theorem valid_zero : ModelSN.ValidTmS (X.model v) .nil (.const zeroN) numT :=
  ModelSN.ValidTmS.inductiveCtor (X.laws v) X.extends_.num X.realRoles_num
    X.realDeclared (List.mem_cons_self ..)
    ((X.valid_num v).validTy (LevelTower.IsUniverse.sort _)) trivial

/-- **`suc` sends a number of a shape to the successor shape**, and realizers of a shape to
realizers of the successor shape: the clause of a constructor of a simple inductive type, with
one recursive field. -/
theorem valid_suc : ModelSN.ValidTmS (X.model v) .nil (.const sucN) (.pi numT numT) := by
  obtain ⟨validT, partsT, _⟩ := ModelSN.Derivable.validS (X.numStage_soundS v)
    (piT (allowed := allowedIn [numN]) (numT_typed (List.mem_cons_self ..))
      (numT_typed (List.mem_cons_self ..)) : Typed _ .nil (.pi numT numT) U0) trivial
  exact ModelSN.ValidTmS.inductiveCtor (X.laws v) X.extends_.num X.realRoles_num
    X.realDeclared (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    (validT.validTy (LevelTower.IsUniverse.sort _)) partsT

/-- **`Power` returns sets.** -/
theorem valid_power : ModelSN.ValidTmS (X.model v) .nil (.const powerN) powerType := by
  have rigid : X.realRoles powerN = .rigid :=
    (X.realRoles_declared (c := powerN) (by decide)).trans
      ((objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_power)
  have stuck : ∀ arity scrutinee, X.realRoles powerN = .computes arity scrutinee →
      1 < arity := by
    intro _ _ role
    rw [rigid] at role
    cases role
  refine ModelSN.ValidTmS.closed (X.laws v)
    (SN.pi (RootShape.spineHeaded X.realShape) X.set_sn X.set_sn)
    (D := X.arrowD v (X.setD v) (X.setD v))
    (fun ξ => ⟨0, X.interp_powerType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ _ _ _ _ _ _
    trivial
  · show (ValueSide.PiPack.real (V := (X.model v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨X.const_sn fun _ _ role => ?_, fun {_ _ _} _ {_} _ {_} _ u hu => ?_⟩
    · rw [rigid] at role
      cases role
    · have sn : SN X.realRules u := hu
      exact SN.constSpine X.realShape (args := [u]) stuck (by simpa using sn)

/-! ## Addition and the iterated power set -/

/-- **A sum has the sum of its arguments' shapes** on the value side. -/
theorem hasShape_add {n : Nat} {x y : Tower.Tm n} {s t : NumShape}
    (left : X.VShape v x s) (right : X.VShape v y t) :
    X.VShape v (.app (.app (.const addN) x) y) (shapeAdd s t) := by
  induction right with
  | zero red =>
      exact HasShape.expand
        (Relation.ReflTransGen.tail (X.add_scrutinee v x red) (X.add_zero_step v x)) left
  | suc red _ ih =>
      exact .suc (Relation.ReflTransGen.tail (X.add_scrutinee v x red) (X.add_suc_step v x _)) ih
  | star red daimonic =>
      exact .star (X.add_scrutinee v x red)
        (Daimonic.stuck (before := [x]) (after := []) X.extends_.add rfl daimonic)

/-- A partial application of a computing constant of arity two to one strongly
normalizing argument is strongly normalizing. -/
theorem computes2_partial_sn {c : DeclName} {scrutinee : InspectTree}
    (role : X.realRoles c = .computes 2 scrutinee) {n : Nat} {u : Tower.Tm n}
    (su : SN X.realRules u) : SN X.realRules (.app (.const c) u) :=
  SN.constSpine X.realShape (args := [u])
    (fun _ _ role' => by rw [role] at role'; cases role'; exact Nat.lt_succ_self 1)
    (by simpa using su)

/-- A computing constant of arity two is strongly normalizing. -/
theorem computes2_const_sn {c : DeclName} {scrutinee : InspectTree}
    (role : X.realRoles c = .computes 2 scrutinee) {n : Nat} :
    SN X.realRules (.const c : Tower.Tm n) :=
  SN.constSpine X.realShape (args := [])
    (fun _ _ role' => by rw [role] at role'; cases role'; exact Nat.zero_lt_two) (by simp)

/-- **Addition sends numbers of two shapes to the number of the sum of the
shapes**, and realizers to the realizer of the sum. -/
theorem valid_add : ModelSN.ValidTmS (X.model v) .nil (.const addN) addType := by
  refine ModelSN.ValidTmS.closed (X.laws v)
    (SN.pi (RootShape.spineHeaded X.realShape) X.numT_sn
      (SN.pi (RootShape.spineHeaded X.realShape) X.numT_sn X.numT_sn))
    (D := X.arrowD v (X.numD v) (X.arrowD v (X.numD v) (X.numD v)))
    (fun ξ => ⟨0, X.interp_addType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ ρ _ a b _ related _ _ ρ' _ c d _ related'
    obtain ⟨s, ha, hb⟩ := ValueSide.numIndPack_rel.mp related
    obtain ⟨t, hc, hd⟩ := ValueSide.numIndPack_rel.mp related'
    exact ValueSide.numIndPack_rel.mpr ⟨shapeAdd s t,
      X.hasShape_add v (X.shape_rename v ρ' ha) hc, X.hasShape_add v (X.shape_rename v ρ' hb) hd⟩
  · show (ValueSide.PiPack.real (V := (X.model v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨X.computes2_const_sn X.realRoles_add, fun {_ ξ' ρ} _ {a} ha {_} ρr u hu => ?_⟩
    show (ValueSide.PiPack.real (V := (X.model v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨X.computes2_partial_sn X.realRoles_add (KCand.sn _ hu),
      fun {_ ξ'' ρ'} _ {c} hc {_} ρr' u' hu' => ?_⟩
    obtain ⟨s, sa, -⟩ := ValueSide.numIndPack_rel.mp ha
    obtain ⟨t, sc, -⟩ := ValueSide.numIndPack_rel.mp hc
    have sa' := X.shape_rename v ρ' sa
    change ((ValueSide.numIndPack (X.model v).value _).real a).mem u at hu
    change ((ValueSide.numIndPack (X.model v).value _).real c).mem u' at hu'
    change ((ValueSide.numIndPack (X.model v).value _).real
      (.app (.app (.const addN) (Presentation.rename ρ' a)) c)).mem
      (.app (.app (.const addN) (Presentation.rename ρr' u)) u')
    rw [X.numIndPack_real v sa] at hu
    rw [X.numIndPack_real v sc] at hu'
    rw [X.numIndPack_real v (X.hasShape_add v sa' sc)]
    exact X.numReal_add t (KCand.rename _ ρr' hu) hu'

/-- **The iterated power set returns sets**; its applications to realizers are
strongly normalizing. -/
theorem valid_pow : ModelSN.ValidTmS (X.model v) .nil (.const powN) powType := by
  refine ModelSN.ValidTmS.closed (X.laws v)
    (SN.pi (RootShape.spineHeaded X.realShape) X.numT_sn
      (SN.pi (RootShape.spineHeaded X.realShape) X.set_sn X.set_sn))
    (D := X.arrowD v (X.numD v) (X.arrowD v (X.setD v) (X.setD v)))
    (fun ξ => ⟨0, X.interp_powType v 0 ξ⟩) (fun _ => ?_) (fun {_} _ {_} => ?_)
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    trivial
  · show (ValueSide.PiPack.real (V := (X.model v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨X.computes2_const_sn X.realRoles_pow, fun {_ ξ' ρ} _ {a} ha {_} ρr u hu => ?_⟩
    show (ValueSide.PiPack.real (V := (X.model v).value) _ _).mem _
    rw [ModelSN.PiPack.mem_real]
    refine ⟨X.computes2_partial_sn X.realRoles_pow (KCand.sn _ hu),
      fun {_ _ _} _ {_} _ {_} ρr' u' hu' => ?_⟩
    obtain ⟨s, sa, -⟩ := ValueSide.numIndPack_rel.mp ha
    change ((ValueSide.numIndPack (X.model v).value _).real a).mem u at hu
    rw [X.numIndPack_real v sa] at hu
    exact X.pow_sn s (KCand.rename _ ρr' hu) hu'

end TExtension

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
