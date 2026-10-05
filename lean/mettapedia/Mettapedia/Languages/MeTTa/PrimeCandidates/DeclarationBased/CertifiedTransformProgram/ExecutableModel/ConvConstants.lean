import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvRules
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Identity

/-!
# The conversion model of the executable package over a realizer side

The constants of the executable package are valid in the conversion model over
every realizer side whose package contains the executable package and whose
roles keep the executable package's roles of the numbers and of the constants
with computation, and keep the sets and the power set rigid (`OverRules`), and with
the value side of every extension of the transport value model by declared names. Three
such realizer sides matter: the executable package itself at a generic equality
(`sideAt`), a package extending it by codes, and that package with a declared datatype.

The executable package `rules` is a realizer side at every lawful generic
equality that respects typed weak-head reduction, with the facts of the
one-sided model (`sideAt`); the realizer side with the conversion algorithm is
the one at the algorithmic equality (`rulesAlgorithmicSide_eq`). With the value
side of an extension every realizer side gives a lawful conversion model (`nmodel`,
`nmodel_laws`).

**Stages.** A stage of the package whose constants are valid is sound for the
model with its root steps read with their typing (`stage_typedSoundN`): a
computation other than identity elimination is a step of the value side's
computation and of the realizer side's, so it preserves meaning, and identity
elimination holds at its typed instances.

**The first constants.** The numbers and the sets are valid terms of the
lowest universe, a type constant and a rigid type realized by the types;
`zero` and `suc` are valid, their values of the shapes zero and successor and
their realizers the constructor terms of those shapes; `Power` is valid, its
values sets and its realizers related by the generic equality.
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
open Package (U0 numT jName)

namespace CodeModel
namespace ConvRules

/-! ## Realizer sides over the executable package -/

/-- **A realizer side over the executable package**: its package contains the
executable package, and its roles keep the executable package's roles of the
numbers and of the constants with computation, and keep the sets and the power
set rigid. -/
structure OverRules (T : RealizerSide Tower.Head ℕ) : Prop where
  sub : RulesSub rules T.R
  keep : Codes.RolesKeep roles T.roles
  set : T.roles setN = .rigid
  power : T.roles powerN = .rigid

namespace OverRules

variable {T : RealizerSide Tower.Head ℕ} (ext : OverRules T)
include ext

/-- The universes of the executable package are universes of the realizer
side. -/
theorem isUniverse_sort (level : LevelExpr Nat) : T.R.isUniverse (.sort level) :=
  ext.sub.isUniverse (LevelTower.IsUniverse.sort level)

/-- The lowest universe is a universe of the realizer side. -/
theorem isUniverse_zero : T.R.isUniverse (.sort Tower.zero) :=
  ext.isUniverse_sort _

/-- A typing of the executable package is a typing of the realizer side. -/
theorem typed {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n} (typing : Typed rules Γ t A) :
    Typed T.R Γ t A :=
  Derivable.mono ext.sub typing

/-- An equality of the executable package is an equality of the realizer side. -/
theorem equal {n : Nat} {Γ : Tower.Ctx n} {t u A : Tower.Tm n} (equal : Equal rules Γ t u A) :
    Equal T.R Γ t u A :=
  Derivable.mono ext.sub equal

/-- A root step of the executable package is a root step of the realizer side. -/
theorem step {n : Nat} {l r : Tower.Tm n} (step : rules.computation.step l r) :
    T.R.computation.step l r :=
  ext.sub.computation step

theorem roles_num : T.roles numN = .inductive ctors := ext.keep ExecutableModel.roles_num nofun
theorem roles_zero : T.roles zeroN = .constructor 0 := ext.keep ExecutableModel.roles_zero nofun
theorem roles_suc : T.roles sucN = .constructor 1 := ext.keep ExecutableModel.roles_suc nofun
theorem roles_numRec : T.roles Package.numRecName =
    .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  ext.keep ExecutableModel.roles_numRec nofun
theorem roles_add : T.roles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  ext.keep ExecutableModel.roles_add nofun
theorem roles_pow : T.roles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  ext.keep ExecutableModel.roles_pow nofun
theorem roles_iter : T.roles Package.iterName =
    .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  ext.keep ExecutableModel.roles_iter nofun

section Typings

variable {n : Nat} {Γ : Tower.Ctx n}

theorem numT_typed : Typed T.R Γ numT U0 :=
  ext.typed (Derivable.mono (stage_sub_rules _)
    (ExecutableModel.numT_typed (names := [numN]) (List.mem_cons_self ..)))

theorem setT_typed : Typed T.R Γ setT U0 :=
  ext.typed (Derivable.mono (stage_sub_rules _)
    (ExecutableModel.setT_typed (names := [setN]) (List.mem_cons_self ..)))

theorem zero_typed : Typed T.R Γ (.const zeroN) numT :=
  ext.typed (Derivable.mono (stage_sub_rules _)
    (ExecutableModel.zero_typed (names := [numN, zeroN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem suc_typed : Typed T.R Γ (.const sucN) (.pi numT numT) :=
  ext.typed (Derivable.mono (stage_sub_rules _)
    (ExecutableModel.suc_typed (names := [numN, sucN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem power_typed : Typed T.R Γ (.const powerN) (.pi setT setT) :=
  ext.typed (Derivable.mono (stage_sub_rules _)
    (ExecutableModel.power_typed (names := [setN, powerN]) (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem numType : IsType T.R Γ numT := ⟨_, ext.isUniverse_zero, ext.numT_typed⟩

end Typings

/-- Identity elimination is declared on the realizer side as an eliminator at the
lowest universes. -/
theorem declaresJ :
    DeclaresEliminator T.toSetting jName (.sort Tower.zero) (.sort Tower.zero) where
  role := ext.keep ExecutableModel.roles_j nofun
  declared := ext.sub.constantType (ExecutableModel.declaresJ (fun _ => 0) (E := T.E)).declared
  rule := ext.step (ExecutableModel.declaresJ (fun _ => 0) (E := T.E)).rule
  hu := ext.isUniverse_zero
  hv := ext.isUniverse_zero
  typed := by
    obtain ⟨w, hw, typed⟩ := (ExecutableModel.declaresJ (fun _ => 0) (E := T.E)).typed
    refine ⟨w, ext.sub.isUniverse hw, Derivable.mono ?_ typed⟩
    exact ⟨ext.sub.headTyping, ext.sub.isUniverse, ext.sub.join, ext.sub.cumulative,
      ext.sub.headEq, fun declared => (nomatch declared), fun step => (nomatch step)⟩

end OverRules

/-! ## The realizer side at a generic equality -/

/-- **The executable package as a realizer side at a generic equality** with the
laws of a generic equality that respects typed weak-head reduction: the facts
about weak-head forms of its types, which do not depend on the equality, come
from the one-sided model. -/
def sideAt (E : GenericEquality Tower.Head) (lawsE : E.Laws rules roles)
    (reduceE : RespectsReduction rules roles E) : RealizerSide Tower.Head ℕ where
  toSetting := settingAt (fun _ => 0) E
  laws := lawsE
  reduce := reduceE
  facts := facts

/-- The executable package at a generic equality is a realizer side over the
executable package. -/
theorem sideAt_over (E : GenericEquality Tower.Head) (lawsE : E.Laws rules roles)
    (reduceE : RespectsReduction rules roles E) : OverRules (sideAt E lawsE reduceE) where
  sub := RulesSub.refl rules
  keep := fun declared _ => declared
  set := roles_set
  power := roles_power

/-- The realizer side with the conversion algorithm is the realizer side at the
algorithmic equality. -/
theorem rulesAlgorithmicSide_eq :
    rulesAlgorithmicSide = sideAt _ rulesAlgorithmicSide.laws rulesAlgorithmicSide.reduce :=
  rfl

/-- Identity elimination is declared at the lowest universes. -/
theorem allTypes_jName : allTypes jName = some Package.jType := by
  decide

section Model

variable (X : TExtension) (v : Nat → Nat) {T : RealizerSide Tower.Head ℕ}

/-- The transport table holds on the value side of the model. -/
theorem nmodel_coeRules : ValueSide.CoeRules (nmodel X v T).value coeN :=
  (tmodelOf_coeTable v X.extends_ fun _ mem => List.mem_append_right _ mem).coeRules
    (V := (nmodel X v T).value) (nmodel_laws X v T).value

/-- Identity elimination computes on the value side to the transport of its
method along its motive. -/
theorem nmodel_jStep {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm m) :
    (nmodel X v T).rules.computation.step
      (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅])
      (ValueSide.coeApp coeN (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃) :=
  X.step v (tmodelListedAt X.roles v 3 (by decide))
    (Realizability.transportJ_step a₀ a₁ a₂ a₃ a₄ a₅)

/-- A constant that is a constructor, a type constant or a rigid constant is
related to itself by the generic equality at its type. -/
theorem convTm_liftable {T : RealizerSide Tower.Head ℕ} {n : Nat} {Γ : Tower.Ctx n} {c : DeclName}
    {A : Tower.Tm n}
    (liftable : Liftable T.roles (.const c : Tower.Tm n)) (typed : Typed T.R Γ (.const c) A) :
    T.E.convTm Γ (.const c) (.const c) A :=
  T.laws.convTm_of_convNe liftable liftable (T.laws.convNe_const c typed)

section Stages

variable (ext : OverRules T)
include ext

/-! ## Stages -/

/-- **Every root step of a stage is validated by the model**: a computation other
than identity elimination is a step of the value side's computation and of the
realizer side's, so it preserves meaning; identity elimination holds at its
typed instances, in every package that declares it, where the stage lists it,
at the lowest universes. -/
theorem stage_root {allowed : DeclName → Bool} {R : Rules Tower.Head}
    (declaredJ : allowed jName = true →
      R.constantType jName = some (elimType (.sort Tower.zero) (.sort Tower.zero)))
    {n : Nat} {l r : Tower.Tm n} (step : (stage allowed).computation.step l r) :
    RootSemanticN (nmodel X v T) l r ∨ TypedRootN R (nmodel X v T) l r := by
  change (RootComputation.unionAll (computations.filter fun entry => allowed entry.1)).step l r
    at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  obtain ⟨listedIn, allowedIn⟩ := List.mem_filter.mp mem
  have realStep : T.R.computation.step l r := ext.step (rules_step listedIn h)
  have semantic : (nmodel X v T).rules.computation.step l r → RootSemanticN (nmodel X v T) l r :=
    fun s => ModelRootN.semantic (nmodel_laws X v T) (X.programDecodes v) ⟨.inl s, realStep⟩
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 0 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 1 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 2 (by decide)) h))
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := h
    exact .inr (TypedRootN.transport (nmodel_laws X v T) (LevelTower.IsUniverse.sort _)
      (declaredJ allowedIn) (nmodel_jStep X v) (nmodel_coeRules X v)
      (fun _ _ _ _ _ _ => ext.declaresJ.rule))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 4 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 5 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 6 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 7 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 8 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 9 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 10 (by decide)) h))
  · exact .inl (semantic (X.step v (tmodelListedAt X.roles v 11 (by decide)) h))

/-- **A stage of the package whose constants are valid is sound for the model,
with its root steps read with their typing.** -/
theorem stage_typedSoundN {allowed : DeclName → Bool}
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ValidTmN (nmodel X v T) .nil (.const name) type) :
    TypedSoundN (stage allowed) (nmodel X v T) where
  laws := nmodel_laws X v T
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := fun typing => ext.sub.headTyping ((stage_sub_rules allowed).headTyping typing)
  isUniverse' := fun hu => ext.sub.isUniverse ((stage_sub_rules allowed).isUniverse hu)
  join' := fun join => ext.sub.join ((stage_sub_rules allowed).join join)
  cumulative' := fun c => ext.sub.cumulative ((stage_sub_rules allowed).cumulative c)
  headEq' := fun same => ext.sub.headEq ((stage_sub_rules allowed).headEq same)
  root := stage_root X v ext fun allowedJ => by
    change (if allowed jName then allTypes jName else none) = _
    rw [if_pos allowedJ, allTypes_jName]
    rfl
  constants := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    split_ifs at declared with h
    exact constants h declared

/-- A stage of the listed names whose constants are valid is sound for the
model. -/
theorem stage_typedSoundN_of {names : List DeclName}
    (constants : ∀ name ∈ names, ∀ {type : Tower.Tm 0}, allTypes name = some type →
      ValidTmN (nmodel X v T) .nil (.const name) type) :
    TypedSoundN (stage (allowedIn names)) (nmodel X v T) :=
  stage_typedSoundN X v ext fun {name _} allowed declared =>
    constants name (by simpa [allowedIn] using allowed) declared

end Stages

/-! ## Packs of the value side -/

/-- The sets are rigid on the value side. -/
theorem value_roles_set : (X.model v).roles setN = .rigid :=
  X.extends_.setRigid

/-- The numbers at every level and world. -/
theorem num_interp (l : Nat) {n : Nat} (ξ : World (nmodel X v T).reading n) :
    NInterp (nmodel X v T) l ξ numT (ValueSide.numIndPack (nmodel X v T).value n) :=
  ValueSide.InterpAt.num (nmodel_laws X v T).value l .refl

/-- The sets, a rigid type, at every level and world. -/
theorem set_interp (l : Nat) {n : Nat} (ξ : World (nmodel X v T).reading n) :
    NInterp (nmodel X v T) l ξ setT (ValueSide.Pack.total (nmodel X v T).value n) :=
  ValueSide.SInterp.rigid (args := []) .refl (value_roles_set X v)
    (by change setN ≠ propN; decide) (by change setN ≠ holdsN; decide)

/-- The sets are of one shape with themselves: a leaf. -/
theorem set_shape (l : Nat) {n : Nat} (ξ : World (nmodel X v T).reading n) :
    ValueSide.Shape (nmodel X v T).value (ValueSide.InterpAt (nmodel X v T).value l) .pair ξ setT
      setT := by
  have leaf := ValueSide.Shape.of_methodForm (nmodel_laws X v T).value (set_interp X v l ξ) .refl
    (.inr (.inr (.inr ⟨setN, [], rfl, value_roles_set X v, by change setN ≠ propN; decide,
      by change setN ≠ holdsN; decide⟩)))
  exact .total leaf leaf

/-- The numbers denote their inductive pack. -/
theorem num_den {n : Nat} {ξ : World (nmodel X v T).reading n} {P : NPack (nmodel X v T) n}
    (den : DenN (nmodel X v T) ξ numT P) : P = ValueSide.numIndPack (nmodel X v T).value n :=
  ValueSide.DenS.num_inv (nmodel_laws X v T).value den

/-- The sets denote the total pack. -/
theorem set_den {n : Nat} {ξ : World (nmodel X v T).reading n} {P : NPack (nmodel X v T) n}
    (den : DenN (nmodel X v T) ξ setT P) : P = ValueSide.Pack.total (nmodel X v T).value n :=
  ValueSide.DenS.deterministic (nmodel_laws X v T).value den ⟨0, set_interp X v 0 ξ⟩

section Constants

variable (ext : OverRules T)
include ext

/-- **The realizers of a number of a shape are the constructor terms of the
shape**, at every denotation of the numbers. -/
theorem num_real {n : Nat} {ξ : World (nmodel X v T).reading n} {P : NPack (nmodel X v T) n}
    (den : DenN (nmodel X v T) ξ numT P) {a : Tower.Tm n} {s : NumShape} (shape : X.VShape v a s)
    {m : Nat} (Δ : Tower.Ctx m) (A t t' : Tower.Tm m) :
    (P.real a).rel Δ A t t' ↔ NumShapeRel T numN zeroN sucN s Δ A t t' := by
  obtain ⟨l, interp⟩ := den
  exact nmodel_num_real X v ext.roles_num interp .refl shape Δ A t t'

/-! ## The numbers and the sets -/

/-- **The numbers are a valid term of the lowest universe**: at every world they
are interpreted by their inductive pack, of one shape with themselves, and they
are realized by the types, a type constant related to itself. -/
theorem valid_num : ValidTmN (nmodel X v T) .nil (.const numN) U0 := by
  have laws := (nmodel_laws X v T).value
  refine ⟨ValidTyN.sort (LevelTower.IsUniverse.sort _) ext.isUniverse_zero,
    fun {m r ξ σ σ' Δ ς ς'} _ {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws (LevelTower.IsUniverse.sort _) den]
  refine ⟨fun {_ ξ' _} _ => ⟨_, ValueSide.InterpAt.num laws _ .refl,
    ValueSide.InterpAt.num laws _ .refl, .const (.inr ⟨_, laws.num_role⟩) .refl .refl⟩, ?_⟩
  have typed : Typed T.R Δ numT U0 := ext.numT_typed
  have form : IsTypeForm T.roles (numT : Tower.Tm r) :=
    .inr (.inr (.inr (.inr (.inr ⟨numN, _, ext.roles_num, rfl⟩))))
  exact ⟨⟨typed, typed, convTm_liftable (.inr (.inr ⟨numN, _, ext.roles_num, rfl⟩)) typed⟩,
    ⟨numT, .refl typed, form⟩, ⟨numT, .refl typed, form⟩⟩

/-- **The sets are a valid term of the lowest universe**: at every world they are
a leaf, and they are realized by the types, a rigid constant related to
itself. -/
theorem valid_set : ValidTmN (nmodel X v T) .nil (.const setN) U0 := by
  have laws := (nmodel_laws X v T).value
  refine ⟨ValidTyN.sort (LevelTower.IsUniverse.sort _) ext.isUniverse_zero,
    fun {m r ξ σ σ' Δ ς ς'} _ {P} den => ?_⟩
  rw [ValueSide.DenS.sort_inv laws (LevelTower.IsUniverse.sort _) den]
  refine ⟨fun {_ ξ' _} _ => ⟨_, set_interp X v _ ξ', set_interp X v _ ξ', set_shape X v _ ξ'⟩, ?_⟩
  have typed : Typed T.R Δ setT U0 := ext.setT_typed
  have neutral : Neutral T.roles (setT : Tower.Tm r) := .rigid (args := []) ext.set
  exact ⟨⟨typed, typed, convTm_liftable (.inl neutral) typed⟩,
    ⟨setT, .refl typed, .inr (.inr (.inr (.inr (.inl neutral))))⟩,
    ⟨setT, .refl typed, .inr (.inr (.inr (.inr (.inl neutral))))⟩⟩

/-- The stage of the numbers is sound for the model. -/
theorem numStage_typedSoundN : TypedSoundN numStage (nmodel X v T) :=
  stage_typedSoundN_of X v ext fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    obtain rfl := Option.some.inj declared
    exact valid_num X v ext

/-- The stage of the numbers and the sets is sound for the model. -/
theorem numSetStage_typedSoundN :
    TypedSoundN (stage (allowedIn [numN, setN])) (nmodel X v T) :=
  stage_typedSoundN_of X v ext fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact valid_num X v ext
    · exact valid_set X v ext

/-! ## `zero`, `suc` and `Power` -/

/-- **`zero` is valid**: its value has shape zero, and it realizes shape zero. -/
theorem valid_zero : ValidTmN (nmodel X v T) .nil (.const zeroN) numT := by
  refine ⟨(valid_num X v ext).validTy (LevelTower.IsUniverse.sort _) ext.isUniverse_zero,
    fun {m r ξ σ σ' Δ ς ς'} _ {P} den => ?_⟩
  have shape : X.VShape v (.const zeroN : Tower.Tm m) .zero := HasShape.zero .refl
  have typed : Typed T.R Δ (.const zeroN) numT := ext.zero_typed
  refine ⟨?_, (num_real X v ext den shape Δ numT _ _).mpr
    (.inr ⟨RedTy.refl ext.numType, .refl typed, .refl typed,
      convTm_liftable (.inr (.inl ⟨zeroN, 0, [], ext.roles_zero, rfl⟩)) typed⟩)⟩
  rw [num_den X v den]
  exact ValueSide.numIndPack_rel.mpr ⟨.zero, shape, shape⟩

/-- **`suc` is valid**: it sends a number of a shape to the successor shape, and
realizers of a shape to realizers of the successor shape. -/
theorem valid_suc : ValidTmN (nmodel X v T) .nil (.const sucN) (.pi numT numT) := by
  have laws := nmodel_laws X v T
  have typedType : Typed numStage .nil (.pi numT numT) U0 :=
    piT (numT_typed (List.mem_cons_self ..)) (numT_typed (List.mem_cons_self ..))
  obtain ⟨validT, partsT, _⟩ :=
    Derivable.validTN (numStage_typedSoundN X v ext) typedType trivial
  refine ValidTmN.close laws (.snoc .nil numT) (C := numT) (f := .const sucN)
    (validT.validTy (LevelTower.IsUniverse.sort _) ext.isUniverse_zero) partsT ext.suc_typed
    (fun args short => .inr (.inr ⟨sucN, args, 1, .inl ext.roles_suc, short, rfl⟩))
    ⟨ValidTyN.liftClosed ((valid_num X v ext).validTy (LevelTower.IsUniverse.sort _)
      ext.isUniverse_zero) _, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨-, RA, denA, hx, rx⟩ := e
  change DenN (nmodel X v T) ξ numT RA at denA
  change (RA.real (σ 0)).rel Δ numT (ς 0) (ς' 0) at rx
  change DenN (nmodel X v T) ξ numT P at den
  rw [num_den X v denA] at hx
  obtain ⟨s, hs, hs'⟩ := ValueSide.numIndPack_rel.mp hx
  have shape : X.VShape v (.app (.const sucN) (σ 0)) (.suc s) := .suc .refl hs
  have shape' : X.VShape v (.app (.const sucN) (σ' 0)) (.suc s) := .suc .refl hs'
  obtain ⟨t₀, t₀'⟩ := ECand.typed _ rx
  have typed : Typed T.R Δ (.app (.const sucN) (ς 0)) numT := .appElim ext.suc_typed t₀
  have typed' : Typed T.R Δ (.app (.const sucN) (ς' 0)) numT := .appElim ext.suc_typed t₀'
  have conv : T.E.convTm Δ (.app (.const sucN) (ς 0)) (.app (.const sucN) (ς' 0)) numT :=
    T.laws.convTm_of_convNe (.inr (.inl ⟨sucN, 1, [ς 0], ext.roles_suc, rfl⟩))
      (.inr (.inl ⟨sucN, 1, [ς' 0], ext.roles_suc, rfl⟩))
      (T.laws.convNe_app (T.laws.convNe_const sucN ext.suc_typed) (ECand.escape _ rx))
  refine ⟨?_, (num_real X v ext den shape Δ numT _ _).mpr
    (.inr ⟨RedTy.refl ext.numType, ς 0, ς' 0, .refl typed, .refl typed', conv,
      (num_real X v ext denA hs Δ numT _ _).mp rx⟩)⟩
  rw [num_den X v den]
  exact ValueSide.numIndPack_rel.mpr ⟨.suc s, shape, shape'⟩

/-- **`Power` is valid**: it returns sets, and its realizers are related by the
generic equality. -/
theorem valid_power : ValidTmN (nmodel X v T) .nil (.const powerN) powerType := by
  have laws := nmodel_laws X v T
  have typedType : Typed (stage (allowedIn [numN, setN])) .nil powerType U0 :=
    powerType_typed (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨validT, partsT, _⟩ :=
    Derivable.validTN (numSetStage_typedSoundN X v ext) typedType trivial
  refine ValidTmN.close laws (.snoc .nil setT) (C := setT) (f := .const powerN)
    (validT.validTy (LevelTower.IsUniverse.sort _) ext.isUniverse_zero) partsT ext.power_typed
    (fun args _ => .inr (.inl (.rigid args ext.power)))
    ⟨ValidTyN.liftClosed ((valid_set X v ext).validTy (LevelTower.IsUniverse.sort _)
      ext.isUniverse_zero) _, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨-, RA, denA, -, rx⟩ := e
  change DenN (nmodel X v T) ξ setT RA at denA
  change (RA.real (σ 0)).rel Δ setT (ς 0) (ς' 0) at rx
  change DenN (nmodel X v T) ξ setT P at den
  obtain ⟨t₀, t₀'⟩ := ECand.typed _ rx
  rw [set_den X v den]
  exact ⟨trivial, .appElim ext.power_typed t₀, .appElim ext.power_typed t₀',
    T.laws.convTm_of_convNe (.inl (.rigid [ς 0] ext.power)) (.inl (.rigid [ς' 0] ext.power))
      (T.laws.convNe_app (T.laws.convNe_const powerN ext.power_typed) (ECand.escape _ rx))⟩

end Constants

end Model

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
