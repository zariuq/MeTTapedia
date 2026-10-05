import Mettapedia.GSLT.Logic.QuotientObservers
import Mettapedia.Cybernetics.DistinctionConservation

/-!
# Views of one subject

A *view* of a subject is a map out of it.  Two points are the same in the view
when the map identifies them, so a view is a quotient bubble: the observers
admissible for the bubble are exactly the observers that factor through the
view (`factors_iff_respects`, `factors_iff_admissible`, with the vocabulary of
`Mettapedia.GSLT.Logic.QuotientObservers`).  A *translation* from one view to
another is a recovering map in the sense of `Factors`
(`Mettapedia.GSLT.Core.NonFactorization`): the second view is a function of the
first.  What a translation keeps is a `Factors` statement; what it forgets is a
`NonTrivialFiber`, two points the target view identifies and the source view
separates.  Equivalently, a view determines a feature exactly when it
conserves every distinction the feature draws (`factors_iff_conserves`, in the
vocabulary of `Mettapedia.Cybernetics.DistinctionConservation`), and a view
loses nothing exactly when it conserves every distinction
(`factors_id_iff_conserves`).  Translations compose (`factors_trans`), and a
fibre that separates a feature separates every view that determines the
feature (`NonTrivialFiber.ofDetermined`).

The pluralist stance says: no view is privileged, the views are translated into
one another, each keeps something the others forget, and they agree on a common
basis of evaluation.  Its parts, stated without any new structure:

* a view is **finest** in a family when every view of the family factors
  through it (`Finest`): it is lossless for the family;
* an evaluation is a **common coarsening** of a family when it factors through
  every view (`CommonCoarsening`): the views agree on it;
* the **joint view** takes all views at once (`joint`); its bubble is the meet of
  the members' bubbles (`ker_joint_iff`), and a member is finest exactly when it
  determines the joint view (`finest_iff_factors_joint`).

## Finest is lossless, not privileged

Finest members come as a class.  Two finest members factor through each other
(`Finest.mutual`) and identify the same points (`Finest.sameFibres`,
`Finest.ker_eq`).  Once one member is finest, the finest members are exactly
the members through which it factors (`Finest.finest_iff`), equivalently the
members that identify no more than it does (`Finest.of_sameFibres`).  So a
finest view settles how much can be told apart and singles out no presentation
of it: in an exact computational trinity all three faces are finest
(`TrinityFaces.Exact.finest` in `Mettapedia.GSLT.Logic.ViewPluralism`).  That no
member of a family is finest is a separate and stronger claim.  What privilege
can mean, relative to a purpose, is the subject of
`Mettapedia.GSLT.Logic.PrivilegedView`.

**All two-valued observations.**  A view determines every two-valued
observation of its subject exactly when it is injective
(`factors_twoValued_iff_injective`).  Adjoined to the family of all two-valued
observations, a view is finest exactly when it is injective
(`finest_adjoinTwoValued_iff_injective`).  Negative example: adjoined to the
constant observations alone, the view that identifies everything is finest
(`finest_adjoinTwoValued_constant`), so the family cannot be restricted
(`not_forall_finest_adjoinTwoValued_iff_injective`).

## The diagonal limit

The joint view of all two-valued observations is injective
(`joint_twoValued_injective`); its values are families of observations, not
elements of the subject.  The limit concerns self-description:

* the subject's own elements cannot name every two-valued observation of the
  subject (`not_surjective_naming`, Cantor's diagonal in Lawvere's fixed-point
  form, `Function.exists_fixed_point_of_surjective`);
* a view of the two-valued observations whose values are the subject's own
  elements is not finest among their two-valued observations
  (`not_finest_selfDescribing`): a self-describing finest view does not exist.

These do not limit lossless views (the identity is one), nor finite syntax: a
finite universal instruction set or a self-interpreter is not excluded.
Related but distinct diagonal arguments show that no type surjects onto a
universe containing it (`Function.not_surjective_Type`), that no universe of the
level tower is a member of itself (`LevelTower.universeAt_not_mem_self` in
`Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerOrdinalLevels`),
and that no hyperset contains every hyperset (`HSet.not_exists_universal` in
`Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet`), the last under
anti-foundation.  For streams the limit has a finite-depth form: every view at a
fixed depth loses information while the tower of all of them separates streams
(`PrivilegedView.no_prefixView_finest`, `PrivilegedView.joint_prefixViews_injective`).

The words are the library's own (view, bubble, factors, fibre) and the
order-theoretic ones for partitions (finest, common coarsening, meet).  For
translations between logics the literature's term is the comorphism of
institutions (Goguen and Burstall; Goguen and Roşu), present in
`Mettapedia.Logic.Institution`; what the views here share is factorization, so
no comorphism is built.  The instances (propositions, verification readings,
the computational trinity, values equal to their own negation, table runs) are
in `Mettapedia.GSLT.Logic.ViewPluralism`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ViewPluralism

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.QuotientObservers

universe u v w x

/-! ## Views, translations, finest views -/

section General

/-- **Translations compose.** -/
theorem factors_trans {A : Sort u} {B : Sort v} {C : Sort w} {D : Sort x}
    {first : A → B} {second : A → C} {third : A → D}
    (firstSecond : Factors first second) (secondThird : Factors second third) :
    Factors first third := by
  obtain ⟨recover, recovers⟩ := firstSecond
  exact secondThird.of_coarsening fun a => (recovers a).symm

/-- **A fibre that separates a feature separates every view that determines
it.** -/
def NonTrivialFiber.ofDetermined {A : Sort u} {S : Sort v} {V : Sort w} {V' : Sort x}
    {shadow : A → S} {feature : A → V} {view : A → V'} (determines : Factors view feature)
    (fiber : NonTrivialFiber shadow feature) : NonTrivialFiber shadow view where
  left := fiber.left
  right := fiber.right
  sameShadow := fiber.sameShadow
  differentValue := fun same => fiber.differentValue (determines.constantOnFibers _ _ same)

variable {A : Sort u} {ι : Sort v} {V : ι → Sort w}

/-- A view `k` of a family is **finest** when every view of the family factors
through it. -/
def Finest (view : (i : ι) → A → V i) (k : ι) : Prop :=
  ∀ i, Factors (view k) (view i)

/-- An evaluation is a **common coarsening** of a family when every view of the
family determines it. -/
def CommonCoarsening {E : Sort x} (view : (i : ι) → A → V i) (evaluation : A → E) : Prop :=
  ∀ i, Factors (view i) evaluation

/-- The joint view: all views of the family at once. -/
def joint (view : (i : ι) → A → V i) (a : A) : (i : ι) → V i :=
  fun i => view i a

theorem factors_joint (view : (i : ι) → A → V i) (i : ι) : Factors (joint view) (view i) :=
  ⟨fun values => values i, fun _ => rfl⟩

/-- **A member is finest exactly when it determines the joint view.** -/
theorem finest_iff_factors_joint (view : (i : ι) → A → V i) (k : ι) :
    Finest view k ↔ Factors (view k) (joint view) := by
  constructor
  · intro finest
    exact ⟨fun shadow i => Classical.choose (finest i) shadow,
      fun a => funext fun i => Classical.choose_spec (finest i) a⟩
  · intro determines i
    exact factors_trans determines (factors_joint view i)

/-- **A non-trivial fibre refutes being finest.** -/
theorem not_finest_of_fiber (view : (i : ι) → A → V i) {k : ι} (i : ι)
    (fiber : NonTrivialFiber (view k) (view i)) : ¬ Finest view k :=
  fun finest => fiber.not_factors (finest i)

/-- A common coarsening of a family with at least one member is determined by
the joint view. -/
theorem CommonCoarsening.joint_determines {E : Sort x} {view : (i : ι) → A → V i}
    {evaluation : A → E} (common : CommonCoarsening view evaluation) (i : ι) :
    Factors (joint view) evaluation :=
  factors_trans (_root_.Mettapedia.GSLT.ViewPluralism.factors_joint view i) (common i)

end General

section Bubbles

variable {A : Type u} {ι : Type v} {V : ι → Type w}

/-- **The bubble of the joint view is the meet of the members' bubbles.** -/
theorem ker_joint_iff (view : (i : ι) → A → V i) (a b : A) :
    Setoid.ker (joint view) a b ↔ ∀ i, Setoid.ker (view i) a b := by
  simp only [Setoid.ker_def]
  exact funext_iff

theorem ker_joint (view : (i : ι) → A → V i) :
    Setoid.ker (joint view) = ⨅ i, Setoid.ker (view i) := by
  ext a b
  rw [ker_joint_iff, show (⨅ i, Setoid.ker (view i)) = sInf (Set.range fun i => Setoid.ker (view i))
    from rfl, Setoid.sInf_iff]
  simp

end Bubbles

section Observers

/-- A feature constant on the fibres of a view factors through it, when the
feature's values are inhabited. -/
theorem factors_of_constantOnFibers {A : Sort u} {S : Sort v} {V : Sort w} [Nonempty V]
    {view : A → S} {feature : A → V} (constant : ConstantOnFibers view feature) :
    Factors view feature := by
  classical
  refine ⟨fun shadow => if seen : ∃ a, view a = shadow then feature seen.choose
    else Classical.arbitrary V, fun a => ?_⟩
  have seen : ∃ a', view a' = view a := ⟨a, rfl⟩
  dsimp only
  rw [dif_pos seen]
  exact constant _ _ seen.choose_spec

/-- **A view determines a feature exactly when it conserves every distinction
the feature draws.** -/
theorem factors_iff_conserves {A : Type u} {S : Type v} {V : Sort w} [Nonempty V]
    (view : A → S) (feature : A → V) :
    Factors view feature ↔
      Mettapedia.Cybernetics.Distinction.Conserves (fun a b => feature a ≠ feature b)
        (Mettapedia.Cybernetics.Distinction.inequality S) view := by
  constructor
  · intro factors a b distinct same
    exact distinct (factors.constantOnFibers a b same)
  · intro conserves
    refine factors_of_constantOnFibers fun a b same => ?_
    by_contra distinct
    exact conserves a b distinct same

/-- **A view loses nothing exactly when it conserves every distinction.** -/
theorem factors_id_iff_conserves {A : Type u} {S : Type v} [Nonempty A] (view : A → S) :
    Factors view id ↔
      Mettapedia.Cybernetics.Distinction.Conserves (Mettapedia.Cybernetics.Distinction.inequality A)
        (Mettapedia.Cybernetics.Distinction.inequality S) view :=
  factors_iff_conserves view id

variable {A : Type u} {S : Sort v}

/-- **An observer factors through a view exactly when it respects the view's
bubble.** -/
theorem factors_iff_respects {Y : Type u} [Nonempty Y] (view : A → S) (observer : A → Y) :
    Factors view observer ↔ Respects (fun a b => view a = view b) observer :=
  ⟨fun factors a b same => factors.constantOnFibers a b same,
    fun respects => factors_of_constantOnFibers respects⟩

/-- **An observer factors through a view exactly when it is admissible for the
view's bubble** in the typed observation relation. -/
theorem factors_iff_admissible {Y : Type u} [Nonempty Y] (view : A → S) (observer : A → Y) :
    Factors view observer ↔
      Mettapedia.GSLT.TypedObservation.Admissible (Carrier := fun _ : Unit => Y)
        (fun a b => view a = view b)
        (Mettapedia.GSLT.TypedObservation.equalityChoice (fun _ : Unit => Y))
        (.arrow .proc (.ground ())) observer :=
  (factors_iff_respects view observer).trans (respects_iff_admissible _ observer)

end Observers

/-! ## Finest views form a class -/

section FinestClass

variable {A : Sort u} {ι : Sort v} {V : ι → Sort w} {view : (i : ι) → A → V i} {k l : ι}

/-- **Two finest members factor through each other.** -/
theorem Finest.mutual (finestK : Finest view k) (finestL : Finest view l) :
    Factors (view k) (view l) ∧ Factors (view l) (view k) :=
  ⟨finestK l, finestL k⟩

/-- **Two finest members identify the same points.** -/
theorem Finest.sameFibres (finestK : Finest view k) (finestL : Finest view l) (a b : A) :
    view k a = view k b ↔ view l a = view l b :=
  ⟨(finestK l).constantOnFibers a b, (finestL k).constantOnFibers a b⟩

/-- **Once one member is finest, the finest members are the members through
which it factors.** -/
theorem Finest.finest_iff (finestK : Finest view k) :
    Finest view l ↔ Factors (view l) (view k) :=
  ⟨fun finestL => finestL k, fun determines i => factors_trans determines (finestK i)⟩

/-- A member that identifies no more points than a finest member is finest. -/
theorem Finest.of_sameFibres [Nonempty (V k)] (finestK : Finest view k)
    (separates : ∀ a b, view l a = view l b → view k a = view k b) : Finest view l :=
  finestK.finest_iff.mpr (factors_of_constantOnFibers separates)

end FinestClass

/-- **Two finest members have one bubble.** -/
theorem Finest.ker_eq {A : Type u} {ι : Sort v} {V : ι → Type w} {view : (i : ι) → A → V i}
    {k l : ι} (finestK : Finest view k) (finestL : Finest view l) :
    Setoid.ker (view k) = Setoid.ker (view l) := by
  ext a b
  simp only [Setoid.ker_def]
  exact finestK.sameFibres finestL a b

/-! ## All two-valued observations -/

section TwoValued

variable {A : Type u}

/-- **A view determines every two-valued observation exactly when it is
injective.** -/
theorem factors_twoValued_iff_injective {S : Sort v} (view : A → S) :
    (∀ observation : A → Bool, Factors view observation) ↔ Function.Injective view := by
  classical
  constructor
  · intro determines a b same
    have recovered := (determines fun x => decide (x = a)).constantOnFibers a b same
    have reversed : b = a := by simpa using recovered.symm
    exact reversed.symm
  · intro injective observation
    exact factors_of_constantOnFibers fun a b same => congrArg observation (injective same)

/-- The values of a view adjoined to a family of two-valued observations. -/
abbrev AdjoinedCarrier (S : Type v) (ι : Type w) : Option ι → Type v
  | none => S
  | some _ => ULift.{v} Bool

/-- A view, at `none`, adjoined to a family of two-valued observations. -/
def adjoinTwoValued {S : Type v} {ι : Type w} (view : A → S) (observations : ι → A → Bool) :
    (i : Option ι) → A → AdjoinedCarrier S ι i
  | none => view
  | some i => fun a => ULift.up (observations i a)

/-- The adjoined view is finest exactly when it determines every observation of
the family. -/
theorem finest_adjoinTwoValued_iff {S : Type v} {ι : Type w} (view : A → S)
    (observations : ι → A → Bool) :
    Finest (adjoinTwoValued view observations) none ↔ ∀ i, Factors view (observations i) := by
  constructor
  · intro finest i
    obtain ⟨recover, recovers⟩ := finest (some i)
    exact ⟨fun shadow => (recover shadow).down, fun a => congrArg ULift.down (recovers a)⟩
  · intro determines
    rintro (_ | i)
    · exact ⟨id, fun _ => rfl⟩
    · obtain ⟨recover, recovers⟩ := determines i
      exact ⟨fun shadow => ULift.up (recover shadow), fun a => congrArg ULift.up (recovers a)⟩

/-- **Adjoined to all two-valued observations, a view is finest exactly when it
is injective.** -/
theorem finest_adjoinTwoValued_iff_injective {S : Type v} (view : A → S) :
    Finest (adjoinTwoValued view fun observation : A → Bool => observation) none ↔
      Function.Injective view :=
  (finest_adjoinTwoValued_iff view _).trans (factors_twoValued_iff_injective view)

end TwoValued

/-- Negative example: adjoined to the constant observations alone, the view of
`Bool` that identifies everything is finest, and it is not injective. -/
theorem finest_adjoinTwoValued_constant :
    Finest (adjoinTwoValued (fun _ : Bool => ()) fun (value _ : Bool) => value) none ∧
      ¬ Function.Injective (fun _ : Bool => ()) := by
  refine ⟨(finest_adjoinTwoValued_iff _ _).mpr fun value => ⟨fun _ => value, fun _ => rfl⟩, ?_⟩
  intro injective
  exact Bool.false_ne_true (injective rfl)

/-- **The family of observations cannot be restricted**: for some family of
two-valued observations, being finest and being injective come apart. -/
theorem not_forall_finest_adjoinTwoValued_iff_injective :
    ¬ ∀ (ι : Type) (observations : ι → Bool → Bool),
      (Finest (adjoinTwoValued (fun _ : Bool => ()) observations) none ↔
        Function.Injective (fun _ : Bool => ())) := fun all =>
  finest_adjoinTwoValued_constant.2 ((all _ _).mp finest_adjoinTwoValued_constant.1)

/-! ## The diagonal limit -/

section Diagonal

variable {A : Type u}

/-- **The joint view of all two-valued observations is injective**; its values
are observations of observations. -/
theorem joint_twoValued_injective :
    Function.Injective (joint fun observation : A → Bool => observation) :=
  (factors_twoValued_iff_injective _).mp fun observation =>
    factors_joint (fun observation : A → Bool => observation) observation

/-- **Cantor's diagonal.**  The subject's own elements cannot name every
two-valued observation of the subject. -/
theorem not_surjective_naming (name : A → A → Bool) : ¬ Function.Surjective name :=
  fun surjective =>
    let ⟨_, fixed⟩ := Function.exists_fixed_point_of_surjective name surjective not
    Bool.not_ne_self _ fixed

/-- **No self-describing finest view.**  A view of the two-valued observations of
`A` whose values are elements of `A` is not finest among the two-valued
observations of the observations. -/
theorem not_finest_selfDescribing (describe : (A → Bool) → A) :
    ¬ Finest (adjoinTwoValued describe fun observation : (A → Bool) → Bool => observation)
      none :=
  fun finest =>
    not_surjective_naming (Function.invFun describe)
      (Function.invFun_surjective ((finest_adjoinTwoValued_iff_injective describe).mp finest))

end Diagonal

/-! ## Axiom audit -/

#print axioms finest_iff_factors_joint
#print axioms factors_iff_admissible
#print axioms factors_iff_conserves
#print axioms ker_joint
#print axioms Finest.finest_iff
#print axioms Finest.of_sameFibres
#print axioms Finest.ker_eq
#print axioms factors_twoValued_iff_injective
#print axioms finest_adjoinTwoValued_iff_injective
#print axioms not_forall_finest_adjoinTwoValued_iff_injective
#print axioms joint_twoValued_injective
#print axioms not_surjective_naming
#print axioms not_finest_selfDescribing

end Mettapedia.GSLT.ViewPluralism
