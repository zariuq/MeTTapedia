import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Algebra
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Realizers

/-!
# The realizer algebra of Kripke candidates

Model S realizes values by Kripke candidates of the realizer side. As a
realizer algebra:

* `top` and `univ` are the strongly normalizing terms, `codes` the terms whose
  decoding is strongly normalizing;
* `meet` is the intersection, with the strongly normalizing terms;
* `piOver d c` is the intersection, over the index, of the function spaces from
  `d i` to `c i`; with one index it is the function space;
* `sigmaOver` is the candidate of pairs, and `ident` the identity candidate;
* `ctorReal T k Xs` holds the strongly normalizing terms that reduce to no other
  constructor of `T` at its number of fields, and whose reducts to `k` at the
  number of `Xs` have their arguments in `Xs`; `stuckReal T` holds those that
  reduce to no constructor of `T`. The constructors of `T` are read from the
  realizer side's roles, and only constructors declared with their number of
  fields are inspected.

At the numbers the constructor candidates are the candidates of the shapes of
numbers (`kcand_ctorReal_num`), and the candidate reading of the algebra is the
candidate reading of model S (`kcandReading_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization
open Consistency (Kind Carrier)
open Realizability (Realizers point Real Girard numReal candidateReading)
open StrongNormalization
open ValueSide (RealizerAlgebra algebraReading)

variable {Head : Type}

/-- The constructors of `T` in a table of roles: those an inductive type lists, and
none otherwise. -/
def ctorsOf (roles : Roles Head) (T : DeclName) : List (DeclName × List (Field Head)) :=
  match roles T with
  | .inductive cs => cs
  | _ => []

theorem ctorsOf_of_inductive {roles : Roles Head} {T : DeclName}
    {cs : List (DeclName × List (Field Head))} (role : roles T = .inductive cs) :
    ctorsOf roles T = cs := by
  unfold ctorsOf
  rw [role]

section Constructors

variable (T : Realizers Head)

/-- `t` reduces to the constructor `k`, declared with `a` fields, applied to the `a`
arguments `us`. -/
def Reaches (k : DeclName) (a : Nat) {m : Nat} (t : Tm Head m) (us : List (Tm Head m)) :
    Prop :=
  T.roles k = .constructor a ∧ us.length = a ∧
    StrongNormalization.ReducesStar T.rules t (appSpine (.const k) us)

variable {T}

namespace Reaches

variable {k : DeclName} {a : Nat}

/-- A reach of a reduct is a reach. -/
theorem head {m : Nat} {t t' : Tm Head m} {us : List (Tm Head m)}
    (step : StrongNormalization.Reduces T.rules t t')
    (reach : Reaches T k a t' us) : Reaches T k a t us :=
  ⟨reach.1, reach.2.1, .head step reach.2.2⟩

/-- An inert term reaches a constructor only through a reduct. -/
theorem inert {m : Nat} {t : Tm Head m} {us : List (Tm Head m)} (hi : Inert T.roles t)
    (reach : Reaches T k a t us) :
    ∃ t', StrongNormalization.Reduces T.rules t t' ∧ Reaches T k a t' us := by
  obtain ⟨t', step, rest⟩ := reach.2.2.first_step (hi.2.2.2.1 k a us reach.1)
  exact ⟨t', step, reach.1, reach.2.1, rest⟩

/-- A reach of a renamed term is the renaming of a reach of the term. -/
theorem rename_inv {m m' : Nat} {ρ : Ren m m'} {t : Tm Head m} {us : List (Tm Head m')}
    (reach : Reaches T k a (Presentation.rename ρ t) us) :
    ∃ us₀, Reaches T k a t us₀ ∧ us₀.map (Presentation.rename ρ) = us := by
  obtain ⟨t', steps, e⟩ := ReducesStar.rename_inv T.reflects reach.2.2
  obtain ⟨us₀, rfl, rfl⟩ := rename_eq_constSpine e.symm
  refine ⟨us₀, ⟨reach.1, ?_, steps⟩, rfl⟩
  rw [← reach.2.1, List.length_map]

end Reaches

variable (T)

/-- The realizers of a value of the inductive type `tyName` built by the
constructor `k` from fields realized by `Xs`. -/
def ctorCand (tyName k : DeclName) (Xs : List T.Cand) : T.Cand where
  mem := fun {m} t => SN T.rules t ∧
    (∀ k' fs, (k', fs) ∈ ctorsOf T.roles tyName → k' ≠ k →
      ∀ us : List (Tm Head m), ¬ Reaches T k' fs.length t us) ∧
    ∀ us : List (Tm Head m), Reaches T k Xs.length t us →
      List.Forall₂ (fun (X : T.Cand) (u : Tm Head m) => X.mem u) Xs us
  rename := fun {_ _} ρ {_} h => by
    refine ⟨SN.rename T.reflects ρ h.1, fun k' fs mem ne us reach => ?_, fun us reach => ?_⟩
    · obtain ⟨us₀, reach₀, -⟩ := reach.rename_inv
      exact h.2.1 k' fs mem ne us₀ reach₀
    · obtain ⟨us₀, reach₀, rfl⟩ := reach.rename_inv
      exact List.forall₂_map_right_iff.mpr ((h.2.2 us₀ reach₀).imp fun X _ hu => X.rename ρ hu)
  sn := fun h => h.1
  reduct := fun h step =>
    ⟨h.1.reduct step, fun k' fs mem ne us reach => h.2.1 k' fs mem ne us (reach.head step),
      fun us reach => h.2.2 us (reach.head step)⟩
  inert := fun hi h => by
    refine ⟨SN.intro fun u step => (h u step).1, fun k' fs mem ne us reach => ?_,
      fun us reach => ?_⟩
    · obtain ⟨t', step, reach'⟩ := reach.inert hi
      exact (h t' step).2.1 k' fs mem ne us reach'
    · obtain ⟨t', step, reach'⟩ := reach.inert hi
      exact (h t' step).2.2 us reach'

/-- The realizers of a value of the inductive type `tyName` stuck on the daimon:
strongly normalizing terms that reach no constructor of `tyName`. -/
def stuckCand (tyName : DeclName) : T.Cand where
  mem := fun {m} t => SN T.rules t ∧
    ∀ k' fs, (k', fs) ∈ ctorsOf T.roles tyName →
      ∀ us : List (Tm Head m), ¬ Reaches T k' fs.length t us
  rename := fun {_ _} ρ {_} h => by
    refine ⟨SN.rename T.reflects ρ h.1, fun k' fs mem us reach => ?_⟩
    obtain ⟨us₀, reach₀, -⟩ := reach.rename_inv
    exact h.2 k' fs mem us₀ reach₀
  sn := fun h => h.1
  reduct := fun h step =>
    ⟨h.1.reduct step, fun k' fs mem us reach => h.2 k' fs mem us (reach.head step)⟩
  inert := fun hi h => by
    refine ⟨SN.intro fun u step => (h u step).1, fun k' fs mem us reach => ?_⟩
    obtain ⟨t', step, reach'⟩ := reach.inert hi
    exact (h t' step).2 k' fs mem us reach'

end Constructors

/-! ## The algebra -/

variable (T : Realizers Head)

/-- The Kripke candidates of the realizer side as a realizer algebra. -/
def kcandAlgebra : RealizerAlgebra Head where
  Cand := T.Cand
  top := T.sn
  univ := T.sn
  codes := T.codes
  meet := fun F => KCand.inter T.reflects F
  piOver := fun d c => KCand.inter T.reflects fun i => KCand.arrow T.shape T.reflects (d i) (c i)
  sigmaOver := KCand.sigma T.shape
  ident := IdCand T.reflects
  ctorReal := ctorCand T
  stuckReal := stuckCand T

/-- **The laws of the Kripke-candidate algebra.** -/
theorem kcandAlgebra_laws : (kcandAlgebra T).Laws where
  meet_const := fun f x all nonempty => by
    obtain ⟨i⟩ := nonempty
    refine KCand.ext fun t => ⟨fun h => ?_, fun h => ⟨x.sn h, fun j => ?_⟩⟩
    · have hi := h.2 i
      rwa [all i] at hi
    · rw [all j]
      exact h
  meet_congr := fun f g fg gf => KCand.ext fun t =>
    ⟨fun h => ⟨h.1, fun j => by
        obtain ⟨i, e⟩ := gf j
        rw [← e]
        exact h.2 i⟩,
      fun h => ⟨h.1, fun i => by
        obtain ⟨j, e⟩ := fg i
        rw [e]
        exact h.2 j⟩⟩
  piOver_congr := fun d c d' c' fg gf => KCand.ext fun t =>
    ⟨fun h => ⟨h.1, fun j => by
        obtain ⟨i, ed, ec⟩ := gf j
        have hi : (KCand.arrow T.shape T.reflects (d i) (c i)).mem t := h.2 i
        show (KCand.arrow T.shape T.reflects (d' j) (c' j)).mem t
        rw [← congrArg₂ (KCand.arrow T.shape T.reflects) ed ec]
        exact hi⟩,
      fun h => ⟨h.1, fun i => by
        obtain ⟨j, ed, ec⟩ := fg i
        have hj : (KCand.arrow T.shape T.reflects (d' j) (c' j)).mem t := h.2 j
        show (KCand.arrow T.shape T.reflects (d i) (c i)).mem t
        rw [congrArg₂ (KCand.arrow T.shape T.reflects) ed ec]
        exact hj⟩⟩

/-- Girard's clause over an inhabited index is the dependent function space of
Kripke candidates. -/
theorem kcand_piOver_eq_pi {ι : Type} (p : ι) (d c : ι → T.Cand) :
    (kcandAlgebra T).piOver d c = KCand.pi T.shape T.reflects p d c :=
  KCand.ext fun _ =>
    ⟨fun h i _ ρ a ha => h.2 i ρ a ha,
      fun h => ⟨(KCand.pi T.shape T.reflects p d c).sn h, fun i _ ρ a ha => h i ρ a ha⟩⟩

/-- The function space of the algebra is the Kripke function space. -/
theorem kcand_arrow (X Y : T.Cand) :
    (kcandAlgebra T).arrow X Y = KCand.arrow T.shape T.reflects X Y :=
  (kcand_piOver_eq_pi T () (fun _ => X) (fun _ => Y)).trans
    (KCand.arrow_eq_pi T.shape T.reflects X Y).symm

/-! ## The numbers -/

/-- The constructors `zero` and `suc` are distinct. -/
theorem zero_ne_suc : T.zero ≠ T.suc := by
  intro e
  have h := T.numerals.zero
  rw [e, T.numerals.suc] at h
  cases h

/-- **The constructor candidates at the numbers are the candidates of the shapes
of numbers.** -/
theorem kcand_ctorReal_num {num : DeclName}
    (role : T.roles num = .inductive [(T.zero, []), (T.suc, [.recursive])]) :
    ∀ s : NumShape,
      (kcandAlgebra T).numReal num T.zero T.suc s = NumReal T.reflects T.numerals s := by
  have ctors := ctorsOf_of_inductive role
  have memCtors : ∀ {k' : DeclName} {fs : List (Field Head)},
      (k', fs) ∈ ctorsOf T.roles num →
        (k' = T.zero ∧ fs = []) ∨ (k' = T.suc ∧ fs = [.recursive]) := by
    intro k' fs mem
    rw [ctors] at mem
    simpa using mem
  have zeroMem : ((T.zero, []) : DeclName × List (Field Head)) ∈ ctorsOf T.roles num := by
    rw [ctors]
    simp
  have sucMem : ((T.suc, [.recursive]) : DeclName × List (Field Head)) ∈
      ctorsOf T.roles num := by
    rw [ctors]
    simp
  have reachZero : ∀ {m : Nat} {t : Tm Head m} {us : List (Tm Head m)},
      Reaches T T.zero 0 t us ↔ us = [] ∧ StrongNormalization.ReducesStar T.rules t (.const T.zero) := by
    intro m t us
    constructor
    · rintro ⟨-, len, steps⟩
      obtain rfl := List.eq_nil_of_length_eq_zero len
      exact ⟨rfl, steps⟩
    · rintro ⟨rfl, steps⟩
      exact ⟨T.numerals.zero, rfl, steps⟩
  have reachSuc : ∀ {m : Nat} {t : Tm Head m} {us : List (Tm Head m)},
      Reaches T T.suc 1 t us ↔
        ∃ u, us = [u] ∧ StrongNormalization.ReducesStar T.rules t (.app (.const T.suc) u) := by
    intro m t us
    constructor
    · rintro ⟨-, len, steps⟩
      obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp len
      exact ⟨u, rfl, steps⟩
    · rintro ⟨u, rfl, steps⟩
      exact ⟨T.numerals.suc, rfl, steps⟩
  intro s
  induction s with
  | zero =>
      refine KCand.ext fun t => ⟨fun h => ⟨h.1, fun u steps => ?_⟩, fun h => ⟨h.1, ?_, ?_⟩⟩
      · exact h.2.1 T.suc [.recursive] sucMem (zero_ne_suc T).symm [u]
          (reachSuc.mpr ⟨u, rfl, steps⟩)
      · intro k' fs mem ne us reach
        rcases memCtors mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ne rfl
        · obtain ⟨u, rfl, steps⟩ := reachSuc.mp reach
          exact h.2 u steps
      · intro us reach
        obtain ⟨rfl, -⟩ := reachZero.mp reach
        exact .nil
  | suc s ih =>
      change ctorCand T num T.suc [(kcandAlgebra T).numReal num T.zero T.suc s] = _
      rw [ih]
      refine KCand.ext fun t => ⟨fun h => ⟨h.1, fun steps => ?_, fun u steps => ?_⟩,
        fun h => ⟨h.1, ?_, ?_⟩⟩
      · exact h.2.1 T.zero [] zeroMem (zero_ne_suc T) [] (reachZero.mpr ⟨rfl, steps⟩)
      · have fields := h.2.2 [u] (reachSuc.mpr ⟨u, rfl, steps⟩)
        cases fields with
        | cons hu _ => exact hu
      · intro k' fs mem ne us reach
        rcases memCtors mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨rfl, steps⟩ := reachZero.mp reach
          exact h.2.1 steps
        · exact ne rfl
      · intro us reach
        obtain ⟨u, rfl, steps⟩ := reachSuc.mp reach
        exact .cons (h.2.2 u steps) .nil
  | star =>
      refine KCand.ext fun t => ⟨fun h => ⟨h.1, fun steps => ?_, fun u steps => ?_⟩,
        fun h => ⟨h.1, ?_⟩⟩
      · exact h.2 T.zero [] zeroMem [] (reachZero.mpr ⟨rfl, steps⟩)
      · exact h.2 T.suc [.recursive] sucMem [u] (reachSuc.mpr ⟨u, rfl, steps⟩)
      · intro k' fs mem us reach
        rcases memCtors mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · obtain ⟨rfl, steps⟩ := reachZero.mp reach
          exact h.2.1 steps
        · obtain ⟨u, rfl, steps⟩ := reachSuc.mp reach
          exact h.2.2 u steps

/-! ## The reading -/

section Reading

variable (S : Consistency.Setting Head) (star num : DeclName)

/-- The realizers of the meanings of carriers in the algebra are those of model S,
when the numbers of the two sides agree. -/
theorem kcand_real (zero : S.zero = T.zero) (suc : S.suc = T.suc)
    (role : T.roles num = .inductive [(T.zero, []), (T.suc, [.recursive])]) :
    ∀ {k : Kind} (K : Carrier k),
      (kcandAlgebra T).Real S star num K = Real S star T K
  | _, .prop => rfl
  | _, .rigid _ => rfl
  | _, .num => by
      funext v
      change (kcandAlgebra T).numValReal S star num v = numReal S star T v
      unfold RealizerAlgebra.numValReal numReal
      rw [zero, suc]
      simp only [kcand_ctorReal_num T role]
      rfl
  | _, @Carrier.arr _ .gen K K' => by
      funext φ
      change (kcandAlgebra T).piOver ((kcandAlgebra T).Real S star num K)
          (fun v => (kcandAlgebra T).Real S star num K' (φ v)) =
        KCand.pi T.shape T.reflects (point S star T.sn K) (Real S star T K)
          fun v => Real S star T K' (φ v)
      rw [kcand_real zero suc role K, kcand_real zero suc role K']
      exact kcand_piOver_eq_pi T _ _ _
  | _, @Carrier.arr .gen .data K K' => by
      funext F
      change (kcandAlgebra T).piOver ((kcandAlgebra T).Real S star num K)
          (fun _ => (kcandAlgebra T).Real S star num K' (Realizability.appGen F)) =
        KCand.pi T.shape T.reflects (point S star T.sn K) (Real S star T K)
          fun _ => Real S star T K' (Realizability.appGen F)
      rw [kcand_real zero suc role K, kcand_real zero suc role K']
      exact kcand_piOver_eq_pi T _ _ _
  | _, @Carrier.arr .data .data K K' => by
      funext F
      change (kcandAlgebra T).piOver ((kcandAlgebra T).Real S star num K)
          (fun a => (kcandAlgebra T).Real S star num K' (Realizability.appData F a)) =
        KCand.pi T.shape T.reflects (point S star T.sn K) (Real S star T K)
          fun a => Real S star T K' (Realizability.appData F a)
      rw [kcand_real zero suc role K, kcand_real zero suc role K']
      exact kcand_piOver_eq_pi T _ _ _

/-- Quantification in the algebra's reading is Girard's clause of model S. -/
theorem kcand_allMeaning (zero : S.zero = T.zero) (suc : S.suc = T.suc)
    (role : T.roles num = .inductive [(T.zero, []), (T.suc, [.recursive])]) {k : Kind}
    (K : Carrier k) (φ : K.Val (S.shapes star) (kcandAlgebra T).Cand → (kcandAlgebra T).Cand) :
    (kcandAlgebra T).piOver ((kcandAlgebra T).Real S star num K) φ = Girard S star T K φ := by
  rw [kcand_real T S star num zero suc role K]
  exact kcand_piOver_eq_pi T _ _ _

/-- **The candidate reading of the algebra is the candidate reading of model S**,
when the numbers of the value side and of the realizer side agree. -/
theorem kcandReading_eq (zero : S.zero = T.zero) (suc : S.suc = T.suc)
    (role : T.roles num = .inductive [(T.zero, []), (T.suc, [.recursive])]) :
    algebraReading S star num (kcandAlgebra T) = candidateReading S star T := by
  have arrow : (kcandAlgebra T).arrow = KCand.arrow T.shape T.reflects :=
    funext fun X => funext fun Y => kcand_arrow T X Y
  unfold algebraReading candidateReading
  simp only [arrow, kcand_allMeaning T S star num zero suc role]
  rfl

end Reading

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
