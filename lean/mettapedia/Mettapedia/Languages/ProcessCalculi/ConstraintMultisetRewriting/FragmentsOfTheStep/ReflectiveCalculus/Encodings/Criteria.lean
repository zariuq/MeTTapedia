import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Calculi

/-!
# The criteria for a good encoding, stated once

Gorla, *Towards a unified approach to encodability and separation results for process calculi*
(Information and Computation 208(9), 2010), §2, takes a calculus to be a triple `(P, ⟼, ≍)` of
terms, reduction and a behavioural equivalence, writes `⟹` for the reflexive and transitive closure
of `⟼`, and asks five properties of a translation `⟦·⟧`. They are quoted with their numbers.

* **Property 1 (Compositionality)**: "for every k-ary operator op of L1 and for every subset of
  names N, there exists a k-ary context C^N_op(_1;...;_k) such that, for all S1,...,Sk with
  F(S1,...,Sk) = N, it holds that ⟦op(S1,...,Sk)⟧ = C^N_op(⟦S1⟧;...;⟦Sk⟧)", where a k-ary context is
  a term in which k occurrences of 0 are linearly replaced by holes, every hole once.
  `CompositionalAt` is the equation for one operator and one context. The criterion is in the class
  of contexts: with an arbitrary function in place of a context every injective translation is
  compositional at every operator (`compositionalAt_of_injective`). Where this file is applied, the
  contexts are the target's own constructions (the parallel composition of states, a rule's pattern
  filled by instantiation).
* **Definition 5.2 (homomorphic with respect to `|`)**: "C^N_|(_1;_2) = _1 | _2 for every N".
  `Homomorphic`, up to a static equivalence of the target.
* **Property 2 (Name invariance)**: "for every S and σ, ⟦Sσ⟧ = ⟦S⟧σ' if σ is injective, ≍2 ⟦S⟧σ'
  otherwise, where σ' is such that φ(σ(a)) = σ'(φ(a)) for every a", with `φ` the renaming policy.
  It needs names and substitutions on both sides; `NameInvariant` states it for any substitution
  actions and policy. How it is read for a calculus whose names are quoted processes is said where
  it is applied.
* **Property 3 (Operational correspondence)**: Complete, "for all S ⟹1 S', it holds that
  ⟦S⟧ ⟹2 ≍2 ⟦S'⟧"; Sound, "for all ⟦S⟧ ⟹2 T, there exists an S' such that S ⟹1 S' and
  T ⟹2 ≍2 ⟦S'⟧". `OperationalCorrespondence`.
* **Property 4 (Divergence reflection)**: "for every S such that ⟦S⟧ ⟼ω2, it holds that S ⟼ω1".
  `DivergenceReflecting`, with `Calculus.Diverges` an infinite run.
* **Property 5 (Success sensitiveness)**: "for every S, it holds that S⇓ iff ⟦S⟧⇓", where `⇓` is
  reachability (may) of a term showing success. `SuccessSensitive`. Gorla also asks that "≍ never
  relates two processes P and Q such that P⇓ and Q⇏" (`Calculus.SuccessRespecting`).

A calculus here (`Calculus`) has terms, a reduction, a success observation and an equivalence. A
calculus with a parallel composition of `ParallelClosed` is one of these once an equivalence is
chosen (`ofParallel`), and a **uniform translation** of `ParallelClosed` is exactly a translation
homomorphic on parallel composition (up to the target's static equivalence, on composable pairs)
and success sensitive (`uniform_iff`): Definition 5.2 together with Property 5.

## Controls (`Controls`)

On calculi of two points, each of the four operational properties is shown to have content: for
each, the identity map between two such calculi fails it and meets the other three
(`only_complete_fails`, `only_sound_fails`, `only_divergence_fails`, `only_success_fails`), and the
identity of a calculus into itself meets all four (`identity_meets_all`). Gorla's coherence condition
fails for an equivalence that relates everything and holds for equality (`coherence_has_content`).
On a calculus of names, the identity is name invariant and a translation that singles out one name is
not (`nameInvariant_has_content`). Compositionality with a function in place of a context is met by
every injective translation (`compositionalAt_of_injective`, `compositional_without_contexts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

universe u v

/-! ## Calculi -/

/-- **A calculus**: terms, a reduction, a success observation, and a behavioural equivalence
(Gorla's `(P, ⟼, ≍)` with his success observation). -/
structure Calculus where
  Term : Type u
  step : Term → Term → Prop
  success : Term → Prop
  equiv : Term → Term → Prop

namespace Calculus

variable (L : Calculus.{u})

/-- Reflexive and transitive closure of the reduction (`⟹`). -/
def Reaches : L.Term → L.Term → Prop := Relation.ReflTransGen L.step

/-- **Success** (`⇓`, may): some run reaches a term showing success. -/
def Succeeds (t : L.Term) : Prop := ∃ t', L.Reaches t t' ∧ L.success t'

/-- **Divergence** (`⟼ω`): an infinite run. -/
def Diverges (t : L.Term) : Prop := ∃ f : ℕ → L.Term, f 0 = t ∧ ∀ n, L.step (f n) (f (n + 1))

/-- Gorla's coherence of the equivalence with success: it never relates a term that succeeds and
one that does not. -/
def SuccessRespecting : Prop := ∀ t t', L.equiv t t' → (L.Succeeds t ↔ L.Succeeds t')

end Calculus

/-! ## The criteria -/

section Criteria

variable {L : Calculus.{u}} {M : Calculus.{v}}

/-- **Operational correspondence** (Property 3), up to the target's equivalence. -/
structure OperationalCorrespondence (map : L.Term → M.Term) : Prop where
  complete : ∀ S S', L.Reaches S S' → ∃ T, M.Reaches (map S) T ∧ M.equiv T (map S')
  sound : ∀ S T, M.Reaches (map S) T →
    ∃ S', L.Reaches S S' ∧ ∃ T', M.Reaches T T' ∧ M.equiv T' (map S')

/-- **Divergence reflection** (Property 4). -/
def DivergenceReflecting (map : L.Term → M.Term) : Prop :=
  ∀ S, M.Diverges (map S) → L.Diverges S

/-- **Success sensitiveness** (Property 5). -/
def SuccessSensitive (map : L.Term → M.Term) : Prop :=
  ∀ S, L.Succeeds S ↔ M.Succeeds (map S)

/-- **Compositional at an operator** (Property 1, one operator, one set of names): the translation
of the operator applied to arguments is the context filled with their translations. -/
def CompositionalAt {k : ℕ} (map : L.Term → M.Term) (op : (Fin k → L.Term) → L.Term)
    (context : (Fin k → M.Term) → M.Term) : Prop :=
  ∀ arguments, map (op arguments) = context (fun i => map (arguments i))

/-- **Homomorphic on parallel composition** (Definition 5.2): the context of parallel composition
is the target's parallel composition, here up to a static equivalence `same` of the target. -/
def Homomorphic (map : L.Term → M.Term) (parL : L.Term → L.Term → L.Term)
    (parM : M.Term → M.Term → M.Term) (same : M.Term → M.Term → Prop) : Prop :=
  ∀ S S', same (map (parL S S')) (parM (map S) (map S'))

/-- A homomorphic translation (up to equality) is compositional at parallel composition, with the
target's parallel composition as the context. -/
theorem Homomorphic.compositionalAt {map : L.Term → M.Term} {parL : L.Term → L.Term → L.Term}
    {parM : M.Term → M.Term → M.Term} (homomorphic : Homomorphic map parL parM Eq) :
    CompositionalAt map (fun arguments : Fin 2 → L.Term => parL (arguments 0) (arguments 1))
      (fun images => parM (images 0) (images 1)) :=
  fun arguments => homomorphic (arguments 0) (arguments 1)

/-- **Name invariance** (Property 2), for substitutions `σ : Sub` acting on source terms by `act`,
a renaming policy giving each its target substitution `policy σ` acting by `act'`, and the
injective substitutions singled out. -/
structure NameInvariant {Sub : Type*} {Sub' : Type*} (map : L.Term → M.Term)
    (act : Sub → L.Term → L.Term) (act' : Sub' → M.Term → M.Term) (policy : Sub → Sub')
    (injective : Sub → Prop) : Prop where
  exact : ∀ σ, injective σ → ∀ S, map (act σ S) = act' (policy σ) (map S)
  upTo : ∀ σ, ¬ injective σ → ∀ S, M.equiv (map (act σ S)) (act' (policy σ) (map S))

/-- **Compositionality needs a class of contexts.** With an arbitrary function as the context,
every injective translation is compositional at every operator. -/
theorem compositionalAt_of_injective [Nonempty L.Term] {map : L.Term → M.Term}
    (injective : Function.Injective map) {k : ℕ} (op : (Fin k → L.Term) → L.Term) :
    CompositionalAt map op (fun images => map (op (fun i => Function.invFun map (images i)))) := by
  intro arguments
  simp only [Function.leftInverse_invFun injective _]

end Criteria

/-! ## Success sensitiveness and divergence along equalities -/

section General

variable {L : Calculus.{u}} {M : Calculus.{v}}

/-- Success is reachable success at once. -/
theorem Calculus.succeeds_of_success {t : L.Term} (shows : L.success t) : L.Succeeds t :=
  ⟨t, .refl, shows⟩

/-- With equality as the equivalence, success is respected. -/
theorem Calculus.successRespecting_of_eq (equality : ∀ t t', L.equiv t t' → t = t') :
    L.SuccessRespecting := by
  intro t t' same
  rw [equality t t' same]

end General

/-! ## Calculi with a parallel composition, and uniform translations -/

/-- **A calculus with a parallel composition, with a chosen behavioural equivalence.** -/
def ofParallel (L : ParallelCalculus.{u}) (equiv : L.Term → L.Term → Prop) : Calculus.{u} :=
  ⟨L.Term, L.step, L.success, equiv⟩

/-- Reachable success is the same notion. -/
theorem succeeds_ofParallel (L : ParallelCalculus.{u}) (equiv : L.Term → L.Term → Prop)
    (t : L.Term) : (ofParallel L equiv).Succeeds t ↔ L.Succeeds t :=
  Iff.rfl

/-- **A uniform translation is a translation homomorphic on parallel composition and success
sensitive**: homomorphism up to the target's static equivalence on composable pairs
(Definition 5.2), and preservation and reflection of reachable success (Property 5). The
equivalences `equivL` and `equivM` only complete the two calculi (`ofParallel`); success
sensitiveness reads reduction and success, not them. -/
theorem uniform_iff {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (equivL : L.Term → L.Term → Prop) (equivM : M.Term → M.Term → Prop) (map : L.Term → M.Term) :
    (∃ τ : UniformTranslation L M, τ.map = map) ↔
      (∀ s s', L.composable s s' → M.same (map (L.par s s')) (M.par (map s) (map s'))) ∧
        SuccessSensitive (L := ofParallel L equivL) (M := ofParallel M equivM) map := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.homomorphic, fun s => ⟨τ.preserves s, τ.reflects s⟩⟩
  · rintro ⟨homomorphic, sensitive⟩
    exact ⟨⟨map, homomorphic, fun s => (sensitive s).mp, fun s => (sensitive s).mpr⟩, rfl⟩

/-! ## Controls on calculi of two points -/

namespace Controls

/-- Two points. -/
inductive Pt where
  | p
  | q
  deriving DecidableEq

/-- A calculus on two points, with equality as the equivalence. -/
def tiny (step : Pt → Pt → Prop) (success : Pt → Prop) : Calculus.{0} := ⟨Pt, step, success, Eq⟩

/-- No reduction. -/
def stuck : Pt → Pt → Prop := fun _ _ => False

/-- One reduction, from `p` to `q`. -/
def toQ : Pt → Pt → Prop := fun x y => x = .p ∧ y = .q

/-- A loop on `p`. -/
def loop : Pt → Pt → Prop := fun x y => x = .p ∧ y = .p

/-- Success at `p`. -/
def atP : Pt → Prop := fun x => x = .p

/-- No success. -/
def never : Pt → Prop := fun _ => False

theorem reaches_stuck {success : Pt → Prop} {x y : Pt} :
    (tiny stuck success).Reaches x y ↔ x = y := by
  constructor
  · intro run
    rcases Relation.ReflTransGen.cases_head run with same | ⟨_, never', _⟩
    · exact same
    · exact never'.elim
  · rintro rfl
    exact .refl

theorem reaches_toQ {success : Pt → Prop} {x y : Pt} :
    (tiny toQ success).Reaches x y ↔ x = y ∨ (x = .p ∧ y = .q) := by
  constructor
  · intro run
    induction run with
    | refl => exact .inl rfl
    | tail _ last ih =>
        obtain ⟨rfl, rfl⟩ := last
        rcases ih with rfl | ⟨_, absurd'⟩
        · exact .inr ⟨rfl, rfl⟩
        · cases absurd'
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact .refl
    · exact .single ⟨rfl, rfl⟩

theorem reaches_loop {success : Pt → Prop} {x y : Pt} :
    (tiny loop success).Reaches x y ↔ x = y := by
  constructor
  · intro run
    induction run with
    | refl => rfl
    | tail _ last ih =>
        obtain ⟨rfl, rfl⟩ := last
        exact ih
  · rintro rfl
    exact .refl

theorem not_diverges_stuck {success : Pt → Prop} (x : Pt) : ¬ (tiny stuck success).Diverges x := by
  rintro ⟨f, _, steps⟩
  exact steps 0

theorem not_diverges_toQ {success : Pt → Prop} (x : Pt) : ¬ (tiny toQ success).Diverges x := by
  rintro ⟨f, _, steps⟩
  have first := (steps 0).2
  have second := (steps 1).1
  rw [first] at second
  cases second

theorem diverges_loop {success : Pt → Prop} : (tiny loop success).Diverges .p :=
  ⟨fun _ => .p, rfl, fun _ => ⟨rfl, rfl⟩⟩

theorem not_succeeds_never {step : Pt → Pt → Prop} (x : Pt) : ¬ (tiny step never).Succeeds x := by
  rintro ⟨_, _, shows⟩
  exact shows

/-- **The identity of a calculus into itself meets the four operational criteria.** -/
theorem identity_meets_all :
    OperationalCorrespondence (L := tiny toQ atP) (M := tiny toQ atP) id ∧
      DivergenceReflecting (L := tiny toQ atP) (M := tiny toQ atP) id ∧
      SuccessSensitive (L := tiny toQ atP) (M := tiny toQ atP) id :=
  ⟨⟨fun _ S' run => ⟨S', run, rfl⟩, fun _ T run => ⟨T, run, T, .refl, rfl⟩⟩,
    fun _ diverges => diverges, fun _ => Iff.rfl⟩

/-- **Completeness has content**: a source reduction `p ⟼ q` the target does not have. The
identity is sound, reflects divergence and is success sensitive, and is not complete. -/
theorem only_complete_fails :
    ¬ (∀ S S', (tiny toQ never).Reaches S S' →
        ∃ T, (tiny stuck never).Reaches (id S) T ∧ (tiny stuck never).equiv T (id S')) ∧
      (∀ S T, (tiny stuck never).Reaches (id S) T →
        ∃ S', (tiny toQ never).Reaches S S' ∧
          ∃ T', (tiny stuck never).Reaches T T' ∧ (tiny stuck never).equiv T' (id S')) ∧
      DivergenceReflecting (L := tiny toQ never) (M := tiny stuck never) id ∧
      SuccessSensitive (L := tiny toQ never) (M := tiny stuck never) id := by
  refine ⟨fun complete => ?_, fun S T run => ?_, fun S diverges => ?_, fun S => ?_⟩
  · obtain ⟨T, run, same⟩ := complete .p .q (reaches_toQ.mpr (.inr ⟨rfl, rfl⟩))
    have start := reaches_stuck.mp run
    rw [← start] at same
    cases same
  · have same := reaches_stuck.mp run
    exact ⟨S, .refl, T, .refl, same.symm⟩
  · exact (not_diverges_stuck _ diverges).elim
  · exact ⟨fun shows => (not_succeeds_never _ shows).elim, fun shows => (not_succeeds_never _ shows).elim⟩

/-- **Soundness has content**: a target reduction `p ⟼ q` with no source counterpart. The identity
is complete, reflects divergence and is success sensitive, and is not sound. -/
theorem only_sound_fails :
    (∀ S S', (tiny stuck never).Reaches S S' →
        ∃ T, (tiny toQ never).Reaches (id S) T ∧ (tiny toQ never).equiv T (id S')) ∧
      ¬ (∀ S T, (tiny toQ never).Reaches (id S) T →
        ∃ S', (tiny stuck never).Reaches S S' ∧
          ∃ T', (tiny toQ never).Reaches T T' ∧ (tiny toQ never).equiv T' (id S')) ∧
      DivergenceReflecting (L := tiny stuck never) (M := tiny toQ never) id ∧
      SuccessSensitive (L := tiny stuck never) (M := tiny toQ never) id := by
  refine ⟨fun S S' run => ?_, fun sound => ?_, fun S diverges => ?_, fun S => ?_⟩
  · have same := reaches_stuck.mp run
    exact ⟨S, .refl, same⟩
  · obtain ⟨S', run, T', later, same⟩ := sound .p .q (reaches_toQ.mpr (.inr ⟨rfl, rfl⟩))
    have start := reaches_stuck.mp run
    subst start
    rcases reaches_toQ.mp later with rfl | ⟨absurd', _⟩
    · cases same
    · cases absurd'
  · exact (not_diverges_toQ _ diverges).elim
  · exact ⟨fun shows => (not_succeeds_never _ shows).elim, fun shows => (not_succeeds_never _ shows).elim⟩

/-- **Divergence reflection has content**: a silent loop the source does not have. The identity is
complete, sound and success sensitive, and does not reflect divergence. -/
theorem only_divergence_fails :
    OperationalCorrespondence (L := tiny stuck never) (M := tiny loop never) id ∧
      ¬ DivergenceReflecting (L := tiny stuck never) (M := tiny loop never) id ∧
      SuccessSensitive (L := tiny stuck never) (M := tiny loop never) id := by
  refine ⟨⟨fun S S' run => ?_, fun S T run => ?_⟩, fun reflects => ?_, fun S => ?_⟩
  · have same := reaches_stuck.mp run
    exact ⟨S, .refl, same⟩
  · have same := reaches_loop.mp run
    exact ⟨S, .refl, T, .refl, same.symm⟩
  · exact not_diverges_stuck _ (reflects .p diverges_loop)
  · exact ⟨fun shows => (not_succeeds_never _ shows).elim, fun shows => (not_succeeds_never _ shows).elim⟩

/-- **Success sensitiveness has content**: success at `p` in the source and nowhere in the target.
The identity is complete, sound and reflects divergence, and is not success sensitive. -/
theorem only_success_fails :
    OperationalCorrespondence (L := tiny stuck atP) (M := tiny stuck never) id ∧
      DivergenceReflecting (L := tiny stuck atP) (M := tiny stuck never) id ∧
      ¬ SuccessSensitive (L := tiny stuck atP) (M := tiny stuck never) id := by
  refine ⟨⟨fun S S' run => ?_, fun S T run => ?_⟩, fun S diverges => ?_, fun sensitive => ?_⟩
  · have same := reaches_stuck.mp run
    exact ⟨S, .refl, same⟩
  · have same := reaches_stuck.mp run
    exact ⟨S, .refl, T, .refl, same.symm⟩
  · exact (not_diverges_stuck _ diverges).elim
  · exact not_succeeds_never _ ((sensitive .p).mp (Calculus.succeeds_of_success (L := tiny stuck atP) rfl))

/-- **Gorla's coherence condition has content**: an equivalence that relates every two terms does
not respect success when one term succeeds and another does not; equality does. -/
theorem coherence_has_content :
    ¬ (⟨Pt, stuck, atP, fun _ _ => True⟩ : Calculus.{0}).SuccessRespecting ∧
      (tiny stuck atP).SuccessRespecting := by
  refine ⟨fun respects => ?_, Calculus.successRespecting_of_eq fun _ _ same => same⟩
  have shows : (⟨Pt, stuck, atP, fun _ _ => True⟩ : Calculus.{0}).Succeeds .p := ⟨.p, .refl, rfl⟩
  obtain ⟨x, run, atX⟩ := (respects .p .q trivial).mp shows
  rcases Relation.ReflTransGen.cases_head run with same | ⟨_, never, _⟩
  · subst same
    cases atX
  · exact never

/-- A calculus of names: a term is one name, with no reduction and no success. -/
abbrev names : Calculus.{0} := ⟨ℕ, fun _ _ => False, fun _ => False, Eq⟩

/-- **Name invariance has content.** With renamings of names acting by application and the identity
policy, the identity translation is name invariant, and the translation that singles out the name
`0` (sending it to `1`) is not: the injective renaming that swaps `0` and `2` separates them. -/
theorem nameInvariant_has_content :
    NameInvariant (L := names) (M := names) (Sub := ℕ → ℕ) (Sub' := ℕ → ℕ) id
        (fun σ n => σ n) (fun σ n => σ n) id Function.Injective ∧
      ¬ NameInvariant (L := names) (M := names) (Sub := ℕ → ℕ) (Sub' := ℕ → ℕ)
        (fun n : ℕ => if n = 0 then 1 else n) (fun σ n => σ n) (fun σ n => σ n) id
        Function.Injective := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun invariant => ?_⟩
  let swap : ℕ → ℕ := fun n => if n = 0 then 2 else if n = 2 then 0 else n
  have injective : Function.Injective swap := by
    intro a b same
    simp only [swap] at same
    split_ifs at same <;> omega
  have atTwo := invariant.exact swap injective 2
  simp [swap] at atTwo

/-- **Compositionality without contexts is empty**: the identity on two points is compositional at
the operator that swaps them, with the function `swap` as its "context". -/
theorem compositional_without_contexts :
    CompositionalAt (L := tiny stuck never) (M := tiny stuck never) (k := 1) id
      (fun arguments => match arguments 0 with | .p => .q | .q => .p)
      (fun images => match images 0 with | .p => .q | .q => .p) :=
  fun _ => rfl

end Controls

#print axioms Homomorphic.compositionalAt
#print axioms compositionalAt_of_injective
#print axioms uniform_iff
#print axioms Controls.identity_meets_all
#print axioms Controls.only_complete_fails
#print axioms Controls.only_sound_fails
#print axioms Controls.only_divergence_fails
#print axioms Controls.only_success_fails
#print axioms Controls.coherence_has_content
#print axioms Controls.nameInvariant_has_content

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
