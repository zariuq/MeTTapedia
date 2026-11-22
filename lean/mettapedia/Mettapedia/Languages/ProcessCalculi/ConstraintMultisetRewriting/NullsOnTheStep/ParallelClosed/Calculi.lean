import Mettapedia.GSLT.Coordination.ConsensusNumbers.WholeSpaceConditions

/-!
# What putting a term beside another keeps, and what an absence guard does not

## The algebra

A calculus with a parallel composition `∥` has a reduction `⟶` and a success observation. Three
things can be invariant under putting a term beside another:

* the reduction, when it is **closed beside** (`ClosedBeside`): `t ⟶ t'` gives `t ∥ u ⟶ t' ∥ u`.
  This is what a parallel context rule says;
* the success observation, when it **persists beside**: `t` shows success, so does `t ∥ u`;
* hence **reachable success** (`ParallelCalculus.Succeeds`, a weak barb): a run of `t` is a run of
  `t ∥ u` (`Persistent.succeeds_par`). Reachable success is then monotone for the preorder
  "is a parallel component of".

An absence guard reads the whole store. On the step its claim holds on a union exactly when it
holds on each part (`Composition.absent_union_iff`), so it is antitone in the store, and an
absence-guarded firing admitted at `C` stays admitted beside `D` exactly when `D` holds no
occurrence of the pattern (`Composition.guarded_union_iff`): invariance holds only on that grade.
Reachable success of a program with an absence guard is therefore not monotone: a neighbour can
switch it off (`ParallelCalculus.Switchable`).

## The theorems

* **Relation level** (`not_iff_of_switchedOff`): no relation that a parallel component switches off
  is a relation closed beside.
* **Encoding level** (`no_uniformTranslation`): no **uniform translation** (`UniformTranslation`:
  homomorphic on parallel composition up to the target's static equivalence on every composable
  pair, and preserving and reflecting reachable success) goes from a switchable calculus into a
  persistent one (`ParallelCalculus.Persistent`: reduction closed beside, success persists beside,
  reachable success read up to the static equivalence).
* One composable pair is enough (`no_translation_at_pair`): the image of the composite need only be,
  up to the static equivalence, the image of the part beside some term.
  `ConsensusNumbers.no_parallel_encoding` is the same argument with equality as the static
  equivalence and any source term in place of the composite; its two target hypotheses are
  persistence (`persistent_of_eq_iff`).

The static equivalence matters: on raw syntax a composition such as a two-element collection is
neither associative, commutative nor unital, so no map from a calculus whose composition has a unit
is homomorphic into it on the nose. Homomorphism is asked up to the target's structural congruence
(the equations of a presentation, or equality on a quotient of processes).

The criterion is named in every statement: a translation that is not homomorphic on parallel
composition, for instance one that maps a whole store to a single term, is outside the theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed

open Mettapedia.GSLT.Coordination.ConsensusNumbers (WeakBarb reflTransGen_par)

universe u v

/-! ## Relations closed beside -/

section Relations

variable {T : Type*}

/-- **Closed beside**: a step of `t` is a step of `t` beside any `u`. -/
def ClosedBeside (step : T → T → Prop) (par : T → T → T) : Prop :=
  ∀ t t' u, step t t' → step (par t u) (par t' u)

/-- A relation that a parallel component **switches off**: it relates `first` to `second`, and no
longer relates them once `extra` is put beside both. -/
def SwitchedOffBeside (R : T → T → Prop) (par : T → T → T) : Prop :=
  ∃ first second extra, R first second ∧ ¬ R (par first extra) (par second extra)

/-- **No relation that a parallel component switches off is a relation closed beside.** -/
theorem not_iff_of_switchedOff {step R : T → T → Prop} {par : T → T → T}
    (closed : ClosedBeside step par) (switched : SwitchedOffBeside R par) :
    ¬ ∀ x y, step x y ↔ R x y := by
  intro same
  obtain ⟨first, second, extra, holds, off⟩ := switched
  exact off ((same _ _).mp (closed _ _ extra ((same _ _).mpr holds)))

/-- A relation switched off beside is not closed beside. -/
theorem not_closedBeside_of_switchedOff {R : T → T → Prop} {par : T → T → T}
    (switched : SwitchedOffBeside R par) : ¬ ClosedBeside R par := fun closed =>
  not_iff_of_switchedOff closed switched fun _ _ => Iff.rfl

/-- **Controls.** The empty relation is closed beside every composition, and on the natural numbers
under addition, "`n` is zero and `m` is one" is switched off beside one: it is not closed. -/
theorem closedBeside_controls :
    ClosedBeside (fun _ _ : ℕ => False) (· + ·) ∧
      SwitchedOffBeside (fun n m : ℕ => n = 0 ∧ m = 1) (· + ·) :=
  ⟨fun _ _ _ never => never, ⟨0, 1, 1, ⟨rfl, rfl⟩, by decide⟩⟩

end Relations

/-! ## Calculi with a parallel composition and a success observation -/

/-- **A calculus with a parallel composition and a success observation**: terms, one-step
reduction, a composition (meaningful on the composable pairs), a success observation, and a static
equivalence (a structural congruence, the equations of a presentation, or equality). -/
structure ParallelCalculus where
  Term : Type u
  step : Term → Term → Prop
  par : Term → Term → Term
  composable : Term → Term → Prop
  success : Term → Prop
  same : Term → Term → Prop

namespace ParallelCalculus

variable (L : ParallelCalculus.{u})

/-- **Reachable success**: some run reaches a term showing success. -/
def Succeeds (t : L.Term) : Prop := WeakBarb L.step L.success t

/-- Success now is reachable success. -/
theorem succeeds_of_success {t : L.Term} (shows : L.success t) : L.Succeeds t :=
  ⟨t, .refl, shows⟩

/-- Reachable success is closed under steps backwards. -/
theorem succeeds_of_step {t t' : L.Term} (step : L.step t t') (later : L.Succeeds t') :
    L.Succeeds t := by
  obtain ⟨t'', run, shows⟩ := later
  exact ⟨t'', Relation.ReflTransGen.head step run, shows⟩

/-- **Persistent**: reduction is closed beside, success persists beside, and reachable success is
read up to the static equivalence. -/
structure Persistent : Prop where
  closed : ClosedBeside L.step L.par
  persists : ∀ t u, L.success t → L.success (L.par t u)
  respects : ∀ t t', L.same t t' → L.Succeeds t' → L.Succeeds t

/-- **Switchable**: a composable neighbour switches reachable success off. -/
def Switchable : Prop :=
  ∃ s s', L.composable s s' ∧ L.Succeeds s ∧ ¬ L.Succeeds (L.par s s')

variable {L}

/-- **Reachable success persists beside**, in a persistent calculus. -/
theorem Persistent.succeeds_par (persistent : L.Persistent) {t : L.Term} (u : L.Term)
    (succeeds : L.Succeeds t) : L.Succeeds (L.par t u) := by
  obtain ⟨t', run, shows⟩ := succeeds
  exact ⟨L.par t' u, reflTransGen_par persistent.closed u run, persistent.persists _ _ shows⟩

/-- **A persistent calculus is not switchable**: reachable success of a part is reachable success of
every composite. -/
theorem Persistent.not_switchable (persistent : L.Persistent) : ¬ L.Switchable := by
  rintro ⟨s, s', _, succeeds, blocked⟩
  exact blocked (persistent.succeeds_par s' succeeds)

/-- With equality as the static equivalence, reachable success is read up to it. -/
theorem respects_of_eq (equality : ∀ t t', L.same t t' → t = t') :
    ∀ t t', L.same t t' → L.Succeeds t' → L.Succeeds t := by
  intro t t' same succeeds
  rw [equality t t' same]
  exact succeeds

end ParallelCalculus

/-! ## The criterion and the separation -/

/-- **A uniform translation**: homomorphic on parallel composition, up to the target's static
equivalence, on every composable pair; preserving and reflecting reachable success. -/
structure UniformTranslation (L : ParallelCalculus.{u}) (M : ParallelCalculus.{v}) where
  map : L.Term → M.Term
  homomorphic : ∀ s s', L.composable s s' → M.same (map (L.par s s')) (M.par (map s) (map s'))
  preserves : ∀ s, L.Succeeds s → M.Succeeds (map s)
  reflects : ∀ s, M.Succeeds (map s) → L.Succeeds s

/-- **One pair is enough.** Let the target be persistent, let `s` succeed while `s` beside `s'` does
not, and let the image of the composite be, up to the target's static equivalence, the image of `s`
beside some term. Then no translation preserves reachable success at `s` and reflects it at the
composite. -/
theorem no_translation_at_pair {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (persistent : M.Persistent) {s s' : L.Term} (succeeds : L.Succeeds s)
    (blocked : ¬ L.Succeeds (L.par s s')) (map : L.Term → M.Term)
    (beside : ∃ w, M.same (map (L.par s s')) (M.par (map s) w))
    (preserves : L.Succeeds s → M.Succeeds (map s))
    (reflects : M.Succeeds (map (L.par s s')) → L.Succeeds (L.par s s')) : False := by
  obtain ⟨w, same⟩ := beside
  exact blocked (reflects (persistent.respects _ _ same
    (persistent.succeeds_par w (preserves succeeds))))

/-- **The separation for encodings homomorphic on parallel composition.** No uniform translation
goes from a switchable calculus into a persistent one. -/
theorem no_uniformTranslation {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (switchable : L.Switchable) (persistent : M.Persistent) (τ : UniformTranslation L M) :
    False := by
  obtain ⟨s, s', composable, succeeds, blocked⟩ := switchable
  exact no_translation_at_pair persistent succeeds blocked τ.map
    ⟨τ.map s', τ.homomorphic s s' composable⟩ (τ.preserves s) (τ.reflects _)

/-- The separation, as emptiness of the type of uniform translations. -/
theorem isEmpty_uniformTranslation {L : ParallelCalculus.{u}} {M : ParallelCalculus.{v}}
    (switchable : L.Switchable) (persistent : M.Persistent) :
    IsEmpty (UniformTranslation L M) :=
  ⟨no_uniformTranslation switchable persistent⟩

/-- **The target hypotheses of the existing weak-barb theorem are persistence.** A calculus given by
a reduction, a composition and a barb, with equality as the static equivalence, is persistent
exactly when it satisfies the two target hypotheses of `ConsensusNumbers.no_parallel_encoding`. -/
theorem persistent_of_eq_iff {T : Type u} (step : T → T → Prop) (par : T → T → T)
    (barb : T → Prop) (composable : T → T → Prop) :
    (⟨T, step, par, composable, barb, Eq⟩ : ParallelCalculus.{u}).Persistent ↔
      (∀ t t' u, step t t' → step (par t u) (par t' u)) ∧ (∀ t u, barb t → barb (par t u)) := by
  constructor
  · intro persistent
    exact ⟨persistent.closed, persistent.persists⟩
  · rintro ⟨closed, persists⟩
    exact ⟨closed, persists, ParallelCalculus.respects_of_eq fun _ _ same => same⟩

#print axioms not_iff_of_switchedOff
#print axioms not_closedBeside_of_switchedOff
#print axioms closedBeside_controls
#print axioms ParallelCalculus.Persistent.succeeds_par
#print axioms ParallelCalculus.Persistent.not_switchable
#print axioms no_translation_at_pair
#print axioms no_uniformTranslation
#print axioms isEmpty_uniformTranslation
#print axioms persistent_of_eq_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
