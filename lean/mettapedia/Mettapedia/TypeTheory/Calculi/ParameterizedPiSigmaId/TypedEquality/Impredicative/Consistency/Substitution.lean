import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Determinism

/-!
# Girard's substitution lemma for truth

A generic stands for an arbitrary meaning. Replacing it by a term with that
meaning changes no truth value: if `f` holds at a generic whose meaning is the
meaning of `a`, then `f a` has that truth value. This is what makes the
quantifier over all meanings, `all@A`, agree with its instances at terms.

A semantic substitution sends each generic either to a generic with the same
meaning or to a term with that meaning. Truth, meaning and application are
stable under it, provided terms read at the replaced carriers apply to
arguments as their meanings do. That proviso holds for every generic carrier,
by induction on the carrier: a term read at `B → C` is applied to an argument
read at `B` either through its reading at the argument's value (when `B` is a
data carrier) or by replacing the fresh generic of its reading by the
argument, which is the substitution lemma for the smaller carrier `B`; the
remaining arguments are then applied at `C`.

For the Kripke clause of a function on a data carrier, the source world and
the target world are placed side by side, so that an argument from the target
world can be supplied before the substitution is applied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

variable {Head : Type} {S : Reading Head}

/-! ## Semantic substitutions -/

/-- A substitution between worlds: each generic goes to a generic with the same
meaning or, when its carrier is allowed, to a term with that meaning. -/
def SemSub (S : Reading Head) (allowed : Carrier .gen → Prop) {n m : Nat} (ξ : World S n)
    (ξ' : World S m) (σ : Sub Head n m) : Prop :=
  ∀ i, (∃ j, σ i = .var j ∧ ξ' j = ξ i) ∨ (allowed (ξ i).1 ∧ Read S ξ' (σ i) (ξ i).1 (ξ i).2)

theorem SemSub.rename {allowed : Carrier .gen → Prop} {n m k : Nat} {ξ : World S n}
    {ξ' : World S m} {ξ'' : World S k} {σ : Sub Head n m} {ρ : Ren m k}
    (sem : SemSub S allowed ξ ξ' σ) (morph : Morph ξ' ξ'' ρ) :
    SemSub S allowed ξ ξ'' (fun i => Presentation.rename ρ (σ i)) := by
  intro i
  rcases sem i with ⟨j, hj, hξ⟩ | ⟨allow, read⟩
  · refine .inl ⟨ρ j, ?_, (morph j).trans hξ⟩
    show Presentation.rename ρ (σ i) = .var (ρ j)
    rw [hj]
    rfl
  · exact .inr ⟨allow, read.rename morph⟩

theorem SemSub.lift {allowed : Carrier .gen → Prop} {n m : Nat} {ξ : World S n}
    {ξ' : World S m} {σ : Sub Head n m} (sem : SemSub S allowed ξ ξ' σ) (g : Gen S) :
    SemSub S allowed (ξ.snoc g) (ξ'.snoc g) (liftSub σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .inl ⟨0, rfl, rfl⟩
  · rcases sem j with ⟨k, hk, hξ⟩ | ⟨allow, read⟩
    · exact .inl ⟨k.succ, by rw [liftSub_succ, hk]; rfl, hξ⟩
    · exact .inr ⟨allow, read.rename (Morph.wk ξ' g)⟩

/-- Replacing the newest generic by a term with its meaning. -/
theorem SemSub.zero {allowed : Carrier .gen → Prop} {n : Nat} {ξ : World S n} {g : Gen S}
    (allow : allowed g.1) {a : Tm Head n} (read : Read S ξ a g.1 g.2) :
    SemSub S allowed (ξ.snoc g) ξ (subst0 a) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .inr ⟨allow, read⟩
  · exact .inl ⟨j, rfl, rfl⟩

theorem SemSub.append {allowed : Carrier .gen → Prop} {n m : Nat} {ξ : World S n}
    {ξ' : World S m} {σ : Sub Head n m} (sem : SemSub S allowed ξ ξ' σ) :
    SemSub S allowed (ξ.append ξ') ξ' (appendSub σ) := by
  intro i
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · have e₁ : appendSub σ (Fin.castAdd m i') = σ i' := Fin.append_left _ _ _
    have e₂ : (ξ.append ξ') (Fin.castAdd m i') = ξ i' := Fin.append_left _ _ _
    rw [e₁, e₂]
    exact sem i'
  · refine .inl ⟨j, ?_, ?_⟩
    · simp only [appendSub, Fin.append_right]
    · simp only [World.append, Fin.append_right]

/-! ## Stability under semantic substitutions, given how allowed terms apply -/

/-- How terms read at a generic carrier apply to arguments. -/
def AppLawAt (S : Reading Head) (A : Carrier .gen) : Prop :=
  ∀ {n : Nat} {ξ : World S n} {a : Tm Head n} {v : A.V S} {args : List (Tm Head n)}
    {P : S.P}, Read S ξ a A v → Apply S ξ A v args P → Truth S ξ (appSpine a args) P

/-- How terms read at allowed carriers apply to arguments. -/
def AppLaw (S : Reading Head) (allowed : Carrier .gen → Prop) : Prop :=
  ∀ {A : Carrier .gen}, allowed A → AppLawAt S A

section Stable

variable (allowed : Carrier .gen → Prop)

mutual

theorem Truth.substAllowed (app : AppLaw S allowed) : ∀ {n m : Nat} {ξ : World S n}
    {ξ' : World S m} {σ : Sub Head n m} {t : Tm Head n} {P : S.P},
    SemSub S allowed ξ ξ' σ → Truth S ξ t P → Truth S ξ' (Presentation.subst σ t) P
  | _, _, _, _, σ, _, _, sem, .imp red p q =>
      .imp (red.subst σ) (Truth.substAllowed app sem p) (Truth.substAllowed app sem q)
  | _, _, _, _, σ, _, _, sem, .all carrier red f =>
      .all carrier (red.subst σ) (Read.substAllowed app sem f)
  | _, _, _, _, σ, _, _, sem, .eq carrier red x y =>
      .eq carrier (red.subst σ) (Read.substAllowed app sem x) (Read.substAllowed app sem y)
  | _, _, _, _, σ, _, _, sem, @Truth.generic _ _ _ _ _ i args _ red apply => by
      have red' := red.subst σ
      rw [subst_appSpine] at red'
      have apply' := Apply.substAllowed app sem apply
      rcases sem i with ⟨j, hj, hξ⟩ | ⟨allow, read⟩
      · rw [Presentation.subst, hj] at red'
        rw [← hξ] at apply'
        exact .generic red' apply'
      · exact Truth.expand red' (app allow read apply')
  | _, _, _, _, σ, _, _, _, .neutral red neutral =>
      .neutral (red.subst σ) (S.neutral_subst σ neutral)

theorem Read.substAllowed (app : AppLaw S allowed) : ∀ {n m : Nat} {ξ : World S n}
    {ξ' : World S m} {σ : Sub Head n m} {t : Tm Head n} {k : Kind} {A : Carrier k}
    {v : A.V S}, SemSub S allowed ξ ξ' σ → Read S ξ t A v →
      Read S ξ' (Presentation.subst σ t) A v
  | _, _, _, _, _, _, _, _, _, sem, .prop truth => .prop (Truth.substAllowed app sem truth)
  | _, _, _, _, _, _, _, _, _, _, @Read.rigid _ _ _ _ _ _T _u => .rigid
  | _, _, _, _, σ, _, _, _, _, _, .data related => by
      rw [← dataValue_subst related σ (DataEq.subst₂ _ related σ σ)]
      exact .data _
  | n, _, ξ, _, σ, t, _, _, _, sem, .dataArg read =>
      .dataArg fun {m'} {ξ''} {ρ'} morph' {s} related => by
        have sem' := (sem.rename morph').append (ξ' := ξ'')
        have h := Read.substAllowed app sem'
          (read (Morph.castAdd ξ ξ'') (related.rename₂ (Fin.natAdd n)))
        simp only [Presentation.subst, subst_appendSub_castAdd, subst_appendSub_natAdd] at h
        rw [dataValue_rename related (Fin.natAdd n), ← rename_subst] at h
        exact h
  | _, _, _, _, σ, t, _, _, _, sem, .genericArg read =>
      .genericArg fun v => by
        have h := Read.substAllowed app (sem.lift ⟨_, v⟩) (read v)
        simpa only [Presentation.subst, subst_liftSub_wk, liftSub_zero] using h

theorem Apply.substAllowed (app : AppLaw S allowed) : ∀ {n m : Nat} {ξ : World S n}
    {ξ' : World S m} {σ : Sub Head n m} {A : Carrier .gen} {v : A.V S}
    {args : List (Tm Head n)} {P : S.P},
    SemSub S allowed ξ ξ' σ → Apply S ξ A v args P →
      Apply S ξ' A v (args.map (Presentation.subst σ)) P
  | _, _, _, _, _, _, _, _, _, _, .done => .done
  | _, _, _, _, _, _, _, _, _, sem, .arg read rest =>
      .arg (Read.substAllowed app sem read) (Apply.substAllowed app sem rest)

end

end Stable

/-! ## How terms read at generic carriers apply -/

/-- A term read at a generic carrier, applied to arguments read at its argument
carriers, has the truth value of its meaning applied to their meanings. -/
theorem Read.appSpine : ∀ (A : Carrier .gen) {n : Nat} {ξ : World S n} {a : Tm Head n}
    {v : A.V S} {args : List (Tm Head n)} {P : S.P},
    Read S ξ a A v → Apply S ξ A v args P → Truth S ξ (appSpine a args) P
  | .prop, _, _, _, _, _, _, read, apply => by
      cases apply
      cases read with
      | prop truth => exact truth
  | .rigid _, _, _, _, _, _, _, _, apply => by cases apply
  | @Carrier.arr .data .gen A₁ B, _, _, a, _, _, _, read, apply => by
      cases apply with
      | arg readArg rest =>
          cases readArg with
          | data related =>
              cases read with
              | dataArg read' =>
                  have h := read' (Morph.id _) related
                  rw [rename_id] at h
                  have truth := Read.appSpine B h rest
                  exact truth
  | @Carrier.arr .gen .gen A₁ B, _, ξ, a, _, _, _, read, apply => by
      cases apply with
      | arg readArg rest =>
          cases read with
          | genericArg read' =>
              have atA₁ : AppLawAt S A₁ := fun read apply => Read.appSpine A₁ read apply
              have law : AppLaw S (· = A₁) := fun allow => by
                subst allow
                exact atA₁
              have h := Read.substAllowed (· = A₁) law
                (SemSub.zero (allowed := (· = A₁)) (g := ⟨A₁, _⟩) rfl readArg) (read' _)
              change Read S ξ (.app (inst0 _ (Presentation.rename wk a)) (inst0 _ (.var 0))) _ _
                at h
              rw [inst0_rename_wk, inst0_var_zero] at h
              have truth := Read.appSpine B h rest
              exact truth
termination_by A => A.size
decreasing_by
  · exact Carrier.size_cod _ _
  · exact Carrier.size_dom _ _
  · exact Carrier.size_cod _ _

/-! ## Replacing generics of every generic carrier -/

theorem Truth.subst {n m : Nat} {ξ : World S n} {ξ' : World S m} {σ : Sub Head n m}
    {t : Tm Head n} {P : S.P} (sem : SemSub S (fun _ => True) ξ ξ' σ)
    (truth : Truth S ξ t P) : Truth S ξ' (Presentation.subst σ t) P :=
  Truth.substAllowed (fun _ => True) (fun _ => fun read apply => Read.appSpine _ read apply) sem truth

theorem Read.subst {n m : Nat} {ξ : World S n} {ξ' : World S m} {σ : Sub Head n m}
    {t : Tm Head n} {k : Kind} {A : Carrier k} {v : A.V S}
    (sem : SemSub S (fun _ => True) ξ ξ' σ) (read : Read S ξ t A v) :
    Read S ξ' (Presentation.subst σ t) A v :=
  Read.substAllowed (fun _ => True) (fun _ => fun read apply => Read.appSpine _ read apply) sem read

/-- Girard's substitution lemma: a truth value read at the newest generic is the
truth value at any term with the generic's meaning. -/
theorem Truth.inst0 {n : Nat} {ξ : World S n} {A : Carrier .gen} {v : A.V S}
    {a : Tm Head n} (read : Read S ξ a A v) {t : Tm Head (n + 1)} {P : S.P}
    (truth : Truth S (ξ.snoc ⟨A, v⟩) t P) : Truth S ξ (inst0 a t) P :=
  Truth.subst (SemSub.zero (g := ⟨A, v⟩) trivial read) truth

theorem Read.inst0 {n : Nat} {ξ : World S n} {A : Carrier .gen} {v : A.V S}
    {a : Tm Head n} (read : Read S ξ a A v) {t : Tm Head (n + 1)} {k : Kind} {B : Carrier k}
    {w : B.V S} (readT : Read S (ξ.snoc ⟨A, v⟩) t B w) : Read S ξ (inst0 a t) B w :=
  Read.subst (SemSub.zero (g := ⟨A, v⟩) trivial read) readT

/-- A function read at a carrier applies to a term read at its domain. -/
theorem Read.app {n : Nat} {ξ : World S n} {f a : Tm Head n} {k : Kind} {A : Carrier k}
    {B : Carrier .gen} {φ : (Carrier.arr A B).V S} {v : A.V S}
    (readF : Read S ξ f (.arr A B) φ) (readA : Read S ξ a A v) :
    Read S ξ (.app f a) B (φ v) := by
  cases readF with
  | dataArg read =>
      cases readA with
      | data related =>
          have h := read (Morph.id _) related
          rwa [rename_id] at h
  | genericArg read =>
      have h := Read.inst0 readA (read v)
      change Read S ξ (.app (Presentation.inst0 _ (Presentation.rename wk f))
        (Presentation.inst0 _ (.var 0))) _ _ at h
      rwa [inst0_rename_wk, inst0_var_zero] at h

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
