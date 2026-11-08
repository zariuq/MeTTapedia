import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.EmptyRootConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Candidates

/-!
# Joinability under directed reduction for a root-free rule package

Directed reduction is β for functions and the projections of pairs under every
term former; universe-head equalities take no step. For a rule package without
declared root computation it is confluent, by the complete development of the
root-free presentation with its head equality removed. Two terms are joinable
when they have a common directed reduct.

Joinability is an equivalence relation, a congruence for every former, and
stable under renaming and substitution. A directed normal form joinable with a
term is a reduct of it, and the reducts of a type former, a reflexivity proof
or a variable-headed spine keep their outer shape. These are the facts an
executable comparison needs to follow a declarative derivation through its own
choice of normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExecutableJoin

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality

variable {Head : Type}

/-- The rule package with its universe-head equalities removed: its steps are the directed ones. -/
def directed (R : Rules Head) : Rules Head := { R with headEq := StrongNormalization.noHeadSteps }

variable {R : Rules Head}

/-- Finitely many directed steps. -/
abbrev Star {n : Nat} (t u : Tm Head n) : Prop := StrongNormalization.ReducesStar R t u

/-- Two terms are joinable when they have a common directed reduct. -/
def Join (R : Rules Head) {n : Nat} (t u : Tm Head n) : Prop :=
  ∃ common, Star (R := R) t common ∧ Star (R := R) u common

/-- A directed normal form: no directed step applies. -/
def Normal (R : Rules Head) {n : Nat} (t : Tm Head n) : Prop :=
  ∀ u, ¬ StrongNormalization.Reduces R t u

theorem star_eqvGen {n : Nat} {t u : Tm Head n} (steps : Star (R := R) t u) :
    Relation.EqvGen (StepCore R.computation StrongNormalization.noHeadSteps) t u := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

variable (empty : R.computation = RootComputation.empty)

include empty in
/-- **Confluence** of directed reduction for a root-free rule package. -/
theorem confluent {n : Nat} {a b c : Tm Head n} (first : Star (R := R) a b) (second : Star (R := R) a c) :
    ∃ d, Star (R := R) b d ∧ Star (R := R) c d :=
  EmptyRootConversion.churchRosser (directed R) empty ⟨fun _ _ impossible => False.elim impossible⟩
    (.trans _ _ _ (.symm _ _ (star_eqvGen first)) (star_eqvGen second))

include empty in
theorem no_root {n : Nat} {t u : Tm Head n} : ¬ R.computation.step t u := by
  rw [empty]
  exact not_false

/-! ## Joinability is an equivalence -/

theorem Join.refl {n : Nat} (t : Tm Head n) : Join R t t := ⟨t, .refl, .refl⟩

theorem Join.symm {n : Nat} {t u : Tm Head n} (joined : Join R t u) : Join R u t := by
  obtain ⟨c, first, second⟩ := joined
  exact ⟨c, second, first⟩

theorem Join.of_star {n : Nat} {t u : Tm Head n} (steps : Star (R := R) t u) : Join R t u :=
  ⟨u, steps, .refl⟩

include empty in
theorem Join.trans {n : Nat} {t u v : Tm Head n} (first : Join R t u) (second : Join R u v) :
    Join R t v := by
  obtain ⟨c, tc, uc⟩ := first
  obtain ⟨d, ud, vd⟩ := second
  obtain ⟨e, ce, de⟩ := confluent empty uc ud
  exact ⟨e, tc.trans ce, vd.trans de⟩

include empty in
theorem Join.star_left {n : Nat} {t t' u : Tm Head n} (steps : Star (R := R) t t') (joined : Join R t u) :
    Join R t' u :=
  Join.trans empty (Join.of_star steps).symm joined

include empty in
theorem Join.star_right {n : Nat} {t u u' : Tm Head n} (joined : Join R t u) (steps : Star (R := R) u u') :
    Join R t u' :=
  Join.trans empty joined (Join.of_star steps)

/-- A normal form reduces only to itself. -/
theorem Normal.star_eq {n : Nat} {t u : Tm Head n} (normal : Normal R t) (steps : Star (R := R) t u) :
    u = t := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ => exact False.elim (normal _ step)

/-- A normal form joinable with a term is one of its reducts. -/
theorem Normal.star_of_join {n : Nat} {t u : Tm Head n} (normal : Normal R u) (joined : Join R t u) :
    Star (R := R) t u := by
  obtain ⟨c, tc, uc⟩ := joined
  rw [normal.star_eq uc] at tc
  exact tc

/-! ## Congruence -/

theorem star_map {n m : Nat} (f : Tm Head n → Tm Head m)
    (preserves : ∀ {a b : Tm Head n}, StrongNormalization.Reduces R a b → StrongNormalization.Reduces R (f a) (f b))
    {a b : Tm Head n} (steps : Star (R := R) a b) : Star (R := R) (f a) (f b) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (preserves step)

theorem star_pi {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (domain : Star (R := R) A A') (codomain : Star (R := R) B B') :
    Star (R := R) (.pi A B) (.pi A' B') :=
  (star_map (fun A => Tm.pi A B) (fun step => .congPiDom step) domain).trans
    (star_map (fun B => Tm.pi A' B) (fun step => .congPiCod step) codomain)

theorem star_sigma {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (domain : Star (R := R) A A') (codomain : Star (R := R) B B') :
    Star (R := R) (.sigma A B) (.sigma A' B') :=
  (star_map (fun A => Tm.sigma A B) (fun step => .congSigmaDom step) domain).trans
    (star_map (fun B => Tm.sigma A' B) (fun step => .congSigmaCod step) codomain)

theorem star_id {n : Nat} {A A' a a' b b' : Tm Head n}
    (carrier : Star (R := R) A A') (left : Star (R := R) a a') (right : Star (R := R) b b') :
    Star (R := R) (.id A a b) (.id A' a' b') :=
  ((star_map (fun A => Tm.id A a b) (fun step => .congIdTy step) carrier).trans
    (star_map (fun a => Tm.id A' a b) (fun step => .congIdLeft step) left)).trans
    (star_map (fun b => Tm.id A' a' b) (fun step => .congIdRight step) right)

theorem star_app {n : Nat} {f f' a a' : Tm Head n}
    (function : Star (R := R) f f') (argument : Star (R := R) a a') :
    Star (R := R) (.app f a) (.app f' a') :=
  (star_map (fun f => Tm.app f a) (fun step => .congAppFun step) function).trans
    (star_map (fun a => Tm.app f' a) (fun step => .congAppArg step) argument)

theorem star_fst {n : Nat} {p p' : Tm Head n} (pair : Star (R := R) p p') :
    Star (R := R) (.fst p) (.fst p') :=
  star_map Tm.fst (fun step => .congFst step) pair

theorem star_snd {n : Nat} {p p' : Tm Head n} (pair : Star (R := R) p p') :
    Star (R := R) (.snd p) (.snd p') :=
  star_map Tm.snd (fun step => .congSnd step) pair

theorem star_refl {n : Nat} {a a' : Tm Head n} (subject : Star (R := R) a a') :
    Star (R := R) (.refl a) (.refl a') :=
  star_map Tm.refl (fun step => .congRefl step) subject

theorem star_rename {n m : Nat} (ρ : Ren n m) {a b : Tm Head n} (steps : Star (R := R) a b) :
    Star (R := R) (Presentation.rename ρ a) (Presentation.rename ρ b) :=
  star_map (Presentation.rename ρ) (fun step => StepCore.renameTerms step ρ) steps

theorem star_subst {n m : Nat} (σ : Sub Head n m) {a b : Tm Head n} (steps : Star (R := R) a b) :
    Star (R := R) (subst σ a) (subst σ b) :=
  star_map (subst σ) (fun step => StepCore.substitute step σ) steps

theorem star_substitute {n m : Nat} {σ τ : Sub Head n m}
    (pointwise : ∀ index, Star (R := R) (σ index) (τ index)) (term : Tm Head n) :
    Star (R := R) (subst σ term) (subst τ term) :=
  AlgebraicParallel.stepStar_substitute (rules := directed R) pointwise term

theorem star_inst0 {n : Nat} {a a' : Tm Head n} {B B' : Tm Head (n + 1)}
    (argument : Star (R := R) a a') (body : Star (R := R) B B') :
    Star (R := R) (inst0 a B) (inst0 a' B') := by
  refine (star_subst _ body).trans ?_
  refine star_substitute (fun index => ?_) B'
  refine Fin.cases ?_ (fun _ => ?_) index
  · exact argument
  · exact .refl

theorem Join.pi {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (domain : Join R A A') (codomain : Join R B B') : Join R (.pi A B) (.pi A' B') := by
  obtain ⟨c, l, r⟩ := domain
  obtain ⟨d, l', r'⟩ := codomain
  exact ⟨.pi c d, star_pi l l', star_pi r r'⟩

theorem Join.sigma {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (domain : Join R A A') (codomain : Join R B B') : Join R (.sigma A B) (.sigma A' B') := by
  obtain ⟨c, l, r⟩ := domain
  obtain ⟨d, l', r'⟩ := codomain
  exact ⟨.sigma c d, star_sigma l l', star_sigma r r'⟩

theorem Join.app {n : Nat} {f f' a a' : Tm Head n} (function : Join R f f') (argument : Join R a a') :
    Join R (.app f a) (.app f' a') := by
  obtain ⟨c, l, r⟩ := function
  obtain ⟨d, l', r'⟩ := argument
  exact ⟨.app c d, star_app l l', star_app r r'⟩

theorem Join.fst {n : Nat} {p p' : Tm Head n} (pair : Join R p p') : Join R (.fst p) (.fst p') := by
  obtain ⟨c, l, r⟩ := pair
  exact ⟨.fst c, star_fst l, star_fst r⟩

theorem Join.snd {n : Nat} {p p' : Tm Head n} (pair : Join R p p') : Join R (.snd p) (.snd p') := by
  obtain ⟨c, l, r⟩ := pair
  exact ⟨.snd c, star_snd l, star_snd r⟩

theorem Join.rename {n m : Nat} (ρ : Ren n m) {a b : Tm Head n} (joined : Join R a b) :
    Join R (Presentation.rename ρ a) (Presentation.rename ρ b) := by
  obtain ⟨c, l, r⟩ := joined
  exact ⟨Presentation.rename ρ c, star_rename ρ l, star_rename ρ r⟩

theorem Join.inst0 {n : Nat} {a a' : Tm Head n} {B B' : Tm Head (n + 1)}
    (argument : Join R a a') (body : Join R B B') : Join R (inst0 a B) (inst0 a' B') := by
  obtain ⟨c, l, r⟩ := argument
  obtain ⟨d, l', r'⟩ := body
  exact ⟨Presentation.inst0 c d, star_inst0 l l', star_inst0 r r'⟩

/-! ## Reducts keep their outer shape -/

section Shapes

include empty

theorem star_pi_inv {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {X : Tm Head n}
    (steps : Star (R := R) (.pi A B) X) :
    ∃ A' B', X = .pi A' B' ∧ Star (R := R) A A' ∧ Star (R := R) B B' := by
  induction steps with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨A', B', rfl, domain, codomain⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congPiDom inner => exact ⟨_, B', rfl, domain.tail inner, codomain⟩
      | congPiCod inner => exact ⟨A', _, rfl, domain, codomain.tail inner⟩

theorem star_sigma_inv {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {X : Tm Head n}
    (steps : Star (R := R) (.sigma A B) X) :
    ∃ A' B', X = .sigma A' B' ∧ Star (R := R) A A' ∧ Star (R := R) B B' := by
  induction steps with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨A', B', rfl, domain, codomain⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congSigmaDom inner => exact ⟨_, B', rfl, domain.tail inner, codomain⟩
      | congSigmaCod inner => exact ⟨A', _, rfl, domain, codomain.tail inner⟩

theorem star_id_inv {n : Nat} {A a b X : Tm Head n} (steps : Star (R := R) (.id A a b) X) :
    ∃ A' a' b', X = .id A' a' b' ∧ Star (R := R) A A' ∧ Star (R := R) a a' ∧ Star (R := R) b b' := by
  induction steps with
  | refl => exact ⟨A, a, b, rfl, .refl, .refl, .refl⟩
  | tail _ step ih =>
      obtain ⟨A', a', b', rfl, carrier, left, right⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congIdTy inner => exact ⟨_, a', b', rfl, carrier.tail inner, left, right⟩
      | congIdLeft inner => exact ⟨A', _, b', rfl, carrier, left.tail inner, right⟩
      | congIdRight inner => exact ⟨A', a', _, rfl, carrier, left, right.tail inner⟩

theorem star_refl_inv {n : Nat} {a X : Tm Head n} (steps : Star (R := R) (.refl a) X) :
    ∃ a', X = .refl a' ∧ Star (R := R) a a' := by
  induction steps with
  | refl => exact ⟨a, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨a', rfl, subject⟩ := ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
      | congRefl inner => exact ⟨_, rfl, subject.tail inner⟩

theorem star_head_inv {n : Nat} {h : Head} {X : Tm Head n} (steps : Star (R := R) (.head h) X) :
    X = .head h := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      cases step with
      | head impossible => exact False.elim impossible
      | root impossible => exact False.elim (no_root empty impossible)

theorem star_var_inv {n : Nat} {i : Fin n} {X : Tm Head n} (steps : Star (R := R) (.var i) X) :
    X = .var i := by
  induction steps with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)

end Shapes

/-! ## Elimination spines -/

/-- A spine of eliminations with a variable or a constant at its head. -/
inductive Elim : {n : Nat} → Tm Head n → Prop where
  | var {n : Nat} (i : Fin n) : Elim (.var i)
  | const {n : Nat} (name : DeclName) : Elim (.const name : Tm Head n)
  | app {n : Nat} {f a : Tm Head n} : Elim f → Elim (.app f a)
  | fst {n : Nat} {p : Tm Head n} : Elim p → Elim (.fst p)
  | snd {n : Nat} {p : Tm Head n} : Elim p → Elim (.snd p)

theorem Elim.not_lam {n : Nat} {body : Tm Head (n + 1)} : ¬ Elim (Tm.lam body) := by
  intro rigid
  cases rigid

theorem Elim.not_pair {n : Nat} {a b : Tm Head n} : ¬ Elim (Tm.pair a b) := by
  intro rigid
  cases rigid

include empty in
theorem Elim.step {n : Nat} {t u : Tm Head n} (rigid : Elim t) (step : StrongNormalization.Reduces R t u) :
    Elim u := by
  induction rigid generalizing u with
  | var i =>
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | const name =>
      cases step with
      | root impossible => exact False.elim (no_root empty impossible)
  | app function ih =>
      cases step with
      | betaPi => exact False.elim (Elim.not_lam function)
      | root impossible => exact False.elim (no_root empty impossible)
      | congAppFun inner => exact .app (ih inner)
      | congAppArg _ => exact .app function
  | fst pair ih =>
      cases step with
      | betaSigmaFst => exact False.elim (Elim.not_pair pair)
      | root impossible => exact False.elim (no_root empty impossible)
      | congFst inner => exact .fst (ih inner)
  | snd pair ih =>
      cases step with
      | betaSigmaSnd => exact False.elim (Elim.not_pair pair)
      | root impossible => exact False.elim (no_root empty impossible)
      | congSnd inner => exact .snd (ih inner)

section Spines

include empty

theorem star_app_inv {n : Nat} {f a X : Tm Head n} (rigid : Elim f) (steps : Star (R := R) (.app f a) X) :
    ∃ f' a', X = .app f' a' ∧ Star (R := R) f f' ∧ Star (R := R) a a' ∧ Elim f' := by
  induction steps with
  | refl => exact ⟨f, a, rfl, .refl, .refl, rigid⟩
  | tail _ step ih =>
      obtain ⟨f', a', rfl, function, argument, elim'⟩ := ih
      cases step with
      | betaPi => exact False.elim (Elim.not_lam elim')
      | root impossible => exact False.elim (no_root empty impossible)
      | congAppFun inner => exact ⟨_, a', rfl, function.tail inner, argument, elim'.step empty inner⟩
      | congAppArg inner => exact ⟨f', _, rfl, function, argument.tail inner, elim'⟩

theorem star_fst_inv {n : Nat} {p X : Tm Head n} (rigid : Elim p) (steps : Star (R := R) (.fst p) X) :
    ∃ p', X = .fst p' ∧ Star (R := R) p p' ∧ Elim p' := by
  induction steps with
  | refl => exact ⟨p, rfl, .refl, rigid⟩
  | tail _ step ih =>
      obtain ⟨p', rfl, pair, elim'⟩ := ih
      cases step with
      | betaSigmaFst => exact False.elim (Elim.not_pair elim')
      | root impossible => exact False.elim (no_root empty impossible)
      | congFst inner => exact ⟨_, rfl, pair.tail inner, elim'.step empty inner⟩

theorem star_snd_inv {n : Nat} {p X : Tm Head n} (rigid : Elim p) (steps : Star (R := R) (.snd p) X) :
    ∃ p', X = .snd p' ∧ Star (R := R) p p' ∧ Elim p' := by
  induction steps with
  | refl => exact ⟨p, rfl, .refl, rigid⟩
  | tail _ step ih =>
      obtain ⟨p', rfl, pair, elim'⟩ := ih
      cases step with
      | betaSigmaSnd => exact False.elim (Elim.not_pair elim')
      | root impossible => exact False.elim (no_root empty impossible)
      | congSnd inner => exact ⟨_, rfl, pair.tail inner, elim'.step empty inner⟩

theorem Elim.star {n : Nat} {t u : Tm Head n} (rigid : Elim t) (steps : Star (R := R) t u) : Elim u := by
  induction steps with
  | refl => exact rigid
  | tail _ step ih => exact ih.step empty step

end Spines

/-! ## Normal forms of joinable shapes -/

section NormalShapes

include empty

theorem Join.pi_normal {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {N : Tm Head n}
    (joined : Join R (.pi A B) N) (normal : Normal R N) :
    ∃ A' B', N = .pi A' B' ∧ Star (R := R) A A' ∧ Star (R := R) B B' :=
  star_pi_inv empty (normal.star_of_join joined)

theorem Join.sigma_normal {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {N : Tm Head n}
    (joined : Join R (.sigma A B) N) (normal : Normal R N) :
    ∃ A' B', N = .sigma A' B' ∧ Star (R := R) A A' ∧ Star (R := R) B B' :=
  star_sigma_inv empty (normal.star_of_join joined)

theorem Join.id_normal {n : Nat} {A a b N : Tm Head n} (joined : Join R (.id A a b) N) (normal : Normal R N) :
    ∃ A' a' b', N = .id A' a' b' ∧ Star (R := R) A A' ∧ Star (R := R) a a' ∧ Star (R := R) b b' :=
  star_id_inv empty (normal.star_of_join joined)

theorem Join.refl_normal {n : Nat} {a N : Tm Head n} (joined : Join R (.refl a) N) (normal : Normal R N) :
    ∃ a', N = .refl a' ∧ Star (R := R) a a' :=
  star_refl_inv empty (normal.star_of_join joined)

theorem Join.head_normal {n : Nat} {h : Head} {N : Tm Head n} (joined : Join R (.head h) N)
    (normal : Normal R N) : N = .head h :=
  star_head_inv empty (normal.star_of_join joined)

theorem Join.pi_inj {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (joined : Join R (.pi A B) (.pi A' B')) : Join R A A' ∧ Join R B B' := by
  obtain ⟨c, l, r⟩ := joined
  obtain ⟨A₁, B₁, rfl, lA, lB⟩ := star_pi_inv empty l
  obtain ⟨A₂, B₂, same, rA, rB⟩ := star_pi_inv empty r
  cases same
  exact ⟨⟨_, lA, rA⟩, ⟨_, lB, rB⟩⟩

theorem Join.sigma_inj {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (joined : Join R (.sigma A B) (.sigma A' B')) : Join R A A' ∧ Join R B B' := by
  obtain ⟨c, l, r⟩ := joined
  obtain ⟨A₁, B₁, rfl, lA, lB⟩ := star_sigma_inv empty l
  obtain ⟨A₂, B₂, same, rA, rB⟩ := star_sigma_inv empty r
  cases same
  exact ⟨⟨_, lA, rA⟩, ⟨_, lB, rB⟩⟩

end NormalShapes

theorem Normal.app_function {n : Nat} {f a : Tm Head n} (normal : Normal R (.app f a)) : Normal R f :=
  fun _ step => normal _ (.congAppFun step)

theorem Normal.app_argument {n : Nat} {f a : Tm Head n} (normal : Normal R (.app f a)) : Normal R a :=
  fun _ step => normal _ (.congAppArg step)

theorem Normal.fst_pair {n : Nat} {p : Tm Head n} (normal : Normal R (.fst p)) : Normal R p :=
  fun _ step => normal _ (.congFst step)

theorem Normal.snd_pair {n : Nat} {p : Tm Head n} (normal : Normal R (.snd p)) : Normal R p :=
  fun _ step => normal _ (.congSnd step)

theorem Normal.refl_subject {n : Nat} {a : Tm Head n} (normal : Normal R (.refl a)) : Normal R a :=
  fun _ step => normal _ (.congRefl step)

end ContextualDependentExecutableJoin
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
