import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Model
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Strong
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Curry
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Inert
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Eliminators

/-!
# The accessibility package over the tower, with a model

A concrete instance of every hypothesis of the consistency theorem for the
accessibility package (`AccessibleRecursion.consistent`):

* the base package is the cumulative tower with the identity eliminator `J` at
  `U₀`, computing at reflexivity;
* the codes are `prop`, `holds`, implication, the quantifier over codes and the
  quantifier over predicates on codes;
* the carrier of the accessibility code is `prop`, and the motives live in `U₀`;
* the model reads the codes by truth values; its reduction casts `J` at every
  path and unfolds the recursor at every argument.

So the base package with codes is sound for the model (`sound_base`), the
model computes the recursor (`computes`), and the package's laws hold
(`laws`). Hence the extended package, with its inert recursor and its
propositional unfolding, proves no closed term of `holds Falsum`
(`consistent_falsum`), where `Falsum := ∀p : prop. p`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
namespace PropInstance

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency
open Presentation.TypedEquality.Normalization
open TelescopeAbstraction (closeType applyClosed)
open Mettapedia.TypeTheory.UniverseLevel

/-! ## Names -/

def propN : DeclName := `AccessibleRecursion.PropInstance.prop
def holdsN : DeclName := `AccessibleRecursion.PropInstance.holds
def impN : DeclName := `AccessibleRecursion.PropInstance.imp
def allPropN : DeclName := `AccessibleRecursion.PropInstance.allProp
def allPredN : DeclName := `AccessibleRecursion.PropInstance.allPred
def recN : DeclName := `AccessibleRecursion.PropInstance.rec
def unfoldN : DeclName := `AccessibleRecursion.PropInstance.unfold
def jN : DeclName := `AccessibleRecursion.PropInstance.J
def numN : DeclName := `AccessibleRecursion.PropInstance.num
def zeroN : DeclName := `AccessibleRecursion.PropInstance.zero
def sucN : DeclName := `AccessibleRecursion.PropInstance.suc

/-- The bottom universe `U₀`. -/
abbrev U0 : Tower.Head := .sort Tower.zero

/-- The universe `U₁`. -/
abbrev U1 : Tower.Head := .sort (.succ Tower.zero)

/-! ## The package -/

/-- The codes: `prop`, `holds`, implication, and the quantifiers over codes and
over predicates on codes. -/
def codes : Codes Tower.Head where
  proofs := U0
  prop := propN
  holds := holdsN
  imp := impN
  quantifiers := fun a =>
    if a = allPropN then some (.const propN)
    else if a = allPredN then some (.pi (.const propN) (.const propN))
    else none
  equations := fun _ => none
  identity := false

/-- The base package: the tower with the identity eliminator at `U₀`. -/
abbrev base : Rules Tower.Head := TowerEliminatorModel.rules jN U0 U0

/-- The accessibility package over `prop`, with motives in `U₀`. -/
def signature : Signature Tower.Head where
  codes := codes
  point := allPropN
  predicate := allPredN
  base := base
  carrier := .const propN
  motive := U0
  recursor := recN
  unfold := unfoldN

/-! ## The model -/

/-- The cast: `J A x P d y e ⟶ d`, at every path. -/
def castComputation : RootComputation Tower.Head where
  step := fun {n} l r => ∃ a₀ a₁ a₂ a₃ a₄ a₅ : Tm Tower.Head n,
    l = appSpine (.const jN) [a₀, a₁, a₂, a₃, a₄, a₅] ∧ r = a₃
  rename := by
    intro n m ρ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁ e₂
    exact ⟨_, _, _, _, _, _, by rw [rename_appSpine]; rfl, rfl⟩
  substitute := by
    intro n m σ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁ e₂
    exact ⟨_, _, _, _, _, _, by rw [subst_appSpine]; rfl, rfl⟩

/-- The recursor's definitional unfolding. -/
abbrev recComputation : RootComputation Tower.Head :=
  definitionComputation recN signature.recTelescope
    (signature.unfolding (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))

/-- The model's rules: the tower's universes, the cast and the unfolding. -/
def modelRules : Rules Tower.Head :=
  { Tower.rules with computation := RootComputation.union castComputation recComputation }

/-- The model's roles: the code formers and the numerals are constructors, `J`
computes at six arguments and the recursor at five, and every other name is
rigid. -/
def modelRoles : Roles Tower.Head := fun name =>
  if name = impN then .constructor 2
  else if name = allPropN then .constructor 1
  else if name = allPredN then .constructor 1
  else if name = numN then .inductive [(zeroN, []), (sucN, [.recursive])]
  else if name = zeroN then .constructor 0
  else if name = sucN then .constructor 1
  else if name = jN then .computes 6 .leaf
  else if name = recN then .computes 5 .leaf
  else .rigid

/-- The quantifiers range over codes and over predicates on codes. -/
def modelAllCarrier (name : DeclName) : Option (Σ k, Carrier k) :=
  if name = allPropN then some ⟨.gen, .prop⟩
  else if name = allPredN then some ⟨.gen, .arr .prop .prop⟩
  else none

/-- The tower's levels, for the model's rules. -/
def modelLevels : LevelModel modelRules ℕ where
  level := (TowerModel.levels fun _ => 0).level
  successor := (TowerModel.levels fun _ => 0).successor
  universe_typing := (TowerModel.levels fun _ => 0).universe_typing
  ground_typing := (TowerModel.levels fun _ => 0).ground_typing
  cumulative_universe := (TowerModel.levels fun _ => 0).cumulative_universe
  headEq_level := (TowerModel.levels fun _ => 0).headEq_level
  join_level := (TowerModel.levels fun _ => 0).join_level
  join_exists := (TowerModel.levels fun _ => 0).join_exists
  join_upper := (TowerModel.levels fun _ => 0).join_upper
  cumulative_refl := (TowerModel.levels fun _ => 0).cumulative_refl
  headEq_symm := (TowerModel.levels fun _ => 0).headEq_symm
  headEq_trans := (TowerModel.levels fun _ => 0).headEq_trans
  universe_decided := (TowerModel.levels fun _ => 0).universe_decided

/-- The consistency model: truth values for the codes, the cast, the recursor's
unfolding, and fresh numerals. -/
def model : Model Tower.Head ℕ where
  rules := modelRules
  roles := modelRoles
  zero := zeroN
  suc := sucN
  imp := impN
  allCarrier := modelAllCarrier
  eqCarrier := fun _ => none
  num := numN
  prop := propN
  holds := holdsN
  levels := modelLevels

theorem role_j : modelRoles jN = .computes 6 .leaf := rfl

theorem role_rec : modelRoles recN = .computes 5 .leaf := rfl

theorem modelShape : RootShape modelRules modelRoles where
  spine := by
    intro n t u step
    rcases step with ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, -⟩ | step
    · exact ⟨jN, 6, .leaf, [a₀, a₁, a₂, a₃, a₄, a₅], role_j, rfl, rfl, .leaf _⟩
    · exact definitionComputation_spine role_rec step
  deterministic := by
    intro n t u u' step step'
    refine (RootComputation.union_deterministic (c := jN) (c' := recN) (by decide)
      (fun {_ _ _} h => ?_) (fun {_ _ _} h => definitionComputation_headed h)
      (fun {_ _ _ _} h h' => ?_) (fun {_ _ _ _} h h' => definitionComputation_deterministic h h')
      step step').symm
    · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, -⟩ := h
      exact ⟨_, rfl⟩
    · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, rfl⟩ := h
      obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, e₂, rfl⟩ := h'
      rw [e₁] at e₂
      obtain ⟨_, args⟩ := appSpine_const_injective e₂
      simp only [List.cons.injEq] at args
      exact args.2.2.2.1.symm

theorem model_laws : model.Laws where
  truth :=
    { shape := modelShape
      zero := rfl
      suc := rfl
      imp := rfl
      all := fun {a} {A} found => by
        simp only [model, modelAllCarrier] at found
        by_cases h₁ : a = allPropN
        · subst h₁
          rfl
        · by_cases h₂ : a = allPredN
          · subst h₂
            rfl
          · rw [if_neg h₁, if_neg h₂] at found
            cases found
      eq := fun found => by cases found
      impNotEq := rfl }
  num := rfl
  prop := rfl
  holds := rfl

/-! ## The codes are read by the model -/

theorem codes_quantifiers {a : DeclName} {T : Tm Tower.Head 0} (found : codes.quantifiers a = some T) :
    (a = allPropN ∧ T = .const propN) ∨ (a = allPredN ∧ T = .pi (.const propN) (.const propN)) := by
  simp only [codes] at found
  by_cases h₁ : a = allPropN
  · rw [if_pos h₁] at found
    cases found
    exact .inl ⟨h₁, rfl⟩
  · rw [if_neg h₁] at found
    by_cases h₂ : a = allPredN
    · rw [if_pos h₂] at found
      cases found
      exact .inr ⟨h₂, rfl⟩
    · rw [if_neg h₂] at found
      cases found

theorem codes_read : CodesRead model codes where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := fun {a} {T} found => by
    rcases codes_quantifiers found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.gen, .prop, rfl, .prop, rfl⟩
    · exact ⟨.gen, .arr .prop .prop, rfl, .arr .prop .prop, rfl⟩
  eq := fun found => by cases found

/-! ## The base package is sound for the model -/

/-- The constant-free tower is sound for the model. -/
theorem sound_tower : Sound Tower.rules model where
  laws := model_laws
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => step.elim
  constants := fun declared => by cases declared

/-- `J` is valid at its declared type: the model casts. -/
theorem valid_j : ValidTm model .nil (.const jN) (elimType U0 U0) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  obtain ⟨validT, partsT, -⟩ := Derivable.valid sound_tower typed trivial
  exact ValidTm.castEliminator model_laws (.sort _)
    (fun a₀ a₁ a₂ a₃ a₄ a₅ => .inl ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩)
    (validT.validTy (sound_tower.isUniverse hw)) partsT

/-- **The base package with the codes is sound for the model.** -/
theorem sound_base : Sound signature.baseRules model where
  laws := model_laws
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun {n l r} step => by
    rcases step with ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ | step
    · exact rootSemantic_of_modelStep (M := model) (Or.inl ⟨_, _, _, _, _, _, rfl, rfl⟩)
    · exact ModelRoot.semantic model_laws codes_read.decodes (.inr step)
  constants := fun {c} {T} declared => by
    change (codes.codeType c).orElse (fun _ => base.constantType c) = some T at declared
    cases e : codes.codeType c with
    | some T' =>
        rw [e] at declared
        cases declared
        exact valid_code model_laws codes_read e
    | none =>
        rw [e] at declared
        change (if c = jN then some (elimType U0 U0) else none) = some T at declared
        by_cases hj : c = jN
        · subst hj
          rw [if_pos rfl] at declared
          cases declared
          exact valid_j
        · rw [if_neg hj] at declared
          cases declared

/-! ## The model computes the recursor -/

theorem computes : ComputesRecursor signature model .prop where
  laws := model_laws
  codes := codes_read
  carrier :=
    { term := rfl
      interpretable := .prop
      point := rfl
      predicate := rfl
      imp := rfl }
  step := fun P R F a q =>
    .inr ⟨consSub q (consSub a (consSub F (consSub R (consSub P (fun i => Fin.elim0 i))))),
      rfl, rfl⟩

/-! ## The laws of the package -/

theorem cumulative_zero : Tower.rules.cumulative U0 U0 := fun _ => le_refl _

theorem prop_typed : Typed signature.baseRules .nil (.const propN) (.head U0) :=
  .const (codes.extend_constantType_of_code base codes.codeType_prop)
    (.headType (.sort Tower.zero)) (.sort _)

theorem laws : signature.Laws where
  universes :=
    { codes :=
        { point := rfl
          predicate := rfl
          point_apart := by decide
          predicate_apart := by decide
          imp_apart := by decide
          holds_apart := by decide
          proofs_universe := .sort _
          proofs_typed := ⟨U1, .sort _, .sort _⟩
          proofs_pi := ⟨.sort (.max Tower.zero Tower.zero), .sorts _ _,
            fun _ => by simp [LevelExpr.eval, LevelTower.zero]⟩
          holds_formed := by
            refine ⟨.sort (.max Tower.zero (.succ Tower.zero)), .sort _, ?_⟩
            exact .piForm prop_typed (.sort _) (.headType (.sort Tower.zero)) (.sort _)
              (.sorts _ _)
          carrier_typed := prop_typed }
      motive_universe := .sort _
      proofs_below_motive := cumulative_zero
      motive_pi := ⟨.sort (.max Tower.zero Tower.zero), .sorts _ _,
        fun _ => by simp [LevelExpr.eval, LevelTower.zero]⟩
      top := ⟨U1, .sort _, .sort _, fun _ => by simp [LevelExpr.eval, LevelTower.zero],
        .sort (.max (.succ Tower.zero) (.succ Tower.zero)), .sorts _ _,
        fun _ => by simp [LevelExpr.eval, LevelTower.zero]⟩ }
  recursor_fresh := ⟨rfl, rfl⟩
  unfold_fresh := ⟨rfl, rfl⟩
  recursor_ne_unfold := by decide

/-! ## Consistency -/

/-- `Falsum := ∀ p : prop. p`. -/
def falsum : Tm Tower.Head 0 := .app (.const allPropN) (.lam (.var 0))

/-- The truth value of `Falsum` is `∀ X : Prop, X`. -/
theorem truth_falsum : Truth model.reading World.closed falsum (∀ X : Prop, X) :=
  Truth.all (a := allPropN) (A := .prop)
    rfl .refl
    (Read.lam_fresh fun _ => Read.generic' _ rfl)

/-- **Consistency of the accessibility package.** The extended package, with
its inert recursor and propositional unfolding over `prop`, proves no closed
term of `holds Falsum`. -/
theorem consistent_falsum (t : Tm Tower.Head 0) :
    ¬ Typed signature.rules .nil t (codes.holdsOf falsum) :=
  AccessibleRecursion.consistent computes laws sound_base truth_falsum (fun h => h False) t

/-- **Consistency of the strong variant**, in the same model: definitional
unfolding at every accessibility proof adds no closed proof of `Falsum`. -/
theorem strong_consistent_falsum (t : Tm Tower.Head 0) :
    ¬ Typed signature.strongRules .nil t (codes.holdsOf falsum) :=
  AccessibleRecursion.strong_consistent computes laws sound_base truth_falsum (fun h => h False) t

/-! ## The guard is essential -/

theorem curryData : CurryData signature jN where
  laws := laws
  carrier := rfl
  jDeclared := rfl
  jFresh := rfl
  jNe := by decide
  jFormed := by
    obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
    refine ⟨w, hw, Normalization.Derivable.mono ?_ typed⟩
    exact
      { headTyping := id
        isUniverse := id
        join := id
        cumulative := id
        headEq := id
        constantType := fun declared => nomatch declared
        computation := fun step => step.elim }
  proofsTyped := ⟨U1, .sort _, .sort _, .sort (.max Tower.zero (.succ Tower.zero)), .sorts _ _,
    fun _ => by simp [LevelExpr.eval, LevelTower.zero]⟩

/-- **The guard is essential.** Over the same base and codes, the unguarded
unfolding derives `Falsum` in the empty context, while the guarded package
derives no closed proof of it. -/
theorem guard_is_essential :
    Typed signature.unguardedRules .nil (Curry.proof signature jN) (codes.holdsOf falsum) ∧
      ∀ t, ¬ Typed signature.rules .nil t (codes.holdsOf falsum) :=
  ⟨curryData.curry_falsum, consistent_falsum⟩

/-! ## The new constants are inert in the kernel's conversion -/

theorem inertLaws : signature.InertLaws where
  base_step := fun {n l r} step h => by
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := step
    simp only [appSpine, List.foldl, Avoids] at h
    exact h.1.1.2
  base_types := fun {c T} declared => by
    change (if c = jN then some (elimType U0 U0) else none) = some T at declared
    split at declared
    · cases declared
      simp [Avoids, elimType, TelescopeAbstraction.closeType, elimTelescope, elimPrefix, elimBody]
    · cases declared
  quantifiers := fun {a A} found => by
    rcases codes_quantifiers found with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · show ¬ (propN = recN ∨ propN = unfoldN)
      decide
    · show ¬ (propN = recN ∨ propN = unfoldN) ∧ ¬ (propN = recN ∨ propN = unfoldN)
      decide
  equations := fun found => by cases found

/-- **The kernel's conversion is unchanged** for this package: on every problem
avoiding the recursor and its unfolding, the extended and the base package
derive the same conversions. -/
theorem algorithm_iff {st : AlgorithmStatement Tower.Head}
    (h : AlgorithmAvoids signature.New st) :
    Algorithm signature.rules st ↔ Algorithm signature.baseRules st :=
  Signature.algorithm_iff laws inertLaws h

end PropInstance

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
