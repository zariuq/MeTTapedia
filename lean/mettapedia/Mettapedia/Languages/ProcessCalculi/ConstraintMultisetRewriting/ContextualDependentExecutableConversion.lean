import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConversionBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTowerBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# Eventual success of executable conversion in the cumulative tower

The executable type-directed conversion, run with the actual normalizer, accepts
every pair of typed terms that are equal in the cumulative tower, at some finite
budget, and keeps its result at every larger budget. The same holds for type
comparison.

The proof follows the algorithmic equality, which is complete for the tower. Its
derivations compare weak-head normal forms; the executable compares the full
normal forms its normalizer returns, and it η-expands the terms it was given,
not their weak-head forms. A derivation therefore guides the executable through
every input that is joinable with its own, under directed reduction, in a
context whose entries are joinable with its own. Confluence makes the shapes
agree; strong normalization of typed tower terms makes every normalizer call
finish; fuel stability merges the budgets of the recursive calls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExecutableConversion

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion ContextualDependentExecutableJoin

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- The actual normalizer of the tower. -/
abbrev red : Reducer (LevelTower.rules L) := ExecutableReduction.normalize (LevelTower.rules L) (fun _ => none)

theorem empty_root : (LevelTower.rules L).computation = RootComputation.empty := rfl

/-! ## The normalizer -/

theorem normalize_star {n : Nat} : ∀ (fuel : Nat) {term : Tm (LevelTower.Head L) n}
    {result : Result (LevelTower.rules L) term},
    ExecutableReduction.normalize (LevelTower.rules L) (fun _ => none) fuel term = some result →
      Star (R := LevelTower.rules L) term result.val
  | 0, _, _, accepted => by cases accepted
  | fuel + 1, term, result, accepted => by
      cases current : step (LevelTower.rules L) (fun _ => none) term with
      | none =>
          simp only [ExecutableReduction.normalize, current, Option.some.injEq] at accepted
          subst accepted
          exact .refl
      | some next =>
          cases later : ExecutableReduction.normalize (LevelTower.rules L) (fun _ => none) fuel next.val with
          | none =>
              simp only [ExecutableReduction.normalize, current, later] at accepted
              cases accepted
          | some answer =>
              simp only [ExecutableReduction.normalize, current, later, Option.some.injEq] at accepted
              subst accepted
              exact Relation.ReflTransGen.head
                (ContextualDependentReductionBudget.step_directed (LevelTower.rules L) _ term next current)
                (normalize_star fuel later)

/-- On a typed term the normalizer eventually returns a normal reduct, and keeps it. -/
theorem red_eventually {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {term type : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (typed : Typed (LevelTower.rules L) Γ term type) :
    ∃ fuel result, Normal (LevelTower.rules L) result.val ∧ Star (R := LevelTower.rules L) term result.val ∧
      ∀ larger, fuel ≤ larger → red larger term = some result := by
  obtain ⟨fuel, result, normal, stable⟩ := ContextualDependentTowerBudget.typed_eventually_stable formed typed
  exact ⟨fuel, result, normal, normalize_star fuel (stable fuel le_rfl), stable⟩

theorem red_eventually_type {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {type : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (isType : IsType (LevelTower.rules L) Γ type) :
    ∃ fuel result, Normal (LevelTower.rules L) result.val ∧ Star (R := LevelTower.rules L) type result.val ∧
      ∀ larger, fuel ≤ larger → red larger type = some result := by
  obtain ⟨_, _, typed⟩ := isType
  exact red_eventually formed typed

/-! ## One unfolding of each executable comparison -/

section Unfold

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]

/-- A successful computation. -/
abbrev Ok {α : Type} (computation : Option α) : Prop := ∃ result, computation = some result

variable {n : Nat} {fuel : Nat} {Γ : Ctx (LevelTower.Head L) n}

theorem compare_pi {left right type domain : Tm (LevelTower.Head L) n} {body : Tm (LevelTower.Head L) (n + 1)}
    {path : Reduces (LevelTower.rules L) type (.pi domain body)}
    (normal : red (fuel + 1) type = some ⟨.pi domain body, path⟩)
    (inner : Ok (compare (LevelTower.rules L) red fuel (.snoc Γ domain)
      (.app (Presentation.rename wk left) (.var 0)) (.app (Presentation.rename wk right) (.var 0)) body)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed]
  exact ⟨_, rfl⟩

theorem compare_sigma {left right type domain : Tm (LevelTower.Head L) n} {body : Tm (LevelTower.Head L) (n + 1)}
    {path : Reduces (LevelTower.rules L) type (.sigma domain body)}
    (normal : red (fuel + 1) type = some ⟨.sigma domain body, path⟩)
    (first : Ok (compare (LevelTower.rules L) red fuel Γ (.fst left) (.fst right) domain))
    (second : Ok (compare (LevelTower.rules L) red fuel Γ (.snd left) (.snd right) (inst0 (.fst left) body))) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := first
  obtain ⟨certificate', computed'⟩ := second
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem compare_universe {left right type : Tm (LevelTower.Head L) n} {value : LevelTower.Head L}
    {path : Reduces (LevelTower.rules L) type (.head value)} (universeHead : (LevelTower.rules L).isUniverse value)
    (normal : red (fuel + 1) type = some ⟨.head value, path⟩)
    (inner : Ok (types (LevelTower.rules L) red fuel Γ left right)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, dif_pos universeHead, computed]
  exact ⟨_, rfl⟩

theorem compare_refl {left right type carrier first second subject subject' : Tm (LevelTower.Head L) n}
    {path : Reduces (LevelTower.rules L) type (.id carrier first second)}
    {leftPath : Reduces (LevelTower.rules L) left (.refl subject)}
    {rightPath : Reduces (LevelTower.rules L) right (.refl subject')}
    (normal : red (fuel + 1) type = some ⟨.id carrier first second, path⟩)
    (leftNormal : red (fuel + 1) left = some ⟨.refl subject, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.refl subject', rightPath⟩)
    (inner : Ok (compare (LevelTower.rules L) red fuel Γ subject subject' carrier)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, leftNormal, rightNormal, computed]
  exact ⟨_, rfl⟩

theorem compareNeutral_of {left right type : Tm (LevelTower.Head L) n}
    {first : Result (LevelTower.rules L) left} {second : Result (LevelTower.rules L) right}
    (leftNormal : red (fuel + 1) left = some first) (rightNormal : red (fuel + 1) right = some second)
    (inner : Ok (neutral (LevelTower.rules L) red fuel Γ first.val second.val)) :
    Ok (compareNeutral (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compareNeutral, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed]
  exact ⟨_, rfl⟩

/-- At a normal type that is an elimination spine, terms are compared as neutral terms. -/
theorem compare_elim {left right type : Tm (LevelTower.Head L) n} {normalType : Result (LevelTower.rules L) type}
    (shape : Elim normalType.val) (normal : red (fuel + 1) type = some normalType)
    (inner : Ok (compareNeutral (LevelTower.rules L) red fuel Γ left right type)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨code, path⟩ := normalType
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases shape <;> exact ⟨_, computed⟩

/-- At a head that is not a universe, terms are compared as neutral terms. -/
theorem compare_ground {left right type : Tm (LevelTower.Head L) n} {value : LevelTower.Head L}
    {path : Reduces (LevelTower.rules L) type (.head value)} (notUniverse : ¬ (LevelTower.rules L).isUniverse value)
    (normal : red (fuel + 1) type = some ⟨.head value, path⟩)
    (inner : Ok (compareNeutral (LevelTower.rules L) red fuel Γ left right type)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, dif_neg notUniverse]
  exact ⟨_, computed⟩

/-- At an identity type, terms whose normal forms are elimination spines are compared as
neutral terms. -/
theorem compare_id_elim {left right type carrier first second : Tm (LevelTower.Head L) n}
    {path : Reduces (LevelTower.rules L) type (.id carrier first second)}
    {leftResult : Result (LevelTower.rules L) left} {rightResult : Result (LevelTower.rules L) right}
    (normal : red (fuel + 1) type = some ⟨.id carrier first second, path⟩)
    (leftNormal : red (fuel + 1) left = some leftResult) (rightNormal : red (fuel + 1) right = some rightResult)
    (shape : Elim leftResult.val)
    (inner : Ok (compareNeutral (LevelTower.rules L) red fuel Γ left right type)) :
    Ok (compare (LevelTower.rules L) red (fuel + 1) Γ left right type) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨leftCode, leftPath⟩ := leftResult
  rw [ExecutableConversion.compare, normal]
  simp only [Option.bind_eq_bind, Option.bind_some, leftNormal, rightNormal]
  cases shape <;> exact ⟨_, computed⟩

theorem neutral_var (i : Fin n) :
    ∃ certificate, neutral (LevelTower.rules L) red (fuel + 1) Γ (.var i) (.var i) =
      some ⟨Ctx.lookup Γ i, certificate⟩ := by
  simp only [ExecutableConversion.neutral]
  exact ⟨_, rfl⟩

theorem neutral_app {function function' argument argument' functionType domain : Tm (LevelTower.Head L) n}
    {body : Tm (LevelTower.Head L) (n + 1)}
    {functionCertificate : Certificate (LevelTower.rules L) (.neutral Γ function function' functionType)}
    {path : Reduces (LevelTower.rules L) functionType (.pi domain body)}
    (functions : neutral (LevelTower.rules L) red fuel Γ function function' = some ⟨functionType, functionCertificate⟩)
    (normal : red (fuel + 1) functionType = some ⟨.pi domain body, path⟩)
    (arguments : Ok (compare (LevelTower.rules L) red fuel Γ argument argument' domain)) :
    ∃ certificate, neutral (LevelTower.rules L) red (fuel + 1) Γ (.app function argument) (.app function' argument') =
      some ⟨inst0 argument body, certificate⟩ := by
  obtain ⟨certificate, computed⟩ := arguments
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, functions, Option.bind_some, normal, computed]
  exact ⟨_, rfl⟩

theorem neutral_fst {pair pair' pairType domain : Tm (LevelTower.Head L) n} {body : Tm (LevelTower.Head L) (n + 1)}
    {pairCertificate : Certificate (LevelTower.rules L) (.neutral Γ pair pair' pairType)}
    {path : Reduces (LevelTower.rules L) pairType (.sigma domain body)}
    (pairs : neutral (LevelTower.rules L) red fuel Γ pair pair' = some ⟨pairType, pairCertificate⟩)
    (normal : red (fuel + 1) pairType = some ⟨.sigma domain body, path⟩) :
    ∃ certificate, neutral (LevelTower.rules L) red (fuel + 1) Γ (.fst pair) (.fst pair') =
      some ⟨domain, certificate⟩ := by
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, pairs, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem neutral_snd {pair pair' pairType domain : Tm (LevelTower.Head L) n} {body : Tm (LevelTower.Head L) (n + 1)}
    {pairCertificate : Certificate (LevelTower.rules L) (.neutral Γ pair pair' pairType)}
    {path : Reduces (LevelTower.rules L) pairType (.sigma domain body)}
    (pairs : neutral (LevelTower.rules L) red fuel Γ pair pair' = some ⟨pairType, pairCertificate⟩)
    (normal : red (fuel + 1) pairType = some ⟨.sigma domain body, path⟩) :
    ∃ certificate, neutral (LevelTower.rules L) red (fuel + 1) Γ (.snd pair) (.snd pair') =
      some ⟨inst0 (.fst pair) body, certificate⟩ := by
  rw [ExecutableConversion.neutral]
  simp only [Option.bind_eq_bind, pairs, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem types_heads {left right : Tm (LevelTower.Head L) n} {a b : LevelTower.Head L}
    {leftPath : Reduces (LevelTower.rules L) left (.head a)} {rightPath : Reduces (LevelTower.rules L) right (.head b)}
    (leftNormal : red (fuel + 1) left = some ⟨.head a, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.head b, rightPath⟩) (same : HeadSame (LevelTower.rules L) a b) :
    Ok (types (LevelTower.rules L) red (fuel + 1) Γ left right) := by
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have same' : a = b ∨ (LevelTower.rules L).headEq a b := same
  rw [dif_pos same']
  exact ⟨_, rfl⟩

theorem types_pi {left right domain domain' : Tm (LevelTower.Head L) n} {body body' : Tm (LevelTower.Head L) (n + 1)}
    {leftPath : Reduces (LevelTower.rules L) left (.pi domain body)}
    {rightPath : Reduces (LevelTower.rules L) right (.pi domain' body')}
    (leftNormal : red (fuel + 1) left = some ⟨.pi domain body, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.pi domain' body', rightPath⟩)
    (domains : Ok (types (LevelTower.rules L) red fuel Γ domain domain'))
    (bodies : Ok (types (LevelTower.rules L) red fuel (.snoc Γ domain) body body')) :
    Ok (types (LevelTower.rules L) red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := domains
  obtain ⟨certificate', computed'⟩ := bodies
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem types_sigma {left right domain domain' : Tm (LevelTower.Head L) n}
    {body body' : Tm (LevelTower.Head L) (n + 1)}
    {leftPath : Reduces (LevelTower.rules L) left (.sigma domain body)}
    {rightPath : Reduces (LevelTower.rules L) right (.sigma domain' body')}
    (leftNormal : red (fuel + 1) left = some ⟨.sigma domain body, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.sigma domain' body', rightPath⟩)
    (domains : Ok (types (LevelTower.rules L) red fuel Γ domain domain'))
    (bodies : Ok (types (LevelTower.rules L) red fuel (.snoc Γ domain) body body')) :
    Ok (types (LevelTower.rules L) red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := domains
  obtain ⟨certificate', computed'⟩ := bodies
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem types_id {left right carrier carrier' a a' b b' : Tm (LevelTower.Head L) n}
    {leftPath : Reduces (LevelTower.rules L) left (.id carrier a b)}
    {rightPath : Reduces (LevelTower.rules L) right (.id carrier' a' b')}
    (leftNormal : red (fuel + 1) left = some ⟨.id carrier a b, leftPath⟩)
    (rightNormal : red (fuel + 1) right = some ⟨.id carrier' a' b', rightPath⟩)
    (carriers : Ok (types (LevelTower.rules L) red fuel Γ carrier carrier'))
    (lefts : Ok (compare (LevelTower.rules L) red fuel Γ a a' carrier))
    (rights : Ok (compare (LevelTower.rules L) red fuel Γ b b' carrier)) :
    Ok (types (LevelTower.rules L) red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := carriers
  obtain ⟨certificate', computed'⟩ := lefts
  obtain ⟨certificate'', computed''⟩ := rights
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some, computed, computed', computed'']
  exact ⟨_, rfl⟩

/-- Types whose normal forms are elimination spines are compared as neutral terms. -/
theorem types_elim {left right : Tm (LevelTower.Head L) n}
    {first : Result (LevelTower.rules L) left} {second : Result (LevelTower.rules L) right}
    (leftNormal : red (fuel + 1) left = some first) (rightNormal : red (fuel + 1) right = some second)
    (shape : Elim first.val) (inner : Ok (neutral (LevelTower.rules L) red fuel Γ first.val second.val)) :
    Ok (types (LevelTower.rules L) red (fuel + 1) Γ left right) := by
  obtain ⟨certificate, computed⟩ := inner
  obtain ⟨code, path⟩ := first
  rw [ExecutableConversion.types, leftNormal, rightNormal]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases shape <;> simp only [computed] <;> exact ⟨_, rfl⟩

end Unfold

/-! ## Tower facts -/

section Tower

local notation "TS" => TowerModel.setting (L := L) (fun _ => UniverseLevel.LevelOrder.bot)

theorem whStep_directed {n : Nat} {t u : Tm (LevelTower.Head L) n}
    (step : WhStep (LevelTower.rules L) (TowerModel.roles (L := L)) t u) :
    StrongNormalization.Reduces (LevelTower.rules L) t u := by
  induction step with
  | beta body a => exact .betaPi body a
  | fstPair a b => exact .betaSigmaFst a b
  | sndPair a b => exact .betaSigmaSnd a b
  | root impossible => exact False.elim (no_root empty_root impossible)
  | appFun _ ih => exact .congAppFun ih
  | fst _ ih => exact .congFst ih
  | snd _ ih => exact .congSnd ih
  | scrutinee role => cases role

theorem whRed_star {n : Nat} {t u : Tm (LevelTower.Head L) n}
    (steps : WhRed (LevelTower.rules L) (TowerModel.roles (L := L)) t u) : Star (R := LevelTower.rules L) t u := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (whStep_directed step)

omit [UniverseLevel.LevelOrder L] in
theorem elim_appSpine {n : Nat} :
    ∀ (args : List (Tm (LevelTower.Head L) n)) {f : Tm (LevelTower.Head L) n}, Elim f → Elim (appSpine f args)
  | [], _, elim => elim
  | _ :: rest, _, elim => elim_appSpine rest (.app elim)

omit [UniverseLevel.LevelOrder L] in
theorem neutral_elim {n : Nat} {t : Tm (LevelTower.Head L) n} (neutral : Neutral (TowerModel.roles (L := L)) t) :
    Elim t := by
  induction neutral with
  | var i => exact .var i
  | app _ ih => exact .app ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | rigid args _ => exact elim_appSpine args (.const _)
  | stuck role => cases role

theorem typed_reduct {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t t' T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (path : Reduces (LevelTower.rules L) t t')
    (typed : Typed (LevelTower.rules L) Γ t T) : Typed (LevelTower.rules L) Γ t' T :=
  (Reduces.preserve (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads formed path typed).1

theorem typeEq_reduct {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A A' : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (path : Reduces (LevelTower.rules L) A A')
    (isType : IsType (LevelTower.rules L) Γ A) : TypeEq (LevelTower.rules L) Γ A A' :=
  let ⟨u, hu, typed⟩ := isType
  ⟨u, hu, (Reduces.preserve (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads formed path typed).2⟩

theorem isType_reduct {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A A' : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (path : Reduces (LevelTower.rules L) A A')
    (isType : IsType (LevelTower.rules L) Γ A) : IsType (LevelTower.rules L) Γ A' := by
  obtain ⟨u, hu, typed⟩ := isType
  exact ⟨u, hu, typed_reduct formed path typed⟩

theorem isType_of_typed {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (typed : Typed (LevelTower.rules L) Γ t T) :
    IsType (LevelTower.rules L) Γ T :=
  Typed.isType (S := TS) typed formed

/-- Two types share a universe. -/
theorem common_universe {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B : Tm (LevelTower.Head L) n}
    (first : IsType (LevelTower.rules L) Γ A) (second : IsType (LevelTower.rules L) Γ B) :
    ∃ u, (LevelTower.rules L).isUniverse u ∧ Typed (LevelTower.rules L) Γ A (.head u) ∧
      Typed (LevelTower.rules L) Γ B (.head u) := by
  obtain ⟨a, ha, ta⟩ := first
  obtain ⟨b, hb, tb⟩ := second
  obtain ⟨w, joined⟩ := (TS).levels.join_exists ha hb
  obtain ⟨left, right⟩ := (TS).levels.join_upper joined
  exact ⟨w, ((TS).levels.join_level joined).1, Derivable.cumul ta left, Derivable.cumul tb right⟩

theorem types_typeEq {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B : Tm (LevelTower.Head L) n}
    (derivation : Algorithm (LevelTower.rules L) (.types Γ A B)) (formed : CtxFormed (LevelTower.rules L) Γ)
    (first : IsType (LevelTower.rules L) Γ A) (second : IsType (LevelTower.rules L) Γ B) :
    TypeEq (LevelTower.rules L) Γ A B := by
  obtain ⟨u, hu, ta, tb⟩ := common_universe first second
  exact ⟨u, hu, Algorithm.sound (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    derivation formed hu ta tb⟩

theorem compare_equal {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {a b T : Tm (LevelTower.Head L) n}
    (derivation : Algorithm (LevelTower.rules L) (.compare Γ a b T)) (formed : CtxFormed (LevelTower.rules L) Γ)
    (first : Typed (LevelTower.rules L) Γ a T) (second : Typed (LevelTower.rules L) Γ b T) :
    Equal (LevelTower.rules L) Γ a b T :=
  Algorithm.sound (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    derivation formed first second

theorem neutral_sound {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {a b U X Y : Tm (LevelTower.Head L) n}
    (derivation : Algorithm (LevelTower.rules L) (.neutral Γ a b U)) (formed : CtxFormed (LevelTower.rules L) Γ)
    (first : Typed (LevelTower.rules L) Γ a X) (second : Typed (LevelTower.rules L) Γ b Y) :
    Typed (LevelTower.rules L) Γ a U ∧ Typed (LevelTower.rules L) Γ b U ∧
      (∀ {X'}, Typed (LevelTower.rules L) Γ a X' → TypeLe (LevelTower.rules L) Γ U X') ∧
      (∀ {Y'}, Typed (LevelTower.rules L) Γ b Y' → TypeLe (LevelTower.rules L) Γ U Y') := by
  obtain ⟨ta, tb, _, le, le'⟩ := Algorithm.sound (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra derivation formed first second
  exact ⟨ta, tb, le, le'⟩

theorem app_var_typed {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {f A : Tm (LevelTower.Head L) n}
    {B : Tm (LevelTower.Head L) (n + 1)} (typed : Typed (LevelTower.rules L) Γ f (.pi A B)) :
    Typed (LevelTower.rules L) (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0)) B := by
  have weakened : Typed (LevelTower.rules L) (.snoc Γ A) (Presentation.rename wk f)
      (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) := Typed.weaken typed
  have applied := Derivable.appElim weakened (.var 0 : Typed (LevelTower.rules L) (.snoc Γ A) (.var 0) _)
  rwa [inst0_var_rename_liftRen_wk] at applied

theorem refl_subject {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {c A x y : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (typed : Typed (LevelTower.rules L) Γ (.refl c) (.id A x y)) :
    Typed (LevelTower.rules L) Γ c A := by
  obtain ⟨A₁, typed₁, le⟩ := Typed.generation typed
  have equal := TypeLe.id_eq (S := TS) TowerModel.facts le (isType_of_typed formed typed) formed
  exact Typed.convType typed₁ (TypeEq.id_injective TowerModel.facts equal formed).1

end Tower

/-! ## Contexts with joinable entries -/

/-- Two contexts whose entries are pairwise joinable. -/
def CtxJoin {n : Nat} (Γ Γ' : Ctx (LevelTower.Head L) n) : Prop :=
  ∀ i, Join (LevelTower.rules L) (Ctx.lookup Γ i) (Ctx.lookup Γ' i)

theorem CtxJoin.refl {n : Nat} (Γ : Ctx (LevelTower.Head L) n) : CtxJoin Γ Γ := fun _ => Join.refl _

theorem CtxJoin.snoc {n : Nat} {Γ Γ' : Ctx (LevelTower.Head L) n} {A A' : Tm (LevelTower.Head L) n}
    (joined : CtxJoin Γ Γ') (entry : Join (LevelTower.rules L) A A') : CtxJoin (.snoc Γ A) (.snoc Γ' A') := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Ctx.lookup_snoc_zero]
    exact Join.rename wk entry
  · simp only [Ctx.lookup_snoc_succ]
    exact Join.rename wk (joined i)

/-! ## The derivation guides the executable -/

section Completeness

local notation "TS" => TowerModel.setting (L := L) (fun _ => UniverseLevel.LevelOrder.bot)

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)]

theorem compare_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {left right type : Tm (LevelTower.Head L) n}
    {result : Certificate (LevelTower.rules L) (.compare Γ left right type)}
    (accepted : compare (LevelTower.rules L) red fuel Γ left right type = some result) (enough : fuel ≤ larger) :
    compare (LevelTower.rules L) red larger Γ left right type = some result :=
  ContextualDependentConversionBudget.normalizer_compare_mono (LevelTower.rules L) (fun _ => none) accepted enough

theorem neutral_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {left right : Tm (LevelTower.Head L) n}
    {result : NeutralResult (LevelTower.rules L) Γ left right}
    (accepted : neutral (LevelTower.rules L) red fuel Γ left right = some result) (enough : fuel ≤ larger) :
    neutral (LevelTower.rules L) red larger Γ left right = some result :=
  ContextualDependentConversionBudget.normalizer_neutral_mono (LevelTower.rules L) (fun _ => none) accepted enough

theorem types_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {left right : Tm (LevelTower.Head L) n}
    {result : Certificate (LevelTower.rules L) (.types Γ left right)}
    (accepted : types (LevelTower.rules L) red fuel Γ left right = some result) (enough : fuel ≤ larger) :
    types (LevelTower.rules L) red larger Γ left right = some result :=
  ContextualDependentConversionBudget.types_success_mono (LevelTower.rules L) red
    (ContextualDependentConversionBudget.normalizer_stable (LevelTower.rules L) (fun _ => none)) accepted enough

/-- Type comparison succeeds on all typed inputs joinable with the given ones. -/
def TypesRealized {n : Nat} (Γ : Ctx (LevelTower.Head L) n) (A B : Tm (LevelTower.Head L) n) : Prop :=
  ∀ {Γ' : Ctx (LevelTower.Head L) n} {A' B' : Tm (LevelTower.Head L) n},
    CtxFormed (LevelTower.rules L) Γ' → CtxJoin Γ Γ' →
    Join (LevelTower.rules L) A A' → Join (LevelTower.rules L) B B' →
    IsType (LevelTower.rules L) Γ' A' → IsType (LevelTower.rules L) Γ' B' →
    ∃ fuel, Ok (types (LevelTower.rules L) red fuel Γ' A' B')

/-- Term comparison succeeds on all typed inputs joinable with the given ones. -/
def TermsRealized {n : Nat} (Γ : Ctx (LevelTower.Head L) n) (t u A : Tm (LevelTower.Head L) n) : Prop :=
  ∀ {Γ' : Ctx (LevelTower.Head L) n} {t' u' A' : Tm (LevelTower.Head L) n},
    CtxFormed (LevelTower.rules L) Γ' → CtxJoin Γ Γ' →
    Join (LevelTower.rules L) t t' → Join (LevelTower.rules L) u u' → Join (LevelTower.rules L) A A' →
    Typed (LevelTower.rules L) Γ' t' A' → Typed (LevelTower.rules L) Γ' u' A' →
    ∃ fuel, Ok (compare (LevelTower.rules L) red fuel Γ' t' u' A')

/-- Neutral comparison succeeds on all typed normal reducts of the given spines, and returns a
type joinable with the derivation's. -/
def SpinesRealized {n : Nat} (Γ : Ctx (LevelTower.Head L) n) (t u U : Tm (LevelTower.Head L) n) : Prop :=
  ∀ {Γ' : Ctx (LevelTower.Head L) n} {t' u' : Tm (LevelTower.Head L) n},
    CtxFormed (LevelTower.rules L) Γ' → CtxJoin Γ Γ' →
    Star (R := LevelTower.rules L) t t' → Star (R := LevelTower.rules L) u u' →
    Normal (LevelTower.rules L) t' → Normal (LevelTower.rules L) u' →
    (∃ X, Typed (LevelTower.rules L) Γ' t' X) → (∃ Y, Typed (LevelTower.rules L) Γ' u' Y) →
    ∃ fuel T certificate, neutral (LevelTower.rules L) red fuel Γ' t' u' = some ⟨T, certificate⟩ ∧
      Join (LevelTower.rules L) U T

/-- What each algorithmic judgment guarantees about the executable. -/
def Realized : AlgorithmicStatement (LevelTower.Head L) → Prop
  | .types Γ A B => TypesRealized Γ A B
  | .typesW Γ A B => TypesRealized Γ A B
  | .terms Γ t u A => TermsRealized Γ t u A
  | .termsW Γ t u A => TermsRealized Γ t u A
  | .spines Γ t u U => SpinesRealized Γ t u U
  | .spinesW Γ t u U => SpinesRealized Γ t u U

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] in
/-- The sides of a spine judgment are elimination spines. -/
def SpineElim (statement : AlgorithmicStatement (LevelTower.Head L)) : Prop :=
  ∀ {n : Nat} (Γ : Ctx (LevelTower.Head L) n) (first second type : Tm (LevelTower.Head L) n),
    (statement = .spines Γ first second type ∨ statement = .spinesW Γ first second type) →
      Elim first ∧ Elim second

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] in
theorem spine_elim {statement : AlgorithmicStatement (LevelTower.Head L)}
    (proof : Algorithmic (LevelTower.rules L) (TowerModel.roles (L := L)) statement) : SpineElim statement := by
  induction proof with
  | types => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | heads => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | pi => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | sigma => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | id => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | inductiveType => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | neutralTypes => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | terms => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | univ => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | eta => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | sigmaEta => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | refl => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | spine => intro _ _ _ _ _ same; rcases same with same | same <;> cases same
  | var index =>
      intro _ _ _ _ _ same
      rcases same with same | same <;> cases same
      exact ⟨.var index, .var index⟩
  | const declared => cases declared
  | @app n Γ f g a b A B functions _ ihFunction _ =>
      intro _ _ _ _ _ same
      rcases same with same | same <;> cases same
      have inner := ihFunction Γ f g _ (.inr rfl)
      exact ⟨.app inner.1, .app inner.2⟩
  | @fst n Γ p q A B pairs ih =>
      intro _ _ _ _ _ same
      rcases same with same | same <;> cases same
      have inner := ih Γ p q _ (.inr rfl)
      exact ⟨.fst inner.1, .fst inner.2⟩
  | @snd n Γ p q A B pairs ih =>
      intro _ _ _ _ _ same
      rcases same with same | same <;> cases same
      have inner := ih Γ p q _ (.inr rfl)
      exact ⟨.snd inner.1, .snd inner.2⟩
  | @spinesW n Γ t u U U' _ _ _ ih =>
      intro _ _ _ _ _ same
      rcases same with same | same <;> cases same
      exact ih Γ t u U (.inl rfl)

/-- **Every algorithmic judgment is realized by the executable**, on every typed input
joinable with its own. -/
theorem realized {statement : AlgorithmicStatement (LevelTower.Head L)}
    (derivation : Algorithmic (LevelTower.rules L) (TowerModel.roles (L := L)) statement) : Realized statement := by
  induction derivation with
  | types redA redB _ _ _ ih =>
      intro Γ' P Q formed joined jP jQ tP tQ
      exact (ih : TypesRealized _ _ _) formed joined (Join.star_left empty_root (whRed_star redA.red) jP)
        (Join.star_left empty_root (whRed_star redB.red) jQ) tP tQ
  | @heads n Γ h h' u same _ _ _ =>
      intro Γ' P Q formed joined jP jQ tP tQ
      obtain ⟨f₁, ⟨code₁, path₁⟩, normal₁, star₁, stable₁⟩ := red_eventually_type formed tP
      obtain ⟨f₂, ⟨code₂, path₂⟩, normal₂, star₂, stable₂⟩ := red_eventually_type formed tQ
      obtain rfl := Join.head_normal empty_root (Join.star_right empty_root jP star₁) normal₁
      obtain rfl := Join.head_normal empty_root (Join.star_right empty_root jQ star₂) normal₂
      exact ⟨f₁ + f₂ + 1, types_heads (stable₁ _ (by omega)) (stable₂ _ (by omega)) same⟩
  | @pi n Γ A A' B B' _ _ _ ihA ihB =>
      intro Γ' P Q formed joined jP jQ tP tQ
      obtain ⟨f₁, ⟨code₁, path₁⟩, normal₁, star₁, stable₁⟩ := red_eventually_type formed tP
      obtain ⟨f₂, ⟨code₂, path₂⟩, normal₂, star₂, stable₂⟩ := red_eventually_type formed tQ
      obtain ⟨D₁, E₁, rfl, sD₁, sE₁⟩ := Join.pi_normal empty_root (Join.star_right empty_root jP star₁) normal₁
      obtain ⟨D₂, E₂, rfl, sD₂, sE₂⟩ := Join.pi_normal empty_root (Join.star_right empty_root jQ star₂) normal₂
      obtain ⟨⟨u₁, hu₁, tD₁⟩, v₁, hv₁, tE₁⟩ := IsType.pi_parts (isType_reduct formed path₁ tP)
      obtain ⟨⟨u₂, hu₂, tD₂⟩, v₂, hv₂, tE₂⟩ := IsType.pi_parts (isType_reduct formed path₂ tQ)
      obtain ⟨g₁, c₁, computed₁⟩ := (ihA : TypesRealized _ _ _) formed joined (Join.of_star sD₁) (Join.of_star sD₂)
        ⟨u₁, hu₁, tD₁⟩ ⟨u₂, hu₂, tD₂⟩
      have domains := types_typeEq c₁.down formed ⟨u₁, hu₁, tD₁⟩ ⟨u₂, hu₂, tD₂⟩
      obtain ⟨g₂, c₂, computed₂⟩ := (ihB : TypesRealized _ _ _) (.snoc formed ⟨u₁, hu₁, tD₁⟩)
        (joined.snoc (Join.of_star sD₁)) (Join.of_star sE₁) (Join.of_star sE₂) ⟨v₁, hv₁, tE₁⟩
        ⟨v₂, hv₂, Typed.ctxConv tE₂ (TypeEq.symm domains)⟩
      exact ⟨f₁ + f₂ + g₁ + g₂ + 1, types_pi (stable₁ _ (by omega)) (stable₂ _ (by omega))
        ⟨_, types_mono computed₁ (by omega)⟩ ⟨_, types_mono computed₂ (by omega)⟩⟩
  | @sigma n Γ A A' B B' _ _ _ ihA ihB =>
      intro Γ' P Q formed joined jP jQ tP tQ
      obtain ⟨f₁, ⟨code₁, path₁⟩, normal₁, star₁, stable₁⟩ := red_eventually_type formed tP
      obtain ⟨f₂, ⟨code₂, path₂⟩, normal₂, star₂, stable₂⟩ := red_eventually_type formed tQ
      obtain ⟨D₁, E₁, rfl, sD₁, sE₁⟩ := Join.sigma_normal empty_root (Join.star_right empty_root jP star₁) normal₁
      obtain ⟨D₂, E₂, rfl, sD₂, sE₂⟩ := Join.sigma_normal empty_root (Join.star_right empty_root jQ star₂) normal₂
      obtain ⟨⟨u₁, hu₁, tD₁⟩, v₁, hv₁, tE₁⟩ := IsType.sigma_parts (isType_reduct formed path₁ tP)
      obtain ⟨⟨u₂, hu₂, tD₂⟩, v₂, hv₂, tE₂⟩ := IsType.sigma_parts (isType_reduct formed path₂ tQ)
      obtain ⟨g₁, c₁, computed₁⟩ := (ihA : TypesRealized _ _ _) formed joined (Join.of_star sD₁) (Join.of_star sD₂)
        ⟨u₁, hu₁, tD₁⟩ ⟨u₂, hu₂, tD₂⟩
      have domains := types_typeEq c₁.down formed ⟨u₁, hu₁, tD₁⟩ ⟨u₂, hu₂, tD₂⟩
      obtain ⟨g₂, c₂, computed₂⟩ := (ihB : TypesRealized _ _ _) (.snoc formed ⟨u₁, hu₁, tD₁⟩)
        (joined.snoc (Join.of_star sD₁)) (Join.of_star sE₁) (Join.of_star sE₂) ⟨v₁, hv₁, tE₁⟩
        ⟨v₂, hv₂, Typed.ctxConv tE₂ (TypeEq.symm domains)⟩
      exact ⟨f₁ + f₂ + g₁ + g₂ + 1, types_sigma (stable₁ _ (by omega)) (stable₂ _ (by omega))
        ⟨_, types_mono computed₁ (by omega)⟩ ⟨_, types_mono computed₂ (by omega)⟩⟩
  | @id n Γ A A' x x' y y' _ _ _ ihA ihx ihy =>
      intro Γ' P Q formed joined jP jQ tP tQ
      obtain ⟨f₁, ⟨code₁, path₁⟩, normal₁, star₁, stable₁⟩ := red_eventually_type formed tP
      obtain ⟨f₂, ⟨code₂, path₂⟩, normal₂, star₂, stable₂⟩ := red_eventually_type formed tQ
      obtain ⟨C₁, a₁, b₁, rfl, sC₁, sa₁, sb₁⟩ := Join.id_normal empty_root (Join.star_right empty_root jP star₁) normal₁
      obtain ⟨C₂, a₂, b₂, rfl, sC₂, sa₂, sb₂⟩ := Join.id_normal empty_root (Join.star_right empty_root jQ star₂) normal₂
      obtain ⟨w₁, _, tN₁⟩ := isType_reduct formed path₁ tP
      obtain ⟨w₂, _, tN₂⟩ := isType_reduct formed path₂ tQ
      obtain ⟨u₁, tC₁, hu₁, ta₁, tb₁, _⟩ := Typed.generation tN₁
      obtain ⟨u₂, tC₂, hu₂, ta₂, tb₂, _⟩ := Typed.generation tN₂
      obtain ⟨g₁, c₁, computed₁⟩ := (ihA : TypesRealized _ _ _) formed joined (Join.of_star sC₁) (Join.of_star sC₂)
        ⟨u₁, hu₁, tC₁⟩ ⟨u₂, hu₂, tC₂⟩
      have carriers := types_typeEq c₁.down formed ⟨u₁, hu₁, tC₁⟩ ⟨u₂, hu₂, tC₂⟩
      obtain ⟨g₂, c₂, computed₂⟩ := (ihx : TermsRealized _ _ _ _) formed joined (Join.of_star sa₁) (Join.of_star sa₂)
        (Join.of_star sC₁) ta₁ (Typed.convType ta₂ (TypeEq.symm carriers))
      obtain ⟨g₃, c₃, computed₃⟩ := (ihy : TermsRealized _ _ _ _) formed joined (Join.of_star sb₁) (Join.of_star sb₂)
        (Join.of_star sC₁) tb₁ (Typed.convType tb₂ (TypeEq.symm carriers))
      exact ⟨f₁ + f₂ + g₁ + g₂ + g₃ + 1, types_id (stable₁ _ (by omega)) (stable₂ _ (by omega))
        ⟨_, types_mono computed₁ (by omega)⟩ ⟨_, compare_mono computed₂ (by omega)⟩
        ⟨_, compare_mono computed₃ (by omega)⟩⟩
  | inductiveType role => cases role
  | @neutralTypes n Γ A B u neutralA _ _ _ ih =>
      intro Γ' P Q formed joined jP jQ tP tQ
      obtain ⟨f₁, N₁, normal₁, star₁, stable₁⟩ := red_eventually_type formed tP
      obtain ⟨f₂, N₂, normal₂, star₂, stable₂⟩ := red_eventually_type formed tQ
      have sA : Star (R := LevelTower.rules L) A N₁.val := normal₁.star_of_join (Join.star_right empty_root jP star₁)
      have sB : Star (R := LevelTower.rules L) B N₂.val := normal₂.star_of_join (Join.star_right empty_root jQ star₂)
      obtain ⟨w₁, _, tN₁⟩ := isType_reduct formed N₁.property tP
      obtain ⟨w₂, _, tN₂⟩ := isType_reduct formed N₂.property tQ
      obtain ⟨g, T, c, computed, _⟩ := (ih : SpinesRealized _ _ _ _) formed joined sA sB normal₁ normal₂
        ⟨_, tN₁⟩ ⟨_, tN₂⟩
      exact ⟨f₁ + f₂ + g + 1, types_elim (stable₁ _ (by omega)) (stable₂ _ (by omega))
        ((neutral_elim neutralA).star empty_root sA) ⟨_, neutral_mono computed (by omega)⟩⟩
  | terms redA _ redt redu _ ih =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      exact (ih : TermsRealized _ _ _ _) formed joined (Join.star_left empty_root (whRed_star redt.red) jt)
        (Join.star_left empty_root (whRed_star redu.red) ju) (Join.star_left empty_root (whRed_star redA.red) jP) tt tu
  | @univ n Γ t u h hh _ _ _ ih =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      have tP := isType_of_typed formed tt
      obtain ⟨f, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed tP
      obtain rfl := Join.head_normal empty_root (Join.star_right empty_root jP star) normal
      have change := typeEq_reduct formed path tP
      obtain ⟨g, c, computed⟩ := (ih : TypesRealized _ _ _) formed joined jt ju ⟨h, hh, Typed.convType tt change⟩
        ⟨h, hh, Typed.convType tu change⟩
      exact ⟨f + g + 1, compare_universe hh (stable _ (by omega)) ⟨_, types_mono computed (by omega)⟩⟩
  | @eta n Γ f g A B _ _ _ _ _ _ ih =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      have tP := isType_of_typed formed tt
      obtain ⟨fuel₀, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed tP
      obtain ⟨D, E, rfl, sD, sE⟩ := Join.pi_normal empty_root (Join.star_right empty_root jP star) normal
      have change := typeEq_reduct formed path tP
      obtain ⟨⟨u₁, hu₁, tD⟩, _⟩ := IsType.pi_parts (isType_reduct formed path tP)
      obtain ⟨g₁, c, computed⟩ := (ih : TermsRealized _ _ _ _) (.snoc formed ⟨u₁, hu₁, tD⟩)
        (joined.snoc (Join.of_star sD)) (Join.app (Join.rename wk jt) (Join.refl _))
        (Join.app (Join.rename wk ju) (Join.refl _)) (Join.of_star sE)
        (app_var_typed (Typed.convType tt change)) (app_var_typed (Typed.convType tu change))
      exact ⟨fuel₀ + g₁ + 1, compare_pi (stable _ (by omega)) ⟨_, compare_mono computed (by omega)⟩⟩
  | @sigmaEta n Γ p q A B _ _ _ _ _ _ ihFst ihSnd =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      have tP := isType_of_typed formed tt
      obtain ⟨fuel₀, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed tP
      obtain ⟨D, E, rfl, sD, sE⟩ := Join.sigma_normal empty_root (Join.star_right empty_root jP star) normal
      have change := typeEq_reduct formed path tP
      have tt' := Typed.convType tt change
      have tu' := Typed.convType tu change
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts (isType_reduct formed path tP)
      obtain ⟨g₁, c₁, computed₁⟩ := (ihFst : TermsRealized _ _ _ _) formed joined (Join.fst jt) (Join.fst ju)
        (Join.of_star sD) (.fstElim tt') (.fstElim tu')
      have firsts := compare_equal c₁.down formed (.fstElim tt') (.fstElim tu')
      have sndChange := TypeEq.symm (TypeEq.of_instantiateEq family hv (.fstElim tt') firsts)
      obtain ⟨g₂, c₂, computed₂⟩ := (ihSnd : TermsRealized _ _ _ _) formed joined (Join.snd jt) (Join.snd ju)
        (Join.inst0 (Join.fst jt) (Join.of_star sE)) (.sndElim tt') (Typed.convType (.sndElim tu') sndChange)
      exact ⟨fuel₀ + g₁ + g₂ + 1, compare_sigma (stable _ (by omega)) ⟨_, compare_mono computed₁ (by omega)⟩
        ⟨_, compare_mono computed₂ (by omega)⟩⟩
  | @refl n Γ x x' A a b _ _ _ ih =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      have tP := isType_of_typed formed tt
      obtain ⟨fuel₀, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed tP
      obtain ⟨C, a₁, b₁, rfl, sC, _, _⟩ := Join.id_normal empty_root (Join.star_right empty_root jP star) normal
      have change := typeEq_reduct formed path tP
      obtain ⟨fuel₁, ⟨codet, patht⟩, normalt, start, stablet⟩ := red_eventually formed tt
      obtain ⟨fuel₂, ⟨codeu, pathu⟩, normalu, staru, stableu⟩ := red_eventually formed tu
      obtain ⟨x₁, rfl, sx₁⟩ := Join.refl_normal empty_root (Join.star_right empty_root jt start) normalt
      obtain ⟨x₂, rfl, sx₂⟩ := Join.refl_normal empty_root (Join.star_right empty_root ju staru) normalu
      have tx₁ := refl_subject formed (typed_reduct formed patht (Typed.convType tt change))
      have tx₂ := refl_subject formed (typed_reduct formed pathu (Typed.convType tu change))
      obtain ⟨g, c, computed⟩ := (ih : TermsRealized _ _ _ _) formed joined (Join.of_star sx₁) (Join.of_star sx₂)
        (Join.of_star sC) tx₁ tx₂
      exact ⟨fuel₀ + fuel₁ + fuel₂ + g + 1, compare_refl (stable _ (by omega)) (stablet _ (by omega))
        (stableu _ (by omega)) ⟨_, compare_mono computed (by omega)⟩⟩
  | @spine n Γ t u A U spineType _ _ _ _ inner ih =>
      intro Γ' t' u' P formed joined jt ju jP tt tu
      have tP := isType_of_typed formed tt
      obtain ⟨fuel₀, N, normal, star, stable⟩ := red_eventually_type formed tP
      obtain ⟨fuel₁, M₁, normal₁, star₁, stable₁⟩ := red_eventually formed tt
      obtain ⟨fuel₂, M₂, normal₂, star₂, stable₂⟩ := red_eventually formed tu
      obtain ⟨elimt, _⟩ := spine_elim inner Γ t u U (.inr rfl)
      have st : Star (R := LevelTower.rules L) t M₁.val := normal₁.star_of_join (Join.star_right empty_root jt star₁)
      have su : Star (R := LevelTower.rules L) u M₂.val := normal₂.star_of_join (Join.star_right empty_root ju star₂)
      obtain ⟨g, T, c, computed, _⟩ := (ih : SpinesRealized _ _ _ _) formed joined st su normal₁ normal₂
        ⟨_, typed_reduct formed M₁.property tt⟩ ⟨_, typed_reduct formed M₂.property tu⟩
      have neutralOk : Ok (compareNeutral (LevelTower.rules L) red (fuel₀ + fuel₁ + fuel₂ + g + 1) Γ' t' u' P) :=
        compareNeutral_of (stable₁ _ (by omega)) (stable₂ _ (by omega)) ⟨_, neutral_mono computed (by omega)⟩
      have jN : Join (LevelTower.rules L) A N.val := Join.star_right empty_root jP star
      refine ⟨fuel₀ + fuel₁ + fuel₂ + g + 2, ?_⟩
      rcases spineType with ⟨C, a, b, rfl⟩ | neutralA | ⟨T₀, ctors, role, rfl⟩ | ⟨h, rfl, notUniverse⟩
      · obtain ⟨code, path⟩ := N
        obtain ⟨C', a', b', rfl, _, _, _⟩ := Join.id_normal empty_root jN normal
        exact compare_id_elim (stable _ (by omega)) (stable₁ _ (by omega)) (stable₂ _ (by omega))
          (elimt.star empty_root st) neutralOk
      · exact compare_elim ((neutral_elim neutralA).star empty_root (normal.star_of_join jN)) (stable _ (by omega))
          neutralOk
      · cases role
      · obtain ⟨code, path⟩ := N
        obtain rfl := Join.head_normal empty_root jN normal
        exact compare_ground notUniverse (stable _ (by omega)) neutralOk
  | var i =>
      intro Γ' t' u' formed joined st su _ _ _ _
      obtain rfl := star_var_inv empty_root st
      obtain rfl := star_var_inv empty_root su
      obtain ⟨c, computed⟩ := neutral_var (L := L) (fuel := 0) (Γ := Γ') i
      exact ⟨1, _, c, computed, joined i⟩
  | const declared => cases declared
  | @app n Γ f g a b A B functions _ ihf iha =>
      intro Γ' t' u' formed joined st su normalt normalu ⟨X, tt⟩ ⟨Y, tu⟩
      obtain ⟨elimf, elimg⟩ := spine_elim functions Γ f g _ (.inr rfl)
      obtain ⟨f₁, a₁, rfl, sf, sa, _⟩ := star_app_inv empty_root elimf st
      obtain ⟨g₁, b₁, rfl, sg, sb, _⟩ := star_app_inv empty_root elimg su
      obtain ⟨A₀, B₀, tf₁, ta₁, _⟩ := Typed.generation tt
      obtain ⟨A₁, B₁, tg₁, tb₁, _⟩ := Typed.generation tu
      obtain ⟨fuel₁, T, c, computed, jT⟩ := (ihf : SpinesRealized _ _ _ _) formed joined sf sg
        normalt.app_function normalu.app_function ⟨_, tf₁⟩ ⟨_, tg₁⟩
      obtain ⟨tfT, _, leF, leG⟩ := neutral_sound c.down formed tf₁ tg₁
      have tT := isType_of_typed formed tfT
      obtain ⟨fuel₂, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed tT
      obtain ⟨D, E, rfl, sD, sE⟩ := Join.pi_normal empty_root (Join.star_right empty_root jT star) normal
      obtain ⟨s, hs, tTs⟩ := tT
      have equal : Equal (LevelTower.rules L) Γ' T (.pi D E) (.head s) :=
        (Reduces.preserve (S := TS) TowerModel.facts TowerModel.roots TowerModel.heads formed path tTs).2
      have domain₀ := (TypeLe.pi_parts_of_equal (S := TS) TowerModel.facts formed hs equal (leF tf₁)
        (isType_of_typed formed tf₁)).1
      have domain₁ := (TypeLe.pi_parts_of_equal (S := TS) TowerModel.facts formed hs equal (leG tg₁)
        (isType_of_typed formed tg₁)).1
      obtain ⟨fuel₃, c', computed'⟩ := (iha : TermsRealized _ _ _ _) formed joined (Join.of_star sa) (Join.of_star sb)
        (Join.of_star sD) (Typed.convType ta₁ (TypeEq.symm domain₀)) (Typed.convType tb₁ (TypeEq.symm domain₁))
      obtain ⟨certificate, result⟩ := neutral_app (fuel := fuel₁ + fuel₂ + fuel₃) (neutral_mono computed (by omega))
        (stable _ (by omega)) ⟨_, compare_mono computed' (by omega)⟩
      exact ⟨_, _, certificate, result, Join.inst0 (Join.of_star sa) (Join.of_star sE)⟩
  | @fst n Γ p q A B pairs ih =>
      intro Γ' t' u' formed joined st su normalt normalu ⟨X, tt⟩ ⟨Y, tu⟩
      obtain ⟨elimp, elimq⟩ := spine_elim pairs Γ p q _ (.inr rfl)
      obtain ⟨p₁, rfl, sp, _⟩ := star_fst_inv empty_root elimp st
      obtain ⟨q₁, rfl, sq, _⟩ := star_fst_inv empty_root elimq su
      obtain ⟨A₀, B₀, tp₁, _⟩ := Typed.generation tt
      obtain ⟨A₁, B₁, tq₁, _⟩ := Typed.generation tu
      obtain ⟨fuel₁, T, c, computed, jT⟩ := (ih : SpinesRealized _ _ _ _) formed joined sp sq
        normalt.fst_pair normalu.fst_pair ⟨_, tp₁⟩ ⟨_, tq₁⟩
      obtain ⟨tpT, _, _, _⟩ := neutral_sound c.down formed tp₁ tq₁
      obtain ⟨fuel₂, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed (isType_of_typed formed tpT)
      obtain ⟨D, E, rfl, sD, _⟩ := Join.sigma_normal empty_root (Join.star_right empty_root jT star) normal
      obtain ⟨certificate, result⟩ := neutral_fst (fuel := fuel₁ + fuel₂) (neutral_mono computed (by omega))
        (stable _ (by omega))
      exact ⟨_, _, certificate, result, Join.of_star sD⟩
  | @snd n Γ p q A B pairs ih =>
      intro Γ' t' u' formed joined st su normalt normalu ⟨X, tt⟩ ⟨Y, tu⟩
      obtain ⟨elimp, elimq⟩ := spine_elim pairs Γ p q _ (.inr rfl)
      obtain ⟨p₁, rfl, sp, _⟩ := star_snd_inv empty_root elimp st
      obtain ⟨q₁, rfl, sq, _⟩ := star_snd_inv empty_root elimq su
      obtain ⟨A₀, B₀, tp₁, _⟩ := Typed.generation tt
      obtain ⟨A₁, B₁, tq₁, _⟩ := Typed.generation tu
      obtain ⟨fuel₁, T, c, computed, jT⟩ := (ih : SpinesRealized _ _ _ _) formed joined sp sq
        normalt.snd_pair normalu.snd_pair ⟨_, tp₁⟩ ⟨_, tq₁⟩
      obtain ⟨tpT, _, _, _⟩ := neutral_sound c.down formed tp₁ tq₁
      obtain ⟨fuel₂, ⟨code, path⟩, normal, star, stable⟩ := red_eventually_type formed (isType_of_typed formed tpT)
      obtain ⟨D, E, rfl, _, sE⟩ := Join.sigma_normal empty_root (Join.star_right empty_root jT star) normal
      obtain ⟨certificate, result⟩ := neutral_snd (fuel := fuel₁ + fuel₂) (neutral_mono computed (by omega))
        (stable _ (by omega))
      exact ⟨_, _, certificate, result, Join.inst0 (Join.fst (Join.of_star sp)) (Join.of_star sE)⟩
  | spinesW _ redU _ ih =>
      intro Γ' t' u' formed joined st su normalt normalu tt tu
      obtain ⟨fuel, T, c, computed, jT⟩ := (ih : SpinesRealized _ _ _ _) formed joined st su normalt normalu tt tu
      exact ⟨fuel, T, c, computed, Join.star_left empty_root (whRed_star redU.red) jT⟩

/-! ## Eventual success -/

/-- **Executable conversion eventually accepts every tower equality**, and keeps its
certificate at every larger budget. -/
theorem compare_eventually {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t u A : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (equal : Equal (LevelTower.rules L) Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare (LevelTower.rules L) red larger Γ t u A = some certificate := by
  obtain ⟨tt, tu⟩ := Equal.typed (S := TS) equal formed
  obtain ⟨fuel, certificate, computed⟩ := (realized (TowerModel.complete formed equal) : TermsRealized _ _ _ _)
    formed (CtxJoin.refl Γ) (Join.refl t) (Join.refl u) (Join.refl A) tt tu
  exact ⟨fuel, certificate, fun _ enough => compare_mono computed enough⟩

/-- **Executable type comparison eventually accepts every equality of tower types**, and keeps
its certificate at every larger budget. -/
theorem types_eventually {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (equal : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types (LevelTower.rules L) red larger Γ A B = some certificate := by
  obtain ⟨u, hu, e⟩ := equal
  obtain ⟨tA, tB⟩ := Equal.typed (S := TS) e formed
  obtain ⟨fuel, certificate, computed⟩ :=
    (realized (AlgorithmicComplete.types (S := TS) TowerModel.complete ⟨u, hu, e⟩ formed) : TypesRealized _ _ _)
    formed (CtxJoin.refl Γ) (Join.refl A) (Join.refl B) ⟨u, hu, tA⟩ ⟨u, hu, tB⟩
  exact ⟨fuel, certificate, fun _ enough => types_mono computed enough⟩

end Completeness

end ContextualDependentExecutableConversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
