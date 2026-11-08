import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBudget
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# Eventual success of executable checking on normal tower terms

The executable synthesis and checking of the tower, run with the actual normalizer
and the constructed universe choices, succeed at some finite budget on every
normal term of a formed context, and keep their result at every larger budget:

* synthesis succeeds on every normal term the kernel's bidirectional typing
  synthesizes, with a type equal to the kernel's;
* checking succeeds on every normal term against every type it has;
* the executable subtype test succeeds on every declarative subtyping between
  types.

The proof is by structural recursion on the normal term, which is also the
recursion of the executable. At each subterm the kernel's typing is complete, so
a derivation for the executable's own context and expected type is available;
the normalizer's choices are matched through the forms of normal types, and
every conversion test is discharged by eventual success of executable
conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentExecutableChecking

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableChecking ContextualDependentExecutableJoin ContextualDependentExecutableConversion

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- The constructed universe choices of the tower. -/
abbrev tc : HeadChoices (LevelTower.rules L) := ExecutableTowerChoices.choices

section Unfold

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

variable {n : Nat} {fuel : Nat} {Γ : Ctx (LevelTower.Head L) n}

theorem synth_var (i : Fin n) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.var i) = some ⟨Ctx.lookup Γ i, r⟩ :=
  ⟨_, rfl⟩

theorem synth_head (h : LevelTower.Head L) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.head h) =
      some ⟨.head (ExecutableTowerChoices.typing h).val, r⟩ := by
  exact ⟨_, rfl⟩

theorem synth_pi {A : Tm (LevelTower.Head L) n} {B : Tm (LevelTower.Head L) (n + 1)}
    {sA : SynthResult (LevelTower.rules L) Γ A} {sB : SynthResult (LevelTower.rules L) (.snoc Γ A) B}
    {lA : {head : LevelTower.Head L // (LevelTower.rules L).isUniverse head ∧ Reduces (LevelTower.rules L) sA.1 (.head head)}}
    {lB : {head : LevelTower.Head L // (LevelTower.rules L).isUniverse head ∧ Reduces (LevelTower.rules L) sB.1 (.head head)}}
    {joined : {result : LevelTower.Head L // (LevelTower.rules L).join lA.val lB.val result}}
    (hA : synth (LevelTower.rules L) tc red fuel Γ A = some sA)
    (uA : asUniverse (LevelTower.rules L) red (fuel + 1) sA.1 = some lA)
    (hB : synth (LevelTower.rules L) tc red fuel (.snoc Γ A) B = some sB)
    (uB : asUniverse (LevelTower.rules L) red (fuel + 1) sB.1 = some lB)
    (hj : tc.join lA.val lB.val = some joined) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.pi A B) = some ⟨.head joined.val, r⟩ := by
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, hA, Option.bind_some, uA, hB, uB, hj]
  exact ⟨_, rfl⟩

theorem synth_sigma {A : Tm (LevelTower.Head L) n} {B : Tm (LevelTower.Head L) (n + 1)}
    {sA : SynthResult (LevelTower.rules L) Γ A} {sB : SynthResult (LevelTower.rules L) (.snoc Γ A) B}
    {lA : {head : LevelTower.Head L // (LevelTower.rules L).isUniverse head ∧ Reduces (LevelTower.rules L) sA.1 (.head head)}}
    {lB : {head : LevelTower.Head L // (LevelTower.rules L).isUniverse head ∧ Reduces (LevelTower.rules L) sB.1 (.head head)}}
    {joined : {result : LevelTower.Head L // (LevelTower.rules L).join lA.val lB.val result}}
    (hA : synth (LevelTower.rules L) tc red fuel Γ A = some sA)
    (uA : asUniverse (LevelTower.rules L) red (fuel + 1) sA.1 = some lA)
    (hB : synth (LevelTower.rules L) tc red fuel (.snoc Γ A) B = some sB)
    (uB : asUniverse (LevelTower.rules L) red (fuel + 1) sB.1 = some lB)
    (hj : tc.join lA.val lB.val = some joined) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.sigma A B) = some ⟨.head joined.val, r⟩ := by
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, hA, Option.bind_some, uA, hB, uB, hj]
  exact ⟨_, rfl⟩

theorem synth_id {A a b : Tm (LevelTower.Head L) n} {sA : SynthResult (LevelTower.rules L) Γ A}
    {lA : {head : LevelTower.Head L // (LevelTower.rules L).isUniverse head ∧ Reduces (LevelTower.rules L) sA.1 (.head head)}}
    (hA : synth (LevelTower.rules L) tc red fuel Γ A = some sA)
    (uA : asUniverse (LevelTower.rules L) red (fuel + 1) sA.1 = some lA)
    (ha : Ok (check (LevelTower.rules L) tc red fuel Γ a A)) (hb : Ok (check (LevelTower.rules L) tc red fuel Γ b A)) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.id A a b) = some ⟨.head lA.val, r⟩ := by
  obtain ⟨ca, ha⟩ := ha
  obtain ⟨cb, hb⟩ := hb
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, hA, Option.bind_some, uA, ha, hb]
  exact ⟨_, rfl⟩

theorem synth_refl {a : Tm (LevelTower.Head L) n} {sa : SynthResult (LevelTower.rules L) Γ a}
    (ha : synth (LevelTower.rules L) tc red fuel Γ a = some sa) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.refl a) = some ⟨.id sa.1 a a, r⟩ := by
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, ha, Option.bind_some]
  exact ⟨_, rfl⟩

theorem synth_app {f a D : Tm (LevelTower.Head L) n} {E : Tm (LevelTower.Head L) (n + 1)}
    (notLam : ∀ body, f ≠ .lam body) {sf : SynthResult (LevelTower.rules L) Γ f}
    {path : Reduces (LevelTower.rules L) sf.1 (.pi D E)}
    (hf : synth (LevelTower.rules L) tc red fuel Γ f = some sf)
    (normal : red (fuel + 1) sf.1 = some ⟨.pi D E, path⟩)
    (ha : Ok (check (LevelTower.rules L) tc red fuel Γ a D)) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.app f a) = some ⟨inst0 a E, r⟩ := by
  obtain ⟨ca, ha⟩ := ha
  cases f
  all_goals first
    | exact absurd rfl (notLam _)
    | (rw [ExecutableChecking.synth] <;> first
        | (intro _ impossible; cases impossible)
        | (simp only [Option.bind_eq_bind, hf, Option.bind_some, normal, ha]
           exact ⟨_, rfl⟩))

theorem synth_fst {p D : Tm (LevelTower.Head L) n} {E : Tm (LevelTower.Head L) (n + 1)}
    {sp : SynthResult (LevelTower.rules L) Γ p} {path : Reduces (LevelTower.rules L) sp.1 (.sigma D E)}
    (hp : synth (LevelTower.rules L) tc red fuel Γ p = some sp)
    (normal : red (fuel + 1) sp.1 = some ⟨.sigma D E, path⟩) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.fst p) = some ⟨D, r⟩ := by
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, hp, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem synth_snd {p D : Tm (LevelTower.Head L) n} {E : Tm (LevelTower.Head L) (n + 1)}
    {sp : SynthResult (LevelTower.rules L) Γ p} {path : Reduces (LevelTower.rules L) sp.1 (.sigma D E)}
    (hp : synth (LevelTower.rules L) tc red fuel Γ p = some sp)
    (normal : red (fuel + 1) sp.1 = some ⟨.sigma D E, path⟩) :
    ∃ r, synth (LevelTower.rules L) tc red (fuel + 1) Γ (.snd p) = some ⟨inst0 (.fst p) E, r⟩ := by
  rw [ExecutableChecking.synth]
  simp only [Option.bind_eq_bind, hp, Option.bind_some, normal]
  exact ⟨_, rfl⟩

theorem check_lam {body : Tm (LevelTower.Head L) (n + 1)} {E D : Tm (LevelTower.Head L) n}
    {C : Tm (LevelTower.Head L) (n + 1)} {path : Reduces (LevelTower.rules L) E (.pi D C)}
    (normal : red (fuel + 1) E = some ⟨.pi D C, path⟩)
    (inner : Ok (check (LevelTower.rules L) tc red fuel (.snoc Γ D) body C)) :
    Ok (check (LevelTower.rules L) tc red (fuel + 1) Γ (.lam body) E) := by
  obtain ⟨c, computed⟩ := inner
  rw [ExecutableChecking.check]
  simp only [Option.bind_eq_bind, normal, Option.bind_some, computed]
  exact ⟨_, rfl⟩

theorem check_pair {a b E D : Tm (LevelTower.Head L) n} {C : Tm (LevelTower.Head L) (n + 1)}
    {path : Reduces (LevelTower.rules L) E (.sigma D C)}
    (normal : red (fuel + 1) E = some ⟨.sigma D C, path⟩)
    (first : Ok (check (LevelTower.rules L) tc red fuel Γ a D))
    (second : Ok (check (LevelTower.rules L) tc red fuel Γ b (inst0 a C))) :
    Ok (check (LevelTower.rules L) tc red (fuel + 1) Γ (.pair a b) E) := by
  obtain ⟨c, computed⟩ := first
  obtain ⟨c', computed'⟩ := second
  rw [ExecutableChecking.check]
  simp only [Option.bind_eq_bind, normal, Option.bind_some, computed, computed']
  exact ⟨_, rfl⟩

theorem check_refl {x E C a b : Tm (LevelTower.Head L) n} {path : Reduces (LevelTower.rules L) E (.id C a b)}
    (normal : red (fuel + 1) E = some ⟨.id C a b, path⟩)
    (subject : Ok (check (LevelTower.rules L) tc red fuel Γ x C))
    (left : Ok (ExecutableConversion.compare (LevelTower.rules L) red fuel Γ x a C))
    (right : Ok (ExecutableConversion.compare (LevelTower.rules L) red fuel Γ x b C)) :
    Ok (check (LevelTower.rules L) tc red (fuel + 1) Γ (.refl x) E) := by
  obtain ⟨c, computed⟩ := subject
  obtain ⟨c', computed'⟩ := left
  obtain ⟨c'', computed''⟩ := right
  rw [ExecutableChecking.check]
  simp only [Option.bind_eq_bind, normal, Option.bind_some, computed, computed', computed'']
  exact ⟨_, rfl⟩

/-- A term that is not an abstraction, a pair or a reflexivity proof is checked by
synthesis and the subtype test. -/
theorem check_switch {t E : Tm (LevelTower.Head L) n} (notLam : ∀ body, t ≠ .lam body)
    (notPair : ∀ a b, t ≠ .pair a b) (notRefl : ∀ a, t ≠ .refl a) {st : SynthResult (LevelTower.rules L) Γ t}
    (synthesized : synth (LevelTower.rules L) tc red fuel Γ t = some st)
    (usable : Ok (below (LevelTower.rules L) red fuel Γ st.1 E)) :
    Ok (check (LevelTower.rules L) tc red (fuel + 1) Γ t E) := by
  obtain ⟨c, computed⟩ := usable
  cases t
  all_goals first
    | exact absurd rfl (notLam _)
    | exact absurd rfl (notPair _ _)
    | exact absurd rfl (notRefl _)
    | (rw [ExecutableChecking.check] <;> first
        | (intro _ _ impossible; cases impossible)
        | (intro _ impossible; cases impossible)
        | (simp only [Option.bind_eq_bind, synthesized, Option.bind_some, computed]
           exact ⟨_, rfl⟩))

theorem below_conv {A B : Tm (LevelTower.Head L) n}
    (same : Ok (ExecutableConversion.types (LevelTower.rules L) red (fuel + 1) Γ A B)) :
    Ok (below (LevelTower.rules L) red (fuel + 1) Γ A B) := by
  obtain ⟨c, computed⟩ := same
  rw [ExecutableChecking.below, computed]
  exact ⟨_, rfl⟩

theorem below_universes {A B : Tm (LevelTower.Head L) n} {u v : LevelTower.Head L}
    {pathA : Reduces (LevelTower.rules L) A (.head u)} {pathB : Reduces (LevelTower.rules L) B (.head v)}
    (different : ExecutableConversion.types (LevelTower.rules L) red (fuel + 1) Γ A B = none)
    (normalA : red (fuel + 1) A = some ⟨.head u, pathA⟩) (normalB : red (fuel + 1) B = some ⟨.head v, pathB⟩)
    (cumulative : (LevelTower.rules L).cumulative u v) :
    Ok (below (LevelTower.rules L) red (fuel + 1) Γ A B) := by
  rw [ExecutableChecking.below, different]
  simp only [Option.bind_eq_bind, normalA, Option.bind_some, normalB]
  rw [dif_pos cumulative]
  exact ⟨_, rfl⟩

theorem below_pi {A B D D' : Tm (LevelTower.Head L) n} {E E' : Tm (LevelTower.Head L) (n + 1)}
    {pathA : Reduces (LevelTower.rules L) A (.pi D E)} {pathB : Reduces (LevelTower.rules L) B (.pi D' E')}
    (different : ExecutableConversion.types (LevelTower.rules L) red (fuel + 1) Γ A B = none)
    (normalA : red (fuel + 1) A = some ⟨.pi D E, pathA⟩) (normalB : red (fuel + 1) B = some ⟨.pi D' E', pathB⟩)
    (domains : Ok (ExecutableConversion.types (LevelTower.rules L) red fuel Γ D D'))
    (bodies : Ok (below (LevelTower.rules L) red fuel (.snoc Γ D) E E')) :
    Ok (below (LevelTower.rules L) red (fuel + 1) Γ A B) := by
  obtain ⟨c, computed⟩ := domains
  obtain ⟨c', computed'⟩ := bodies
  rw [ExecutableChecking.below, different]
  simp only [Option.bind_eq_bind, normalA, Option.bind_some, normalB, computed, computed']
  exact ⟨_, rfl⟩

theorem below_sigma {A B D D' : Tm (LevelTower.Head L) n} {E E' : Tm (LevelTower.Head L) (n + 1)}
    {pathA : Reduces (LevelTower.rules L) A (.sigma D E)} {pathB : Reduces (LevelTower.rules L) B (.sigma D' E')}
    (different : ExecutableConversion.types (LevelTower.rules L) red (fuel + 1) Γ A B = none)
    (normalA : red (fuel + 1) A = some ⟨.sigma D E, pathA⟩) (normalB : red (fuel + 1) B = some ⟨.sigma D' E', pathB⟩)
    (domains : Ok (below (LevelTower.rules L) red fuel Γ D D'))
    (bodies : Ok (below (LevelTower.rules L) red fuel (.snoc Γ D) E E')) :
    Ok (below (LevelTower.rules L) red (fuel + 1) Γ A B) := by
  obtain ⟨c, computed⟩ := domains
  obtain ⟨c', computed'⟩ := bodies
  rw [ExecutableChecking.below, different]
  simp only [Option.bind_eq_bind, normalA, Option.bind_some, normalB, computed, computed']
  exact ⟨_, rfl⟩

end Unfold

/-! ## Normal forms of types -/

section Forms

local notation "TS" => TowerModel.setting (L := L) (fun _ => UniverseLevel.LevelOrder.bot)

variable {n : Nat} {Γ : Ctx (LevelTower.Head L) n}

theorem step_none_of_normal {t : Tm (LevelTower.Head L) n} (normal : Normal (LevelTower.rules L) t) :
    ExecutableReduction.step (LevelTower.rules L) (fun _ => none) t = none := by
  cases computed : ExecutableReduction.step (LevelTower.rules L) (fun _ => none) t with
  | none => rfl
  | some next =>
      exact absurd (ContextualDependentReductionBudget.step_directed (LevelTower.rules L) _ t next computed)
        (normal _)

/-- A normal term is returned unchanged at every positive budget. -/
theorem red_normal {t : Tm (LevelTower.Head L) n} (normal : Normal (LevelTower.rules L) t) (fuel : Nat) :
    red (fuel + 1) t = some ⟨t, .refl⟩ := by
  simp only [red, ExecutableReduction.normalize, step_none_of_normal normal]

theorem normal_typeForm (formed : CtxFormed (LevelTower.rules L) Γ) {N : Tm (LevelTower.Head L) n}
    (normal : Normal (LevelTower.rules L) N) (isType : IsType (LevelTower.rules L) Γ N) :
    IsTypeForm (TowerModel.roles (L := L)) N := by
  obtain ⟨N', reduced, form⟩ := TowerModel.facts.typeForm isType formed
  rw [normal.star_eq (whRed_star reduced.red)] at form
  exact form

/-- The normal form of a type, reached at a threshold and kept above it. -/
theorem type_normal (formed : CtxFormed (LevelTower.rules L) Γ) {T : Tm (LevelTower.Head L) n}
    (isType : IsType (LevelTower.rules L) Γ T) :
    ∃ fuel N, Normal (LevelTower.rules L) N.val ∧ TypeEq (LevelTower.rules L) Γ T N.val ∧
      IsType (LevelTower.rules L) Γ N.val ∧ ∀ larger, fuel ≤ larger → red larger T = some N := by
  obtain ⟨fuel, N, normal, _, stable⟩ := red_eventually_type formed isType
  exact ⟨fuel, N, normal, typeEq_reduct formed N.property isType, isType_reduct formed N.property isType, stable⟩

theorem forms_match (formed : CtxFormed (LevelTower.rules L) Γ) {X N : Tm (LevelTower.Head L) n}
    (equal : TypeEq (LevelTower.rules L) Γ X N) (form : IsTypeForm (TowerModel.roles (L := L)) X)
    (normal : Normal (LevelTower.rules L) N) (isType : IsType (LevelTower.rules L) Γ N) :
    FormsMatch (LevelTower.rules L) (TowerModel.roles (L := L)) Γ X N :=
  TowerModel.facts.forms equal formed form (normal_typeForm formed normal isType)

theorem headSame_typeEq {w w' : LevelTower.Head L} (same : HeadSame (LevelTower.rules L) w w')
    (hw : (LevelTower.rules L).isUniverse w) : TypeEq (LevelTower.rules L) Γ (.head w) (.head w') := by
  rcases same with rfl | equal
  · exact IsType.refl (IsType.head_of_universe (S := TS) hw)
  · obtain ⟨s, hs, typed⟩ := IsType.head_of_universe (S := TS) (Γ := Γ) hw
    exact ⟨s, hs, .headEq equal typed (TowerModel.heads equal typed)⟩

theorem headSame_eval {l l' : UniverseLevel.LevelExpr L}
    (same : HeadSame (LevelTower.rules L) (.sort l) (.sort l')) (valuation : Nat → L) :
    UniverseLevel.LevelExpr.eval valuation l = UniverseLevel.LevelExpr.eval valuation l' := by
  rcases same with same | same
  · cases same
    rfl
  · exact same valuation

/-- Joins of the same universes are the same universe. -/
theorem join_same {u u' v v' w w' : LevelTower.Head L} (left : HeadSame (LevelTower.rules L) u u')
    (right : HeadSame (LevelTower.rules L) v v') (joined : (LevelTower.rules L).join u v w)
    (joined' : (LevelTower.rules L).join u' v' w') : HeadSame (LevelTower.rules L) w w' := by
  cases joined with
  | sorts l r =>
      cases joined' with
      | sorts l' r' =>
          right
          intro valuation
          simp only [UniverseLevel.LevelExpr.eval, headSame_eval left valuation, headSame_eval right valuation]

variable [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] in
/-- The universe test eventually recognizes a type equal to a universe. -/
theorem asUniverse_eventually (formed : CtxFormed (LevelTower.rules L) Γ) {T : Tm (LevelTower.Head L) n}
    (isType : IsType (LevelTower.rules L) Γ T) {u : LevelTower.Head L} (hu : (LevelTower.rules L).isUniverse u)
    (equal : TypeEq (LevelTower.rules L) Γ (.head u) T) :
    ∃ fuel, ∀ larger, fuel ≤ larger → ∃ result,
      asUniverse (LevelTower.rules L) red larger T = some result ∧ HeadSame (LevelTower.rules L) u result.val := by
  obtain ⟨fuel, ⟨code, path⟩, normal, toCode, codeType, stable⟩ := type_normal formed isType
  obtain ⟨h', rfl, same⟩ :=
    (forms_match formed (TypeEq.trans (TS).levels equal toCode) (.inl ⟨u, rfl⟩) normal codeType).head_left
  have hh' : (LevelTower.rules L).isUniverse h' := ((HeadSame.level (TS).levels same).1).mp hu
  refine ⟨fuel, fun larger enough => ⟨⟨h', hh', path⟩, ?_, same⟩⟩
  rw [ExecutableChecking.asUniverse, stable larger enough]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [dif_pos hh']

end Forms

/-! ## The subtype test -/

section Below

local notation "TS" => TowerModel.setting (L := L) (fun _ => UniverseLevel.LevelOrder.bot)

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

theorem below_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {first second : Tm (LevelTower.Head L) n}
    {result : PLift (BelowAlgorithm (LevelTower.rules L) Γ first second)}
    (accepted : below (LevelTower.rules L) red fuel Γ first second = some result) (enough : fuel ≤ larger) :
    below (LevelTower.rules L) red larger Γ first second = some result :=
  ContextualDependentCheckingBudget.below_success_mono (LevelTower.rules L) red
    (ContextualDependentConversionBudget.normalizer_stable (LevelTower.rules L) (fun _ => none)) accepted enough

/-- Equal types pass the subtype test by conversion. -/
theorem below_of_typeEq {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (equal : TypeEq (LevelTower.rules L) Γ A B) :
    ∃ fuel, Ok (below (LevelTower.rules L) red fuel Γ A B) := by
  obtain ⟨fuel, certificate, stable⟩ := types_eventually formed equal
  exact ⟨fuel + 1, below_conv ⟨_, stable (fuel + 1) (Nat.le_succ fuel)⟩⟩

/-- Below a type whose normal form is not a universe, a function type or a pair type,
subtyping is equality. -/
theorem below_rigid {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B N : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (le : Below (LevelTower.rules L) Γ A B)
    (toN : TypeEq (LevelTower.rules L) Γ A N) (normal : Normal (LevelTower.rules L) N)
    (isType : IsType (LevelTower.rules L) Γ N)
    (notHead : ∀ h, (LevelTower.rules L).isUniverse h → N ≠ .head h)
    (notPi : ∀ D E, N ≠ .pi D E) (notSigma : ∀ D E, N ≠ .sigma D E) :
    ∃ fuel, Ok (below (LevelTower.rules L) red fuel Γ A B) := by
  refine below_of_typeEq formed (Below.rigid (S := TS) le formed ?_ ?_ ?_)
  · intro u hu toHead
    obtain ⟨h', same, headSame⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toHead) toN)
      (.inl ⟨u, rfl⟩) normal isType).head_left
    exact notHead h' (((HeadSame.level (TS).levels headSame).1).mp hu) same
  · intro D E toPi
    obtain ⟨D', E', same, _⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toPi) toN)
      (.inr (.inl ⟨D, E, rfl⟩)) normal isType).pi_left
    exact notPi D' E' same
  · intro D E toSigma
    obtain ⟨D', E', same, _⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toSigma) toN)
      (.inr (.inr (.inl ⟨D, E, rfl⟩))) normal isType).sigma_left
    exact notSigma D' E' same

/-- **The executable subtype test eventually accepts every declarative subtyping**
between types, by recursion on the normal form of the lower type. -/
theorem below_eventually : ∀ {n : Nat} (N : Tm (LevelTower.Head L) n) {Γ : Ctx (LevelTower.Head L) n}
    {A B : Tm (LevelTower.Head L) n} {pathA : Reduces (LevelTower.rules L) A N},
    CtxFormed (LevelTower.rules L) Γ → Below (LevelTower.rules L) Γ A B →
    IsType (LevelTower.rules L) Γ A → IsType (LevelTower.rules L) Γ B →
    (∃ fuel, ∀ larger, fuel ≤ larger → red larger A = some ⟨N, pathA⟩) → Normal (LevelTower.rules L) N →
    ∃ fuel, Ok (below (LevelTower.rules L) red fuel Γ A B) := by
  intro n N
  induction N with
  | head u =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      have toN := typeEq_reduct formed pathA tA
      have tN := isType_reduct formed pathA tA
      by_cases hu : (LevelTower.rules L).isUniverse u
      · obtain ⟨fB, ⟨M, pathB⟩, normalM, toM, tM, stableB⟩ := type_normal formed tB
        obtain ⟨v, hv, toV, cumulative⟩ :=
          Below.universe_cumulative (S := TS) TowerModel.facts TowerModel.algebra le formed hu toN
        obtain ⟨v', rfl, same⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toV) toM)
          (.inl ⟨v, rfl⟩) normalM tM).head_left
        refine ⟨fA + fB + 1, ?_⟩
        cases different : ExecutableConversion.types (LevelTower.rules L) red (fA + fB + 1) Γ A B with
        | some certificate => exact below_conv ⟨_, different⟩
        | none =>
            exact below_universes different (stableA _ (by omega)) (stableB _ (by omega))
              (TowerModel.algebra.same_right cumulative same)
      · exact below_rigid formed le toN normal tN (fun h hh same => by cases same; exact hu hh)
          (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | pi D E _ ihE =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      have toN := typeEq_reduct formed pathA tA
      obtain ⟨⟨u₁, hu₁, tD⟩, v₁, hv₁, tE⟩ := IsType.pi_parts (isType_reduct formed pathA tA)
      obtain ⟨fB, ⟨M, pathB⟩, normalM, toM, tM, stableB⟩ := type_normal formed tB
      obtain ⟨A', B', toPi, domains, bodies⟩ := Below.pi_source (S := TS) TowerModel.facts le formed toN
      obtain ⟨D₂, E₂, rfl, domains', bodies'⟩ := (forms_match formed
        (TypeEq.trans (TS).levels (TypeEq.symm toPi) toM) (.inr (.inl ⟨A', B', rfl⟩)) normalM tM).pi_left
      obtain ⟨⟨u₂, hu₂, tD₂⟩, v₂, hv₂, tE₂⟩ := IsType.pi_parts tM
      have sameDomains : TypeEq (LevelTower.rules L) Γ D D₂ := TypeEq.trans (TS).levels domains domains'
      obtain ⟨g₁, c₁, stable₁⟩ := types_eventually formed sameDomains
      obtain ⟨w, hw, bodiesEqual⟩ := bodies'
      have bodiesBelow : Below (LevelTower.rules L) (.snoc Γ D) E E₂ :=
        .subTrans bodies (TypeEq.below ⟨w, hw, Equal.ctxConv bodiesEqual (TypeEq.symm domains)⟩)
      obtain ⟨g₂, c₂, computed₂⟩ := ihE (pathA := .refl) (.snoc formed ⟨u₁, hu₁, tD⟩) bodiesBelow ⟨v₁, hv₁, tE⟩
        ⟨v₂, hv₂, Typed.ctxConv tE₂ (TypeEq.symm sameDomains)⟩
        ⟨1, fun larger enough => by
          obtain ⟨k, rfl⟩ : ∃ k, larger = k + 1 := ⟨larger - 1, by omega⟩
          exact red_normal (fun _ step => normal _ (.congPiCod step)) k⟩
        (fun _ step => normal _ (.congPiCod step))
      refine ⟨fA + fB + g₁ + g₂ + 1, ?_⟩
      cases different : ExecutableConversion.types (LevelTower.rules L) red (fA + fB + g₁ + g₂ + 1) Γ A B with
      | some certificate => exact below_conv ⟨_, different⟩
      | none =>
          exact below_pi different (stableA _ (by omega)) (stableB _ (by omega))
            ⟨_, stable₁ _ (by omega)⟩ ⟨_, below_mono computed₂ (by omega)⟩
  | sigma D E ihD ihE =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      have toN := typeEq_reduct formed pathA tA
      obtain ⟨⟨u₁, hu₁, tD⟩, v₁, hv₁, tE⟩ := IsType.sigma_parts (isType_reduct formed pathA tA)
      obtain ⟨fB, ⟨M, pathB⟩, normalM, toM, tM, stableB⟩ := type_normal formed tB
      obtain ⟨A', B', toSigma, domains, bodies⟩ := Below.sigma_source (S := TS) TowerModel.facts le formed toN
      obtain ⟨D₂, E₂, rfl, domains', bodies'⟩ := (forms_match formed
        (TypeEq.trans (TS).levels (TypeEq.symm toSigma) toM) (.inr (.inr (.inl ⟨A', B', rfl⟩))) normalM tM).sigma_left
      obtain ⟨⟨u₂, hu₂, tD₂⟩, v₂, hv₂, tE₂⟩ := IsType.sigma_parts tM
      have domainsBelow : Below (LevelTower.rules L) Γ D D₂ := .subTrans domains (TypeEq.below domains')
      obtain ⟨w, hw, bodiesEqual⟩ := bodies'
      have bodiesEqual' : Equal (LevelTower.rules L) (.snoc Γ D) B' E₂ (.head w) := by
        simpa using Derivable.substitutes bodiesEqual (SubstMor.ctxBelow domains)
      have bodiesBelow : Below (LevelTower.rules L) (.snoc Γ D) E E₂ :=
        .subTrans bodies (TypeEq.below ⟨w, hw, bodiesEqual'⟩)
      obtain ⟨g₁, c₁, computed₁⟩ := ihD (pathA := .refl) formed domainsBelow ⟨u₁, hu₁, tD⟩ ⟨u₂, hu₂, tD₂⟩
        ⟨1, fun larger enough => by
          obtain ⟨k, rfl⟩ : ∃ k, larger = k + 1 := ⟨larger - 1, by omega⟩
          exact red_normal (fun _ step => normal _ (.congSigmaDom step)) k⟩
        (fun _ step => normal _ (.congSigmaDom step))
      obtain ⟨g₂, c₂, computed₂⟩ := ihE (pathA := .refl) (.snoc formed ⟨u₁, hu₁, tD⟩) bodiesBelow ⟨v₁, hv₁, tE⟩
        ⟨v₂, hv₂, Typed.ctxBelow tE₂ domainsBelow⟩
        ⟨1, fun larger enough => by
          obtain ⟨k, rfl⟩ : ∃ k, larger = k + 1 := ⟨larger - 1, by omega⟩
          exact red_normal (fun _ step => normal _ (.congSigmaCod step)) k⟩
        (fun _ step => normal _ (.congSigmaCod step))
      refine ⟨fA + fB + g₁ + g₂ + 1, ?_⟩
      cases different : ExecutableConversion.types (LevelTower.rules L) red (fA + fB + g₁ + g₂ + 1) Γ A B with
      | some certificate => exact below_conv ⟨_, different⟩
      | none =>
          exact below_sigma different (stableA _ (by omega)) (stableB _ (by omega))
            ⟨_, below_mono computed₁ (by omega)⟩ ⟨_, below_mono computed₂ (by omega)⟩
  | var i =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | const name =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | lam body _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | app f a _ _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | pair a b _ _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | fst p _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | snd p _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | id C a b _ _ _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)
  | refl a _ =>
      intro Γ A B pathA formed le tA tB ⟨fA, stableA⟩ normal
      exact below_rigid formed le (typeEq_reduct formed pathA tA) normal (isType_reduct formed pathA tA)
        (fun _ _ same => by cases same) (fun _ _ same => by cases same) (fun _ _ same => by cases same)

end Below

/-! ## Synthesis and checking of normal terms -/

section Realization

local notation "TS" => TowerModel.setting (L := L) (fun _ => UniverseLevel.LevelOrder.bot)

variable [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative]

theorem synth_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {term : Tm (LevelTower.Head L) n}
    {result : SynthResult (LevelTower.rules L) Γ term}
    (accepted : synth (LevelTower.rules L) tc red fuel Γ term = some result) (enough : fuel ≤ larger) :
    synth (LevelTower.rules L) tc red larger Γ term = some result :=
  ContextualDependentCheckingBudget.synth_success_mono (LevelTower.rules L) tc red
    (ContextualDependentConversionBudget.normalizer_stable (LevelTower.rules L) (fun _ => none)) accepted enough

theorem check_mono {n fuel larger : Nat} {Γ : Ctx (LevelTower.Head L) n} {term type : Tm (LevelTower.Head L) n}
    {result : CheckResult (LevelTower.rules L) Γ term type}
    (accepted : check (LevelTower.rules L) tc red fuel Γ term type = some result) (enough : fuel ≤ larger) :
    check (LevelTower.rules L) tc red larger Γ term type = some result :=
  ContextualDependentCheckingBudget.check_success_mono (LevelTower.rules L) tc red
    (ContextualDependentConversionBudget.normalizer_stable (LevelTower.rules L) (fun _ => none)) accepted enough

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem join_some {u v : LevelTower.Head L} (hu : (LevelTower.rules L).isUniverse u)
    (hv : (LevelTower.rules L).isUniverse v) : ∃ joined, tc.join u v = some joined := by
  cases hu
  cases hv
  exact ⟨_, rfl⟩

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem typeEq_of_redTy {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A A' : Tm (LevelTower.Head L) n}
    (reduced : RedTy (LevelTower.rules L) (TowerModel.roles (L := L)) Γ A A') : TypeEq (LevelTower.rules L) Γ A A' := by
  obtain ⟨s, hs, _, _, e⟩ := reduced.sort
  exact ⟨s, hs, e⟩

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem isType_right {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {A B : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (equal : TypeEq (LevelTower.rules L) Γ A B) :
    IsType (LevelTower.rules L) Γ B := by
  obtain ⟨s, hs, e⟩ := equal
  exact ⟨s, hs, (Equal.typed (S := TS) e formed).2⟩

/-- What the executable does on a normal term of a formed context. -/
def Realized {n : Nat} (t : Tm (LevelTower.Head L) n) : Prop :=
  ∀ {Γ : Ctx (LevelTower.Head L) n}, CtxFormed (LevelTower.rules L) Γ → Normal (LevelTower.rules L) t →
    (∀ {T₀ : Tm (LevelTower.Head L) n}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ t T₀ →
      ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ t = some ⟨T, r⟩ ∧ TypeEq (LevelTower.rules L) Γ T₀ T) ∧
    (∀ {E : Tm (LevelTower.Head L) n}, Typed (LevelTower.rules L) Γ t E →
      ∃ fuel, Ok (check (LevelTower.rules L) tc red fuel Γ t E))

/-- A term that is not an introduction is checked through its synthesized type. -/
theorem check_of_synth {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t E : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ) (normal : Normal (LevelTower.rules L) t)
    (notLam : ∀ body, t ≠ .lam body) (notPair : ∀ a b, t ≠ .pair a b) (notRefl : ∀ a, t ≠ .refl a)
    (synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) n}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ t T₀ →
      ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ t = some ⟨T, r⟩ ∧ TypeEq (LevelTower.rules L) Γ T₀ T)
    (typed : Typed (LevelTower.rules L) Γ t E) : ∃ fuel, Ok (check (LevelTower.rules L) tc red fuel Γ t E) := by
  have kernel := ContextualDependentNormalChecking.normal_checked (S := TS) TowerModel.facts TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique formed typed normal
  cases kernel with
  | lamCheck => exact absurd rfl (notLam _)
  | pairCheck => exact absurd rfl (notPair _ _)
  | reflCheck => exact absurd rfl (notRefl _)
  | switch synthesized le =>
      obtain ⟨fuel, T, r, computed, equal⟩ := synthesizes synthesized
      have tT := isType_right formed equal
      have tE := isType_of_typed formed typed
      obtain ⟨g, ⟨N, path⟩, normalN, _, _, stable⟩ := type_normal formed tT
      obtain ⟨h, certificate, below'⟩ := below_eventually N (pathA := path) formed
        (.subTrans (TypeEq.below (TypeEq.symm equal)) le) tT tE ⟨g, stable⟩ normalN
      exact ⟨fuel + h + 1, check_switch notLam notPair notRefl (synth_mono computed (by omega))
        ⟨_, below_mono below' (by omega)⟩⟩

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem synth_principal {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (synthesized : Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ t T) :
    Typed (LevelTower.rules L) Γ t T ∧ ∀ {X}, Typed (LevelTower.rules L) Γ t X → TypeLe (LevelTower.rules L) Γ T X :=
  Synth.principal (S := TS) TowerModel.facts TowerModel.algebra ContextualDependentNormalCheckingTower.head_typing_unique
    synthesized formed

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem check_sound {n : Nat} {Γ : Ctx (LevelTower.Head L) n} {t E : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (checked : Normalization.Check (LevelTower.rules L) (TowerModel.roles (L := L)) Γ t E) : Typed (LevelTower.rules L) Γ t E :=
  Check.sound (S := TS) TowerModel.facts TowerModel.algebra ContextualDependentNormalCheckingTower.head_typing_unique
    checked formed

/-- **Executable synthesis and checking succeed on every normal term**: synthesis with a type
equal to the kernel's, checking against every type of the term. -/
theorem realized {n : Nat} (t : Tm (LevelTower.Head L) n) : Realized t := by
  induction t with
  | var i =>
      intro Γ formed normal
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.var i) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.var i) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized
        obtain ⟨r, computed⟩ := synth_var (L := L) (fuel := 0) (Γ := Γ) i
        exact ⟨1, _, r, computed, IsType.refl (CtxFormed.lookup formed i)⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | const name =>
      intro Γ formed normal
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.const name) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.const name) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | const declared => cases declared
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | head h =>
      intro Γ formed normal
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.head h) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.head h) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | @head _ _ _ u typing =>
            obtain ⟨r, computed⟩ := synth_head (L := L) (fuel := 0) (Γ := Γ) h
            have same : u = (ExecutableTowerChoices.typing h).val := by
              rw [ExecutableTowerChoices.typing_val]
              exact (ExecutableTowerChoices.typing_exact h _).mp typing
            refine ⟨1, _, r, computed, ?_⟩
            rw [← same]
            exact IsType.refl (isType_of_typed formed (.headType typing))
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | pi A B ihA ihB =>
      intro Γ formed normal
      have normalA : Normal (LevelTower.rules L) A := fun _ step => normal _ (.congPiDom step)
      have normalB : Normal (LevelTower.rules L) B := fun _ step => normal _ (.congPiCod step)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.pi A B) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.pi A B) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | pi sA rA hu sB rB hv joined =>
            have toU := typeEq_of_redTy rA
            have tA : Typed (LevelTower.rules L) Γ A (.head _) := Typed.convType (synth_principal formed sA).1 toU
            obtain ⟨f₁, TA, r₁, computed₁, equal₁⟩ := (ihA formed normalA).1 sA
            obtain ⟨g₁, universe₁⟩ := asUniverse_eventually formed (isType_right formed equal₁) hu
              (TypeEq.trans (TS).levels (TypeEq.symm toU) equal₁)
            have formedA : CtxFormed (LevelTower.rules L) (.snoc Γ A) := .snoc formed ⟨_, hu, tA⟩
            obtain ⟨f₂, TB, r₂, computed₂, equal₂⟩ := (ihB formedA normalB).1 sB
            obtain ⟨g₂, universe₂⟩ := asUniverse_eventually formedA (isType_right formedA equal₂) hv
              (TypeEq.trans (TS).levels (TypeEq.symm (typeEq_of_redTy rB)) equal₂)
            obtain ⟨l₁, level₁, same₁⟩ := universe₁ (f₁ + f₂ + g₁ + g₂ + 1) (by omega)
            obtain ⟨l₂, level₂, same₂⟩ := universe₂ (f₁ + f₂ + g₁ + g₂ + 1) (by omega)
            obtain ⟨j, hj⟩ := join_some l₁.property.1 l₂.property.1
            obtain ⟨r, computed⟩ := synth_pi (synth_mono computed₁ (Nat.le_add_right_of_le (by omega)))
              level₁ (synth_mono computed₂ (by omega)) level₂ hj
            exact ⟨_, _, r, computed, headSame_typeEq (join_same same₁ same₂ joined j.property)
              (((TS).levels.join_level joined).1)⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | sigma A B ihA ihB =>
      intro Γ formed normal
      have normalA : Normal (LevelTower.rules L) A := fun _ step => normal _ (.congSigmaDom step)
      have normalB : Normal (LevelTower.rules L) B := fun _ step => normal _ (.congSigmaCod step)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.sigma A B) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.sigma A B) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | sigma sA rA hu sB rB hv joined =>
            have toU := typeEq_of_redTy rA
            have tA : Typed (LevelTower.rules L) Γ A (.head _) := Typed.convType (synth_principal formed sA).1 toU
            obtain ⟨f₁, TA, r₁, computed₁, equal₁⟩ := (ihA formed normalA).1 sA
            obtain ⟨g₁, universe₁⟩ := asUniverse_eventually formed (isType_right formed equal₁) hu
              (TypeEq.trans (TS).levels (TypeEq.symm toU) equal₁)
            have formedA : CtxFormed (LevelTower.rules L) (.snoc Γ A) := .snoc formed ⟨_, hu, tA⟩
            obtain ⟨f₂, TB, r₂, computed₂, equal₂⟩ := (ihB formedA normalB).1 sB
            obtain ⟨g₂, universe₂⟩ := asUniverse_eventually formedA (isType_right formedA equal₂) hv
              (TypeEq.trans (TS).levels (TypeEq.symm (typeEq_of_redTy rB)) equal₂)
            obtain ⟨l₁, level₁, same₁⟩ := universe₁ (f₁ + f₂ + g₁ + g₂ + 1) (by omega)
            obtain ⟨l₂, level₂, same₂⟩ := universe₂ (f₁ + f₂ + g₁ + g₂ + 1) (by omega)
            obtain ⟨j, hj⟩ := join_some l₁.property.1 l₂.property.1
            obtain ⟨r, computed⟩ := synth_sigma (synth_mono computed₁ (Nat.le_add_right_of_le (by omega)))
              level₁ (synth_mono computed₂ (by omega)) level₂ hj
            exact ⟨_, _, r, computed, headSame_typeEq (join_same same₁ same₂ joined j.property)
              (((TS).levels.join_level joined).1)⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | id A a b ihA iha ihb =>
      intro Γ formed normal
      have normalA : Normal (LevelTower.rules L) A := fun _ step => normal _ (.congIdTy step)
      have normala : Normal (LevelTower.rules L) a := fun _ step => normal _ (.congIdLeft step)
      have normalb : Normal (LevelTower.rules L) b := fun _ step => normal _ (.congIdRight step)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.id A a b) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.id A a b) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | id sA rA hu ca cb =>
            obtain ⟨f₁, TA, r₁, computed₁, equal₁⟩ := (ihA formed normalA).1 sA
            obtain ⟨g₁, universe₁⟩ := asUniverse_eventually formed (isType_right formed equal₁) hu
              (TypeEq.trans (TS).levels (TypeEq.symm (typeEq_of_redTy rA)) equal₁)
            obtain ⟨f₂, checked₂⟩ := (iha formed normala).2 (check_sound formed ca)
            obtain ⟨f₃, checked₃⟩ := (ihb formed normalb).2 (check_sound formed cb)
            obtain ⟨c₂, h₂⟩ := checked₂
            obtain ⟨c₃, h₃⟩ := checked₃
            obtain ⟨l₁, level₁, same₁⟩ := universe₁ (f₁ + f₂ + f₃ + g₁ + 1) (by omega)
            obtain ⟨r, computed⟩ := synth_id (synth_mono computed₁ (Nat.le_add_right_of_le (by omega))) level₁
              ⟨_, check_mono h₂ (by omega)⟩ ⟨_, check_mono h₃ (by omega)⟩
            exact ⟨_, _, r, computed, headSame_typeEq same₁ hu⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | lam body ihBody =>
      intro Γ formed normal
      refine ⟨fun synthesized => (by cases synthesized), fun {E} typed => ?_⟩
      have normalBody : Normal (LevelTower.rules L) body := fun _ step => normal _ (.congLam step)
      obtain ⟨domain, codomain, toPi⟩ := ContextualDependentNormalChecking.lambda_type (S := TS) TowerModel.facts
        formed typed
      have tE := isType_of_typed formed typed
      obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed tE
      obtain ⟨D, C, rfl, _, _⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toPi) toN)
        (.inr (.inl ⟨domain, codomain, rfl⟩)) normalN tN).pi_left
      obtain ⟨A, B, u, tPi, hu, tBody, le⟩ := Typed.generation typed
      obtain ⟨s, hs, eN⟩ := toN
      obtain ⟨domains, bodies⟩ := TypeLe.pi_parts (S := TS) TowerModel.facts (le.trans (.conv eN hs (.refl _))) tN formed
      obtain ⟨⟨u₁, hu₁, tD⟩, _⟩ := IsType.pi_parts tN
      obtain ⟨f, checked⟩ := (ihBody (.snoc formed ⟨u₁, hu₁, tD⟩) normalBody).2
        (Typed.ctxConv (.sub tBody bodies) domains)
      obtain ⟨c, computed⟩ := checked
      exact ⟨f + g + 1, check_lam (stable _ (by omega)) ⟨_, check_mono computed (by omega)⟩⟩
  | app f a ihf iha =>
      intro Γ formed normal
      have normalf : Normal (LevelTower.rules L) f := fun _ step => normal _ (.congAppFun step)
      have normala : Normal (LevelTower.rules L) a := fun _ step => normal _ (.congAppArg step)
      have notLam : ∀ body, f ≠ .lam body := by
        rintro body rfl
        exact normal _ (.betaPi body a)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.app f a) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.app f a) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | redex => exact absurd rfl (notLam _)
        | app sf rF ca =>
            obtain ⟨f₁, F, r₁, computed₁, equal₁⟩ := (ihf formed normalf).1 sf
            obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed (isType_right formed equal₁)
            obtain ⟨D, E, rfl, domains, bodies⟩ := (forms_match formed
              (TypeEq.trans (TS).levels (TypeEq.symm (typeEq_of_redTy rF)) (TypeEq.trans (TS).levels equal₁ toN))
              (.inr (.inl ⟨_, _, rfl⟩)) normalN tN).pi_left
            have ta := check_sound formed ca
            obtain ⟨f₂, checked⟩ := (iha formed normala).2 (Typed.convType ta domains)
            obtain ⟨c, h₂⟩ := checked
            obtain ⟨r, computed⟩ := synth_app (fuel := f₁ + g + f₂) notLam (synth_mono computed₁ (by omega))
              (stable _ (by omega)) ⟨_, check_mono h₂ (by omega)⟩
            exact ⟨_, _, r, computed, TypeEq.instantiate bodies ta⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | pair a b iha ihb =>
      intro Γ formed normal
      refine ⟨fun synthesized => (by cases synthesized), fun {E} typed => ?_⟩
      have normala : Normal (LevelTower.rules L) a := fun _ step => normal _ (.congPairFst step)
      have normalb : Normal (LevelTower.rules L) b := fun _ step => normal _ (.congPairSnd step)
      obtain ⟨domain, codomain, toSigma⟩ := ContextualDependentNormalChecking.pair_type (S := TS) TowerModel.facts
        formed typed
      have tE := isType_of_typed formed typed
      obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed tE
      obtain ⟨D, C, rfl, _, _⟩ := (forms_match formed (TypeEq.trans (TS).levels (TypeEq.symm toSigma) toN)
        (.inr (.inr (.inl ⟨domain, codomain, rfl⟩))) normalN tN).sigma_left
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := Typed.generation typed
      obtain ⟨s, hs, eN⟩ := toN
      obtain ⟨domains, bodies⟩ := TypeLe.sigma_parts (S := TS) TowerModel.facts (le.trans (.conv eN hs (.refl _))) tN formed
      obtain ⟨f₁, checked₁⟩ := (iha formed normala).2 (.sub ta domains)
      obtain ⟨f₂, checked₂⟩ := (ihb formed normalb).2 (.sub tb (Derivable.substitutes bodies (SubstMor.single ta) :
        Below (LevelTower.rules L) Γ (inst0 a B) (inst0 a C)))
      obtain ⟨c₁, h₁⟩ := checked₁
      obtain ⟨c₂, h₂⟩ := checked₂
      exact ⟨f₁ + f₂ + g + 1, check_pair (stable _ (by omega)) ⟨_, check_mono h₁ (by omega)⟩
        ⟨_, check_mono h₂ (by omega)⟩⟩
  | fst p ihp =>
      intro Γ formed normal
      have normalp : Normal (LevelTower.rules L) p := fun _ step => normal _ (.congFst step)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.fst p) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.fst p) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | fst sp rP =>
            obtain ⟨f₁, P, r₁, computed₁, equal₁⟩ := (ihp formed normalp).1 sp
            obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed (isType_right formed equal₁)
            obtain ⟨D, E, rfl, domains, _⟩ := (forms_match formed
              (TypeEq.trans (TS).levels (TypeEq.symm (typeEq_of_redTy rP)) (TypeEq.trans (TS).levels equal₁ toN))
              (.inr (.inr (.inl ⟨_, _, rfl⟩))) normalN tN).sigma_left
            obtain ⟨r, computed⟩ := synth_fst (fuel := f₁ + g) (synth_mono computed₁ (by omega)) (stable _ (by omega))
            exact ⟨_, _, r, computed, domains⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | snd p ihp =>
      intro Γ formed normal
      have normalp : Normal (LevelTower.rules L) p := fun _ step => normal _ (.congSnd step)
      have synthesizes : ∀ {T₀ : Tm (LevelTower.Head L) _}, Synth (LevelTower.rules L) (TowerModel.roles (L := L)) Γ (.snd p) T₀ →
          ∃ fuel T r, synth (LevelTower.rules L) tc red fuel Γ (.snd p) = some ⟨T, r⟩ ∧
            TypeEq (LevelTower.rules L) Γ T₀ T := by
        intro T₀ synthesized
        cases synthesized with
        | snd sp rP =>
            obtain ⟨f₁, P, r₁, computed₁, equal₁⟩ := (ihp formed normalp).1 sp
            obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed (isType_right formed equal₁)
            have toSigma := typeEq_of_redTy rP
            obtain ⟨D, E, rfl, _, bodies⟩ := (forms_match formed
              (TypeEq.trans (TS).levels (TypeEq.symm toSigma) (TypeEq.trans (TS).levels equal₁ toN))
              (.inr (.inr (.inl ⟨_, _, rfl⟩))) normalN tN).sigma_left
            have tp := Typed.convType (synth_principal formed sp).1 toSigma
            obtain ⟨r, computed⟩ := synth_snd (fuel := f₁ + g) (synth_mono computed₁ (by omega)) (stable _ (by omega))
            exact ⟨_, _, r, computed, TypeEq.instantiate bodies (.fstElim tp)⟩
      exact ⟨synthesizes, fun typed => check_of_synth formed normal (fun _ h => by cases h)
        (fun _ _ h => by cases h) (fun _ h => by cases h) synthesizes typed⟩
  | refl x ihx =>
      intro Γ formed normal
      have normalx : Normal (LevelTower.rules L) x := fun _ step => normal _ (.congRefl step)
      refine ⟨fun {T₀} synthesized => ?_, fun {E} typed => ?_⟩
      · cases synthesized with
        | refl sx _ =>
            obtain ⟨f₁, X, r₁, computed₁, equal₁⟩ := (ihx formed normalx).1 sx
            obtain ⟨r, computed⟩ := synth_refl computed₁
            have tx := (synth_principal formed sx).1
            obtain ⟨u, hu, e⟩ := equal₁
            exact ⟨_, _, r, computed, ⟨u, hu, .idCong e hu (.refl tx) (.refl tx)⟩⟩
      · obtain ⟨carrier, toId⟩ := ContextualDependentNormalChecking.refl_type (S := TS) TowerModel.facts formed typed
        have tE := isType_of_typed formed typed
        obtain ⟨g, ⟨N, path⟩, normalN, toN, tN, stable⟩ := type_normal formed tE
        obtain ⟨C, a', b', rfl, carriers, lefts, rights⟩ := (forms_match formed
          (TypeEq.trans (TS).levels (TypeEq.symm toId) toN) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) normalN tN).id_left
        have tx : Typed (LevelTower.rules L) Γ x C := Typed.convType (Equal.typed (S := TS) lefts formed).1 carriers
        obtain ⟨f₁, checked⟩ := (ihx formed normalx).2 tx
        obtain ⟨c₁, h₁⟩ := checked
        obtain ⟨f₂, c₂, stable₂⟩ := compare_eventually formed (Equal.convType lefts carriers)
        obtain ⟨f₃, c₃, stable₃⟩ := compare_eventually formed (Equal.convType rights carriers)
        exact ⟨f₁ + f₂ + f₃ + g + 1, check_refl (stable _ (by omega)) ⟨_, check_mono h₁ (by omega)⟩
          ⟨_, stable₂ _ (by omega)⟩ ⟨_, stable₃ _ (by omega)⟩⟩

/-! ## The solver's executable building blocks -/

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
/-- The tower declares no constants. -/
theorem declared : DeclaredTypesFormed (LevelTower.rules L) := by
  intro name type known
  cases known

/-- The decision procedures of a tower setting are those of the tower. -/
local instance settingHeadEq (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.headEq :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).headEq)

local instance settingUniverse (valuation : Nat → L) (head : LevelTower.Head L) :
    Decidable ((TowerModel.setting valuation).R.isUniverse head) :=
  inferInstanceAs (Decidable ((LevelTower.rules L).isUniverse head))

local instance settingCumulative (valuation : Nat → L) : DecidableRel (TowerModel.setting valuation).R.cumulative :=
  inferInstanceAs (DecidableRel (LevelTower.rules L).cumulative)

/-- **The executable type former eventually forms every normal type** of a formed tower
context, and keeps succeeding at every larger budget. -/
theorem formType_eventually (valuation : Nat → L) {Γ : TypedContextual.Context (LevelTower.rules L)}
    {code : Tm (LevelTower.Head L) Γ.arity} (normal : Normal (LevelTower.rules L) code)
    (isType : IsType (LevelTower.rules L) Γ.raw code) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (ContextualDependentPruning.formType (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger Γ code).isSome := by
  have fragment := ContextualDependentNormalChecking.normal_type_synthesizes (S := TS) TowerModel.facts Γ.formed
    isType normal
  obtain ⟨u, hu, typed⟩ := isType
  obtain ⟨T₀, synthesized⟩ := Bidirectional.complete (S := TS) TowerModel.facts TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique fragment Γ.formed typed
  obtain ⟨f, T, r, computed, equal⟩ := (realized code Γ.formed normal).1 synthesized
  have le := TypeLe.toBelow ((synth_principal Γ.formed synthesized).2 typed) (IsType.head_of_universe (S := TS) hu)
  obtain ⟨w, hw, toW, _⟩ := Below.universe_target (S := TS) TowerModel.facts le Γ.formed hu
    (IsType.refl (IsType.head_of_universe (S := TS) hu))
  obtain ⟨g, recognizes⟩ := asUniverse_eventually Γ.formed (isType_right Γ.formed equal) hw
    (TypeEq.trans (TS).levels (TypeEq.symm toW) equal)
  refine ⟨f + g, fun larger enough => ?_⟩
  obtain ⟨level, recognized, _⟩ := recognizes larger (by omega)
  have synthesized' : synth (TowerModel.setting valuation).R tc red larger Γ.raw code = some ⟨T, r⟩ :=
    synth_mono computed (by omega)
  have recognized' : asUniverse (TowerModel.setting valuation).R red larger T = some level := recognized
  unfold ContextualDependentPruning.formType
  rw [synthesized']
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [recognized']
  rfl

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (LevelTower.rules L).headEq]
  [∀ head, Decidable ((LevelTower.rules L).isUniverse head)] [DecidableRel (LevelTower.rules L).cumulative] in
theorem normal_of_rename {n m : Nat} (ρ : Ren n m) {t : Tm (LevelTower.Head L) n}
    (normal : Normal (LevelTower.rules L) (Presentation.rename ρ t)) : Normal (LevelTower.rules L) t :=
  fun _ step => normal _ (StepCore.renameTerms step ρ)

/-- **Checked recovery eventually returns every recovery of a normal target**, at every larger
budget: the budgeted recovery and the budget-free normal recovery agree wherever both run. -/
theorem recover_eventually (valuation : Nat → L) {Γ Δ : TypedContextual.Context (LevelTower.rules L)}
    (inclusion : ContextualDependentTypedInversion.Inclusion Γ Δ) (type : TypedContextual.TypeOver Γ)
    {target : Tm (LevelTower.Head L) Δ.arity}
    (recovered : ContextualDependentTypedInversion.Recovery inclusion type target)
    (normal : Normal (LevelTower.rules L) target) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      ContextualDependentTypedInversion.recover (S := TowerModel.setting valuation) TowerModel.facts TowerModel.roots
        TowerModel.heads TowerModel.algebra declared tc red larger inclusion type target = some recovered := by
  have found : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) target =
      some recovered.body.code := by
    have inverted := ContextualDependentInversion.invert_rename recovered.body.code inclusion.forward _
      (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective)
    rwa [recovered.recovers] at inverted
  have normalBody : Normal (LevelTower.rules L) recovered.body.code := by
    apply normal_of_rename inclusion.forward
    rw [recovered.recovers]
    exact normal
  obtain ⟨fuel, checked⟩ := (realized recovered.body.code Γ.formed normalBody).2 recovered.body.typed
  obtain ⟨certificate, computed⟩ := checked
  refine ⟨fuel, fun larger enough => ?_⟩
  have checked' : check (TowerModel.setting valuation).R tc red larger Γ.raw recovered.body.code type.code =
      some certificate := check_mono computed enough
  unfold ContextualDependentTypedInversion.recover
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i body same
    rw [found] at same
    cases same
    rw [checked']
    exact congrArg some (ContextualDependentTypedInversion.Recovery.unique _ _)

end Realization

end ContextualDependentExecutableChecking
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
