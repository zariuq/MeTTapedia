import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralLaws

/-!
# Exact inversion of dependent syntax along an injective variable map

The operation traverses the existing dependent term grammar, lifting the
partial inverse under every binder. It neither interprets constants nor
restricts their names. The computed finite lookup is an exact inverse of any
injective variable map, including permutations and non-prefix selections.

The resulting exact-image theorem concerns raw syntax. Failure is not a
refutation modulo conversion: reduction may erase a forbidden occurrence.
Typing of a recovered body is a separate checked obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInversion

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

abbrev Partial (n m : Nat) := Fin m → Option (Fin n)

def lift {n m : Nat} (inverse : Partial n m) : Partial (n + 1) (m + 1) :=
  Fin.cases (some 0) (fun index => (inverse index).map Fin.succ)

def Exact {n m : Nat} (forward : Ren n m) (inverse : Partial n m) : Prop :=
  ∀ target source, inverse target = some source ↔ forward source = target

theorem Exact.lift {n m : Nat} {forward : Ren n m} {inverse : Partial n m}
    (exact : Exact forward inverse) : Exact (liftRen forward) (lift inverse) := by
  intro target source
  refine Fin.cases ?_ (fun target => ?_) target
  · refine Fin.cases ?_ (fun source => ?_) source <;> simp [ContextualDependentInversion.lift, liftRen, Fin.ext_iff]
  · refine Fin.cases ?_ (fun source => ?_) source
    · cases found : inverse target <;> simp [ContextualDependentInversion.lift, liftRen, found, Fin.ext_iff]
    · simpa only [ContextualDependentInversion.lift, liftRen, Fin.cases_succ, Option.map_eq_some_iff,
        Fin.succ_inj, exists_eq_right] using exact target source

def lookup {n m : Nat} (forward : Ren n m) (target : Fin m) : Option (Fin n) :=
  (List.finRange n).find? fun source => decide (forward source = target)

theorem lookup_sound {n m : Nat} (forward : Ren n m) {target : Fin m} {source : Fin n}
    (found : lookup forward target = some source) : forward source = target :=
  by
  have selected := List.find?_some (p := fun index => decide (forward index = target)) found
  exact of_decide_eq_true selected

theorem lookup_complete {n m : Nat} (forward : Ren n m) (injective : Function.Injective forward)
    (source : Fin n) : lookup forward (forward source) = some source := by
  cases found : lookup forward (forward source) with
  | none =>
      have absent := (List.find?_eq_none.mp found) source (List.mem_finRange source)
      simp at absent
  | some other => exact congrArg some (injective (lookup_sound forward found))

theorem lookup_exact {n m : Nat} (forward : Ren n m) (injective : Function.Injective forward) :
    Exact forward (lookup forward) := by
  intro target source
  constructor
  · exact lookup_sound forward
  · rintro rfl
    exact lookup_complete forward injective source

def invert : {n m : Nat} → Partial n m → Tm Head m → Option (Tm Head n)
  | _, _, inverse, .var index => (.var ·) <$> inverse index
  | _, _, _, .head head => some (.head head)
  | _, _, _, .const name => some (.const name)
  | _, _, inverse, .pi domain body => do
      return .pi (← invert inverse domain) (← invert (lift inverse) body)
  | _, _, inverse, .sigma domain body => do
      return .sigma (← invert inverse domain) (← invert (lift inverse) body)
  | _, _, inverse, .id type left right => do
      return .id (← invert inverse type) (← invert inverse left) (← invert inverse right)
  | _, _, inverse, .lam body => return .lam (← invert (lift inverse) body)
  | _, _, inverse, .app function argument => do
      return .app (← invert inverse function) (← invert inverse argument)
  | _, _, inverse, .pair first second => do
      return .pair (← invert inverse first) (← invert inverse second)
  | _, _, inverse, .fst pair => return .fst (← invert inverse pair)
  | _, _, inverse, .snd pair => return .snd (← invert inverse pair)
  | _, _, inverse, .refl value => return .refl (← invert inverse value)

theorem invert_rename {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (forward : Ren n m) (inverse : Partial n m), Exact forward inverse →
      invert inverse (rename forward term) = some term := by
  induction term with
  | var index =>
      intro m forward inverse exact
      simp only [rename, invert, Option.map_eq_map, (exact _ index).mpr rfl, Option.map_some]
  | head head => intros; rfl
  | const name => intros; rfl
  | pi domain body ihDomain ihBody =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihDomain forward inverse exact,
        ihBody (liftRen forward) (lift inverse) exact.lift, Option.bind_some]
  | sigma domain body ihDomain ihBody =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihDomain forward inverse exact,
        ihBody (liftRen forward) (lift inverse) exact.lift, Option.bind_some]
  | id type left right ihType ihLeft ihRight =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihType forward inverse exact,
        ihLeft forward inverse exact, ihRight forward inverse exact, Option.bind_some]
  | lam body ihBody =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihBody (liftRen forward) (lift inverse) exact.lift, Option.bind_some]
  | app function argument ihFunction ihArgument =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihFunction forward inverse exact, ihArgument forward inverse exact, Option.bind_some]
  | pair first second ihFirst ihSecond =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ihFirst forward inverse exact, ihSecond forward inverse exact, Option.bind_some]
  | fst pair ih =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ih forward inverse exact, Option.bind_some]
  | snd pair ih =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ih forward inverse exact, Option.bind_some]
  | refl value ih =>
      intro m forward inverse exact
      simp only [rename, invert, Option.bind_eq_bind, Option.pure_def, ih forward inverse exact, Option.bind_some]

theorem invert_sound {m : Nat} (term : Tm Head m) :
    ∀ {n : Nat} (forward : Ren n m) (inverse : Partial n m), Exact forward inverse →
      ∀ body, invert inverse term = some body → rename forward body = term := by
  induction term with
  | var index =>
      intro n forward inverse exact body found
      simp only [invert, Option.map_eq_map] at found
      obtain ⟨source, selected, rfl⟩ := Option.map_eq_some_iff.mp found
      exact congrArg Tm.var ((exact _ _).mp selected)
  | head head =>
      intro n forward inverse exact body found
      cases Option.some.inj found
      rfl
  | const name =>
      intro n forward inverse exact body found
      cases Option.some.inj found
      rfl
  | pi domain codomain ihDomain ihCodomain =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨domain', selectedDomain, codomain', selectedCodomain, rfl⟩ := found
      simp only [rename, ihDomain forward inverse exact _ selectedDomain,
        ihCodomain (liftRen forward) (lift inverse) exact.lift _ selectedCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨domain', selectedDomain, codomain', selectedCodomain, rfl⟩ := found
      simp only [rename, ihDomain forward inverse exact _ selectedDomain,
        ihCodomain (liftRen forward) (lift inverse) exact.lift _ selectedCodomain]
  | id type left right ihType ihLeft ihRight =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨type', selectedType, left', selectedLeft, right', selectedRight, rfl⟩ := found
      simp only [rename, ihType forward inverse exact _ selectedType,
        ihLeft forward inverse exact _ selectedLeft, ihRight forward inverse exact _ selectedRight]
  | lam body ih =>
      intro n forward inverse exact recovered found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨body', selected, rfl⟩ := found
      simp only [rename, ih (liftRen forward) (lift inverse) exact.lift _ selected]
  | app function argument ihFunction ihArgument =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨function', selectedFunction, argument', selectedArgument, rfl⟩ := found
      simp only [rename, ihFunction forward inverse exact _ selectedFunction,
        ihArgument forward inverse exact _ selectedArgument]
  | pair first second ihFirst ihSecond =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨first', selectedFirst, second', selectedSecond, rfl⟩ := found
      simp only [rename, ihFirst forward inverse exact _ selectedFirst,
        ihSecond forward inverse exact _ selectedSecond]
  | fst pair ih =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨pair', selected, rfl⟩ := found
      simp only [rename, ih forward inverse exact _ selected]
  | snd pair ih =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨pair', selected, rfl⟩ := found
      simp only [rename, ih forward inverse exact _ selected]
  | refl value ih =>
      intro n forward inverse exact body found
      simp only [invert, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨value', selected, rfl⟩ := found
      simp only [rename, ih forward inverse exact _ selected]

theorem invert_eq_some_iff {n m : Nat} (forward : Ren n m) (inverse : Partial n m)
    (exact : Exact forward inverse) (target : Tm Head m) (body : Tm Head n) :
    invert inverse target = some body ↔ rename forward body = target :=
  ⟨invert_sound target forward inverse exact body,
    fun same => same ▸ invert_rename body forward inverse exact⟩

theorem invert_eq_none_iff {n m : Nat} (forward : Ren n m) (inverse : Partial n m)
    (exact : Exact forward inverse) (target : Tm Head m) :
    invert inverse target = none ↔ ¬ ∃ body, rename forward body = target := by
  constructor
  · intro missing ⟨body, same⟩
    have found := (invert_eq_some_iff forward inverse exact target body).mpr same
    rw [missing] at found
    cases found
  · intro absent
    cases found : invert inverse target with
    | none => rfl
    | some body => exact False.elim (absent ⟨body, invert_sound target forward inverse exact body found⟩)

end ContextualDependentInversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
