import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentCollapse

/-!
# Miller occurrences, and their stability under pattern instantiation

A term over a context whose variables are marked **flexible** (metavariables) or **rigid**
(bound locals) has **Miller occurrences** when every application spine headed by a flexible
variable is a Miller pattern `F y₁ … yₖ`: distinct rigid variables. A flexible spine is never
projected. This is the occurrence condition of the dynamic pattern fragment (Miller; Abel and
Pientka), read on a term in normal form.

**Stability.** Let `σ` instantiate one flexible variable `F` by a pattern solution `λ z̄. u`, with
`u` normal and with Miller occurrences, and rename every other variable injectively, respecting the
marking. If every occurrence of `F` in a normal term `t` is applied to exactly `|z̄|` arguments, then
`σ t` reduces to a normal term with Miller occurrences. Each occurrence `F ȳ` collapses to the
renaming `u[ȳ/z̄]` of the solution body, and nothing else changes shape, so no redex is created.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ContextualDependentExecutableJoin
open ContextualDependentGeneralPattern (liftFlexible)

variable {Head : Type}

/-! ## Spines -/

/-- The head of an application spine. -/
def spineHead {n : Nat} : Tm Head n → Tm Head n
  | .app function _ => spineHead function
  | .var i => .var i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi A B
  | .sigma A B => .sigma A B
  | .id A a b => .id A a b
  | .lam body => .lam body
  | .pair a b => .pair a b
  | .fst p => .fst p
  | .snd p => .snd p
  | .refl a => .refl a

/-- A spine head that is a flexible variable. -/
def flexHead {n : Nat} (flexible : Fin n → Bool) : Tm Head n → Bool
  | .var i => flexible i
  | _ => false

/-- Read a variable applied to variables, innermost argument first. -/
def readSpine {n : Nat} : Tm Head n → Option (Fin n × List (Fin n))
  | .var head => some (head, [])
  | .app function (.var argument) => (readSpine function).map fun read => (read.1, argument :: read.2)
  | _ => none

/-- **A Miller spine**: a flexible variable applied to distinct rigid variables. -/
def millerSpine {n : Nat} (flexible : Fin n → Bool) (t : Tm Head n) : Bool :=
  match readSpine t with
  | some (head, arguments) =>
      flexible head && arguments.all (fun argument => !flexible argument) && decide arguments.Nodup
  | none => false

/-- **Miller occurrences**: every flexible spine is a Miller spine, and none is projected. -/
def miller : {n : Nat} → (Fin n → Bool) → Tm Head n → Bool
  | _, _, .var _ => true
  | _, _, .const _ => true
  | _, _, .head _ => true
  | _, flexible, .pi A B => miller flexible A && miller (liftFlexible flexible) B
  | _, flexible, .sigma A B => miller flexible A && miller (liftFlexible flexible) B
  | _, flexible, .id A a b => miller flexible A && miller flexible a && miller flexible b
  | _, flexible, .lam body => miller (liftFlexible flexible) body
  | _, flexible, .app f a =>
      if flexHead flexible (spineHead f) then millerSpine flexible (.app f a)
      else miller flexible f && miller flexible a
  | _, flexible, .pair a b => miller flexible a && miller flexible b
  | _, flexible, .fst p => !flexHead flexible (spineHead p) && miller flexible p
  | _, flexible, .snd p => !flexHead flexible (spineHead p) && miller flexible p
  | _, flexible, .refl a => miller flexible a

/-- The number of arguments of an application spine. -/
def spineLength {n : Nat} : Tm Head n → Nat
  | .app function _ => spineLength function + 1
  | _ => 0

/-- Arities under one more binder: the binder is rigid. -/
def liftArity {n : Nat} (arity : Fin n → Nat) : Fin (n + 1) → Nat := Fin.cases 0 arity

/-- The arity of a spine head that is a variable. -/
def headArity {n : Nat} (arity : Fin n → Nat) : Tm Head n → Nat
  | .var i => arity i
  | _ => 0

/-- **Arities**: every flexible variable is applied to exactly its arity. -/
def arities : {n : Nat} → (Fin n → Bool) → (Fin n → Nat) → Tm Head n → Bool
  | _, flexible, arity, .var i => !flexible i || decide (arity i = 0)
  | _, _, _, .const _ => true
  | _, _, _, .head _ => true
  | _, flexible, arity, .pi A B => arities flexible arity A && arities (liftFlexible flexible) (liftArity arity) B
  | _, flexible, arity, .sigma A B => arities flexible arity A && arities (liftFlexible flexible) (liftArity arity) B
  | _, flexible, arity, .id A a b => arities flexible arity A && arities flexible arity a && arities flexible arity b
  | _, flexible, arity, .lam body => arities (liftFlexible flexible) (liftArity arity) body
  | _, flexible, arity, .app f a =>
      if flexHead flexible (spineHead f) then decide (spineLength f + 1 = headArity arity (spineHead f))
      else arities flexible arity f && arities flexible arity a
  | _, flexible, arity, .pair a b => arities flexible arity a && arities flexible arity b
  | _, flexible, arity, .fst p => arities flexible arity p
  | _, flexible, arity, .snd p => arities flexible arity p
  | _, flexible, arity, .refl a => arities flexible arity a

def isLam {n : Nat} : Tm Head n → Bool
  | .lam _ => true
  | _ => false

def isPair {n : Nat} : Tm Head n → Bool
  | .pair _ _ => true
  | _ => false

/-! ## Spine facts -/

theorem readSpine_spec {n : Nat} : ∀ {t : Tm Head n} {head : Fin n} {arguments : List (Fin n)},
    readSpine t = some (head, arguments) → t = appsVar (.var head) arguments
  | .var h, head, arguments, read => by
      simp only [readSpine, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      rfl
  | .app function (.var argument), head, arguments, read => by
      simp only [readSpine] at read
      cases inner : readSpine function with
      | none => rw [inner] at read; cases read
      | some found =>
          rw [inner] at read
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at read
          obtain ⟨rfl, rfl⟩ := read
          rw [readSpine_spec inner]
          rfl
  | .app _ (.const _), _, _, read => by simp [readSpine] at read
  | .app _ (.head _), _, _, read => by simp [readSpine] at read
  | .app _ (.pi _ _), _, _, read => by simp [readSpine] at read
  | .app _ (.sigma _ _), _, _, read => by simp [readSpine] at read
  | .app _ (.id _ _ _), _, _, read => by simp [readSpine] at read
  | .app _ (.lam _), _, _, read => by simp [readSpine] at read
  | .app _ (.app _ _), _, _, read => by simp [readSpine] at read
  | .app _ (.pair _ _), _, _, read => by simp [readSpine] at read
  | .app _ (.fst _), _, _, read => by simp [readSpine] at read
  | .app _ (.snd _), _, _, read => by simp [readSpine] at read
  | .app _ (.refl _), _, _, read => by simp [readSpine] at read
  | .const _, _, _, read => by simp [readSpine] at read
  | .head _, _, _, read => by simp [readSpine] at read
  | .pi _ _, _, _, read => by simp [readSpine] at read
  | .sigma _ _, _, _, read => by simp [readSpine] at read
  | .id _ _ _, _, _, read => by simp [readSpine] at read
  | .lam _, _, _, read => by simp [readSpine] at read
  | .pair _ _, _, _, read => by simp [readSpine] at read
  | .fst _, _, _, read => by simp [readSpine] at read
  | .snd _, _, _, read => by simp [readSpine] at read
  | .refl _, _, _, read => by simp [readSpine] at read

theorem readSpine_appsVar {n : Nat} (head : Fin n) :
    ∀ arguments : List (Fin n), readSpine (appsVar (Head := Head) (.var head) arguments) = some (head, arguments)
  | [] => rfl
  | argument :: rest => by
      simp only [appsVar, readSpine, readSpine_appsVar head rest, Option.map_some]

theorem spineHead_appsVar {n : Nat} (head : Fin n) :
    ∀ arguments : List (Fin n), spineHead (appsVar (Head := Head) (.var head) arguments) = .var head
  | [] => rfl
  | argument :: rest => by simp only [appsVar, spineHead, spineHead_appsVar head rest]

theorem spineLength_appsVar {n : Nat} (head : Fin n) :
    ∀ arguments : List (Fin n), spineLength (appsVar (Head := Head) (.var head) arguments) = arguments.length
  | [] => rfl
  | argument :: rest => by simp only [appsVar, spineLength, spineLength_appsVar head rest, List.length_cons]

theorem spineHead_rename {n m : Nat} (ρ : Ren n m) : ∀ t : Tm Head n, spineHead (rename ρ t) = rename ρ (spineHead t)
  | .app function _ => by simp only [rename, spineHead, spineHead_rename ρ function]
  | .var _ => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .pi _ _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

theorem flexHead_rename {n m : Nat} (ρ : Ren n m) {flexible : Fin n → Bool} {flexible' : Fin m → Bool}
    (respects : ∀ i, flexible' (ρ i) = flexible i) : ∀ t : Tm Head n, flexHead flexible' (rename ρ t) = flexHead flexible t
  | .var i => respects i
  | .const _ => rfl
  | .head _ => rfl
  | .pi _ _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .app _ _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

theorem readSpine_rename {n m : Nat} (ρ : Ren n m) :
    ∀ t : Tm Head n, readSpine (rename ρ t) = (readSpine t).map fun read => (ρ read.1, read.2.map ρ)
  | .var _ => rfl
  | .app function (.var argument) => by
      simp only [rename, readSpine, readSpine_rename ρ function, Option.map_map]
      rfl
  | .app _ (.const _) => rfl
  | .app _ (.head _) => rfl
  | .app _ (.pi _ _) => rfl
  | .app _ (.sigma _ _) => rfl
  | .app _ (.id _ _ _) => rfl
  | .app _ (.lam _) => rfl
  | .app _ (.app _ _) => rfl
  | .app _ (.pair _ _) => rfl
  | .app _ (.fst _) => rfl
  | .app _ (.snd _) => rfl
  | .app _ (.refl _) => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .pi _ _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

/-! ## Miller occurrences are invariant under respecting embeddings -/

theorem liftFlexible_respects {n m : Nat} {ρ : Ren n m} {flexible : Fin n → Bool} {flexible' : Fin m → Bool}
    (respects : ∀ i, flexible' (ρ i) = flexible i) :
    ∀ i, liftFlexible flexible' (liftRen ρ i) = liftFlexible flexible i := by
  intro i
  refine Fin.cases ?_ (fun prior => ?_) i
  · rfl
  · exact respects prior

theorem millerSpine_rename {n m : Nat} {ρ : Ren n m} (injective : Function.Injective ρ) {flexible : Fin n → Bool}
    {flexible' : Fin m → Bool} (respects : ∀ i, flexible' (ρ i) = flexible i) {t : Tm Head n}
    (spine : millerSpine flexible t = true) : millerSpine flexible' (rename ρ t) = true := by
  unfold millerSpine at spine ⊢
  rw [readSpine_rename]
  cases read : readSpine t with
  | none => rw [read] at spine; cases spine
  | some found =>
      obtain ⟨head, arguments⟩ := found
      rw [read] at spine
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_true_eq] at spine
      obtain ⟨⟨flexibleHead, rigid⟩, distinct⟩ := spine
      simp only [Option.map_some, Bool.and_eq_true, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
      refine ⟨⟨by rw [respects]; exact flexibleHead, fun argument member => by rw [respects]; exact rigid argument member⟩,
        distinct.map injective⟩

/-- **Miller occurrences are kept by every injective renaming that respects the marking.** -/
theorem miller_rename : ∀ {n m : Nat} (t : Tm Head n) {ρ : Ren n m} (_ : Function.Injective ρ)
    {flexible : Fin n → Bool} {flexible' : Fin m → Bool} (_ : ∀ i, flexible' (ρ i) = flexible i),
    miller flexible t = true → miller flexible' (rename ρ t) = true
  | _, _, .var _, _, _, _, _, _, _ => rfl
  | _, _, .const _, _, _, _, _, _, _ => rfl
  | _, _, .head _, _, _, _, _, _, _ => rfl
  | _, _, .pi A B, _, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename A injective respects holds.1,
        miller_rename B (liftRen_injective injective) (liftFlexible_respects respects) holds.2⟩
  | _, _, .sigma A B, _, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename A injective respects holds.1,
        miller_rename B (liftRen_injective injective) (liftFlexible_respects respects) holds.2⟩
  | _, _, .id A a b, _, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨⟨miller_rename A injective respects holds.1.1, miller_rename a injective respects holds.1.2⟩,
        miller_rename b injective respects holds.2⟩
  | _, _, .lam body, _, injective, _, _, respects, holds => by
      simp only [miller] at holds ⊢
      exact miller_rename body (liftRen_injective injective) (liftFlexible_respects respects) holds
  | _, _, .app f a, ρ, injective, flexible, flexible', respects, holds => by
      simp only [miller] at holds
      simp only [rename, miller, spineHead_rename, flexHead_rename ρ respects]
      split
      · rename_i flexibleSpine
        rw [if_pos flexibleSpine] at holds
        exact millerSpine_rename injective respects (t := .app f a) holds
      · rename_i rigidSpine
        rw [if_neg rigidSpine] at holds
        simp only [Bool.and_eq_true] at holds ⊢
        exact ⟨miller_rename f injective respects holds.1, miller_rename a injective respects holds.2⟩
  | _, _, .pair a b, _, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      exact ⟨miller_rename a injective respects holds.1, miller_rename b injective respects holds.2⟩
  | _, _, .fst p, ρ, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      rw [spineHead_rename, flexHead_rename ρ respects]
      exact ⟨holds.1, miller_rename p injective respects holds.2⟩
  | _, _, .snd p, ρ, injective, _, _, respects, holds => by
      simp only [rename, miller, Bool.and_eq_true] at holds ⊢
      rw [spineHead_rename, flexHead_rename ρ respects]
      exact ⟨holds.1, miller_rename p injective respects holds.2⟩
  | _, _, .refl a, _, injective, _, _, respects, holds => by
      simp only [miller] at holds ⊢
      exact miller_rename a injective respects holds

/-- A flexible variable applied to distinct rigid variables has Miller occurrences. -/
theorem miller_appsVar {n : Nat} {flexible : Fin n → Bool} {head : Fin n} (flexibleHead : flexible head = true) :
    ∀ (arguments : List (Fin n)), (∀ argument ∈ arguments, flexible argument = false) → arguments.Nodup →
      miller flexible (appsVar (Head := Head) (.var head) arguments) = true
  | [], _, _ => rfl
  | argument :: rest, rigid, distinct => by
      change miller flexible (.app (appsVar (.var head) rest) (.var argument)) = true
      simp only [miller, spineHead_appsVar, flexHead, flexibleHead, if_true]
      change millerSpine flexible (appsVar (.var head) (argument :: rest)) = true
      unfold millerSpine
      rw [readSpine_appsVar]
      simp only [flexibleHead, Bool.true_and, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_true_eq]
      exact ⟨rigid, distinct⟩

/-! ## Arities are invariant under respecting renamings -/

theorem spineLength_rename {n m : Nat} (ρ : Ren n m) : ∀ t : Tm Head n, spineLength (rename ρ t) = spineLength t
  | .app function _ => by simp only [rename, spineLength, spineLength_rename ρ function]
  | .var _ => rfl
  | .const _ => rfl
  | .head _ => rfl
  | .pi _ _ => rfl
  | .sigma _ _ => rfl
  | .id _ _ _ => rfl
  | .lam _ => rfl
  | .pair _ _ => rfl
  | .fst _ => rfl
  | .snd _ => rfl
  | .refl _ => rfl

theorem headArity_rename {n m : Nat} (ρ : Ren n m) {flexible : Fin n → Bool} {arity : Fin n → Nat}
    {arity' : Fin m → Nat} (aritiesRespect : ∀ i, flexible i = true → arity' (ρ i) = arity i) :
    ∀ t : Tm Head n, flexHead flexible t = true → headArity arity' (rename ρ t) = headArity arity t
  | .var i, flexibleHead => aritiesRespect i flexibleHead
  | .const _, impossible => by cases impossible
  | .head _, impossible => by cases impossible
  | .pi _ _, impossible => by cases impossible
  | .sigma _ _, impossible => by cases impossible
  | .id _ _ _, impossible => by cases impossible
  | .lam _, impossible => by cases impossible
  | .app _ _, impossible => by cases impossible
  | .pair _ _, impossible => by cases impossible
  | .fst _, impossible => by cases impossible
  | .snd _, impossible => by cases impossible
  | .refl _, impossible => by cases impossible

theorem liftArity_respects {n m : Nat} {ρ : Ren n m} {flexible : Fin n → Bool} {arity : Fin n → Nat}
    {arity' : Fin m → Nat} (aritiesRespect : ∀ i, flexible i = true → arity' (ρ i) = arity i) :
    ∀ i, liftFlexible flexible i = true → liftArity arity' (liftRen ρ i) = liftArity arity i := by
  intro i
  refine Fin.cases ?_ (fun prior => ?_) i
  · intro impossible; cases impossible
  · exact aritiesRespect prior

/-- **Arities are kept by every renaming that respects the marking and the arities.** -/
theorem arities_rename : ∀ {n m : Nat} (t : Tm Head n) {ρ : Ren n m} {flexible : Fin n → Bool}
    {flexible' : Fin m → Bool} {arity : Fin n → Nat} {arity' : Fin m → Nat},
    (∀ i, flexible' (ρ i) = flexible i) → (∀ i, flexible i = true → arity' (ρ i) = arity i) →
      arities flexible arity t = true → arities flexible' arity' (rename ρ t) = true
  | _, _, .var i, ρ, flexible, _, _, _, respects, aritiesRespect, holds => by
      simp only [arities, rename, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at holds ⊢
      rw [respects]
      rcases holds with rigid | zero
      · exact .inl rigid
      · cases flexibleVariable : flexible i
        · exact .inl rfl
        · exact .inr (by rw [aritiesRespect i flexibleVariable]; exact zero)
  | _, _, .const _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .head _, _, _, _, _, _, _, _, _ => rfl
  | _, _, .pi A B, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities, Bool.and_eq_true] at holds ⊢
      exact ⟨arities_rename A respects aritiesRespect holds.1,
        arities_rename B (liftFlexible_respects respects) (liftArity_respects aritiesRespect) holds.2⟩
  | _, _, .sigma A B, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities, Bool.and_eq_true] at holds ⊢
      exact ⟨arities_rename A respects aritiesRespect holds.1,
        arities_rename B (liftFlexible_respects respects) (liftArity_respects aritiesRespect) holds.2⟩
  | _, _, .id A a b, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities, Bool.and_eq_true] at holds ⊢
      exact ⟨⟨arities_rename A respects aritiesRespect holds.1.1, arities_rename a respects aritiesRespect holds.1.2⟩,
        arities_rename b respects aritiesRespect holds.2⟩
  | _, _, .lam body, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities] at holds ⊢
      exact arities_rename body (liftFlexible_respects respects) (liftArity_respects aritiesRespect) holds
  | _, _, .app f a, ρ, flexible, flexible', arity, arity', respects, aritiesRespect, holds => by
      simp only [arities] at holds
      simp only [rename, arities, spineHead_rename, flexHead_rename ρ respects]
      split
      · rename_i flexibleSpine
        rw [if_pos flexibleSpine] at holds
        rw [spineLength_rename, headArity_rename ρ aritiesRespect _ flexibleSpine]
        exact holds
      · rename_i rigidSpine
        rw [if_neg rigidSpine] at holds
        simp only [Bool.and_eq_true] at holds ⊢
        exact ⟨arities_rename f respects aritiesRespect holds.1, arities_rename a respects aritiesRespect holds.2⟩
  | _, _, .pair a b, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities, Bool.and_eq_true] at holds ⊢
      exact ⟨arities_rename a respects aritiesRespect holds.1, arities_rename b respects aritiesRespect holds.2⟩
  | _, _, .fst p, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities] at holds ⊢
      exact arities_rename p respects aritiesRespect holds
  | _, _, .snd p, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities] at holds ⊢
      exact arities_rename p respects aritiesRespect holds
  | _, _, .refl a, _, _, _, _, _, respects, aritiesRespect, holds => by
      simp only [rename, arities] at holds ⊢
      exact arities_rename a respects aritiesRespect holds

/-- A flexible variable applied to its arity of arguments has its arities. -/
theorem arities_appsVar {n : Nat} {flexible : Fin n → Bool} {arity : Fin n → Nat} {head : Fin n}
    (flexibleHead : flexible head = true) :
    ∀ (arguments : List (Fin n)), arguments.length = arity head →
      arities flexible arity (appsVar (Head := Head) (.var head) arguments) = true
  | [], length => by
      simp only [appsVar, arities, flexibleHead, Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact length.symm
  | argument :: rest, length => by
      change arities flexible arity (.app (appsVar (.var head) rest) (.var argument)) = true
      simp only [arities, spineHead_appsVar, flexHead, flexibleHead, if_true, headArity, spineLength_appsVar,
        decide_eq_true_eq]
      exact length

/-- A flexible spine with its arities is applied to its arity of arguments. -/
theorem arities_appsVar_length {n : Nat} {flexible : Fin n → Bool} {arity : Fin n → Nat} {head : Fin n}
    (flexibleHead : flexible head = true) :
    ∀ (arguments : List (Fin n)), arities flexible arity (appsVar (Head := Head) (.var head) arguments) = true →
      arguments.length = arity head
  | [], holds => by
      simp only [appsVar, arities, flexibleHead, Bool.not_true, Bool.false_or, decide_eq_true_eq] at holds
      exact holds.symm
  | argument :: rest, holds => by
      change arities flexible arity (.app (appsVar (.var head) rest) (.var argument)) = true at holds
      simp only [arities, spineHead_appsVar, flexHead, flexibleHead, if_true, headArity, spineLength_appsVar,
        decide_eq_true_eq] at holds
      exact holds

/-! ## Normal forms of a root-free rule package -/

section Normal

variable {R : Rules Head} (empty : R.computation = RootComputation.empty)
include empty

theorem normal_var {n : Nat} (i : Fin n) : Normal R (.var i : Tm Head n) :=
  (ContextualDependentNormalizing.normal_iff_step_none empty _).mpr rfl

theorem normal_const {n : Nat} (c : DeclName) : Normal R (.const c : Tm Head n) :=
  (ContextualDependentNormalizing.normal_iff_step_none empty _).mpr rfl

theorem normal_head {n : Nat} (h : Head) : Normal R (.head h : Tm Head n) :=
  (ContextualDependentNormalizing.normal_iff_step_none empty _).mpr rfl

theorem normal_pi_iff {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} :
    Normal R (.pi A B) ↔ Normal R A ∧ Normal R B := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    ContextualDependentNormalizing.normal_iff_step_none empty, step.eq_4]
  cases step R (fun _ => none) A <;> cases step R (fun _ => none) B <;> simp

theorem normal_sigma_iff {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} :
    Normal R (.sigma A B) ↔ Normal R A ∧ Normal R B := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    ContextualDependentNormalizing.normal_iff_step_none empty, step.eq_5]
  cases step R (fun _ => none) A <;> cases step R (fun _ => none) B <;> simp

theorem normal_id_iff {n : Nat} {A a b : Tm Head n} :
    Normal R (.id A a b) ↔ Normal R A ∧ Normal R a ∧ Normal R b := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    step.eq_6]
  cases step R (fun _ => none) A <;> cases step R (fun _ => none) a <;> cases step R (fun _ => none) b <;> simp

theorem normal_lam_iff {n : Nat} {body : Tm Head (n + 1)} : Normal R (.lam body) ↔ Normal R body := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    step.eq_7]
  cases step R (fun _ => none) body <;> simp

theorem normal_pair_iff {n : Nat} {a b : Tm Head n} : Normal R (.pair a b) ↔ Normal R a ∧ Normal R b := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    ContextualDependentNormalizing.normal_iff_step_none empty, step.eq_10]
  cases step R (fun _ => none) a <;> cases step R (fun _ => none) b <;> simp

theorem normal_refl_iff {n : Nat} {a : Tm Head n} : Normal R (.refl a) ↔ Normal R a := by
  rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
    step.eq_15]
  cases step R (fun _ => none) a <;> simp

theorem normal_app_iff {n : Nat} {f a : Tm Head n} :
    Normal R (.app f a) ↔ isLam f = false ∧ Normal R f ∧ Normal R a := by
  by_cases redex : ∃ body, f = .lam body
  · obtain ⟨body, rfl⟩ := redex
    simp only [isLam, Bool.true_eq_false, false_and, iff_false]
    intro normal
    exact normal _ (.betaPi _ _)
  · have notLam : isLam f = false := by
      cases f <;> first | rfl | exact absurd ⟨_, rfl⟩ redex
    rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
      ContextualDependentNormalizing.normal_iff_step_none empty,
      step.eq_9 R _ _ f a (fun body same => redex ⟨body, same⟩)]
    simp only [notLam, true_and]
    cases step R (fun _ => none) f <;> cases step R (fun _ => none) a <;> simp

theorem normal_fst_iff {n : Nat} {p : Tm Head n} : Normal R (.fst p) ↔ isPair p = false ∧ Normal R p := by
  by_cases redex : ∃ a b, p = .pair a b
  · obtain ⟨a, b, rfl⟩ := redex
    simp only [isPair, Bool.true_eq_false, false_and, iff_false]
    intro normal
    exact normal _ (.betaSigmaFst _ _)
  · have notPair : isPair p = false := by
      cases p <;> first | rfl | exact absurd ⟨_, _, rfl⟩ redex
    rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
      step.eq_12 R _ _ p (fun a b same => redex ⟨a, b, same⟩)]
    simp only [notPair, true_and]
    cases step R (fun _ => none) p <;> simp

theorem normal_snd_iff {n : Nat} {p : Tm Head n} : Normal R (.snd p) ↔ isPair p = false ∧ Normal R p := by
  by_cases redex : ∃ a b, p = .pair a b
  · obtain ⟨a, b, rfl⟩ := redex
    simp only [isPair, Bool.true_eq_false, false_and, iff_false]
    intro normal
    exact normal _ (.betaSigmaSnd _ _)
  · have notPair : isPair p = false := by
      cases p <;> first | rfl | exact absurd ⟨_, _, rfl⟩ redex
    rw [ContextualDependentNormalizing.normal_iff_step_none empty, ContextualDependentNormalizing.normal_iff_step_none empty,
      step.eq_14 R _ _ p (fun a b same => redex ⟨a, b, same⟩)]
    simp only [notPair, true_and]
    cases step R (fun _ => none) p <;> simp

/-- A variable applied to variables is normal. -/
theorem normal_appsVar {n : Nat} (head : Fin n) :
    ∀ arguments : List (Fin n), Normal R (appsVar (Head := Head) (.var head) arguments)
  | [] => normal_var empty head
  | argument :: rest => by
      refine (normal_app_iff empty).mpr ⟨?_, normal_appsVar head rest, normal_var empty argument⟩
      cases rest <;> rfl

end Normal

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
