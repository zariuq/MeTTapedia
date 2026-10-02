import Mathlib.Data.List.Forall2
import Mettapedia.OSLF.Programs.GradualTypes

/-!
# The static gradual guarantee, via abstraction

A gradually typed λ-calculus with numbers, booleans, addition, conditionals,
annotated λ-abstraction, application and type ascription (the language GTFL
of Abstracting Gradual Typing, with de Bruijn variables).  Its typing rules
use the gradual liftings of the static rules: consistency `Consis` for
equality, the meet `meet` for the two branches of a conditional, and the
liftings `dom`, `cod` of the domain and codomain functions
(`dom_isAbstraction`, `cod_isAbstraction`).

**Static gradual guarantee** (`static_gradual_guarantee`): making the type
annotations of a well-typed program less precise keeps it well typed, at a
less precise type.  The proof uses only that each lifted predicate and
function is monotone for precision (`Consis.mono`, `meet_mono`, `dom_mono`,
`cod_mono`), and each of those is inclusion of concretisations.

**Conservative extension** (`static_iff_gradual`): on fully static programs
the gradual type system coincides with the static one.

**Dynamic embedding** (`embed_hasType`): every well-scoped program becomes
well typed at `?` once every annotation is `?` and every subterm is ascribed
`?`.

Control: the guarantee is about precision, not arbitrary change; replacing an
annotation by an *inconsistent* one breaks typing (`Controls.inconsistent_breaks`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.GradualGuarantee

open Mettapedia.OSLF.Programs.GradualTypes

/-! ## Liftings of the domain and codomain functions -/

/-- The gradual domain function. -/
def dom : GType → Option GType
  | .unknown => some .unknown
  | .arr A _ => some A
  | _ => none

/-- The gradual codomain function. -/
def cod : GType → Option GType
  | .unknown => some .unknown
  | .arr _ B => some B
  | _ => none

/-- The domains of the function types that `G` stands for. -/
def domains (G : GType) : Set SType := {a | ∃ b, Conc (.arr a b) G}

/-- The codomains of the function types that `G` stands for. -/
def codomains (G : GType) : Set SType := {b | ∃ a, Conc (.arr a b) G}

/-- **`dom` is the gradual lifting of the domain function**: `dom G` is the
abstraction of the domains `G` stands for. -/
theorem dom_isAbstraction {G D : GType} (h : dom G = some D) :
    IsAbstraction (domains G) D := by
  cases G with
  | unknown =>
    cases h
    refine ⟨fun _ _ => .unknown _, fun G' covers => ?_⟩
    exact prec_iff_concretisation_subset.mpr fun a _ =>
      covers ⟨.int, .unknown _⟩
  | arr A B =>
    cases h
    refine ⟨fun a ⟨_, ha⟩ => (conc_arr_iff.mp ha).1, fun G' covers => ?_⟩
    exact prec_iff_concretisation_subset.mpr fun a ha =>
      covers ⟨witness B, .arr ha (conc_witness B)⟩
  | int => cases h
  | bool => cases h

/-- `dom` is undefined exactly where no function type is represented. -/
theorem dom_eq_none_iff {G : GType} : dom G = none ↔ domains G = ∅ := by
  cases G with
  | unknown =>
    refine ⟨nofun, fun h => ?_⟩
    have member : SType.int ∈ domains .unknown := ⟨.int, .unknown _⟩
    rw [h] at member
    simp at member
  | arr A B =>
    refine ⟨nofun, fun h => ?_⟩
    have member : witness A ∈ domains (.arr A B) :=
      ⟨witness B, .arr (conc_witness A) (conc_witness B)⟩
    rw [h] at member
    simp at member
  | int =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    ext a
    constructor
    · rintro ⟨_, h⟩
      cases h
    · intro h
      simp at h
  | bool =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    ext a
    constructor
    · rintro ⟨_, h⟩
      cases h
    · intro h
      simp at h

/-- **`cod` is the gradual lifting of the codomain function.** -/
theorem cod_isAbstraction {G C : GType} (h : cod G = some C) :
    IsAbstraction (codomains G) C := by
  cases G with
  | unknown =>
    cases h
    refine ⟨fun _ _ => .unknown _, fun G' covers => ?_⟩
    exact prec_iff_concretisation_subset.mpr fun b _ =>
      covers ⟨.int, .unknown _⟩
  | arr A B =>
    cases h
    refine ⟨fun b ⟨_, hb⟩ => (conc_arr_iff.mp hb).2, fun G' covers => ?_⟩
    exact prec_iff_concretisation_subset.mpr fun b hb =>
      covers ⟨witness A, .arr (conc_witness A) hb⟩
  | int => cases h
  | bool => cases h

theorem dom_mono {G G' D : GType} (h : dom G = some D) (hG : Prec G G') :
    ∃ D', dom G' = some D' ∧ Prec D D' := by
  cases hG with
  | unknown => exact ⟨.unknown, rfl, .unknown _⟩
  | int => cases h
  | bool => cases h
  | arr hA _ =>
    cases h
    exact ⟨_, rfl, hA⟩

theorem cod_mono {G G' C : GType} (h : cod G = some C) (hG : Prec G G') :
    ∃ C', cod G' = some C' ∧ Prec C C' := by
  cases hG with
  | unknown => exact ⟨.unknown, rfl, .unknown _⟩
  | int => cases h
  | bool => cases h
  | arr _ hB =>
    cases h
    exact ⟨_, rfl, hB⟩

/-! ## The gradually typed language -/

/-- Gradually typed terms, with de Bruijn variables. -/
inductive Term where
  | var (index : Nat)
  | num (value : Nat)
  | bool (value : Bool)
  | add (left right : Term)
  | ite (condition thenBranch elseBranch : Term)
  | lam (annotation : GType) (body : Term)
  | app (function argument : Term)
  | asc (term : Term) (annotation : GType)

/-- **Gradual typing**: the static rules with consistency, meet, `dom` and
`cod` in place of equality, equate, domain and codomain. -/
inductive HasType : List GType → Term → GType → Prop
  | var {Γ : List GType} {i : Nat} {A : GType} : Γ[i]? = some A → HasType Γ (.var i) A
  | num (Γ : List GType) (n : Nat) : HasType Γ (.num n) .int
  | bool (Γ : List GType) (b : Bool) : HasType Γ (.bool b) .bool
  | add {Γ : List GType} {a b : Term} {A B : GType} :
      HasType Γ a A → HasType Γ b B → Consis A .int → Consis B .int → HasType Γ (.add a b) .int
  | ite {Γ : List GType} {c t e : Term} {C A B M : GType} :
      HasType Γ c C → Consis C .bool → HasType Γ t A → HasType Γ e B → meet A B = some M →
        HasType Γ (.ite c t e) M
  | lam {Γ : List GType} {A B : GType} {body : Term} :
      HasType (A :: Γ) body B → HasType Γ (.lam A body) (.arr A B)
  | app {Γ : List GType} {f a : Term} {F A D C : GType} :
      HasType Γ f F → HasType Γ a A → dom F = some D → Consis A D → cod F = some C →
        HasType Γ (.app f a) C
  | asc {Γ : List GType} {t : Term} {A B : GType} :
      HasType Γ t A → Consis A B → HasType Γ (.asc t B) B

/-- **Precision of programs**: the same program with annotations at least as
precise. -/
inductive TermPrec : Term → Term → Prop
  | var (i : Nat) : TermPrec (.var i) (.var i)
  | num (n : Nat) : TermPrec (.num n) (.num n)
  | bool (b : Bool) : TermPrec (.bool b) (.bool b)
  | add {a b a' b' : Term} : TermPrec a a' → TermPrec b b' → TermPrec (.add a b) (.add a' b')
  | ite {c t e c' t' e' : Term} : TermPrec c c' → TermPrec t t' → TermPrec e e' →
      TermPrec (.ite c t e) (.ite c' t' e')
  | lam {A A' : GType} {body body' : Term} : Prec A A' → TermPrec body body' →
      TermPrec (.lam A body) (.lam A' body')
  | app {f a f' a' : Term} : TermPrec f f' → TermPrec a a' → TermPrec (.app f a) (.app f' a')
  | asc {t t' : Term} {A A' : GType} : TermPrec t t' → Prec A A' →
      TermPrec (.asc t A) (.asc t' A')

theorem forall₂_getElem? : ∀ {Γ Γ' : List GType}, List.Forall₂ Prec Γ Γ' →
    ∀ {i : Nat} {A : GType}, Γ[i]? = some A → ∃ A', Γ'[i]? = some A' ∧ Prec A A'
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hA _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hA⟩
  | _, _, .cons _ rest, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact forall₂_getElem? rest h

/-- **The static gradual guarantee.**  Making annotations less precise keeps a
well-typed program well typed, at a less precise type. -/
theorem static_gradual_guarantee {Γ : List GType} {t : Term} {A : GType}
    (typed : HasType Γ t A) :
    ∀ {Γ' : List GType} {t' : Term}, List.Forall₂ Prec Γ Γ' → TermPrec t t' →
      ∃ A', HasType Γ' t' A' ∧ Prec A A' := by
  induction typed with
  | var hA =>
    intro Γ' t' hΓ ht
    cases ht
    obtain ⟨A', hA', prec⟩ := forall₂_getElem? hΓ hA
    exact ⟨A', .var hA', prec⟩
  | num => intro Γ' t' _ ht; cases ht; exact ⟨_, .num _ _, Prec.refl _⟩
  | bool => intro Γ' t' _ ht; cases ht; exact ⟨_, .bool _ _, Prec.refl _⟩
  | add _ _ hA hB iha ihb =>
    intro Γ' t' hΓ ht
    cases ht with
    | add ha hb =>
      obtain ⟨A', ta, pa⟩ := iha hΓ ha
      obtain ⟨B', tb, pb⟩ := ihb hΓ hb
      exact ⟨_, .add ta tb (hA.mono pa (Prec.refl _)) (hB.mono pb (Prec.refl _)), Prec.refl _⟩
  | ite _ hC _ _ hM ihc iht ihe =>
    intro Γ' t' hΓ ht
    cases ht with
    | ite hc htt hte =>
      obtain ⟨C', tc, pc⟩ := ihc hΓ hc
      obtain ⟨A', tt, pa⟩ := iht hΓ htt
      obtain ⟨B', te, pb⟩ := ihe hΓ hte
      obtain ⟨M', hM', pm⟩ := meet_mono hM pa pb
      exact ⟨M', .ite tc (hC.mono pc (Prec.refl _)) tt te hM', pm⟩
  | lam _ ih =>
    intro Γ' t' hΓ ht
    cases ht with
    | lam pA hb =>
      obtain ⟨B', tb, pb⟩ := ih (.cons pA hΓ) hb
      exact ⟨_, .lam tb, .arr pA pb⟩
  | app _ _ hD hAD hC ihf iha =>
    intro Γ' t' hΓ ht
    cases ht with
    | app hf ha =>
      obtain ⟨F', tf, pf⟩ := ihf hΓ hf
      obtain ⟨A', ta, pa⟩ := iha hΓ ha
      obtain ⟨D', hD', pd⟩ := dom_mono hD pf
      obtain ⟨C', hC', pc⟩ := cod_mono hC pf
      exact ⟨C', .app tf ta hD' (hAD.mono pa pd) hC', pc⟩
  | asc _ hAB ih =>
    intro Γ' t' hΓ ht
    cases ht with
    | asc htt pB =>
      obtain ⟨A', tt, pa⟩ := ih hΓ htt
      exact ⟨_, .asc tt (hAB.mono pa pB), pB⟩

/-! ## Conservative extension -/

/-- Static types. -/
inductive HasTypeS : List SType → Term → SType → Prop
  | var {Γ : List SType} {i : Nat} {T : SType} : Γ[i]? = some T → HasTypeS Γ (.var i) T
  | num (Γ : List SType) (n : Nat) : HasTypeS Γ (.num n) .int
  | bool (Γ : List SType) (b : Bool) : HasTypeS Γ (.bool b) .bool
  | add {Γ : List SType} {a b : Term} :
      HasTypeS Γ a .int → HasTypeS Γ b .int → HasTypeS Γ (.add a b) .int
  | ite {Γ : List SType} {c t e : Term} {T : SType} :
      HasTypeS Γ c .bool → HasTypeS Γ t T → HasTypeS Γ e T → HasTypeS Γ (.ite c t e) T
  | lam {Γ : List SType} {T U : SType} {body : Term} :
      HasTypeS (T :: Γ) body U → HasTypeS Γ (.lam T.toG body) (.arr T U)
  | app {Γ : List SType} {f a : Term} {T U : SType} :
      HasTypeS Γ f (.arr T U) → HasTypeS Γ a T → HasTypeS Γ (.app f a) U
  | asc {Γ : List SType} {t : Term} {T : SType} :
      HasTypeS Γ t T → HasTypeS Γ (.asc t T.toG) T

/-- A program is static when every annotation is a static type. -/
def Static : Term → Prop
  | .var _ => True
  | .num _ => True
  | .bool _ => True
  | .add a b => Static a ∧ Static b
  | .ite c t e => Static c ∧ Static t ∧ Static e
  | .lam A body => (∃ T : SType, A = T.toG) ∧ Static body
  | .app f a => Static f ∧ Static a
  | .asc t A => Static t ∧ ∃ T : SType, A = T.toG

theorem SType.toG_injective : Function.Injective SType.toG := by
  intro T U h
  exact conc_toG_iff.mp (h ▸ conc_toG_iff.mpr rfl)

/-- On static types, consistency is equality. -/
theorem consis_toG_iff {T U : SType} : Consis T.toG U.toG ↔ T = U := by
  rw [consis_iff_exists_conc]
  constructor
  · rintro ⟨V, hT, hU⟩
    exact (conc_toG_iff.mp hT).symm.trans (conc_toG_iff.mp hU)
  · rintro rfl
    exact ⟨T, conc_toG_iff.mpr rfl, conc_toG_iff.mpr rfl⟩

/-- On static types, the meet is defined exactly on equal types. -/
theorem meet_toG_eq_some {T U : SType} {M : GType} (h : meet T.toG U.toG = some M) :
    T = U ∧ M = T.toG := by
  have equal : T = U := consis_toG_iff.mp (meet_isSome_iff.mp ⟨M, h⟩)
  subst equal
  refine ⟨rfl, ?_⟩
  apply Prec.antisymm
  · exact ((prec_meet_iff h M).mp (Prec.refl M)).1
  · exact (prec_meet_iff h T.toG).mpr ⟨Prec.refl _, Prec.refl _⟩

theorem meet_toG_self (T : SType) : meet T.toG T.toG = some T.toG := by
  obtain ⟨M, h⟩ := meet_isSome_iff.mpr (consis_toG_iff.mpr (rfl : T = T))
  rw [h, (meet_toG_eq_some h).2]

theorem dom_toG {T : SType} {D : GType} (h : dom T.toG = some D) :
    ∃ a b, T = .arr a b ∧ D = a.toG := by
  cases T with
  | arr a b => cases h; exact ⟨a, b, rfl, rfl⟩
  | int => cases h
  | bool => cases h

theorem cod_toG {T : SType} {C : GType} (h : cod T.toG = some C) :
    ∃ a b, T = .arr a b ∧ C = b.toG := by
  cases T with
  | arr a b => cases h; exact ⟨a, b, rfl, rfl⟩
  | int => cases h
  | bool => cases h

theorem map_toG_getElem? {Γ : List SType} {i : Nat} {A : GType}
    (h : (Γ.map SType.toG)[i]? = some A) : ∃ T, Γ[i]? = some T ∧ A = T.toG := by
  rw [List.getElem?_map] at h
  cases hT : Γ[i]? with
  | none => rw [hT] at h; cases h
  | some T => rw [hT] at h; cases h; exact ⟨T, rfl, rfl⟩

/-- Static typing is gradual typing at static types. -/
theorem hasType_of_static {Γ : List SType} {t : Term} {T : SType} (typed : HasTypeS Γ t T) :
    HasType (Γ.map SType.toG) t T.toG := by
  induction typed with
  | var h => exact .var (by rw [List.getElem?_map, h]; rfl)
  | num => exact .num _ _
  | bool => exact .bool _ _
  | add _ _ iha ihb =>
    exact .add iha ihb (consis_toG_iff.mpr rfl) (consis_toG_iff.mpr rfl)
  | ite _ _ _ ihc iht ihe =>
    exact .ite ihc (consis_toG_iff.mpr (rfl : SType.bool = .bool)) iht ihe (meet_toG_self _)
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha rfl (consis_toG_iff.mpr rfl) rfl
  | asc _ ih => exact .asc ih (consis_toG_iff.mpr rfl)

/-- Gradual typing of a static program in a static context is static typing. -/
theorem static_of_hasType {Γ : List SType} {t : Term} {A : GType}
    (typed : HasType (Γ.map SType.toG) t A) (static : Static t) :
    ∃ T, A = T.toG ∧ HasTypeS Γ t T := by
  generalize hΓ : Γ.map SType.toG = Δ at typed
  induction typed generalizing Γ with
  | var h =>
    subst hΓ
    obtain ⟨T, hT, rfl⟩ := map_toG_getElem? h
    exact ⟨T, rfl, .var hT⟩
  | num => exact ⟨.int, rfl, .num _ _⟩
  | bool => exact ⟨.bool, rfl, .bool _ _⟩
  | add _ _ hA hB iha ihb =>
    obtain ⟨T, rfl, ta⟩ := iha static.1 hΓ
    obtain ⟨U, rfl, tb⟩ := ihb static.2 hΓ
    rw [show GType.int = SType.int.toG from rfl, consis_toG_iff] at hA hB
    subst hA hB
    exact ⟨.int, rfl, .add ta tb⟩
  | ite _ hC _ _ hM ihc iht ihe =>
    obtain ⟨C, rfl, tc⟩ := ihc static.1 hΓ
    obtain ⟨T, rfl, tt⟩ := iht static.2.1 hΓ
    obtain ⟨U, rfl, te⟩ := ihe static.2.2 hΓ
    rw [show GType.bool = SType.bool.toG from rfl, consis_toG_iff] at hC
    subst hC
    obtain ⟨rfl, rfl⟩ := meet_toG_eq_some hM
    exact ⟨T, rfl, .ite tc tt te⟩
  | lam _ ih =>
    obtain ⟨⟨T, rfl⟩, sb⟩ := static
    obtain ⟨U, rfl, tb⟩ := ih sb (Γ := T :: Γ) (by rw [List.map_cons, hΓ])
    exact ⟨.arr T U, rfl, .lam tb⟩
  | app _ _ hD hAD hC ihf iha =>
    obtain ⟨F, rfl, tf⟩ := ihf static.1 hΓ
    obtain ⟨A, rfl, ta⟩ := iha static.2 hΓ
    obtain ⟨a, b, rfl, rfl⟩ := dom_toG hD
    obtain ⟨a', b', equal, rfl⟩ := cod_toG hC
    cases equal
    rw [consis_toG_iff] at hAD
    subst hAD
    exact ⟨b, rfl, .app tf ta⟩
  | asc _ hAB ih =>
    obtain ⟨st, ⟨U, rfl⟩⟩ := static
    obtain ⟨T, rfl, tt⟩ := ih st hΓ
    rw [consis_toG_iff] at hAB
    subst hAB
    exact ⟨T, rfl, .asc tt⟩

/-- **Conservative extension**: on static programs in static contexts, the
gradual type system coincides with the static one. -/
theorem static_iff_gradual {Γ : List SType} {t : Term} (static : Static t) (T : SType) :
    HasTypeS Γ t T ↔ HasType (Γ.map SType.toG) t T.toG := by
  constructor
  · exact hasType_of_static
  · intro typed
    obtain ⟨U, equal, typedS⟩ := static_of_hasType typed static
    rw [SType.toG_injective equal]
    exact typedS

/-! ## Dynamic embedding -/

/-- Every annotation `?`, every subterm ascribed `?`. -/
def embed : Term → Term
  | .var i => .var i
  | .num n => .asc (.num n) .unknown
  | .bool b => .asc (.bool b) .unknown
  | .add a b => .asc (.add (embed a) (embed b)) .unknown
  | .ite c t e => .ite (embed c) (embed t) (embed e)
  | .lam _ body => .asc (.lam .unknown (embed body)) .unknown
  | .app f a => .app (embed f) (embed a)
  | .asc t _ => embed t

/-- Every variable is below the given bound. -/
def WellScoped : Nat → Term → Prop
  | n, .var i => i < n
  | _, .num _ => True
  | _, .bool _ => True
  | n, .add a b => WellScoped n a ∧ WellScoped n b
  | n, .ite c t e => WellScoped n c ∧ WellScoped n t ∧ WellScoped n e
  | n, .lam _ body => WellScoped (n + 1) body
  | n, .app f a => WellScoped n f ∧ WellScoped n a
  | n, .asc t _ => WellScoped n t

/-- **Dynamic embedding**: a well-scoped program is well typed at `?` in the
context where every variable has type `?`. -/
theorem embed_hasType : ∀ (t : Term) (n : Nat), WellScoped n t →
    HasType (List.replicate n .unknown) (embed t) .unknown
  | .var i, n, h => .var (by
      have below : i < n := h
      simp [below])
  | .num _, _, _ => .asc (.num _ _) (.unknownRight _)
  | .bool _, _, _ => .asc (.bool _ _) (.unknownRight _)
  | .add a b, n, ⟨ha, hb⟩ =>
      .asc (.add (embed_hasType a n ha) (embed_hasType b n hb) (.unknownLeft _) (.unknownLeft _))
        (.unknownRight _)
  | .ite c t e, n, ⟨hc, ht, he⟩ =>
      .ite (embed_hasType c n hc) (.unknownLeft _) (embed_hasType t n ht) (embed_hasType e n he) rfl
  | .lam _ body, n, h =>
      .asc (.lam (by simpa [List.replicate_succ] using embed_hasType body (n + 1) h))
        (.unknownRight _)
  | .app f a, n, ⟨hf, ha⟩ =>
      .app (embed_hasType f n hf) (embed_hasType a n ha) rfl (.unknownLeft _) rfl
  | .asc t _, n, h => embed_hasType t n h

/-! ## Controls -/

namespace Controls

/-- `λx:Int. x + 1`. -/
def successor (A : GType) : Term := .lam A (.add (.var 0) (.num 1))

theorem successor_int : HasType [] (successor .int) (.arr .int .int) :=
  .lam (.add (.var rfl) (.num _ _) .int .int)

/-- **Positive**: loosening the annotation to `?` keeps the program typed, at a
less precise type. -/
theorem successor_unknown :
    HasType [] (successor .unknown) (.arr .unknown .int) ∧
      Prec (.arr .int .int) (.arr .unknown .int) :=
  ⟨.lam (.add (.var rfl) (.num _ _) (.unknownLeft _) .int), .arr (.unknown _) .int⟩

/-- **Negative**: replacing the annotation by an inconsistent one, which is not
a precision step, breaks typing. -/
theorem inconsistent_breaks : ¬ ∃ A, HasType [] (successor .bool) A := by
  rintro ⟨A, typed⟩
  cases typed with
  | lam body =>
    cases body with
    | add hx _ hA _ =>
      cases hx with
      | var h =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact absurd hA nofun

/-- `Bool` is not a precision step up from `Int`. -/
theorem not_prec_int_bool : ¬ Prec .int .bool := nofun

end Controls

end Mettapedia.OSLF.Programs.GradualGuarantee
