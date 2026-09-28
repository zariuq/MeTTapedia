import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation

/-!
# Type formers as terms of universes

The type formers build terms of a universe from terms of universes. A
dependent function or pair type whose domain and codomain are types of one
level is interpreted at that level: its partial equivalence is read from the
interpretations of the domain and of the codomain at each argument, at every
world. Two such types with related domains and related codomains at related
arguments share this partial equivalence. An identity type relates all terms
when its endpoints are related, so two identity types with related carriers
and related endpoints relate the same pairs.

A context may also be converted along a type equality at a universe: related
substitutions for the one extension are related substitutions for the other.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Families of types at one level -/

/-- The partial equivalences of a dependent function or pair type whose domain
and codomain are read at level `k`, at every world. -/
def PiRel.ofFamily (M : Model Head L) (k : L) {n : Nat} (ξ : World M.reading n) (A : Tm Head n)
    (B : Tm Head (n + 1)) : PiRel Head ξ where
  dom := fun {_ ξ' ρ} _ a b => ∃ R, InterpAt M k ξ' (Presentation.rename ρ A) R ∧ R a b
  cod := fun {_ ξ' ρ} _ {a} _ t u =>
    ∃ R, InterpAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) R ∧ R t u

section Family

variable (laws : M.Laws)
include laws

theorem PiRel.ofFamily_dom {k : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {R : Rel Head m}
    (interp : InterpAt M k ξ' (Presentation.rename ρ A) R) :
    (PiRel.ofFamily M k ξ A B).dom w = R := by
  funext a b
  apply propext
  constructor
  · rintro ⟨R', interp', r⟩
    rw [InterpAt.deterministic laws interp' interp] at r
    exact r
  · intro r
    exact ⟨R, interp, r⟩

theorem PiRel.ofFamily_cod {k : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
    (ha : (PiRel.ofFamily M k ξ A B).dom w a a) {R : Rel Head m}
    (interp : InterpAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) R) :
    (PiRel.ofFamily M k ξ A B).cod w ha = R := by
  funext t u
  apply propext
  constructor
  · rintro ⟨R', interp', r⟩
    rw [InterpAt.deterministic laws interp' interp] at r
    exact r
  · intro r
    exact ⟨R, interp, r⟩

/-- Dependent function and pair types with related domains, and codomains
related at related arguments, have one interpretation at the level. -/
theorem interp_family {k : L} {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (dom : universeAt M k ξ A A')
    (cod : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {R : Rel Head m} {a b : Tm Head m}, InterpAt M k ξ' (Presentation.rename ρ A) R → R a b →
        universeAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
          (inst0 b (Presentation.rename (liftRen ρ) B'))) :
    ∃ P : PiRel Head ξ,
      (InterpAt M k ξ (.pi A B) P.rel ∧ InterpAt M k ξ (.pi A' B') P.rel) ∧
      (InterpAt M k ξ (.sigma A B) P.pairRel ∧ InterpAt M k ξ (.sigma A' B') P.pairRel) := by
  let P := PiRel.ofFamily M k ξ A B
  have domI : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      InterpAt M k ξ' (Presentation.rename ρ A) (P.dom w) ∧
        InterpAt M k ξ' (Presentation.rename ρ A') (P.dom w) := by
    intro _ _ _ w
    obtain ⟨R, hA, hA'⟩ := dom w
    rw [PiRel.ofFamily_dom laws w hA]
    exact ⟨hA, hA'⟩
  have codI : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
      (ha : P.dom w a a),
      InterpAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (P.cod w ha) ∧
        InterpAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ) B')) (P.cod w ha) := by
    intro _ _ _ w a ha
    obtain ⟨R, hA, _⟩ := dom w
    have ha' : R a a := by
      rw [← PiRel.ofFamily_dom laws w hA]
      exact ha
    obtain ⟨Rc, hB, hB'⟩ := universeAt.den (cod w hA ha')
    rw [PiRel.ofFamily_cod laws w ha hB]
    exact ⟨hB, hB'⟩
  have respect : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a b : Tm Head m} (ha : P.dom w a a) (hb : P.dom w b b), P.dom w a b →
        P.cod w ha = P.cod w hb := by
    intro _ _ _ w a b ha hb hab
    obtain ⟨R, hA, _⟩ := dom w
    have hab' : R a b := by
      rw [← PiRel.ofFamily_dom laws w hA]
      exact hab
    have hb' : R b b := by
      rw [← PiRel.ofFamily_dom laws w hA]
      exact hb
    obtain ⟨R₁, hBa, hB'b⟩ := universeAt.den (cod w hA hab')
    obtain ⟨R₂, hBb, hB'b₂⟩ := universeAt.den (cod w hA hb')
    rw [PiRel.ofFamily_cod laws w ha hBa, PiRel.ofFamily_cod laws w hb hBb]
    exact InterpAt.deterministic laws hB'b hB'b₂
  exact ⟨P,
    ⟨Interp.pi .refl P (fun w => (domI w).1) (fun {_ _ _} w {_} ha => (codI w ha).1) respect,
      Interp.pi .refl P (fun w => (domI w).2) (fun {_ _ _} w {_} ha => (codI w ha).2) respect⟩,
    ⟨Interp.sigma .refl P (fun w => (domI w).1) (fun {_ _ _} w {_} ha => (codI w ha).1) respect,
      Interp.sigma .refl P (fun w => (domI w).2) (fun {_ _ _} w {_} ha => (codI w ha).2) respect⟩⟩

end Family

/-! ## Formation and congruence at a universe -/

theorem level_join {u v w : Head} (join : M.rules.join u v w) :
    M.levels.level u ≤ M.levels.level w ∧ M.levels.level v ≤ M.levels.level w := by
  rw [(M.levels.join_level join).2]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

section Rules

variable (laws : M.Laws)
include laws

/-- The codomains of two dependent types over one context are related at a
level at related arguments of the domain, under related substitutions. -/
theorem codomain_related {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B B' : Tm Head (n + 1)}
    {v : Head} {k : L} (le : M.levels.level v ≤ k)
    (related : ∀ {m : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m},
      EqSubst M (.snoc Γ A) ξ τ τ' →
        universeAt M (M.levels.level v) ξ (Presentation.subst τ B) (Presentation.subst τ' B'))
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    ∀ {m' : Nat} {ξ' : World M.reading m'} {ρ : Ren m m'}, Morph ξ ξ' ρ →
      ∀ {R : Rel Head m'} {a b : Tm Head m'},
        InterpAt M k ξ' (Presentation.rename ρ (Presentation.subst σ A)) R → R a b →
          universeAt M k ξ' (inst0 a (Presentation.rename (liftRen ρ)
              (Presentation.subst (liftSub σ) B)))
            (inst0 b (Presentation.rename (liftRen ρ) (Presentation.subst (liftSub σ') B'))) := by
  intro _ _ _ w R a b hA hab
  rw [rename_subst] at hA
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact universeAt.mono le (related (EqSubst.cons (EqSubst.rename laws e w) ⟨k, hA⟩ hab))

/-- A dependent function type formed from terms of universes is a term of
their join. -/
theorem ValidTm.piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (validB : ValidTm M (.snoc Γ A) B (.head v)) (hv : M.rules.isUniverse v)
    (join : M.rules.join u v w) : ValidTm M Γ (.pi A B) (.head w) := by
  have hw := (M.levels.join_level join).1
  obtain ⟨leU, leV⟩ := level_join join
  refine ⟨ValidTy.sort hw, fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hw den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨P, ⟨hPi, hPi'⟩, _⟩ := interp_family laws (universeAt.mono leU (validA.universe hu e'))
    (codomain_related laws leV (fun e'' => validB.universe hv e'') e')
  exact ⟨P.rel, hPi, hPi'⟩

/-- A dependent pair type formed from terms of universes is a term of their
join. -/
theorem ValidTm.sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTm M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (validB : ValidTm M (.snoc Γ A) B (.head v)) (hv : M.rules.isUniverse v)
    (join : M.rules.join u v w) : ValidTm M Γ (.sigma A B) (.head w) := by
  have hw := (M.levels.join_level join).1
  obtain ⟨leU, leV⟩ := level_join join
  refine ⟨ValidTy.sort hw, fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hw den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨P, _, hS, hS'⟩ := interp_family laws (universeAt.mono leU (validA.universe hu e'))
    (codomain_related laws leV (fun e'' => validB.universe hv e'') e')
  exact ⟨P.pairRel, hS, hS'⟩

/-- Dependent function types with equal domains and codomains are equal terms
of the join of their universes. -/
theorem ValidEq.piCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEq M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (eqB : ValidEq M (.snoc Γ A) B B' (.head v))
    (hv : M.rules.isUniverse v) (join : M.rules.join u v w)
    (validPi' : ValidTm M Γ (.pi A' B') (.head w)) :
    ValidEq M Γ (.pi A B) (.pi A' B') (.head w) := by
  have hw := (M.levels.join_level join).1
  obtain ⟨leU, leV⟩ := level_join join
  refine ⟨ValidTm.piForm laws eqA.1 hu eqB.1 hv join, validPi',
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hw den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨P, ⟨hPi, hPi'⟩, _⟩ := interp_family laws (universeAt.mono leU (eqA.universe hu e'))
    (codomain_related laws leV (fun e'' => eqB.universe hv e'') e')
  exact ⟨P.rel, hPi, hPi'⟩

/-- Dependent pair types with equal domains and codomains are equal terms of
the join of their universes. -/
theorem ValidEq.sigmaCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEq M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (eqB : ValidEq M (.snoc Γ A) B B' (.head v))
    (hv : M.rules.isUniverse v) (join : M.rules.join u v w)
    (validSigma' : ValidTm M Γ (.sigma A' B') (.head w)) :
    ValidEq M Γ (.sigma A B) (.sigma A' B') (.head w) := by
  have hw := (M.levels.join_level join).1
  obtain ⟨leU, leV⟩ := level_join join
  refine ⟨ValidTm.sigmaForm laws eqA.1 hu eqB.1 hv join, validSigma',
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hw den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨P, _, hS, hS'⟩ := interp_family laws (universeAt.mono leU (eqA.universe hu e'))
    (codomain_related laws leV (fun e'' => eqB.universe hv e'') e')
  exact ⟨P.pairRel, hS, hS'⟩

/-- Identity types over related carriers with related endpoints relate the
same pairs. -/
theorem interp_ident {k : L} {n : Nat} {ξ : World M.reading n} {A A' a a' b b' : Tm Head n}
    (ty : universeAt M k ξ A A')
    (lhs : ∀ {R : Rel Head n}, InterpAt M k ξ A R → R a a')
    (rhs : ∀ {R : Rel Head n}, InterpAt M k ξ A R → R b b') :
    ∃ R, InterpAt M k ξ (.id A a b) R ∧ InterpAt M k ξ (.id A' a' b') R := by
  obtain ⟨R, hA, hA'⟩ := universeAt.den ty
  have ha := lhs hA
  have hb := rhs hA
  have symm : ∀ {t u : Tm Head n}, R t u → R u t := InterpAt.symm laws hA
  have trans : ∀ {t u v : Tm Head n}, R t u → R u v → R t v := InterpAt.trans laws hA
  have same : (fun _ _ : Tm Head n => R a b) = fun _ _ => R a' b' := by
    funext _ _
    exact propext ⟨fun h => trans (symm ha) (trans h hb),
      fun h => trans ha (trans h (symm hb))⟩
  refine ⟨fun _ _ => R a b, Interp.ident .refl R hA (trans ha (symm ha)) (trans hb (symm hb)), ?_⟩
  rw [same]
  exact Interp.ident .refl R hA' (trans (symm ha) ha) (trans (symm hb) hb)

/-- An identity type formed from a term of a universe and two of its terms is
a term of the universe. -/
theorem ValidTm.idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
    (validA : ValidTm M Γ A (.head u)) (hu : M.rules.isUniverse u) (valida : ValidTm M Γ a A)
    (validb : ValidTm M Γ b A) : ValidTm M Γ (.id A a b) (.head u) := by
  refine ⟨ValidTy.sort hu, fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hu den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  exact interp_ident laws (validA.universe hu e') (fun hA => valida.2 e' ⟨_, hA⟩)
    (fun hA => validb.2 e' ⟨_, hA⟩)

/-- Identity types with equal carriers and endpoints are equal terms of the
universe. -/
theorem ValidEq.idCong {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
    {u : Head} (eqA : ValidEq M Γ A A' (.head u)) (hu : M.rules.isUniverse u)
    (eqa : ValidEq M Γ a a' A) (eqb : ValidEq M Γ b b' A)
    (validId' : ValidTm M Γ (.id A' a' b') (.head u)) :
    ValidEq M Γ (.id A a b) (.id A' a' b') (.head u) := by
  refine ⟨ValidTm.idForm laws eqA.1 hu eqa.1 eqb.1, validId', fun {_ ξ σ σ'} e {R} den => ?_⟩
  rw [Den.sort_inv laws hu den]
  refine universeAt.of_interp laws (fun e' => ?_) e
  exact interp_ident laws (eqA.universe hu e') (fun hA => eqa.2.2 e' ⟨_, hA⟩)
    (fun hA => eqb.2.2 e' ⟨_, hA⟩)

/-! ## Conversion of a context extension -/

/-- Related substitutions for an extension by a type are related for an
extension by an equal type of a universe. -/
theorem ValidMor.convert {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (ctx : ValidCtx M Γ) (eqA : ValidEq M Γ A A' (.head u)) (hu : M.rules.isUniverse u) :
    ValidMor M (.snoc Γ A') ids (.snoc Γ A) := by
  intro _ ξ σ σ' e
  rw [show (fun i => Presentation.subst σ (ids i)) = σ from rfl,
    show (fun i => Presentation.subst σ' (ids i)) = σ' from rfl]
  obtain ⟨tail, R, den, h⟩ := e
  obtain ⟨R', denA, denA'⟩ := eqA.den hu (EqSubst.refl_left laws ctx tail)
  rw [Den.deterministic laws den denA'] at h
  exact ⟨tail, R', denA, h⟩

end Rules

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
