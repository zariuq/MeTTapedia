import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families

/-!
# Type formers as terms of universes in model S

The type formers build terms of a universe from terms of universes. The
universe relation relates types with one pack and one shape at every world
reached by a morphism, so a type former must be shown to give both.

**One pack.** The pack of a type at a level is described by its
interpretations there (`Pack.describe`): a type has at most one interpretation
at a level, so the description is its interpretation whenever it has one. A
dependent function or pair type whose domain and codomain are types of one
level is interpreted at that level by the family that reads its domain and its
codomain there, at every world reached by a morphism. Codomains at related
arguments are related in the universe, so they have one pack, and the family
respects the domain. Two such types with related domains, and codomains
related at related arguments, are interpreted by one family
(`ValueSide.interp_family`).

**One shape.** There is no skeleton relation to compare the instances of a
codomain. Its role is played by the shapes the universe relation carries:
related domains are of one shape at every world reached by a morphism, and
codomains related at related arguments are of one shape there, which are the
premises of the clauses of dependent function and pair types
(`ValueSide.shape_family`). Under related valuations, a codomain at related arguments is
the codomain under related valuations of the extended context, of one shape
by the validity of the codomain as a term of its universe, and of one shape
at the level of the join by cumulativity (`universePack_mono`, through
`Shape.mono`).

An identity type is a leaf: it relates all terms. Two identity types over
related carriers with related endpoints have one pack, realized by the
identity candidate of the endpoints' relation, and they are of one shape as
hereditarily total types (`ValueSide.interp_ident`).

A context may also be converted along a type equality at a universe: related
valuations of the one extension are related valuations of the other.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization (inst0_rename_subst_liftSub)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-! ## Valuations and universes -/

section Rules

variable (laws : M.Laws)
include laws

/-- The realizer instance of the codomain of a dependent type is strongly
normalizing: extending a related valuation by the daimon, a valid value of the
domain, realized by a fresh variable, gives a related valuation of the extended
context, under which the codomain has a strongly normalizing realizer
instance. -/
theorem codomain_sn {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (validA : ValidTyS M Γ A) (validB : ValidTyS M (.snoc Γ A) B) {m r : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    SN M.realizers.rules (Presentation.subst (liftSub ς) B) := by
  obtain ⟨P, den, -, -⟩ := validA e
  obtain ⟨-, -, -, sn⟩ := validB (EqSubstS.cons (e.renameReal wk) den (den.star_val laws.value)
    ((P.real _).var_mem (RootShape.spineHeaded M.realizers.shape) 0))
  exact sn

/-- Instances of two types under related valuations are related in a universe
when related valuations give them one interpretation and one shape at its
level. -/
theorem universeAt.of_interp {k : L} {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n}
    (here : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς →
        ∃ P, InterpAt M.value k ξ (Presentation.subst σ T) P ∧
          InterpAt M.value k ξ (Presentation.subst σ' T') P ∧
          Shape M.value (InterpAt M.value k) .pair ξ (Presentation.subst σ T)
            (Presentation.subst σ' T'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    (universeAt M k ξ).rel (Presentation.subst σ T) (Presentation.subst σ' T') := by
  intro _ _ _ w
  rw [rename_subst, rename_subst]
  exact here (EqSubstS.rename laws e w)

/-- A term of a universe is valid when related valuations give related instances
and a strongly normalizing realizer instance. -/
theorem ValidTmS.of_universe {n : Nat} {Γ : Ctx Head n} {T : Tm Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u)
    (rel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς →
        (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ T)
            (Presentation.subst σ' T) ∧
          SN M.realizers.rules (Presentation.subst ς T)) :
    ValidTmS M Γ T (.head u) := by
  refine ⟨ValidTyS.sort isUniverse, fun {_ _ _ _ _ _} e {P} den => ?_⟩
  rw [DenS.sort_inv laws isUniverse den]
  exact rel e

/-- Two valid terms of a universe are validly equal when related valuations give
related instances of the one and the other. -/
theorem ValidEqS.of_universe {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n} {u : Head}
    (isUniverse : M.rules.isUniverse u) (valid : ValidTmS M Γ T (.head u))
    (valid' : ValidTmS M Γ T' (.head u))
    (rel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς →
        (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ T)
          (Presentation.subst σ' T')) :
    ValidEqS M Γ T T' (.head u) := by
  refine ⟨valid, valid', fun {_ _ _ _ _ _} e {P} den => ?_⟩
  rw [DenS.sort_inv laws isUniverse den]
  exact rel e

/-- The codomains of two dependent types over one context are related at a
level at related arguments of the domain, under related valuations. -/
theorem codomain_related {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B B' : Tm Head (n + 1)}
    {v : Head} {k : L} (le : M.levels.level v ≤ k)
    (related : ∀ {m r : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m}
      {ς : Sub Head (n + 1) r}, EqSubstS M (.snoc Γ A) ξ τ τ' ς →
        (universeAt M (M.levels.level v) ξ).rel (Presentation.subst τ B)
          (Presentation.subst τ' B'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    ∀ {m' : Nat} {ξ' : World M.reading m'} {ρ : Ren m m'}, Morph ξ ξ' ρ →
      ∀ {P : Pack M.value m'} {a b : Tm Head m'},
        InterpAt M.value k ξ' (Presentation.rename ρ (Presentation.subst σ A)) P →
          P.rel a b →
            (universeAt M k ξ').rel
              (inst0 a (Presentation.rename (liftRen ρ)
                (Presentation.subst (liftSub σ) B)))
              (inst0 b (Presentation.rename (liftRen ρ)
                (Presentation.subst (liftSub σ') B'))) := by
  intro _ _ _ w P a b hA hab
  rw [rename_subst] at hA
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact universeAt.mono laws.value le
    (related (EqSubstS.cons ((EqSubstS.rename laws e w).renameReal wk) ⟨k, hA⟩ hab
      ((P.real a).var_mem (RootShape.spineHeaded M.realizers.shape) 0)))

/-- **The formation rules at a universe.** Under related valuations, one family
at a level interprets the instances of two dependent types whose domains are
related in a universe below it, and whose codomains are related in a universe
below it under related valuations; and the instances are of one shape at that
level, as dependent function types and as dependent pair types. -/
theorem family_related {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v : Head} {k : L} (leU : M.levels.level u ≤ k)
    (leV : M.levels.level v ≤ k)
    (domRel : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r},
      EqSubstS M Γ ξ σ σ' ς →
        (universeAt M (M.levels.level u) ξ).rel (Presentation.subst σ A)
          (Presentation.subst σ' A'))
    (codRel : ∀ {m r : Nat} {ξ : World M.reading m} {τ τ' : Sub Head (n + 1) m}
      {ς : Sub Head (n + 1) r}, EqSubstS M (.snoc Γ A) ξ τ τ' ς →
        (universeAt M (M.levels.level v) ξ).rel (Presentation.subst τ B)
          (Presentation.subst τ' B'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) :
    ∃ Q : ValueSide.PiPack M.value ξ,
      Q.Interprets (InterpAt M.value k) (Presentation.subst σ A)
          (Presentation.subst (liftSub σ) B) ∧
        Q.Interprets (InterpAt M.value k) (Presentation.subst σ' A')
          (Presentation.subst (liftSub σ') B') ∧
        Shape M.value (InterpAt M.value k) .pair ξ (Presentation.subst σ (.pi A B))
          (Presentation.subst σ' (.pi A' B')) ∧
        Shape M.value (InterpAt M.value k) .pair ξ (Presentation.subst σ (.sigma A B))
          (Presentation.subst σ' (.sigma A' B')) := by
  have dom : (universeAt M k ξ).rel (Presentation.subst σ A) (Presentation.subst σ' A') :=
    universeAt.mono laws.value leU (domRel e)
  obtain ⟨Q, interprets, interprets'⟩ :=
    interp_family dom (codomain_related laws leV codRel e) laws.value
  exact ⟨Q, interprets, interprets', shape_family dom (codomain_related laws leV codRel e)⟩

/-- A dependent function type formed from terms of universes is a term of their
join. -/
theorem ValidTmS.piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTmS M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (validB : ValidTmS M (.snoc Γ A) B (.head v)) (hv : M.rules.isUniverse v)
    (join : M.rules.join u v w) : ValidTmS M Γ (.pi A B) (.head w) := by
  obtain ⟨leU, leV⟩ := level_join (V := M.value) join
  refine ValidTmS.of_universe laws (M.levels.join_level join).1 (fun e => ⟨?_, ?_⟩)
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', shape, -⟩ := family_related laws leU leV
      (fun e'' => (validA.universe hu e'').1) (fun e'' => (validB.universe hv e'').1) e'
    exact ⟨_, PiPack.Interprets.pi interprets, PiPack.Interprets.pi interprets', shape⟩
  · exact SN.pi (RootShape.spineHeaded M.realizers.shape) (validA.universe hu e).2
      (codomain_sn laws (validA.validTy hu) (validB.validTy hv) e)

/-- A dependent pair type formed from terms of universes is a term of their
join. -/
theorem ValidTmS.sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {u v w : Head} (validA : ValidTmS M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (validB : ValidTmS M (.snoc Γ A) B (.head v)) (hv : M.rules.isUniverse v)
    (join : M.rules.join u v w) : ValidTmS M Γ (.sigma A B) (.head w) := by
  obtain ⟨leU, leV⟩ := level_join (V := M.value) join
  refine ValidTmS.of_universe laws (M.levels.join_level join).1 (fun e => ⟨?_, ?_⟩)
  · refine universeAt.of_interp laws (fun e' => ?_) e
    obtain ⟨Q, interprets, interprets', -, shape⟩ := family_related laws leU leV
      (fun e'' => (validA.universe hu e'').1) (fun e'' => (validB.universe hv e'').1) e'
    exact ⟨_, PiPack.Interprets.sigma interprets, PiPack.Interprets.sigma interprets', shape⟩
  · exact SN.sigma (RootShape.spineHeaded M.realizers.shape) (validA.universe hu e).2
      (codomain_sn laws (validA.validTy hu) (validB.validTy hv) e)

/-- Dependent function types with equal domains and codomains are equal terms
of the join of their universes. -/
theorem ValidEqS.piCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEqS M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (eqB : ValidEqS M (.snoc Γ A) B B' (.head v))
    (hv : M.rules.isUniverse v) (join : M.rules.join u v w)
    (validPi' : ValidTmS M Γ (.pi A' B') (.head w)) :
    ValidEqS M Γ (.pi A B) (.pi A' B') (.head w) := by
  obtain ⟨leU, leV⟩ := level_join (V := M.value) join
  refine ValidEqS.of_universe laws (M.levels.join_level join).1
    (ValidTmS.piForm laws eqA.1 hu eqB.1 hv join) validPi' fun e => ?_
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨Q, interprets, interprets', shape, -⟩ := family_related laws leU leV
    (fun e'' => eqA.universe hu e'') (fun e'' => eqB.universe hv e'') e'
  exact ⟨_, PiPack.Interprets.pi interprets, PiPack.Interprets.pi interprets', shape⟩

/-- Dependent pair types with equal domains and codomains are equal terms of the
join of their universes. -/
theorem ValidEqS.sigmaCong {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {u v w : Head} (eqA : ValidEqS M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (eqB : ValidEqS M (.snoc Γ A) B B' (.head v))
    (hv : M.rules.isUniverse v) (join : M.rules.join u v w)
    (validSigma' : ValidTmS M Γ (.sigma A' B') (.head w)) :
    ValidEqS M Γ (.sigma A B) (.sigma A' B') (.head w) := by
  obtain ⟨leU, leV⟩ := level_join (V := M.value) join
  refine ValidEqS.of_universe laws (M.levels.join_level join).1
    (ValidTmS.sigmaForm laws eqA.1 hu eqB.1 hv join) validSigma' fun e => ?_
  refine universeAt.of_interp laws (fun e' => ?_) e
  obtain ⟨Q, interprets, interprets', -, shape⟩ := family_related laws leU leV
    (fun e'' => eqA.universe hu e'') (fun e'' => eqB.universe hv e'') e'
  exact ⟨_, PiPack.Interprets.sigma interprets, PiPack.Interprets.sigma interprets', shape⟩

/-! ## Identity types -/

/-- An identity type formed from a term of a universe and two of its terms is
a term of the universe. -/
theorem ValidTmS.idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
    (validA : ValidTmS M Γ A (.head u)) (hu : M.rules.isUniverse u)
    (valida : ValidTmS M Γ a A) (validb : ValidTmS M Γ b A) :
    ValidTmS M Γ (.id A a b) (.head u) := by
  refine ValidTmS.of_universe laws hu (fun e => ⟨?_, ?_⟩)
  · exact universeAt.of_interp laws (fun e' => interp_ident laws.value (validA.universe hu e').1
      (fun interp => (valida.2 e' ⟨_, interp⟩).1) (fun interp => (validb.2 e' ⟨_, interp⟩).1)) e
  · obtain ⟨P, den, -, -⟩ := valida.1 e
    exact SN.id (RootShape.spineHeaded M.realizers.shape) (validA.universe hu e).2
      ((P.real _).sn (valida.2 e den).2) ((P.real _).sn (validb.2 e den).2)

/-- Identity types with equal carriers and endpoints are equal terms of the
universe. -/
theorem ValidEqS.idCong {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
    {u : Head} (eqA : ValidEqS M Γ A A' (.head u))
    (hu : M.rules.isUniverse u) (eqa : ValidEqS M Γ a a' A) (eqb : ValidEqS M Γ b b' A)
    (validId' : ValidTmS M Γ (.id A' a' b') (.head u)) :
    ValidEqS M Γ (.id A a b) (.id A' a' b') (.head u) :=
  ValidEqS.of_universe laws hu (ValidTmS.idForm laws eqA.1 hu eqa.1 eqb.1) validId'
    fun e => universeAt.of_interp laws (fun e' => interp_ident laws.value (eqA.universe hu e')
      (fun interp => eqa.2.2 e' ⟨_, interp⟩) (fun interp => eqb.2.2 e' ⟨_, interp⟩)) e

/-! ## Conversion of a context extension -/

/-- Related valuations for an extension by a type are related valuations for an
extension by an equal type of a universe. -/
theorem ValidMorS.convert {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {u : Head}
    (ctx : ValidCtxS M Γ) (eqA : ValidEqS M Γ A A' (.head u)) (hu : M.rules.isUniverse u) :
    ValidMorS M (.snoc Γ A') ids (.snoc Γ A) := by
  intro _ _ ξ σ σ' ς e
  show EqSubstS M (.snoc Γ A) ξ σ σ' ς
  obtain ⟨tail, P, den, h⟩ := e
  obtain ⟨P', denA, denA'⟩ := eqA.den hu (EqSubstS.refl_left laws ctx tail)
  obtain rfl := DenS.deterministic laws.value den denA'
  exact ⟨tail, P, denA, h⟩

end Rules

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
