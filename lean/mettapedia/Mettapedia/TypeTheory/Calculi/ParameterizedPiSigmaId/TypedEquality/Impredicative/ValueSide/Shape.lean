import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Inductive

/-!
# Types of one shape

Types with one pack need not have one structure: `Π U₀ ⋆` and `Π U₁ ⋆` relate
every pair of functions and have the same realizers, while their domains are
universes of different levels. The transport inspects structure, so the
universe relation relates types that have one pack *and one shape*
(`universePack`). Shapes are read over any interpretation `I` of types:

* two hereditarily total types have one shape, whatever their structure;
* so do two universes of one level, one type constant on both sides, two
  dependent function types whose domains have one pack and one shape, and whose
  codomains at related points have packs with one relation and one shape, and
  two dependent pair types whose domains, and codomains at related points, have
  packs with one relation and one shape. Function types are compared at every
  world reached by a morphism, pair types at the world itself, as their packs
  are. The domain of a function type carries its whole pack, realizers
  included: an argument is checked against the domain, so a function type
  of one shape with a declared one reads its arguments' realizers as the
  declared domain does;
* a type is hereditarily total when it is a leaf (a type relating every pair
  that reduces to no form the transport inspects), a dependent function type
  over a domain of one shape with itself into hereditarily total types, or a
  dependent pair type of hereditarily total types.

## The laws

For an interpretation with the facts of `InterpFacts`, the relation is
symmetric, and transitive on interpreted types; a type of one shape with a
hereditarily total type is hereditarily total when it is interpreted; and the
relation grows with the interpretation.

Transitivity as stated does not go through by induction on the first
derivation. Where a hereditarily total type `Y` meets a dependent function type
`Z`, the third type `Z` must be shown hereditarily total, which needs the domain
of `Z` of one shape with itself: the composite of the derivation relating the
domains of `Y` and `Z` with its own inverse, neither of which is a
subderivation of the first derivation. The induction therefore proves a
stronger statement: for every derivation relating `P` and `Q`, shapes compose
*through* `P` and through `Q`, and hereditary totality passes *from* `P` and
from `Q` to every interpreted type of one shape with them. In the mixed case
the composite of the domains is taken through the domain of `Y`, whose
derivation is a subderivation.

Hereditary totality of a dependent function type includes its
interpretation, which the clause relating two dependent function types does
not provide; transitivity and the transfer of totality therefore assume that
the outer types are interpreted. Types related by the universe relation are.

The weak-head normal forms of interpreted types (`TypeForm`), among them the
forms at which the transport returns its method (`MethodForm`), are named here,
before the facts of an interpretation that mention them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L]

/-! ## Type constants and leaves -/

/-- The type constants at which the transport inspects its source: the codes
and the inductive types. -/
def TypeConst (V : Model Head L) (c : DeclName) : Prop :=
  c = V.prop ∨ ∃ cs, V.roles c = .inductive cs

theorem TypeConst.whnf {V : Model Head L} (laws : V.Laws) {c : DeclName} (hc : TypeConst V c)
    {n : Nat} : Whnf V.rules V.roles (.const c : Tm Head n) := by
  rcases hc with rfl | ⟨cs, role⟩
  · exact laws.values.whnf_prop
  · exact inductive_whnf laws.shape role

/-! ## Forms the transport reads -/

/-- The weak-head normal forms at which the transport returns its method: a
head that is not a universe, an identity type, a decoding, and a rigid spine
other than the codes and the decoder. A type constant is none of them: an
inductive type is no rigid spine. -/
def MethodForm (V : Model Head L) {n : Nat} (w : Tm Head n) : Prop :=
  (∃ h, w = .head h ∧ ¬ V.rules.isUniverse h) ∨ (∃ A a b, w = .id A a b) ∨
    (∃ c, w = .app (.const V.holds) c) ∨
    ∃ T args, w = appSpine (.const T) args ∧ V.roles T = .rigid ∧ T ≠ V.prop ∧ T ≠ V.holds

namespace MethodForm

variable {V : Model Head L} {n : Nat} {w : Tm Head n}

theorem whnf (laws : V.Laws) (form : MethodForm V w) : Whnf V.rules V.roles w := by
  rcases form with ⟨h, rfl, -⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, role, -, -⟩
  · exact head_whnf laws.shape h
  · exact id_whnf laws.shape A a b
  · exact laws.values.whnf_holds c
  · exact laws.values.whnf_rigidSpine role args

theorem ne_univ (form : MethodForm V w) {u : Head} (hu : V.rules.isUniverse u) :
    w ≠ .head u := by
  rcases form with ⟨h, rfl, hh⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, -, -, -⟩
  · intro e
    cases e
    exact hh hu
  · intro e
    cases e
  · intro e
    cases e
  · exact Consistency.appSpine_const_ne_head

theorem ne_typeConst (form : MethodForm V w) {c : DeclName} (hc : TypeConst V c) :
    w ≠ .const c := by
  rcases form with ⟨h, rfl, -⟩ | ⟨A, a, b, rfl⟩ | ⟨c', rfl⟩ | ⟨T, args, rfl, role, notProp, -⟩
  · intro e
    cases e
  · intro e
    cases e
  · intro e
    cases e
  · intro e
    obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const e
    rcases hc with rfl | ⟨cs, role'⟩
    · exact notProp rfl
    · rw [role] at role'
      cases role'

theorem ne_pi (form : MethodForm V w) {A : Tm Head n} {B : Tm Head (n + 1)} :
    w ≠ .pi A B := by
  rcases form with ⟨h, rfl, -⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, -, -, -⟩
  · intro e
    cases e
  · intro e
    cases e
  · intro e
    cases e
  · exact Consistency.appSpine_const_ne_pi

theorem ne_sigma (form : MethodForm V w) {A : Tm Head n} {B : Tm Head (n + 1)} :
    w ≠ .sigma A B := by
  rcases form with ⟨h, rfl, -⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, -, -, -⟩
  · intro e
    cases e
  · intro e
    cases e
  · intro e
    cases e
  · exact Consistency.appSpine_const_ne_sigma

end MethodForm

/-- The weak-head normal forms of interpreted types: universes, type constants,
dependent function and pair types, the forms at which the transport returns its
method, and terms stuck on the daimon. -/
def TypeForm (V : Model Head L) {n : Nat} (w : Tm Head n) : Prop :=
  (∃ u, w = .head u ∧ V.rules.isUniverse u) ∨ (∃ c, TypeConst V c ∧ w = .const c) ∨
    (∃ A B, w = .pi A B) ∨ (∃ A B, w = .sigma A B) ∨ MethodForm V w ∨
    Daimonic V.roles V.star w

/-- A leaf: an interpreted type whose pack relates every pair, and which reduces
to no universe, no type constant and no dependent function type. -/
structure Leaf (V : Model Head L) (I : IPack V) {n : Nat} (ξ : World V.reading n)
    (X : Tm Head n) : Prop where
  interp : ∃ P, I ξ X P ∧ ∀ a b, P.rel a b
  notUniv : ∀ u, WhRed V.rules V.roles X (.head u) → ¬ V.rules.isUniverse u
  notConst : ∀ c, TypeConst V c → ¬ WhRed V.rules V.roles X (.const c)
  notPi : ∀ A B, ¬ WhRed V.rules V.roles X (.pi A B)

/-! ## Shapes -/

/-- Pairs of types of one shape, and hereditarily total types. -/
inductive Grade where
  | pair
  | total

/-- `Shape V I .pair ξ X X'`: types of one shape. `Shape V I .total ξ X X`: `X` is
hereditarily total. -/
inductive Shape (V : Model Head L) (I : IPack V) :
    Grade → {n : Nat} → World V.reading n → Tm Head n → Tm Head n → Prop where
  | total {n : Nat} {ξ : World V.reading n} {X X' : Tm Head n}
      (left : Shape V I .total ξ X X) (right : Shape V I .total ξ X' X') :
      Shape V I .pair ξ X X'
  | univ {n : Nat} {ξ : World V.reading n} {X X' : Tm Head n} {u u' : Head}
      (red : WhRed V.rules V.roles X (.head u)) (red' : WhRed V.rules V.roles X' (.head u'))
      (isUniverse : V.rules.isUniverse u) (isUniverse' : V.rules.isUniverse u')
      (level : V.levels.level u = V.levels.level u') : Shape V I .pair ξ X X'
  | const {n : Nat} {ξ : World V.reading n} {X X' : Tm Head n} {c : DeclName}
      (typeConst : TypeConst V c) (red : WhRed V.rules V.roles X (.const c))
      (red' : WhRed V.rules V.roles X' (.const c)) : Shape V I .pair ξ X X'
  | pi {n : Nat} {ξ : World V.reading n} {X X' A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles X (.pi A B)) (red' : WhRed V.rules V.roles X' (.pi A' B'))
      (domPacks : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∃ P P', I ξ' (Presentation.rename ρ A) P ∧ I ξ' (Presentation.rename ρ A') P' ∧
          P = P')
      (domShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        Shape V I .pair ξ' (Presentation.rename ρ A) (Presentation.rename ρ A'))
      (codPacks : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a b : Tm Head m}, P.rel a b →
          ∃ C C', I ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) C ∧
            I ξ' (inst0 b (Presentation.rename (liftRen ρ) B')) C' ∧ C.rel = C'.rel)
      (codShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a b : Tm Head m}, P.rel a b →
          Shape V I .pair ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
            (inst0 b (Presentation.rename (liftRen ρ) B'))) :
      Shape V I .pair ξ X X'
  | sigma {n : Nat} {ξ : World V.reading n} {X X' A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles X (.sigma A B))
      (red' : WhRed V.rules V.roles X' (.sigma A' B'))
      (domPacks : ∃ P P', I ξ A P ∧ I ξ A' P' ∧ P.rel = P'.rel)
      (domShape : Shape V I .pair ξ A A')
      (codPacks : ∀ {P : Pack V n}, I ξ A P → ∀ {a b : Tm Head n}, P.rel a b →
        ∃ C C', I ξ (inst0 a B) C ∧ I ξ (inst0 b B') C' ∧ C.rel = C'.rel)
      (codShape : ∀ {P : Pack V n}, I ξ A P → ∀ {a b : Tm Head n}, P.rel a b →
        Shape V I .pair ξ (inst0 a B) (inst0 b B')) :
      Shape V I .pair ξ X X'
  | leaf {n : Nat} {ξ : World V.reading n} {X : Tm Head n} (leaf : Leaf V I ξ X)
      (notSigma : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B)) : Shape V I .total ξ X X
  | totalPi {n : Nat} {ξ : World V.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles X (.pi A B)) (interp : ∃ P, I ξ X P)
      (domShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        Shape V I .pair ξ' (Presentation.rename ρ A) (Presentation.rename ρ A))
      (codShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a : Tm Head m}, P.rel a a →
          Shape V I .total ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
            (inst0 a (Presentation.rename (liftRen ρ) B))) :
      Shape V I .total ξ X X
  | totalSigma {n : Nat} {ξ : World V.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
      (red : WhRed V.rules V.roles X (.sigma A B)) (interp : ∃ P, I ξ X P)
      (domShape : Shape V I .total ξ A A)
      (codShape : ∀ {P : Pack V n}, I ξ A P → ∀ {a : Tm Head n}, P.rel a a →
        Shape V I .total ξ (inst0 a B) (inst0 a B)) :
      Shape V I .total ξ X X

/-! ## The universe relation -/

/-- The pack of a universe whose types are interpreted by `below`: types with one
pack and one shape at every world reached by a morphism, realized by `univ`. -/
def universePack (V : Model Head L) (below : IPack V) {n : Nat} (ξ : World V.reading n) :
    Pack V n where
  rel := fun A B => ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∃ P, below ξ' (Presentation.rename ρ A) P ∧ below ξ' (Presentation.rename ρ B) P ∧
      Shape V below .pair ξ' (Presentation.rename ρ A) (Presentation.rename ρ B)
  real := fun _ => V.alg.univ

/-! ## The facts of an interpretation -/

/-- What the laws of shapes, and the transport after them, read from an
interpretation of types: it is deterministic; each pack's relation is a
partial equivalence; interpretations and relations are closed under weak-head
expansion; relations grow along world morphisms; the pack at each normal form
the transport inspects is that form's clause pack, the pack of a daimonic type
the total pack. The transport reads four more facts: terms stuck on the daimon,
`⋆` among them, are related at every type; related values have one realizer;
every interpreted type reduces to a type form, where the rows of the transport
apply; and the relation of a universe grows with its level. -/
structure InterpFacts (V : Model Head L) (I : IPack V) : Prop where
  deterministic : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P P' : Pack V n},
    I ξ A P → I ξ A P' → P = P'
  symm : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {a b : Tm Head n}, P.rel a b → P.rel b a
  trans : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {a b c : Tm Head n}, P.rel a b → P.rel b c → P.rel a c
  expand : ∀ {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n},
    WhRed V.rules V.roles A A' → I ξ A' P → I ξ A P
  expandRel : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {t t' u u' : Tm Head n}, WhRed V.rules V.roles t t' → WhRed V.rules V.roles u u' →
      P.rel t' u' → P.rel t u
  rename : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∃ P', I ξ' (Presentation.rename ρ A) P' ∧
        ∀ {a b : Tm Head n}, P.rel a b →
          P'.rel (Presentation.rename ρ a) (Presentation.rename ρ b)
  piPack : ∀ {n : Nat} {ξ : World V.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
    {P : Pack V n}, I ξ X P → WhRed V.rules V.roles X (.pi A B) →
      ∃ Q : PiPack V ξ, P = Q.piPack ∧ Q.Interprets I A B
  sigmaPack : ∀ {n : Nat} {ξ : World V.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
    {P : Pack V n}, I ξ X P → WhRed V.rules V.roles X (.sigma A B) →
      ∃ Q : PiPack V ξ, P = Q.sigmaPack ∧ Q.Interprets I A B
  univPack : ∀ {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {u : Head} {P : Pack V n},
    I ξ X P → WhRed V.rules V.roles X (.head u) → V.rules.isUniverse u →
      ∃ below : IPack V, P = universePack V below ξ
  propPack : ∀ {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {P : Pack V n},
    I ξ X P → WhRed V.rules V.roles X (.const V.prop) → P = propPack V ξ
  indPack : ∀ {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {T : DeclName}
    {cs : List (DeclName × List (Field Head))} {P : Pack V n},
    I ξ X P → WhRed V.rules V.roles X (.const T) → V.roles T = .inductive cs →
      ∃ field : Tm Head 0 → Pack V n, P = indPack V T cs field ∧
        ∀ {F : Tm Head 0}, F ∈ closedFields cs → I ξ (liftClosed F) (field F)
  daimonic : ∀ {n : Nat} {ξ : World V.reading n} {X u : Tm Head n} {P : Pack V n},
    I ξ X P → WhRed V.rules V.roles X u → Daimonic V.roles V.star u → P = Pack.total V n
  /-- Terms stuck on the daimon, `⋆` among them, are related at every type. -/
  daimonicRel : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {d d' : Tm Head n}, Daimonic V.roles V.star d → Daimonic V.roles V.star d' → P.rel d d'
  /-- Related values have one realizer. -/
  realEq : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∀ {a b : Tm Head n}, P.rel a b → P.real a = P.real b
  /-- An interpreted type reduces to a type form. -/
  typeForm : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}, I ξ A P →
    ∃ w, WhRed V.rules V.roles A w ∧ TypeForm V w
  /-- The relation of a universe grows with its level. -/
  univMono : ∀ {n : Nat} {ξ : World V.reading n} {X Z : Tm Head n} {u u' : Head}
    {P Q : Pack V n}, I ξ X P → I ξ Z Q → WhRed V.rules V.roles X (.head u) →
      WhRed V.rules V.roles Z (.head u') → V.rules.isUniverse u → V.rules.isUniverse u' →
        V.levels.level u ≤ V.levels.level u' → ∀ {A B : Tm Head n}, P.rel A B → Q.rel A B

namespace InterpFacts

variable {V : Model Head L} {I : IPack V} (facts : InterpFacts V I)
include facts

/-- A value related to something is valid on the right. -/
theorem refl_right {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : I ξ A P) {a b : Tm Head n} (h : P.rel a b) : P.rel b b :=
  facts.trans interp (facts.symm interp h) h

/-- A value related to something is valid on the left. -/
theorem refl_left {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : I ξ A P) {a b : Tm Head n} (h : P.rel a b) : P.rel a a :=
  facts.trans interp h (facts.symm interp h)

end InterpFacts

/-! ## The premises of the clauses -/

section Parts

variable (V : Model Head L) (I : IPack V)

/-- The premises of `Shape.pi` for the domains `A`, `A'` and codomains `B`, `B'`. -/
structure PiParts {n : Nat} (ξ : World V.reading n) (A A' : Tm Head n)
    (B B' : Tm Head (n + 1)) : Prop where
  domPacks : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∃ P P', I ξ' (Presentation.rename ρ A) P ∧ I ξ' (Presentation.rename ρ A') P' ∧ P = P'
  domShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    Shape V I .pair ξ' (Presentation.rename ρ A) (Presentation.rename ρ A')
  codPacks : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a b : Tm Head m}, P.rel a b →
      ∃ C C', I ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) C ∧
        I ξ' (inst0 b (Presentation.rename (liftRen ρ) B')) C' ∧ C.rel = C'.rel
  codShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a b : Tm Head m}, P.rel a b →
      Shape V I .pair ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
        (inst0 b (Presentation.rename (liftRen ρ) B'))

/-- The premises of `Shape.sigma` for the domains `A`, `A'` and codomains `B`, `B'`. -/
structure SigmaParts {n : Nat} (ξ : World V.reading n) (A A' : Tm Head n)
    (B B' : Tm Head (n + 1)) : Prop where
  domPacks : ∃ P P', I ξ A P ∧ I ξ A' P' ∧ P.rel = P'.rel
  domShape : Shape V I .pair ξ A A'
  codPacks : ∀ {P : Pack V n}, I ξ A P → ∀ {a b : Tm Head n}, P.rel a b →
    ∃ C C', I ξ (inst0 a B) C ∧ I ξ (inst0 b B') C' ∧ C.rel = C'.rel
  codShape : ∀ {P : Pack V n}, I ξ A P → ∀ {a b : Tm Head n}, P.rel a b →
    Shape V I .pair ξ (inst0 a B) (inst0 b B')

/-- The premises of `Shape.totalPi` for `X` with domain `A` and codomain `B`. -/
structure TotalPiParts {n : Nat} (ξ : World V.reading n) (X A : Tm Head n)
    (B : Tm Head (n + 1)) : Prop where
  interp : ∃ P, I ξ X P
  domShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    Shape V I .pair ξ' (Presentation.rename ρ A) (Presentation.rename ρ A)
  codShape : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a : Tm Head m}, P.rel a a →
      Shape V I .total ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
        (inst0 a (Presentation.rename (liftRen ρ) B))

/-- The premises of `Shape.totalSigma` for `X` with domain `A` and codomain `B`. -/
structure TotalSigmaParts {n : Nat} (ξ : World V.reading n) (X A : Tm Head n)
    (B : Tm Head (n + 1)) : Prop where
  interp : ∃ P, I ξ X P
  domShape : Shape V I .total ξ A A
  codShape : ∀ {P : Pack V n}, I ξ A P → ∀ {a : Tm Head n}, P.rel a a →
    Shape V I .total ξ (inst0 a B) (inst0 a B)

end Parts

/-! ## Inversion -/

namespace Shape

variable {V : Model Head L} {I : IPack V} {n : Nat} {ξ : World V.reading n}

/-- A hereditarily total type is interpreted. -/
theorem total_interp {X X' : Tm Head n} (t : Shape V I .total ξ X X') : ∃ P, I ξ X P := by
  cases t with
  | leaf leaf =>
      obtain ⟨P, hP, -⟩ := leaf.interp
      exact ⟨P, hP⟩
  | totalPi _ interp => exact interp
  | totalSigma _ interp => exact interp

section Laws

variable (laws : V.Laws)
include laws

/-- A hereditarily total type reduces to no universe. -/
theorem total_not_head {X X' : Tm Head n} (t : Shape V I .total ξ X X') {u : Head}
    (red : WhRed V.rules V.roles X (.head u)) (hu : V.rules.isUniverse u) : False := by
  cases t with
  | leaf leaf => exact leaf.notUniv u red hu
  | totalPi red' =>
      cases laws.unique red red' (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
  | totalSigma red' =>
      cases laws.unique red red' (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)

/-- A hereditarily total type reduces to no type constant. -/
theorem total_not_const {X X' : Tm Head n} (t : Shape V I .total ξ X X') {c : DeclName}
    (hc : TypeConst V c) (red : WhRed V.rules V.roles X (.const c)) : False := by
  cases t with
  | leaf leaf => exact leaf.notConst c hc red
  | totalPi red' =>
      cases laws.unique red red' (hc.whnf laws) (pi_whnf laws.shape _ _)
  | totalSigma red' =>
      cases laws.unique red red' (hc.whnf laws) (sigma_whnf laws.shape _ _)

/-- A hereditarily total dependent function type has the premises of
`Shape.totalPi`. -/
theorem total_pi {X : Tm Head n} (t : Shape V I .total ξ X X) {A : Tm Head n}
    {B : Tm Head (n + 1)} (red : WhRed V.rules V.roles X (.pi A B)) :
    TotalPiParts V I ξ X A B := by
  cases t with
  | leaf leaf => exact absurd red (leaf.notPi A B)
  | totalPi red' interp domShape codShape =>
      cases laws.unique red red' (pi_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
      exact ⟨interp, domShape, codShape⟩
  | totalSigma red' =>
      cases laws.unique red red' (pi_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)

/-- A hereditarily total dependent pair type has the premises of
`Shape.totalSigma`. -/
theorem total_sigma {X : Tm Head n} (t : Shape V I .total ξ X X) {A : Tm Head n}
    {B : Tm Head (n + 1)} (red : WhRed V.rules V.roles X (.sigma A B)) :
    TotalSigmaParts V I ξ X A B := by
  cases t with
  | leaf _ notSigma => exact absurd red (notSigma A B)
  | totalPi red' =>
      cases laws.unique red red' (sigma_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
  | totalSigma red' interp domShape codShape =>
      cases laws.unique red red' (sigma_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)
      exact ⟨interp, domShape, codShape⟩

/-- A type of one shape with a universe on its left is a universe of the same
level. -/
theorem pair_head_left {X Y : Tm Head n} (d : Shape V I .pair ξ X Y) {u : Head}
    (red : WhRed V.rules V.roles X (.head u)) (hu : V.rules.isUniverse u) :
    ∃ u', WhRed V.rules V.roles Y (.head u') ∧ V.rules.isUniverse u' ∧
      V.levels.level u = V.levels.level u' := by
  cases d with
  | total left => exact (left.total_not_head laws red hu).elim
  | univ red₁ red₁' _ hu₁' level =>
      cases laws.unique red red₁ (head_whnf laws.shape _) (head_whnf laws.shape _)
      exact ⟨_, red₁', hu₁', level⟩
  | const hc red₁ => cases laws.unique red red₁ (head_whnf laws.shape _) (hc.whnf laws)
  | pi red₁ => cases laws.unique red red₁ (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
  | sigma red₁ =>
      cases laws.unique red red₁ (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a universe on its right is a universe of the same
level. -/
theorem pair_head_right {X Y : Tm Head n} (d : Shape V I .pair ξ X Y) {u' : Head}
    (red : WhRed V.rules V.roles Y (.head u')) (hu' : V.rules.isUniverse u') :
    ∃ u, WhRed V.rules V.roles X (.head u) ∧ V.rules.isUniverse u ∧
      V.levels.level u = V.levels.level u' := by
  cases d with
  | total _ right => exact (right.total_not_head laws red hu').elim
  | univ red₁ red₁' hu₁ _ level =>
      cases laws.unique red red₁' (head_whnf laws.shape _) (head_whnf laws.shape _)
      exact ⟨_, red₁, hu₁, level⟩
  | const hc _ red₁' => cases laws.unique red red₁' (head_whnf laws.shape _) (hc.whnf laws)
  | pi _ red₁' => cases laws.unique red red₁' (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
  | sigma _ red₁' =>
      cases laws.unique red red₁' (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a type constant on its left is that constant. -/
theorem pair_const_left {X Y : Tm Head n} (d : Shape V I .pair ξ X Y) {c : DeclName}
    (hc : TypeConst V c) (red : WhRed V.rules V.roles X (.const c)) :
    WhRed V.rules V.roles Y (.const c) := by
  cases d with
  | total left => exact (left.total_not_const laws hc red).elim
  | univ red₁ => cases laws.unique red red₁ (hc.whnf laws) (head_whnf laws.shape _)
  | const hc₁ red₁ red₁' =>
      cases laws.unique red red₁ (hc.whnf laws) (hc₁.whnf laws)
      exact red₁'
  | pi red₁ => cases laws.unique red red₁ (hc.whnf laws) (pi_whnf laws.shape _ _)
  | sigma red₁ => cases laws.unique red red₁ (hc.whnf laws) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a type constant on its right is that constant. -/
theorem pair_const_right {X Y : Tm Head n} (d : Shape V I .pair ξ X Y) {c : DeclName}
    (hc : TypeConst V c) (red : WhRed V.rules V.roles Y (.const c)) :
    WhRed V.rules V.roles X (.const c) := by
  cases d with
  | total _ right => exact (right.total_not_const laws hc red).elim
  | univ _ red₁' => cases laws.unique red red₁' (hc.whnf laws) (head_whnf laws.shape _)
  | const hc₁ red₁ red₁' =>
      cases laws.unique red red₁' (hc.whnf laws) (hc₁.whnf laws)
      exact red₁
  | pi _ red₁' => cases laws.unique red red₁' (hc.whnf laws) (pi_whnf laws.shape _ _)
  | sigma _ red₁' => cases laws.unique red red₁' (hc.whnf laws) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a dependent function type on its left: both are
hereditarily total, or the other is a dependent function type with the
premises of `Shape.pi`. -/
theorem pair_pi_left {X Y A : Tm Head n} {B : Tm Head (n + 1)} (d : Shape V I .pair ξ X Y)
    (red : WhRed V.rules V.roles X (.pi A B)) :
    (Shape V I .total ξ X X ∧ Shape V I .total ξ Y Y) ∨
      ∃ A' B', WhRed V.rules V.roles Y (.pi A' B') ∧ PiParts V I ξ A A' B B' := by
  cases d with
  | total left right => exact .inl ⟨left, right⟩
  | univ red₁ => cases laws.unique red red₁ (pi_whnf laws.shape _ _) (head_whnf laws.shape _)
  | const hc red₁ => cases laws.unique red red₁ (pi_whnf laws.shape _ _) (hc.whnf laws)
  | pi red₁ red₁' domPacks domShape codPacks codShape =>
      cases laws.unique red red₁ (pi_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
      exact .inr ⟨_, _, red₁', domPacks, domShape, codPacks, codShape⟩
  | sigma red₁ =>
      cases laws.unique red red₁ (pi_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a dependent function type on its right: both are
hereditarily total, or the other is a dependent function type with the
premises of `Shape.pi`. -/
theorem pair_pi_right {X Y A' : Tm Head n} {B' : Tm Head (n + 1)} (d : Shape V I .pair ξ X Y)
    (red : WhRed V.rules V.roles Y (.pi A' B')) :
    (Shape V I .total ξ X X ∧ Shape V I .total ξ Y Y) ∨
      ∃ A B, WhRed V.rules V.roles X (.pi A B) ∧ PiParts V I ξ A A' B B' := by
  cases d with
  | total left right => exact .inl ⟨left, right⟩
  | univ _ red₁' =>
      cases laws.unique red red₁' (pi_whnf laws.shape _ _) (head_whnf laws.shape _)
  | const hc _ red₁' => cases laws.unique red red₁' (pi_whnf laws.shape _ _) (hc.whnf laws)
  | pi red₁ red₁' domPacks domShape codPacks codShape =>
      cases laws.unique red red₁' (pi_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
      exact .inr ⟨_, _, red₁, domPacks, domShape, codPacks, codShape⟩
  | sigma _ red₁' =>
      cases laws.unique red red₁' (pi_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)

/-- A type of one shape with a dependent pair type on its left: both are
hereditarily total, or the other is a dependent pair type with the premises of
`Shape.sigma`. -/
theorem pair_sigma_left {X Y A : Tm Head n} {B : Tm Head (n + 1)} (d : Shape V I .pair ξ X Y)
    (red : WhRed V.rules V.roles X (.sigma A B)) :
    (Shape V I .total ξ X X ∧ Shape V I .total ξ Y Y) ∨
      ∃ A' B', WhRed V.rules V.roles Y (.sigma A' B') ∧ SigmaParts V I ξ A A' B B' := by
  cases d with
  | total left right => exact .inl ⟨left, right⟩
  | univ red₁ =>
      cases laws.unique red red₁ (sigma_whnf laws.shape _ _) (head_whnf laws.shape _)
  | const hc red₁ => cases laws.unique red red₁ (sigma_whnf laws.shape _ _) (hc.whnf laws)
  | pi red₁ =>
      cases laws.unique red red₁ (sigma_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
  | sigma red₁ red₁' domPacks domShape codPacks codShape =>
      cases laws.unique red red₁ (sigma_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)
      exact .inr ⟨_, _, red₁', domPacks, domShape, codPacks, codShape⟩

/-- A type of one shape with a dependent pair type on its right: both are
hereditarily total, or the other is a dependent pair type with the premises of
`Shape.sigma`. -/
theorem pair_sigma_right {X Y A' : Tm Head n} {B' : Tm Head (n + 1)}
    (d : Shape V I .pair ξ X Y) (red : WhRed V.rules V.roles Y (.sigma A' B')) :
    (Shape V I .total ξ X X ∧ Shape V I .total ξ Y Y) ∨
      ∃ A B, WhRed V.rules V.roles X (.sigma A B) ∧ SigmaParts V I ξ A A' B B' := by
  cases d with
  | total left right => exact .inl ⟨left, right⟩
  | univ _ red₁' =>
      cases laws.unique red red₁' (sigma_whnf laws.shape _ _) (head_whnf laws.shape _)
  | const hc _ red₁' =>
      cases laws.unique red red₁' (sigma_whnf laws.shape _ _) (hc.whnf laws)
  | pi _ red₁' =>
      cases laws.unique red red₁' (sigma_whnf laws.shape _ _) (pi_whnf laws.shape _ _)
  | sigma red₁ red₁' domPacks domShape codPacks codShape =>
      cases laws.unique red red₁' (sigma_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)
      exact .inr ⟨_, _, red₁, domPacks, domShape, codPacks, codShape⟩

end Laws

/-- A type of one shape with a leaf on its left is hereditarily total. -/
theorem leaf_pair_left {X Y : Tm Head n} (leaf : Leaf V I ξ X)
    (notSigma : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B)) (d : Shape V I .pair ξ X Y) :
    Shape V I .total ξ Y Y := by
  cases d with
  | total _ right => exact right
  | univ red _ hu => exact (leaf.notUniv _ red hu).elim
  | const hc red => exact (leaf.notConst _ hc red).elim
  | pi red => exact (leaf.notPi _ _ red).elim
  | sigma red => exact (notSigma _ _ red).elim

/-- A type of one shape with a leaf on its right is hereditarily total. -/
theorem leaf_pair_right {X Y : Tm Head n} (leaf : Leaf V I ξ X)
    (notSigma : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B)) (d : Shape V I .pair ξ Y X) :
    Shape V I .total ξ Y Y := by
  cases d with
  | total left => exact left
  | univ _ red _ hu => exact (leaf.notUniv _ red hu).elim
  | const hc _ red => exact (leaf.notConst _ hc red).elim
  | pi _ red => exact (leaf.notPi _ _ red).elim
  | sigma _ red => exact (notSigma _ _ red).elim

/-! ## Symmetry -/

/-- **Symmetry.** -/
theorem symm (facts : InterpFacts V I) {g : Grade} {X Y : Tm Head n}
    (d : Shape V I g ξ X Y) : Shape V I g ξ Y X := by
  induction d with
  | total left right => exact .total right left
  | univ red red' hu hu' level => exact .univ red' red hu' hu level.symm
  | const hc red red' => exact .const hc red' red
  | pi red red' domPacks _ codPacks _ domIH codIH =>
      refine .pi red' red (fun w => ?_) (fun w => domIH w) (fun {_ _ _} w {_} hP' {a b} hab => ?_)
        (fun {_ _ _} w {_} hP' {a b} hab => ?_)
      · obtain ⟨P, P', hP, hP', e⟩ := domPacks w
        exact ⟨P', P, hP', hP, e.symm⟩
      · obtain ⟨P, P', hP, hP'', e⟩ := domPacks w
        obtain rfl := facts.deterministic hP' hP''
        have hba : P.rel b a := by
          rw [e]
          exact facts.symm hP' hab
        obtain ⟨C, C', hC, hC', e'⟩ := codPacks w hP hba
        exact ⟨C', C, hC', hC, e'.symm⟩
      · obtain ⟨P, P', hP, hP'', e⟩ := domPacks w
        obtain rfl := facts.deterministic hP' hP''
        have hba : P.rel b a := by
          rw [e]
          exact facts.symm hP' hab
        exact codIH w hP hba
  | sigma red red' domPacks _ codPacks _ domIH codIH =>
      refine .sigma red' red ?_ domIH (fun {_} hP' {a b} hab => ?_)
        (fun {_} hP' {a b} hab => ?_)
      · obtain ⟨P, P', hP, hP', e⟩ := domPacks
        exact ⟨P', P, hP', hP, e.symm⟩
      · obtain ⟨P, P', hP, hP'', e⟩ := domPacks
        obtain rfl := facts.deterministic hP' hP''
        have hba : P.rel b a := by
          rw [e]
          exact facts.symm hP' hab
        obtain ⟨C, C', hC, hC', e'⟩ := codPacks hP hba
        exact ⟨C', C, hC', hC, e'.symm⟩
      · obtain ⟨P, P', hP, hP'', e⟩ := domPacks
        obtain rfl := facts.deterministic hP' hP''
        have hba : P.rel b a := by
          rw [e]
          exact facts.symm hP' hab
        exact codIH hP hba
  | leaf leaf notSigma => exact .leaf leaf notSigma
  | totalPi red interp domShape codShape => exact .totalPi red interp domShape codShape
  | totalSigma red interp domShape codShape => exact .totalSigma red interp domShape codShape

/-! ## Composition and transfer of totality -/

variable (V I) in
/-- Shapes compose through `M`: types of one shape with `M` on either side, when
interpreted, have one shape. -/
def Through {n : Nat} (ξ : World V.reading n) (M : Tm Head n) : Prop :=
  ∀ {X Z : Tm Head n}, Shape V I .pair ξ X M → Shape V I .pair ξ M Z → (∃ P, I ξ X P) →
    (∃ P, I ξ Z P) → Shape V I .pair ξ X Z

variable (V I) in
/-- Hereditary totality passes from `M`: when `M` is hereditarily total, so is
every interpreted type of one shape with it. -/
def Transfer {n : Nat} (ξ : World V.reading n) (M : Tm Head n) : Prop :=
  Shape V I .total ξ M M → ∀ {X : Tm Head n}, Shape V I .pair ξ M X → (∃ P, I ξ X P) →
    Shape V I .total ξ X X

section Compose

variable (laws : V.Laws) (facts : InterpFacts V I)
include laws facts

omit facts in
/-- Composition and transfer through a universe: universes of one level compose,
and no universe is hereditarily total. -/
theorem through_head {M : Tm Head n} {u : Head} (red : WhRed V.rules V.roles M (.head u))
    (hu : V.rules.isUniverse u) : Through V I ξ M ∧ Transfer V I ξ M := by
  refine ⟨fun d₁ d₂ _ _ => ?_, fun tM => (tM.total_not_head laws red hu).elim⟩
  obtain ⟨v, rv, hv, ev⟩ := d₁.pair_head_right laws red hu
  obtain ⟨w, rw, hw, ew⟩ := d₂.pair_head_left laws red hu
  exact .univ rv rw hv hw (ev.trans ew)

omit facts in
/-- Composition and transfer through a type constant. -/
theorem through_const {M : Tm Head n} {c : DeclName} (hc : TypeConst V c)
    (red : WhRed V.rules V.roles M (.const c)) : Through V I ξ M ∧ Transfer V I ξ M :=
  ⟨fun d₁ d₂ _ _ => .const hc (d₁.pair_const_right laws hc red) (d₂.pair_const_left laws hc red),
    fun tM => (tM.total_not_const laws hc red).elim⟩

/-- Composition and transfer through a dependent function type, given
composition through its domain at every world reached by a morphism, and
composition and transfer through its codomain at every valid point. -/
theorem through_pi {M A : Tm Head n} {B : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles M (.pi A B))
    (dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      Through V I ξ' (Presentation.rename ρ A))
    (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {P : Pack V m}, I ξ' (Presentation.rename ρ A) P → ∀ {a : Tm Head m}, P.rel a a →
        Through V I ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) ∧
          Transfer V I ξ' (inst0 a (Presentation.rename (liftRen ρ) B))) :
    Through V I ξ M ∧ Transfer V I ξ M := by
  have transfer : Transfer V I ξ M := by
    intro tM X d hX
    have parts := tM.total_pi laws red
    rcases d.pair_pi_left laws red with ⟨-, tX⟩ | ⟨A₂, B₂, red₂, parts₂⟩
    · exact tX
    · refine .totalPi red₂ hX (fun w => ?_) (fun {_ _ _} w {_} hP₂ {a} ha => ?_)
      · obtain ⟨-, P₂, -, hP₂, -⟩ := parts₂.domPacks w
        exact dom w ((parts₂.domShape w).symm facts) (parts₂.domShape w) ⟨P₂, hP₂⟩ ⟨P₂, hP₂⟩
      · obtain ⟨P, P₂, hP, hP₂', e⟩ := parts₂.domPacks w
        obtain rfl := facts.deterministic hP₂ hP₂'
        have ha' : P.rel a a := by
          rw [e]
          exact ha
        obtain ⟨-, C₂, -, hC₂, -⟩ := parts₂.codPacks w hP ha'
        exact (cod w hP ha').2 (parts.codShape w hP ha') (parts₂.codShape w hP ha') ⟨C₂, hC₂⟩
  refine ⟨fun {X Z} d₁ d₂ hX hZ => ?_, transfer⟩
  rcases d₁.pair_pi_right laws red with ⟨tX, tM⟩ | ⟨A₀, B₀, red₀, parts₁⟩
  · exact .total tX (transfer tM d₂ hZ)
  rcases d₂.pair_pi_left laws red with ⟨tM, tZ⟩ | ⟨A₂, B₂, red₂, parts₂⟩
  · exact .total (transfer tM (d₁.symm facts) hX) tZ
  refine .pi red₀ red₂ (fun w => ?_) (fun w => ?_) (fun {_ _ _} w {_} hP₀ {a b} hab => ?_)
    (fun {_ _ _} w {_} hP₀ {a b} hab => ?_)
  · obtain ⟨P₀, P, hP₀, hP, e₁⟩ := parts₁.domPacks w
    obtain ⟨P', P₂, hP', hP₂, e₂⟩ := parts₂.domPacks w
    obtain rfl := facts.deterministic hP hP'
    exact ⟨P₀, P₂, hP₀, hP₂, e₁.trans e₂⟩
  · obtain ⟨P₀, -, hP₀, -, -⟩ := parts₁.domPacks w
    obtain ⟨-, P₂, -, hP₂, -⟩ := parts₂.domPacks w
    exact dom w (parts₁.domShape w) (parts₂.domShape w) ⟨P₀, hP₀⟩ ⟨P₂, hP₂⟩
  · obtain ⟨Q₀, Q, hQ₀, hQ, e₁⟩ := parts₁.domPacks w
    obtain rfl := facts.deterministic hP₀ hQ₀
    have hbb : Q.rel b b := by
      rw [← e₁]
      exact facts.refl_right hP₀ hab
    obtain ⟨C₀, C₁, hC₀, hC₁, e₃⟩ := parts₁.codPacks w hP₀ hab
    obtain ⟨C₁', C₂, hC₁', hC₂, e₄⟩ := parts₂.codPacks w hQ hbb
    obtain rfl := facts.deterministic hC₁ hC₁'
    exact ⟨C₀, C₂, hC₀, hC₂, e₃.trans e₄⟩
  · obtain ⟨Q₀, Q, hQ₀, hQ, e₁⟩ := parts₁.domPacks w
    obtain rfl := facts.deterministic hP₀ hQ₀
    have hbb : Q.rel b b := by
      rw [← e₁]
      exact facts.refl_right hP₀ hab
    obtain ⟨C₀, -, hC₀, -, -⟩ := parts₁.codPacks w hP₀ hab
    obtain ⟨-, C₂, -, hC₂, -⟩ := parts₂.codPacks w hQ hbb
    exact (cod w hQ hbb).1 (parts₁.codShape w hP₀ hab) (parts₂.codShape w hQ hbb) ⟨C₀, hC₀⟩
      ⟨C₂, hC₂⟩

/-- Composition and transfer through a dependent pair type, given composition
and transfer through its domain, and through its codomain at every valid
point. -/
theorem through_sigma {M A : Tm Head n} {B : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles M (.sigma A B)) (dom : Through V I ξ A ∧ Transfer V I ξ A)
    (cod : ∀ {P : Pack V n}, I ξ A P → ∀ {a : Tm Head n}, P.rel a a →
      Through V I ξ (inst0 a B) ∧ Transfer V I ξ (inst0 a B)) :
    Through V I ξ M ∧ Transfer V I ξ M := by
  have transfer : Transfer V I ξ M := by
    intro tM X d hX
    have parts := tM.total_sigma laws red
    rcases d.pair_sigma_left laws red with ⟨-, tX⟩ | ⟨A₂, B₂, red₂, parts₂⟩
    · exact tX
    · obtain ⟨P, P₂, hP, hP₂, e⟩ := parts₂.domPacks
      refine .totalSigma red₂ hX (dom.2 parts.domShape parts₂.domShape ⟨P₂, hP₂⟩)
        (fun {_} hP₂' {a} ha => ?_)
      obtain rfl := facts.deterministic hP₂' hP₂
      have ha' : P.rel a a := by
        rw [e]
        exact ha
      obtain ⟨-, C₂, -, hC₂, -⟩ := parts₂.codPacks hP ha'
      exact (cod hP ha').2 (parts.codShape hP ha') (parts₂.codShape hP ha') ⟨C₂, hC₂⟩
  refine ⟨fun {X Z} d₁ d₂ hX hZ => ?_, transfer⟩
  rcases d₁.pair_sigma_right laws red with ⟨tX, tM⟩ | ⟨A₀, B₀, red₀, parts₁⟩
  · exact .total tX (transfer tM d₂ hZ)
  rcases d₂.pair_sigma_left laws red with ⟨tM, tZ⟩ | ⟨A₂, B₂, red₂, parts₂⟩
  · exact .total (transfer tM (d₁.symm facts) hX) tZ
  obtain ⟨P₀, P, hP₀, hP, e₁⟩ := parts₁.domPacks
  obtain ⟨P', P₂, hP', hP₂, e₂⟩ := parts₂.domPacks
  obtain rfl := facts.deterministic hP hP'
  refine .sigma red₀ red₂ ⟨P₀, P₂, hP₀, hP₂, e₁.trans e₂⟩
    (dom.1 parts₁.domShape parts₂.domShape ⟨P₀, hP₀⟩ ⟨P₂, hP₂⟩) (fun {_} hP₀' {a b} hab => ?_)
    (fun {_} hP₀' {a b} hab => ?_)
  · obtain rfl := facts.deterministic hP₀' hP₀
    have hbb : P.rel b b := by
      rw [← e₁]
      exact facts.refl_right hP₀' hab
    obtain ⟨C₀, C₁, hC₀, hC₁, e₃⟩ := parts₁.codPacks hP₀' hab
    obtain ⟨C₁', C₂, hC₁', hC₂, e₄⟩ := parts₂.codPacks hP hbb
    obtain rfl := facts.deterministic hC₁ hC₁'
    exact ⟨C₀, C₂, hC₀, hC₂, e₃.trans e₄⟩
  · obtain rfl := facts.deterministic hP₀' hP₀
    have hbb : P.rel b b := by
      rw [← e₁]
      exact facts.refl_right hP₀' hab
    obtain ⟨C₀, -, hC₀, -, -⟩ := parts₁.codPacks hP₀' hab
    obtain ⟨-, C₂, -, hC₂, -⟩ := parts₂.codPacks hP hbb
    exact (cod hP hbb).1 (parts₁.codShape hP₀' hab) (parts₂.codShape hP hbb) ⟨C₀, hC₀⟩
      ⟨C₂, hC₂⟩

omit laws facts in
/-- Composition and transfer through a leaf: types of one shape with a leaf are
hereditarily total. -/
theorem through_leaf {M : Tm Head n} (leaf : Leaf V I ξ M)
    (notSigma : ∀ A B, ¬ WhRed V.rules V.roles M (.sigma A B)) :
    Through V I ξ M ∧ Transfer V I ξ M :=
  ⟨fun d₁ d₂ _ _ => .total (leaf_pair_right leaf notSigma d₁) (leaf_pair_left leaf notSigma d₂),
    fun _ _ d _ => leaf_pair_left leaf notSigma d⟩

/-- Every derivation of a shape gives composition through, and transfer of
totality from, both of the types it relates. -/
theorem through_transfer {g : Grade} {P Q : Tm Head n} (e : Shape V I g ξ P Q) :
    Through V I ξ P ∧ Through V I ξ Q ∧ Transfer V I ξ P ∧ Transfer V I ξ Q := by
  induction e with
  | total _ _ ihL ihR => exact ⟨ihL.1, ihR.1, ihL.2.2.1, ihR.2.2.1⟩
  | univ red red' hu hu' =>
      exact ⟨(through_head laws red hu).1, (through_head laws red' hu').1,
        (through_head laws red hu).2, (through_head laws red' hu').2⟩
  | const hc red red' =>
      exact ⟨(through_const laws hc red).1, (through_const laws hc red').1,
        (through_const laws hc red).2, (through_const laws hc red').2⟩
  | pi red red' domPacks _ _ _ domIH codIH =>
      have left := through_pi laws facts red (fun w => (domIH w).1)
        (fun {_ _ _} w {_} hP {_} ha => ⟨(codIH w hP ha).1, (codIH w hP ha).2.2.1⟩)
      have right := through_pi laws facts red' (fun w => (domIH w).2.1)
        (fun {_ _ _} w {_} hP' {a} ha => by
        obtain ⟨P, P', hP, hP'', e⟩ := domPacks w
        obtain rfl := facts.deterministic hP' hP''
        have ha' : P.rel a a := by
          rw [e]
          exact ha
        exact ⟨(codIH w hP ha').2.1, (codIH w hP ha').2.2.2⟩)
      exact ⟨left.1, right.1, left.2, right.2⟩
  | sigma red red' domPacks _ _ _ domIH codIH =>
      have left := through_sigma laws facts red ⟨domIH.1, domIH.2.2.1⟩
        (fun {_} hP {_} ha => ⟨(codIH hP ha).1, (codIH hP ha).2.2.1⟩)
      have right := through_sigma laws facts red' ⟨domIH.2.1, domIH.2.2.2⟩
        (fun {_} hP' {a} ha => by
        obtain ⟨P, P', hP, hP'', e⟩ := domPacks
        obtain rfl := facts.deterministic hP' hP''
        have ha' : P.rel a a := by
          rw [e]
          exact ha
        exact ⟨(codIH hP ha').2.1, (codIH hP ha').2.2.2⟩)
      exact ⟨left.1, right.1, left.2, right.2⟩
  | leaf leaf notSigma =>
      have h := through_leaf leaf notSigma
      exact ⟨h.1, h.1, h.2, h.2⟩
  | totalPi red _ _ _ domIH codIH =>
      have h := through_pi laws facts red (fun w => (domIH w).1)
        (fun {_ _ _} w {_} hP {_} ha => ⟨(codIH w hP ha).1, (codIH w hP ha).2.2.1⟩)
      exact ⟨h.1, h.1, h.2, h.2⟩
  | totalSigma red _ _ _ domIH codIH =>
      have h := through_sigma laws facts red ⟨domIH.1, domIH.2.2.1⟩
        (fun {_} hP {_} ha => ⟨(codIH hP ha).1, (codIH hP ha).2.2.1⟩)
      exact ⟨h.1, h.1, h.2, h.2⟩

/-- **Transfer of hereditary totality.** An interpreted type of one shape with a
hereditarily total type is hereditarily total. -/
theorem total_transfer {X Y : Tm Head n} (d : Shape V I .pair ξ X Y)
    (total : Shape V I .total ξ Y Y) (interp : ∃ P, I ξ X P) : Shape V I .total ξ X X :=
  (total.through_transfer laws facts).2.2.1 total (d.symm facts) interp

/-- **Transitivity**, on interpreted outer types. -/
theorem trans {X Y Z : Tm Head n} (first : Shape V I .pair ξ X Y)
    (second : Shape V I .pair ξ Y Z) (interp : ∃ P, I ξ X P) (interp' : ∃ P, I ξ Z P) :
    Shape V I .pair ξ X Z :=
  (first.through_transfer laws facts).2.1 first second interp interp'

end Compose

/-! ## Monotonicity -/

/-- **Monotonicity.** Shapes over an interpretation are shapes over every
deterministic interpretation containing it. -/
theorem mono (facts : InterpFacts V I) {I' : IPack V}
    (incl : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n},
      I ξ A P → I' ξ A P)
    (deterministic : ∀ {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P P' : Pack V n},
      I' ξ A P → I' ξ A P' → P = P')
    {g : Grade} {X Y : Tm Head n} (d : Shape V I g ξ X Y) : Shape V I' g ξ X Y := by
  induction d with
  | total _ _ ihL ihR => exact .total ihL ihR
  | univ red red' hu hu' level => exact .univ red red' hu hu' level
  | const hc red red' => exact .const hc red red'
  | pi red red' domPacks _ codPacks _ domIH codIH =>
      refine .pi red red' (fun w => ?_) domIH (fun {_ _ _} w {_} hP {_ _} hab => ?_)
        (fun {_ _ _} w {_} hP {_ _} hab => ?_)
      · obtain ⟨P, P', hP, hP', e⟩ := domPacks w
        exact ⟨P, P', incl hP, incl hP', e⟩
      · obtain ⟨P₀, -, hP₀, -, -⟩ := domPacks w
        obtain rfl := deterministic hP (incl hP₀)
        obtain ⟨C, C', hC, hC', e⟩ := codPacks w hP₀ hab
        exact ⟨C, C', incl hC, incl hC', e⟩
      · obtain ⟨P₀, -, hP₀, -, -⟩ := domPacks w
        obtain rfl := deterministic hP (incl hP₀)
        exact codIH w hP₀ hab
  | sigma red red' domPacks _ codPacks _ domIH codIH =>
      obtain ⟨P₀, P₀', hP₀, hP₀', e₀⟩ := domPacks
      refine .sigma red red' ⟨P₀, P₀', incl hP₀, incl hP₀', e₀⟩ domIH (fun {_} hP {_ _} hab => ?_)
        (fun {_} hP {_ _} hab => ?_)
      · obtain rfl := deterministic hP (incl hP₀)
        obtain ⟨C, C', hC, hC', e⟩ := codPacks hP₀ hab
        exact ⟨C, C', incl hC, incl hC', e⟩
      · obtain rfl := deterministic hP (incl hP₀)
        exact codIH hP₀ hab
  | leaf leaf notSigma =>
      obtain ⟨P, hP, total⟩ := leaf.interp
      exact .leaf ⟨⟨P, incl hP, total⟩, leaf.notUniv, leaf.notConst, leaf.notPi⟩ notSigma
  | totalPi red interp _ _ domIH codIH =>
      obtain ⟨P₀, hP₀⟩ := interp
      obtain ⟨Q, rfl, iQ⟩ := facts.piPack hP₀ red
      refine .totalPi red ⟨_, incl hP₀⟩ domIH (fun {_ _ _} w {_} hP {_} ha => ?_)
      obtain rfl := deterministic hP (incl (iQ.dom w))
      exact codIH w (iQ.dom w) ha
  | totalSigma red interp domShape _ domIH codIH =>
      obtain ⟨P₀, hP₀⟩ := interp
      obtain ⟨A₀, hA₀⟩ := domShape.total_interp
      refine .totalSigma red ⟨P₀, incl hP₀⟩ domIH (fun {_} hP {_} ha => ?_)
      obtain rfl := deterministic hP (incl hA₀)
      exact codIH hA₀ ha

end Shape

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
