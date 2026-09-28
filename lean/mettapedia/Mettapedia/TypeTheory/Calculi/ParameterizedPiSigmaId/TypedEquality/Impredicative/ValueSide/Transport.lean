import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.DecoderShape

/-!
# The transport between types of one shape

The transport is a term: the spine `coe X Y d` of a constant `coe`
(`coeApp`). Its value-side reductions, the rows of the transport table, are
hypotheses on the reduction of a value model (`CoeRules`), read on the
weak-head normal forms of the two types, the target first:

* into a universe, from a universe of at most its level, the method; from any
  other type form, a term stuck on the daimon;
* into a type constant, the codes or any inductive type, from the same
  constant, the method; from any other type form, another type constant among
  them, a term stuck on the daimon;
* into `Π A' B'` from `Π A B`, a λ-abstraction whose body, at every renaming and
  argument `a`, reduces to `coe (B a₀) (B' a) (f a₀)` with `a₀ := coe A' A a`;
  from any other type form, a term stuck on the daimon;
* into `Σ A' B'` from `Σ A B`, the pair of `a₁ := coe A A' (fst p)` and a term
  reducing to `coe (B (fst p)) (B' a₁) (snd p)`; from any other type form, a
  term stuck on the daimon;
* into a form at which it returns its method (`MethodForm`: a head that is no
  universe, an identity type, a decoding, a rigid spine), the method; into a
  type stuck on the daimon, the method or a term stuck on the daimon.

The rows cover every pair of interpreted types (`CoeRules.reduct`).

An inductive type is a type constant with its own row, not a form at which the
transport returns its method: a transport that returned `zero` from the
numbers into another inductive type would have a result that is no value of
that type (`methodRow_ind_not_val`, and a lawful model in which such a row
fires, `InductiveMethodControl`).

## The laws

The laws hold over every interpretation with the facts of an interpretation
(`InterpFacts`), among them the interpretation at a level and the denotation.
One induction on shape derivations (`Shape.claims`) proves, for a pair of types
of one shape: transports into the pair, and out of it, respect related inputs;
the transport between its two types returns a term related to its method, both
ways; and a transport into the pair from a hereditarily total type is related
to the daimon. For a hereditarily total type it proves that transports out of
it, into either type of any pair, are related to the daimon.

The argument of a transport into a dependent function type goes back along the
domains, into the source's domain; its validity there comes from the claims
about the target's domain, a subderivation. So validity and coherence are
proved together.

Consequences: a transport of a valid value between types of one shape with
themselves is valid (`coe_val`); transports of related values between pairs are
related (`coe_congr`); the transport between types with one pack and one shape
is related to its method (`coe_coherent`) and has its realizers (`coe_real`);
a transport out of a hereditarily total type is related to the daimon
(`coe_total_star`), and two of them are related (`coe_total_congr`).
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

/-! ## The transport as a term -/

/-- The transport of `d` from `X` to `Y`: the spine `coe X Y d` of the
transport's constant. -/
def coeApp (coe : DeclName) {n : Nat} (X Y d : Tm Head n) : Tm Head n :=
  appSpine (.const coe) [X, Y, d]

theorem rename_coeApp (coe : DeclName) {n m : Nat} (ρ : Ren n m) (X Y d : Tm Head n) :
    Presentation.rename ρ (coeApp coe X Y d) =
      coeApp coe (Presentation.rename ρ X) (Presentation.rename ρ Y)
        (Presentation.rename ρ d) :=
  rfl

theorem subst_coeApp (coe : DeclName) {n m : Nat} (σ : Sub Head n m) (X Y d : Tm Head n) :
    Presentation.subst σ (coeApp coe X Y d) =
      coeApp coe (Presentation.subst σ X) (Presentation.subst σ Y)
        (Presentation.subst σ d) :=
  rfl

/-- The argument of a transport into a dependent function type, transported
back along the domains: `coe A' A a`, after a renaming of the two domains. -/
abbrev coeArg (coe : DeclName) {n m : Nat} (ρ : Ren n m) (A A' : Tm Head n) (a : Tm Head m) :
    Tm Head m :=
  coeApp coe (Presentation.rename ρ A') (Presentation.rename ρ A) a

/-- A renamed term that reduces to a λ-abstraction, applied, reduces to the
body at the argument. -/
theorem lam_app_red {R : Rules Head} {roles : Roles Head} {n k : Nat} {t : Tm Head n}
    {body : Tm Head (n + 1)} (red : WhRed R roles t (.lam body)) (ρ : Ren n k) (a : Tm Head k) :
    WhRed R roles (.app (Presentation.rename ρ t) a)
      (inst0 a (Presentation.rename (liftRen ρ) body)) :=
  (WhRed.app (red.rename ρ) a).tail (.beta _ _)

/-! ## The rows of the table -/

/-- The rows of the transport table on the value side, as hypotheses on the
reduction of `coe X Y d`. Each row reads the weak-head normal form of the
target, then that of the source. -/
structure CoeRules (V : Model Head L) (coe : DeclName) : Prop where
  /-- Into a universe, from a universe of at most its level: the method. -/
  univ : ∀ {n : Nat} {X Y d : Tm Head n} {u u' : Head},
    WhRed V.rules V.roles Y (.head u) → V.rules.isUniverse u →
    WhRed V.rules V.roles X (.head u') → V.rules.isUniverse u' →
    V.levels.level u' ≤ V.levels.level u → WhRed V.rules V.roles (coeApp coe X Y d) d
  /-- Into a universe, from any other type form: a term stuck on the daimon. -/
  univOther : ∀ {n : Nat} {X Y d w : Tm Head n} {u : Head},
    WhRed V.rules V.roles Y (.head u) → V.rules.isUniverse u →
    WhRed V.rules V.roles X w → TypeForm V w →
    (∀ u', w = .head u' → V.rules.isUniverse u' → V.levels.level u < V.levels.level u') →
    ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v
  /-- Into a type constant, the codes or an inductive type, from the same
  constant: the method. -/
  const : ∀ {n : Nat} {X Y d : Tm Head n} {c : DeclName}, TypeConst V c →
    WhRed V.rules V.roles Y (.const c) → WhRed V.rules V.roles X (.const c) →
    WhRed V.rules V.roles (coeApp coe X Y d) d
  /-- Into a type constant, from any other type form, another type constant
  among them: a term stuck on the daimon. -/
  constOther : ∀ {n : Nat} {X Y d w : Tm Head n} {c : DeclName}, TypeConst V c →
    WhRed V.rules V.roles Y (.const c) → WhRed V.rules V.roles X w → TypeForm V w →
    w ≠ .const c → ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v
  /-- Into a dependent function type from a dependent function type: a
  λ-abstraction whose body, at every renaming and argument `a`, reduces to the
  transport along the codomains of the method applied to `a` transported back
  along the domains. -/
  pi : ∀ {n : Nat} {X Y d A A' : Tm Head n} {B B' : Tm Head (n + 1)},
    WhRed V.rules V.roles Y (.pi A' B') → WhRed V.rules V.roles X (.pi A B) →
    ∃ body : Tm Head (n + 1), WhRed V.rules V.roles (coeApp coe X Y d) (.lam body) ∧
      ∀ {m : Nat} (ρ : Ren n m) (a : Tm Head m),
        WhRed V.rules V.roles (inst0 a (Presentation.rename (liftRen ρ) body))
          (coeApp coe (inst0 (coeArg coe ρ A A' a) (Presentation.rename (liftRen ρ) B))
            (inst0 a (Presentation.rename (liftRen ρ) B'))
            (.app (Presentation.rename ρ d) (coeArg coe ρ A A' a)))
  /-- Into a dependent function type, from any other type form: a term stuck on
  the daimon. -/
  piOther : ∀ {n : Nat} {X Y d w A' : Tm Head n} {B' : Tm Head (n + 1)},
    WhRed V.rules V.roles Y (.pi A' B') → WhRed V.rules V.roles X w → TypeForm V w →
    (∀ A B, w ≠ .pi A B) →
      ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v
  /-- Into a dependent pair type from a dependent pair type: the pair of the
  first projection transported along the domains and the second projection
  transported along the codomains. -/
  sigma : ∀ {n : Nat} {X Y p A A' : Tm Head n} {B B' : Tm Head (n + 1)},
    WhRed V.rules V.roles Y (.sigma A' B') → WhRed V.rules V.roles X (.sigma A B) →
    ∃ s : Tm Head n,
      WhRed V.rules V.roles (coeApp coe X Y p) (.pair (coeApp coe A A' (.fst p)) s) ∧
      WhRed V.rules V.roles s
        (coeApp coe (inst0 (.fst p) B) (inst0 (coeApp coe A A' (.fst p)) B') (.snd p))
  /-- Into a dependent pair type, from any other type form: a term stuck on the
  daimon. -/
  sigmaOther : ∀ {n : Nat} {X Y d w A' : Tm Head n} {B' : Tm Head (n + 1)},
    WhRed V.rules V.roles Y (.sigma A' B') → WhRed V.rules V.roles X w → TypeForm V w →
    (∀ A B, w ≠ .sigma A B) →
      ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v
  /-- Into a head that is no universe, an identity type, a decoding or a rigid
  spine: the method. -/
  method : ∀ {n : Nat} {X Y d w : Tm Head n}, WhRed V.rules V.roles Y w → MethodForm V w →
    WhRed V.rules V.roles (coeApp coe X Y d) d
  /-- Into a type stuck on the daimon: the method, at a rigid spine of the
  daimon, or a term stuck on the daimon. -/
  stuck : ∀ {n : Nat} {X Y d w : Tm Head n}, WhRed V.rules V.roles Y w →
    Daimonic V.roles V.star w →
    WhRed V.rules V.roles (coeApp coe X Y d) d ∨
      ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v

/-! ## Distinct weak-head normal forms -/

section Distinct

variable {V : Model Head L} (laws : V.Laws) {n : Nat} {X : Tm Head n}
include laws

theorem red_head_not_pi {u : Head} (r : WhRed V.rules V.roles X (.head u)) :
    ∀ A B, ¬ WhRed V.rules V.roles X (.pi A B) :=
  fun _ _ r' => nomatch laws.unique r r' (head_whnf laws.shape _) (pi_whnf laws.shape _ _)

theorem red_head_not_sigma {u : Head} (r : WhRed V.rules V.roles X (.head u)) :
    ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B) :=
  fun _ _ r' => nomatch laws.unique r r' (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)

theorem red_head_not_const {u : Head} (r : WhRed V.rules V.roles X (.head u)) {c : DeclName}
    (hc : TypeConst V c) : ¬ WhRed V.rules V.roles X (.const c) :=
  fun r' => nomatch laws.unique r r' (head_whnf laws.shape _) (hc.whnf laws)

theorem red_const_not_head {c : DeclName} (hc : TypeConst V c)
    (r : WhRed V.rules V.roles X (.const c)) (u : Head) : ¬ WhRed V.rules V.roles X (.head u) :=
  fun r' => nomatch laws.unique r r' (hc.whnf laws) (head_whnf laws.shape _)

theorem red_const_not_pi {c : DeclName} (hc : TypeConst V c)
    (r : WhRed V.rules V.roles X (.const c)) : ∀ A B, ¬ WhRed V.rules V.roles X (.pi A B) :=
  fun _ _ r' => nomatch laws.unique r r' (hc.whnf laws) (pi_whnf laws.shape _ _)

theorem red_const_not_sigma {c : DeclName} (hc : TypeConst V c)
    (r : WhRed V.rules V.roles X (.const c)) : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B) :=
  fun _ _ r' => nomatch laws.unique r r' (hc.whnf laws) (sigma_whnf laws.shape _ _)

theorem red_pi_not_head {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.pi A B)) (u : Head) : ¬ WhRed V.rules V.roles X (.head u) :=
  fun r' => nomatch laws.unique r r' (pi_whnf laws.shape _ _) (head_whnf laws.shape _)

theorem red_pi_not_const {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.pi A B)) {c : DeclName} (hc : TypeConst V c) :
    ¬ WhRed V.rules V.roles X (.const c) :=
  fun r' => nomatch laws.unique r r' (pi_whnf laws.shape _ _) (hc.whnf laws)

theorem red_pi_not_sigma {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.pi A B)) : ∀ A' B', ¬ WhRed V.rules V.roles X (.sigma A' B') :=
  fun _ _ r' => nomatch laws.unique r r' (pi_whnf laws.shape _ _) (sigma_whnf laws.shape _ _)

theorem red_sigma_not_head {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.sigma A B)) (u : Head) : ¬ WhRed V.rules V.roles X (.head u) :=
  fun r' => nomatch laws.unique r r' (sigma_whnf laws.shape _ _) (head_whnf laws.shape _)

theorem red_sigma_not_const {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.sigma A B)) {c : DeclName} (hc : TypeConst V c) :
    ¬ WhRed V.rules V.roles X (.const c) :=
  fun r' => nomatch laws.unique r r' (sigma_whnf laws.shape _ _) (hc.whnf laws)

theorem red_sigma_not_pi {A : Tm Head n} {B : Tm Head (n + 1)}
    (r : WhRed V.rules V.roles X (.sigma A B)) : ∀ A' B', ¬ WhRed V.rules V.roles X (.pi A' B') :=
  fun _ _ r' => nomatch laws.unique r r' (sigma_whnf laws.shape _ _) (pi_whnf laws.shape _ _)

end Distinct

/-! ## Relations read through the facts of an interpretation -/

/-- A relation equal to the relation of a pack relates what that pack
relates. -/
theorem Pack.rel_of_same {V : Model Head L} {n : Nat} {P P' : Pack V n}
    (same : P.rel = P'.rel) {a b : Tm Head n} (h : P.rel a b) : P'.rel a b := by
  rw [← same]
  exact h

namespace InterpFacts

variable {V : Model Head L} {I : IPack V} (facts : InterpFacts V I) {n : Nat}
  {ξ : World V.reading n}
include facts

/-- Terms that reduce to terms stuck on the daimon are related. -/
theorem rel_of_daimonic {A : Tm Head n} {P : Pack V n} (interp : I ξ A P) {t u v v' : Tm Head n}
    (red : WhRed V.rules V.roles t v) (daimonic : Daimonic V.roles V.star v)
    (red' : WhRed V.rules V.roles u v') (daimonic' : Daimonic V.roles V.star v') : P.rel t u :=
  facts.expandRel interp red red' (facts.daimonicRel interp daimonic daimonic')

/-- A term that reduces to a term stuck on the daimon is related to the
daimon. -/
theorem rel_star {A : Tm Head n} {P : Pack V n} (interp : I ξ A P) {t v : Tm Head n}
    (red : WhRed V.rules V.roles t v) (daimonic : Daimonic V.roles V.star v) :
    P.rel t (.const V.star) :=
  facts.rel_of_daimonic interp red daimonic .refl .star

/-- Two terms related to the daimon are related. -/
theorem rel_of_star {A : Tm Head n} {P : Pack V n} (interp : I ξ A P) {t u : Tm Head n}
    (ht : P.rel t (.const V.star)) (hu : P.rel u (.const V.star)) : P.rel t u :=
  facts.trans interp ht (facts.symm interp hu)

/-- A relation is closed under weak-head expansion on the left. -/
theorem expandLeft {A : Tm Head n} {P : Pack V n} (interp : I ξ A P) {t t' u : Tm Head n}
    (red : WhRed V.rules V.roles t t') (h : P.rel t' u) : P.rel t u :=
  facts.expandRel interp red .refl h

/-- Packs of two types given by interpretations share the relations stated for
some interpretations of them. -/
theorem same_of_packs {X X' : Tm Head n} {P₀ P₀' : Pack V n}
    (h : ∃ P P', I ξ X P ∧ I ξ X' P' ∧ P.rel = P'.rel) (interp : I ξ X P₀)
    (interp' : I ξ X' P₀') : P₀.rel = P₀'.rel := by
  obtain ⟨P, P', hP, hP', e⟩ := h
  rw [facts.deterministic interp hP, facts.deterministic interp' hP']
  exact e

/-- **Types that reduce to one type constant have one pack**: the codes, or the
inductive pack over the packs of the closed field types, which interpretation
determines. -/
theorem pack_eq_of_typeConst {c : DeclName} (hc : TypeConst V c) {X Z : Tm Head n}
    {PX PZ : Pack V n} (hX : I ξ X PX) (hZ : I ξ Z PZ) (rX : WhRed V.rules V.roles X (.const c))
    (rZ : WhRed V.rules V.roles Z (.const c)) : PX = PZ := by
  rcases hc with rfl | ⟨cs, role⟩
  · rw [facts.propPack hX rX, facts.propPack hZ rZ]
  · obtain ⟨field, rfl, fieldI⟩ := facts.indPack hX rX role
    obtain ⟨field', rfl, fieldI'⟩ := facts.indPack hZ rZ role
    exact indPack_congr _ fun hF => facts.deterministic (fieldI hF) (fieldI' hF)

end InterpFacts

namespace PiPack

variable {V : Model Head L} {I : IPack V} {n : Nat} {ξ : World V.reading n}

theorem Interprets.dom_id {Q : PiPack V ξ} {A : Tm Head n} {B : Tm Head (n + 1)}
    (i : Q.Interprets I A B) : I ξ A (Q.dom (Morph.id ξ)) := by
  have h := i.dom (Morph.id ξ)
  rwa [rename_id] at h

theorem Interprets.cod_id {Q : PiPack V ξ} {A : Tm Head n} {B : Tm Head (n + 1)}
    (i : Q.Interprets I A B) {a : Tm Head n} (ha : (Q.dom (Morph.id ξ)).Val a) :
    I ξ (inst0 a B) (Q.cod (Morph.id ξ) ha) := by
  have h := i.cod (Morph.id ξ) ha
  rwa [liftRen_id, rename_id] at h

/-- A pair is related to a term whose first projection is related to the pair's
first component, when the pair's second component is related to the term's
second projection at the codomain of the first component. -/
theorem sigmaRel_pair (facts : InterpFacts V I) {Q : PiPack V ξ} {A : Tm Head n}
    {B : Tm Head (n + 1)} (i : Q.Interprets I A B) {a s q : Tm Head n}
    (ha : (Q.dom (Morph.id ξ)).Val a) (hfst : (Q.dom (Morph.id ξ)).rel a (.fst q))
    (hsnd : (Q.cod (Morph.id ξ) ha).rel s (.snd q)) : Q.sigmaPack.rel (.pair a s) q := by
  have iA := i.dom_id
  have red : WhRed V.rules V.roles (.fst (.pair a s)) a := .single (.fstPair _ _)
  have hp : (Q.dom (Morph.id ξ)).Val (.fst (.pair a s)) := facts.expandRel iA red red ha
  have codEq : Q.cod (Morph.id ξ) hp = Q.cod (Morph.id ξ) ha :=
    i.codRespect (Morph.id ξ) hp ha (facts.expandLeft iA red ha)
  refine ⟨hp, facts.expandLeft iA red hfst, ?_⟩
  rw [codEq]
  exact facts.expandLeft (i.cod_id ha) (.single (.sndPair _ _)) hsnd

end PiPack

/-! ## Pairs of one shape -/

/-- Two types of one shape whose packs have one relation. -/
structure ShapePair (V : Model Head L) (I : IPack V) {n : Nat} (ξ : World V.reading n)
    (X X' : Tm Head n) (P P' : Pack V n) : Prop where
  left : I ξ X P
  right : I ξ X' P'
  same : P.rel = P'.rel
  shape : Shape V I .pair ξ X X'

/-- Types related by a universe relation form a pair of one shape, with one
pack, in the world itself. -/
theorem ShapePair.of_universe {V : Model Head L} {I : IPack V} {n : Nat}
    {ξ : World V.reading n} {A B : Tm Head n} (related : (universePack V I ξ).rel A B) :
    ∃ P, ShapePair V I ξ A B P P := by
  obtain ⟨P, hA, hB, s⟩ := universePack_rel_self related
  exact ⟨P, hA, hB, rfl, s⟩

section ShapePairs

variable {V : Model Head L} {I : IPack V} (facts : InterpFacts V I) {n : Nat}
  {ξ : World V.reading n}
include facts

/-- The domains of two dependent function types of one shape form a pair at
every world reached by a morphism. -/
theorem shapePair_dom {Q Q' : PiPack V ξ} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (parts : PiParts V I ξ A A' B B') (i : Q.Interprets I A B) (i' : Q'.Interprets I A' B')
    {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ShapePair V I ξ' (Presentation.rename ρ A) (Presentation.rename ρ A') (Q.dom w) (Q'.dom w) := by
  obtain ⟨P, P', hP, hP', e⟩ := parts.domPacks w
  refine ⟨i.dom w, i'.dom w, ?_, parts.domShape w⟩
  rw [facts.deterministic (i.dom w) hP, facts.deterministic (i'.dom w) hP', e]

/-- The codomains of two dependent function types of one shape, at related
points, form a pair. -/
theorem shapePair_cod {Q Q' : PiPack V ξ} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (parts : PiParts V I ξ A A' B B') (i : Q.Interprets I A B) (i' : Q'.Interprets I A' B')
    {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a b : Tm Head m}
    (ha : (Q.dom w).Val a) (hab : (Q.dom w).rel a b) (hb : (Q'.dom w).Val b) :
    ShapePair V I ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
      (inst0 b (Presentation.rename (liftRen ρ) B')) (Q.cod w ha) (Q'.cod w hb) :=
  ⟨i.cod w ha, i'.cod w hb,
    facts.same_of_packs (parts.codPacks w (i.dom w) hab) (i.cod w ha) (i'.cod w hb),
    parts.codShape w (i.dom w) hab⟩

/-- The domains of two dependent pair types of one shape form a pair. -/
theorem shapePair_sigmaDom {Q Q' : PiPack V ξ} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (parts : SigmaParts V I ξ A A' B B') (i : Q.Interprets I A B)
    (i' : Q'.Interprets I A' B') :
    ShapePair V I ξ A A' (Q.dom (Morph.id ξ)) (Q'.dom (Morph.id ξ)) :=
  ⟨i.dom_id, i'.dom_id, facts.same_of_packs parts.domPacks i.dom_id i'.dom_id, parts.domShape⟩

/-- The codomains of two dependent pair types of one shape, at related points,
form a pair. -/
theorem shapePair_sigmaCod {Q Q' : PiPack V ξ} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (parts : SigmaParts V I ξ A A' B B') (i : Q.Interprets I A B)
    (i' : Q'.Interprets I A' B') {a b : Tm Head n} (ha : (Q.dom (Morph.id ξ)).Val a)
    (hab : (Q.dom (Morph.id ξ)).rel a b) (hb : (Q'.dom (Morph.id ξ)).Val b) :
    ShapePair V I ξ (inst0 a B) (inst0 b B') (Q.cod (Morph.id ξ) ha)
      (Q'.cod (Morph.id ξ) hb) :=
  ⟨i.cod_id ha, i'.cod_id hb,
    facts.same_of_packs (parts.codPacks i.dom_id hab) (i.cod_id ha) (i'.cod_id hb),
    parts.codShape i.dom_id hab⟩

/-- A hereditarily total type relates every pair. -/
theorem Shape.total_rel_aux {g : Grade} {X X' : Tm Head n} (h : Shape V I g ξ X X') :
    g = .total → ∀ {P : Pack V n}, I ξ X P → ∀ a b, P.rel a b := by
  induction h with
  | total => intro e; cases e
  | univ => intro e; cases e
  | const => intro e; cases e
  | pi => intro e; cases e
  | sigma => intro e; cases e
  | leaf lx =>
      intro _ P interp
      obtain ⟨P', hP', total⟩ := lx.interp
      rw [facts.deterministic interp hP']
      exact total
  | totalPi red _ _ _ _ codIH =>
      intro _ P interp
      obtain ⟨Q, rfl, iQ⟩ := facts.piPack interp red
      exact fun _ _ {_ _ _} w {_ _} ha _ => codIH w (iQ.dom w) ha rfl (iQ.cod w ha) _ _
  | totalSigma red _ _ _ domIH codIH =>
      intro _ P interp
      obtain ⟨Q, rfl, iQ⟩ := facts.sigmaPack interp red
      have dom := domIH rfl iQ.dom_id
      exact fun _ _ => ⟨dom _ _, dom _ _, codIH iQ.dom_id (dom _ _) rfl (iQ.cod_id (dom _ _)) _ _⟩

/-- **A hereditarily total type relates every pair.** -/
theorem Shape.total_rel {X X' : Tm Head n} (h : Shape V I .total ξ X X') {P : Pack V n}
    (interp : I ξ X P) : ∀ a b, P.rel a b :=
  Shape.total_rel_aux facts h rfl interp

end ShapePairs

/-! ## Transports of one source into several types -/

namespace CoeRules

variable {V : Model Head L} {coe : DeclName} (rules : CoeRules V coe) {I : IPack V}
  (facts : InterpFacts V I) {n : Nat} {ξ : World V.reading n}
include rules facts

/-- Into a universe, from an interpreted type that reduces to no universe of at
most its level: a term stuck on the daimon. -/
theorem univ_other {X Y d : Tm Head n} {P : Pack V n} {u : Head} (hX : I ξ X P)
    (target : WhRed V.rules V.roles Y (.head u)) (hu : V.rules.isUniverse u)
    (other : ∀ u', WhRed V.rules V.roles X (.head u') → V.rules.isUniverse u' →
      V.levels.level u < V.levels.level u') :
    ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v := by
  obtain ⟨w, rX, form⟩ := facts.typeForm hX
  exact rules.univOther target hu rX form fun u' e hu' => other u' (by rw [← e]; exact rX) hu'

/-- Into a type constant, from an interpreted type that reduces to another
type form: a term stuck on the daimon. -/
theorem const_other {X Y d : Tm Head n} {P : Pack V n} {c : DeclName} (hX : I ξ X P)
    (hc : TypeConst V c) (target : WhRed V.rules V.roles Y (.const c))
    (other : ¬ WhRed V.rules V.roles X (.const c)) :
    ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v := by
  obtain ⟨w, rX, form⟩ := facts.typeForm hX
  exact rules.constOther hc target rX form fun e => other (by rw [← e]; exact rX)

/-- Into a dependent function type, from an interpreted type that reduces to no
dependent function type: a term stuck on the daimon. -/
theorem pi_other {X Y d A' : Tm Head n} {B' : Tm Head (n + 1)} {P : Pack V n} (hX : I ξ X P)
    (target : WhRed V.rules V.roles Y (.pi A' B'))
    (other : ∀ A B, ¬ WhRed V.rules V.roles X (.pi A B)) :
    ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v := by
  obtain ⟨w, rX, form⟩ := facts.typeForm hX
  exact rules.piOther target rX form fun A B e => other A B (by rw [← e]; exact rX)

/-- Into a dependent pair type, from an interpreted type that reduces to no
dependent pair type: a term stuck on the daimon. -/
theorem sigma_other {X Y d A' : Tm Head n} {B' : Tm Head (n + 1)} {P : Pack V n}
    (hX : I ξ X P) (target : WhRed V.rules V.roles Y (.sigma A' B'))
    (other : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B)) :
    ∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v := by
  obtain ⟨w, rX, form⟩ := facts.typeForm hX
  exact rules.sigmaOther target rX form fun A B e => other A B (by rw [← e]; exact rX)

end CoeRules

/-! ## The rows cover every pair of interpreted types -/

/-- The reducts the rows of the table give to `coe X Y d`: the method; a term
stuck on the daimon; at two dependent function types, a λ-abstraction whose
body is a transport along the codomains; at two dependent pair types, a pair
of transports. -/
inductive CoeReduct (V : Model Head L) (coe : DeclName) {n : Nat} (X Y d : Tm Head n) :
    Tm Head n → Prop where
  | method : CoeReduct V coe X Y d d
  | daimon {v : Tm Head n} : Daimonic V.roles V.star v → CoeReduct V coe X Y d v
  | pi {A A' : Tm Head n} {B B' body : Tm Head (n + 1)} :
      WhRed V.rules V.roles X (.pi A B) → WhRed V.rules V.roles Y (.pi A' B') →
      (∀ {m : Nat} (ρ : Ren n m) (a : Tm Head m),
        WhRed V.rules V.roles (inst0 a (Presentation.rename (liftRen ρ) body))
          (coeApp coe (inst0 (coeArg coe ρ A A' a) (Presentation.rename (liftRen ρ) B))
            (inst0 a (Presentation.rename (liftRen ρ) B'))
            (.app (Presentation.rename ρ d) (coeArg coe ρ A A' a)))) →
      CoeReduct V coe X Y d (.lam body)
  | sigma {A A' : Tm Head n} {B B' : Tm Head (n + 1)} {s : Tm Head n} :
      WhRed V.rules V.roles X (.sigma A B) → WhRed V.rules V.roles Y (.sigma A' B') →
      WhRed V.rules V.roles s
        (coeApp coe (inst0 (.fst d) B) (inst0 (coeApp coe A A' (.fst d)) B') (.snd d)) →
      CoeReduct V coe X Y d (.pair (coeApp coe A A' (.fst d)) s)

/-- The transport between types that reduce to type forms reduces to a reduct
the rows give. -/
theorem CoeRules.reduct_of_typeForm {V : Model Head L} (laws : V.Laws) {coe : DeclName}
    (rules : CoeRules V coe) {n : Nat} {X Y : Tm Head n}
    (formX : ∃ w, WhRed V.rules V.roles X w ∧ TypeForm V w)
    (formY : ∃ w, WhRed V.rules V.roles Y w ∧ TypeForm V w) (d : Tm Head n) :
    ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r := by
  obtain ⟨w, rY, form⟩ := formY
  obtain ⟨wX, rX, formX⟩ := formX
  have daimon : (∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v) →
      ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
    fun ⟨v, rv, dv⟩ => ⟨v, rv, .daimon dv⟩
  rcases form with ⟨u, rfl, hu⟩ | ⟨c, hc, rfl⟩ | ⟨A', B', rfl⟩ | ⟨A', B', rfl⟩ | method |
    stuck
  · -- into a universe
    have notUniv : (∀ u', wX = .head u' → ¬ V.rules.isUniverse u') →
        ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
      fun h => daimon (rules.univOther rY hu rX formX fun u' e hu' => absurd hu' (h u' e))
    rcases formX with ⟨u', rfl, hu'⟩ | ⟨c, hc, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | methodX |
      stuckX
    · rcases lt_or_ge (V.levels.level u) (V.levels.level u') with lt | le
      · exact daimon (rules.univOther rY hu rX (.inl ⟨u', rfl, hu'⟩) fun u'' e _ => by
          cases e
          exact lt)
      · exact ⟨d, rules.univ rY hu rX hu' le, .method⟩
    · exact notUniv fun _ e => by cases e
    · exact notUniv fun _ e => by cases e
    · exact notUniv fun _ e => by cases e
    · exact notUniv fun u' e => by
        rcases methodX with ⟨h, rfl, hh⟩ | ⟨A, a, b, rfl⟩ | ⟨c, rfl⟩ | ⟨T, args, rfl, -, -, -⟩
        · cases e
          exact hh
        · cases e
        · cases e
        · exact absurd e Consistency.appSpine_const_ne_head
    · exact notUniv fun u' e => absurd e ((laws.daimonic_not_former stuckX).1 u')
  · -- into a type constant
    have other : wX ≠ .const c →
        ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
      fun ne => daimon (rules.constOther hc rY rX formX ne)
    rcases formX with ⟨u', rfl, -⟩ | ⟨c', hc', rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | methodX |
      stuckX
    · exact other (by intro e; cases e)
    · by_cases e : c' = c
      · subst e
        exact ⟨d, rules.const hc rY rX, .method⟩
      · exact other fun e' => e (Tm.const.inj e')
    · exact other (by intro e; cases e)
    · exact other (by intro e; cases e)
    · exact other (methodX.ne_typeConst hc)
    · exact other (laws.daimonic_ne_typeConst stuckX hc)
  · -- into a dependent function type
    have other : (∀ A B, wX ≠ .pi A B) →
        ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
      fun ne => daimon (rules.piOther rY rX formX ne)
    rcases formX with ⟨u', rfl, -⟩ | ⟨c', hc', rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | methodX |
      stuckX
    · exact other fun _ _ e => by cases e
    · exact other fun _ _ e => by cases e
    · obtain ⟨body, rb, inst⟩ := rules.pi (d := d) rY rX
      exact ⟨_, rb, .pi rX rY inst⟩
    · exact other fun _ _ e => by cases e
    · exact other fun _ _ => methodX.ne_pi
    · exact other fun A B => (laws.daimonic_not_former stuckX).2.1 A B
  · -- into a dependent pair type
    have other : (∀ A B, wX ≠ .sigma A B) →
        ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
      fun ne => daimon (rules.sigmaOther rY rX formX ne)
    rcases formX with ⟨u', rfl, -⟩ | ⟨c', hc', rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | methodX |
      stuckX
    · exact other fun _ _ e => by cases e
    · exact other fun _ _ e => by cases e
    · exact other fun _ _ e => by cases e
    · obtain ⟨s, rp, rs⟩ := rules.sigma (p := d) rY rX
      exact ⟨_, rp, .sigma rX rY rs⟩
    · exact other fun _ _ => methodX.ne_sigma
    · exact other fun A B => (laws.daimonic_not_former stuckX).2.2.1 A B
  · exact ⟨d, rules.method rY method, .method⟩
  · rcases rules.stuck (X := X) (d := d) rY stuck with rd | h
    · exact ⟨d, rd, .method⟩
    · exact daimon h

/-- **The transport exists.** Between interpreted types, at every method, the
transport reduces to a reduct the rows give: interpreted types reduce to type
forms, and the rows cover every pair of type forms. -/
theorem CoeRules.reduct {V : Model Head L} (laws : V.Laws) {I : IPack V}
    (facts : InterpFacts V I) {coe : DeclName} (rules : CoeRules V coe) {n : Nat}
    {ξ : World V.reading n} {X Y : Tm Head n} {PX PY : Pack V n} (hX : I ξ X PX)
    (hY : I ξ Y PY) (d : Tm Head n) :
    ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
  rules.reduct_of_typeForm laws (facts.typeForm hX) (facts.typeForm hY) d

/-! ## The claims -/

section Claims

variable (V : Model Head L) (I : IPack V) (coe : DeclName)

/-- Transports into the two types of a pair, from the two types of any pair of
sources, are related at related methods. -/
def TgtRel {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  ∀ {PT PT' : Pack V n}, I ξ T PT → I ξ T' PT' → PT.rel = PT'.rel →
    ∀ {X X' : Tm Head n} {PX PX' : Pack V n}, ShapePair V I ξ X X' PX PX' →
      ∀ {d d' : Tm Head n}, PX.rel d d' → PT.rel (coeApp coe X T d) (coeApp coe X' T' d')

/-- Transports out of the two types of a pair, into the two types of any pair of
targets, are related at related methods. -/
def SrcRel {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  ∀ {PT PT' : Pack V n}, I ξ T PT → I ξ T' PT' → PT.rel = PT'.rel →
    ∀ {Z Z' : Tm Head n} {PZ PZ' : Pack V n}, ShapePair V I ξ Z Z' PZ PZ' →
      ∀ {d d' : Tm Head n}, PT.rel d d' → PZ.rel (coeApp coe T Z d) (coeApp coe T' Z' d')

/-- The transport from the first type of a pair to the second returns a term
related to its method. -/
def CohFwd {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  ∀ {PT PT' : Pack V n}, I ξ T PT → I ξ T' PT' → PT.rel = PT'.rel →
    ∀ {d : Tm Head n}, PT.Val d → PT'.rel (coeApp coe T T' d) d

/-- The transport from the second type of a pair to the first returns a term
related to its method. -/
def CohBwd {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  ∀ {PT PT' : Pack V n}, I ξ T PT → I ξ T' PT' → PT.rel = PT'.rel →
    ∀ {d : Tm Head n}, PT'.Val d → PT.rel (coeApp coe T' T d) d

/-- Transports into the two types of a pair, from any hereditarily total type,
are related to the daimon. -/
def TgtStar {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  ∀ {PT PT' : Pack V n}, I ξ T PT → I ξ T' PT' → PT.rel = PT'.rel →
    ∀ {S : Tm Head n}, Shape V I .total ξ S S → ∀ e : Tm Head n,
      PT.rel (coeApp coe S T e) (.const V.star) ∧ PT.rel (coeApp coe S T' e) (.const V.star)

/-- Transports out of a type, into the two types of any pair, are related to
the daimon. -/
def SrcStar {n : Nat} (ξ : World V.reading n) (S : Tm Head n) : Prop :=
  ∀ {Z Z' : Tm Head n} {PZ PZ' : Pack V n}, ShapePair V I ξ Z Z' PZ PZ' →
    ∀ e : Tm Head n,
      PZ.rel (coeApp coe S Z e) (.const V.star) ∧ PZ.rel (coeApp coe S Z' e) (.const V.star)

/-- The claims about a pair of types of one shape. -/
structure PairClaims {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop where
  tgt : TgtRel V I coe ξ T T'
  src : SrcRel V I coe ξ T T'
  cohFwd : CohFwd V I coe ξ T T'
  cohBwd : CohBwd V I coe ξ T T'
  tgtStar : TgtStar V I coe ξ T T'

/-- The claims about a shape derivation: those of a pair, or, for a
hereditarily total type, that transports out of it are related to the daimon. -/
def ShapeClaims (g : Grade) {n : Nat} (ξ : World V.reading n) (T T' : Tm Head n) : Prop :=
  match g with
  | .pair => PairClaims V I coe ξ T T'
  | .total => SrcStar V I coe ξ T

end Claims

/-! ## Transports that do not recurse -/

section NonRecursive

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- Transports into two universes of one level, from the two types of a pair,
are related: between universes, by the method, the relation of a universe
growing with its level; from any other type form, through the daimon. -/
theorem coe_rel_into_univ {X X' Z Z' : Tm Head n} {PX PX' PZ : Pack V n} {uz uz' : Head}
    (sp : ShapePair V I ξ X X' PX PX') (zl : I ξ Z PZ)
    (rz : WhRed V.rules V.roles Z (.head uz)) (rz' : WhRed V.rules V.roles Z' (.head uz'))
    (hz : V.rules.isUniverse uz) (hz' : V.rules.isUniverse uz')
    (lz : V.levels.level uz = V.levels.level uz') {d d' : Tm Head n} (hdd' : PX.rel d d') :
    PZ.rel (coeApp coe X Z d) (coeApp coe X' Z' d') := by
  obtain ⟨xl, xr, -, xshape⟩ := sp
  have both : (∀ u, WhRed V.rules V.roles X (.head u) → ¬ V.rules.isUniverse u) →
      (∀ u, WhRed V.rules V.roles X' (.head u) → ¬ V.rules.isUniverse u) →
      PZ.rel (coeApp coe X Z d) (coeApp coe X' Z' d') := fun h h' => by
    obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := d) xl rz hz fun u r hu => absurd hu (h u r)
    obtain ⟨v', rv', dv'⟩ :=
      rules.univ_other facts (d := d') xr rz' hz' fun u r hu => absurd hu (h' u r)
    exact facts.rel_of_daimonic zl rv dv rv' dv'
  cases xshape with
  | @univ _ _ _ _ ux ux' rx rx' hx hx' lx =>
      rcases lt_or_ge (V.levels.level uz) (V.levels.level ux) with lt | le
      · obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := d) xl rz hz fun u' r _ => by
          cases laws.unique rx r (head_whnf laws.shape _) (head_whnf laws.shape _)
          exact lt
        obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := d') xr rz' hz' fun u' r _ => by
          cases laws.unique rx' r (head_whnf laws.shape _) (head_whnf laws.shape _)
          rw [← lx, ← lz]
          exact lt
        exact facts.rel_of_daimonic zl rv dv rv' dv'
      · have le' : V.levels.level ux' ≤ V.levels.level uz' := by
          rw [← lx, ← lz]
          exact le
        exact facts.expandRel zl (rules.univ rz hz rx hx le) (rules.univ rz' hz' rx' hx' le')
          (facts.univMono xl zl rx rz hx hz le hdd')
  | const hc rx rx' =>
      exact both (fun u r _ => red_const_not_head laws hc rx u r)
        (fun u r _ => red_const_not_head laws hc rx' u r)
  | pi rx rx' =>
      exact both (fun u r _ => red_pi_not_head laws rx u r)
        (fun u r _ => red_pi_not_head laws rx' u r)
  | sigma rx rx' =>
      exact both (fun u r _ => red_sigma_not_head laws rx u r)
        (fun u r _ => red_sigma_not_head laws rx' u r)
  | total lx lx' =>
      exact both (fun _ r hu => lx.total_not_head laws r hu)
        (fun _ r hu => lx'.total_not_head laws r hu)

/-- Transports into one type constant on both sides, the codes or an inductive
type, from the two types of a pair, are related: from the same constant by the
method, the two types having one pack; from any other type form, another type
constant among them, through the daimon. -/
theorem coe_rel_into_const {X X' Z Z' : Tm Head n} {PX PX' PZ : Pack V n} {c : DeclName}
    (sp : ShapePair V I ξ X X' PX PX') (zl : I ξ Z PZ) (hc : TypeConst V c)
    (rz : WhRed V.rules V.roles Z (.const c)) (rz' : WhRed V.rules V.roles Z' (.const c))
    {d d' : Tm Head n} (hdd' : PX.rel d d') :
    PZ.rel (coeApp coe X Z d) (coeApp coe X' Z' d') := by
  obtain ⟨xl, xr, -, xshape⟩ := sp
  have both : ¬ WhRed V.rules V.roles X (.const c) → ¬ WhRed V.rules V.roles X' (.const c) →
      PZ.rel (coeApp coe X Z d) (coeApp coe X' Z' d') := fun h h' => by
    obtain ⟨v, rv, dv⟩ := rules.const_other facts (d := d) xl hc rz h
    obtain ⟨v', rv', dv'⟩ := rules.const_other facts (d := d') xr hc rz' h'
    exact facts.rel_of_daimonic zl rv dv rv' dv'
  cases xshape with
  | @const _ _ _ _ c' hc' rx rx' =>
      by_cases e : c' = c
      · subst e
        rw [← facts.pack_eq_of_typeConst hc xl zl rx rz]
        exact facts.expandRel xl (rules.const hc rz rx) (rules.const hc rz' rx') hdd'
      · have ne : ∀ {Y : Tm Head n}, WhRed V.rules V.roles Y (.const c') →
            ¬ WhRed V.rules V.roles Y (.const c) := fun r r' =>
          e (Tm.const.inj (laws.unique r r' (hc'.whnf laws) (hc.whnf laws)))
        exact both (ne rx) (ne rx')
  | univ rx rx' => exact both (red_head_not_const laws rx hc) (red_head_not_const laws rx' hc)
  | pi rx rx' => exact both (red_pi_not_const laws rx hc) (red_pi_not_const laws rx' hc)
  | sigma rx rx' => exact both (red_sigma_not_const laws rx hc) (red_sigma_not_const laws rx' hc)
  | total lx lx' =>
      exact both (fun r => lx.total_not_const laws hc r) (fun r => lx'.total_not_const laws hc r)

/-- Transports from two types that are no dependent function or pair types are
related, whatever the pair of targets. -/
theorem coe_rel_flatSource {X X' Z Z' : Tm Head n} {PX PX' PZ PZ' : Pack V n}
    (sp : ShapePair V I ξ X X' PX PX') (tp : ShapePair V I ξ Z Z' PZ PZ')
    (notPi : ∀ A B, ¬ WhRed V.rules V.roles X (.pi A B))
    (notPi' : ∀ A B, ¬ WhRed V.rules V.roles X' (.pi A B))
    (notSigma : ∀ A B, ¬ WhRed V.rules V.roles X (.sigma A B))
    (notSigma' : ∀ A B, ¬ WhRed V.rules V.roles X' (.sigma A B)) {d d' : Tm Head n}
    (hdd' : PX.rel d d') : PZ.rel (coeApp coe X Z d) (coeApp coe X' Z' d') := by
  obtain ⟨zl, -, -, zshape⟩ := tp
  cases zshape with
  | total lz _ => exact lz.total_rel facts zl _ _
  | univ rz rz' hz hz' lz => exact coe_rel_into_univ laws facts rules sp zl rz rz' hz hz' lz hdd'
  | const hc rz rz' => exact coe_rel_into_const laws facts rules sp zl hc rz rz' hdd'
  | pi rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := d) sp.left rz notPi
      obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := d') sp.right rz' notPi'
      exact facts.rel_of_daimonic zl rv dv rv' dv'
  | sigma rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := d) sp.left rz notSigma
      obtain ⟨v', rv', dv'⟩ := rules.sigma_other facts (d := d') sp.right rz' notSigma'
      exact facts.rel_of_daimonic zl rv dv rv' dv'

/-- The claims about two universes of one level. -/
theorem pairClaims_univ {T T' : Tm Head n} {u u' : Head} (red : WhRed V.rules V.roles T (.head u))
    (red' : WhRed V.rules V.roles T' (.head u')) (hu : V.rules.isUniverse u)
    (hu' : V.rules.isUniverse u') (level : V.levels.level u = V.levels.level u') :
    PairClaims V I coe ξ T T' where
  tgt := fun hT _ _ _ _ _ _ sp _ _ hdd' =>
    coe_rel_into_univ laws facts rules sp hT red red' hu hu' level hdd'
  src := fun hT hT' same _ _ _ _ tp _ _ hdd' =>
    coe_rel_flatSource laws facts rules ⟨hT, hT', same, .univ red red' hu hu' level⟩ tp
      (red_head_not_pi laws red) (red_head_not_pi laws red') (red_head_not_sigma laws red)
      (red_head_not_sigma laws red') hdd'
  cohFwd := fun _ hT' same _ hd =>
    facts.expandLeft hT' (rules.univ red' hu' red hu level.le) (Pack.rel_of_same same hd)
  cohBwd := fun hT _ same _ hd =>
    facts.expandLeft hT (rules.univ red hu red' hu' level.ge) (Pack.rel_of_same same.symm hd)
  tgtStar := fun hT _ _ _ hS e => by
    obtain ⟨PS, iS⟩ := hS.total_interp
    obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := e) iS red hu fun _ r hu₀ =>
      (hS.total_not_head laws r hu₀).elim
    obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := e) iS red' hu' fun _ r hu₀ =>
      (hS.total_not_head laws r hu₀).elim
    exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩

/-- The claims about one type constant on both sides: the codes, or an
inductive type. -/
theorem pairClaims_const {T T' : Tm Head n} {c : DeclName} (hc : TypeConst V c)
    (red : WhRed V.rules V.roles T (.const c)) (red' : WhRed V.rules V.roles T' (.const c)) :
    PairClaims V I coe ξ T T' where
  tgt := fun hT _ _ _ _ _ _ sp _ _ hdd' =>
    coe_rel_into_const laws facts rules sp hT hc red red' hdd'
  src := fun hT hT' same _ _ _ _ tp _ _ hdd' =>
    coe_rel_flatSource laws facts rules ⟨hT, hT', same, .const hc red red'⟩ tp
      (red_const_not_pi laws hc red) (red_const_not_pi laws hc red')
      (red_const_not_sigma laws hc red) (red_const_not_sigma laws hc red') hdd'
  cohFwd := fun _ hT' same _ hd =>
    facts.expandLeft hT' (rules.const hc red' red) (Pack.rel_of_same same hd)
  cohBwd := fun hT _ same _ hd =>
    facts.expandLeft hT (rules.const hc red red') (Pack.rel_of_same same.symm hd)
  tgtStar := fun hT _ _ _ hS e => by
    obtain ⟨PS, iS⟩ := hS.total_interp
    obtain ⟨v, rv, dv⟩ := rules.const_other facts (d := e) iS hc red fun r =>
      hS.total_not_const laws hc r
    obtain ⟨v', rv', dv'⟩ := rules.const_other facts (d := e) iS hc red' fun r =>
      hS.total_not_const laws hc r
    exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩

omit laws rules in
/-- The claims about two hereditarily total types: transports out of them are
related through the daimon. -/
theorem pairClaims_total {T T' : Tm Head n} (left : Shape V I .total ξ T T)
    (right : Shape V I .total ξ T' T') (leftIH : SrcStar V I coe ξ T)
    (rightIH : SrcStar V I coe ξ T') : PairClaims V I coe ξ T T' where
  tgt := fun hT _ _ _ _ _ _ _ _ _ _ => left.total_rel facts hT _ _
  src := fun _ _ _ _ _ _ _ tp _ _ _ =>
    facts.rel_of_star tp.left (leftIH tp _).1 (rightIH tp _).2
  cohFwd := fun _ hT' _ _ _ => right.total_rel facts hT' _ _
  cohBwd := fun hT _ _ _ _ => left.total_rel facts hT _ _
  tgtStar := fun hT _ _ _ _ _ => ⟨left.total_rel facts hT _ _, left.total_rel facts hT _ _⟩

omit laws in
/-- Transports out of a leaf are related to the daimon: into a type that is not
hereditarily total, a leaf is of another form. -/
theorem srcStar_leaf {S : Tm Head n} (leaf : Leaf V I ξ S)
    (notSigma : ∀ A B, ¬ WhRed V.rules V.roles S (.sigma A B)) : SrcStar V I coe ξ S := by
  intro Z Z' PZ PZ' tp e
  obtain ⟨zl, -, -, zshape⟩ := tp
  obtain ⟨PS, iS, -⟩ := leaf.interp
  cases zshape with
  | total lz _ => exact ⟨lz.total_rel facts zl _ _, lz.total_rel facts zl _ _⟩
  | univ rz rz' hz hz' =>
      obtain ⟨v, rv, dv⟩ :=
        rules.univ_other facts (d := e) iS rz hz fun u r hu => absurd hu (leaf.notUniv u r)
      obtain ⟨v', rv', dv'⟩ :=
        rules.univ_other facts (d := e) iS rz' hz' fun u r hu => absurd hu (leaf.notUniv u r)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | const hc rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.const_other facts (d := e) iS hc rz (leaf.notConst _ hc)
      obtain ⟨v', rv', dv'⟩ := rules.const_other facts (d := e) iS hc rz' (leaf.notConst _ hc)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | pi rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := e) iS rz leaf.notPi
      obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := e) iS rz' leaf.notPi
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | sigma rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := e) iS rz notSigma
      obtain ⟨v', rv', dv'⟩ := rules.sigma_other facts (d := e) iS rz' notSigma
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩

end NonRecursive

/-! ## Dependent function types -/

section Functions

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- The claims about two dependent function types of one shape, from the
claims about their domains at every world reached by a morphism and about their
codomains at related points. -/
theorem pairClaims_pi {T T' A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles T (.pi A B)) (red' : WhRed V.rules V.roles T' (.pi A' B'))
    (parts : PiParts V I ξ A A' B B')
    (domIH : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (_ : Morph ξ ξ' ρ),
      PairClaims V I coe ξ' (Presentation.rename ρ A) (Presentation.rename ρ A'))
    (codIH : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (_ : Morph ξ ξ' ρ)
      {P : Pack V m} (_ : I ξ' (Presentation.rename ρ A) P) {a b : Tm Head m} (_ : P.rel a b),
      PairClaims V I coe ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
        (inst0 b (Presentation.rename (liftRen ρ) B'))) :
    PairClaims V I coe ξ T T' := by
  -- Transports from a hereditarily total type are related to the daimon.
  have tgtStar : TgtStar V I coe ξ T T' := by
    intro PT PT' hT hT' same S hS e
    obtain ⟨QT, rfl, iT⟩ := facts.piPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.piPack hT' red'
    cases hS with
    | leaf lf _ =>
        obtain ⟨PS, iS, -⟩ := lf.interp
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := e) iS red lf.notPi
        obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := e) iS red' lf.notPi
        exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩
    | totalSigma rS interpS =>
        obtain ⟨PS, iS⟩ := interpS
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := e) iS red (red_sigma_not_pi laws rS)
        obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := e) iS red' (red_sigma_not_pi laws rS)
        exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩
    | @totalPi _ _ _ D E rS interpS domShapeS codShapeS =>
        obtain ⟨PS, iS⟩ := interpS
        obtain ⟨QS, rfl, iQS⟩ := facts.piPack iS rS
        obtain ⟨body, rb, inst⟩ := rules.pi (d := e) red rS
        obtain ⟨body', rb', inst'⟩ := rules.pi (d := e) red' rS
        -- The argument, transported back into the source's domain, is valid.
        have argVal : ∀ {k : Nat} {ξ' : World V.reading k} {ρ : Ren n k} (w : Morph ξ ξ' ρ)
            {z : Tm Head k}, (QT.dom w).Val z →
            (QS.dom w).Val (coeArg coe ρ D A z) ∧ (QS.dom w).Val (coeArg coe ρ D A' z) := by
          intro k ξ' ρ w z hz
          have pT := shapePair_dom facts parts iT iT' w
          have pS : ShapePair V I ξ' (Presentation.rename ρ D) (Presentation.rename ρ D)
              (QS.dom w) (QS.dom w) := ⟨iQS.dom w, iQS.dom w, rfl, domShapeS w⟩
          have h := (domIH w).src pT.left pT.right pT.same pS hz
          exact ⟨facts.refl_left (iQS.dom w) h, facts.refl_right (iQS.dom w) h⟩
        constructor
        · intro k ξ' ρ w z z' hz _
          have pT := shapePair_dom facts parts iT iT' w
          have pB := shapePair_cod facts parts iT iT' w hz hz (Pack.rel_of_same pT.same hz)
          have c := ((codIH w (iT.dom w) hz).tgtStar pB.left pB.right pB.same
            (codShapeS w (iQS.dom w) (argVal w hz).1)
            (.app (Presentation.rename ρ e) (coeArg coe ρ D A z))).1
          exact facts.expandRel (iT.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z)) .refl
            (facts.trans (iT.cod w hz) c (facts.daimonicRel (iT.cod w hz) .star (.app .star)))
        · intro k ξ' ρ w z z' hz _
          have pT := shapePair_dom facts parts iT iT' w
          have pB := shapePair_cod facts parts iT iT' w hz hz (Pack.rel_of_same pT.same hz)
          have c := ((codIH w (iT.dom w) hz).tgtStar pB.left pB.right pB.same
            (codShapeS w (iQS.dom w) (argVal w hz).2)
            (.app (Presentation.rename ρ e) (coeArg coe ρ D A' z))).2
          exact facts.expandRel (iT.cod w hz) ((lam_app_red rb' ρ z).trans (inst' ρ z)) .refl
            (facts.trans (iT.cod w hz) c (facts.daimonicRel (iT.cod w hz) .star (.app .star)))
  refine ⟨?_, ?_, ?_, ?_, tgtStar⟩
  · -- transports into the pair
    intro PT PT' hT hT' same X X' PX PX' sp d d' hdd'
    obtain ⟨xl, xr, -, xshape⟩ := sp
    cases xshape with
    | total lx lx' =>
        exact facts.rel_of_star hT (tgtStar hT hT' same lx d).1 (tgtStar hT hT' same lx' d').2
    | univ rx rx' =>
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := d) xl red (red_head_not_pi laws rx)
        obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := d') xr red' (red_head_not_pi laws rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | const hc rx rx' =>
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := d) xl red (red_const_not_pi laws hc rx)
        obtain ⟨v', rv', dv'⟩ :=
          rules.pi_other facts (d := d') xr red' (red_const_not_pi laws hc rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | sigma rx rx' =>
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := d) xl red (red_sigma_not_pi laws rx)
        obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := d') xr red' (red_sigma_not_pi laws rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | @pi _ _ _ _ C C' D D' rx rx' xdP xdS xcP xcS =>
        obtain ⟨QT, rfl, iT⟩ := facts.piPack hT red
        obtain ⟨QT', rfl, iT'⟩ := facts.piPack hT' red'
        obtain ⟨QX, rfl, iX⟩ := facts.piPack xl rx
        obtain ⟨QX', rfl, iX'⟩ := facts.piPack xr rx'
        have xparts : PiParts V I ξ C C' D D' := ⟨xdP, xdS, xcP, xcS⟩
        obtain ⟨body, rb, inst⟩ := rules.pi (d := d) red rx
        obtain ⟨body', rb', inst'⟩ := rules.pi (d := d') red' rx'
        intro k ξ' ρ w z z' hz hzz'
        have pT := shapePair_dom facts parts iT iT' w
        have pX := shapePair_dom facts xparts iX iX' w
        have hab₀ : (QX.dom w).rel (coeArg coe ρ C A z) (coeArg coe ρ C' A' z') :=
          (domIH w).src pT.left pT.right pT.same pX hzz'
        have ha₀ := facts.refl_left (iX.dom w) hab₀
        have hb₀ := facts.refl_right (iX.dom w) hab₀
        have pD := shapePair_cod facts xparts iX iX' w ha₀ hab₀ (Pack.rel_of_same pX.same hb₀)
        have pB := shapePair_cod facts parts iT iT' w hz hzz'
          (Pack.rel_of_same pT.same (facts.refl_right (iT.dom w) hzz'))
        exact facts.expandRel (iT.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z))
          ((lam_app_red rb' ρ z').trans (inst' ρ z'))
          ((codIH w (iT.dom w) hzz').tgt pB.left pB.right pB.same pD (hdd' w ha₀ hab₀))
  · -- transports out of the pair
    intro PT PT' hT hT' same Z Z' PZ PZ' tp d d' hdd'
    obtain ⟨zl, zr, -, zshape⟩ := tp
    cases zshape with
    | total lz _ => exact lz.total_rel facts zl _ _
    | univ rz rz' hz hz' =>
        obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := d) hT rz hz fun u r _ =>
          (red_pi_not_head laws red u r).elim
        obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := d') hT' rz' hz' fun u r _ =>
          (red_pi_not_head laws red' u r).elim
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | const hc rz rz' =>
        obtain ⟨v, rv, dv⟩ :=
          rules.const_other facts (d := d) hT hc rz (red_pi_not_const laws red hc)
        obtain ⟨v', rv', dv'⟩ :=
          rules.const_other facts (d := d') hT' hc rz' (red_pi_not_const laws red' hc)
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | sigma rz rz' =>
        obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := d) hT rz (red_pi_not_sigma laws red)
        obtain ⟨v', rv', dv'⟩ :=
          rules.sigma_other facts (d := d') hT' rz' (red_pi_not_sigma laws red')
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | @pi _ _ _ _ E E' F F' rz rz' zdP zdS zcP zcS =>
        obtain ⟨QT, rfl, iT⟩ := facts.piPack hT red
        obtain ⟨QT', rfl, iT'⟩ := facts.piPack hT' red'
        obtain ⟨QZ, rfl, iZ⟩ := facts.piPack zl rz
        obtain ⟨QZ', rfl, iZ'⟩ := facts.piPack zr rz'
        have zparts : PiParts V I ξ E E' F F' := ⟨zdP, zdS, zcP, zcS⟩
        obtain ⟨body, rb, inst⟩ := rules.pi (d := d) rz red
        obtain ⟨body', rb', inst'⟩ := rules.pi (d := d') rz' red'
        intro k ξ' ρ w z z' hz hzz'
        have pZ := shapePair_dom facts zparts iZ iZ' w
        have pT := shapePair_dom facts parts iT iT' w
        have hab₀ : (QT.dom w).rel (coeArg coe ρ A E z) (coeArg coe ρ A' E' z') :=
          (domIH w).tgt pT.left pT.right pT.same pZ hzz'
        have ha₀ := facts.refl_left (iT.dom w) hab₀
        have hb₀ := facts.refl_right (iT.dom w) hab₀
        have pB := shapePair_cod facts parts iT iT' w ha₀ hab₀ (Pack.rel_of_same pT.same hb₀)
        have pF := shapePair_cod facts zparts iZ iZ' w hz hzz'
          (Pack.rel_of_same pZ.same (facts.refl_right (iZ.dom w) hzz'))
        exact facts.expandRel (iZ.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z))
          ((lam_app_red rb' ρ z').trans (inst' ρ z'))
          ((codIH w (iT.dom w) hab₀).src pB.left pB.right pB.same pF (hdd' w ha₀ hab₀))
  · -- coherence from the first type to the second
    intro PT PT' hT hT' same d hd
    obtain ⟨QT, rfl, iT⟩ := facts.piPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.piPack hT' red'
    obtain ⟨body, rb, inst⟩ := rules.pi (d := d) red' red
    intro k ξ' ρ w z z' hz hzz'
    have pT := shapePair_dom facts parts iT iT' w
    have coh₀ : (QT.dom w).rel (coeArg coe ρ A A' z) z :=
      (domIH w).cohBwd pT.left pT.right pT.same hz
    have ha₀ := facts.refl_left (iT.dom w) coh₀
    have pB := shapePair_cod facts parts iT iT' w ha₀ coh₀ hz
    have c₁ := (codIH w (iT.dom w) coh₀).cohFwd pB.left pB.right pB.same (hd w ha₀ ha₀)
    have c₂ : (QT.cod w ha₀).rel (.app (Presentation.rename ρ d) (coeArg coe ρ A A' z))
        (.app (Presentation.rename ρ d) z') :=
      hd w ha₀ (facts.trans (iT.dom w) coh₀ (Pack.rel_of_same pT.same.symm hzz'))
    exact facts.expandLeft (iT'.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z))
      (facts.trans (iT'.cod w hz) c₁ (Pack.rel_of_same pB.same c₂))
  · -- coherence from the second type to the first
    intro PT PT' hT hT' same d hd
    obtain ⟨QT, rfl, iT⟩ := facts.piPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.piPack hT' red'
    obtain ⟨body, rb, inst⟩ := rules.pi (d := d) red red'
    intro k ξ' ρ w z z' hz hzz'
    have pT := shapePair_dom facts parts iT iT' w
    have coh₀ : (QT'.dom w).rel (coeArg coe ρ A' A z) z :=
      (domIH w).cohFwd pT.left pT.right pT.same hz
    have ha₀' := facts.refl_left (iT'.dom w) coh₀
    have back : (QT.dom w).rel z (coeArg coe ρ A' A z) :=
      Pack.rel_of_same pT.same.symm (facts.symm (iT'.dom w) coh₀)
    have pB := shapePair_cod facts parts iT iT' w hz back ha₀'
    have c₁ := (codIH w (iT.dom w) back).cohBwd pB.left pB.right pB.same (hd w ha₀' ha₀')
    have c₂ : (QT'.cod w ha₀').rel (.app (Presentation.rename ρ d) (coeArg coe ρ A' A z))
        (.app (Presentation.rename ρ d) z') :=
      hd w ha₀' (facts.trans (iT'.dom w) coh₀ (Pack.rel_of_same pT.same hzz'))
    exact facts.expandLeft (iT.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z))
      (facts.trans (iT.cod w hz) c₁ (Pack.rel_of_same pB.same.symm c₂))

/-- Transports out of a hereditarily total dependent function type are related
to the daimon: at a dependent function type, the body is a transport out of a
hereditarily total codomain, at an argument transported back into the source's
domain, which is valid by the claims about that domain. -/
theorem srcStar_totalPi {S A : Tm Head n} {B : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles S (.pi A B)) (interp : ∃ P, I ξ S P)
    (domIH : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (_ : Morph ξ ξ' ρ),
      PairClaims V I coe ξ' (Presentation.rename ρ A) (Presentation.rename ρ A))
    (codIH : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (_ : Morph ξ ξ' ρ)
      {P : Pack V m} (_ : I ξ' (Presentation.rename ρ A) P) {a : Tm Head m} (_ : P.rel a a),
      SrcStar V I coe ξ' (inst0 a (Presentation.rename (liftRen ρ) B))) :
    SrcStar V I coe ξ S := by
  intro Z Z' PZ PZ' tp e
  obtain ⟨PS, iS⟩ := interp
  obtain ⟨QS, rfl, iQS⟩ := facts.piPack iS red
  obtain ⟨zl, zr, -, zshape⟩ := tp
  cases zshape with
  | total lz _ => exact ⟨lz.total_rel facts zl _ _, lz.total_rel facts zl _ _⟩
  | univ rz rz' hz hz' =>
      obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := e) iS rz hz fun u r _ =>
        (red_pi_not_head laws red u r).elim
      obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := e) iS rz' hz' fun u r _ =>
        (red_pi_not_head laws red u r).elim
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | const hc rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.const_other facts (d := e) iS hc rz (red_pi_not_const laws red hc)
      obtain ⟨v', rv', dv'⟩ :=
        rules.const_other facts (d := e) iS hc rz' (red_pi_not_const laws red hc)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | sigma rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := e) iS rz (red_pi_not_sigma laws red)
      obtain ⟨v', rv', dv'⟩ := rules.sigma_other facts (d := e) iS rz' (red_pi_not_sigma laws red)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | @pi _ _ _ _ E E' F F' rz rz' zdP zdS zcP zcS =>
      obtain ⟨QZ, rfl, iZ⟩ := facts.piPack zl rz
      obtain ⟨QZ', rfl, iZ'⟩ := facts.piPack zr rz'
      have zparts : PiParts V I ξ E E' F F' := ⟨zdP, zdS, zcP, zcS⟩
      obtain ⟨body, rb, inst⟩ := rules.pi (d := e) rz red
      obtain ⟨body', rb', inst'⟩ := rules.pi (d := e) rz' red
      -- The argument, transported back into the source's domain, is valid.
      have argVal : ∀ {k : Nat} {ξ' : World V.reading k} {ρ : Ren n k} (w : Morph ξ ξ' ρ)
          {z : Tm Head k}, (QZ.dom w).Val z →
          (QS.dom w).Val (coeArg coe ρ A E z) ∧ (QS.dom w).Val (coeArg coe ρ A E' z) := by
        intro k ξ' ρ w z hz
        have pE := shapePair_dom facts zparts iZ iZ' w
        have h := (domIH w).tgt (iQS.dom w) (iQS.dom w) rfl pE hz
        exact ⟨facts.refl_left (iQS.dom w) h, facts.refl_right (iQS.dom w) h⟩
      constructor
      · intro k ξ' ρ w z z' hz _
        have pE := shapePair_dom facts zparts iZ iZ' w
        have pF := shapePair_cod facts zparts iZ iZ' w hz hz (Pack.rel_of_same pE.same hz)
        have c := (codIH w (iQS.dom w) (argVal w hz).1 pF
          (.app (Presentation.rename ρ e) (coeArg coe ρ A E z))).1
        exact facts.expandRel (iZ.cod w hz) ((lam_app_red rb ρ z).trans (inst ρ z)) .refl
          (facts.trans (iZ.cod w hz) c (facts.daimonicRel (iZ.cod w hz) .star (.app .star)))
      · intro k ξ' ρ w z z' hz _
        have pE := shapePair_dom facts zparts iZ iZ' w
        have pF := shapePair_cod facts zparts iZ iZ' w hz hz (Pack.rel_of_same pE.same hz)
        have c := (codIH w (iQS.dom w) (argVal w hz).2 pF
          (.app (Presentation.rename ρ e) (coeArg coe ρ A E' z))).2
        exact facts.expandRel (iZ.cod w hz) ((lam_app_red rb' ρ z).trans (inst' ρ z)) .refl
          (facts.trans (iZ.cod w hz) c (facts.daimonicRel (iZ.cod w hz) .star (.app .star)))

end Functions

/-! ## Dependent pair types -/

section Pairs

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- The claims about two dependent pair types of one shape, from the claims
about their domains and about their codomains at related points. -/
theorem pairClaims_sigma {T T' A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles T (.sigma A B)) (red' : WhRed V.rules V.roles T' (.sigma A' B'))
    (parts : SigmaParts V I ξ A A' B B') (domIH : PairClaims V I coe ξ A A')
    (codIH : ∀ {P : Pack V n} (_ : I ξ A P) {a b : Tm Head n} (_ : P.rel a b),
      PairClaims V I coe ξ (inst0 a B) (inst0 b B')) :
    PairClaims V I coe ξ T T' := by
  -- Transports from a hereditarily total type are related to the daimon.
  have tgtStar : TgtStar V I coe ξ T T' := by
    intro PT PT' hT hT' same S hS e
    obtain ⟨QT, rfl, iT⟩ := facts.sigmaPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.sigmaPack hT' red'
    have pA := shapePair_sigmaDom facts parts iT iT'
    cases hS with
    | leaf lf notSigma =>
        obtain ⟨PS, iS, -⟩ := lf.interp
        obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := e) iS red notSigma
        obtain ⟨v', rv', dv'⟩ := rules.sigma_other facts (d := e) iS red' notSigma
        exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩
    | totalPi rS interpS =>
        obtain ⟨PS, iS⟩ := interpS
        obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := e) iS red (red_pi_not_sigma laws rS)
        obtain ⟨v', rv', dv'⟩ :=
          rules.sigma_other facts (d := e) iS red' (red_pi_not_sigma laws rS)
        exact ⟨facts.rel_star hT rv dv, facts.rel_star hT rv' dv'⟩
    | @totalSigma _ _ _ D E rS interpS domShapeS codShapeS =>
        obtain ⟨PS, iS⟩ := interpS
        obtain ⟨QS, rfl, iQS⟩ := facts.sigmaPack iS rS
        have hfe : (QS.dom (Morph.id ξ)).Val (.fst e) := domShapeS.total_rel facts iQS.dom_id _ _
        have hE := codShapeS iQS.dom_id hfe
        have dstar := domIH.tgtStar pA.left pA.right pA.same domShapeS (.fst e)
        obtain ⟨s, rp, rs⟩ := rules.sigma (p := e) red rS
        obtain ⟨s', rp', rs'⟩ := rules.sigma (p := e) red' rS
        have ha₁ := facts.refl_left iT.dom_id dstar.1
        have ha₂ := facts.refl_left iT.dom_id dstar.2
        constructor
        · have pB := shapePair_sigmaCod facts parts iT iT' ha₁ ha₁ (Pack.rel_of_same pA.same ha₁)
          have c := ((codIH iT.dom_id ha₁).tgtStar pB.left pB.right pB.same hE (.snd e)).1
          exact facts.expandLeft hT rp (PiPack.sigmaRel_pair facts iT ha₁
            (facts.trans iT.dom_id dstar.1 (facts.daimonicRel iT.dom_id .star (.fst .star)))
            (facts.expandLeft (iT.cod_id ha₁) rs (facts.trans (iT.cod_id ha₁) c
              (facts.daimonicRel (iT.cod_id ha₁) .star (.snd .star)))))
        · have pB := shapePair_sigmaCod facts parts iT iT' ha₂ ha₂ (Pack.rel_of_same pA.same ha₂)
          have c := ((codIH iT.dom_id ha₂).tgtStar pB.left pB.right pB.same hE (.snd e)).2
          exact facts.expandLeft hT rp' (PiPack.sigmaRel_pair facts iT ha₂
            (facts.trans iT.dom_id dstar.2 (facts.daimonicRel iT.dom_id .star (.fst .star)))
            (facts.expandLeft (iT.cod_id ha₂) rs' (facts.trans (iT.cod_id ha₂) c
              (facts.daimonicRel (iT.cod_id ha₂) .star (.snd .star)))))
  refine ⟨?_, ?_, ?_, ?_, tgtStar⟩
  · -- transports into the pair
    intro PT PT' hT hT' same X X' PX PX' sp d d' hdd'
    obtain ⟨xl, xr, -, xshape⟩ := sp
    cases xshape with
    | total lx lx' =>
        exact facts.rel_of_star hT (tgtStar hT hT' same lx d).1 (tgtStar hT hT' same lx' d').2
    | univ rx rx' =>
        obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := d) xl red (red_head_not_sigma laws rx)
        obtain ⟨v', rv', dv'⟩ :=
          rules.sigma_other facts (d := d') xr red' (red_head_not_sigma laws rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | const hc rx rx' =>
        obtain ⟨v, rv, dv⟩ :=
          rules.sigma_other facts (d := d) xl red (red_const_not_sigma laws hc rx)
        obtain ⟨v', rv', dv'⟩ :=
          rules.sigma_other facts (d := d') xr red' (red_const_not_sigma laws hc rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | pi rx rx' =>
        obtain ⟨v, rv, dv⟩ := rules.sigma_other facts (d := d) xl red (red_pi_not_sigma laws rx)
        obtain ⟨v', rv', dv'⟩ :=
          rules.sigma_other facts (d := d') xr red' (red_pi_not_sigma laws rx')
        exact facts.rel_of_daimonic hT rv dv rv' dv'
    | @sigma _ _ _ _ C C' D D' rx rx' xdP xdS xcP xcS =>
        obtain ⟨QT, rfl, iT⟩ := facts.sigmaPack hT red
        obtain ⟨QT', rfl, iT'⟩ := facts.sigmaPack hT' red'
        obtain ⟨QX, rfl, iX⟩ := facts.sigmaPack xl rx
        obtain ⟨QX', rfl, iX'⟩ := facts.sigmaPack xr rx'
        have xparts : SigmaParts V I ξ C C' D D' := ⟨xdP, xdS, xcP, xcS⟩
        have pA := shapePair_sigmaDom facts parts iT iT'
        have pC := shapePair_sigmaDom facts xparts iX iX'
        obtain ⟨s, rp, rs⟩ := rules.sigma (p := d) red rx
        obtain ⟨s', rp', rs'⟩ := rules.sigma (p := d') red' rx'
        obtain ⟨hfd, hfdd', hsdd'⟩ := hdd'
        have hab₁ := domIH.tgt pA.left pA.right pA.same pC hfdd'
        have ha₁ := facts.refl_left iT.dom_id hab₁
        have hb₁ := facts.refl_right iT.dom_id hab₁
        have pB := shapePair_sigmaCod facts parts iT iT' ha₁ hab₁ (Pack.rel_of_same pA.same hb₁)
        have pD := shapePair_sigmaCod facts xparts iX iX' hfd hfdd'
          (Pack.rel_of_same pC.same (facts.refl_right iX.dom_id hfdd'))
        have c := (codIH iT.dom_id hab₁).tgt pB.left pB.right pB.same pD hsdd'
        exact facts.expandRel hT rp rp' (PiPack.sigmaRel_pair facts iT ha₁
          (facts.expandRel iT.dom_id .refl (.single (.fstPair _ _)) hab₁)
          (facts.expandRel (iT.cod_id ha₁) rs
            ((Relation.ReflTransGen.single (.sndPair _ _)).trans rs') c))
  · -- transports out of the pair
    intro PT PT' hT hT' same Z Z' PZ PZ' tp d d' hdd'
    obtain ⟨zl, zr, -, zshape⟩ := tp
    cases zshape with
    | total lz _ => exact lz.total_rel facts zl _ _
    | univ rz rz' hz hz' =>
        obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := d) hT rz hz fun u r _ =>
          (red_sigma_not_head laws red u r).elim
        obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := d') hT' rz' hz' fun u r _ =>
          (red_sigma_not_head laws red' u r).elim
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | const hc rz rz' =>
        obtain ⟨v, rv, dv⟩ :=
          rules.const_other facts (d := d) hT hc rz (red_sigma_not_const laws red hc)
        obtain ⟨v', rv', dv'⟩ :=
          rules.const_other facts (d := d') hT' hc rz' (red_sigma_not_const laws red' hc)
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | pi rz rz' =>
        obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := d) hT rz (red_sigma_not_pi laws red)
        obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := d') hT' rz' (red_sigma_not_pi laws red')
        exact facts.rel_of_daimonic zl rv dv rv' dv'
    | @sigma _ _ _ _ E E' F F' rz rz' zdP zdS zcP zcS =>
        obtain ⟨QT, rfl, iT⟩ := facts.sigmaPack hT red
        obtain ⟨QT', rfl, iT'⟩ := facts.sigmaPack hT' red'
        obtain ⟨QZ, rfl, iZ⟩ := facts.sigmaPack zl rz
        obtain ⟨QZ', rfl, iZ'⟩ := facts.sigmaPack zr rz'
        have zparts : SigmaParts V I ξ E E' F F' := ⟨zdP, zdS, zcP, zcS⟩
        have pA := shapePair_sigmaDom facts parts iT iT'
        have pE := shapePair_sigmaDom facts zparts iZ iZ'
        obtain ⟨s, rp, rs⟩ := rules.sigma (p := d) rz red
        obtain ⟨s', rp', rs'⟩ := rules.sigma (p := d') rz' red'
        obtain ⟨hfd, hfdd', hsdd'⟩ := hdd'
        have hab₁ := domIH.src pA.left pA.right pA.same pE hfdd'
        have ha₁ := facts.refl_left iZ.dom_id hab₁
        have hb₁ := facts.refl_right iZ.dom_id hab₁
        have pF := shapePair_sigmaCod facts zparts iZ iZ' ha₁ hab₁ (Pack.rel_of_same pE.same hb₁)
        have pB := shapePair_sigmaCod facts parts iT iT' hfd hfdd'
          (Pack.rel_of_same pA.same (facts.refl_right iT.dom_id hfdd'))
        have c := (codIH iT.dom_id hfdd').src pB.left pB.right pB.same pF hsdd'
        exact facts.expandRel zl rp rp' (PiPack.sigmaRel_pair facts iZ ha₁
          (facts.expandRel iZ.dom_id .refl (.single (.fstPair _ _)) hab₁)
          (facts.expandRel (iZ.cod_id ha₁) rs
            ((Relation.ReflTransGen.single (.sndPair _ _)).trans rs') c))
  · -- coherence from the first type to the second
    intro PT PT' hT hT' same p hp
    obtain ⟨QT, rfl, iT⟩ := facts.sigmaPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.sigmaPack hT' red'
    have pA := shapePair_sigmaDom facts parts iT iT'
    obtain ⟨s, rp, rs⟩ := rules.sigma (p := p) red' red
    obtain ⟨hfp, -, hsp⟩ := hp
    have coh₁ := domIH.cohFwd pA.left pA.right pA.same hfp
    have ha₁' := facts.refl_left iT'.dom_id coh₁
    have back : (QT.dom (Morph.id ξ)).rel (.fst p) (coeApp coe A A' (.fst p)) :=
      Pack.rel_of_same pA.same.symm (facts.symm iT'.dom_id coh₁)
    have pB := shapePair_sigmaCod facts parts iT iT' hfp back ha₁'
    have c := (codIH iT.dom_id back).cohFwd pB.left pB.right pB.same hsp
    exact facts.expandLeft hT' rp (PiPack.sigmaRel_pair facts iT' ha₁' coh₁
      (facts.expandLeft (iT'.cod_id ha₁') rs c))
  · -- coherence from the second type to the first
    intro PT PT' hT hT' same p hp
    obtain ⟨QT, rfl, iT⟩ := facts.sigmaPack hT red
    obtain ⟨QT', rfl, iT'⟩ := facts.sigmaPack hT' red'
    have pA := shapePair_sigmaDom facts parts iT iT'
    obtain ⟨s, rp, rs⟩ := rules.sigma (p := p) red red'
    obtain ⟨hfp, -, hsp⟩ := hp
    have coh₁ := domIH.cohBwd pA.left pA.right pA.same hfp
    have ha₁ := facts.refl_left iT.dom_id coh₁
    have pB := shapePair_sigmaCod facts parts iT iT' ha₁ coh₁ hfp
    have c := (codIH iT.dom_id coh₁).cohBwd pB.left pB.right pB.same hsp
    exact facts.expandLeft hT rp (PiPack.sigmaRel_pair facts iT ha₁ coh₁
      (facts.expandLeft (iT.cod_id ha₁) rs c))

/-- Transports out of a hereditarily total dependent pair type are related to
the daimon: at a dependent pair type, both components are transports out of
hereditarily total types. -/
theorem srcStar_totalSigma {S A : Tm Head n} {B : Tm Head (n + 1)}
    (red : WhRed V.rules V.roles S (.sigma A B)) (interp : ∃ P, I ξ S P)
    (domShape : Shape V I .total ξ A A) (domIH : SrcStar V I coe ξ A)
    (codIH : ∀ {P : Pack V n} (_ : I ξ A P) {a : Tm Head n} (_ : P.rel a a),
      SrcStar V I coe ξ (inst0 a B)) :
    SrcStar V I coe ξ S := by
  intro Z Z' PZ PZ' tp e
  obtain ⟨PS, iS⟩ := interp
  obtain ⟨QS, rfl, iQS⟩ := facts.sigmaPack iS red
  obtain ⟨zl, zr, -, zshape⟩ := tp
  cases zshape with
  | total lz _ => exact ⟨lz.total_rel facts zl _ _, lz.total_rel facts zl _ _⟩
  | univ rz rz' hz hz' =>
      obtain ⟨v, rv, dv⟩ := rules.univ_other facts (d := e) iS rz hz fun u r _ =>
        (red_sigma_not_head laws red u r).elim
      obtain ⟨v', rv', dv'⟩ := rules.univ_other facts (d := e) iS rz' hz' fun u r _ =>
        (red_sigma_not_head laws red u r).elim
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | const hc rz rz' =>
      obtain ⟨v, rv, dv⟩ :=
        rules.const_other facts (d := e) iS hc rz (red_sigma_not_const laws red hc)
      obtain ⟨v', rv', dv'⟩ :=
        rules.const_other facts (d := e) iS hc rz' (red_sigma_not_const laws red hc)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | pi rz rz' =>
      obtain ⟨v, rv, dv⟩ := rules.pi_other facts (d := e) iS rz (red_sigma_not_pi laws red)
      obtain ⟨v', rv', dv'⟩ := rules.pi_other facts (d := e) iS rz' (red_sigma_not_pi laws red)
      exact ⟨facts.rel_star zl rv dv, facts.rel_star zl rv' dv'⟩
  | @sigma _ _ _ _ E E' F F' rz rz' zdP zdS zcP zcS =>
      obtain ⟨QZ, rfl, iZ⟩ := facts.sigmaPack zl rz
      obtain ⟨QZ', rfl, iZ'⟩ := facts.sigmaPack zr rz'
      have zparts : SigmaParts V I ξ E E' F F' := ⟨zdP, zdS, zcP, zcS⟩
      have pE := shapePair_sigmaDom facts zparts iZ iZ'
      have hfe : (QS.dom (Morph.id ξ)).Val (.fst e) := domShape.total_rel facts iQS.dom_id _ _
      obtain ⟨s, rp, rs⟩ := rules.sigma (p := e) rz red
      obtain ⟨s', rp', rs'⟩ := rules.sigma (p := e) rz' red
      have dstar := domIH pE (.fst e)
      have ha₁ := facts.refl_left iZ.dom_id dstar.1
      have ha₂ := facts.refl_left iZ.dom_id dstar.2
      constructor
      · have pF := shapePair_sigmaCod facts zparts iZ iZ' ha₁ ha₁ (Pack.rel_of_same pE.same ha₁)
        have c := (codIH iQS.dom_id hfe pF (.snd e)).1
        exact facts.expandLeft zl rp (PiPack.sigmaRel_pair facts iZ ha₁
          (facts.trans iZ.dom_id dstar.1 (facts.daimonicRel iZ.dom_id .star (.fst .star)))
          (facts.expandLeft (iZ.cod_id ha₁) rs (facts.trans (iZ.cod_id ha₁) c
            (facts.daimonicRel (iZ.cod_id ha₁) .star (.snd .star)))))
      · have pF := shapePair_sigmaCod facts zparts iZ iZ' ha₂ ha₂ (Pack.rel_of_same pE.same ha₂)
        have c := (codIH iQS.dom_id hfe pF (.snd e)).2
        exact facts.expandLeft zl rp' (PiPack.sigmaRel_pair facts iZ ha₂
          (facts.trans iZ.dom_id dstar.2 (facts.daimonicRel iZ.dom_id .star (.fst .star)))
          (facts.expandLeft (iZ.cod_id ha₂) rs' (facts.trans (iZ.cod_id ha₂) c
            (facts.daimonicRel (iZ.cod_id ha₂) .star (.snd .star)))))

end Pairs

/-! ## The induction -/

/-- **The semantic core of the transport.** Every shape derivation satisfies its
claims: for a pair of types of one shape, transports into and out of it respect
related inputs, the transport between its two types returns a term related to
its method in both directions, and transports into it from a hereditarily total
type are related to the daimon; for a hereditarily total type, transports out
of it into either type of any pair are related to the daimon. -/
theorem Shape.claims {V : Model Head L} (laws : V.Laws) {I : IPack V} (facts : InterpFacts V I)
    {coe : DeclName} (rules : CoeRules V coe) {g : Grade} {n : Nat} {ξ : World V.reading n}
    {X X' : Tm Head n} (h : Shape V I g ξ X X') : ShapeClaims V I coe g ξ X X' := by
  induction h with
  | total left right leftIH rightIH => exact pairClaims_total facts left right leftIH rightIH
  | univ red red' hu hu' level => exact pairClaims_univ laws facts rules red red' hu hu' level
  | const hc red red' => exact pairClaims_const laws facts rules hc red red'
  | pi red red' domPacks domShape codPacks codShape domIH codIH =>
      exact pairClaims_pi laws facts rules red red' ⟨domPacks, domShape, codPacks, codShape⟩
        domIH codIH
  | sigma red red' domPacks domShape codPacks codShape domIH codIH =>
      exact pairClaims_sigma laws facts rules red red' ⟨domPacks, domShape, codPacks, codShape⟩
        domIH codIH
  | leaf leaf notSigma => exact srcStar_leaf facts rules leaf notSigma
  | totalPi red interp _ _ domIH codIH =>
      exact srcStar_totalPi laws facts rules red interp domIH codIH
  | totalSigma red interp domShape _ domIH codIH =>
      exact srcStar_totalSigma laws facts rules red interp domShape domIH codIH

/-! ## The transport's laws -/

section Laws

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- The claims about a pair of types of one shape. -/
theorem Shape.pairClaims {X X' : Tm Head n} (h : Shape V I .pair ξ X X') :
    PairClaims V I coe ξ X X' :=
  Shape.claims laws facts rules h

/-- Transports out of a hereditarily total type are related to the daimon. -/
theorem Shape.srcStar {S : Tm Head n} (h : Shape V I .total ξ S S) : SrcStar V I coe ξ S :=
  Shape.claims laws facts rules h

/-- **Validity.** A transport of a valid method, between types each of one shape
with itself, is a valid value of the target. -/
theorem coe_val {X Y : Tm Head n} {PX PY : Pack V n} (hX : I ξ X PX) (hY : I ξ Y PY)
    (coverX : Shape V I .pair ξ X X) (coverY : Shape V I .pair ξ Y Y) {d : Tm Head n}
    (hd : PX.Val d) : PY.Val (coeApp coe X Y d) :=
  (coverY.pairClaims laws facts rules).tgt hY hY rfl ⟨hX, hX, rfl, coverX⟩ hd

/-- **Congruence.** Transports of related methods, from the two types of a pair
of sources into the two types of a pair of targets, are related. -/
theorem coe_congr {X X' Y Y' : Tm Head n} {PX PX' PY PY' : Pack V n}
    (sources : ShapePair V I ξ X X' PX PX') (targets : ShapePair V I ξ Y Y' PY PY')
    {d d' : Tm Head n} (hdd' : PX.rel d d') :
    PY.rel (coeApp coe X Y d) (coeApp coe X' Y' d') :=
  (targets.shape.pairClaims laws facts rules).tgt targets.left targets.right targets.same sources
    hdd'

/-- **Coherence.** Between two types of one shape whose packs have one relation,
the transport returns a term related to its method. -/
theorem coe_coherent {X Y : Tm Head n} {PX PY : Pack V n} (same : ShapePair V I ξ X Y PX PY)
    {d : Tm Head n} (hd : PX.Val d) : PY.rel (coeApp coe X Y d) d :=
  (same.shape.pairClaims laws facts rules).cohFwd same.left same.right same.same hd

/-- Between two types of one shape whose packs have one relation, the transport
has the realizers of its method. -/
theorem coe_real {X Y : Tm Head n} {PX PY : Pack V n} (same : ShapePair V I ξ X Y PX PY)
    {d : Tm Head n} (hd : PX.Val d) : PY.real (coeApp coe X Y d) = PY.real d :=
  facts.realEq same.right (coe_coherent laws facts rules same hd)

/-- **A transport out of a hereditarily total type is related to the daimon**,
in the pack of any type of one shape with itself. -/
theorem coe_total_star {S Z : Tm Head n} {PZ : Pack V n} (total : Shape V I .total ξ S S)
    (hZ : I ξ Z PZ) (cover : Shape V I .pair ξ Z Z) (e : Tm Head n) :
    PZ.rel (coeApp coe S Z e) (.const V.star) :=
  (total.srcStar laws facts rules ⟨hZ, hZ, rfl, cover⟩ e).1

/-- Transports out of two hereditarily total types, of any structures, into the
two types of a pair, are related. -/
theorem coe_total_congr {S S' Z Z' : Tm Head n} {PZ PZ' : Pack V n}
    (total : Shape V I .total ξ S S) (total' : Shape V I .total ξ S' S')
    (targets : ShapePair V I ξ Z Z' PZ PZ') (e e' : Tm Head n) :
    PZ.rel (coeApp coe S Z e) (coeApp coe S' Z' e') :=
  facts.rel_of_star targets.left (total.srcStar laws facts rules targets e).1
    (total'.srcStar laws facts rules targets e').2

/-- The transport along one type is related to its method: identity
elimination at reflexivity, on the value side. -/
theorem coe_self {X : Tm Head n} {PX : Pack V n} (hX : I ξ X PX)
    (cover : Shape V I .pair ξ X X) {d : Tm Head n} (hd : PX.Val d) :
    PX.rel (coeApp coe X X d) d :=
  coe_coherent laws facts rules ⟨hX, hX, rfl, cover⟩ hd

end Laws

/-! ## Transports between type constants -/

section TypeConstants

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- **The transport between one type constant returns its method**, at the
codes and at every inductive type, and it is a valid value. -/
theorem coe_typeConst_same {c : DeclName} (hc : TypeConst V c) {X Y : Tm Head n}
    {PX PY : Pack V n} (hX : I ξ X PX) (hY : I ξ Y PY) (rX : WhRed V.rules V.roles X (.const c))
    (rY : WhRed V.rules V.roles Y (.const c)) {d : Tm Head n} (hd : PX.Val d) :
    WhRed V.rules V.roles (coeApp coe X Y d) d ∧ PY.Val (coeApp coe X Y d) :=
  ⟨rules.const hc rY rX, coe_val laws facts rules hX hY (.const hc rX rX) (.const hc rY rY) hd⟩

omit laws in
/-- **The transport between two type constants is stuck on the daimon**, and it
is a valid value, whatever the method. -/
theorem coe_typeConst_other {c c' : DeclName} (hc : TypeConst V c) (hc' : TypeConst V c')
    (ne : c ≠ c') {X Y : Tm Head n} {PY : Pack V n} (rX : WhRed V.rules V.roles X (.const c))
    (hY : I ξ Y PY) (rY : WhRed V.rules V.roles Y (.const c')) (d : Tm Head n) :
    (∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v) ∧
      PY.Val (coeApp coe X Y d) := by
  obtain ⟨v, rv, dv⟩ := rules.constOther hc' rY rX (.inr (.inl ⟨c, hc, rfl⟩))
    fun e => ne (Tm.const.inj e)
  exact ⟨⟨v, rv, dv⟩, facts.rel_of_daimonic hY rv dv rv dv⟩

/-- **Transport between one inductive type returns its method**, a valid
value. -/
theorem coe_ind_same {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {X Y : Tm Head n} {PX PY : Pack V n} (hX : I ξ X PX)
    (hY : I ξ Y PY) (rX : WhRed V.rules V.roles X (.const T))
    (rY : WhRed V.rules V.roles Y (.const T)) {d : Tm Head n} (hd : PX.Val d) :
    WhRed V.rules V.roles (coeApp coe X Y d) d ∧ PY.Val (coeApp coe X Y d) :=
  coe_typeConst_same laws facts rules (.inr ⟨cs, role⟩) hX hY rX rY hd

omit laws in
/-- **Transport between two inductive types is stuck on the daimon**, a valid
value of the target, whatever the method. -/
theorem coe_ind_other {T T' : DeclName} {cs cs' : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) (role' : V.roles T' = .inductive cs') (ne : T ≠ T')
    {X Y : Tm Head n} {PY : Pack V n} (rX : WhRed V.rules V.roles X (.const T)) (hY : I ξ Y PY)
    (rY : WhRed V.rules V.roles Y (.const T')) (d : Tm Head n) :
    (∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v) ∧
      PY.Val (coeApp coe X Y d) :=
  coe_typeConst_other facts rules (.inr ⟨cs, role⟩) (.inr ⟨cs', role'⟩) ne rX hY rY d

end TypeConstants

/-! ## Controls -/

section Controls

variable {V : Model Head L} (laws : V.Laws)
include laws

/-- A type that reduces to `num → num` is of one shape with itself, by the
clause of dependent function types, over every interpretation with the facts. -/
theorem Shape.numArrow_of_red {I : IPack V} (facts : InterpFacts V I) {n : Nat}
    {ξ : World V.reading n} {Y : Tm Head n} {PY : Pack V n} (hY : I ξ Y PY)
    (rY : WhRed V.rules V.roles Y (.pi (.const V.num) (.const V.num))) :
    Shape V I .pair ξ Y Y := by
  obtain ⟨Q, rfl, iQ⟩ := facts.piPack hY rY
  have hnum : TypeConst V V.num := .inr ⟨_, laws.num_role⟩
  refine .pi rY rY (fun w => ⟨_, _, iQ.dom w, iQ.dom w, rfl⟩) (fun _ => .const hnum .refl .refl)
    (fun {_ _ _} w {P} hP {a b} hab => ?_) (fun {_ _ _} _ {_} _ {_ _} _ => .const hnum .refl .refl)
  obtain rfl := facts.deterministic hP (iQ.dom w)
  have ha := facts.refl_left (iQ.dom w) hab
  have hb := facts.refl_right (iQ.dom w) hab
  exact ⟨_, _, iQ.cod w ha, iQ.cod w hb, by rw [iQ.codRespect w ha hb hab]⟩

/-- **A large motive does not break the transport** (the positive form of the
large-motive control). A transport from a type that computes the numbers into
a type that computes `num → num` is stuck on the daimon, the source being no
dependent function type, and it is a valid value of the target. A cast of
identity elimination returns the number itself, which the pack of `num → num`
does not relate to itself: applied to the daimon, a number, it has no shape. -/
theorem coe_num_numArrow {I : IPack V} (facts : InterpFacts V I) {coe : DeclName}
    (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n}
    {PX PY : Pack V n} (hX : I ξ X PX) (hY : I ξ Y PY)
    (rX : WhRed V.rules V.roles X (.const V.num))
    (rY : WhRed V.rules V.roles Y (.pi (.const V.num) (.const V.num))) {d : Tm Head n}
    (hd : PX.Val d) :
    (∃ v, WhRed V.rules V.roles (coeApp coe X Y d) v ∧ Daimonic V.roles V.star v) ∧
      PY.Val (coeApp coe X Y d) := by
  have hnum : TypeConst V V.num := .inr ⟨_, laws.num_role⟩
  exact ⟨rules.pi_other facts hX rY (red_const_not_pi laws hnum rX),
    coe_val laws facts rules hX hY (.const hnum rX rX) (Shape.numArrow_of_red laws facts hY rY) hd⟩

/-- The transport along a type that reduces to `num → num` is related to its
method: coherence through the clause of dependent function types, which
`num → num`, not hereditarily total (`numArrow_shape`), exercises. -/
theorem coe_numArrow_self {I : IPack V} (facts : InterpFacts V I) {coe : DeclName}
    (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n} {Y : Tm Head n} {PY : Pack V n}
    (hY : I ξ Y PY) (rY : WhRed V.rules V.roles Y (.pi (.const V.num) (.const V.num)))
    {f : Tm Head n} (hf : PY.Val f) : PY.rel (coeApp coe Y Y f) f :=
  coe_self laws facts rules hY (Shape.numArrow_of_red laws facts hY rY) hf

/-- **A method row at an inductive type breaks validity.** A term that reduces
to a nullary constructor `k` that the inductive type `T` does not list is no
value of `T`, whatever the packs of its closed field types: it reduces neither
to a spine of a constructor `T` lists nor to a term stuck on the daimon. So a
transport into `T` that returned such a method is not valid. -/
theorem methodRow_ind_not_val {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) {k : DeclName} (ctor : V.roles k = .constructor 0)
    (notListed : ∀ fs, (k, fs) ∉ cs) {n : Nat} {field : Tm Head 0 → Pack V n} {t : Tm Head n}
    (method : WhRed V.rules V.roles t (.const k)) : ¬ (indPack V T cs field).Val t := by
  have notComputing : ∀ arity inspect, V.roles k ≠ .computes arity inspect := fun _ _ h => by
    rw [ctor] at h
    cases h
  have normal : Whnf V.rules V.roles (.const k : Tm Head n) :=
    constSpine_whnf laws.shape notComputing (args := [])
  intro valid
  cases valid with
  | ctor mem red _ _ =>
      have e := laws.unique red method (laws.ctorSpine_whnf role mem _) normal
      obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const e
      exact notListed _ mem
  | star red daimonic _ _ =>
      have e := laws.unique red method (laws.daimonic_whnf daimonic) normal
      subst e
      exact Model.Laws.daimonic_ne_constSpine (args := []) daimonic
        (fun e => by rw [e, laws.star] at ctor; cases ctor) notComputing rfl

/-- **`MethodForm` must exclude inductive types.** For an inductive type `T`
without closed fields that does not list `zero`, the premises of `coe_val` hold
for the transport of `zero` from the numbers into `T`, at every level: both
types are interpreted and of one shape with themselves, and `zero` is a valid
number. A transport that returned its method there would have a result that is
no value of `T`. -/
theorem methodRow_ind_breaks_coe_val {T : DeclName} {cs : List (DeclName × List (Field Head))}
    (role : V.roles T = .inductive cs) (closed : closedFields cs = [])
    (notListed : ∀ fs, (V.zero, fs) ∉ cs) (l : L) {n : Nat} (ξ : World V.reading n)
    {coe : DeclName}
    (method : WhRed V.rules V.roles
      (coeApp coe (.const V.num) (.const T) (.const V.zero) : Tm Head n) (.const V.zero)) :
    InterpAt V l ξ (.const V.num) (numIndPack V n) ∧
      InterpAt V l ξ (.const T) (indPack V T cs fun _ => Pack.total V n) ∧
      Shape V (InterpAt V l) .pair ξ (.const V.num) (.const V.num) ∧
      Shape V (InterpAt V l) .pair ξ (.const T) (.const T) ∧
      (numIndPack V n).Val (.const V.zero) ∧
      ¬ (indPack V T cs fun _ => Pack.total V n).Val
        (coeApp coe (.const V.num) (.const T) (.const V.zero)) := by
  refine ⟨InterpAt.num laws l .refl, SInterp.ind .refl role _ fun hF => ?_,
    .const (.inr ⟨_, laws.num_role⟩) .refl .refl, .const (.inr ⟨_, role⟩) .refl .refl,
    numIndPack_rel.mpr ⟨.zero, .zero .refl, .zero .refl⟩,
    methodRow_ind_not_val laws role laws.values.truth.zero notListed method⟩
  rw [closed] at hF
  cases hF

end Controls

/-! ## A lawful model in which a method row fires at an inductive type

The value model below has the numbers and an inductive type `bool` with the
constructors `true` and `false`, and a transport constant `coe` that returns its
method at every pair of types: `coe X Y d ⟶ d`. It has every law of a value
model. So its method row fires from the numbers into `bool`, and the transport
of the valid number `zero` is no value of `bool`: `coe_val` fails for a table
whose method row reaches an inductive type. -/

namespace InductiveMethodControl

/-- The constants by number: `zero`, `suc`, `imp`, the numbers, the codes, the
decoder, the daimon, `bool`, `true`, `false`, and `coe`, numbered `0` to `10`. -/
def name (i : Nat) : DeclName := .num .anonymous i

/-- The one computation: `coe X Y d ⟶ d`. -/
def computation : RootComputation Empty where
  step := fun t u => ∃ X Y d, t = appSpine (.const (name 10)) [X, Y, d] ∧ u = d
  rename := fun {_ _} ρ {_ _} ⟨X, Y, d, e, e'⟩ =>
    ⟨Presentation.rename ρ X, Presentation.rename ρ Y, Presentation.rename ρ d,
      by subst e; rfl, by subst e'; rfl⟩
  substitute := fun {_ _} σ {_ _} ⟨X, Y, d, e, e'⟩ =>
    ⟨Presentation.subst σ X, Presentation.subst σ Y, Presentation.subst σ d,
      by subst e; rfl, by subst e'; rfl⟩

/-- The constructors of `bool`. -/
def boolConstructors : List (DeclName × List (Field Empty)) := [(name 8, []), (name 9, [])]

/-- The roles: `zero`, `suc`, `imp`, `true` and `false` are constructors; the
numbers and `bool` are inductive; `coe` computes on three arguments; every
other constant is rigid. -/
def roles : Roles Empty := fun c =>
  if c = name 0 then .constructor 0
  else if c = name 1 then .constructor 1
  else if c = name 2 then .constructor 2
  else if c = name 3 then .inductive [(name 0, []), (name 1, [.recursive])]
  else if c = name 7 then .inductive boolConstructors
  else if c = name 8 then .constructor 0
  else if c = name 9 then .constructor 0
  else if c = name 10 then .computes 3 .leaf
  else .rigid

/-- The package: no heads, and the computation of `coe`. -/
def rules : Rules Empty where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  computation := computation

theorem rootShape : RootShape rules roles where
  spine := fun {_ _ _} ⟨X, Y, d, e, _⟩ => ⟨name 10, 3, .leaf, [X, Y, d], rfl, e, rfl, .leaf _⟩
  deterministic := fun {_ _ _ _} ⟨X, Y, d, e, e'⟩ ⟨X', Y', d', f, f'⟩ => by
    subst e' f'
    rw [e] at f
    obtain ⟨-, args⟩ := appSpine_const_injective f
    exact (List.cons.inj (List.cons.inj (List.cons.inj args).2).2).1

/-- The inductive types are the numbers and `bool`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Empty))}
    (role : roles T = .inductive cs) :
    cs = [(name 0, []), (name 1, [.recursive])] ∨ cs = boolConstructors := by
  unfold roles at role
  split_ifs at role <;> first
    | (cases role; done)
    | (cases role; exact .inl rfl)
    | (cases role; exact .inr rfl)

theorem declared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fs role mem
    rcases roles_inductive role with rfl | rfl
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
    · simp only [boolConstructors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  distinct := by
    intro T cs role
    rcases roles_inductive role with rfl | rfl <;> decide

/-- The setting of the package: no quantifiers or equations. -/
def setting : Consistency.Setting Empty where
  rules := rules
  roles := roles
  zero := name 0
  suc := name 1
  imp := name 2
  allCarrier := fun _ => none
  eqCarrier := fun _ => none

theorem setting_laws : setting.Laws where
  shape := rootShape
  zero := rfl
  suc := rfl
  imp := rfl
  all := fun h => nomatch h
  eq := fun h => nomatch h
  impNotEq := rfl

/-- The levels of the package: it has no universes. -/
def levelModel : LevelModel rules ℕ where
  level := fun _ => 0
  successor := fun hu => False.elim hu
  universe_typing := fun hu _ => False.elim hu
  ground_typing := fun h => False.elim h
  cumulative_universe := fun h => False.elim h
  headEq_level := fun h => False.elim h
  join_level := fun h => False.elim h
  join_exists := fun hu _ => False.elim hu
  join_upper := fun h => False.elim h
  cumulative_refl := fun hu => False.elim hu
  headEq_symm := fun h => False.elim h
  headEq_trans := fun h _ => False.elim h
  universe_decided := fun _ => .inr id

/-- The value model of the package, with the daimon `name 6` and the realizer
algebra with one candidate. -/
def model : Model Empty Nat where
  toSetting := setting
  num := name 3
  prop := name 4
  holds := name 5
  levels := levelModel
  star := name 6
  alg := UndeclaredControl.unitAlgebra

/-- **The model has every law of a value model.** -/
theorem model_laws : model.Laws where
  values := ⟨setting_laws, rfl, rfl, rfl⟩
  star := rfl
  starNotProp := by decide
  starNotHolds := by decide
  alg := UndeclaredControl.unitAlgebra_laws
  declared := declared

/-- **In a lawful value model, a method row at an inductive type breaks
`coe_val`.** The transport returns its method from the numbers into `bool`;
the premises of `coe_val` hold for the transport of `zero`, at every level; and
the result is no value of `bool`. -/
theorem methodRow_breaks_coe_val (l : Nat) :
    model.Laws ∧
      WhRed model.rules model.roles
        (coeApp (name 10) (.const model.num) (.const (name 7)) (.const model.zero) : Tm Empty 0)
        (.const model.zero) ∧
      InterpAt model l Consistency.World.closed (.const model.num) (numIndPack model 0) ∧
      InterpAt model l Consistency.World.closed (.const (name 7))
        (indPack model (name 7) boolConstructors fun _ => Pack.total model 0) ∧
      Shape model (InterpAt model l) .pair Consistency.World.closed (.const model.num)
        (.const model.num) ∧
      Shape model (InterpAt model l) .pair Consistency.World.closed (.const (name 7))
        (.const (name 7)) ∧
      (numIndPack model 0).Val (.const model.zero) ∧
      ¬ (indPack model (name 7) boolConstructors fun _ => Pack.total model 0).Val
        (coeApp (name 10) (.const model.num) (.const (name 7)) (.const model.zero)) := by
  have method : WhRed model.rules model.roles
      (coeApp (name 10) (.const model.num) (.const (name 7)) (.const model.zero) : Tm Empty 0)
      (.const model.zero) :=
    Relation.ReflTransGen.single (.root ⟨_, _, _, rfl, rfl⟩)
  exact ⟨model_laws, method, methodRow_ind_breaks_coe_val model_laws rfl rfl
    (fun fs mem => by
      simp only [boolConstructors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at mem
      rcases mem with ⟨e, -⟩ | ⟨e, -⟩ <;> exact absurd e (by decide))
    l _ method⟩

end InductiveMethodControl

/-! ## At the interpretation at a level and at the denotation -/

section Instances

variable {V : Model Head L} {coe : DeclName} (laws : V.Laws) (rules : CoeRules V coe)
  {n : Nat} {ξ : World V.reading n}
include laws rules

/-- Validity at a level. -/
theorem InterpAt.coe_val {l : L} {X Y : Tm Head n} {PX PY : Pack V n}
    (hX : InterpAt V l ξ X PX) (hY : InterpAt V l ξ Y PY)
    (coverX : Shape V (InterpAt V l) .pair ξ X X) (coverY : Shape V (InterpAt V l) .pair ξ Y Y)
    {d : Tm Head n} (hd : PX.Val d) : PY.Val (coeApp coe X Y d) :=
  ValueSide.coe_val laws (InterpAt.facts laws l) rules hX hY coverX coverY hd

/-- Validity of denotations. -/
theorem DenS.coe_val {X Y : Tm Head n} {PX PY : Pack V n} (hX : DenS V ξ X PX)
    (hY : DenS V ξ Y PY) (coverX : Shape V (DenS V) .pair ξ X X)
    (coverY : Shape V (DenS V) .pair ξ Y Y) {d : Tm Head n} (hd : PX.Val d) :
    PY.Val (coeApp coe X Y d) :=
  ValueSide.coe_val laws (DenS.facts laws) rules hX hY coverX coverY hd

/-- Congruence of denotations. -/
theorem DenS.coe_congr {X X' Y Y' : Tm Head n} {PX PX' PY PY' : Pack V n}
    (sources : ShapePair V (DenS V) ξ X X' PX PX') (targets : ShapePair V (DenS V) ξ Y Y' PY PY')
    {d d' : Tm Head n} (hdd' : PX.rel d d') :
    PY.rel (coeApp coe X Y d) (coeApp coe X' Y' d') :=
  ValueSide.coe_congr laws (DenS.facts laws) rules sources targets hdd'

/-- Coherence of denotations. -/
theorem DenS.coe_coherent {X Y : Tm Head n} {PX PY : Pack V n}
    (same : ShapePair V (DenS V) ξ X Y PX PY) {d : Tm Head n} (hd : PX.Val d) :
    PY.rel (coeApp coe X Y d) d :=
  ValueSide.coe_coherent laws (DenS.facts laws) rules same hd

/-- The transport between denoted types exists. -/
theorem DenS.coe_reduct {X Y : Tm Head n} {PX PY : Pack V n} (hX : DenS V ξ X PX)
    (hY : DenS V ξ Y PY) (d : Tm Head n) :
    ∃ r, WhRed V.rules V.roles (coeApp coe X Y d) r ∧ CoeReduct V coe X Y d r :=
  CoeRules.reduct laws (DenS.facts laws) rules hX hY d

end Instances

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
