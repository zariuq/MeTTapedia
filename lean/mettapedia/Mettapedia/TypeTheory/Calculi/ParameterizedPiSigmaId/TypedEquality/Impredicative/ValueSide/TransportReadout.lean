import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport
import Mettapedia.TypeTheory.ObserverTransportCompatibility

/-!
# The transport commutes with the extensional readout

The extensional readout of a term at a pack is its class under the pack's
relation (`Pack.readout`).  A pair of types of one shape whose packs have one
relation (`ShapePair`) is erased to the equation between the two relations, and
extensional transport along that equation
(`ObserverTransportCompatibility.transportE`) sends the class of a term to the
class of the same term.  The transport `coe` commutes with the readout:

`E_Y (coe X Y d) = transport_E (E p) (E_X d)`  (`coe_readout`).

The relation behind the equation is the target pack's relation,
`PY.rel (coe X Y d) d` (`coe_coherent`).  In the terms of
`NonFactorization.Factors`, the readout of the transported value factors through
the readout of the method, by extensional transport (`coe_readout_factors`).

**Identity transport.**  On the value side identity elimination transports its
method along its motive: `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`.  When
the motive's two instances form a pair of one shape with one pack `Q`, as a
valid motive's instances do at related endpoints, the eliminator is related to
its method at `Q` and has the method's readout (`transportJ_rel`,
`transportJ_readout`).  The pair is what a universe relates: motive instances
related in a universe have one pack (`transportJ_rel_of_universe`), which is how
a valid motive's instances at related endpoints are related in the model of
denotations.  The path enters only through the motive's instance: an identity
type relates every two paths.  Instances at the denotation and at a level:
`DenS.coe_readout`, `InterpAt.transportJ_rel_of_universe`.

**The relation is the pack's, not equality of terms.**  The transported term
itself is not an observer of the readout: a value and its weak-head expansion
`fst (d, d)` have one readout and transport to different terms
(`coe_term_not_factors`).  This is the model's instance of the corrected law of
`ObserverTransportCompatibility`: an observer commutes with transport when it
factors through the extensional readout.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Rel World)
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.ObserverTransportCompatibility (transportE)

variable {Head L : Type} [LevelOrder L]

/-! ## The extensional readout of a pack -/

section Readout

variable {V : Model Head L} {n : Nat}

/-- The extensional readout of a term at a pack: its class under the pack's
relation. -/
def Pack.readout (P : Pack V n) (t : Tm Head n) : Quot P.rel :=
  Quot.mk P.rel t

/-- Related terms have one readout. -/
theorem Pack.readout_eq {P : Pack V n} {t u : Tm Head n} (related : P.rel t u) :
    P.readout t = P.readout u :=
  Quot.sound related

/-- Extensional transport along an equation of relations sends the class of a
term to the class of the same term. -/
theorem quot_transportE {α : Type} {first second : α → α → Prop} (same : first = second)
    (t : α) :
    transportE (fun relation : α → α → Prop => Quot relation) same (Quot.mk first t) =
      Quot.mk second t := by
  subst same
  rfl

/-- The same, for the readouts of two packs with one relation. -/
theorem readout_transportE {P P' : Pack V n} (same : P.rel = P'.rel) (t : Tm Head n) :
    transportE (fun relation : Rel Head n => Quot relation) same (P.readout t) = P'.readout t :=
  quot_transportE same t

end Readout

/-! ## The transport and the readout -/

section Transport

variable {V : Model Head L} {I : IPack V} {coe : DeclName} (laws : V.Laws)
  (facts : InterpFacts V I) (rules : CoeRules V coe) {n : Nat} {ξ : World V.reading n}
include laws facts rules

/-- **The transport commutes with the extensional readout**:
`E_Y (coe X Y d) = transport_E (E p) (E_X d)`, for a pair of types of one shape
whose packs have one relation and a valid method. -/
theorem coe_readout {X Y : Tm Head n} {PX PY : Pack V n} (same : ShapePair V I ξ X Y PX PY)
    {d : Tm Head n} (hd : PX.Val d) :
    PY.readout (coeApp coe X Y d) =
      transportE (fun relation : Rel Head n => Quot relation) same.same (PX.readout d) := by
  rw [readout_transportE]
  exact Pack.readout_eq (coe_coherent laws facts rules same hd)

/-- In the observer framework: the readout of the transported value factors
through the readout of the method, and its readout is extensional transport. -/
theorem coe_readout_factors {X Y : Tm Head n} {PX PY : Pack V n}
    (same : ShapePair V I ξ X Y PX PY) :
    Factors (fun d : {d : Tm Head n // PX.Val d} => PX.readout d.1)
      (fun d => PY.readout (coeApp coe X Y d.1)) :=
  ⟨transportE (fun relation : Rel Head n => Quot relation) same.same,
    fun d => (coe_readout laws facts rules same d.2).symm⟩

/-- **Identity transport is related to its method.**  If on the value side the
eliminator `J` transports its method along its motive, and the motive's
instances at the base point with reflexivity and at the endpoint with the path
form a pair of one shape with one pack `Q`, then `J A x P d y e` is related to
`d` at `Q`. -/
theorem transportJ_rel {J : DeclName}
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      V.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    {A x P d y e : Tm Head n} {Q : Pack V n}
    (same : ShapePair V I ξ (.app (.app P x) (.refl x)) (.app (.app P y) e) Q Q)
    (hd : Q.Val d) :
    Q.rel (appSpine (.const J) [A, x, P, d, y, e]) d :=
  facts.expandLeft same.right (.single (.root (jStep A x P d y e)))
    (coe_coherent laws facts rules same hd)

/-- **Identity transport commutes with the extensional readout**:
`E (J A x P d y e) = transport_E (E e) (E d)`, where the erasure of the path is
the equation of the motive's relation with itself. -/
theorem transportJ_readout {J : DeclName}
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      V.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    {A x P d y e : Tm Head n} {Q : Pack V n}
    (same : ShapePair V I ξ (.app (.app P x) (.refl x)) (.app (.app P y) e) Q Q)
    (hd : Q.Val d) :
    Q.readout (appSpine (.const J) [A, x, P, d, y, e]) =
      transportE (fun relation : Rel Head n => Quot relation) same.same (Q.readout d) := by
  rw [readout_transportE]
  exact Pack.readout_eq (transportJ_rel laws facts rules jStep same hd)

/-- **Identity transport at related instances of the motive.**  If the motive's
instances at the base point with reflexivity and at the endpoint with the path
are related in a universe of the interpretation, as a valid motive's instances
are at related endpoints, then the endpoint instance has the pack `Q` of the base
instance (the erased path is trivial), and `J A x P d y e` is related to `d` at
`Q`. -/
theorem transportJ_rel_of_universe {J : DeclName}
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      V.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    {A x P d y e : Tm Head n} {Q : Pack V n}
    (related : (universePack V I ξ).rel (.app (.app P x) (.refl x)) (.app (.app P y) e))
    (hQ : I ξ (.app (.app P x) (.refl x)) Q) (hd : Q.Val d) :
    I ξ (.app (.app P y) e) Q ∧ Q.rel (appSpine (.const J) [A, x, P, d, y, e]) d := by
  obtain ⟨_, same⟩ := ShapePair.of_universe related
  obtain rfl := facts.deterministic hQ same.left
  exact ⟨same.right, transportJ_rel laws facts rules jStep same hd⟩

end Transport

/-! ## At the denotation and at a level -/

section Instances

variable {V : Model Head L} {coe : DeclName} (laws : V.Laws) (rules : CoeRules V coe)
  {n : Nat} {ξ : World V.reading n}
include laws rules

/-- The transport commutes with the readout of denotations. -/
theorem DenS.coe_readout {X Y : Tm Head n} {PX PY : Pack V n}
    (same : ShapePair V (DenS V) ξ X Y PX PY) {d : Tm Head n} (hd : PX.Val d) :
    PY.readout (coeApp coe X Y d) =
      transportE (fun relation : Rel Head n => Quot relation) same.same (PX.readout d) :=
  ValueSide.coe_readout laws (DenS.facts laws) rules same hd

/-- Identity transport at the interpretation at a level, the universe level of
the motive. -/
theorem InterpAt.transportJ_rel_of_universe (l : L) {J : DeclName}
    (jStep : ∀ {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head m),
      V.rules.computation.step (appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, a₅])
        (coeApp coe (.app (.app a₂ a₁) (.refl a₁)) (.app (.app a₂ a₄) a₅) a₃))
    {A x P d y e : Tm Head n} {Q : Pack V n}
    (related : (universePack V (InterpAt V l) ξ).rel (.app (.app P x) (.refl x))
      (.app (.app P y) e))
    (hQ : InterpAt V l ξ (.app (.app P x) (.refl x)) Q) (hd : Q.Val d) :
    InterpAt V l ξ (.app (.app P y) e) Q ∧ Q.rel (appSpine (.const J) [A, x, P, d, y, e]) d :=
  ValueSide.transportJ_rel_of_universe laws (InterpAt.facts laws l) rules jStep related hQ hd

end Instances

/-! ## The relation is the pack's -/

section Terms

variable {V : Model Head L} {I : IPack V} (facts : InterpFacts V I) {n : Nat}
  {ξ : World V.reading n}
include facts

/-- A value is related to its weak-head expansion `fst (d, d)`. -/
theorem fstPair_rel {X : Tm Head n} {PX : Pack V n} (hX : I ξ X PX) {d : Tm Head n}
    (hd : PX.Val d) : PX.rel (.fst (.pair d d)) d :=
  facts.expandLeft hX (.single (.fstPair d d)) hd

/-- The expansion is a valid value. -/
theorem fstPair_val {X : Tm Head n} {PX : Pack V n} (hX : I ξ X PX) {d : Tm Head n}
    (hd : PX.Val d) : PX.Val (.fst (.pair d d)) :=
  facts.expandRel hX (.single (.fstPair d d)) (.single (.fstPair d d)) hd

omit facts in
/-- A term is not its own expansion. -/
theorem fstPair_ne (d : Tm Head n) : (Tm.fst (Tm.pair d d) : Tm Head n) ≠ d := fun same => by
  have sizes := congrArg sizeOf same
  simp only [Tm.fst.sizeOf_spec, Tm.pair.sizeOf_spec] at sizes
  omega

/-- **The transported term is not an observer of the readout**: a valid value
and its expansion have one readout and transport to different terms. -/
theorem coe_term_not_factors (coe : DeclName) {X Y : Tm Head n} {PX : Pack V n}
    (hX : I ξ X PX) {d : Tm Head n} (hd : PX.Val d) :
    ¬ Factors (fun d : {d : Tm Head n // PX.Val d} => PX.readout d.1)
      (fun d => coeApp coe X Y d.1) :=
  NonTrivialFiber.not_factors
    { left := ⟨.fst (.pair d d), fstPair_val facts hX hd⟩
      right := ⟨d, hd⟩
      sameShadow := Pack.readout_eq (fstPair_rel facts hX hd)
      differentValue := fun same => fstPair_ne d (Tm.app.inj same).2 }

end Terms

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
