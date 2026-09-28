import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator

/-!
# Motives of identity elimination on the value side

Over every realizer algebra:

* **Motives.** A motive related to another, applied to related points and to any
  two paths, gives types related in the motive's universe, since an identity
  type relates every two paths (`idMotive_universe`); so the two applications
  are a pair of one shape with one pack at the motive's level
  (`idMotive_shapePair`).
* **Transports.** Between two types of one shape with one pack, the transport
  of a valid method has the realizers of the method, at the pack of any
  denotation of the target (`coe_realAt`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization (motiveType inst0_motiveCod)
open UniverseLevel (LevelOrder)
open Consistency (World)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

section Motives

variable (laws : V.Laws)
include laws

/-- **A motive of identity elimination related to another, applied to related
points and to any two paths, gives types related in the motive's universe**:
an identity type relates every two paths. -/
theorem idMotive_universe {n : Nat} {ξ : World V.reading n} {A x a b f g p q : Tm Head n}
    {w : Head} (hw : V.rules.isUniverse w) {RF : Pack V n}
    (denF : DenS V ξ (motiveType A x w) RF) (hfg : RF.rel f g)
    (hab : ∀ {RA : Pack V n}, DenS V ξ A RA → RA.rel a b) :
    (universeAt V (V.levels.level w) ξ).rel (.app (.app f a) p) (.app (.app g b) q) := by
  obtain ⟨R₁, den₁, h₁⟩ := DenS.pi_app_exists laws denF hfg hab
  rw [inst0_motiveCod] at den₁
  obtain ⟨R₂, den₂, h₂⟩ := DenS.pi_app_exists laws den₁ h₁
    fun denI => DenS.id_rel laws denI p q
  have den₂' : DenS V ξ (.head w) R₂ := den₂
  obtain rfl := DenS.sort_inv laws hw den₂'
  exact @h₂

/-- A motive related to another, applied to related points and to any two
paths, gives a pair of types of one shape with one pack at the level of the
motive's universe. -/
theorem idMotive_shapePair {n : Nat} {ξ : World V.reading n} {A x a b f g p q : Tm Head n}
    {w : Head} (hw : V.rules.isUniverse w) {RF : Pack V n}
    (denF : DenS V ξ (motiveType A x w) RF) (hfg : RF.rel f g)
    (hab : ∀ {RA : Pack V n}, DenS V ξ A RA → RA.rel a b) :
    ∃ Q, ShapePair V (InterpAt V (V.levels.level w)) ξ (.app (.app f a) p)
      (.app (.app g b) q) Q Q := by
  obtain ⟨Q, hl, hr, s⟩ := universeAt.den (idMotive_universe laws hw denF hfg hab)
  exact ⟨Q, hl, hr, rfl, s⟩

/-- **Between two types of one shape with one pack, the transport has the
realizers of its method**, at the pack of any denotation of the target. -/
theorem coe_realAt {coe : DeclName} (transport : CoeRules V coe) {k : L} {n : Nat}
    {ξ : World V.reading n} {X Y d : Tm Head n} {Q : Pack V n}
    (same : ShapePair V (InterpAt V k) ξ X Y Q Q) (hd : Q.Val d) {P : Pack V n}
    (den : DenS V ξ Y P) : P.real (coeApp coe X Y d) = Q.real d := by
  obtain rfl := DenS.deterministic laws den ⟨k, same.right⟩
  exact coe_real laws (InterpAt.facts laws k) transport same hd

end Motives

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
