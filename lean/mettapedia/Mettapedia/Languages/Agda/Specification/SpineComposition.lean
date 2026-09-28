import Mettapedia.Languages.Agda.Specification.Renaming

/-!
# Composition of finite spine computations

Application concatenates the pending eliminations in their source order.
Substitution traverses the two parts of a concatenated spine independently.
-/

namespace Mettapedia.Languages.Agda.Specification

def Apply.append {t u v : Term n} {es fs : Spine n}
    (h : Apply t es u) (k : Apply u fs v) : Apply t (es.append fs) v := by
  match h with
  | .nil _ => exact k
  | .var i gs e hs =>
    have hv := k.deterministic (Apply.variableSpine i (gs.append (.cons e hs)) fs)
    rw [hv, Spine.append_assoc]
    exact Apply.variableSpine i gs ((Spine.cons e hs).append fs)
  | .defn f gs e hs =>
    have hv := k.deterministic (Apply.definition f (gs.append (.cons e hs)) fs)
    rw [hv, Spine.append_assoc]
    exact Apply.definition f gs ((Spine.cons e hs).append fs)
  | .con c gs e hs =>
    have hv := k.deterministic (Apply.constructor c (gs.append (.cons e hs)) fs)
    rw [hv, Spine.append_assoc]
    exact Apply.constructor c gs ((Spine.cons e hs).append fs)
  | .lam hi ha => exact .lam hi (ha.append k)

def SubstituteSpine.append {σ : Substitution n m}
    {es fs : Spine n} {es' fs' : Spine m}
    (h : SubstituteSpine σ es es') (k : SubstituteSpine σ fs fs') :
    SubstituteSpine σ (es.append fs) (es'.append fs') := by
  match h with
  | .nil _ => exact k
  | .cons ht he => exact .cons ht (he.append k)

/-- A bare variable substitutes to its image without introducing a binder. -/
def Substitute.bvar (σ : Substitution n m) (i : Fin n) :
    Substitute σ (Term.bvar i) (σ i) :=
  .var (.nil σ) (.nil (σ i))

theorem Substitute.bvar_result {σ : Substitution n m} {i : Fin n} {t : Term m}
    (h : Substitute σ (Term.bvar i) t) : t = σ i :=
  h.deterministic (Substitute.bvar σ i)

end Mettapedia.Languages.Agda.Specification
