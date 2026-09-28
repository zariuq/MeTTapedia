import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.Interp

/-!
# Controls for the interpretation

Positive: β for functions and for both projections of pairs holds as an
equality of ideals, in every environment.

Negative: η does not hold as an equality of ideals. The identity function and
the function sending `p` to `(p.1, p.2)` are equal at every type of pairs
`Σ A B → Σ A B` by the η-law of pairs, but their interpretations differ: the
identity maps the universe to the universe, and the other maps it to the least
element, since a function term carries no domain and its interpretation is its
graph on all inputs. So for this calculus, whose functions carry no domain, a
denotational model can only validate the typed equality up to agreement on
typed elements; it cannot interpret equal terms by equal ideals, as the model
of Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès and Weirich,
*Definitional Inversion, Without Normalisation* (Theorem 2.31), does for
functions that carry their domain.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace InterpControls

open Ideal

/-- A reading with no heads and no constants of interest. -/
def unitReading : Reading Unit where
  head := fun _ => []
  const := fun _ => bot

/-- The identity function. -/
def idFun : Tm Unit 0 := .lam (.var 0)

/-- The η-expansion of the identity at pairs. -/
def etaPairFun : Tm Unit 0 := .lam (.pair (.fst (.var 0)) (.snd (.var 0)))

/-- The empty environment. -/
def emptyEnv : Env 0 := fun i => nomatch i

/-- The observation "maps the universe to the universe". -/
def univToUniv : Tok := .fn .lam [] [.tag .univ] [.tag .univ]

theorem idFun_maps_univ : (interp unitReading idFun emptyEnv).Mem univToUniv := by
  refine (mem_lam_fn (interp_family_monotone unitReading (.var 0) emptyEnv)).2 ?_
  intro t ht
  rw [List.mem_singleton.1 ht]
  exact ent_of_mem List.mem_cons_self

/-- A pair ideal has no tags. -/
theorem pair_no_tag (I J : Ideal) (k : Kind) : ¬ (Ideal.pair I J).Mem (.tag k) := by
  rintro ⟨v, hv, ht⟩
  rw [ent_tag, hasTag_iff] at ht
  rcases hv _ ht with ⟨s, h, -⟩ | ⟨C, s, h, -⟩ <;> cases h

theorem etaPairFun_not_maps_univ :
    ¬ (interp unitReading etaPairFun emptyEnv).Mem univToUniv := by
  intro h
  have := (mem_lam_fn (interp_family_monotone unitReading
    (.pair (.fst (.var 0)) (.snd (.var 0))) emptyEnv)).1 h
  exact pair_no_tag _ _ .univ (this _ List.mem_cons_self)

/-- **Negative control**: η does not hold as an equality of interpretations. -/
theorem eta_not_equal_interp :
    interp unitReading idFun emptyEnv ≠ interp unitReading etaPairFun emptyEnv := by
  intro h
  exact etaPairFun_not_maps_univ (h ▸ idFun_maps_univ)

/-- **Positive control**: β for functions, in every environment. -/
theorem beta_identity (a : Tm Unit 0) :
    interp unitReading (.app idFun a) emptyEnv = interp unitReading a emptyEnv := by
  rw [idFun, interp_beta, interp_inst0]
  rfl

/-- **Positive control**: β for both projections. -/
theorem beta_projections (a b : Tm Unit 0) :
    interp unitReading (.fst (.pair a b)) emptyEnv = interp unitReading a emptyEnv ∧
      interp unitReading (.snd (.pair a b)) emptyEnv = interp unitReading b emptyEnv :=
  ⟨interp_fst_pair _ _ _ _, interp_snd_pair _ _ _ _⟩

end InterpControls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
