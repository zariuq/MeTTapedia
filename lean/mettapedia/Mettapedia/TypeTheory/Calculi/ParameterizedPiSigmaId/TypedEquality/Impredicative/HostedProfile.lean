import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingInduction

/-!
# Hosted profiles and the facts they publish

A hosted profile is a HOL signature read, under the identity reading, into a
package of proposition codes (`HostedProfile`):

* the reading and its laws, a universe of motives above the universe of proofs,
  and an identity eliminator of the package;
* the defining equations, each realized by a root step of the package;
* the admitted inductive sorts, each read as a simple inductive type of the
  package with its recursor;
* the tracked assumptions of the source.

The facts it publishes (`Published`) are reflexivity and substitution at every
type, induction over every admitted inductive sort, the universal closure of
every defining equation, η at every function type, and each tracked assumption
for which a realizer typed at the decoding of its code is given. Each has a
realization (`Published.realization`), a closed term of the package typed at
the decoding of the code of its formula (`Published.typed`).

**Linking** (`linked_typedO`): a proof from published facts whose conversion
articles stay inside the read terms, compiled against the realizations, is a
closed term of the package at the decoding of the code of its theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

/-- A hosted profile: a HOL signature read into a package of proposition codes
under the identity reading, with its realized defining equations, an identity
eliminator and a universe of motives, its admitted inductive sorts and its
tracked assumptions. -/
structure HostedProfile (Head : Type) (Base : Type u) (Const : HOL.Ty Base → Type v) where
  reading : HOLReading Head Base Const
  laws : reading.Laws
  motives : reading.MotiveUniverse
  identity : reading.IdentityEliminator
  equations : List (HOL.DefiningEquation Const)
  realizes : reading.Realizes equations
  inductives : List (HOLReading.AdmittedInductive Base Const)
  inductiveLaws : ∀ I ∈ inductives, I.Laws reading
  assumptions : List (HOL.Formula Const [])

namespace HostedProfile

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The facts a hosted profile publishes. -/
inductive Published (P : HostedProfile Head Base Const) : HOL.Formula Const [] → Type (max u v)
  | reflexivity (τ : HOL.Ty Base) : Published P (HOL.reflexivityFormula τ)
  | substitution (τ : HOL.Ty Base) : Published P (HOL.substitutionFormula τ)
  | induction {I : HOLReading.AdmittedInductive Base Const} (mem : I ∈ P.inductives) :
      Published P I.inductionFormula
  | definingEquation {equation : HOL.DefiningEquation Const} (mem : equation ∈ P.equations) :
      Published P equation.closedFormula
  | eta (σ τ : HOL.Ty Base) : Published P (HOL.etaFormula σ τ)
  | realized {assumption : HOL.Formula Const []} (mem : assumption ∈ P.assumptions)
      (realizer : Tm Head 0)
      (typed : ∃ code, P.reading.term assumption = some code ∧
        Typed P.reading.rules .nil realizer (P.reading.holdsOf code)) :
      Published P assumption

variable {P : HostedProfile Head Base Const}

/-- The realization of a published fact:
reflexivity by `λx. refl x`, substitution by the identity eliminator at the
code motive, induction by the recursor at the code motive, a defining equation
by `λx⃗. refl l`, η by `λf. refl f`, and an assumption by its given realizer. -/
def Published.realization : {fact : HOL.Formula Const []} → Published P fact → Tm Head 0
  | _, .reflexivity _ => .lam (.refl (.var 0))
  | _, .substitution τ => P.reading.substRealization P.identity.name τ
  | _, @Published.induction _ _ _ _ I _ => I.realization P.reading
  | _, @Published.definingEquation _ _ _ _ equation _ => P.reading.equationRealization equation
  | _, .eta _ _ => .lam (.refl (.var 0))
  | _, .realized _ realizer _ => realizer

/-- **Every published fact is realized.** Its formula is read, and its
realization is a closed term of the package at the decoding of its code. -/
theorem Published.typed : {fact : HOL.Formula Const []} → (p : Published P fact) →
    ∃ code, P.reading.term fact = some code ∧
      Typed P.reading.rules .nil p.realization (P.reading.holdsOf code)
  | _, .reflexivity τ => ⟨_, P.reading.term_reflexivityFormula τ, P.laws.refl_typed τ⟩
  | _, .substitution τ => ⟨_, P.reading.term_substitutionFormula τ,
      P.laws.substRealization_typed P.motives P.identity τ⟩
  | _, @Published.induction _ _ _ _ I mem => ⟨_, P.reading.term_inductionFormula I (P.inductiveLaws I mem),
      HOLReading.AdmittedInductive.realization_typed P.laws P.motives (P.inductiveLaws I mem)⟩
  | _, .definingEquation mem => P.laws.equationRealization_typed P.realizes mem
  | _, .eta σ τ => ⟨_, P.reading.term_etaFormula σ τ, P.laws.etaRealization_typed σ τ⟩
  | _, .realized _ _ typed => typed

theorem subst_elim0 (t : Tm Head 0) : Presentation.subst (fun i => Fin.elim0 i : Sub Head 0 0) t = t := by
  have same : (fun i => Fin.elim0 i : Sub Head 0 0) = ids := funext fun i => Fin.elim0 i
  rw [same, subst_ids]

/-- **Linking.** A proof from published facts whose conversion articles stay
inside the read terms, compiled against the realizations, is a closed term of
the package at the decoding of the code of its theorem. -/
theorem linked_typedO (P : HostedProfile Head Base Const) {assumptions : List (HOL.Formula Const [])}
    {statement : HOL.Formula Const []}
    {proof : HOL.ProofSyntaxModulo P.equations assumptions statement}
    (articles : P.reading.ArticlesRead P.equations proof)
    (published : ∀ i : Fin assumptions.length, Published P (assumptions.get i)) {term : Tm Head 0}
    (compiled : P.reading.compile proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    ∃ code, P.reading.term statement = some code ∧
      Typed P.reading.rules .nil term (P.reading.holdsOf code) := by
  obtain ⟨code, hcode, typed⟩ := P.laws.compile_typed (target := .nil) P.realizes articles
    (fun i => Fin.elim0 i)
    (fun i => by
      obtain ⟨c, hc, t⟩ := (published i).typed
      refine ⟨c, hc, ?_⟩
      convert t using 2
      exact subst_elim0 c)
    compiled
  refine ⟨code, hcode, ?_⟩
  convert typed using 2
  exact (subst_elim0 code).symm

/-- Linking under a reading that interprets every constant: every proof from
published facts compiles, and whenever it compiles its link is typed. -/
theorem linked_typedO_of_total (P : HostedProfile Head Base Const) (total : P.reading.Total)
    {assumptions : List (HOL.Formula Const [])} {statement : HOL.Formula Const []}
    (proof : HOL.ProofSyntaxModulo P.equations assumptions statement)
    (published : ∀ i : Fin assumptions.length, Published P (assumptions.get i)) {term : Tm Head 0}
    (compiled : P.reading.compile proof (fun i => Fin.elim0 i)
      (fun i => (published i).realization) = some term) :
    ∃ code, P.reading.term statement = some code ∧
      Typed P.reading.rules .nil term (P.reading.holdsOf code) :=
  P.linked_typedO (HOLReading.ArticlesRead.of_total total proof) published compiled

end HostedProfile

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
