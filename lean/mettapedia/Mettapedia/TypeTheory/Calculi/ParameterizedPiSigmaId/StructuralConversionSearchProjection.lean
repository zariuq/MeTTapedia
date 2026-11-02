import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchCertification

/-!
# Exact projection of a bounded conversion candidate

The projected computation returns exactly the term field of the existing
candidate producer, with the same fuel and root-selection guards. It avoids
constructing a recipe only when that field is the complete observation.
The actual producer and its certificate checker retain their recipes.

This is a bounded candidate projection, not a normal-form algorithm or a
typed normalization theorem. Its result can depend on the supplied fuel.
-/
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch
variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
    (searchRoot : {n : Nat} → Tm Head n → Option (RootCode n))

private def rootTarget {n : Nat} (term : Tm Head n) : Option (Tm Head n) := do
  let proposed ← searchRoot term
  let (left,right) ← decodeRoot proposed
  if left = term then some right else none

private def stepTarget {n : Nat} (term : Tm Head n) : Option (Tm Head n) :=
  match term with
  | .app (.lam body) argument => some (inst0 argument body)
  | .fst (.pair first _) => some first
  | .snd (.pair _ second) => some second
  | term => rootTarget decodeRoot searchRoot term

mutual
def termProjection : Nat → {n : Nat} → Tm Head n → Tm Head n
  | 0, _, term => term
  | fuel+1, _, term =>
      let candidate := match term with
        | .var _ | .head _ | .const _ => term
        | .pi domain body => .pi (termProjection fuel domain) (termProjection fuel body)
        | .sigma domain body => .sigma (termProjection fuel domain) (termProjection fuel body)
        | .lam body => .lam (termProjection fuel body)
        | .app function argument => .app (termProjection fuel function) (termProjection fuel argument)
        | .pair first second => .pair (termProjection fuel first) (termProjection fuel second)
        | .fst pair => .fst (termProjection fuel pair)
        | .snd pair => .snd (termProjection fuel pair)
        | .refl subject => .refl (termProjection fuel subject)
        | .id carrier left right => .id (termProjection fuel carrier)
            (termProjection fuel left) (termProjection fuel right)
      finishProjection fuel candidate

def finishProjection : Nat → {n : Nat} → Tm Head n → Tm Head n
  | 0, _, term => term
  | fuel+1, _, term => match stepTarget decodeRoot searchRoot term with
      | none => term
      | some next => termProjection fuel next
end

private theorem root_finish_projection (fuel : Nat)
    (projected : ∀ {n : Nat} (term : Tm Head n),
      (produce decodeRoot searchRoot fuel term).term = termProjection decodeRoot searchRoot fuel term)
    {n : Nat} (term : Tm Head n) (recipe : StructuralConversionCode.Code Head RootCode n) :
    (match (do
        let proposed ← searchRoot term
        let (left,right) ← decodeRoot proposed
        if left = term then some (right,StructuralConversionCode.Code.single (.root proposed)) else none) with
      | none => Candidate.mk term recipe
      | some (next,step) =>
          let rest := produce decodeRoot searchRoot fuel next
          ⟨rest.term,.trans recipe (.trans step rest.recipe)⟩).term =
    (match rootTarget decodeRoot searchRoot term with
      | none => term
      | some next => termProjection decodeRoot searchRoot fuel next) := by
  cases searched : searchRoot term with
  | none => simp [rootTarget,searched]
  | some root =>
      cases decoded : decodeRoot root with
      | none => simp [rootTarget,searched,decoded]
      | some pair =>
          rcases pair with ⟨left,right⟩
          by_cases same : left = term <;>
            simp [rootTarget,searched,decoded,same,projected]

private theorem produce_finish_projection (fuel : Nat) :
    (∀ {n : Nat} (term : Tm Head n),
      (produce decodeRoot searchRoot fuel term).term = termProjection decodeRoot searchRoot fuel term) ∧
    (∀ {n : Nat} (candidate : Candidate Head RootCode n),
      (finish decodeRoot searchRoot fuel candidate).term =
        finishProjection decodeRoot searchRoot fuel candidate.term) := by
  induction fuel with
  | zero => exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ fuel ih =>
      constructor
      · intro n term
        cases term <;> simp only [produce,termProjection,ih.2,ih.1]
      · intro n candidate
        rcases candidate with ⟨term,recipe⟩
        cases term <;> try exact root_finish_projection decodeRoot searchRoot fuel ih.1 _ recipe
        case app function argument =>
          cases function <;> try exact root_finish_projection decodeRoot searchRoot fuel ih.1 _ recipe
          simp only [finish,finishProjection,stepTarget]
          exact ih.1 _
        case fst pair =>
          cases pair <;> try exact root_finish_projection decodeRoot searchRoot fuel ih.1 _ recipe
          simp only [finish,finishProjection,stepTarget]
          exact ih.1 _
        case snd pair =>
          cases pair <;> try exact root_finish_projection decodeRoot searchRoot fuel ih.1 _ recipe
          simp only [finish,finishProjection,stepTarget]
          exact ih.1 _

theorem produce_term (fuel : Nat) {n : Nat} (term : Tm Head n) :
    (produce decodeRoot searchRoot fuel term).term = termProjection decodeRoot searchRoot fuel term :=
  (produce_finish_projection decodeRoot searchRoot fuel).1 term

#print axioms produce_term
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch
