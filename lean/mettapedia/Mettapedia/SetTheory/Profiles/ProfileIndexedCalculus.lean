import Mettapedia.SetTheory.Profiles.CommonCoreSubstitution

/-!
# Profile-indexed material deductions and their retained declarations

The logical signature is the existing first-order equality/membership
language. A profile authors its primitive rule instances independently of
any model. Substitution closes those instances under actual variable maps.
Declarations retain their origin, and local hypotheses retain their list
positions. Neither an unselected foreign rule nor equality of formulas
identifies distinct declaration occurrences.

Hypothesis substitution acts on the complete natural-deduction tree. Its
quantifier cases weaken the substituted proofs through the variable binder;
its case-analysis cases protect the newly introduced local hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute weakenFormula liftVariables)
open GraphRealizedDeduction (Proof)
open CommonCoreSubstitution

universe u v w

/-- Authored primitive rules over the material signature. Validity is not
part of the rule declaration: concrete interpretations must prove it. -/
structure Profile where
  RuleName : Type u
  Rule : {count : Nat} → Formula count → Type u
  ruleName : {count : Nat} → {body : Formula count} → Rule body → RuleName

inductive Adoption (profile : Profile.{u}) : {count : Nat} → Formula count → Type u where
  | primitive {count : Nat} {body : Formula count} (rule : profile.Rule body) : Adoption profile body
  | substitution {count other : Nat} {body : Formula count}
      (indices : Fin count → Fin other) (previous : Adoption profile body) :
      Adoption profile (substitute indices body)

def Adoption.name {profile : Profile.{u}} {count : Nat} {body : Formula count} :
    Adoption profile body → profile.RuleName
  | .primitive rule => profile.ruleName rule
  | .substitution _ previous => previous.name

structure Declaration (profile : Profile.{u}) (count : Nat) where
  formula : Formula count
  adoption : Adoption profile formula
  origin : Nat

def Declaration.substitute {profile : Profile.{u}} {count other : Nat}
    (indices : Fin count → Fin other) (declaration : Declaration profile count) :
    Declaration profile other where
  formula := ContextualMaterialLogic.substitute indices declaration.formula
  adoption := .substitution indices declaration.adoption
  origin := declaration.origin

def declarationFormulas {profile : Profile.{u}} {count : Nat}
    (declarations : List (Declaration profile count)) : List (Formula count) :=
  declarations.map Declaration.formula

structure Derivation (profile : Profile.{u}) {count : Nat}
    (assumptions : List (Formula count)) (conclusion : Formula count) where
  declarations : List (Declaration profile count)
  proof : Proof (declarationFormulas declarations ++ assumptions) conclusion

/-- Logical proofs keep their actual source tree when no law is adopted. -/
def Derivation.logical {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : Proof assumptions conclusion) : Derivation profile assumptions conclusion :=
  ⟨[], proof⟩

def Derivation.adopt {profile : Profile.{u}} {count : Nat} {body : Formula count}
    (origin : Nat) (adoption : Adoption profile body) : Derivation profile [] body where
  declarations := [⟨body, adoption, origin⟩]
  proof := .hypothesis (assumptions := [body]) 0

theorem declarationFormulas_substitute {profile : Profile.{u}} {count other : Nat}
    (indices : Fin count → Fin other) (declarations : List (Declaration profile count)) :
    declarationFormulas (declarations.map (Declaration.substitute indices)) =
      (declarationFormulas declarations).map (substitute indices) := by
  simp only [declarationFormulas, List.map_map]
  rfl

def Derivation.substitute {profile : Profile.{u}} {count other : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (indices : Fin count → Fin other) (derivation : Derivation profile assumptions conclusion) :
    Derivation profile (assumptions.map (substitute indices)) (substitute indices conclusion) where
  declarations := derivation.declarations.map (Declaration.substitute indices)
  proof := by
    rw [declarationFormulas_substitute, ← List.map_append]
    exact substituteProof indices derivation.proof

/-- Protect a branch's freshly introduced local assumption while replacing
every older occurrence by its chosen proof. -/
def liftHypotheses {count : Nat} {source target : List (Formula count)} (extra : Formula count)
    (replacement : (index : Fin source.length) → Proof target source[index.val]) :
    (index : Fin (extra :: source).length) → Proof (extra :: target) (extra :: source)[index.val] :=
  Fin.cases (Proof.hypothesis (assumptions := extra :: target) 0) (fun index =>
    Proof.weakening (replacement index) Fin.succ (fun _ => rfl))

def weakenHypotheses {count : Nat} {source target : List (Formula count)}
    (replacement : (index : Fin source.length) → Proof target source[index.val]) :
    (index : Fin (source.map weakenFormula).length) →
      Proof (target.map weakenFormula) (source.map weakenFormula)[index.val] := by
  intro index
  let original := originalPosition weakenFormula source index
  have changed := substituteProof Fin.succ (replacement original)
  have weakened : target.map (substitute Fin.succ) = target.map weakenFormula := rfl
  rw [weakened] at changed
  simpa [original, originalPosition, weakenFormula] using changed

/-- Genuine cut: local hypotheses may be replaced by arbitrary proofs,
including proofs containing quantifiers and equality elimination. -/
def substituteHypotheses {count : Nat} {source target : List (Formula count)}
    {conclusion : Formula count} (proof : Proof source conclusion)
    (replacement : (index : Fin source.length) → Proof target source[index.val]) :
    Proof target conclusion :=
  match proof with
  | .hypothesis index => replacement index
  | .weakening previous positions same =>
      substituteHypotheses previous (fun index => same index ▸ replacement (positions index))
  | .bottomElim previous => .bottomElim (substituteHypotheses previous replacement)
  | .bothIntro left right =>
      .bothIntro (substituteHypotheses left replacement) (substituteHypotheses right replacement)
  | .bothLeft previous => .bothLeft (substituteHypotheses previous replacement)
  | .bothRight previous => .bothRight (substituteHypotheses previous replacement)
  | .eitherLeft previous => .eitherLeft (substituteHypotheses previous replacement)
  | .eitherRight previous => .eitherRight (substituteHypotheses previous replacement)
  | .eitherElim previous left right =>
      .eitherElim (substituteHypotheses previous replacement)
        (substituteHypotheses left (liftHypotheses _ replacement))
        (substituteHypotheses right (liftHypotheses _ replacement))
  | .implyIntro previous =>
      .implyIntro (substituteHypotheses previous (liftHypotheses _ replacement))
  | .implyElim previous premise =>
      .implyElim (substituteHypotheses previous replacement) (substituteHypotheses premise replacement)
  | .allIntro previous => .allIntro (substituteHypotheses previous (weakenHypotheses replacement))
  | .allElim previous index => .allElim (substituteHypotheses previous replacement) index
  | .existIntro index previous => .existIntro index (substituteHypotheses previous replacement)
  | .existElim previous branch =>
      .existElim (substituteHypotheses previous replacement)
        (substituteHypotheses branch (liftHypotheses _ (weakenHypotheses replacement)))
  | .equalRefl index => .equalRefl index
  | .equalElim same previous =>
      .equalElim (substituteHypotheses same replacement) (substituteHypotheses previous replacement)

def appendLeft {count : Nat} {source : List (Formula count)} {conclusion : Formula count}
    (extra : List (Formula count)) (proof : Proof source conclusion) :
    Proof (source ++ extra) conclusion :=
  Proof.weakening proof (fun index => ⟨index.val, by simp; omega⟩)
    (fun index => List.getElem_append_left index.isLt)

def appendRight {count : Nat} {source : List (Formula count)} {conclusion : Formula count}
    (extra : List (Formula count)) (proof : Proof source conclusion) :
    Proof (extra ++ source) conclusion :=
  Proof.weakening proof (fun index => ⟨extra.length + index.val, by simp⟩)
    (fun index => by simp)

def appendReplacements {count : Nat} {first second target : List (Formula count)}
    (left : (index : Fin first.length) → Proof target first[index.val])
    (right : (index : Fin second.length) → Proof target second[index.val]) :
    (index : Fin (first ++ second).length) → Proof target (first ++ second)[index.val] := by
  intro index
  by_cases earlier : index.val < first.length
  · simpa only [List.getElem_append_left earlier] using left ⟨index.val, earlier⟩
  · have bound : index.val - first.length < second.length := by
      have total := index.isLt
      simp only [List.length_append] at total
      omega
    simpa only [List.getElem_append_right (Nat.le_of_not_gt earlier)] using
      right ⟨index.val - first.length, bound⟩

/-- Cut the local hypotheses while retaining precisely the adopted law
occurrences. A replacement may use those laws and the new local context. -/
def Derivation.cut {profile : Profile.{u}} {count : Nat}
    {source target : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation profile source conclusion)
    (replacement : (index : Fin source.length) →
      Proof (declarationFormulas derivation.declarations ++ target) source[index.val]) :
    Derivation profile target conclusion where
  declarations := derivation.declarations
  proof := substituteHypotheses derivation.proof (appendReplacements
    (fun index => appendLeft target (Proof.hypothesis index)) replacement)

/-- A profile map is directed. The source rule is explicitly translated to
an adopted target rule; no reverse map or equality of theories is inferred. -/
structure Translation (source : Profile.{u}) (target : Profile.{v}) where
  rule : {count : Nat} → {body : Formula count} → source.Rule body → Adoption target body

def Translation.adoption {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat} {body : Formula count} :
    Adoption source body → Adoption target body
  | .primitive rule => translation.rule rule
  | .substitution indices previous => .substitution indices (translation.adoption previous)

def Translation.declaration {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat}
    (declaration : Declaration source count) : Declaration target count :=
  ⟨declaration.formula, translation.adoption declaration.adoption, declaration.origin⟩

theorem translated_declarationFormulas {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat}
    (declarations : List (Declaration source count)) :
    declarationFormulas (declarations.map translation.declaration) = declarationFormulas declarations := by
  simp only [declarationFormulas, List.map_map]
  rfl

def Translation.derivation {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation source assumptions conclusion) : Derivation target assumptions conclusion where
  declarations := derivation.declarations.map translation.declaration
  proof := by rw [translated_declarationFormulas]; exact derivation.proof

def Translation.identity (profile : Profile.{u}) : Translation profile profile where
  rule := Adoption.primitive

def Translation.comp {first : Profile.{u}} {middle : Profile.{v}} {last : Profile.{w}}
    (earlier : Translation first middle) (later : Translation middle last) : Translation first last where
  rule := fun rule => later.adoption (earlier.rule rule)

theorem identity_adoption {profile : Profile.{u}} {count : Nat} {body : Formula count}
    (adoption : Adoption profile body) :
    (Translation.identity profile).adoption adoption = adoption := by
  induction adoption with
  | primitive => rfl
  | substitution indices previous ih =>
      simp only [Translation.adoption, ih]

theorem composition_adoption {first : Profile.{u}} {middle : Profile.{v}} {last : Profile.{w}}
    (earlier : Translation first middle) (later : Translation middle last)
    {count : Nat} {body : Formula count} (adoption : Adoption first body) :
    (earlier.comp later).adoption adoption = later.adoption (earlier.adoption adoption) := by
  induction adoption with
  | primitive => rfl
  | substitution indices previous ih =>
      simp only [Translation.adoption, ih]

theorem translation_substitution {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count other : Nat}
    (indices : Fin count → Fin other) (declaration : Declaration source count) :
    translation.declaration (declaration.substitute indices) =
      (translation.declaration declaration).substitute indices := rfl

theorem translation_substituted_declarations {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count other : Nat}
    (indices : Fin count → Fin other) (declarations : List (Declaration source count)) :
    (declarations.map (Declaration.substitute indices)).map translation.declaration =
      (declarations.map translation.declaration).map (Declaration.substitute indices) := by
  simp only [List.map_map]
  rfl

theorem translation_origin {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat} (declaration : Declaration source count) :
    (translation.declaration declaration).origin = declaration.origin := rfl

theorem substitution_origin {profile : Profile.{u}} {count other : Nat}
    (indices : Fin count → Fin other) (declaration : Declaration profile count) :
    (declaration.substitute indices).origin = declaration.origin := rfl

theorem substitution_name {profile : Profile.{u}} {count other : Nat}
    (indices : Fin count → Fin other) (declaration : Declaration profile count) :
    (declaration.substitute indices).adoption.name = declaration.adoption.name := rfl

/-- Origins remain a list: repeated declarations and their order are retained. -/
def Derivation.origins {profile : Profile.{u}} {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation profile assumptions conclusion) : List Nat :=
  derivation.declarations.map Declaration.origin

theorem translate_origins {source : Profile.{u}} {target : Profile.{v}}
    (translation : Translation source target) {count : Nat}
    {assumptions : List (Formula count)} {conclusion : Formula count}
    (derivation : Derivation source assumptions conclusion) :
    (translation.derivation derivation).origins = derivation.origins := by
  simp only [Derivation.origins, Translation.derivation, List.map_map]
  rfl

theorem substitute_origins {profile : Profile.{u}} {count other : Nat}
    (indices : Fin count → Fin other) {assumptions : List (Formula count)}
    {conclusion : Formula count} (derivation : Derivation profile assumptions conclusion) :
    (derivation.substitute indices).origins = derivation.origins := by
  simp only [Derivation.origins, Derivation.substitute, List.map_map]
  rfl

theorem duplicate_local_occurrences_distinct {count : Nat} (body : Formula count) :
    (Proof.hypothesis (assumptions := [body, body]) 0) ≠
      Proof.hypothesis (assumptions := [body, body]) 1 := by
  intro same
  have indices := congrArg (fun proof => (CommonCore.freeHypotheses proof).map Fin.val) same
  exact (by decide : ([0] : List Nat) ≠ [1]) indices

end Mettapedia.SetTheory.Profiles.ProfileIndexedCalculus
