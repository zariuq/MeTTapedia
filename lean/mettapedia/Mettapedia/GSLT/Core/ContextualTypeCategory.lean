import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# The category of types over a context

For a category with families `C` and a context `Γ`, types over `Γ` form a
category.  A morphism `A ⟶ B` is represented here by a substitution from the
display context `Γ.A` to `Γ.B` which lies over `Γ`.

This display-map presentation makes identities and composition inherit their
laws directly from context substitution.  Context comprehension also gives
the equivalent term presentation: an arrow `A ⟶ B` is exactly a term of
`B` in context `Γ.A`.  These are the categories in which the substitution
comparison isomorphisms of pseudo CwF morphisms live.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-- A type over the fixed context `Γ`, bundled as an object. -/
@[ext]
structure TypeOver (C : Cwf.{u, v, w, w'}) (Γ : C.Ctx) where
  val : C.Ty Γ

namespace TypeOver

/-- A display-map morphism over `Γ`. -/
structure Hom {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    (A B : TypeOver C Γ) where
  substitution : C.Sub (C.ext Γ A.val) (C.ext Γ B.val)
  over : C.compS (C.wk B.val) substitution = C.wk A.val

/-- Display-map morphisms are determined by their underlying substitution. -/
@[ext]
theorem Hom.ext {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} {left right : Hom A B}
    (substitutionEq : left.substitution = right.substitution) :
    left = right := by
  cases left
  cases right
  cases substitutionEq
  rfl

/-- Types over one context and display maps over that context form a
category. -/
instance {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx} :
    Category.{v} (TypeOver C Γ) where
  Hom := Hom
  id A :=
    { substitution := C.idS (C.ext Γ A.val)
      over := C.comp_id (C.wk A.val) }
  comp left right :=
    { substitution := C.compS right.substitution left.substitution
      over := by
        calc
          C.compS (C.wk _) (C.compS right.substitution left.substitution) =
              C.compS (C.compS (C.wk _) right.substitution)
                left.substitution :=
            (C.comp_assoc (C.wk _) right.substitution
              left.substitution).symm
          _ = C.compS (C.wk _) left.substitution := by
            rw [right.over]
          _ = C.wk _ := left.over }
  id_comp morphism := Hom.ext (C.comp_id morphism.substitution)
  comp_id morphism := Hom.ext (C.id_comp morphism.substitution)
  assoc first second third :=
    Hom.ext (C.comp_assoc third.substitution second.substitution
      first.substitution).symm

/-- Two substitutions into a display context are equal when their base
projections agree and their readings of the generic variable agree.  The
heterogeneous term equality avoids choosing a cast before the base equality
is known. -/
theorem substitution_ext {C : Cwf.{u, v, w, w'}}
    {Γ Θ : C.Ctx} {A : C.Ty Γ}
    {left right : C.Sub Θ (C.ext Γ A)}
    (baseEq : C.compS (C.wk A) left = C.compS (C.wk A) right)
    (termEq : HEq (C.tmSub (C.vz A) left) (C.tmSub (C.vz A) right)) :
    left = right := by
  let DisplayData := Σ base : C.Sub Θ Γ, C.Tm Θ (C.tySub A base)
  let etaTerm (substitution : C.Sub Θ (C.ext Γ A)) :
      C.Tm Θ (C.tySub A (C.compS (C.wk A) substitution)) :=
    cast (by rw [← C.tySub_comp])
      (C.tmSub (C.vz A) substitution)
  have etaTermsAgree : HEq (etaTerm left) (etaTerm right) := by
    exact (cast_heq _ _).trans (termEq.trans (cast_heq _ _).symm)
  have dataAgree :
      (⟨C.compS (C.wk A) left, etaTerm left⟩ : DisplayData) =
        ⟨C.compS (C.wk A) right, etaTerm right⟩ :=
    Sigma.ext baseEq etaTermsAgree
  have pairAgree := congrArg
    (fun data : DisplayData => C.pair data.1 A data.2) dataAgree
  exact (C.pair_eta A left).symm.trans
    (pairAgree.trans (C.pair_eta A right))

/-- Turn a term of `B` in display context `Γ.A` into the corresponding
display map `A ⟶ B`. -/
def ofTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ}
    (term : C.Tm (C.ext Γ A.val) (C.tySub B.val (C.wk A.val))) :
    A ⟶ B where
  substitution := C.pair (C.wk A.val) B.val term
  over := C.wk_pair (C.wk A.val) B.val term

/-- Term substitution respects heterogeneous equality of its input terms. -/
theorem tmSub_heq {C : Cwf.{u, v, w, w'}} {Γ Δ : C.Ctx}
    {A B : C.Ty Δ} {left : C.Tm Δ A} {right : C.Tm Δ B}
    (typesEqual : A = B) (termsEqual : HEq left right)
    (substitution : C.Sub Γ Δ) :
    HEq (C.tmSub left substitution) (C.tmSub right substitution) := by
  cases typesEqual
  have termsPropositionallyEqual : left = right := eq_of_heq termsEqual
  cases termsPropositionallyEqual
  rfl

/-- The term-substitution composition law without selecting the cast on its
right-hand side. -/
theorem tmSub_comp_heq {C : Cwf.{u, v, w, w'}} {Γ Δ Θ : C.Ctx}
    {A : C.Ty Θ} (term : C.Tm Θ A) (first : C.Sub Δ Θ)
    (second : C.Sub Γ Δ) :
    HEq (C.tmSub term (C.compS first second))
      (C.tmSub (C.tmSub term first) second) :=
  (heq_of_eq (C.tmSub_comp term first second)).trans (cast_heq _ _)

/-- Reading the generic variable along the display map constructed from a
term recovers that term, before selecting a cast convention. -/
theorem vz_ofTerm_heq {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ}
    (term : C.Tm (C.ext Γ A.val) (C.tySub B.val (C.wk A.val))) :
    HEq (C.tmSub (C.vz B.val) (ofTerm term).substitution) term :=
  (heq_of_eq (C.vz_pair (C.wk A.val) B.val term)).trans
    (cast_heq _ _)

/-- Read the generic variable along a display map to recover its term
presentation. -/
def toTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (morphism : A ⟶ B) :
    C.Tm (C.ext Γ A.val) (C.tySub B.val (C.wk A.val)) :=
  cast (by rw [← C.tySub_comp, morphism.over])
    (C.tmSub (C.vz B.val) morphism.substitution)

/-- The term presentation is the raw reading of the target generic variable,
before choosing the cast induced by the display-map equation. -/
theorem toTerm_raw_heq {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (morphism : A ⟶ B) :
    HEq (toTerm morphism)
      (C.tmSub (C.vz B.val) morphism.substitution) :=
  cast_heq _ _

/-- The term obtained from its comprehension display map is the original
term. -/
theorem toTerm_ofTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ}
    (term : C.Tm (C.ext Γ A.val) (C.tySub B.val (C.wk A.val))) :
    toTerm (ofTerm term) = term := by
  simp only [toTerm, ofTerm]
  rw [C.vz_pair]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Every display map is reconstructed by pairing its projection with the
term read from its generic variable. -/
theorem ofTerm_toTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (morphism : A ⟶ B) :
    ofTerm (toTerm morphism) = morphism := by
  apply Hom.ext
  let sigmaZero : C.Sub (C.ext Γ A.val) Γ :=
    C.compS (C.wk B.val) morphism.substitution
  let rawTerm := C.tmSub (C.vz B.val) morphism.substitution
  let canonicalTerm :
      C.Tm (C.ext Γ A.val) (C.tySub B.val sigmaZero) :=
    cast (by rw [← C.tySub_comp]) rawTerm
  let DisplayData := Σ substitution : C.Sub (C.ext Γ A.val) Γ,
    C.Tm (C.ext Γ A.val) (C.tySub B.val substitution)
  have termAgreement : HEq (toTerm morphism) canonicalTerm := by
    dsimp only [toTerm, canonicalTerm, rawTerm]
    exact (cast_heq _ _).trans (cast_heq _ _).symm
  have dataAgreement :
      (⟨C.wk A.val, toTerm morphism⟩ : DisplayData) =
        ⟨sigmaZero, canonicalTerm⟩ :=
    Sigma.ext morphism.over.symm termAgreement
  have pairAgreement := congrArg
    (fun data : DisplayData => C.pair data.1 B.val data.2) dataAgreement
  exact pairAgreement.trans (C.pair_eta B.val morphism.substitution)

/-- Context comprehension identifies display maps with terms in the extended
context. -/
def homEquivTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    (A B : TypeOver C Γ) :
    (A ⟶ B) ≃ C.Tm (C.ext Γ A.val) (C.tySub B.val (C.wk A.val)) where
  toFun := toTerm
  invFun := ofTerm
  left_inv := ofTerm_toTerm
  right_inv := toTerm_ofTerm

/-- Apply a type-over-context arrow to a term at its source.  Categorically,
this substitutes the argument section into the term representing the arrow. -/
def transportTerm {C : Cwf.{u, v, w, w'}} {Γ : C.Ctx}
    {A B : TypeOver C Γ} (morphism : A ⟶ B)
    (term : C.Tm Γ A.val) : C.Tm Γ B.val :=
  cast (by rw [← C.tySub_comp, C.wk_pair, C.tySub_id])
    (C.tmSub (toTerm morphism)
      (C.pair (C.idS Γ) A.val (cast (by rw [C.tySub_id]) term)))

/-! ## Positive and negative controls -/

/-- A Boolean type in the set-families CwF over the one-point context. -/
def unitBoolType : TypeOver (familiesCwf.{0}) PUnit where
  val := fun _ => Bool

/-- A nontrivial display-map endomorphism induced by Boolean negation. -/
def boolNegationDisplay : unitBoolType ⟶ unitBoolType :=
  ofTerm (fun point => !point.2)

/-- Positive: decoding the negation display map recovers its defining term. -/
theorem boolNegationDisplay_toTerm :
    toTerm boolNegationDisplay = (fun point => !point.2) :=
  toTerm_ofTerm _

/-- Applying the Boolean display isomorphism to `true` computes to `false`. -/
theorem boolNegationDisplay_transports_true :
    transportTerm boolNegationDisplay (fun _ => true) =
      (fun _ => false) := by
  funext point
  cases point
  change transportTerm
    (ofTerm (A := unitBoolType) (B := unitBoolType)
      (fun point => !point.2))
    (fun _ : PUnit => true) PUnit.unit = false
  simp only [transportTerm]
  rw [toTerm_ofTerm]
  rfl

/-- Negative: the category of types over a context is not made discrete by
the display-map construction.  Boolean negation is not the identity arrow. -/
theorem boolNegationDisplay_ne_identity :
    boolNegationDisplay ≠ 𝟙 unitBoolType := by
  intro equalArrows
  have equalSubstitutions := congrArg Hom.substitution equalArrows
  have atTrue := congrFun equalSubstitutions
    (⟨PUnit.unit, true⟩ : Σ _ : PUnit, Bool)
  have valuesEqual := congrArg (fun point => point.2) atTrue
  change false = true at valuesEqual
  cases valuesEqual

/-- Boolean negation is a genuine non-identity isomorphism in the category of
types over the one-point context. -/
def boolNegationIso : unitBoolType ≅ unitBoolType where
  hom := boolNegationDisplay
  inv := boolNegationDisplay
  hom_inv_id := by
    apply Hom.ext
    funext point
    rcases point with ⟨unitValue, value⟩
    cases unitValue
    cases value <;> rfl
  inv_hom_id := by
    apply Hom.ext
    funext point
    rcases point with ⟨unitValue, value⟩
    cases unitValue
    cases value <;> rfl

#print axioms TypeOver.Hom.ext
#print axioms TypeOver.instCategory
#print axioms TypeOver.substitution_ext
#print axioms TypeOver.tmSub_heq
#print axioms TypeOver.tmSub_comp_heq
#print axioms TypeOver.vz_ofTerm_heq
#print axioms TypeOver.toTerm_raw_heq
#print axioms TypeOver.toTerm_ofTerm
#print axioms TypeOver.ofTerm_toTerm
#print axioms TypeOver.homEquivTerm
#print axioms TypeOver.transportTerm
#print axioms TypeOver.boolNegationDisplay_toTerm
#print axioms TypeOver.boolNegationDisplay_transports_true
#print axioms TypeOver.boolNegationDisplay_ne_identity
#print axioms TypeOver.boolNegationIso

end TypeOver

end Mettapedia.GSLT.Core.ContextualLadder
