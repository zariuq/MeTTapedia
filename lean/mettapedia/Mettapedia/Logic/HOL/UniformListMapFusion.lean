import Mettapedia.Logic.HOL.UniformListInduction
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Uniform map fusion in object HOL

The two function parameters and the list are quantified in the existing HOL
syntax. An explicit proof tree instantiates the existing predicate-quantified
list induction principle; its base and cons obligations use map equations,
object beta and congruence. No semantic list theorem supplies the object proof.

The same proof is reusable at arbitrary typed function and list expressions.
A reversed-composition candidate fits every empty-list sample but is refuted
in the existing standard list model, which validates the complete theory.
This is mathematical theorem use, not a learning or proof-search algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.UniformListMapFusion

open UniformListInduction

variable {Γ Ξ : Ctx BaseSort} {σ τ : Ty BaseSort}

def compose (f g : Expr Γ mapping) : Expr Γ mapping :=
  .lam (.app (weaken f) (.app (weaken g) (.var .vz)))

def fuses (f g : Expr Γ mapping) (xs : Expr Γ sequence) : Formula Symbol Γ :=
  .eq (map f (map g xs)) (map (compose f g) xs)

def fusionPredicate (f g : Expr Γ mapping) : Expr Γ predicate :=
  .lam (fuses (weaken f) (weaken g) (.var .vz))

/-- All three binders belong to the object language. The signature's map
acts on endofunctions of its arbitrary element sort. -/
def mapFusion : Formula Symbol Γ :=
  .all (.all (.all (fuses (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_compose (substitution : Subst Symbol Γ Ξ) (f g : Expr Γ mapping) :
    subst substitution (compose f g) = compose (subst substitution f) (subst substitution g) := by
  simp [compose, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_fuses (substitution : Subst Symbol Γ Ξ)
    (f g : Expr Γ mapping) (xs : Expr Γ sequence) :
    subst substitution (fuses f g xs) =
      fuses (subst substitution f) (subst substitution g) (subst substitution xs) := by
  simp only [fuses, map, subst, subst_compose]

@[simp] theorem weaken_compose (f g : Expr Γ mapping) :
    weaken (σ := τ) (compose f g) = compose (weaken f) (weaken g) := by
  simp [compose, weaken, rename, rename_comp, Rename.lift, Rename.weaken]

@[simp] theorem subst_fusionPredicate (substitution : Subst Symbol Γ Ξ)
    (f g : Expr Γ mapping) :
    subst substitution (fusionPredicate f g) =
      fusionPredicate (subst substitution f) (subst substitution g) := by
  simp [fusionPredicate, subst, subst_fuses, subst_weaken, Subst.lift]

@[simp] theorem weaken_fusionPredicate (f g : Expr Γ mapping) :
    weaken (σ := τ) (fusionPredicate f g) = fusionPredicate (weaken f) (weaken g) := by
  simp [fusionPredicate, fuses, compose, map, weaken, rename,
    rename_comp, Rename.lift, Rename.weaken]

private theorem substitute_weaken (term : Expr Γ σ) (body : Expr Γ τ) :
    subst (Subst.single term) (weaken body) = body := instantiate_weaken term body

private theorem substitute_renamed_weaken (term : Expr Γ σ) (body : Expr Γ τ) :
    subst (Subst.single term) (rename Rename.weaken body) = body := instantiate_weaken term body

@[simp] theorem instantiate_fusionBody (f g : Expr Γ mapping) (xs : Expr Γ sequence) :
    instantiate xs (fuses (weaken f) (weaken g) (.var .vz)) = fuses f g xs := by
  simp only [instantiate, subst_fuses, substitute_weaken, subst, Subst.single]

def compositionBeta (f g : Expr Γ mapping) (x : Expr Γ element)
    (Δ : List (Formula Symbol Γ)) :
    ProofSyntax Symbol Δ (.eq (.app (compose f g) x) (.app f (.app g x))) := by
  simpa only [compose, instantiate, subst, substitute_weaken, Subst.single] using
    (ProofSyntax.beta (Δ := Δ) x (.app (weaken f) (.app (weaken g) (.var .vz))))

private def predicateBeta (f g : Expr Γ mapping) (xs : Expr Γ sequence)
    (Δ : List (Formula Symbol Γ)) :
    ProofSyntax Symbol Δ (.eq (.app (fusionPredicate f g) xs) (fuses f g xs)) := by
  simpa only [fusionPredicate, instantiate_fusionBody] using
    (ProofSyntax.beta (Δ := Δ) xs (fuses (weaken f) (weaken g) (.var .vz)))

private def predicateOfEquation {f g : Expr Γ mapping} {xs : Expr Γ sequence}
    {Δ : List (Formula Symbol Γ)} (proof : ProofSyntax Symbol Δ (fuses f g xs)) :
    ProofSyntax Symbol Δ (.app (fusionPredicate f g) xs) :=
  .impE (.eqPropER (predicateBeta f g xs Δ)) proof

private def equationOfPredicate {f g : Expr Γ mapping} {xs : Expr Γ sequence}
    {Δ : List (Formula Symbol Γ)} (proof : ProofSyntax Symbol Δ (.app (fusionPredicate f g) xs)) :
    ProofSyntax Symbol Δ (fuses f g xs) :=
  .impE (.eqPropEL (predicateBeta f g xs Δ)) proof

def mapNilProof (f : Expr Γ mapping) :
    ProofSyntax Symbol equations (.eq (map f nil) nil) := by
  have ax : ProofSyntax Symbol (equations (Γ := Γ)) mapNil := .hyp ⟨0, by simp [equations]⟩
  simpa [mapNil, instantiate, subst, Subst.single, map, nil] using ProofSyntax.allE f ax

def mapConsProof (f : Expr Γ mapping) (x : Expr Γ element) (xs : Expr Γ sequence) :
    ProofSyntax Symbol equations
      (.eq (map f (cons x xs)) (cons (.app f x) (map f xs))) := by
  have ax : ProofSyntax Symbol (equations (Γ := Γ)) mapCons := .hyp ⟨1, by simp [equations]⟩
  have atFunction : ProofSyntax Symbol equations
      (.all (.all (.eq
        (map (weaken (weaken f)) (cons (.var (.vs .vz)) (.var .vz)))
        (cons (.app (weaken (weaken f)) (.var (.vs .vz)))
          (map (weaken (weaken f)) (.var .vz)))))) := by
    simpa [mapCons, map, cons, instantiate, subst, Subst.single, Subst.lift,
      weaken, Rename.weaken] using ProofSyntax.allE f ax
  have atElement := ProofSyntax.allE x atFunction
  have atSequence := ProofSyntax.allE xs atElement
  simpa [map, cons, instantiate, subst, Subst.single, Subst.lift,
    substitute_weaken, substitute_renamed_weaken] using atSequence

def baseProof (f g : Expr Γ mapping) : ProofSyntax Symbol equations (fuses f g nil) :=
  .eqTrans (.eqAppArg (.app (.const Symbol.map) f) (mapNilProof g))
    (.eqTrans (mapNilProof f) (.eqSymm (mapNilProof (compose f g))))

/-- The induction hypothesis is an actual assumption occurrence. The two map
equations expose a common cons head; object beta aligns the composed head. -/
def stepProof (f g : Expr Γ mapping) (x : Expr Γ element) (xs : Expr Γ sequence) :
    ProofSyntax Symbol (fuses f g xs :: equations) (fuses f g (cons x xs)) := by
  have inner := (mapConsProof g x xs).prepend (fuses f g xs)
  have outer := (mapConsProof f (.app g x) (map g xs)).prepend (fuses f g xs)
  have fused := (mapConsProof (compose f g) x xs).prepend (fuses f g xs)
  have ih : ProofSyntax Symbol (fuses f g xs :: equations) (fuses f g xs) :=
    .hyp ⟨0, by simp⟩
  have head := ProofSyntax.eqApp (map (compose f g) xs)
    (.eqAppArg (.const Symbol.cons) (compositionBeta f g x (fuses f g xs :: equations)))
  exact .eqTrans (.eqAppArg (.app (.const Symbol.map) f) inner)
    (.eqTrans outer (.eqTrans
      (.eqAppArg (.app (.const Symbol.cons) (.app f (.app g x))) ih)
      (.eqTrans (.eqSymm head) (.eqSymm fused))))

private def predicateStep (f g : Expr Γ mapping) :
    ProofSyntax Symbol equations (inductionStep (fusionPredicate f g)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  simp only [weaken_equations, weaken_fusionPredicate]
  apply predicateOfEquation
  let f' : Expr (sequence :: element :: Γ) mapping := weaken (weaken f)
  let g' : Expr (sequence :: element :: Γ) mapping := weaken (weaken g)
  have ih : ProofSyntax Symbol
      (.app (fusionPredicate f' g') (.var .vz) :: equations)
      (fuses f' g' (.var .vz)) := equationOfPredicate (.hyp ⟨0, by simp⟩)
  exact .impE ((ProofSyntax.impI (stepProof f' g' (.var (.vs .vz)) (.var .vz))).prepend _) ih

/-- This is the same predicate-quantified induction sentence as map-length,
now instantiated with fusion and retained as an explicit object proof tree. -/
private def inductionProof (p : Expr Γ predicate) {Δ : List (Formula Symbol Γ)}
    (principle : ProofSyntax Symbol Δ inductionPrinciple)
    (base : ProofSyntax Symbol Δ (.app p nil))
    (step : ProofSyntax Symbol Δ (inductionStep p)) :
    ProofSyntax Symbol Δ (.all (.app (weaken p) (.var .vz))) := by
  have instantiated : ProofSyntax Symbol Δ
      (.imp (.app p nil)
        (.imp (inductionStep p) (.all (.app (weaken p) (.var .vz))))) := by
    simpa [inductionPrinciple, inductionStep, nil, cons, instantiate, subst, Subst.single,
      Subst.lift, weaken, rename, Rename.lift, Rename.weaken] using ProofSyntax.allE p principle
  exact .impE (.impE instantiated base) step

def allListsProof (f g : Expr Γ mapping) :
    ProofSyntax Symbol theory (.all (fuses (weaken f) (weaken g) (.var .vz))) := by
  have predicateAll := inductionProof (fusionPredicate f g)
    (Δ := theory) (.hyp ⟨0, by simp [theory]⟩)
    (predicateOfEquation ((baseProof f g).prepend _))
    ((predicateStep f g).prepend _)
  apply ProofSyntax.allI
  simp only [weaken_theory]
  apply equationOfPredicate
  have weakened : ProofSyntax Symbol (theory (Γ := sequence :: Γ))
      (.all (.app (weaken (weaken (fusionPredicate f g))) (.var .vz))) := by
    have renamed := ProofSyntax.rename (Rename.weaken (σ := sequence)) predicateAll
    change ProofSyntax Symbol (weakenHyps theory) _ at renamed
    simp only [weaken_theory, rename, ExtDerivation.rename_weaken, Rename.lift] at renamed
    simpa only [weaken] using renamed
  have atSequence := ProofSyntax.allE (.var .vz) weakened
  simpa only [instantiate, subst, substitute_weaken, Subst.single,
    weaken_fusionPredicate, subst_fusionPredicate] using atSequence

/-- One universal, Type-valued object-HOL proof, not a family of sample checks. -/
def mapFusionProof : ProofSyntax Symbol (theory (Γ := Γ)) mapFusion := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  simp only [weaken_theory]
  exact allListsProof (.var (.vs .vz)) (.var .vz)

theorem mapFusion_derivation : ExtDerivation Symbol (theory (Γ := Γ)) mapFusion :=
  mapFusionProof.erase

/-- Use the established universal theorem at the actual submitted terms.
The output keeps their source syntax, binders and original theory. -/
def applyFusion (f g : Expr Γ mapping) (xs : Expr Γ sequence) :
    ProofSyntax Symbol theory (fuses f g xs) := by
  have atFunction : ProofSyntax Symbol theory
      (.all (.all (fuses (weaken (weaken f)) (.var (.vs .vz)) (.var .vz)))) := by
    simpa [mapFusion, fuses, compose, map, instantiate, subst, Subst.single, Subst.lift,
      weaken, rename, Rename.weaken, Rename.lift] using ProofSyntax.allE f mapFusionProof
  have atSecond := ProofSyntax.allE g atFunction
  have atSequence := ProofSyntax.allE xs atSecond
  simpa [instantiate, subst_fuses, subst, Subst.single, Subst.lift,
    substitute_weaken, substitute_renamed_weaken] using atSequence

/-- Arbitrary capture-safe instantiation stays in this theorem's family. -/
def substitutedFusion (substitution : Subst Symbol Γ Ξ)
    (f g : Expr Γ mapping) (xs : Expr Γ sequence) :
    ProofSyntax Symbol (theory (Γ := Ξ)) (subst substitution (fuses f g xs)) := by
  rw [subst_fuses]
  exact applyFusion (subst substitution f) (subst substitution g) (subst substitution xs)

/-- A typed surrounding application may use the equation, including when
its result type is itself higher order. This does not identify quoted syntax. -/
def useUnderApplication (consumer : Expr Γ (sequence ⇒ τ))
    (f g : Expr Γ mapping) (xs : Expr Γ sequence) :
    ProofSyntax Symbol theory
      (.eq (.app consumer (map f (map g xs))) (.app consumer (map (compose f g) xs))) :=
  .eqAppArg consumer (applyFusion f g xs)

private theorem standard_valid_of_derivation {φ : ClosedFormula Symbol}
    (proof : ExtDerivation Symbol theory φ) : StandardListModel.model.models φ := by
  exact Soundness.extDerivation_sound proof
    (M := StandardListModel.model)
    (HenkinModel.functionsRespectEqv_of_fullDomains StandardListModel.model
      (HenkinModel.fullDomains_standard StandardListModel.carrier StandardListModel.constant))
    (by intro τ v; nomatch v)
    (by
      intro ψ membership
      refine Eq.mp ?_ (StandardListModel.theory_valid ψ membership)
      unfold HenkinModel.models PreModel.models
      apply congrArg ULift.down
      apply congrArg (PreModel.denote StandardListModel.model.toPreModel ψ)
      funext τ v
      nomatch v)

/-- Semantic validity follows from the constructed object proof, not the
other way around. The model validates every original theory assumption. -/
theorem mapFusion_valid : StandardListModel.model.models mapFusion :=
  standard_valid_of_derivation mapFusion_derivation

namespace Controls

def twoElementProof (f g : Expr Γ mapping) (x y : Expr Γ element) :
    ProofSyntax Symbol theory (fuses f g (cons x (cons y nil))) :=
  applyFusion f g (cons x (cons y nil))

def wrongEquation (f g : Expr Γ mapping) (xs : Expr Γ sequence) : Formula Symbol Γ :=
  .eq (map f (map g xs)) (map (compose g f) xs)

def wrongFusion : Formula Symbol Γ :=
  .all (.all (.all (wrongEquation (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

/-- Empty-list samples cannot distinguish the correct composition order. -/
def wrong_empty_fits (f g : Expr Γ mapping) :
    ProofSyntax Symbol equations (wrongEquation f g nil) :=
  .eqTrans (.eqAppArg (.app (.const Symbol.map) f) (mapNilProof g))
    (.eqTrans (mapNilProof f) (.eqSymm (mapNilProof (compose g f))))

/-- Even all lists and all equal-function pairs fail to expose the wrong
order. In particular, arbitrarily many nonempty samples may fit it. -/
def wrong_diagonal_fits (f : Expr Γ mapping) (xs : Expr Γ sequence) :
    ProofSyntax Symbol theory (wrongEquation f f xs) := applyFusion f f xs

theorem wrongFusion_invalid : ¬ StandardListModel.model.models wrongFusion := by
  intro valid
  have impossible := valid (fun _ => (⟨true⟩ : StandardListModel.LiftedElement)) trivial
    (fun x => (⟨!x.down⟩ : StandardListModel.LiftedElement)) trivial
    (⟨[false]⟩ : StandardListModel.LiftedSequence) trivial
  change (ULift.up [true] : StandardListModel.LiftedSequence) = ULift.up [false] at impossible
  have bad := congrArg ULift.down impossible
  cases bad

/-- A standard-model counterexample excludes an object proof from the full
theory, not merely acceptance by one incomplete proof-search procedure. -/
theorem wrongFusion_not_derivable :
    ¬ ExtDerivation Symbol (theory (Γ := [])) wrongFusion := by
  intro proof
  exact wrongFusion_invalid (standard_valid_of_derivation proof)

end Controls

#print axioms mapFusionProof
#print axioms mapFusion_derivation
#print axioms applyFusion
#print axioms substitutedFusion
#print axioms useUnderApplication
#print axioms mapFusion_valid
#print axioms Controls.wrongFusion_not_derivable

end Mettapedia.Logic.HOL.UniformListMapFusion
