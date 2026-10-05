import Mathlib.SetTheory.ZFC.Basic
import Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyCoherence

/-!
# Higher-order set operations and dependent predicate families

The carrier is Mathlib's extensional `ZFSet`, not a finite set fixture or an
abstract structure assuming the interpretation laws. Membership, separation,
replacement, union and powerset are interpreted by their actual set operations
in one full-domain Henkin model. Higher-order set induction is validated by
well-founded membership.

Bounded HOL predicates decode as the elements of an actual separated set.
This comparison preserves the underlying set element, commutes with HOL
substitution, and takes HOL implication proofs to inclusions of these sets.

This constructs the set-operation and foundation part needed by HOTG hosting.
It does not construct `UnivOf`, a Grothendieck universe closure operator, or
the native dependent proof translation. In particular, a full-domain HOL
model on `ZFSet` is not by itself a model of the complete HOTG preamble.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation

open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

abbrev set : Ty Unit := .base ()
abbrev predicate : Ty Unit := set ⇒ .prop
abbrev mapping : Ty Unit := set ⇒ set

/-- Typed mathematical constants; logical connectives remain HOL syntax. -/
inductive Symbol : Ty Unit → Type where
  | member : Symbol (set ⇒ set ⇒ .prop)
  | empty : Symbol set
  | union : Symbol mapping
  | power : Symbol mapping
  | separate : Symbol (set ⇒ predicate ⇒ set)
  | replace : Symbol (set ⇒ mapping ⇒ set)

abbrev Expr (Γ : Ctx Unit) (A : Ty Unit) := Term Symbol Γ A

noncomputable def replacement (bound : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    ZFSet.{u} := by
  letI : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun xs : Fin 1 → ZFSet.{u} => f (xs 0))
  exact ZFSet.image f bound

theorem mem_replacement {bound value : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    value ∈ replacement bound f ↔ ∃ x ∈ bound, f x = value := by
  unfold replacement
  let : ZFSet.Definable₁ f :=
    Classical.allZFSetDefinable (fun xs : Fin 1 → ZFSet.{u} => f (xs 0))
  exact ZFSet.mem_image

abbrev carrier (_ : Unit) : Type (u + 1) := ZFSet.{u}

noncomputable def denoteSymbol :
    {A : Ty Unit} → Symbol A → Ty.denote.{0, u + 1} carrier.{u} A
  | _, .member => fun (x a : ZFSet.{u}) => .up (x ∈ a)
  | _, .empty => (∅ : ZFSet.{u})
  | _, .union => ZFSet.sUnion
  | _, .power => ZFSet.powerset
  | _, .separate => fun a p => ZFSet.sep (fun x => (p x).down) a
  | _, .replace => replacement

/-- An independently constructed standard HOL model with actual sets. -/
noncomputable def model : HenkinModel.{0, 0, u + 1} Unit Symbol :=
  HenkinModel.standard carrier denoteSymbol

theorem fullDomains : model.{u}.FullDomains :=
  HenkinModel.fullDomains_standard carrier denoteSymbol

theorem functionsRespectEqv : model.{u}.FunctionsRespectEqv :=
  model.functionsRespectEqv_of_fullDomains fullDomains

noncomputable def inhabitedDomains : model.{u}.InhabitedDomains :=
  model.inhabitedDomains_of_fullDomains fullDomains (fun _ => (∅ : ZFSet.{u}))

/-- Choice is supplied by the ambient classical model, not by an added
Lean axiom or an unexplained checker acceptance. -/
noncomputable def hilbertChoice : model.{u}.HilbertChoice :=
  HenkinModel.HilbertChoice.ofFullInhabitedDomains fullDomains inhabitedDomains

def member {Γ : Ctx Unit} (x a : Expr Γ set) : Formula Symbol Γ :=
  .app (.app (.const .member) x) a

def separate {Γ : Ctx Unit} (a : Expr Γ set) (p : Expr Γ predicate) : Expr Γ set :=
  .app (.app (.const .separate) a) p

def replace {Γ : Ctx Unit} (a : Expr Γ set) (f : Expr Γ mapping) : Expr Γ set :=
  .app (.app (.const .replace) a) f

def iffFormula {Γ : Ctx Unit} (φ ψ : Formula Symbol Γ) : Formula Symbol Γ :=
  .and (.imp φ ψ) (.imp ψ φ)

/-- Extensionality is about set membership, not identity of proof routes. -/
def extensionality : ClosedFormula Symbol :=
  .all (.all (.imp
    (.all (iffFormula
      (member (.var .vz) (.var (.vs (.vs .vz))))
      (member (.var .vz) (.var (.vs .vz)))))
    (.eq (.var (.vs .vz)) (.var .vz))))

def emptyLaw : ClosedFormula Symbol :=
  .all (.not (member (.var .vz) (.const .empty)))

def unionLaw : ClosedFormula Symbol :=
  .all (.all (iffFormula
    (member (.var .vz) (.app (.const .union) (.var (.vs .vz))))
    (.ex (.and (member (.var .vz) (.var (.vs (.vs .vz))))
      (member (.var (.vs .vz)) (.var .vz))))))

def powerLaw : ClosedFormula Symbol :=
  .all (.all (iffFormula
    (member (.var .vz) (.app (.const .power) (.var (.vs .vz))))
    (.all (.imp (member (.var .vz) (.var (.vs .vz)))
      (member (.var .vz) (.var (.vs (.vs .vz))))))))

def separationLaw : ClosedFormula Symbol :=
  .all (.all (.all (iffFormula
    (member (.var .vz) (separate (.var (.vs (.vs .vz))) (.var (.vs .vz))))
    (.and (member (.var .vz) (.var (.vs (.vs .vz))))
      (.app (.var (.vs .vz)) (.var .vz))))))

def replacementLaw : ClosedFormula Symbol :=
  .all (.all (.all (iffFormula
    (member (.var .vz) (replace (.var (.vs (.vs .vz))) (.var (.vs .vz))))
    (.ex (.and (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
      (.eq (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))))))

/-- The quantifier ranges over every predicate, not a list of instances. -/
def setInduction : ClosedFormula Symbol :=
  .all (.imp
    (.all (.imp
      (.all (.imp (member (.var .vz) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))
      (.app (.var (.vs .vz)) (.var .vz))))
    (.all (.app (.var (.vs .vz)) (.var .vz))))

theorem extensionality_valid : model.{u}.models extensionality := by
  intro a _ b _ h
  exact ZFSet.ext (fun x => ⟨(h x trivial).1, (h x trivial).2⟩)

theorem emptyLaw_valid : model.{u}.models emptyLaw := by
  intro x _
  exact ZFSet.notMem_empty x

theorem unionLaw_valid : model.{u}.models unionLaw := by
  intro a _ x _
  constructor
  · intro h
    obtain ⟨y, hya, hxy⟩ := ZFSet.mem_sUnion.mp h
    exact ⟨y, trivial, hya, hxy⟩
  · rintro ⟨y, _, hya, hxy⟩
    exact ZFSet.mem_sUnion.mpr ⟨y, hya, hxy⟩

theorem powerLaw_valid : model.{u}.models powerLaw := by
  intro a _ b _
  constructor
  · intro h x _ hx
    exact ZFSet.mem_powerset.mp h hx
  · intro h
    exact ZFSet.mem_powerset.mpr (fun _ hx => h _ trivial hx)

theorem separationLaw_valid : model.{u}.models separationLaw := by
  intro a _ p _ x _
  change ZFSet.{u} at a x
  change ZFSet.{u} → ULift.{u + 1} Prop at p
  change (x ∈ ZFSet.sep (fun y => (p y).down) a →
      (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∧ (p x).down) ∧
    ((x : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∧ (p x).down →
      x ∈ ZFSet.sep (fun y => (p y).down) a)
  exact ⟨(ZFSet.mem_sep (p := fun y => (p y).down)).mp,
    (ZFSet.mem_sep (p := fun y => (p y).down)).mpr⟩

theorem replacementLaw_valid : model.{u}.models replacementLaw := by
  intro a _ f _ y _
  constructor
  · intro h
    obtain ⟨x, hxa, hxy⟩ := mem_replacement.mp h
    exact ⟨x, trivial, hxa, hxy⟩
  · rintro ⟨x, _, hxa, hxy⟩
    exact mem_replacement.mpr ⟨x, hxa, hxy⟩

theorem setInduction_valid : model.{u}.models setInduction := by
  intro p _ step x _
  exact ZFSet.inductionOn x (fun a ih => step a trivial
    (fun b _ hba => ih b hba))

/-! ## Actual separation decodes dependent refinement -/

variable {Γ Δ : Ctx Unit}

/-- The bounded predicate retains both its set bound and its HOL property. -/
def bounded (bound : Expr Γ set) (φ : Formula Symbol (set :: Γ)) :
    Formula Symbol (set :: Γ) :=
  .and (member (.var .vz) (weaken bound)) φ

/-- An actual set, formed by separation using the denotation of an arbitrary
HOL formula. The predicate may itself quantify over functions or predicates. -/
noncomputable def predicateSet (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (valuation : AdmissibleContext model.{u} Γ) :
    ZFSet.{u} :=
  ZFSet.sep (fun x => (model.denote φ (model.extend (σ := set) valuation.1 x)).down)
    (model.denote bound valuation.1)

/-- The authored higher-order separation expression denotes this exact set. -/
theorem predicateSet_denote (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (valuation : AdmissibleContext model.{u} Γ) :
    model.denote (separate bound (.lam φ)) valuation.1 =
      predicateSet bound φ valuation := rfl

theorem mem_predicateSet (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (valuation : AdmissibleContext model.{u} Γ)
    (x : ZFSet.{u}) :
    x ∈ predicateSet bound φ valuation ↔
      (model.denote (bounded bound φ) (model.extend (σ := set) valuation.1 x)).down := by
  change (x ∈ ZFSet.sep _ _) ↔
    (x ∈ (show ZFSet.{u} from model.denote (weaken bound)
      (model.extend (σ := set) valuation.1 x)) ∧ _)
  erw [ZFSet.mem_sep, Soundness.denote_weaken]

/-- The dependent refinement and the elements of the separated set contain
the same witnesses. Neither direction chooses a new representative. -/
noncomputable def refinementSetEquiv (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (valuation : AdmissibleContext model.{u} Γ) :
    refinementFamily model (bounded bound φ) valuation ≃
      { x : ZFSet.{u} // x ∈ predicateSet bound φ valuation } where
  toFun point := ⟨point.1.1, (mem_predicateSet bound φ valuation point.1.1).mpr
    point.2.down.down⟩
  invFun point := ⟨⟨point.1, trivial⟩, ⟨⟨
    (mem_predicateSet bound φ valuation point.1).mp point.2⟩⟩⟩
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

theorem refinementSetEquiv_preserves_value (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (valuation : AdmissibleContext model.{u} Γ)
    (point : refinementFamily model (bounded bound φ) valuation) :
    (refinementSetEquiv bound φ valuation point).1 = point.1.1 := rfl

/-- The set denoted by a predicate is natural under actual simultaneous
substitution, including non-ground predicates and parameters. -/
theorem predicateSet_substitution (bound : Expr Γ set)
    (φ : Formula Symbol (set :: Γ)) (θ : Subst Symbol Γ Δ)
    (valuation : AdmissibleContext model.{u} Δ) :
    predicateSet (HOL.subst θ bound) (HOL.subst (Subst.lift θ) φ) valuation =
      predicateSet bound φ (interpretSubstitution model θ valuation) := by
  apply ZFSet.ext
  intro x
  unfold predicateSet
  erw [ZFSet.mem_sep, ZFSet.mem_sep, Soundness.denote_subst,
    Soundness.denote_subst, Soundness.substVal_lift]
  rfl

/-- A retained HOL implication restricts to the same bound in the object
proof language; the bound is not an extra semantic assumption. -/
def boundedProof (bound : Expr Γ set)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (set :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ))) :
    ProofSyntax Symbol hypotheses (.all (.imp (bounded bound φ) (bounded bound ψ))) :=
  .allI (.impI (.andI
    (.andEL (.hyp ⟨0, by simp⟩))
    (.impE ((HenkinPredicateFamilyCoherence.specializeBound proof).prepend _)
      (.andER (.hyp ⟨0, by simp⟩)))))

/-- The interpreted HOL proof induces actual inclusion of separated sets. -/
theorem predicateSet_subset_of_proof (bound : Expr Γ set)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (set :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext model.{u} hypotheses) :
    predicateSet bound φ valuation.1 ⊆ predicateSet bound ψ valuation.1 := by
  intro x memberSource
  let source := (refinementSetEquiv bound φ valuation.1).symm ⟨x, memberSource⟩
  let target := refinementMapOfProof model functionsRespectEqv
    (boundedProof bound proof) valuation source
  exact (refinementSetEquiv bound ψ valuation.1 target).2

/-- A set-element map obtained from the actual HOL proof interpretation. -/
noncomputable def setMapOfProof (bound : Expr Γ set)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (set :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext model.{u} hypotheses) :
    { x : ZFSet.{u} // x ∈ predicateSet bound φ valuation.1 } →
      { x : ZFSet.{u} // x ∈ predicateSet bound ψ valuation.1 } :=
  fun point => ⟨point.1, predicateSet_subset_of_proof bound proof valuation point.2⟩

/-- The refinement interpretation and extensional set inclusion agree on
actual witnesses, not merely on whether their domains are inhabited. -/
theorem proof_refinement_set_square (bound : Expr Γ set)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (set :: Γ)}
    (proof : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext model.{u} hypotheses)
    (point : refinementFamily model (bounded bound φ) valuation.1) :
    refinementSetEquiv bound ψ valuation.1
        (refinementMapOfProof model functionsRespectEqv (boundedProof bound proof)
          valuation point) =
      setMapOfProof bound proof valuation (refinementSetEquiv bound φ valuation.1 point) := by
  apply Subtype.ext
  rfl

/-- Both directions of a proved equivalence give equality of the actual
separated sets, without equating the retained proof trees. -/
theorem predicateSet_eq_of_proofs (bound : Expr Γ set)
    {hypotheses : List (Formula Symbol Γ)} {φ ψ : Formula Symbol (set :: Γ)}
    (forward : ProofSyntax Symbol hypotheses (.all (.imp φ ψ)))
    (backward : ProofSyntax Symbol hypotheses (.all (.imp ψ φ)))
    (valuation : SatisfiedContext model.{u} hypotheses) :
    predicateSet bound φ valuation.1 = predicateSet bound ψ valuation.1 :=
  ZFSet.ext fun _ => ⟨fun h => predicateSet_subset_of_proof bound forward valuation h,
    fun h => predicateSet_subset_of_proof bound backward valuation h⟩

/-! ## One validated theory and its boundary controls -/

/-- The exact closed mathematical assumptions validated above. -/
def theory : List (ClosedFormula Symbol) :=
  [extensionality, emptyLaw, unionLaw, powerLaw, separationLaw,
    replacementLaw, setInduction]

theorem theory_valid (φ : ClosedFormula Symbol) (h : φ ∈ theory) :
    model.{u}.models φ := by
  simp only [theory, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact extensionality_valid
  · exact emptyLaw_valid
  · exact unionLaw_valid
  · exact powerLaw_valid
  · exact separationLaw_valid
  · exact replacementLaw_valid
  · exact setInduction_valid

noncomputable def emptyContext : AdmissibleContext model.{u} [] :=
  ⟨(fun v => nomatch v), by intro A v; exact nomatch v⟩

/-- The same model supplies the original hypotheses of any HOL proof over
this set theory; the family interpretation does not assume their validity. -/
noncomputable def satisfiedTheory : SatisfiedContext model.{u} theory :=
  ⟨emptyContext, by
    intro φ memberTheory
    refine Eq.mp ?_ (theory_valid.{u} φ memberTheory)
    unfold HenkinModel.models PreModel.models
    congr 2
    funext A v
    nomatch v⟩

noncomputable def theoremSection {φ : ClosedFormula Symbol}
    (proof : ProofSyntax Symbol theory φ) : truthFamily model.{u} φ emptyContext :=
  proofSection model functionsRespectEqv proof satisfiedTheory

/-- The universal-set sentence is false in the very same model. Having
a nonempty HOL domain of sets does not make that domain an internal set. -/
def universalSet : ClosedFormula Symbol :=
  .ex (.all (member (.var .vz) (.var (.vs .vz))))

theorem universalSet_false : ¬ model.{u}.models universalSet := by
  rintro ⟨a, _, ha⟩
  exact ZFSet.mem_irrefl a (ha a trivial)

theorem universalSet_no_section :
    ¬ Nonempty (truthFamily model.{u} universalSet emptyContext) := by
  rintro ⟨witness⟩
  exact universalSet_false witness.down.down

/-- The concrete interpretation separates two sets, independently of
the chosen object-level proof language. -/
theorem empty_ne_singleton : (∅ : ZFSet.{u}) ≠ {∅} := by
  intro h
  have : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← h] at this
  exact ZFSet.notMem_empty ∅ this

def isEmpty : Formula Symbol (set :: []) :=
  .eq (.var .vz) (.const .empty)

def smallBound : Expr [] set := .app (.const .power) (.const .empty)

theorem empty_in_predicateSet :
    (∅ : ZFSet.{u}) ∈ predicateSet smallBound isEmpty emptyContext := by
  change (∅ : ZFSet.{u}) ∈ ZFSet.sep (fun x => x = ∅) (ZFSet.powerset ∅)
  exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (ZFSet.empty_subset ∅), rfl⟩

theorem singleton_not_in_predicateSet :
    ({∅} : ZFSet.{u}) ∉ predicateSet smallBound isEmpty emptyContext := by
  intro h
  change ({∅} : ZFSet.{u}) ∈ ZFSet.sep (fun x => x = ∅) (ZFSet.powerset ∅) at h
  exact empty_ne_singleton (ZFSet.mem_sep.mp h).2.symm

/-- This is a witness in the existing dependent family, obtained from the
actual separated set rather than from a separately constructed toy model. -/
noncomputable def emptyRefinement :
    refinementFamily model.{u} (bounded smallBound isEmpty) emptyContext :=
  (refinementSetEquiv smallBound isEmpty emptyContext).symm ⟨∅, empty_in_predicateSet⟩

theorem singleton_fibre_empty :
    ¬ Nonempty (predicateFamily model.{u} (bounded smallBound isEmpty)
      emptyContext ⟨({∅} : ZFSet.{u}), trivial⟩) := by
  rintro ⟨witness⟩
  exact singleton_not_in_predicateSet
    (refinementSetEquiv smallBound isEmpty emptyContext
      ⟨⟨({∅} : ZFSet.{u}), trivial⟩, witness⟩).2

/-- An empty refinement remains empty although the HOL set type is inhabited. -/
theorem empty_bound_has_no_refinement (φ : Formula Symbol (set :: [])) :
    ¬ Nonempty (refinementFamily model.{u} (bounded (.const .empty) φ) emptyContext) := by
  rintro ⟨point⟩
  have memberEmpty := (refinementSetEquiv (.const .empty) φ emptyContext point).2
  exact ZFSet.notMem_empty _ (ZFSet.mem_sep.mp memberEmpty).1

#print axioms replacementLaw_valid
#print axioms separationLaw_valid
#print axioms setInduction_valid
#print axioms hilbertChoice
#print axioms refinementSetEquiv
#print axioms predicateSet_substitution
#print axioms boundedProof
#print axioms predicateSet_subset_of_proof
#print axioms proof_refinement_set_square
#print axioms predicateSet_eq_of_proofs
#print axioms satisfiedTheory
#print axioms theoremSection
#print axioms universalSet_no_section
#print axioms emptyRefinement
#print axioms singleton_fibre_empty
#print axioms empty_bound_has_no_refinement

/-! ## A conservative choice operator

`Eps_set` chooses a set satisfying a predicate, and the empty set when none does.
It is not a constructor of `Symbol`: the package constant `epsN` already chooses
by `epsChoice`, and `Classical.choose` is not that function. `ChoiceSymbol` keeps
the seven set operations and adds the operator. -/

/-- The set signature extended by the choice operator. -/
inductive ChoiceSymbol : Ty Unit → Type where
  | core : {A : Ty Unit} → Symbol A → ChoiceSymbol A
  | epsilon : ChoiceSymbol (predicate ⇒ set)

/-- A set at which `p` holds, if there is one, and the empty set otherwise.
The witness is `Classical.choose`. -/
noncomputable def epsilonSet (p : ZFSet.{u} → ULift.{u + 1} Prop) : ZFSet.{u} :=
  haveI := Classical.propDecidable (∃ x, (p x).down)
  if h : ∃ x, (p x).down then Classical.choose h else ∅

/-- The chosen set satisfies `p` whenever some set does. -/
theorem epsilonSet_spec (p : ZFSet.{u} → ULift.{u + 1} Prop) {x : ZFSet.{u}}
    (hx : (p x).down) : (p (epsilonSet p)).down := by
  have witness : ∃ y, (p y).down := ⟨x, hx⟩
  unfold epsilonSet
  split
  · next h => exact Classical.choose_spec h
  · next h => exact absurd witness h

/-- With no satisfying set, the operator returns the empty set. -/
theorem epsilonSet_default (p : ZFSet.{u} → ULift.{u + 1} Prop)
    (h : ¬ ∃ x, (p x).down) : epsilonSet p = ∅ := by
  unfold epsilonSet
  split
  · next h' => exact absurd h' h
  · rfl

/-- Core symbols keep their set operations. `epsilon` is `epsilonSet`. -/
noncomputable def choiceDenote :
    {A : Ty Unit} → ChoiceSymbol A → Ty.denote.{0, u + 1} carrier.{u} A
  | _, .core c => denoteSymbol c
  | _, .epsilon => epsilonSet

/-- The set model extended by the choice operator. -/
noncomputable def choiceModel : HenkinModel.{0, 0, u + 1} Unit ChoiceSymbol :=
  HenkinModel.standard carrier choiceDenote

/-- `EpsI`: a predicate true of a set is true of `Eps_set` at that predicate. -/
def choiceLaw : ClosedFormula ChoiceSymbol :=
  .all (.all (.imp
    (.app (.var (.vs .vz)) (.var .vz))
    (.app (.var (.vs .vz)) (.app (.const .epsilon) (.var (.vs .vz))))))

theorem choiceLaw_valid : choiceModel.{u}.models choiceLaw := by
  intro P _ x _ hx
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  change ZFSet.{u} at x
  change (P (epsilonSet P)).down
  exact epsilonSet_spec P hx

end Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
