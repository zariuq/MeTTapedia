import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# A uniform induction principle with equational obligations

One object-language HOL sentence quantifies over list predicates. Its instance
for preservation of length by `map` has equational base and step obligations.
The higher-order representation remains available after those obligations are
discharged; it is not replaced by the backend's language.

The signature below is an abstract list interface, not a choice of programming
language or proof kernel. Its count sort has only the displayed equations.
-/

namespace Mettapedia.Logic.HOL.UniformListInduction

inductive BaseSort where
  | element | sequence | count

abbrev element : Ty BaseSort := .base .element
abbrev sequence : Ty BaseSort := .base .sequence
abbrev count : Ty BaseSort := .base .count
abbrev mapping : Ty BaseSort := element ⇒ element
abbrev predicate : Ty BaseSort := sequence ⇒ .prop

inductive Symbol : Ty BaseSort → Type where
  | nil : Symbol sequence
  | cons : Symbol (element ⇒ sequence ⇒ sequence)
  | map : Symbol (mapping ⇒ sequence ⇒ sequence)
  | length : Symbol (sequence ⇒ count)
  | zero : Symbol count
  | succ : Symbol (count ⇒ count)

abbrev Expr (Γ : Ctx BaseSort) (τ : Ty BaseSort) := Term Symbol Γ τ
abbrev Sentence (Γ : Ctx BaseSort) := Formula Symbol Γ

variable {Γ : Ctx BaseSort} {σ τ : Ty BaseSort}

def nil : Expr Γ sequence := .const .nil
def cons (x : Expr Γ element) (xs : Expr Γ sequence) : Expr Γ sequence :=
  .app (.app (.const .cons) x) xs
def map (f : Expr Γ mapping) (xs : Expr Γ sequence) : Expr Γ sequence :=
  .app (.app (.const .map) f) xs
def length (xs : Expr Γ sequence) : Expr Γ count := .app (.const .length) xs
def succ (n : Expr Γ count) : Expr Γ count := .app (.const .succ) n

def mapNil : Sentence Γ :=
  .all (.eq (map (.var .vz) nil) nil)

def mapCons : Sentence Γ :=
  .all (.all (.all
    (.eq (map (.var (.vs (.vs .vz))) (cons (.var (.vs .vz)) (.var .vz)))
      (cons (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (map (.var (.vs (.vs .vz))) (.var .vz))))))

def lengthNil : Sentence Γ := .eq (length nil) (.const .zero)

def lengthCons : Sentence Γ :=
  .all (.all (.eq (length (cons (.var (.vs .vz)) (.var .vz)))
    (succ (length (.var .vz)))))

def inductionStep (p : Expr Γ predicate) : Sentence Γ :=
  .all (.all (.imp
    (.app (weaken (weaken p)) (.var .vz))
    (.app (weaken (weaken p)) (cons (.var (.vs .vz)) (.var .vz)))))

/-- Quantification over predicates is in HOL syntax, not a Lean axiom schema. -/
def inductionPrinciple : Sentence Γ :=
  .all (.imp (.app (.var .vz) nil)
    (.imp (inductionStep (.var .vz))
      (.all (.app (.var (.vs .vz)) (.var .vz)))))

def equations : List (Sentence Γ) := [mapNil, mapCons, lengthNil, lengthCons]
def theory : List (Sentence Γ) := inductionPrinciple :: equations

def preservesLength (f : Expr Γ mapping) (xs : Expr Γ sequence) : Sentence Γ :=
  .eq (length (map f xs)) (length xs)

def lengthPredicate (f : Expr Γ mapping) : Expr Γ predicate :=
  .lam (preservesLength (weaken f) (.var .vz))

def mapLength : Sentence Γ :=
  .all (.all (preservesLength (.var (.vs .vz)) (.var .vz)))

@[simp] theorem instantiate_lengthPredicateBody
    (f : Expr Γ mapping) (xs : Expr Γ sequence) :
    instantiate xs (preservesLength (weaken f) (.var .vz)) =
      preservesLength f xs := by
  simp only [preservesLength, length, map, instantiate, subst]
  rw [← instantiate, instantiate_weaken]
  rfl

@[simp] theorem weaken_lengthPredicate (f : Expr Γ mapping) :
    weaken (σ := τ) (lengthPredicate f) = lengthPredicate (weaken f) := by
  simp [lengthPredicate, preservesLength, length, map, weaken, rename,
    rename_comp, Rename.lift, Rename.weaken]

@[simp] theorem weaken_equations : weakenHyps (σ := τ) (equations (Γ := Γ)) = equations := rfl
@[simp] theorem weaken_theory : weakenHyps (σ := τ) (theory (Γ := Γ)) = theory := rfl

private theorem predicate_beta (f : Expr Γ mapping) (xs : Expr Γ sequence)
    (Δ : List (Sentence Γ)) :
    ExtDerivation Symbol Δ (.eq (.app (lengthPredicate f) xs) (preservesLength f xs)) := by
  simpa only [lengthPredicate, instantiate_lengthPredicateBody] using
    (ExtDerivation.beta (Δ := Δ) xs (preservesLength (weaken f) (.var .vz)))

theorem predicate_of_equation {f : Expr Γ mapping} {xs : Expr Γ sequence}
    {Δ : List (Sentence Γ)} (h : ExtDerivation Symbol Δ (preservesLength f xs)) :
    ExtDerivation Symbol Δ (.app (lengthPredicate f) xs) :=
  .impE (.eqPropER (predicate_beta f xs Δ)) h

theorem equation_of_predicate {f : Expr Γ mapping} {xs : Expr Γ sequence}
    {Δ : List (Sentence Γ)} (h : ExtDerivation Symbol Δ (.app (lengthPredicate f) xs)) :
    ExtDerivation Symbol Δ (preservesLength f xs) :=
  .impE (.eqPropEL (predicate_beta f xs Δ)) h

theorem base_obligation (f : Expr Γ mapping) :
    ExtDerivation Symbol equations (preservesLength f nil) := by
  have ax : ExtDerivation Symbol (equations (Γ := Γ)) mapNil := .hyp (by simp [equations])
  have h : ExtDerivation Symbol equations (.eq (map f nil) nil) := by
    simpa [mapNil, instantiate, subst, Subst.single, map, nil] using .allE f ax
  exact .eqAppArg (.const .length) h

private theorem subst_single_weaken (t : Expr Γ σ) (u : Expr Γ τ) :
    subst (Subst.single t) (weaken u) = u := instantiate_weaken t u

private theorem subst_single_rename_weaken (t : Expr Γ σ) (u : Expr Γ τ) :
    subst (Subst.single t) (rename Rename.weaken u) = u := instantiate_weaken t u

theorem map_cons_equation (f : Expr Γ mapping) (x : Expr Γ element)
    (xs : Expr Γ sequence) :
    ExtDerivation Symbol equations
      (.eq (map f (cons x xs)) (cons (.app f x) (map f xs))) := by
  have ax : ExtDerivation Symbol (equations (Γ := Γ)) mapCons :=
    .hyp (by simp [equations])
  have atFunction : ExtDerivation Symbol equations
      (.all (.all (.eq
        (map (weaken (weaken f)) (cons (.var (.vs .vz)) (.var .vz)))
        (cons (.app (weaken (weaken f)) (.var (.vs .vz)))
          (map (weaken (weaken f)) (.var .vz)))))) := by
    simpa [mapCons, map, cons, instantiate, subst, Subst.single, Subst.lift,
      weaken, Rename.weaken] using ExtDerivation.allE f ax
  have atElement := ExtDerivation.allE x atFunction
  have atSequence := ExtDerivation.allE xs atElement
  simpa [map, cons, instantiate, subst, Subst.single, Subst.lift,
    subst_single_weaken, subst_single_rename_weaken] using atSequence

theorem length_cons_equation (x : Expr Γ element) (xs : Expr Γ sequence) :
    ExtDerivation Symbol equations
      (.eq (length (cons x xs)) (succ (length xs))) := by
  have ax : ExtDerivation Symbol (equations (Γ := Γ)) lengthCons :=
    .hyp (by simp [equations])
  have atElement := ExtDerivation.allE x ax
  have atSequence := ExtDerivation.allE xs atElement
  simpa [lengthCons, length, cons, succ, instantiate, subst, Subst.single,
    Subst.lift, subst_single_rename_weaken] using atSequence

/-- The cons obligation uses only the displayed equations and its induction
hypothesis: rewrite map and length, then apply successor congruence. -/
theorem step_obligation (f : Expr Γ mapping) (x : Expr Γ element)
    (xs : Expr Γ sequence) :
    ExtDerivation Symbol (preservesLength f xs :: equations)
      (preservesLength f (cons x xs)) := by
  have liftEquation {φ : Sentence Γ} (h : ExtDerivation Symbol equations φ) :
      ExtDerivation Symbol (preservesLength f xs :: equations) φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  have mapEq := liftEquation (map_cons_equation f x xs)
  have mappedLength := liftEquation (length_cons_equation (.app f x) (map f xs))
  have originalLength := liftEquation (length_cons_equation x xs)
  have ih : ExtDerivation Symbol (preservesLength f xs :: equations)
      (preservesLength f xs) := .hyp (by simp)
  exact .eqTrans (.eqAppArg (.const Symbol.length) mapEq)
    (.eqTrans mappedLength (.eqTrans (.eqAppArg (.const Symbol.succ) ih)
      (.eqSymm originalLength)))

/-- Actual HOL proof reconstruction from an instance of the single quantified
principle and proofs of its predicate's base and step obligations. -/
theorem induction_reconstruction (p : Expr Γ predicate) {Δ : List (Sentence Γ)}
    (principle : ExtDerivation Symbol Δ inductionPrinciple)
    (base : ExtDerivation Symbol Δ (.app p nil))
    (step : ExtDerivation Symbol Δ (inductionStep p)) :
    ExtDerivation Symbol Δ (.all (.app (weaken p) (.var .vz))) := by
  have instanceProof : ExtDerivation Symbol Δ
      (.imp (.app p nil)
        (.imp (inductionStep p) (.all (.app (weaken p) (.var .vz))))) := by
    simpa [inductionPrinciple, inductionStep, nil, cons, instantiate, subst, Subst.single,
      Subst.lift, weaken, rename, Rename.lift, Rename.weaken] using
      ExtDerivation.allE p principle
  exact .impE (.impE instanceProof base) step

private theorem length_predicate_step (f : Expr Γ mapping) :
    ExtDerivation Symbol equations (inductionStep (lengthPredicate f)) := by
  apply ExtDerivation.allI
  apply ExtDerivation.allI
  apply ExtDerivation.impI
  simp only [weaken_equations, weaken_lengthPredicate]
  apply predicate_of_equation
  let f' : Expr (sequence :: element :: Γ) mapping := weaken (weaken f)
  have equationStep := step_obligation f'
    (.var (.vs .vz)) (.var .vz)
  have ih : ExtDerivation Symbol
      (.app (lengthPredicate f') (.var .vz) :: equations)
      (preservesLength f' (.var .vz)) :=
    equation_of_predicate (.hyp (by simp))
  exact .impE
    (ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ)
      (.impI equationStep)) ih

/-- The higher-order theorem is reconstructed in object HOL. The function
parameter and predicate-quantified induction application are retained. -/
theorem mapLength_derivation : ExtDerivation Symbol (theory (Γ := Γ)) mapLength := by
  apply ExtDerivation.allI
  simp only [weaken_theory]
  have liftEquation {φ : Sentence (mapping :: Γ)}
      (h : ExtDerivation Symbol equations φ) : ExtDerivation Symbol theory φ :=
    ExtDerivation.mono (by intro ψ hψ; exact List.mem_cons_of_mem _ hψ) h
  have predicateAll := induction_reconstruction (lengthPredicate (.var .vz))
    (Δ := theory)
    (.hyp (by simp [theory]))
    (predicate_of_equation (liftEquation (base_obligation (.var .vz))))
    (liftEquation (length_predicate_step (.var .vz)))
  apply ExtDerivation.allI
  simp only [weaken_theory]
  apply equation_of_predicate
  have weakened := ExtDerivation.rename (Rename.weaken (σ := sequence)) predicateAll
  have atSequence := ExtDerivation.allE (.var .vz) weakened
  simpa [weakenHyps, weaken, rename, Rename.lift, Rename.weaken, instantiate,
    subst, Subst.single, Subst.lift, lengthPredicate, preservesLength, length, map,
    theory, equations, inductionPrinciple, inductionStep, mapNil, mapCons,
    lengthNil, lengthCons, cons, nil, succ] using atSequence

/-! ## Standard list semantics -/

namespace StandardListModel

abbrev LiftedElement := ULift.{1, 0} Bool
abbrev LiftedSequence := ULift.{1, 0} (List Bool)
abbrev LiftedCount := ULift.{1, 0} Nat

def carrier : BaseSort → Type 1
  | .element => LiftedElement
  | .sequence => LiftedSequence
  | .count => LiftedCount

def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .nil => ⟨[]⟩
  | _, .cons => fun x xs => ⟨x.down :: xs.down⟩
  | _, .map => fun f xs => ⟨xs.down.map (fun x => (f ⟨x⟩).down)⟩
  | _, .length => fun xs => ⟨xs.down.length⟩
  | _, .zero => ⟨0⟩
  | _, .succ => fun n => ⟨Nat.succ n.down⟩

/-- Full predicate domains over ordinary finite Boolean lists. -/
def model : HenkinModel.{0, 0, 0} BaseSort Symbol :=
  HenkinModel.standard carrier constant

theorem mapNil_valid : model.models mapNil := by
  intro f _
  rfl

theorem mapCons_valid : model.models mapCons := by
  intro f _ x _ xs _
  rfl

theorem lengthNil_valid : model.models lengthNil := rfl

theorem lengthCons_valid : model.models lengthCons := by
  intro x _ xs _
  rfl

theorem induction_valid : model.models inductionPrinciple := by
  intro p _ base step xs hxs
  clear hxs
  rcases xs with ⟨xs⟩
  induction xs with
  | nil => exact base
  | cons x xs ih => exact step ⟨x⟩ trivial ⟨xs⟩ trivial ih

theorem equations_valid : ∀ φ ∈ equations (Γ := []), model.models φ := by
  intro φ membership
  simp only [equations, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  · exact mapNil_valid
  · exact mapCons_valid
  · exact lengthNil_valid
  · exact lengthCons_valid

theorem theory_valid : ∀ φ ∈ theory (Γ := []), model.models φ := by
  intro φ membership
  rcases List.mem_cons.mp membership with rfl | membership
  · exact induction_valid
  · exact equations_valid φ membership

/-- An independent semantic readout using ordinary list length. -/
theorem mapLength_valid : model.models mapLength := by
  intro f _ xs _
  change (ULift.up ((xs.down.map (fun x : Bool => (f (ULift.up x)).down)).length) :
      LiftedCount) = ULift.up xs.down.length
  simp only [List.length_map]

end StandardListModel

/-! ## An explicit model of the equations without induction

This is a countermodel for exactly the displayed signature and equations.
Its sequence carrier has a junk point, and its count successor is the
identity on two values.  No Peano successor laws, list-constructor injectivity,
or nil/cons disjointness belong to `equations`; this model does not refute
claims about a theory that additionally requires those properties.
-/

namespace JunkModel

abbrev LiftedBool := ULift.{1, 0} Bool

def carrier : BaseSort → Type 1 := fun _ => LiftedBool

def constant : {τ : Ty BaseSort} → Symbol τ → Ty.denote.{0, 0} carrier τ
  | _, .nil => ⟨false⟩
  | _, .cons => fun _ xs => xs
  | _, .map => fun _ _ => ⟨false⟩
  | _, .length => fun xs => xs
  | _, .zero => ⟨false⟩
  | _, .succ => fun n => n

/-- The `true` sequence is not generated from nil by this cons operation. -/
def model : HenkinModel.{0, 0, 0} BaseSort Symbol :=
  HenkinModel.standard carrier constant

theorem mapNil_valid : model.models mapNil := by
  intro f _
  rfl

theorem mapCons_valid : model.models mapCons := by
  intro f _ x _ xs _
  rfl

theorem lengthNil_valid : model.models lengthNil := rfl

theorem lengthCons_valid : model.models lengthCons := by
  intro x _ xs _
  rfl

theorem equations_valid : ∀ φ ∈ equations (Γ := []), model.models φ := by
  intro φ membership
  simp only [equations, List.mem_cons, List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  · exact mapNil_valid
  · exact mapCons_valid
  · exact lengthNil_valid
  · exact lengthCons_valid

/-- Mapping the junk point to nil changes its count. -/
theorem mapLength_invalid : ¬ model.models mapLength := by
  intro h
  have impossible := h (fun x => x) trivial ⟨true⟩ trivial
  change (ULift.up false : LiftedBool) = ULift.up true at impossible
  exact Bool.false_ne_true (congrArg ULift.down impossible)

/-- The predicate selecting nil is cons-closed but excludes the junk point. -/
theorem induction_invalid : ¬ model.models inductionPrinciple := by
  intro h
  have allSequences := h (fun (xs : LiftedBool) => ULift.up (xs.down = false))
    trivial rfl (by intro x _ xs _ hx; exact hx)
  have impossible := allSequences ⟨true⟩ trivial
  exact Bool.noConfusion impossible

end JunkModel

/-- The displayed equations do not prove the higher-order map/length theorem;
soundness transfers any purported object proof to the explicit countermodel. -/
theorem equations_do_not_derive_mapLength :
    ¬ ExtDerivation Symbol (equations (Γ := [])) mapLength := by
  intro proof
  apply JunkModel.mapLength_invalid
  exact Soundness.extDerivation_sound proof
    (M := JunkModel.model) (ρ := fun {_} v => nomatch v)
    (HenkinModel.functionsRespectEqv_of_fullDomains JunkModel.model
      (HenkinModel.fullDomains_standard JunkModel.carrier JunkModel.constant))
    (by intro τ v; nomatch v)
    (by
      intro φ membership
      refine Eq.mp ?_ (JunkModel.equations_valid φ membership)
      unfold HenkinModel.models PreModel.models
      apply congrArg ULift.down
      apply congrArg (PreModel.denote JunkModel.model.toPreModel φ)
      funext τ v
      nomatch v)

/-- A jointly satisfied full theory and an explicit equations-only failure
keep consistency and the need for the additional principle separate. -/
theorem standard_and_junk_controls :
    (∀ φ ∈ theory (Γ := []), StandardListModel.model.models φ) ∧
    StandardListModel.model.models mapLength ∧
    (∀ φ ∈ equations (Γ := []), JunkModel.model.models φ) ∧
    ¬ JunkModel.model.models inductionPrinciple ∧
    ¬ JunkModel.model.models mapLength :=
  ⟨StandardListModel.theory_valid, StandardListModel.mapLength_valid,
    JunkModel.equations_valid, JunkModel.induction_invalid, JunkModel.mapLength_invalid⟩

#print axioms base_obligation
#print axioms step_obligation
#print axioms induction_reconstruction
#print axioms mapLength_derivation
#print axioms StandardListModel.theory_valid
#print axioms JunkModel.induction_invalid
#print axioms equations_do_not_derive_mapLength
#print axioms standard_and_junk_controls

end Mettapedia.Logic.HOL.UniformListInduction
