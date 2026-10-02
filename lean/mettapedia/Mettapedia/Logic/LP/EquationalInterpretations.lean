import Mettapedia.Logic.LP.FirstOrderRewriting
import Mathlib.ModelTheory.Quotients

/-!
# Interpretations that respect an equational theory

Rewriting with a set of equations preserves membership in a Herbrand
interpretation when the interpretation does not tell apart ground terms that
the equations identify.

The ground terms the rules identify form the least congruence containing
every ground instance of a rule. An interpretation respects the rules when
membership of a ground atom depends on its arguments only up to that
congruence.

The Herbrand structure of such an interpretation passes to the quotient of
the ground terms by the congruence. In the quotient every rule is valid, and
a ground atom is true exactly when it belongs to the interpretation. The
theorem on rewriting in a model of the rules then gives the statement for the
interpretation itself (`rewrite_groundAtom_iff`).

The hypothesis is the right one in two ways. An interpretation respects the
rules exactly when it consists of the ground atoms true in some model of the
rules (`respects_iff_exists_model`), and exactly when rewriting an argument
never changes membership (`respects_iff_rewriteInvariant`). Every
interpretation has a least extension that respects the rules (`saturate`).

The free Herbrand structure is the case of the trivial congruence: rules
valid in it identify no two ground terms, and every interpretation respects
them (`respects_of_valid_herbrand`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP

universe u v

variable {σ : LPSignature.{u, u, v, u}}

namespace Grounding

/-- Grounding a substitution instance grounds the substituted terms. -/
theorem groundTerm_applyTerm (grounding : Grounding σ) (substitution : Subst σ)
    (term : Term σ) :
    grounding.groundTerm (substitution.applyTerm term) =
      Grounding.groundTerm (fun name => grounding.groundTerm (substitution name)) term := by
  induction term with
  | var name => rfl
  | const symbol => rfl
  | app symbol arguments ih => simp only [Subst.applyTerm, Grounding.groundTerm, ih]

/-- A ground term is its own ground instance. -/
theorem groundTerm_of_ground (grounding : Grounding σ) (term : GroundTerm σ) :
    grounding.groundTerm term.toTerm = term := by
  induction term with
  | const symbol => rfl
  | app symbol arguments ih => simp only [GroundTerm.toTerm, Grounding.groundTerm, ih]

end Grounding

/-- A ground atom is its own ground instance. -/
theorem Grounding.groundAtom_of_ground (grounding : Grounding σ) (symbol : σ.relationSymbols)
    (arguments : Fin (σ.relationArity symbol) → GroundTerm σ) :
    grounding.groundAtom ⟨symbol, fun position => (arguments position).toTerm⟩ =
      ⟨symbol, arguments⟩ := by
  simp only [Grounding.groundAtom, Grounding.groundTerm_of_ground]

/-- Changing one ground argument and then reading the arguments as terms is
changing one argument of the terms. -/
theorem toTerm_update {arity : ℕ} (arguments : Fin arity → GroundTerm σ) (position : Fin arity)
    (value : GroundTerm σ) :
    Function.update (fun index => (arguments index).toTerm) position value.toTerm =
      fun index => (Function.update arguments position value index).toTerm := by
  funext index
  by_cases same : index = position
  · subst same
    simp only [Function.update_self]
  · simp only [Function.update_of_ne same]

/-- A relation on tuples that is reflexive and transitive, and that relates a
tuple to its change at one coordinate along `step`, relates any two tuples
that are `step`-related at every coordinate. -/
theorem relates_of_coordinate_updates {arity : ℕ} {α : Type*} {step : α → α → Prop}
    {related : (Fin arity → α) → (Fin arity → α) → Prop}
    (refl : ∀ tuple, related tuple tuple)
    (trans : ∀ first second third, related first second → related second third →
      related first third)
    (single : ∀ (tuple : Fin arity → α) (position : Fin arity) (value : α),
      step (tuple position) value → related tuple (Function.update tuple position value))
    (left right : Fin arity → α) (pointwise : ∀ position, step (left position) (right position)) :
    related left right := by
  classical
  have mixed : ∀ changed : Finset (Fin arity),
      related left (fun index => if index ∈ changed then right index else left index) := by
    intro changed
    induction changed using Finset.induction_on with
    | empty => simpa using refl left
    | insert position changed notMember ih =>
        refine trans _ _ _ ih ?_
        have one := single (fun index => if index ∈ changed then right index else left index)
          position (right position) (by simpa only [if_neg notMember] using pointwise position)
        have same : Function.update
            (fun index => if index ∈ changed then right index else left index) position
              (right position) =
            fun index => if index ∈ insert position changed then right index else left index := by
          funext index
          by_cases here : index = position
          · subst here
            simp
          · simp [Finset.mem_insert, here]
        rwa [same] at one
  simpa using mixed Finset.univ

namespace FirstOrderRewriting

open FirstOrderBridge

/-- The ground terms the rules identify: the least congruence that contains
every ground instance of a rule. -/
inductive GroundCongruent (rules : Set (Equation σ)) : GroundTerm σ → GroundTerm σ → Prop where
  | rule (equation : Equation σ) (member : equation ∈ rules) (grounding : Grounding σ) :
      GroundCongruent rules (grounding.groundTerm equation.left)
        (grounding.groundTerm equation.right)
  | refl (term : GroundTerm σ) : GroundCongruent rules term term
  | symm {left right : GroundTerm σ} :
      GroundCongruent rules left right → GroundCongruent rules right left
  | trans {first second third : GroundTerm σ} :
      GroundCongruent rules first second → GroundCongruent rules second third →
        GroundCongruent rules first third
  | app (symbol : σ.functionSymbols)
      {left right : Fin (σ.functionArity symbol) → GroundTerm σ} :
      (∀ position, GroundCongruent rules (left position) (right position)) →
        GroundCongruent rules (.app symbol left) (.app symbol right)

/-- The congruence of the rules as an equivalence relation on ground terms. -/
def groundCongruence (rules : Set (Equation σ)) : Setoid (GroundTerm σ) where
  r := GroundCongruent rules
  iseqv := ⟨GroundCongruent.refl, GroundCongruent.symm, GroundCongruent.trans⟩

theorem GroundCongruent.mono {rules more : Set (Equation σ)} (subset : rules ⊆ more)
    {left right : GroundTerm σ} (congruent : GroundCongruent rules left right) :
    GroundCongruent more left right := by
  induction congruent with
  | rule equation member grounding => exact .rule equation (subset member) grounding
  | refl term => exact .refl term
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | app symbol _ ih => exact .app symbol ih

/-- The ground instances of a rewriting step are congruent. -/
theorem Rewrite.groundCongruent {rules : Set (Equation σ)} {left right : Term σ}
    (rewrite : Rewrite rules left right) (grounding : Grounding σ) :
    GroundCongruent rules (grounding.groundTerm left) (grounding.groundTerm right) := by
  cases rewrite with
  | rule equation member substitution context =>
    induction context with
    | hole =>
        simp only [Context.fill, Grounding.groundTerm_applyTerm]
        exact .rule equation member _
    | app symbol arguments position inner ih =>
        simp only [Context.fill, Grounding.groundTerm]
        refine .app symbol fun index => ?_
        by_cases same : index = position
        · subst index
          simpa only [Function.update_self] using ih
        · simp only [Function.update_of_ne same]
          exact .refl _

/-- The ground instances of the two ends of a rewriting sequence are
congruent. -/
theorem Rewrites.groundCongruent {rules : Set (Equation σ)} {left right : Term σ}
    (derivation : Rewrites rules left right) (grounding : Grounding σ) :
    GroundCongruent rules (grounding.groundTerm left) (grounding.groundTerm right) := by
  induction derivation with
  | refl => exact .refl _
  | step _ rewrite ih => exact .trans ih (rewrite.groundCongruent grounding)

/-- Ground atoms with the same relation symbol and congruent arguments. -/
inductive AtomCongruent (rules : Set (Equation σ)) : GroundAtom σ → GroundAtom σ → Prop where
  | arguments (symbol : σ.relationSymbols)
      {left right : Fin (σ.relationArity symbol) → GroundTerm σ}
      (pointwise : ∀ position, GroundCongruent rules (left position) (right position)) :
      AtomCongruent rules ⟨symbol, left⟩ ⟨symbol, right⟩

theorem AtomCongruent.refl (rules : Set (Equation σ)) (atom : GroundAtom σ) :
    AtomCongruent rules atom atom :=
  .arguments atom.symbol fun _ => .refl _

theorem AtomCongruent.symm {rules : Set (Equation σ)} {first second : GroundAtom σ}
    (congruent : AtomCongruent rules first second) : AtomCongruent rules second first := by
  cases congruent with
  | arguments symbol pointwise => exact .arguments symbol fun position => (pointwise position).symm

theorem AtomCongruent.trans {rules : Set (Equation σ)} {first second third : GroundAtom σ}
    (earlier : AtomCongruent rules first second) (later : AtomCongruent rules second third) :
    AtomCongruent rules first third := by
  cases earlier with
  | arguments symbol pointwise =>
    cases later with
    | arguments _ further =>
      exact .arguments symbol fun position => (pointwise position).trans (further position)

/-- An interpretation respects the rules when it does not tell apart ground
atoms whose arguments the rules identify. -/
def Respects (rules : Set (Equation σ)) (interpretation : Interpretation σ) : Prop :=
  ∀ ⦃first second : GroundAtom σ⦄, AtomCongruent rules first second →
    first ∈ interpretation → second ∈ interpretation

theorem Respects.mem_iff {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation) {first second : GroundAtom σ}
    (congruent : AtomCongruent rules first second) :
    first ∈ interpretation ↔ second ∈ interpretation :=
  ⟨respects congruent, respects congruent.symm⟩

/-- Fewer rules are easier to respect. -/
theorem Respects.mono {rules more : Set (Equation σ)} (subset : rules ⊆ more)
    {interpretation : Interpretation σ} (respects : Respects more interpretation) :
    Respects rules interpretation := by
  intro first second congruent
  cases congruent with
  | arguments symbol pointwise =>
    exact respects (.arguments symbol fun position => (pointwise position).mono subset)

/-! ## The term model -/

/-- The Herbrand structure of an interpretation that respects the rules passes
to the quotient of the ground terms by the congruence of the rules. -/
@[instance_reducible] def herbrandPrestructure {rules : Set (Equation σ)}
    {interpretation : Interpretation σ} (respects : Respects rules interpretation) :
    (language σ).Prestructure (groundCongruence rules) where
  toStructure := herbrandStructure interpretation
  fun_equiv := by
    intro arity symbol left right equivalent
    cases symbol with
    | constant symbol => exact GroundCongruent.refl _
    | function symbol => exact GroundCongruent.app symbol equivalent
  rel_equiv := by
    intro arity symbol left right equivalent
    cases symbol with
    | relation symbol =>
      exact propext (respects.mem_iff (AtomCongruent.arguments symbol equivalent))

/-- The ground terms up to the congruence of the rules. -/
abbrev TermModel (rules : Set (Equation σ)) : Type u := Quotient (groundCongruence rules)

/-- The structure on the term model: functions build terms, and a relation
holds of classes when the interpretation contains the atom of any of their
representatives. -/
@[instance_reducible] def termModelStructure {rules : Set (Equation σ)}
    {interpretation : Interpretation σ} (respects : Respects rules interpretation) :
    (language σ).Structure (TermModel rules) :=
  @FirstOrder.Language.quotientStructure (language σ) (GroundTerm σ) (groundCongruence rules)
    (herbrandPrestructure respects)

/-- In the term model a term denotes the class of its ground instance. -/
theorem realizeTerm_termModel {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation) (grounding : Grounding σ) (term : Term σ) :
    @realizeTerm σ (TermModel rules) (termModelStructure respects)
        (fun name => (⟦grounding name⟧ : TermModel rules)) term =
      (⟦grounding.groundTerm term⟧ : TermModel rules) := by
  let := herbrandPrestructure respects
  refine (@encodeTerm_realize σ (TermModel rules) (termModelStructure respects) _ term).symm.trans ?_
  refine (FirstOrder.Language.Term.realize_quotient_mk' (groundCongruence rules)
    (encodeTerm term) grounding).trans ?_
  exact congrArg (Quotient.mk (groundCongruence rules))
    (encodeTerm_realize_herbrand interpretation grounding term)

/-- **Every rule is valid in the term model.** -/
theorem valid_termModel {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation) :
    ∀ equation ∈ rules,
      @Equation.Valid σ equation (TermModel rules) (termModelStructure respects) := by
  intro equation member assignment
  obtain ⟨grounding, rfl⟩ : ∃ grounding : Grounding σ,
      assignment = fun name => (⟦grounding name⟧ : TermModel rules) :=
    ⟨fun name => (assignment name).out, funext fun name => (Quotient.out_eq _).symm⟩
  rw [realizeTerm_termModel respects, realizeTerm_termModel respects]
  exact Quotient.sound (GroundCongruent.rule equation member grounding)

/-- In the term model an atom is true exactly when its ground instance belongs
to the interpretation. -/
theorem realizeAtom_termModel {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation) (grounding : Grounding σ) (atom : Atom σ) :
    @realizeAtom σ (TermModel rules) (termModelStructure respects)
        (fun name => (⟦grounding name⟧ : TermModel rules)) atom ↔
      grounding.groundAtom atom ∈ interpretation := by
  let := herbrandPrestructure respects
  unfold realizeAtom
  simp only [realizeTerm_termModel respects]
  exact FirstOrder.Language.relMap_quotient_mk' (L := language σ) (groundCongruence rules)
    (RelationSymbol.relation atom.symbol : (language σ).Relations _)
    (fun position => grounding.groundTerm (atom.args position))

/-- **Rewriting an argument preserves membership in an interpretation that
respects the rules.** -/
theorem rewrite_groundAtom_iff {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation)
    (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol))
    (replacement : Term σ) (rewrite : Rewrite rules (atom.args position) replacement)
    (grounding : Grounding σ) :
    grounding.groundAtom atom ∈ interpretation ↔
      grounding.groundAtom ⟨atom.symbol, Function.update atom.args position replacement⟩
        ∈ interpretation := by
  let := termModelStructure respects
  exact (realizeAtom_termModel respects grounding atom).symm.trans
    ((rewrite_atom_iff (valid_termModel respects) atom position replacement rewrite _).trans
      (realizeAtom_termModel respects grounding _))

/-- The same for a rewriting sequence. -/
theorem rewrites_groundAtom_iff {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation)
    (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol))
    (replacement : Term σ) (derivation : Rewrites rules (atom.args position) replacement)
    (grounding : Grounding σ) :
    grounding.groundAtom atom ∈ interpretation ↔
      grounding.groundAtom ⟨atom.symbol, Function.update atom.args position replacement⟩
        ∈ interpretation := by
  let := termModelStructure respects
  exact (realizeAtom_termModel respects grounding atom).symm.trans
    ((rewrites_atom_iff (valid_termModel respects) atom position replacement derivation _).trans
      (realizeAtom_termModel respects grounding _))

/-! ## Models of the rules -/

section Models

variable (Model : Type*) [(language σ).Structure Model]

/-- The value of a ground term in a structure. -/
def evaluateGround : GroundTerm σ → Model
  | .const symbol =>
    FirstOrder.Language.Structure.funMap (L := language σ) (.constant symbol) Fin.elim0
  | .app symbol arguments =>
    FirstOrder.Language.Structure.funMap (L := language σ) (.function symbol)
      (fun position => evaluateGround (arguments position))

/-- The ground atoms true in a structure. -/
def inducedInterpretation : Interpretation σ :=
  {atom | FirstOrder.Language.Structure.RelMap (L := language σ) (.relation atom.symbol)
    (fun position => evaluateGround Model (atom.args position))}

variable {Model}

/-- The value of a ground instance is the value of the term under the values
of the grounding. -/
theorem realizeTerm_evaluateGround (grounding : Grounding σ) (term : Term σ) :
    realizeTerm (fun name => evaluateGround Model (grounding name)) term =
      evaluateGround Model (grounding.groundTerm term) := by
  induction term with
  | var name => rfl
  | const symbol => rfl
  | app symbol arguments ih => simp only [realizeTerm, Grounding.groundTerm, evaluateGround, ih]

/-- A ground term has its value under every assignment. -/
theorem realizeTerm_toTerm (assignment : σ.vars → Model) (term : GroundTerm σ) :
    realizeTerm assignment term.toTerm = evaluateGround Model term := by
  induction term with
  | const symbol => rfl
  | app symbol arguments ih => simp only [GroundTerm.toTerm, realizeTerm, evaluateGround, ih]

/-- A ground instance of an atom is in the induced interpretation exactly when
the atom is true under the values of the grounding. -/
theorem groundAtom_mem_inducedInterpretation (grounding : Grounding σ) (atom : Atom σ) :
    grounding.groundAtom atom ∈ inducedInterpretation Model ↔
      realizeAtom (fun name => evaluateGround Model (grounding name)) atom := by
  change FirstOrder.Language.Structure.RelMap (L := language σ) (.relation atom.symbol)
      (fun position => evaluateGround Model (grounding.groundTerm (atom.args position))) ↔ _
  simp only [realizeAtom, realizeTerm_evaluateGround]

/-- Ground terms the rules identify have the same value in every model of the
rules. -/
theorem GroundCongruent.evaluateGround_eq {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model) {left right : GroundTerm σ}
    (congruent : GroundCongruent rules left right) :
    evaluateGround Model left = evaluateGround Model right := by
  induction congruent with
  | rule equation member grounding =>
      rw [← realizeTerm_evaluateGround, ← realizeTerm_evaluateGround]
      exact valid equation member _
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | app symbol _ ih => simp only [evaluateGround, ih]

/-- **The ground atoms true in a model of the rules form an interpretation
that respects the rules.** -/
theorem respects_inducedInterpretation {rules : Set (Equation σ)}
    (valid : ∀ equation ∈ rules, equation.Valid Model) :
    Respects rules (inducedInterpretation Model) := by
  intro first second congruent member
  cases congruent with
  | @arguments symbol left right pointwise =>
    have same : (fun position => evaluateGround Model (left position)) =
        fun position => evaluateGround Model (right position) :=
      funext fun position => (pointwise position).evaluateGround_eq valid
    change FirstOrder.Language.Structure.RelMap (L := language σ) (.relation symbol)
      (fun position => evaluateGround Model (right position))
    rw [← same]
    exact member

end Models

/-- In the term model a ground term denotes its class. -/
theorem evaluateGround_termModel {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (respects : Respects rules interpretation) (term : GroundTerm σ) :
    @evaluateGround σ (TermModel rules) (termModelStructure respects) term =
      (⟦term⟧ : TermModel rules) := by
  have step := realizeTerm_termModel respects (fun _ => term) term.toTerm
  have self : Grounding.groundTerm (fun _ => term) term.toTerm = term :=
    Grounding.groundTerm_of_ground _ term
  exact ((@realizeTerm_toTerm σ (TermModel rules) (termModelStructure respects) _ term).symm.trans
    step).trans (congrArg (Quotient.mk (groundCongruence rules)) self)

/-- **The term model induces the interpretation it was built from.** -/
theorem inducedInterpretation_termModel {rules : Set (Equation σ)}
    {interpretation : Interpretation σ} (respects : Respects rules interpretation) :
    @inducedInterpretation σ (TermModel rules) (termModelStructure respects) = interpretation := by
  let := herbrandPrestructure respects
  ext atom
  change FirstOrder.Language.Structure.RelMap (L := language σ) (.relation atom.symbol)
      (fun position => @evaluateGround σ (TermModel rules) (termModelStructure respects)
        (atom.args position)) ↔ _
  simp only [evaluateGround_termModel respects]
  exact FirstOrder.Language.relMap_quotient_mk' (L := language σ) (groundCongruence rules)
    (RelationSymbol.relation atom.symbol : (language σ).Relations _) atom.args

/-- **An interpretation respects the rules exactly when it consists of the
ground atoms true in some model of the rules.** -/
theorem respects_iff_exists_model (rules : Set (Equation σ)) (interpretation : Interpretation σ) :
    Respects rules interpretation ↔
      ∃ (Model : Type u) (symbols : (language σ).Structure Model),
        (∀ equation ∈ rules, @Equation.Valid σ equation Model symbols) ∧
          @inducedInterpretation σ Model symbols = interpretation := by
  constructor
  · intro respects
    exact ⟨TermModel rules, termModelStructure respects, valid_termModel respects,
      inducedInterpretation_termModel respects⟩
  · rintro ⟨Model, symbols, valid, rfl⟩
    exact @respects_inducedInterpretation σ Model symbols rules valid

/-- The free Herbrand structure induces its own interpretation. -/
theorem inducedInterpretation_herbrand (interpretation : Interpretation σ) :
    @inducedInterpretation σ (GroundTerm σ) (herbrandStructure interpretation) = interpretation := by
  let _ := herbrandStructure interpretation
  have value : ∀ term : GroundTerm σ, evaluateGround (GroundTerm σ) term = term := by
    intro term
    induction term with
    | const symbol => rfl
    | app symbol arguments ih =>
        change GroundTerm.app symbol (fun position => evaluateGround (GroundTerm σ) (arguments position)) = _
        simp only [ih]
  ext atom
  change (⟨atom.symbol, fun position => evaluateGround (GroundTerm σ) (atom.args position)⟩ :
    GroundAtom σ) ∈ interpretation ↔ _
  simp only [value]

/-- Rules valid in the free Herbrand structure are respected by every
interpretation: there the congruence is equality, and the statement about
rewriting is about replacing a term by itself. -/
theorem respects_of_valid_herbrand (interpretation : Interpretation σ)
    {rules : Set (Equation σ)}
    (valid : let := herbrandStructure interpretation
      ∀ equation ∈ rules, equation.Valid (GroundTerm σ)) :
    Respects rules interpretation := by
  have induced := @respects_inducedInterpretation σ (GroundTerm σ)
    (herbrandStructure interpretation) rules valid
  rwa [inducedInterpretation_herbrand] at induced

/-! ## The least extension that respects the rules -/

/-- The ground atoms congruent to an atom of the interpretation. -/
def saturate (rules : Set (Equation σ)) (interpretation : Interpretation σ) : Interpretation σ :=
  {atom | ∃ origin ∈ interpretation, AtomCongruent rules origin atom}

theorem subset_saturate (rules : Set (Equation σ)) (interpretation : Interpretation σ) :
    interpretation ⊆ saturate rules interpretation :=
  fun atom member => ⟨atom, member, .refl rules atom⟩

theorem respects_saturate (rules : Set (Equation σ)) (interpretation : Interpretation σ) :
    Respects rules (saturate rules interpretation) := by
  rintro first second congruent ⟨origin, member, earlier⟩
  exact ⟨origin, member, earlier.trans congruent⟩

/-- **The saturation is the least extension that respects the rules.** -/
theorem saturate_subset {rules : Set (Equation σ)} {interpretation larger : Interpretation σ}
    (respects : Respects rules larger) (subset : interpretation ⊆ larger) :
    saturate rules interpretation ⊆ larger := by
  rintro atom ⟨origin, member, congruent⟩
  exact respects congruent (subset member)

theorem respects_iff_saturate_eq (rules : Set (Equation σ)) (interpretation : Interpretation σ) :
    Respects rules interpretation ↔ saturate rules interpretation = interpretation := by
  constructor
  · intro respects
    exact Set.Subset.antisymm (saturate_subset respects (Set.Subset.refl _))
      (subset_saturate rules interpretation)
  · intro same
    rw [← same]
    exact respects_saturate rules interpretation

/-! ## Respecting the rules is invariance under rewriting -/

/-- Membership never changes when an argument is rewritten. -/
def RewriteInvariant (rules : Set (Equation σ)) (interpretation : Interpretation σ) : Prop :=
  ∀ (atom : Atom σ) (position : Fin (σ.relationArity atom.symbol)) (replacement : Term σ),
    Rewrite rules (atom.args position) replacement → ∀ grounding : Grounding σ,
      (grounding.groundAtom atom ∈ interpretation ↔
        grounding.groundAtom ⟨atom.symbol, Function.update atom.args position replacement⟩
          ∈ interpretation)

/-- Under invariance, ground terms the rules identify can replace each other
anywhere inside an argument. -/
theorem RewriteInvariant.of_groundCongruent {rules : Set (Equation σ)}
    {interpretation : Interpretation σ} (invariant : RewriteInvariant rules interpretation)
    {left right : GroundTerm σ} (congruent : GroundCongruent rules left right) :
    ∀ (context : Context σ) (symbol : σ.relationSymbols)
      (arguments : Fin (σ.relationArity symbol) → Term σ)
      (position : Fin (σ.relationArity symbol)) (grounding : Grounding σ),
      (grounding.groundAtom
          ⟨symbol, Function.update arguments position (context.fill left.toTerm)⟩
            ∈ interpretation ↔
        grounding.groundAtom
          ⟨symbol, Function.update arguments position (context.fill right.toTerm)⟩
            ∈ interpretation) := by
  induction congruent with
  | rule equation member ground =>
      intro context symbol arguments position grounding
      have step : Rewrite rules (context.fill (ground.groundTerm equation.left).toTerm)
          (context.fill (ground.groundTerm equation.right).toTerm) := by
        rw [Grounding.groundTerm_toTerm, Grounding.groundTerm_toTerm]
        exact Rewrite.rule equation member ground.toSubst context
      have result := invariant
        ⟨symbol, Function.update arguments position
          (context.fill (ground.groundTerm equation.left).toTerm)⟩ position
        (context.fill (ground.groundTerm equation.right).toTerm)
        (by simpa only [Function.update_self] using step) grounding
      simpa only [Function.update_idem] using result
  | refl => exact fun _ _ _ _ _ => Iff.rfl
  | symm _ ih =>
      exact fun context symbol arguments position grounding =>
        (ih context symbol arguments position grounding).symm
  | trans _ _ first second =>
      exact fun context symbol arguments position grounding =>
        (first context symbol arguments position grounding).trans
          (second context symbol arguments position grounding)
  | @app function left right pointwise ih =>
      intro context symbol arguments position grounding
      refine relates_of_coordinate_updates
        (step := fun (earlier later : GroundTerm σ) => ∀ inner : Context σ,
          (grounding.groundAtom
              ⟨symbol, Function.update arguments position (inner.fill earlier.toTerm)⟩
                ∈ interpretation ↔
            grounding.groundAtom
              ⟨symbol, Function.update arguments position (inner.fill later.toTerm)⟩
                ∈ interpretation))
        (related := fun earlier later =>
          (grounding.groundAtom ⟨symbol, Function.update arguments position
              (context.fill (Term.app function fun index => (earlier index).toTerm))⟩
                ∈ interpretation ↔
            grounding.groundAtom ⟨symbol, Function.update arguments position
              (context.fill (Term.app function fun index => (later index).toTerm))⟩
                ∈ interpretation))
        (fun _ => Iff.rfl) (fun _ _ _ first second => first.trans second) ?_ left right
        (fun index inner => ih index inner symbol arguments position grounding)
      intro tuple coordinate value related
      have one := related
        (context.comp (.app function (fun index => (tuple index).toTerm) coordinate .hole))
      simp only [Context.fill_comp, Context.fill] at one
      rw [toTerm_update tuple coordinate (tuple coordinate), Function.update_eq_self,
        toTerm_update tuple coordinate value] at one
      exact one

/-- Invariance under rewriting gives respect for the rules. -/
theorem RewriteInvariant.respects {rules : Set (Equation σ)} {interpretation : Interpretation σ}
    (invariant : RewriteInvariant rules interpretation) : Respects rules interpretation := by
  intro first second congruent member
  cases congruent with
  | @arguments symbol left right pointwise =>
    refine (relates_of_coordinate_updates (step := GroundCongruent rules)
      (related := fun earlier later =>
        ((⟨symbol, earlier⟩ : GroundAtom σ) ∈ interpretation ↔
          (⟨symbol, later⟩ : GroundAtom σ) ∈ interpretation))
      (fun _ => Iff.rfl) (fun _ _ _ first second => first.trans second) ?_ left right
      pointwise).mp member
    intro tuple coordinate value congruent
    have ground : Grounding σ := fun _ => value
    have one := invariant.of_groundCongruent congruent .hole symbol
      (fun index => (tuple index).toTerm) coordinate ground
    simp only [Context.fill] at one
    rw [toTerm_update tuple coordinate (tuple coordinate), Function.update_eq_self,
      toTerm_update tuple coordinate value, Grounding.groundAtom_of_ground,
      Grounding.groundAtom_of_ground] at one
    exact one

/-- **An interpretation respects the rules exactly when rewriting an argument
never changes membership.** -/
theorem respects_iff_rewriteInvariant (rules : Set (Equation σ))
    (interpretation : Interpretation σ) :
    Respects rules interpretation ↔ RewriteInvariant rules interpretation :=
  ⟨fun respects atom position replacement rewrite grounding =>
      rewrite_groundAtom_iff respects atom position replacement rewrite grounding,
    RewriteInvariant.respects⟩

end FirstOrderRewriting

end Mettapedia.Logic.LP
