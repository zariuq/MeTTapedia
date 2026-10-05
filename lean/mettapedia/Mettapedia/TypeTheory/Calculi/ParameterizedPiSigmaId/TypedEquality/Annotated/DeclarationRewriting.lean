import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationLists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeExtension
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantRenaming

/-!
# The rewriting of a package with a list of declarations

A list of declarations (`DeclarationLists.lean`) extends a package by root steps of three
kinds: the computation rules of the recursor of each datatype, and the equations of each
definition, by structural recursion or explicit. This module proves what these steps look
like, that they never overlap, and that the rewriting is Church–Rosser.

**The left sides.** Every equation of a definition has on its left the defined constant
applied to arguments (`Definition.equation_head`): an explicit definition applies it to its
variables (`explicitEquation_left_erase`), a definition by recursion to a constructor applied
to its fields, followed by the later arguments (`laterEquation_left_erase`).

**Root shape.** A root step of the package with the list (`rulesWith_step_iff`) is a root
step of the package, a computation rule of the recursor of a datatype of the list, or an
instance of an equation of a definition of the list. So every root step starts at a spine of
a constant that computes (`rulesWith_rootStep_shape`): a computing constant of the package,
the recursor of a datatype of the list with a constructor of that datatype as its last
argument, or a defined constant at an instance of one of its equations
(`EquationInstance`). A spine of any other constant takes no root step
(`rulesWith_rootStep_not_head`); in an admissible list, a root step at a spine of a defined
constant is an instance of one of its own equations (`AdmissibleDeclarations.rootStep_defined`).

**No overlap.** Admissibility makes the names a list declares new: the recursors and the
defined constants of the list are distinct (`AdmissibleDeclarations.computingNames_nodup`,
`AdmissibleDeclarations.definition_name_unique`), no constructor of a datatype of the list is
one of them (`AdmissibleDeclarations.ctor_not_computingName`), and none is declared in the
package itself. A definition by recursion has one equation for each constructor of its
datatype, whose constructor names are distinct. So two equations of definitions of the list
apply at one term only when they are one equation at one instance
(`AdmissibleDeclarations.equation_unique`), and when the package's own computation is a
definition by constructor patterns that speaks only of declared names (`NamesDeclared`), the
root steps of the package with the list are deterministic
(`AdmissibleDeclarations.root_deterministic`).

**Each declaration as a case tree.** A datatype's recursor splits its last argument over the
constructors (`Datatype.caseTree`), a definition by recursion splits its first argument
(`RecursiveDefinition.caseTree`), and an explicit definition is one leaf
(`ExplicitDefinition.caseTree`). Each computes exactly by the steps of its declaration
(`Datatype.step_iff`, `RecursiveDefinition.step_iff`, `ExplicitDefinition.step_iff`), so the
package with the list computes exactly as the package extended by these case trees
(`AdmissibleDeclarations.step_iff`).

**Confluence.** The case trees of an admissible list meet the leaf conditions
(`AdmissibleDeclarations.leafConditions`) and are kept apart from the package's equations
(`AdmissibleDeclarations.apart`), so the extension is a constructor system and is
Church–Rosser. Church–Rosser depends only on the head equality and the root steps
(`ConversionCoherence.churchRosser_of_steps`, through `StepCore.root_mono`), so the rewriting of
the package with the list is Church–Rosser (`AdmissibleDeclarations.churchRosser`). This needs
every explicit definition of the list to take an argument (`ExplicitArguments`): an explicit
definition without arguments, `c ⟶ t`, has a bare constant as its left side, and the complete
development of constructor systems is proved for left sides that apply their constant to at
least one argument. That a package speaks only of declared names is checked on a test that
every constant of each left side passes (`ConstructorSystem.mentionsConst_allConstants`).

Positive examples: the empty list is admissible over every package, and its rewriting is the
package's own; over the object package, the program of the two reversals of a list is an
admissible list whose rewriting is Church–Rosser by this theorem. Negative examples: a list with two definitions `f x ⟶ a` and `f x ⟶ b` of one
name is not admissible (`twice_not_admissible`), and over a package that computes nothing its
rewriting is not Church–Rosser: `f x` reaches `a` and `b`, which take no step
(`twice_not_churchRosser`). A definition by recursion with two equations for one constructor
and different right sides, `g (k x) ⟶ A` and `g (k x) ⟶ B`, exists only over a datatype that
lists `k` twice (`overlapping_steps`), and admissibility rejects it
(`overlapping_not_admissible`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-! ## Steps over a larger root computation -/

/-- A step over a root computation is a step over every root computation with more root
steps. -/
theorem StepCore.root_mono {root root' : RootComputation Head} {headEq : Head → Head → Prop}
    (sub : ∀ {n : Nat} {t u : Tm Head n}, root.step t u → root'.step t u) {n : Nat}
    {t u : Tm Head n} (step : StepCore root headEq t u) : StepCore root' headEq t u := by
  induction step with
  | betaPi body a => exact .betaPi body a
  | betaSigmaFst a b => exact .betaSigmaFst a b
  | betaSigmaSnd a b => exact .betaSigmaSnd a b
  | head same => exact .head same
  | root step => exact .root (sub step)
  | congPiDom _ ih => exact .congPiDom ih
  | congPiCod _ ih => exact .congPiCod ih
  | congSigmaDom _ ih => exact .congSigmaDom ih
  | congSigmaCod _ ih => exact .congSigmaCod ih
  | congIdTy _ ih => exact .congIdTy ih
  | congIdLeft _ ih => exact .congIdLeft ih
  | congIdRight _ ih => exact .congIdRight ih
  | congLam _ ih => exact .congLam ih
  | congAppFun _ ih => exact .congAppFun ih
  | congAppArg _ ih => exact .congAppArg ih
  | congPairFst _ ih => exact .congPairFst ih
  | congPairSnd _ ih => exact .congPairSnd ih
  | congFst _ ih => exact .congFst ih
  | congSnd _ ih => exact .congSnd ih
  | congRefl _ ih => exact .congRefl ih

namespace ConstructorSystem

/-- A constant that occurs in a term passes every test that all the constants of the term
pass. -/
theorem mentionsConst_allConstants {p : DeclName → Bool} {c : DeclName} {n : Nat}
    (t : Tm Head n) : mentionsConst c t = true → t.allConstants p = true → p c = true := by
  induction t with
  | var => intro mentioned; cases mentioned
  | head => intro mentioned; cases mentioned
  | const name =>
      intro mentioned all
      simp only [mentionsConst, beq_iff_eq] at mentioned
      subst mentioned
      exact all
  | pi A B ihA ihB | sigma A B ihA ihB | app A B ihA ihB | pair A B ihA ihB =>
      intro mentioned all
      simp only [mentionsConst, Bool.or_eq_true] at mentioned
      simp only [Tm.allConstants, Bool.and_eq_true] at all
      exact mentioned.elim (ihA · all.1) (ihB · all.2)
  | id A a b ihA iha ihb =>
      intro mentioned all
      simp only [mentionsConst, Bool.or_eq_true] at mentioned
      simp only [Tm.allConstants, Bool.and_eq_true] at all
      rcases mentioned with (inA | ina) | inb
      · exact ihA inA all.1.1
      · exact iha ina all.1.2
      · exact ihb inb all.2
  | lam body ih | fst body ih | snd body ih | refl body ih =>
      intro mentioned all
      exact ih mentioned all

end ConstructorSystem

namespace ConversionCoherence

/-- **Church–Rosser depends only on the head equality and the root steps**: two packages
with one head equality and the same root steps are Church–Rosser together. -/
theorem churchRosser_of_steps {R₁ R₂ : Rules Head} (headEq : R₁.headEq = R₂.headEq)
    (steps : ∀ {n : Nat} {t u : Tm Head n},
      R₁.computation.step t u ↔ R₂.computation.step t u)
    (churchRosser : ChurchRosser R₂) : ChurchRosser R₁ := by
  have forward : ∀ {n : Nat} (t u : Tm Head n),
      StepCore R₁.computation R₁.headEq t u → StepCore R₂.computation R₂.headEq t u :=
    fun _ _ step => headEq ▸ StepCore.root_mono steps.mp step
  have backward : ∀ {n : Nat} (t u : Tm Head n),
      StepCore R₂.computation R₂.headEq t u → StepCore R₁.computation R₁.headEq t u :=
    fun _ _ step => headEq ▸ StepCore.root_mono steps.mpr step
  intro n left right conv
  obtain ⟨common, toLeft, toRight⟩ :=
    churchRosser (Relation.EqvGen.mono (fun a b step => forward a b step) _ _ conv)
  exact ⟨common, Relation.ReflTransGen.mono (fun a b step => backward a b step) _ _ toLeft,
    Relation.ReflTransGen.mono (fun a b step => backward a b step) _ _ toRight⟩

end ConversionCoherence

namespace TypedEquality
namespace Normalization

/-! ## Patterns -/

/-- Renaming commutes with filling patterns. -/
theorem Pat.terms_rename {n m : Nat} (ρ : Ren n m) (ps : List Pat) (values : List (Tm Head n)) :
    (Pat.terms ps values).map (Presentation.rename ρ) =
      Pat.terms ps (values.map (Presentation.rename ρ)) :=
  Pat.fillAll_map (fun c xs => rename_appSpine ρ (.const c) xs) rfl ps values

/-- The variables of two lists of patterns, one list after the other. -/
theorem Pat.varsAll_append : ∀ ps qs : List Pat,
    Pat.varsAll (ps ++ qs) = Pat.varsAll ps + Pat.varsAll qs
  | [], _ => by simp
  | p :: ps, qs => by
      simp only [List.cons_append, Pat.varsAll_cons, Pat.varsAll_append ps qs]
      omega

/-- A constructor applied to `fields` variables, then `later` variables, filled with values:
the constructor applied to the first values, then the remaining values. -/
theorem Pat.terms_con_vars {n : Nat} (k : DeclName) (fields later : Nat)
    (values : List (Tm Head n)) (length : values.length = fields + later) :
    Pat.terms (.con k (List.replicate fields .var) :: List.replicate later .var) values =
      appSpine (.const k) (values.take fields) :: values.drop fields := by
  have front := Pat.fillAll_replicate (fun c args => appSpine (.const c) args) defaultTm
    (values.take fields)
  have back := Pat.fillAll_replicate (fun c args => appSpine (.const c) args) defaultTm
    (values.drop fields)
  rw [List.length_take_of_le (by omega)] at front
  rw [List.length_drop, show values.length - fields = later by omega] at back
  simp only [Pat.terms, Pat.fillAll, Pat.fill, Pat.vars_con, Pat.varsAll_replicate]
  rw [front, back]

/-! ## Case trees -/

/-- A leaf over `vars` variables is scoped at every number equal to it. -/
theorem CaseTree.scoped_leaf {vars k : Nat} (rhs : Tm Head vars) (same : vars = k) :
    (CaseTree.leaf vars rhs).Scoped k := by
  subst same
  exact .leaf rhs

/-- The root steps of case-tree definitions, one definition at a time. -/
theorem caseTreeComputation_cons {d : CaseTreeDefinition Head}
    {defs : List (CaseTreeDefinition Head)} {n : Nat} {t u : Tm Head n} :
    (caseTreeComputation (d :: defs)).step t u ↔
      d.tree.Step d.name d.arity t u ∨ (caseTreeComputation defs).step t u := by
  constructor
  · rintro ⟨x, member, step⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact .inl step
    · exact .inr ⟨x, member, step⟩
  · rintro (step | ⟨x, member, step⟩)
    · exact ⟨d, List.mem_cons_self, step⟩
    · exact ⟨x, List.mem_cons_of_mem _ member, step⟩

end Normalization

namespace Annotated

open Normalization
open Normalization.CaseTreeExtension (extend Apart)
open ConstructorSystem (ConstructorPresentation mentionsConst spineHead spineHead_appSpine_const
  computation_head)
open ConversionCoherence (ChurchRosser StepStar)

/-! ## Telescopes and the variables of a scope -/

namespace CTele

/-- A telescope from `n` variables ends at no fewer. -/
theorem le : ∀ {n m : Nat}, CTele Head n m → n ≤ m
  | _, _, .nil => Nat.le_refl _
  | _, _, .cons _ rest => Nat.le_of_succ_le (le rest)

/-- Started at `k` variables, a telescope from `n` to `m` variables ends at `k + m - n`. -/
theorem endAt_add : ∀ {n m : Nat} (tele : CTele Head n m) (k : Nat), tele.endAt k + n = k + m
  | _, _, .nil, _ => rfl
  | _, _, .cons _ rest, k => by
      have shifted := endAt_add rest (k + 1)
      show rest.endAt (k + 1) + _ = _
      omega

/-- **The η-body of a constant spine is a constant spine**: when a term erases to the constant
`f` applied to a neighbourhood filled with the variables, its η-body along a telescope erases
to `f` applied to the neighbourhood followed by one variable for each entry, filled with the
variables of the extended scope. -/
theorem etaBody_erase {f : DeclName} : ∀ {n m : Nat} (tele : CTele Head n m) {h : CTm Head n}
    {N : List Pat}, Pat.varsAll N = n →
      h.erase = appSpine (.const f) (Pat.terms N (varTerms n)) →
        (tele.etaBody h).erase =
          appSpine (.const f) (Pat.terms (N ++ List.replicate (m - n) .var) (varTerms m))
  | _, _, .nil, _, _, _, erased => by
      rw [Nat.sub_self, List.replicate_zero, List.append_nil]
      exact erased
  | n, m, .cons _ rest, h, N, vars, erased => by
      have bound := rest.le
      have split : Pat.terms (N ++ [.var]) (varTerms (n + 1)) =
          (Pat.terms N (varTerms n)).map (Presentation.rename wk) ++ [.var 0] :=
        (Pat.fillAll_append (fun (c : DeclName) (args : List (Tm Head (n + 1))) =>
          appSpine (.const c) args) defaultTm N [.var]
          ((varTerms n).map (Presentation.rename wk)) [.var 0]
          (by rw [List.length_map, varTerms_length, vars])).trans
          (congrArg (· ++ [.var 0]) (Pat.terms_rename wk N (varTerms n)).symm)
      have next : (CTm.app (h.rename wk) (.var 0)).erase =
          appSpine (.const f) (Pat.terms (N ++ [.var]) (varTerms (n + 1))) := by
        rw [split, appSpine_concat]
        show Tm.app (CTm.rename wk h).erase (.var 0) = _
        rw [CTm.erase_rename, erased, rename_appSpine]
        rfl
      have inner := etaBody_erase rest (h := .app (h.rename wk) (.var 0)) (N := N ++ [.var])
        (by rw [Pat.varsAll_append, vars]; rfl) next
      show (rest.etaBody (.app (h.rename wk) (.var 0))).erase = _
      rw [inner, List.append_assoc, show m - n = m - (n + 1) + 1 by omega, List.replicate_succ]
      rfl

end CTele

/-- The metavariables of a schema, oldest first, are the variables of a case tree's leaf. -/
theorem metaVars_eq_varTerms (N : Nat) : metaVars (Head := Head) N = varTerms N := by
  have identity : ∀ i, listSub N (varTerms N) i = (Presentation.ids i : Tm Head N) := by
    intro i
    have recovered := valueSub_map_varTerms (Presentation.ids : Sub Head N N) i
    rw [List.map_id'' Presentation.subst_ids] at recovered
    exact recovered
  have fixed : ∀ t : Tm Head N, Presentation.subst (listSub N (varTerms N)) t = t :=
    fun t => (Presentation.subst_ext identity t).trans (Presentation.subst_ids t)
  calc metaVars N = (metaVars N).map (Presentation.subst (listSub N (varTerms N))) := by
        rw [List.map_id'' fixed]
    _ = varTerms N := map_listSub_metaVars (varTerms N) (varTerms_length N)

/-! ## The left sides of the equations -/

/-- **The equation of an explicit definition** has on its left the defined constant applied
to the variables of the arguments. -/
theorem explicitEquation_left_erase (f : DeclName) {m : Nat} (Ξ : CTele Head 0 m)
    (body : CTm Head m) :
    (explicitEquation f Ξ body).left.erase =
      appSpine (.const f) (varTerms (explicitEquation f Ξ body).arity) := by
  have spine := Ξ.etaBody_erase (f := f) (h := .const f) (N := []) rfl rfl
  have filled := Pat.terms_replicate (varTerms (Head := Head) m)
  rw [varTerms_length] at filled
  rw [List.nil_append, Nat.sub_zero, filled] at spine
  exact spine

section Recursion

variable (f T : DeclName) {m : Nat} (Ξ : CTele Head 1 m) (k : DeclName)
  (fields : List (Field Head))
  (body : CTm Head (Ξ.endAt (fields.length + (recPositions fields).length)))

/-- The written equation of a constructor is over the fields and the later arguments: one
variable fewer than the fields and the arguments of the function. -/
theorem laterEquation_arity :
    (laterEquation f T Ξ k fields body).arity + 1 = fields.length + m := by
  have outer := (laterTele Ξ k fields).endAt_add fields.length
  have inner := Ξ.endAt_add (fields.length + (recPositions fields).length)
  show (laterTele Ξ k fields).endAt fields.length + 1 = _
  omega

/-- The written equation of a constructor has at least its fields as variables. -/
theorem laterEquation_fields_le :
    fields.length ≤ (laterEquation f T Ξ k fields body).arity :=
  (writtenTele f Ξ k fields).le

/-- **The written equation of a constructor** has on its left the defined constant applied to
the constructor at the first variables, the fields, and then to the later arguments. -/
theorem laterEquation_left_erase :
    (laterEquation f T Ξ k fields body).left.erase =
      appSpine (.const f)
        (appSpine (.const k)
            ((varTerms (laterEquation f T Ξ k fields body).arity).take fields.length) ::
          (varTerms (laterEquation f T Ξ k fields body).arity).drop fields.length) := by
  have bound := (writtenTele f Ξ k fields).le
  have head : (CTm.app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length))) :
      CTm Head fields.length).erase =
      appSpine (.const f)
        (Pat.terms [.con k (List.replicate fields.length .var)] (varTerms fields.length)) := by
    have filled := Pat.terms_con_vars k fields.length 0 (varTerms (Head := Head) fields.length)
      (by simp)
    rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)] at filled
    show Tm.app (.const f) (liftTm (appSpine (.const k) (metaVars (Head := Head)
        fields.length))).erase =
      appSpine (.const f) (Pat.terms (.con k (List.replicate fields.length .var) ::
        List.replicate 0 .var) (varTerms fields.length))
    rw [filled, erase_liftTm, metaVars_eq_varTerms]
    rfl
  have spine := (writtenTele f Ξ k fields).etaBody_erase
    (h := .app (.const f) (liftTm (appSpine (.const k) (metaVars fields.length))))
    (N := [.con k (List.replicate fields.length .var)])
    (by simp [Pat.varsAll_replicate]) head
  rw [List.singleton_append, Pat.terms_con_vars k fields.length _ _
    (by rw [varTerms_length]; omega)] at spine
  exact spine

/-- An instance of the written equation of a constructor: the defined constant applied to the
constructor at the first values, the fields, and then to the remaining values. -/
theorem laterEquation_instance {n : Nat}
    (σ : Sub Head (laterEquation f T Ξ k fields body).arity n) :
    Presentation.subst σ (laterEquation f T Ξ k fields body).left.erase =
      appSpine (.const f)
        (appSpine (.const k)
            (((varTerms (laterEquation f T Ξ k fields body).arity).map
              (Presentation.subst σ)).take fields.length) ::
          ((varTerms (laterEquation f T Ξ k fields body).arity).map
            (Presentation.subst σ)).drop fields.length) := by
  rw [laterEquation_left_erase, subst_appSpine, List.map_cons, subst_appSpine, List.map_take,
    List.map_drop]
  rfl

end Recursion

/-- **Every equation of a definition is headed by the defined constant.** -/
theorem Definition.equation_head : ∀ (D : Definition Head) {e : DefiningEquation Head},
    e ∈ D.equations → ∃ args, e.left.erase = appSpine (.const D.name) args
  | .recursive _, _, member => by
      obtain ⟨_, k, fields, -, rfl⟩ := mem_laterEquations member
      exact ⟨_, laterEquation_left_erase ..⟩
  | .explicit _, _, member => by
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, explicitEquation_left_erase ..⟩

/-- `t` is an instance of the left side of an equation of `D`. -/
def EquationInstance (D : Definition Head) {n : Nat} (t : Tm Head n) : Prop :=
  ∃ e ∈ D.equations, ∃ σ : Sub Head e.arity n, t = Presentation.subst σ e.left.erase

/-- An instance of an equation of a definition is a spine of the defined constant. -/
theorem EquationInstance.head {D : Definition Head} {n : Nat} {t : Tm Head n}
    (instance_ : EquationInstance D t) : ∃ args, t = appSpine (.const D.name) args := by
  obtain ⟨e, member, σ, rfl⟩ := instance_
  obtain ⟨args, erased⟩ := D.equation_head member
  exact ⟨args.map (Presentation.subst σ), by rw [erased, subst_appSpine]; rfl⟩

/-! ## The root steps of a package with declarations -/

variable {R : Rules Head}

/-- The head equality of a package with declarations is the package's. -/
theorem rulesWith_headEq : ∀ ds : List (Declaration Head), (rulesWith R ds).headEq = R.headEq
  | [] => rfl
  | .datatype _ :: ds => rulesWith_headEq ds
  | .definition _ :: ds => rulesWith_headEq ds

/-- **The root steps of a package with declarations**: the package's own, the computation
rules of the recursors of the datatypes of the list, and the instances of the equations of the
definitions of the list. -/
theorem rulesWith_step_iff {n : Nat} {t u : Tm Head n} : ∀ {ds : List (Declaration Head)},
    (rulesWith R ds).computation.step t u ↔ R.computation.step t u ∨
      (∃ d, Declaration.datatype d ∈ ds ∧ IotaStep d.recursor d.ctors t u) ∨
      ∃ D, Declaration.definition D ∈ ds ∧ (erasedComputation D.equations).step t u
  | [] => ⟨.inl, fun step => step.elim id fun rest => rest.elim
      (fun ⟨_, member, _⟩ => nomatch member) fun ⟨_, member, _⟩ => nomatch member⟩
  | .datatype d :: ds => by
      show (rulesWith R ds).computation.step t u ∨ IotaStep d.recursor d.ctors t u ↔ _
      rw [rulesWith_step_iff]
      constructor
      · rintro ((base | ⟨d', member, iota⟩ | ⟨D, member, step⟩) | iota)
        · exact .inl base
        · exact .inr (.inl ⟨d', List.mem_cons_of_mem _ member, iota⟩)
        · exact .inr (.inr ⟨D, List.mem_cons_of_mem _ member, step⟩)
        · exact .inr (.inl ⟨d, List.mem_cons_self, iota⟩)
      · rintro (base | ⟨d', member, iota⟩ | ⟨D, member, step⟩)
        · exact .inl (.inl base)
        · rcases List.mem_cons.mp member with same | member
          · cases same
            exact .inr iota
          · exact .inl (.inr (.inl ⟨d', member, iota⟩))
        · rcases List.mem_cons.mp member with same | member
          · cases same
          · exact .inl (.inr (.inr ⟨D, member, step⟩))
  | .definition D :: ds => by
      show (rulesWith R ds).computation.step t u ∨ (erasedComputation D.equations).step t u ↔ _
      rw [rulesWith_step_iff]
      constructor
      · rintro ((base | ⟨d, member, iota⟩ | ⟨D', member, step⟩) | step)
        · exact .inl base
        · exact .inr (.inl ⟨d, List.mem_cons_of_mem _ member, iota⟩)
        · exact .inr (.inr ⟨D', List.mem_cons_of_mem _ member, step⟩)
        · exact .inr (.inr ⟨D, List.mem_cons_self, step⟩)
      · rintro (base | ⟨d, member, iota⟩ | ⟨D', member, step⟩)
        · exact .inl (.inl base)
        · rcases List.mem_cons.mp member with same | member
          · cases same
          · exact .inl (.inr (.inl ⟨d, member, iota⟩))
        · rcases List.mem_cons.mp member with same | member
          · cases same
            exact .inr step
          · exact .inl (.inr (.inr ⟨D', member, step⟩))

/-- **Root shape**: every root step of a package with declarations starts at a spine of a
constant that computes: a computing constant of the package, the recursor of a datatype of
the list with a constructor of the datatype as its last argument, or a defined constant of the
list at an instance of one of its equations. -/
theorem rulesWith_rootStep_shape {roles : Roles Head} (shape : RootShape R roles)
    {ds : List (Declaration Head)} {n : Nat} {t u : Tm Head n}
    (step : (rulesWith R ds).computation.step t u) :
    ∃ c args, t = appSpine (.const c) args ∧
      ((∃ arity inspect, roles c = .computes arity inspect) ∨
        (∃ d, Declaration.datatype d ∈ ds ∧ c = d.recursor ∧
          ∃ (before : List (Tm Head n)) (k : DeclName) (fields : List (Field Head))
            (xs : List (Tm Head n)),
            (k, fields) ∈ d.ctors ∧ args = before ++ [appSpine (.const k) xs]) ∨
        ∃ D, Declaration.definition D ∈ ds ∧ c = D.name ∧ EquationInstance D t) := by
  rcases rulesWith_step_iff.mp step with
    base | ⟨d, member, iota⟩ | ⟨D, member, e, equation, σ, rfl, -⟩
  · obtain ⟨c, arity, inspect, args, role, rfl, -, -⟩ := shape.spine base
    exact ⟨c, args, rfl, .inl ⟨arity, inspect, role⟩⟩
  · obtain ⟨p, ms, i, k, fields, xs, -, -, entry, -, -, rfl, -⟩ := iota
    exact ⟨d.recursor, _, rfl,
      .inr (.inl ⟨d, member, rfl, p :: ms, k, fields, xs, List.mem_of_getElem? entry, rfl⟩)⟩
  · obtain ⟨args, head⟩ := EquationInstance.head ⟨e, equation, σ, rfl⟩
    exact ⟨D.name, args, head, .inr (.inr ⟨D, member, rfl, e, equation, σ, rfl⟩)⟩

/-- **A spine of a constant that computes nowhere takes no root step**: neither in the
package, nor as the recursor of a datatype of the list, nor as a defined constant of the
list. -/
theorem rulesWith_rootStep_not_head {roles : Roles Head} (shape : RootShape R roles)
    {ds : List (Declaration Head)} {c : DeclName}
    (notComputing : ∀ arity inspect, roles c ≠ .computes arity inspect)
    (notRecursor : ∀ d, Declaration.datatype d ∈ ds → c ≠ d.recursor)
    (notDefined : ∀ D, Declaration.definition D ∈ ds → c ≠ D.name) {n : Nat}
    (args : List (Tm Head n)) (u : Tm Head n) :
    ¬ (rulesWith R ds).computation.step (appSpine (.const c) args) u := by
  intro step
  obtain ⟨c', args', same, object | ⟨d, member, rfl, -⟩ | ⟨D, member, rfl, -⟩⟩ :=
    rulesWith_rootStep_shape shape step
  all_goals obtain ⟨rfl, -⟩ := appSpine_const_injective same
  · obtain ⟨arity, inspect, role⟩ := object
    exact notComputing arity inspect role
  · exact notRecursor d member rfl
  · exact notDefined D member rfl

/-! ## The names an admissible list declares -/

/-- The name a declaration computes by: the recursor of a datatype, the defined constant of a
definition. -/
def Declaration.computingName : Declaration Head → DeclName
  | .datatype d => d.recursor
  | .definition D => D.name

variable {B : ChurchRules R}

/-- A name new to the package with some declarations is not declared in the package. -/
theorem undeclared_of_new (post : List (Declaration Head)) {c : DeclName}
    (new : (withDeclarations B post).constantType c = none) : R.constantType c = none := by
  rw [← B.erase_constantType c]
  cases declared : B.constantType c with
  | none => rfl
  | some _ =>
      rw [(withDeclarations_base B post).constantType declared] at new
      cases new

/-- The name a declaration of an admissible list computes by is declared in the package of
the list. -/
theorem AdmissibleDeclarations.computingName_declared {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {e : Declaration Head} (member : e ∈ ds) :
    (withDeclarations B ds).constantType e.computingName ≠ none := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  cases e with
  | datatype d =>
      have stage := admissible.datatype_split.2
      show (withDeclarations B (pre ++ .datatype d :: post)).constantType d.recursor ≠ none
      rw [(withDeclarations_sub B (.datatype d :: post) pre).constantType
        (sum_rec_declared (u := d.typeUniverse) (v := d.motiveUniverse) (withDeclarations B post)
          stage.distinct stage.lamFree stage.new)]
      exact Option.some_ne_none _
  | definition D =>
      rw [Declaration.computingName, admissible.definition_declared member]
      exact Option.some_ne_none _

/-- A constructor of a datatype of an admissible list is declared in the package of the
list. -/
theorem AdmissibleDeclarations.ctor_declared {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {d : Datatype Head}
    (member : Declaration.datatype d ∈ ds) {k : DeclName} (named : k ∈ d.ctors.map Prod.fst) :
    (withDeclarations B ds).constantType k ≠ none := by
  obtain ⟨⟨k', fields⟩, entry, rfl⟩ := List.mem_map.mp named
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp entry
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  have stage := admissible.datatype_split.2
  rw [(withDeclarations_sub B (.datatype d :: post) pre).constantType
    (sum_ctor_declared (u := d.typeUniverse) (v := d.motiveUniverse) (withDeclarations B post)
      stage.distinct stage.lamFree stage.new found)]
  exact Option.some_ne_none _

/-- The name the last declaration of an admissible list computes by is new to the package of
the declarations before it. -/
theorem AdmissibleDeclarations.computingName_new {e : Declaration Head}
    {post : List (Declaration Head)} (admissible : AdmissibleDeclarations B (e :: post)) :
    (withDeclarations B post).constantType e.computingName = none := by
  cases e with
  | datatype d => exact admissible.2.new.recNew
  | definition D => exact admissible.2.new

/-- **The names the declarations of an admissible list compute by are distinct.** -/
theorem AdmissibleDeclarations.computingNames_nodup :
    ∀ {ds : List (Declaration Head)}, AdmissibleDeclarations B ds →
      (ds.map Declaration.computingName).Nodup
  | [], _ => List.nodup_nil
  | _ :: _, admissible => by
      refine List.nodup_cons.mpr ⟨fun mem => ?_, computingNames_nodup admissible.tail⟩
      obtain ⟨e', member, same⟩ := List.mem_map.mp mem
      exact admissible.tail.computingName_declared member
        (by rw [same]; exact admissible.computingName_new)

/-- **Two definitions of an admissible list with one name are one definition.** -/
theorem AdmissibleDeclarations.definition_name_unique {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {D D' : Definition Head}
    (member : Declaration.definition D ∈ ds) (member' : Declaration.definition D' ∈ ds)
    (same : D.name = D'.name) : D = D' := by
  have equal := List.inj_on_of_nodup_map admissible.computingNames_nodup member member' same
  cases equal
  rfl

/-- **No constructor of a datatype of an admissible list is a name a declaration of the list
computes by.** -/
theorem AdmissibleDeclarations.ctor_not_computingName :
    ∀ {ds : List (Declaration Head)}, AdmissibleDeclarations B ds →
      ∀ {d : Datatype Head}, Declaration.datatype d ∈ ds →
        ∀ {k : DeclName}, k ∈ d.ctors.map Prod.fst → k ∉ ds.map Declaration.computingName
  | [], _, _, member, _, _ => nomatch member
  | _ :: _, admissible, _, member, _, named => by
      intro mem
      rcases List.mem_cons.mp mem with same | later
      · subst same
        rcases List.mem_cons.mp member with rfl | member
        · exact admissible.2.distinct.recNotCtor named
        · exact admissible.tail.ctor_declared member named admissible.computingName_new
      · rcases List.mem_cons.mp member with rfl | member
        · obtain ⟨e', member', rfl⟩ := List.mem_map.mp later
          obtain ⟨entry, entryMember, named⟩ := List.mem_map.mp named
          exact admissible.tail.computingName_declared member'
            (by rw [← named]; exact admissible.2.new.ctorsNew entry entryMember)
        · exact ctor_not_computingName admissible.tail member named later

/-- The name a declaration of an admissible list computes by is not declared in the package
itself. -/
theorem AdmissibleDeclarations.computingName_undeclared {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {e : Declaration Head} (member : e ∈ ds) :
    R.constantType e.computingName = none := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact undeclared_of_new post
    (AdmissibleDeclarations.after (pre := pre) admissible).computingName_new

/-- A constructor of a datatype of an admissible list is not declared in the package
itself. -/
theorem AdmissibleDeclarations.ctor_undeclared {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {d : Datatype Head}
    (member : Declaration.datatype d ∈ ds) {k : DeclName} (named : k ∈ d.ctors.map Prod.fst) :
    R.constantType k = none := by
  obtain ⟨⟨k', fields⟩, entry, rfl⟩ := List.mem_map.mp named
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact undeclared_of_new post (admissible.datatype_split.2.new.ctorsNew _ entry)

/-- The constructors of a datatype of an admissible list have distinct names. -/
theorem AdmissibleDeclarations.ctors_nodup {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {d : Datatype Head}
    (member : Declaration.datatype d ∈ ds) : (d.ctors.map Prod.fst).Nodup := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact admissible.datatype_split.2.distinct.ctorsNodup

/-- The datatype of a definition by recursion of an admissible list is in the list. -/
theorem AdmissibleDeclarations.recursive_datatype {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {δ : RecursiveDefinition Head}
    (member : Declaration.definition (.recursive δ) ∈ ds) :
    Declaration.datatype δ.datatype ∈ ds := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem member
  exact List.mem_append_right pre (List.mem_cons_of_mem _ admissible.definition_split.2.1)

/-- **In an admissible list, a root step at a spine of a defined constant is an instance of
one of its equations**, when the constant computes nowhere in the package. -/
theorem AdmissibleDeclarations.rootStep_defined {roles : Roles Head} (shape : RootShape R roles)
    {ds : List (Declaration Head)} (admissible : AdmissibleDeclarations B ds)
    {D : Definition Head} (member : Declaration.definition D ∈ ds)
    (notComputing : ∀ arity inspect, roles D.name ≠ .computes arity inspect) {n : Nat}
    {args : List (Tm Head n)} {u : Tm Head n}
    (step : (rulesWith R ds).computation.step (appSpine (.const D.name) args) u) :
    EquationInstance D (appSpine (.const D.name) args) := by
  obtain ⟨c, args', same,
      object | ⟨d, member', recursor, -⟩ | ⟨D', member', name, instance_⟩⟩ :=
    rulesWith_rootStep_shape shape step
  all_goals obtain ⟨rfl, -⟩ := appSpine_const_injective same
  · obtain ⟨arity, inspect, role⟩ := object
    exact absurd role (notComputing arity inspect)
  · exact absurd (List.inj_on_of_nodup_map admissible.computingNames_nodup member member'
      recursor) nofun
  · obtain rfl := admissible.definition_name_unique member' member name.symm
    exact instance_

/-- **No overlap between the equations of an admissible list**: two equations of definitions
of the list apply at one term only when they are one equation of one definition, at one
instance. -/
theorem AdmissibleDeclarations.equation_unique {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {D D' : Definition Head}
    (member : Declaration.definition D ∈ ds) (member' : Declaration.definition D' ∈ ds)
    {e e' : DefiningEquation Head} (equation : e ∈ D.equations) (equation' : e' ∈ D'.equations)
    {n : Nat} (σ : Sub Head e.arity n) (σ' : Sub Head e'.arity n)
    (same : Presentation.subst σ e.left.erase = Presentation.subst σ' e'.left.erase) :
    D = D' ∧
      (⟨e, σ⟩ : Σ e : DefiningEquation Head, Sub Head e.arity n) = ⟨e', σ'⟩ := by
  have spines := same
  obtain ⟨args, head⟩ := D.equation_head equation
  obtain ⟨args', head'⟩ := D'.equation_head equation'
  rw [head, head', subst_appSpine, subst_appSpine] at spines
  obtain rfl := admissible.definition_name_unique member member'
    (appSpine_const_injective spines).1
  refine ⟨rfl, ?_⟩
  have values : ∀ {a : Nat} (σ τ : Sub Head a n),
      (varTerms a).map (Presentation.subst σ) = (varTerms a).map (Presentation.subst τ) →
        σ = τ := fun σ τ equal => funext fun i => by
    rw [← valueSub_map_varTerms σ i, ← valueSub_map_varTerms τ i, equal]
  cases D with
  | explicit ε =>
      obtain rfl := List.mem_singleton.mp equation
      obtain rfl := List.mem_singleton.mp equation'
      rw [explicitEquation_left_erase, subst_appSpine, subst_appSpine] at same
      obtain rfl := values σ σ' (appSpine_const_injective same).2
      rfl
  | recursive δ =>
      obtain ⟨i, k, fields, entry, rfl⟩ := mem_laterEquations equation
      obtain ⟨i', k', fields', entry', rfl⟩ := mem_laterEquations equation'
      rw [laterEquation_instance, laterEquation_instance] at same
      obtain ⟨heads, rests⟩ := List.cons.inj (appSpine_const_injective same).2
      obtain ⟨rfl, fieldsSame⟩ := appSpine_const_injective heads
      have nodup := admissible.ctors_nodup (admissible.recursive_datatype member)
      have names : (δ.datatype.ctors.map Prod.fst)[i]? = some k := by simp [entry]
      have names' : (δ.datatype.ctors.map Prod.fst)[i']? = some k := by simp [entry']
      obtain rfl := nodup_getElem?_inj nodup names names'
      rw [entry] at entry'
      obtain rfl := (Prod.mk.inj (Option.some.inj entry')).2
      have whole := congrArg₂ (· ++ ·) fieldsSame rests
      simp only [List.take_append_drop] at whole
      obtain rfl := values σ σ' whole
      rfl

/-! ## Each declaration as a case-tree definition -/

/-- The branches of a split over constructors: for each constructor, its number of fields and
the tree given for it at its index, counted from `start`. -/
def ctorBranches (tree : Nat → DeclName → List (Field Head) → CaseTree Head) :
    Nat → List (DeclName × List (Field Head)) → CaseBranches Head
  | _, [] => .nil
  | start, (k, fields) :: rest =>
      .cons k fields.length (tree start k fields) (ctorBranches tree (start + 1) rest)

/-- A constructor found among the branches is listed, with the tree given for it. -/
theorem ctorBranches_find {tree : Nat → DeclName → List (Field Head) → CaseTree Head} :
    ∀ {start : Nat} {ctors : List (DeclName × List (Field Head))} {k : DeclName} {count : Nat}
      {found : CaseTree Head}, (ctorBranches tree start ctors).find k = some (count, found) →
        ∃ i fields, ctors[i]? = some (k, fields) ∧ count = fields.length ∧
          found = tree (start + i) k fields
  | _, [], _, _, _, found => by simp [ctorBranches, CaseBranches.find] at found
  | start, (k', fields') :: rest, k, count, found, lookup => by
      simp only [ctorBranches, CaseBranches.find] at lookup
      split at lookup
      · next same =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj lookup)
          subst same
          exact ⟨0, fields', rfl, rfl, rfl⟩
      · obtain ⟨i, fields, entry, rfl, rfl⟩ := ctorBranches_find lookup
        exact ⟨i + 1, fields, by rw [List.getElem?_cons_succ]; exact entry, rfl,
          by rw [show start + 1 + i = start + (i + 1) by omega]⟩

/-- A listed constructor is found among the branches, when the names are distinct. -/
theorem find_ctorBranches {tree : Nat → DeclName → List (Field Head) → CaseTree Head} :
    ∀ {start : Nat} {ctors : List (DeclName × List (Field Head))},
      (ctors.map Prod.fst).Nodup → ∀ {i : Nat} {k : DeclName} {fields : List (Field Head)},
        ctors[i]? = some (k, fields) →
          (ctorBranches tree start ctors).find k = some (fields.length, tree (start + i) k fields)
  | _, [], _, _, _, _, entry => by simp at entry
  | start, (k', fields') :: rest, nodup, i, k, fields, entry => by
      simp only [ctorBranches, CaseBranches.find]
      cases i with
      | zero =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj entry)
          rw [if_pos rfl]
          rfl
      | succ i =>
          rw [List.getElem?_cons_succ] at entry
          have distinct := List.nodup_cons.mp nodup
          have notHead : k ≠ k' := by
            rintro rfl
            exact distinct.1 (List.mem_map.mpr ⟨(k, fields), List.mem_of_getElem? entry, rfl⟩)
          rw [if_neg notHead, find_ctorBranches distinct.2 entry,
            show start + 1 + i = start + (i + 1) by omega]

/-- The branches are scoped when the tree of each constructor is. -/
theorem ctorBranches_scoped {tree : Nat → DeclName → List (Field Head) → CaseTree Head}
    {vars : Nat} : ∀ {start : Nat} {ctors : List (DeclName × List (Field Head))},
      (∀ i k fields, (k, fields) ∈ ctors →
        (tree i k fields).Scoped (vars - 1 + fields.length)) →
        (ctorBranches tree start ctors).Scoped vars
  | _, [], _ => .nil
  | start, (k, fields) :: _, inScope =>
      .cons (inScope start k fields List.mem_cons_self)
        (ctorBranches_scoped fun i k' fields' member =>
          inScope i k' fields' (List.mem_cons_of_mem _ member))

/-- Over leaves, the branches split on the listed constructors. -/
theorem ctorBranches_constructors {tree : Nat → DeclName → List (Field Head) → CaseTree Head}
    (leaves : ∀ i k fields, (tree i k fields).constructors = []) :
    ∀ {start : Nat} (ctors : List (DeclName × List (Field Head))),
      (ctorBranches tree start ctors).constructors = ctors.map Prod.fst
  | _, [] => rfl
  | _, (k, fields) :: rest => by
      simp only [ctorBranches, CaseBranches.constructors, leaves, List.nil_append, List.map_cons,
        ctorBranches_constructors leaves rest]

/-- **The case tree of a datatype's recursor**: it splits its last argument over the
constructors, and the leaf of the constructor at index `i` is the right side of its
computation rule. -/
def Datatype.caseTree (d : Datatype Head) : CaseTreeDefinition Head where
  name := d.recursor
  arity := 1 + d.ctors.length + 1
  tree := .split (1 + d.ctors.length) d.type
    (ctorBranches (fun i _ fields => .leaf _ (iotaRight d.recursor d.ctors.length i fields)) 0
      d.ctors)

/-- The written equation of a constructor of a definition by recursion is over the fields and
the later arguments. -/
theorem RecursiveDefinition.equation_arity (δ : RecursiveDefinition Head) (k : DeclName)
    (fields : List (Field Head)) :
    (laterEquation δ.name δ.datatype.type δ.later k fields (δ.body k fields)).arity =
      δ.width - 1 + fields.length := by
  have arity := laterEquation_arity δ.name δ.datatype.type δ.later k fields (δ.body k fields)
  have positive := δ.later.le
  omega

/-- **The case tree of a definition by recursion**: it splits its first argument over the
constructors of its datatype, and the leaf of a constructor is the right side of its written
equation. -/
def RecursiveDefinition.caseTree (δ : RecursiveDefinition Head) : CaseTreeDefinition Head where
  name := δ.name
  arity := δ.width
  tree := .split 0 δ.datatype.type
    (ctorBranches (fun _ k fields => .leaf _
      (laterEquation δ.name δ.datatype.type δ.later k fields (δ.body k fields)).right.erase)
      0 δ.datatype.ctors)

/-- **The case tree of an explicit definition**: one leaf, the body. -/
def ExplicitDefinition.caseTree (ε : ExplicitDefinition Head) : CaseTreeDefinition Head where
  name := ε.name
  arity := ε.width
  tree := .leaf _ (explicitEquation ε.name ε.arguments ε.body).right.erase

/-- The case tree of a declaration. -/
def Declaration.caseTree : Declaration Head → CaseTreeDefinition Head
  | .datatype d => d.caseTree
  | .definition (.recursive δ) => δ.caseTree
  | .definition (.explicit ε) => ε.caseTree

/-- The case tree of a declaration is named by the name the declaration computes by. -/
theorem Declaration.caseTree_name : ∀ e : Declaration Head, e.caseTree.name = e.computingName
  | .datatype _ => rfl
  | .definition (.recursive _) => rfl
  | .definition (.explicit _) => rfl

/-! ## Each case tree computes by its declaration -/

/-- The right side of the computation rule of the constructor at index `i`, at the motive, the
methods and the fields. -/
theorem iotaRight_values (rec : DeclName) (c i : Nat) (fields : List (Field Head)) {n : Nat}
    (p : Tm Head n) (ms xs : List (Tm Head n)) (methods : ms.length = c)
    (arguments : xs.length = fields.length) :
    Presentation.subst (valueSub (1 + c + fields.length) (p :: ms ++ xs))
        (iotaRight rec c i fields) =
      appSpine ((p :: ms).getD (1 + i) defaultTm)
        (xs ++ (recArgs fields xs).map (recApp rec (p :: ms))) := by
  have length : (p :: ms ++ xs).length = 1 + c + fields.length := by
    simp [methods, arguments]
    omega
  have values : (metaVars (1 + c + fields.length)).map
      (Presentation.subst (valueSub (1 + c + fields.length) (p :: ms ++ xs))) = p :: ms ++ xs :=
    map_listSub_metaVars _ length
  have front : (p :: ms ++ xs).take (1 + c) = p :: ms := by
    rw [List.cons_append, Nat.add_comm, List.take_succ_cons, List.take_left' methods]
  have back : (p :: ms ++ xs).drop (1 + c) = xs := by
    rw [List.cons_append, Nat.add_comm, List.drop_succ_cons, List.drop_left' methods]
  rw [subst_iotaRight, values, front, back]

/-- **The tree of a recursor computes by its computation rules**, when its constructors have
distinct names. -/
theorem Datatype.step_iff (d : Datatype Head) (nodup : (d.ctors.map Prod.fst).Nodup) {n : Nat}
    {t u : Tm Head n} :
    IotaStep d.recursor d.ctors t u ↔
      d.caseTree.tree.Step d.caseTree.name d.caseTree.arity t u := by
  constructor
  · rintro ⟨p, ms, i, k, fields, xs, m, methods, entry, arguments, method, rfl, rfl⟩
    refine ⟨p :: ms ++ [appSpine (.const k) xs], rfl, ?_, ?_⟩
    · simp only [Datatype.caseTree, List.length_append, List.length_cons, List.length_nil,
        methods]
      omega
    have found : (ctorBranches (fun i _ fields => CaseTree.leaf _
        (iotaRight d.recursor d.ctors.length i fields)) 0 d.ctors).find k =
          some (xs.length, CaseTree.leaf _ (iotaRight d.recursor d.ctors.length i fields)) := by
      rw [find_ctorBranches nodup entry, arguments, Nat.zero_add]
    have method' : (p :: ms).getD (1 + i) defaultTm = m := by
      rw [show 1 + i = i + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem?_getD, method]
      rfl
    have leaf := CaseTree.Eval.leaf (iotaRight d.recursor d.ctors.length i fields)
      (values := p :: ms ++ xs) (by simp [methods, arguments]; omega)
    rw [iotaRight_values _ _ _ _ p ms xs methods arguments, method'] at leaf
    refine .split (before := p :: ms) (after := []) (by simp [methods]; omega) found ?_
    rw [List.append_nil]
    exact leaf
  · rintro ⟨args, rfl, length, eval⟩
    cases eval with
    | @split _ _ _ before after xs k found' _ lengthBefore lookup inner =>
        obtain ⟨i, fields, entry, arguments, rfl⟩ := ctorBranches_find lookup
        simp only [Datatype.caseTree, List.length_append, List.length_cons] at length
        obtain rfl : after = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨p, ms, rfl⟩ : ∃ p ms, before = p :: ms := by
          cases before with
          | nil =>
              simp only [List.length_nil] at lengthBefore
              omega
          | cons p ms => exact ⟨p, ms, rfl⟩
        have methods : ms.length = d.ctors.length := by
          simp only [List.length_cons] at lengthBefore
          omega
        have below : i < ms.length := by
          rw [methods]
          exact (List.getElem?_eq_some_iff.mp entry).1
        rw [List.append_nil] at inner
        cases inner with
        | leaf _ _ =>
            refine ⟨p, ms, i, k, fields, xs, ms[i], methods, entry, arguments,
              List.getElem?_eq_getElem below, rfl, ?_⟩
            rw [Nat.zero_add, iotaRight_values _ _ _ _ p ms xs methods arguments,
              show 1 + i = i + 1 by omega, List.getD_cons_succ, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem below]
            rfl

/-- **The tree of a definition by recursion computes by its written equations**, when the
constructors of its datatype have distinct names. -/
theorem RecursiveDefinition.step_iff (δ : RecursiveDefinition Head)
    (nodup : (δ.datatype.ctors.map Prod.fst).Nodup) {n : Nat} {t u : Tm Head n} :
    (erasedComputation (Definition.recursive δ).equations).step t u ↔
      δ.caseTree.tree.Step δ.caseTree.name δ.caseTree.arity t u := by
  constructor
  · rintro ⟨e, member, σ, rfl, rfl⟩
    obtain ⟨i, k, fields, entry, rfl⟩ := mem_laterEquations member
    have arity := laterEquation_arity δ.name δ.datatype.type δ.later k fields (δ.body k fields)
    have bound :=
      laterEquation_fields_le δ.name δ.datatype.type δ.later k fields (δ.body k fields)
    have length : ((varTerms (laterEquation δ.name δ.datatype.type δ.later k fields
        (δ.body k fields)).arity).map (Presentation.subst σ)).length =
          (laterEquation δ.name δ.datatype.type δ.later k fields (δ.body k fields)).arity := by
      simp
    refine ⟨_, laterEquation_instance δ.name δ.datatype.type δ.later k fields
      (δ.body k fields) σ, ?_, ?_⟩
    · simp only [List.length_cons, List.length_drop, length, RecursiveDefinition.caseTree]
      omega
    have found : (ctorBranches (fun _ k fields => CaseTree.leaf _ (laterEquation δ.name
        δ.datatype.type δ.later k fields (δ.body k fields)).right.erase) 0
          δ.datatype.ctors).find k =
        some ((((varTerms (laterEquation δ.name δ.datatype.type δ.later k fields
          (δ.body k fields)).arity).map (Presentation.subst σ)).take fields.length).length,
          CaseTree.leaf _ (laterEquation δ.name δ.datatype.type δ.later k fields
            (δ.body k fields)).right.erase) := by
      rw [find_ctorBranches nodup entry, List.length_take_of_le (by rw [length]; exact bound)]
    have leaf := CaseTree.Eval.leaf (laterEquation δ.name δ.datatype.type δ.later k fields
      (δ.body k fields)).right.erase length
    rw [Presentation.subst_ext (valueSub_map_varTerms σ)] at leaf
    refine .split (before := []) rfl found ?_
    rw [List.nil_append, List.take_append_drop]
    exact leaf
  · rintro ⟨args, rfl, length, eval⟩
    cases eval with
    | @split _ _ _ before after xs k found' _ lengthBefore lookup inner =>
        obtain rfl := List.eq_nil_of_length_eq_zero lengthBefore
        obtain ⟨i, fields, entry, arguments, rfl⟩ := ctorBranches_find lookup
        rw [List.nil_append] at inner
        cases inner with
        | leaf _ valuesLength =>
            refine ⟨_, List.mem_map.mpr ⟨(k, fields), List.mem_of_getElem? entry, rfl⟩,
              valueSub _ (xs ++ after), ?_, rfl⟩
            rw [laterEquation_instance, varTerms_map_valueSub valuesLength,
              List.take_left' arguments, List.drop_left' arguments]
            rfl

/-- **The tree of an explicit definition computes by its equation.** -/
theorem ExplicitDefinition.step_iff (ε : ExplicitDefinition Head) {n : Nat} {t u : Tm Head n} :
    (erasedComputation (Definition.explicit ε).equations).step t u ↔
      ε.caseTree.tree.Step ε.caseTree.name ε.caseTree.arity t u := by
  constructor
  · rintro ⟨e, member, σ, rfl, rfl⟩
    obtain rfl := List.mem_singleton.mp member
    have length : ((varTerms (explicitEquation ε.name ε.arguments ε.body).arity).map
        (Presentation.subst σ)).length =
          (explicitEquation ε.name ε.arguments ε.body).arity := by
      simp
    refine ⟨(varTerms (explicitEquation ε.name ε.arguments ε.body).arity).map
      (Presentation.subst σ), ?_, length, ?_⟩
    · rw [explicitEquation_left_erase, subst_appSpine]
      rfl
    · have leaf := CaseTree.Eval.leaf (explicitEquation ε.name ε.arguments ε.body).right.erase
        length
      rw [Presentation.subst_ext (valueSub_map_varTerms σ)] at leaf
      exact leaf
  · rintro ⟨args, rfl, length, eval⟩
    cases eval with
    | leaf _ valuesLength =>
        refine ⟨_, List.mem_singleton_self _, valueSub _ args, ?_, rfl⟩
        rw [explicitEquation_left_erase, subst_appSpine, varTerms_map_valueSub valuesLength]
        rfl

/-- **The package with an admissible list computes exactly as the package extended by the case
trees of the list.** -/
theorem AdmissibleDeclarations.step_iff :
    ∀ {ds : List (Declaration Head)}, AdmissibleDeclarations B ds →
      ∀ {n : Nat} {t u : Tm Head n},
      (rulesWith R ds).computation.step t u ↔
        (extend R (ds.map Declaration.caseTree)).computation.step t u
  | [], _, _, _, _ => ⟨.inl, fun step => step.elim id fun ⟨_, member, _⟩ => nomatch member⟩
  | .datatype d :: _, admissible, _, _, _ =>
      (or_congr (step_iff admissible.tail) (d.step_iff admissible.2.distinct.ctorsNodup)).trans
        (or_assoc.trans (or_congr_right (or_comm.trans caseTreeComputation_cons.symm)))
  | .definition (.recursive δ) :: _, admissible, _, _, _ =>
      (or_congr (step_iff admissible.tail)
        (δ.step_iff (admissible.tail.ctors_nodup admissible.2.1))).trans
        (or_assoc.trans (or_congr_right (or_comm.trans caseTreeComputation_cons.symm)))
  | .definition (.explicit ε) :: _, admissible, _, _, _ =>
      (or_congr (step_iff admissible.tail) ε.step_iff).trans
        (or_assoc.trans (or_congr_right (or_comm.trans caseTreeComputation_cons.symm)))

/-! ## Church–Rosser -/

/-- **A package whose computation is a definition by constructor patterns over declared
names**: every defined name of the presentation, and every constant of a left side of one of
its equations, is declared in the package. -/
structure NamesDeclared (equations : ConstructorPresentation R) : Prop where
  defined : ∀ {c : DeclName}, equations.system.defined c → R.constantType c ≠ none
  left : ∀ {m : Nat} {left right : Tm Head m}, equations.system.schema left right →
    ∀ {c : DeclName}, mentionsConst c left = true → R.constantType c ≠ none

/-- Every explicit definition of the list takes at least one argument. -/
def ExplicitArguments (ds : List (Declaration Head)) : Prop :=
  ∀ ε : ExplicitDefinition Head, Declaration.definition (.explicit ε) ∈ ds → 0 < ε.width

/-- The constructors a case tree of an admissible list splits on are constructors of a
datatype of the list. -/
theorem AdmissibleDeclarations.caseTree_constructor {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) {e : Declaration Head} (member : e ∈ ds)
    {c : DeclName} (split : c ∈ e.caseTree.tree.constructors) :
    ∃ d, Declaration.datatype d ∈ ds ∧ c ∈ d.ctors.map Prod.fst := by
  match e, member, split with
  | .datatype d, member, split =>
      have listed : (Declaration.caseTree (.datatype d)).tree.constructors =
          d.ctors.map Prod.fst :=
        ctorBranches_constructors (fun _ _ _ => by rfl) d.ctors
      exact ⟨d, member, listed ▸ split⟩
  | .definition (.recursive δ), member, split =>
      have listed : (Declaration.caseTree (.definition (.recursive δ))).tree.constructors =
          δ.datatype.ctors.map Prod.fst :=
        ctorBranches_constructors (fun _ _ _ => by rfl) δ.datatype.ctors
      exact ⟨δ.datatype, admissible.recursive_datatype member, listed ▸ split⟩
  | .definition (.explicit _), _, split => nomatch split

/-- The names of the case trees of a list are the names its declarations compute by. -/
theorem Declaration.caseTree_names (ds : List (Declaration Head)) :
    (ds.map Declaration.caseTree).map CaseTreeDefinition.name =
      ds.map Declaration.computingName := by
  rw [List.map_map]
  exact List.map_congr_left fun e _ => e.caseTree_name

/-- **The case trees of an admissible list meet the leaf conditions**, when its explicit
definitions take arguments. -/
theorem AdmissibleDeclarations.leafConditions {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) (arguments : ExplicitArguments ds) :
    LeafConditions (ds.map Declaration.caseTree) where
  names := by
    rw [Declaration.caseTree_names ds]
    exact admissible.computingNames_nodup
  arity_pos := by
    intro _ member
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    match e, listed with
    | .datatype _, _ => exact Nat.succ_pos _
    | .definition (.recursive δ), _ => exact δ.later.le
    | .definition (.explicit ε), listed => exact arguments ε listed
  inScope := by
    intro _ member
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    match e with
    | .datatype d =>
        exact .split (by show 1 + d.ctors.length < 1 + d.ctors.length + 1; omega)
          (ctorBranches_scoped fun _ _ _ _ => .leaf _)
    | .definition (.recursive δ) =>
        refine .split (by show 0 < δ.width; exact δ.later.le) (ctorBranches_scoped ?_)
        intro _ k fields _
        exact CaseTree.scoped_leaf _ (δ.equation_arity k fields)
    | .definition (.explicit ε) => exact .leaf _
  constructors := by
    intro _ member c split
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    obtain ⟨d, datatype, named⟩ := admissible.caseTree_constructor listed split
    rw [Declaration.caseTree_names ds]
    exact admissible.ctor_not_computingName datatype named

/-- **The case trees of an admissible list are kept apart from the package's equations**, when
these speak only of declared names. -/
theorem AdmissibleDeclarations.apart {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) (equations : ConstructorPresentation R)
    (declared : NamesDeclared equations) :
    Apart (ds.map Declaration.caseTree) equations.system where
  names := by
    intro _ member defined
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    exact declared.defined defined
      (by rw [e.caseTree_name]; exact admissible.computingName_undeclared listed)
  constructors := by
    intro _ member c split defined
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    obtain ⟨d, datatype, named⟩ := admissible.caseTree_constructor listed split
    exact declared.defined defined (admissible.ctor_undeclared datatype named)
  absent := by
    intro _ member m left right rule
    obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
    cases mentioned : mentionsConst e.caseTree.name left with
    | false => rfl
    | true =>
        exact absurd (by rw [e.caseTree_name]; exact admissible.computingName_undeclared listed)
          (declared.left rule mentioned)

/-- **Confluence**: over a package whose computation is a definition by constructor patterns
over declared names, the rewriting of the package with an admissible list of declarations,
whose explicit definitions take arguments, is Church–Rosser. -/
theorem AdmissibleDeclarations.churchRosser {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) (equations : ConstructorPresentation R)
    (declared : NamesDeclared equations) (arguments : ExplicitArguments ds) :
    ChurchRosser (rulesWith R ds) :=
  ConversionCoherence.churchRosser_of_steps (R₂ := extend R (ds.map Declaration.caseTree))
    (rulesWith_headEq (R := R) ds) admissible.step_iff
    (CaseTreeExtension.extend_churchRosser equations (admissible.leafConditions arguments)
      (admissible.apart equations declared))

/-- A root step of the package and a root step of a case tree of an admissible list never
start at one term. -/
theorem AdmissibleDeclarations.base_tree_apart {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) (equations : ConstructorPresentation R)
    (declared : NamesDeclared equations) {n : Nat} {t u u' : Tm Head n}
    (base : R.computation.step t u)
    (tree : (caseTreeComputation (ds.map Declaration.caseTree)).step t u') : False := by
  obtain ⟨name, count, defined, head⟩ := computation_head equations base
  obtain ⟨_, member, args, rfl, -, -⟩ := tree
  obtain ⟨e, listed, rfl⟩ := List.mem_map.mp member
  rw [spineHead_appSpine_const] at head
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj head)
  exact declared.defined defined
    (by rw [e.caseTree_name]; exact admissible.computingName_undeclared listed)

/-- **Root steps are deterministic** in the package with an admissible list, over a package
whose computation is a definition by constructor patterns over declared names. -/
theorem AdmissibleDeclarations.root_deterministic {ds : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B ds) (equations : ConstructorPresentation R)
    (declared : NamesDeclared equations) {n : Nat} {t u u' : Tm Head n}
    (step : (rulesWith R ds).computation.step t u)
    (step' : (rulesWith R ds).computation.step t u') : u = u' := by
  rcases (admissible.step_iff).mp step with base | tree <;>
    rcases (admissible.step_iff).mp step' with base' | tree'
  · exact ConstructorSystem.root_deterministic equations base base'
  · exact (admissible.base_tree_apart equations declared base tree').elim
  · exact (admissible.base_tree_apart equations declared base' tree).elim
  · have names := admissible.computingNames_nodup
    rw [← Declaration.caseTree_names ds] at names
    exact (caseTreeComputation_deterministic names tree tree').symm

/-! ## Controls -/

namespace DeclarationRewritingControls

/-- `f x ⟶ c`: an explicit definition of `f`, with one argument, whose body is the constant
`c`. -/
def constantly (c : DeclName) : ExplicitDefinition Head where
  name := `f
  width := 1
  arguments := .cons (.const `A) .nil
  result := .const `A
  body := .const c

/-- Two definitions of one name: `f x ⟶ a`, then `f x ⟶ b`. -/
abbrev twice : List (Declaration Head) :=
  [.definition (.explicit (constantly `b)), .definition (.explicit (constantly `a))]

/-- **A list with two definitions of one name is not admissible.** -/
theorem twice_not_admissible (B : ChurchRules R) :
    ¬ AdmissibleDeclarations B (twice (Head := Head)) := by
  intro admissible
  have nodup := admissible.computingNames_nodup
  simp [Declaration.computingName, Definition.name, constantly] at nodup

/-- `f x` steps to `c` by the definition `f x ⟶ c` of the list. -/
theorem twice_step (c : DeclName) (listed : c = `a ∨ c = `b) :
    (rulesWith R (twice (Head := Head))).computation.step (.app (.const `f) (.var 0) : Tm Head 1)
      (.const c) := by
  rcases listed with rfl | rfl
  · exact .inl (.inr ⟨_, List.mem_singleton_self _, fun i => .var i, rfl, rfl⟩)
  · exact .inr ⟨_, List.mem_singleton_self _, fun i => .var i, rfl, rfl⟩

/-- A constant takes no step, when the package computes nothing. -/
theorem constant_normal (quiet : ∀ {n : Nat} {t u : Tm Head n}, ¬ R.computation.step t u)
    (c : DeclName) {u : Tm Head 1} :
    ¬ StepCore (rulesWith R (twice (Head := Head))).computation
      (rulesWith R (twice (Head := Head))).headEq (.const c) u := by
  intro step
  cases step with
  | root root =>
      rcases root with (base | ⟨_, member, _, same, -⟩) | ⟨_, member, _, same, -⟩
      · exact quiet base
      all_goals
        obtain rfl := List.mem_singleton.mp member
        cases same

/-- **The rewriting of the list with two definitions of one name is not Church–Rosser**, over
a package that computes nothing: `f x` reaches `a` and `b`, which take no step. -/
theorem twice_not_churchRosser
    (quiet : ∀ {n : Nat} {t u : Tm Head n}, ¬ R.computation.step t u) :
    ¬ ChurchRosser (rulesWith R (twice (Head := Head))) := by
  intro churchRosser
  have conv : Conv (rulesWith R (twice (Head := Head))).headEq (.const `a : Tm Head 1) (.const `b)
      (rulesWith R (twice (Head := Head))).computation :=
    .trans _ _ _ (.symm _ _ (.rel _ _ (.root (twice_step `a (.inl rfl)))))
      (.rel _ _ (.root (twice_step `b (.inr rfl))))
  obtain ⟨common, toA, toB⟩ := churchRosser conv
  have stays : ∀ (c : DeclName) {common : Tm Head 1},
      StepStar (rulesWith R (twice (Head := Head))) (.const c) common → common = .const c := by
    intro c common steps
    induction steps with
    | refl => rfl
    | tail _ step ih =>
        subst ih
        exact absurd step (constant_normal quiet c)
  have same := (stays `a toA).symm.trans (stays `b toB)
  simp at same

/-- A datatype that lists the constructor `k` twice, with a field of type `A` and with a field
of type `B`. -/
def twiceListed (u : Head) : Datatype Head where
  type := `T
  typeUniverse := u
  ctors := [(`k, [.closed (.const `A)]), (`k, [.closed (.const `B)])]
  recursor := `T.rec
  motiveUniverse := u

/-- The name of a single closed field type that is a constant. -/
def fieldName : List (Field Head) → DeclName
  | [.closed (.const c)] => c
  | _ => .anonymous

/-- `g (k x) ⟶ A` and `g (k x) ⟶ B`: a definition by recursion over `twiceListed`, whose right
side at a constructor is the name of its field type. -/
def overlapping (u : Head) : RecursiveDefinition Head where
  name := `g
  datatype := twiceListed u
  width := 1
  later := .nil
  result := .const `C
  body := fun _ fields => .const (fieldName fields)

/-- **Two equations for one constructor with different right sides**: `g (k x)` steps to `A`
and to `B`. -/
theorem overlapping_steps (u : Head) (c : DeclName) (listed : c = `A ∨ c = `B) :
    (erasedComputation (Definition.recursive (overlapping u)).equations).step
      (.app (.const `g) (.app (.const `k) (.var 0)) : Tm Head 1) (.const c) := by
  rcases listed with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun i => .var i, rfl, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun i => .var i, rfl, rfl⟩

/-- **Admissibility rejects the overlapping definition**: its datatype lists one constructor
twice, so no admissible list has it. -/
theorem overlapping_not_admissible (B : ChurchRules R) (u : Head) (ds : List (Declaration Head)) :
    ¬ AdmissibleDeclarations B (.definition (.recursive (overlapping u)) :: ds) := by
  intro admissible
  have nodup := admissible.ctors_nodup (admissible.recursive_datatype List.mem_cons_self)
  simp [overlapping, twiceListed] at nodup

end DeclarationRewritingControls

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
