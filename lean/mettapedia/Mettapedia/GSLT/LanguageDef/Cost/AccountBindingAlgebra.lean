import Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution
import Mettapedia.CategoryTheory.WriterActionTransport
import Mettapedia.OSLF.Syntax.SecondOrderBindingAlgebraMap
import Mettapedia.OSLF.Syntax.RhoSourceEquationModel
import Mettapedia.OSLF.Syntax.LambdaContextualRung

/-!
# Account actions on complete observed binding clones

Objects retain every sort, context, binding operator and simultaneous
substitution of a binding clone, together with a clone morphism to an
independently specified source algebra.  Account atoms are source values;
their substitution is the actual source clone substitution.  An action can
mark values inside binding arguments without extracting their effects from
the binder.

The forgetful functor discards only the account action.  The fixed-context
comparison is an actual object and functor into the previously constructed
slice of actions.  Neither a free binding account construction nor the
authored Cost transformer is asserted here.  Encoding a LanguageDef's
equations in the chosen source algebra remains a separate comparison.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt)

/-- A full binding clone over the source observation, equipped with coherent
source-account actions at every context and output sort.  The carrier keeps
all of its marked elements when the action operation is forgotten. -/
structure Model where
  observed : Over Q
  act : {Γ : Ctx S} → {sort : S.Srt} →
    SourceAccountSubstitution.Account Q accountSort Γ →
    observed.left.substitution.Carrier Γ sort →
    observed.left.substitution.Carrier Γ sort
  act_one : ∀ {Γ : Ctx S} {sort : S.Srt}
    (value : observed.left.substitution.Carrier Γ sort), act 1 value = value
  act_mul : ∀ {Γ : Ctx S} {sort : S.Srt}
    (first second : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : observed.left.substitution.Carrier Γ sort),
    act (first * second) value = act first (act second value)
  observe_act : ∀ {Γ : Ctx S} {sort : S.Srt}
    (account : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : observed.left.substitution.Carrier Γ sort),
    observed.hom.raw.map (act account value) = observed.hom.raw.map value
  act_substitute : ∀ {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S observed.left.substitution.Carrier Γ Δ)
    (account : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : observed.left.substitution.Carrier Γ sort),
    observed.left.substitution.substitute env (act account value) =
      act (SourceAccountSubstitution.substitute Q accountSort
        (fun s v => observed.hom.raw.map (env s v)) account)
        (observed.left.substitution.substitute env value)

/-- Maps preserve the entire binding clone and source observation, as well
as every context-indexed account action. -/
structure Hom (A B : Model Q accountSort) where
  underlying : A.observed ⟶ B.observed
  map_act : ∀ {Γ : Ctx S} {sort : S.Srt}
    (account : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : A.observed.left.substitution.Carrier Γ sort),
    underlying.left.raw.map (A.act account value) =
      B.act account (underlying.left.raw.map value)

namespace Hom

@[ext] theorem ext {A B : Model Q accountSort} {f g : Hom Q accountSort A B}
    (same : f.underlying = g.underlying) : f = g := by
  cases f
  cases g
  cases same
  rfl

def id (A : Model Q accountSort) : Hom Q accountSort A A where
  underlying := 𝟙 A.observed
  map_act := by intro Γ sort account value; rfl

def comp {A B C : Model Q accountSort}
    (f : Hom Q accountSort A B) (g : Hom Q accountSort B C) :
    Hom Q accountSort A C where
  underlying := f.underlying ≫ g.underlying
  map_act := by
    intro Γ sort account value
    change g.underlying.left.raw.map (f.underlying.left.raw.map (A.act account value)) =
      C.act account (g.underlying.left.raw.map (f.underlying.left.raw.map value))
    exact (congrArg g.underlying.left.raw.map (f.map_act account value)).trans
      (g.map_act account (f.underlying.left.raw.map value))

end Hom

instance modelCategory : Category (Model Q accountSort) where
  Hom := Hom Q accountSort
  id := Hom.id Q accountSort
  comp := Hom.comp Q accountSort
  id_comp := by intro A B f; apply Hom.ext; exact Category.id_comp _
  comp_id := by intro A B f; apply Hom.ext; exact Category.comp_id _
  assoc := by intro A B C D f g h; apply Hom.ext; exact Category.assoc _ _ _

/-- Discard only the action operation, retaining the complete clone, all
marked values and the observation morphism. -/
def forget : Model Q accountSort ⥤ Over Q where
  obj A := A.observed
  map f := f.underlying

instance forget_faithful : (forget Q accountSort).Faithful where
  map_injective := fun same => Hom.ext Q accountSort same

/-- Pure action on an arbitrary observed clone.  This supplies a comparison
object, not the free account construction. -/
def pure (A : Over Q) : Model Q accountSort where
  observed := A
  act := fun _ value => value
  act_one := fun _ => rfl
  act_mul := fun _ _ _ => rfl
  observe_act := fun _ _ => rfl
  act_substitute := fun _ _ _ => rfl

/-- A genuine full-clone morphism over the source becomes a map between
the pure comparison objects. -/
def pureFunctor : Over Q ⥤ Model Q accountSort where
  obj := pure Q accountSort
  map f := { underlying := f, map_act := fun _ _ => rfl }
  map_id := fun _ => by apply Hom.ext; rfl
  map_comp := fun _ _ => by apply Hom.ext; rfl

theorem pure_forget : pureFunctor Q accountSort ⋙ forget Q accountSort = 𝟭 (Over Q) := rfl

/-- Evaluate a full source-observed clone at a selected context and sort. -/
def evaluate (Γ : Ctx S) (sort : S.Srt) : Over Q ⥤ Over
    (Q.substitution.Carrier Γ sort) where
  obj A := Over.mk (TypeCat.ofHom A.hom.raw.map)
  map f := Over.homMk (TypeCat.ofHom f.left.raw.map) (by
    apply ConcreteCategory.ext_apply
    intro value
    exact congrArg (fun h : FreeBindingClone.Hom _ _ => h.raw.map value) (Over.w f))
  map_id := fun _ => by apply Over.OverMorphism.ext; rfl
  map_comp := fun _ _ => by apply Over.OverMorphism.ext; rfl

/-- The account action on a fibre is an actual Mathlib action. -/
def fibreAction (A : Model Q accountSort) (Γ : Ctx S) (sort : S.Srt) :
    Action (Type u) (SourceAccountSubstitution.Account Q accountSort Γ) where
  V := A.observed.left.substitution.Carrier Γ sort
  ρ :=
    { toFun := fun account => TypeCat.ofHom (A.act account)
      map_one' := by
        apply End.ext
        apply ConcreteCategory.ext_apply
        intro value
        exact A.act_one value
      map_mul' := by
        intro first second
        apply End.ext
        apply ConcreteCategory.ext_apply
        intro value
        exact A.act_mul first second value }

/-- Observation invariance supplies an equivariant map to the source fibre
with its trivial action. -/
def fibreObservation (A : Model Q accountSort) (Γ : Ctx S) (sort : S.Srt) :
    fibreAction Q accountSort A Γ sort ⟶
      Action.trivial (SourceAccountSubstitution.Account Q accountSort Γ)
        (Q.substitution.Carrier Γ sort) where
  hom := TypeCat.ofHom A.observed.hom.raw.map
  comm := fun account => by
    apply ConcreteCategory.ext_apply
    intro value
    exact A.observe_act account value

/-- The selected fibre comparison respects all maps of accounted binding
clones; it does not discard marked elements under binders. -/
def fibre (Γ : Ctx S) (sort : S.Srt) : Model Q accountSort ⥤
    Over (Action.trivial (SourceAccountSubstitution.Account Q accountSort Γ)
      (Q.substitution.Carrier Γ sort)) where
  obj A := Over.mk (fibreObservation Q accountSort A Γ sort)
  map f := Over.homMk
    { hom := TypeCat.ofHom f.underlying.left.raw.map
      comm := fun account => by
        apply ConcreteCategory.ext_apply
        intro value
        exact f.map_act account value }
    (by
      apply Action.Hom.ext
      apply ConcreteCategory.ext_apply
      intro value
      exact congrArg (fun h : FreeBindingClone.Hom _ _ => h.raw.map value)
        (Over.w f.underlying))
  map_id := fun _ => by apply Over.OverMorphism.ext; apply Action.Hom.ext; rfl
  map_comp := fun _ _ => by apply Over.OverMorphism.ext; apply Action.Hom.ext; rfl

/-- The two forgetful comparisons retain the same source-observed fibre. -/
theorem fibre_forget (Γ : Ctx S) (sort : S.Srt) :
    fibre Q accountSort Γ sort ⋙
      Mettapedia.CategoryTheory.WriterActionSlice.forget
        (SourceAccountSubstitution.Account Q accountSort Γ)
        (Q.substitution.Carrier Γ sort) =
      forget Q accountSort ⋙ evaluate Q Γ sort := rfl

/-- Observe every supplied substitution value through the actual source
clone morphism.  This includes marked values, not only source syntax. -/
def sourceEnvironment (A : Model Q accountSort) {Γ Δ : Ctx S}
    (env : Environment S A.observed.left.substitution.Carrier Γ Δ) :
    Environment S Q.substitution.Carrier Γ Δ :=
  fun sort v => A.observed.hom.raw.map (env sort v)

def accountSubstitution (A : Model Q accountSort) {Γ Δ : Ctx S}
    (env : Environment S A.observed.left.substitution.Carrier Γ Δ) :
    SourceAccountSubstitution.Account Q accountSort Γ →*
      SourceAccountSubstitution.Account Q accountSort Δ :=
  SourceAccountSubstitution.substitute Q accountSort
    (sourceEnvironment Q accountSort A env)

theorem accountSubstitution_identity (A : Model Q accountSort) {Γ : Ctx S} :
    accountSubstitution Q accountSort A
        (fun _ v => A.observed.left.substitution.injectVar v) =
      MonoidHom.id (SourceAccountSubstitution.Account Q accountSort Γ) := by
  have sourceIdentity : sourceEnvironment Q accountSort A (Γ := Γ) (Δ := Γ)
      (fun _ v => A.observed.left.substitution.injectVar v) =
        (fun _ v => Q.substitution.injectVar v) := by
    funext sort v
    exact A.observed.hom.raw.map_variable v
  unfold accountSubstitution
  rw [sourceIdentity]
  exact SourceAccountSubstitution.substitute_identity Q accountSort

theorem accountSubstitution_comp (A : Model Q accountSort) {Γ Δ Θ : Ctx S}
    (first : Environment S A.observed.left.substitution.Carrier Γ Δ)
    (second : Environment S A.observed.left.substitution.Carrier Δ Θ) :
    (accountSubstitution Q accountSort A second).comp
        (accountSubstitution Q accountSort A first) =
      accountSubstitution Q accountSort A
        (fun sort v => A.observed.left.substitution.substitute second (first sort v)) := by
  unfold accountSubstitution
  rw [SourceAccountSubstitution.substitute_comp]
  congr 1
  funext sort v
  exact (A.observed.hom.map_substitute second (first sort v)).symm

/-- Actual substitution is equivariant after restricting target scalars
along its derived source-account substitution homomorphism. -/
def fibreSubstitution (A : Model Q accountSort) {Γ Δ : Ctx S} (sort : S.Srt)
    (env : Environment S A.observed.left.substitution.Carrier Γ Δ) :
    fibreAction Q accountSort A Γ sort ⟶
      (Action.res (Type u) (accountSubstitution Q accountSort A env)).obj
        (fibreAction Q accountSort A Δ sort) where
  hom := TypeCat.ofHom (A.observed.left.substitution.substitute env)
  comm := fun account => by
    apply ConcreteCategory.ext_apply
    intro value
    exact A.act_substitute env account value

/-- The semilinear substitution map also transports the full source
observation through the actual source substitution, yielding a typed map
between the appropriately reindexed action slices. -/
def fibreSubstitutionObserved (A : Model Q accountSort) {Γ Δ : Ctx S}
    (sort : S.Srt) (env : Environment S A.observed.left.substitution.Carrier Γ Δ) :
    (Over.map
      (Mettapedia.CategoryTheory.WriterActionTransport.observationMap
        (M := SourceAccountSubstitution.Account Q accountSort Γ)
        (Q.substitution.substitute (sourceEnvironment Q accountSort A env)))).obj
      ((fibre Q accountSort Γ sort).obj A) ⟶
    (Over.post (Action.res (Type u) (accountSubstitution Q accountSort A env))).obj
      ((fibre Q accountSort Δ sort).obj A) :=
  Over.homMk (fibreSubstitution Q accountSort A sort env) (by
    apply Action.Hom.ext
    apply ConcreteCategory.ext_apply
    intro value
    exact A.observed.hom.map_substitute env value)

theorem fibreSubstitution_identity_apply (A : Model Q accountSort) {Γ : Ctx S}
    (sort : S.Srt) (value : A.observed.left.substitution.Carrier Γ sort) :
    (fibreSubstitution Q accountSort A sort
      (fun _ v => A.observed.left.substitution.injectVar v)).hom value = value :=
  A.observed.left.substitution.substitute_identity value

theorem fibreSubstitution_comp_apply (A : Model Q accountSort) {Γ Δ Θ : Ctx S}
    (sort : S.Srt)
    (first : Environment S A.observed.left.substitution.Carrier Γ Δ)
    (second : Environment S A.observed.left.substitution.Carrier Δ Θ)
    (value : A.observed.left.substitution.Carrier Γ sort) :
    (fibreSubstitution Q accountSort A sort second).hom
        ((fibreSubstitution Q accountSort A sort first).hom value) =
      (fibreSubstitution Q accountSort A sort
        (fun s v => A.observed.left.substitution.substitute second (first s v))).hom value :=
  A.observed.left.substitution.substitute_comp first second value

namespace OccurrenceMarker

open FreeBindingTerms
open SecondOrderContext

variable {M : List (MetaArity S)}

/-- Instantiation into the original signature commutes with the actual
capture-avoiding binder lift. -/
theorem instantiate_liftSub
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {Γ Δ : Ctx S} (env : Sub (withMetas S M) Γ Δ) :
    ∀ (binders : List S.Srt) (sort : S.Srt) (v : Var (binders ++ Γ) sort),
      instantiate body (liftSub env binders sort v) =
        liftSub (fun s w => instantiate body (env s w)) binders sort v
  | [], _, _ => rfl
  | _ :: binders, _, .zero => rfl
  | _ :: binders, _, .succ old => by
      simp only [liftSub, weaken, instantiate_rename,
        instantiate_liftSub body env binders]

mutual

/-- Actual schema instantiation preserves full simultaneous substitution,
including binding arguments and nonempty metavariable dependencies. -/
theorem instantiate_bind
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (env : Sub (withMetas S M) Γ Δ)
      (term : Term (withMetas S M) Γ sort),
      instantiate body (bind env term) =
        bind (fun s v => instantiate body (env s v)) (instantiate body term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, env, .op (.inl op) args => by
      simp only [Mettapedia.OSLF.Binding.bind, instantiate,
        instantiateArgs_bindArgs body env args]
  | _, _, _, env, .op (.inr (.mk index)) args => by
      simp only [Mettapedia.OSLF.Binding.bind, instantiate,
        instantiateArgs_bindArgs body env args, bind_comp]
      congr 1
      funext sort v
      exact argsToSub_bindArgs _ _ _ _ _

/-- Every argument is instantiated and substituted in its own declared
binder-extended context. -/
theorem instantiateArgs_bindArgs
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (env : Sub (withMetas S M) Γ Δ)
      (args : Args (withMetas S M) arities Γ),
      instantiateArgs body (bindArgs env args) =
        bindArgs (fun s v => instantiate body (env s v)) (instantiateArgs body args)
  | _, _, _, _, .nil => rfl
  | _, _, _, env, .cons (bs := binders) head tail => by
      have lifts : (fun sort v => instantiate body (liftSub env binders sort v)) =
          liftSub (fun sort v => instantiate body (env sort v)) binders := by
        funext sort v
        exact instantiate_liftSub body env binders sort v
      simp only [bindArgs, instantiateArgs, instantiateArgs_bindArgs body env tail,
        instantiate_bind body (liftSub env binders) head, lifts]

end

theorem instantiateArgs_toSyntax (X : Object S)
    (body : (i : Fin X.arities.length) →
      Term S (X.arities.get i).1 (X.arities.get i).2) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (restrictedSubstitution X).Carrier arities Γ),
      instantiateArgs body (toSyntax X args) =
        (FreeBindingTerms.terms.familyToSyntax S)
          (FamilyArgs.map (instantiate body) args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (Args.cons (instantiate body head))
      (instantiateArgs_toSyntax X body tail)

/-- Interpreting the extra operators by actual scoped bodies gives a full
clone morphism, not merely a constructor or first-order map. -/
def instantiateHom (X : Object S)
    (body : (i : Fin X.arities.length) →
      Term S (X.arities.get i).1 (X.arities.get i).2) :
    FreeBindingClone.Hom (termAlgebra X) (BindingCloneAlgebra.terms S) where
  raw :=
    { map := instantiate body
      map_variable := by intros; rfl
      map_operation := by
        intro Γ sort op args
        exact congrArg (Term.op op) (instantiateArgs_toSyntax X body args) }
  map_substitute := by
    intro Γ Δ sort env term
    exact instantiate_bind body env term

/-- A single unary marker at the selected sort.  The original binding
signature and every original operator remain available in its carrier. -/
def context (markSort : S.Srt) : Object S := single S [markSort] markSort

def body (markSort : S.Srt) (index : Fin (context markSort).arities.length) :
    Term S ((context markSort).arities.get index).1
      ((context markSort).arities.get index).2 := by
  have zero : index = ⟨0, by simp [context, single]⟩ := Fin.ext (by
    change index.val = 0
    have bound := index.isLt
    change index.val < 1 at bound
    omega)
  subst index
  exact .var .zero

def mark (markSort : S.Srt) {Γ : Ctx S}
    (value : Term (withMetas S (context markSort).arities) Γ markSort) :
    Term (withMetas S (context markSort).arities) Γ markSort :=
  .op (.inr (.mk ⟨0, by simp [context, single]⟩)) (.cons value .nil)

theorem erase_mark (markSort : S.Srt) {Γ : Ctx S}
    (value : Term (withMetas S (context markSort).arities) Γ markSort) :
    instantiate (body markSort) (mark markSort value) =
      instantiate (body markSort) value := rfl

variable [DecidableEq S.Srt]

/-- Mark values at the selected sort and retain every other sort unchanged.
This comparison records marker multiplicity, not source-account labels. -/
def markAt (markSort : S.Srt) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (withMetas S (context markSort).arities) Γ sort) :
    Term (withMetas S (context markSort).arities) Γ sort :=
  if same : sort = markSort then same.symm ▸ mark markSort (same ▸ value) else value

theorem bind_markAt (markSort : S.Srt) {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Sub (withMetas S (context markSort).arities) Γ Δ)
    (value : Term (withMetas S (context markSort).arities) Γ sort) :
    bind env (markAt markSort value) = markAt markSort (bind env value) := by
  by_cases same : sort = markSort
  · subst sort
    simp only [markAt]
    rfl
  · simp only [markAt, dif_neg same]

theorem erase_markAt (markSort : S.Srt) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (withMetas S (context markSort).arities) Γ sort) :
    instantiate (body markSort) (markAt markSort value) =
      instantiate (body markSort) value := by
  by_cases same : sort = markSort
  · subst sort
    simpa [markAt] using erase_mark markSort value
  · simp only [markAt, dif_neg same]

theorem bind_iterate_markAt (markSort : S.Srt) {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Sub (withMetas S (context markSort).arities) Γ Δ)
    (value : Term (withMetas S (context markSort).arities) Γ sort) :
    ∀ count, bind env ((markAt markSort)^[count] value) =
      (markAt markSort)^[count] (bind env value)
  | 0 => rfl
  | count + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', bind_markAt,
        bind_iterate_markAt markSort env value count]

theorem erase_iterate_markAt (markSort : S.Srt) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (withMetas S (context markSort).arities) Γ sort) :
    ∀ count, instantiate (body markSort) ((markAt markSort)^[count] value) =
      instantiate (body markSort) value
  | 0 => rfl
  | count + 1 => by
      rw [Function.iterate_succ_apply', erase_markAt,
        erase_iterate_markAt markSort value count]

/-- The source observation erases the auxiliary markers, then interprets
the complete original term in the independently supplied source algebra. -/
def observe (source : BindingCloneAlgebra.Algebra.{0} S) (markSort : S.Srt) :
    FreeBindingClone.Hom (termAlgebra (context markSort)) source :=
  FreeBindingClone.Hom.comp (instantiateHom (context markSort) (body markSort))
    (FreeBindingClone.interpretHom source)

/-- A nontrivial accounted binding clone over any small source algebra.
Source account words act by adding their length in unary markers.  This
intentionally forgets account-label distinctions and is an inhabitance
comparison, not the authored meter or a free construction. -/
def comparison (source : BindingCloneAlgebra.Algebra.{0} S) (markSort : S.Srt) :
    Model source markSort where
  observed := Over.mk (observe source markSort)
  act := fun account value => (markAt markSort)^[account.length] value
  act_one := by intros; rfl
  act_mul := by
    intro Γ sort first second value
    change Term (withMetas S (context markSort).arities) Γ sort at value
    rw [FreeMonoid.length_mul]
    exact Function.iterate_add_apply _ _ _ _
  observe_act := by
    intro Γ sort account value
    change Term (withMetas S (context markSort).arities) Γ sort at value
    change (FreeBindingClone.interpretHom source).raw.map
        (instantiate (body markSort) ((markAt markSort)^[account.length] value)) =
      (FreeBindingClone.interpretHom source).raw.map (instantiate (body markSort) value)
    exact congrArg (FreeBindingClone.interpretHom source).raw.map
      (erase_iterate_markAt markSort value account.length)
  act_substitute := by
    intro Γ Δ sort env account value
    change Term (withMetas S (context markSort).arities) Γ sort at value
    change Sub (withMetas S (context markSort).arities) Γ Δ at env
    change bind env ((markAt markSort)^[account.length] value) =
      (markAt markSort)^[
        (SourceAccountSubstitution.substitute source markSort
          (fun s v => BindingCloneFoldSubstitution.interpret source
            (instantiate (body markSort) (env s v))) account).length]
        (bind env value)
    rw [SourceAccountSubstitution.substitute_length]
    exact bind_iterate_markAt markSort env value account.length

/-- A genuine source atom changes a genuine variable in the marked carrier;
the account action is not the identity comparison. -/
theorem comparison_nontrivial (source : BindingCloneAlgebra.Algebra.{0} S)
    (markSort : S.Srt)
    (atom : source.substitution.Carrier [markSort] markSort) :
    (comparison source markSort).act (FreeMonoid.of atom)
        (.var .zero : Term (withMetas S (context markSort).arities) [markSort] markSort) ≠
      .var .zero := by
  intro same
  change markAt markSort (Term.var Var.zero) = Term.var Var.zero at same
  simp only [markAt, dif_pos] at same
  cases same

/-- The actual fixed-fibre slice receives the full marked carrier and its
source observation, with a visibly nontrivial account action. -/
theorem comparison_fibre_nontrivial (source : BindingCloneAlgebra.Algebra.{0} S)
    (markSort : S.Srt)
    (atom : source.substitution.Carrier [markSort] markSort) :
    (((fibre source markSort [markSort] markSort).obj
      (comparison source markSort)).left.ρ (FreeMonoid.of atom))
        (Term.var Var.zero) ≠ Term.var Var.zero :=
  comparison_nontrivial source markSort atom

end OccurrenceMarker

namespace RhoSourceComparison

open RhoSchema
open OccurrenceMarker
open RhoSchema.IntrinsicEncoding

/-- The existing complete intrinsic source quotient, including ACU and
QuoteDrop.  Its authored canonical-pattern encoding is available, with its
existing binary-parallel and quote-safety comparison boundaries. -/
noncomputable abbrev source := (FreeBindingEquationModel.presented rhoSourceE).algebra

noncomputable def model : Model source Srt.pr := comparison source Srt.pr

/-- The auxiliary action category is inhabited over the actual source
equation presentation, without asserting those equations for marked values. -/
noncomputable instance : Nonempty (Model source Srt.pr) := ⟨model⟩

theorem source_equations : BindingEquationInterpretation.Satisfies source rhoSourceE :=
  (FreeBindingEquationModel.presented rhoSourceE).satisfies

theorem action_nontrivial :
    (model.act (FreeMonoid.of (source.substitution.injectVar
        (Var.zero : Var [Srt.pr] Srt.pr)))
      (Term.var Var.zero)) ≠ Term.var Var.zero :=
  comparison_nontrivial source Srt.pr _

/-- Erasure then interpretation keeps the complete original source class;
the observation is not a leaf inventory or a source-key digest. -/
theorem observe_source {Γ : Ctx sig} {sort : Srt} (term : Term sig Γ sort) :
    model.observed.hom.raw.map (embed (M := (context (S := sig) Srt.pr).arities) term) =
      (Quotient.mk _ term : TermQ rhoSourceE Γ sort) := by
  change BindingCloneFoldSubstitution.interpret source
      (instantiate (body Srt.pr) (embed term)) = _
  rw [instantiate_embed]
  exact BindingEquationQuotientModel.interpret_eq_mk rhoSourceE term

/-- Reading the existing authored canonical encoding after an account
action retains the full observed source program.  No reconstruction of
account factors or of marked syntax is claimed. -/
theorem canonical_source_observation_act {Γ : Ctx sig} {sort : Srt}
    (account : SourceAccountSubstitution.Account source Srt.pr Γ)
    (value : model.observed.left.substitution.Carrier Γ sort) :
    encodeEquationClass (model.observed.hom.raw.map (model.act account value)) =
      encodeEquationClass (model.observed.hom.raw.map value) :=
  congrArg encodeEquationClass (model.observe_act account value)

def zero {Γ : Ctx sig} : Term sig Γ Srt.pr := .op .nil .nil

def quotedZero {Γ : Ctx sig} : Term sig Γ Srt.nm := .op .quo (.cons zero .nil)

/-- A send under the input binder uses the received name twice, in its
channel and in a dropped payload. -/
def sendBody : Term sig [Srt.nm] Srt.pr :=
  .op .out (.cons (.var .zero) (.cons (.op .drp (.cons (.var .zero) .nil)) .nil))

def input : Term sig [] Srt.pr := .op .inp (.cons quotedZero (.cons sendBody .nil))

def markedSendBody : Term (withMetas sig (context (S := sig) Srt.pr).arities) [Srt.nm] Srt.pr :=
  mark (S := sig) Srt.pr (embed sendBody)

/-- The marker stays inside the declared input body; it is not moved onto
the outside of a function or input constructor. -/
def markedInput : Term (withMetas sig (context (S := sig) Srt.pr).arities) [] Srt.pr :=
  .op (.inl .inp) (.cons (embed quotedZero) (.cons markedSendBody .nil))

theorem marked_input_source :
    model.observed.hom.raw.map markedInput =
      (Quotient.mk _ input : TermQ rhoSourceE [] Srt.pr) := by
  change BindingCloneFoldSubstitution.interpret source input = _
  exact BindingEquationQuotientModel.interpret_eq_mk rhoSourceE input

/-- Actual binder elimination preserves the supplied internal marker and
substitutes both occurrences of the received name capture-avoidantly. -/
theorem marked_body_instantiation :
    bind (extend (embed (M := (context (S := sig) Srt.pr).arities)
        (quotedZero (Γ := [])))) markedSendBody =
      mark (S := sig) Srt.pr
        (bind (extend (embed (M := (context (S := sig) Srt.pr).arities)
          (quotedZero (Γ := [])))) (embed sendBody)) := rfl

/-- This comparison intentionally identifies actions with equal word length.
It cannot substitute for the meter's source-labelled ordered accounts. -/
theorem action_eq_of_length_eq {Γ : Ctx sig} {sort : Srt}
    (first second : SourceAccountSubstitution.Account source Srt.pr Γ)
    (sameLength : first.length = second.length)
    (value : model.observed.left.substitution.Carrier Γ sort) :
    model.act first value = model.act second value := by
  change (markAt (S := sig) Srt.pr)^[first.length] value = (markAt (S := sig) Srt.pr)^[second.length] value
  exact congrArg (fun count => (markAt (S := sig) Srt.pr)^[count] value) sameLength

noncomputable def firstAtom : source.substitution.Carrier [Srt.pr, Srt.pr] Srt.pr :=
  Quotient.mk _ (.var .zero : Term sig [Srt.pr, Srt.pr] Srt.pr)

noncomputable def secondAtom : source.substitution.Carrier [Srt.pr, Srt.pr] Srt.pr :=
  Quotient.mk _ (.var (.succ .zero) : Term sig [Srt.pr, Srt.pr] Srt.pr)

theorem source_atoms_different : firstAtom ≠ secondAtom := by
  intro same
  have encoded := congrArg encodeEquationClass same
  change Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.bvar 0 = .bvar 1 at encoded
  cases encoded

noncomputable def firstWord : SourceAccountSubstitution.Account source Srt.pr
    [Srt.pr, Srt.pr] := FreeMonoid.of firstAtom * FreeMonoid.of secondAtom

noncomputable def secondWord : SourceAccountSubstitution.Account source Srt.pr
    [Srt.pr, Srt.pr] := FreeMonoid.of secondAtom * FreeMonoid.of firstAtom

/-- The genuine source-word monoid retains order even though this selected
comparison action deliberately forgets it. -/
theorem ordered_accounts_different : firstWord ≠ secondWord := by
  intro same
  have words := congrArg FreeMonoid.toList same
  change [firstAtom, secondAtom] = [secondAtom, firstAtom] at words
  exact source_atoms_different (List.cons.inj words).1

/-- This explicit negative control licenses only an inhabitance use of the
marker comparison: distinct ordered accounts can have identical actions. -/
theorem comparison_loses_account_order
    (value : model.observed.left.substitution.Carrier [Srt.pr, Srt.pr] Srt.pr) :
    firstWord ≠ secondWord ∧ model.act firstWord value = model.act secondWord value :=
  ⟨ordered_accounts_different, action_eq_of_length_eq firstWord secondWord rfl value⟩

end RhoSourceComparison

namespace LambdaBindingComparison

open LambdaContextualRung
open OccurrenceMarker

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

abbrev source := BindingCloneAlgebra.terms sig

def model : Model source Srt.term := comparison source Srt.term

/-- The full intrinsic lambda carrier retains self-application under its
actual binder.  This does not require two independently supplied inputs. -/
def selfApplication : Term sig [] Srt.term :=
  lamT (appT (.var .zero) (.var .zero))

/-- Independently marking one occurrence of the same bound variable is a
typed element of the complete enlarged binding clone. -/
def markedSelfApplication : Term (withMetas sig (context (S := sig) Srt.term).arities) [] Srt.term :=
  .op (.inl .lam) (.cons
    (.op (.inl .app) (.cons (mark (S := sig) Srt.term (.var .zero)) (.cons (.var .zero) .nil))) .nil)

theorem marked_self_application_source :
    model.observed.hom.raw.map markedSelfApplication = selfApplication := rfl

theorem marked_self_application_keeps_occurrence :
    markedSelfApplication ≠ embed (M := (context (S := sig) Srt.term).arities) selfApplication := by
  intro same
  cases same

theorem action_nontrivial :
    model.act (FreeMonoid.of (Term.var (Var.zero : Var [Srt.term] Srt.term)))
      (Term.var Var.zero) ≠ Term.var Var.zero :=
  comparison_nontrivial source Srt.term _

end LambdaBindingComparison

end Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra
