import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel

/-!
# Quotienting full binding terms by a substitution congruence

This reusable proof core takes an equivalence relation preserved by the actual
binding operators, raw substitution, and pointwise replacement of a complete
typed environment. It constructs substitution by arbitrary quotient values,
including the environment lift beneath every binder. No equation list or
choice of canonical representative is part of the interface.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingTermCongruenceQuotient

open BindingSubstitutionAlgebra FreeBindingTerms

variable {S : Signature}

/-- Relations on argument heads are at their exact binder-extended contexts. -/
inductive ArgumentRelation
    (relation : {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → Term S Γ sort → Prop) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args S arity Γ → Args S arity Γ → Prop where
  | nil {Γ : Ctx S} : ArgumentRelation relation (Args.nil (S := S) (Γ := Γ)) .nil
  | cons {binders : Ctx S} {sort : S.Srt}
      {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      {first second : Term S (binders ++ Γ) sort}
      {rest rest' : Args S arity Γ} :
      relation first second → ArgumentRelation relation rest rest' →
        ArgumentRelation relation (.cons first rest) (.cons second rest')

/-- A congruence of the existing full term clone, with its typed positional
substitution and the original operator binding arities. -/
structure Congruence (S : Signature) where
  relation : {Γ : Ctx S} → {sort : S.Srt} → Term S Γ sort → Term S Γ sort → Prop
  reflexive : ∀ {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort), relation value value
  symmetric : ∀ {Γ : Ctx S} {sort : S.Srt} {first second : Term S Γ sort},
    relation first second → relation second first
  transitive : ∀ {Γ : Ctx S} {sort : S.Srt} {first middle last : Term S Γ sort},
    relation first middle → relation middle last → relation first last
  bind_relation : ∀ {Γ Δ : Ctx S} {sort : S.Srt} (env : Sub S Γ Δ)
    {first second : Term S Γ sort}, relation first second →
      relation (bind env first) (bind env second)
  bind_pointwise : ∀ {Γ Δ : Ctx S} {sort : S.Srt} (first second : Sub S Γ Δ),
    (∀ type position, relation (first type position) (second type position)) →
    ∀ value : Term S Γ sort, relation (bind first value) (bind second value)
  operation_relation : ∀ {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    {first second : Args S (S.arity operator) Γ}, ArgumentRelation relation first second →
      relation (.op operator first) (.op operator second)

variable (congruence : Congruence S)

def setoid (Γ : Ctx S) (sort : S.Srt) : Setoid (Term S Γ sort) where
  r := congruence.relation
  iseqv := ⟨congruence.reflexive, congruence.symmetric, congruence.transitive⟩

abbrev Carrier (Γ : Ctx S) (sort : S.Srt) := Quotient (setoid congruence Γ sort)

def project {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort) :
    Carrier congruence Γ sort := Quotient.mk _ value

def bindQ {Γ Δ : Ctx S} {sort : S.Srt} (env : Sub S Γ Δ) :
    Carrier congruence Γ sort → Carrier congruence Δ sort :=
  Quotient.map (bind env) (fun _ _ related => congruence.bind_relation env related)

noncomputable def representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier congruence) Γ Δ) : Sub S Γ Δ :=
  fun sort position => Quotient.out (env sort position)

theorem project_representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier congruence) Γ Δ) (sort : S.Srt) (position : Var Γ sort) :
    project congruence (representativeEnv congruence env sort position) = env sort position :=
  Quotient.out_eq _

noncomputable def substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier congruence) Γ Δ)
    (value : Carrier congruence Γ sort) : Carrier congruence Δ sort :=
  bindQ congruence (representativeEnv congruence env) value

theorem substitute_project {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier congruence) Γ Δ) (value : Term S Γ sort) :
    substitute congruence env (project congruence value) =
      project congruence (bind (representativeEnv congruence env) value) := rfl

theorem substitute_var {Γ Δ : Ctx S}
    (env : Environment S (Carrier congruence) Γ Δ) {sort : S.Srt} (position : Var Γ sort) :
    substitute congruence env (project congruence (.var position)) = env sort position :=
  project_representativeEnv congruence env sort position

theorem bind_classes_eq {Γ Δ : Ctx S} {sort : S.Srt}
    (first second : Sub S Γ Δ)
    (agree : ∀ type position,
      project congruence (first type position) = project congruence (second type position))
    (value : Term S Γ sort) :
    project congruence (bind first value) = project congruence (bind second value) := by
  apply Quotient.sound
  exact congruence.bind_pointwise first second
    (fun type position => Quotient.exact (agree type position)) value

theorem substitute_identity {Γ : Ctx S} {sort : S.Srt}
    (value : Carrier congruence Γ sort) :
    substitute congruence (fun _ position => project congruence (.var position)) value = value := by
  induction value using Quotient.inductionOn with
  | _ term =>
      change project congruence
          (bind (representativeEnv congruence
            (fun _ position => project congruence (.var position))) term) =
        project congruence term
      have comparison := bind_classes_eq congruence
        (representativeEnv congruence (fun _ position => project congruence (.var position)))
        (fun _ position => .var position)
        (by intro type position; exact project_representativeEnv congruence _ type position) term
      simpa only [bind_id] using comparison

theorem representativeEnv_comp {Γ Δ Θ : Ctx S}
    (first : Environment S (Carrier congruence) Γ Δ)
    (second : Environment S (Carrier congruence) Δ Θ)
    (sort : S.Srt) (position : Var Γ sort) :
    project congruence
        (bind (representativeEnv congruence second)
          (representativeEnv congruence first sort position)) =
      project congruence
        (representativeEnv congruence
          (fun type position => substitute congruence second (first type position)) sort position) := by
  rw [project_representativeEnv]
  change bindQ congruence (representativeEnv congruence second)
    (project congruence (representativeEnv congruence first sort position)) = _
  rw [project_representativeEnv]
  rfl

theorem substitute_comp {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment S (Carrier congruence) Γ Δ)
    (second : Environment S (Carrier congruence) Δ Θ)
    (value : Carrier congruence Γ sort) :
    substitute congruence second (substitute congruence first value) =
      substitute congruence
        (fun type position => substitute congruence second (first type position)) value := by
  induction value using Quotient.inductionOn with
  | _ term =>
      change project congruence
          (bind (representativeEnv congruence second)
            (bind (representativeEnv congruence first) term)) = _
      rw [bind_comp]
      exact bind_classes_eq congruence _ _ (representativeEnv_comp congruence first second) term

theorem substitute_represented {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier congruence) Γ Δ) (raw : Sub S Γ Δ)
    (agree : ∀ type position, project congruence (raw type position) = env type position)
    (value : Carrier congruence Γ sort) :
    substitute congruence env value = bindQ congruence raw value := by
  induction value using Quotient.inductionOn with
  | _ term =>
      exact bind_classes_eq congruence _ _
        (fun type position => (project_representativeEnv congruence env type position).trans
          (agree type position).symm) term

/-- Full semantic substitution is constructed on the quotient fibres. -/
noncomputable abbrev substitutionAlgebra : BindingSubstitutionAlgebra.Algebra S where
  Carrier := Carrier congruence
  injectVar := fun position => project congruence (.var position)
  substitute := substitute congruence
  substitute_var := substitute_var congruence
  substitute_identity := substitute_identity congruence
  substitute_comp := substitute_comp congruence

theorem weaken_project {Γ : Ctx S} {sort fresh : S.Srt} (value : Term S Γ sort) :
    (substitutionAlgebra congruence).weaken (fresh := fresh) (project congruence value) =
      project congruence (weaken value) := by
  change substitute congruence (fun _ position => project congruence (.var (.succ position)))
      (project congruence value) = _
  rw [substitute_represented congruence _ (fun _ position => .var (.succ position))
    (by intro type position; rfl)]
  exact congrArg (project congruence) (bind_var_eq_rename _ value)

theorem liftEnvironment_represented {Γ Δ : Ctx S}
    (env : Environment S (Carrier congruence) Γ Δ) :
    ∀ (binders : Ctx S) (sort : S.Srt) (position : Var (binders ++ Γ) sort),
      project congruence (liftSub (representativeEnv congruence env) binders sort position) =
        (substitutionAlgebra congruence).liftEnvironment env binders sort position
  | [], sort, position => project_representativeEnv congruence env sort position
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change project congruence (weaken (liftSub (representativeEnv congruence env) binders sort old)) =
        (substitutionAlgebra congruence).weaken
          ((substitutionAlgebra congruence).liftEnvironment env binders sort old)
      rw [← liftEnvironment_represented env binders sort old, weaken_project]

noncomputable def representativeArgs :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    FamilyArgs S (Carrier congruence) arity Γ → Args S arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (Quotient.out head) (representativeArgs tail)

noncomputable def operation {Γ : Ctx S} {sort : S.Srt} (operator : S.Op sort)
    (arguments : FamilyArgs S (Carrier congruence) (S.arity operator) Γ) :
    Carrier congruence Γ sort :=
  project congruence (.op operator (representativeArgs congruence arguments))

/-- The syntactic lifted environment represents the actual quotient lift,
so every argument comparison stays below that argument's own binders. -/
theorem representativeArgs_substitute {Γ Δ : Ctx S}
    (env : Environment S (Carrier congruence) Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (arguments : FamilyArgs S (Carrier congruence) arity Γ),
      ArgumentRelation congruence.relation
        (bindArgs (representativeEnv congruence env)
          (representativeArgs congruence arguments))
        (representativeArgs congruence
          ((substitutionAlgebra congruence).substituteArgs env arguments))
  | _, .nil => .nil
  | _, .cons (bs := binders) head tail => by
      apply ArgumentRelation.cons
      · have comparison :
            project congruence
                (bind (liftSub (representativeEnv congruence env) binders)
                  (Quotient.out head)) =
              project congruence
                (Quotient.out
                  (substitute congruence
                    ((substitutionAlgebra congruence).liftEnvironment env binders) head)) := by
          calc
            project congruence
                (bind (liftSub (representativeEnv congruence env) binders)
                  (Quotient.out head)) =
                bindQ congruence (liftSub (representativeEnv congruence env) binders) head := by
              change bindQ congruence _ (Quotient.mk _ (Quotient.out head)) = _
              rw [Quotient.out_eq]
            _ = substitute congruence
                ((substitutionAlgebra congruence).liftEnvironment env binders) head :=
              (substitute_represented congruence _ _
                (liftEnvironment_represented congruence env binders) head).symm
            _ = project congruence (Quotient.out _) := (Quotient.out_eq _).symm
        exact Quotient.exact comparison
      · exact representativeArgs_substitute env tail

/-- The quotient retains the complete binding-clone algebra, rather than
only substitution by raw representative environments. -/
noncomputable abbrev algebra : BindingCloneAlgebra.Algebra S where
  substitution := substitutionAlgebra congruence
  operation := operation congruence
  operation_substitute := by
    intro Γ Δ sort env operator arguments
    change project congruence
        (bind (representativeEnv congruence env)
          (.op operator (representativeArgs congruence arguments))) =
      project congruence
        (.op operator
          (representativeArgs congruence
            ((substitutionAlgebra congruence).substituteArgs env arguments)))
    exact Quotient.sound (congruence.operation_relation operator
      (representativeArgs_substitute congruence env arguments))

theorem representativeArgs_project :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : FamilyArgs S (Term S) arity Γ),
      ArgumentRelation congruence.relation
        (representativeArgs congruence
          (FamilyArgs.map (fun {_Γ _sort} value => project congruence value) arguments))
        ((FreeBindingTerms.terms.familyToSyntax S) arguments)
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (Quotient.exact (Quotient.out_eq (project congruence head)))
        (representativeArgs_project tail)

/-- The genuine free-clone map preserves all operators and substitution. -/
noncomputable def projection :
    FreeBindingClone.Hom (BindingCloneAlgebra.terms S) (algebra congruence) where
  raw :=
    { map := project congruence
      map_variable := by intros; rfl
      map_operation := by
        intro Γ sort operator arguments
        apply Quotient.sound
        exact congruence.symmetric (congruence.operation_relation operator
          (representativeArgs_project congruence arguments)) }
  map_substitute := by
    intro Γ Δ sort env value
    change project congruence (bind env value) =
      substitute congruence (fun type position => project congruence (env type position))
        (project congruence value)
    rw [substitute_represented congruence _ env (by intro type position; rfl)]
    rfl

/-- Initiality identifies the independently constructed quotient projection
with the usual structural term fold. -/
theorem interpret_eq_project {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort) :
    BindingCloneFoldSubstitution.interpret (algebra congruence) value = project congruence value := by
  exact (congrArg
    (fun hom : FreeBindingClone.Hom (BindingCloneAlgebra.terms S) (algebra congruence) =>
      hom.raw.map value)
    (FreeBindingClone.hom_unique (algebra congruence) (projection congruence))).symm

universe u

/-- This is the exact descent condition for an independently specified
target algebra's existing term fold. -/
def Sound (target : BindingCloneAlgebra.Algebra.{u} S) : Prop :=
  ∀ {Γ : Ctx S} {sort : S.Srt} {first second : Term S Γ sort},
    congruence.relation first second →
      BindingCloneFoldSubstitution.interpret target first =
        BindingCloneFoldSubstitution.interpret target second

variable (target : BindingCloneAlgebra.Algebra.{u} S) (sound : Sound congruence target)

def interpretQuotient {Γ : Ctx S} {sort : S.Srt} :
    Carrier congruence Γ sort → target.substitution.Carrier Γ sort :=
  Quotient.lift (BindingCloneFoldSubstitution.interpret target) (fun _ _ relation => sound relation)

theorem interpretQuotient_project {Γ : Ctx S} {sort : S.Srt} (value : Term S Γ sort) :
    interpretQuotient congruence target sound (project congruence value) =
      BindingCloneFoldSubstitution.interpret target value := rfl

theorem interpretQuotient_out {Γ : Ctx S} {sort : S.Srt} (value : Carrier congruence Γ sort) :
    interpretQuotient congruence target sound value =
      BindingCloneFoldSubstitution.interpret target (Quotient.out value) := by
  have comparison := interpretQuotient_project congruence target sound (Quotient.out value)
  change interpretQuotient congruence target sound (Quotient.mk _ (Quotient.out value)) = _ at comparison
  rw [Quotient.out_eq] at comparison
  exact comparison

theorem interpretQuotient_bindQ {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Sub S Γ Δ) (value : Carrier congruence Γ sort) :
    interpretQuotient congruence target sound (bindQ congruence env value) =
      target.substitution.substitute
        (fun type position => BindingCloneFoldSubstitution.interpret target (env type position))
        (interpretQuotient congruence target sound value) := by
  induction value using Quotient.inductionOn with
  | _ term => exact BindingCloneFoldSubstitution.interpret_bind target env term

theorem interpretArgs_representativeArgs :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : FamilyArgs S (Carrier congruence) arity Γ),
      BindingCloneFoldSubstitution.interpretArgs target (representativeArgs congruence arguments) =
        FamilyArgs.map (interpretQuotient congruence target sound) arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ FamilyArgs.cons (interpretQuotient_out congruence target sound head).symm
        (interpretArgs_representativeArgs tail)

/-- The unique descended fold preserves the entire binding algebra and
arbitrary quotient-valued semantic environments. -/
noncomputable def quotientHom : FreeBindingClone.Hom (algebra congruence) target where
  raw :=
    { map := interpretQuotient congruence target sound
      map_variable := by intros; rfl
      map_operation := by
        intro Γ sort operator arguments
        change interpretQuotient congruence target sound
            (project congruence (.op operator (representativeArgs congruence arguments))) = _
        rw [interpretQuotient_project]
        exact congrArg (target.operation operator)
          (interpretArgs_representativeArgs congruence target sound arguments) }
  map_substitute := by
    intro Γ Δ sort env value
    change interpretQuotient congruence target sound (substitute congruence env value) = _
    rw [substitute_represented congruence env (representativeEnv congruence env)
      (project_representativeEnv congruence env) value, interpretQuotient_bindQ]
    congr 1
    funext type position
    exact (interpretQuotient_out congruence target sound (env type position)).symm

/-- Every clone map from this quotient is the descended structural fold. -/
theorem hom_unique (hom : FreeBindingClone.Hom (algebra congruence) target) :
    hom = quotientHom congruence target sound := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort value
  induction value using Quotient.inductionOn with
  | _ term =>
      have comparison := FreeBindingClone.hom_unique target
        (FreeBindingClone.Hom.comp (projection congruence) hom)
      have onTerm := congrArg
        (fun arrow : FreeBindingClone.Hom (BindingCloneAlgebra.terms S) target =>
          arrow.raw.map term) comparison
      exact onTerm.trans (interpretQuotient_project congruence target sound term).symm

end Mettapedia.OSLF.Binding.BindingTermCongruenceQuotient
