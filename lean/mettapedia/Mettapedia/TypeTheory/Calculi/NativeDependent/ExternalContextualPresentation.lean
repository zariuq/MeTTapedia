import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualComparison
import Mettapedia.TypeTheory.ContextualModelTelescopes

/-!
# Chosen-comprehension presentations of generated contexts

Every admitted raw telescope has a finite presentation built from the selected
empty context and selected type representatives. Generated context conversion
gives the comparison to the supplied raw telescope. Its arrows retain every
variable position, including variables in dependent annotations.

The comparison is an isomorphism, not equality of the two context objects.
Conjugation supplies a context functor naturally isomorphic to the identity.
Naturality then determines a transformation on every raw object from its
components on the chosen presentation image. These are presentation and
coherent-cell uniqueness results; no arbitrary-model interpretation or
classifying initiality is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation

open _root_.CategoryTheory

universe u v w
variable {S : Symbols.{u}} {D : Signature S}

inductive Chosen (D : Signature S) : Context D → Prop where
  | empty : Chosen D (Contextual.empty D)
  | extend {context : Context D} (previous : Chosen D context) (type : QType context) :
      Chosen D (Contextual.extend context (QuotientCwf.typeRepresentative type))

theorem formed_previous {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
    (formed : Formed D (.snoc context type)) : Formed D context := by
  cases formed with
  | snoc previous _ => exact previous

theorem formed_last {n : Nat} {context : ContextExpr S n} {type : TypeExpr S n}
    (formed : Formed D (.snoc context type)) : Holds D (.type context type) := by
  cases formed with
  | snoc _ last => exact last

theorem contextEquality_refl {n : Nat} {context : ContextExpr S n}
    (formed : Formed D context) : Holds D (.contextEq context context) :=
  conclude (.contextReflexivity context) ⟨formed.judgment, trivial⟩

theorem contextEquality_symm {n : Nat} {first second : ContextExpr S n}
    (same : Holds D (.contextEq first second)) : Holds D (.contextEq second first) :=
  conclude (.contextSymmetry first second) ⟨same, trivial⟩

def contextOf {n : Nat} (raw : ContextExpr S n) (formed : Formed D raw) : Context D :=
  ⟨n, raw, formed⟩

def contextArrow {n : Nat} (first second : ContextExpr S n)
    (firstFormed : Formed D first) (secondFormed : Formed D second)
    (same : Holds D (.contextEq first second)) :
    contextOf first firstFormed ⟶ contextOf second secondFormed where
  substitution := TermExpr.var
  admitted := conclude (.transportSubstitution first first first second TermExpr.var)
    ⟨contextEquality_refl firstFormed, same,
      conclude (.substitutionIdentity first) ⟨firstFormed.judgment, trivial⟩, trivial⟩

@[simp] theorem contextArrow_substitution {n : Nat} (first second : ContextExpr S n)
    (firstFormed : Formed D first) (secondFormed : Formed D second)
    (same : Holds D (.contextEq first second)) :
    (contextArrow first second firstFormed secondFormed same).substitution = TermExpr.var := rfl

def contextIso {n : Nat} (first second : ContextExpr S n)
    (firstFormed : Formed D first) (secondFormed : Formed D second)
    (same : Holds D (.contextEq first second)) :
    contextOf first firstFormed ≅ contextOf second secondFormed where
  hom := contextArrow first second firstFormed secondFormed same
  inv := contextArrow second first secondFormed firstFormed (contextEquality_symm same)
  hom_inv_id := Hom.ext (composeSubstitution_identity TermExpr.var)
  inv_hom_id := Hom.ext (composeSubstitution_identity TermExpr.var)

@[simp] theorem contextIso_hom_substitution {n : Nat} (first second : ContextExpr S n)
    (firstFormed : Formed D first) (secondFormed : Formed D second)
    (same : Holds D (.contextEq first second)) :
    (contextIso first second firstFormed secondFormed same).hom.substitution = TermExpr.var := rfl

@[simp] theorem contextIso_inv_substitution {n : Nat} (first second : ContextExpr S n)
    (firstFormed : Formed D first) (secondFormed : Formed D second)
    (same : Holds D (.contextEq first second)) :
    (contextIso first second firstFormed secondFormed same).inv.substitution = TermExpr.var := rfl

structure Data {n : Nat} (original : ContextExpr S n) where
  selected : ContextExpr S n
  formed : Formed D selected
  chosen : Chosen D (contextOf selected formed)
  equivalent : Holds D (.contextEq selected original)

def Data.context {n : Nat} {original : ContextExpr S n} (data : Data (D := D) original) :
    Context D := contextOf data.selected data.formed

/-- Selection recurses on raw syntax; all supplied formation witnesses occur
only in proof fields. Each selected family is actually admitted by conversion. -/
noncomputable def select : {n : Nat} → (raw : ContextExpr S n) →
    Formed D raw → Data (D := D) raw
  | _, .nil, _ => ⟨.nil, .nil, .empty, contextEquality_refl .nil⟩
  | _, .snoc previous type, formed =>
      let earlier := select previous (formed_previous formed)
      let transported : TypeOver earlier.context :=
        ⟨type, conclude (.transportType previous earlier.selected type)
          ⟨contextEquality_symm earlier.equivalent, formed_last formed, trivial⟩⟩
      let annotation := QuotientCwf.typeRepresentative (QType.mk transported)
      ⟨.snoc earlier.selected annotation.code, .snoc earlier.formed annotation.formed,
        .extend earlier.chosen (QType.mk transported),
        conclude (.contextExtendEquality earlier.selected previous annotation.code type)
          ⟨earlier.equivalent,
            (QType.mk_eq_iff annotation transported).mp
              (QuotientCwf.typeRepresentative_class (QType.mk transported)),
            formed_last formed, trivial⟩⟩

noncomputable def selectedContext (context : Context D) : Context D :=
  (select context.raw context.formed).context

theorem selected_chosen (context : Context D) : Chosen D (selectedContext context) :=
  (select context.raw context.formed).chosen

/-- The chosen presentation is an actual repeated comprehension telescope
in the constructed CwF, rather than a separate surrogate notion of context. -/
theorem Chosen.telescope {context : Context D} (chosen : Chosen D context) :
    Nonempty (Mettapedia.TypeTheory.ContextualModelTelescopes.Telescope
      (QuotientCwf.withTerminal D) context.arity ((quotientProjection D).obj context)) := by
  induction chosen with
  | empty => exact ⟨.nil⟩
  | @extend context previous type ih =>
      rcases ih with ⟨earlier⟩
      exact ⟨.snoc earlier type⟩

noncomputable def selectedTelescope (context : Context D) :
    Mettapedia.TypeTheory.ContextualModelTelescopes.Telescope
      (QuotientCwf.withTerminal D) context.arity
      ((quotientProjection D).obj (selectedContext context)) :=
  Classical.choice (selected_chosen context).telescope

@[simp] theorem selected_arity (context : Context D) : (selectedContext context).arity = context.arity := rfl

noncomputable def comparison (context : Context D) : selectedContext context ≅ context :=
  contextIso (select context.raw context.formed).selected context.raw
    (select context.raw context.formed).formed context.formed
    (select context.raw context.formed).equivalent

@[simp] theorem comparison_hom_substitution (context : Context D) :
    (comparison context).hom.substitution = TermExpr.var := rfl

@[simp] theorem comparison_inv_substitution (context : Context D) :
    (comparison context).inv.substitution = TermExpr.var := rfl

theorem comparison_type_code (context : Context D) (type : TypeOver context) :
    (type.reindex (comparison context).hom).code = type.code :=
  TypeExpr.substitute_identity type.code

theorem comparison_term_code (context : Context D) {type : TypeOver context}
    (term : Term context type) : (term.reindex (comparison context).hom).code = term.code :=
  TermExpr.substitute_identity term.code

/-- The arrow action transports both endpoint presentations. -/
noncomputable def normalizer (D : Signature S) : Context D ⥤ Context D where
  obj := selectedContext
  map {source target} morphism := (comparison source).hom ≫ morphism ≫ (comparison target).inv
  map_id context := by simp
  map_comp first second := by simp [Category.assoc]

theorem normalizer_map_substitution {source target : Context D} (morphism : source ⟶ target) :
    ((normalizer D).map morphism).substitution = morphism.substitution := by
  change composeSubstitution TermExpr.var (composeSubstitution morphism.substitution TermExpr.var) = _
  rw [composeSubstitution_identity, identity_composeSubstitution]

noncomputable def normalizerIso (D : Signature S) : normalizer D ≅ 𝟭 (Context D) :=
  NatIso.ofComponents comparison (by intro source target morphism; simp [normalizer, Category.assoc])

theorem normalizer_map_congruent {source target : Context D} {first second : source ⟶ target}
    (same : homEquality D first second) :
    homEquality D ((normalizer D).map first) ((normalizer D).map second) :=
  homEquality_precompose (comparison source).hom
    (homEquality_postcompose same (comparison target).inv)

noncomputable def quotientNormalizer (D : Signature S) : quotientContext D ⥤ quotientContext D :=
  _root_.CategoryTheory.Quotient.lift (homEquality D) (normalizer D ⋙ quotientProjection D)
    (fun _ _ _ _ same =>
      (quotientProjection_map_eq_iff _ _).mpr (normalizer_map_congruent same))

@[simp] theorem quotientNormalizer_obj_as (context : quotientContext D) :
    ((quotientNormalizer D).obj context).as = selectedContext context.as := rfl

noncomputable def quotientComparison (context : quotientContext D) :
    (quotientNormalizer D).obj context ≅ context :=
  (quotientProjection D).mapIso (comparison context.as)

noncomputable def quotientNormalizerIso (D : Signature S) :
    quotientNormalizer D ≅ 𝟭 (quotientContext D) :=
  NatIso.ofComponents quotientComparison (by
    intro source target morphism
    induction morphism using Quot.inductionOn with
    | h raw =>
      exact ((quotientProjection D).map_comp _ _).symm.trans
        ((congrArg (quotientProjection D).map
          ((normalizerIso D).hom.naturality raw)).trans
          ((quotientProjection D).map_comp _ _)))

theorem quotientNormalizer_chosen (context : quotientContext D) :
    Chosen D ((quotientNormalizer D).obj context).as := selected_chosen context.as

/-- Equality on the finite selected-comprehension image determines a genuine
natural transformation on every admitted raw context. -/
theorem natTrans_ext_chosen {Target : Type v} [Category.{w} Target]
    {first second : quotientContext D ⥤ Target} (left right : first ⟶ second)
    (onChosen : ∀ context, Chosen D context.as → left.app context = right.app context) :
    left = right := by
  apply NatTrans.ext
  funext context
  let arrow := (quotientComparison context).hom
  apply (cancel_epi (first.map arrow)).mp
  rw [left.naturality, right.naturality]
  rw [onChosen ((quotientNormalizer D).obj context) (quotientNormalizer_chosen context)]

theorem natIso_ext_chosen {Target : Type v} [Category.{w} Target]
    {first second : quotientContext D ⥤ Target} (left right : first ≅ second)
    (onChosen : ∀ context, Chosen D context.as → (left.app context).hom = (right.app context).hom) :
    left = right := by
  apply Iso.ext
  exact natTrans_ext_chosen left.hom right.hom onChosen

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation
