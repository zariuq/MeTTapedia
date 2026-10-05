import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.SystemF
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Renaming

/-!
# Strong normalization of System F from the normalization model

System F embeds in the package of proposition codes over the cumulative tower, and strong
normalization of the package on typed terms implies strong normalization of System F. This
file gives the package its normalization model, model SN over the skeleton-free value side,
and so proves strong normalization of Church-style System F for full β- and
type-β-reduction.

The model has two sides.

* The value side reads the package by the tower's reduction, which has no root computation:
  the decoder `holds` is rigid, implication and the quantifier over codes are constructors,
  and a code means a Kripke candidate of realizers. The quantifier over codes means
  Girard's clause: the terms that send, after any renaming, every realizer of codes into
  the family's candidate at every candidate. The laws of the value side also ask for a
  type of numbers with its two constructors, declared as the constructors they list, and
  for a daimon; these are fresh names the package does not declare. The levels are the
  tower's.
* The realizer side is the package itself under its own reduction: full β together with
  the decoding of codes, where the decoder computes at one argument, the code.

The package is sound for this model in the untyped reading: its universe rules are the
tower's, its only root steps are decodings, which preserve meaning without their typing,
and its only constants are the codes, each a valid term of its declared type. Every
constant is strongly normalizing on the realizer side, since only the decoder computes and
it needs an argument, and so is the closed type of every carrier.
The context of every layout is formed, each entry being the type of codes or the decoding
of a code. So the translation of a well-typed System F term is a term typed in a formed
context, hence strongly normalizing, and a System F term is strongly normalizing when its
translation is (`strongNormalization`).

**Constants that never compute.** The daimon is rigid on the realizer side
(`realizerRoles_daimon`), so the model reads every constant that never computes as the
daimon (`ModelSN.Typed.sn_of_noSteps`). Hence every term typed in a formed context of a
package with the universe rules of the tower and no root step is strongly normalizing,
whatever constants the package declares and at whatever types (`noSteps_sn`). Positive
example: the tower with the constants of a set theory and constants for the rules of its
logic. Negative example: a package with a declared equation is outside the theorem, and a
constant whose equation unfolds again at every step has a typed term with an infinite
reduction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace SystemF

open Normalization
open Consistency (Carrier Kind Model CodesRead)
open Realizability
open StrongNormalization
open Metatheory.SystemF (Context Term Ty)

variable {L : Type} [UniverseLevel.LevelOrder L]

/-! ## Fresh names -/

/-- The type of numbers the laws of the value side ask for. The package does not declare
it. -/
def numName : DeclName := `SystemF.num

/-- The constructor `zero` of the numbers. -/
def zeroName : DeclName := `SystemF.zero

/-- The constructor `suc` of the numbers. -/
def sucName : DeclName := `SystemF.suc

/-- The daimon: a fresh rigid constant of the value side. -/
def daimonName : DeclName := `SystemF.daimon

/-! ## The (codesOver L) of the package -/

/-- The quantifier over (codesOver L) is the package's only quantifier instance, and its carrier
is the type of (codesOver L). -/
theorem quantifiers_some {a : DeclName} {T : LevelTower.Tm L 0} (found : (codesOver L).quantifiers a = some T) :
    a = allProp ∧ T = .const (codesOver L).prop := by
  change List.lookup a [(allProp, .const (codesOver L).prop)] = some T at found
  unfold List.lookup at found
  cases e : a == allProp with
  | false =>
      rw [e] at found
      cases found
  | true =>
      rw [e] at found
      cases found
      exact ⟨eq_of_beq e, rfl⟩

/-- The package has no equation (codesOver L). -/
theorem equationCarrier_none (e : DeclName) : (codesOver L).equationCarrier e = none := rfl

/-! ## The value side -/

/-- The roles of the value side: implication and the quantifier over (codesOver L) are
constructors, the numbers are an inductive type with constructors `zero` and `suc`, and
every other name is rigid, the decoder included. -/
def valueRoles : Roles (LevelTower.Head L) := fun name =>
  if name = (codesOver L).imp then .constructor 2
  else if name = allProp then .constructor 1
  else if name = numName then .inductive [(zeroName, []), (sucName, [.recursive])]
  else if name = zeroName then .constructor 0
  else if name = sucName then .constructor 1
  else .rigid

/-- The quantifier over (codesOver L) ranges over the carrier of (codesOver L). -/
def valueAllCarrier (name : DeclName) : Option (Σ k, Carrier k) :=
  if name = allProp then some ⟨.gen, .prop⟩ else none

theorem valueAllCarrier_some {a : DeclName} {A : Σ k, Carrier k}
    (found : valueAllCarrier a = some A) : a = allProp := by
  unfold valueAllCarrier at found
  by_cases e : a = allProp
  · exact e
  · rw [if_neg e] at found
    cases found

/-- The value side: the tower's reduction, which decodes nothing, read with the (codesOver L) of
System F and fresh numbers. -/
def valueModel (L : Type) [UniverseLevel.LevelOrder L] : Model (LevelTower.Head L) L where
  rules := (LevelTower.rules L)
  roles := valueRoles
  zero := zeroName
  suc := sucName
  imp := (codesOver L).imp
  allCarrier := valueAllCarrier
  eqCarrier := fun _ => none
  num := numName
  prop := (codesOver L).prop
  holds := (codesOver L).holds
  levels := TowerModel.levels fun _ => UniverseLevel.LevelOrder.bot

theorem valueModel_laws : (valueModel L).Laws where
  truth :=
    { shape := ⟨fun step => step.elim, fun step => step.elim⟩
      zero := rfl
      suc := rfl
      imp := rfl
      all := fun found => by
        obtain rfl := valueAllCarrier_some found
        rfl
      eq := fun found => by cases found
      impNotEq := rfl }
  num := rfl
  prop := rfl
  holds := rfl

/-! ## The realizer side -/

/-- The roles of the realizer side: the decoder computes at one argument, the code, and
the code constructors and the numerals are constructors. -/
def realizerRoles : Roles (LevelTower.Head L) := fun name =>
  if name = (codesOver L).holds then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else if name = (codesOver L).imp then .constructor 2
  else if name = allProp then .constructor 1
  else if name = zeroName then .constructor 0
  else if name = sucName then .constructor 1
  else .rigid

/-- Only the decoder computes on the realizer side, at one argument. -/
theorem realizerRoles_computes {c : DeclName} {arity : Nat} {scrutinee : InspectTree}
    (role : realizerRoles (L := L) c = .computes arity scrutinee) : c = (codesOver L).holds ∧ arity = 1 := by
  unfold realizerRoles at role
  split at role
  · cases role
    exact ⟨‹_›, rfl⟩
  · repeat' split at role
    all_goals cases role

theorem realizerDecoderRoles : DecoderRoles (realizerRoles (L := L)) (codesOver L).decoders where
  holds := rfl
  imp := rfl
  all := fun found => by
    obtain ⟨rfl, -⟩ := quantifiers_some found
    rfl
  eq := fun found => by cases found

/-- The realizer side's reduction has root shape: the tower has no root computation, and
the decoding of (codesOver L) has its own shape. -/
theorem realizerShape : RootShape (rulesOver L) realizerRoles :=
  (codesOver L).extend_rootShape TowerModel.shape (fun declared => nomatch declared)
    (fun declared nonrigid => (nonrigid declared.symm).elim) rfl realizerDecoderRoles rfl

theorem realizerReflects : RootReflectsRename (rulesOver L).computation :=
  RootReflectsRename.union RootReflectsRename.empty (decoderComputation_reflectsRename _)

/-- The realizer side: the package under its own reduction. -/
def realizerSide : Realizers (LevelTower.Head L) where
  rules := (rulesOver L)
  roles := realizerRoles
  decoders := (codesOver L).decoders
  zero := zeroName
  suc := sucName
  shape := realizerShape
  reflects := realizerReflects
  decoderRoles := realizerDecoderRoles
  numerals := ⟨rfl, rfl⟩
  decodes := fun step => (codesOver L).extend_decoder_step (LevelTower.rules L) step

/-! ## The (codesOver L) are read by the (model L) -/

/-- Every constant is strongly normalizing on the realizer side: only the decoder
computes, and it needs an argument. -/
theorem const_sn (c : DeclName) {n : Nat} : SN (rulesOver L) (.const c : LevelTower.Tm L n) :=
  SN.constSpine realizerShape (args := [])
    (fun _ _ role => by
      obtain ⟨-, rfl⟩ := realizerRoles_computes role
      exact Nat.zero_lt_one)
    (fun _ mem => nomatch mem)

/-- The closed type of every interpretable carrier is strongly normalizing on the
realizer side. -/
theorem carrier_sn : ∀ {k : Kind} {C : Carrier k}, C.Interpretable (valueModel L) →
    SN (rulesOver L) (C.term (valueModel L))
  | _, _, .prop => const_sn _
  | _, _, .num => const_sn _
  | _, _, .rigid _ _ _ => const_sn _
  | _, _, .arr dom cod =>
      SN.pi (RootShape.spineHeaded realizerShape) (carrier_sn dom)
        (SN.rename realizerReflects wk (carrier_sn cod))

theorem codes_read : CodesRead (valueModel L) (codesOver L) where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := fun found => by
    obtain ⟨rfl, rfl⟩ := quantifiers_some found
    exact ⟨.gen, .prop, rfl, .prop, rfl⟩
  eq := fun found => by cases found

/-! ## The (model L) -/

/-- The only inductive type of the value side is the numbers, with the
constructors `zero` and `suc`. -/
theorem valueRoles_inductive {T : DeclName} {cs : List (DeclName × List (Normalization.Field (LevelTower.Head L)))}
    (role : valueRoles T = .inductive cs) :
    T = numName ∧ cs = [(zeroName, []), (sucName, [.recursive])] := by
  unfold valueRoles at role
  by_cases hi : T = (codesOver L).imp
  · rw [if_pos hi] at role
    cases role
  rw [if_neg hi] at role
  by_cases ha : T = allProp
  · rw [if_pos ha] at role
    cases role
  rw [if_neg ha] at role
  by_cases hn : T = numName
  · rw [if_pos hn] at role
    exact ⟨hn, (Role.inductive.inj role).symm⟩
  rw [if_neg hn] at role
  by_cases hz : T = zeroName
  · rw [if_pos hz] at role
    cases role
  rw [if_neg hz] at role
  by_cases hs : T = sucName
  · rw [if_pos hs] at role
    cases role
  rw [if_neg hs] at role
  cases role

/-- The constructors the numbers list are declared as constructors, with their
numbers of fields. -/
theorem valueRoles_declared : ConstructorsDeclared (valueRoles (L := L)) where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := valueRoles_inductive role
    show [zeroName, sucName].Nodup
    decide

/-- The normalization (model L) of the System F package: its value side, the daimon
and its realizer side, with the tower's levels. -/
def model (L : Type) [UniverseLevel.LevelOrder L] : ModelSN.SNModel (LevelTower.Head L) L where
  toModel := valueModel L
  star := daimonName
  realizers := realizerSide

theorem model_laws : (model L).Laws where
  values := valueModel_laws
  star := rfl
  starNotProp := by
    show daimonName ≠ propName
    decide
  starNotHolds := by
    show daimonName ≠ holdsName
    decide
  declared := valueRoles_declared

/-- The (codesOver L) of System F are read by the (model L). -/
theorem codes_readS : ModelSN.CodesReadS (model L) (codesOver L) where
  read := codes_read
  decoders := rfl
  propStuck := fun _ _ role =>
    absurd (realizerRoles_computes (c := (codesOver L).prop) role).1
      (by show ¬ propName = holdsName; decide)
  carrierSN := carrier_sn

/-! ## Soundness -/

/-- Every root step of the System F package is a decoding, which preserves
meaning in the (model L) without its typing. -/
theorem root_semantic {n : Nat} {l r : LevelTower.Tm L n} (step : (rulesOver L).computation.step l r) :
    ModelSN.RootSemanticS (model L) l r := by
  rcases step with step | step
  · exact step.elim
  · exact ModelSN.ModelRootS.semantic model_laws codes_read.decodes (.inr step)

/-- **The System F package is sound for the (model L), in the untyped reading**: its
universe (rulesOver L) are the tower's, its root steps are decodings, each preserving
meaning without its typing, and its constants are the (codesOver L). -/
theorem soundS : ModelSN.SoundS (rulesOver L) (model L) := by
  refine ⟨{ laws := model_laws
            headTyping := id
            isUniverse := id
            join := id
            cumulative := id
            headEq := id
            root := fun step => .inl (root_semantic step)
            constants := ?_ }, root_semantic⟩
  intro name type declared
  change ((codesOver L).codeType name).orElse (fun _ => none) = some type at declared
  cases code : (codesOver L).codeType name with
  | none =>
      rw [code] at declared
      cases declared
  | some T =>
      rw [code] at declared
      cases declared
      exact ModelSN.valid_codeS model_laws codes_readS code

/-! ## Strong normalization -/

/-- **Strong normalization of the System F package.** Every term typed in a formed
context of the package is strongly normalizing under the package's own reduction,
full β together with the decoding of (codesOver L), and so is its type. -/
theorem rules_sn {n : Nat} {Δ : LevelTower.Ctx L n} {t A : LevelTower.Tm L n}
    (formed : CtxFormed (rulesOver L) Δ) (typed : Typed (rulesOver L) Δ t A) : SN (rulesOver L) t ∧ SN (rulesOver L) A :=
  ModelSN.Typed.sn soundS.typed formed typed

/-- The daimon is rigid on the realizer side. -/
theorem realizerRoles_daimon : realizerRoles (L := L) daimonName = .rigid := by
  have holds : daimonName ≠ (codesOver L).holds := by
    show daimonName ≠ holdsName
    decide
  have imp : daimonName ≠ (codesOver L).imp := by
    show daimonName ≠ impName
    decide
  have all : daimonName ≠ allProp := by decide
  have zero : daimonName ≠ zeroName := by decide
  have suc : daimonName ≠ sucName := by decide
  unfold realizerRoles
  rw [if_neg holds, if_neg imp, if_neg all, if_neg zero, if_neg suc]

/-- **Strong normalization over the tower, whatever constants are declared.** Every term
typed in a formed context of a package with the universe rules of the tower and no root step
is strongly normalizing under the package's reduction, β and the projections. -/
theorem noSteps_sn {R : Rules (LevelTower.Head L)}
    (headTyping : ∀ {h u : LevelTower.Head L}, R.headTyping h u →
      (LevelTower.rules L).headTyping h u)
    (isUniverse : ∀ {u : LevelTower.Head L}, R.isUniverse u → (LevelTower.rules L).isUniverse u)
    (join : ∀ {u v w : LevelTower.Head L}, R.join u v w → (LevelTower.rules L).join u v w)
    (cumulative : ∀ {u v : LevelTower.Head L}, R.cumulative u v →
      (LevelTower.rules L).cumulative u v)
    (headEq : ∀ {h h' : LevelTower.Head L}, R.headEq h h' → (LevelTower.rules L).headEq h h')
    (noSteps : ∀ {n : Nat} {l r : LevelTower.Tm L n}, ¬ R.computation.step l r)
    {n : Nat} {Γ : LevelTower.Ctx L n} {t A : LevelTower.Tm L n} (formed : CtxFormed R Γ)
    (typed : Typed R Γ t A) : SN R t :=
  ModelSN.Typed.sn_of_noSteps (M := model L) headTyping isUniverse join cumulative headEq noSteps
    model_laws realizerRoles_daimon formed typed

/-- **Strong normalization of System F.** Every well-typed term of Church-style
System F is strongly normalizing for full β- and type-β-reduction. -/
theorem strongNormalization {k : Nat} {Γ : Context} {M : Term} {τ : Ty}
    (typing : Metatheory.SystemF.HasType k Γ M τ) : Metatheory.SystemF.SN M :=
  sn_of_formedPackageSN (fun formed typed => (rules_sn formed typed).1) typing

/-- The polymorphic identity is strongly normalizing. -/
example : Metatheory.SystemF.SN Term.polyId :=
  strongNormalization (k := 0) (Γ := []) (τ := Ty.idTy)
    (.tlam (.lam Nat.zero_lt_one (.var rfl)))

/-! ## The self-application loop -/

/-- The self-application loop `(λx:σ. x x) (λx:σ. x x)` of the untyped λ-calculus. -/
def loop (σ : Ty) : Term :=
  .app (.lam σ (.app (.var 0) (.var 0))) (.lam σ (.app (.var 0) (.var 0)))

/-- The loop reduces to itself in one β-step. -/
theorem loop_step (σ : Ty) : Metatheory.SystemF.StrongStep (loop σ) (loop σ) :=
  .beta σ (.app (.var 0) (.var 0)) (.lam σ (.app (.var 0) (.var 0)))

/-- A term that reduces to itself is not strongly normalizing. -/
theorem not_sn_of_step_self {M : Term} (step : Metatheory.SystemF.StrongStep M M) :
    ¬ Metatheory.SystemF.SN M := by
  intro sn
  have key : ∀ N, Metatheory.SystemF.SN N → N = M → False := by
    intro N accessible
    induction accessible with
    | intro N _ ih =>
        intro same
        subst same
        exact ih _ step rfl
  exact key M sn rfl

/-- The loop has no type in System F, in any context. -/
theorem loop_untypable {k : Nat} {Γ : Context} (σ τ : Ty) :
    ¬ Metatheory.SystemF.HasType k Γ (loop σ) τ :=
  fun typing => not_sn_of_step_self (loop_step σ) (strongNormalization typing)

end SystemF

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
