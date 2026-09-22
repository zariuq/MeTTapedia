import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizInterface
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLLeibnizDerived
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Native proof traversal under predicate equality

This alternative proof compiler uses the formed Leibniz logical signature.
The primitive-equality compiler and native decoder rules remain unchanged.
Unsupported proof constructors return no term. Its mixed object/proof
environment retains the actual source proof's variable occurrences.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeProofTranslation

open Presentation Mettapedia.Logic
open HOL.UniformListInduction

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Formula (gamma : SourceContext) := HOL.Formula Symbol gamma

def represent {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) : Option (Tower.Tm gamma.length) :=
  FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature term

def rawEquality {n : Nat} (type : HOL.Ty BaseSort) (x y : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed (FormationSensitiveHOLLeibnizInterface.equality type)) x) y

@[simp] theorem rawEquality_rename {n m : Nat} (rho : Ren n m)
    (type : HOL.Ty BaseSort) (x y : Tower.Tm n) :
    rename rho (rawEquality type x y) = rawEquality type (rename rho x) (rename rho y) := by
  simp only [rawEquality, rename, rename_liftClosed]

@[simp] theorem rawEquality_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty BaseSort) (x y : Tower.Tm n) :
    subst sigma (rawEquality type x y) = rawEquality type (subst sigma x) (subst sigma y) := by
  simp only [rawEquality, subst, subst_liftClosed]

theorem represent_eq {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (x y : HOL.Term Symbol gamma type) :
    represent (.eq x y) = (do
      let xc ← represent x
      let yc ← represent y
      pure (rawEquality type xc yc)) := by
  simp only [represent, FormationSensitiveHOLInterface.represent]
  cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature x <;>
    cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature y <;> rfl

theorem represent_app {gamma : SourceContext} {a b : HOL.Ty BaseSort}
    (f : HOL.Term Symbol gamma (.arr a b)) (x : HOL.Term Symbol gamma a) :
    represent (.app f x) = (do
      let fc ← represent f
      let xc ← represent x
      pure (.app fc xc)) := rfl

theorem represent_lam {gamma : SourceContext} {a b : HOL.Ty BaseSort}
    (body : HOL.Term Symbol (a :: gamma) b) :
    represent (.lam body) = (represent body).map Tm.lam := rfl

theorem represent_imp {gamma : SourceContext} (p q : Formula gamma) :
    represent (.imp p q) = (do
      let pc ← represent p
      let qc ← represent q
      pure (FormationSensitiveHOLUniformList.rawImp pc qc)) := by
  simp only [represent, FormationSensitiveHOLInterface.represent]
  cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature p <;>
    cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature q <;> rfl

theorem represent_all {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (p : Formula (type :: gamma)) :
    represent (.all p) = (represent p).map
      (FormationSensitiveHOLUniformList.rawAll type) := by
  simp only [represent, FormationSensitiveHOLInterface.represent]
  cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLLeibnizInterface.signature p <;> rfl

theorem represent_weaken {gamma : SourceContext} {type a : HOL.Ty BaseSort}
    (p : HOL.Term Symbol gamma type) :
    represent (HOL.weaken (σ := a) p) = (represent p).map (rename wk) :=
  FormationSensitiveHOLInterface.represent_rename _ HOL.Rename.weaken wk (fun _ => rfl) p

theorem represent_instantiate {gamma : SourceContext} {type a : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma a) (body : HOL.Term Symbol (a :: gamma) type)
    {code : Tower.Tm gamma.length} (represented : represent term = some code) :
    represent (HOL.instantiate term body) = (represent body).map (inst0 code) := by
  apply FormationSensitiveHOLInterface.represent_subst _ (HOL.Subst.single term) (subst0 code)
  intro b index
  cases index with
  | vz => exact represented
  | vs prior => rfl

def compile {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Option (Tower.Tm n) :=
  match source with
  | .hyp occurrence => some (hypotheses occurrence)
  | @HOL.ProofSyntax.impI _ _ gamma delta p _ body => do
      let _ ← represent p
      let nativeBody ← compile body (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i)))
      pure (.lam nativeBody)
  | .impE function argument => do
      let nativeFunction ← compile function objects hypotheses
      let nativeArgument ← compile argument objects hypotheses
      pure (.app nativeFunction nativeArgument)
  | .allI body => do
      let nativeBody ← compile body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
      pure (.lam nativeBody)
  | .allE term function => do
      let nativeArgument ← represent term
      let nativeFunction ← compile function objects hypotheses
      pure (.app nativeFunction (subst objects nativeArgument))
  | .eqRefl term => do
      let _ ← represent term
      pure FormationSensitiveHOLLeibnizDerived.reflTerm
  | @HOL.ProofSyntax.eqSymm _ _ _ _ type x y comparison => do
      let xc ← represent x
      let _ ← represent y
      let h ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.symmetry type (subst objects xc) h)
  | @HOL.ProofSyntax.eqTrans _ _ _ _ type x y z first second => do
      let xc ← represent x
      let _ ← represent y
      let _ ← represent z
      let h ← compile first objects hypotheses
      let k ← compile second objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.transitivity type (subst objects xc) h k)
  | @HOL.ProofSyntax.eqApp _ _ _ _ _ result f g x comparison => do
      let fc ← represent f
      let _ ← represent g
      let xc ← represent x
      let h ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.functionCongruence result
        (subst objects fc) (subst objects xc) h)
  | @HOL.ProofSyntax.eqAppArg _ _ _ _ _ result f x y comparison => do
      let fc ← represent f
      let xc ← represent x
      let _ ← represent y
      let h ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.congruence result
        (subst objects fc) (subst objects xc) h)
  | @HOL.ProofSyntax.eqPropEL _ _ _ _ p q comparison => do
      let _ ← represent p
      let _ ← represent q
      let h ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.propForward h)
  | @HOL.ProofSyntax.eqPropER _ _ _ _ p q comparison => do
      let pc ← represent p
      let _ ← represent q
      let h ← compile comparison objects hypotheses
      pure (FormationSensitiveHOLLeibnizDerived.propForward
        (FormationSensitiveHOLLeibnizDerived.symmetry .prop (subst objects pc) h))
  | .beta term body => do
      let _ ← represent term
      let _ ← represent body
      pure FormationSensitiveHOLLeibnizDerived.reflTerm
  | _ => none

theorem compile_cast_conclusion {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi psi : Formula gamma} (equal : phi = psi)
    (source : HOL.ProofSyntax Symbol delta phi) {n : Nat}
    (objects : Sub Tower.Head gamma.length n) (hypotheses : Fin delta.length → Tower.Tm n) :
    compile (cast (congrArg (HOL.ProofSyntax Symbol delta) equal) source) objects hypotheses =
      compile source objects hypotheses := by
  cases equal
  rfl

/-- Moving the native environment through a substitution moves the emitted
proof term by that same substitution, including under both kinds of binder. -/
theorem compile_substitute {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n m : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (sigma : Sub Tower.Head n m) :
    compile source (fun i => subst sigma (objects i))
        (fun i => subst sigma (hypotheses i)) =
      (compile source objects hypotheses).map (subst sigma) := by
  induction source generalizing n m with
  | hyp occurrence => rfl
  | @impI gamma delta p q body ih =>
      have obj : (fun i => rename wk (subst sigma (objects i))) =
          (fun i => subst (liftSub sigma) (rename wk (objects i))) := by
        funext i
        simp only [subst_liftSub_wk]
      have hyp : Fin.cases (.var 0) (fun i => rename wk (subst sigma (hypotheses i))) =
          (fun i => subst (liftSub sigma)
            (Fin.cases (.var 0) (fun j => rename wk (hypotheses j)) i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      simp only [compile, obj, hyp]
      erw [ih (fun i => rename wk (objects i))
        (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) (liftSub sigma)]
      cases represent p <;>
        cases compile body (fun i => rename wk (objects i))
          (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) <;> rfl
  | impE function argument ihf iha =>
      simp only [compile, ihf, iha]
      cases compile function objects hypotheses <;>
        cases compile argument objects hypotheses <;> rfl
  | @allI gamma delta type phi body ih =>
      have obj : liftSub (fun i => subst sigma (objects i)) =
          (fun i => subst (liftSub sigma) (liftSub objects i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [liftSub]
      have hyp : (fun i : Fin (HOL.weakenHyps (σ := type) delta).length =>
          rename wk (subst sigma (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) =
          (fun i => subst (liftSub sigma)
            (rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))) := by
        funext i
        simp only [subst_liftSub_wk]
      simp only [compile, obj, hyp]
      erw [ih (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps]))))
        (liftSub sigma)]
      cases compile body (liftSub objects)
        (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) <;> rfl
  | allE term function ih =>
      simp only [compile, ih]
      cases represent term with
      | none => rfl
      | some code =>
          cases compile function objects hypotheses with
          | none => rfl
          | some native => simp [subst, subst_comp]
  | eqRefl term => simp only [compile]; cases represent term <;> rfl
  | @eqSymm gamma delta type x y comparison ih =>
      simp only [compile, ih]
      cases represent x <;> cases represent y <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.symmetry_subst]
  | @eqTrans gamma delta type x y z first second ihh ihk =>
      simp only [compile, ihh, ihk]
      cases represent x <;> cases represent y <;> cases represent z <;>
        cases compile first objects hypotheses <;> cases compile second objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.transitivity_subst]
  | @eqApp gamma delta a b f g x comparison ih =>
      simp only [compile, ih]
      cases represent f <;> cases represent g <;> cases represent x <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.functionCongruence_subst]
  | @eqAppArg gamma delta a b f x y comparison ih =>
      simp only [compile, ih]
      cases represent f <;> cases represent x <;> cases represent y <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.congruence_subst]
  | @eqPropEL gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent p <;> cases represent q <;>
        cases compile comparison objects hypotheses <;> rfl
  | @eqPropER gamma delta p q comparison ih =>
      simp only [compile, ih]
      cases represent p <;> cases represent q <;>
        cases compile comparison objects hypotheses <;>
          simp [subst_comp, FormationSensitiveHOLLeibnizDerived.symmetry_subst,
            FormationSensitiveHOLLeibnizDerived.propForward_subst]
  | beta term body => simp only [compile]; cases represent term <;> cases represent body <;> rfl
  | _ => rfl

/-- Supplying a proof argument is the same capture-safe substitution used by
native beta reduction. This is an equation about the actual compiler output,
not an independently authored second proof. -/
theorem implication_cut_computes {gamma : SourceContext} {delta : List (Formula gamma)}
    {p q : Formula gamma} (body : HOL.ProofSyntax Symbol (p :: delta) q)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) (argument : Tower.Tm n)
    {nativeBody : Tower.Tm (n + 1)}
    (compiled : compile body (fun i => rename wk (objects i))
      (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) = some nativeBody) :
    compile body objects (Fin.cases argument hypotheses) = some (inst0 argument nativeBody) ∧
      Step FormationSensitiveHOLProofFamily.rules.headEq (.app (.lam nativeBody) argument)
        (inst0 argument nativeBody) FormationSensitiveHOLProofFamily.rules.computation := by
  have substitution := compile_substitute body (fun i => rename wk (objects i))
    (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) (subst0 argument)
  have objectEquation : (fun i => subst (subst0 argument) (rename wk (objects i))) = objects := by
    funext i
    exact inst0_rename_wk argument (objects i)
  have hypothesisEquation :
      (fun i => subst (subst0 argument)
        (Fin.cases (.var 0) (fun j => rename wk (hypotheses j)) i)) =
      Fin.cases argument hypotheses := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact inst0_rename_wk argument (hypotheses j)
  rw [objectEquation] at substitution
  erw [hypothesisEquation, compiled] at substitution
  exact ⟨substitution, Step.betaPi nativeBody argument⟩

namespace NativeTyping

open FormationSensitive

def Objects {gamma : SourceContext} {n : Nat} (target : Tower.Ctx n)
    (objects : Sub Tower.Head gamma.length n) : Prop :=
  FormationSensitive.CtxMor FormationSensitiveHOLProofFamily.rules (FormationSensitiveHOLInterface.context FormationSensitiveHOLUniformList.types gamma) target objects

def Hypotheses {gamma : SourceContext} {delta : List (Formula gamma)}
    {n : Nat} (target : Tower.Ctx n) (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin delta.length → Tower.Tm n) : Prop :=
  ∀ i, ∃ code, represent (delta.get i) = some code ∧
    Typing FormationSensitiveHOLProofFamily.rules target (hypotheses i) (FormationSensitiveHOLProofFamily.proof (subst objects code))

theorem represented_typed {gamma : SourceContext} {type : HOL.Ty BaseSort}
    {term : HOL.Term Symbol gamma type} {code : Tower.Tm gamma.length}
    (represented : represent term = some code) {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n} (typed : Objects target objects) :
    Typing FormationSensitiveHOLProofFamily.rules target (subst objects code) (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type) := by
  have source := FormationSensitiveHOLProofFamily.include_typed (FormationSensitiveHOLInterface.represent_typed FormationSensitiveHOLLeibnizInterface.signature term represented)
  simpa only [FormationSensitiveHOLInterface.typeAt_subst,
    FormationSensitiveHOLLeibnizInterface.signature,
    FormationSensitiveHOLUniformList.signature] using source.substitute typed

theorem Objects.weaken {gamma : SourceContext} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n} (typed : Objects target objects)
    (extension : Tower.Tm n) :
    Objects (.snoc target extension) (fun i => rename wk (objects i)) := by
  intro i
  simpa only [rename_subst] using (typed i).weaken (extension := extension)

theorem Objects.lift {gamma : SourceContext} {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n} (typed : Objects target objects)
    (type : HOL.Ty BaseSort) :
    Objects (gamma := type :: gamma) (.snoc target (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
      (liftSub objects) := by
  simpa only [Objects, FormationSensitiveHOLInterface.context, FormationSensitiveHOLInterface.typeAt_subst] using
    FormationSensitive.CtxMor.lift typed (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types gamma.length type)

theorem Hypotheses.prepend {gamma : SourceContext} {delta : List (Formula gamma)}
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} (typed : Hypotheses target objects hypotheses)
    {p : Formula gamma} {pc : Tower.Tm gamma.length} (represented : represent p = some pc) :
    Hypotheses (delta := p :: delta) (.snoc target (FormationSensitiveHOLProofFamily.proof (subst objects pc)))
      (fun i => rename wk (objects i))
      (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨pc, represented, ?_⟩
    simpa only [Fin.cases_zero, Ctx.lookup_snoc_zero, FormationSensitiveHOLProofFamily.proof_rename, rename_subst] using
      (Typing.var (R := FormationSensitiveHOLProofFamily.rules) (Γ := .snoc target (FormationSensitiveHOLProofFamily.proof (subst objects pc))) 0)
  · obtain ⟨code, success, admitted⟩ := typed j
    refine ⟨code, success, ?_⟩
    simpa only [Fin.cases_succ, FormationSensitiveHOLProofFamily.proof_rename, rename_subst] using
      admitted.weaken (extension := FormationSensitiveHOLProofFamily.proof (subst objects pc))

theorem Hypotheses.lift {gamma : SourceContext} {delta : List (Formula gamma)}
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} (typed : Hypotheses target objects hypotheses)
    (type : HOL.Ty BaseSort) :
    Hypotheses (delta := HOL.weakenHyps (σ := type) delta)
      (.snoc target (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type)) (liftSub objects)
      (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) := by
  intro i
  obtain ⟨code, success, admitted⟩ := typed (i.cast (by simp [HOL.weakenHyps]))
  refine ⟨rename wk code, ?_, ?_⟩
  · have entry : (HOL.weakenHyps (σ := type) delta).get i =
        HOL.weaken (delta.get (i.cast (by simp [HOL.weakenHyps]))) := by
      have indexValid : i.val < delta.length := by simpa [HOL.weakenHyps] using i.isLt
      change (delta.map (HOL.weaken (σ := type)))[i.val] = HOL.weaken delta[i.val]
      simp only [List.getElem_map]
    rw [entry, represent_weaken, success]
    rfl
  · simpa only [subst_liftSub_wk, ← FormationSensitiveHOLProofFamily.proof_rename] using
      admitted.weaken (extension := FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type)

open FormationSensitiveHOLProofFamily
open FormationSensitiveHOLUniformList (rawImp rawAll)

theorem equality_proposition {n : Nat} {target : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm n}
    (hx : Typing rules target x (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (hy : Typing rules target y (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type)) :
    Typing rules target (rawEquality type x y) (.const `HOLUniformList.prop) := by
  have declared := include_typed (FormationSensitiveHOLLeibnizInterface.equality_typed_at type target)
  exact FormationSensitiveHOLLeibnizRules.application_typed
    (FormationSensitiveHOLLeibnizRules.application_typed declared hx) hy

theorem equality_conversion {n : Nat} (type : HOL.Ty BaseSort) (x y : Tower.Tm n) :
    Conv rules.headEq (proof (rawEquality type x y))
      (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz type x y)) rules.computation :=
  Conv.congApp (.refl _) (FormationSensitiveHOLLeibnizInterface.Decoded.include_conversion
    (FormationSensitiveHOLLeibnizInterface.equality_application_conversion type x y))

theorem equality_to_predicate {n : Nat} {target : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h : Tower.Tm n}
    (hx : Typing rules target x (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (hy : Typing rules target y (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (comparison : Typing rules target h (proof (rawEquality type x y))) :
    Typing rules target h (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz type x y)) :=
  .conv comparison (proof_formed (FormationSensitiveHOLLeibnizRules.rawLeibniz_typed hx hy))
    (.sort Tower.zero) (equality_conversion type x y)

theorem equality_from_predicate {n : Nat} {target : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y h : Tower.Tm n}
    (hx : Typing rules target x (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (hy : Typing rules target y (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (comparison : Typing rules target h (proof (FormationSensitiveHOLLeibnizInterface.rawLeibniz type x y))) :
    Typing rules target h (proof (rawEquality type x y)) :=
  .conv comparison (proof_formed (equality_proposition hx hy))
    (.sort Tower.zero) (.symm _ _ (equality_conversion type x y))

theorem equality_reflexivity {n : Nat} {target : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x : Tower.Tm n}
    (hx : Typing rules target x (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type)) :
    Typing rules target FormationSensitiveHOLLeibnizDerived.reflTerm (proof (rawEquality type x x)) :=
  equality_from_predicate hx hx (FormationSensitiveHOLLeibnizRules.reflexivity hx)

theorem equality_of_conversion {n : Nat} {target : Tower.Ctx n} {type : HOL.Ty BaseSort}
    {x y : Tower.Tm n}
    (hx : Typing rules target x (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (hy : Typing rules target y (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type))
    (conversion : Conv rules.headEq x y rules.computation) :
    Typing rules target FormationSensitiveHOLLeibnizDerived.reflTerm (proof (rawEquality type x y)) :=
  .conv (equality_reflexivity hx) (proof_formed (equality_proposition hx hy))
    (.sort Tower.zero) (Conv.congApp (.refl _) (Conv.congApp (.refl _) conversion))

theorem represented_equality {gamma : SourceContext} {type : HOL.Ty BaseSort}
    {x y : HOL.Term Symbol gamma type} {xc yc code : Tower.Tm gamma.length}
    (hx : represent x = some xc) (hy : represent y = some yc)
    (represented : represent (.eq x y) = some code)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n} {native : Tower.Tm n}
    (typed : Typing rules target native (proof (subst objects code))) :
    Typing rules target native (proof (rawEquality type (subst objects xc) (subst objects yc))) := by
  have shape : code = rawEquality type xc yc := by
    simpa [represent_eq, hx, hy, eq_comm] using represented
  subst code
  simpa only [rawEquality_subst] using typed

/-- Every successful translation is checked by the existing native dependent
typing rules against the represented source conclusion. The hypothesis
environment must contain actual native inhabitants of the source assumptions.
No proof-rule preservation law is an assumption of this theorem. -/
theorem compile_typed {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (objectTyped : Objects target objects) (hypothesisTyped : Hypotheses target objects hypotheses)
    (success : compile source objects hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      Typing rules target native (proof (subst objects code)) := by
  induction source generalizing n with
  | hyp occurrence =>
      simp only [compile, Option.some.injEq] at success
      subst native
      exact hypothesisTyped occurrence
  | @impI gamma delta p q body ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hb : compile body (fun i => rename wk (objects i))
              (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) with
          | none => simp [compile, hp, hb] at success
          | some b =>
              simp [compile, hp, hb] at success
              subst native
              obtain ⟨qc, hq, bodyTyped⟩ := ih (objectTyped.weaken (proof (subst objects pc)))
                (hypothesisTyped.prepend hp) hb
              refine ⟨rawImp pc qc, by simp [represent_imp, hp, hq], ?_⟩
              apply implication_intro (represented_typed hp objectTyped)
                (represented_typed hq objectTyped)
              simpa only [proof_rename, rename_subst] using bodyTyped
  | @impE gamma delta p q function argument ihf iha =>
      cases hf : compile function objects hypotheses with
      | none => simp [compile, hf] at success
      | some f =>
          cases ha : compile argument objects hypotheses with
          | none => simp [compile, hf, ha] at success
          | some a =>
              simp [compile, hf, ha] at success
              subst native
              obtain ⟨fc, hfc, ft⟩ := ihf objectTyped hypothesisTyped hf
              obtain ⟨pc, hp, argumentTyped⟩ := iha objectTyped hypothesisTyped ha
              cases hq : represent q with
              | none => simp [represent_imp, hp, hq] at hfc
              | some qc =>
                  have shape : fc = rawImp pc qc := by
                    simpa [represent_imp, hp, hq, eq_comm] using hfc
                  subst fc
                  exact ⟨qc, rfl, implication_elim (represented_typed hp objectTyped)
                    (represented_typed hq objectTyped) ft argumentTyped⟩
  | @allI gamma delta type phi body ih =>
      cases hb : compile body (liftSub objects)
          (fun i => rename wk (hypotheses (i.cast (by simp [HOL.weakenHyps])))) with
      | none => simp [compile, hb] at success
      | some b =>
          simp [compile, hb] at success
          subst native
          obtain ⟨pc, hp, bt⟩ := ih (objectTyped.lift type) (hypothesisTyped.lift type) hb
          refine ⟨rawAll type pc, by rw [represent_all, hp]; rfl, ?_⟩
          have intro := universal_intro (simple_type_formed type target)
            (represented_typed hp (objectTyped.lift type)) bt
          simpa only [rawAll, FormationSensitiveHOLUniformList.universal,
            universalProposition, liftClosed, Presentation.rename,
            Presentation.subst, FormationSensitiveHOLInterface.typeAt_rename,
            FormationSensitiveHOLInterface.typeAt_subst] using intro
  | @allE gamma delta type phi term function ih =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some tc =>
          cases hf : compile function objects hypotheses with
          | none => simp [compile, ht, hf] at success
          | some f =>
              simp [compile, ht, hf] at success
              subst native
              obtain ⟨fc, hfc, ft⟩ := ih objectTyped hypothesisTyped hf
              cases hp : represent phi with
              | none => simp [represent_all, hp] at hfc
              | some pc =>
                  have shape : fc = rawAll type pc := by
                    simpa [represent_all, hp, eq_comm] using hfc
                  subst fc
                  refine ⟨inst0 tc pc, by rw [represent_instantiate term phi ht, hp]; rfl, ?_⟩
                  have fm : Typing rules target f
                      (proof (universalProposition
                        (FormationSensitiveHOLInterface.typeAt FormationSensitiveHOLUniformList.types n type)
                        (.lam (subst (liftSub objects) pc)))) := by
                    simpa only [rawAll, FormationSensitiveHOLUniformList.universal,
                      universalProposition, liftClosed, Presentation.rename,
                      Presentation.subst, FormationSensitiveHOLInterface.typeAt_rename,
                      FormationSensitiveHOLInterface.typeAt_subst] using ft
                  have elimination := universal_elim (simple_type_formed type target)
                    (represented_typed hp (objectTyped.lift type)) fm
                    (represented_typed ht objectTyped)
                  simpa only [subst_inst0] using elimination
  | @eqRefl gamma delta type term =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some tc =>
          simp [compile, ht] at success
          subst native
          refine ⟨rawEquality type tc tc, by simp [represent_eq, ht], ?_⟩
          simpa only [rawEquality_subst] using equality_reflexivity (represented_typed ht objectTyped)
  | @eqSymm gamma delta type x y comparison ih =>
      cases hx : represent x with
      | none => simp [compile, hx] at success
      | some xc =>
          cases hy : represent y with
          | none => simp [compile, hx, hy] at success
          | some yc =>
              cases hh : compile comparison objects hypotheses with
              | none => simp [compile, hx, hy, hh] at success
              | some h =>
                  simp [compile, hx, hy, hh] at success
                  subst native
                  obtain ⟨code, represented, admitted⟩ := ih objectTyped hypothesisTyped hh
                  have input := represented_equality hx hy represented admitted
                  refine ⟨rawEquality type yc xc, by simp [represent_eq, hx, hy], ?_⟩
                  simpa only [rawEquality_subst] using equality_from_predicate (represented_typed hy objectTyped) (represented_typed hx objectTyped)
                    (FormationSensitiveHOLLeibnizDerived.symmetry_typed (represented_typed hx objectTyped) (represented_typed hy objectTyped)
                      (equality_to_predicate (represented_typed hx objectTyped) (represented_typed hy objectTyped) input))
  | @eqTrans gamma delta type x y z first second ihh ihk =>
      cases hx : represent x with
      | none => simp [compile, hx] at success
      | some xc =>
          cases hy : represent y with
          | none => simp [compile, hx, hy] at success
          | some yc =>
              cases hz : represent z with
              | none => simp [compile, hx, hy, hz] at success
              | some zc =>
                  cases hh : compile first objects hypotheses with
                  | none => simp [compile, hx, hy, hz, hh] at success
                  | some h =>
                      cases hk : compile second objects hypotheses with
                      | none => simp [compile, hx, hy, hz, hh, hk] at success
                      | some k =>
                          simp [compile, hx, hy, hz, hh, hk] at success
                          subst native
                          obtain ⟨firstCode, firstRepresented, firstAdmitted⟩ := ihh objectTyped hypothesisTyped hh
                          obtain ⟨secondCode, secondRepresented, secondAdmitted⟩ := ihk objectTyped hypothesisTyped hk
                          have firstInput := represented_equality hx hy firstRepresented firstAdmitted
                          have secondInput := represented_equality hy hz secondRepresented secondAdmitted
                          refine ⟨rawEquality type xc zc, by simp [represent_eq, hx, hz], ?_⟩
                          simpa only [rawEquality_subst] using equality_from_predicate (represented_typed hx objectTyped) (represented_typed hz objectTyped)
                            (FormationSensitiveHOLLeibnizDerived.transitivity_typed (represented_typed hx objectTyped) (represented_typed hy objectTyped) (represented_typed hz objectTyped)
                              (equality_to_predicate (represented_typed hx objectTyped) (represented_typed hy objectTyped) firstInput)
                              (equality_to_predicate (represented_typed hy objectTyped) (represented_typed hz objectTyped) secondInput))
  | @eqApp gamma delta a b f g x comparison ih =>
      cases hf : represent f with
      | none => simp [compile, hf] at success
      | some fc =>
          cases hg : represent g with
          | none => simp [compile, hf, hg] at success
          | some gc =>
              cases hx : represent x with
              | none => simp [compile, hf, hg, hx] at success
              | some xc =>
                  cases hh : compile comparison objects hypotheses with
                  | none => simp [compile, hf, hg, hx, hh] at success
                  | some h =>
                      simp [compile, hf, hg, hx, hh] at success
                      subst native
                      obtain ⟨code, represented, admitted⟩ := ih objectTyped hypothesisTyped hh
                      have input := represented_equality hf hg represented admitted
                      have fx := FormationSensitiveHOLLeibnizRules.application_typed (represented_typed hf objectTyped) (represented_typed hx objectTyped)
                      have gx := FormationSensitiveHOLLeibnizRules.application_typed (represented_typed hg objectTyped) (represented_typed hx objectTyped)
                      refine ⟨rawEquality b (.app fc xc) (.app gc xc), by simp [represent_eq, represent_app, hf, hg, hx], ?_⟩
                      simpa only [rawEquality_subst, subst] using equality_from_predicate fx gx
                        (FormationSensitiveHOLLeibnizDerived.functionCongruence_typed (represented_typed hf objectTyped) (represented_typed hg objectTyped) (represented_typed hx objectTyped)
                          (equality_to_predicate (represented_typed hf objectTyped) (represented_typed hg objectTyped) input))
  | @eqAppArg gamma delta a b f x y comparison ih =>
      cases hf : represent f with
      | none => simp [compile, hf] at success
      | some fc =>
          cases hx : represent x with
          | none => simp [compile, hf, hx] at success
          | some xc =>
              cases hy : represent y with
              | none => simp [compile, hf, hx, hy] at success
              | some yc =>
                  cases hh : compile comparison objects hypotheses with
                  | none => simp [compile, hf, hx, hy, hh] at success
                  | some h =>
                      simp [compile, hf, hx, hy, hh] at success
                      subst native
                      obtain ⟨code, represented, admitted⟩ := ih objectTyped hypothesisTyped hh
                      have input := represented_equality hx hy represented admitted
                      have fx := FormationSensitiveHOLLeibnizRules.application_typed (represented_typed hf objectTyped) (represented_typed hx objectTyped)
                      have fy := FormationSensitiveHOLLeibnizRules.application_typed (represented_typed hf objectTyped) (represented_typed hy objectTyped)
                      refine ⟨rawEquality b (.app fc xc) (.app fc yc), by simp [represent_eq, represent_app, hf, hx, hy], ?_⟩
                      simpa only [rawEquality_subst, subst] using equality_from_predicate fx fy
                        (FormationSensitiveHOLLeibnizDerived.congruence_typed (represented_typed hf objectTyped) (represented_typed hx objectTyped) (represented_typed hy objectTyped)
                          (equality_to_predicate (represented_typed hx objectTyped) (represented_typed hy objectTyped) input))
  | @eqPropEL gamma delta p q comparison ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hq : represent q with
          | none => simp [compile, hp, hq] at success
          | some qc =>
              cases hh : compile comparison objects hypotheses with
              | none => simp [compile, hp, hq, hh] at success
              | some h =>
                  simp [compile, hp, hq, hh] at success
                  subst native
                  obtain ⟨code, represented, admitted⟩ := ih objectTyped hypothesisTyped hh
                  have input := represented_equality hp hq represented admitted
                  refine ⟨rawImp pc qc, by simp [represent_imp, hp, hq], ?_⟩
                  exact FormationSensitiveHOLLeibnizDerived.propForward_typed (represented_typed hp objectTyped) (represented_typed hq objectTyped)
                    (equality_to_predicate (represented_typed hp objectTyped) (represented_typed hq objectTyped) input)
  | @eqPropER gamma delta p q comparison ih =>
      cases hp : represent p with
      | none => simp [compile, hp] at success
      | some pc =>
          cases hq : represent q with
          | none => simp [compile, hp, hq] at success
          | some qc =>
              cases hh : compile comparison objects hypotheses with
              | none => simp [compile, hp, hq, hh] at success
              | some h =>
                  simp [compile, hp, hq, hh] at success
                  subst native
                  obtain ⟨code, represented, admitted⟩ := ih objectTyped hypothesisTyped hh
                  have input := represented_equality hp hq represented admitted
                  refine ⟨rawImp qc pc, by simp [represent_imp, hp, hq], ?_⟩
                  exact FormationSensitiveHOLLeibnizDerived.propBackward_typed (represented_typed hp objectTyped) (represented_typed hq objectTyped)
                    (equality_to_predicate (represented_typed hp objectTyped) (represented_typed hq objectTyped) input)
  | @beta gamma delta a b term body =>
      cases ht : represent term with
      | none => simp [compile, ht] at success
      | some tc =>
          cases hb : represent body with
          | none => simp [compile, ht, hb] at success
          | some bc =>
              simp [compile, ht, hb] at success
              subst native
              have sourceRepresentation : represent (.app (.lam body) term) = some (.app (.lam bc) tc) := by
                simp [represent_app, represent_lam, ht, hb]
              have targetRepresentation : represent (HOL.instantiate term body) = some (inst0 tc bc) := by
                rw [represent_instantiate term body ht, hb]
                rfl
              refine ⟨rawEquality b (.app (.lam bc) tc) (inst0 tc bc),
                by simp [represent_eq, sourceRepresentation, targetRepresentation], ?_⟩
              rw [rawEquality_subst]
              apply equality_of_conversion (represented_typed sourceRepresentation objectTyped)
                (represented_typed targetRepresentation objectTyped)
              simpa only [subst, subst_inst0] using
                FormationSensitiveHOLLeibnizDerived.beta_conversion (subst (liftSub objects) bc) (subst objects tc)
  | _ => simp [compile] at success

/-- The compiler preserves the complete judgment when used in a formed
native telescope, not merely the raw typing relation. -/
theorem compile_judgment {gamma : SourceContext} {delta : List (Formula gamma)}
    {phi : Formula gamma} (source : HOL.ProofSyntax Symbol delta phi)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {native : Tower.Tm n}
    (formed : ContextFormation rules target)
    (objectTyped : Objects target objects) (hypothesisTyped : Hypotheses target objects hypotheses)
    (success : compile source objects hypotheses = some native) :
    ∃ code, represent phi = some code ∧
      Judgment rules target native (proof (subst objects code)) := by
  obtain ⟨code, represented, typed⟩ := compile_typed source objectTyped hypothesisTyped success
  exact ⟨code, represented, formed, typed⟩

/-- Closed proof translation has no object or proof assumptions to supply. -/
theorem compile_closed {phi : Formula []} (source : HOL.ProofSyntax Symbol [] phi)
    {native : Tower.Tm 0}
    (success : compile source Fin.elim0 Fin.elim0 = some native) :
    ∃ code, represent phi = some code ∧
      Judgment rules .nil native (proof code) := by
  obtain ⟨code, represented, typed⟩ := compile_judgment source .nil
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) success
  refine ⟨code, represented, ?_⟩
  have emptySub : (Fin.elim0 : Sub Tower.Head 0 0) = ids := by funext i; exact Fin.elim0 i
  simpa only [emptySub, subst_ids] using typed


end NativeTyping

namespace Controls

/-- Function extensionality is not introduced by translating constructive
equality elimination. Even a valid instance remains unsupported here. -/
theorem extensionality_not_compiled :
    compile (HOL.ProofSyntax.funExt (Const := Symbol) (Δ := [])
      (f := HOL.Term.lam (Γ := []) (σ := .prop) (.var .vz))
      (g := HOL.Term.lam (Γ := []) (σ := .prop) (.var .vz))
      (.allI (.eqRefl (.app (HOL.weaken (.lam (.var .vz))) (.var .vz)))))
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

theorem lambda_equality_not_compiled :
    compile (HOL.ProofSyntax.eqLam (Const := Symbol) (Δ := [])
      (.eqRefl (HOL.Term.var (Γ := [.prop]) .vz)))
      (n := 0) Fin.elim0 Fin.elim0 = none := rfl

theorem propositional_extensionality_not_compiled :
    compile (HOL.ProofSyntax.eqPropI (Const := Symbol) (Δ := [])
      (p := HOL.Term.var (Γ := [.prop]) .vz) (q := .var .vz)
      (.impI (.hyp 0)) (.impI (.hyp 0)))
      (n := 1) ids Fin.elim0 = none := rfl

end Controls

#print axioms compile_substitute
#print axioms NativeTyping.equality_of_conversion
#print axioms NativeTyping.compile_typed
#print axioms NativeTyping.compile_judgment
#print axioms NativeTyping.compile_closed
#print axioms Controls.extensionality_not_compiled
#print axioms Controls.lambda_equality_not_compiled
#print axioms Controls.propositional_extensionality_not_compiled

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizNativeProofTranslation
