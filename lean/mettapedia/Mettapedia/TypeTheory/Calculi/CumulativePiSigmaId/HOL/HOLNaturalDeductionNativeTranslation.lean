import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofFamily
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofConversion
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Native terms from retained HOL natural deduction

The source is the existing indexed HOL proof syntax. This partial translation
handles hypotheses, implication and universal introduction/elimination; it
returns no term for an unsupported proof rule. Object variables and proof
hypotheses have separate environments, but both are realized by variables in
the same native dependent telescope. In particular, object quantification
does not reset or capture the proof environment.

The translation constructs ordinary native lambdas and applications. It does
not replace an unsupported inference by an opaque proof constant, recover a
proof from semantic truth, or select a language profile.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNaturalDeductionNativeTranslation

open Presentation Mettapedia.Logic
open HOL.UniformListInduction

abbrev SourceContext := HOL.Ctx BaseSort
abbrev Formula (gamma : SourceContext) := HOL.Formula Symbol gamma

def represent {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (term : HOL.Term Symbol gamma type) : Option (Tower.Tm gamma.length) :=
  FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature term

theorem represent_imp {gamma : SourceContext} (p q : Formula gamma) :
    represent (.imp p q) = (do
      let pc ← represent p
      let qc ← represent q
      pure (FormationSensitiveHOLUniformList.rawImp pc qc)) := by
  simp only [represent, FormationSensitiveHOLInterface.represent]
  cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature p <;>
    cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature q <;> rfl

theorem represent_all {gamma : SourceContext} {type : HOL.Ty BaseSort}
    (p : Formula (type :: gamma)) :
    represent (.all p) = (represent p).map
      (FormationSensitiveHOLUniformList.rawAll type) := by
  simp only [represent, FormationSensitiveHOLInterface.represent]
  cases FormationSensitiveHOLInterface.represent FormationSensitiveHOLUniformList.signature p <;> rfl

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
  have source := FormationSensitiveHOLProofFamily.include_typed (FormationSensitiveHOLInterface.represent_typed FormationSensitiveHOLUniformList.signature term represented)
  simpa only [FormationSensitiveHOLInterface.typeAt_subst,
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

/-- The compiler's proof substitution and the decoder's typed beta law meet
on the same native term, telescope and conclusion. -/
theorem implication_cut_judgment {gamma : SourceContext} {delta : List (Formula gamma)}
    {p q : Formula gamma} (body : HOL.ProofSyntax Symbol (p :: delta) q)
    {pc : Tower.Tm gamma.length} (represented : represent p = some pc)
    {n : Nat} {target : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin delta.length → Tower.Tm n} {argument : Tower.Tm n}
    {nativeBody : Tower.Tm (n + 1)}
    (formed : ContextFormation rules target)
    (objectTyped : Objects target objects) (hypothesisTyped : Hypotheses target objects hypotheses)
    (argumentTyped : Typing rules target argument (proof (subst objects pc)))
    (compiled : compile body (fun i => rename wk (objects i))
      (Fin.cases (.var 0) (fun i => rename wk (hypotheses i))) = some nativeBody) :
    ∃ qc, represent q = some qc ∧
      compile body objects (Fin.cases argument hypotheses) = some (inst0 argument nativeBody) ∧
      Judgment rules target (.app (.lam nativeBody) argument) (proof (subst objects qc)) ∧
      Step rules.headEq (.app (.lam nativeBody) argument) (inst0 argument nativeBody)
        rules.computation ∧
      Judgment rules target (inst0 argument nativeBody) (proof (subst objects qc)) := by
  obtain ⟨qc, hq, bodyTyped⟩ := compile_typed body
    (objectTyped.weaken (proof (subst objects pc))) (hypothesisTyped.prepend represented) compiled
  have aligned : Typing rules (.snoc target (proof (subst objects pc))) nativeBody
      (rename wk (proof (subst objects qc))) := by
    simpa only [proof_rename, rename_subst] using bodyTyped
  obtain ⟨before, step, after⟩ := FormationSensitiveHOLProofConversion.implication_beta_preserves
    (represented_typed represented objectTyped) (represented_typed hq objectTyped)
    aligned argumentTyped
  exact ⟨qc, hq, (implication_cut_computes body objects hypotheses argument compiled).1,
    ⟨formed, before⟩, step, ⟨formed, after⟩⟩

end NativeTyping

/-! The independent expected terms expose both sorts of binder. -/

def implicationIdentity {gamma : SourceContext} (p : Formula gamma) :
    HOL.ProofSyntax Symbol [] (.imp p p) := .impI (.hyp 0)

theorem compile_implicationIdentity {gamma : SourceContext} (p : Formula gamma)
    {code : Tower.Tm gamma.length} (represented : represent p = some code)
    {n : Nat} (objects : Sub Tower.Head gamma.length n) :
    compile (implicationIdentity p) objects Fin.elim0 = some (.lam (.var 0)) := by
  simp [implicationIdentity, compile, represented]

def transitivity {gamma : SourceContext} (p q r : Formula gamma) :
    HOL.ProofSyntax Symbol [] (.imp (.imp p q) (.imp (.imp q r) (.imp p r))) :=
  .impI (.impI (.impI (.impE (.hyp 1) (.impE (.hyp 2) (.hyp 0)))))

def quantifiedIdentity : HOL.ProofSyntax Symbol ([] : List (Formula []))
    (.all (.imp (.var .vz) (.var .vz))) :=
  .allI (implicationIdentity (.var .vz))

theorem compile_quantifiedIdentity :
    compile quantifiedIdentity (n := 0) Fin.elim0 Fin.elim0 =
      some (.lam (.lam (.var 0))) := rfl

def quantifiedTransitivity : HOL.ProofSyntax Symbol ([] : List (Formula []))
    (.all (.all (.all
      (.imp (.imp (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.imp (.imp (.var (.vs .vz)) (.var .vz))
          (.imp (.var (.vs (.vs .vz))) (.var .vz))))))) :=
  .allI (.allI (.allI
    (transitivity (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

theorem compile_quantifiedTransitivity :
    compile quantifiedTransitivity (n := 0) Fin.elim0 Fin.elim0 =
      some (.lam (.lam (.lam (.lam (.lam (.lam
        (.app (.var 1) (.app (.var 2) (.var 0))))))))) := rfl

theorem quantifiedTransitivity_native_judgment :
    ∃ code : Tower.Tm 0, represent (gamma := [])
      (.all (.all (.all
        (.imp (.imp (.var (.vs (.vs .vz))) (.var (.vs .vz)))
          (.imp (.imp (.var (.vs .vz)) (.var .vz))
            (.imp (.var (.vs (.vs .vz))) (.var .vz))))))) = some code ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil
        (.lam (.lam (.lam (.lam (.lam (.lam
          (.app (.var 1) (.app (.var 2) (.var 0)))))))))
        (FormationSensitiveHOLProofFamily.proof code) :=
  NativeTyping.compile_closed quantifiedTransitivity compile_quantifiedTransitivity

/-- Use the actual predicate-quantified list induction sentence. Its premise
is retained as an assumption here; applying it does not assert that arbitrary
induction-shaped declarations license native recursive definitions. -/
def applyInduction {gamma : SourceContext} (p : Expr gamma predicate) :
    HOL.ProofSyntax Symbol [inductionPrinciple, .app p nil, inductionStep p]
      (.all (.app (HOL.weaken p) (.var .vz))) := by
  have major := HOL.ProofSyntax.allE p
    (HOL.ProofSyntax.hyp (Const := Symbol)
      (Δ := [inductionPrinciple, .app p nil, inductionStep p]) 0)
  have instanceEquation : HOL.instantiate p
      (.imp (.app (.var .vz) nil)
        (.imp (inductionStep (.var .vz))
          (.all (.app (.var (.vs .vz)) (.var .vz))))) =
      .imp (.app p nil)
        (.imp (inductionStep p) (.all (.app (HOL.weaken p) (.var .vz)))) := by
    simp [inductionStep, nil, cons, HOL.instantiate, HOL.subst,
      HOL.Subst.single, HOL.Subst.lift, HOL.weaken, HOL.rename,
      HOL.Rename.weaken]
  let instanceProof := cast
    (congrArg (HOL.ProofSyntax Symbol [inductionPrinciple, .app p nil, inductionStep p])
      instanceEquation) major
  exact .impE (.impE instanceProof (.hyp 1)) (.hyp 2)

theorem compile_applyInduction {gamma : SourceContext} (p : Expr gamma predicate)
    {code : Tower.Tm gamma.length} (represented : represent p = some code)
    {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin 3 → Tower.Tm n) :
    compile (applyInduction p) objects hypotheses =
      some (.app (.app (.app (hypotheses 0) (subst objects code))
        (hypotheses 1)) (hypotheses 2)) := by
  simp only [applyInduction, compile]
  erw [compile_cast_conclusion]
  · simp [compile, represented]
  · simp [inductionStep, nil, cons, HOL.instantiate, HOL.subst,
      HOL.Subst.single, HOL.Subst.lift, HOL.weaken, HOL.rename, HOL.Rename.weaken]

/-- The same retained induction application receives an actual native proof
type; the induction principle, base and step are exactly its dependencies. -/
theorem applyInduction_native_judgment {gamma : SourceContext}
    (p : Expr gamma predicate) {code : Tower.Tm gamma.length}
    (represented : represent p = some code) {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head gamma.length n} {hypotheses : Fin 3 → Tower.Tm n}
    (formed : FormationSensitive.ContextFormation FormationSensitiveHOLProofFamily.rules target)
    (objectTyped : NativeTyping.Objects target objects)
    (hypothesisTyped : NativeTyping.Hypotheses
      (delta := [inductionPrinciple, .app p nil, inductionStep p]) target objects hypotheses) :
    ∃ conclusion, represent (.all (.app (HOL.weaken p) (.var .vz))) = some conclusion ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules target
        (.app (.app (.app (hypotheses 0) (subst objects code)) (hypotheses 1)) (hypotheses 2))
        (FormationSensitiveHOLProofFamily.proof (subst objects conclusion)) :=
  NativeTyping.compile_judgment (applyInduction p) formed objectTyped hypothesisTyped
    (compile_applyInduction p represented objects hypotheses)

/-- A proof rule outside the implemented fragment is not silently translated
to reflexivity or to a newly declared axiom. -/
theorem equalityRule_not_translated :
    compile (HOL.ProofSyntax.eqRefl (Δ := ([] : List (Formula [])))
      (nil : Expr [] sequence)) (n := 0) Fin.elim0 Fin.elim0 = none := rfl

#print axioms compile_implicationIdentity
#print axioms compile_substitute
#print axioms implication_cut_computes
#print axioms NativeTyping.compile_typed
#print axioms NativeTyping.compile_judgment
#print axioms NativeTyping.compile_closed
#print axioms NativeTyping.implication_cut_judgment
#print axioms compile_quantifiedIdentity
#print axioms compile_quantifiedTransitivity
#print axioms quantifiedTransitivity_native_judgment
#print axioms compile_applyInduction
#print axioms applyInduction_native_judgment
#print axioms equalityRule_not_translated

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNaturalDeductionNativeTranslation
