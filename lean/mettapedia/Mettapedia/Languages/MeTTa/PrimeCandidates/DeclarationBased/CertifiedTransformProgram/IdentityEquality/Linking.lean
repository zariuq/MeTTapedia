import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Carriers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Evaluation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SetHostedProfile
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLNativeProofCompilerCompleteness

/-!
# Linking every proof from the published equality and induction facts

A `set:` document proves its theorem from assumed facts.  The proof library
publishes reflexivity `refl@T` and substitution `subst@T` for each carrier it
is given, and expands symmetry, transitivity, congruence and calculations
into them; induction is the declared `num-ind`.  These facts are a fragment of
the facts the set profile publishes as a hosted profile (`Published.toHosted`),
and each is realized as there.  When every assumption of a proof is one of
these facts, linking replaces each by its realization:

* the compiler's output from the proof, with the realizations as hypotheses,
  is a closed program typed in the identity profile at the proof family of
  the theorem (`linked_typed`);
* the zero-add document is one instance;
* symmetry at a function carrier, as the proof library expands it, is
  another: at every closed function `f` its linked proof applied to `f`, `f`
  and `refl f` runs to `refl f`;
* congruence of the power set at the carrier `set` is a third: it turns a
  path `a = b` between sets into identity evidence `Power a = Power b`, and at
  every closed set `a` its linked proof applied to `a`, `a` and `refl a` runs
  to `refl (Power a)`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Linking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open FormationSensitiveHOLInterface (typeAt represent)
open SetProfile (holdsName)
open CertifiedTransformProgram.Package CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open CertifiedTransformProgram.IdentityEquality.Translation
open HOLNativeGenericProofCompiler (Modulo.compileModulo)
open Mettapedia.Logic

/-! ## Published facts -/

/-- The facts the proof library publishes. -/
inductive Published : HOL.Formula SetProfile.SetConst [] → Type
  | reflexivity (type : HOL.Ty SetProfile.SetBase) :
      Published (FormationSensitiveHOLIdentityEquality.reflexivity type)
  | substitution (type : HOL.Ty SetProfile.SetBase) : Published (Carriers.substitution type)
  | induction : Published SetProfile.inductionAxiom

/-- Each fact the proof library publishes is a fact the set profile publishes as
a hosted profile. -/
def Published.toHosted {fact : HOL.Formula SetProfile.SetConst []} :
    Published fact →
      TypedEquality.Impredicative.HostedProfile.Published ExecutableModel.CodeModel.setHostedProfile
        fact
  | .reflexivity type => .reflexivity type
  | .substitution type => .substitution type
  | .induction => .induction ExecutableModel.CodeModel.numInductive_mem

/-- The realization of a published fact: its realization as a fact of the hosted
profile. -/
def Published.realization {fact : HOL.Formula SetProfile.SetConst []}
    (published : Published fact) : Tower.Tm 0 :=
  published.toHosted.realization

theorem Published.toHosted_realization {fact : HOL.Formula SetProfile.SetConst []}
    (published : Published fact) : published.toHosted.realization = published.realization :=
  rfl

/-- Each realization is typed at the proof family of its fact. -/
theorem Published.typed {fact : HOL.Formula SetProfile.SetConst []} (published : Published fact) :
    ∃ code, represent SetProfile.signature fact = some code ∧
      Typing identityRules .nil published.realization (Holds code) := by
  cases published with
  | reflexivity type =>
      exact ⟨_, FormationSensitiveHOLIdentityEquality.reflexivity_represented SetProfile.signature type,
        FormationSensitiveHOLIdentityEquality.refl_realizes SetProfile.signature holdsName
          proofToIdentity SetProfile.holdsName_fresh identity_decodes type⟩
  | substitution type =>
      obtain ⟨code, represented⟩ := Carriers.substitution_represented type
      refine ⟨code, represented, ?_⟩
      rw [show (Published.substitution type).realization = Carriers.substRealizationAt type from
        ExecutableModel.CodeModel.realization_substitution type]
      exact Carriers.substRealizationAt_typed type represented
  | induction => exact ⟨SetProfile.inductionCode, rfl, inductionRealization_typed⟩

/-! ## The general translation -/

/-- Every source proof whose assumptions are published facts links to a closed
program typed, in the identity profile, at the proof family of its theorem. -/
theorem linked_typed {assumptions : List (HOL.Formula SetProfile.SetConst [])}
    {statement : HOL.Formula SetProfile.SetConst []}
    (proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement)
    (published : ∀ index : Fin assumptions.length, Published (assumptions.get index))
    {term : Tower.Tm 0}
    (compiled : Modulo.compileModulo SetProfile.signature proof Fin.elim0
      (fun index => (published index).realization) = some term) :
    ∃ code, represent SetProfile.signature statement = some code ∧
      Typing identityRules .nil term (Holds code) := by
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed SetProfile.signature holdsName
      identityOperations SetProfile.realization proof (objects := Fin.elim0)
      (fun index => index.elim0)
      (fun index => by
        obtain ⟨code, represented, typed⟩ := (published index).typed
        refine ⟨code, represented, ?_⟩
        rw [SetProfile.subst_elim0]
        exact typed)
      compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨code, represented, typed⟩

/-- A proof whose assumptions are published facts, compiled, gives a closed
program typed at the proof family of its theorem. Compilation is a hypothesis
here; `linked_of_core` shows it for every core proof. -/
theorem linked_exists {assumptions : List (HOL.Formula SetProfile.SetConst [])}
    {statement : HOL.Formula SetProfile.SetConst []}
    (proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement)
    (published : ∀ index : Fin assumptions.length, Published (assumptions.get index))
    (compiles : ∃ term, Modulo.compileModulo SetProfile.signature proof Fin.elim0
      (fun index => (published index).realization) = some term) :
    ∃ term code, represent SetProfile.signature statement = some code ∧
      Typing identityRules .nil term (Holds code) := by
  obtain ⟨term, compiled⟩ := compiles
  obtain ⟨code, represented, typed⟩ := linked_typed proof published compiled
  exact ⟨term, code, represented, typed⟩

/-- Every core proof whose assumptions are published facts links: it compiles,
against their realizations, to a closed program typed in the identity profile at
the proof family of its theorem. -/
theorem linked_of_core {assumptions : List (HOL.Formula SetProfile.SetConst [])}
    {statement : HOL.Formula SetProfile.SetConst []}
    (proof : HOL.ProofSyntaxModulo SetProfile.sourceEquations assumptions statement)
    (published : ∀ index : Fin assumptions.length, Published (assumptions.get index))
    (core : HOL.ImpredicativeConnectives.IsCoreProofModulo proof) :
    ∃ term code, represent SetProfile.signature statement = some code ∧
      Typing identityRules .nil term (Holds code) := by
  obtain ⟨term, compiled⟩ := Option.isSome_iff_exists.mp
    (HOLNativeGenericProofCompiler.compileModulo_core_isSome SetProfile.signature proof core
      Fin.elim0 (fun index => (published index).realization))
  obtain ⟨code, represented, typed⟩ := linked_typed proof published compiled
  exact ⟨term, code, represented, typed⟩

/-! ## The zero-add document -/

/-- The zero-add document's assumptions are published facts. -/
def zeroAddPublished : ∀ index : Fin SetProfile.zeroAddAssumptions.length,
    Published (SetProfile.zeroAddAssumptions.get index)
  | ⟨0, _⟩ => .induction
  | ⟨1, _⟩ => .reflexivity SetProfile.numTy
  | ⟨2, _⟩ => .substitution SetProfile.numTy

theorem zeroAdd_links :
    Modulo.compileModulo SetProfile.signature SetProfile.zeroAddProof Fin.elim0
      (fun index => (zeroAddPublished index).realization) = some linkedZeroAdd :=
  rfl

/-- The general translation, at the zero-add document. -/
theorem zeroAdd_linked_typed :
    Typing identityRules .nil linkedZeroAdd (Holds SetProfile.zeroAddCode) := by
  obtain ⟨code, represented, typed⟩ :=
    linked_typed SetProfile.zeroAddProof zeroAddPublished zeroAdd_links
  rw [SetProfile.zeroAdd_represented] at represented
  cases represented
  exact typed

/-! ## Symmetry at a carrier, as the proof library expands it -/

section Symmetry

variable (type : HOL.Ty SetProfile.SetBase)

/-- `∀ f g. f = g → g = f`. -/
def symmetryStatement : HOL.Formula SetProfile.SetConst [] :=
  .all (σ := type) (.all (σ := type)
    (.imp (.eq (.var (.vs .vz)) (.var .vz)) (.eq (.var .vz) (.var (.vs .vz)))))

/-- `refl@T` and `subst@T`. -/
abbrev symmetryAssumptions : List (HOL.Formula SetProfile.SetConst []) :=
  [FormationSensitiveHOLIdentityEquality.reflexivity type, Carriers.substitution type]

/-- `λ z. z = f`, under the outer variables `g` and `f`. -/
def symmetryMotive : HOL.Term SetProfile.SetConst [type, type] (.arr type .prop) :=
  .lam (.eq (.var .vz) (.var (.vs (.vs .vz))))

theorem symmetryReflArticle :
    HOL.CoreConversion SetProfile.sourceEquations (Γ := [type, type])
      (.eq (.var (.vs .vz)) (.var (.vs .vz))) (.app (symmetryMotive type) (.var (.vs .vz))) :=
  .symm _ _ (SetProfile.coreStep (.beta _ _) rfl rfl)

theorem symmetryConclusionArticle :
    HOL.CoreConversion SetProfile.sourceEquations (Γ := [type, type])
      (.app (symmetryMotive type) (.var .vz)) (.eq (.var .vz) (.var (.vs .vz))) :=
  SetProfile.coreStep (.beta _ _) rfl rfl

/-- The hypotheses inside the proof: the path `f = g`, then the facts. -/
abbrev symmetryHypotheses : List (HOL.Formula SetProfile.SetConst [type, type]) :=
  .eq (.var (.vs .vz)) (.var .vz) ::
    HOL.weakenHyps (σ := type) (HOL.weakenHyps (σ := type) (symmetryAssumptions type))

def symmetryPath :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations (symmetryHypotheses type)
      (.eq (.var (.vs .vz)) (.var .vz)) :=
  .hyp (Δ := symmetryHypotheses type) ⟨0, Nat.zero_lt_succ _⟩

def symmetryRefl :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations (symmetryHypotheses type)
      (HOL.weaken (HOL.weaken (FormationSensitiveHOLIdentityEquality.reflexivity type))) :=
  .hyp (Δ := symmetryHypotheses type) ⟨1, (by decide : 1 < 3)⟩

def symmetrySubst :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations (symmetryHypotheses type)
      (HOL.weaken (HOL.weaken (Carriers.substitution type))) :=
  .hyp (Δ := symmetryHypotheses type) ⟨2, (by decide : 2 < 3)⟩

/-- The expansion of `pf:sym`: substitution at the motive `λ z. z = f`, applied
to the path and to reflexivity at `f`. -/
def symmetryProof :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations (symmetryAssumptions type)
      (symmetryStatement type) :=
  .allI (.allI (.impI
    (.convert (symmetryConclusionArticle type)
      (.impE
        (.impE
          (.allE (.var .vz) (.allE (.var (.vs .vz))
            (.allE (symmetryMotive type) (symmetrySubst type))))
          (symmetryPath type))
        (.convert (symmetryReflArticle type) (.allE (.var (.vs .vz)) (symmetryRefl type)))))))

/-- Its assumptions are published facts. -/
def symmetryPublished : ∀ index : Fin (symmetryAssumptions type).length,
    Published ((symmetryAssumptions type).get index)
  | ⟨0, _⟩ => .reflexivity type
  | ⟨1, _⟩ => .substitution type

theorem symmetry_compiles :
    ∃ term, Modulo.compileModulo SetProfile.signature (symmetryProof type) Fin.elim0
      (fun index => (symmetryPublished type index).realization) = some term :=
  ⟨_, rfl⟩

/-- At every carrier, the linked symmetry proof is typed at the proof family of
`∀ f g. f = g → g = f`. -/
theorem symmetry_linked :
    ∃ term code, represent SetProfile.signature (symmetryStatement type) = some code ∧
      Typing identityRules .nil term (Holds code) :=
  linked_exists (symmetryProof type) (symmetryPublished type) (symmetry_compiles type)

end Symmetry

/-! ### At the function carrier `num → num` -/

/-- `num → num`. -/
abbrev functions : HOL.Ty SetProfile.SetBase := .arr SetProfile.numTy SetProfile.numTy

/-- `λ f g p. subst@ (λ z. z = f) f g p (refl@ f)`, linked. -/
def linkedSymmetry : Tower.Tm 0 :=
  .lam (.lam (.lam
    (.app
      (.app (.app (.app (.app (liftClosed (Carriers.substRealizationAt functions))
        (.lam (.app (.app (.const (SetProfile.eqName functions)) (.var 0)) (.var 3))))
        (.var 2)) (.var 1)) (.var 0))
      (.app (liftClosed reflRealization) (.var 2)))))

theorem functions_links :
    Modulo.compileModulo SetProfile.signature (symmetryProof functions) Fin.elim0
      (fun index => (symmetryPublished functions index).realization) = some linkedSymmetry :=
  rfl

/-- `Π f g : num → num. Id f g → Id g f`. -/
def symmetryDecoded : Tower.Tm 0 :=
  .pi (Carriers.carrier functions) (.pi (Carriers.carrier functions)
    (.pi (.id (Carriers.carrier functions) (.var 1) (.var 0))
      (.id (Carriers.carrier functions) (.var 1) (.var 2))))

theorem symmetryStatement_decoded :
    FormationSensitiveHOLIdentityEquality.decode SetProfile.signature holdsName
      (symmetryStatement functions) = some symmetryDecoded :=
  rfl

theorem symmetryDecoded_formed : Typing R .nil symmetryDecoded U0 :=
  pi_at (Carriers.carrier_typed functions) (pi_at (Carriers.carrier_typed functions)
    (pi_at (id_at (Carriers.carrier_typed functions) (Typing.var 1) (Typing.var 0))
      (id_at (Carriers.carrier_typed functions) (Typing.var 1) (Typing.var 2))))

/-- The linked symmetry proof has the dependent reading of symmetry at `num → num`. -/
theorem linkedSymmetry_decoded : Typing identityRules .nil linkedSymmetry symmetryDecoded := by
  obtain ⟨code, represented, typed⟩ :=
    linked_typed (symmetryProof functions) (symmetryPublished functions) functions_links
  exact Typing.conv typed (toIdentity symmetryDecoded_formed) (isUniverseAt Tower.zero)
    (toIdentity_runs (FormationSensitiveHOLIdentityEquality.decodes SetProfile.signature holdsName
      proofToIdentity identity_decodes (symmetryStatement functions) represented
      symmetryStatement_decoded))

/-- The context `f g : num → num, p : Id f g`. -/
abbrev pathContext : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (Carriers.carrier functions)) (Carriers.carrier functions))
    (.id (Carriers.carrier functions) (.var 1) (.var 0))

/-- At open functions `f`, `g` and an open path `p`, the linked proof is
evidence for `Id g f`. -/
theorem linkedSymmetry_open :
    Typing identityRules pathContext
      (.app (.app (.app (liftClosed linkedSymmetry) (.var 2)) (.var 1)) (.var 0))
      (.id (Carriers.carrier functions) (.var 1) (.var 2)) := by
  have closed := FormationSensitiveHOLInterface.closed_typed linkedSymmetry_decoded pathContext
  exact Typing.appElim (Typing.appElim (Typing.appElim closed (Typing.var 2)) (Typing.var 1))
    (Typing.var 0)

/-- At an open function `f`, symmetry at `f`, `f` and `refl f` runs to `refl f`:
three beta steps, five into the substitution realization, identity elimination
at reflexivity, and one into the reflexivity realization. -/
theorem linkedSymmetry_runs_open :
    Execution.Runs
      (.app (.app (.app (liftClosed linkedSymmetry) (.var 0)) (.var 0)) (.refl (.var 0)) : Tower.Tm 1)
      (.refl (.var 0)) := by
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.beta _ _) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.beta _ _) .refl).trans ?_
  refine (Execution.Runs.beta _ _).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app
    (Execution.Runs.beta _ _) .refl) .refl) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app
    (Execution.Runs.beta _ _) .refl) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.beta _ _) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.beta _ _) .refl).trans ?_
  refine (Execution.Runs.beta _ _).trans ?_
  refine (Execution.Runs.equation listed_jIota
    (Execution.patternValues ![Carriers.carrier functions, .var 0, _, _])).trans ?_
  exact Execution.Runs.beta _ _

/-- At every closed function `f`, the linked symmetry proof applied to `f`, `f`
and `refl f` runs to `refl f`, in the draft's own rules. -/
theorem linkedSymmetry_runs (function : Tower.Tm 0) :
    Execution.Runs (.app (.app (.app linkedSymmetry function) function) (.refl function))
      (.refl function) :=
  Evaluation.runs_substitute (subst0 function) linkedSymmetry_runs_open

/-! ## Congruence of the power set, as the proof library expands `pf:cong` -/

/-- The carrier `set`. -/
abbrev sets : HOL.Ty SetProfile.SetBase := SetProfile.setTy

/-- `Power x`. -/
def powerT {Γ : HOL.Ctx SetProfile.SetBase} (set : HOL.Term SetProfile.SetConst Γ sets) :
    HOL.Term SetProfile.SetConst Γ sets :=
  .app (.const .power) set

/-- `∀ a b : set. a = b → Power a = Power b`. -/
def congruenceStatement : HOL.Formula SetProfile.SetConst [] :=
  .all (σ := sets) (.all (σ := sets)
    (.imp (.eq (.var (.vs .vz)) (.var .vz)) (.eq (powerT (.var (.vs .vz))) (powerT (.var .vz)))))

/-- `refl@set` and `subst@set`. -/
abbrev congruenceAssumptions : List (HOL.Formula SetProfile.SetConst []) :=
  [FormationSensitiveHOLIdentityEquality.reflexivity sets, Carriers.substitution sets]

/-- `λ z. Power a = Power z`, under the outer variables `b` and `a`. -/
def congruenceMotive : HOL.Term SetProfile.SetConst [sets, sets] (.arr sets .prop) :=
  .lam (.eq (powerT (.var (.vs (.vs .vz)))) (powerT (.var .vz)))

theorem congruenceReflArticle :
    HOL.CoreConversion SetProfile.sourceEquations (Γ := [sets, sets])
      (.eq (powerT (.var (.vs .vz))) (powerT (.var (.vs .vz))))
      (.app congruenceMotive (.var (.vs .vz))) :=
  .symm _ _ (SetProfile.coreStep (.beta _ _) rfl rfl)

theorem congruenceConclusionArticle :
    HOL.CoreConversion SetProfile.sourceEquations (Γ := [sets, sets])
      (.app congruenceMotive (.var .vz)) (.eq (powerT (.var (.vs .vz))) (powerT (.var .vz))) :=
  SetProfile.coreStep (.beta _ _) rfl rfl

abbrev congruenceHypotheses : List (HOL.Formula SetProfile.SetConst [sets, sets]) :=
  .eq (.var (.vs .vz)) (.var .vz) ::
    HOL.weakenHyps (σ := sets) (HOL.weakenHyps (σ := sets) congruenceAssumptions)

def congruencePath :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations congruenceHypotheses
      (.eq (.var (.vs .vz)) (.var .vz)) :=
  .hyp (Δ := congruenceHypotheses) ⟨0, by decide⟩

def congruenceRefl :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations congruenceHypotheses
      (HOL.weaken (HOL.weaken (FormationSensitiveHOLIdentityEquality.reflexivity sets))) :=
  .hyp (Δ := congruenceHypotheses) ⟨1, by decide⟩

def congruenceSubst :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations congruenceHypotheses
      (HOL.weaken (HOL.weaken (Carriers.substitution sets))) :=
  .hyp (Δ := congruenceHypotheses) ⟨2, by decide⟩

/-- The expansion of `pf:cong set set (λ r. Power r) a b p`: substitution at the
motive `λ z. Power a = Power z`, applied to the path and to reflexivity at
`Power a`. -/
def congruenceProof :
    HOL.ProofSyntaxModulo SetProfile.sourceEquations congruenceAssumptions congruenceStatement :=
  .allI (.allI (.impI
    (.convert congruenceConclusionArticle
      (.impE
        (.impE
          (.allE (.var .vz) (.allE (.var (.vs .vz)) (.allE congruenceMotive congruenceSubst)))
          congruencePath)
        (.convert congruenceReflArticle (.allE (powerT (.var (.vs .vz))) congruenceRefl))))))

def congruencePublished : ∀ index : Fin congruenceAssumptions.length,
    Published (congruenceAssumptions.get index)
  | ⟨0, _⟩ => .reflexivity sets
  | ⟨1, _⟩ => .substitution sets

/-- `Power` as a term. -/
abbrev powerNative {n : Nat} (set : Tower.Tm n) : Tower.Tm n :=
  .app (.const (SetProfile.constantName .power)) set

/-- `λ a b p. subst@ (λ z. Power a = Power z) a b p (refl@ (Power a))`, linked. -/
def linkedCongruence : Tower.Tm 0 :=
  .lam (.lam (.lam
    (.app
      (.app (.app (.app (.app (liftClosed (Carriers.substRealizationAt sets))
        (.lam (.app (.app (.const (SetProfile.eqName sets)) (powerNative (.var 3)))
          (powerNative (.var 0)))))
        (.var 2)) (.var 1)) (.var 0))
      (.app (liftClosed reflRealization) (powerNative (.var 2))))))

theorem sets_links :
    Modulo.compileModulo SetProfile.signature congruenceProof Fin.elim0
      (fun index => (congruencePublished index).realization) = some linkedCongruence :=
  rfl

/-- `Π a b : set. Id a b → Id (Power a) (Power b)`. -/
def congruenceDecoded : Tower.Tm 0 :=
  .pi (Carriers.carrier sets) (.pi (Carriers.carrier sets)
    (.pi (.id (Carriers.carrier sets) (.var 1) (.var 0))
      (.id (Carriers.carrier sets) (powerNative (.var 2)) (powerNative (.var 1)))))

theorem congruenceStatement_decoded :
    FormationSensitiveHOLIdentityEquality.decode SetProfile.signature holdsName
      congruenceStatement = some congruenceDecoded :=
  rfl

theorem powerNative_typed {n : Nat} {Γ : Tower.Ctx n} {set : Tower.Tm n}
    (typed : Typing R Γ set (Carriers.carrier sets)) :
    Typing R Γ (powerNative set) (Carriers.carrier sets) :=
  Typing.appElim (B := Carriers.carrier sets) (constant_typed .power) typed

theorem congruenceDecoded_formed : Typing R .nil congruenceDecoded U0 :=
  pi_at (Carriers.carrier_typed sets) (pi_at (Carriers.carrier_typed sets)
    (pi_at (id_at (Carriers.carrier_typed sets) (Typing.var 1) (Typing.var 0))
      (id_at (Carriers.carrier_typed sets) (powerNative_typed (Typing.var 2))
        (powerNative_typed (Typing.var 1)))))

/-- The linked congruence proof has the dependent reading of its theorem. -/
theorem linkedCongruence_decoded : Typing identityRules .nil linkedCongruence congruenceDecoded := by
  obtain ⟨code, represented, typed⟩ :=
    linked_typed congruenceProof congruencePublished sets_links
  exact Typing.conv typed (toIdentity congruenceDecoded_formed) (isUniverseAt Tower.zero)
    (toIdentity_runs (FormationSensitiveHOLIdentityEquality.decodes SetProfile.signature holdsName
      proofToIdentity identity_decodes congruenceStatement represented
      congruenceStatement_decoded))

/-- The context `a b : set, p : Id a b`. -/
abbrev setPathContext : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (Carriers.carrier sets)) (Carriers.carrier sets))
    (.id (Carriers.carrier sets) (.var 1) (.var 0))

/-- At open sets `a`, `b` and an open path `p`, the linked proof is evidence
for `Id (Power a) (Power b)`. -/
theorem linkedCongruence_open :
    Typing identityRules setPathContext
      (.app (.app (.app (liftClosed linkedCongruence) (.var 2)) (.var 1)) (.var 0))
      (.id (Carriers.carrier sets) (powerNative (.var 2)) (powerNative (.var 1))) := by
  have closed := FormationSensitiveHOLInterface.closed_typed linkedCongruence_decoded setPathContext
  exact Typing.appElim (Typing.appElim (Typing.appElim closed (Typing.var 2)) (Typing.var 1))
    (Typing.var 0)

theorem linkedCongruence_runs_open :
    Execution.Runs
      (.app (.app (.app (liftClosed linkedCongruence) (.var 0)) (.var 0)) (.refl (.var 0)) :
        Tower.Tm 1)
      (.refl (powerNative (.var 0))) := by
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.beta _ _) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.beta _ _) .refl).trans ?_
  refine (Execution.Runs.beta _ _).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app
    (Execution.Runs.beta _ _) .refl) .refl) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.app
    (Execution.Runs.beta _ _) .refl) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.app (Execution.Runs.beta _ _) .refl) .refl).trans ?_
  refine (Execution.Runs.app (Execution.Runs.beta _ _) .refl).trans ?_
  refine (Execution.Runs.beta _ _).trans ?_
  refine (Execution.Runs.equation listed_jIota
    (Execution.patternValues ![Carriers.carrier sets, .var 0, _, _])).trans ?_
  exact Execution.Runs.beta _ _

/-- At every closed set `a`, the linked congruence proof applied to `a`, `a` and
`refl a` runs to `refl (Power a)`, in the draft's own rules. -/
theorem linkedCongruence_runs (set : Tower.Tm 0) :
    Execution.Runs (.app (.app (.app linkedCongruence set) set) (.refl set))
      (.refl (powerNative set)) :=
  Evaluation.runs_substitute (subst0 set) linkedCongruence_runs_open

#print axioms Published.typed
#print axioms linkedCongruence_decoded
#print axioms linkedCongruence_open
#print axioms linkedCongruence_runs
#print axioms linkedSymmetry_decoded
#print axioms linkedSymmetry_open
#print axioms linkedSymmetry_runs
#print axioms symmetry_linked
#print axioms functions_links
#print axioms linked_typed
#print axioms zeroAdd_linked_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Linking
