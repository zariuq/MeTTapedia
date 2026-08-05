import Metamath.Spec.Equivalence

/-!
# Finite support and renaming for declarative Metamath proofs

The canonical declarative `Metamath.Provable` relation has an unrestricted
`var` constructor.  The operational verifier, source GSLT, and
`SupportedProvable` instead require every variable used by a derivation to
have an active floating hypothesis.  Fixed-frame conservativity is false.

This module factors the honest reconciliation into two reusable pieces:

1. a type-preserving renaming action on semantic formulas and substitutions;
2. a theorem that every declarative derivation has a finite list of variable
   leaves sufficient to rebuild the renamed derivation in any active frame
   that supports those images and transports the original context.

The theorem does not assume that an arbitrary finite frame can represent
arbitrary semantic variable identifiers.  Constructing a fresh, source-valid
dummy extension and a suitable renaming is the next, separate obligation.
-/

namespace Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport

open Metamath
open Metamath.Spec
open Metamath.Spec.Equivalence
open Metamath.Spec.Bridge (MarioVR MarioFormula MarioExpr)

/-! ## Type-preserving semantic renaming -/

/-- Rename semantic variable references while leaving constants untouched. -/
def renameSym (ρ : MarioVR → MarioVR) : Metamath.Sym → Metamath.Sym
  | .const c => .const c
  | .var v => .var (ρ v)

/-- Pointwise renaming of a semantic expression. -/
def renameExpr (ρ : MarioVR → MarioVR) (expression : MarioExpr) : MarioExpr :=
  expression.map (renameSym ρ)

/-- A formula's constant typecode is fixed; only its expression is renamed. -/
def renameFormula (ρ : MarioVR → MarioVR)
    (formula : MarioFormula) : MarioFormula :=
  (formula.1, renameExpr ρ formula.2)

/-- Rename every expression produced by a substitution.  The substitution's
domain belongs to the referenced assertion and is intentionally unchanged. -/
def renameSubstitution (ρ : MarioVR → MarioVR)
    (σ : MarioVR → MarioExpr) : MarioVR → MarioExpr :=
  fun v => renameExpr ρ (σ v)

/-- Renaming respects the semantic typecode carried by a variable reference. -/
def TypePreserving (ρ : MarioVR → MarioVR) : Prop :=
  ∀ v, (ρ v).type = v.type

@[simp] theorem renameExpr_nil (ρ : MarioVR → MarioVR) :
    renameExpr ρ [] = [] := rfl

@[simp] theorem renameExpr_const_cons (ρ : MarioVR → MarioVR)
    (c : Metamath.CN) (tail : MarioExpr) :
    renameExpr ρ (.const c :: tail) =
      .const c :: renameExpr ρ tail := rfl

@[simp] theorem renameExpr_var_cons (ρ : MarioVR → MarioVR)
    (v : MarioVR) (tail : MarioExpr) :
    renameExpr ρ (.var v :: tail) =
      .var (ρ v) :: renameExpr ρ tail := rfl

theorem renameExpr_append (ρ : MarioVR → MarioVR)
    (left right : MarioExpr) :
    renameExpr ρ (left ++ right) =
      renameExpr ρ left ++ renameExpr ρ right := by
  change List.map (renameSym ρ) (List.append left right) =
    List.append (List.map (renameSym ρ) left)
      (List.map (renameSym ρ) right)
  exact List.map_append

/-- Renaming after substitution is the same as renaming each substitution
image first. -/
theorem renameExpr_subst (ρ : MarioVR → MarioVR)
    (σ : MarioVR → MarioExpr) (expression : MarioExpr) :
    renameExpr ρ (Metamath.Expr.subst σ expression) =
      Metamath.Expr.subst (renameSubstitution ρ σ) expression := by
  induction expression with
  | nil => rfl
  | cons symbol tail ih =>
      cases symbol with
      | const c =>
          simp [Metamath.Expr.subst, ih]
      | var v =>
          simp [Metamath.Expr.subst, renameSubstitution,
            renameExpr_append, ih]

/-- Formula-level fusion of renaming with substitution. -/
theorem renameFormula_subst (ρ : MarioVR → MarioVR)
    (σ : MarioVR → MarioExpr) (formula : MarioFormula) :
    renameFormula ρ (Metamath.Formula.subst σ formula) =
      Metamath.Formula.subst (renameSubstitution ρ σ) formula := by
  cases formula with
  | mk typecode expression =>
      simp [renameFormula, Metamath.Formula.subst, renameExpr_subst]

/-- A renamed variable formula is the variable formula of the renamed
reference when the renaming preserves typecodes. -/
theorem renameFormula_vhyp {ρ : MarioVR → MarioVR}
    (htype : TypePreserving ρ) (v : MarioVR) :
    renameFormula ρ (Metamath.VR.vhyp v) =
      Metamath.VR.vhyp (ρ v) := by
  simp [renameFormula, Metamath.VR.vhyp, renameExpr, renameSym, htype v]

@[simp] theorem renameSym_id (symbol : Metamath.Sym) :
    renameSym id symbol = symbol := by
  cases symbol <;> rfl

@[simp] theorem renameExpr_id (expression : MarioExpr) :
    renameExpr id expression = expression := by
  unfold renameExpr
  induction expression with
  | nil => rfl
  | cons symbol tail ih => simp [renameSym_id, ih]

@[simp] theorem renameFormula_id (formula : MarioFormula) :
    renameFormula id formula = formula := by
  cases formula
  simp [renameFormula]

/-! ## Transport of disjointness -/

/-- Every variable in a renamed expression comes from a variable in the
original expression. -/
theorem var_mem_renameExpr {ρ : MarioVR → MarioVR}
    {renamed : MarioVR} {expression : MarioExpr}
    (hmem : Metamath.Sym.var renamed ∈ renameExpr ρ expression) :
    ∃ original,
      Metamath.Sym.var original ∈ expression ∧ ρ original = renamed := by
  unfold renameExpr at hmem
  rcases List.mem_map.mp hmem with ⟨symbol, hsymbol, heq⟩
  cases symbol with
  | const c => exact nomatch heq
  | var original =>
      exact ⟨original, hsymbol, Metamath.Sym.var.inj heq⟩

/-- A morphism of caller disjointness relations preserves expression
disjointness after renaming. -/
theorem Expr.disjoint_rename
    {ρ : MarioVR → MarioVR} {sourceDJ targetDJ : Metamath.DJ}
    (hdj : ∀ a b, sourceDJ a b → targetDJ (ρ a) (ρ b))
    {left right : MarioExpr}
    (hdisjoint : Metamath.Expr.disjoint sourceDJ left right) :
    Metamath.Expr.disjoint targetDJ
      (renameExpr ρ left) (renameExpr ρ right) := by
  intro a b ha hb
  obtain ⟨a₀, ha₀, rfl⟩ := var_mem_renameExpr ha
  obtain ⟨b₀, hb₀, rfl⟩ := var_mem_renameExpr hb
  exact hdj a₀ b₀ (hdisjoint a₀ b₀ ha₀ hb₀)

/-- Substitution respects transported caller disjointness after all of its
images are renamed. -/
theorem DJ.subst_rename
    {ρ : MarioVR → MarioVR} {sourceDJ targetDJ axiomDJ : Metamath.DJ}
    (hdj : ∀ a b, sourceDJ a b → targetDJ (ρ a) (ρ b))
    {σ : MarioVR → MarioExpr}
    (hsubst : Metamath.DJ.subst σ axiomDJ sourceDJ) :
    Metamath.DJ.subst (renameSubstitution ρ σ) axiomDJ targetDJ := by
  intro a b hab
  exact Expr.disjoint_rename hdj (hsubst a b hab)

/-! ## Finite derivation-local support -/

/-- The target active frame transports the source context through `ρ` when
all source hypotheses remain available after renaming and all source `$d`
facts remain valid. -/
structure ContextTransport (ρ : MarioVR → MarioVR)
    (source : Metamath.Context) (target : Metamath.Spec.Frame) : Prop where
  hypothesis : ∀ formula ∈ source.hyps,
    renameFormula ρ formula ∈ (frameToContext target).hyps
  distinct : ∀ a b, source.dj a b →
    (frameToContext target).dj (ρ a) (ρ b)

/-- A finite list supports a semantic derivation when support for its renamed
members, together with context transport and type preservation, is sufficient
to construct a supported derivation in the target active frame. -/
def FiniteSupportWitness
    {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    {formula : MarioFormula}
    (support : List MarioVR) : Prop :=
  ∀ (ρ : MarioVR → MarioVR) (target : Metamath.Spec.Frame),
    TypePreserving ρ →
    ContextTransport ρ source target →
    (∀ v ∈ support,
      ∃ sourceVariable : Metamath.Spec.Variable,
        findVar (varMapOfFrame target) (ρ v) = some sourceVariable) →
    SupportedProvable Γ target (renameFormula ρ formula)

/-- Local support is monotone in the finite support list. -/
theorem FiniteSupportWitness.mono
    {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    {formula : MarioFormula}
    {smaller larger : List MarioVR}
    (hwitness : FiniteSupportWitness (Γ := Γ) (source := source)
      (formula := formula) smaller)
    (hsubset : ∀ v ∈ smaller, v ∈ larger) :
    FiniteSupportWitness (Γ := Γ) (source := source)
      (formula := formula) larger := by
  intro ρ target htype hcontext hsupported
  exact hwitness ρ target htype hcontext
    (fun v hv => hsupported v (hsubset v hv))

/-- Finitely many branches with monotone support requirements have one
common support list, obtained by concatenation.  No choice principle is needed:
the list itself supplies the induction order. -/
theorem exists_common_support
    {α : Type _} (items : List α)
    (property : α → List MarioVR → Prop)
    (hmono : ∀ item {smaller larger},
      property item smaller →
      (∀ v ∈ smaller, v ∈ larger) →
      property item larger)
    (hexists : ∀ item ∈ items, ∃ support, property item support) :
    ∃ support, ∀ item ∈ items, property item support := by
  induction items with
  | nil => exact ⟨[], fun item hmem => nomatch hmem⟩
  | cons head tail ih =>
      obtain ⟨headSupport, headWitness⟩ :=
        hexists head (List.Mem.head tail)
      obtain ⟨tailSupport, tailWitness⟩ := ih
        (fun item hmem => hexists item (List.Mem.tail head hmem))
      refine ⟨headSupport ++ tailSupport, ?_⟩
      intro item hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · subst item
        exact hmono _ headWitness
          (fun v hv => List.mem_append_left tailSupport hv)
      · exact hmono item (tailWitness item htail)
          (fun v hv => List.mem_append_right headSupport hv)

/-- **Finite-support extraction.** Every canonical declarative derivation has
a finite list of variable leaves sufficient to reconstruct any
type-preservingly renamed copy as a frame-supported derivation, provided the
target active frame transports the source context and supports the listed
images. -/
theorem Provable.exists_finiteSupport
    {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    {formula : MarioFormula}
    (derivation : Metamath.Provable (dbToAxioms Γ) source formula) :
    ∃ support : List MarioVR,
      FiniteSupportWitness (Γ := Γ) (source := source)
        (formula := formula) support := by
  induction derivation with
  | hyp formula hmem =>
      refine ⟨[], ?_⟩
      intro ρ target htype hcontext hsupported
      exact SupportedProvable.hyp (renameFormula ρ formula)
        (hcontext.hypothesis formula hmem)
  | var v =>
      refine ⟨[v], ?_⟩
      intro ρ target htype hcontext hsupported
      rw [renameFormula_vhyp htype v]
      exact SupportedProvable.var (ρ v) (hsupported v (by simp))
  | @ax σ ax hax hdj hhyps hvars ih_h ih_v =>
      obtain ⟨hypSupport, hypWitness⟩ :=
        exists_common_support ax.ctx.hyps
          (fun hypothesis support =>
            FiniteSupportWitness (Γ := Γ) (source := source)
              (formula := Metamath.Formula.subst σ hypothesis) support)
          (fun _ {_ _} hwitness hsubset =>
            FiniteSupportWitness.mono hwitness hsubset)
          ih_h
      obtain ⟨varSupport, varWitness⟩ :=
        exists_common_support ax.vars
          (fun v support =>
            FiniteSupportWitness (Γ := Γ) (source := source)
              (formula := (v.type, σ v)) support)
          (fun _ {_ _} hwitness hsubset =>
            FiniteSupportWitness.mono hwitness hsubset)
          ih_v
      refine ⟨hypSupport ++ varSupport, ?_⟩
      intro ρ target htype hcontext hsupported
      have hypSupported : ∀ hypothesis ∈ ax.ctx.hyps,
          SupportedProvable Γ target
            (renameFormula ρ (Metamath.Formula.subst σ hypothesis)) := by
        intro hypothesis hmem
        exact hypWitness hypothesis hmem ρ target htype hcontext
          (fun v hv => hsupported v (List.mem_append_left varSupport hv))
      have varSupported : ∀ v ∈ ax.vars,
          SupportedProvable Γ target
            (renameFormula ρ (v.type, σ v)) := by
        intro v hmem
        exact varWitness v hmem ρ target htype hcontext
          (fun v hv => hsupported v (List.mem_append_right hypSupport hv))
      rw [renameFormula_subst]
      exact SupportedProvable.ax (renameSubstitution ρ σ) hax
        (DJ.subst_rename hcontext.distinct hdj)
        (fun hypothesis hmem => by
          rw [← renameFormula_subst]
          exact hypSupported hypothesis hmem)
        (fun v hmem => by
          simpa [renameFormula, renameSubstitution] using
            varSupported v hmem)
        (fun v hmem =>
          supported_wellformed (varSupported v hmem))

/-! ## Positive and negative calibration -/

/-- A variable leaf needs exactly its singleton support as a sufficient
witness. -/
theorem singleton_supports_var
    {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    (v : MarioVR) :
    FiniteSupportWitness (Γ := Γ) (source := source)
      (formula := Metamath.VR.vhyp v) [v] := by
  intro ρ target htype hcontext hsupported
  rw [renameFormula_vhyp htype v]
  exact SupportedProvable.var (ρ v) (hsupported v (by simp))

def emptyDatabase : Metamath.Spec.Database := fun _ => none

def emptyFrame : Metamath.Spec.Frame := ⟨[], []⟩

def emptyContext : Metamath.Context := ⟨[], Metamath.DJ.mk' []⟩

theorem emptyContextTransport : ContextTransport id emptyContext emptyFrame := by
  constructor
  · intro formula hmem
    exact nomatch hmem
  · intro a b hdj
    simp [emptyContext, Metamath.DJ.mk'] at hdj

/-- With no hypotheses, variables, or assertions, the supported relation has
no derivations. -/
theorem no_supported_empty {formula : MarioFormula} :
    ¬ SupportedProvable emptyDatabase emptyFrame formula := by
  intro h
  cases h with
  | hyp formula hmem =>
      simp [frameToContext, emptyFrame] at hmem
  | var v hsupported =>
      obtain ⟨sourceVariable, hfind⟩ := hsupported
      simp [varMapOfFrame, floatList, varMapOfFrameAux, findVar,
        emptyFrame] at hfind
  | ax σ hax hdj hhyps hvars hwf =>
      obtain ⟨label, frame, expression, hlookup, -, -⟩ := hax
      simp [emptyDatabase] at hlookup

/-- Negative calibration: the empty list is not a sufficient support witness
for even one unrestricted variable leaf. -/
theorem nil_does_not_support_var (v : MarioVR) :
    ¬ FiniteSupportWitness (Γ := emptyDatabase) (source := emptyContext)
      (formula := Metamath.VR.vhyp v) [] := by
  intro hwitness
  have hsupported := hwitness id emptyFrame (fun _ => rfl)
    emptyContextTransport (fun v hmem => nomatch hmem)
  rw [renameFormula_id] at hsupported
  exact no_supported_empty hsupported

/-! ## Typed extraction: leaf-typecode provenance

The plain extraction returns an opaque support list.  For source-side
composition the leaf typecodes must be traceable, because a source
state can only declare optional floats whose typecodes are declared
constants.  Variable leaves occur in a canonical derivation only at the
root (typecode = the conclusion's) or as premises of an `ax` node
(typecode = an axiom-context hypothesis head or a statement-variable
type), so the support can be extracted together with exactly that
bound. -/

/-- Premise typecodes reachable from the database's axioms: heads of
axiom-context hypotheses and types of statement variables. -/
def AxiomPremiseTypecode (Γ : Metamath.Spec.Database) (t : String) : Prop :=
  ∃ ax, dbToAxioms Γ ax ∧
    ((∃ h ∈ ax.ctx.hyps, h.1 = t) ∨
      ∃ v ∈ ax.vars, Metamath.VR.type v = t)

/-- Substitution preserves the formula head. -/
theorem formulaSubst_fst (σ : Metamath.VR → Metamath.Expr)
    (h : MarioFormula) :
    (Metamath.Formula.subst σ h).1 = h.1 := by
  cases h
  rfl

/-- `exists_common_support` with a per-leaf bound carried through the
concatenation. -/
theorem exists_common_support_bounded
    {α : Type _} (items : List α)
    (property : α → List MarioVR → Prop) (leafBound : MarioVR → Prop)
    (hmono : ∀ item {smaller larger},
      property item smaller →
      (∀ v ∈ smaller, v ∈ larger) →
      property item larger)
    (hexists : ∀ item ∈ items, ∃ support,
      property item support ∧ ∀ v ∈ support, leafBound v) :
    ∃ support, (∀ item ∈ items, property item support) ∧
      ∀ v ∈ support, leafBound v := by
  induction items with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · intro item hmem
        exact nomatch hmem
      · intro v hv
        exact nomatch hv
  | cons head tail ih =>
      obtain ⟨headSupport, headWitness, headBound⟩ :=
        hexists head (List.Mem.head tail)
      obtain ⟨tailSupport, tailWitness, tailBound⟩ := ih
        (fun item hmem => hexists item (List.Mem.tail head hmem))
      refine ⟨headSupport ++ tailSupport, ?_, ?_⟩
      · intro item hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · subst item
          exact hmono _ headWitness
            (fun v hv => List.mem_append_left tailSupport hv)
        · exact hmono item (tailWitness item htail)
            (fun v hv => List.mem_append_right headSupport hv)
      · intro v hv
        rcases List.mem_append.mp hv with hleft | hright
        · exact headBound v hleft
        · exact tailBound v hright

/-- **Typed finite-support extraction.**  Every canonical declarative
derivation has a finite support whose witness is as in
`Provable.exists_finiteSupport`, and whose every leaf typecode is the
conclusion's own typecode or a premise typecode of some database
axiom. -/
theorem Provable.exists_finiteSupport_typed
    {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    {formula : MarioFormula}
    (derivation : Metamath.Provable (dbToAxioms Γ) source formula) :
    ∃ support : List MarioVR,
      FiniteSupportWitness (Γ := Γ) (source := source)
        (formula := formula) support ∧
      ∀ v ∈ support, Metamath.VR.type v = formula.1 ∨
        AxiomPremiseTypecode Γ (Metamath.VR.type v) := by
  induction derivation with
  | hyp formula hmem =>
      refine ⟨[], ?_, fun v hv => nomatch hv⟩
      intro ρ target htype hcontext hsupported
      exact SupportedProvable.hyp (renameFormula ρ formula)
        (hcontext.hypothesis formula hmem)
  | var v =>
      refine ⟨[v], ?_, ?_⟩
      · intro ρ target htype hcontext hsupported
        rw [renameFormula_vhyp htype v]
        exact SupportedProvable.var (ρ v) (hsupported v (by simp))
      · intro w hw
        rcases List.mem_singleton.mp hw with rfl
        exact Or.inl rfl
  | @ax σ ax hax hdj hhyps hvars ih_h ih_v =>
      obtain ⟨hypSupport, hypWitness, hypBound⟩ :=
        exists_common_support_bounded ax.ctx.hyps
          (fun hypothesis support =>
            FiniteSupportWitness (Γ := Γ) (source := source)
              (formula := Metamath.Formula.subst σ hypothesis) support)
          (fun v => AxiomPremiseTypecode Γ (Metamath.VR.type v))
          (fun _ {_ _} hwitness hsubset =>
            FiniteSupportWitness.mono hwitness hsubset)
          (fun hypothesis hmem => by
            obtain ⟨support, hwitness, hbound⟩ := ih_h hypothesis hmem
            refine ⟨support, hwitness, fun v hv => ?_⟩
            rcases hbound v hv with heq | haxt
            · refine ⟨ax, hax, Or.inl ⟨hypothesis, hmem, ?_⟩⟩
              rw [← formulaSubst_fst σ hypothesis]
              exact heq.symm
            · exact haxt)
      obtain ⟨varSupport, varWitness, varBound⟩ :=
        exists_common_support_bounded ax.vars
          (fun v support =>
            FiniteSupportWitness (Γ := Γ) (source := source)
              (formula := (Metamath.VR.type v, σ v)) support)
          (fun v => AxiomPremiseTypecode Γ (Metamath.VR.type v))
          (fun _ {_ _} hwitness hsubset =>
            FiniteSupportWitness.mono hwitness hsubset)
          (fun v hmem => by
            obtain ⟨support, hwitness, hbound⟩ := ih_v v hmem
            refine ⟨support, hwitness, fun w hw => ?_⟩
            rcases hbound w hw with heq | haxt
            · exact ⟨ax, hax, Or.inr ⟨v, hmem, heq.symm⟩⟩
            · exact haxt)
      refine ⟨hypSupport ++ varSupport, ?_, ?_⟩
      · intro ρ target htype hcontext hsupported
        have hypSupported : ∀ hypothesis ∈ ax.ctx.hyps,
            SupportedProvable Γ target
              (renameFormula ρ (Metamath.Formula.subst σ hypothesis)) := by
          intro hypothesis hmem
          exact hypWitness hypothesis hmem ρ target htype hcontext
            (fun v hv => hsupported v (List.mem_append_left varSupport hv))
        have varSupported : ∀ v ∈ ax.vars,
            SupportedProvable Γ target
              (renameFormula ρ (Metamath.VR.type v, σ v)) := by
          intro v hmem
          exact varWitness v hmem ρ target htype hcontext
            (fun v hv => hsupported v (List.mem_append_right hypSupport hv))
        rw [renameFormula_subst]
        exact SupportedProvable.ax (renameSubstitution ρ σ) hax
          (DJ.subst_rename hcontext.distinct hdj)
          (fun hypothesis hmem => by
            rw [← renameFormula_subst]
            exact hypSupported hypothesis hmem)
          (fun v hmem => by
            simpa [renameFormula, renameSubstitution] using
              varSupported v hmem)
          (fun v hmem =>
            supported_wellformed (varSupported v hmem))
      · intro v hv
        rcases List.mem_append.mp hv with hleft | hright
        · exact Or.inr (hypBound v hleft)
        · exact Or.inr (varBound v hright)

/-- Coherence: the plain extraction is recovered from the typed one. -/
example {Γ : Metamath.Spec.Database} {source : Metamath.Context}
    {formula : MarioFormula}
    (derivation : Metamath.Provable (dbToAxioms Γ) source formula) :
    ∃ support : List MarioVR,
      FiniteSupportWitness (Γ := Γ) (source := source)
        (formula := formula) support :=
  (Provable.exists_finiteSupport_typed derivation).imp
    fun _ h => h.1

end Mettapedia.Languages.Metamath.InferenceSemanticFiniteSupport
