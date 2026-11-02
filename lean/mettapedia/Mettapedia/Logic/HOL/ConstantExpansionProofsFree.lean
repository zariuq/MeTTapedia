import Mettapedia.Logic.HOL.ConstantExpansionProofs

/-!
# Constant expansion without function extensionality

The retained expansion construction introduces neither eta nor function
extensionality when its supplied defining equations use neither rule. This
includes expansion under lambda, universal and existential binders. The
congruence lemmas describe the existing proof programs, preserving their
ordered assumptions rather than replacing them by semantic equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {Δ : List (Formula Const Γ)}

namespace ContextualTrinity

@[simp] theorem castConclusion_free {φ ψ : Formula Const Γ} (same : φ = ψ)
    (proof : ProofSyntax Const Δ φ) :
    (castConclusion same proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  cases same
  rfl

@[simp] theorem castEq_free {τ : Ty Base} {s s' t t' : Term Const Γ τ}
    (sources : s = s') (targets : t = t') (proof : ProofSyntax Const Δ (.eq s t)) :
    (castEq sources targets proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  unfold castEq
  exact castConclusion_free _ proof

@[simp] theorem holeCongr_free {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
    {hole hole' : Term Const Γ σ} (proof : ProofSyntax Const Δ (.eq hole hole')) :
    (holeCongr body proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [holeCongr, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem instantiateFresh_free {σ : Ty Base} {Ξ : List (Formula Const (σ :: Γ))}
    {φ : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const Ξ (.all (rename (Rename.lift (Rename.weaken (Γ := Γ) (σ := σ))) φ))) :
    (instantiateFresh proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [instantiateFresh, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem allImp_free {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const Δ (.all (.imp φ φ'))) :
    (allImp proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [allImp, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem exImp_free {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const Δ (.all (.imp φ φ'))) :
    (exImp proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [exImp, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem allCongr_free {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ')) :
    (allCongr proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [allCongr, ProofSyntax.FunctionExtensionalityFree]

@[simp] theorem exCongr_free {σ : Ty Base} {φ φ' : Formula Const (σ :: Γ)}
    (proof : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq φ φ')) :
    (exCongr proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [exCongr, ProofSyntax.FunctionExtensionalityFree]

end ContextualTrinity

namespace ProofSyntax

@[simp] theorem andCongr_free {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const Δ (.eq left left'))
    (second : ProofSyntax Const Δ (.eq right right')) :
    (andCongr first second).FunctionExtensionalityFree ↔
      first.FunctionExtensionalityFree ∧ second.FunctionExtensionalityFree := by
  simp [andCongr, FunctionExtensionalityFree]

@[simp] theorem orCongr_free {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const Δ (.eq left left'))
    (second : ProofSyntax Const Δ (.eq right right')) :
    (orCongr first second).FunctionExtensionalityFree ↔
      first.FunctionExtensionalityFree ∧ second.FunctionExtensionalityFree := by
  simp [orCongr, FunctionExtensionalityFree]

@[simp] theorem impCongr_free {left left' right right' : Formula Const Γ}
    (first : ProofSyntax Const Δ (.eq left left'))
    (second : ProofSyntax Const Δ (.eq right right')) :
    (impCongr first second).FunctionExtensionalityFree ↔
      first.FunctionExtensionalityFree ∧ second.FunctionExtensionalityFree := by
  simp [impCongr, FunctionExtensionalityFree]

@[simp] theorem eqCongr_free {τ : Ty Base} {left left' right right' : Term Const Γ τ}
    (first : ProofSyntax Const Δ (.eq left left'))
    (second : ProofSyntax Const Δ (.eq right right')) :
    (eqCongr first second).FunctionExtensionalityFree ↔
      first.FunctionExtensionalityFree ∧ second.FunctionExtensionalityFree := by
  simp [eqCongr, FunctionExtensionalityFree]

@[simp] theorem appCongr_free {σ τ : Ty Base} {first first' : Term Const Γ (σ ⇒ τ)}
    {second second' : Term Const Γ σ}
    (function : ProofSyntax Const Δ (.eq first first'))
    (argument : ProofSyntax Const Δ (.eq second second')) :
    (appCongr function argument).FunctionExtensionalityFree ↔
      function.FunctionExtensionalityFree ∧ argument.FunctionExtensionalityFree := by
  rfl

@[simp] theorem notCongr_free {first second : Formula Const Γ}
    (proof : ProofSyntax Const Δ (.eq first second)) :
    (notCongr proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  simp [notCongr]

end ProofSyntax

namespace ConstantExpansionProofs

@[simp] theorem weakenProof_free {theory : List (ClosedFormula Const)}
    {formula : ClosedFormula Const} (context : Ctx Base) (proof : ProofSyntax Const theory formula) :
    (weakenProof context proof).FunctionExtensionalityFree ↔ proof.FunctionExtensionalityFree := by
  induction context with
  | nil => simp [weakenProof]
  | cons type context ih => simp only [weakenProof,
      ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.functionExtensionalityFree_rename, ih]

private theorem optionCasesOn_some {α : Type _} {R : Sort _}
    (o t : Option α)
    (noneBranch : o = none → R)
    (someBranch : (val : α) → o = some val → R)
    (ht : o = t) {v : α} (hv : t = some v) :
    Option.casesOn (motive := fun x => o = x → R) t noneBranch someBranch ht =
      someBranch v (ht.trans hv) := by
  subst hv
  rfl

private theorem optionRec_some {α : Type _} {R : Sort _}
    (o t : Option α)
    (noneBranch : o = none → R)
    (someBranch : (val : α) → o = some val → R)
    (ht : o = t) {v : α} (hv : t = some v) :
    Option.rec (motive := fun x => o = x → R) noneBranch someBranch t ht =
      someBranch v (ht.trans hv) := by
  subst hv
  rfl

private theorem eqRec_eq_arrow {α : Sort _} {R : Sort _} {o a b : α}
    (f : o = a → R) (h1 : a = b) (h2 : o = b) :
    (Eq.rec (motive := fun x _ => o = x → R) f h1 h2 : R) = f (h2.trans h1.symm) := by
  subst h1
  rfl

@[simp] private theorem eqRec_proof_free {β : Sort _} {Ξ : List (Formula Const Γ)}
    {F : β → Formula Const Γ} {a b : β} (hab : a = b)
    (p : ProofSyntax Const Ξ (F a)) :
    (Eq.rec (motive := fun x _ => ProofSyntax Const Ξ (F x)) p hab).FunctionExtensionalityFree ↔
      p.FunctionExtensionalityFree := by
  subst hab
  rfl

@[simp] private theorem eqNdrec_proof_free {β : Sort _} {Ξ : List (Formula Const Γ)}
    {F : β → Formula Const Γ} {a b : β} (hab : a = b)
    (p : ProofSyntax Const Ξ (F a)) :
    (Eq.ndrec (motive := fun x => ProofSyntax Const Ξ (F x)) p hab).FunctionExtensionalityFree ↔
      p.FunctionExtensionalityFree := by
  subst hab
  rfl

/-- Expansion adds no eta or function-extensionality rule when its individual
defining equations satisfy that restriction. -/
theorem expand_free (theory : List (ClosedFormula Const))
    (replacements : ∀ {type}, Const type → Option (ClosedTerm Const type))
    (equations : ∀ {type} (constant : Const type) (body : ClosedTerm Const type),
      replacements constant = some body → ProofSyntax Const theory (.eq (.const constant) body))
    (equationsFree : ∀ {type} (constant : Const type) (body : ClosedTerm Const type)
      (present : replacements constant = some body),
      (equations constant body present).FunctionExtensionalityFree)
    {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ)
    {result : Term Const Γ τ} (success : substConst? replacements term = some result) :
    (expand theory replacements equations term success).FunctionExtensionalityFree := by
  induction term with
  | var index =>
      have hres : Term.var index = result := Option.some.inj success
      subst hres; trivial
  | top =>
      have hres : (Term.top : Term Const _ _) = result := Option.some.inj success
      subst hres; trivial
  | bot =>
      have hres : (Term.bot : Term Const _ _) = result := Option.some.inj success
      subst hres; trivial
  | const constant =>
      cases hrep : replacements constant with
      | none => simp [substConst?, hrep] at success
      | some body =>
          have hres : weakenCtx _ body = result := by simpa [substConst?, hrep] using success
          subst hres
          unfold expand
          rw [optionCasesOn_some _ _ _ _ _ hrep]
          dsimp only
          rw [eqRec_eq_arrow]
          simp [equationsFree]
  | app function argument ihFunction ihArgument =>
      cases hf : substConst? replacements function with
      | none => simp [substConst?, hf] at success
      | some _ =>
          cases ha : substConst? replacements argument with
          | none => simp [substConst?, hf, ha] at success
          | some _ =>
              unfold expand
              rw [optionCasesOn_some _ _ _ _ _ hf]
              dsimp only
              rw [eqRec_eq_arrow, optionRec_some _ _ _ _ _ ha, eqRec_eq_arrow]
              simp [ProofSyntax.FunctionExtensionalityFree, ihFunction hf, ihArgument ha]
  | and left right ihLeft ihRight | or left right ihLeft ihRight
  | imp left right ihLeft ihRight | eq left right ihLeft ihRight =>
      cases hl : substConst? replacements left with
      | none => simp [substConst?, hl] at success
      | some _ =>
          cases hr : substConst? replacements right with
          | none => simp [substConst?, hl, hr] at success
          | some _ =>
              unfold expand
              rw [optionCasesOn_some _ _ _ _ _ hl]
              dsimp only
              rw [eqRec_eq_arrow, optionRec_some _ _ _ _ _ hr, eqRec_eq_arrow]
              simp [ihLeft hl, ihRight hr]
  | not body ih | all body ih | ex body ih =>
      cases hb : substConst? replacements body with
      | none => simp [substConst?, hb] at success
      | some _ =>
          unfold expand
          rw [optionCasesOn_some _ _ _ _ _ hb]
          dsimp only
          rw [eqRec_eq_arrow]
          simp [ih hb]
  | lam body ih =>
      cases hb : substConst? replacements body with
      | none => simp [substConst?, hb] at success
      | some _ =>
          unfold expand
          rw [optionCasesOn_some _ _ _ _ _ hb]
          dsimp only
          rw [eqRec_eq_arrow]
          simp [ProofSyntax.FunctionExtensionalityFree, ih hb]

end ConstantExpansionProofs

namespace ConstantExpansionProofsFreeControls

inductive Constant : Ty Empty → Type where
  | atom : Constant .prop
  | identity : Constant (.prop ⇒ .prop)
  | missing : Constant .prop

def replacements : {type : Ty Empty} → Constant type → Option (ClosedTerm Constant type)
  | _, .atom => some .top
  | _, .identity => some (.lam (.var .vz))
  | _, .missing => none

def theory : List (ClosedFormula Constant) :=
  [.eq (.const .atom) .top, .eq (.const .identity) (.lam (.var .vz))]

def equations : {type : Ty Empty} → (constant : Constant type) → (body : ClosedTerm Constant type) →
    replacements constant = some body → ProofSyntax Constant theory (.eq (.const constant) body)
  | _, .atom, _, present => by
      cases Option.some.inj present
      exact .hyp ⟨0, by decide⟩
  | _, .identity, _, present => by
      cases Option.some.inj present
      exact .hyp ⟨1, by decide⟩
  | _, .missing, _, present => by cases present

theorem equations_free {type : Ty Empty} (constant : Constant type) (body : ClosedTerm Constant type)
    (present : replacements constant = some body) :
    (equations constant body present).FunctionExtensionalityFree := by
  cases constant with
  | atom | identity => cases Option.some.inj present; trivial
  | missing => cases present

/-- Two nested object binders retain the distinct inner and outer variables. -/
def source : ClosedFormula Constant :=
  .all (.ex (.and (.app (.const .identity) (.var .vz))
    (.eq (.var (.vs .vz)) (.const .atom))))

def target : ClosedFormula Constant :=
  .all (.ex (.and (.app (.lam (.var .vz)) (.var .vz))
    (.eq (.var (.vs .vz)) .top)))

theorem traversal : substConst? replacements source = some target := rfl

def expanded : ProofSyntax Constant (ConstantExpansionProofs.assumptionsAt theory []) (.eq source target) :=
  ConstantExpansionProofs.expand theory replacements equations source traversal

theorem expanded_free : expanded.FunctionExtensionalityFree :=
  ConstantExpansionProofs.expand_free theory replacements equations equations_free source traversal

def capturedTarget : ClosedFormula Constant :=
  .all (σ := .prop) (.ex (.and (.app (.lam (.var .vz)) (.var .vz)) (.eq (.var .vz) .top)))

theorem capture_refused : substConst? replacements source ≠ some capturedTarget := by
  rw [traversal]
  intro same
  cases same

theorem used_missing_refused :
    substConst? replacements (.all (σ := .prop) (.const .missing) : ClosedFormula Constant) = none := rfl

/-- A supplied eta proof cannot be passed off as evidence in the restricted fragment. -/
def etaReplacements : {type : Ty Empty} → Constant type → Option (ClosedTerm Constant type)
  | _, .identity => some (.lam (.app (.const .identity) (.var .vz)))
  | _, .atom | _, .missing => none

def etaEquations : {type : Ty Empty} → (constant : Constant type) → (body : ClosedTerm Constant type) →
    etaReplacements constant = some body → ProofSyntax Constant [] (.eq (.const constant) body)
  | _, .identity, _, present => by
      cases Option.some.inj present
      exact .eqSymm (.eta (.const Constant.identity))
  | _, .atom, _, present | _, .missing, _, present => by cases present

def etaExpanded := ConstantExpansionProofs.expand [] etaReplacements etaEquations
  (.const .identity : ClosedTerm Constant (.prop ⇒ .prop)) rfl

theorem supplied_eta_not_free : ¬etaExpanded.FunctionExtensionalityFree := by
  exact fun impossible => impossible

end ConstantExpansionProofsFreeControls

#print axioms ContextualTrinity.allCongr_free
#print axioms ContextualTrinity.exCongr_free
#print axioms ProofSyntax.andCongr_free
#print axioms ProofSyntax.eqCongr_free
#print axioms ConstantExpansionProofs.weakenProof_free
#print axioms ConstantExpansionProofs.expand_free
#print axioms ConstantExpansionProofsFreeControls.expanded_free
#print axioms ConstantExpansionProofsFreeControls.capture_refused
#print axioms ConstantExpansionProofsFreeControls.used_missing_refused
#print axioms ConstantExpansionProofsFreeControls.supplied_eta_not_free

end Mettapedia.Logic.HOL
