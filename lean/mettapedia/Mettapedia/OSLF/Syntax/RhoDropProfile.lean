import Mettapedia.OSLF.Syntax.RhoCommunicationSchema
import Mettapedia.OSLF.Syntax.LinearContexts

/-!
# Reflection and communication in the chapter-seven rho presentation

The source lists communication and Drop as distinct operational rules.  The
authored ACU presentation below isolates the exact question of whether the
second rule follows from the first.  Its equations rearrange parallel
components; they do not themselves identify `drop (quote P)` with `P`.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema

set_option autoImplicit false

/-- A structural one-hole context with the hole on the left of parallel. -/
def parLeftHole (remainder : Term sig [] Srt.pr) :
    LinCtx sig Srt.pr [] Srt.pr :=
  .op Op.par (.here .hole (.cons remainder .nil))

/-- A structural one-hole context with the hole on the right of parallel. -/
def parRightHole (remainder : Term sig [] Srt.pr) :
    LinCtx sig Srt.pr [] Srt.pr :=
  .op Op.par (.there remainder (.here .hole .nil))

theorem parLeftHole_inst (remainder process : Term sig [] Srt.pr) :
    inst (LinCtx.toTerm (parLeftHole remainder)) process = parT process remainder := by
  change Term.op Op.par (.cons process
    (.cons (inst (weaken remainder) process) .nil)) = parT process remainder
  rw [inst_weaken]

theorem parRightHole_inst (remainder process : Term sig [] Srt.pr) :
    inst (LinCtx.toTerm (parRightHole remainder)) process = parT remainder process := by
  change Term.op Op.par (.cons (inst (weaken remainder) process)
    (.cons process .nil)) = parT remainder process
  rw [inst_weaken]

/-- The output operator contributes one occurrence. -/
def outputHeadCount {s : Srt} (o : Op s) : Nat :=
  match o with
  | .out => 1
  | _ => 0

mutual
/-- Count output occurrences, including occurrences below input binders,
quotes, and drops. -/
def outputCount : {Γ : Ctx sig} → {s : Srt} → Term sig Γ s → Nat
  | _, _, .var _ => 0
  | _, _, .op o args => outputHeadCount o + outputCountArgs args

def outputCountArgs : {as : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig as Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => outputCount head + outputCountArgs tail
end

mutual
/-- Renaming does not change the output count. -/
theorem outputCount_rename : ∀ {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ)
    {s : Srt} (term : Term sig Γ s),
    outputCount (rename rho term) = outputCount term
  | _, _, _, _, .var _ => rfl
  | _, _, rho, _, .op _ args => by
      simp only [rename, outputCount, outputCountArgs_rename rho args]

theorem outputCountArgs_rename : ∀ {Γ Δ : Ctx sig} (rho : Ren sig Γ Δ)
    {as : List (List Srt × Srt)} (args : Args sig as Γ),
    outputCountArgs (renameArgs rho args) = outputCountArgs args
  | _, _, _, _, .nil => rfl
  | _, _, rho, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, outputCountArgs,
        outputCount_rename (liftRen rho bs) head,
        outputCountArgs_rename rho tail]
end

/-- A lifted substitution still sends every occurrence of the selected outer
variable to a term containing an output. -/
theorem outputCount_liftSub_positive {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ) {c : Srt} (x : Var Γ c)
    (positive : ∀ {s : Srt} (v : Var Γ s),
      sameVar x v = true → 0 < outputCount (sigma s v)) :
    ∀ (bs : List Srt) {s : Srt} (v : Var (bs ++ Γ) s),
      sameVar (weakenVar bs x) v = true →
        0 < outputCount (liftSub sigma bs s v)
  | [], _, v, h => positive v h
  | _ :: bs, _, .zero, h => by cases h
  | _ :: bs, _, .succ v, h => by
      change sameVar (weakenVar bs x) v = true at h
      change 0 < outputCount (weaken (liftSub sigma bs _ v))
      rw [show outputCount (weaken (liftSub sigma bs _ v)) =
        outputCount (liftSub sigma bs _ v) from outputCount_rename _ _]
      exact outputCount_liftSub_positive sigma x positive bs v h

mutual
/-- If a selected variable occurs in a term and its substitution image
contains an output, the substituted term contains an output. -/
theorem outputCount_bind_positive : ∀ {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {c : Srt} (x : Var Γ c)
    (_ : ∀ {s : Srt} (v : Var Γ s),
      sameVar x v = true → 0 < outputCount (sigma s v))
    {s : Srt} (term : Term sig Γ s),
    0 < countVar x term → 0 < outputCount (bind sigma term)
  | _, _, sigma, _, x, positive, _, .var v, occurs => by
      simp only [countVar] at occurs
      simp only [bind]
      exact positive v (by cases h : sameVar x v <;> simp [h] at occurs ⊢)
  | _, _, sigma, _, x, positive, _, .op o args, occurs => by
      have child := outputCountArgs_bind_positive sigma x positive args (by
        simpa only [countVar] using occurs)
      simp only [bind, outputCount]
      omega

theorem outputCountArgs_bind_positive : ∀ {Γ Δ : Ctx sig} (sigma : Sub sig Γ Δ)
    {c : Srt} (x : Var Γ c)
    (_ : ∀ {s : Srt} (v : Var Γ s),
      sameVar x v = true → 0 < outputCount (sigma s v))
    {as : List (List Srt × Srt)} (args : Args sig as Γ),
    0 < countVarArgs x args → 0 < outputCountArgs (bindArgs sigma args)
  | _, _, _, _, _, _, _, .nil, occurs => by simp [countVarArgs] at occurs
  | _, _, sigma, _, x, positive, _, .cons (bs := bs) head tail, occurs => by
      simp only [countVarArgs] at occurs
      simp only [bindArgs, outputCountArgs]
      rcases lt_or_ge 0 (countVar (weakenVar bs x) head) with headOccurs | headZero
      · have headPositive := outputCount_bind_positive (liftSub sigma bs)
          (weakenVar bs x)
          (outputCount_liftSub_positive sigma x positive bs) head headOccurs
        omega
      · have tailOccurs : 0 < countVarArgs x tail := by omega
        have tailPositive := outputCountArgs_bind_positive sigma x positive tail tailOccurs
        omega
end

/-- ACU equations preserve the number of output occurrences in every scope. -/
theorem outputCount_axiom : ∀ (i : Fin rhoE.length) {Γ : Ctx sig}
    (body : (k : Fin metas.length) → Term sig (metas.get k).1 (metas.get k).2)
    (close : Sub sig (rhoE.get i).ctx Γ),
    outputCount (bind close (instantiate body (rhoE.get i).lhs)) =
      outputCount (bind close (instantiate body (rhoE.get i).rhs))
  | ⟨0, _⟩, _, body, close => by
      show outputCount (bind close (instantiate body commPar.lhs)) =
        outputCount (bind close (instantiate body commPar.rhs))
      simp only [commPar, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        outputCount, outputCountArgs, outputHeadCount]
      omega
  | ⟨1, _⟩, _, body, close => by
      show outputCount (bind close (instantiate body assocPar.lhs)) =
        outputCount (bind close (instantiate body assocPar.rhs))
      simp only [assocPar, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        outputCount, outputCountArgs, outputHeadCount]
      omega
  | ⟨2, _⟩, _, body, close => by
      show outputCount (bind close (instantiate body rightUnitPar.lhs)) =
        outputCount (bind close (instantiate body rightUnitPar.rhs))
      simp only [rightUnitPar, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        outputCount, outputCountArgs, outputHeadCount]
      omega
  | ⟨_ + 3, h⟩, _, _, _ => by simp [rhoE] at h

mutual
/-- The output count descends to the authored structural congruence. -/
theorem outputCount_eqClosure : ∀ {Γ : Ctx sig} {s : Srt}
    {t u : Term sig Γ s}, EqClosure rhoE t u → outputCount t = outputCount u
  | _, _, _, _, .ax i body close => outputCount_axiom i body close
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (outputCount_eqClosure h).symm
  | _, _, _, _, .trans h h' => (outputCount_eqClosure h).trans (outputCount_eqClosure h')
  | _, _, _, _, .cong _ h => by
      simp only [outputCount, outputCountArgs_eqClosure h]

theorem outputCountArgs_eqClosure : ∀ {as : List (List Srt × Srt)}
    {Γ : Ctx sig} {x y : Args sig as Γ},
    EqArgs rhoE x y → outputCountArgs x = outputCountArgs y
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      simp only [outputCountArgs, outputCount_eqClosure head,
        outputCountArgs_eqClosure tail]
end

/-! ## The independently authored Drop rule -/

/-- `*( @P )`: the left-hand side of the Chapter 7 Drop rule. -/
def dropLhs : Term schemaSig [Srt.pr] Srt.pr :=
  Term.op (S := schemaSig) (Sum.inl Op.drp)
    (.cons (Term.op (S := schemaSig) (Sum.inl Op.quo)
      (.cons (.var .zero) .nil)) .nil)

/-- Drop returns the process that was quoted. -/
def dropRhs : Term schemaSig [Srt.pr] Srt.pr := .var .zero

/-- Drop, with the whole redex selected as its operational focus. -/
def dropRule : PositionedRewrite schemaSig where
  ctx := [Srt.pr]
  sort := Srt.pr
  lhs := dropLhs
  rhs := dropRhs
  position :=
    { carrier := Srt.pr
      ctxt := .var .zero
      redex := dropLhs
      plugs := rfl
      linear := rfl }

/-- The ACU communication theory extended by the distinct Drop rewrite. -/
def rhoACUWithDrop : Presentation sig where
  metas := metas
  eqs := rhoE
  rules := [comm, dropRule]

/-- Every old communication step remains a step of the extension. -/
theorem rho_step_in_ACUWithDrop {s : Srt} {source target : Term sig [] s}
    (h : rho.StepModE source target) :
    rhoACUWithDrop.StepModE source target := by
  obtain ⟨i, fires⟩ := h
  have first : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rho] using i.isLt
    change i.val = 0
    omega)
  subst i
  exact ⟨⟨0, by decide⟩, fires⟩

/-- Closing the Drop rule with a process. -/
def closeDrop (process : Term sig [] Srt.pr) : Sub sig [Srt.pr] []
  | _, .zero => process

/-- The extension reduces every closed quote/drop round trip. -/
theorem drop_round_trip (process : Term sig [] Srt.pr) :
    rhoACUWithDrop.StepModE
      (Term.op (S := sig) (Γ := []) Op.drp
        (.cons (Term.op (S := sig) (Γ := []) Op.quo (.cons process .nil)) .nil))
      process := by
  apply Presentation.stepModE_of_rule (i := ⟨1, by decide⟩)
  apply stepModE_of_step
  apply step_of_rootStep
  exact rootStep_of_instance dropRule
    { body := contDiscard
      close := closeDrop process }

/-- In particular, the quoted null process returns to null. -/
theorem drop_nil : rhoACUWithDrop.StepModE dropChan nilP :=
  drop_round_trip nilP

/-- The separate reflection equation from Chapter 7, at the name sort:
`@(*n) = n`. It is distinct from the process-sorted Drop rewrite. -/
def quoteDrop : EqAxiom sig metas where
  ctx := [Srt.nm]
  sort := Srt.nm
  lhs := Term.op (S := schemaSig) (Sum.inl Op.quo)
    (.cons (Term.op (S := schemaSig) (Sum.inl Op.drp)
      (.cons (.var .zero) .nil)) .nil)
  rhs := .var .zero

/-- ACU, unit, and the authored name-sorted reflection equation. -/
abbrev rhoSourceE : List (EqAxiom sig metas) :=
  [commPar, assocPar, rightUnitPar, quoteDrop]

/-- A binary-ACU encoding of Chapter 7's communication rule and equations.
Comparison to the canonical hash-bag rule with a collection rest is separate. -/
def rhoSourceComm : Presentation sig where
  metas := metas
  eqs := rhoSourceE
  rules := [comm]

/-- The binary-ACU profile with both Chapter 7 operational rules. -/
def rhoSourceWithDrop : Presentation sig where
  metas := metas
  eqs := rhoSourceE
  rules := [comm, dropRule]

/-- The source's name-sorted reflection equation holds in both Chapter 7
profiles. -/
theorem quote_drop_equation (name : Term sig [] Srt.nm) :
    EqClosure rhoSourceE
      (Term.op (S := sig) (Γ := []) Op.quo
        (.cons (Term.op (S := sig) (Γ := []) Op.drp (.cons name .nil)) .nil))
      name :=
  EqClosure.ax (E := rhoSourceE) 3 contDiscard
    (fun _ v => match v with | .zero => name)

/-- Extending the rule list retains every communication step with the full
source equation set. -/
theorem source_comm_step_in_withDrop {s : Srt}
    {source target : Term sig [] s}
    (h : rhoSourceComm.StepModE source target) :
    rhoSourceWithDrop.StepModE source target := by
  obtain ⟨i, fires⟩ := h
  have first : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rhoSourceComm] using i.isLt
    change i.val = 0
    omega)
  subst i
  exact ⟨⟨0, by decide⟩, fires⟩

/-- The source's ParCong action on the left component is supplied by
composition of linear contexts, for either Comm or Drop, and remains valid
after the structural equations are applied. -/
theorem source_par_cong_left (remainder : Term sig [] Srt.pr)
    {source target : Term sig [] Srt.pr}
    (step : rhoSourceWithDrop.StepModE source target) :
    rhoSourceWithDrop.StepModE
      (parT source remainder) (parT target remainder) := by
  obtain ⟨i, source', target', before, fires, after⟩ := step
  have beforePar : EqClosure rhoSourceE
      (parT source remainder) (parT source' remainder) :=
    EqClosure.cong (E := rhoSourceE) Op.par
      (.cons before (.cons (.refl remainder) .nil))
  have afterPar : EqClosure rhoSourceE
      (parT target' remainder) (parT target remainder) :=
    EqClosure.cong (E := rhoSourceE) Op.par
      (.cons after (.cons (.refl remainder) .nil))
  refine ⟨i, parT source' remainder, parT target' remainder,
    beforePar, ?_, afterPar⟩
  fin_cases i
  · change Step comm source' target' at fires
    change Step comm (parT source' remainder) (parT target' remainder)
    have under := step_under_linear_context comm (parLeftHole remainder) fires
    simpa only [parLeftHole_inst] using under
  · change Step dropRule source' target' at fires
    change Step dropRule (parT source' remainder) (parT target' remainder)
    have under := step_under_linear_context dropRule (parLeftHole remainder) fires
    exact (parLeftHole_inst remainder source') ▸
      (parLeftHole_inst remainder target') ▸ under

/-- Parallel congruence also holds on the right component of the binary ACU
encoding, without needing to choose an equation representative first. -/
theorem source_par_cong_right (remainder : Term sig [] Srt.pr)
    {source target : Term sig [] Srt.pr}
    (step : rhoSourceWithDrop.StepModE source target) :
    rhoSourceWithDrop.StepModE
      (parT remainder source) (parT remainder target) := by
  obtain ⟨i, source', target', before, fires, after⟩ := step
  have beforePar : EqClosure rhoSourceE
      (parT remainder source) (parT remainder source') :=
    EqClosure.cong (E := rhoSourceE) Op.par
      (.cons (.refl remainder) (.cons before .nil))
  have afterPar : EqClosure rhoSourceE
      (parT remainder target') (parT remainder target) :=
    EqClosure.cong (E := rhoSourceE) Op.par
      (.cons (.refl remainder) (.cons after .nil))
  refine ⟨i, parT remainder source', parT remainder target',
    beforePar, ?_, afterPar⟩
  fin_cases i
  · change Step comm source' target' at fires
    change Step comm (parT remainder source') (parT remainder target')
    have under := step_under_linear_context comm (parRightHole remainder) fires
    simpa only [parRightHole_inst] using under
  · change Step dropRule source' target' at fires
    change Step dropRule (parT remainder source') (parT remainder target')
    have under := step_under_linear_context dropRule (parRightHole remainder) fires
    exact (parRightHole_inst remainder source') ▸
      (parRightHole_inst remainder target') ▸ under

/-- The original ACU communication profile embeds into the Chapter 7
communication profile. Its equations and rule are literally retained. -/
theorem rho_step_in_sourceComm {s : Srt}
    {source target : Term sig [] s}
    (h : rho.StepModE source target) :
    rhoSourceComm.StepModE source target := by
  obtain ⟨i, source', target', before, firing, after⟩ := h
  have first : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rho] using i.isLt
    change i.val = 0
    omega)
  subst i
  have includes : ∀ i : Fin rhoE.length,
      ∃ j : Fin rhoSourceE.length, rhoSourceE.get j = rhoE.get i := by
    intro i
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  exact ⟨⟨0, by decide⟩, source', target',
    eqClosure_of_axiom_inclusion includes before, firing,
    eqClosure_of_axiom_inclusion includes after⟩

/-- Both the equation and the reduction are realized by the combined profile. -/
theorem source_drop_nil : rhoSourceWithDrop.StepModE dropChan nilP := by
  exact ⟨⟨1, by decide⟩, dropChan, nilP,
    EqClosure.refl _,
    step_of_rootStep dropRule
      (rootStep_of_instance dropRule
        { body := contDiscard, close := closeDrop nilP }),
    EqClosure.refl _⟩

/-! ## Drop is not a consequence of communication and ACU -/

/-- Every root communication consumes a source containing an output, regardless
of the continuation or closing substitution. -/
theorem root_comm_has_output {source target : Term sig [] Srt.pr}
    (fires : RootStep comm source target) : 0 < outputCount source := by
  obtain ⟨ruleInstance, sourceEq, _⟩ := fires
  rw [← sourceEq]
  simp only [commLhs, instantiate, instantiateArgs, bind, bindArgs, liftSub,
    outputCount, outputCountArgs, outputHeadCount]
  omega

/-- A linear context cannot erase the output needed by communication. -/
theorem contextual_comm_has_output {s : Srt} {source target : Term sig [] s}
    (fires : Step comm source target) : 0 < outputCount source := by
  obtain ⟨context, redex, reduct, linear, root, sourceEq, _⟩ := fires
  have redexPositive := root_comm_has_output root
  rw [← sourceEq]
  unfold inst
  refine outputCount_bind_positive (extend redex)
    (Var.zero : Var [Srt.pr] Srt.pr) ?_ context ?_
  · intro s v matched
    cases v with
    | zero => simpa only [extend] using redexPositive
    | succ v => cases matched
  · change countVar (Var.zero : Var [Srt.pr] Srt.pr) context = 1 at linear
    omega

/-- Structural congruence does not create an output at a communication source. -/
theorem equation_closed_comm_has_output {s : Srt}
    {source target : Term sig [] s}
    (fires : StepModE rhoE comm source target) : 0 < outputCount source := by
  obtain ⟨source', target', before, step, _⟩ := fires
  rw [outputCount_eqClosure before]
  exact contextual_comm_has_output step

/-- A quoted null process, immediately dropped, has no output occurrence. -/
theorem dropChan_has_no_output : outputCount dropChan = 0 := rfl

/-- The Comm-only ACU presentation cannot execute Drop, even below a context
or after rearranging parallel components by its authored equations. -/
theorem drop_nil_not_comm (target : Term sig [] Srt.pr) :
    ¬ rho.StepModE dropChan target := by
  rintro ⟨i, fires⟩
  have onlyComm : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rho] using i.isLt
    change i.val = 0
    omega)
  subst i
  have positive := equation_closed_comm_has_output fires
  rw [dropChan_has_no_output] at positive
  omega

/-- Adding Drop genuinely adds a step on the old term carrier. -/
theorem rhoACUWithDrop_not_operationally_conservative :
    rhoACUWithDrop.StepModE dropChan nilP ∧
      ¬ rho.StepModE dropChan nilP :=
  ⟨drop_nil, drop_nil_not_comm nilP⟩

/-- The name-sorted reflection equation also preserves output count. Thus
adding it cannot turn a pure drop/quote source into a COMM redex. -/
theorem outputCount_source_axiom : ∀ (i : Fin rhoSourceE.length) {Γ : Ctx sig}
    (body : (k : Fin metas.length) → Term sig (metas.get k).1 (metas.get k).2)
    (close : Sub sig (rhoSourceE.get i).ctx Γ),
    outputCount (bind close (instantiate body (rhoSourceE.get i).lhs)) =
      outputCount (bind close (instantiate body (rhoSourceE.get i).rhs))
  | ⟨0, _⟩, _, body, close =>
      outputCount_axiom ⟨0, by decide⟩ body close
  | ⟨1, _⟩, _, body, close =>
      outputCount_axiom ⟨1, by decide⟩ body close
  | ⟨2, _⟩, _, body, close =>
      outputCount_axiom ⟨2, by decide⟩ body close
  | ⟨3, _⟩, _, body, close => by
      show outputCount (bind close (instantiate body quoteDrop.lhs)) =
        outputCount (bind close (instantiate body quoteDrop.rhs))
      simp only [quoteDrop, instantiate, instantiateArgs, bind, bindArgs, liftSub,
        outputCount, outputCountArgs, outputHeadCount]
      omega
  | ⟨_ + 4, h⟩, _, _, _ => by simp [rhoSourceE] at h

mutual
/-- Output count remains invariant under the complete Chapter 7 equations,
including congruence through input binders. -/
theorem outputCount_source_eqClosure : ∀ {Γ : Ctx sig} {s : Srt}
    {t u : Term sig Γ s}, EqClosure rhoSourceE t u → outputCount t = outputCount u
  | _, _, _, _, .ax i body close => outputCount_source_axiom i body close
  | _, _, _, _, .refl _ => rfl
  | _, _, _, _, .symm h => (outputCount_source_eqClosure h).symm
  | _, _, _, _, .trans h h' =>
      (outputCount_source_eqClosure h).trans (outputCount_source_eqClosure h')
  | _, _, _, _, .cong _ h => by
      simp only [outputCount, outputCountArgs_source_eqClosure h]

theorem outputCountArgs_source_eqClosure : ∀ {as : List (List Srt × Srt)}
    {Γ : Ctx sig} {x y : Args sig as Γ},
    EqArgs rhoSourceE x y → outputCountArgs x = outputCountArgs y
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons head tail => by
      simp only [outputCountArgs, outputCount_source_eqClosure head,
        outputCountArgs_source_eqClosure tail]
end

/-- COMM still requires an output after closing under all Chapter 7 equations. -/
theorem source_comm_has_output {s : Srt}
    {source target : Term sig [] s}
    (fires : StepModE rhoSourceE comm source target) :
    0 < outputCount source := by
  obtain ⟨source', target', before, step, _⟩ := fires
  rw [outputCount_source_eqClosure before]
  exact contextual_comm_has_output step

/-- The full source equation set does not derive Drop from COMM. -/
theorem source_drop_nil_not_comm (target : Term sig [] Srt.pr) :
    ¬ rhoSourceComm.StepModE dropChan target := by
  rintro ⟨i, fires⟩
  have onlyComm : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (by
    have bound : i.val < 1 := by simpa [rhoSourceComm] using i.isLt
    change i.val = 0
    omega)
  subst i
  have positive := source_comm_has_output fires
  rw [dropChan_has_no_output] at positive
  omega

/-- In this scoped binary-ACU encoding, the combined profile is a proper
operational extension of its Comm-only profile, not a conservative extension
of one-step behavior on the common process carrier. -/
theorem sourceWithDrop_is_proper_extension :
    rhoSourceWithDrop.StepModE dropChan nilP ∧
      ¬ rhoSourceComm.StepModE dropChan nilP :=
  ⟨source_drop_nil, source_drop_nil_not_comm nilP⟩


end Mettapedia.OSLF.Binding.RhoSchema
