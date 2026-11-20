import Mettapedia.GSLT.Compilation.CanonicalHornModule
import Mathlib.Data.List.OfFn

/-!
# The authored and moded readings of a Horn clause

The source interpretation ranges over the original constructor signature.
Compiler tags live only in the representation of a call and its result.
Readback projects payload terms onto the original signature; on the
authored image it recovers every constructor and every argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.CanonicalHornSemantics

open Mettapedia.Logic.LP (Term Atom Subst)
open Mettapedia.GSLT.Parsing
open Mettapedia.Data.List (option_mapM_forall₂)
open CanonicalHornModule ModedRuleModule

abbrev RawTerm := Term HornUnification.signature
abbrev RawAtom := Atom HornUnification.signature
abbrev RawSubst := Subst HornUnification.signature
abbrev RawTuple := HornUnification.RelationSymbol × List RawTerm

variable {Labels : Type}

def tuple (atom : RawAtom) : RawTuple :=
  (atom.symbol, List.ofFn atom.args)

/-- A total retraction used in the proof of source-model soundness.
Unexpected administrative terms are projected to a fixed constant.
This is not a run-time readback of a result. -/
def projectTerm : Datum Labels → RawTerm
  | .var v => .var v
  | .const c => .const c
  | .app (.con (.authored ctor)) fields => .app ctor fun i => projectTerm (fields i)
  | .app _ _ => .const (.atom "")

theorem project_wrap (term : RawTerm) :
    projectTerm (wrapTerm (Labels := Labels) term) = term := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app ctor args ih =>
      change Term.app ctor (fun i => projectTerm (wrapTerm (Labels := Labels) (args i))) = _
      exact congrArg (Term.app ctor) (funext ih)

theorem wrap_ground_iff (term : RawTerm) :
    (wrapTerm (Labels := Labels) term).isGround ↔ term.isGround := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app ctor args ih =>
      change (∀ i, (wrapTerm (Labels := Labels) (args i)).isGround) ↔
        (∀ i, (args i).isGround)
      exact forall_congr' ih

theorem wrap_atom_ground_iff (atom : RawAtom) :
    (wrapAtom (Labels := Labels) atom).isGround ↔ atom.isGround :=
  forall_congr' fun i => wrap_ground_iff (atom.args i)

def liftSubst (θ : RawSubst) : Subst (Signature Labels) := fun v => wrapTerm (θ v)

def projectSubst (θ : Subst (Signature Labels)) : RawSubst := fun v => projectTerm (θ v)

theorem wrap_apply (θ : RawSubst) (term : RawTerm) :
    wrapTerm (Labels := Labels) (θ.applyTerm term) =
      (liftSubst (Labels := Labels) θ).applyTerm (wrapTerm term) := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app ctor args ih =>
      exact congrArg (Term.app (σ := Signature Labels) (.con (.authored ctor))) (funext ih)

theorem project_apply_wrap (θ : Subst (Signature Labels)) (term : RawTerm) :
    projectTerm (θ.applyTerm (wrapTerm term)) = (projectSubst θ).applyTerm term := by
  induction term with
  | var _ => rfl
  | const _ => rfl
  | app ctor args ih =>
      change Term.app ctor _ = Term.app ctor _
      exact congrArg (Term.app ctor) (funext ih)

def projectAtom (atom : Atom (Signature Labels)) : RawAtom :=
  ⟨atom.symbol, fun i => projectTerm (atom.args i)⟩

theorem project_wrap_atom (atom : RawAtom) :
    projectAtom (wrapAtom (Labels := Labels) atom) = atom := by
  cases atom with
  | mk symbol args =>
      exact congrArg (Atom.mk symbol) (funext fun i => project_wrap (args i))

theorem wrap_apply_atom (θ : RawSubst) (atom : RawAtom) :
    wrapAtom (Labels := Labels) (θ.applyAtom atom) =
      (liftSubst (Labels := Labels) θ).applyAtom (wrapAtom atom) := by
  cases atom with
  | mk symbol args =>
      exact congrArg (Atom.mk (σ := Signature Labels) symbol)
        (funext fun i => wrap_apply (Labels := Labels) θ (args i))

theorem project_apply_wrap_atom (θ : Subst (Signature Labels)) (atom : RawAtom) :
    projectAtom (θ.applyAtom (wrapAtom atom)) = (projectSubst θ).applyAtom atom := by
  cases atom with
  | mk symbol args =>
      exact congrArg (Atom.mk symbol) (funext fun i => project_apply_wrap θ (args i))

def readback (modes : Modes) (row : Datum Labels × Datum Labels) : Option RawTuple := do
  let .app (.con (.call symbol _)) inputs := row.1 | none
  let .app (.con (.outputs _)) outputs := row.2 | none
  let .derived mask ← modes symbol | none
  let fields ← ModedArguments.assemble mask
    (List.ofFn fun i => projectTerm (inputs i))
    (List.ofFn fun i => projectTerm (outputs i))
  return (symbol, fields)

/-- Actual lowering components, separated by the checked mode. -/
theorem lowerAtom?_cases {modes : Modes} {atom : RawAtom}
    {literal : BodyLiteral (Signature Labels)}
    (compiled : lowerAtom? modes atom = some literal) :
    (modes atom.symbol = some .external ∧ literal = .extensional (wrapAtom atom)) ∨
    ∃ mask inputs outputs, modes atom.symbol = some (.derived mask) ∧
      ModedArguments.split mask (List.ofFn fun i => wrapTerm (Labels := Labels) (atom.args i)) =
        some (inputs, outputs) ∧
      literal = .intensional
        ⟨pack (.call atom.symbol inputs.length) inputs.get,
          pack (.outputs outputs.length) outputs.get⟩ := by
  cases mode : modes atom.symbol with
  | none => simp [lowerAtom?, mode] at compiled
  | some selected =>
      cases selected with
      | external => exact Or.inl ⟨rfl, by simpa [lowerAtom?, mode] using compiled.symm⟩
      | derived mask =>
          cases cols : ModedArguments.split mask
              (List.ofFn fun i => wrapTerm (Labels := Labels) (atom.args i)) with
          | none => simp [lowerAtom?, mode, splitCall?, cols] at compiled
          | some pair =>
              rcases pair with ⟨inputs, outputs⟩
              exact Or.inr ⟨mask, inputs, outputs, rfl, cols,
                by simpa [lowerAtom?, mode, splitCall?, cols] using compiled.symm⟩

def applyLiteral (θ : Subst (Signature Labels)) :
    BodyLiteral (Signature Labels) → BodyLiteral (Signature Labels)
  | .intensional row => .intensional ⟨θ.applyTerm row.input, θ.applyTerm row.output⟩
  | .extensional atom => .extensional (θ.applyAtom atom)

private theorem pack_eq_of_columns (tag : Nat → Symbol) {m n : Nat}
    {first : Fin (tag m).arity → Datum Labels} {second : Fin (tag n).arity → Datum Labels}
    (length : m = n) (columns : List.ofFn first = List.ofFn second) :
    pack (tag m) first = pack (tag n) second := by
  subst n
  exact congrArg (pack (tag m)) (List.ofFn_injective columns)

private theorem pack_apply (θ : Subst (Signature Labels)) (rel : HornUnification.RelationSymbol)
    (inputs outputs : List (Datum Labels)) :
    (⟨θ.applyTerm (pack (.call rel inputs.length) inputs.get),
      θ.applyTerm (pack (.outputs outputs.length) outputs.get)⟩ : CallRow (Signature Labels)) =
      ⟨pack (.call rel (inputs.map θ.applyTerm).length) (inputs.map θ.applyTerm).get,
        pack (.outputs (outputs.map θ.applyTerm).length) (outputs.map θ.applyTerm).get⟩ := by
  have left : θ.applyTerm (pack (.call rel inputs.length) inputs.get) =
      pack (.call rel (inputs.map θ.applyTerm).length) (inputs.map θ.applyTerm).get := by
    change pack (.call rel inputs.length) (fun i => θ.applyTerm (inputs.get i)) = _
    apply pack_eq_of_columns (.call rel ·) (List.length_map θ.applyTerm).symm
    change List.ofFn (θ.applyTerm ∘ inputs.get) = List.ofFn (inputs.map θ.applyTerm).get
    rw [← List.map_ofFn, List.ofFn_get, List.ofFn_get]
  have right : θ.applyTerm (pack (.outputs outputs.length) outputs.get) =
      pack (.outputs (outputs.map θ.applyTerm).length) (outputs.map θ.applyTerm).get := by
    change pack (.outputs outputs.length) (fun i => θ.applyTerm (outputs.get i)) = _
    apply pack_eq_of_columns Symbol.outputs (List.length_map θ.applyTerm).symm
    change List.ofFn (θ.applyTerm ∘ outputs.get) = List.ofFn (outputs.map θ.applyTerm).get
    rw [← List.map_ofFn, List.ofFn_get, List.ofFn_get]
  rw [left, right]

theorem lowerAtom?_apply {modes : Modes} {atom : RawAtom}
    {literal : BodyLiteral (Signature Labels)} (compiled : lowerAtom? modes atom = some literal)
    (θ : RawSubst) :
    lowerAtom? modes (θ.applyAtom atom) = some (applyLiteral (liftSubst θ) literal) := by
  rcases lowerAtom?_cases compiled with ⟨mode, rfl⟩ | ⟨mask, inputs, outputs, mode, split, rfl⟩
  · simp only [lowerAtom?, show (θ.applyAtom atom).symbol = atom.symbol from rfl, mode,
      applyLiteral]
    exact congrArg (some ∘ BodyLiteral.extensional) (wrap_apply_atom θ atom)
  · let lifted := liftSubst (Labels := Labels) θ
    have split' :
        ModedArguments.split mask (List.ofFn fun i =>
          wrapTerm (Labels := Labels) (θ.applyTerm (atom.args i))) =
          some (inputs.map lifted.applyTerm, outputs.map lifted.applyTerm) := by
      have corresponding : lifted.applyTerm ∘ (fun i => wrapTerm (atom.args i)) =
          (fun i => wrapTerm (θ.applyTerm (atom.args i))) :=
        funext fun i => (wrap_apply (Labels := Labels) θ (atom.args i)).symm
      simpa only [List.map_ofFn, corresponding] using
        ModedArguments.split_map lifted.applyTerm split
    have substRow := pack_apply lifted atom.symbol inputs outputs
    simpa [lowerAtom?, Subst.applyAtom, mode, splitCall?, split', applyLiteral, lifted]
      using congrArg (some ∘ BodyLiteral.intensional) substRow.symm

theorem readback_instantiated_call {modes : Modes} {atom : RawAtom}
    {row : CallRow (Signature Labels)}
    (compiled : lowerAtom? modes atom = some (.intensional row))
    (θ : Subst (Signature Labels)) :
    readback modes (row.instantiate θ) = some (tuple ((projectSubst θ).applyAtom atom)) := by
  rcases lowerAtom?_cases compiled with ⟨_, impossible⟩ | ⟨mask, inputs, outputs, mode, split, same⟩
  · cases impossible
  · cases same
    let read : Datum Labels → RawTerm := fun t => projectTerm (θ.applyTerm t)
    have recovered := ModedArguments.assemble_split (ModedArguments.split_map read split)
    change (do
      let .derived selected ← modes atom.symbol | none
      let args ← ModedArguments.assemble selected (List.ofFn (read ∘ inputs.get))
        (List.ofFn (read ∘ outputs.get))
      pure (atom.symbol, args)) = _
    rw [← List.map_ofFn, ← List.map_ofFn, List.ofFn_get, List.ofFn_get]
    simp [mode, recovered, List.map_ofFn, Function.comp_def, read, project_apply_wrap,
      Subst.applyAtom, tuple]

theorem readback_compile_call {modes : Modes} {atom : RawAtom}
    {row : CallRow (Signature Labels)}
    (compiled : lowerAtom? modes atom = some (.intensional row)) :
    readback modes (row.input, row.output) = some (tuple atom) := by
  have projects : projectSubst (Subst.id (Signature Labels)) =
      Subst.id HornUnification.signature := rfl
  simpa only [CallRow.instantiate, Subst.applyTerm_id, Subst.applyAtom_id, projects] using
    readback_instantiated_call compiled (Subst.id (Signature Labels))

theorem tuple_injective : Function.Injective tuple := by
  intro a b same
  cases a with
  | mk symbol xs =>
      cases b with
      | mk symbol' ys =>
          have head : symbol = symbol' := congrArg Prod.fst same
          subst symbol'
          exact congrArg (Atom.mk symbol) (List.ofFn_injective (congrArg Prod.snd same))

/-- A source declaration says where a relation gets its facts. It says
nothing about which columns demand-driven evaluation must know first. -/
inductive RelationRole where
  | derived
  | external

abbrev RelationRoles := HornUnification.RelationSymbol → Option RelationRole

def rolesOf (modes : Modes) : RelationRoles := fun relation =>
  match modes relation with
  | some (.derived _) => some .derived
  | some .external => some .external
  | none => none

/-- Interpret the premises in the original Horn constructor signature.
The interpretation has no mode mask, demand key, or evaluation strategy. -/
def sourceHolds (roles : RelationRoles) (facts model : Set RawAtom) (θ : RawSubst)
    (atom : RawAtom) : Prop :=
  match roles atom.symbol with
  | some .external => θ.applyAtom atom ∈ facts
  | some .derived => θ.applyAtom atom ∈ model
  | none => False

def SourceClosed (roles : RelationRoles) (source : Labels → HornCertificate.Rule)
    (facts model : Set RawAtom) : Prop :=
  ∀ label θ, (∀ a ∈ (source label).body,
    sourceHolds roles facts model θ (HornUnification.encodeAtom a)) →
      θ.applyAtom (HornUnification.encodeAtom (source label).head) ∈ model

def SourceLeast (roles : RelationRoles) (source : Labels → HornCertificate.Rule)
    (facts : Set RawAtom) (goal : RawAtom) : Prop :=
  ∀ model, SourceClosed roles source facts model → goal ∈ model

/-- Only the roles of actual source premises enter the source model. -/
theorem sourceLeast_congr {first second : RelationRoles}
    (source : Labels → HornCertificate.Rule) (facts : Set RawAtom) (goal : RawAtom)
    (same : ∀ label a, a ∈ (source label).body →
      first (HornUnification.encodeAtom a).symbol = second (HornUnification.encodeAtom a).symbol) :
    SourceLeast first source facts goal ↔ SourceLeast second source facts goal := by
  have equivalent (model : Set RawAtom) :
      SourceClosed first source facts model ↔ SourceClosed second source facts model := by
    have premise (label : Labels) (θ : RawSubst) (a : HornCertificate.Atom)
        (member : a ∈ (source label).body) :
        sourceHolds first facts model θ (HornUnification.encodeAtom a) ↔
          sourceHolds second facts model θ (HornUnification.encodeAtom a) := by
      simp only [sourceHolds, same label a member]
    exact ⟨fun closed label θ holds => closed label θ fun a member =>
      (premise label θ a member).mpr (holds a member),
      fun closed label θ holds => closed label θ fun a member =>
        (premise label θ a member).mp (holds a member)⟩
  exact ⟨fun least model closed => least model ((equivalent model).mpr closed),
    fun least model closed => least model ((equivalent model).mp closed)⟩

private theorem all_paired_imp {α β : Type} {pairs : α → β → Prop}
    {left : List α} {right : List β} {P : α → Prop} {Q : β → Prop}
    (paired : List.Forall₂ pairs left right)
    (pointwise : ∀ a b, pairs a b → P a → Q b) :
    (∀ a ∈ left, P a) → (∀ b ∈ right, Q b) := by
  induction paired with
  | nil => exact fun _ _ member => False.elim (List.not_mem_nil member)
  | cons p ps ih =>
      simp only [List.forall_mem_cons]
      exact fun prior => ⟨pointwise _ _ p prior.1, ih prior.2⟩

private def pullModel (modes : Modes) (sourceModel : Set RawAtom) :
    Set (Datum Labels × Datum Labels) :=
  { row | ∀ a, readback modes row = some (tuple a) → a ∈ sourceModel }

private def pushModel (modes : Modes) (targetModel : Set (Datum Labels × Datum Labels)) :
    Set RawAtom :=
  { a | ∀ row, lowerAtom? modes a = some (.intensional row) →
      (row.input, row.output) ∈ targetModel }

private theorem sourceHolds_of_pull {modes : Modes} {atom : RawAtom}
    {lit : BodyLiteral (Signature Labels)} (compiled : lowerAtom? modes atom = some lit)
    (θ : Subst (Signature Labels)) (facts model : Set RawAtom) :
    literalHolds (wrapAtom '' facts) (pullModel modes model) θ lit →
      sourceHolds (rolesOf modes) facts model (projectSubst θ) atom := by
  rcases lowerAtom?_cases compiled with ⟨mode, rfl⟩ | ⟨mask, inputs, outputs, mode, _, rfl⟩
  · simp only [sourceHolds, rolesOf, mode, literalHolds]
    rintro ⟨fact, member, same⟩
    rw [← project_apply_wrap_atom θ atom, ← same, project_wrap_atom]
    exact member
  · simp only [sourceHolds, rolesOf, mode, literalHolds]
    intro holds
    exact holds _ (readback_instantiated_call compiled θ)

private theorem literalHolds_of_push {modes : Modes} {atom : RawAtom}
    {lit : BodyLiteral (Signature Labels)} (compiled : lowerAtom? modes atom = some lit)
    (θ : RawSubst) (facts : Set RawAtom) (model : Set (Datum Labels × Datum Labels)) :
    sourceHolds (rolesOf modes) facts (pushModel modes model) θ atom →
      literalHolds (wrapAtom '' facts) model (liftSubst θ) lit := by
  rcases lowerAtom?_cases compiled with ⟨mode, rfl⟩ | ⟨mask, inputs, outputs, mode, _, rfl⟩
  · simp only [sourceHolds, rolesOf, mode, literalHolds]
    intro member
    exact ⟨_, member, wrap_apply_atom θ atom⟩
  · simp only [sourceHolds, rolesOf, mode, literalHolds]
    intro holds
    exact holds _ (lowerAtom?_apply compiled θ)

/-- For each authored goal with a declared input/output mode, the least
models before and after compilation agree. The hypothesis aligns source
and emitted rule occurrences; the proof does not posit source/target
semantic equivalence. External facts are transported by the same
injective constructor encoding. -/
theorem least_iff_source (modes : Modes) (source : Labels → HornCertificate.Rule)
    (target : Labels → Clause (Signature Labels))
    (compiled : ∀ label, compileRule? modes (source label) = some (target label))
    (facts : Set RawAtom) (goal : RawAtom) (row : CallRow (Signature Labels))
    (goalMode : lowerAtom? modes goal = some (.intensional row)) :
    Least target (wrapAtom '' facts) (row.input, row.output) ↔
      SourceLeast (rolesOf modes) source facts goal := by
  constructor
  · intro least sourceModel closed
    have targetClosed : Closed target (wrapAtom '' facts) (pullModel modes sourceModel) := by
      intro l θ premises queried read
      obtain ⟨head, body, _⟩ := compileRule?_components (compiled l)
      have paired := option_mapM_forall₂ (lowerCall? modes) (source l).body (target l).body body
      have proved : ∀ raw ∈ (source l).body,
          sourceHolds (rolesOf modes) facts sourceModel (projectSubst θ)
            (HornUnification.encodeAtom raw) :=
        all_paired_imp paired.flip
          (fun _ _ accepted => sourceHolds_of_pull accepted θ facts sourceModel) premises
      have inModel := closed l (projectSubst θ) proved
      have observed := readback_instantiated_call head θ
      have equal := tuple_injective (Option.some.inj (read.symm.trans observed))
      rwa [equal]
    exact least _ targetClosed _ (readback_compile_call goalMode)
  · intro least targetModel closed
    have sourceClosed : SourceClosed (rolesOf modes) source facts (pushModel modes targetModel) := by
      intro l θ premises found foundEq
      obtain ⟨head, body, _⟩ := compileRule?_components (compiled l)
      have paired := option_mapM_forall₂ (lowerCall? modes) (source l).body (target l).body body
      have proved : ∀ lit ∈ (target l).body,
          literalHolds (wrapAtom '' facts) targetModel (liftSubst θ) lit :=
        all_paired_imp paired
          (fun _ _ accepted => literalHolds_of_push accepted θ facts targetModel) premises
      have headEq := lowerAtom?_apply head θ
      have equal : found = _ :=
        BodyLiteral.intensional.inj (Option.some.inj (foundEq.symm.trans headEq))
      subst found
      exact closed l (liftSubst θ) proved
    exact least _ sourceClosed _ goalMode

/-- Two admitted mode plans observe the same authored answers. The codes of
the calls, the stored result columns, and the paths to saturation can differ.
No schedule or termination equivalence is required. -/
theorem admitted_mode_plans_agree (first second : Modes) (source : Labels → HornCertificate.Rule)
    (facts : Set RawAtom) (goal : RawAtom)
    (sameRoles : ∀ label a, a ∈ (source label).body →
      rolesOf first (HornUnification.encodeAtom a).symbol =
        rolesOf second (HornUnification.encodeAtom a).symbol)
    (left right : Labels → Clause (Signature Labels)) (leftRow rightRow : CallRow (Signature Labels))
    (leftOK : ∀ label, compileRule? first (source label) = some (left label))
    (rightOK : ∀ label, compileRule? second (source label) = some (right label))
    (firstGoal : lowerAtom? first goal = some (.intensional leftRow))
    (secondGoal : lowerAtom? second goal = some (.intensional rightRow)) :
    Least left (wrapAtom '' facts) (leftRow.input, leftRow.output) ↔
      Least right (wrapAtom '' facts) (rightRow.input, rightRow.output) :=
  (least_iff_source first source left leftOK facts goal leftRow firstGoal).trans
    ((sourceLeast_congr source facts goal sameRoles).trans
      (least_iff_source second source right rightOK facts goal rightRow secondGoal).symm)

namespace Controls

private def direction (first : Bool) : Modes := fun _ => some (.derived [first, !first])

private def edge : HornCertificate.Atom :=
  ⟨"link", HornCertificate.Terms.ofList [.atom "left", .atom "right"]⟩

private def edgeFact : Unit → HornCertificate.Rule := fun _ => ⟨"edge", edge, []⟩

private def edgeRow (known result : String) : CallRow (Signature Unit) :=
  ⟨pack (.call ⟨"link", 2⟩ 1) [Term.const (σ := Signature Unit) (.atom known)].get,
    pack (.outputs 1) [Term.const (σ := Signature Unit) (.atom result)].get⟩

private def edgeClause (known result : String) : Unit → Clause (Signature Unit) :=
  fun _ => ⟨edgeRow known result, []⟩

/-- The two plans demand different values, but witness the same source fact. -/
theorem opposite_modes_keep_the_fact :
    (edgeRow "left" "right").input ≠ (edgeRow "right" "left").input ∧
    Least (edgeClause "left" "right") ∅
      ((edgeRow "left" "right").input, (edgeRow "left" "right").output) ∧
    Least (edgeClause "right" "left") ∅
      ((edgeRow "right" "left").input, (edgeRow "right" "left").output) := by
  have first : Least (edgeClause "left" "right") ∅
      ((edgeRow "left" "right").input, (edgeRow "left" "right").output) := by
    intro model closed
    have found := closed () (Subst.id (Signature Unit)) (by simp [edgeClause])
    simpa only [edgeClause, CallRow.instantiate, Subst.applyTerm_id] using found
  have agreement := admitted_mode_plans_agree (direction true) (direction false)
    edgeFact ∅ (HornUnification.encodeAtom edge) (by simp [edgeFact])
    (edgeClause "left" "right") (edgeClause "right" "left")
    (edgeRow "left" "right") (edgeRow "right" "left")
    (fun _ => rfl) (fun _ => rfl) rfl rfl
  simp only [Set.image_empty] at agreement
  exact ⟨by decide +kernel, first, agreement.mp first⟩

private def supplied : HornCertificate.Atom := ⟨"supplied", .nil⟩
private def conclusion : HornCertificate.Atom := ⟨"conclusion", .nil⟩
private def usesSupplied : Unit → HornCertificate.Rule :=
  fun _ => ⟨"use", conclusion, [supplied]⟩

private def suppliedFacts : Set RawAtom := {HornUnification.encodeAtom supplied}

/-- Changing who supplies a relation is a semantic change, unlike changing
which columns a compiler consumes as inputs. -/
theorem provider_role_can_change_answers :
    SourceLeast (fun _ => some .external) usesSupplied suppliedFacts
      (HornUnification.encodeAtom conclusion) ∧
    ¬ SourceLeast (fun _ => some .derived) usesSupplied suppliedFacts
      (HornUnification.encodeAtom conclusion) := by
  constructor
  · intro model closed
    have derived := closed () (Subst.id HornUnification.signature) (by
      intro atom member
      have same : atom = supplied := List.mem_singleton.mp member
      subst atom
      simp [sourceHolds, suppliedFacts, Subst.applyAtom_id])
    simpa only [usesSupplied, Subst.applyAtom_id] using derived
  · intro least
    apply least ∅
    intro label θ premises
    exact premises supplied (by simp [usesSupplied])

private def exampleModes : Modes := fun symbol =>
  if symbol.arity != 2 then none
  else if symbol.name == "different" then some .external
  else if symbol.name == "lookup" || symbol.name == "run" then some (.derived [true, false])
  else none

private def exampleAtom (name : String) : HornCertificate.Atom :=
  ⟨name, HornCertificate.Terms.ofList [.var 0, .var 1]⟩

private def exampleRule (body : List HornCertificate.Atom) : HornCertificate.Rule :=
  ⟨"guarded-lookup", exampleAtom "run", body⟩

/-- The same guard succeeds at load time after the read that binds its
operand and is refused before that read. -/
theorem guard_must_follow_binder :
    (compileRule? (Labels := Unit) exampleModes
      (exampleRule [exampleAtom "lookup", exampleAtom "different"])).isSome = true ∧
    (compileRule? (Labels := Unit) exampleModes
      (exampleRule [exampleAtom "different", exampleAtom "lookup"])).isSome = false := by
  decide +kernel

end Controls

#print axioms project_wrap
#print axioms wrap_ground_iff
#print axioms wrap_atom_ground_iff
#print axioms wrap_apply
#print axioms project_apply_wrap
#print axioms lowerAtom?_apply
#print axioms readback_instantiated_call
#print axioms readback_compile_call
#print axioms sourceLeast_congr
#print axioms least_iff_source
#print axioms admitted_mode_plans_agree
#print axioms Controls.opposite_modes_keep_the_fact
#print axioms Controls.provider_role_can_change_answers
#print axioms Controls.guard_must_follow_binder

end Mettapedia.GSLT.Compilation.CanonicalHornSemantics
