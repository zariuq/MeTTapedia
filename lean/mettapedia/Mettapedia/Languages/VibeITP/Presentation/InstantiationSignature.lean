import Mettapedia.Languages.VibeITP.Presentation.InstantiationCorrespondence

/-!
# Signature snapshots for postorder instantiation

Instantiation can inspect the source, the replacement and recursively produced
arguments. Successful operations preserve the union of their input heads. A
finite snapshot storing the source and replacement heads, together with the
instantiated symbol's declaration, therefore suffices for every raw query.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation

open ComputationalData ComputationalShift ComputationalSubstitution
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def HeadsWithin (heads : List Spec.SymId) (term : Spec.Term) : Prop :=
  ∀ symbol ∈ termHeads term, symbol ∈ heads

def ListHeadsWithin (heads : List Spec.SymId) (terms : List Spec.Term) : Prop :=
  ∀ symbol ∈ termHeadsList terms, symbol ∈ heads

theorem HeadsWithin.app_head {heads : List Spec.SymId} {symbol : Spec.SymId} {terms : List Spec.Term}
    (known : HeadsWithin heads (.app symbol terms)) : symbol ∈ heads :=
  known symbol (List.mem_cons_self ..)

theorem HeadsWithin.app_args {heads : List Spec.SymId} {symbol : Spec.SymId} {terms : List Spec.Term}
    (known : HeadsWithin heads (.app symbol terms)) : ListHeadsWithin heads terms :=
  fun next used => known next (List.mem_cons_of_mem _ used)

theorem HeadsWithin.app {heads : List Spec.SymId} {symbol : Spec.SymId} {terms : List Spec.Term}
    (known : symbol ∈ heads) (arguments : ListHeadsWithin heads terms) : HeadsWithin heads (.app symbol terms) := by
  intro next used
  rcases List.mem_cons.mp used with same | child
  · exact same ▸ known
  · exact arguments next child

theorem ListHeadsWithin.cons_head {heads : List Spec.SymId} {first : Spec.Term} {rest : List Spec.Term}
    (known : ListHeadsWithin heads (first :: rest)) : HeadsWithin heads first :=
  fun symbol used => known symbol (List.mem_append_left _ used)

theorem ListHeadsWithin.cons_tail {heads : List Spec.SymId} {first : Spec.Term} {rest : List Spec.Term}
    (known : ListHeadsWithin heads (first :: rest)) : ListHeadsWithin heads rest :=
  fun symbol used => known symbol (List.mem_append_right _ used)

theorem ListHeadsWithin.cons {heads : List Spec.SymId} {first : Spec.Term} {rest : List Spec.Term}
    (head : HeadsWithin heads first) (tail : ListHeadsWithin heads rest) : ListHeadsWithin heads (first :: rest) := by
  intro symbol used
  rcases List.mem_append.mp used with first | rest
  · exact head symbol first
  · exact tail symbol rest

theorem ListHeadsWithin.getD {heads : List Spec.SymId} (terms : List Spec.Term)
    (known : ListHeadsWithin heads terms) (index : Nat) : HeadsWithin heads (terms.getD index (.bvar 0)) := by
  induction terms generalizing index with
  | nil => intro symbol used; cases used
  | cons first rest ih =>
      cases index with
      | zero => exact known.cons_head
      | succ index => exact ih known.cons_tail index

mutual

theorem shift_heads (signature : Spec.Sig) (amount cutoff : Nat) (term result : Spec.Term)
    (heads : List Spec.SymId) (known : HeadsWithin heads term)
    (success : Spec.shift signature amount cutoff term = some result) : HeadsWithin heads result := by
  cases term with
  | bvar index =>
      simp only [Spec.shift] at success
      split at success
      · cases success; exact known
      · split at success
        · cases success; intro symbol used; cases used
        · cases success
  | lit bytes => cases success; exact known
  | app symbol terms =>
      simp only [Spec.shift, shiftArgs_eq, List.drop_zero] at success
      split at success
      · cases success; exact known
      · cases children : shiftList signature amount cutoff (bindersOf signature symbol) terms with
        | none => simp only [children, Option.map_none] at success; cases success
        | some terms' =>
            simp only [children, Option.map_some, Option.some.injEq] at success
            subst result
            exact HeadsWithin.app known.app_head
              (shiftList_heads signature amount cutoff _ terms terms' heads known.app_args children)

theorem shiftList_heads (signature : Spec.Sig) (amount cutoff : Nat) (binders : List Nat)
    (terms results : List Spec.Term) (heads : List Spec.SymId) (known : ListHeadsWithin heads terms)
    (success : shiftList signature amount cutoff binders terms = some results) : ListHeadsWithin heads results := by
  cases terms with
  | nil => cases success; exact known
  | cons first rest =>
      simp only [shiftList] at success
      split at success
      · cases head : Spec.shift signature amount (cutoff + binders.headD 0) first with
        | none => simp only [head] at success; cases success
        | some first' =>
            cases tail : shiftList signature amount cutoff binders.tail rest with
            | none => simp only [head, tail] at success; cases success
            | some rest' =>
                simp only [head, tail, Option.some.injEq] at success
                subst results
                exact ListHeadsWithin.cons
                  (shift_heads signature amount _ first first' heads known.cons_head head)
                  (shiftList_heads signature amount cutoff binders.tail rest rest' heads known.cons_tail tail)
      · cases success

end

mutual

theorem substGo_heads (signature : Spec.Sig) (count : Nat) (images : List Spec.Term) (offset : Nat)
    (term result : Spec.Term) (heads : List Spec.SymId)
    (imagesKnown : ListHeadsWithin heads images) (known : HeadsWithin heads term)
    (success : Spec.substGo signature count images offset term = some result) : HeadsWithin heads result := by
  cases term with
  | bvar index =>
      simp only [Spec.substGo] at success
      split at success
      · cases success; exact known
      · split at success
        · exact shift_heads signature offset 0 _ result heads (imagesKnown.getD images _) success
        · split at success
          · cases success; intro symbol used; cases used
          · cases success
  | lit bytes => cases success; exact known
  | app symbol terms =>
      simp only [Spec.substGo, substGoArgs_eq, List.drop_zero] at success
      split at success
      · cases success; exact known
      · cases children : substList signature count images offset (bindersOf signature symbol) terms with
        | none => simp only [children, Option.map_none] at success; cases success
        | some terms' =>
            simp only [children, Option.map_some, Option.some.injEq] at success
            subst result
            exact HeadsWithin.app known.app_head
              (substList_heads signature count images offset _ terms terms' heads imagesKnown known.app_args children)

theorem substList_heads (signature : Spec.Sig) (count : Nat) (images : List Spec.Term) (offset : Nat)
    (binders : List Nat) (terms results : List Spec.Term) (heads : List Spec.SymId)
    (imagesKnown : ListHeadsWithin heads images) (known : ListHeadsWithin heads terms)
    (success : substList signature count images offset binders terms = some results) : ListHeadsWithin heads results := by
  cases terms with
  | nil => cases success; exact known
  | cons first rest =>
      simp only [substList] at success
      split at success
      · cases head : Spec.substGo signature count images (offset + binders.headD 0) first with
        | none => simp only [head] at success; cases success
        | some first' =>
            cases tail : substList signature count images offset binders.tail rest with
            | none => simp only [head, tail] at success; cases success
            | some rest' =>
                simp only [head, tail, Option.some.injEq] at success
                subst results
                exact ListHeadsWithin.cons
                  (substGo_heads signature count images _ first first' heads imagesKnown known.cons_head head)
                  (substList_heads signature count images offset binders.tail rest rest' heads imagesKnown known.cons_tail tail)
      · cases success

end

theorem substitution_heads (signature : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (term result : Spec.Term) (offset : Nat) (heads : List Spec.SymId)
    (imagesKnown : ListHeadsWithin heads images) (known : HeadsWithin heads term)
    (success : Spec.substBVars signature count images term offset = some result) : HeadsWithin heads result := by
  simp only [Spec.substBVars] at success
  split at success
  · cases success; exact known
  · exact substGo_heads signature count images offset term result heads imagesKnown known success

mutual

theorem instGo_heads (signature : Spec.Sig) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (term result : Spec.Term) (heads : List Spec.SymId)
    (valueKnown : HeadsWithin heads value) (known : HeadsWithin heads term)
    (success : Spec.instGo signature F arity value offset term = some result) : HeadsWithin heads result := by
  cases term with
  | bvar index => cases success; exact known
  | lit bytes => cases success; exact known
  | app symbol terms =>
      simp only [Spec.instGo, instArgs_eq, List.drop_zero] at success
      split at success
      · cases success; exact known
      · cases children : instList signature F arity value offset (bindersOf signature symbol) terms with
        | none => simp only [children] at success; cases success
        | some terms' =>
            simp only [children] at success
            have processed := instList_heads signature F arity value offset _ terms terms' heads
              valueKnown known.app_args children
            split at success
            · cases shifted : Spec.shift signature offset arity value with
              | none => simp only [shifted] at success; cases success
              | some value' =>
                  simp only [shifted] at success
                  exact substitution_heads signature arity terms' value' result 0 heads processed
                    (shift_heads signature offset arity value value' heads valueKnown shifted) success
            · cases success; exact HeadsWithin.app known.app_head processed

theorem instList_heads (signature : Spec.Sig) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (binders : List Nat) (terms results : List Spec.Term) (heads : List Spec.SymId)
    (valueKnown : HeadsWithin heads value) (known : ListHeadsWithin heads terms)
    (success : instList signature F arity value offset binders terms = some results) : ListHeadsWithin heads results := by
  cases terms with
  | nil => cases success; exact known
  | cons first rest =>
      simp only [instList] at success
      split at success
      · cases head : Spec.instGo signature F arity value (offset + binders.headD 0) first with
        | none => simp only [head] at success; cases success
        | some first' =>
            cases tail : instList signature F arity value offset binders.tail rest with
            | none => simp only [head, tail] at success; cases success
            | some rest' =>
                simp only [head, tail, Option.some.injEq] at success
                subst results
                exact ListHeadsWithin.cons
                  (instGo_heads signature F arity value _ first first' heads valueKnown known.cons_head head)
                  (instList_heads signature F arity value offset binders.tail rest rest' heads valueKnown known.cons_tail tail)
      · cases success

end

def InfoAgree (source target : Spec.Sig) (heads : List Spec.SymId) : Prop :=
  ∀ symbol ∈ heads, source symbol = target symbol

theorem InfoAgree.head {source target : Spec.Sig} {symbol : Spec.SymId} {heads : List Spec.SymId}
    (agree : InfoAgree source target (symbol :: heads)) : source symbol = target symbol :=
  agree symbol (List.mem_cons_self ..)

theorem InfoAgree.tail {source target : Spec.Sig} {symbol : Spec.SymId} {heads : List Spec.SymId}
    (agree : InfoAgree source target (symbol :: heads)) : InfoAgree source target heads :=
  fun next used => agree next (List.mem_cons_of_mem _ used)

theorem InfoAgree.left {source target : Spec.Sig} {left right : List Spec.SymId}
    (agree : InfoAgree source target (left ++ right)) : InfoAgree source target left :=
  fun symbol used => agree symbol (List.mem_append_left _ used)

theorem InfoAgree.right {source target : Spec.Sig} {left right : List Spec.SymId}
    (agree : InfoAgree source target (left ++ right)) : InfoAgree source target right :=
  fun symbol used => agree symbol (List.mem_append_right _ used)

theorem InfoAgree.append {source target : Spec.Sig} {left right : List Spec.SymId}
    (first : InfoAgree source target left) (second : InfoAgree source target right) :
    InfoAgree source target (left ++ right) := by
  intro symbol used
  rcases List.mem_append.mp used with firstHead | secondHead
  · exact first symbol firstHead
  · exact second symbol secondHead

theorem InfoAgree.binders {source target : Spec.Sig} {heads : List Spec.SymId}
    (agree : InfoAgree source target heads) : ComputationalShift.BindersAgree source target heads := by
  intro symbol used
  unfold bindersOf
  rw [agree symbol used]

theorem InfoAgree.restrict {source target : Spec.Sig} {heads : List Spec.SymId}
    (agree : InfoAgree source target heads) {term : Spec.Term} (known : HeadsWithin heads term) :
    InfoAgree source target (termHeads term) := fun symbol used => agree symbol (known symbol used)

theorem InfoAgree.restrictList {source target : Spec.Sig} {heads : List Spec.SymId}
    (agree : InfoAgree source target heads) {terms : List Spec.Term} (known : ListHeadsWithin heads terms) :
    InfoAgree source target (termHeadsList terms) := fun symbol used => agree symbol (known symbol used)

theorem isFvar_on_info (source target : Spec.Sig) (symbol : Spec.SymId)
    (agree : source symbol = target symbol) : Spec.isFvarSym source symbol = Spec.isFvarSym target symbol := by
  unfold Spec.isFvarSym
  rw [agree]

mutual

theorem hasFvar_on_heads (source target : Spec.Sig) (term : Spec.Term)
    (agree : InfoAgree source target (termHeads term)) : Spec.hasFvar source term = Spec.hasFvar target term := by
  cases term with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol terms =>
      rw [Spec.hasFvar, Spec.hasFvar, isFvar_on_info source target symbol agree.head,
        hasFvarList_on_heads source target terms agree.tail]

theorem hasFvarList_on_heads (source target : Spec.Sig) (terms : List Spec.Term)
    (agree : InfoAgree source target (termHeadsList terms)) :
    Spec.hasFvarList source terms = Spec.hasFvarList target terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      rw [Spec.hasFvarList, Spec.hasFvarList, hasFvar_on_heads source target first agree.left,
        hasFvarList_on_heads source target rest agree.right]

end

mutual

theorem instGo_on_heads (source target : Spec.Sig) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (term : Spec.Term) (valueAgree : InfoAgree source target (termHeads value))
    (agree : InfoAgree source target (termHeads term)) :
    Spec.instGo source F arity value offset term = Spec.instGo target F arity value offset term := by
  cases term with
  | bvar index => rfl
  | lit bytes => rfl
  | app symbol terms =>
      rw [Spec.instGo, Spec.instGo, hasFvar_on_heads source target (.app symbol terms) agree]
      split
      · rfl
      · rw [instArgs_eq, instArgs_eq, List.drop_zero, List.drop_zero, agree.binders.head,
          instList_on_heads source target F arity value offset _ terms valueAgree agree.tail]
        cases children : instList target F arity value offset (bindersOf target symbol) terms with
        | none => rfl
        | some terms' =>
            dsimp only
            have processed : ListHeadsWithin (termHeadsList terms ++ termHeads value) terms' :=
              instList_heads target F arity value offset _ terms terms' _
                (fun next used => List.mem_append_right _ used)
                (fun next used => List.mem_append_left _ used) children
            have processedAgree := (InfoAgree.append agree.tail valueAgree).restrictList processed
            split
            · rw [shift_on_heads source target offset arity value valueAgree.binders]
              cases shifted : Spec.shift target offset arity value with
              | none => rfl
              | some value' =>
                  have replacementKnown := shift_heads target offset arity value value' _ (fun _ used => used) shifted
                  exact substitution_on_heads source target arity terms' value' 0 processedAgree.binders
                    (valueAgree.restrict replacementKnown).binders
            · rfl

theorem instList_on_heads (source target : Spec.Sig) (F : Spec.SymId) (arity : Nat) (value : Spec.Term)
    (offset : Nat) (binders : List Nat) (terms : List Spec.Term)
    (valueAgree : InfoAgree source target (termHeads value))
    (agree : InfoAgree source target (termHeadsList terms)) :
    instList source F arity value offset binders terms = instList target F arity value offset binders terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      rw [instList, instList]
      split
      · rw [instGo_on_heads source target F arity value (offset + binders.headD 0) first valueAgree agree.left,
          instList_on_heads source target F arity value offset binders.tail rest valueAgree agree.right]
      · rfl

end

theorem instantiate_on_heads (source target : Spec.Sig) (F : Spec.SymId) (value statement : Spec.Term)
    (declaration : source F = target F) (valueAgree : InfoAgree source target (termHeads value))
    (agree : InfoAgree source target (termHeads statement)) :
    Spec.instantiateStatement source F value statement = Spec.instantiateStatement target F value statement := by
  rw [Spec.instantiateStatement, Spec.instantiateStatement, declaration]
  cases declared : target F with
  | none => rfl
  | some info =>
      dsimp only
      rw [depth_on_heads source target value valueAgree.binders]
      split
      · rw [instGo_on_heads source target F info.arity value 0 statement valueAgree agree]
        cases computed : Spec.instGo target F info.arity value 0 statement with
        | none => rfl
        | some result =>
            have known := instGo_heads target F info.arity value 0 statement result
              (termHeads statement ++ termHeads value)
              (fun next used => List.mem_append_right _ used)
              (fun next used => List.mem_append_left _ used) computed
            dsimp only
            rw [depth_on_heads source target result ((InfoAgree.append agree valueAgree).restrict known).binders]
      · rfl

def instantiationSnapshot (signature : Spec.Sig) (F : Spec.SymId) (value statement : Spec.Term) : SignatureTable :=
  tableFor signature ((termHeads statement ++ termHeads value) ++ [F])

theorem instantiationSnapshot_info (signature : Spec.Sig) (F : Spec.SymId) (value statement : Spec.Term) :
    InfoAgree (signatureOf (instantiationSnapshot signature F value statement)) signature
      ((termHeads statement ++ termHeads value) ++ [F]) := by
  intro symbol used
  unfold instantiationSnapshot
  rw [tableFor_lookup signature _ symbol, if_pos used]

theorem snapshot_instGo (signature : Spec.Sig) (F : Spec.SymId) (arity : Nat) (value statement : Spec.Term)
    (offset : Nat) :
    Spec.instGo (signatureOf (instantiationSnapshot signature F value statement)) F arity value offset statement =
      Spec.instGo signature F arity value offset statement :=
  instGo_on_heads _ _ F arity value offset statement (instantiationSnapshot_info signature F value statement).left.right
    (instantiationSnapshot_info signature F value statement).left.left

theorem snapshot_instantiation (signature : Spec.Sig) (F : Spec.SymId) (value statement : Spec.Term) :
    Spec.instantiateStatement (signatureOf (instantiationSnapshot signature F value statement)) F value statement =
      Spec.instantiateStatement signature F value statement :=
  instantiate_on_heads _ _ F value statement
    ((instantiationSnapshot_info signature F value statement).right F (by simp))
    (instantiationSnapshot_info signature F value statement).left.right
    (instantiationSnapshot_info signature F value statement).left.left

theorem instGo_computes_for_signature (signature : Spec.Sig) (F : Spec.SymId) (arity : Nat)
    (value statement : Spec.Term) (offset : Nat) :
    Applies instantiationProgram computationalHost "vibe:inst-go"
      [encodeTable (instantiationSnapshot signature F value statement), encodeSymbol F, natural arity,
        encode value, natural offset, encode statement]
      (encodeResult (Spec.instGo signature F arity value offset statement)) := by
  rw [← snapshot_instGo signature F arity value statement offset]
  exact instGo_computes _ _ _ _ _ _

theorem instantiation_computes_for_signature (signature : Spec.Sig) (F : Spec.SymId)
    (value statement : Spec.Term) :
    Applies instantiationProgram computationalHost "vibe:instantiate"
      [encodeTable (instantiationSnapshot signature F value statement), encodeSymbol F, encode value, encode statement]
      (encodeResult (Spec.instantiateStatement signature F value statement)) := by
  rw [← snapshot_instantiation signature F value statement]
  exact instantiation_computes _ _ _ _

theorem instantiation_signature_result_exact (signature : Spec.Sig) (F : Spec.SymId)
    (value statement : Spec.Term) (result : Term) :
    Applies instantiationProgram computationalHost "vibe:instantiate"
      [encodeTable (instantiationSnapshot signature F value statement), encodeSymbol F, encode value, encode statement] result ↔
      result = encodeResult (Spec.instantiateStatement signature F value statement) := by
  rw [instantiation_result_exact, snapshot_instantiation]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation
