import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Pack

/-!
# Inductive families: the laws of the pack

The laws each case of the logical relation must have, for the family pack: weak-head
normality of its normal forms, reflexivity, the two ends of an equality, symmetry,
transitivity, transfer between reducibly equal indices, renaming along a world, closure
under expansion, reflection of neutral terms, and escape. As for simple inductive types,
the facts about the packs of the value fields and of the index types are hypotheses, so
this module does not depend on how those packs arise.

What families add to simple inductive types is that recursive fields sit at indices
computed from the other fields. Two reducibly equal constructor forms compare their
recursive fields at the left-hand indices, so symmetry, transitivity and the ends of an
equality move a reducible term between reducibly equal indices. That needs two facts,
stated as hypotheses: the family's type respects reducible equality of indices
(`TypeCongr`), and reducibly equal fields give reducibly equal indices to the recursive
fields (`RecursiveExt`), the counterpart of the codomain law of dependent pair types.
Constructor forms are rigid (`FormsRigid`): weak-head normal, not neutral, and a normal
form is at most one constructor with one list of fields.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## Lists -/

/-- An element of the left list of a pointwise relation has a partner in the right list. -/
theorem forall₂_exists_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : α}, a ∈ l → ∃ b ∈ l', R a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons r rest, _, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, List.mem_cons_self .., r⟩
      · obtain ⟨b, hb, rb⟩ := forall₂_exists_of_mem rest h
        exact ⟨b, List.mem_cons_of_mem _ hb, rb⟩

/-! ## The hypotheses of the laws -/

section Hypotheses

variable (S) {n : Nat}

/-- A pack of a value field of one of the constructors. -/
def IsValuePack (F : FamilyAt Head n) (P : Pack Head n) : Prop :=
  ∃ c ∈ F.ctors, FieldAt.value P ∈ c.fields

/-- Constructor forms are rigid: weak-head normal, not neutral, and a normal form is at
most one constructor with one list of fields. -/
structure FormsRigid (F : FamilyAt Head n) : Prop where
  whnf : ∀ {c : CtorAt Head n} {nf : Tm Head n} {fs : List (Tm Head n)}, c ∈ F.ctors →
    c.form nf fs → Whnf S.R S.roles nf
  not_neutral : ∀ {c : CtorAt Head n} {nf : Tm Head n} {fs : List (Tm Head n)}, c ∈ F.ctors →
    c.form nf fs → ¬ Neutral S.roles nf
  unique : ∀ {c c' : CtorAt Head n} {nf : Tm Head n} {fs fs' : List (Tm Head n)},
    c ∈ F.ctors → c' ∈ F.ctors → c.form nf fs → c'.form nf fs' → c = c' ∧ fs = fs'

/-- The packs of the index types are symmetric and transitive. -/
structure IndexPER (F : FamilyAt Head n) : Prop where
  symm : ∀ {P : Pack Head n}, P ∈ F.indexPacks → ∀ {a b : Tm Head n}, P.eqTm a b → P.eqTm b a
  trans : ∀ {P : Pack Head n}, P ∈ F.indexPacks → ∀ {a b c : Tm Head n}, P.eqTm a b →
    P.eqTm b c → P.eqTm a c

/-- The family's type respects reducible equality of indices. -/
def TypeCongr (Γ : Ctx Head n) (F : FamilyAt Head n) : Prop :=
  ∀ {is is' : List (Tm Head n)}, IndexAgree F.indexPacks is is' →
    TypeEq S.R Γ (F.type is) (F.type is')

/-- Reducibly equal fields of a constructor give reducibly equal indices to each of its
recursive fields. -/
def RecursiveExt (Γ : Ctx Head n) (F : FamilyAt Head n) : Prop :=
  ∀ {c : CtorAt Head n} {fs fs' : List (Tm Head n)}, c ∈ F.ctors →
    FamEqFields S Γ F fs c.fields fs fs' →
    ∀ {idx : List (Tm Head n) → List (Tm Head n)}, FieldAt.recursive idx ∈ c.fields →
      IndexAgree F.indexPacks (idx fs) (idx fs')

end Hypotheses

/-! ## Index agreement -/

section Agreement

variable {n : Nat}

theorem IndexAgree.length {Ps : List (Pack Head n)} {is js : List (Tm Head n)}
    (agree : IndexAgree Ps is js) : is.length = Ps.length ∧ js.length = Ps.length := by
  induction agree with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg (· + 1) ih.1, congrArg (· + 1) ih.2⟩

theorem IndexAgree.symm {Ps : List (Pack Head n)}
    (symm : ∀ {P : Pack Head n}, P ∈ Ps → ∀ {a b : Tm Head n}, P.eqTm a b → P.eqTm b a) :
    ∀ {is js : List (Tm Head n)}, IndexAgree Ps is js → IndexAgree Ps js is := by
  intro is js agree
  induction agree with
  | nil => exact .nil
  | @cons P Ps i j is js head _ ih =>
      exact .cons (symm (List.mem_cons_self ..) head)
        (ih fun {_} mem {_ _} h => symm (List.mem_cons_of_mem _ mem) h)

theorem IndexAgree.trans {Ps : List (Pack Head n)}
    (trans : ∀ {P : Pack Head n}, P ∈ Ps → ∀ {a b c : Tm Head n}, P.eqTm a b → P.eqTm b c →
      P.eqTm a c) :
    ∀ {is js ks : List (Tm Head n)}, IndexAgree Ps is js → IndexAgree Ps js ks →
      IndexAgree Ps is ks := by
  intro is js ks first
  induction first generalizing ks with
  | nil => intro second; cases second; exact .nil
  | @cons P Ps i j is js head _ ih =>
      intro second
      cases second with
      | cons head' tail' =>
          exact .cons (trans (List.mem_cons_self ..) head head')
            (ih (fun {_} mem {_ _ _} h h' => trans (List.mem_cons_of_mem _ mem) h h') tail')

/-- The left indices of an agreement agree with themselves. -/
theorem IndexAgree.left_refl {Ps : List (Pack Head n)}
    (symm : ∀ {P : Pack Head n}, P ∈ Ps → ∀ {a b : Tm Head n}, P.eqTm a b → P.eqTm b a)
    (trans : ∀ {P : Pack Head n}, P ∈ Ps → ∀ {a b c : Tm Head n}, P.eqTm a b → P.eqTm b c →
      P.eqTm a c) {is js : List (Tm Head n)} (agree : IndexAgree Ps is js) :
    IndexAgree Ps is is :=
  IndexAgree.trans trans agree (IndexAgree.symm symm agree)

theorem IndexAgree.rename {m : Nat} {ρ : Ren n m} :
    ∀ {Ps : List (Pack Head n)} {Ps' : List (Pack Head m)},
      List.Forall₂ (fun (P : Pack Head n) (P' : Pack Head m) => ∀ {a b : Tm Head n},
        P.eqTm a b → P'.eqTm (Presentation.rename ρ a) (Presentation.rename ρ b)) Ps Ps' →
      ∀ {is js : List (Tm Head n)}, IndexAgree Ps is js →
        IndexAgree Ps' (is.map (Presentation.rename ρ)) (js.map (Presentation.rename ρ)) := by
  intro Ps Ps' rel is js agree
  induction agree generalizing Ps' with
  | nil => cases rel; exact .nil
  | cons head _ ih =>
      cases rel with
      | cons r rest => exact .cons (r head) (ih rest)

end Agreement

/-! ## Weak-head normal forms -/

section Normal

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

theorem FamNf.whnf (rigid : FormsRigid S F) {is : List (Tm Head n)} {nf : Tm Head n}
    (normal : FamNf S Γ F is nf) : Whnf S.R S.roles nf := by
  cases normal with
  | ctor mem form _ _ => exact rigid.whnf mem form
  | neutral neutral _ => exact neutral.whnf S.shape

theorem FamEqNf.whnf (rigid : FormsRigid S F) {is : List (Tm Head n)} {nf nf' : Tm Head n}
    (normal : FamEqNf S Γ F is nf nf') : Whnf S.R S.roles nf ∧ Whnf S.R S.roles nf' := by
  cases normal with
  | ctor mem form form' _ _ _ => exact ⟨rigid.whnf mem form, rigid.whnf mem form'⟩
  | neutral neutral neutral' _ => exact ⟨neutral.whnf S.shape, neutral'.whnf S.shape⟩

end Normal

/-! ## Transfer between reducibly equal indices -/

section Transfer

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

theorem FamNf.transfer (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) {is is' : List (Tm Head n)}
    (agree : IndexAgree F.indexPacks is is') {nf : Tm Head n} :
    FamNf S Γ F is nf → FamNf S Γ F is' nf
  | .ctor mem form fields agreeT =>
      .ctor mem form fields (IndexAgree.trans per.trans (IndexAgree.symm per.symm agree) agreeT)
  | .neutral nNf conv => .neutral nNf (laws.convNe_conv conv (congr agree))

/-- Reducibility at reducibly equal indices agrees. -/
theorem FamRedTm.transfer (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) {is is' : List (Tm Head n)}
    (agree : IndexAgree F.indexPacks is is') {t : Tm Head n} :
    FamRedTm S Γ F is t → FamRedTm S Γ F is' t
  | .mk red conv normal =>
      .mk (red.conv (congr agree)) (laws.convTm_conv conv (congr agree))
        (FamNf.transfer laws per congr agree normal)

theorem FamEqNf.transfer (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) {is is' : List (Tm Head n)}
    (agree : IndexAgree F.indexPacks is is') {nf nf' : Tm Head n} :
    FamEqNf S Γ F is nf nf' → FamEqNf S Γ F is' nf nf'
  | .ctor mem form form' fields agreeT agreeT' =>
      .ctor mem form form' fields
        (IndexAgree.trans per.trans (IndexAgree.symm per.symm agree) agreeT)
        (IndexAgree.trans per.trans (IndexAgree.symm per.symm agree) agreeT')
  | .neutral nNf nNf' conv => .neutral nNf nNf' (laws.convNe_conv conv (congr agree))

/-- Reducible equality at reducibly equal indices agrees. -/
theorem FamEqTm.transfer (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) {is is' : List (Tm Head n)}
    (agree : IndexAgree F.indexPacks is is') {t t' : Tm Head n} :
    FamEqTm S Γ F is t t' → FamEqTm S Γ F is' t t'
  | .mk red red' conv normal =>
      .mk (red.conv (congr agree)) (red'.conv (congr agree)) (laws.convTm_conv conv (congr agree))
        (FamEqNf.transfer laws per congr agree normal)

end Transfer

/-! ## Reflexivity -/

section Reflexivity

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

mutual

theorem FamRedTm.refl
    (valueRefl : ∀ {P}, IsValuePack F P → ∀ {a}, P.redTm a → P.eqTm a a) :
    ∀ {is : List (Tm Head n)} {t : Tm Head n}, FamRedTm S Γ F is t → FamEqTm S Γ F is t t
  | _, _, .mk red conv normal => .mk red red conv (FamNf.refl valueRefl normal)

theorem FamNf.refl
    (valueRefl : ∀ {P}, IsValuePack F P → ∀ {a}, P.redTm a → P.eqTm a a) :
    ∀ {is : List (Tm Head n)} {nf : Tm Head n}, FamNf S Γ F is nf → FamEqNf S Γ F is nf nf
  | _, _, .ctor mem form fields agree =>
      .ctor mem form form (FamFields.refl valueRefl (fun h => ⟨_, mem, h⟩) fields) agree agree
  | _, _, .neutral neutral conv => .neutral neutral neutral conv

theorem FamFields.refl
    (valueRefl : ∀ {P}, IsValuePack F P → ∀ {a}, P.redTm a → P.eqTm a a) :
    ∀ {all : List (Tm Head n)} {fields : List (FieldAt Head n)} {args : List (Tm Head n)},
      (∀ {P}, FieldAt.value P ∈ fields → IsValuePack F P) →
      FamFields S Γ F all fields args → FamEqFields S Γ F all fields args args
  | _, _, _, _, .nil => .nil
  | _, _, _, sub, .value head tail =>
      .value (valueRefl (sub (List.mem_cons_self ..)) head)
        (FamFields.refl valueRefl (fun h => sub (List.mem_cons_of_mem _ h)) tail)
  | _, _, _, sub, .recursive head tail =>
      .recursive (FamRedTm.refl valueRefl head)
        (FamFields.refl valueRefl (fun h => sub (List.mem_cons_of_mem _ h)) tail)

end

end Reflexivity

/-! ## The two ends of an equality -/

section Ends

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

mutual

theorem FamEqTm.ends (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueEnds : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.redTm a ∧ P.redTm b) :
    ∀ {is : List (Tm Head n)} {t t' : Tm Head n}, FamEqTm S Γ F is t t' →
      FamRedTm S Γ F is t ∧ FamRedTm S Γ F is t'
  | _, _, _, .mk red red' conv normal =>
      have normals := FamEqNf.ends laws per congr recExt valueEnds normal
      ⟨.mk red (laws.convTm_trans conv (laws.convTm_symm conv)) normals.1,
        .mk red' (laws.convTm_trans (laws.convTm_symm conv) conv) normals.2⟩

theorem FamEqNf.ends (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueEnds : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.redTm a ∧ P.redTm b) :
    ∀ {is : List (Tm Head n)} {nf nf' : Tm Head n}, FamEqNf S Γ F is nf nf' →
      FamNf S Γ F is nf ∧ FamNf S Γ F is nf'
  | _, _, _, .ctor mem form form' fields agree agree' =>
      have args := FamEqFields.ends laws per congr recExt valueEnds (fun h => ⟨_, mem, h⟩)
        (fun h => recExt mem fields h) fields
      ⟨.ctor mem form args.1 agree, .ctor mem form' args.2 agree'⟩
  | _, _, _, .neutral neutral neutral' conv =>
      ⟨.neutral neutral (laws.convNe_trans conv (laws.convNe_symm conv)),
        .neutral neutral' (laws.convNe_trans (laws.convNe_symm conv) conv)⟩

theorem FamEqFields.ends (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueEnds : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.redTm a ∧ P.redTm b) :
    ∀ {all all' : List (Tm Head n)} {fields : List (FieldAt Head n)}
      {args args' : List (Tm Head n)},
      (∀ {P}, FieldAt.value P ∈ fields → IsValuePack F P) →
      (∀ {idx}, FieldAt.recursive idx ∈ fields → IndexAgree F.indexPacks (idx all) (idx all')) →
      FamEqFields S Γ F all fields args args' →
      FamFields S Γ F all fields args ∧ FamFields S Γ F all' fields args'
  | _, _, _, _, _, _, _, .nil => ⟨.nil, .nil⟩
  | _, _, _, _, _, sub, recSub, .value head tail =>
      have h := valueEnds (sub (List.mem_cons_self ..)) head
      have t := FamEqFields.ends laws per congr recExt valueEnds
        (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h)) tail
      ⟨.value h.1 t.1, .value h.2 t.2⟩
  | _, _, _, _, _, sub, recSub, .recursive head tail =>
      have h := FamEqTm.ends laws per congr recExt valueEnds head
      have t := FamEqFields.ends laws per congr recExt valueEnds
        (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h)) tail
      ⟨.recursive h.1 t.1,
        .recursive (FamRedTm.transfer laws per congr (recSub (List.mem_cons_self ..)) h.2) t.2⟩

end

end Ends

/-! ## Symmetry -/

section Symmetry

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

mutual

theorem FamEqTm.symm (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueSymm : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.eqTm b a) :
    ∀ {is : List (Tm Head n)} {t t' : Tm Head n}, FamEqTm S Γ F is t t' →
      FamEqTm S Γ F is t' t
  | _, _, _, .mk red red' conv normal =>
      .mk red' red (laws.convTm_symm conv) (FamEqNf.symm laws per congr recExt valueSymm normal)

theorem FamEqNf.symm (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueSymm : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.eqTm b a) :
    ∀ {is : List (Tm Head n)} {nf nf' : Tm Head n}, FamEqNf S Γ F is nf nf' →
      FamEqNf S Γ F is nf' nf
  | _, _, _, .ctor mem form form' fields agree agree' =>
      .ctor mem form' form
        (FamEqFields.symm laws per congr recExt valueSymm (fun h => ⟨_, mem, h⟩)
          (fun h => recExt mem fields h) fields) agree' agree
  | _, _, _, .neutral neutral neutral' conv => .neutral neutral' neutral (laws.convNe_symm conv)

theorem FamEqFields.symm (laws : S.E.Laws S.R S.roles) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueSymm : ∀ {P}, IsValuePack F P → ∀ {a b}, P.eqTm a b → P.eqTm b a) :
    ∀ {all all' : List (Tm Head n)} {fields : List (FieldAt Head n)}
      {args args' : List (Tm Head n)},
      (∀ {P}, FieldAt.value P ∈ fields → IsValuePack F P) →
      (∀ {idx}, FieldAt.recursive idx ∈ fields → IndexAgree F.indexPacks (idx all) (idx all')) →
      FamEqFields S Γ F all fields args args' → FamEqFields S Γ F all' fields args' args
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, sub, recSub, .value head tail =>
      .value (valueSymm (sub (List.mem_cons_self ..)) head)
        (FamEqFields.symm laws per congr recExt valueSymm
          (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h))
          tail)
  | _, _, _, _, _, sub, recSub, .recursive head tail =>
      .recursive
        (FamEqTm.transfer laws per congr (recSub (List.mem_cons_self ..))
          (FamEqTm.symm laws per congr recExt valueSymm head))
        (FamEqFields.symm laws per congr recExt valueSymm
          (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h))
          tail)

end

end Symmetry

/-! ## Transitivity -/

section Transitivity

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

mutual

theorem FamEqTm.trans (laws : S.E.Laws S.R S.roles) (rigid : FormsRigid S F) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueTrans : ∀ {P}, IsValuePack F P → ∀ {a b c}, P.eqTm a b → P.eqTm b c → P.eqTm a c) :
    ∀ {is : List (Tm Head n)} {t t' t'' : Tm Head n}, FamEqTm S Γ F is t t' →
      FamEqTm S Γ F is t' t'' → FamEqTm S Γ F is t t''
  | _, _, _, _, .mk red red' conv normal, .mk red₂ red₂' conv₂ normal₂ => by
      have same := WhRed.whnf_unique S.shape red'.red red₂.red (FamEqNf.whnf rigid normal).2
        (FamEqNf.whnf rigid normal₂).1
      exact .mk red red₂' (laws.convTm_trans conv (by rw [same]; exact conv₂))
        (FamEqNf.trans laws rigid per congr recExt valueTrans normal normal₂ same)

theorem FamEqNf.trans (laws : S.E.Laws S.R S.roles) (rigid : FormsRigid S F) (per : IndexPER F)
    (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueTrans : ∀ {P}, IsValuePack F P → ∀ {a b c}, P.eqTm a b → P.eqTm b c → P.eqTm a c) :
    ∀ {is : List (Tm Head n)} {a b b' c : Tm Head n}, FamEqNf S Γ F is a b →
      FamEqNf S Γ F is b' c → b = b' → FamEqNf S Γ F is a c
  | _, _, _, _, _, .ctor mem form form' fields agree _, .ctor mem₂ form₂ form₂' fields₂ _ agree₂',
      same => by
      subst same
      obtain ⟨rfl, rfl⟩ := rigid.unique mem mem₂ form' form₂
      exact .ctor mem form form₂'
        (FamEqFields.trans laws rigid per congr recExt valueTrans (fun h => ⟨_, mem, h⟩)
          (fun h => IndexAgree.symm per.symm (recExt mem fields h)) fields fields₂ rfl rfl)
        agree agree₂'
  | _, _, _, _, _, .ctor mem _ form' _ _ _, .neutral nNf _ _, same => by
      subst same
      exact absurd nNf (rigid.not_neutral mem form')
  | _, _, _, _, _, .neutral _ nNf' _, .ctor mem₂ form₂ _ _ _ _, same => by
      subst same
      exact absurd nNf' (rigid.not_neutral mem₂ form₂)
  | _, _, _, _, _, .neutral nNf _ conv, .neutral _ nNf₂' conv₂, same => by
      subst same
      exact .neutral nNf nNf₂' (laws.convNe_trans conv conv₂)

theorem FamEqFields.trans (laws : S.E.Laws S.R S.roles) (rigid : FormsRigid S F)
    (per : IndexPER F) (congr : TypeCongr S Γ F) (recExt : RecursiveExt S Γ F)
    (valueTrans : ∀ {P}, IsValuePack F P → ∀ {a b c}, P.eqTm a b → P.eqTm b c → P.eqTm a c) :
    ∀ {all all' : List (Tm Head n)} {fields fields' : List (FieldAt Head n)}
      {args args' args'' args''' : List (Tm Head n)},
      (∀ {P}, FieldAt.value P ∈ fields → IsValuePack F P) →
      (∀ {idx}, FieldAt.recursive idx ∈ fields →
        IndexAgree F.indexPacks (idx all') (idx all)) →
      FamEqFields S Γ F all fields args args' → FamEqFields S Γ F all' fields' args'' args''' →
      fields = fields' → args' = args'' → FamEqFields S Γ F all fields args args'''
  | _, _, _, _, _, _, _, _, _, _, .nil, .nil, _, _ => .nil
  | _, _, _, _, _, _, _, _, sub, recSub, .value head tail, .value head' tail', sameFields,
      sameArgs => by
      obtain ⟨sameField, restFields⟩ := List.cons.inj sameFields
      obtain ⟨sameHead, restArgs⟩ := List.cons.inj sameArgs
      cases sameField
      cases sameHead
      exact .value (valueTrans (sub (List.mem_cons_self ..)) head head')
        (FamEqFields.trans laws rigid per congr recExt valueTrans
          (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h))
          tail tail' restFields restArgs)
  | _, _, _, _, _, _, _, _, sub, recSub, .recursive head tail, .recursive head' tail',
      sameFields, sameArgs => by
      obtain ⟨sameField, restFields⟩ := List.cons.inj sameFields
      obtain ⟨sameHead, restArgs⟩ := List.cons.inj sameArgs
      cases sameField
      cases sameHead
      exact .recursive
        (FamEqTm.trans laws rigid per congr recExt valueTrans head
          (FamEqTm.transfer laws per congr (recSub (List.mem_cons_self ..)) head'))
        (FamEqFields.trans laws rigid per congr recExt valueTrans
          (fun h => sub (List.mem_cons_of_mem _ h)) (fun h => recSub (List.mem_cons_of_mem _ h))
          tail tail' restFields restArgs)
  | _, _, _, _, _, _, _, _, _, _, .nil, .value _ _, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, _, _, _, .nil, .recursive _ _, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, _, _, _, .value _ _, .nil, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, _, _, _, .value _ _, .recursive _ _, sameFields, _ =>
      nomatch sameFields
  | _, _, _, _, _, _, _, _, _, _, .recursive _ _, .nil, sameFields, _ => nomatch sameFields
  | _, _, _, _, _, _, _, _, _, _, .recursive _ _, .value _ _, sameFields, _ =>
      nomatch sameFields

end

end Transitivity

/-! ## Renaming along a world -/

section Rename

variable {n m : Nat}

/-- A field read in the target context that is the renaming of a field read in the source
context: the value packs contain the renamed reducible terms and equalities, and the
recursive indices commute with renaming. -/
inductive FieldAt.Renamed (ρ : Ren n m) : FieldAt Head n → FieldAt Head m → Prop where
  | value {P : Pack Head n} {P' : Pack Head m}
      (redTm : ∀ {a : Tm Head n}, P.redTm a → P'.redTm (Presentation.rename ρ a))
      (eqTm : ∀ {a b : Tm Head n}, P.eqTm a b →
        P'.eqTm (Presentation.rename ρ a) (Presentation.rename ρ b)) :
      FieldAt.Renamed ρ (.value P) (.value P')
  | recursive {idx : List (Tm Head n) → List (Tm Head n)}
      {idx' : List (Tm Head m) → List (Tm Head m)}
      (indices : ∀ fs : List (Tm Head n),
        (idx fs).map (Presentation.rename ρ) = idx' (fs.map (Presentation.rename ρ))) :
      FieldAt.Renamed ρ (.recursive idx) (.recursive idx')

/-- A constructor read in the target context that is the renaming of one read in the
source context. -/
structure CtorAt.Renamed (ρ : Ren n m) (c : CtorAt Head n) (c' : CtorAt Head m) : Prop where
  form : ∀ {nf : Tm Head n} {fs : List (Tm Head n)}, c.form nf fs →
    c'.form (Presentation.rename ρ nf) (fs.map (Presentation.rename ρ))
  fields : List.Forall₂ (FieldAt.Renamed ρ) c.fields c'.fields
  target : ∀ fs : List (Tm Head n),
    (c.target fs).map (Presentation.rename ρ) = c'.target (fs.map (Presentation.rename ρ))

/-- A family read in the target context that is the renaming of one read in the source
context. -/
structure FamilyAt.Renamed (F : FamilyAt Head n) (ρ : Ren n m) (F' : FamilyAt Head m) :
    Prop where
  type : ∀ is : List (Tm Head n),
    Presentation.rename ρ (F.type is) = F'.type (is.map (Presentation.rename ρ))
  ctors : List.Forall₂ (CtorAt.Renamed ρ) F.ctors F'.ctors
  indexPacks : List.Forall₂ (fun (P : Pack Head n) (P' : Pack Head m) => ∀ {a b : Tm Head n},
    P.eqTm a b → P'.eqTm (Presentation.rename ρ a) (Presentation.rename ρ b))
    F.indexPacks F'.indexPacks
  sameFormer : ∀ {X : Tm Head n} {is' : List (Tm Head n)}, F.sameFormer X is' →
    F'.sameFormer (Presentation.rename ρ X) (is'.map (Presentation.rename ρ))

variable {Γ : Ctx Head n} {Δ : Ctx Head m} {ρ : Ren n m} {F : FamilyAt Head n}
  {F' : FamilyAt Head m}

mutual

theorem FamRedTm.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {is : List (Tm Head n)} {t : Tm Head n}, FamRedTm S Γ F is t →
      FamRedTm S Δ F' (is.map (Presentation.rename ρ)) (Presentation.rename ρ t)
  | is, _, .mk red conv normal => by
      have r := red.rename w.1
      have c := laws.convTm_rename w.1 w.2 conv
      rw [renamed.type is] at r c
      exact .mk r c (FamNf.rename laws w renamed normal)

theorem FamNf.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {is : List (Tm Head n)} {nf : Tm Head n}, FamNf S Γ F is nf →
      FamNf S Δ F' (is.map (Presentation.rename ρ)) (Presentation.rename ρ nf)
  | _, _, .ctor (fs := fs) mem form fields agree => by
      obtain ⟨c', mem', rc⟩ := forall₂_exists_of_mem renamed.ctors mem
      have agree' := IndexAgree.rename renamed.indexPacks agree
      rw [rc.target fs] at agree'
      exact .ctor mem' (rc.form form) (FamFields.rename laws w renamed rc.fields fields) agree'
  | is, _, .neutral neutral conv => by
      have c := laws.convNe_rename w.1 w.2 conv
      rw [renamed.type is] at c
      exact .neutral (neutral.rename ρ) c

theorem FamFields.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {all : List (Tm Head n)} {fields : List (FieldAt Head n)}
      {fields' : List (FieldAt Head m)} {args : List (Tm Head n)},
      List.Forall₂ (FieldAt.Renamed ρ) fields fields' →
      FamFields S Γ F all fields args →
      FamFields S Δ F' (all.map (Presentation.rename ρ)) fields'
        (args.map (Presentation.rename ρ))
  | _, _, _, _, rel, .nil => by cases rel; exact .nil
  | _, _, _, _, rel, .value head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | value redTm _ => exact .value (redTm head) (FamFields.rename laws w renamed rest tail)
  | all, _, _, _, rel, .recursive head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | recursive indices =>
              have h := FamRedTm.rename laws w renamed head
              rw [indices all] at h
              exact .recursive h (FamFields.rename laws w renamed rest tail)

end

mutual

theorem FamEqTm.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {is : List (Tm Head n)} {t t' : Tm Head n}, FamEqTm S Γ F is t t' →
      FamEqTm S Δ F' (is.map (Presentation.rename ρ)) (Presentation.rename ρ t)
        (Presentation.rename ρ t')
  | is, _, _, .mk red red' conv normal => by
      have r := red.rename w.1
      have r' := red'.rename w.1
      have c := laws.convTm_rename w.1 w.2 conv
      rw [renamed.type is] at r r' c
      exact .mk r r' c (FamEqNf.rename laws w renamed normal)

theorem FamEqNf.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {is : List (Tm Head n)} {nf nf' : Tm Head n}, FamEqNf S Γ F is nf nf' →
      FamEqNf S Δ F' (is.map (Presentation.rename ρ)) (Presentation.rename ρ nf)
        (Presentation.rename ρ nf')
  | _, _, _, .ctor (fs := fs) (fs' := fs') mem form form' fields agree agree' => by
      obtain ⟨c', mem', rc⟩ := forall₂_exists_of_mem renamed.ctors mem
      have a := IndexAgree.rename renamed.indexPacks agree
      have a' := IndexAgree.rename renamed.indexPacks agree'
      rw [rc.target fs] at a
      rw [rc.target fs'] at a'
      exact .ctor mem' (rc.form form) (rc.form form')
        (FamEqFields.rename laws w renamed rc.fields fields) a a'
  | is, _, _, .neutral neutral neutral' conv => by
      have c := laws.convNe_rename w.1 w.2 conv
      rw [renamed.type is] at c
      exact .neutral (neutral.rename ρ) (neutral'.rename ρ) c

theorem FamEqFields.rename (laws : S.E.Laws S.R S.roles) (w : World S Γ Δ ρ)
    (renamed : F.Renamed ρ F') :
    ∀ {all : List (Tm Head n)} {fields : List (FieldAt Head n)}
      {fields' : List (FieldAt Head m)} {args args' : List (Tm Head n)},
      List.Forall₂ (FieldAt.Renamed ρ) fields fields' →
      FamEqFields S Γ F all fields args args' →
      FamEqFields S Δ F' (all.map (Presentation.rename ρ)) fields'
        (args.map (Presentation.rename ρ)) (args'.map (Presentation.rename ρ))
  | _, _, _, _, _, rel, .nil => by cases rel; exact .nil
  | _, _, _, _, _, rel, .value head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | value _ eqTm => exact .value (eqTm head) (FamEqFields.rename laws w renamed rest tail)
  | all, _, _, _, _, rel, .recursive head tail => by
      cases rel with
      | cons r rest =>
          cases r with
          | recursive indices =>
              have h := FamEqTm.rename laws w renamed head
              rw [indices all] at h
              exact .recursive h (FamEqFields.rename laws w renamed rest tail)

end

end Rename

/-! ## Expansion, reflection and escape -/

section Closure

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

theorem FamRedTm.expand {is : List (Tm Head n)} {t u : Tm Head n}
    (red : RedTm S.R S.roles Γ t u (F.type is)) (reducible : FamRedTm S Γ F is u) :
    FamRedTm S Γ F is t := by
  obtain ⟨red', conv, normal⟩ := reducible
  exact .mk (red.trans red') conv normal

theorem FamEqTm.expand {is : List (Tm Head n)} {t t' u u' : Tm Head n}
    (redT : RedTm S.R S.roles Γ t t' (F.type is)) (redU : RedTm S.R S.roles Γ u u' (F.type is))
    (equal : FamEqTm S Γ F is t' u') : FamEqTm S Γ F is t u := by
  obtain ⟨r, r', conv, normal⟩ := equal
  exact .mk (redT.trans r) (redU.trans r') conv normal

/-- Expansion of a reducible term: the source is reducible and reducibly equal to the
target. -/
theorem FamRedTm.expand_eq
    (valueRefl : ∀ {P}, IsValuePack F P → ∀ {a}, P.redTm a → P.eqTm a a)
    {is : List (Tm Head n)} {t u : Tm Head n}
    (red : RedTm S.R S.roles Γ t u (F.type is)) (reducible : FamRedTm S Γ F is u) :
    FamRedTm S Γ F is t ∧ FamEqTm S Γ F is t u :=
  ⟨FamRedTm.expand red reducible,
    FamEqTm.expand red (RedTm.refl red.target) (FamRedTm.refl valueRefl reducible)⟩

/-- A typed neutral term convertible to itself is reducible. -/
theorem FamRedTm.of_neutral (laws : S.E.Laws S.R S.roles) {is : List (Tm Head n)}
    {t : Tm Head n} (neutral : Neutral S.roles t) (typing : Typed S.R Γ t (F.type is))
    (refl : S.E.convNe Γ t t (F.type is)) : FamRedTm S Γ F is t :=
  .mk (RedTm.refl typing) (laws.convTm_of_convNe (.inl neutral) (.inl neutral) refl)
    (.neutral neutral refl)

/-- Two typed convertible neutral terms are reducibly equal. -/
theorem FamEqTm.of_neutral (laws : S.E.Laws S.R S.roles) {is : List (Tm Head n)}
    {t t' : Tm Head n} (neutral : Neutral S.roles t) (neutral' : Neutral S.roles t')
    (typing : Typed S.R Γ t (F.type is)) (typing' : Typed S.R Γ t' (F.type is))
    (conv : S.E.convNe Γ t t' (F.type is)) : FamEqTm S Γ F is t t' :=
  .mk (RedTm.refl typing) (RedTm.refl typing')
    (laws.convTm_of_convNe (.inl neutral) (.inl neutral') conv) (.neutral neutral neutral' conv)

/-- A reducible term is typed and convertible to itself. -/
theorem FamRedTm.escape (laws : S.E.Laws S.R S.roles) {is : List (Tm Head n)} {t : Tm Head n} :
    FamRedTm S Γ F is t → Typed S.R Γ t (F.type is) ∧ S.E.convTm Γ t t (F.type is)
  | .mk red conv _ => ⟨red.source, laws.convTm_expand red red conv⟩

/-- Reducibly equal terms are convertible. -/
theorem FamEqTm.escape (laws : S.E.Laws S.R S.roles) {is : List (Tm Head n)}
    {t t' : Tm Head n} : FamEqTm S Γ F is t t' → S.E.convTm Γ t t' (F.type is)
  | .mk red red' conv _ => laws.convTm_expand red red' conv

end Closure

/-! ## The pack -/

section PackLaws

variable {n : Nat} {Γ : Ctx Head n} {F : FamilyAt Head n}

/-- The family's type is reducibly equal to itself. -/
theorem familyPack_eqTy_refl {A : Tm Head n} {is : List (Tm Head n)}
    (red : RedTy S.R S.roles Γ A (F.type is)) (same : F.sameFormer (F.type is) is)
    (conv : S.E.convTy Γ (F.type is) (F.type is)) (agree : IndexAgree F.indexPacks is is) :
    (familyPack S Γ F is).eqTy A :=
  ⟨_, is, red, same, conv, agree⟩

/-- Reducible type equality is closed under expansion of the other type. -/
theorem familyPack_eqTy_expand {is : List (Tm Head n)} {B B' : Tm Head n}
    (red : RedTy S.R S.roles Γ B B') (equal : (familyPack S Γ F is).eqTy B') :
    (familyPack S Γ F is).eqTy B := by
  obtain ⟨X, is', redB, same, conv, agree⟩ := equal
  exact ⟨X, is', red.trans S.levels redB, same, conv, agree⟩

/-- Reducibly equal types are convertible. -/
theorem familyPack_eqTy_escape (laws : S.E.Laws S.R S.roles) {is : List (Tm Head n)}
    {A B : Tm Head n} (red : RedTy S.R S.roles Γ A (F.type is))
    (equal : (familyPack S Γ F is).eqTy B) : S.E.convTy Γ A B := by
  obtain ⟨X, is', redB, _, conv, _⟩ := equal
  exact laws.convTy_expand red redB conv

/-- Every relation of the pack is closed under renaming along a world. -/
theorem familyPack_rename (laws : S.E.Laws S.R S.roles) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} {F' : FamilyAt Head m} (w : World S Γ Δ ρ) (renamed : F.Renamed ρ F')
    {is : List (Tm Head n)} :
    (∀ {B}, (familyPack S Γ F is).eqTy B →
      (familyPack S Δ F' (is.map (Presentation.rename ρ))).eqTy (Presentation.rename ρ B)) ∧
    (∀ {t}, (familyPack S Γ F is).redTm t →
      (familyPack S Δ F' (is.map (Presentation.rename ρ))).redTm (Presentation.rename ρ t)) ∧
    (∀ {t t'}, (familyPack S Γ F is).eqTm t t' →
      (familyPack S Δ F' (is.map (Presentation.rename ρ))).eqTm (Presentation.rename ρ t)
        (Presentation.rename ρ t')) := by
  refine ⟨?_, fun h => FamRedTm.rename laws w renamed h, fun h => FamEqTm.rename laws w renamed h⟩
  rintro B ⟨X, is', redB, same, conv, agree⟩
  have c := laws.convTy_rename w.1 w.2 conv
  rw [renamed.type is] at c
  exact ⟨Presentation.rename ρ X, is'.map (Presentation.rename ρ), redB.rename w.1,
    renamed.sameFormer same, c, IndexAgree.rename renamed.indexPacks agree⟩

end PackLaws

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
