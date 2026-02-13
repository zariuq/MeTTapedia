/-
# Czech Numeral-Noun Agreement

Functions governing how numerals interact with nouns.
Czech numerals change the case and agreement of the governed noun.

## Source
Ported from: ~/claude/gf-rgl/src/czech/ResCze.gf (lines 922-943)

## Key Rule (CEG 6.1)
- Num1: singular agreement (jeden dum)
- Num2_4: plural agreement (dva domy)
- Num5: Nom/Acc force genitive plural; verb agrees neuter singular
  (pet domu je ...; literally "five of-houses is")
-/

import Mettapedia.Languages.GF.Czech.Morphology

namespace Mettapedia.Languages.GF.Czech.Agreement

open Mettapedia.Languages.GF.Czech

/-! ## NumSize Form Selection

Selects the correct case form of a noun based on numeral size.
Source: GF ResCze.gf lines 923-931
-/

/-- Select noun form based on numeral size.
    Num1: singular, same case.
    Num2_4: plural, same case.
    Num5: Nom/Acc redirect to Pl Gen (quantitative genitive); else plural.
    Source: GF ResCze.gf lines 923-931 -/
def numSizeForm (cns : Number → Case → String) (n : NumSize) (c : Case) : String :=
  match n with
  | .Num1   => cns .Sg c
  | .Num2_4 => cns .Pl c
  | .Num5   => match c with
    | .Nom | .Acc => cns .Pl .Gen
    | _ => cns .Pl c

/-! ## NumSize Agreement

Determines verb agreement features based on numeral size.
Source: GF ResCze.gf lines 933-938
-/

/-- Verb agreement based on numeral size.
    Num5 forces neuter singular agreement (CEG 6.1.4).
    Source: GF ResCze.gf lines 933-938 -/
def numSizeAgr (g : Gender) (ns : NumSize) (p : Person) : Agr :=
  match ns with
  | .Num5   => { gender := .Neutr, number := .Sg, person := p }
  | .Num2_4 => { gender := g, number := .Pl, person := p }
  | .Num1   => { gender := g, number := .Sg, person := p }

/-- Number selected by numeral size.
    Source: GF ResCze.gf lines 940-943 -/
def numSizeNumber (ns : NumSize) : Number :=
  match ns with
  | .Num1 => .Sg
  | _     => .Pl

/-! ## Agreement Theorems -/

/-- Num5 always produces neuter singular agreement regardless of gender -/
theorem numSizeAgr_num5 (g : Gender) (p : Person) :
    numSizeAgr g .Num5 p = { gender := .Neutr, number := .Sg, person := p } := by
  rfl

/-- Num1 preserves gender and uses singular -/
theorem numSizeAgr_num1 (g : Gender) (p : Person) :
    numSizeAgr g .Num1 p = { gender := g, number := .Sg, person := p } := by
  rfl

/-- Num2_4 preserves gender and uses plural -/
theorem numSizeAgr_num2_4 (g : Gender) (p : Person) :
    numSizeAgr g .Num2_4 p = { gender := g, number := .Pl, person := p } := by
  rfl

/-- numSizeForm for Num5 redirects Nom to Pl Gen (quantitative genitive) -/
theorem numSizeForm_num5_nom (cns : Number → Case → String) :
    numSizeForm cns .Num5 .Nom = cns .Pl .Gen := by
  rfl

/-- numSizeForm for Num5 redirects Acc to Pl Gen -/
theorem numSizeForm_num5_acc (cns : Number → Case → String) :
    numSizeForm cns .Num5 .Acc = cns .Pl .Gen := by
  rfl

end Mettapedia.Languages.GF.Czech.Agreement
