{-# OPTIONS --safe --without-K #-}
module BudgetZero where
open import NikStructuralExport
open import Agda.Builtin.Unit
check : ⊤
check = nikStructural 0 Set₁ Set
