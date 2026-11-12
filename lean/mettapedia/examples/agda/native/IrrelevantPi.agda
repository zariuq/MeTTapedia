{-# OPTIONS --safe --without-K #-}
module IrrelevantPi where
open import NikStructuralExport
open import Agda.Builtin.Unit
check : ⊤
check = nikStructural 64 Set₁ ((A : Set) → .(x : A) → A)
