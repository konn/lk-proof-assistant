{-# LANGUAGE QuasiQuotes, UnicodeSyntax #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module LJRules where
import SequentTypes
import SequentMacros

isInitial :: Sequent -> Bool
isInitial [lkseq| a |- b |] = a == b

[rule|
# Permutation
  Γ, A, B, Σ ├ Δ
-------------------- permutation
  Γ, B, A, Σ ├ Δ

# Cut
  Γ |- A   A, Σ |- Π
--------------------------- cut
       Γ, Σ |- Π

# Contraction
 A, A, Γ |- Δ
--------------- contract
    A, Γ |- Δ

# Weakening
    Γ ├ Δ
------------- weaken
 A, Γ ├ Δ

# Rules for AND
 Γ ├ A   Σ ├ B
-------------------------- andRight
  Γ, Σ ├ A ∧ B

      A, Γ ├ Δ
------------------ andLeftR
  A ∧ B, Γ ├ Δ

      A, Γ ├ Δ
------------------ andLeftL
  B ∧ A, Γ ├ Δ

# Rules for OR
 A, Γ ├ Δ   B, Σ |- Δ
-------------------------- orLeft
  A ∨ B, Γ, Σ |- Δ

 Γ ├ A
---------------- orRightR
 Γ ├ A ∨ B

 Γ ├ A
---------------- orRightL
 Γ ├ B ∨ A

# Rules for Implies
  A, Γ ├ B
------------------ implRight
     Γ ├ A → B

  Γ ├ A   B, Σ ├ Π
----------------------- implLeft
  A → B , Γ, Σ ├ Π

# Rules for Not
 A, Γ ├ 
------------------- notRight
    Γ ├ ¬ A

      Γ ├ A
------------------ notLeft
 ¬ A, Γ ├ 
|]
