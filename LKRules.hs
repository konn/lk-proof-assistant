{-# LANGUAGE QuasiQuotes, UnicodeSyntax #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module LKRules where
import LKDataTypes
import LKMacros

isInitial :: Sequent -> Bool
isInitial [lkseq| a |- b |] = a == b

[rule|
# Permutation
  Γ, A, B, Σ ├ Δ
-------------------- permutationL
  Γ, B, A, Σ ├ Δ

  Γ ├ Δ, A, B, Π
-------------------- permutationR
  Γ ├ Δ, B, A, Π 

# Cut
  Γ |- Δ, A   A, Σ |- Π
--------------------------- cut
       Γ, Σ |- Δ, Π

# Contraction
 A, A, Γ |- Δ
--------------- contractL
    A, Γ |- Δ

 Γ |- Δ, A, A
--------------- contractR
 Γ |- Δ, A


# Weakening
    Γ ├ Δ
------------- weakenL
 A, Γ ├ Δ

 Γ ├ Δ
------------- weakenR
 Γ ├ Δ, A

# Rules for AND
 Γ ├ Δ, A   Σ ├ Π, B
-------------------------- andRight
  Γ, Σ ├ Δ, Π, A ∧ B

      A, Γ ├ Δ
------------------ andLeftR
  A ∧ B, Γ ├ Δ

      A, Γ ├ Δ
------------------ andLeftL
  B ∧ A, Γ ├ Δ

# Rules for OR
 A, Γ ├ Δ   B, Σ |- Π
-------------------------- orLeft
  A ∨ B, Γ, Σ |- Δ, Π

 Γ ├ Δ, A
---------------- orRightR
 Γ ├ Δ, A ∨ B

 Γ ├ Δ, A
---------------- orRightL
 Γ ├ Δ, B ∨ A

# Rules for Implies
  A, Γ ├ Δ, B
-------------------------- implRight
     Γ ├ Δ, A → B

  Γ ├ Δ, A   B, Σ ├ Π
--------------------------- implLeft
  A → B , Γ, Σ ├ Δ, Π

# Rules for Not
 A, Γ ├ Δ
------------------- notRight
    Γ ├ Δ, ¬ A

      Γ ├ Δ, A
------------------ notLeft
 ¬ A, Γ ├ Δ
|]
