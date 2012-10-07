{-# LANGUAGE QuasiQuotes, UnicodeSyntax, TypeOperators, DataKinds, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module LKRules where
import SequentTypes
import SequentMacros
import NAry

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

anyLeft :: Rule '[String, String] '[String]
anyLeft = Rule "$\\forall$-Left" (toNAry app) (toNAry unapp)
  where
    app old new [(f : gs) :|- ds] =
        [ (Forall new (replaceFreeVarWith old new f) : gs) :|- ds]
    app _ _ _ = []
    unapp new [(Forall x f : gs) :|- ds]
      | let orig = replaceFreeVarWith x new f
      , replaceFreeVarWith new x orig == f = [ (orig : gs) :|- ds]
    unapp _ _ = []

anyRight :: Rule '[String, String] '[String]
anyRight = Rule "$\\forall$-Left" (toNAry app) (toNAry unapp)
  where
    app old new [ gs :|- (f : ds)]
        | not (any (new `isFreeIn`) $ gs ++ ds)
        = [ gs :|- (Forall new (replaceFreeVarWith old new f) : ds)]
    app _ _ _ = []
    unapp new [ gs :|- (Forall x f : ds)]
        | not (any (new `isFreeIn`) (Forall x f : gs ++ ds))
        , let orig = replaceFreeVarWith x new f
        , replaceFreeVarWith new x orig == f
        = [ gs :|- (replaceFreeVarWith x new f : ds)]
    unapp _ _ = []

existsRight :: Rule '[String, String] '[String]
existsRight = Rule "$\\exists$-Right" (toNAry app) (toNAry unapp)
  where
    app old new [gs :|- (f : ds)] =
        [ gs :|- (Exists new (replaceFreeVarWith old new f) : ds)]
    app _ _ _ = []
    unapp new [gs :|- (Exists x f : ds)]
        | let orig = replaceFreeVarWith x new f
        , replaceFreeVarWith new x orig == f =
        [ gs :|- (orig : ds)]
    unapp _ _ = []

existsLeft :: Rule '[String, String] '[String]
existsLeft = Rule "$\\exists$-Left" (toNAry app) (toNAry unapp)
  where
    app old new [ (f : gs) :|- ds]
        | not (any (new `isFreeIn`) $ gs ++ ds)
        = [(Exists new (replaceFreeVarWith old new f) : gs) :|- ds]
    app _ _ _ = []
    unapp new [ (Exists x f : gs) :|- ds ]
        | not (any (new `isFreeIn`) (Exists x f : gs ++ ds))
        , let orig = replaceFreeVarWith x new f
        , replaceFreeVarWith new x orig == f
        = [ (replaceFreeVarWith x new f : gs) :|- ds]
    unapp _ _ = []
