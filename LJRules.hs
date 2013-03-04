{-# LANGUAGE QuasiQuotes, UnicodeSyntax, TypeOperators, DataKinds, PatternGuards #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fwarn-unused-imports #-}
module LJRules where
import SequentTypes
import SequentMacros
import NAry

isInitial :: Sequent -> Bool
isInitial [lkseq| a |- b |] = a == b

[rule|
# Permutation
  Γ, A, B, Σ ├ Θ
-------------------- permutationL
  Γ, B, A, Σ ├ Θ

# Cut
  Γ |- A   A, Σ |- Θ
--------------------------- cut
       Γ, Σ |- Θ

# Contraction
 A, A, Γ |- Θ
--------------- contractL
    A, Γ |- Θ


# Weakening
    Γ ├ Θ
------------- weakenL
 A, Γ ├ Θ

 Γ ├
------------- weakenR
 Γ ├ A

# Rules for AND
 Γ ├ A   Γ ├  B
-------------------------- andRight
  Γ ├ A ∧ B

      A, Γ ├ Θ
------------------ andLeftR
  A ∧ B, Γ ├ Θ

      A, Γ ├ Θ
------------------ andLeftL
  B ∧ A, Γ ├ Θ

# Rules for OR
 A, Γ ├ Δ   B, Γ |- Δ
-------------------------- orLeft
  A ∨ B, Γ |- Δ

 Γ ├ A
---------------- orRightR
 Γ ├ A ∨ B

 Γ ├ A
---------------- orRightL
 Γ ├ B ∨ A

# Rules for Implies
  A, Γ ├ B
-------------------------- implRight
     Γ ├ A → B

  Γ ├ A   B, Σ ├ Θ
--------------------------- implLeft
  A → B , Γ, Σ ├ Θ

# Rules for Not
 A, Γ ├
------------------- notRight
    Γ ├ ¬ A

      Γ ├ A
------------------ notLeft
 ¬ A, Γ ├
|]

anyLeft :: Rule '[String, String] '[String]
anyLeft = Rule "$\\forall$-Left" (toNAry app) (toNAry unapp)
  where
    app old new [(f : gs) :|- ds] =
        [ (Forall new (replaceFreeVarWith old new f) : gs) :|- ds]
    app _ _ _ = []
    unapp new [(Forall x f : gs) :|- ds]
      | let orig = replaceFreeVarWith x new f
      = [ (orig : gs) :|- ds]
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
        = [ gs :|- (orig : ds)]
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
