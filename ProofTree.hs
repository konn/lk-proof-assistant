{-# LANGUAGE ExtendedDefaultRules, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module ProofTree where
import           Data.List
import           Data.Maybe
import qualified Data.Text              as T
import           SequentTypes
import           Text.LaTeX
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Syntax

default (Int)

data Tree a = NullaryInf { label :: Maybe String, child :: a }
            | UnaryInf   { label  :: Maybe String
                         , parent :: Tree a
                         , child  :: a
                         }
            | BinaryInf  { label :: Maybe String
                         , left  :: Tree a, right :: Tree a
                         , child :: a
                         }
              deriving (Show, Eq, Ord)

axiomC :: LaTeXC l => l -> l
axiomC = liftL $ \l -> TeXComm "AxiomC" [FixArg l]

smallcaps :: LaTeXC l => l -> l
smallcaps = liftL $ \l -> TeXComm "sc" [FixArg l]

binaryInf :: LaTeXC l => l -> l
binaryInf = liftL $ \l -> TeXComm "BinaryInfC" [FixArg l]

unaryInf :: LaTeXC l => l -> l
unaryInf = liftL $ \l -> TeXComm "UnaryInfC" [FixArg l]

rightLabel :: String -> LaTeX
rightLabel l = TeXComm "RightLabel" [FixArg $ scriptsize $ smallcaps $ raw $ T.pack l]

sequentToLaTeX :: LaTeXC l => Sequent -> l
sequentToLaTeX (fs :|- gs) = math $ lhs <> comm0 "vdash" <> rhs
  where
    mkFs = mconcat . intersperse ", " . map formulaToLaTeX
    lhs = mkFs fs
    rhs = mkFs $ reverse gs

formulaToLaTeX :: LaTeXC l => Formula -> l
formulaToLaTeX = ftxPrec 0
  where
    ftxPrec _ (Var [] v) = renderVar v
    ftxPrec _ (Var vs v) =
      mconcat [renderVar v, "(", mconcat (intersperse ", " $ map renderVar vs), ")"]
    ftxPrec _ (Not f)           = comm0 "neg" <> ftxPrec 11 f
    ftxPrec d (l :\/: r)        = parenPrec (d > 7) $ mconcat [ftxPrec 8 l, comm0 "vee", ftxPrec 8 r]
    ftxPrec d (l :->: r)        = parenPrec (d > 6) $ mconcat [ftxPrec 7 l, comm0 "to", ftxPrec 7 r]
    ftxPrec d (l :/\: r)        = parenPrec (d > 8) $ mconcat [ftxPrec 9 l, comm0 "wedge", ftxPrec 9 r]
    ftxPrec d (Forall v f)      = parenPrec (d > 9) $ mconcat [comm0 "forall", renderVar v, ", ", ftxPrec 11 f]
    ftxPrec d (Exists v f)      = parenPrec (d > 9) $ mconcat [comm0 "exists", renderVar v, ", ", ftxPrec 11 f]

parenPrec :: LaTeXC l => Bool -> l -> l
parenPrec True = paren
parenPrec _    = id

paren :: LaTeXC l => l -> l
paren l = comm0 "left(" <> l <> comm0 "right)"

renderVar :: LaTeXC l => String -> l
renderVar var = fromMaybe (fromString var) $ lookup var dic
  where
    dic = [("alpha", alpha), ("beta", beta), ("gamma", gamma)
          ,("delta", delta), ("epsilon", epsilon), ("zeta", zeta)
          ,("eta", eta), ("theta", theta), ("iota", iota)
          ,("kappa", kappa), ("lambda", lambda), ("mu", mu)
          ,("nu", nu), ("xi", xi), ("pi", pi_), ("rho", rho)
          ,("sigma", sigma), ("tau", tau), ("upsilon", upsilon)
          ,("phi", phi), ("chi", chi), ("psi", psi), ("omega", omega)
          ,("α", alpha), ("β", beta), ("γ", gamma)
          ,("δ", delta), ("ε", epsilon), ("ζ", zeta)
          ,("η", eta), ("θ", theta), ("ι", iota)
          ,("κ", kappa), ("λ", lambda), ("μ", mu)
          ,("ν", nu), ("ξ", xi), ("π", pi_), ("ρ", rho)
          ,("σ", sigma), ("τ", tau), ("υ", upsilon)
          ,("φ", phi), ("χ", chi), ("ψ", psi), ("ω", omega)
          ,("Alpha", "A"), ("Beta", "B"), ("Gamma", gammau)
          ,("Delta", deltau), ("Epsilon", "E"), ("Zeta", "Z")
          ,("Eta", "H"), ("Theta", thetau), ("Iota", "I")
          ,("Kappa", "K"), ("Lambda", lambdau), ("Mu", "M")
          ,("Nu", "N"), ("Xi", xiu), ("Pi", piu), ("Rho", "P")
          ,("Sigma", sigmau), ("tau", "T"), ("Upsilon", upsilonu)
          ,("Phi", phiu), ("Chi", "X"), ("Psi", psiu), ("Omega", omegau)
          ,("Α", "A"), ("Β", "B"), ("Γ", gammau)
          ,("Δ", deltau), ("Ε", "E"), ("Ζ", "Z")
          ,("Η", "H"), ("Θ", thetau), ("Ι", "I")
          ,("Κ", "K"), ("Λ", lambdau), ("Μ", "M")
          ,("Ν", "N"), ("Ξ", xiu), ("Π", piu), ("Ρ", "P")
          ,("Σ", sigmau), ("Τ", "T"), ("Υ", upsilonu)
          ,("Φ", phiu), ("Χ", "X"), ("Ψ", psiu), ("Ω", omegau)
          ]

treeToLaTeX :: Tree Sequent -> LaTeX
treeToLaTeX (NullaryInf ml a)      = axiomC "" <> maybe "" (rightLabel . fromString) ml
                                     <> unaryInf (sequentToLaTeX a)
treeToLaTeX (UnaryInf ml tree a)   = treeToLaTeX tree <> maybe "" (rightLabel . fromString) ml
                                     <> unaryInf (sequentToLaTeX a)
treeToLaTeX (BinaryInf ml t1 t2 a) = treeToLaTeX t1 <> treeToLaTeX t2
                                       <> maybe "" (rightLabel . fromString) ml
                                       <> binaryInf (sequentToLaTeX a)
