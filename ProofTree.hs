{-# LANGUAGE ExtendedDefaultRules, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}
module ProofTree where
import           Data.List
import           Data.Maybe
import qualified Data.Text               as T
import           SequentTypes
import           Text.LaTeX
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSMath

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

axiom :: LaTeXC l => l -> l
axiom = liftL $ \l -> TeXCommS "Axiom" <> l

smallcaps :: LaTeXC l => l -> l
smallcaps = liftL $ \l -> TeXComm "sc" [FixArg l]

binaryInfC :: LaTeXC l => l -> l
binaryInfC = liftL $ \l -> TeXComm "BinaryInfC" [FixArg l]

unaryInfC :: LaTeXC l => l -> l
unaryInfC = liftL $ \l -> TeXComm "UnaryInfC" [FixArg l]

binaryInf :: Bool -> LaTeX -> LaTeX
binaryInf False = binaryInfC
binaryInf True  = liftL $ \l -> TeXCommS "BinaryInf" <> l

unaryInf :: Bool -> LaTeX -> LaTeX
unaryInf False = unaryInfC
unaryInf True  = liftL $ \l -> TeXCommS "UnaryInf" <> l

rightLabel :: String -> LaTeX
rightLabel l = TeXComm "RightLabel" [FixArg $ scriptsize $ smallcaps $ raw $ T.pack l]

sequentToLaTeX :: LaTeXC l => Sequent -> l
sequentToLaTeX (fs :|- gs) = math $ lhs <> comm0 "fCenter" <> rhs
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
    ftxPrec d (Forall v f)      = parenPrec (d > 9) $ mconcat [comm0 "forall", renderVar v, ftxPrec 11 f]
    ftxPrec d (Exists v f)      = parenPrec (d > 9) $ mconcat [comm0 "exists", renderVar v, ftxPrec 11 f]

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

treeToLaTeX :: Bool -> Tree Sequent -> LaTeX
treeToLaTeX c tr = TeXCommS "def" <> TeXComm "fCenter" [FixArg $ TeXCommS " " <> comm0 "vdash" <> TeXCommS " "]
                      <> body tr <> TeXCommS "DisplayProof"
  where
    body (NullaryInf ml a)      = axiomC "" <> maybe "" (rightLabel . fromString) ml
                                  <> unaryInf c (sequentToLaTeX a)
    body (UnaryInf ml tree a)   = body tree <> maybe "" (rightLabel . fromString) ml
                                  <> unaryInf c (sequentToLaTeX a)
    body (BinaryInf ml t1 t2 a) = body t1 <> body t2
                                  <> maybe "" (rightLabel . fromString) ml
                                  <> binaryInf c (sequentToLaTeX a)
