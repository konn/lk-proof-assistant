{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleInstances #-}
{-# LANGUAGE GADTs, TypeOperators, EmptyDataDecls, TypeFamilies #-}
-- {-# LANGUAGE DataKinds #-}
module SequentTypes where
import Text.Parsec.Expr
import Text.Parsec
import qualified Text.Parsec.Token as T
import Text.Parsec.String
import Data.List
import Control.Applicative hiding (many, (<|>))
import Data.List
import Data.Char
import Data.Either
import Data.Data (Typeable, Data)

infix  6 :|-
infixr 7 :->:
infixl 8 :\/:
infixl 9 :/\:

data Formula = Var String
             | Not Formula
             | Formula :\/: Formula
             | Formula :->: Formula
             | Formula :/\: Formula
               deriving (Read, Eq, Ord, Data, Typeable)

data Sequent = (:|-) { lefts :: [Formula], rights :: [Formula] }
             deriving (Eq, Ord, Data, Typeable)

{-
-- For GHC 7.4.*
type family   (:~>) (a :: [*]) (f :: *)
type instance '[] :~> f = f
type instance (a ': b) :~> f = a -> b :~> f
-}

data Nil
data a :- b

type family   (:~>) a f
type instance Nil :~> f = f
type instance (a :- b) :~> f = a -> b :~> f

infixr :~>
-- data Rule (as :: [*]) (bs :: [*]) where
data Rule as bs where
  Rule :: { ruleName :: String
          , apply   :: as :~> ([Sequent] -> [Sequent])
          , unapply  :: bs :~> ([Sequent] -> [Sequent])}
       -> Rule as bs

instance Show (Rule a b) where
  show (Rule name _ _) = "<" ++ name ++ ">"

instance Show Formula where
  showsPrec _ (Var v)    = showString v
  showsPrec d (Not f)    = showString "¬" . showsPrec 11 f
  showsPrec d (l :\/: r) = showParen (d > 7) $ showsPrec 8 l . showString " ∨ " . showsPrec 8 r
  showsPrec d (l :->: r) = showParen (d > 6) $ showsPrec 7 l . showString " → " . showsPrec 7 r
  showsPrec d (l :/\: r) = showParen (d > 8) $ showsPrec 9 l . showString " ∧ " . showsPrec 9 r

instance Show Sequent where
  showsPrec d (l :|- r) = showParen (d > 10) $ showsFs l . showString " |- " . showsFs (reverse r)
    where
      showsFs fs = foldr (.) id $ intersperse (showString ", ") $ map shows fs

isGreek = (`elem` (letters ++ map toLower letters))
  where
    letters = "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΞΨΩ"
greek = satisfy isGreek

lang :: T.LanguageDef ()
lang = T.LanguageDef { T.commentStart = "{-"
                     , T.commentEnd   = "-}"
                     , T.commentLine  = "#"
                     , T.nestedComments = True
                     , T.identStart     = letter <|> greek
                     , T.identLetter    = alphaNum <|> greek <|> char '\''
                     , T.opStart        = empty
                     , T.opLetter       = empty
                     , T.reservedNames  = []
                     , T.reservedOpNames = ["~", "->", "\\/", "/\\", "⊃", "|-"
                                           ,"¬", "→", "∧", "∨", "^", "v", "├"
                                           ]
                     , T.caseSensitive   = True
                     }

T.TokenParser {..} = T.makeTokenParser lang

formula :: Parser Formula
formula = buildExpressionParser table term
      <?> "formula"

term = parens formula
   <|> Var <$> identifier

table = [ [ Prefix $ Not   <$ choice (map reservedOp ["~", "¬"])]
        , [ Infix  ((:/\:) <$ choice (map reservedOp ["∧", "/\\", "^"])) AssocLeft ]
        , [ Infix  ((:\/:) <$ choice (map reservedOp ["∨", "\\/", "v"])) AssocLeft ]
        , [ Infix  ((:->:) <$ choice (map reservedOp ["→", "->", "⊃"])) AssocRight ]
        ]

sequent = (:|-) <$> fs <* (choice $ map reservedOp ["|-", "├"])
                <*> (reverse <$> fs)
  where
    fs = formula `sepBy` comma

parseSequent = run sequent
parseFormula = run formula

run p src =
    case parse (whiteSpace *> p <* eof) "" src of
      Left err -> error $ show err
      Right ans -> ans

class FormulaListable a where
  toFormulaList :: a -> [Formula]

instance FormulaListable Formula where
  toFormulaList = pure

instance FormulaListable [Formula] where
  toFormulaList = id

deducRule = (,,) <$> (sequent `sepBy` whiteSpace)
                 <*  lexeme (skipMany1 (char '-'))
                 <*> identifier
                 <*> sequent
--                 <*  newline
