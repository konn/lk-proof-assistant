{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, TypeOperators, EmptyDataDecls, TypeFamilies, ScopedTypeVariables, FunctionalDependencies, FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
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

class HasArity a where
  arity :: a -> Int

instance HasArity Nil where
  arity _ = 0

instance HasArity as => HasArity (a :- as) where
  arity (_ :: a :- as) = 1 + arity (undefined :: as)

instance HasArity ([Sequent] -> [Sequent]) where
  arity _ = 0

instance HasArity as => HasArity (a -> as) where
  arity (_ :: a -> as) = 1 + arity (undefined :: as)

forwardArity :: HasArity as => Rule as bs -> Int
forwardArity (_ :: Rule as bs) = arity (undefined :: as)

backwardArity :: HasArity bs => Rule as bs -> Int
backwardArity (_ :: Rule as bs) = arity (undefined :: bs)

data Z
data S n

data Vector a len where
  VNil  :: Vector a Z
  VCons :: a -> Vector a n -> Vector a (S n)

class ListToVector len where
  listToVector :: [a] -> Maybe (Vector a len)

instance ListToVector Z where
  listToVector [] = Just VNil
  listToVector _  = Nothing

instance ListToVector n => ListToVector (S n) where
  listToVector (x:xs) = VCons x <$> (listToVector xs)
  listToVector []     = Nothing

class ApplyVec len xs | len -> xs where
  applyVec :: (xs :~> a) -> Vector String len -> a

instance ApplyVec Z Nil where
  applyVec f VNil = f

instance (Read x, ApplyVec len xs) => ApplyVec (S len) (x :- xs) where
  applyVec f (VCons x xs) = applyVec (f $ read x) xs

unapplyList :: (ListToVector (Length b), ApplyVec (Length b) b)
            => Rule a b -> [String] -> Maybe ([Sequent] -> [Sequent])
unapplyList (Rule _ _ f :: Rule as bs) xs =
    applyVec f <$> (listToVector xs :: Maybe (Vector String (Length bs)))

applyList :: (ListToVector (Length as), ApplyVec (Length as) as)
          => Rule as b -> [String] -> Maybe ([Sequent] -> [Sequent])
applyList (Rule _ f _ :: Rule as bs) xs =
    applyVec f <$> (listToVector xs :: Maybe (Vector String (Length as)))

type family   Length as
type instance Length Nil = Z
type instance Length (a :- as) = S (Length as)

class RuleArgument a where
  toArg :: [Formula] -> String -> Maybe a

instance RuleArgument Int where
  toArg fs str = maybe formulaRange Just index
    where
      index = 
        case reads str of
          [(i, "")] -> Just i
          _         -> Nothing
      formulaRange
          | Right prfx <- parse (parens $ formula `sepBy` comma) "" str
          , prfx `isPrefixOf` fs = Just $ length prfx
          | otherwise = Nothing
instance RuleArgument Formula where
  toArg _ str = either (const Nothing) Just $ parse formula "" str

{-
unApplyVector :: (Read b, Length bs ~ n)
              => Vector String (S n)
              -> Rule as (b :- bs)
              -> (Vector String n, Rule as bs)
unApplyVector (VCons a as) (Rule name app unapp) = (as, Rule name app (unapp $ read a))
-}

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
