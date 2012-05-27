{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GADTs, TypeOperators, EmptyDataDecls, TypeFamilies, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, UndecidableInstances, FunctionalDependencies #-}
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
  applyVec :: (xs :~> a) -> [Sequent] -> Vector String len -> Maybe a

instance ApplyVec Z Nil where
  applyVec f _ VNil = Just f

instance (RuleArgument x, ApplyVec len xs) => ApplyVec (S len) (x :- xs) where
  applyVec f s (VCons x xs) =
      case f <$> toArg s x of
        Just f' -> applyVec f' s xs
        Nothing -> Nothing

unapplyList :: (ListToVector (Length b), ApplyVec (Length b) b)
            => Rule a b -> [String] -> [Sequent] -> Maybe ([Sequent] -> [Sequent])
unapplyList (Rule _ _ f :: Rule as bs) xs ss =
    applyVec f ss =<< (listToVector xs :: Maybe (Vector String (Length bs)))

applyList :: (ListToVector (Length as), ApplyVec (Length as) as)
          => Rule as b -> [String] -> [Sequent] -> Maybe ([Sequent] -> [Sequent])
applyList (Rule _ f _ :: Rule as bs) xs ss =
    applyVec f ss =<< (listToVector xs :: Maybe (Vector String (Length as)))

class ToInt a where
  toInt :: a -> Int

instance ToInt Z where
  toInt _ = 0

instance ToInt n => ToInt (S n) where
  toInt (_ :: S n) = toInt (undefined :: n) + 1

type family   Length as
type instance Length Nil = Z
type instance Length (a :- as) = S (Length as)

data Index nth side = Index { runIndex :: Int }
data LHS
data RHS

class RuleArgument a where
  toArg :: [Sequent] -> String -> Maybe a

instance ToInt n => RuleArgument (Index n LHS) where
  toArg fs str = maybe (formulaRange $ toInt (undefined :: n)) Just index :: Maybe (Index n LHS)
    where
      index = 
        case reads str of
          [(i, "")] -> Just $ Index i
          _         -> Nothing
      formulaRange nth
          | Right prfx <- parse (parens $ formula `sepBy` comma) "" str
          , let target = lefts (fs !! nth)
          , prfx `isPrefixOf` target = Just $ Index $ length prfx
          | otherwise = Nothing

instance ToInt n => RuleArgument (Index n RHS) where
  toArg fs str = maybe (formulaRange $ toInt (undefined :: n)) Just index
               :: Maybe (Index n RHS)
    where
      index = 
        case reads str of
          [(i, "")] -> Just $ Index i
          _         -> Nothing
      formulaRange nth
          | Right sufx <- parse (parens $ formula `sepBy` comma) "" str
          , let target = rights (fs !! nth)
          , reverse sufx `isSuffixOf` target = Just $ Index $ length target - length sufx
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
