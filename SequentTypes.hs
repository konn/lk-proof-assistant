{-# LANGUAGE FlexibleContexts, UndecidableInstances, MultiParamTypeClasses, PatternGuards #-}
{-# LANGUAGE DeriveDataTypeable, RecordWildCards, FlexibleInstances, TupleSections#-}
{-# LANGUAGE GADTs, TypeOperators, EmptyDataDecls, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE DataKinds, PolyKinds, ScopedTypeVariables, TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module SequentTypes where
import Text.Parsec.Expr
import Text.Parsec
import qualified Text.Parsec.Token as T
import Text.Parsec.String
import Data.List
import Control.Applicative hiding (many, (<|>))
import Data.Char
import Data.Generics hiding (Fixity(..), empty)
import Data.Generics.Uniplate.Direct

import NAry

infix  6 :|-
infixr 7 :->:
infixl 8 :\/:
infixl 9 :/\:

data Formula = Var [String] String
             | Not Formula
             | Formula :\/: Formula
             | Formula :->: Formula
             | Formula :/\: Formula
             | Forall String Formula
             | Exists String Formula
               deriving (Read, Eq, Ord, Data, Typeable)

replace :: Eq a => a -> a -> a -> a
replace old new a | a == old  = new
                  | otherwise = a

isFreeIn :: String -> Formula -> Bool
isFreeIn x (Var vs v)   = x `elem` (v:vs)
isFreeIn x (Forall v f) = if x == v then False else x `isFreeIn` f
isFreeIn x (Exists v f) = if x == v then False else x `isFreeIn` f
isFreeIn x f            = any (isFreeIn x) $ children f

replaceFreeVarWith :: String -> String -> Formula -> Formula
replaceFreeVarWith old new (Var vs v) =
    let v' = if v == old then new else v
    in Var (map (replace old new) vs) v'
replaceFreeVarWith old _ f@(Forall v _)
    | v == old = f
replaceFreeVarWith old _ f@(Exists v _)
    | v == old = f
replaceFreeVarWith old new f = descend (replaceFreeVarWith old new) f

data Sequent = (:|-) { lefts :: [Formula], rights :: [Formula] }
             deriving (Eq, Ord, Data, Typeable)

instance Uniplate Sequent where
  {-# INLINE uniplate #-}
  uniplate x = plate x
 
instance Uniplate Formula where
  {-# INLINE uniplate #-}
  uniplate (Not x1) = plate Not |* x1
  uniplate ((:\/:) x1 x2) = plate (:\/:) |* x1 |* x2
  uniplate ((:->:) x1 x2) = plate (:->:) |* x1 |* x2
  uniplate ((:/\:) x1 x2) = plate (:/\:) |* x1 |* x2
  uniplate (Forall x1 x2) = plate (Forall x1) |* x2
  uniplate (Exists x1 x2) = plate (Exists x1) |* x2
  uniplate x = plate x
 
instance Biplate Formula String where
  {-# INLINE biplate #-}
  biplate (Var xs x1)    = plate Var ||* xs |* x1
  biplate (Not x1)       = plate Not |+ x1
  biplate ((:\/:) x1 x2) = plate (:\/:) |+ x1 |+ x2
  biplate ((:->:) x1 x2) = plate (:->:) |+ x1 |+ x2
  biplate ((:/\:) x1 x2) = plate (:/\:) |+ x1 |+ x2
  biplate (Forall x1 x2) = plate Forall |* x1 |+ x2
  biplate (Exists x1 x2) = plate Exists |* x1 |+ x2

instance Biplate Sequent String where
  {-# INLINE biplate #-}
  biplate ((:|-) x1 x2) = plate (:|-) ||+ x1 ||+ x2

instance Biplate Sequent Formula where
  {-# INLINE biplate #-}
  biplate ((:|-) x1 x2) = plate (:|-) ||* x1 ||* x2

data Rule :: [*] -> [*] -> * where
  Rule :: { ruleName :: String
          , apply    :: NAry as ([Sequent] -> [Sequent])
          , unapply  :: NAry bs ([Sequent] -> [Sequent])}
       -> Rule as bs

attach :: a -> (b -> c) -> b -> (c, a)
attach a f = (,a) . f

unapply' :: Rule as bs -> (bs :~> ([Sequent] -> ([Sequent], String)))
unapply' (Rule n _ f) = sub n f
  where
    sub :: String -> NAry xs (a -> b) -> (xs :~> (a -> (b, String)))
    sub n (Arg g)   = sub n . g
    sub n (Value e) = attach n e

inverseArity :: forall as bs. SingList bs => Rule as bs -> Int
inverseArity _ = len (slist :: SList bs)
  where
    len :: SList x -> Int
    len SNil = 0
    len (SCons _ xs) = 1 + len xs

data SomeRule = forall as bs. SomeRule (Rule as bs)

instance Show (Rule a b) where
  show (Rule name _ _) = "<" ++ name ++ ">"

instance Show Formula where
  showsPrec _ (Var [] v)    = showString v
  showsPrec _ (Var as v)    = showString v . showParen True (showString (intercalate ", " as))
  showsPrec _ (Not f)       = showString "¬" . showsPrec 11 f
  showsPrec d (l :\/: r)    = showParen (d > 7) $ showsPrec 8 l . showString " ∨ " . showsPrec 8 r
  showsPrec d (l :->: r)    = showParen (d > 6) $ showsPrec 7 l . showString " → " . showsPrec 7 r
  showsPrec d (l :/\: r)    = showParen (d > 8) $ showsPrec 9 l . showString " ∧ " . showsPrec 9 r
  showsPrec d (Forall v f)  = showParen (d > 9) $ showString "∀" . showString v . showString ". " . showsPrec 11 f
  showsPrec d (Exists v f)  = showParen (d > 9) $ showString "∃" . showString v . showString ". " . showsPrec 11 f

instance Show Sequent where
  showsPrec d (l :|- r) = showParen (d > 10) $ showsFs l . showString " |- " . showsFs (reverse r)
    where
      showsFs fs = foldr (.) id $ intersperse (showString ", ") $ map shows fs

isGreek :: Char -> Bool
isGreek = (`elem` (letters ++ map toLower letters))
  where
    letters = "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΞΨΩ"

greek :: Parser Char
greek = satisfy isGreek

unapplyList ::(All RuleArgument bs)
            => Rule as bs -> [String] -> [Sequent] -> Maybe ([Sequent] -> ([Sequent], String))
unapplyList (Rule n _ f) xs ss =
  attach n <$> applyStringList (Proxy :: Proxy RuleArgument) (toArg ss) f xs

applyList :: (All RuleArgument as)
          => Rule as bs -> [String] -> [Sequent] -> Maybe ([Sequent] -> ([Sequent], String))
applyList (Rule n f _ :: Rule as bs) xs ss =
  attach n <$> applyStringList (Proxy :: Proxy RuleArgument) (toArg ss) f xs

data Index (nth :: Nat) (side :: Side) = Index { runIndex :: Int }
data Side = LHS | RHS

class RuleArgument a where
  toArg :: [Sequent] -> String -> Maybe a

instance ToInt n => RuleArgument (Index n LHS) where
  toArg fs str = maybe (formulaRange $ toInt (Proxy :: Proxy n)) Just index
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
  toArg fs str = maybe (formulaRange $ toInt (Proxy :: Proxy n)) Just index
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

instance RuleArgument String where
  toArg _ str = Just str

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
formula = Forall <$  choice (map reservedOp ["forall", "∀"])
                 <*> lexeme identifier
                 <*  lexeme (char '.')
                 <*> formula
      <|> Exists <$  choice (map reservedOp ["exists", "∃"])
                 <*> lexeme identifier
                 <*  lexeme (char '.')
                 <*> formula
      <|> buildExpressionParser table term
  <?> "formula"

term :: Parser Formula
term = parens formula
   <|> try (flip Var <$> identifier
                     <*> parens (identifier `sepBy1` comma))
   <|> Var [] <$> identifier

table = [ [ Prefix $ Not    <$ choice (map reservedOp ["~", "¬"])]
        , [ Infix  ((:/\:)  <$ choice (map reservedOp ["∧", "/\\", "^"])) AssocLeft ]
        , [ Infix  ((:\/:)  <$ choice (map reservedOp ["∨", "\\/", "v"])) AssocLeft ]
        , [ Infix  ((:->:)  <$ choice (map reservedOp ["→", "->", "⊃"])) AssocRight ]
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
