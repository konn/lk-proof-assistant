{-# LANGUAGE DoAndIfThenElse, QuasiQuotes #-}
module Main where
import           Control.Applicative
import           Data.Generics.Uniplate.Operations
import           Data.List
import qualified Data.Text.IO                      as T
import           ProofTree
import           SequentMacros
import           SequentTypes
import           Text.LaTeX

main :: IO ()
main = do
  seq <- parseFormula <$> getLine
  if any isQuantifier $ universe seq
  then error "メイダイ ロンリ シカ ワカリマセン．．．"
  else case prove seq of
         Nothing   -> putStrLn "Not provable."
         Just tree -> do
           T.putStrLn $ render $ treeToLaTeX True tree

prove :: Formula -> Maybe (Tree Sequent)
prove f = proveSequent ([] :|- [f])

proveSequent :: Sequent -> Maybe (Tree Sequent)
proveSequent sq@[lkseq| xs |- ys |] =
  case intersect xs ys of
    (a:_)  | xs == ys  -> Just $ NullaryInf Nothing (xs :|- ys)
           | otherwise -> Just $ UnaryInf (Just "Weaken") (NullaryInf Nothing ([a] :|- [a])) sq
    [] -> reduceUnary sq <|> reduceBinary sq

reduceUnary :: Sequent -> Maybe (Tree Sequent)
reduceUnary sq@(xs :|- ys) =
    case break isLeftReducable xs of
      (ini, f:tl) ->
          case f of
            a :/\: b -> UnaryInf (Just "$\\wedge$-Left")
                          <$> proveSequent ((ini ++ [a,b] ++ tl) :|- ys)
                          <*> pure sq
            Not b    -> UnaryInf (Just "$\\neg$-Left")
                          <$> proveSequent ((ini ++ tl) :|- (b:ys))
                          <*> pure sq
            _ -> Nothing
      _ -> case break isRightReducable ys of
             (ini, f:tl) ->
                 case f of
                   a :\/: b -> UnaryInf (Just "$\\vee$-Right")
                                 <$> proveSequent (xs :|- (ini ++ [b, a] ++ tl))
                                 <*> pure sq
                   a :->: b -> UnaryInf (Just "$\\to$-Right")
                                 <$> proveSequent ((a:xs) :|- (b:ini ++ tl))
                                 <*> pure sq
                   Not b    -> UnaryInf (Just "$\\neg$-Right")
                                 <$> proveSequent ((b:xs) :|- (ini ++ tl))
                                 <*> pure sq
                   _ -> Nothing

             _ -> Nothing

reduceBinary :: Sequent -> Maybe (Tree Sequent)
reduceBinary sq@(xs :|- ys) =
  case (break (not . isVar) xs) of
    (ini, f:tl) ->
        case f of
          a :\/: b -> BinaryInf (Just "$\\vee$-Left")
                        <$> proveSequent ((ini ++ [a] ++ tl) :|- ys)
                        <*> proveSequent ((ini ++ [b] ++ tl) :|- ys)
                        <*> pure sq
          a :->: b -> UnaryInf (Just "Contraction")
                        <$> (BinaryInf (Just "$\\to$-Left")
                               <$> proveSequent ((ini ++ tl) :|- (a:ys))
                               <*> proveSequent ((b:ini ++tl) :|- ys)
                               <*> pure ((ini ++ (a :->: b):tl++ini++tl) :|- (ys++ys)))
                        <*> pure sq
          _ -> Nothing
    _ -> case (break (not . isVar) ys) of
           (ini, f:tl) ->
               case f of
                 a :/\: b -> BinaryInf (Just "$\\wedge$-Right")
                                     <$> proveSequent (xs :|- (ini ++ [a] ++ tl))
                                     <*> proveSequent (xs :|- (ini ++ [b] ++ tl))
                                     <*> pure sq
                 _ -> Nothing
           _ -> Nothing

isLeftReducable, isRightReducable :: Formula -> Bool
isLeftReducable  x = isNot x || isAnd x
isRightReducable x = isNot x || isOr x || isImpl x
