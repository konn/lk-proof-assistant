{-# LANGUAGE PatternGuards, QuasiQuotes #-}
module Main where
import Control.Applicative
import Control.Monad.Writer
import Data.List
import LKRules
import SequentMacros
import SequentTypes
import System.IO
import Text.Parsec
import Control.Monad.State

import NAry

main :: IO ()
main = getLine >>= proof . run sequent >>= print

data Tree = NullaryInf Sequent
          | UnaryInf   Sequent Sequent
          | BinaryInf  (Sequent, Sequent) Sequent
type Log = String

type Prover = StateT (Tree, [Log]) IO

proof :: Sequent -> IO [String]
proof seq = snd <$> runWriterT (prover seq)

prover :: Sequent -> WriterT [String] IO ()
prover s@[lkseq| a |- b |] | not (null a) && a == b = liftIO $ putStrLn $ "complete: " ++ show s
prover fm = do
  liftIO $ putStrLn "----------------------"
  liftIO $ putStrLn $ "Goal: " ++ show fm
  liftIO $ putStr "> " >> hFlush stdout
  cmd <- liftIO getLine
  let rule =
        case words cmd of
          ("cut":args) -> unapplyList cut args [fm]
          ("permutationL":args) -> unapplyList permutationL args [fm]
          ("permutationR":rest) -> unapplyList permutationR rest [fm]
          ("contractL":rest)    -> unapplyList contractL rest [fm]
          ("contractR":_) -> Just $ fromNAry $ unapply contractR
          ("weakenL":_) -> Just $ fromNAry $ unapply weakenL
          ("weakenR":_) -> Just $ fromNAry $ unapply weakenR
          ("andRight":args)
            | [lkseq| as |- gs, a ∧ b |] <- fm -> unapplyList andRight args [seqs| as |- gs |]
          ("andLeftR":_) -> Just $ fromNAry $ unapply andLeftR
          ("andLeftL":_) -> Just $ fromNAry $ unapply andLeftL
          ("leftR":_) -> Just $ fromNAry $ unapply andLeftR
          ("leftL":_) -> Just $ fromNAry $ unapply andLeftL
          ("rightR":_) -> Just $ fromNAry $ unapply orRightR
          ("rightL":_) -> Just $ fromNAry $ unapply orRightL
          ("orRightR":_) -> Just $ fromNAry $ unapply orRightR
          ("orRightL":_) -> Just $ fromNAry $ unapply orRightL
          ("orLeft":args)
            | [lkseq| a ∨ b, as |- gs |] <- fm -> unapplyList orLeft args [fm]
          ("implRight":_) -> Just $ fromNAry $ unapply implRight
          ("implLeft":args)
            | [lkseq| a → b, as |- gs |] <- fm -> unapplyList implLeft args [fm]
          ("notLeft":_) -> Just $ fromNAry $ unapply notLeft
          ("notRight":_) -> Just $ fromNAry $ unapply notRight
          ("anyLeft":args) -> unapplyList anyLeft args [fm]
          ("anyRight":args) -> unapplyList anyRight args [fm]
          ("existsLeft":args) -> unapplyList existsLeft args [fm]
          ("existsRight":args) -> unapplyList existsRight args [fm]
          ("left":rest)
            | [lkseq| ¬ a, as |- gs |] <- fm -> Just $ fromNAry $ unapply notLeft
            | (Forall _ _ : _) :|- _ <- fm -> unapplyList anyLeft rest [fm]
            | (Exists _ _ : _) :|- _ <- fm -> unapplyList existsLeft rest [fm]
            | [lkseq| a → b, as |- gs |] <- fm -> unapplyList implLeft rest [seqs| as |- gs |]
            | [lkseq| a ∨ b, as |- gs |] <- fm -> unapplyList orLeft rest [seqs| as |- gs |]
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == b -> Just $ fromNAry $ unapply andLeftR
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == a -> Just $ fromNAry $ unapply andLeftL
          ("right":rest)
            | _ :|- (Exists _ _ : _) <- fm -> unapplyList existsRight rest [fm]
            | _ :|- (Forall _ _ : _) <- fm -> unapplyList anyRight rest [fm]
            | [lkseq| as |- gs, ¬ a |] <- fm -> Just $ fromNAry $ unapply notRight
            | [lkseq| as |- gs, a → b |] <- fm -> Just $ fromNAry $ unapply implRight
            | [lkseq| as |- gs, a ∧ b |] <- fm -> unapplyList andRight rest [seqs| as |- gs |]
            | [lkseq| as |- gs, a ∨ b |] <- fm
            , (lhs:_) <- rest
            , run formula lhs == a -> Just $ fromNAry $ unapply orRightL
            | [lkseq| as |- gs, a ∨ b |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == b -> Just $ fromNAry $ unapply orRightR
          _ -> Nothing
  case rule <*> pure [fm] of
    Nothing -> liftIO (putStrLn "*** Command Not Found") >> prover fm
    Just [] -> liftIO (putStrLn "*** applying rule failure") >> prover fm
    Just xs | any (== ([] :|- [])) xs -> liftIO (putStrLn "*** proof failure") >> prover fm
            | otherwise -> tell [cmd] >> mapM_ prover xs
