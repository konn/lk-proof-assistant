{-# LANGUAGE QuasiQuotes, BangPatterns #-}
module Main where
import LKRules
import SequentMacros
import SequentTypes
import Text.Parsec
import Control.Monad.Writer
import Control.Applicative
import Data.List
import System.IO

main :: IO ()
main = getLine >>= proof . run sequent >>= print

proof :: Sequent -> IO [String]
proof seq = snd <$> runWriterT (prover seq)

prover :: Sequent -> WriterT [String] IO ()
prover s@[lkseq| a |- b |] | a == b = liftIO $ putStrLn $ "complete: " ++ show s
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
          ("contractL":rest) -> unapplyList contractL rest [fm]
          ("contractR":_) -> Just $ unapply contractR
          ("weakenL":_) -> Just $ unapply weakenL
          ("weakenR":_) -> Just $ unapply weakenR
          ("andRight":args)
            | [lkseq| as |- gs, a ∧ b |] <- fm -> unapplyList andRight args [seqs| as |- gs |]
          ("andLeftR":_) -> Just $ unapply andLeftR
          ("andLeftL":_) -> Just $ unapply andLeftL
          ("leftR":_) -> Just $ unapply andLeftR
          ("leftL":_) -> Just $ unapply andLeftL
          ("rightR":_) -> Just $ unapply orRightR
          ("rightL":_) -> Just $ unapply orRightL
          ("orRightR":_) -> Just $ unapply orRightR
          ("orRightL":_) -> Just $ unapply orRightL
          ("orLeft":args)
            | [lkseq| a ∨ b, as |- gs |] <- fm -> unapplyList orLeft args [fm]
          ("implRight":_) -> Just $ unapply implRight
          ("implLeft":args)
            | [lkseq| a → b, as |- gs |] <- fm -> unapplyList implLeft args [fm]
          ("notLeft":_) -> Just $ unapply notLeft
          ("notRight":_) -> Just $ unapply notRight
          ("left":rest)
            | [lkseq| ¬ a, as |- gs |] <- fm -> Just $ unapply notLeft
            | [lkseq| a → b, as |- gs |] <- fm -> unapplyList implLeft rest [seqs| as |- gs |]
            | [lkseq| a ∨ b, as |- gs |] <- fm -> unapplyList orLeft rest [seqs| as |- gs |]
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == b -> Just $ unapply andLeftR
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == a -> Just $ unapply andLeftL
          ("right":rest)
            | [lkseq| as |- gs, ¬ a |] <- fm -> Just $ unapply notRight
            | [lkseq| as |- gs, a → b |] <- fm -> Just $ unapply implRight
            | [lkseq| as |- gs, a ∧ b |] <- fm -> unapplyList andRight rest [seqs| as |- gs |]
            | [lkseq| as |- gs, a ∨ b |] <- fm
            , (lhs:_) <- rest
            , run formula lhs == a -> Just $ unapply orRightL
            | [lkseq| as |- gs, a ∨ b |] <- fm
            , (rhs:_) <- rest
            , run formula rhs == b -> Just $ unapply orRightR

          _ -> Nothing
  case rule <*> pure [fm] of
    Nothing -> liftIO (putStrLn "*** Command Not Found") >> prover fm
    Just [] -> liftIO (putStrLn "*** applying rule failure") >> prover fm
    Just xs -> tell [cmd] >> mapM_ prover xs
