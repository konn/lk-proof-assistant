{-# LANGUAGE DeriveFunctor, ExtendedDefaultRules, FlexibleInstances  #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PatternGuards #-}
{-# LANGUAGE QuasiQuotes, TupleSections, UndecidableInstances        #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Rewind where
import           Control.Applicative
import           Control.Monad.CC
import           Control.Monad.Writer
import qualified Data.Text            as T
import qualified Data.Text.IO         as T
import           LKRules
import           NAry
import           ProofTree
import           SequentMacros
import           SequentTypes
import           System.IO
import           Text.LaTeX           hiding (proof)

default (T.Text)

puts :: MonadIO m => String -> m ()
puts = liftIO . putStrLn

gets :: MonadIO m => m String
gets = liftIO getLine

data Result a = Done a
              | Retry
              | Abort
                deriving (Show, Eq, Ord, Functor)

instance Applicative Result where
  pure = Done
  Done f <*> Done a = Done (f a)
  Retry  <*> _      = Retry
  Abort  <*> _      = Abort
  _      <*> Retry  = Retry
  _      <*> Abort  = Abort

proof :: Sequent -> IO (Result Proof)
proof s = runCCT $ reset $ buildProof s

type Proof = Tree Sequent

buildProof :: Sequent -> Prompt ans (Result Proof) -> CCT ans IO (Result Proof)
buildProof s@[lkseq| a |- b |] _ | not (null a) && a == b = do
  liftIO $ putStrLn $ "complete: " ++ show s
  return $ Done $ NullaryInf Nothing s
buildProof fm p = do
  liftIO $ putStrLn "----------------------"
  liftIO $ putStrLn $ "Goal: " ++ show fm
  liftIO $ putStr "> " >> hFlush stdout
  cmd <- gets
  mans <- reset $ \q -> do
    rule <- case words cmd of
              [":r"] -> abort p $ return Retry
              [":a"] -> abort p $ return Abort
              ("cut":args) -> return $ unapplyList cut args [fm]
              ("permutationL":args) -> return $ unapplyList permutationL args [fm]
              ("permutationR":rest) -> return $ unapplyList permutationR rest [fm]
              ("contractL":rest)    -> return $ unapplyList contractL rest [fm]
              ("contractR":_) -> return $ Just $ unapply' contractR
              ("weakenL":_) -> return $ Just $ unapply' weakenL
              ("weakenR":_) -> return $ Just $ unapply' weakenR
              ("andRight":args)
                  | [lkseq| as |- gs, a ∧ b |] <- fm -> return $ unapplyList andRight args [seqs| as |- gs |]
              ("andLeftR":_) -> return $ Just $ unapply' andLeftR
              ("andLeftL":_) -> return $ Just $ unapply' andLeftL
              ("leftR":_) -> return $ Just $ unapply' andLeftR
              ("leftL":_) -> return $ Just $ unapply' andLeftL
              ("rightR":_) -> return $ Just $ unapply' orRightR
              ("rightL":_) -> return $ Just $ unapply' orRightL
              ("orRightR":_) -> return $ Just $ unapply' orRightR
              ("orRightL":_) -> return $ Just $ unapply' orRightL
              ("orLeft":args)
                  | [lkseq| a ∨ b, as |- gs |] <- fm -> return $ unapplyList orLeft args [fm]
              ("implRight":_) -> return $ Just $ unapply' implRight
              ("implLeft":args)
                  | [lkseq| a → b, as |- gs |] <- fm -> return $ unapplyList implLeft args [fm]
              ("notLeft":_) -> return $ Just $ unapply' notLeft
              ("notRight":_) -> return $ Just $ unapply' notRight
              ("anyLeft":args) -> return $ unapplyList anyLeft args [fm]
              ("anyRight":args) -> return $ unapplyList anyRight args [fm]
              ("existsLeft":args) -> return $ unapplyList existsLeft args [fm]
              ("existsRight":args) -> return $ unapplyList existsRight args [fm]
              ("left":rest)
                  | [lkseq| ¬ a, as |- gs |] <- fm -> return $ Just $ unapply' notLeft
                  | (Forall _ _ : _) :|- _ <- fm -> return $ unapplyList anyLeft rest [fm]
                  | (Exists _ _ : _) :|- _ <- fm -> return $ unapplyList existsLeft rest [fm]
                  | [lkseq| a → b, as |- gs |] <- fm -> return $ unapplyList implLeft rest [seqs| as |- gs |]
                  | [lkseq| a ∨ b, as |- gs |] <- fm -> return $ unapplyList orLeft rest [seqs| as |- gs |]
                  | [lkseq| a ∧ b, as |- gs |] <- fm
                  , (rhs:_) <- rest
                  , run formula rhs == b -> return $ Just $ unapply' andLeftR
                  | [lkseq| a ∧ b, as |- gs |] <- fm
                  , (rhs:_) <- rest
                  , run formula rhs == a -> return $ Just $ unapply' andLeftL
              ("right":rest)
                  | _ :|- (Exists _ _ : _) <- fm -> return $ unapplyList existsRight rest [fm]
                  | _ :|- (Forall _ _ : _) <- fm -> return $ unapplyList anyRight rest [fm]
                  | [lkseq| as |- gs, ¬ a |] <- fm -> return $ Just $ unapply' notRight
                  | [lkseq| as |- gs, a → b |] <- fm -> return $ Just $ unapply' implRight
                  | [lkseq| as |- gs, a ∧ b |] <- fm -> return $ unapplyList andRight rest [seqs| as |- gs |]
                  | [lkseq| as |- gs, a ∨ b |] <- fm
                  , (lhs:_) <- rest
                  , run formula lhs == a -> return $ Just $ unapply' orRightL
                  | [lkseq| as |- gs, a ∨ b |] <- fm
                  , (rhs:_) <- rest
                  , run formula rhs == b -> return $ Just $ unapply' orRightR
              _ -> return Nothing
    case rule <*> pure [fm] of
      Just ([a], rName) -> shift p $ \k -> k $ do
        liftA2 (UnaryInf $ Just rName) <$> buildProof a q <*> pure (Done fm)
      Just ([a, b], rName) -> shift p $ \k -> k $ do
        liftA3 (BinaryInf $ Just rName) <$> buildProof a q <*> buildProof b q <*> pure (Done fm)
      _ -> liftIO (putStrLn $ "***invalid command: " ++ cmd) >> return Retry
  case mans of
    Done tr -> return (Done tr)
    Retry -> buildProof fm p
    Abort -> return Abort

main :: IO ()
main = getLine >>= proof . run sequent >>= T.putStrLn . maybe "" (render . treeToLaTeX) . maybeResult

maybeResult :: Result a -> Maybe a
maybeResult (Done v) = Just v
maybeResult _        = Nothing
