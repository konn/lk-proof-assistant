{-# LANGUAGE QuasiQuotes, BangPatterns #-}
module Main where
import LKRules
import SequentMacros
import SequentTypes
import Control.Monad.Writer
import Control.Applicative

main :: IO ()
main = getLine >>= proof . run sequent >>= print

proof :: Sequent -> IO [String]
proof seq = snd <$> runWriterT (prover seq)

prover :: Sequent -> WriterT [String] IO ()
prover s@[lkseq| a |- b |] | a == b = liftIO $ putStrLn $ "complete: " ++ show s
prover fm = do
  liftIO $ putStrLn "----------------------"
  liftIO $ putStrLn $ "Goal: " ++ show fm
  liftIO $ putStr "> "
  cmd <- liftIO getLine
  let rule =
        case words cmd of
          ("cut":a:i:j:_) -> Just $ unapply cut (run formula a) (read i) (read j)
          ("permutationL":i:_) -> Just $ unapply permutationL (read i)
          ("permutationR":i:_) -> Just $ unapply permutationR (read i)
          ("contractL":_) -> Just $ unapply contractL
          ("contractR":_) -> Just $ unapply contractR
          ("weakenL":_) -> Just $ unapply weakenL
          ("weakenR":_) -> Just $ unapply weakenR
          ("andRight":i:j:_) -> Just $ unapply andRight (read i) (read j)
          ("andLeftR":_) -> Just $ unapply andLeftR
          ("andLeftL":_) -> Just $ unapply andLeftL
          ("leftR":_) -> Just $ unapply andLeftR
          ("leftL":_) -> Just $ unapply andLeftL
          ("orLeft":i:j:_) -> Just $ unapply orLeft (read i) (read j)
          ("rightR":_) -> Just $ unapply orRightR
          ("rightL":_) -> Just $ unapply orRightL
          ("orRightR":_) -> Just $ unapply orRightR
          ("orRightL":_) -> Just $ unapply orRightL
          ("implRight":_) -> Just $ unapply implRight
          ("implLeft":i:j:_) -> Just $ unapply implLeft (read i) (read j)
          ("notLeft":_) -> Just $ unapply notLeft
          ("notRight":_) -> Just $ unapply notRight
          ("left":rest)
            | [lkseq| ¬ a, as |- gs |] <- fm -> Just $ unapply notLeft
            | [lkseq| a → b, as |- gs |] <- fm
            , (i:j:_) <- rest -> Just $ unapply implLeft (read i) (read j)
            | [lkseq| a ∨ b, as |- gs |] <- fm
            , (i:j:_) <- rest -> Just $ unapply orLeft (read i) (read j)
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , ("L":_) <- rest -> Just $ unapply andLeftL
            | [lkseq| a ∧ b, as |- gs |] <- fm
            , ("R":_) <- rest -> Just $ unapply andLeftR
          ("right":rest)
            | [lkseq| as |- gs, ¬ a |] <- fm -> Just $ unapply notRight
            | [lkseq| as |- gs, a → b |] <- fm -> Just $ unapply implRight
            | [lkseq| as |- gs, a ∧ b |] <- fm
            , (i:j:_) <- rest -> Just $ unapply andRight (read i) (read j)
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
