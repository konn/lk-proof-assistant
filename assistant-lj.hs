{-# LANGUAGE QuasiQuotes, BangPatterns #-}
module Main where
import LJRules
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
          ("cut":a:i:_) -> Just $ unapply cut (run formula a) (read i)
          ("permutation":i:_) -> Just $ unapply permutation (read i)
          ("contract":_) -> Just $ unapply contract
          ("weaken":_) -> Just $ unapply weaken
          ("andRight":i:_) -> Just $ unapply andRight (read i)
          ("andLeftR":_) -> Just $ unapply andLeftR
          ("andLeftL":_) -> Just $ unapply andLeftL
          ("orLeft":i:_) -> Just $ unapply orLeft (read i)
          ("orRightR":_) -> Just $ unapply orRightR
          ("orRightL":_) -> Just $ unapply orRightL
          ("implRight":_) -> Just $ unapply implRight
          ("implLeft":i:_) -> Just $ unapply implLeft (read i)
          ("notLeft":_) -> Just $ unapply notLeft
          ("notRight":_) -> Just $ unapply notRight
          _ -> Nothing
  case rule <*> pure [fm] of
    Nothing -> liftIO (putStrLn "*** Command Not Found") >> prover fm
    Just [] -> liftIO (putStrLn "*** applying rule failure") >> prover fm
    Just xs -> tell [cmd] >> mapM_ prover xs
