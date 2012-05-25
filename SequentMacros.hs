{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module SequentMacros where
import SequentTypes
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Data.Char
import Data.Generics
import Data.Maybe
import Control.Applicative
import Text.Parsec
import Data.List
import Data.Foldable (foldrM)
import Control.Monad.State
import qualified  Data.Map as M

lkseq :: QuasiQuoter
lkseq = QuasiQuoter { quoteType = undefined
                    , quoteDec  = undefined
                    , quoteExp  = lkSeqExp
                    , quotePat  = lkSeqPat
                    }

lkSeqExp str = dataToExpQ (mkQ Nothing anti) $ parseSequent str
  where
    anti :: [Formula] -> Maybe ExpQ
    anti gs = Just [| concat $(listE $ map (appE [| toFormulaList |] . dataToExpQ (mkQ Nothing trans)) gs) |]
    trans (Var s) | isFree s = Just $ varE (mkName s)
    trans _ = Nothing
lkSeqPat str = dataToPatQ (mkQ Nothing anti) $ parseSequent str
  where
    anti :: [Formula] -> Maybe PatQ
    anti fs = Just $ foldr1 (\a b -> infixP a ('(:)) b) $ map (dataToPatQ (mkQ Nothing trans)) fs
    trans (Var str) | isFree str = Just $ varP $ mkName str
    trans _ = Nothing

seqs :: QuasiQuoter
seqs = QuasiQuoter { quoteType = undefined
                   , quoteDec  = undefined
                   , quoteExp  = seqsExp
                   , quotePat  = seqsPat
                   }

isFree s = not (null s) && isLower (head s)

seqsExp str = dataToExpQ (mkQ Nothing anti) $ run (sequent `sepBy` spaces) str
  where
    anti :: [Formula] -> Maybe ExpQ
    anti gs = Just [| concat $(listE $ map (appE [| toFormulaList |] . dataToExpQ (mkQ Nothing trans)) gs) |]
    trans (Var s) | isFree s = Just $ varE (mkName s)
    trans _ = Nothing
seqsPat str = dataToPatQ (mkQ Nothing anti) $ run (sequent `sepBy` spaces) str
  where
    anti :: [Formula] -> Maybe PatQ
    anti fs = Just $ foldr1 (\a b -> infixP a ('(:)) b) $ map (dataToPatQ (mkQ Nothing trans)) fs
    trans (Var str) | isFree str = Just $ varP $ mkName str
    trans _ = Nothing

lkf :: QuasiQuoter
lkf = QuasiQuoter { quoteType = undefined
                  , quoteDec  = undefined
                  , quoteExp  = formulaExp
                  , quotePat  = undefined
                  }

formulaExp str = dataToExpQ (const Nothing) $ parseFormula str


rule :: QuasiQuoter
rule = QuasiQuoter { quoteType = undefined
                   , quoteExp  = undefined
                   , quotePat  = undefined
                   , quoteDec  = ruleDec
                   }

mkHList :: [TypeQ] -> TypeQ
-- mkHList = foldr (appT . appT (conT '(:))) (conT '[]) -- for GHC 7.4.*
mkHList = foldr (appT . appT [t| (:-) |]) [t| Nil |]

ruleDec :: String -> Q [Dec]
ruleDec str = do
  let rules = run (many1 deducRule) str
  concat <$> mapM mkRule rules
  where
    mkRule (from, ruleName, to) = do
      (appTypes, app) <- build from "app" [to]
      (unappTypes, unApp) <- build [to] "unApp" from
      let name = mkName ruleName
      sig <- sigD name [t| Rule $(mkHList appTypes) $(mkHList unappTypes) |]
      fun <- funD name [ clause [] (normalB [| Rule $(litE $ stringL ruleName) $(varE $ mkName "app") $(varE $ mkName "unApp") |])
                                [return app, return unApp]]
      return [sig, fun]
    arrow a b = [t| $(a) -> $(b) |]
    build from name to = do
      (is, pattern, guards) <- compilePattern from
      body    <- dataToExpQ (mkQ Nothing expq) to
      let pnames = nub $ everything (++) (mkQ [] extractName) from
          enames = nub $ everything (++) (mkQ [] extractName) to
          unknown = map mkName $ enames \\ pnames
          ts = map (const [t| Formula |]) unknown ++ map (const [t| Int |]) is
      funApp <- funD (mkName name) [ clause (map varP (unknown++is) ++[pattern])
                                             (guardedB [liftM2 (,) (patG guards) $ return body])
                                             []
                                , clause (wildP:map (const wildP) (unknown ++ is)) (normalB [| [] |]) []
                                ]
      return (ts, funApp)
    expq :: [Formula] -> Maybe ExpQ
    expq gs = Just $ [| concat $(listE $ map trans gs) |]
    trans s@(Var str) | isBlock s = fromJust $ simplTrans s
                      | otherwise = listE [ fromJust $ simplTrans s ]
    trans v = listE [dataToExpQ (mkQ Nothing simplTrans) v]
    simplTrans (Var s) = Just $ varE $ mkName $ normalizeName s
    simplTrans _       = Nothing
    normalizeName xs = map toLower xs
    extractName (Var v) = [normalizeName v]
    extractName _       = []
    renamer (Var name) = do
      dic <- get
      case M.lookup name dic of
        Nothing -> do
          put $ M.insert name [name] dic
          return $ Var name
        Just xs -> do
          name' <- show <$> lift (newName name)
          put $ M.insert name (name' : xs) dic
          return $ Var name'

(~=~) :: Formula -> Formula -> Bool
a ~=~ b = not (isBlock a) && not (isBlock b)

isBlock (Var (a:_)) = isGreek a
isBlock _           = False

allEq :: Eq a => [a] -> Bool
allEq xs = and $ zipWith (==) xs $ tail xs

type ExtMap = M.Map String (Maybe Name, [String])

compilePattern :: [Sequent] -> Q ([Name], PatQ, [StmtQ])
compilePattern sqs = do
  (unzip3 -> (nns, pats, sss), dic) <- runStateT (mapM extractSequent sqs) M.empty
  let overlaps = filter (not . null . drop 1) $ map (snd . snd) $ M.toList dic
      conds    = map (noBindS . appE [| allEq |] . listE . map (varE . mkName)) overlaps
  return (concat nns, listP pats, concat sss ++ conds)

extractSequent :: Sequent -> StateT ExtMap Q ([Name], PatQ, [StmtQ])
extractSequent (ls :|- rs) = do
  (is, lsPat, gs) <- extractFromFormulae ls
  (is', rsPat, gs') <- extractFromFormulae rs
  return (is ++ is', infixP lsPat '(:|-) rsPat, gs ++ gs')

extractFromFormulae :: [Formula] -> StateT (M.Map String (Maybe Name, [String])) Q ([Name], PatQ, [StmtQ])
extractFromFormulae fs = do
  let sps = groupBy (~=~) fs
  case sps of
    []  -> return ([], [p| [] |], [])
    _   -> do
      arg <- lift $ newName "rs"
      (stmts, is) <- buildGuards sps arg
      dic <- get
      return (is, varP arg, stmts)
  where
    normalizeName = map toLower
    trans var (Var str) = Just $ var $ mkName $ normalizeName str
    trans _ _ = Nothing
    toPatQ :: Data a => a -> PatQ
    toPatQ = dataToPatQ (mkQ Nothing $ trans varP)
    buildGuards [c]    name = do
      c' <- mapM (everywhereM $ mkM renamer) c
      if isBlock (head c')
        then return ([bindS (toPatQ $ head c') (varE name)], [])
        else return ([bindS (toPatQ c') (varE name)], [])
    buildGuards (c:cs) name | [Var c'] <- c, isBlock (Var c') = do
      rest <- lift $ newName "rs"
      dic <- get
      case M.lookup c' dic of
        Nothing -> do
          ind  <- lift $ newName "i"
          put $ M.insert c' (Just ind, [c']) dic
          let bind = bindS (tupP [ toPatQ (Var c'), varP rest ]) [| splitAt $(varE ind) $(varE name) |]
          (gd, is) <- buildGuards cs rest
          return (bind:gd, ind:is)
        Just (Just ind, xs) -> do
          c'' <- show <$> lift (newName c')
          put $ M.insert c' (Just ind, (c'' : xs)) dic
          let bind = bindS (tupP [ toPatQ (Var c'), varP rest ]) [| splitAt $(varE ind) $(varE name) |]
          (gd, is) <- buildGuards cs rest
          return (bind:gd, is)
    buildGuards (c:cs) name = do
      rest <- lift $ newName "rs"
      c' <- mapM (everywhereM $ mkM renamer) c
      let cons x y = infixP x '(:) y
          bind = bindS (foldr cons (varP rest) $ map toPatQ c') (varE name)
      (gd, is) <- buildGuards cs rest
      return (bind:gd, is)
    renamer (Var (normalizeName -> name)) = do
      dic <- get
      case M.lookup name dic of
        Nothing -> do
          put $ M.insert name (Nothing, [name]) dic
          return $ Var name
        Just (_, xs) -> do
          name' <- show <$> lift (newName name)
          put $ M.insert name (Nothing, name' : xs) dic
          return $ Var name'
    renamer a = return a
