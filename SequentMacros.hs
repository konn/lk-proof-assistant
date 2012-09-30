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

import NAry

lkseq :: QuasiQuoter
lkseq = QuasiQuoter { quoteType = undefined
                    , quoteDec  = undefined
                    , quoteExp  = lkSeqExp
                    , quotePat  = lkSeqPat
                    }

lkSeqExp :: String -> Q Exp
seqsExp :: String -> Q Exp
lkSeqExp str = dataToExpQ (mkQ Nothing anti) $ parseSequent str
  where
    anti :: [Formula] -> Maybe ExpQ
    anti gs = Just [| concat $(listE $ map (appE [| toFormulaList |] . dataToExpQ (mkQ Nothing trans)) gs) |]
    trans (Var xs s) | isFree s = Just $ varE (mkName s)
    trans _ = Nothing
lkSeqPat str = dataToPatQ (mkQ Nothing anti) $ parseSequent str
  where
    anti :: [Formula] -> Maybe PatQ
    anti fs = Just $ foldr1 (\a b -> infixP a ('(:)) b) $ map (dataToPatQ (mkQ Nothing trans)) fs
    trans (Var xs str) | isFree str = Just $ varP $ mkName str
    trans (Forall v f) | isFree v = Just $ conP 'Forall [varP (mkName v), dataToPatQ (mkQ Nothing anti)f]
    trans (Exists v f) | isFree v = Just $ conP 'Forall [varP (mkName v), dataToPatQ (mkQ Nothing anti)f]
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
    trans (Var xs s) | isFree s = Just $ varE (mkName s)
    trans _ = Nothing
seqsPat str = dataToPatQ (mkQ Nothing anti) $ run (sequent `sepBy` spaces) str
  where
    anti :: [Formula] -> Maybe PatQ
    anti fs = Just $ foldr1 (\a b -> infixP a ('(:)) b) $ map (dataToPatQ (mkQ Nothing trans)) fs
    trans (Var xs str) | isFree str = Just $ varP $ mkName str
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
mkHList = foldr (appT . appT (conT '(:))) (conT '[]) -- for GHC 7.4.*

toTeX :: String -> String
toTeX (break isUpper -> (hdr, rest)) = proc hdr ++ rest
  where
    proc "and" = "$\\wedge$-"
    proc "or" = "$\\vee$-"
    proc "not" = "$\\neg$-"
    proc "impl" = "$\\to$-"
    proc (c:st) = toUpper c : st
    proc str    = str

ruleDec :: String -> Q [Dec]
ruleDec str = do
  let rules = run (many1 deducRule) str
  concat <$> mapM mkRule rules
  where
    mkRule (from, ruleName, to) = do
      (appTypes, app) <- build ruleName from "app" [to]
      (unappTypes, unApp) <- build ruleName [to] "unApp" from
      let name = mkName ruleName
      sig <- sigD name [t| Rule $(mkHList appTypes) $(mkHList unappTypes) |]
      fun <- funD name [ clause [] (normalB [| Rule $(litE $ stringL $ toTeX ruleName) (toNAry $(varE $ mkName "app")) (toNAry $(varE $ mkName "unApp")) |])
                                [return app, return unApp]]
      return [sig, fun]
    arrow a b = [t| $(a) -> $(b) |]
    build rName from name to = do
      (types, is, pattern, guards) <- compilePattern from
      body    <- dataToExpQ (mkQ Nothing expq) to
      let pnames = nub $ everything (++) (mkQ [] extractName) from
          enames = nub $ everything (++) (mkQ [] extractName) to
          unknown = map mkName $ enames \\ pnames
          ts = map (const [t| Formula |]) unknown ++ types
      funApp <- funD (mkName name) [ clause (map varP unknown++map (conP 'Index . pure . varP) is ++[pattern])
                                             (guardedB [liftM2 (,) (patG guards) $ return body])
                                             []
                                   , clause (wildP:map (const wildP) (unknown ++is)) (normalB [| [] |]) []
                                   ]
      return (ts, funApp)
    expq :: [Formula] -> Maybe ExpQ
    expq gs = Just $ [| concat $(listE $ map trans gs) |]
    trans s@(Var xs str) | isBlock s = fromJust $ simplTrans s
                         | otherwise = listE [ fromJust $ simplTrans s ]
    trans v = listE [dataToExpQ (mkQ Nothing simplTrans) v]
    simplTrans (Var vvs s) = Just $ varE $ mkName $ normalizeName s
    simplTrans _       = Nothing
    normalizeName xs = map toLower xs
    extractName (Var vvs v) = map normalizeName (v : vvs)
    extractName _       = []
    renamer (Var vvs name) = do
      dic <- get
      case M.lookup name dic of
        Nothing -> do
          put $ M.insert name [name] dic
          return $ Var vvs name
        Just xs -> do
          name' <- show <$> lift (newName name)
          put $ M.insert name (name' : xs) dic
          return $ Var vvs name'

(~=~) :: Formula -> Formula -> Bool
a ~=~ b = not (isBlock a) && not (isBlock b)

isBlock (Var xs (a:_)) = isGreek a
isBlock _              = False

allEq :: Eq a => [a] -> Bool
allEq xs = and $ zipWith (==) xs $ tail xs

type ExtMap = M.Map String (Maybe Name, [String])

compilePattern :: [Sequent] -> Q ([TypeQ], [Name], PatQ, [StmtQ])
compilePattern sqs = do
  (unzip4 -> (tps, names, pats, sss), dic) <- runStateT (mapM extractSequent sqs) M.empty
  let overlaps = filter (not . null . drop 1) $ map (snd . snd) $ M.toList dic
      conds    = map (noBindS . appE [| allEq |] . listE . map (varE . mkName)) overlaps
      appIndex a b = [t| Index $a $b |]
      tNums = iterate (appT [t| 'S |]) [t| 'Z |]
      types = concat $ zipWith (map . appIndex) (take (length tps) tNums) tps
  return (types, concat names, listP pats, concat sss ++ conds)

extractSequent :: Sequent -> StateT ExtMap Q ([TypeQ], [Name], PatQ, [StmtQ])
extractSequent (ls :|- rs) = do
  (is, lsPat, gs) <- extractFromFormulae ls
  (is', rsPat, gs') <- extractFromFormulae rs
  return (map (const $ conT 'LHS) is ++ map (const $ conT 'RHS) is', is ++ is'
         , infixP lsPat '(:|-) rsPat, gs ++ gs')

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
    trans var (Var [] str) = Just $ var $ mkName $ normalizeName str
    trans _ _ = Nothing
    toPatQ :: Data a => a -> PatQ
    toPatQ = dataToPatQ (mkQ Nothing $ trans varP)
    buildGuards [c]    name = do
      c' <- mapM (everywhereM $ mkM renamer) c
      if isBlock (head c')
        then return ([bindS (toPatQ $ head c') (varE name)], [])
        else return ([bindS (toPatQ c') (varE name)], [])
    buildGuards (c:cs) name | [Var vvvs c'] <- c, isBlock (Var vvvs c') = do
      rest <- lift $ newName "rs"
      dic <- get
      case M.lookup c' dic of
        Nothing -> do
          ind  <- lift $ newName "i"
          put $ M.insert c' (Just ind, [c']) dic
          let bind = bindS (tupP [ toPatQ (Var [] c'), varP rest ]) [| splitAt $(varE ind) $(varE name) |]
          (gd, is) <- buildGuards cs rest
          return (bind:gd, ind:is)
        Just (Just ind, xs) -> do
          c'' <- show <$> lift (newName c')
          put $ M.insert c' (Just ind, (c'' : xs)) dic
          let bind = bindS (tupP [ toPatQ (Var [] c'), varP rest ]) [| splitAt $(varE ind) $(varE name) |]
          (gd, is) <- buildGuards cs rest
          return (bind:gd, is)
    buildGuards (c:cs) name = do
      rest <- lift $ newName "rs"
      c' <- mapM (everywhereM $ mkM renamer) c
      let cons x y = infixP x '(:) y
          bind = bindS (foldr cons (varP rest) $ map toPatQ c') (varE name)
      (gd, is) <- buildGuards cs rest
      return (bind:gd, is)
    renamer (Var (map normalizeName -> vs) (normalizeName -> name)) = do
      dic <- get
      case M.lookup name dic of
        Nothing -> do
          put $ M.insert name (Nothing, [name]) dic
          return $ Var vs name
        Just (_, xs) -> do
          name' <- show <$> lift (newName name)
          put $ M.insert name (Nothing, name' : xs) dic
          return $ Var vs name'
    renamer a = return a
