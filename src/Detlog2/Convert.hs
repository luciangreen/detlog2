-- | The Detlog converter: Prolog with choicepoints and cuts becomes
-- deterministic code that combines alternatives with splices.
--
-- After cut elimination ("Detlog2.CutElim"), every predicate @p/n@ becomes a
-- deterministic predicate
--
-- > p__cp(A1, ..., An, Rows)
--
-- which always succeeds exactly once.  @Rows@ is the answer packet of the
-- original predicate: one row @[A1', ..., An']@ per answer, in Prolog order,
-- duplicates included.  Inside a clause, alternatives are never explored by
-- backtracking; instead each goal maps a list of environment rows to a new
-- list of rows:
--
--   * facts become a choice packet: @member_cp(P, [[a],[b]]), cp_filter(P, Args, Rows)@;
--   * @member/2@ and @between/3@ become @member_cp/2@ / @between_cp/3@ packets;
--   * a call to a user predicate asks for its packet and splices it into the
--     environment with @splice_extend/4@;
--   * independent generators in a conjunction are computed once each and
--     combined with @splice/2@ (a deterministic Cartesian product) - "splice
--     early, enumerate late";
--   * disjunction concatenates packets (@rows_concat/2@);
--   * if-then-else, once/1 and \+/1 become @if_commit/3@ decisions.
--
-- The output uses no cut, no disjunction, no if-then-else and no
-- nondeterministic built-in.  Every generated predicate has either one
-- clause, or two clauses whose first arguments are @[]@ and @[_|_]@ (row
-- iteration), so no call can leave a choicepoint; "Detlog2.Check" verifies
-- this.
module Detlog2.Convert
  ( ConvertOptions(..)
  , defaultConvertOptions
  , ConvertResult(..)
  , convertProgram
  , cpName
  , queryKey
  , addQueryClause
  , prepareProgram
  ) where

import Control.Monad (foldM, forM)
import qualified Data.IntSet as IS
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Detlog2.Builtins
import Detlog2.CutElim
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Term

data ConvertOptions = ConvertOptions
  { coSpliceEarly :: Bool          -- ^ combine independent generators with splice/2
  , coExternal :: Set.Set PredKey  -- ^ predicates whose __cp code is supplied elsewhere (memo tables)
  }

defaultConvertOptions :: ConvertOptions
defaultConvertOptions = ConvertOptions True Set.empty

data ConvertResult = ConvertResult
  { crProgram :: Program        -- ^ the deterministic Detlog program
  , crEvents :: [String]        -- ^ what was converted, and how
  }

cpName :: String -> String
cpName f = f ++ "__cp"

queryKey :: PredKey
queryKey = ("$query", 0)

-- | Add a clause '$query'(V1, ..., Vk) :- Goal for a query with variables
-- V1..Vk, so that the query is converted like any other predicate.
addQueryClause :: Term -> [Term] -> Int -> Program -> (Program, PredKey)
addQueryClause goal vars nv p =
  let key = ("$query", length vars)
      h = if null vars then Atom "$query" else Comp "$query" vars
      cl = Clause h goal nv
      p' = p { progPreds = M.insert key [cl] (progPreds p)
             , progOrder = filter (/= key) (progOrder p) ++ [key] }
  in (p', key)

-- | Cut elimination, library predicates, closure specialisation and
-- removal of unused library code.
prepareProgram :: Set.Set PredKey -> Program -> Either String (Program, [String])
prepareProgram external p0 = do
  (p1, cutEvents) <- case eliminateCuts p0 of
    Left bad -> Left ("cannot convert these cuts:\n  " ++ intercalate "\n  " (map showCutEvent bad))
    Right r -> Right r
  let p2 = withPrelude p1
  (p3, metaEvents) <- specialiseMeta p2
  let p4 = pruneUnused (Set.fromList (progOrder p0)) external p3
  return (p4, map showCutEvent cutEvents ++ metaEvents)

convertProgram :: ConvertOptions -> Program -> Either String ConvertResult
convertProgram opts p0 = do
  (p1, prepEvents) <- prepareProgram (coExternal opts) p0
  -- member/2 that the program does not define itself is the Detlog
  -- runtime's member_cp/2 packet, not a library predicate.
  let userMember = M.member ("member", 2) (progPreds p0)
      p = if userMember then p1
          else p1 { progPreds = M.delete ("member", 2) (progPreds p1)
                  , progOrder = filter (/= ("member", 2)) (progOrder p1) }
      defined = Set.fromList (progOrder p) `Set.union` coExternal opts
      effectful = effectfulPreds p
      env0 = Env { envDefined = defined, envEffectful = effectful, envOpts = opts }
  results <- forM (programClauses p) $ \(key, cls) ->
    if Set.member key (coExternal opts) then return ([], []) else convertPred env0 key cls
  let clauses = concatMap fst results
      events = prepEvents ++ concatMap snd results
  return (ConvertResult (programFromClauses clauses) events)

-- ---------------------------------------------------------------------------
-- Code generation monad

data GenSt = GenSt
  { gsNext :: !Int
  , gsAux :: [Clause]       -- reversed
  , gsCount :: !Int
  , gsEvents :: [String]
  , gsBase :: String
  }

newtype G a = G { runG :: GenSt -> Either String (a, GenSt) }

instance Functor G where
  fmap f (G g) = G $ \s -> fmap (\(a, s') -> (f a, s')) (g s)
instance Applicative G where
  pure a = G $ \s -> Right (a, s)
  G f <*> G g = G $ \s -> case f s of
    Left e -> Left e
    Right (h, s') -> fmap (\(a, s'') -> (h a, s'')) (g s')
instance Monad G where
  G g >>= k = G $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> runG (k a) s'

gfail :: String -> G a
gfail e = G $ \_ -> Left e

fresh :: String -> G Term
fresh n = G $ \s -> Right (Var (gsNext s) n, s { gsNext = gsNext s + 1 })

auxName :: G String
auxName = G $ \s -> Right (cpName (gsBase s) ++ "_" ++ show (gsCount s + 1), s { gsCount = gsCount s + 1 })

emitAux :: Clause -> G ()
emitAux c = G $ \s -> Right ((), s { gsAux = c : gsAux s })

event :: String -> G ()
event e = G $ \s -> Right ((), s { gsEvents = e : gsEvents s })

data Env = Env
  { envDefined :: Set.Set PredKey
  , envEffectful :: Set.Set PredKey
  , envOpts :: ConvertOptions
  }

nilT :: Term
nilT = Atom "[]"

list :: [Term] -> Term
list xs = mkList xs nilT

eq :: Term -> Term -> Term
eq a b = Comp "=" [a, b]

ifCommit :: Term -> Term -> Term -> Term
ifCommit c t e = Comp "if_commit" [c, t, e]

-- | A clause whose variables are counted from the term itself.
mkClause :: Term -> Term -> Clause
mkClause h b = Clause h b (maxVarId (Comp "c" [h, b]) + 1)

-- ---------------------------------------------------------------------------
-- Predicates

convertPred :: Env -> PredKey -> [Clause] -> Either String ([Clause], [String])
convertPred env key@(f, n) cls
  | all (\c -> clBody c == Atom "true") cls && not (null cls) = do
      -- Facts: a single choice packet.
      let args = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1] ]
          (rows, _) = foldl (\(acc, off) c -> (acc ++ [list (goalArgs (renameTerm off (clHead c)))], off + clNVars c))
                            ([], n + 2) cls
          pv = Var n "P"
          rv = Var (n + 1) "Rows"
          h = Comp (cpName f) (args ++ [rv])
          b = mkConj [Comp "member_cp" [pv, list rows], Comp "cp_filter" [pv, list args, rv]]
      return ([mkClause h b], ["facts_to_member_cp(" ++ f ++ "/" ++ show n ++ ", "
                                ++ show (length cls) ++ " facts)"])
  | otherwise = do
      parts <- forM (zip [1 :: Int ..] cls) $ \(i, c) -> convertClause env key i c
      let args = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1] ]
          base = n
          rowVars = [ Var (base + i) ("R" ++ show i) | i <- [1 .. length cls] ]
          rv = Var (base + length cls + 1) "Rows"
          calls = [ Comp (cpName f ++ "_c" ++ show i) [list args, r] | (i, r) <- zip [1 :: Int ..] rowVars ]
          h = Comp (cpName f) (args ++ [rv])
          b = case calls of
            [] -> eq rv nilT
            [Comp g [a, _]] -> Comp g [a, rv]
            _ -> mkConj (calls ++ [Comp "rows_concat" [list rowVars, rv]])
          top = mkClause h b
          ev = "predicate_to_packet(" ++ f ++ "/" ++ show n ++ ", " ++ show (length cls) ++ " clauses)"
      return (top : concatMap fst parts, ev : concatMap snd parts)

convertClause :: Env -> PredKey -> Int -> Clause -> Either String ([Clause], [String])
convertClause env (f, _) i (Clause h b _) = do
  let vs = termVarsOrdered (Comp "c" [h, b])
      envT = list vs
      start = maxVarId (Comp "c" [h, b]) + 1
      name = cpName f ++ "_c" ++ show i
      headArgs = list (goalArgs h)
      seen0 = termVarIds h
      gen = do
        argsV <- fresh "Args"
        rowsV <- fresh "Rows"
        body <- case b of
          Atom "true" -> return [eq rowsV (list [headArgs])]
          _ -> do
            envRows <- fresh "Env"
            code <- envCode env seen0 b envT envRows
            return (code ++ [Comp "splice_extend" [envRows, headArgs, envT, rowsV]])
        let cl = mkClause (Comp name [argsV, rowsV])
                   (ifCommit (Comp "copy_term" [argsV, headArgs]) (mkConj body) (eq rowsV nilT))
        return cl
  (cl, st) <- runG gen (GenSt start [] 0 [] (f ++ "_c" ++ show i))
  return (cl : reverse (gsAux st), reverse (gsEvents st))

-- ---------------------------------------------------------------------------
-- Goals

-- | Code computing Out, the rows after Goal, from the single environment row
-- Env (whose components are the clause variables, bound in place).
envCode :: Env -> IS.IntSet -> Term -> Term -> Term -> G [Term]
envCode env seen g envT out = case g of
  Atom "true" -> return [eq out (list [envT])]
  Atom "fail" -> return [eq out nilT]
  Atom "false" -> return [eq out nilT]
  Comp "," _ -> envSeq env seen (conjList g) envT out
  Comp ";" [Comp "->" [c, t], e] -> commitCode c t e
  Comp ";" [Comp "*->" _, _] -> gfail "soft cut (*->) cannot be converted"
  Comp "->" [c, t] -> commitCode c t (Atom "fail")
  Comp "if_commit" [c, t, e] -> commitCode c t e
  Comp "once" [x] -> commitCode x (Atom "true") (Atom "fail")
  Comp "once_det" [x] -> commitCode x (Atom "true") (Atom "fail")
  Comp "ignore" [x] -> commitCode x (Atom "true") (Atom "true")
  Comp ";" [a, b] -> do
    ra <- fresh "Ra"
    rb <- fresh "Rb"
    ca <- rowsCode env seen a (list [envT]) envT ra
    cb <- rowsCode env seen b (list [envT]) envT rb
    event "disjunction_to_rows_concat"
    return (ca ++ cb ++ [Comp "rows_concat" [list [ra, rb], out]])
  Comp "\\+" [x] -> negCode x
  Comp "not" [x] -> negCode x
  Comp "forall" [c, a] -> negCode (Comp "," [c, Comp "\\+" [a]])
  Comp "findall" [t, x, l] -> do
    rg <- fresh "Found"
    ls <- fresh "L"
    cg <- rowsCode env seen x (list [envT]) envT rg
    event "findall_to_packet"
    return (cg ++ [ Comp "splice_extend" [rg, t, envT, ls]
                  , ifCommit (eq l ls) (eq out (list [envT])) (eq out nilT) ])
  Comp "aggregate_all" [Atom "count", x, r] -> do
    rg <- fresh "Found"
    cnt <- fresh "Count"
    cg <- rowsCode env seen x (list [envT]) envT rg
    return (cg ++ [ Comp "length_det" [rg, cnt]
                  , ifCommit (eq r cnt) (eq out (list [envT])) (eq out nilT) ])
  Comp "aggregate_all" [Comp "bag" [t], x, r] -> envCode env seen (Comp "findall" [t, x, r]) envT out
  Comp "decision" [cases, d] -> case termToListStatic cases of
    Just cs -> envCode env seen (foldr (\c e -> case c of
                                                 Comp "-" [cc, bb] -> Comp "if_commit" [cc, bb, e]
                                                 _ -> e) d cs) envT out
    Nothing -> gfail "decision/2 needs a literal list of Condition-Goal pairs"
  Comp "call" (x : extra) -> case x of
    Var _ _ -> gfail ("call/" ++ show (1 + length extra) ++ " on a variable goal cannot be converted statically")
    _ -> case addArgs x extra of
      Just g' -> envCode env seen g' envT out
      Nothing -> gfail "call/N: not callable"
  Var _ _ -> gfail "a variable goal cannot be converted statically"
  _ -> atomicGoal env g envT out
  where
    commitCode c t e
      | detBuiltinConj env c = do
          tc <- envCode env (seen `IS.union` termVarIds c) t envT out
          ec <- envCode env seen e envT out
          return [ifCommit c (mkConj tc) (mkConj ec)]
      | otherwise = do
          rc <- fresh "Cond"
          firstV <- fresh "First"
          rest <- fresh "_"
          cc <- rowsCode env seen c (list [envT]) envT rc
          tc <- rowsCode env (seen `IS.union` termVarIds c) t (list [firstV]) envT out
          ec <- envCode env seen e envT out
          event "if_then_else_to_if_commit"
          return (cc ++ [ifCommit (eq rc (mkList [firstV] rest)) (mkConj tc) (mkConj ec)])
    negCode x
      | detBuiltinConj env x = return [ifCommit x (eq out nilT) (eq out (list [envT]))]
      | otherwise = do
          rg <- fresh "Found"
          cg <- rowsCode env seen x (list [envT]) envT rg
          return (cg ++ [ifCommit (eq rg nilT) (eq out (list [envT])) (eq out nilT)])

termToListStatic :: Term -> Maybe [Term]
termToListStatic (Atom "[]") = Just []
termToListStatic (Comp "." [h, t]) = (h :) <$> termToListStatic t
termToListStatic _ = Nothing

-- | A conjunction of deterministic built-ins (it can be a condition of
-- if_commit/3 directly).
detBuiltinConj :: Env -> Term -> Bool
detBuiltinConj env g = all isDetB (conjList g)
  where
    isDetB x = case goalKey x of
      Just k -> isBuiltinKey k && not (Set.member k (envDefined env))
                && k `notElem` nondetBuiltinKeys && k /= ("atom_concat", 3)
      Nothing -> False

-- | A conjunction in one environment.
envSeq :: Env -> IS.IntSet -> [Term] -> Term -> Term -> G [Term]
envSeq _ _ [] envT out = return [eq out (list [envT])]
envSeq env seen [g] envT out = envCode env seen g envT out
envSeq env seen gs envT out
  -- leading deterministic built-ins bind the environment in place
  | (bs@(_ : _), rest) <- span (detBuiltinConj env) gs = do
      rc <- envSeq env (seen `IS.union` IS.unions (map termVarIds bs)) rest envT out
      return [ifCommit (mkConj bs) (mkConj rc) (eq out nilT)]
  | coSpliceEarly (envOpts env)
  , (grp@(_ : _ : _), rest) <- spliceGroup env gs = do
      r <- if null rest then return out else fresh "Spliced"
      sc <- spliceCode env seen grp envT r
      rc <- if null rest then return [] else
              rowsCode env (seen `IS.union` IS.unions (map termVarIds grp)) (mkConj rest) r envT out
      return (sc ++ rc)
  | (g : rest) <- gs = do
      r1 <- fresh "R"
      c1 <- envCode env seen g envT r1
      cr <- rowsCode env (seen `IS.union` termVarIds g) (mkConj rest) r1 envT out
      return (c1 ++ cr)
  | otherwise = return [eq out (list [envT])]

-- | Code mapping a list of rows to the rows after Goal: an auxiliary
-- predicate iterates over the rows (first argument [] or [_|_]).
rowsCode :: Env -> IS.IntSet -> Term -> Term -> Term -> Term -> G [Term]
rowsCode env seen g rin envT out = case g of
  Atom "true" -> return [eq out rin]
  _ -> do
    name <- auxName
    rowV <- fresh "Row"
    rsV <- fresh "Rows"
    o1 <- fresh "Out1"
    o2 <- fresh "Out2"
    outV <- fresh "Out"
    body <- envCode env seen g envT o1
    emitAux (mkClause (Comp name [nilT, nilT]) (Atom "true"))
    emitAux (mkClause (Comp name [mkList [rowV] rsV, outV])
               (mkConj ([Comp "copy_term" [rowV, envT]] ++ body
                        ++ [Comp name [rsV, o2], Comp "rows_concat" [list [o1, o2], outV]])))
    return [Comp name [rin, out]]

-- | A single goal that is not a control construct.
atomicGoal :: Env -> Term -> Term -> Term -> G [Term]
atomicGoal env g envT out = case goalKey g of
  Nothing -> gfail ("not a callable goal: " ++ showTermQ g)
  Just key@(f, n)
    | Set.member key (envDefined env) -> do
        qr <- fresh "Packet"
        return [ Comp (cpName f) (goalArgs g ++ [qr])
               , Comp "splice_extend" [qr, envT, list (goalArgs g), out] ]
    | key == ("member", 2) -> do
        p <- fresh "P"
        pr <- fresh "PRows"
        let [x, l] = goalArgs g
        event "member_to_member_cp"
        return [ Comp "member_cp" [p, l], Comp "cp_rows" [p, pr]
               , Comp "splice_extend" [pr, envT, list [x], out] ]
    | key == ("between", 3) -> do
        p <- fresh "P"
        pr <- fresh "PRows"
        let [lo, hi, x] = goalArgs g
        event "between_to_between_cp"
        return [ Comp "between_cp" [lo, hi, p], Comp "cp_rows" [p, pr]
               , Comp "splice_extend" [pr, envT, list [x], out] ]
    | key == ("length", 2) ->
        return [ifCommit (Comp "length_det" (goalArgs g)) (eq out (list [envT])) (eq out nilT)]
    | key `elem` nondetBuiltinKeys || key == ("atom_concat", 3) -> do
        br <- fresh "BRows"
        return [ Comp "builtin_rows" [g, br], Comp "splice_extend" [br, envT, list [g], out] ]
    | isBuiltinKey key -> return [ifCommit g (eq out (list [envT])) (eq out nilT)]
    | key `elem` controlKeys -> gfail ("cannot convert control construct " ++ f ++ "/" ++ show n)
    | otherwise -> gfail ("unknown procedure " ++ f ++ "/" ++ show n)

-- | A leading run of independent, effect-free generators.
spliceGroup :: Env -> [Term] -> ([Term], [Term])
spliceGroup env = go IS.empty []
  where
    go _ acc [] = (reverse acc, [])
    go used acc (g : gs)
      | isGenerator g && IS.null (IS.intersection used (termVarIds g)) =
          go (used `IS.union` termVarIds g) (g : acc) gs
      | otherwise = (reverse acc, g : gs)
    isGenerator g = case goalKey g of
      Just k | Set.member k (envDefined env) -> not (Set.member k (envEffectful env))
             | k == ("member", 2) || k == ("between", 3) -> True
      _ -> False

-- | Compute each generator's packet once and splice the packets.
spliceCode :: Env -> IS.IntSet -> [Term] -> Term -> Term -> G [Term]
spliceCode env seen grp envT out = do
  parts <- forM grp $ \g -> do
    p <- fresh "P"
    case goalKey g of
      Just k@(f, _) | Set.member k (envDefined env) ->
        return ([Comp (cpName f) (goalArgs g ++ [p])], p, list (goalArgs g))
      Just ("member", 2) -> do
        m <- fresh "M"
        let [x, l] = goalArgs g
        return ([Comp "member_cp" [m, l], Comp "cp_rows" [m, p]], p, list [x])
      Just ("between", 3) -> do
        m <- fresh "M"
        let [lo, hi, x] = goalArgs g
        return ([Comp "between_cp" [lo, hi, m], Comp "cp_rows" [m, p]], p, list [x])
      _ -> gfail "internal: not a generator"
  combos <- fresh "Combos"
  let pats = list [ pat | (_, _, pat) <- parts ]
      finalG = [ Comp "splice" [list [ Comp "cp" [p] | (_, p, _) <- parts ], combos]
               , Comp "splice_extend" [combos, envT, pats, out] ]
      -- compute packets left to right; stop as soon as one is empty
      chain [] = finalG
      chain ((code, p, _) : more) = code ++ [ifCommit (eq p nilT) (eq out nilT) (mkConj (chain more))]
      needsGuard = not (IS.null (IS.intersection seen (IS.unions (map termVarIds grp))))
  event ("splice_early(" ++ intercalate ", " [ showTermQ g | g <- grp ] ++ ")")
  if needsGuard
    then do
      seqCode <- envSeqNoSplice env seen grp envT out
      return [ifCommit (Comp "splice_safe" [pats]) (mkConj (chain parts)) (mkConj seqCode)]
    else return (chain parts)

envSeqNoSplice :: Env -> IS.IntSet -> [Term] -> Term -> Term -> G [Term]
envSeqNoSplice env = envSeq env { envOpts = (envOpts env) { coSpliceEarly = False } }

-- ---------------------------------------------------------------------------
-- Analyses

-- | Predicates that (transitively) write output.
effectfulPreds :: Program -> Set.Set PredKey
effectfulPreds p = fixp direct
  where
    calls = M.fromList [ (k, concatMap (bodyCalls . clBody) cs) | (k, cs) <- programClauses p ]
    direct = Set.fromList [ k | (k, cs) <- M.toList calls, any (`elem` effectKeys) cs ]
    fixp s = let s' = s `Set.union` Set.fromList [ k | (k, cs) <- M.toList calls, any (`Set.member` s) cs ]
             in if s' == s then s else fixp s'

bodyCalls :: Term -> [PredKey]
bodyCalls t = case t of
  Comp op [a, b] | op `elem` [",", ";", "->", "*->"] -> bodyCalls a ++ bodyCalls b
  Comp f [a] | f `elem` ["\\+", "not", "once", "once_det", "ignore", "call"] -> bodyCalls a
  Comp "if_commit" [a, b, c] -> bodyCalls a ++ bodyCalls b ++ bodyCalls c
  Comp "findall" [_, g, _] -> bodyCalls g
  Comp "forall" [a, b] -> bodyCalls a ++ bodyCalls b
  Comp "aggregate_all" [_, g, _] -> bodyCalls g
  Comp "call" (g : extra) | Just g' <- addArgs g extra, not (isVar g) -> bodyCalls g'
  _ -> maybe [] (: []) (goalKey t)

-- | Keep the program's own predicates and the library predicates they use.
pruneUnused :: Set.Set PredKey -> Set.Set PredKey -> Program -> Program
pruneUnused own _ p =
  let calls k = concatMap (bodyCalls . clBody) (M.findWithDefault [] k (progPreds p))
      reach s = let s' = s `Set.union` Set.fromList [ c | k <- Set.toList s, c <- calls k
                                                         , M.member c (progPreds p) ]
                in if s' == s then s else reach s'
      keep = reach (Set.filter (`M.member` progPreds p) own `Set.union` specialised)
      specialised = Set.fromList [ k | k@(f, _) <- progOrder p, "__m" `isInfix` f, Set.member k ownCalled ]
      ownCalled = Set.fromList (concatMap (\k -> calls k) (Set.toList own))
  in p { progPreds = M.filterWithKey (\k _ -> Set.member k keep) (progPreds p)
       , progOrder = filter (`Set.member` keep) (progOrder p) }
  where
    isInfix needle hay = any (startsWith needle) (tails' hay)
    startsWith a b = take (length a) b == a
    tails' [] = [[]]
    tails' xs@(_ : rest) = xs : tails' rest

-- ---------------------------------------------------------------------------
-- Closure specialisation: maplist(succ, L, R) calls a copy of maplist/3 in
-- which call(G, X, Y) has become succ(X, Y), so no meta-call remains.

specialiseMeta :: Program -> Either String (Program, [String])
specialiseMeta p0 = loop p0 M.empty [] (progOrder p0)
  where
    loop p _ evs [] = Right (p, reverse evs)
    loop p memo evs (k : ks) = do
      let cls = M.findWithDefault [] k (progPreds p)
      (cls', memo', p', newKeys, evs') <-
        foldM (\(acc, m, pr, nk, ev) c -> do
                  (c', m2, pr2, nk2, ev2) <- specClause pr m c
                  return (acc ++ [c'], m2, pr2, nk ++ nk2, ev ++ ev2))
              ([], memo, p, [], []) cls
      let p'' = p' { progPreds = M.insert k cls' (progPreds p') }
      loop p'' memo' (reverse evs' ++ evs) (ks ++ newKeys)

    specClause p memo (Clause h b nv) = do
      (b', memo', p', newKeys, evs, nv') <- specBody p memo nv b
      return (Clause h b' nv', memo', p', newKeys, evs)

    specBody p memo nv t = case t of
      Comp op [a, b] | op `elem` [",", ";", "->", "*->"] -> do
        (a', m1, p1, k1, e1, nv1) <- specBody p memo nv a
        (b', m2, p2, k2, e2, nv2) <- specBody p1 m1 nv1 b
        return (Comp op [a', b'], m2, p2, k1 ++ k2, e1 ++ e2, nv2)
      Comp "if_commit" [a, b, c] -> do
        (a', m1, p1, k1, e1, nv1) <- specBody p memo nv a
        (b', m2, p2, k2, e2, nv2) <- specBody p1 m1 nv1 b
        (c', m3, p3, k3, e3, nv3) <- specBody p2 m2 nv2 c
        return (Comp "if_commit" [a', b', c'], m3, p3, k1 ++ k2 ++ k3, e1 ++ e2 ++ e3, nv3)
      Comp f [a] | f `elem` ["\\+", "not", "once", "once_det", "ignore"] -> do
        (a', m1, p1, k1, e1, nv1) <- specBody p memo nv a
        return (Comp f [a'], m1, p1, k1, e1, nv1)
      Comp "findall" [x, g, l] -> do
        (g', m1, p1, k1, e1, nv1) <- specBody p memo nv g
        return (Comp "findall" [x, g', l], m1, p1, k1, e1, nv1)
      Comp "call" (g : extra) | not (isVar g), Just g' <- addArgs g extra ->
        specBody p memo nv g'
      _ -> case goalKey t of
        Just key | Just pos <- metaPosition p key, isJust (closureAt t pos) -> do
          let Just clo = closureAt t pos
          specialiseCall p memo nv key pos clo t
        _ -> return (t, memo, p, [], [], nv)

    metaSet = metaPositions p0
    metaPosition _ key =
      case [ i | i <- [0 .. snd key - 1], Set.member (key, i) metaSet ] of
        (i : _) -> Just i
        [] -> Nothing

    closureAt t pos = case goalArgs t !! pos of
      Var _ _ -> Nothing
      c | isCallable c -> Just c
      _ -> Nothing

    specialiseCall p memo nv key@(f, n) pos clo t = do
      let freeVs = termVarsOrdered clo
          canon = showAnswerTerm (Comp "k" [Atom f, Int (fromIntegral n), Int (fromIntegral pos), clo])
          otherArgs = [ a | (j, a) <- zip [0 ..] (goalArgs t), j /= pos ]
      case M.lookup canon memo of
        Just name -> return (Comp name (freeVs ++ otherArgs), memo, p, [], [], nv)
        Nothing | M.size memo >= 500 -> Left "closure specialisation did not reach a fixpoint (closures keep growing)"
        Nothing -> do
          let name = f ++ "__m" ++ show (M.size memo + 1)
              newKey = (name, length freeVs + n - 1)
              memo' = M.insert canon name memo
              cls = M.findWithDefault [] key (progPreds p)
          cls' <- forM cls $ \(Clause h b cnv) -> do
            let g = goalArgs h !! pos
                (cloR, cloVars) = renameClosure cnv clo
                sub = substVar g cloR
                h' = Comp name (cloVars ++ [ sub a | (j, a) <- zip [0 ..] (goalArgs h), j /= pos ])
                b' = sub b
            return (Clause h' b' (cnv + length cloVars + maxVarId clo + 2))
          let p' = p { progPreds = M.insert newKey cls' (progPreds p)
                     , progOrder = progOrder p ++ [newKey] }
          return ( Comp name (freeVs ++ otherArgs), memo', p', [newKey]
                 , ["closure_specialised(" ++ f ++ "/" ++ show n ++ ", " ++ showTermQ clo ++ ") as " ++ name], nv)

    -- rename the closure's variables into the clause's variable space
    renameClosure cnv clo =
      let c' = renameTerm cnv clo
      in (c', termVarsOrdered c')

    substVar v by t = case t of
      Var _ _ | t == v -> by
      Comp "call" (g : extra) | g == v, Just g' <- addArgs by extra -> g'
      Comp fn as -> Comp fn (map (substVar v by) as)
      _ -> t

-- | (Predicate, argument) pairs whose argument is called as a closure:
-- directly by call/N, or by being passed to such a position.
metaPositions :: Program -> Set.Set (PredKey, Int)
metaPositions p = fixp direct
  where
    clauses = programClauses p
    headVarPos c = [ (i, v) | (i, v@(Var _ _)) <- zip [0 ..] (goalArgs (clHead c)) ]
    direct = Set.fromList
      [ (k, i) | (k, cs) <- clauses, c <- cs, (i, v) <- headVarPos c, calledIn v (clBody c) ]
    fixp s =
      let s' = s `Set.union` Set.fromList
                 [ (k, i) | (k, cs) <- clauses, c <- cs, (i, v) <- headVarPos c
                          , (q, j) <- passedTo v (clBody c), Set.member (q, j) s ]
      in if s' == s then s else fixp s'
    calledIn v t = case t of
      Comp "call" (g : _) | g == v -> True
      Comp _ as -> any (calledIn v) as
      _ -> False
    passedTo v t = case t of
      Comp op [a, b] | op `elem` [",", ";", "->", "*->"] -> passedTo v a ++ passedTo v b
      Comp "if_commit" as -> concatMap (passedTo v) as
      Comp f [a] | f `elem` ["\\+", "not", "once", "once_det", "ignore"] -> passedTo v a
      Comp "findall" [_, g, _] -> passedTo v g
      _ -> case goalKey t of
        Just q -> [ (q, j) | (j, a) <- zip [0 ..] (goalArgs t), a == v ]
        Nothing -> []
