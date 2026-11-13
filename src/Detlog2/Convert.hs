-- | The Detlog converter: Prolog with choicepoints and cuts becomes
-- deterministic code that combines alternatives with splices, together with
-- a proof of every rewrite.
--
-- After cut elimination ("Detlog2.CutElim") and closure specialisation,
-- every predicate @p/n@ becomes a deterministic predicate
--
-- > p__cp(A1, ..., An, Packet)
--
-- which succeeds exactly once.  @Packet@ is the answer packet of the
-- original predicate: in Prolog order, one row @[A1', ..., An']@ per answer
-- (duplicates included) and one item @out(Text)@ for each piece of output,
-- placed where Prolog would write it.  Inside a clause, each goal maps a
-- packet of environment rows to a new packet:
--
--   * facts become a choice packet: @member_cp(P, [[a],[b]]), cp_filter(P, Args, Rows)@;
--   * @member/2@ and @between/3@ become @member_cp/2@ / @between_cp/3@ packets;
--   * a call to a user predicate asks for its packet and splices it into the
--     environment with @splice_extend/4@;
--   * independent, output-free generators are computed once each and
--     combined with @splice/2@ (a deterministic Cartesian product);
--   * disjunction concatenates packets (@rows_concat/2@);
--   * if-then-else, once/1 and \+/1 become @if_commit/3@ decisions;
--   * output built-ins become @effect_text/2@ items.
--
-- Every piece of generated code is justified by a proof step: a derivation
-- node naming the rule, the source goal, and the code it produced.
-- "Detlog2.Proof" checks the steps independently of this module.
module Detlog2.Convert
  ( ConvertOptions(..)
  , defaultConvertOptions
  , ConvertResult(..)
  , convertProgram
  , cpName
  , addQueryClause
  , prepareProgram
  , bodyCalls
  ) where

import Control.Monad (foldM, forM)
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
  , coRoots :: Maybe [PredKey]     -- ^ convert only what these reach (Nothing: everything)
  }

defaultConvertOptions :: ConvertOptions
defaultConvertOptions = ConvertOptions True Set.empty Nothing

data ConvertResult = ConvertResult
  { crProgram :: Program        -- ^ the deterministic Detlog program
  , crEvents :: [String]        -- ^ what was converted, and how
  , crProof :: [Term]           -- ^ proof steps, checked by Detlog2.Proof
  }

cpName :: String -> String
cpName f = f ++ "__cp"

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
prepareProgram :: Set.Set PredKey -> Program -> Either String (Program, [String], [Term])
prepareProgram external p0 = do
  (p1, cutEvents) <- case eliminateCuts p0 of
    Left bad -> Left ("cannot convert these cuts:\n  " ++ intercalate "\n  " (map showCutEvent bad))
    Right r -> Right r
  let p2 = withPrelude p1
  (p3, metaEvents, metaSteps) <- specialiseMeta p2
  let p4 = pruneUnused (Set.fromList (progOrder p0)) external p3
      cutSteps = [ Comp "cut_elim" [keyT k] | k <- progOrder p0
                 , any (hasCut . clBody) (M.findWithDefault [] k (progPreds p0)) ]
  return (p4, map showCutEvent cutEvents ++ metaEvents, cutSteps ++ metaSteps)

keyT :: PredKey -> Term
keyT (f, n) = Comp "/" [Atom f, Int (fromIntegral n)]

convertProgram :: ConvertOptions -> Program -> Either String ConvertResult
convertProgram opts p0 = do
  let p0' = maybe p0 (\roots -> restrictTo roots p0) (coRoots opts)
  (p1, prepEvents, prepSteps) <- prepareProgram (coExternal opts) p0'
  -- member/2 that the program does not define itself is the Detlog
  -- runtime's member_cp/2 packet, not a library predicate.
  let userMember = M.member ("member", 2) (progPreds p0')
      p = if userMember then p1
          else p1 { progPreds = M.delete ("member", 2) (progPreds p1)
                  , progOrder = filter (/= ("member", 2)) (progOrder p1) }
      defined = Set.fromList (progOrder p) `Set.union` coExternal opts
      -- predicates answered by memo tables are treated as writing output
      env0 = Env { envDefined = defined, envEffectful = effectfulPreds p `Set.union` coExternal opts
                 , envOpts = opts }
  results <- forM (programClauses p) $ \(key, cls) ->
    if Set.member key (coExternal opts) then return ([], [], []) else convertPred env0 key cls
  let clauses = concat [ c | (c, _, _) <- results ]
      events = prepEvents ++ concat [ e | (_, e, _) <- results ]
      steps = prepSteps ++ concat [ s | (_, _, s) <- results ]
  return (ConvertResult (programFromClauses clauses) events steps)

-- ---------------------------------------------------------------------------
-- Code generation monad

data GenSt = GenSt
  { gsNext :: !Int
  , gsAux :: [(Clause, Clause, Term)]   -- reversed: the two clauses and the body derivation
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

emitAux :: Clause -> Clause -> Term -> G ()
emitAux c1 c2 d = G $ \s -> Right ((), s { gsAux = (c1, c2, d) : gsAux s })

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

-- | A derivation node: d(Rule, Source, Env, Out, Generated, Subderivations).
dnode :: String -> Term -> Term -> Term -> [Term] -> [Term] -> Term
dnode r src env out gen subs = Comp "d" [Atom r, src, env, out, list gen, list subs]

genOf :: Term -> [Term]
genOf (Comp "d" [_, _, _, _, gs, _]) = maybe [] id (staticList gs)
genOf _ = []

staticList :: Term -> Maybe [Term]
staticList (Atom "[]") = Just []
staticList (Comp "." [h, t]) = (h :) <$> staticList t
staticList _ = Nothing

-- | A clause whose variables are counted from the term itself.
mkClause :: Term -> Term -> Clause
mkClause h b = Clause h b (maxVarId (Comp "c" [h, b]) + 1)

clauseT :: Clause -> Term
clauseT (Clause h b _) = Comp ":-" [h, b]

-- ---------------------------------------------------------------------------
-- Predicates

convertPred :: Env -> PredKey -> [Clause] -> Either String ([Clause], [String], [Term])
convertPred env key@(f, n) cls
  | all (\c -> clBody c == Atom "true") cls && not (null cls) = do
      let args = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1] ]
          (rows, _) = foldl (\(acc, off) c -> (acc ++ [list (goalArgs (renameTerm off (clHead c)))], off + clNVars c))
                            ([], n + 2) cls
          pv = Var n "P"
          rv = Var (n + 1) "Rows"
          h = Comp (cpName f) (args ++ [rv])
          b = mkConj [Comp "member_cp" [pv, list rows], Comp "cp_filter" [pv, list args, rv]]
          cl = mkClause h b
      return ( [cl]
             , ["facts_to_member_cp(" ++ f ++ "/" ++ show n ++ ", " ++ show (length cls) ++ " facts)"]
             , [Comp "facts_packet" [keyT key, clauseT cl]] )
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
          step = Comp "pred_packet" [keyT key, Int (fromIntegral (length cls)), clauseT top]
      return ( top : concat [ c | (c, _, _) <- parts ]
             , ev : concat [ e | (_, e, _) <- parts ]
             , step : concat [ s | (_, _, s) <- parts ] )

convertClause :: Env -> PredKey -> Int -> Clause -> Either String ([Clause], [String], [Term])
convertClause env key@(f, _) i src@(Clause h b _) = do
  let vs = termVarsOrdered (Comp "c" [h, b])
      envT = list vs
      start = maxVarId (Comp "c" [h, b]) + 1
      name = cpName f ++ "_c" ++ show i
      headArgs = list (goalArgs h)
      gen = do
        argsV <- fresh "Args"
        rowsV <- fresh "Rows"
        (body, deriv) <- case b of
          Atom "true" -> return ([eq rowsV (list [headArgs])], Atom "none")
          _ -> do
            envRows <- fresh "Env"
            d <- envCode env b envT envRows
            return (genOf d ++ [Comp "splice_extend" [envRows, headArgs, envT, rowsV]], d)
        let cl = mkClause (Comp name [argsV, rowsV])
                   (ifCommit (Comp "copy_term" [argsV, headArgs]) (mkConj body) (eq rowsV nilT))
        return (cl, deriv)
  ((cl, deriv), st) <- runG gen (GenSt start [] 0 [] (f ++ "_c" ++ show i))
  let auxes = reverse (gsAux st)
      auxSteps = [ Comp "aux" [ Atom (auxNameOf c1), envT, list [clauseT c1, clauseT c2], d ]
                 | (c1, c2, d) <- auxes ]
      step = Comp "clause_packet" [keyT key, Int (fromIntegral i), clauseT src, clauseT cl, deriv]
  return ( cl : concat [ [c1, c2] | (c1, c2, _) <- auxes ]
         , reverse (gsEvents st)
         , step : auxSteps )
  where
    auxNameOf c = maybe "" fst (goalKey (clHead c))

-- ---------------------------------------------------------------------------
-- Goals.  Each function returns a derivation node whose generated code
-- computes Out from the single environment row Env (the clause variables).

envCode :: Env -> Term -> Term -> Term -> G Term
envCode env g envT out = case g of
  Atom "true" -> return (dnode "true" g envT out [eq out (list [envT])] [])
  Atom "fail" -> return (dnode "fail" g envT out [eq out nilT] [])
  Atom "false" -> return (dnode "fail" g envT out [eq out nilT] [])
  Comp "," _ -> envSeq env g envT out
  Comp ";" [Comp "->" [c, t], e] -> commitCode g c t e
  Comp ";" [Comp "*->" _, _] -> gfail "soft cut (*->) cannot be converted"
  Comp "->" [c, t] -> commitCode g c t (Atom "fail")
  Comp "if_commit" [c, t, e] -> commitCode g c t e
  Comp "once" [x] -> commitCode g x (Atom "true") (Atom "fail")
  Comp "once_det" [x] -> commitCode g x (Atom "true") (Atom "fail")
  Comp "ignore" [x] -> commitCode g x (Atom "true") (Atom "true")
  Comp ";" [a, b] -> do
    ra <- fresh "Ra"
    rb <- fresh "Rb"
    da <- rowsCode env a (list [envT]) envT ra
    db <- rowsCode env b (list [envT]) envT rb
    event "disjunction_to_rows_concat"
    return (dnode "disj" g envT out (genOf da ++ genOf db ++ [Comp "rows_concat" [list [ra, rb], out]]) [da, db])
  Comp "\\+" [x] -> negCode x
  Comp "not" [x] -> negCode x
  Comp "forall" [c, a] -> rewriteTo (Comp "\\+" [Comp "," [c, Comp "\\+" [a]]])
  Comp "findall" [t, x, l] -> do
    rg <- fresh "Found"
    outs <- fresh "Outs"
    rows0 <- fresh "Rows0"
    ls <- fresh "L"
    dx <- rowsCode env x (list [envT]) envT rg
    event "findall_to_packet"
    return (dnode "findall" g envT out
              (genOf dx ++ [ Comp "packet_split" [rg, outs, rows0]
                           , Comp "splice_extend" [rows0, t, envT, ls]
                           , ifCommit (eq l ls) (Comp "rows_concat" [list [outs, list [envT]], out]) (eq out outs) ])
              [dx])
  Comp "aggregate_all" [Atom "count", x, r] -> do
    rg <- fresh "Found"
    outs <- fresh "Outs"
    rows0 <- fresh "Rows0"
    cnt <- fresh "Count"
    dx <- rowsCode env x (list [envT]) envT rg
    return (dnode "count" g envT out
              (genOf dx ++ [ Comp "packet_split" [rg, outs, rows0]
                           , Comp "length_det" [rows0, cnt]
                           , ifCommit (eq r cnt) (Comp "rows_concat" [list [outs, list [envT]], out]) (eq out outs) ])
              [dx])
  Comp "aggregate_all" [Comp "bag" [t], x, r] -> rewriteTo (Comp "findall" [t, x, r])
  Comp "decision" [cases, d] -> case staticList cases of
    Just cs | all isPair cs -> rewriteTo (foldr (\c e -> case c of
                                                           Comp "-" [cc, bb] -> Comp "if_commit" [cc, bb, e]
                                                           _ -> e) d cs)
    _ -> gfail "decision/2 needs a literal list of Condition-Goal pairs"
  Comp "call" (x : extra) -> case x of
    Var _ _ -> gfail ("call/" ++ show (1 + length extra) ++ " on a variable goal cannot be converted statically")
    _ -> case addArgs x extra of
      Just g' -> rewriteTo g'
      Nothing -> gfail "call/N: not callable"
  Var _ _ -> gfail "a variable goal cannot be converted statically"
  _ -> atomicGoal env g envT out
  where
    isPair (Comp "-" [_, _]) = True
    isPair _ = False
    rewriteTo g' = do
      d <- envCode env g' envT out
      return (dnode "rewrite" g envT out (genOf d) [d])
    commitCode src c t e
      | detBuiltinConj env c = do
          dt <- envCode env t envT out
          de <- envCode env e envT out
          return (dnode "ite_det" src envT out [ifCommit c (mkConj (genOf dt)) (mkConj (genOf de))] [dt, de])
      | otherwise = do
          rc <- fresh "Cond"
          pre <- fresh "Pre"
          res <- fresh "Res"
          firstV <- fresh "First"
          ot <- fresh "OutT"
          oe <- fresh "OutE"
          dc <- rowsCode env c (list [envT]) envT rc
          dt <- rowsCode env t (list [firstV]) envT ot
          de <- envCode env e envT oe
          event "if_then_else_to_if_commit"
          return (dnode "ite" src envT out
                    (genOf dc ++
                     [ Comp "packet_first" [rc, pre, res]
                     , ifCommit (eq res (Atom "none"))
                                (mkConj (genOf de ++ [Comp "rows_concat" [list [pre, oe], out]]))
                                (mkConj ([eq res (Comp "first" [firstV])] ++ genOf dt
                                         ++ [Comp "rows_concat" [list [pre, ot], out]])) ])
                    [dc, dt, de])
    negCode x
      | detBuiltinConj env x =
          return (dnode "neg_det" g envT out [ifCommit x (eq out nilT) (eq out (list [envT]))] [])
      | otherwise = do
          rg <- fresh "Found"
          pre <- fresh "Pre"
          res <- fresh "Res"
          dx <- rowsCode env x (list [envT]) envT rg
          return (dnode "neg" g envT out
                    (genOf dx ++ [ Comp "packet_first" [rg, pre, res]
                                 , ifCommit (eq res (Atom "none"))
                                            (Comp "rows_concat" [list [pre, list [envT]], out])
                                            (eq out pre) ])
                    [dx])

-- | A conjunction of deterministic, output-free built-ins (it can be a
-- condition of if_commit/3 directly).
detBuiltinConj :: Env -> Term -> Bool
detBuiltinConj env g = all isDetB (conjList g)
  where
    isDetB x = case goalKey x of
      Just k -> isBuiltinKey k && not (Set.member k (envDefined env))
                && k `notElem` nondetBuiltinKeys && k /= ("atom_concat", 3)
                && k `notElem` effectKeys
      Nothing -> False

-- | A conjunction in one environment.
envSeq :: Env -> Term -> Term -> Term -> G Term
envSeq env g envT out = case conjList g of
  [] -> envCode env (Atom "true") envT out
  [x] -> envCode env x envT out
  gs
    -- leading deterministic built-ins bind the environment in place
    | (bs@(_ : _), rest) <- span (detBuiltinConj env) gs -> do
        dr <- envSeq env (mkConj rest) envT out
        return (dnode "det_prefix" g envT out [ifCommit (mkConj bs) (mkConj (genOf dr)) (eq out nilT)] [dr])
    | coSpliceEarly (envOpts env)
    , (grp@(_ : _ : _), rest) <- spliceGroup env gs -> do
        r <- if null rest then return out else fresh "Spliced"
        (chain, dseq) <- spliceCode env grp envT r
        case rest of
          [] -> return (dnode "splice" g envT out chain [dseq])
          _ -> do
            drest <- rowsCode env (mkConj rest) r envT out
            return (dnode "splice" g envT out (chain ++ genOf drest) [dseq, drest])
    | (x : rest) <- gs -> do
        r1 <- fresh "R"
        d1 <- envCode env x envT r1
        dr <- rowsCode env (mkConj rest) r1 envT out
        return (dnode "seq" g envT out (genOf d1 ++ genOf dr) [d1, dr])
    | otherwise -> gfail "internal: empty conjunction"

-- | Code mapping a packet of rows to the packet after Goal: an auxiliary
-- predicate iterates over the packet (first argument [] or [_|_]); output
-- items pass through unchanged.
rowsCode :: Env -> Term -> Term -> Term -> Term -> G Term
rowsCode env g rin envT out = case g of
  Atom "true" -> return (dnode "rows_true" g rin out [eq out rin] [])
  _ -> do
    name <- auxName
    rowV <- fresh "Row"
    rsV <- fresh "Rows"
    o1 <- fresh "Out1"
    o2 <- fresh "Out2"
    outV <- fresh "Out"
    txt <- fresh "Text"
    d <- envCode env g envT o1
    let c1 = mkClause (Comp name [nilT, nilT]) (Atom "true")
        c2 = mkClause (Comp name [mkList [rowV] rsV, outV])
               (mkConj [ ifCommit (eq rowV (Comp "out" [txt]))
                                  (eq o1 (list [Comp "out" [txt]]))
                                  (mkConj (Comp "copy_term" [rowV, envT] : genOf d))
                       , Comp name [rsV, o2]
                       , Comp "rows_concat" [list [o1, o2], outV] ])
    emitAux c1 c2 d
    return (dnode "rows" g rin out [Comp name [rin, out]] [Atom name])

-- | A single goal that is not a control construct.
atomicGoal :: Env -> Term -> Term -> Term -> G Term
atomicGoal env g envT out = case goalKey g of
  Nothing -> gfail ("not a callable goal: " ++ showTermQ g)
  Just key@(f, n)
    | Set.member key (envDefined env) -> do
        qr <- fresh "Packet"
        return (dnode "call" g envT out
                  [ Comp (cpName f) (goalArgs g ++ [qr])
                  , Comp "splice_extend" [qr, envT, list (goalArgs g), out] ] [])
    | key == ("member", 2) -> do
        p <- fresh "P"
        pr <- fresh "PRows"
        let [x, l] = goalArgs g
        event "member_to_member_cp"
        return (dnode "member_cp" g envT out
                  [ Comp "member_cp" [p, l], Comp "cp_rows" [p, pr]
                  , Comp "splice_extend" [pr, envT, list [x], out] ] [])
    | key == ("between", 3) -> do
        p <- fresh "P"
        pr <- fresh "PRows"
        let [lo, hi, x] = goalArgs g
        event "between_to_between_cp"
        return (dnode "between_cp" g envT out
                  [ Comp "between_cp" [lo, hi, p], Comp "cp_rows" [p, pr]
                  , Comp "splice_extend" [pr, envT, list [x], out] ] [])
    | key == ("length", 2) ->
        return (dnode "length_det" g envT out
                  [ifCommit (Comp "length_det" (goalArgs g)) (eq out (list [envT])) (eq out nilT)] [])
    | key `elem` nondetBuiltinKeys || key == ("atom_concat", 3) -> do
        br <- fresh "BRows"
        return (dnode "builtin_rows" g envT out
                  [Comp "builtin_rows" [g, br], Comp "splice_extend" [br, envT, list [g], out]] [])
    | key `elem` effectKeys -> do
        t <- fresh "Text"
        return (dnode "effect" g envT out
                  [Comp "effect_text" [g, t], eq out (list [Comp "out" [t], envT])] [])
    | isBuiltinKey key ->
        return (dnode "det" g envT out [ifCommit g (eq out (list [envT])) (eq out nilT)] [])
    | key `elem` controlKeys -> gfail ("cannot convert control construct " ++ f ++ "/" ++ show n)
    | otherwise -> gfail ("unknown procedure " ++ f ++ "/" ++ show n)

-- | A leading run of independent, output-free generators.
spliceGroup :: Env -> [Term] -> ([Term], [Term])
spliceGroup env = go [] []
  where
    go _ acc [] = (reverse acc, [])
    go used acc (g : gs)
      | isGenerator g && all (`notElem` used) (varIds g) = go (used ++ varIds g) (g : acc) gs
      | otherwise = (reverse acc, g : gs)
    varIds t = [ i | Var i _ <- termVarsOrdered t ]
    isGenerator g = case goalKey g of
      Just k | Set.member k (envDefined env) -> not (Set.member k (envEffectful env))
             | k == ("member", 2) || k == ("between", 3) -> True
      _ -> False

-- | Compute each generator's packet once and splice the packets, guarded by
-- splice_safe/1 (the generators share no unbound variable at run time); the
-- sequential code is the fallback.
spliceCode :: Env -> [Term] -> Term -> Term -> G ([Term], Term)
spliceCode env grp envT out = do
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
      chain [] = finalG
      chain ((code, p, _) : more) = code ++ [ifCommit (eq p nilT) (eq out nilT) (mkConj (chain more))]
  event ("splice_early(" ++ intercalate ", " [ showSourceTerm g | g <- grp ] ++ ")")
  dseq <- envSeq env { envOpts = (envOpts env) { coSpliceEarly = False } } (mkConj grp) envT out
  return ([ifCommit (Comp "splice_safe" [pats]) (mkConj (chain parts)) (mkConj (genOf dseq))], dseq)

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

-- | The predicates reachable from some roots.
restrictTo :: [PredKey] -> Program -> Program
restrictTo roots p =
  let calls k = concatMap (bodyCalls . clBody) (M.findWithDefault [] k (progPreds p))
      reach s = let s' = s `Set.union` Set.fromList [ c | k <- Set.toList s, c <- calls k
                                                         , M.member c (progPreds p) ]
                in if s' == s then s else reach s'
      keep = reach (Set.fromList (filter (`M.member` progPreds p) roots))
  in p { progPreds = M.filterWithKey (\k _ -> Set.member k keep) (progPreds p)
       , progOrder = filter (`Set.member` keep) (progOrder p) }

-- | Keep the program's own predicates and the library predicates they use.
pruneUnused :: Set.Set PredKey -> Set.Set PredKey -> Program -> Program
pruneUnused own _ p = restrictTo (Set.toList own) p

-- ---------------------------------------------------------------------------
-- Closure specialisation: maplist(succ, L, R) calls a copy of maplist/3 in
-- which call(G, X, Y) has become succ(X, Y), so no meta-call remains.
-- Each new predicate is recorded as closure_spec(New/NewArity, Old/Arity,
-- Position, Closure); the checker re-derives its clauses.

specialiseMeta :: Program -> Either String (Program, [String], [Term])
specialiseMeta p0 = loop p0 M.empty [] [] (progOrder p0)
  where
    metaSet = metaPositions p0
    loop p _ evs steps [] = Right (p, reverse evs, reverse steps)
    loop p memo evs steps (k : ks) = do
      let cls = M.findWithDefault [] k (progPreds p)
      (cls', memo', p', newKeys, evs', steps') <-
        foldM (\(acc, m, pr, nk, ev, st) c -> do
                  (c', m2, pr2, nk2, ev2, st2) <- specClause pr m c
                  return (acc ++ [c'], m2, pr2, nk ++ nk2, ev ++ ev2, st ++ st2))
              ([], memo, p, [], [], []) cls
      let p'' = p' { progPreds = M.insert k cls' (progPreds p') }
      loop p'' memo' (reverse evs' ++ evs) (reverse steps' ++ steps) (ks ++ newKeys)

    specClause p memo (Clause h b nv) = do
      (b', memo', p', newKeys, evs, steps) <- specBody p memo b
      return (Clause h b' nv, memo', p', newKeys, evs, steps)

    specBody p memo t = case t of
      Comp op [a, b] | op `elem` [",", ";", "->", "*->"] -> do
        (a', m1, p1, k1, e1, s1) <- specBody p memo a
        (b', m2, p2, k2, e2, s2) <- specBody p1 m1 b
        return (Comp op [a', b'], m2, p2, k1 ++ k2, e1 ++ e2, s1 ++ s2)
      Comp "if_commit" [a, b, c] -> do
        (a', m1, p1, k1, e1, s1) <- specBody p memo a
        (b', m2, p2, k2, e2, s2) <- specBody p1 m1 b
        (c', m3, p3, k3, e3, s3) <- specBody p2 m2 c
        return (Comp "if_commit" [a', b', c'], m3, p3, k1 ++ k2 ++ k3, e1 ++ e2 ++ e3, s1 ++ s2 ++ s3)
      Comp f [a] | f `elem` ["\\+", "not", "once", "once_det", "ignore"] -> do
        (a', m1, p1, k1, e1, s1) <- specBody p memo a
        return (Comp f [a'], m1, p1, k1, e1, s1)
      Comp "findall" [x, g, l] -> do
        (g', m1, p1, k1, e1, s1) <- specBody p memo g
        return (Comp "findall" [x, g', l], m1, p1, k1, e1, s1)
      Comp "call" (g : extra) | not (isVar g), Just g' <- addArgs g extra ->
        specBody p memo g'
      _ -> case goalKey t of
        Just key | Just pos <- metaPosition key, isJust (closureAt t pos) -> do
          let Just clo = closureAt t pos
          specialiseCall p memo key pos clo t
        _ -> return (t, memo, p, [], [], [])

    metaPosition key =
      case [ i | i <- [0 .. snd key - 1], Set.member (key, i) metaSet ] of
        (i : _) -> Just i
        [] -> Nothing

    closureAt t pos = case goalArgs t !! pos of
      Var _ _ -> Nothing
      c | isCallable c -> Just c
      _ -> Nothing

    specialiseCall p memo key@(f, n) pos clo t = do
      let freeVs = termVarsOrdered clo
          canon = showAnswerTerm (Comp "k" [Atom f, Int (fromIntegral n), Int (fromIntegral pos), clo])
          otherArgs = [ a | (j, a) <- zip [0 ..] (goalArgs t), j /= pos ]
      case M.lookup canon memo of
        Just name -> return (Comp name (freeVs ++ otherArgs), memo, p, [], [], [])
        Nothing | M.size memo >= 500 -> Left "closure specialisation did not reach a fixpoint (closures keep growing)"
        Nothing -> do
          let name = f ++ "__m" ++ show (M.size memo + 1)
              newKey = (name, length freeVs + n - 1)
              memo' = M.insert canon name memo
              cls = M.findWithDefault [] key (progPreds p)
          cls' <- forM cls $ \(Clause h b cnv) -> do
            let g = goalArgs h !! pos
                cloR = renameTerm cnv clo
                cloVars = termVarsOrdered cloR
                sub = substVar g cloR
                h' = Comp name (cloVars ++ [ sub a | (j, a) <- zip [0 ..] (goalArgs h), j /= pos ])
            case g of
              Var _ _ -> return (Clause h' (sub b) (cnv + maxVarId clo + 2))
              _ -> Left ("closure argument of " ++ f ++ "/" ++ show n ++ " is not a variable in every clause")
          let p' = p { progPreds = M.insert newKey cls' (progPreds p)
                     , progOrder = progOrder p ++ [newKey] }
              step = Comp "closure_spec" [keyT newKey, keyT key, Int (fromIntegral pos), clo]
          return ( Comp name (freeVs ++ otherArgs), memo', p', [newKey]
                 , ["closure_specialised(" ++ f ++ "/" ++ show n ++ ", " ++ showTermQ clo ++ ") as " ++ name]
                 , [step] )

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
