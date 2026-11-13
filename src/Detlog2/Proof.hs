-- | Independent checker for detlog2 conversion proofs.
--
-- The converter ("Detlog2.Convert") emits one proof step per rewrite.  This
-- module checks them without using the converter or the cut eliminator:
--
--   1. It re-derives the cut-free intermediate program from the source with
--      its own implementation of the cut-elimination lemma (rule CUT) and of
--      closure specialisation (rule SPEC), and checks that the clauses the
--      converter compiled are these clauses, up to variable renaming and up
--      to calls replaced by their specialised copies.
--   2. For every generated clause it checks the step that justifies it:
--      the predicate packet (PRED, FACTS), the clause packet (CLAUSE), and
--      every row iteration (ROWS).  Inside clauses, each derivation node is
--      checked against its rule: the generated goals must be exactly the
--      rule's template instantiated with the source goal, the sub-derivations'
--      code and fresh variables, and the rule's side conditions must hold.
--   3. Every clause of the converted program must be justified, and every
--      justification must be in the program.
--
-- The rules and the lemma behind each one are in docs/proof_rules.md.  A
-- step is accepted only if all of its conditions are re-established here.
module Detlog2.Proof
  ( ProofContext(..)
  , checkProof
  , proofToText
  , proofFromText
  ) where

import Control.Monad (forM, forM_, unless, zipWithM)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Builtins
import Detlog2.Interp (defaultOptions)
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference (refRun)
import Detlog2.Term

data ProofContext = ProofContext
  { pcSource :: Program               -- ^ the program that was converted (with any query clause)
  , pcExternal :: Set.Set PredKey     -- ^ predicates answered by complete memo tables
  , pcOriginal :: Program             -- ^ the original program (memo tables are re-run on it)
  }

type Check a = Either String a

failWith :: String -> Check a
failWith = Left

ensure :: Bool -> String -> Check ()
ensure b msg = unless b (Left msg)

-- ---------------------------------------------------------------------------
-- Proof files are plain Prolog terms, one step per clause.

proofToText :: [Term] -> String
proofToText steps = unlines
  ("% detlog2 conversion proof: one step per rewrite (see docs/proof_rules.md)."
   : [ showTermQ s ++ "." | s <- steps ])

proofFromText :: String -> Either String [Term]
proofFromText src = do
  p <- parseProgram src
  return [ if clBody c == Atom "true" then clHead c else Comp ":-" [clHead c, clBody c]
         | (_, cs) <- programClauses p, c <- cs ]

-- ---------------------------------------------------------------------------
-- Entry point

checkProof :: ProofContext -> [Term] -> Program -> Check [String]
checkProof ctx0 steps conv = do
  -- predicates answered by complete memo tables count as external
  let completeMemo = Set.fromList [ k | Comp "memo_table" [kt, Atom "true", _] <- steps, Just k <- [termKey kt] ]
      ctx = ctx0 { pcExternal = pcExternal ctx0 `Set.union` completeMemo }
  base0 <- baseProgram (pcSource ctx)
  let specSteps = [ s | s@(Comp "closure_spec" _) <- steps ]
  (base, specTable) <- foldlM addSpec (base0, M.empty) specSteps
  let predSteps = [ s | s@(Comp f _) <- steps, f `elem` ["pred_packet", "facts_packet"] ]
      clauseSteps = [ s | s@(Comp "clause_packet" _) <- steps ]
      auxSteps = [ s | s@(Comp "aux" _) <- steps ]
      memoSteps = [ s | s@(Comp "memo_table" _) <- steps ]
  -- 1. the compiled clauses are the cut-free intermediate clauses
  intermediate <- fmap M.fromList $ forM predSteps $ \s -> do
    key <- stepKey s
    baseCls <- maybe (failWith ("no source predicate " ++ showKey key)) return (M.lookup key (progPreds base))
    case s of
      Comp "facts_packet" _ -> do
        ensure (all (\c -> clBody c == Atom "true") baseCls && not (null baseCls))
               (showKey key ++ ": facts_packet for a predicate that is not all facts")
        return (key, baseCls)
      _ -> do
        let mine = [ cs | cs@(Comp "clause_packet" (k : _)) <- clauseSteps, termKey k == Just key ]
        ensure (length mine == length baseCls)
               (showKey key ++ ": " ++ show (length baseCls) ++ " clauses but " ++ show (length mine) ++ " clause_packet steps")
        srcs <- forM (zip [1 :: Integer ..] baseCls) $ \(i, bc) -> do
          cs <- case [ c | c@(Comp "clause_packet" [_, Int j, _, _, _]) <- mine, j == i ] of
            [c] -> return c
            _ -> failWith (showKey key ++ ": missing or repeated clause_packet " ++ show i)
          let Comp "clause_packet" [_, _, srcT, _, _] = cs
          srcC <- asClause srcT
          ensure (clauseMatches specTable bc srcC)
                 (showKey key ++ " clause " ++ show i ++ ": compiled clause is not the cut-free source clause\n  source:   "
                  ++ showTermQ (clauseTerm bc) ++ "\n  compiled: " ++ showTermQ (clauseTerm srcC))
          return srcC
        return (key, srcs)
  let userMember = M.member ("member", 2) (progPreds (pcSource ctx))
      defined = Set.fromList (M.keys intermediate) `Set.union` pcExternal ctx
                `Set.union` Set.fromList [ k | Comp "memo_table" (kt : _) <- memoSteps, Just k <- [termKey kt] ]
      -- predicates answered by memo tables are treated as writing output
      effectful = effectfulOf intermediate `Set.union` pcExternal ctx
      convKeys = Set.fromList (progOrder conv)
      auxMap = M.fromList [ (n, s) | s@(Comp "aux" [Atom n, _, _, _]) <- auxSteps ]
      cx0 = Cx { cxDefined = defined, cxEffectful = effectful, cxUserMember = userMember
               , cxConv = convKeys, cxAux = auxMap, cxVs = Atom "[]", cxClauseVars = IS.empty }
  -- 2. every step
  predClauses <- forM predSteps $ \s -> checkPredStep intermediate s
  clauseClauses <- forM clauseSteps $ \s -> checkClauseStep cx0 s
  auxClauses <- forM auxSteps $ \s -> checkAuxStep cx0 s
  memoClauses <- forM memoSteps $ \s -> checkMemoStep ctx s
  -- 3. coverage: the converted program is exactly the justified clauses
  let computeRenamed = M.fromList [ (cpName f, cpName f ++ "__compute") | (f, False) <- memoKinds ]
      memoKinds = [ (f, c == Atom "true") | Comp "memo_table" [kt, c, _] <- memoSteps, Just (f, _) <- [termKey kt] ]
      renameHead c = case clHead c of
        Comp nm as | Just nm' <- M.lookup nm computeRenamed -> c { clHead = Comp nm' as }
        _ -> c
      justified = map renameHead (concat predClauses) ++ concat clauseClauses ++ concat auxClauses ++ concat memoClauses
      byKey = M.fromListWith (flip (++)) [ (k, [c]) | c <- justified, Just k <- [goalKey (clHead c)] ]
  forM_ (programClauses conv) $ \(k, cs) -> do
    js <- maybe (failWith ("unjustified predicate in the converted program: " ++ showKey k)) return (M.lookup k byKey)
    ensure (length js == length cs) (showKey k ++ ": " ++ show (length cs) ++ " clauses, " ++ show (length js) ++ " justified")
    forM_ (zip cs js) $ \(c, j) ->
      ensure (variant (emptyState 0) (clauseTerm c) (clauseTerm j))
             (showKey k ++ ": a clause differs from its justification:\n  program: " ++ showTermQ (clauseTerm c)
              ++ "\n  proof:   " ++ showTermQ (clauseTerm j))
  forM_ (M.keys byKey) $ \k -> ensure (Set.member k convKeys) ("justified but missing from the program: " ++ showKey k)
  return [ "proof accepted: " ++ show (length steps) ++ " steps, "
           ++ show (length (concat (map snd (programClauses conv)))) ++ " clauses justified" ]

foldlM :: (b -> a -> Check b) -> b -> [a] -> Check b
foldlM f z xs = foldl (\acc x -> acc >>= \a -> f a x) (Right z) xs

showKey :: PredKey -> String
showKey (f, n) = f ++ "/" ++ show n

termKey :: Term -> Maybe PredKey
termKey (Comp "/" [Atom f, Int n]) = Just (f, fromIntegral n)
termKey _ = Nothing

stepKey :: Term -> Check PredKey
stepKey (Comp _ (k : _)) = maybe (failWith "bad predicate indicator in a step") return (termKey k)
stepKey _ = failWith "bad step"

asClause :: Term -> Check Clause
asClause t = case t of
  Comp ":-" [h, b] -> return (Clause h b (maxVarId t + 1))
  h | isCallable h -> return (Clause h (Atom "true") (maxVarId t + 1))
  _ -> failWith ("not a clause: " ++ showTermQ t)

listOf :: Term -> Check [Term]
listOf (Atom "[]") = return []
listOf (Comp "." [h, t]) = (h :) <$> listOf t
listOf t = failWith ("not a list: " ++ showTermQ t)

list :: [Term] -> Term
list xs = mkList xs (Atom "[]")

cpName :: String -> String
cpName f = f ++ "__cp"

-- ---------------------------------------------------------------------------
-- Rule CUT, re-derived: the cut-free form of the source program.

baseProgram :: Program -> Check Program
baseProgram src = do
  cls <- forM (programClauses src) $ \(k, cs) -> (,) k <$> cutFree k cs
  let p1 = src { progPreds = M.fromList cls }
      withLib = withPrelude p1
      userMember = M.member ("member", 2) (progPreds src)
  return (if userMember then withLib
          else withLib { progPreds = M.delete ("member", 2) (progPreds withLib)
                       , progOrder = filter (/= ("member", 2)) (progOrder withLib) })

-- | A cut in a goal position.
goalCut :: Term -> Bool
goalCut t = case t of
  Atom "!" -> True
  Comp op [a, b] | op `elem` [",", ";", "->", "*->", "forall"] -> goalCut a || goalCut b
  Comp "if_commit" as -> any goalCut as
  Comp f [a] | f `elem` ["\\+", "not", "once", "once_det", "ignore", "call"] -> goalCut a
  Comp "findall" [_, g, _] -> goalCut g
  Comp "aggregate_all" [_, g, _] -> goalCut g
  _ -> False

cutFree :: PredKey -> [Clause] -> Check [Clause]
cutFree (f, n) cls
  | not (any (goalCut . clBody) cls) = return cls
  | otherwise = do
      let cls1 = [ c { clBody = local (clBody c) } | c <- cls ]
      forM_ cls1 $ \c -> ensure (all (\g -> g == Atom "!" || not (goalCut g)) (conjList (clBody c)))
                                (showKey (f, n) ++ ": a cut that is neither top-level nor local")
      if not (any (elem (Atom "!") . conjList . clBody) cls1)
        then return cls1
        else do
          let args = [ Var i ("A" ++ show i) | i <- [0 .. n - 1] ]
              headT = if n == 0 then Atom f else Comp f args
              go _ [] = Atom "fail"
              go off (c : rest) =
                let h = renameTerm off (clHead c)
                    b = renameTerm off (clBody c)
                    off' = off + clNVars c
                    match = [ Comp "=" [a, x] | (a, x) <- zip args (goalArgs h) ]
                in case break (== Atom "!") (conjList b) of
                     (before, _ : after) -> Comp "if_commit" [mkConj (match ++ before), commitRest after, go off' rest]
                     _ -> orElse (mkConj (match ++ conjList b)) (go off' rest)
              orElse x (Atom "fail") = x
              orElse x r = Comp ";" [x, r]
              body = go n cls1
          return [Clause headT body (maxVarId (Comp "c" [headT, body]) + 1)]
  where
    commitRest gs = case break (== Atom "!") gs of
      (before, _ : after) -> Comp "if_commit" [mkConj before, commitRest after, Atom "fail"]
      _ -> mkConj gs
    -- cuts local to opaque goals commit inside them
    local t = case t of
      Comp "," [a, b] -> Comp "," [local a, local b]
      Comp ";" [Comp "->" [c, x], e] -> Comp ";" [Comp "->" [barrier c, local x], local e]
      Comp ";" [a, b] -> Comp ";" [local a, local b]
      Comp "->" [c, x] -> Comp "->" [barrier c, local x]
      Comp g [x] | g `elem` ["\\+", "not", "once", "ignore", "call"] -> Comp g [barrier x]
      Comp "findall" [x, g, l] -> Comp "findall" [x, barrier g, l]
      Comp "forall" [c, a] -> Comp "forall" [barrier c, barrier a]
      Comp "aggregate_all" [s, g, r] -> Comp "aggregate_all" [s, barrier g, r]
      _ -> t
    barrier g = let g1 = local g
                in if Atom "!" `elem` conjList g1 then commitRest (conjList g1) else g1

-- ---------------------------------------------------------------------------
-- Rule SPEC, re-derived: a closure-specialised copy of a predicate.

type SpecTable = M.Map String String       -- canonical (pred, position, closure) -> new name

addSpec :: (Program, SpecTable) -> Term -> Check (Program, SpecTable)
addSpec (p, table) s = case s of
  Comp "closure_spec" [newT, oldT, Int pos, clo] -> do
    newKey@(newName, newArity) <- maybe (failWith "closure_spec: bad new key") return (termKey newT)
    oldKey@(f, n) <- maybe (failWith "closure_spec: bad old key") return (termKey oldT)
    oldCls <- maybe (failWith ("closure_spec: unknown " ++ showKey oldKey)) return (M.lookup oldKey (progPreds p))
    let posI = fromIntegral pos
        freeVs = termVarsOrdered clo
    ensure (isCallable clo) "closure_spec: closure is not callable"
    ensure (newArity == length freeVs + n - 1) "closure_spec: wrong arity"
    newCls <- forM oldCls $ \(Clause h b nv) -> do
      let g = goalArgs h !! posI
          cloR = renameTerm nv clo
          sub t = case t of
            _ | t == g -> cloR
            Comp "call" (x : extra) | x == g, Just t' <- addArgs cloR extra -> t'
            Comp fn as -> Comp fn (map sub as)
            _ -> t
      ensure (isVar g) ("closure_spec: argument " ++ show (posI + 1) ++ " of " ++ showKey oldKey ++ " is not a variable")
      let h' = Comp newName (termVarsOrdered cloR ++ [ sub a | (j, a) <- zip [0 ..] (goalArgs h), j /= posI ])
          b' = sub b
      return (Clause h' b' (maxVarId (Comp "c" [h', b']) + 1))
    let canon = showAnswerTerm (Comp "k" [Atom f, Int (fromIntegral n), Int pos, clo])
    return ( p { progPreds = M.insert newKey newCls (progPreds p), progOrder = progOrder p ++ [newKey] }
           , M.insert canon newName table )
  _ -> failWith "bad closure_spec step"

-- | A compiled clause matches a cut-free source clause: equal up to variable
-- renaming, call(G, X...) with a known G read as G(X...), and closure calls
-- replaced by their specialised copies.
clauseMatches :: SpecTable -> Clause -> Clause -> Bool
clauseMatches table (Clause h1 b1 _) (Clause h2 b2 _) =
  case mTerm h1 h2 (IM.empty, IM.empty) of
    Just bij -> mGoal table b1 b2 bij /= Nothing
    Nothing -> False

type Bij = (IM.IntMap Int, IM.IntMap Int)

mTerm :: Term -> Term -> Bij -> Maybe Bij
mTerm a b bij@(m1, m2) = case (a, b) of
  (Var i _, Var j _) -> case (IM.lookup i m1, IM.lookup j m2) of
    (Nothing, Nothing) -> Just (IM.insert i j m1, IM.insert j i m2)
    (Just j', Just i') | j' == j && i' == i -> Just bij
    _ -> Nothing
  (Comp f as, Comp g bs) | f == g && length as == length bs -> mArgs as bs bij
  _ | isVar a || isVar b -> Nothing
    | a == b -> Just bij
    | otherwise -> Nothing
  where
    mArgs [] [] x = Just x
    mArgs (x : xs) (y : ys) x0 = mTerm x y x0 >>= mArgs xs ys
    mArgs _ _ _ = Nothing

mGoal :: SpecTable -> Term -> Term -> Bij -> Maybe Bij
mGoal table a b bij = case (a, b) of
  (Comp "call" (g : extra), _) | not (isVar g), Just a' <- addArgs g extra -> mGoal table a' b bij
  (Comp f [x, y], Comp g [u, v]) | f == g, f `elem` [",", ";", "->", "*->"] ->
    mGoal table x u bij >>= mGoal table y v
  (Comp "if_commit" [x, y, z], Comp "if_commit" [u, v, w]) ->
    mGoal table x u bij >>= mGoal table y v >>= mGoal table z w
  (Comp f [x], Comp g [u]) | f == g, f `elem` ["\\+", "not", "once", "once_det", "ignore"] -> mGoal table x u bij
  (Comp "findall" [t, x, l], Comp "findall" [t', u, l']) ->
    mTerm t t' bij >>= mGoal table x u >>= mTerm l l'
  _ -> case mTerm a b bij of
    Just r -> Just r
    Nothing -> specCall
  where
    specCall = case (goalKey a, b) of
      (Just (f, n), Comp name args') ->
        let cands = [ (pos, clo) | (pos, clo) <- zip [0 :: Int ..] (goalArgs a), not (isVar clo), isCallable clo ]
            hit = [ (pos, clo) | (pos, clo) <- cands
                  , M.lookup (showAnswerTerm (Comp "k" [Atom f, Int (fromIntegral n), Int (fromIntegral pos), clo])) table == Just name ]
        in case hit of
             ((pos, clo) : _) ->
               let expected = termVarsOrdered clo ++ [ x | (j, x) <- zip [0 ..] (goalArgs a), j /= pos ]
               in mTerm (list expected) (list args') bij
             [] -> Nothing
      _ -> Nothing

-- ---------------------------------------------------------------------------
-- Rules PRED and FACTS

checkPredStep :: M.Map PredKey [Clause] -> Term -> Check [Clause]
checkPredStep inter s = case s of
  Comp "facts_packet" [kt, clT] -> do
    key@(f, n) <- maybe (failWith "facts_packet: bad key") return (termKey kt)
    cl <- asClause clT
    facts <- maybe (failWith ("facts_packet: " ++ showKey key)) return (M.lookup key inter)
    case (clHead cl, conjList (clBody cl)) of
      (Comp name hargs, [Comp "member_cp" [p, rowsT], Comp "cp_filter" [p', argsT, rv]])
        | name == cpName f && length hargs == n + 1 -> do
            let args = take n hargs
            ensure (p == p' && isVar p && last hargs == rv && isVar rv) "facts_packet: packet variables"
            ensure (distinctVars (args ++ [p, rv])) "facts_packet: argument variables are not distinct"
            argsL <- listOf argsT
            ensure (argsL == args) "facts_packet: cp_filter pattern is not the arguments"
            rows <- listOf rowsT
            ensure (length rows == length facts) "facts_packet: one row per fact"
            forM_ (zip rows facts) $ \(r, c) ->
              ensure (variant (emptyState 0) r (list (goalArgs (clHead c)))) "facts_packet: a row is not its fact"
            ensure (pairwiseDisjoint (map termVarIds rows ++ [termVarIds (list (args ++ [p, rv]))]))
                   "facts_packet: rows share variables"
            return [cl]
      _ -> failWith ("facts_packet: wrong shape for " ++ showKey key)
  Comp "pred_packet" [kt, Int k, clT] -> do
    key@(f, n) <- maybe (failWith "pred_packet: bad key") return (termKey kt)
    cl <- asClause clT
    cls <- maybe (failWith ("pred_packet: " ++ showKey key)) return (M.lookup key inter)
    ensure (fromIntegral k == length cls) "pred_packet: clause count"
    case clHead cl of
      Comp name hargs | name == cpName f && length hargs == n + 1 -> do
        let args = take n hargs
            rv = last hargs
            calls = conjList (clBody cl)
        ensure (distinctVars (args ++ [rv])) "pred_packet: head variables are not distinct"
        case (k, calls) of
          (0, [Comp "=" [r, Atom "[]"]]) | r == rv -> return ()
          (1, [Comp c [a, r]]) | c == cpName f ++ "_c1" && r == rv && a == list args -> return ()
          (_, _) | k >= 2 -> do
            let (cs, lastG) = (init calls, last calls)
            ensure (length cs == fromIntegral k) "pred_packet: one call per clause"
            rs <- zipWithM (\i c -> case c of
                               Comp nm [a, r] | nm == cpName f ++ "_c" ++ show i && a == list args && isVar r -> return r
                               _ -> failWith "pred_packet: clause call") [1 :: Int ..] cs
            ensure (lastG == Comp "rows_concat" [list rs, rv]) "pred_packet: rows_concat"
            ensure (distinctVars (args ++ rv : rs)) "pred_packet: packet variables are not distinct"
          _ -> failWith "pred_packet: wrong body"
        return [cl]
      _ -> failWith "pred_packet: wrong head"
  _ -> failWith "bad predicate step"

distinctVars :: [Term] -> Bool
distinctVars ts = all isVar ts && IS.size (IS.fromList [ i | Var i _ <- ts ]) == length ts

pairwiseDisjoint :: [IS.IntSet] -> Bool
pairwiseDisjoint [] = True
pairwiseDisjoint (s : ss) = all (IS.null . IS.intersection s) ss && pairwiseDisjoint ss

-- ---------------------------------------------------------------------------
-- Rule CLAUSE and the goal rules

data Cx = Cx
  { cxDefined :: Set.Set PredKey
  , cxEffectful :: Set.Set PredKey
  , cxUserMember :: Bool
  , cxConv :: Set.Set PredKey
  , cxAux :: M.Map String Term
  , cxVs :: Term              -- ^ the environment row: all clause variables
  , cxClauseVars :: IS.IntSet
  }

checkClauseStep :: Cx -> Term -> Check [Clause]
checkClauseStep cx0 s = case s of
  Comp "clause_packet" [kt, Int i, srcT, genT, deriv] -> do
    (f, _) <- maybe (failWith "clause_packet: bad key") return (termKey kt)
    src <- asClause srcT
    gen <- asClause genT
    let h = clHead src
        b = clBody src
        vs = list (termVarsOrdered (Comp "c" [h, b]))
        headArgs = list (goalArgs h)
        cx = cx0 { cxVs = vs, cxClauseVars = termVarIds vs }
        name = cpName f ++ "_c" ++ show i
        where' = name ++ ": "
    case (clHead gen, clBody gen) of
      (Comp nm [argsV, rowsV], Comp "if_commit" [Comp "copy_term" [a', ha], body, Comp "=" [r', Atom "[]"]])
        | nm == name -> do
            ensure (a' == argsV && r' == rowsV && ha == headArgs) (where' ++ "packet frame")
            ensure (fresh cx [argsV, rowsV]) (where' ++ "Args/Rows are not fresh")
            intro <- case b of
              Atom "true" -> do
                ensure (deriv == Atom "none" && body == Comp "=" [rowsV, list [headArgs]]) (where' ++ "fact clause")
                return []
              _ -> do
                n <- node deriv
                let goals = conjList body
                ensure (not (null goals)) (where' ++ "empty body")
                ensure (nSrc n == b && nEnv n == vs) (where' ++ "derivation is not of the clause body")
                let envRows = nOut n
                ensure (goals == nGen n ++ [Comp "splice_extend" [envRows, headArgs, vs, rowsV]])
                       (where' ++ "body is not the derivation's code followed by the projection")
                ensure (fresh cx [envRows]) (where' ++ "Env is not fresh")
                xs <- chk cx deriv
                return (varIds [envRows] ++ xs)
            ensure (distinctIds (varIds [argsV, rowsV] ++ intro)) (where' ++ "a fresh variable is introduced twice")
            return [gen]
      _ -> failWith (where' ++ "wrong clause shape")
  _ -> failWith "bad clause step"

-- | Rule ROWS: iteration over a packet.
checkAuxStep :: Cx -> Term -> Check [Clause]
checkAuxStep cx0 s = case s of
  Comp "aux" [Atom name, vs, clsT, deriv] -> do
    (c1T, c2T) <- listOf clsT >>= \cs -> case cs of
      [a, b] -> return (a, b)
      _ -> failWith "aux: expected two clauses"
    c1 <- asClause c1T
    c2 <- asClause c2T
    let cx = cx0 { cxVs = vs, cxClauseVars = termVarIds vs }
        where' = name ++ ": "
    ensure (clHead c1 == Comp name [Atom "[]", Atom "[]"] && clBody c1 == Atom "true") (where' ++ "empty-packet clause")
    n <- node deriv
    case (clHead c2, conjList (clBody c2)) of
      (Comp nm [Comp "." [row, rs], out], [ Comp "if_commit" [Comp "=" [row', Comp "out" [t]], Comp "=" [o1, outItem], rest]
                                          , Comp nm2 [rs', o2], Comp "rows_concat" [lst, out'] ])
        | nm == name && nm2 == name -> do
            ensure (row' == row && rs' == rs && out' == out && outItem == list [Comp "out" [t]]) (where' ++ "frame")
            ensure (lst == list [o1, o2]) (where' ++ "rows_concat")
            ensure (conjList rest == Comp "copy_term" [row, vs] : nGen n) (where' ++ "row body")
            ensure (nEnv n == vs && nOut n == o1) (where' ++ "derivation env/out")
            let frame = [row, rs, out, o1, o2, t]
            ensure (fresh cx frame) (where' ++ "frame variables are not fresh")
            xs <- chk cx deriv
            ensure (distinctIds (varIds frame ++ xs)) (where' ++ "a fresh variable is introduced twice")
            return [c1, c2]
      _ -> failWith (where' ++ "wrong iteration clause")
  _ -> failWith "bad aux step"

-- | Rule MEMO, checked by evaluation: the memo clause is the lookup
-- template, and every table entry is re-run on the original program with
-- ordinary Prolog semantics and must give exactly the recorded packet.
checkMemoStep :: ProofContext -> Term -> Check [Clause]
checkMemoStep ctx s = case s of
  Comp "memo_table" [kt, completeT, clT] -> do
    key@(f, n) <- maybe (failWith "memo_table: bad key") return (termKey kt)
    cl <- asClause clT
    let here = "memo table for " ++ showKey key ++ ": "
    case (clHead cl, clBody cl) of
      (Comp nm hargs, Comp "if_commit" [Comp "memo_lookup" [argsT, table, rows], Atom "true", fallback])
        | nm == cpName f && length hargs == n + 1 -> do
            let args = take n hargs
            ensure (distinctVars (args ++ [last hargs]) && rows == last hargs && argsT == list args) (here ++ "frame")
            ensure (fallback == (if completeT == Atom "true"
                                   then Comp "memo_miss" [Comp "/" [Atom f, Int (fromIntegral n)], list args]
                                   else Comp (cpName f ++ "__compute") hargs)) (here ++ "fallback")
            entries <- listOf table
            forM_ entries $ \entry -> do
              (pat, recorded) <- listOf entry >>= \es -> case es of
                [a, b] -> return (a, b)
                _ -> failWith (here ++ "bad table entry")
              pats <- listOf pat
              ensure (length pats == n) (here ++ "pattern arity")
              let goal = if n == 0 then Atom f else Comp f pats
                  nv = maxVarId goal + 1
                  stream = take 100001 (refRun defaultOptions (withPrelude (pcOriginal ctx)) goal nv)
                  errs = [ e | Err e <- stream ]
              ensure (null errs) (here ++ "re-running " ++ showTermQ goal ++ " raised " ++ concat (take 1 errs))
              let actual = concat [ case ev of
                                      Ans st -> [resolve st pat]
                                      Out o -> [Comp "out" [Atom o]]
                                      Err _ -> []
                                  | ev <- stream ]
              rec <- listOf recorded
              ensure (length rec == length actual && and (zipWith (variant (emptyState 0)) rec actual))
                     (here ++ showTermQ goal ++ ": the recorded packet is not the program's answers")
            return [cl]
      _ -> failWith (here ++ "not a memo lookup clause")
  _ -> failWith "bad memo step"

data N = N { nRule :: String, nSrc :: Term, nEnv :: Term, nOut :: Term, nGen :: [Term], nSubs :: [Term] }

node :: Term -> Check N
node t = case t of
  Comp "d" [Atom r, src, env, out, gen, subs] -> N r src env out <$> listOf gen <*> listOf subs
  _ -> failWith ("not a derivation node: " ++ take 200 (showTermQ t))

fresh :: Cx -> [Term] -> Bool
fresh cx ts = all (\t -> case t of
                          Var i _ -> not (IS.member i (cxClauseVars cx))
                          _ -> False) ts

varIds :: [Term] -> [Int]
varIds ts = [ i | Var i _ <- ts ]

distinctIds :: [Int] -> Bool
distinctIds is = IS.size (IS.fromList is) == length is

allDistinct :: [Term] -> Bool
allDistinct ts = IS.size (IS.fromList [ i | Var i _ <- ts ]) == length ts && all isVar ts

eqG :: Term -> Term -> Term
eqG a b = Comp "=" [a, b]

ifC :: Term -> Term -> Term -> Term
ifC c t e = Comp "if_commit" [c, t, e]

-- | Check one derivation node.  Returns the fresh variables it introduces.
chk :: Cx -> Term -> Check [Int]
chk cx d = do
  n <- node d
  let src = nSrc n
      e = nEnv n
      o = nOut n
      gen = nGen n
      vs = cxVs cx
      rule = nRule n
      here = "rule " ++ rule ++ " for " ++ take 120 (showTermQ src) ++ ": "
      need b m = ensure b (here ++ m)
      genIs xs = need (gen == xs) "generated code is not the rule's template"
      freshIs xs = do
        need (fresh cx xs) "a new variable is not fresh"
        need (allDistinct xs) "new variables are not distinct"
        return [ i | Var i _ <- xs ]
      sub k = case drop k (nSubs n) of
        (x : _) -> node x
        [] -> failWith (here ++ "missing sub-derivation")
      subT k = case drop k (nSubs n) of
        (x : _) -> return x
        [] -> failWith (here ++ "missing sub-derivation")
      envLevel = need (e == vs) "environment is not the clause variables"
      -- a rows node over input Rin with output Out for source G
      rowsSub k g rin out = do
        r <- sub k
        need (nSrc r == g && nEnv r == rin && nOut r == out) "sub-derivation does not match"
        need (nRule r `elem` ["rows", "rows_true"]) "expected a packet iteration"
        x <- subT k
        chk cx x
      envSub k g out = do
        r <- sub k
        need (nSrc r == g && nEnv r == vs && nOut r == out) "sub-derivation does not match"
        x <- subT k
        chk cx x
  case rule of
    "true" -> envLevel >> need (src == Atom "true") "source" >> genIs [eqG o (list [e])] >> return []
    "fail" -> envLevel >> need (src `elem` [Atom "fail", Atom "false"]) "source" >> genIs [eqG o (list [])] >> return []
    "det" -> do
      envLevel
      need (isDetGoal cx src) "not a deterministic, output-free built-in"
      genIs [ifC src (eqG o (list [e])) (eqG o (list []))]
      return []
    "effect" -> do
      envLevel
      need (maybe False (`elem` effectKeys) (goalKey src) && not (definedHere cx src)) "not an output built-in"
      case gen of
        [Comp "effect_text" [g', t], Comp "=" [o', item]] | g' == src && o' == o && item == list [Comp "out" [t], e] ->
          freshIs [t]
        _ -> failWith (here ++ "template")
    "call" -> do
      envLevel
      key@(f, k) <- maybe (failWith (here ++ "not callable")) return (goalKey src)
      need (Set.member key (cxDefined cx)) "callee is not a converted predicate"
      need (Set.member (cpName f, k + 1) (cxConv cx)) "callee packet missing from the program"
      case gen of
        [Comp q qargs, Comp "splice_extend" [p, e', pat, o']]
          | q == cpName f && qargs == goalArgs src ++ [p] && e' == e && pat == list (goalArgs src) && o' == o ->
              freshIs [p]
        _ -> failWith (here ++ "template")
    "member_cp" -> do
      envLevel
      need (not (cxUserMember cx)) "member/2 is user-defined"
      case (src, gen) of
        (Comp "member" [x, l], [Comp "member_cp" [p, l'], Comp "cp_rows" [p', pr], Comp "splice_extend" [pr', e', pat, o']])
          | l' == l && p' == p && pr' == pr && e' == e && pat == list [x] && o' == o -> freshIs [p, pr]
        _ -> failWith (here ++ "template")
    "between_cp" -> do
      envLevel
      need (not (Set.member ("between", 3) (cxDefined cx))) "between/3 is user-defined"
      case (src, gen) of
        (Comp "between" [lo, hi, x], [Comp "between_cp" [lo', hi', p], Comp "cp_rows" [p', pr], Comp "splice_extend" [pr', e', pat, o']])
          | lo' == lo && hi' == hi && p' == p && pr' == pr && e' == e && pat == list [x] && o' == o -> freshIs [p, pr]
        _ -> failWith (here ++ "template")
    "length_det" -> do
      envLevel
      need (not (Set.member ("length", 2) (cxDefined cx))) "length/2 is user-defined"
      case src of
        Comp "length" as -> genIs [ifC (Comp "length_det" as) (eqG o (list [e])) (eqG o (list []))] >> return []
        _ -> failWith (here ++ "source")
    "builtin_rows" -> do
      envLevel
      let k = goalKey src
      need (maybe False (\x -> x `elem` nondetBuiltinKeys || x == ("atom_concat", 3)) k && not (definedHere cx src))
           "not a nondeterministic built-in"
      case gen of
        [Comp "builtin_rows" [g', br], Comp "splice_extend" [br', e', pat, o']]
          | g' == src && br' == br && e' == e && pat == list [src] && o' == o -> freshIs [br]
        _ -> failWith (here ++ "template")
    "rewrite" -> do
      envLevel
      g' <- maybe (failWith (here ++ "no rewrite applies")) return (rewriteOf src)
      r <- sub 0
      need (nSrc r == g' && nEnv r == vs && nOut r == o) "rewritten goal"
      genIs (nGen r)
      subT 0 >>= chk cx
    "det_prefix" -> do
      envLevel
      let gs = conjList src
          (bs, rest) = span (isDetGoal cx) gs
      need (length gs >= 2 && not (null bs)) "no deterministic prefix"
      r <- sub 0
      need (nSrc r == mkConj rest && nEnv r == vs && nOut r == o) "rest derivation"
      genIs [ifC (mkConj bs) (mkConj (nGen r)) (eqG o (list []))]
      subT 0 >>= chk cx
    "seq" -> do
      envLevel
      case conjList src of
        (g1 : rest@(_ : _)) -> do
          d1 <- sub 0
          d2 <- sub 1
          let r1 = nOut d1
          need (nSrc d1 == g1 && nEnv d1 == vs) "first goal"
          need (nSrc d2 == mkConj rest && nEnv d2 == r1 && nOut d2 == o) "rest"
          need (nRule d2 `elem` ["rows", "rows_true"]) "rest must iterate the packet"
          genIs (nGen d1 ++ nGen d2)
          a <- freshIs [r1]
          x1 <- subT 0 >>= chk cx
          x2 <- subT 1 >>= chk cx
          return (a ++ x1 ++ x2)
        _ -> failWith (here ++ "not a conjunction of two or more goals")
    "rows_true" -> do
      need (src == Atom "true") "source"
      genIs [eqG o e]
      return []
    "rows" -> do
      case (gen, nSubs n) of
        ([Comp name [rin, o']], [Atom name']) | name == name' && rin == e && o' == o -> do
          step <- maybe (failWith (here ++ "no iteration step " ++ name)) return (M.lookup name (cxAux cx))
          case step of
            Comp "aux" [_, vs', _, dAux] -> do
              na <- node dAux
              need (vs' == vs && nSrc na == src) "iteration step is for another goal"
              return []
            _ -> failWith (here ++ "bad iteration step")
        _ -> failWith (here ++ "template")
    "disj" -> do
      envLevel
      case src of
        Comp ";" [a, b] | not (isIte a) -> do
          da <- sub 0
          db <- sub 1
          let ra = nOut da
              rb = nOut db
          genIs (nGen da ++ nGen db ++ [Comp "rows_concat" [list [ra, rb], o]])
          xa <- rowsSub 0 a (list [e]) ra
          xb <- rowsSub 1 b (list [e]) rb
          f' <- freshIs [ra, rb]
          return (f' ++ xa ++ xb)
        _ -> failWith (here ++ "not a disjunction")
    "ite_det" -> do
      envLevel
      (c, t, el) <- maybe (failWith (here ++ "not a commitment")) return (iteParts src)
      need (all (isDetGoal cx) (conjList c)) "condition is not deterministic built-ins"
      dt <- sub 0
      de <- sub 1
      genIs [ifC c (mkConj (nGen dt)) (mkConj (nGen de))]
      xt <- envSub 0 t o
      xe <- envSub 1 el o
      return (xt ++ xe)
    "ite" -> do
      envLevel
      (c, t, el) <- maybe (failWith (here ++ "not a commitment")) return (iteParts src)
      dc <- sub 0
      dt <- sub 1
      de <- sub 2
      let rc = nOut dc
          firstV = case nEnv dt of
            Comp "." [x, Atom "[]"] -> x
            x -> x
          ot = nOut dt
          oe = nOut de
      case drop (length (nGen dc)) gen of
        [Comp "packet_first" [rc', pre, res], Comp "if_commit" [Comp "=" [res', Atom "none"], elseG, thenG]]
          | rc' == rc && res' == res -> do
              need (take (length (nGen dc)) gen == nGen dc) "condition code"
              need (conjList elseG == nGen de ++ [Comp "rows_concat" [list [pre, oe], o]]) "else branch"
              need (conjList thenG == [eqG res (Comp "first" [firstV])] ++ nGen dt
                                      ++ [Comp "rows_concat" [list [pre, ot], o]]) "then branch"
              xc <- rowsSub 0 c (list [e]) rc
              xt <- rowsSub 1 t (list [firstV]) ot
              xe <- envSub 2 el oe
              f' <- freshIs [rc, pre, res, firstV, ot, oe]
              return (f' ++ xc ++ xt ++ xe)
        _ -> failWith (here ++ "template")
    "neg_det" -> do
      envLevel
      x <- maybe (failWith (here ++ "not a negation")) return (negOf src)
      need (all (isDetGoal cx) (conjList x)) "negated goal is not deterministic built-ins"
      genIs [ifC x (eqG o (list [])) (eqG o (list [e]))]
      return []
    "neg" -> do
      envLevel
      x <- maybe (failWith (here ++ "not a negation")) return (negOf src)
      dx <- sub 0
      let rg = nOut dx
      case drop (length (nGen dx)) gen of
        [Comp "packet_first" [rg', pre, res], Comp "if_commit" [Comp "=" [res', Atom "none"], yes, no]]
          | rg' == rg && res' == res
          , yes == Comp "rows_concat" [list [pre, list [e]], o], no == eqG o pre -> do
              need (take (length (nGen dx)) gen == nGen dx) "goal code"
              xs <- rowsSub 0 x (list [e]) rg
              f' <- freshIs [rg, pre, res]
              return (f' ++ xs)
        _ -> failWith (here ++ "template")
    "findall" -> do
      envLevel
      case src of
        Comp "findall" [t, x, l] -> do
          dx <- sub 0
          let rg = nOut dx
          case drop (length (nGen dx)) gen of
            [Comp "packet_split" [rg', outs, rows0], Comp "splice_extend" [rows0', t', e', ls], Comp "if_commit" [Comp "=" [l', ls'], yes, no]]
              | rg' == rg && rows0' == rows0 && t' == t && e' == e && l' == l && ls' == ls
              , yes == Comp "rows_concat" [list [outs, list [e]], o], no == eqG o outs -> do
                  need (take (length (nGen dx)) gen == nGen dx) "goal code"
                  xs <- rowsSub 0 x (list [e]) rg
                  f' <- freshIs [rg, outs, rows0, ls]
                  return (f' ++ xs)
            _ -> failWith (here ++ "template")
        _ -> failWith (here ++ "source")
    "count" -> do
      envLevel
      case src of
        Comp "aggregate_all" [Atom "count", x, r] -> do
          dx <- sub 0
          let rg = nOut dx
          case drop (length (nGen dx)) gen of
            [Comp "packet_split" [rg', outs, rows0], Comp "length_det" [rows0', cnt], Comp "if_commit" [Comp "=" [r', cnt'], yes, no]]
              | rg' == rg && rows0' == rows0 && r' == r && cnt' == cnt
              , yes == Comp "rows_concat" [list [outs, list [e]], o], no == eqG o outs -> do
                  need (take (length (nGen dx)) gen == nGen dx) "goal code"
                  xs <- rowsSub 0 x (list [e]) rg
                  f' <- freshIs [rg, outs, rows0, cnt]
                  return (f' ++ xs)
            _ -> failWith (here ++ "template")
        _ -> failWith (here ++ "source")
    "splice" -> do
      envLevel
      dseq <- sub 0
      let gs = conjList src
          grp = conjList (nSrc dseq)
          k = length grp
          rest = drop k gs
          r = nOut dseq
      need (k >= 2 && take k gs == grp) "group is not a prefix of the conjunction"
      need (all (isGenerator cx) grp) "a spliced goal is not an output-free generator"
      need (pairwiseDisjoint (map termVarIds grp)) "spliced goals share variables"
      need (nEnv dseq == vs) "fallback derivation env"
      case gen of
        (Comp "if_commit" [Comp "splice_safe" [pats], chainG, seqG] : restGen) -> do
          need (conjList seqG == nGen dseq) "fallback code"
          (chainFresh) <- checkChain cx here grp pats r (conjList chainG)
          xseq <- subT 0 >>= chk cx
          xrest <- if null rest
            then need (r == o && null restGen) "output" >> return []
            else do
              drest <- sub 1
              need (restGen == nGen drest) "rest code"
              xr <- rowsSub 1 (mkConj rest) r o
              f' <- freshIs [r]
              return (f' ++ xr)
          f2 <- freshIs chainFresh
          return (f2 ++ xseq ++ xrest)
        _ -> failWith (here ++ "template")
    _ -> failWith (here ++ "unknown rule")

-- | The splice chain: each generator's packet, stop if empty, then
-- splice/2 and splice_extend/4.
checkChain :: Cx -> String -> [Term] -> Term -> Term -> [Term] -> Check [Term]
checkChain cx here grp pats out goals = go grp goals [] []
  where
    vs = cxVs cx
    go [] gs ps patsAcc = case gs of
      [Comp "splice" [cps, combos], Comp "splice_extend" [combos', e', pats', out']]
        | cps == list [ Comp "cp" [p] | p <- reverse ps ] && combos' == combos && e' == vs
          && pats' == pats && out' == out && pats == list (reverse patsAcc) -> return [combos]
      _ -> failWith (here ++ "splice chain end")
    go (g : more) gs ps patsAcc = do
      (consumed, p, pat, newVs) <- case (goalKey g, gs) of
        (Just ("member", 2), Comp "member_cp" [m, l] : Comp "cp_rows" [m', p] : _)
          | not (Set.member ("member", 2) (cxDefined cx)), [x, l'] <- goalArgs g, l' == l, m' == m ->
              return (2, p, list [x], [m, p])
        (Just ("between", 3), Comp "between_cp" [lo, hi, m] : Comp "cp_rows" [m', p] : _)
          | [lo', hi', x] <- goalArgs g, lo' == lo, hi' == hi, m' == m -> return (2, p, list [x], [m, p])
        (Just key@(f, _), Comp q qargs : _)
          | Set.member key (cxDefined cx), q == cpName f, init qargs == goalArgs g -> return (1, last qargs, list (goalArgs g), [last qargs])
        _ -> failWith (here ++ "splice chain step for " ++ showTermQ g)
      case drop consumed gs of
        [Comp "if_commit" [Comp "=" [p', Atom "[]"], Comp "=" [out', Atom "[]"], rest]] | p' == p && out' == out -> do
          more' <- go more (conjList rest) (p : ps) (pat : patsAcc)
          return (newVs ++ more')
        _ -> failWith (here ++ "splice chain test")

isIte :: Term -> Bool
isIte (Comp "->" [_, _]) = True
isIte (Comp "*->" [_, _]) = True
isIte _ = False

iteParts :: Term -> Maybe (Term, Term, Term)
iteParts t = case t of
  Comp ";" [Comp "->" [c, x], e] -> Just (c, x, e)
  Comp "->" [c, x] -> Just (c, x, Atom "fail")
  Comp "if_commit" [c, x, e] -> Just (c, x, e)
  Comp "once" [x] -> Just (x, Atom "true", Atom "fail")
  Comp "once_det" [x] -> Just (x, Atom "true", Atom "fail")
  Comp "ignore" [x] -> Just (x, Atom "true", Atom "true")
  _ -> Nothing

negOf :: Term -> Maybe Term
negOf (Comp "\\+" [x]) = Just x
negOf (Comp "not" [x]) = Just x
negOf _ = Nothing

-- | The fixed equivalences used by rule REWRITE.
rewriteOf :: Term -> Maybe Term
rewriteOf t = case t of
  Comp "forall" [c, a] -> Just (Comp "\\+" [Comp "," [c, Comp "\\+" [a]]])
  Comp "aggregate_all" [Comp "bag" [x], g, r] -> Just (Comp "findall" [x, g, r])
  Comp "decision" [cases, d] -> do
    cs <- either (const Nothing) Just (listOf cases)
    foldr (\c acc -> case c of
                       Comp "-" [cc, bb] -> fmap (\e -> Comp "if_commit" [cc, bb, e]) acc
                       _ -> Nothing) (Just d) cs
  Comp "call" (g : extra) | not (isVar g) -> addArgs g extra
  _ -> Nothing

definedHere :: Cx -> Term -> Bool
definedHere cx g = maybe False (`Set.member` cxDefined cx) (goalKey g)

isDetGoal :: Cx -> Term -> Bool
isDetGoal cx g = case goalKey g of
  Just k -> isBuiltinKey k && not (Set.member k (cxDefined cx))
            && k `notElem` nondetBuiltinKeys && k /= ("atom_concat", 3)
            && k `notElem` effectKeys && k `notElem` controlKeys
  Nothing -> False

isGenerator :: Cx -> Term -> Bool
isGenerator cx g = case goalKey g of
  Just k | Set.member k (cxDefined cx) -> not (Set.member k (cxEffectful cx))
         | k == ("member", 2) -> not (cxUserMember cx)
         | k == ("between", 3) -> True
  _ -> False

-- | Predicates that (transitively) write output, computed on the
-- intermediate program.
effectfulOf :: M.Map PredKey [Clause] -> Set.Set PredKey
effectfulOf inter = fixp direct
  where
    calls = M.map (concatMap (goalsOf . clBody)) inter
    direct = Set.fromList [ k | (k, cs) <- M.toList calls, any (`elem` effectKeys) cs ]
    fixp s = let s' = s `Set.union` Set.fromList [ k | (k, cs) <- M.toList calls, any (`Set.member` s) cs ]
             in if s' == s then s else fixp s'
    goalsOf t = case t of
      Comp op as | op `elem` [",", ";", "->", "*->", "if_commit", "\\+", "not", "once", "once_det", "ignore", "forall"] ->
        concatMap goalsOf as
      Comp "findall" [_, g, _] -> goalsOf g
      Comp "aggregate_all" [_, g, _] -> goalsOf g
      Comp "call" (g : extra) | Just g' <- addArgs g extra, not (isVar g) -> goalsOf g'
      _ -> maybe [] (: []) (goalKey t)

