{-# LANGUAGE NoImplicitPrelude, TypeSynonymInstances, FlexibleInstances #-}
module R7RSDS where

import Prelude hiding ( lookup )

import qualified Data.IntMap as IntMap
import qualified Data.Map    as Map

{- Denotational Semantics of R7RS scheme, written in Haskell -}

-- Denotational Domain
type Ide = String

data Exp = Econst ScmPrimVal
         | Eapply Exp [Exp]
         | Eide Ide
         | Elambda Args [Exp] Exp
         | Eif Exp Exp Exp
         | Eset Ide Exp
         deriving (Show)

data Args = Args [Ide] | VArgs [Ide] Ide
          deriving (Show)


type ScmIde           = String
type ScmNat           = Int
type ScmCharacter     = String
type ScmNumber        = Double
data ScmBoolean       = ScmTru | ScmFls deriving (Show, Eq)
data ScmPrimVal       = ScmSymbol String | ScmChars String | ScmNum Int
                      deriving (Show, Eq)
type ScmLocation      = Int


type ScmProcedureValue = ( ScmLocation
                         , [ScmExpressedValue] -> ScmDynamicPoint -> 
                           ScmExpCont -> ScmCommandCont
                         )

instance Show ([ScmExpressedValue]
               -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont) where
  show s = "#<procedure>"
             
data ScmExpressedValue  = EVprim ScmPrimVal -- Q + H + R
                        | EVpair ScmLocation ScmLocation ScmBoolean
                        | EVvector [ScmLocation] ScmBoolean
                        | EVstring [ScmLocation] ScmBoolean
                        | EVundefined
                        | EVunspecified
                        | EVnull
                        | EVboolean ScmBoolean
                        | EVprocval ScmProcedureValue
                        deriving (Show)

type ScmEnvironmnt   = Map.Map Ide ScmLocation
data ScmDynamicPoint = ScmDynamicPoint ScmProcedureValue ScmProcedureValue ScmDynamicPoint
                     | ScmRoot
type ScmExpCont      = [ScmExpressedValue] -> ScmCommandCont
type ScmCommandCont  = ScmStore -> ScmAnswer
type ScmStore        = IntMap.IntMap (ScmExpressedValue, ScmBoolean)
type ScmError        = String
type ScmAnswer       = ScmExpressedValue

instance Eq ScmDynamicPoint where
  (==) ScmRoot ScmRoot = True
  (==) (ScmDynamicPoint _ _ p1) (ScmDynamicPoint _ _ p2) = p1 == p2

--- Semantic Function
semConst :: ScmPrimVal -> ScmExpressedValue
semConst x = EVprim x

semEval :: Exp
        -> ScmEnvironmnt
        -> ScmDynamicPoint
        -> ScmExpCont
        -> ScmCommandCont
semEval (Econst x) = \env point cont ->
  send (semConst x) cont
semEval (Eide i) = \env point cont ->
  hold (lookup env i)
       (single (\ exp -> case exp of
                   EVundefined -> wrong ("undefined value: " ++ show i)
                   _ -> send exp cont))
semEval (Eapply exp exps) = \env point cont ->
  semEvals (permute $ exp:exps)
           env point 
           (\exps -> case unpermute exps of
               (exp:exps) -> applicate exp exps point cont)
semEval (Elambda (Args ides) gammas exp) = \env point cont ->
  \store -> let newloc = new store in
    send (EVprocval (newloc, \exps point' cont' ->
                      if length exps == length ides
                      then tievals 
                           (\locs -> let env' = extends env ides locs in
                             semCommand gammas env' point' 
                                        (semEval exp env' point' cont'))
                           exps
                      else wrong "wrong number of arguments"))
         cont (update newloc EVunspecified store)
semEval (Elambda (VArgs ides ide) gammas exp) = \env point cont ->
  \store -> let newloc = new store in
    send (EVprocval (newloc, \exps point' cont' -> 
                      if length exps >= length ides 
                      then tievalsrest 
                           (\locs -> let env' = extends env (ides++[ide]) locs in
                             semCommand gammas env' point' 
                                        (semEval exp env' point' cont'))
                           exps (length ides) point'
                      else wrong "too few arguments"))
         cont (update newloc EVunspecified store)
semEval (Eif expCond expThen expElse) = \env point cont ->
  semEval expCond env point (single $ \exp -> case truish exp of
                             ScmTru -> semEval expThen env point cont
                             ScmFls -> semEval expElse env point cont)
semEval (Eset ide exp) = \env point cont -> 
  semEval exp env point (single $ \exp -> assign (lookup env ide)
                                                 exp
                                                 (send EVunspecified cont))

semEvals :: [Exp] -> ScmEnvironmnt
            -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
semEvals [] = \env point cont -> cont []
semEvals (exp:exps) = \env point cont ->
  semEval exp env point (single $ \ exp -> semEvals exps env point 
                                                    (\exps -> cont (exp:exps)))


semCommand :: [Exp]
            -> ScmEnvironmnt
            -> ScmDynamicPoint
            -> ScmCommandCont
            -> ScmCommandCont
semCommand [] = \env point cont -> cont
semCommand (gamma:gammas) = \env point cont ->
  semEval gamma env point (\exps -> semCommand gammas env point cont)

--- Auxiliary Functions
lookup :: ScmEnvironmnt -> Ide -> ScmLocation
lookup env ide = env Map.! ide

extends :: ScmEnvironmnt -> [Ide] -> [ScmLocation] -> ScmEnvironmnt
extends env [] _ = env
extends env (ide:ides) (loc:locs) =
  extends (Map.insert ide loc env) ides locs

send :: ScmExpressedValue -> ScmExpCont -> ScmCommandCont
send e k = k [e]

new :: ScmStore -> ScmLocation
new store = 1 + (findMax' store)
  where findMax' m | IntMap.null store = -1
                   | otherwise = fst $ IntMap.findMax m

hold :: ScmLocation -> ScmExpCont -> ScmCommandCont
hold loc kont = \store ->
  send (fst $ store IntMap.! loc) kont store

wrong :: ScmError -> ScmCommandCont
wrong msg = \cont -> error msg

single :: (ScmExpressedValue -> ScmCommandCont) -> ScmExpCont
single phi (exp:[]) = phi exp
single _ _          = wrong "wrong number of return values"

truish :: ScmExpressedValue -> ScmBoolean
truish (EVboolean ScmFls) = ScmFls
truish _                  = ScmTru


assign :: ScmLocation -> ScmExpressedValue -> ScmCommandCont -> ScmCommandCont
assign loc val cmdCont store = cmdCont (update loc val store)

update :: ScmLocation -> ScmExpressedValue -> ScmStore -> ScmStore
update loc val store = IntMap.insert loc (val, ScmTru) store


tievals :: ([ScmLocation] -> ScmCommandCont) -> [ScmExpressedValue] -> ScmCommandCont
tievals psi [] store = psi [] store
tievals psi (exp:exps) store =
  let ns = new store in
  tievals (\locs -> psi (ns:locs))
          exps
          (update ns exp store)

tievalsrest :: ([ScmLocation] -> ScmCommandCont) -> [ScmExpressedValue] 
               -> ScmNat -> ScmDynamicPoint -> ScmCommandCont
tievalsrest psi exps n point =
  list (dropfirst exps n) point
       (single (\exp -> tievals psi ((takefirst exps n) ++ [exp])))

dropfirst l 0 = l
dropfirst l n = dropfirst (tail l) (n-1)

takefirst l 0 = []
takefirst (x:xs) n = x : takefirst xs (n-1)

list :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
list [] point cont = send EVnull cont
list (exp:exps) point cont = 
  list exps point (single (\exp' -> cons [exp, exp'] point cont))

cons :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
cons = twoarg (\exp1 exp2 point cont store -> 
                let newloc = new store in
                (\store' -> let newloc' = new store' in
                  send (EVpair newloc newloc' ScmTru)
                       cont
                       (update newloc' exp2 store'))
                (update newloc exp1 store))

onearg :: (ScmExpressedValue -> ScmDynamicPoint
           -> ScmExpCont -> ScmCommandCont)
          -> ([ScmExpressedValue] -> ScmDynamicPoint 
              -> ScmExpCont -> ScmCommandCont)
onearg xi [exp] point cont = xi exp point cont
onearg _  []    _     _    = wrong "onearg: wrong number of arguments"

twoarg :: (ScmExpressedValue -> ScmExpressedValue -> ScmDynamicPoint
           -> ScmExpCont -> ScmCommandCont)
          -> ([ScmExpressedValue] -> ScmDynamicPoint 
              -> ScmExpCont -> ScmCommandCont)
twoarg xi [exp1, exp2] point cont = xi exp1 exp2 point cont
twoarg _ _ _ _ = wrong "twoarg: wrong number of arguments"

threearg :: (ScmExpressedValue -> ScmExpressedValue -> ScmExpressedValue
             -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont)
            -> ([ScmExpressedValue] -> ScmDynamicPoint 
                -> ScmExpCont -> ScmCommandCont)
threearg xi [exp1, exp2, exp3] point cont = xi exp1 exp2 exp3 point cont
threearg _ _ _ _ = wrong "threearg: wrong number of arguments"

permute :: [Exp] -> [Exp]
permute exps = exps

unpermute :: [ScmExpressedValue] -> [ScmExpressedValue]
unpermute exps = exps

applicate :: ScmExpressedValue -> [ScmExpressedValue] ->
             ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
applicate (EVprocval (_, p)) exps point kont = p exps point kont
applicate _ _ _ _ = wrong "applicate: bad procedure"

less :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
less = twoarg (\exp1 exp2 point cont ->
                case (exp1, exp2) of
                  (EVprim (ScmNum n1), EVprim (ScmNum n2)) -> 
                    send (EVboolean $ if n1 < n2 then ScmTru else ScmFls) cont
                  _ -> 
                    wrong "<: non-numeric arguments")

add :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
add = twoarg (\exp1 exp2 point cont ->
               case (exp1, exp2) of
                  (EVprim (ScmNum n1), EVprim (ScmNum n2)) -> 
                    send (EVprim $ ScmNum $ n1 + n2) cont
                  _ -> 
                    wrong "+: non-numeric arguments")

car :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
car = onearg (\exp point cont -> carInternal exp cont)

carInternal =  \exp cont -> 
  case exp of
    EVpair loc _ _ -> hold loc cont
    _ -> wrong "car: non-pair argument"

cdr :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
cdr = onearg (\exp point cont -> cdrInternal exp cont)

cdrInternal = \exp cont -> 
  case exp of
    EVpair _ loc _ -> hold loc cont
    _ -> wrong "cdr: non-pair argument"

setcar :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
setcar = twoarg (\exp1 exp2 point cont ->
                  case exp1 of
                    EVpair loc _ ScmTru -> assign loc exp2 (send EVunspecified cont)
                    EVpair _   _ ScmFls -> wrong "setcar: immutable argument"
                    _ -> wrong "setcar: non-pair argument")

boolToScmBoolean True  = ScmTru
boolToScmBoolean False = ScmFls

eqv :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
eqv = twoarg (\exp1 exp2 point cont ->
               case (exp1, exp2) of
                 (EVboolean b1, EVboolean b2) ->
                   send (EVboolean $ boolToScmBoolean $ b1 == b2) cont
                 (EVundefined, EVundefined) ->
                   send (EVboolean ScmTru) cont
                 (EVunspecified, EVunspecified) -> 
                   send (EVboolean ScmTru) cont
                 (EVnull, EVnull) ->
                   send (EVboolean ScmTru) cont
                 (EVprim p1, EVprim p2) ->
                   send (EVboolean $ boolToScmBoolean $ p1 == p2) cont
                 (EVpair loc1 loc1' _, EVpair loc2 loc2' _) ->
                   send (EVboolean $ boolToScmBoolean $
                          loc1 == loc2 && loc1' == loc2') cont
                 (EVvector locs1 _, EVvector locs2 _) ->
                   send (EVboolean $ boolToScmBoolean $ locs1 == locs2) cont
                 (EVstring locs1 _, EVstring locs2 _) ->
                   send (EVboolean $ boolToScmBoolean $ locs1 == locs2) cont
                 _ -> send (EVboolean ScmFls) cont)

apply :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
apply = twoarg (\exp1 exp2 point cont ->
                 case exp1 of
                   EVprocval p -> 
                     valueslist [exp2] (\exps -> applicate exp1 exps point cont)
                   _ -> wrong "apply: bad procedure argument")

valueslist :: [ScmExpressedValue] -> ScmExpCont -> ScmCommandCont
valueslist = \[exp] cont -> case exp of
  EVpair _ _ _ -> cdrInternal exp (\exps ->
                                    valueslist exps
                                    (\exps -> carInternal exp
                                              (single (\exp ->
                                                        cont $ exp : exps))))

cwcc :: [ScmExpressedValue] -> ScmDynamicPoint -> ScmExpCont -> ScmCommandCont
cwcc = onearg (\exp point cont -> case exp of 
                  EVprocval procedure -> \store ->
                    let newloc = new store in
                    applicate exp [EVprocval (newloc, \exps point' cont' ->
                                               travel point' point (cont exps))]
                              point cont (update newloc EVunspecified store)
                  _ -> wrong "cwcc: bad procedure argument")

travel :: ScmDynamicPoint -> ScmDynamicPoint -> ScmCommandCont -> ScmCommandCont
travel = \point1 point2 -> 
  travelpath ((pathup point1 (commonancest point1 point2))
              ++ (pathdown (commonancest point1 point2) point2))

pointdepth :: ScmDynamicPoint -> Int
pointdepth ScmRoot = 0
pointdepth (ScmDynamicPoint _ _ point) = 1 + (pointdepth point)

ancestors :: ScmDynamicPoint -> [ScmDynamicPoint]
ancestors ScmRoot = [ScmRoot]
ancestors (ScmDynamicPoint _ _ point) = point : ancestors point

commonancest :: ScmDynamicPoint -> ScmDynamicPoint -> ScmDynamicPoint
commonancest = \point1 point2 ->
  head [ point | point <- (ancestors point1 ++ ancestors point2)
               , all (\point' -> pointdepth point >= pointdepth point')
                     (ancestors point1 ++ ancestors point2) ]

pathup :: ScmDynamicPoint -> ScmDynamicPoint
          -> [(ScmDynamicPoint, ScmProcedureValue)]
pathup point1@(ScmDynamicPoint _ p point1') point2
  | point1 == point2 = []
  | otherwise = (point1, p) : pathup point1' point2

pathdown :: ScmDynamicPoint -> ScmDynamicPoint 
            -> [(ScmDynamicPoint, ScmProcedureValue)]
pathdown point1 point2@(ScmDynamicPoint _ p point2')
  | point1 == point2 = []
  | otherwise = pathdown point1 point2' ++ [(point2, p)]

travelpath :: [(ScmDynamicPoint, ScmProcedureValue)] 
              -> ScmCommandCont -> ScmCommandCont
travelpath [] ccont = ccont
travelpath ((ScmDynamicPoint _ (_, proc2) p1, _):pis) ccont = 
  proc2 [] p1 (\exps -> travelpath pis ccont)

dynamicwind :: [ScmExpressedValue] -> ScmDynamicPoint 
               -> ScmExpCont -> ScmCommandCont
dynamicwind = 
  threearg (\exp1 exp2 exp3 point cont -> 
             case (exp1, exp2, exp3) of
               (EVprocval p1, EVprocval p2, EVprocval p3) ->
                 applicate exp1 [] point
                   (\xis ->
                     applicate exp2 [] (ScmDynamicPoint p1 p3 point)
                       (\exps -> applicate exp3 [] point (\xis -> cont exps)))
               _ -> wrong "dynamicwind: bad procedure argument")

values :: [ScmExpressedValue] -> ScmDynamicPoint
          -> ScmExpCont -> ScmCommandCont
values = \exps point cont -> cont exps

cwv :: [ScmExpressedValue] -> ScmDynamicPoint 
       -> ScmExpCont -> ScmCommandCont
cwv = twoarg $ \exp1 exp2 point cont ->
  applicate exp1 [] point (\exps -> applicate exp2 exps point cont)

-- evaluation and print
eval :: Exp -> ScmExpCont -> ScmAnswer
eval exp cont = semEval exp initEnv ScmRoot cont initStore

evalShow exp = case eval exp showCont of
  EVprim (ScmSymbol s) -> s
  where showCont exps store = 
          EVprim $ ScmSymbol $ unlines $ map (resolveShow store) exps
        resolveShow store expr = case expr of
          EVprim (ScmSymbol s) -> '\'' : s
          EVprim (ScmChars s) -> s
          EVprim (ScmNum n) -> show n
          p@(EVpair _ _ _) ->
            "(" ++ unwords (resolvePair p) ++ ")"
          EVvector locs _ ->
            "[" ++
            unwords (map (\loc -> resolveShow store (resolve loc)) locs)
            ++ "]"
          EVstring locs _ ->
            "\"" ++ 
            concat (map (\loc -> resolveShow store (resolve loc)) locs)
            ++ "\""
          EVundefined -> "#<undef>"
          EVunspecified -> "#<unspecified>"
          EVnull -> "()"
          EVboolean ScmTru -> "#t"
          EVboolean ScmFls -> "#f"
          EVprocval _ -> "#<procedure>"
          where resolve loc = fst (store IntMap.! loc)
                resolvePair (EVpair loc1 loc2 _) = 
                  resolveShow store (resolve loc1) : resolvePair (resolve loc2)
        

(initStore, initEnv) = 
  makeEnv [ ("cons", cons)
          , ("car", car)
          , ("cdr", cdr)
          , ("<", less)
          , ("+", add)
          , ("eqv?", eqv)
          , ("set-car!", setcar)
          , ("apply", apply)
          , ("call-with-current-continuation", cwcc)
          , ("call/cc", cwcc)
          , ("values", values)
          , ("call-with-values", cwv)
          , ("dynamic-wind", dynamicwind)
          ]

makeEnv nameVals = (initStore, initEnv)
  where (names, vals) = split nameVals ([], [])
        loop store locs [] = (store, reverse locs)
        loop store locs (v:vs) =
          let newloc = new store in
          loop (update newloc (EVprocval (newloc, v)) store) (newloc:locs) vs
        (initStore, locs) = loop IntMap.empty [] vals
        initEnv = extends Map.empty names locs

split [] plst = plst
split ((v1, v2):vs) (ls1, ls2) = split vs (v1:ls1, v2:ls2)

