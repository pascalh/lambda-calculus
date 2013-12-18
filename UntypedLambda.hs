{-|
simple implementation of untyped lambda-calculus based on the book

[1] : J. Roger Hindley, Basic simple type theory, 
      Cambridge University Press, 1997

-}
module UntypedLambda where
import Prelude hiding (null,filter,map,length,rem)
import qualified Data.List as List
import Data.Set hiding (fold)
import Data.Tree

-- |a variable is represented by a name and a numerical index
data Var = Var { name :: Char  -- ^ variable name
               , index :: Int -- ^ variable index
               }  deriving (Ord,Eq)

instance Show Var where
  show (Var c 0) = return c
  show (Var c i) = return c ++ show i

-- |this data type represents untyped lambda terms
data Lambda = Lambda Var Lambda -- ^ abstraction
            | App Lambda Lambda -- ^ application
            | LVar Var          -- ^ term variable
            deriving (Eq,Ord)


instance Show Lambda where
  show (LVar v) = show v
  show (App (LVar v1) (LVar v2)) = show v1 ++" "++ show v2
  show (App e1 (LVar v)) = "("++show e1++") " ++show v 
  show (App e1 e2) = "("++show e1++") ("++show e2++")" 
  show t@(Lambda _ _) = 
    let (vs,p) = multipleAbstractions t 
    in"\\"++concatMap (\v -> show v ++" ") vs 
          ++ ". "++show p
    where

      multipleAbstractions :: Lambda -> ([Var],Lambda)
      multipleAbstractions = flip helper [] where
        helper :: Lambda -> [Var] -> ([Var],Lambda)
        helper (Lambda v e) vs = helper e (vs++[v]) 
        helper  e vs           = (vs,e)

-- |a catamorphism for lambda terms
--      lambda             app              lvar
fold :: (Var -> a -> a) -> (a -> a -> a) -> (Var -> a) -> Lambda -> a
fold _ _ h (LVar v)     = h v
fold f g h (Lambda v e) = f v (fold f g h e) 
fold f g h (App e1 e2)  = g (fold f g h e1) (fold f g h e2)

-- * variables

-- returns one fresh term variable which does not occour in given lambda term
freshTermVar :: Lambda -> Var
freshTermVar = head . toList . freshVars 1 . vars 

-- returns n distinct fresh variables which do not occour in given set. Note
-- that this function works on an arbitrary variable set.
freshVars :: Int -> Set Var -> Set Var
freshVars n = fromList . getFreshN' n . toList where

  getFreshN' :: Int -> [Var] -> [Var]
  getFreshN' n []             = take n $ zipWith Var ['x'..] [0,1..]
  getFreshN' n (v@(Var c _):vs) = 
    let m = maximum $ 
            List.map index $ 
            List.filter ((==c) . name) 
            (v:vs)
    in take n $ zipWith Var [c,c..] [1+m,2+m..]

-- |all variables in given lambda term
vars :: Lambda -> Set Var
vars = fold insert union singleton

-- |returns all variables which are not bound by a lambda abstraction
freeVars :: Lambda -> Set Var
freeVars = fold delete union singleton

-- |returns all variables which are bound by a lambda abstraction
boundVars :: Lambda -> Set Var
boundVars l = difference (vars l) (freeVars l)

-- |the length of a lambda term, see [1] 1A2 
length :: Lambda -> Int
length = fold (\_ l -> 1+l) (+) (const 1)

-- |all subterms of given lambda term, see [1] 1A3
subterms :: Lambda -> [Lambda]
subterms e@(LVar _)     = [e]
subterms e@(Lambda _ t) = e : subterms t
subterms e@(App e1 e2)  = e : (subterms e1 ++ subterms e2)

-- |a lambda term is closed iff it has no free variables
closed :: Lambda -> Bool
closed = null . freeVars

-- |returns a functions, which substitutes all free occourences of @x@ by @n@ 
sub :: Var -> Lambda -> Lambda -> Lambda
sub x n (LVar y) | x == y = n 
                 | x /= y = LVar y  
sub x n (App p q) = App (sub x n p) (sub x n q)
sub x n (Lambda y p)
  | x == y                                               = Lambda x p 
  | not $ member x (freeVars p)                          = Lambda y p
  | member x (freeVars p) && not (member y (freeVars n)) = Lambda y (sub x n p)
  | member x (freeVars p) && member y (freeVars n)       = 
     let z = freshTermVar $ App n p 
     in Lambda z $ sub x n $ sub y (LVar z) p

-- * beta reduction

-- |returns all beta redexes of given lambda term
betaRedexes :: Lambda -> [Lambda] 
betaRedexes (LVar _)                = [] 
betaRedexes e@(App (Lambda _ e1) e2) = e : (betaRedexes e1 ++ betaRedexes e2)
betaRedexes (App e1 e2)              = betaRedexes e1 ++ betaRedexes e2
betaRedexes (Lambda _ f)             = betaRedexes f

-- |determines whether given lambda term contains at least one beta redex
hasBetaRedex :: Lambda -> Bool
hasBetaRedex = not . List.null . betaRedexes

-- |determines whether given lambda term is in beta normal form, i.e. contains
-- no beta redex
inBetaNF :: Lambda -> Bool
inBetaNF = not . hasBetaRedex

-- |computes the beta normal form of a lambda term
betaNF :: Lambda -> Lambda
betaNF t
  | hasBetaRedex t = betaNF $ betaReduction t
  | otherwise      = t

-- |one step beta reduction
betaReduction :: Lambda -> Lambda
betaReduction (App (Lambda v e) a) = sub v a e
betaReduction (App e1 e2)          
  | e1 == betaReduction e1 = App e1 (betaReduction e2)
  | otherwise               = App (betaReduction e1) e2
betaReduction (Lambda v e)         = Lambda v $ betaReduction e
betaReduction (LVar v)             = LVar v

-- * eta reduction

-- |determines whether given lambda term is in eta normal form, i.e. contains
-- no eta redex
inEtaNF :: Lambda -> Bool
inEtaNF = not . hasEtaRedex

-- |determines whether given lambda term contains at least one eta redex
hasEtaRedex :: Lambda -> Bool
hasEtaRedex (LVar _)                    = False
hasEtaRedex (App e1 e2)                 = hasEtaRedex e1 || hasEtaRedex e2
hasEtaRedex (Lambda v (App f (LVar u))) = v==u && not (member u $ freeVars f) || hasEtaRedex f 
hasEtaRedex (Lambda _ e)                = hasEtaRedex e

-- |computes the eta normal form of a lambda term
etaNF :: Lambda -> Lambda
etaNF t 
  | hasEtaRedex t = etaNF $ etaReduction t
  | otherwise     = t

-- |one step eta reduction
etaReduction :: Lambda -> Lambda
etaReduction (Lambda v (App f (LVar u))) 
  | v==u && not (member u $ freeVars f) = etaReduction f
  | otherwise                           = Lambda v (App (etaReduction f) (LVar u))
etaReduction (App e1 e2)  
  | e1 == etaReduction e1 = App e1 (etaReduction e2)
  | otherwise             = App (etaReduction e1) (etaReduction e2)
etaReduction (Lambda v f) = Lambda v (etaReduction f)
etaReduction (LVar v)     = LVar v

-- * alpha reduction

-- |one step alpha reduction
alphaReduction :: Lambda -> Lambda 
alphaReduction (Lambda x f) = 
  let y = freshTermVar f in Lambda y $ sub x (LVar y) f
alphaReduction t@(LVar _)   = LVar $ freshTermVar t
alphaReduction (App e1 e2)  =
  if alphaReduction e1 == e1
  then App e1 (alphaReduction e2)
  else App (alphaReduction e1) (alphaReduction e2)
  
-- |returns whether both lambda terms are equivalent up to 
-- bound variable renaming
alphaEquiv :: Lambda -> Lambda -> Bool
alphaEquiv (LVar x) (LVar y)   = x == y
alphaEquiv (App a b) (App x y) = alphaEquiv a x && alphaEquiv b y
alphaEquiv (Lambda x f) (Lambda y g) =
  alphaEquiv f $ sub y (LVar x) g
alphaEquiv _ _ = False


-- * beta-eta-reduction 

-- |determines whether given lambda term has a beta or an eta redex,
-- ([1] 1C5)
hasBetaEtaRedex :: Lambda -> Bool
hasBetaEtaRedex e = hasEtaRedex e || hasBetaRedex e

-- |first try to apply a beta reduction and then a eta reduction,
-- ([1] 1C7)
betaEtaReduction :: Lambda -> Lambda
betaEtaReduction = etaReduction . betaReduction

-- |computes the beta-eta formal form 
betaEtaNF :: Lambda -> Lambda
betaEtaNF t
  | hasBetaEtaRedex t = betaEtaNF $ betaEtaReduction t
  | otherwise         = t

-- * visualization of reductions

-- ** a sequential visualization of left-outermost beta reduction

betaNFSteps :: Lambda -> [Lambda]
betaNFSteps l = case betaRedexes l of
  []     -> [l]
  (x:_)  -> x : betaNFSteps (betaReduction l)

visualizeBeta :: Lambda -> IO ()
visualizeBeta l = 
  let betas = betaNFSteps l in mapM_ (putStrLn . (\s -> " ==> " ++ s) .  show) betas

-- ** tree based visualization of all possible beta reductions

rList :: (Lambda -> Lambda) -> Lambda -> Set Lambda
rList f (LVar v)  = singleton $ f $ LVar v
rList f p@(App m n) = insert (f $ betaReduction p) $ 
  rList (\x -> f $ App x n) m  `union` rList (f . App m) n 
rList f (Lambda v e) = rList (f . Lambda v) e

-- |builds the tree of all possible reductions
rTree :: Lambda -> Tree Lambda
rTree x = Node x (List.map rTree . toList . delete x $ rList id x)

-- |draws the tree with all possible reductions
drawPossibleReductions ::Lambda -> IO ()
drawPossibleReductions = putStrLn . drawTree . fmap show . rTree 


-- * example lambda terms

a = Var 'a' 0
b = Var 'b' 0
p = Var 'p' 0
v = Var 'v' 0 
u = Var 'u' 0 
w = Var 'w' 0 
x = Var 'x' 0 
z = Var 'z' 0 
x1 = Var 'x' 1
x2 = Var 'x' 2

-- ** well known functions

-- |identity function
idLambda  = Lambda x2 (LVar x2)

-- |constant function
constLambda  = Lambda x (LVar z)

-- |applying betaReduction to omega yields omega, thus the evaluation to betanf 
-- diverges 
omega = let f = Lambda x (LVar x `App` LVar x) in App f f

-- |the well known fixed point combinator
y = let f = Lambda x (App (LVar h) (App (LVar x) (LVar x))) 
        h = Var 'h' 0
    in Lambda h $ App f f

-- ** church encodings of basic logic
true = Lambda x (Lambda v (LVar x))
false = Lambda x (Lambda v (LVar v))
implication = Lambda x $ Lambda z $ LVar x `App` LVar z `App` true

ifthenelse = 
  Lambda p $ Lambda a $ Lambda b $ LVar p `App` LVar a `App` LVar b

ifBetaNf = betaNF $ ((ifthenelse `App` true) `App` LVar x1) `App` LVar x2


-- ** other example functions

bspEta      = Lambda  v (Lambda u (App idLambda (LVar u)))
bspEtaAlpha = Lambda  w $ LVar x `App` LVar w

bspBeta = App bspEta (LVar x1)

bspBetaScope = 
  App 
    (Lambda u (App (LVar x) (Lambda u (App (LVar u) (LVar u))))) 
    (LVar x2)

bspBetaScope2 = 
  App 
    (Lambda u (App (LVar x) (Lambda w (App (LVar u) (LVar u))))) 
    (LVar x2)





-- p 199: theories of programming langs, 
-- crt does not evaluate using the innermost beta-redex
crt = App (Lambda u idLambda) omega

-- p200: theories of pl

bspJohn = 
  Lambda x (Lambda w (LVar w `App` LVar x) `App` LVar z)
  `App` 
  (LVar z `App` LVar x2)


-- an example term for beta-eta reduction. be-reduces to z
be = Lambda x (idLambda `App` LVar z) `App` LVar x


blaa = Lambda x (LVar v `App` LVar x) `App` Lambda v (LVar v)

ll = Lambda u $ Lambda x2 (LVar x)



