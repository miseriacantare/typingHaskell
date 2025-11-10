module TypingHaskell where
import Data.List(nub, intersect, union)
import Data.List
import Text.Parsec
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)

type Index = Int
type Id = String
type Subst = [(Id, SimpleType)]

data Assump = Id :>: SimpleType deriving (Eq, Show)

data Kind = Kfun Kind Kind | Unit
            deriving Eq

data SimpleType = TVar Id
                | TCon Tycon
                | TArr SimpleType SimpleType
                | TGen Int
            deriving Eq

data Tycon = Tycon Id Kind
           deriving Eq

instance Show SimpleType where
    show (TVar i) = i
    show (TArr (TVar i) t) = i++ " -> " ++ show t
    show (TArr t t') = "("++ show t ++ ")" ++"->"++show t'

tArrow = TCon (Tycon "(->)" (Kfun Unit (Kfun Unit Unit)))
tList = TCon (Tycon "[]" (Kfun Unit Unit))
tProduct = TCon (Tycon "(,)" (Kfun Unit (Kfun Unit Unit)))

infixr 4 `fn`
fn :: SimpleType -> SimpleType -> SimpleType
a `fn` b = TArr (TArr tArrow a) b

list :: SimpleType -> SimpleType
list t = TArr tList t

class Subs t where
    apply :: Subst -> t -> t
    tv :: t -> [Id]

instance Subs SimpleType where
    apply s (TVar u) = case lookup u s of
                            Just t -> t
                            Nothing -> TVar u
    apply s (TArr l r) = (TArr (apply s l) (apply s r))

    tv (TVar u) = [u]
    tv (TArr l r) = tv l `union` tv r

instance Subs a => Subs [a] where
    apply s = map (apply s)
    tv = nub . concat . map tv

instance Subs Assump where
    apply s (i:>:t) = i:>:apply s t
    tv (i:>:t) = tv t

data TI a = TI (Index -> (a,Index))

instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a,e))
   TI fs <*> TI vs = TI (\e -> let (f,e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
   TI m >>= f = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

t --> t' = TArr t t'

infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u,apply s1 t) | (u,t) <- s2] ++ s1

as /+/ as' = as' ++ filter compl as
   where is = dom as'
         compl (i:>:_) = notElem i is

dom = map (\(i:>:_)-> i)

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++ show e in (TVar v, e+1))

runTI (TI m) = let (t, _) = m 0 in t

varBind :: Id -> SimpleType -> Maybe Subst
varBind u t | t == TVar u = Just []
            | u `elem` tv t = Nothing
            | otherwise = Just [(u,t)]

mgu (TArr l r, TArr l' r') = do s1 <- mgu (l,l')
                                s2 <- mgu ((apply s1 r),(apply s1 r'))
                                return (s2 @@ s1)
mgu (t, TVar u) = varBind u t
mgu (TVar u, t) = varBind u t

unify t t' = case mgu (t,t') of
      Nothing -> error ("\nTrying to unify: " ++ (show t) ++ " and " ++ (show t') ++ "\n")
      Just s -> s

---------------- Inference Algorithm ---------------

data Expr = Var Id
          | App Expr Expr
          | Lamb Id Expr
     deriving (Eq,Show)

tiContext g i = if l /= [] then t else error ("Unndefined: " ++ i ++ "\n")
    where l = dropWhile (\(i' :>: _) -> i /= i') g
          (_ :>: t) = head l

tiExpr g (Var i) = return (tiContext g i, [])
tiExpr g (App e e') = do (t,s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t'-->b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lamb i e) = do b <- freshVar
                         (t,s) <- tiExpr (g/+/[i:>:b]) e
                         return (apply s (b --> t),s) 

infer e = runTI (tiExpr [] e)

-------- Parsing the Expression -----------
lingDef = emptyDef
          { L.commentLine = "--"
           ,L.identStart = letter
           ,L.identLetter = letter
          }

lexical = L.makeTokenParser lingDef

symbol = L.symbol lexical
parens = L.parens lexical
identifier = L.identifier lexical
comma = L.comma lexical

parseExpr = runParser expr [] "lambda-calculus"

expr :: Parsec String u Expr
expr = chainl1 parseNonApp $ return $ App

var = do {i <- identifier; return (Var i)}

lamApps = do  symbol "\\"
              i <- identifier
              symbol "."
              symbol "("
              e' <- expr
              symbol ","
              e <- expr
              symbol ")"
              return (App e' e)

lamAbs = do symbol "\\"
            i <- identifier
            symbol "."
            e <- expr
            return (Lamb i e)

parseNonApp = parens expr
              <|> lamAbs
              <|> lamApps
              <|> var

------------- Driver Code --------------

parseLambda s = case parseExpr s of
                Left er -> print er
                Right e -> (print e >> print (infer e))

main = do putStr "Lambda: "
          e <- getLine
          parseLambda e
