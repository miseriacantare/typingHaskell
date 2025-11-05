module TypingHaskell where
import Data.List(nub, intersect,union)

type Index = Int
type Id = String
type Subst = [(Id, SimpleType)]

data Assump = Id :>: SimpleType deriving (Eq, Show)


data SimpleType = TVar Id 
                | TArr SimpleType SimpleType
            deriving Eq

instance Show SimpleType where
    show (TVar i) = i
    show (TArr (TVar i) t) = i++ " -> " ++ show t
    show (TArr t t') = "("++ show t ++ ")" ++"->"++show t'

class Subs t where
    apply :: Subst -> t -> t
    tv :: t -> [Id]

instance Subs SimpleType where
    apply s (TVar u) = case lookup u s of
                            Just t -> t
                            Nothing -> TVar u
    apply s (TArr l r) = (TArr (apply s l) (apply s r))

tv (TVar u) = [u]
tv (TArr l r) tv l `union` tv r

instance Subs a => Subs [a] where
    apply s = map (apply s)
    tv = nub . concat . map tv

instance Subs Assump where
    apply s (i:>:t) = i:>:apply s t
    tv (I:>:) = tv t

data TI a = TI (Index -> (a,Index))

instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a,e))
   TI fs <*> TI vs = TI (\e -> let (f,e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
--   return x = TI (\e -> (x,e))
   TI m >>= f = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++ show e in (TVar v, e+1))

runTI (TI m) = let (t, _) = m 0 in t


