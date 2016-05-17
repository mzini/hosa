module HoSA.SizeType.Index (
  -- * Index Terms
  Term (..)
  , Var (..)
  , VarId
  , Sym (..)
  , MetaVar (..)
  , fvar
  , bvar
  , ixZero
  , ixSucc
  , ixSum
  , fvars
  , metaVar
  , freshMetaVar
  , substituteMetaVar
  , unsafePeakVar
  -- * Constraints
  , Constraint (..)
  -- * Substitutions on Index Terms
  , Substitutable (..)
  , Subst
  , idSubst
  , after
  , o
  , inst
  , substFromList
  ) where

import HoSA.Utils
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)

import Data.Maybe (fromMaybe)

type VarId = Int

data Var = BVar VarId | FVar VarId deriving (Eq, Ord)

data MetaVar = MetaVar Unique (IORef (Maybe Term))

data Sym = Sym { ixsName :: Maybe String, ixsId :: Unique } deriving (Eq, Ord)

data Term =
  Zero
  | Succ Term
  | Sum [Term]
  | Fun Sym [Term]
  | Var Var
  | MVar MetaVar

data Constraint = Term :>=: Term

infixr 0 :>=:

fvar :: VarId -> Term
fvar = Var . FVar

bvar :: VarId -> Term
bvar = Var . BVar

ixZero :: Term
ixZero = Zero

ixSucc :: Term -> Term
ixSucc = Succ

ixSum :: [Term] -> Term
ixSum [] = ixZero
ixSum [t] = t
ixSum ts = Sum ts

metaVar :: MetaVar -> Term
metaVar = MVar

freshMetaVar :: MonadIO m => Unique -> m MetaVar
freshMetaVar u = MetaVar u <$> liftIO (newIORef Nothing)

substituteMetaVar :: MonadIO m => MetaVar -> Term -> m Bool
substituteMetaVar (MetaVar _ ref) t = do
  c <- liftIO (readIORef ref)
  case c of
    Nothing -> liftIO (writeIORef ref (Just t)) >> return True
    _ -> return False

unsafePeakVar :: MetaVar -> Either Unique Term
unsafePeakVar (MetaVar u ref) =
  case unsafePerformIO (readIORef ref) of
    Nothing -> Left u
    Just ix -> Right ix

fvars :: Term -> [VarId]
fvars Zero = []
fvars (Succ ix) = fvars ix
fvars (Sum ixs) = concatMap fvars ixs
fvars (Fun _ ixs) = concatMap fvars ixs
fvars (Var (BVar _)) = []
fvars (Var (FVar v)) = [v]
fvars (MVar mv) = either err fvars (unsafePeakVar mv) where
  err _ = error "HoSA.Index.fvars: free variables on terms with meta-variables cannot be determined"



-- pretty printers

prettyFn :: PP.Pretty a => String -> [a] -> PP.Doc
prettyFn n as = PP.text n PP.<> prettyArgLst as

prettyArgLst :: PP.Pretty a => [a] -> PP.Doc
prettyArgLst as = PP.encloseSep PP.lparen PP.rparen PP.comma [PP.pretty ai | ai <- as]

instance PP.Pretty Var where
  pretty (BVar i) = PP.text "x" PP.<> PP.int i
  pretty (FVar i) = PP.text "y" PP.<> PP.int i

instance PP.Pretty Sym where
  pretty (Sym mn u) = PP.text n PP.<> PP.int (uniqueToInt u) where
    n = fromMaybe "f" mn

instance PP.Pretty Term where
  pretty Zero = PP.text "0"
  pretty (Succ ix) = prettyFn "s" [ix]
  pretty (Sum ixs) = prettyFn "sum" ixs
  pretty (Fun sym as) = PP.pretty sym PP.<> prettyArgLst as
  pretty (Var v) = PP.pretty v
  pretty (MVar mv@(MetaVar v _)) = PP.text "X" PP.<> PP.int (uniqueToInt v) PP.<> ppContent (unsafePeakVar mv) where
    ppContent (Left _) = PP.empty 
    ppContent (Right t) = PP.text "@" PP.<> PP.braces (PP.pretty t)

instance PP.Pretty Constraint where
  pretty (ix1 :>=: ix2) = PP.hang 2 $ PP.pretty ix1 PP.<+> PP.text ">=" PP.</> PP.pretty ix2

-- substitutions

type Subst = VarId -> Term -- Invariant: image is free of BVar's 

idSubst :: Subst
idSubst = fvar

substFromList :: [(VarId, Term)] -> Subst
substFromList []           v = fvar v
substFromList ((v,ix):ls)  v' 
  | v == v' = ix
  | otherwise = substFromList ls v'

after :: Subst -> Subst -> Subst
s1 `after` s2 = \ v -> s1 `o` s2 v

class Substitutable c where
  type Image c
  subst_ :: (Var -> Image c) -> c -> c

o :: (Substitutable c, Image c ~ Term) => Subst -> c -> c
o s = subst_ s' where 
  s' (BVar v) = bvar v
  s' (FVar v) = s v
    
inst :: (Substitutable c, Image c ~ Term) => Subst -> c -> c
inst s = subst_ s' where 
  s' (BVar v) = s v 
  s' (FVar v) = fvar v
  
instance Substitutable Term where
  type Image Term = Term
  subst_ _ Zero = Zero
  subst_ s (Succ ix) = Succ (subst_ s ix)
  subst_ s (Sum ixs) = Sum (map (subst_ s) ixs)
  subst_ s (Fun f ixs) = Fun f (map (subst_ s) ixs)
  subst_ s (Var v) = s v
  subst_ s t@MVar{} = t

instance Substitutable t => Substitutable [t] where
  type Image [t] = Image t
  subst_ s = map (subst_ s)

