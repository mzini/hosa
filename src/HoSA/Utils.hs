{-# LANGUAGE UndecidableInstances #-}
module HoSA.Utils (
  -- * Uniques
  Unique
  , uniqueToInt
  , uniqueFromInt
  , MonadUnique (..)
  , UniqueM    
  , UniqueT
  , uniques
  , runUnique
  , runUniqueT
  , runUniqueWithout
  , runUniqueWithoutT
  -- * Monad Utils
  , scoped
  , concatMapM
  , composeM
  , assertJust
  , assertRight
  -- * Pretty Printing Utils
  , (//)
  , ($$)
  , ppSeq
  , putDocLn
  , hPutDocLn
  , renderPretty
  -- * Lists
  , groupWith
) where

import System.IO (hPutStrLn, Handle)
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.RWS
import           Control.Monad.Trace
import Control.Monad.Identity (Identity, runIdentity)
import           Data.Function (on)
import           Data.List (groupBy,sortBy)


import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- lists

groupWith :: (Eq b, Ord b) => (a -> b) -> [a] -> [[a]]
groupWith f = groupBy (\eq1 eq2 -> f eq1 == f eq2) . sortBy (compare `on` f)

-- monad utils

scoped :: MonadState s m => m a -> m a
scoped m = do { s <- get; a <- m; put s; return a }
    
concatMapM :: (Monad m, Monoid b) => (a -> m b) -> [a] -> m b
concatMapM f xs = mconcat `liftM` (f `mapM` xs)

composeM :: Monad m => [a -> m a] -> a -> m a
composeM = foldr (>=>) return

assertJust :: MonadError e m => e -> Maybe a -> m a
assertJust err = maybe (throwError err) return

assertRight :: MonadError e m => (l -> e) -> (Either l r) -> m r
assertRight err = either (throwError . err) return

-- pretty printing

($$) :: PP.Doc -> PP.Doc -> PP.Doc
pa $$ pb = PP.align (pa PP.<$> PP.indent 1 pb)

(//) :: PP.Doc -> PP.Doc -> PP.Doc
pa // pb = PP.align (pa PP.</> pb)

ppSeq :: PP.Doc -> [PP.Doc] -> PP.Doc
ppSeq _ [] = PP.empty
ppSeq _ [a] = a
ppSeq s (a:as) = PP.align (a PP.<//> PP.cat [s PP.<> a' | a' <- as])

putDocLn :: PP.Pretty e => e -> IO ()
putDocLn = putStrLn . renderPretty

hPutDocLn :: PP.Pretty e => Handle -> e -> IO ()
hPutDocLn h = hPutStrLn h . renderPretty

renderPretty :: PP.Pretty e => e -> String
renderPretty d = PP.displayS (PP.renderSmart 1.0 120 (PP.pretty d)) ""

----------------------------------------------------------------------
-- uniques
----------------------------------------------------------------------

newtype Unique = Unique Int deriving (Eq, Ord, Show, Enum)

uniqueToInt :: Unique -> Int
uniqueToInt (Unique i) = i

uniqueFromInt :: Int -> Unique
uniqueFromInt = Unique

newtype UniqueT m a = UniqueT { runUniqueT_ :: StateT Unique m a }
                      deriving (Applicative, Functor, Monad, MonadIO)
                               
type UniqueM = UniqueT Identity                               

demand :: Monad m => UniqueT m Unique
demand = getU <* modifyU (\ (Unique i) -> Unique (i+1)) where
  getU = UniqueT get
  modifyU = UniqueT . modify

resetUnique :: Monad m => UniqueT m ()
resetUnique = UniqueT (put (Unique 1))

runUniqueWithoutT :: Monad m => [Unique] -> UniqueT m a -> m a
runUniqueWithoutT vs = flip evalStateT (Unique (i+1)) . runUniqueT_ where
  Unique i = maximum (Unique 0 : vs)

runUniqueT :: Monad m => UniqueT m a -> m a
runUniqueT = runUniqueWithoutT []

runUniqueWithout :: [Unique] -> UniqueM a -> a
runUniqueWithout vs = runIdentity . runUniqueWithoutT vs
  
runUnique :: UniqueM a -> a
runUnique = runIdentity . runUniqueT

instance MonadTrans UniqueT where lift = UniqueT . lift
deriving instance MonadError e m => MonadError e (UniqueT m)

-- MonadUnique


class Monad m => MonadUnique m where
  unique :: m Unique
  reset :: m ()

instance Monad m => MonadUnique (UniqueT m) where
  unique = demand
  reset = resetUnique

uniques :: MonadUnique m => Int -> m [Unique]
uniques n = replicateM n unique

instance MonadUnique m => MonadUnique (ExceptT e m) where
  unique = lift unique
  reset = lift reset
  
instance MonadUnique m => MonadUnique (TraceT t m) where
  unique = lift unique
  reset = lift reset

instance MonadUnique m => MonadUnique (StateT t m) where
  unique = lift unique
  reset = lift reset

instance MonadUnique m => MonadUnique (ReaderT t m) where
  unique = lift unique
  reset = lift reset

instance (Monoid w, MonadUnique m) => MonadUnique (RWST r w s m) where
  unique = lift unique
  reset = lift reset
  
instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
  unique = lift unique
  reset = lift reset

  
