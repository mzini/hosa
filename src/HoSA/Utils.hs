{-# LANGUAGE UndecidableInstances #-}
module HoSA.Utils (
  -- * Uniques
  Unique
  , uniqueToInt
  , MonadUnique (..)
  , UniqueM    
  , UniqueT
  , uniques
  , runUnique
  , runUniqueT
  -- * Monad Utils
  , scoped
  , concatMapM
  , assertJust
  , assertRight
  -- * Pretty Printing Utils
  , (//)
  , ($$)
  , ppSeq
  , putDocLn
  , renderPretty
) where

import System.IO (hPutStrLn, Handle, stderr)
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Except
import           Control.Monad.Trace
import Control.Monad.Identity (Identity, runIdentity)

import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- monad utils

scoped :: MonadState s m => m a -> m a
scoped m = do { s <- get; a <- m; put s; return a }
    
concatMapM :: (Monad m) => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat `liftM` (f `mapM` xs)

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
renderPretty d = PP.displayS (PP.renderSmart 1.0 200 (PP.pretty d)) ""

----------------------------------------------------------------------
-- uniques
----------------------------------------------------------------------

newtype Unique = Unique Int deriving (Eq, Ord, Show)

uniqueToInt :: Unique -> Int
uniqueToInt (Unique i) = i

newtype UniqueT m a = UniqueT { runUniqueT_ :: StateT Unique m a }
                      deriving (Applicative, Functor, Monad, MonadIO)
                               
type UniqueM = UniqueT Identity                               

demand :: Monad m => UniqueT m Unique
demand = getU <* modifyU (\ (Unique i) -> Unique (i+1)) where
  getU = UniqueT get
  modifyU = UniqueT . modify
  

runUniqueT :: Monad m => UniqueT m a -> m a
runUniqueT = flip evalStateT (Unique 1) . runUniqueT_

runUnique :: UniqueM a -> a
runUnique = runIdentity . runUniqueT

instance MonadTrans UniqueT where lift = UniqueT . lift
deriving instance MonadError e m => MonadError e (UniqueT m)

-- MonadUnique


class Monad m => MonadUnique m where
  unique :: m Unique

instance Monad m => MonadUnique (UniqueT m) where
  unique = demand

uniques :: MonadUnique m => Int -> m [Unique]
uniques n = replicateM n unique

instance MonadUnique m => MonadUnique (ExceptT e m) where unique = lift unique
instance MonadUnique m => MonadUnique (TraceT t m) where unique = lift unique
instance MonadUnique m => MonadUnique (StateT t m) where unique = lift unique
instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where unique = lift unique

  
