{-# LANGUAGE UndecidableInstances #-}
module HoSA.Utils (
  -- * Uniques
  Unique
  , uniqueToInt
  , UniqueM    
  , UniqueT
  , unique
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
  -- * Logging
  , LogT
  , LogM
  , logBlock
  , logMessage
  , runLogT
  , runLog
) where

import           Control.Monad.Supply
import           Control.Monad.State
import           Control.Monad.Writer
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.Except (throwError, MonadError)
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

renderPretty :: PP.Pretty e => e -> String
renderPretty d = PP.displayS (PP.renderSmart 1.0 80 (PP.pretty d)) ""

-- logging

newtype LogT m a = LogT { runLogM_ :: StateT Int m a }
                   deriving (Applicative, Functor, Monad, MonadState Int)

deriving instance (MonadWriter w m) => (MonadWriter w (LogT m))
deriving instance (MonadError e m) => (MonadError e (LogT m))
deriving instance (MonadIO m) => (MonadIO (LogT m))

type LogM = LogT Identity

instance MonadTrans LogT where
  lift = LogT . lift

runLogT :: Monad m => LogT m a -> m a
runLogT = flip evalStateT 0 . runLogM_

runLog :: LogM a -> a
runLog = runIdentity . runLogT


logMessage :: (MonadIO m, PP.Pretty e) => e -> LogT m ()
logMessage e = do
  i <- get
  liftIO (putDocLn (PP.indent i (PP.pretty e)))

logBlock :: (MonadIO m, PP.Pretty e) => e -> LogT m a -> LogT m a
logBlock e m = scoped $ logMessage e >> modify succ >> m

-- uniques

newtype Unique = Unique Int deriving (Eq, Ord)

newtype UniqueT m a = UniqueT { runUniqueT_ :: SupplyT Unique m a }
                      deriving (Applicative, Functor, Monad, MonadIO)

instance MonadTrans UniqueT where
  lift = UniqueT . lift

type UniqueM = UniqueT Identity

uniqueToInt :: Unique -> Int
uniqueToInt (Unique i) = i

unique :: Monad m => UniqueT m Unique
unique = UniqueT demand

uniques :: Monad m => Int -> UniqueT m [Unique]
uniques n = replicateM n unique

runUniqueT :: Monad m => UniqueT m a -> m a
runUniqueT m = runSupplyT (runUniqueT_ m) inc (Unique 0) where
  inc (Unique i) = Unique (i + 1)

runUnique :: UniqueM a -> a
runUnique = runIdentity . runUniqueT
