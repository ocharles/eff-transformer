{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Environment
       (EffEnvironment, runInEnvironment, ask, asks, mapEnvironment, liftReader,
        effToReaderT, readerTToEff)
       where

import Control.Effect
import Control.Monad.Morph (lift, hoist, generalize)
import Control.Monad.Trans.Reader (Reader, ReaderT(..))
import qualified Control.Monad.Trans.Reader as Reader

class (Monad m) => EffEnvironment env m | m -> env where
  liftReader :: Reader env a -> m a

instance Monad m => EffEnvironment env (Eff (Reader env) m) where
  liftReader = interpret
  {-# INLINE liftReader #-}

instance {-# OVERLAPPABLE #-} (EffEnvironment env m) => EffEnvironment env (Eff effects m) where
  liftReader = lift . liftReader
  {-# INLINE liftReader #-}

ask :: (EffEnvironment env m) => m env
ask = liftReader Reader.ask
{-# INLINE ask #-}

asks :: (EffEnvironment a m) => (a -> b) -> m b
asks f = fmap f ask
{-# INLINE asks #-}

runInEnvironment
  :: Monad m
  => Eff (Reader env) m a -> env -> m a
runInEnvironment = runReaderT . effToReaderT
{-# INLINE runInEnvironment #-}

mapEnvironment
  :: (EffEnvironment env m)
  => (env -> env') -> Eff (Reader env') m a -> m a
mapEnvironment f m = ask >>= runInEnvironment m . f
{-# INLINE mapEnvironment #-}

effToReaderT :: Monad m => Eff (Reader e) m a -> ReaderT e m a
effToReaderT = translate (hoist generalize)
{-# INLINE effToReaderT #-}

readerTToEff :: (Monad m, EffEnvironment e m) => ReaderT e m a -> m a
readerTToEff m = ask >>= runReaderT m
{-# INLINE readerTToEff #-}
