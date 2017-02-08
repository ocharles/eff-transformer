{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Effect.Nondeterminism where

import Control.Monad (join)
import Control.Monad.Trans.Class (lift)
import Control.Effect
import Data.Foldable (Foldable, toList)
import List.Transformer (fold, foldM, select)

class Monad m => Nondeterministic m where
  liftNondeterminism :: [a] -> m a

instance Monad m => Nondeterministic (Eff [] m) where
  liftNondeterminism = interpret
  {-# INLINE liftNondeterminism #-}

instance {-# OVERLAPPABLE #-} (Nondeterministic m) => Nondeterministic (Eff f m) where
  liftNondeterminism = lift . liftNondeterminism
  {-# INLINE liftNondeterminism #-}

choose :: (Nondeterministic m, Foldable f) => f a -> m a
choose = liftNondeterminism . toList
{-# INLINE choose #-}

runNondeterminism :: (Monad m, Foldable f) => (b -> a -> b) -> b -> Eff f m a -> m b
runNondeterminism f z = fold f z id . translate (lift . select)
{-# INLINE runNondeterminism #-}

runNondeterminismM :: (Monad m, Foldable f) => (b -> a -> m b) -> m b -> Eff f m a -> m b
runNondeterminismM f z = foldM f z return . translate (lift . select)
{-# INLINE runNondeterminismM #-}

-- TODO Non-conflicting names?

mzero :: Nondeterministic m => m a
mzero = choose []

mplus :: Nondeterministic m => m a -> m a -> m a
mplus l r = join (choose [l,r])
