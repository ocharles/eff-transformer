{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Effect.Nondeterminism where

import Control.Monad (join)
import Control.Monad.Trans.Class (lift)
import Control.Effect
import List.Transformer (fold, foldM, select)

-- TODO Can probably generalize over any foldable.

class Monad m => Nondeterministic m where
  liftNondeterminism :: [a] -> m a

instance Monad m => Nondeterministic (Eff [] m) where
  liftNondeterminism = interpret
  {-# INLINE liftNondeterminism #-}

instance {-# OVERLAPPABLE #-} (Nondeterministic m) => Nondeterministic (Eff f m) where
  liftNondeterminism = lift . liftNondeterminism
  {-# INLINE liftNondeterminism #-}

choose :: Nondeterministic m => [a] -> m a
choose = liftNondeterminism
{-# INLINE choose #-}

runNondeterminism :: Monad m => (b -> a -> b) -> b -> Eff [] m a -> m b
runNondeterminism f z = fold f z id . translate (lift . select)
{-# INLINE runNondeterminism #-}

runNondeterminismM :: Monad m => (b -> a -> m b) -> m b -> Eff [] m a -> m b
runNondeterminismM f z = foldM f z return . translate (lift . select)
{-# INLINE runNondeterminismM #-}

-- TODO Non-conflicting names?

mzero :: Nondeterministic m => m a
mzero = choose mempty

mplus :: Nondeterministic m => m a -> m a -> m a
mplus l r = join (choose [l,r])
