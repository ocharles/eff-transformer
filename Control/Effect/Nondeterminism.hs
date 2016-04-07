{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Effect.Nondeterminism where

import Control.Effect
import Control.Monad (join)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (runContT, shiftT)
import qualified Pipes as P
import qualified Pipes.Prelude as P

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

runNondeterminism :: Monad m => Eff [] m a -> m [a]
runNondeterminism eff = P.toListM (P.enumerate (translate makeChoice eff))
  where makeChoice choices = flip runContT return $
          shiftT (\k ->
                    lift (P.Select (P.for (P.each choices)
                                          (P.enumerate . k))))
{-# INLINE runNondeterminism #-}

-- TODO Non-conflicting names?

mzero :: Nondeterministic m => m a
mzero = choose mempty

mplus :: Nondeterministic m => m a -> m a -> m a
mplus l r = join (choose [l,r])
