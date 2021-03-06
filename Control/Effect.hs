{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

#if __GLASGOW_HASKELL__ >=800
{-# LANGUAGE UndecidableSuperClasses #-}
#endif

module Control.Effect
       ( -- * Core API
         Eff(..), translate, Interprets, interpret, IsEff) where

import Control.Monad
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Morph
import Control.Monad.Trans.Class(MonadTrans(lift))
import Control.Monad.Trans.Cont (ContT(..))
import Data.Functor.Sum
import GHC.Exts (Constraint)

-- | The 'Eff' monad transformer is used to write programs that require access to
-- specific effects. In this library, effects are combined by stacking multiple
-- 'Eff's together, just as you would do with traditional monad transformers.
-- 'Eff's are parameterized by an effect /algebra/. This is a
-- description of programs in a single effect, such as non-determinism (@[]@)or
-- exceptions (@Either e@). As 'Eff' is a monad transformer, @m@ is the monad
-- that 'Eff' transforms, which can itself be another instance of 'Eff'.
newtype Eff f m a =
  Eff (forall g r. (forall x. Sum f m x -> Cont (g r) x) -> Cont (g r) a)

-- | The 'IsEff' type family is used to make sure that a given monad stack
-- is based around 'Eff'. This is important, as it allows us to reason about
-- Eff-based type classes, knowing that /only/ 'Eff' implements them, thus
-- giving us the orthogonal-handling properties that we desire.
type family IsEff (m :: * -> *) :: Constraint where
  IsEff (Eff f m) = ()

-- NOTE The second argument to Eff is statically determined in translate,
-- but moving this into the 'MonadTrans' definition seems to half the
-- performance in benchmarks.

-- | In order to run 'Eff' computations, we need to provide a way to run its
-- effects in a specific monad transformer. Notice that 'run' eliminates one
-- layer of 'Eff', returning you with the original @a@ now captured under the
-- result of the effects described by the @effect@ functor.
translate :: (Monad m,Monad (t m),MonadTrans t)
          => (forall x r. f x -> ContT r (t m) x)
          -> Eff f m a
          -> t m a
translate step (Eff go) =
  runCont (go (\sum ->
                 case sum of
                   InL a -> cont (runContT (step a))
                   InR a -> cont (\k -> join (lift (fmap k a)))))
          return
{-# INLINE translate #-}

-- | 'LiftProgram' defines an @mtl@-style type class for automatically lifting
-- effects into 'Eff' stacks. When exporting libraries that you intend to
-- publish on Hackage, it's suggested that you still provide your own type class
-- (such as 'MonadThrow' or 'MonadHTTP') to avoid locking people into this
-- library, but 'interpret' can be useful to define your own instances of
-- that type class for 'Eff'.
class (IsEff m, Monad m) => Interprets p m | m -> p where
  interpret :: p a -> m a

instance Monad m => Interprets f (Eff f m) where
  interpret p = Eff (\i -> i (InL p))
  {-# INLINE interpret #-}

instance (Monad m, Interprets f (Eff h m)) => Interprets f (Eff g (Eff h m)) where
  interpret = lift . interpret
  {-# INLINE interpret #-}

instance Functor (Eff f m) where
  fmap f (Eff g) = Eff (\a -> fmap f (g a))
  {-# INLINE fmap #-}

instance Applicative (Eff f m) where
  pure a = Eff (\_ -> pure a)
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff f m) where
  return = pure
  {-# INLINE return #-}
  Eff a >>= f = Eff (\u -> a u >>= \b -> case f b of Eff g -> g u)
  {-# INLINE (>>=) #-}

instance MonadTrans (Eff f) where
  lift m = Eff (\l -> l (InR m))
  {-# INLINE lift #-}

instance MonadIO m => MonadIO (Eff effect m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

{-

Welcome to @effect-interpreters@, a composable approach to managing effects in
Haskell. @effect-interpreters@ is a small abstraction over the ideas of monad
transformers, the @mtl@, and algebraic effects made popular through free monads
and various implementations of extensible effects. Rather than defining the
whole program within a free monad and duplicating code on how to interpret
well defined effects, this library leverages the tools of the monad transformer
library to deliver something that is familiar, compatible with other libraries
and as fast as vanilla monad transformers.

With the marketting pitch out of the way, you may be asking yourself: why does
this library exist? Firstly, if you use restrict yourself to only using monad
transformers you incur a lot of boilerplate code by having to specify all the
necessary @lift@s to move between layers. On top of this, the resulting code
is extremely difficult to compose with different effects - if you're lucky
the transformer will be an instance of @MFunctor@ and can be mapped between
different effects, but again - this is boilerplate that we'd ideally like to
avoid. The monad transformer library (@mtl@) solves some of these problems by
moving operations into a type class, but introduces a more subtle problem along
the way. Consider the following:

@
lookupPerson :: PersonName -> 
@

. @effect-interpreters@ provides you with a toolkit to
write programs that are polymorphic over the choice of monad, stipulating that
whatever monad is chosen has access to certain underlying effects.
@effect-interpreters@ comes with the 'Eff' monad to eliminate individual effects
one-by-one, and allows you to easily define your own effects and multiple
interpretations. In this short guide, I'll demonstrate how to get started with
this library.

Within @effect-interpreters@, effects consist of:

1. A language to write programs using operations within the given effect
2. Interpretations of these effects using only the effects of a "smaller" monad.

To start, let's walk through the construction of an effect for failure. You're
probably already familiar with the language to write failing programs - it's the
'Maybe' monad! Within the 'Maybe' monad, we have the ability to fail earlier
by using 'Nothing', or we can produce successful values with 'Just' or 'return'.
Importantly, we can combine multiple 'Maybe' programs together by using its
'Monad' instance.

Now that we have our language, we need to write interpretations of 'Maybe'. One
such interpretation in any bigger monad is to run the program down to @Maybe a@.
That is, we seek a combinator with a type similar to:

@
attempt :: PotentiallyFailing a -> m (Maybe a)
@

Here @attempt@ will attempt to run a program and handle the case when it
attempts to fail. We can build this combinator using @effect-interpreters@ with
'handle':

@
attempt :: Eff Maybe m a -> m (Maybe a)
attempt =
  handle Intepretation { run = \continue p -> case p of
                                                Just a -> continue a
                                                Nothing -> return Nothing
                       , finalize = Just}
@

Let's take this line by line. On the first line with the type. It's similar to
the type I suggested earlier, but to speak specifically about
@PotentiallyFailing@ programs means to be working in an 'Eff' monad transformer
that has the ability to interpret to 'Maybe' programs.

Next, we build our 'Interpretation' and eliminate the 'Maybe' effect by calling
'handle' with this interpretation. An 'Intepreration' consists of a way to run
effectful computations, and a way to lift pure values into the final return
type.

To understand 'run', let's specialize the type of it given what we know. We know
that the 'Intepreration' we are building has type
'Interpretation Maybe Maybe m'. This means that 'run' has the type:

@
run :: forall a b. (a -> m (Maybe b)) -> Maybe a -> m (Maybe b)
@

The first argument to 'run' is a /continuation/. Whenever we try and lift a
an effect into 'Eff', we are given the rest of the program - it's then up to the
'Interpretation' if it will actually continue. In the case of failing programs,
it depends. If we're lifting a successful program - that is, @Just a@ - then we
can continue, but if we're lifting a failure then we certainly can't continue.
If you now return to our definition of run, you'll see that we pattern match
on the effectful program that we have to run, continuing or failing as
appropriate.

The other part of an 'Interpretation' is a description of what happens if we
never use the effect that we have access to. That is, what if we are told to
run an 'Eff Maybe' program that never actually uses the ability to fail? In this
case, we have to provide a way to lift pure values into the same context as
'run' - so we simply treat it as success.

-}

-- Redefinition of Control.Monad.Trans.Cont because, surprise surprise, it has
-- no inline pragmas.

cont :: ((a -> r) -> r) -> Cont r a
cont = Cont
{-# INLINE cont #-}

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  fmap f m = Cont $ \c -> runCont m (c . f)
  {-# INLINE fmap #-}

instance Applicative (Cont r) where
  pure x = Cont ($ x)
  {-# INLINE pure #-}
  f <*> v = Cont $ \c -> runCont f $ \g -> runCont v (c . g)
  {-# INLINE (<*>) #-}

instance Monad (Cont r) where
  return x = Cont ($ x)
  {-# INLINE return #-}
  m >>= k = Cont $ \c -> runCont m (\x -> runCont (k x) c)
  {-# INLINE (>>=) #-}
