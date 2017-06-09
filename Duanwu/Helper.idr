module Duanwu.Helper

import Control.Monad.Trans

%access export

public export
record EitherT (e : Type) (m : Type -> Type) (a : Type) where
  constructor ET
  runEitherT : m (Either e a)

Monad m => Functor (EitherT e m) where
  map f = ET . liftA (map f) . runEitherT

Monad m => Applicative (EitherT e m) where
  pure = ET . pure . Right
  mf <*> ma = ET $ do f <- runEitherT mf
                      a <- runEitherT ma
                      pure $ f <*> a

Monad m => Monad (EitherT e m) where
  x >>= f = ET $ do Right a <- runEitherT x
                      | Left b => pure (Left b)
                    runEitherT (f a)

MonadTrans (EitherT e) where
  lift = ET . liftA Right 

left : Monad m => e -> EitherT e m a
left = ET . pure . Left

right : Monad m => a -> EitherT e m a
right = ET . pure . Right

eitherT : Monad m => (e -> m c) -> (a -> m c) -> EitherT e m a -> m c
eitherT f g (ET mx) = do Right x <- mx | Left y => f y
                         g x

liftEither : Monad m => Either e a -> EitherT e m a
liftEither (Left err) = left err
liftEither (Right val) = right val
