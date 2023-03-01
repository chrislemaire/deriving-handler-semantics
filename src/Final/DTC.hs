{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}

module Final.DTC where

import GHC.TypeLits
import Data.Kind (Type)

-- * kinded DTC
infixr 9 :+:

data sig1 :+: sig2 :: Type where
  Inl0 :: sig1 -> sig1 :+: sig2
  Inr0 :: sig2 -> sig1 :+: sig2

class sig1 :<: sig2 where
  inj0 :: sig1 -> sig2

instance sig :<: sig where
  inj0 = id

instance {-# OVERLAPPABLE #-} sig1 :<: (sig1 :+: sig2) where
  inj0 = Inl0

instance {-# OVERLAPPABLE #-} (sig1 :<: sig3) => sig1 :<: (sig2 :+: sig3) where
  inj0 = Inr0 . inj0

instance (Show sig1, Show sig2) => Show (sig1 :+: sig2) where
  show (Inl0 s1) = show s1
  show (Inr0 s2) = show s2

-- * -> * kinded DTC
infixr 9 :++:

data sig1 :++: sig2 :: Type -> Type where
  Inl :: sig1 c -> (sig1 :++: sig2) c
  Inr :: sig2 c -> (sig1 :++: sig2) c

class (sig1 :: Type -> Type) :<<: sig2 where
  inj :: sig1 c -> sig2 c

instance sig :<<: sig where
  inj = id

instance {-# OVERLAPPABLE #-} sig1 :<<: (sig1 :++: sig2) where
  inj = Inl

instance {-# OVERLAPPABLE #-} (sig1 :<<: sig3) => sig1 :<<: (sig2 :++: sig3) where
  inj = Inr . inj

-- * -> * -> * -> * kinded DTC
infixr 9 :+++:

data sig1 :+++: sig2 :: (Type -> Type) -> Type -> Type where
  Inl2 :: sig1 op c -> (sig1 :+++: sig2) op c
  Inr2 :: sig2 op c -> (sig1 :+++: sig2) op c

class (sig1 :: (Type -> Type) -> Type -> Type) :<<<: sig2 where
  inj2 :: sig1 op c -> sig2 op c

instance sig :<<<: sig where
  inj2 = id

instance {-# OVERLAPPABLE #-} sig1 :<<<: (sig1 :+++: sig2) where
  inj2 = Inl2

instance {-# OVERLAPPABLE #-} (sig1 :<<<: sig3) => sig1 :<<<: (sig2 :+++: sig3) where
  inj2 = Inr2 . inj2
