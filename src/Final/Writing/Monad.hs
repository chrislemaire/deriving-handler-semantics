module Final.Writing.Monad where

import GHC.Base (ap)

data Tree a = Leaf {
                    value :: a
            }
            | Node {
                    nleft :: Tree a,
                    nright :: Tree a
            }

instance Functor Tree where
-- fmap :: (a -> b) -> Tree a -> Tree b
  fmap f (Leaf v)     = Leaf (f v)
  fmap f (Node nl nr) = Node (fmap f nl) (fmap f nr)

instance Applicative Tree where
  pure  = Leaf
  (<*>) = ap

instance Monad Tree where
  return = pure

-- (>>=) :: Tree a -> (a -> Tree b) -> Tree b
  (>>=) (Leaf v)     f = f v
  (>>=) (Node nl nr) f = Node ((>>=) nl f) ((>>=) nr f)



data St s a = St { runSt :: s -> (s, a) }

instance Functor (St s) where
  fmap f = (>>= (return . f))

instance Applicative (St s) where
  pure a = St (\s -> (s, a))
  (<*>) = ap

instance Monad (St s) where
  return = pure

  -- (>>=) :: St s a -> (a -> St s b) -> St s b
  (>>=) (St stf) f = St (\s -> let (s', a) = stf s
                                in runSt (f a) s')

put :: s -> St s ()
put s = St (\_ -> (s, ()))

get :: St s s
get = St (\s -> (s, s))

-- for (int i = 0; ..; i++)

--incr :: St Int Int
--incr = get >>= (\i ->
--       put (i + 1) >>
--       return i
--   )

lc :: [Int]
lc = [x + y | x <- [1, 2, 3], y <- [1, 2, 3]]

lc' :: [Int]
lc' = [1, 2, 3] >>= (\x ->
      [1, 2, 3] >>= (\y ->
      return (x + y)))

incr :: St Int Int
incr = do
  i <- get
  put (i + 1)
  return i


program = put 0 >> incr >> incr >> incr
