{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}

module Course.State where

import Course.Core
import qualified Prelude as P
import Course.Optional
import Course.List
import Course.Functor
import Course.Applicative
import Course.Monad
import qualified Data.Set as S
import qualified Course.Core as S
import System.Directory.Internal.Prelude (fromIntegral)

-- $setup
-- >>> import Test.QuickCheck.Function
-- >>> import Data.List(nub)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> import Course.Core
-- >>> import Course.List
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- A `State` is a function from a state value `s` to (a produced value `a`, and a resulting state `s`).
newtype State s a =
  State (
    s
    -> (a, s)
  )

runState ::
  State s a
  -> s
  -> (a, s)
runState (State f) =
  f

-- | Run the `State` seeded with `s` and retrieve the resulting state.
--
-- prop> \(Fun _ f) s -> exec (State f) s == snd (runState (State f) s)
exec ::
  State s a
  -> s
  -> s
exec sa s = snd $ runState sa s

-- | Run the `State` seeded with `s` and retrieve the resulting value.
--
-- prop> \(Fun _ f) s -> eval (State f) s == fst (runState (State f) s)
eval ::
  State s a
  -> s
  -> a
eval sa s = fst $ runState sa s

-- | A `State` where the state also distributes into the produced value.
--
-- >>> runState get 0
-- (0,0)
get ::
  State s s
get = State $ \s -> (s, s)

-- | A `State` where the resulting state is seeded with the given value.
--
-- >>> runState (put 1) 0
-- ((),1)
put ::
  s
  -> State s ()
put = State . const . ((),)

-- | Implement the `Functor` instance for `State s`.
--
-- >>> runState ((+1) <$> State (\s -> (9, s * 2))) 3
-- (10,6)
instance Functor (State s) where
  (<$>) ::
    (a -> b)
    -> State s a
    -> State s b
  (<$>) f sa = State $ \s -> let (a, newState) = runState sa s
                                in (f a, newState)

-- | Implement the `Applicative` instance for `State s`.
--
-- >>> runState (pure 2) 0
-- (2,0)
--
-- >>> runState (pure (+1) <*> pure 0) 0
-- (1,0)
--
-- >>> runState (State (\s -> ((+3), s ++ ("apple":.Nil))) <*> State (\s -> (7, s ++ ("banana":.Nil)))) Nil
-- (10,["apple","banana"])
instance Applicative (State s) where
  pure ::
    a
    -> State s a
  pure a = State (a,)

  (<*>) ::
    State s (a -> b)
    -> State s a
    -> State s b
  (<*>) (State sab) (State sa) = State $ \s -> let (f, newState) = sab s
                                                   (a, newerState) = sa newState
                                                in (f a, newerState)

-- | Implement the `Monad` instance for `State s`.
--
-- >>> runState ((const $ put 2) =<< put 1) 0
-- ((),2)
--
-- >>> let modify f = State (\s -> ((), f s)) in runState (modify (+1) >>= \() -> modify (*2)) 7
-- ((),16)
--
-- >>> runState ((\a -> State (\s -> (a + s, 10 + s))) =<< State (\s -> (s * 2, 4 + s))) 2
-- (10,16)
instance Monad (State s) where
  (=<<) ::
    (a -> State s b)
    -> State s a
    -> State s b 
  (=<<) f (State sa) = State $ \s -> let (a, newState) = sa s
                                         State sb = f a
                                      in sb newState

-- | Find the first element in a `List` that satisfies a given predicate.
-- It is possible that no element is found, hence an `Optional` result.
-- However, while performing the search, we sequence some `Monad` effect through.
--
-- Note the similarity of the type signature to List#find
-- where the effect appears in every return position:
--   find ::  (a ->   Bool) -> List a ->    Optional a
--   findM :: (a -> f Bool) -> List a -> f (Optional a)
--
-- >>> let p x = (\s -> (const $ pure (x == 'c')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Full 'c',3)
--
-- >>> let p x = (\s -> (const $ pure (x == 'i')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Empty,8)
findM ::
  Monad f =>
  (a -> f Bool)
  -> List a
  -> f (Optional a)
-- findM _ Nil = pure Empty
-- findM f (x :. xs) = f x >>= (\b -> if b then pure $ Full x else findM f xs)
findM f = foldRight (\x y -> f x >>= (\b -> if b then pure (Full x) else y )) (pure Empty)

-- | Find the first element in a `List` that repeats.
-- It is possible that no element repeats, hence an `Optional` result.
--
-- /Tip:/ Use `findM` and `State` with a @Data.Set#Set@.
--
-- >>> firstRepeat $ 1 :. 2 :. 0 :. 9 :. 2 :. 1 :. Nil
-- Full 2
--
-- prop> \xs -> case firstRepeat xs of Empty -> let xs' = hlist xs in nub xs' == xs'; Full x -> length (filter (== x) xs) > 1
-- prop> \xs -> case firstRepeat xs of Empty -> True; Full x -> let (l, (rx :. rs)) = span (/= x) xs in let (l2, r2) = span (/= x) rs in let l3 = hlist (l ++ (rx :. Nil) ++ l2) in nub l3 == l3
firstRepeat ::
  Ord a =>
  List a
  -> Optional a
firstRepeat la = let fr a = do
                              ds <- get
                              let b = S.member a ds
                              put $ S.insert a ds
                              pure b
                        in eval (findM fr la) S.empty

-- | Remove all duplicate elements in a `List`.
-- /Tip:/ Use `filtering` and `State` with a @Data.Set#Set@.
--
-- prop> \xs -> firstRepeat (distinct xs) == Empty
--
-- prop> \xs -> distinct xs == distinct (flatMap (\x -> x :. x :. Nil) xs)
distinct ::
  Ord a =>
  List a
  -> List a
-- distinct la = eval (filtering (\a -> (\ds -> lift2 (,) (S.notMember a ds) (S.insert a ds)) <$> get) la) S.empty
distinct la = eval (filtering (State . lift2 (lift2 (,)) S.notMember S.insert) la) S.empty

t :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t = lift2 (lift2 (,)) S.member S.insert
t2 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t2 = lift2 (,) <$> S.member <*> S.insert
t3 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t3 = lift2 (,) . S.member <*> S.insert
t4 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t4 = (\a -> ((,) <$> S.member a <*>)) <*> S.insert
t5 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t5 aa = (\a -> ((,) <$> S.member a <*>)) aa $ S.insert aa
t6 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t6 aa = (\a sec -> (,) . S.member a <*> sec) aa $ S.insert aa
t7 :: Ord a => a -> S.Set a -> (Bool, S.Set a)
t7 aa = (\a sec ds -> (S.member a ds,) $ sec ds) aa $ S.insert aa
t8 :: Ord a => a -> State (S.Set a) Bool
t8 aa = State $ (\a sec ds -> (S.member a ds, sec ds)) aa $ S.insert aa
t9 :: Ord a => a -> State (S.Set a) Bool
t9 aa = State $ (\sec ds -> (S.member aa ds, sec ds)) $ S.insert aa
t10 :: Ord a => a -> State (S.Set a) Bool
t10 = \a -> State $ \ds -> (S.member a ds, S.insert a ds)
-- t10 = \aa -> State $ (\sec ds -> (S.member aa ds, sec ds)) $ S.insert aa
-- distinct =
  -- listWithState filtering S.notMember 
-- listWithState :: 
--   Ord a1 =>
--   ((a1 -> State (S.Set a1) a2) 
--   -> t 
--   -> State (S.Set a3) a)
--   -> (a1 -> S.Set a1 -> a2) 
--   -> t 
--   -> a 
-- listWithState f m x =
--   eval (f (State . lift2 (lift2 (,)) m S.insert) x) S.empty


-- | A happy number is a positive integer, where the sum of the square of its digits eventually reaches 1 after repetition.
-- In contrast, a sad number (not a happy number) is where the sum of the square of its digits never reaches 1
-- because it results in a recurring sequence.
--
-- /Tip:/ Use `firstRepeat` with `produce`.
--
-- /Tip:/ Use `join` to write a @square@ function.
--
-- /Tip:/ Use library functions: @Optional#contains@, @Data.Char#digitToInt@.
--
-- >>> isHappy 4
-- False
--
-- >>> isHappy 7
-- True
--
-- >>> isHappy 42
-- False
--
-- >>> isHappy 44
-- True
isHappy ::
  Integer
  -> Bool
isHappy = contains 1 . firstRepeat . produce (fromIntegral . sum . map (join (*) . digitToInt) . show')
