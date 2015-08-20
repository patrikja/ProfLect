{-# LANGUAGE GADTs #-}
data Mu f where
  Inn :: f (Mu f) -> Mu f

inn = Inn

out :: Mu f -> f (Mu f)
out (Inn x) = x

cataT :: Functor f => (f a -> a) -> (Mu f -> a)
cataT alg = alg . fmap (cataT alg) . out

data ITree subtree where
  Leaf  :: Int -> ITree subtree
  Bin   :: subtree -> subtree -> ITree subtree

type Tree = Mu ITree
leaf :: Int -> Tree
leaf = inn . Leaf
bin :: Tree -> Tree -> Tree
bin l r = inn (Bin l r)

instance Functor ITree where
  fmap = fmapITree

fmapITree :: (a->b) -> ITree a -> ITree b
fmapITree f (Leaf i) = Leaf i
fmapITree f (Bin l r) = Bin (f l) (f r)

fsum :: ITree Int -> Int
fsum (Leaf i) = i
fsum (Bin l r) = l + r

psum = cataT fsum

anaT :: Functor f => (a -> f a) -> (a -> Mu f)
anaT coalg = inn . fmap (anaT coalg) . coalg

flevels :: Int -> ITree Int
flevels l | l <= 0     = Leaf 1
          | otherwise  = Bin (l-1) (l-1)

plevels :: Int -> Mu ITree
plevels = anaT flevels

exampleTree = plevels 10

main = print $ psum exampleTree
