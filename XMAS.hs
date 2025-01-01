{-# language TypeFamilies #-}
module XMAS where
import Data.Maybe
import Data.List
import Control.Comonad
import Data.Distributive
import Data.Functor.Compose
import Data.Functor.Foldable

-- Infinite stream

data Stream a = (:>) { headS :: a
                     , tailS :: Stream a }
    deriving Functor

infixr 5 :>

-- Recursion scheme for streams
data FPair a x = P a x
    deriving Functor

type instance Base (Stream a) = FPair a

instance Recursive (Stream a) where
    project (a :> as) = P a as

instance Corecursive (Stream a) where
    embed (P a as) = a :> as

instance Applicative Stream where
    pure :: a -> Stream a
    pure = ana (\a -> P a a)
    (<*>) :: Stream (a -> b) -> Stream a -> Stream b
    (f :> fs) <*> (a :> as) = f a :> (fs <*> as)

-- Stream is distributive over any functor
instance Distributive Stream where
    distribute :: Functor f => f (Stream a) -> Stream (f a)
    distribute stms = (headS <$> stms) :> distribute (tailS <$> stms)

instance Show a => Show (Stream a) where
    show = show . take 4 . toInfList
-- Backward infinite stream

data BStream a = (:<) { tBStream :: BStream a
                      , hBStream :: a }
    deriving Functor

infixl 5 :<

data BPair a x = BP x a
    deriving Functor

type instance Base (BStream a) = BPair a

instance Corecursive (BStream a) where
    embed (BP as a) = as :< a

instance Applicative BStream where
    pure :: a -> BStream a
    pure = ana (\a -> BP a a)
    (<*>) :: BStream (a -> b) -> BStream a -> BStream b
    (fs :< f) <*> (as :< a) = (fs <*> as) :< f a

instance Distributive BStream where
    distribute :: Functor f => f (BStream a) -> BStream (f a)
    distribute stms = distribute (tBStream <$> stms) :< (hBStream <$> stms)

-- Forward and backward iterate
iterateS :: (a -> a) -> a -> Stream a
iterateS f = ana (\a -> P a (f a))

iterateB :: (a -> a) -> a -> BStream a
iterateB f = ana (\x -> BP (f x) x)

toInfList :: Stream a -> [a]
toInfList = cata (\(P a as) -> a : as)

stmToList :: Stream (Maybe b) -> [b]
stmToList = fmap fromJust . takeWhile isJust . toInfList

stmToMatrix :: Stream [a] -> [[a]]
stmToMatrix = takeWhile (not . null) . toInfList

-- Pointer to a location in an infinite bidirectional stream
data Cursor a = Cur { bwStm :: BStream a
                    , cur   :: a
                    , fwStm :: Stream a }
    deriving Functor

instance Applicative Cursor where
    pure :: a -> Cursor a
    pure a = Cur (pure a) a (pure a)
    (<*>) :: Cursor (a -> b) -> Cursor a -> Cursor b
    Cur fbw f ffw <*> Cur fw a bw = Cur (fbw <*> fw) (f a) (ffw <*> bw)

instance Distributive Cursor where
    distribute :: Functor f => f (Cursor a) -> Cursor (f a)
    distribute fCur = Cur (distribute (bwStm <$> fCur))
                          (cur <$> fCur)
                          (distribute (fwStm <$> fCur))

instance Comonad Cursor where
    extract (Cur _ a _) = a
    duplicate cur = Cur (iterateB moveBwd (moveBwd cur))
                         cur
                        (iterateS moveFwd (moveFwd cur))

-- move the cursor

moveFwd :: Cursor a -> Cursor a
moveFwd (Cur bw a (x :> fw)) = Cur (bw :< a) x fw

moveBwd :: Cursor a -> Cursor a
moveBwd (Cur (bw :< x) a fw) = Cur bw x (a :> fw)

curToList :: Cursor (Maybe a) -> [a]
curToList (Cur _ Nothing as) = []
curToList (Cur _ (Just a) as) = a : stmToList as

listToCur :: (a -> b) -> b -> [a] -> Cursor b
listToCur convert padding [] = Cur (pure padding) padding (pure padding)
listToCur convert padding (a : as) = Cur (pure padding) (convert a) (stmFromList as)
    where stmFromList = foldr ((:>) . convert) (pure padding)



---------------------------
-- A two-dimensional cursor, or a grid
---------------------------

type Grid a = Compose Cursor Cursor a

instance (Comonad w, Distributive w) => Comonad (Compose w w) where
    extract = extract . extract . getCompose
    duplicate = fmap Compose . Compose .
                fmap distribute . duplicate . fmap duplicate .
                getCompose

instance {-# OVERLAPPING #-} Show a => Show (Grid a) where
  show = show . getCompose

matrixToGrid :: [[a]] -> Grid (Maybe a)
matrixToGrid ass = Compose $ listToCur id (pure Nothing) $
                             listToCur Just Nothing <$> ass

gridToMatrix :: Grid (Maybe a) -> [[a]]
gridToMatrix (Compose curcur) = stmToMatrix (a :> as)
  where (Cur _ a as) = curToList <$> curcur

data Dir = B | Z | F
    deriving (Eq, Enum, Bounded, Show)

-- (x, y) direction
type Dir2 = (Dir, Dir)

allDirs :: [Dir2]
allDirs = [(F, Z), (F, F), (Z, F), (B, F), (B, Z), (B, B), (Z, B), (F, B)]

move :: Dir -> Cursor a -> Cursor a
move dir =
    case dir of
        B -> moveBwd
        Z -> id
        F -> moveFwd

-- move all rows in the same direction
moveH :: Dir -> Grid a -> Grid a
moveH dir (Compose (Cur  up cur dn)) = Compose $ Cur (mv <$> up) (mv cur) (mv <$> dn)
    where mv = move dir

move2 :: Dir2 -> Grid a -> Grid a
move2 (h, v) = moveH h .  Compose . move v . getCompose

match :: Eq a => [a] -> Grid (Maybe a) -> Maybe Int
match (a : as) grid =
    let mx = extract grid
    in case mx of
        Nothing -> Nothing -- we're out of bounds
        Just x ->  if x == a -- the beginning matches: check the suffix
                   then Just $ sum $ fmap (suffix as grid) allDirs -- in all directions
                   else Just 0 -- no local match

suffix :: Eq a => [a] -> Grid (Maybe a) -> Dir2 -> Int
suffix as grid dir =
    let grid' = move2 dir grid
        x' = extract grid'
        xs = fromJust <$> takeWhile isJust (walk dir x' grid')
    in
        if as `isPrefixOf` xs then 1 else 0

-- walk the grid and acuumulate values
-- provide the direction and the starting value
walk :: Dir2 -> a -> Grid a -> [a]
walk dir a grid =  fst <$> iterate (go dir) (a, move2 dir grid)
    where go :: Dir2 -> (a, Grid a) -> (a, Grid a)
          go dir (a, grid) = (extract grid, move2 dir grid)

solve :: Grid (Maybe Char) -> Int
solve grid =
    let matches = extend (match "XMAS") grid
        sums = gridToMatrix matches
    in sum $ sum <$> sums


main :: IO ()
main = do
    txt <- readFile "data.txt"
    let grid = matrixToGrid $ lines txt
    print $ solve grid

----------
-- Testing
----------
-- Laws
grid = matrixToGrid [[1,2],[3,4]]
instance Show a => Show (Cursor a) where
    show (Cur _ a (b :> c :> _)) = 
        show a ++ show b ++ show c ++ "\n"
-- extract . duplicate = id
law1 = gridToMatrix $ (extract . duplicate) grid

-- fmap extract . duplicate = id
law2 = gridToMatrix $  (fmap extract . duplicate) grid

-- duplicate . duplicate = fmap duplicate . duplicate
law3 = fmap gridToMatrix <$> (duplicate . duplicate) grid
law4 = fmap gridToMatrix <$> (fmap duplicate . duplicate) grid

test = solve $ matrixToGrid txt

-- answer: XMAS 18 times
txt :: [String]
txt = [
    "MMMSXXMASM",
    "MSAMXMSMSA",
    "AMXSXMAAMM",
    "MSAMASMSMX",
    "XMASAMXAMM",
    "XXAMMXXAMA",
    "SMSMSASXSS",
    "SAXAMASAAA",
    "MAMMMXMMMM",
    "MXMXAXMASX"]