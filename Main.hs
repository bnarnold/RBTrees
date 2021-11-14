{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | Enum type for vertex colors.
data Color = Red | Black deriving (Show)

-- | Peano naturals
data N = Z | S N

-- | reified Peano naturals
data NP (n :: N) where
  ZP :: NP Z
  SP :: NP n -> NP (S n)

-- | reified inequality between Peano naturals
data LEq (m :: N) (n :: N) where
  IsEq :: LEq m m
  IsLess :: LEq m n -> LEq m (S n)

-- | reified inequality between Peano naturals
data Less (m :: N) (n :: N) where
  Less :: LEq m n -> Less m (S n)

-- | reified comparison between Peano naturals
data Compare (m :: N) (n :: N) where
  Smaller :: Less m n -> Compare m n
  Equal :: Compare m m
  Bigger :: Less n m -> Compare m n

-- | Red-black node of given color and height
data Node (c :: Color) (d :: N) (a :: *) where
  Leaf :: Node Black Z a
  BNode :: Node cl d a -> a -> Node cr d a -> Node Black (S d) a
  RNode :: Node Black d a -> a -> Node Black d a -> Node Red d a

-- | Enum to distinguish children
data Dir = Lf | Rg deriving (Eq)

-- | helper class to combine left- and right-rotations
data Unpacked (c :: Color) (d :: N) (a :: *) where
  WasLeaf :: Unpacked Black Z a
  WasNode :: a -> (Dir -> (Child c d a,Child c d a)) -> Unpacked c d a

-- | reified color constraints
data ColorProxy (c :: Color) where
  BlackP :: ColorProxy Black
  RedP :: ColorProxy Red

-- | Red-Black node without root color
data UncoloredNode (d :: N) (a :: *) where
  Colored :: Node c d a -> UncoloredNode d a

-- | possible children of a node of color 'c' and depth 'd'
data Child (c :: Color) (d :: N) (a :: *) where
  BChild :: Node c d a -> Child Black (S d) a
  RChild :: Node Black d a -> Child Red d a

-- | intermediate result of deletion
data Delete (c :: Color) (d :: N) (a :: *) where
  Still :: Node c d a -> Delete c d a
  NowBlack :: Node Black d a -> Delete Red d a
  Short :: Node Black d a -> Delete Black (S d) a

-- | intermediate result of min-removal
data DeleteBd (c :: Color) (d :: N) (a :: *) where
  FromLeaf :: DeleteBd Black Z a
  Popped :: a -> Delete c d a -> DeleteBd c d a

-- | red-black node with upper bound on height
data SubNode (c :: Color) (d :: N) (a :: *) where
  StillRed :: Node Red d a -> SubNode Red d a
  Sub :: LEq d' d -> Node Black d' a -> SubNode c d a

-- | red-black tree with arbitrary height
data RBTree (a :: *) where
  Tree :: Node Black d a -> RBTree a

-- | in-order traversal
instance Foldable (Node c d) where
  foldMap _ Leaf = mempty
  foldMap f (BNode l a r) = foldMap f l <> f a <> foldMap f r
  foldMap f (RNode l a r) = foldMap f l <> f a <> foldMap f r
instance Foldable RBTree where
  foldMap f (Tree n) = foldMap f n

-- | Peano inequality arithmetic
incl :: Less m n -> Less (S m) (S n)
incl (Less e) = Less $ inc e

-- | Peano inequality arithmetic
inc :: LEq m n -> LEq (S m) (S n)
inc IsEq = IsEq
inc (IsLess e) = IsLess $ inc e

-- | Peano inequality arithmetic: zero is smallest
zless :: NP n -> Less Z (S n)
zless ZP = Less $ IsEq
zless (SP n) = case zless n of
  Less e -> Less $ IsLess e

-- | Peano comparison
cmp :: NP m -> NP n -> Compare m n
cmp ZP ZP = Equal
cmp ZP (SP n) = Smaller $ zless n
cmp (SP n) ZP = Bigger $ zless n
cmp (SP m) (SP n) = case cmp m n of
  Equal -> Equal
  Smaller e -> Smaller $ incl e
  Bigger e -> Bigger $ incl e

-- | reified node color
color :: Node c d a -> ColorProxy c
color (RNode _ _ _) = RedP
color (BNode _ _ _) = BlackP
color Leaf = BlackP

-- | reified insert color
icolor :: Insert c d a -> ColorProxy c
icolor (Same n) = color n
icolor (NowRed _) = BlackP
icolor (TwoRed _ _ _ _) = RedP

-- | reified tree height
depth :: Node c d a -> NP d
depth Leaf = ZP
depth (BNode l _ _) = SP $ depth l
depth (RNode l _ _) = depth l

-- | ambidextrous constructor for node
node :: Dir -> a -> Child c d a -> Child c d a -> Node c d a
node Lf a (BChild l) (BChild r) = BNode l a r
node Rg a (BChild r) (BChild l) = BNode l a r
node Lf a (RChild l) (RChild r) = RNode l a r
node Rg a (RChild r) (RChild l) = RNode l a r

-- | 'Nothing' for equal values, otherwise 'Just d' for correct direction
dir :: Ordering -> Maybe Dir
dir EQ = Nothing
dir LT = Just Lf
dir GT = Just Rg

-- | negation of inequality constraint
flip_dir :: Dir -> Dir
flip_dir Lf = Rg
flip_dir Rg = Lf

-- | ambidextrous pattern matching for 'Node'
unpack :: Node c d a -> Unpacked c d a
unpack Leaf = WasLeaf
unpack (BNode l a r) = WasNode a order
  where order Lf = (wrap l,wrap r)
        order Rg = (wrap r,wrap l)
        wrap = BChild
unpack (RNode l a r) = WasNode a order
  where order Lf = (wrap l,wrap r)
        order Rg = (wrap r,wrap l)
        wrap = RChild

-- | red-black tree where constraints hold everywhere except root
data Insert (c :: Color) (d :: N) (a :: *) where
  Same :: Node c d a -> Insert c d a
  NowRed :: Node Red d a -> Insert Black d a
  TwoRed :: Dir -> a -> Node Red d a -> Node Black d a -> Insert Red d a

-- | insert into a RBTree by creating a 'Leaf' and rebalancing the violation up to the root
insert :: Ord a => (a -> a -> a) -> Node c d a -> a -> Insert c d a
insert f n a = case unpack n of
  WasLeaf -> NowRed $ RNode Leaf a Leaf
  WasNode pivot c -> let maybe_d = dir $ compare a pivot in case maybe_d of
                      Nothing
                        -> Same $ update_root f n a
                      Just d -> case c d of
                             (BChild x,BChild y)
                               -> rebalance d pivot (insert f x a) y
                             (RChild x,RChild y)
                               -> rebalance_r d pivot (insert f x a) y

-- | change the value at the node itself
update_root :: (a -> a -> a) -> Node c d a -> a -> Node c d a
update_root _ Leaf _ = Leaf
update_root f (BNode l old r) new = BNode l (f old new) r
update_root f (RNode l old r) new = RNode l (f old new) r

-- | rotate to get invariants with black root and higher height
rebalance :: Dir -> a -> Insert cx d a -> Node cy d a -> Insert Black (S d) a
rebalance d a (Same x) y = Same $ node d a (BChild x) (BChild y)
rebalance d a (NowRed x) y = Same $ node d a (BChild x) (BChild y)
rebalance d a (TwoRed dx ax xx yx) y = case color y of
  BlackP -> Same $ node d a1 c1 c2
    where
      c1 = BChild $ node d a2 (RChild g1) (RChild g2)
      c2 = BChild $ node d a3 (RChild g3) (RChild g4)
      WasNode axx cx = unpack xx
      (RChild t1,RChild t2) = cx d
      (g1,g2,g3,g4,a1,a2,a3) = if d == dx
                               then (t1,t2,yx,y,ax,axx,a)
                               else (yx,t1,t2,y,axx,ax,a)
  RedP -> let WasNode ay c = unpack y in case c d of
    (RChild xy,RChild yy) -> let x' = node dx ax (BChild xx) (BChild yx)
                                 y' = node d ay (BChild xy) (BChild yy)
                             in NowRed $ node d a (RChild x') (RChild y')

-- | flip red nodes up
rebalance_r :: Dir -> a -> Insert Black d a -> Node Black d a -> Insert Red d a
rebalance_r d a (Same x) y = Same $ node d a (RChild x) (RChild y)
rebalance_r d a (NowRed x) y = TwoRed d a x y

-- | change color of root and increase height
make_black :: Node Red d a -> Node Black (S d) a
make_black (RNode l a r) = BNode l a r

-- | remove and return minimum or maximum
pop_bd :: Dir -> Node c d a -> DeleteBd c d a
pop_bd d n = case unpack n of
  WasLeaf -> FromLeaf
  WasNode a c -> case c d of
    (RChild x,RChild y) -> case pop_bd d x of
      FromLeaf -> Popped a $ NowBlack Leaf
      Popped m x' -> Popped m $ debalance_r d a x' y 
    (BChild x,BChild y) -> case pop_bd d x of
      FromLeaf -> case color y of
        BlackP -> Popped a $ Short Leaf
        RedP -> Popped a $ Still $ make_black y
      Popped m x' -> Popped m $ debalance_b d a x' y

-- | delete value if it is present
delete :: Ord a => Node c d a -> a -> Maybe (Delete c d a)
delete n a = case unpack n of
  WasLeaf -> Nothing
  WasNode pivot c -> case dir $ compare a pivot of
    Nothing -> case c Lf of
      (BChild x,BChild y) -> case pop_bd Rg x of
        FromLeaf -> case color y of
          RedP -> Just $ Still $ make_black y
          BlackP -> Just $ Short y
        Popped ax x' -> Just $ debalance_b Lf ax x' y
      (RChild x,RChild y) -> case pop_bd Rg x of
        FromLeaf -> Just $ NowBlack y
        Popped ax x' -> Just $ debalance_r Lf ax x' y
    Just d -> case c d of
      (BChild x,BChild y) -> case delete x a of
        Nothing -> Nothing
        Just x' -> Just $ debalance_b d pivot x' y
      (RChild x,RChild y) -> case delete x a of
        Nothing -> Nothing
        Just x' -> Just $ debalance_r d pivot x' y
      
-- | balance deleted tree to ensure invariants hold except at root (black root)
debalance_b :: Dir -> a -> Delete cx d a -> Node cy d a -> Delete Black (S d) a
debalance_b d a (Still x') y = Still $ node d a (BChild x') (BChild y)
debalance_b d a (NowBlack x') y = Still $ node d a (BChild x') (BChild y)
debalance_b d a (Short x') y = let WasNode ay cy = unpack y
  in case cy d of
    (BChild xy,BChild yy) -> case (color xy,color yy) of
      (_,RedP) -> let x'' = node d a (BChild x') (BChild xy)
                      y' = make_black yy
                  in Still $ node d ay (BChild x'') (BChild y')
      (RedP,BlackP) -> case unpack xy of
        WasNode axy cxy -> case cxy d of
          (RChild xxy,RChild yxy)
            -> let x'' = node d a (BChild x') (BChild xxy)
                   y' = node d axy (BChild yxy) (BChild yy)
               in Still $ node d ay (BChild x'') (BChild y')
      (BlackP,BlackP) -> let y' = node d ay (RChild xy) (RChild yy)
                         in Short $ node d a (BChild x') (BChild y')
    (RChild xy,RChild yy) -> debalance_b d ay (debalance_r d a (Short x') xy) yy

-- | balance deleted tree to ensure invariants hold except at root (red root)
debalance_r :: Dir -> a -> Delete Black d a -> Node Black d a -> Delete Red d a
debalance_r d a (Still x') y = Still $ node d a (RChild x') (RChild y)
debalance_r d a (Short x') y = let WasNode ay cy = unpack y
  in case cy d of
    (BChild xy,BChild yy) -> case (color xy,color yy) of
      (_,RedP) -> let x'' = node d a (BChild x') (BChild xy)
                      y' = make_black yy
                  in Still $ node d ay (RChild x'') (RChild y')
      (RedP,BlackP) -> case unpack xy of
        WasNode axy cxy -> case cxy d of
          (RChild xxy,RChild yxy)
            -> let x'' = node d a (BChild x') (BChild xxy)
                   y' = node d axy (BChild yxy) (BChild yy)
               in Still $ node d ay (RChild x'') (RChild y')
      (BlackP,BlackP)
        -> let y' = node d ay (RChild xy) (RChild yy)
           in NowBlack $ node d a (BChild x') (BChild y')

-- | join two trees of unequal heights at a new node
join_ins :: Dir -> a -> SubNode Black d a -> Node c d a -> Insert c d a
join_ins d a (Sub IsEq x) y = case color y of
  BlackP -> NowRed $ node d a (RChild x) (RChild y)
  RedP -> TwoRed (flip_dir d) a y x
join_ins d a (Sub (IsLess e) x) y = case unpack y of
  WasNode ay cy -> case cy d of
    (BChild xy,BChild yy)
      -> let x' = join_ins d a (Sub e x) xy
         in rebalance d ay x' yy
    (RChild xy,RChild yy)
      -> let x' = join_ins d a (Sub (IsLess e) x) xy
         in rebalance_r d ay x' yy

-- | paint insert black, remember proof that height increased by at most one
paint_insert_black :: Insert c d a -> SubNode Black (S d) a
paint_insert_black (Same n) = case color n of
  BlackP -> Sub (IsLess IsEq) n
  RedP -> Sub IsEq $ make_black n
paint_insert_black (NowRed n) = Sub IsEq $ make_black n
paint_insert_black (TwoRed d a x y) = Sub IsEq $ node d a (BChild x) (BChild y)

-- | send children to trees of smaller height
child_to_sub :: Child c d a -> SubNode c d a
child_to_sub (BChild x) = case color x of
  BlackP -> Sub (IsLess IsEq) x
  RedP -> Sub IsEq $ make_black x
child_to_sub (RChild x) = Sub IsEq x

-- | finish partial deletion and remember proof that height decreased
delete_to_sub :: Delete c d a -> SubNode c d a
delete_to_sub (Still x) = case color x of
  RedP -> StillRed x
  BlackP -> Sub IsEq x
delete_to_sub (NowBlack x) = Sub IsEq x
delete_to_sub (Short x) = Sub (IsLess IsEq) x

-- | compose inequality constraints
lift_sub :: LEq d' d -> SubNode c d' a -> SubNode c d a
lift_sub IsEq x = x
lift_sub (IsLess e) (StillRed x) = Sub (inc e) $ make_black x
lift_sub (IsLess e) (Sub e' x) = lift_sub (inc e) $ Sub (IsLess e') x

-- | weaken inequality constraints
inc_sub :: SubNode c d a -> SubNode c' (S d) a
inc_sub (StillRed x) = Sub IsEq $ make_black x
inc_sub (Sub e x) = Sub (IsLess e) x

-- | for Subnode, can assume root is red
red_sub :: SubNode c d a -> SubNode Red d a
red_sub (StillRed x) = StillRed x
red_sub (Sub e x) = Sub e x

-- | join nodes with upper bounds on height at new black node
join_b :: Dir -> a -> SubNode cx d a -> Node cy d a -> SubNode Black (S d) a
join_b d a (StillRed x) y = Sub IsEq $ node d a (BChild x) (BChild y)
join_b d a (Sub e x) y = paint_insert_black $ join_ins d a (Sub e x) y

-- | join nodes with upper bounds on height at new red node
join_r :: Dir -> a -> SubNode Black d a -> Node Black d a -> SubNode Red d a
join_r d a (Sub e x) y = case join_ins d a (Sub e x) y of
  Same n -> Sub IsEq n
  NowRed n -> StillRed n

-- | join two trees of unequal heights, new root is black
join2_b :: Dir -> SubNode cx d a -> Node cy d a -> SubNode Black (S d) a
join2_b d (StillRed x) y = case pop_bd (flip_dir d) x of
  Popped a x' -> join_b d a (delete_to_sub x') y
join2_b d (Sub e x) y = case pop_bd (flip_dir d) x of
  FromLeaf -> case color y of
    RedP -> Sub IsEq $ make_black y
    BlackP -> Sub (IsLess IsEq) y
  Popped a x' -> join_b d a (lift_sub e $ delete_to_sub x') y

-- | join two trees of unequal heights, new root is red
join2_r :: Dir -> SubNode Black d a -> Node Black d a -> SubNode Red d a
join2_r d (Sub e x) y = case pop_bd (flip_dir d) x of
  FromLeaf -> Sub IsEq y
  Popped a x' -> join_r d a (lift_sub e $ delete_to_sub x') y

-- | join two trees of unequal heights, with a possible value between them, black root
joinm_b :: Dir -> Maybe a -> SubNode cx d a -> Node cy d a -> SubNode Black (S d) a
joinm_b d Nothing x y = join2_b d x y
joinm_b d (Just a) x y = join_b d a x y

-- | join two trees of unequal heights, with a possible value between them, red root
joinm_r :: Dir -> Maybe a -> SubNode Black d a -> Node Black d a -> SubNode Red d a
joinm_r d Nothing x y = join2_r d x y
joinm_r d (Just a) x y = join_r d a x y

-- | split red-black tree at a given value
split :: Ord a => Node c d a -> a -> (Maybe a,SubNode c d a,SubNode c d a)
split n a = case unpack n of
  WasLeaf -> (Nothing, Sub IsEq Leaf, Sub IsEq Leaf)
  WasNode pivot c -> case dir $ compare a pivot of
    Nothing -> case c Lf of
      (x,y) -> (Just pivot,child_to_sub x,child_to_sub y)
    Just d -> case c d of
      (BChild x,BChild y) -> case split x a of
        (found,xl,xr) -> if d == Lf
          then (found,inc_sub xl,join_b Lf pivot xr y)
          else (found,join_b Rg pivot xl y,inc_sub xr)
      (RChild x,RChild y) -> case split x a of
        (found,xl,xr) -> if d == Lf
          then (found,red_sub xl,join_r Lf pivot xr y)
          else (found,join_r Rg pivot xl y,red_sub xr)

-- | red-black tree without fixed height
tree :: Node c d a -> RBTree a
tree x = case color x of
  BlackP -> Tree x
  RedP -> Tree $ make_black x

-- | finish insertion by dropping height data and painting root black
finish :: Insert Black d a -> RBTree a
finish (Same n) = Tree n
finish (NowRed (RNode l a r)) = Tree $ BNode l a r

-- | finish insertion by dropping height data
findish :: Delete Black d a -> RBTree a
findish (Still n) = Tree n
findish (Short n) = Tree n

-- | insert 'a', or update 'b' to 'f b a'
insert_tree_with :: Ord a => (a -> a -> a) -> RBTree a -> a -> RBTree a
insert_tree_with f (Tree n) a = finish $ insert f n a

-- | insert, keep most recent value
insert_tree :: Ord a => RBTree a -> a -> RBTree a
insert_tree = insert_tree_with (\a b->b)

-- | remove minimum value, if it exists
pop_min :: RBTree a -> Maybe (a,RBTree a)
pop_min (Tree n) = case pop_bd Lf n of
  FromLeaf -> Nothing
  Popped a n' -> Just (a,findish n')

-- | delete element, if it exists
delete_tree :: Ord a => RBTree a -> a -> Maybe (RBTree a)
delete_tree (Tree n) a = fmap findish $ delete n a

-- | join two trees of unequal heights at a new node
join_tree :: RBTree a -> a -> RBTree a -> RBTree a
join_tree (Tree x) a (Tree y) = case cmp (depth x) (depth y) of
  Equal -> Tree $ node Lf a (BChild x) (BChild y)
  Smaller (Less e) -> finish $ join_ins Lf a (Sub (IsLess e) x) y
  Bigger (Less e) -> finish $ join_ins Rg a (Sub (IsLess e) y) x

-- | join two trees of unequal heights
join2_tree :: RBTree a -> RBTree a -> RBTree a
join2_tree (Tree x) (Tree y) = case cmp (depth x) (depth y) of
  Equal -> subnode_to_tree $ join2_b Lf (Sub IsEq x) y
  Smaller (Less e) -> subnode_to_tree $ join2_b Lf (Sub (IsLess e) x) y
  Bigger (Less e) -> subnode_to_tree $ join2_b Rg (Sub (IsLess e) y) x

-- | take the union of two red-black trees, save 'f a b' if 'a' present in first,
-- | 'b' present in second, and 'cmp a b == Eq'
union_with :: Ord a => (a -> a -> a) -> RBTree a -> RBTree a -> RBTree a
union_with f (Tree x) (Tree y) = case cmp (depth x) (depth y) of
  Bigger _ -> union_with (flip f) (Tree y) (Tree x)
  _ -> case unpack y of
    WasLeaf -> Tree x
    WasNode pivot c ->
      let (cxy,cyy) = c Lf
          xy = subnode_to_tree $ child_to_sub cxy
          yy = subnode_to_tree $ child_to_sub cyy
          (found,xx,yx) = split_tree (Tree x) pivot
          a = maybe pivot (flip f pivot) found
      in join_tree (union_with f xx xy) a (union_with f yx yy)

-- | take the union, keep elements of first tree
union :: Ord a => RBTree a -> RBTree a -> RBTree a
union = union_with (\a b -> a)

-- | partial monad law for RBTree
union_map :: Ord b => (a -> RBTree b) -> RBTree a -> RBTree b
union_map f = foldr (\a b -> union (f a) b) empty

-- | forget constraints on node depth
subnode_to_tree :: SubNode Black d a -> RBTree a
subnode_to_tree (Sub _ x) = Tree x

-- | split red-black tree at given value
split_tree :: Ord a => RBTree a -> a -> (Maybe a,RBTree a,RBTree a)
split_tree (Tree n) a = let (found,l,r) = split n a
                        in (found,subnode_to_tree l,subnode_to_tree r)

-- | build tree by iterative insertion
fold_tree :: (Foldable t, Ord a) => t a -> RBTree a
fold_tree = foldl insert_tree (Tree Leaf)

-- | iteratively generate 'b' values and update internal 'a' state
unfold :: (a -> Maybe (b,a)) -> a -> [b]
unfold f a = case f a of
  Nothing -> []
  Just (b,a') -> b : unfold f a'

-- | iterate a partially defined function
iter :: (a -> Maybe a) -> a -> [a]
iter f = unfold (fmap (\x -> (x,x)) . f)

-- | red-black tree with no elements
empty :: RBTree a
empty = Tree Leaf

-- | red-black tree with one element
singleton :: a -> RBTree a
singleton a = Tree $ BNode Leaf a Leaf

-- | find a value in the middle of the tree by alternatively taking left and right children
middle :: Node c d a -> Maybe a -> Dir -> Maybe a
middle Leaf x _ = x
middle (BNode l a _) _ Lf = middle l (Just a) Rg
middle (BNode _ a r) _ Rg = middle r (Just a) Lf
middle (RNode l a _) _ Lf = middle l (Just a) Rg
middle (RNode _ a r) _ Rg = middle r (Just a) Lf

-- | find a value in the middle of the tree
mid :: RBTree a -> Maybe a
mid (Tree n) = middle n Nothing Lf

-- | return values of red-black tree by iteratively removing middles
shuffled :: Ord a => RBTree a -> [a]
shuffled = unfold remove_mid
  where remove_mid t = do
          m <- mid t
          t' <- delete_tree t m
          return (m,t')

-- | change the BST type by splitting at a leaf value and then recombining
shuffle :: Ord a => RBTree a -> Maybe (RBTree a)
shuffle t = do
  m <- mid t
  let (found,l,r) = split_tree t m
  m' <- found
  return $ join_tree l m' r

-- | delete all values from a List
delete_many :: Ord a => RBTree a -> [a] -> [RBTree a]
delete_many t [] = [t]
delete_many t (a:as) = case delete_tree t a of
  Nothing -> delete_many t as
  Just t' -> t : delete_many t' as

data InfList a = Cons a (InfList a)

-- | (Lazy) 'List' of all prime numbers using priority queue http://dx.doi.org/10.1017/S0956796804005210
primes :: [Int]
primes = 2 : 3 : go (insert_tree empty (9,6)) cands
  where
    go q cs@(Cons c cs') = case pop_min q of
      Nothing -> undefined
      Just ((k,p2),q') -> case compare k c of
        LT -> go (insert_tree q' (k + p2,p2)) cs
        EQ -> go (insert_tree q' (k + p2,p2)) cs'
        GT -> c : go (insert_tree q (c*c,2*c)) cs'
    cands = loop 5 where loop k = k `Cons` loop (k + 2)

-- | red-black tree without existential height constraint
data URBTree a = ULeaf | UNode Color (URBTree a) a (URBTree a) deriving (Show)

-- | remove height constraint
untype :: Node c d a -> URBTree a
untype Leaf = ULeaf
untype (BNode l a r) = UNode Black (untype l) a (untype r)
untype (RNode l a r) = UNode Red (untype l) a (untype r)

-- | remove existential height constraint
tuntype :: RBTree a -> URBTree a
tuntype (Tree n) = untype n

-- | helper function: get all elements of 'Foldable'
to_list :: Foldable t => t a -> [a]
to_list = foldr (:) []

-- | calculate a large(ish) prime number
main = mapM print . map (primes !!) . takeWhile (<100000) $ iterate (*2) 1
