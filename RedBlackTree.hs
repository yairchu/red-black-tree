{-# OPTIONS -Wall #-}
{-# LANGUAGE EmptyDataDecls, ExistentialQuantification, GADTs #-}

module RedBlackTree
    ( RedBlackTree
    , redBlackEmpty, redBlackInsert
    , redBlackFromList, redBlackToList
    ) where

import Data.List (foldl')

-- Type definition
data Zero
data Succ n

data RedBlackTree a = forall n. RBTree (BlackNode n a)
data BlackNode n a where
    RBNil :: BlackNode Zero a
    BlackNode :: RBNode n a -> a -> RBNode n a -> BlackNode (Succ n) a
data RBNode n a
    = ItsRed (RedNode n a)
    | ItsBlack (BlackNode n a)
data RedNode n a = RedNode (BlackNode n a) a (BlackNode n a)

-- Show instance
instance Show a => Show (RedBlackTree a) where
    show (RBTree tree) = show tree
instance Show a => Show (BlackNode n a) where
    show RBNil = ""
    show (BlackNode left mid right) = showNode "B" left mid right
instance Show a => Show (RBNode n a) where
    show (ItsRed tree) = show tree
    show (ItsBlack tree) = show tree
instance Show a => Show (RedNode n a) where
    show (RedNode left mid right) = showNode "R" left mid right

showNode :: (Show a, Show b) => String -> a -> b -> a -> String
showNode color left mid right =
    indentSide (' ', '|') (show left) ++
    color ++ ":" ++ show mid ++ "\n" ++
    indentSide ('|', ' ') (show right)

indentSide :: (Char, Char) -> String -> String
indentSide _ "" = ""
indentSide (leftIndent, rightIndent) side =
    unlines $ map (leftIndent:) left ++ ['+':mid] ++ map (rightIndent:) right
    where
        (left, mid:right) = break ((`notElem` " |+") . head) $ lines side

-- Functions
redBlackToList :: RedBlackTree a -> [a]
redBlackToList (RBTree node) = rbNodeToList (ItsBlack node)

rbNodeToList :: RBNode n a -> [a]
rbNodeToList (ItsRed (RedNode left x right)) =
    rbNodeToList (ItsBlack left) ++ [x] ++ rbNodeToList (ItsBlack right)
rbNodeToList (ItsBlack RBNil) = []
rbNodeToList (ItsBlack (BlackNode left x right)) =
    rbNodeToList left ++ [x] ++ rbNodeToList right

redBlackEmpty :: RedBlackTree a
redBlackEmpty = RBTree RBNil

redBlackFromList :: Ord a => [a] -> RedBlackTree a
redBlackFromList = foldl' (flip redBlackInsert) redBlackEmpty

-- Insert
redBlackInsert :: Ord a => a -> RedBlackTree a -> RedBlackTree a
redBlackInsert x (RBTree tree) =
    case bInsert x tree of
        ItsBlack newTree -> RBTree newTree
        ItsRed (RedNode left mid right) -> RBTree $ BlackNode (ItsBlack left) mid (ItsBlack right)

bInsert :: Ord a => a -> BlackNode n a -> RBNode n a
bInsert x RBNil = ItsRed $ RedNode RBNil x RBNil
bInsert x (BlackNode left mid right)
    | x < mid = bInsertH False x left mid right
    | otherwise = bInsertH True x right mid left

bInsertH :: Ord a => Bool -> a -> RBNode n a -> a -> RBNode n a -> RBNode (Succ n) a
bInsertH isRev x left mid right =
    case revInsertResult isRev $ rbInsert x left of
        ValidTree newLeft -> ItsBlack $ makeNode isRev BlackNode newLeft mid right
        RRB ll lm lr -> rrb ll lm lr
        BRR ll lm lr ->
            let (RedNode lrl lrm lrr) = revRedNode isRev lr
            in rrb (makeNode isRev RedNode ll lm lrl) lrm lrr
    where
        rrb ll lm lr =
            case right of
                ItsRed r ->
                    let (RedNode rl rm rr) = revRedNode isRev r
                    in ItsRed $ makeNode isRev RedNode
                        (makeNode isRev BlackNode (ItsRed ll) lm (ItsBlack lr))
                        mid
                        (makeNode isRev BlackNode (ItsBlack rl) rm (ItsBlack rr))
                ItsBlack r ->
                    ItsBlack $ makeNode isRev BlackNode
                        (ItsRed ll)
                        lm
                        (ItsRed (makeNode isRev RedNode lr mid r))

makeNode :: Bool -> (a -> b -> a -> c) -> a -> b -> a -> c
makeNode False func left mid right = func left mid right
makeNode True func left mid right = func right mid left

revRedNode :: Bool -> RedNode n a -> RedNode n a
revRedNode False x = x
revRedNode True (RedNode left mid right) = RedNode right mid left

rbInsert :: Ord a => a -> RBNode n a -> InsertResult n a
rbInsert x (ItsBlack node) = ValidTree $ bInsert x node
rbInsert x (ItsRed (RedNode left mid right))
    | x < mid = rInsert False x left mid right
    | otherwise = rInsert True x right mid left

data InsertResult n a where
    ValidTree :: RBNode n a -> InsertResult n a
    RRB :: RedNode n a -> a -> BlackNode n a -> InsertResult n a
    BRR :: BlackNode n a -> a -> RedNode n a -> InsertResult n a

rInsert :: Ord a => Bool -> a -> BlackNode n a -> a -> BlackNode n a -> InsertResult n a
rInsert isRev x left mid right =
    case bInsert x left of
        ItsBlack newLeft -> ValidTree . ItsRed $ makeNode isRev RedNode newLeft mid right
        ItsRed newLeft -> revInsertResult isRev $ RRB newLeft mid right

revInsertResult :: Bool -> InsertResult n a -> InsertResult n a
revInsertResult False x = x
revInsertResult True (ValidTree x) = ValidTree x
revInsertResult True (RRB left mid right) = BRR right mid left
revInsertResult True (BRR left mid right) = RRB right mid left
