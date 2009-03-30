<!--
This is the source for the splonderzoek blog entry dated 2008-02-15:

http://splonderzoek.blogspot.com/2009/02/incremental-fold-design-pattern.html
-->

<p>
I recently read the article "How to Refold a Map" by David F. Place in <a href="http://www.haskell.org/haskellwiki/The_Monad.Reader">The Monad.Reader</a> <a href="http://www.haskell.org/sitewiki/images/6/6a/TMR-Issue11.pdf">Issue 11</a>. I've been thinking about incremental algorithms in Haskell for some time, and I realized that Place has written a specific instance (and optimization) of a more general concept: the <em>incremental fold</em>.
</p>
<p>
In this article, I demonstrate a design pattern for converting a datatype and related functions into an incremental fold. The pattern is not difficult to comprehend, but it would be nice to improve upon it. I explore a few improvements and issues with those improvements. Ultimately, I'd like to see this functionality in a program instead of a design pattern.
</p>
<p>
<em>Note: This is a <a href="http://www.haskell.org/haskellwiki/Literate_programming">literate Haskell</a> article. You can copy the text of the entire article, paste it into a new file called <code>IncrementalTreeFold.lhs</code>, and load it into <a href="http://www.haskell.org/ghc/docs/latest/html/users_guide/ghci.html">GHCi</a>.</em>
</p>
<pre>

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module IncrementalTreeFold where
> import Prelude hiding (elem)
> import qualified Data.Char as Char (ord)

</pre>

<h2>Introducing a Typical Binary Tree</h2>

<p>
Before we get to the conversion, let's choose an appropriate datatype. Place adapted the <a href="http://hackage.haskell.org/packages/archive/containers/0.2.0.0/doc/html/src/Data-Map.html#Map">Map type</a> used in <a href="http://hackage.haskell.org/packages/archive/containers/0.2.0.0/doc/html/Data-Map.html">Data.Map</a> (or <a href="http://hackage.haskell.org/packages/archive/containers/0.2.0.0/doc/html/src/Data-Set.html#Set">Set</a> in <a href="http://hackage.haskell.org/packages/archive/containers/0.2.0.0/doc/html/Data-Set.html">Data.Set</a>). To simplify my presentation, I will use an ordered binary tree with labeled nodes.
</p>
<pre>

> data Tree a
>   = Tip
>   | Bin a (Tree a) (Tree a)
>   deriving Show

</pre>
<p>
Next, let's introduce some useful functions. An incremental fold is not necessarily like applying a <a href="http://www.citeulike.org/user/spl/tag/fold">fold function</a> (a.k.a. a <a href="http://knol.google.com/k/edward-kmett/catamorphisms/3qi7x2qrdushx/2">catamorphism</a>, not a <a href="http://www.citeulike.org/user/spl/tag/crush">crush function</a> that has become known as a fold) to a value directly. Instead, as I will later show, it integrates into existing functions that manipulate values.  That said, we should have some functions for building <code>Tree</code>s. Here is the beginning of a <code>Tree</code> API. (There are a number of other operations, e.g. <code>delete</code> and <code>lookup</code>, that can easily be added but do not contribute much to the discussion.)
</p>
<p>
<code>empty</code> builds a tree with no elements.
</p>
<pre>

> empty :: (Ord a) => Tree a
> empty = Tip

</pre>
<p>
<code>singleton</code> builds a tree with a single element.
</p>
<pre>

> singleton :: (Ord a) => a -> Tree a
> singleton x = Bin x Tip Tip

</pre>
<p>
<code>insert</code> puts a value in the appropriate place given a left-to-right ordering of values in the tree.
</p>
<pre>

> insert :: (Ord a) => a -> Tree a -> Tree a
> insert x t =
>   case t of
>     Tip ->
>       singleton x
>     Bin y lt rt ->
>       case compare x y of
>         LT -> Bin y (insert x lt) rt
>         GT -> Bin y lt (insert x rt)
>         EQ -> Bin x lt rt

</pre>
<p>
<code>fromList</code> creates a tree from a list of values.
</p>
<pre>

> fromList :: (Ord a) => [a] -> Tree a
> fromList = foldr insert empty

</pre>
<p>
<code>elem</code> determines if a value is an element of a tree.
</p>
<pre>

> elem :: (Ord a) => a -> Tree a -> Bool
> elem x t =
>   case t of
>     Tip ->
>       False
>     Bin y lt rt ->
>       case compare x y of
>         LT -> elem x lt
>         GT -> elem x rt
>         EQ -> True

</pre>
<p>
Now, using our library of sorts, we can create binary search tree and check if a value is in the tree.
</p>
<pre>

> test1 = 37 `elem` fromList [8,23,37,82,3]

</pre>

<h2>Tree Folds</h2>

<p>
Suppose that we now want the size of the tree. For good abstraction and high reuse, we create a <code>fold</code> function.
</p>
<pre>

> data Alg a b = Alg { ftip :: b, fbin :: a -> b -> b -> b }

> fold :: Alg a b -> Tree a -> b
> fold alg = go
>   where
>     go Tip           = ftip alg
>     go (Bin x lt rt) = fbin alg x (go lt) (go rt)

</pre>
<p>
<code>fold</code> allows us to write a simple <code>size</code> function.
</p>
<pre>

> size :: Tree a -> Int
> size = fold (Alg 0 (\_ lr rr -> 1 + lr + rr))

</pre>
<p>
I use the datatype <code>Alg</code> here to contain the <a href="http://www.alpheccar.org/en/posts/show/77">algebra of the fold</a>. In <code>size</code>, we simply replace each constructor in the algebra of <code>Tree</code> with a corresponding element from the algebra of integer addition. Since you're reading this article, you're probably a Haskell programmer and already familiar with the sorts of functions that can be written with folds. Here are a few others.
</p>
<pre>

> filter :: (a -> Bool) -> Tree a -> [a]
> filter f = fold (Alg [] (\x lr rr -> if f x then [x] else [] ++ lr ++ rr))

> ord :: Tree Char -> Tree Int
> ord  = fold (Alg Tip (\x lt rt -> Bin (Char.ord x) lt rt))

</pre>

<h2>Incremental Change</h2>

<p>
Now that we have a grasp on using a fold on a datatype, I would like to show how to extend my binary tree "library" defined above to support an incremental fold. The incremental fold can (I believe) do everything a traditional fold can do, but it does it during <code>Tree</code> construction instead of externally in a separate function. This means that every time we produce a new <code>Tree</code> (via <code>singleton</code>, <code>insert</code>, or <code>fromList</code> for example), we get a new result of the incremental fold.
</p>
<p>
Transforming our library into an incremental calculating machine involves several steps. The first step is extending the datatype to hold the incremental result. Since we want to be polymorphic in the result type, we add a type parameter <code>r</code> to the <code>Tree</code> type constructor. And since each constructor may possibly have an incremental result, it must also be extended with a place holder for <code>r</code>.
</p>
<pre>

> data Tree' a r
>   = Tip' r
>   | Bin' a (Tree' a r) (Tree' a r) r
>   deriving Show

</pre>
<p>
For convenience and possibly to hide the modified constructors from the outside world, we add a function for retrieving the increment result.
</p>
<pre>

> result' :: Tree' a r -> r
> result' (Tip' r)       = r
> result' (Bin' _ _ _ r) = r

</pre>
<p>
As I mentioned earlier, the machinery of the fold is now in the construction. To implement this second step, we use <a href="http://splonderzoek.blogspot.com/2008/01/smart-constructors.html">smart constructors</a>.
</p>
<pre>

> tip' :: Alg a r -> Tree' a r
> tip' alg = Tip' (ftip alg)

> bin' :: Alg a r -> a -> Tree' a r -> Tree' a r -> Tree' a r
> bin' alg x lt rt = Bin' x lt rt (fbin alg x (result' lt) (result' rt))

</pre>
<p>
Both <code>tip'</code> and <code>bin'</code> construct new values of <code>Tree' a r</code> and using the algebra, calculate the incremental result to be stored in each value. Thus, the actual fold operation is "hidden" in the construction of values.
</p>
<p>
Now, in order to put the incremental fold to work in a function, we simply (1) add the algebra to the function's arguments, (2) add an wildcard pattern for the result field in constructor patterns, and (3) replace applications of the constructors with that of their incremental cousins. Here's an example of the <code>singleton</code> and <code>insert</code> functions modified for incremental folding.
</p>
<pre>

> singleton' :: (Ord a) => Alg a r -> a -> Tree' a r
> singleton' alg x = bin' alg x (tip' alg) (tip' alg)

> insert' :: (Ord a) => Alg a r -> a -> Tree' a r -> Tree' a r
> insert' alg x t =
>   case t of
>     Tip' _ ->
>       singleton' alg x
>     Bin' y lt rt _ ->
>       case compare x y of
>         LT -> bin' alg y (insert' alg x lt) rt
>         GT -> bin' alg y lt (insert' alg x rt)
>         EQ -> bin' alg x lt rt

</pre>
<p>
Comparing these functions with the initial versions, we see that the changes are readily apparent. Modify every other <code>Tree'</code>-hugging function in the same manner, and you have a design pattern for an incremental fold!
</p>

<h2>Improving the Incremental Implementation</h2>

<p>
Of course, you may complain that there's some amount of boilerplate work involved. For example, we have to add this <code>alg</code> argument everywhere. Let's try to replace that with a type class.
</p>
<pre>

< class Alg'' a r where
<   ftip'' :: r
<   fbin'' :: a -> r -> r -> r

</pre>
<p>
And we redefine our smart constructors.
</p>
<pre>

< tip'' :: (Alg' a r) => Tree' a r
< tip'' = Tip' ftip''

</pre>
<p>
But there's a problem here! GHC reports that it <code>Could not deduce (Alg'' a r) from the context (Alg'' a1 r)</code>. The poor compiler cannot infer the type of the parameter <code>a</code> since <code>ftip''</code> has only type <code>r</code>.
</p>
<p>
Let's try another version of the class. In this one, we add a dummy argument to <code>ftip'</code> in order to force GHC to correctly infer the full type.
</p>
<pre>

> class Alg'' a r where
>   ftip'' :: a -> r
>   fbin'' :: a -> r -> r -> r

> tip'' :: forall a r . (Alg'' a r) => Tree' a r
> tip'' = Tip' (ftip'' (undefined :: a))

> bin'' :: (Alg'' a r) => a -> Tree' a r -> Tree' a r -> Tree' a r
> bin'' x lt rt = Bin' x lt rt (fbin'' x (result' lt) (result' rt))

</pre>
<p>
This provides one (not very pretty) solution to the problem. I'm able to get around the need to require an argument for <code>tip''</code> by using <a href="http://www.haskell.org/ghc/docs/latest/html/users_guide/other-type-extensions.html#scoped-type-variables">lexically scoped type variables</a>. But it doesn't remove the ugly type from <code>ftip''</code>, and the user is forced to ignore it when writing an instance.
</p>
<p>
The functions can now be rewritten with the <code>Alg''</code> constraint.
</p>
<pre>

> empty'' :: (Ord a, Alg'' a r) => Tree' a r
> empty'' = tip''

> singleton'' :: (Ord a, Alg'' a r) => a -> Tree' a r
> singleton'' x = bin'' x tip'' tip''

> insert'' :: (Ord a, Alg'' a r) => a -> Tree' a r -> Tree' a r
> insert'' x t =
>   case t of
>     Tip' _ ->
>       singleton'' x
>     Bin' y lt rt _ ->
>       case compare x y of
>         LT -> bin'' y (insert'' x lt) rt
>         GT -> bin'' y lt (insert'' x rt)
>         EQ -> bin'' x lt rt

> fromList'' :: (Ord a, Alg'' a r) => [a] -> Tree' a r
> fromList'' = foldr insert'' empty''

</pre>
<p>
These versions look more like the non-incremental implementations above. To use them, we need to declare an instance of <code>Alg''</code> with an appropriate algebra for our desired incremental result. Here's how we would rewrite <code>size</code>.
</p>
<pre>

> newtype Size = Size { unSize :: Int }

> instance Alg'' a Size where
>   ftip'' _ = Size 0
>   fbin'' _ lr rr = Size (1 + unSize lr + unSize rr)

> size'' :: Tree' a Size -> Int
> size'' = unSize . result'

> test2 = size'' $ insert'' 's' $ insert'' 'p' $ insert'' 'l' $ fromList'' "onderzoek"

</pre>

<p>
<code>Size</code> is still defined as a fold, but the result is incrementally built with each application of a library function. This can have a nice performance boost as Place also found in his article.
</p>

<h2>Generic Thoughts</h2>

<p>
On reflecting over my implementation, I really don't like the dummy arguments required by constructors like <code>Tip</code>. There are other approaches to dealing with this, but I haven't yet found a better one. If you use a <a href="http://www.haskell.org/haskellwiki/Functional_dependencies">functional dependency</a> such as <code>r -> a</code> in the definition of <code>Alg''</code>, then <code>a</code> would be uniquely determined by <code>r</code>. In the case of <code>size''</code>, we would have to specify a concrete element type for <code>Tree'</code> instead of the parameter <code>a</code> (or use <a href="http://www.haskell.org/ghc/docs/latest/html/users_guide/type-class-extensions.html#undecidable-instances">undecidable instances</a>). Perhaps, dear reader, you might have a better solution?
</p>
<p>
The incremental fold pattern is great for documenting an idea, but it has several downsides: (1) The obvious one is that it requires modifying a datatype and code. This is not always desirable and often not practical. (2) Implementing an incremental fold can involve a lot of boilerplate code and many, small changes that are monotonous and boring. It's very easy to make mistakes. In fact, I made several copy-paste-and-forget-to-change errors while writing this article.
</p>
<p>
As <a href="http://www.comlab.ox.ac.uk/jeremy.gibbons/">Jeremy Gibbons</a> and others have shown us, <a href="http://www.comlab.ox.ac.uk/publications/publication1452-abstract.html">design patterns are better as programs</a>. Since the code is so regular, it seems very receptive to some <a href="http://www.cs.uu.nl/wiki/GenericProgramming">generic programming</a>. I plan to explore this further, possibly using one of the <a href="http://hackage.haskell.org/packages/archive/pkg-list.html#cat:generics">many generics libraries</a> available for Haskell or designing a new one. Suggestions and feedback are welcome.
</p>
