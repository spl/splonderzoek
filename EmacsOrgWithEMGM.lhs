**Note:** This is the source for the post dated 2008-03-06:

http://splonderzoek.blogspot.com/2009/03/experiments-with-emgm-emacs-org-files.html

I've been meaning to write some things about
[EMGM](http://www.cs.uu.nl/wiki/GenericProgramming/EMGM) for a while, but I
hadn't found one of those [round
tuits](http://en.wiktionary.org/wiki/round_tuit) as of yet. Until now.

David Miani is working on a Haskell library for interacting with emacs [org
files](http://orgmode.org/). "For those that do not know, an org file is a
structured outline style file that has nested headings, text, tables and other
elements," [says
David](http://thread.gmane.org/gmane.comp.lang.haskell.cafe/54031). He has a
collection of datatypes for building and manipulating these files.

David seeks a better way to do what he's doing. (It's a noble goal. I hope you
keep doing it.) To return to his words: "While writing an OrgFile is fairly
easy, reading (and accessing inner parts) of an org file is very tedious, and
modifying them is horrendous." He goes on to give an example that I'll describe
more below.

When I read the above statement, I was expecting that [generic
programming](http://www.haskell.org/haskellwiki/Research_papers/Generics) could
help him out. When I saw his code, I knew it was a perfect use case. That's what
inspired this entry, the first use case for EMGM from [Haskell
Café](http://www.haskell.org/mailman/listinfo/haskell-cafe).

First, this is a [literate
Haskell](http://www.haskell.org/haskellwiki/Literate_programming) post, so we
run through the usual preliminaries.

> {-# LANGUAGE TemplateHaskell       #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleContexts      #-}
> {-# LANGUAGE FlexibleInstances     #-}
> {-# LANGUAGE OverlappingInstances  #-}
> {-# LANGUAGE UndecidableInstances  #-}
> 
> module EmacsOrgWithEMGM where
>
> import Text.Regex.Posix

We import
[Generics.EMGM.Derive](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM-Derive.html)
for the deriving portion of EMGM. This is not exported from the main body of the
library, because it has a lot of symbols only needed for building a
representation. We'd rather not clog up your symbol list if possible.

> import Generics.EMGM.Derive

In general, I'd recommend doing the deriving in a separate module and only
export the datatype and generated type class instances. Then, in other modules,
you can use EMGM functions or write your own. However, this being a
demonstration, we will also import
[Generics.EMGM](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM.html)
here to use the available functions.

> import qualified Generics.EMGM as G

The following collection of types are copied from [David's
post](http://thread.gmane.org/gmane.comp.lang.haskell.cafe/54031). They describe
the structure of an org file.

> type Line = Int
> type Column = Int
> 
> data FilePosition = FilePosition Line Column
> 
> data WithPos a = WithPos { filePos :: FilePosition, innerValue :: a }
> 
> data OrgTableP = OrgTableP [WithPos OrgTableRow]
> 
> data OrgFileElementP
>   = TableP OrgTableP
>   | ParagraphP String
>   | HeadingP OrgHeadingP
> 
> data OrgHeadingP = OrgHeadingP Int String [WithPos OrgFileElementP]
> 
> data OrgFileP = OrgFileP [WithPos OrgFileElementP]
> 
> data OrgTableRow
>   = OrgTableRow [String]
>   | OrgTableRowSep 

In order to use EMGM, we must generate the values and instances used by the
library. This is simple with one Template Haskell (TH).

> $(deriveMany 
>   [ ''FilePosition
>   , ''WithPos
>   , ''OrgTableP
>   , ''OrgHeadingP
>   , ''OrgFileElementP
>   , ''OrgFileP
>   , ''OrgTableRow
>   ])

Note that in this case, we had to use
[`deriveMany`](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM-Derive.html#v%3AderiveMany)
for a list of type names. For the most part, we'd probably use
[`derive`](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM-Derive.html#v%3Aderive);
however, the datatypes `OrgHeadingP` and `OrgFileElementP` are mutually
recursive. If we use `derive` for each type, then some values are generated that
are naturally also muturally recursive. Apparently, TH expects all symbols to be
available on a per-splice basis. This means that we can't `$(derive
''OrgFileElementP)` and then `$(derive ''OrgHeadingP)` or vice versa. We have to
derive them simultaneously, so that both sets of symbols are available at the
same time.

David gives the example of reading "the description line for the project named
'Project14'" in the following file:

~~~
* 2007 Projects
** Project 1
Description: 1
Tags: None
** Project 2
Tags: asdf,fdsa
Description: hello
* 2008 Projects
* 2009 Projects
** Project14
Tags: RightProject
Description: we want this
~~~

He then provides some messy code to perform it. (No offense meant. Mine would've
looked no better.) I'll skip the code, since I couldn't get it to compile as
provided.

Our solution using EMGM follows:

> projDesc :: String -> OrgFileP -> Maybe String
> projDesc name file = do
>   hdg <- G.firstr (headings name file)
>   para <- firstPara hdg
>   if para =~ "Description" then return para else Nothing
>
> headings :: String -> OrgFileP -> [OrgHeadingP]
> headings name = filter check . G.collect
>   where
>     check (OrgHeadingP _ possible _) = name == possible
> 
> firstPara :: OrgHeadingP -> Maybe String
> firstPara hdg = paraStr =<< G.firstr (G.collect hdg)
>   where
>     paraStr (ParagraphP str) = Just str
>     paraStr _                = Nothing

Primarily, we take advantage of the functions `collect` and `firstr`. Here,
[`collect`](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM-Functions-Collect.html#v%3Acollect)
is the key. It's type is `collect :: (Rep (Collect b) a) => a -> [b]`, and it
returns a list of `b`s stored somewhere in a value of type `a`. This allows us
to collect the `OrgHeadingP`s in an `OrgFileP` (`headings`) and the
`OrgFileElementP`s in an `OrgHeadingP` (`firstPara`). Now, we don't have to
build a bunch of functions that break down each of these types to get to their
components.

Our use of
[`firstr`](http://hackage.haskell.org/packages/archive/emgm/0.3.1/doc/html/Generics-EMGM-Functions-Crush.html#v%3Afirstr)
is simply the same as we would use the `Prelude` function `head`, except that
`firstr` returns a `Maybe`: unlike `head`, it's a total function.

David's top-level function would now become this:

> get14 :: OrgFileP -> Maybe String
> get14 = projDesc "Project14"

Well, this was a fun experiment with generic programming. I hope to do more in
the future.

I want to thank David for bringing up this problem in the mailing list. Not only
did I get to play more with EMGM, I also released [an update to the
library](http://hackage.haskell.org/cgi-bin/hackage-scripts/package/emgm-0.3.1)
when I discovered the issue requiring `deriveMany`.
