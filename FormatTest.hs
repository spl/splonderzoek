{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module FormatTest where

import Format

t1 = sprintf $(fmt "Hello, there!")
-- "Hello, there!"

t2 = sprintf $(fmt "Hello, %s!") "there"
-- "Hello, there!"

t3 = sprintf $(fmt "The value of %s is %d") "x" 3
-- "The value of x is 3"

t3q = sprintf [$fmtq|The value of %s is %i|] "x" 3
-- "The value of x is 3"

-- Mismatch between the formatting string and the printf arguments
-- is a type error.

{-
t4 = sprintf $(fmt "The value of %s is %d") "x" True
-- Couldn't match expected type `Bool' against inferred type `Double'
-}

{-
t5 = $(sprintff "The value of %s is %d") "x" True
-- Couldn't match expected type `Double' against inferred type `Bool'
-}

-- Notice the difference between the errors in t4 and t5. I think the latter
-- makes more sense.

{-
t6 = sprintf $(fmt "The value of %s is %d") "x" 3 10
--  Couldn't match expected type `t1 -> t'
--         against inferred type `[Char]'
--  Probable cause: `sprintf' is applied to too many arguments
-}

{-
t7 = $(sprintff "The value of %s is %d") "x" 3 10
--  Couldn't match expected type `t1 -> t'
--         against inferred type `String'
--  In the first argument of `(Format.literal ['T', 'h', 'e', ' ', ....]
--                           ...
-}

-- Notice the difference between the errors in t6 and t7. The latter is less
-- comprehensible.

t8 = let x = [9,16,25]
	 i = 2
     in sprintf $(fmt "The element number %i of %e is %f") i x (x !! i)
-- "The element number 2 of [9,16,25] is 25"

t9 = let x = [9,16,25]
	 i = 2
     in $(sprintff "The element number %N of %S is %N") i x (x !! i)
-- "The element number 2 of [9,16,25] is 25"

t10 = sprintf $(fmt "The EMGM output of %s is %e") "3" (3 :: Int)
-- "The value in EMGM of x is 3"

t11 = sprintf $(fmt "The SYB output of %s is %y") "3" (3 :: Int)
-- "The value in SYB of x is 3"

