{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module EmacsOrgWithEMGM2 where

import Generics.EMGM.Derive
import Generics.EMGM (collect)

import Data.List (isPrefixOf)
import Data.Maybe (listToMaybe)

type Line = Int
type Column = Int

data FilePosition = FilePosition Line Column

data WithPos a = WithPos { filePos :: FilePosition, innerValue :: a }

data OrgTableP = OrgTableP [WithPos OrgTableRow]

data OrgFileElementP
  = TableP OrgTableP
  | ParagraphP String
  | HeadingP OrgHeadingP

data OrgHeadingP = OrgHeadingP Int String [WithPos OrgFileElementP]

data OrgFileP = OrgFileP [WithPos OrgFileElementP]

data OrgTableRow
  = OrgTableRow [String]
  | OrgTableRowSep 

$(deriveMany 
  [ ''FilePosition
  , ''WithPos
  , ''OrgTableP
  , ''OrgHeadingP
  , ''OrgFileElementP
  , ''OrgFileP
  , ''OrgTableRow
  ])

-- EMGM adaptation of Neil's Uniplate version from:
-- http://neilmitchell.blogspot.com/2009/03/concise-generic-queries.html
projDesc :: String -> OrgFileP -> Maybe String
projDesc name p = listToMaybe [y |
  OrgHeadingP _ x ys <- collect p, name == x,
  ParagraphP y <- collect ys, "Description" `isPrefixOf` y]

