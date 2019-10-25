{-# OPTIONS --without-K #-}

module Main where

import Homotopy
import FormalTopologySambin
import Poset
import Frame
import Nucleus
import Coverage

-- Proof that the set of downward-closed subsets of a poset forms a frame:
_ = Frame.downward-subset-frame

-- Proof that the set of fixed points of a nucleus forms a frame.
_ = Nucleus.nuclear-fixed-point-frame
