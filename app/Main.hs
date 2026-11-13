module Main (main) where
import Detlog2.Parser
import Detlog2.Interp
import Detlog2.Reference ()
import Detlog2.Prelude
main :: IO ()
main = print (length (progOrder (withPrelude emptyProgram))) >> print (optMaxDepth defaultOptions)
