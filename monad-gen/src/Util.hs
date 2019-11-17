module Util where

import qualified System.IO as IO
import qualified System.Console.ANSI as Console

import Data.Coerce

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce

writeFile' :: FilePath -> [String] -> IO ()
writeFile' filePath content =
  IO.withFile filePath IO.WriteMode $ \h ->
    let loop _ []       = putStrLn ""
        loop i (l:rest) =
          do IO.hPutStrLn h l
             Console.cursorUp 1
             putStrLn $ "Line [" ++ show i ++ "]"
             loop (i+1) rest
    in initialize >> loop (1::Int) content
  where
    initialize =
      do putStrLn $ "Writing " ++ show filePath
         putStrLn "Line [0]"
