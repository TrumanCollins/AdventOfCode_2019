{-# LANGUAGE ScopedTypeVariables #-}

import Data.Char
import Data.List
import Data.Maybe
import Data.Function
import qualified Data.Map as M
import qualified Data.Array.Unboxed as UA
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Unboxed.Mutable as UVM
import qualified Data.Graph.Inductive.Graph as GR
import qualified Data.Graph.Inductive.PatriciaTree as GRPT
import qualified Data.Graph.Inductive.Query.SP as GRSP
import System.IO (hFlush, stdout)
import Control.Monad.ST
import System.Clock
import Text.Printf

-- Helper functions for time calculations.

convertTimeToDouble :: TimeSpec -> Double
convertTimeToDouble tm = fromIntegral (sec tm) + fromIntegral (nsec tm) / 1.0e9

computeElapsedTime :: TimeSpec -> TimeSpec -> Double
computeElapsedTime startTime endTime
  = convertTimeToDouble endTime - convertTimeToDouble startTime

-- Time the computation, then print the answer along with the elapsed time. Check that the result is
-- what it should be, and if not, print an error message showing the answer computed and the
-- expected answer.

computeAndCheck :: IO Int -> Int -> IO String
computeAndCheck solveFn correctAns = do

  -- Time the computation and make sure the calculation is done before the second time is read.

  startTime <- getTime Realtime
  result <- solveFn
  endTime <- result `seq` getTime Realtime

  -- Print and label the result, and left pad the answer so the timings line up.

  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff
      ansStr = show result
      ansPaddedStr = foldl' (\acc _ -> ' ' : acc) ansStr [(length ansStr)..14]
      resultStr = if result == correctAns
                  then ansPaddedStr ++ "  (" ++ diffStr ++ ")"
                  else printf "Error: expected %d, but computed %d." correctAns result
  return resultStr

-- Time the computation, then print the answer along with the elapsed time. Check that the result is
-- what it should be, and if not, print an error message showing the answer computed and the
-- expected answer. This is the version for String output
-- These are currently not used and prefixed by a '_' to avoid a compiler warning.

_computeAndCheckS :: IO String -> String -> IO String
_computeAndCheckS solveFn correctAns = do

  -- Time the computation and make sure the calculation is done before the second time is read.

  startTime <- getTime Realtime
  result <- solveFn
  endTime <- result `seq` getTime Realtime

  -- Print and label the result, and left pad the answer so the timings line up.

  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff
      ansStr = result
      ansPaddedStr = foldl' (\acc _ -> ' ' : acc) ansStr [(length ansStr)..14]
      resultStr = if result == correctAns
                  then ansPaddedStr ++ "  (" ++ diffStr ++ ")"
                  else printf "Error: expected %s, but computed %s." correctAns result
  return resultStr

_computeAndCheckSNoCheck :: IO String -> String -> IO String
_computeAndCheckSNoCheck solveFn _ = do

  -- Time the computation and make sure the calculation is done before the second time is read.

  startTime <- getTime Realtime
  result <- solveFn
  endTime <- result `seq` getTime Realtime

  -- Print and label the result, and left pad the answer so the timings line up.

  let diff = computeElapsedTime startTime endTime
      diffStr = printf "%0.5f sec" diff
      ansStr = result
      ansPaddedStr = foldl' (\acc _ -> ' ' : acc) ansStr [(length ansStr)..14]
      resultStr = ansPaddedStr ++ "  (" ++ diffStr ++ ")"
  return resultStr

-- This function assumes that both lists are sorted, and returns the list where all of the elements
-- of the first list are removed from the second. Either or both lists may be infinite.

removeElementsSorted :: (Eq a, Ord a) => [a] -> [a] -> [a]
removeElementsSorted [] xs = xs
removeElementsSorted _ [] = []
removeElementsSorted allR@(r : rs) allX@(x : xs)
  | r == x = removeElementsSorted rs xs
  | r < x  = removeElementsSorted rs allX
  | otherwise = x : removeElementsSorted allR xs

-- Generate all pairs of an element of digitsLeft and the list of all of the
-- remaining elements.  This algorithm is single-pass and O(n).
-- The order of the remaining list is not sorted.
-- Example: allPairsFirstAndRest [1,2,3,4]
--                        = [(4,[3,2,1]),(3,[2,1,4]),(2,[1,3,4]),(1,[2,3,4])]

allPairsFirstAndRest :: [a] -> [(a, [a])]
allPairsFirstAndRest fullList = aPFARIter fullList [] []
  where
    aPFARIter :: [a] -> [a] -> [(a, [a])] -> [(a, [a])]
    aPFARIter [] _ resultSoFar = resultSoFar
    aPFARIter (d : ds) digitsAlreadyUsed resultSoFar
      = aPFARIter ds (d : digitsAlreadyUsed)
                  ((d, digitsAlreadyUsed ++ ds) : resultSoFar)

-- Split the given string on the given character.

splitOnChar :: Char -> String -> [String]
splitOnChar ch str = case break (== ch) str of
                       (a, _ : b) -> a : splitOnChar ch b
                       (a, _)     -> [a]

-- Read a file of integers and return all of them as a list of Ints. The integers are separated by
-- whitespace or newlines.

readAllIntegersFromFile :: String -> IO [Int]
readAllIntegersFromFile fileName = fmap (map read . words) (readFile fileName)

-- Read comma-separated ints from a file and return an unboxed vector filled with the values. Add
-- zeros at the end to be used for working memory. It doesn't indicate how much is needed, but 1000
-- works for problem 11.

readCSOpcodesFromFileToIntcodeMachine :: String -> IO (UV.Vector Int)
readCSOpcodesFromFileToIntcodeMachine fileName = do
  progCodeList <- fmap (map read . splitOnChar ',') (readFile fileName)
  let intcodeMemory = UV.fromList (progCodeList ++ replicate 1000 0)
  return intcodeMemory

-- Types used for the Intcode computer.

type IntcodeMemState = UV.Vector Int
data StopReasonT = Begin | Input | Halt deriving (Eq, Show)
type InputT  = [Int]
type OutputT = [Int]

-- The record holding the state of the Intcode machine. Note that output is added to the front of
-- the output list, so when reading the output, it should be reversed. Before restarting a run,
-- either clear the output list or re-reverse it.

data IntcodeMachState = IntcodeMachState { memoryState :: IntcodeMemState
                                         , reasonStop  :: StopReasonT
                                         , restartAddr :: Int
                                         , relatAddr   :: Int
                                         , inputList   :: InputT
                                         , outputList  :: OutputT
                                         }
-- Return the output list of the machine state reversing it before the return. This will allow it to
-- be processed in the order the output was generated, but it does not change the value of the
-- output held by the machine state.

outputListRev :: IntcodeMachState -> OutputT
outputListRev = reverse . outputList

-- Create a new Intcode machine given the contents of memory and the inputs.

makeInitIntcodeMachState :: IntcodeMemState -> InputT -> IntcodeMachState
makeInitIntcodeMachState memVec initInput
  = IntcodeMachState { memoryState = memVec, reasonStop = Begin, restartAddr = 0,
                       relatAddr = 0, inputList = initInput, outputList = [] }

-- Execute the program in instruction memory starting from the index given. Before execution, change
-- the values listed in the initChanges list. This modification is a little awkward, but it is used
-- in three problems.

runIntcodeProgram :: IntcodeMachState -> [(Int, Int)] -> IntcodeMachState
runIntcodeProgram (IntcodeMachState compMem _ startAddr relAddr inpt outpt) initChanges = runST $ do
  memVec <- UV.thaw compMem

  -- Change any memory locations needed before starting. Ideally, this would be done before calling
  -- runIntcodeProgram, but it's called for in a few cases, so I put it here.

  mapM_ (uncurry (UVM.write memVec)) initChanges

  -- Run until we hit a halt instruction or need to wait for input. Return the current state.

  runUntilHalt memVec startAddr relAddr inpt outpt

  where

    -- Recursive function to run the interpreter.

    runUntilHalt :: UVM.MVector s Int -> Int -> Int -> InputT -> OutputT -> ST s IntcodeMachState
    runUntilHalt vec currAddr currRelAddr currInput currOutput = do
      instruction <- UVM.read vec currAddr

      -- Get the opcode and the modes of the three parameters.

      let (modes, opcode)  = instruction `quotRem` 100
          (modes23, mode1) = modes `quotRem` 10
          (mode3, mode2)   = modes23 `quotRem` 10

      -- Do what's needed for the opcode we have.

      case opcode of
        1  ->  -- Addition.
          doOpAndContinue vec (+) mode1 mode2 mode3
        2  ->  -- Multiplication.
          doOpAndContinue vec (*) mode1 mode2 mode3
        3  ->  -- Read from input.

          -- If an input is requested and there is something in the input buffer, use it and
          -- continue. If the input buffer is null, then stop and return the current state of the
          -- machine with the restart address at the input opcode so it can be restarted with the
          -- next input.

          if null currInput then do
            frozenMem <- UV.freeze vec
            return (IntcodeMachState frozenMem Input currAddr currRelAddr [] currOutput)
          else do
            let (firstInput : remainingInput) = currInput
            writeValueToParam vec (currAddr + 1) mode1 firstInput
            runUntilHalt vec (currAddr + 2) currRelAddr remainingInput currOutput
        4  -> do  -- Write to output.
          toOutput <- readLiteralOrIndirect vec (currAddr + 1) mode1
          runUntilHalt vec (currAddr + 2) currRelAddr currInput (toOutput : currOutput)
        5  -> doTest0Jump vec (/=) mode1 mode2  -- Jump if true (/= 0).
        6  -> doTest0Jump vec (==) mode1 mode2  -- Jump if false (== 0).
        7  -> doCompare vec (<) mode1 mode2 mode3   -- Store 1 if less than.
        8  -> doCompare vec (==) mode1 mode2 mode3  -- Store 1 if equal.
        9  -> do -- Adjust the relative offset.
          adjustment <- readLiteralOrIndirect vec (currAddr + 1) mode1
          runUntilHalt vec (currAddr + 2) (currRelAddr + adjustment) currInput currOutput
        99 -> do  -- Halt.
          frozenMem <- UV.freeze vec
          return (IntcodeMachState frozenMem Halt (currAddr + 1) currRelAddr currInput currOutput)
        _  -> error ("Bad instruction at index " ++ show currAddr ++ " code: " ++ show instruction)
      where

        -- Read a parameter value from the indexed location. If the mode is 'position' then return
        -- the value in the location referenced by the indexed location, and if it is 'immediate',
        -- then return the value at that location. Error on any other mode.

        readLiteralOrIndirect :: UVM.MVector s Int -> Int -> Int -> ST s Int
        readLiteralOrIndirect vec' addr 0 = do
          srcLoc <- UVM.read vec' addr
          UVM.read vec' srcLoc
        readLiteralOrIndirect vec' addr 1 =
          UVM.read vec' addr
        readLiteralOrIndirect vec' addr 2 = do
          srcLoc <- UVM.read vec' addr
          UVM.read vec' (srcLoc + currRelAddr)
        readLiteralOrIndirect _ addr mode
          = error ("Bad mode (" ++ show mode ++ ") for reading at index " ++ show addr ++ ".")

        -- Write the given value to the location to the location indicated by the value at the
        -- indexed location. Note that only 'position' mode makes sense for writing, so error on
        -- any other mode.

        writeValueToParam :: UVM.MVector s Int -> Int -> Int -> Int -> ST s ()
        writeValueToParam vec' addr 0 value = do
          writeLoc <- UVM.read vec' addr
          UVM.write vec' writeLoc value
        writeValueToParam vec' addr 2 value = do
          writeLoc <- UVM.read vec' addr
          UVM.write vec' (writeLoc + currRelAddr) value
        writeValueToParam _ addr mode value
          = error ("Bad mode (" ++ show mode ++ ") for writing value " ++ show value
                   ++ " at index " ++ show addr ++ ".")

        -- Perform a test on the first operand and if true, jump to the location in the second.

        doTest0Jump :: UVM.MVector s Int -> (Int -> Int -> Bool) -> Int -> Int
                       -> ST s IntcodeMachState
        doTest0Jump vec' testOp mode1' mode2' = do
          testVal <- readLiteralOrIndirect vec' (currAddr + 1) mode1'
          if testOp testVal 0 then do
            jumpAddr <- readLiteralOrIndirect vec' (currAddr + 2) mode2'
            runUntilHalt vec' jumpAddr currRelAddr currInput currOutput
          else
            runUntilHalt vec' (currAddr + 3) currRelAddr currInput currOutput

        -- Compare the first two operands and store a 1 in the third if true, else store 0.

        doCompare :: UVM.MVector s Int -> (Int -> Int -> Bool) -> Int -> Int -> Int
                           -> ST s IntcodeMachState
        doCompare vec' compOp mode1' mode2' mode3' = do
          firstVal  <- readLiteralOrIndirect vec' (currAddr + 1) mode1'
          secondVal <- readLiteralOrIndirect vec' (currAddr + 2) mode2'
          writeValueToParam vec' (currAddr + 3) mode3' (if compOp firstVal secondVal then 1 else 0)
          runUntilHalt vec' (currAddr + 4) currRelAddr currInput currOutput

        -- Perform the given operation on the operands and then call run on the next instruction.

        doOpAndContinue :: UVM.MVector s Int -> (Int -> Int -> Int) -> Int -> Int -> Int
                           -> ST s IntcodeMachState
        doOpAndContinue vec' operator mode1' mode2' mode3' = do
          opend1 <- readLiteralOrIndirect vec' (currAddr + 1) mode1'
          opend2 <- readLiteralOrIndirect vec' (currAddr + 2) mode2'
          writeValueToParam vec' (currAddr + 3) mode3' (operator opend1 opend2)
          runUntilHalt vec' (currAddr + 4) currRelAddr currInput currOutput

-- Just compute the fuel for each weight given in the input file.

puzzle_01a :: IO Int
puzzle_01a = do
  inputNumbers <- readAllIntegersFromFile "puzzle_01.inp"
  let result = (sum . map calcFuel) inputNumbers
  return result
  where
    calcFuel :: Int -> Int
    calcFuel mass = mass `quot` 3 - 2

-- Compute the iterated fuel amounts, starting with the weight of each item, and then iteratively
-- including the weight of the additional fuel.

puzzle_01b :: IO Int
puzzle_01b = do
  inputNumbers <- readAllIntegersFromFile "puzzle_01.inp"
  let result = (sum . map calcFuelIter) inputNumbers
  return result
  where
    calcFuelIter :: Int -> Int
    calcFuelIter = sum . tail . takeWhile (> 0) . iterate calcAdditionalFuel
    calcAdditionalFuel mass = mass `quot` 3 - 2

-- Run the given program after resetting the values in memory locations 1 and 2.

puzzle_02a :: IO Int
puzzle_02a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_02.inp"
  let initMachState = makeInitIntcodeMachState initProgram []
      finalMachState = runIntcodeProgram initMachState [(1, 12), (2, 2)]
      memState = memoryState finalMachState
  return (memState UV.! 0)

-- Run the program with all combinations of [0..99] for memory locations 1 and 2 and return the pair
-- that result in the value 19690720 in memory location 0.

puzzle_02b :: IO Int
puzzle_02b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_02.inp"
  let initMachState = makeInitIntcodeMachState initProgram []
      nounVerbPairsToTry = [[(1, noun), (2, verb)] | noun <- [0..99], verb <- [0..99]]
      allResults  = map (tryNounVerbPair initMachState) nounVerbPairsToTry
      goodNVPairs = filter ((== 19690720) . fst) allResults
      nvResult    = if null goodNVPairs then -1 else (snd . head) goodNVPairs
  return nvResult
  where

    -- Run the program with the given noun and verb and return the result from memory loation 0
    -- along with the combined noun and verb.

    tryNounVerbPair :: IntcodeMachState -> [(Int, Int)] -> (Int, Int)
    tryNounVerbPair machState nounAndVerb = (result, combinedNounAndVerb)
      where
        [(_, noun), (_, verb)] = nounAndVerb
        combinedNounAndVerb    = 100 * noun + verb
        finalMachState = runIntcodeProgram machState nounAndVerb
        memState = memoryState finalMachState
        result = memState UV.! 0

data DirectionT = UpDir | DownDir | LeftDir | RightDir deriving (Eq, Ord, Show)

-- Convert a string like "U256" to (UpDir, 256), with the first character in the
-- set ['U', 'D', 'L', 'R'].

toDirDist :: String -> (DirectionT, Int)
toDirDist str = dist `seq` (dir, dist)
  where
    dirChar = head str
    dir = case dirChar of
      'U' -> UpDir
      'D' -> DownDir
      'L' -> LeftDir
      'R' -> RightDir
      _   -> error "Unknown direction."
    dist = dir `seq` read (tail str)

-- Read in the two move lists from the given file, and generate a map of intersection points keyed
-- on these points with the associated distance the sum of the two shortest paths to that point for
-- each wire.

genIntersectionMap :: String -> IO (M.Map (Int, Int) Int)
genIntersectionMap fileName = do
  [firstPath, secondPath] <- fmap convertToDistPairs (readFile fileName)
  let firstLocMap  = genAllPoints firstPath
      secondLocMap = genAllPoints secondPath

      -- Generate the intersection map that has the sum of the minimum wire paths to the keyed point.

      intersection = M.intersectionWith (+) firstLocMap secondLocMap
  return intersection
  where
    convertToDistPairs = map (map toDirDist . splitOnChar ',') . lines

    -- Generate all points from the current location, given a direction and number o steps. Insert
    -- these all into the map and update the current location and total wire distance.

    genAllPoints :: [(DirectionT, Int)] -> M.Map (Int, Int) Int
    genAllPoints dirList = finalMap
      where
        (_, _, _, finalMap) = foldl' addLineToMap (0, 0, 0, M.empty) dirList

        -- Add all of the locations between the current location and the one we will end up at after
        -- the given jump, to the map along with the wire distance to each of those points.

        addLineToMap (currX, currY, currD, currMap) (dir, dist)
          | dir == UpDir = let newY = currY + dist
                               yRange = [(currY + 1)..newY]
                               newMap = addAllToMap (zip [(currX, y) | y <- yRange]
                                                         furtherWireDistances)
                           in newMap `seq` (currX, newY, newD, newMap)
          | dir == DownDir = let newY = currY - dist
                                 yRange = [(currY - 1),(currY - 2)..newY]
                                 newMap = addAllToMap (zip [(currX, y) | y <- yRange]
                                                           furtherWireDistances)
                             in newMap `seq` (currX, newY, newD, newMap)
          | dir == LeftDir = let newX = currX - dist
                                 xRange = [(currX - 1),(currX - 2)..newX]
                                 newMap = addAllToMap (zip [(x, currY) | x <- xRange]
                                                           furtherWireDistances)
                             in newMap `seq` (newX, currY, newD, newMap)
          | dir == RightDir = let newX = currX + dist
                                  xRange = [(currX + 1)..newX]
                                  newMap = addAllToMap (zip [(x, currY) | x <- xRange]
                                                            furtherWireDistances)
                              in newMap `seq` (newX, currY, newD, newMap)
          | otherwise = error "Unknown direction."
          where

            -- As we move from the current point, the wire distances at each step.

            furtherWireDistances = [(currD+1)..]
            newD = currD + dist

            -- Add all of the elements of the list to the map. Note that the insert will not
            -- overwrite a value associated with the point if it already exists because we want the
            -- minimum wire distance for each point.

            addAllToMap = foldl' (\accMap (loc, dst) -> M.insertWith min loc dst accMap) currMap

-- Use a common routine for this and part 2 of this day's problem, that generates the intersection
-- of the points visited by the first wire and those visited by the second wire. The key is the
-- point, which is all that is needed for this problem, because we just want the closest point to
-- the start measured by Manhattan distance.  Just go through the map, taking the keys and find the
-- minimum distance to return.
-- It is about 10% faster to just use a set to keep track of the points, but then we have to
-- reproduce most of the code between this problem and part 2.

puzzle_03a :: IO Int
puzzle_03a = do
  intersection <- genIntersectionMap "puzzle_03.inp"
  return ((minimum . map (genManhattan . fst)) (M.toList intersection))
  where
    genManhattan (x, y) = abs x + abs y

-- Use a common routine for this and part 1 of this day's problem, that generates the intersection
-- of the points visited by the first wire and those visited by the second wire. The key is the
-- point, and the value is the sum of the shortest path distances to that point for each
-- wire. Return the minimum of these path distances.

puzzle_03b :: IO Int
puzzle_03b = do
  intersection <- genIntersectionMap "puzzle_03.inp"
  return ((minimum . map snd) (M.toList intersection))

-- Convert an int to a list of ints.

intToListOfInts :: Int -> [Int]
intToListOfInts value = intToListOfInts' value []
  where
    intToListOfInts' 0 xs = xs
    intToListOfInts' val xs
      = let (quotient, remainder) = val `quotRem` 10
        in intToListOfInts' quotient (remainder : xs)

-- Returns true if the given number passes the constraints for problem 4. A function is passed in to
-- check whether we are looking for exactly two identical digits in a row (== 2), or two or more
-- identical digits in a row (>= 2). It is used by both parts of this puzzle.

passesConstraints04 :: (Int -> Bool) -> Int -> Bool
passesConstraints04 _ 0 = False
passesConstraints04 compFn value = correctOrder && pairOrMore
  where
    correctOrder   = all (uncurry (<=)) pairedAdjacent
    pairedAdjacent = zip listOfDigits (tail listOfDigits)
    pairOrMore     = (any (compFn . length) . group) listOfDigits
    listOfDigits   = intToListOfInts value

-- For both of these puzzles it's just a matter of testing each number in the range for the
-- constraints, which can be done with the same function for both by passing a comparison function
-- for the number of adjacent identical digits needed to meet the constraint. I believe there is a
-- more efficient way to count these, and that relies on the digits being in >= order. We could
-- start with the 3 in the sixth digit, and generate them going up from there. It would be more
-- difficult, and what I have here only takes about 1 20th of a second, so it didn't seem worth the
-- trouble. A depth-first search could be used to explore the possibilities.

puzzle_04a :: IO Int
puzzle_04a = do
  let inputRange = [372304..847060]
      result = (length . filter (passesConstraints04 (>= 2))) inputRange
  return result

puzzle_04b :: IO Int
puzzle_04b = do
  let inputRange = [372304..847060]
      result = (length . filter (passesConstraints04 (== 2))) inputRange
  return result

-- Enhancement of Intcode interpreter to handle new instructions.

puzzle_05a :: IO Int
puzzle_05a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_05.inp"
  let initMachState = makeInitIntcodeMachState initProgram [1]
      finalMachState = runIntcodeProgram initMachState []
      outputs = reverse $ outputList finalMachState
      output
        | null outputs = -1
        | otherwise = last outputs
  return output

puzzle_05b :: IO Int
puzzle_05b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_05.inp"
  let initMachState = makeInitIntcodeMachState initProgram [5]
      finalMachState = runIntcodeProgram initMachState []
      outputs = reverse $ outputList finalMachState
      output
        | null outputs = -1
        | null (tail outputs) = head outputs
        | otherwise = -1
  return output

-- Get the index associated with a name in the graph. Assume the name exists.

getPlanetInd :: M.Map String Int -> String -> Int
getPlanetInd nameToIndMap x = fromJust $ M.lookup x nameToIndMap

generateGraphForPuzzle06 :: IO (GRPT.Gr String Int, M.Map String Int)
generateGraphForPuzzle06 = do

  -- Read all of the orbit relationships, and convert them to a list of pairs, with the second of
  -- each pair orbiting the first.

  edgePairs <- fmap (map ((\[a, b] -> (a, b)) . splitOnChar ')') . concatMap words . lines)
                    (readFile "puzzle_06.inp")
  let planetNames = (map head . group . sort) (foldr (\(s1, s2) acc -> s1 : s2 : acc) [] edgePairs)

      -- The graph nodes will be the planet names paired with indexes starting wtih 1.

      grNodes = zip [1..] planetNames

      -- These are the edges of the graph. Note that we reverse the nodes for this list. The
      -- orbiting planet points to the orbited planet.

      grEdges = map (\(x, y) -> (getPInd y, getPInd x, 1)) edgePairs

      -- Generate the graph representing all of the orbital relationships.

      planetGraph :: GRPT.Gr String Int
      planetGraph = GR.mkGraph grNodes grEdges

      -- We also create a map from the planet names to the planet indexes, which is used in both
      -- problems.

      nameToIndMap = M.fromList $ map (\(x, y) -> (y, x)) grNodes

      -- Simplifying function to get the planetary index.

      getPInd = getPlanetInd nameToIndMap
  return (planetGraph, nameToIndMap)

-- For both of these problems create a graph from the planetary orbit data and then use that to find
-- the results of both problems.

puzzle_06a :: IO Int
puzzle_06a = do

  -- Generate a directed graph of the planetary orbits for this problem along with a map from planet
  -- name to index.

  (planetGraph, nameToIndMap) <- generateGraphForPuzzle06

  let comIndex = getPlanetInd nameToIndMap "COM"

      -- Compute the distance from each node to COM and then sum them.

      sumOfPaths = (sum . map computeDist) (M.toList nameToIndMap)

      -- Function to compute the distance from the given node to COM, which is one less than the
      -- path length.

      computeDist :: (String, Int) -> Int
      computeDist (str, ind)
        | str == "COM" = 0
        | isNothing pathM = error ("No path from " ++ str ++ " to COM.")
        | otherwise = length path - 1
        where
          path :: [GR.Node]
          path = fromJust pathM
          pathM = GRSP.sp ind comIndex planetGraph

  return sumOfPaths

puzzle_06b :: IO Int
puzzle_06b = do

  -- Generate a directed graph of the planetary orbits for this problem along with a map from planet
  -- name to index.

  (planetGraph, nameToIndMap) <- generateGraphForPuzzle06
  let comIndex = getPlanetInd nameToIndMap "COM"
      sanIndex = getPlanetInd nameToIndMap "SAN"
      youIndex = getPlanetInd nameToIndMap "YOU"

      -- Find the paths to the root body from both SAN and YOU, and reverse them so we can easily
      -- remove the common parts from the root body.

      sanPathR = reverse $ fromJust $ GRSP.sp sanIndex comIndex planetGraph
      youPathR = reverse $ fromJust $ GRSP.sp youIndex comIndex planetGraph
      (sanBranch, youBranch) = dropCommonPrefix sanPathR youPathR

      -- The number of orbital transfers needed is two less than the sum of the lengths of the
      -- non-common parts of the paths from SAN and YOU to the root orbital body.

      orbitalTransfersNeeded = (length sanBranch - 1) + (length youBranch - 1)

  return orbitalTransfersNeeded
  where

    -- Take in two lists and return the remainder of each after dropping any common prefix.

    dropCommonPrefix :: (Eq a) => [a] -> [a] -> ([a], [a])
    dropCommonPrefix [] ys = ([], ys)
    dropCommonPrefix xs [] = (xs, [])
    dropCommonPrefix xss@(x : xs) yss@(y : ys)
      | x == y = dropCommonPrefix xs ys
      | otherwise = (xss, yss)

-- Run the sequence of Amp programs with all permutations of the phases [0..4] and return the
-- largest final value generated by the sequence of Amps.

puzzle_07a :: IO Int
puzzle_07a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_07.inp"
  let initMachState = makeInitIntcodeMachState initProgram []
  return ((maximum . map (runSeriesOfAmps initMachState) . permutations) [0..4])
  where

    -- Run the sequence of amp programs with the given phases and feeding the output signal of each
    -- to the input of the next one. Return the final output signal. The last output to feed to the
    -- first amp is 0.

    runSeriesOfAmps :: IntcodeMachState -> [Int] -> Int
    runSeriesOfAmps initMachState = foldl' runAmp 0
      where
        runAmp lastOutput currPhase = (head . outputListRev) finalMachState
          where
            finalMachState = runIntcodeProgram machineStateWithThisInput []
            machineStateWithThisInput
              = initMachState { inputList = [currPhase, lastOutput], outputList = [] }

-- This one is more complicated than part 1 of this problem. I had to enhance the Intcode
-- interpreter to stop and wait for input, saving the state of the machine. Then I was able to run
-- the amps in a series of loops, saving the state of each until the input signal was available
-- after looping.

puzzle_07b :: IO Int
puzzle_07b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_07.inp"
  let initMachState = makeInitIntcodeMachState initProgram []
  return ((maximum . map (runLoopingSeriesOfAmps initMachState) . permutations) [5..9])
  where

    -- Given this set of phases, run the amp loop until the fifth one in the series halts, then
    -- return the output generated by that last amp.

    runLoopingSeriesOfAmps :: IntcodeMachState -> [Int] -> Int
    runLoopingSeriesOfAmps intcodeMach phases = executeUntilHalt 0 0 initialAmpStates
      where

        -- Generate the initial amp program states to start with, which are the initial program
        -- state to begin execution at index 0 and with the appropriate phase as the initial input.

        initialAmpStates = map (\p -> (intcodeMach { inputList = [p] })) phases

        -- Take the state of the the next amp to execute. If it encountered a halt instruction when
        -- it last executed and it is the last amp in the series, return the current output, and
        -- we're done. Otherwise, execute the current amp program feeding it the signal generated by
        -- the last one executed.

        executeUntilHalt :: Int -> Int -> [IntcodeMachState] -> Int
        executeUntilHalt _ _ [] = error "Null Intcode machines in executeUntilHalt."
        executeUntilHalt currCount currSignal (ics : icss)
          | reasonStop ics == Halt && currCount `rem` 5 == 4 = (head . outputListRev) ics
          | otherwise = executeUntilHalt nextCount nextSignal nextFiveAmps
          where
            nextCount  = currCount + 1
            nextSignal = (head . outputListRev) afterRunState
            nextFiveAmps  = icss ++ [afterRunState]

            -- Get the state of this amp after we add the signal from the last one to its input and
            -- clear its output.

            afterRunState = runIntcodeProgram icsWithSignalFromList []
            icsWithSignalFromList = ics { inputList = newInputList, outputList = [] }
            newInputList = inputList ics ++ [currSignal]

-- Break the full string up into strings of length (25 * 6) for puzzle 8.

breakIntoLayers :: Int -> String -> [String]
breakIntoLayers _ [] = []
breakIntoLayers chunkSize currString = currLayer : breakIntoLayers chunkSize remaining
  where
    (currLayer, remaining) = splitAt chunkSize currString

-- Break the input code up into strings (25 * 6) long. There's no need to break them down further
-- because we don't need to do anything for the rows or columns within a layer. Then count the 0s,
-- 1s, and 2s for each layer and generate the result based on the layer with the fewest 0s. Because
-- of lazy evaluation, we will only count the 1s and 2s on the layer with the fewest zeros.

puzzle_08a :: IO Int
puzzle_08a = do
  codeString <- fmap (concat . lines) (readFile "puzzle_08.inp")
  let layerList = breakIntoLayers (25 * 6) codeString
      layerCounts = map count0s1sAnd2s layerList
      (_, oneCount, twoCount) = minimumBy (compare `on` (\(z, _, _) -> z)) layerCounts
  return (oneCount * twoCount)
  where

    -- Return a tuple containing the number of 0s, 1s, and 2s in the given list.

    count0s1sAnd2s str = (countChars '0' str, countChars '1' str, countChars '2' str)
      where
        countChars chToCount = length . filter (== chToCount)

-- This one wasn't hard, but to get the answer, you had to display the pattern generated by the
-- pixels and visually read it, and the pattern was: 'ZYBLH'. To have a value, I added up the 1s in
-- the resulting layers.

puzzle_08b :: IO Int
puzzle_08b = do
  codeString <- fmap (concat . lines) (readFile "puzzle_08.inp")
  let layerList = breakIntoLayers (25 * 6) codeString
      combinedLayer = combineLayersBasedOnTransparency layerList
      result = (length . filter (== '1')) combinedLayer

      -- These lines convert the resulting layer to six strings that when printed out and lined up
      -- show visually the answer.

      _combinedLayerClear = map _changeColor combinedLayer
      _resultLayerVisual  = breakIntoLayers 25 _combinedLayerClear

  return result
  where

    -- Change the values to it can be printed out and read.

    _changeColor ch
      | ch == '0' = '.'
      | ch == '1' = '#'
      | otherwise = '-'

    -- Combine all of the layers in pairs from the top using the transparency rules.

    combineLayersBasedOnTransparency :: [String] -> String
    combineLayersBasedOnTransparency [] = []
    combineLayersBasedOnTransparency [str] = str
    combineLayersBasedOnTransparency (str1 : str2 : strs)
      = combineLayersBasedOnTransparency (firstTwoCombined : strs)
      where
        firstTwoCombined = zipWith combineChars str1 str2
        combineChars charTop charBot
          | charTop == '0' || charTop == '1' = charTop
          | charBot == '0' || charBot == '1' = charBot
          | otherwise = '2'

-- Additons to the Intcode computer.

puzzle_09a :: IO Int
puzzle_09a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_09.inp"
  let initMachState = makeInitIntcodeMachState initProgram [1]
      finalMachState = runIntcodeProgram initMachState []
      result = (head . outputListRev) finalMachState
  return result

puzzle_09b :: IO Int
puzzle_09b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_09.inp"
  let initMachState = makeInitIntcodeMachState initProgram [2]
      finalMachState = runIntcodeProgram initMachState []
      result = (head . outputListRev) finalMachState
  return result

-- Returns true if the asteroid at (x, y) is visible from (baseX, baseY). The array holds the
-- locations with asteroids, and an asteroid exactly between (baseX, baseY) and (x, y) will result
-- in returning false.

isVisible_10 :: (Int, Int) -> UA.UArray (Int, Int) Bool -> (Int, Int) -> Bool
isVisible_10 (baseX, baseY) asterArray (x, y)
  | baseX == x && baseY == y = False
  | gcdVal == 1 = True
  | otherwise = (not . any (asterArray UA.!)) pointsToCheck
  where
    (diffX, diffY) = (x - baseX, y - baseY)
    (diffXA, diffYA) = (abs diffX, abs diffY)
    (xStep, yStep) = (diffX `div` gcdVal, diffY `div` gcdVal)
    gcdVal = gcd diffXA diffYA

    -- We have to special-case where they are in the same row or column.

    pointsToCheck
      | baseX == x = [(baseX, y1) | y1 <- [(min baseY y + 1)..(max baseY y - 1)]]
      | baseY == y = [(x1, baseY) | x1 <- [(min baseX x + 1)..(max baseX x - 1)]]
      | otherwise = (takeWhile (\(x1, _) -> x1 /= x) . tail
                     . iterate (\(xVal, yVal) -> (xVal + xStep, yVal + yStep)))
                    (baseX, baseY)

-- Walk through the asteroids, and for each walk through the set of asteroids again and determine
-- how many are visible. Use the gcd of the X-Y differences to figure out what points to check to
-- see if there are any asteroids in the way.

puzzle_10a :: IO Int
puzzle_10a = do
  boolLists <- fmap (map (map (== '#')) . lines) (readFile "puzzle_10.inp")
  let (xCount, yCount) = ((length . head) boolLists, length boolLists)
      (maxXInd, maxYInd) = (xCount - 1, yCount - 1)
      initList = zip [(x, y) | y <- [0..maxYInd], x <- [0..maxXInd]] (concat boolLists)
      asteroidList = (map fst . filter snd) initList
      asteroidArray :: UA.UArray (Int, Int) Bool
      asteroidArray = UA.array ((0, 0), (xCount - 1, yCount - 1)) initList
      asteroidVisCounts = map countVisibleAsteroids asteroidList
      maxVisAsteroid = maximumBy (\acc curr -> compare (snd acc) (snd curr)) asteroidVisCounts

      -- Count the number of visible other asteroids from the given asteroid.

      countVisibleAsteroids :: (Int, Int) -> ((Int, Int), Int)
      countVisibleAsteroids (x, y) = ((x, y), visibleCount)
        where
          visibleCount = (length . filter id . map isVisible) asteroidList
          isVisible :: (Int, Int) -> Bool
          isVisible = isVisible_10 (x, y) asteroidArray

  return (snd maxVisAsteroid)

puzzle_10b :: IO Int
puzzle_10b = do
  boolLists <- fmap (map (map (== '#')) . lines) (readFile "puzzle_10.inp")
  let (laserX, laserY) = (19, 11)  -- Use the best monitoring location from the last problem.
      nthToReturn = 200
      (xCount, yCount) = ((length . head) boolLists, length boolLists)
      (maxX, maxY) = (xCount - 1, yCount - 1)
      initList = zipWith remMon [(x, y) | y <- [0..maxY], x <- [0..maxX]] (concat boolLists)
        where
          remMon (x, y) bl = if x == laserX && y == laserY then ((x, y), False) else ((x, y), bl)
      asteroidList = (sort . map fst . filter snd) initList
      asteroidArray :: UA.UArray (Int, Int) Bool
      asteroidArray = UA.array ((0, 0), (xCount - 1, yCount - 1)) initList
      asteroidsVaporizedCWOrder = genAsteroidsRemovedClockwise asteroidList asteroidArray
      (resX, resY) = asteroidsVaporizedCWOrder !! (nthToReturn - 1)

      -- Return an ordered list of the asteroids as they are removed. Use a similar technique to
      -- problem 10a to determine each set removed in a rotation of the laser.

      genAsteroidsRemovedClockwise :: [(Int, Int)] -> UA.UArray (Int, Int) Bool -> [(Int, Int)]
      genAsteroidsRemovedClockwise [] _ = []
      genAsteroidsRemovedClockwise asterList asterArray
        = clockwiseAsteroidsRemoved ++ genAsteroidsRemovedClockwise newAsterList newAsterArray
        where
          clockwiseAsteroidsRemoved = (map snd . sortBy (compare `on` fst))
                                      (zip (map clockwiseRadiansFromVertical visibleAsteroids)
                                           visibleAsteroids)
          newAsterList = removeElementsSorted visibleAsteroids asterList
          newAsterArray = asterArray UA.// zip visibleAsteroids (repeat False)
          visibleAsteroids = filter isVisible asterList
          isVisible :: (Int, Int) -> Bool
          isVisible = isVisible_10 (laserX, laserY) asterArray

      -- Given this point, generate a radian value for this point relative to the location of the
      -- lazer. The range is from [-pi..pi) with -pi being straight up, then progressing clockwise
      -- from there. We need to do some manipulation of the straight arcTangent2 value due to
      -- starting at 90 degrees and because the coordinates are flipped for Y.

      clockwiseRadiansFromVertical :: (Int, Int) -> Double
      clockwiseRadiansFromVertical (x, y) = -moddedVal
        where
          moddedVal = if rawVal > pi then rawVal - 2.0 * pi else rawVal
          rawVal = atanVal + pi / 2.0
          atanVal = atan2 (fromIntegral relY) (fromIntegral relX)

          -- Because the Y-coordinates are flipped in the input, we subtract y from laserY.

          (relX, relY) = (x - laserX, laserY - y)

  return (resX * 100 + resY)

-- Types used by puzzle 11.

data Direction_11  = North | East | South | West deriving (Show, Eq)
data Color_11      = Black | White deriving (Show, Eq, Enum)
data RobotState_11 = RobotState_11 { currLocR    :: (Int, Int)
                                   , currDirR    :: Direction_11
                                   , paintedMapR :: M.Map (Int, Int) Color_11
                                   } deriving (Show)
type FullRobotProgState_11 = (RobotState_11, IntcodeMachState)

-- Generate an initial robot state staring at the origin, facing North, and with no panels painted.

initialRobotState_11 :: RobotState_11
initialRobotState_11 = RobotState_11 { currLocR = (0, 0), currDirR = North, paintedMapR = M.empty }

-- Run the robot, keeping track of the state of the panels, location of the robot, and its
-- direction, until the program halts.

runRobotUntilFinished_11 :: FullRobotProgState_11 -> FullRobotProgState_11
runRobotUntilFinished_11 fullState@(currRobotState, currProgramState)
  | reasonStop currProgramState == Halt = fullState
  | null outputL = (currRobotState, programStateWithOutput)
  | otherwise    = runRobotUntilFinished_11 (robotStateForNextRun, programStateForNextRun)
  where

    -- Clear the output before running the program again.

    programStateForNextRun = programStateWithOutput { outputList = [] }

    -- Create the robot state for the next run of the program. This involves painting the current
    -- panel, turning, and moving forward one step.

    robotStateForNextRun = RobotState_11 newLoc newDir newMap
    newMap = M.insert startLoc (toEnum colorToPaint) startMap
    newDir = turnDir (currDirR currRobotState) turnDirection
    newLoc = advanceOne startLoc newDir

    -- After running the program, see if output was generated, and if so, it will be a color and
    -- turn indication.

    outputL = reverse $ outputList programStateWithOutput
    [colorToPaint, turnDirection] = outputL

    -- Run the program giving it the color under the robot.

    programStateWithOutput = runIntcodeProgram programStateWithInput []
    programStateWithInput = currProgramState { inputList = [fromEnum startColor] }

    -- The location and map from the input robot state.

    startLoc = currLocR currRobotState
    startMap = paintedMapR currRobotState

    -- The color the robot is on top of is either in the map or it is black.

    startColor = fromMaybe Black (M.lookup startLoc startMap)

    -- Turn the robot. Left for 0 and right for 1.

    turnDir :: Direction_11 -> Int -> Direction_11
    turnDir dir turn = case dir of
                         North -> if turn == 0 then West else East
                         East  -> if turn == 0 then North else South
                         South -> if turn == 0 then East else West
                         West  -> if turn == 0 then South else North

    -- Move the robot one step in the given direction.

    advanceOne :: (Int, Int) -> Direction_11 -> (Int, Int)
    advanceOne (x, y) dir = case dir of
                              North -> (x, y + 1)
                              East  -> (x + 1, y)
                              South -> (x, y - 1)
                              West -> (x - 1, y)

-- Load the program, then initialize the robot and run them together, finally returning the number
-- of panels painted.

puzzle_11a :: IO Int
puzzle_11a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_11.inp"
  let initMachState = makeInitIntcodeMachState initProgram []
      initFullState = (initialRobotState_11, initMachState)
      (finalRobotState, _) = runRobotUntilFinished_11 initFullState
  return ((M.size . paintedMapR) finalRobotState)

-- Run the robot as in 11a, but begin with the first panel painted white and then generate the list
-- of message strings that when lined up vertically show the message "PKFPAZRP". To fit into my
-- testing framework, ultimately return the count of the white panels.

puzzle_11b :: IO Int
puzzle_11b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_11.inp"
  let initMachState = makeInitIntcodeMachState initProgram []

      -- Modify the initial robot state by indicating that the panel the robot starts on is already
      -- painted white.

      initialRobotState = initialRobotState_11 { paintedMapR = M.insert (0, 0) White M.empty }
      initFullState = (initialRobotState, initMachState)

      -- Run the robot until it halts, then retain the state of the robot.

      (finalRobotState, _) = runRobotUntilFinished_11 initFullState
      finalColorMap = paintedMapR finalRobotState
      xAndYBounds = M.foldlWithKey' updateMinMax
                      ((maxBound, minBound), (maxBound, minBound)) finalColorMap

      -- If you print out messageStrings and line up the strings vertically you can read the
      -- message.

      messageStrings = genRows finalColorMap xAndYBounds
      countOfWhites = (sum . map (\ch -> if ch == '#' then 1 else 0) . concat) messageStrings
  return countOfWhites
  where

    -- Keep track of the minimum and maximum x and y values.

    updateMinMax :: ((Int, Int), (Int, Int)) -> (Int, Int) -> Color_11 -> ((Int, Int), (Int, Int))
    updateMinMax ((xMin, xMax), (yMin, yMax)) (x, y) _ = ((newXMin, newXMax), (newYMin, newYMax))
      where
        newXMin = if x < xMin then x else xMin
        newXMax = if x > xMax then x else xMax
        newYMin = if y < yMin then y else yMin
        newYMax = if y > yMax then y else yMax

    -- Generate a list of strings representing the panels that have been painted.

    genRows :: M.Map (Int, Int) Color_11 -> ((Int, Int), (Int, Int)) -> [String]
    genRows coordMap ((xMin, xMax), (yMin, yMax)) = foldr genRow [] [yMax,(yMax - 1)..yMin]
      where
        genRow yVal acc = genStringForY coordMap yVal (xMin, xMax) : acc

    -- Generate a string for the coordinates [xMin..xMax] for yVal where a white panel is
    -- represented by '#' and a black panel by ' '.

    genStringForY :: M.Map (Int, Int) Color_11 -> Int -> (Int, Int) -> String
    genStringForY coordMap yVal (xMin, xMax) = foldr whiteOrBlack "" [xMin..xMax]
      where
        whiteOrBlack xVal acc
          | isNothing spaceLookup || (fromJust spaceLookup == Black) = ' ' : acc
          | otherwise = '#' : acc
          where
            spaceLookup = M.lookup (xVal, yVal) coordMap

-- Record definition to hold moon information including position, velocity and energy.

data MoonParams = MoonParams { xPos    :: Int
                             , yPos    :: Int
                             , zPos    :: Int
                             , xVel    :: Int
                             , yVel    :: Int
                             , zVel    :: Int
                             , potEngy :: Int
                             , kinEngy :: Int
                             , totEngy :: Int
                             } deriving (Show, Eq, Ord)

-- Create a moon record given the position, which is what we have at the beginning. All of the other
-- values are set to zero.

moonDataGivenPos :: [Int] -> MoonParams
moonDataGivenPos [] = error "MoonData needs 3 positions."
moonDataGivenPos [_] = error "MoonData needs 3 positions."
moonDataGivenPos [_, _] = error "MoonData needs 3 positions."
moonDataGivenPos [x, y, z] = MoonParams { xPos = x, yPos = y, zPos = z, xVel = 0, yVel = 0,
                                          zVel = 0, potEngy = 0, kinEngy = 0, totEngy = 0 }
moonDataGivenPos _ = error "MoonData needs 3 positions."

-- Given a list of moon records, create the corresponding list of moon records one time step
-- later. This involves updating the velocities, positions, and energy data. Note that making the
-- positions and veloitites strict in the returned record speeds 12b up by a factor of 2.

nextMoonDataList :: [MoonParams] -> [MoonParams]
nextMoonDataList moonList = newMoonList
  where
    newMoonList = (map createUpdatedMoonData . reverse . allPairsFirstAndRest) moonList
    createUpdatedMoonData :: (MoonParams, [MoonParams]) -> MoonParams
    createUpdatedMoonData (currMoon, otherMoons) = newMoonData
      where
        newMoonData = newXPos `seq` newYPos `seq` newZPos `seq`
                      MoonParams { xPos = newXPos, yPos = newYPos, zPos = newZPos,
                                   xVel = newXVel, yVel = newYVel, zVel = newZVel,
                                   potEngy = newPot, kinEngy = newKin, totEngy = newTot }
        newTot  = newPot * newKin
        newPot  = (sum . map abs) [newXPos, newYPos, newZPos]
        newKin  = (sum . map abs) [newXVel, newYVel, newZVel]
        newXPos = newXVel `seq` xPos currMoon + newXVel
        newYPos = newYVel `seq` yPos currMoon + newYVel
        newZPos = newZVel `seq` zPos currMoon + newZVel
        [newXVel, newYVel, newZVel]
          = map (uncurry genVelocity) [(xPos, xVel), (yPos, yVel), (zPos, zVel)] <*> [otherMoons]

        -- Generate new velocity given velocity and position functions.

        genVelocity posFn velFn = foldl' (updateVel posFn) (velFn currMoon)

        -- Update the velocity given the relative position values between the two moons.

        updateVel posFn acc otherMoon
          | currPos > otherPos = acc - 1
          | currPos < otherPos = acc + 1
          | otherwise = acc
          where
            currPos  = posFn currMoon
            otherPos = posFn otherMoon

-- Given the input string for puzzle 12, convert it to a list of moon records.

convertToMoonDataList_12 :: String -> [MoonParams]
convertToMoonDataList_12
  = map (moonDataGivenPos . map read . splitOnChar ',' . filter numbersAndCommas) . lines
  where
    numbersAndCommas :: Char -> Bool
    numbersAndCommas ch
      | isDigit ch || ch == '-' || ch == ',' = True
      | otherwise = False

-- Read the input file into a list of moon records, then iterate time steps and return the total
-- energy for the 1000th iteration.

puzzle_12a :: IO Int
puzzle_12a = do
  moonDataList <- fmap convertToMoonDataList_12 (readFile "puzzle_12.inp")
  let moonDataAtEnd = (!! 1000) (iterate nextMoonDataList moonDataList)
      totalEnergy = (sum . map totEngy) moonDataAtEnd
  return totalEnergy

-- This one was difficult until I understood that the x, y, and z positions and velocities would
-- repeat independently, and by identifying the repeating period length of each, we could find the
-- answer by computing the least common multiple of the three of them.

puzzle_12b :: IO Int
puzzle_12b = do
  moonDataList <- fmap convertToMoonDataList_12 (readFile "puzzle_12.inp")
  let infMoonDataList = iterate nextMoonDataList moonDataList
      startLoopLooking = drop 1 infMoonDataList
      [xRepeatPeriod, yRepeatPeriod, zRepeatPeriod] = map (uncurry calcRepeatPeriodForAxis)
                                                      [(xPos, xVel), (yPos, yVel), (zPos, zVel)]
      repeatingPeriod = foldl' lcm 1 [xRepeatPeriod, yRepeatPeriod, zRepeatPeriod]

      -- Function to calculate the repeating period for axis of the position and velocity passed in.

      calcRepeatPeriodForAxis :: (MoonParams -> Int) -> (MoonParams -> Int) -> Int
      calcRepeatPeriodForAxis posFn velFn = lookForRepeat posFn velFn 1 (tail startLoopLooking)

      -- Take the positions and velocities of the first list of moon records in the infinite series,
      -- then move through the infinite series to get a count of how many steps to match that first
      -- list. This will be the repeat period for this axis.

      lookForRepeat :: (MoonParams -> Int) -> (MoonParams -> Int) -> Int -> [[MoonParams]] -> Int
      lookForRepeat _ _ _ [] = 0
      lookForRepeat posFn velFn startIndex moonDataL = lookLoop startIndex moonDataL
        where

          -- These are the positions and velocities we are going to look for further in the list.

          toMatch = getPosAndVels posFn velFn (head startLoopLooking)

          -- Loop through the remainder of the list until we find a match, then return the count.

          lookLoop :: Int -> [[MoonParams]] -> Int
          lookLoop _ [] = 0
          lookLoop currIndex (currMoonData : remainderMoonList)
            | relevantParts == toMatch = currIndex
            | otherwise = let newIndex = currIndex + 1
                          in  newIndex `seq` lookLoop newIndex remainderMoonList
            where
              relevantParts = getPosAndVels posFn velFn currMoonData

  return repeatingPeriod
  where

    -- Given a position function and a velocity function get the positions and velocities of the
    -- given list of moon records and return them as a list.

    getPosAndVels :: (MoonParams -> Int) -> (MoonParams -> Int) -> [MoonParams] -> [Int]
    getPosAndVels fn1 fn2 = concatMap getTwoVals
      where
        getTwoVals moonData = map (\fn -> fn moonData) [fn1, fn2]

data TileKind = Empty | Wall | Block | HPaddle | Ball deriving (Show, Eq, Enum)
type TileMap = M.Map (Int, Int) TileKind
data TileMapScore = TileMapScore { boardMap :: TileMap
                                 , score    :: Int
                                 }
initialTileMapScore :: TileMapScore
initialTileMapScore = TileMapScore { boardMap = M.empty, score = 0 }

recordTile :: TileMapScore -> (Int, Int, Int) -> TileMapScore
recordTile inputMap (x, y, thing)
  | x == -1 && y == 0 = inputMap { score = thing }
  | otherwise = inputMap { boardMap = M.insert (x, y) (toEnum thing) (boardMap inputMap) }

-- Update the TileMapScore with a series of drawn tiles.

updateTileMapScore :: TileMapScore -> [Int] -> TileMapScore
updateTileMapScore inputMapScore tilesDrawn = outputMapScore
  where
    outputMapScore = foldl' recordTile inputMapScore (breakIntoTriples_13 tilesDrawn)

-- Break the list of ints into (x, y, object) triplets. Print an error for not divisible by 3.

breakIntoTriples_13 :: [Int] -> [(Int, Int, Int)]
breakIntoTriples_13 [] = []
breakIntoTriples_13 [_] = error "Tile input count not divisible by 3."
breakIntoTriples_13 [_, _] = error "Tile input count not divisible by 3."
breakIntoTriples_13 (x : y : thing : remainder) = (x, y, thing) : breakIntoTriples_13 remainder

-- Count the number of block tiles in the given TileMapScore map. Also return the x coordinates of
-- the ball and paddle.

blockCountBallAndPaddle_13 :: TileMapScore -> (Int, Int, Int)
blockCountBallAndPaddle_13 mapScore = M.foldlWithKey' accFn (0, 0, 0) (boardMap mapScore)
  where
    accFn acc@(blocks, ballX, paddleX) (x, _) tile
      | tile == Block   = let newBlocks = blocks + 1
                          in newBlocks `seq` (newBlocks, ballX, paddleX)
      | tile == Ball    = (blocks, x, paddleX)
      | tile == HPaddle = (blocks, ballX, x)
      | otherwise       = acc

-- Load the program, run it, and put the output into a map keyed off the X and Y coordinates with
-- the tile contents the data in the map. Count the blocks.

puzzle_13a :: IO Int
puzzle_13a = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_13.inp"
  let initMachState  = makeInitIntcodeMachState initProgram []
      finalMachState = runIntcodeProgram initMachState []
      tilesDrawn     = outputListRev finalMachState
      finalMapScore  = updateTileMapScore initialTileMapScore tilesDrawn
      (blkCnt, _, _) = blockCountBallAndPaddle_13 finalMapScore
  return blkCnt

-- Load the program and run to create the map with the initial position. Iterate moving until there
-- are no blocks left in the map, moving the paddle in the direction of the ball at each step.

puzzle_13b :: IO Int
puzzle_13b = do
  initProgram <- readCSOpcodesFromFileToIntcodeMachine "puzzle_13.inp"
  let initMachState  = makeInitIntcodeMachState initProgram []
      readyMachState = runIntcodeProgram initMachState [(0, 2)]
      tilesDrawn     = outputListRev readyMachState
      readyMapScore  = updateTileMapScore initialTileMapScore tilesDrawn
      finalScore     = playUntilNoBlocksLeft readyMachState readyMapScore
  return finalScore
  where

    -- Take in the machine state and state of the game board and iterate moving the paddle
    -- horizontally toward the ball at each step. Do this until there are no more blocks left, then
    -- return the score.

    playUntilNoBlocksLeft :: IntcodeMachState -> TileMapScore -> Int
    playUntilNoBlocksLeft currMachState currMapScore
      | blockCount == 0 = score currMapScore
      | otherwise = playUntilNoBlocksLeft newMachState newMapScore
      where
        (blockCount, ballX, paddleX) = blockCountBallAndPaddle_13 currMapScore
        newMapScore  = updateTileMapScore currMapScore tilesDrawn
        tilesDrawn   = outputListRev newMachState
        newMachState = runIntcodeProgram machStateToRun []
          where
            machStateToRun = currMachState { inputList = [currJS], outputList = [] }
            currJS
              | ballX < paddleX = -1
              | ballX > paddleX = 1
              | otherwise = 0

type ChemicalUnitPair = (String, Int)
type ChemicalRecipe = (ChemicalUnitPair, [ChemicalUnitPair])

-- Sort a lit of ChemicalUnitPairs.

sortChemUnitPairs_14 :: [ChemicalUnitPair] -> [ChemicalUnitPair]
sortChemUnitPairs_14 = sortBy (compare `on` fst)

-- Take in a list of (name, quantity) pairs, remove any where the quantity is zero, sort based on
-- the chemical name, and combine the quantities of any duplicate chemical entries.

sortGroupAndCombineChemUnitPairs_14 :: [ChemicalUnitPair] -> [ChemicalUnitPair]
sortGroupAndCombineChemUnitPairs_14
  = map sumQuants . groupBy ((==) `on` fst) . sortChemUnitPairs_14 . filter ((/= 0) . snd)
  where
    sumQuants :: [ChemicalUnitPair] -> ChemicalUnitPair
    sumQuants [] = error "Empty list in sumQuants."
    sumQuants ((fstName, fstQuant) : rest) = (fstName, sum (fstQuant : map snd rest))

-- Convert an input line to a list of pairs holding the name of the compound and number of
-- units. The list of goal chemicals will be in alphabetical order, as will each list of ingredient
-- chemicals.

convertToPairs_14 :: String -> ChemicalRecipe
convertToPairs_14 = sepResult . reverse . pairUp . filter (/= "=>") . words . filter (/= ',')
  where
    pairUp :: [String] -> [ChemicalUnitPair]
    pairUp [] = []
    pairUp [_] = error "Odd number of input strings."
    pairUp (countStr : nameStr : remainder) = (nameStr, read countStr) : pairUp remainder
    sepResult :: [ChemicalUnitPair] -> ChemicalRecipe
    sepResult chemPairList
      | isJust headTailMaybe = (goalChem, sortChemUnitPairs_14 ingredientChems)
      | otherwise = error "Empty recipe."
      where
        (goalChem, ingredientChems) = fromJust headTailMaybe
        headTailMaybe = uncons chemPairList

-- Recursive function that will take in a list of needed chemicals and their quantities, and
-- will use the possible reactions given to work back down, step by step, to the amount of ore
-- needed. The lists are kept sorted and we keep a list of extra amounts of each chemical where
-- there was some left over from a prior reaction and use those before breaking them down to
-- components again.

genNeededOre :: [ChemicalRecipe] -> [ChemicalUnitPair] -> [ChemicalUnitPair] -> Int
genNeededOre _ [] _ = error "Something must be needed."
genNeededOre _ [("ORE", quantity)] _ = quantity
genNeededOre recipesS neededS extraS = genNeededOre recipesS newNeededS newExtraS
  where

    -- Use any extras we have of needed chemicals, and return the resulting needs and the unused
    -- extras.

    (newNeededS, newExtraS) = useAnyExtrasWeCan initialNewNeeds allExtras

    -- All the initial new needs from breaking down the input needs to their components.

    initialNewNeeds = sortGroupAndCombineChemUnitPairs_14 newNeededRaw
      where newNeededRaw = concatMap fst newNeedsAndExtras

    -- All the extras we came in with plus any created generating the needs.

    allExtras = sortGroupAndCombineChemUnitPairs_14 (extraS ++ newExtras)
      where newExtras = map snd newNeedsAndExtras

    newNeedsAndExtras = genNewNeeds neededS recipesS

    -- Go through the list of needed chemicals and generate the chemicals and their amounts needed
    -- to create them. Because we have to make each chemical through reactions with integer
    -- proportions, we may have extra amounts, and keep track of any extra associated with each
    -- reaction. The quantity will be zero when there is none left over, and these will be filtered
    -- out later. We leave ore alone, as it can't be broken down.  Note that these lists are sorted,
    -- so we can walk them together.

    genNewNeeds :: [ChemicalUnitPair] -> [ChemicalRecipe]
                   -> [([ChemicalUnitPair], ChemicalUnitPair)]
    genNewNeeds [] _ = []
    genNewNeeds _ [] = error "Empty recipes before empty needs."
    genNewNeeds needs@(needHead@(needName, needQuant) : needRest)
                recipes@(((recipeName, recipeQuant), recipeIngred) : recipeRest)

      -- Skip an ore entry since there is nothing to decompose it into. Also, make the extra of it
      -- have zero quantity, which will be filtered out later.

      | needName == "ORE" = ([needHead], (needName, 0)) : genNewNeeds needRest recipes

      -- If we don't need this recipe, move on.

      | needName > recipeName = genNewNeeds needs recipeRest

      -- This should never happen because there will be a recipe for each chemical.

      | needName < recipeName = error "Need not an element of recipes."

      -- Figure out how many copies of the reaction are needed to generate the amount of the target
      -- needed, and possibly more. If more, put the extra quantity in the extra field.

      | otherwise = (map (\(nm, quant) -> (nm, quant * recipeFactor)) recipeIngred,
                           (needName, extraQ)) : genNewNeeds needRest recipeRest
      where

        -- Figure out how many units of the reaction we need (recipeFactor), and the quantity extra
        -- of the resulting chemical.

        (recipeFactor, extraQ) = if r == 0 then (q, 0) else (q + 1, recipeQuant - r)
        (q, r) = quotRem needQuant recipeQuant

    -- Take in a list of needed chemicals generated in this call as well as the extras, both of
    -- which lists are in sorted order by chemical name. Apply any extra quantities of chemicals to
    -- the needs. Return both updated lists. We have to consider, as we're walking through the
    -- lists, skipping over entries in one or the other, and then when we find a match, whether the
    -- quantities are equal, or if not, which is larger, and how to handle each.

    useAnyExtrasWeCan :: [ChemicalUnitPair] -> [ChemicalUnitPair]
                         -> ([ChemicalUnitPair], [ChemicalUnitPair])
    useAnyExtrasWeCan [] extras = ([], extras)
    useAnyExtrasWeCan needed [] = (needed, [])
    useAnyExtrasWeCan needs@((needNm, needQuant) : needRest)
                      extras@((extraNm, extraQuant) : extraRest)
      | needNm < extraNm = let (deeperNeeds, deeperExtras) = useAnyExtrasWeCan needRest extras
                           in ((needNm, needQuant) : deeperNeeds, deeperExtras)
      | needNm > extraNm = let (deeperNeeds, deeperExtras) = useAnyExtrasWeCan needs extraRest
                           in (deeperNeeds, (extraNm, extraQuant) : deeperExtras)
      | needQuant > extraQuant
        = ((needNm, needQuant - extraQuant) : deeperNeedsFromRest, deeperExtrasFromRest)
      | needQuant < extraQuant
        = (deeperNeedsFromRest, (extraNm, extraQuant - needQuant) : deeperExtrasFromRest)
      | otherwise = (deeperNeedsFromRest, deeperExtrasFromRest)
      where
        (deeperNeedsFromRest, deeperExtrasFromRest) = useAnyExtrasWeCan needRest extraRest

-- This works well and quickly for the full input and all of the examples. I keep the lists sorted
-- by chemical name, and that works fine, but I wonder if there may be cases where a an extra is
-- generated too late to use because of the alphabetical ordering. Perhaps they should be ordered
-- topologically.

puzzle_14a :: IO Int
puzzle_14a = do
  recipes <- fmap (sortBy (compare `on` (fst . fst)) . map convertToPairs_14 . lines)
                  (readFile "puzzle_14.inp")
  let oreNeeded = genNeededOre recipes [("FUEL", 1)] []
  return oreNeeded

-- Because of the use of extra chemical ingredients, multiplying the amount of fuel wanted by n
-- doesn't necessarily multiply the amount of ore by n. It can and often is less. Use a binary
-- search to find the amount of fuel that needs closest to 1 trillion ore units.

puzzle_14b :: IO Int
puzzle_14b = do
  recipes <- fmap (sortBy (compare `on` (fst . fst)) . map convertToPairs_14 . lines)
                  (readFile "puzzle_14.inp")
  let oreNeeded1Fuel = genNeededOre recipes [("FUEL", 1)] []
      lowEst  = targetOre `div` oreNeeded1Fuel
      highEst = lowEst * 2
      maxFuelForTargetOre = binarySearchOre recipes (lowEst, highEst)
  return maxFuelForTargetOre
  where
    targetOre = 1000000000000
    binarySearchOre recipes (low, high)
      | mid == low || mid == high = low
      | midOre >= targetOre = binarySearchOre recipes (low, mid)
      | otherwise = binarySearchOre recipes (mid, high)
      where
        midOre = genNeededOre recipes [("FUEL", mid)] []
        mid = (low + high) `div` 2

-- Compute the value associated with the given puzzle, check for the correct answer, then print the
-- result.

computeCheckAndPrint :: IO Int -> String -> Int -> IO ()
computeCheckAndPrint puzzleFn puzzleName correctAns = do
  result <- computeAndCheck puzzleFn correctAns
  putStrLn $ mconcat ["Result ", puzzleName, ": ", result]
  hFlush stdout

-- Compute the value associated with the given puzzle, check for the correct answer, then print the
-- result. This is the version for String output.
-- These are currently not used and prefixed by a '_' to avoid a compiler warning.

_computeCheckAndPrintS :: IO String -> String -> String -> IO ()
_computeCheckAndPrintS puzzleFn puzzleName correctAns = do
  result <- _computeAndCheckS puzzleFn correctAns
  putStrLn $ mconcat ["Result ", puzzleName, ": ", result]
  hFlush stdout

_computeCheckAndPrintSNoCheck :: IO String -> String -> String -> IO ()
_computeCheckAndPrintSNoCheck puzzleFn puzzleName correctAns = do
  result <- _computeAndCheckSNoCheck puzzleFn correctAns
  putStrLn $ mconcat ["Result ", puzzleName, ": ", result]
  hFlush stdout

main :: IO ()
main = do

  -- Generate the results for each problem and check for the expected answer. The result will
  -- contain not only the result, but the time taken to compute it.

  computeCheckAndPrint puzzle_01a "01a" 3388015
  computeCheckAndPrint puzzle_01b "01b" 5079140
  computeCheckAndPrint puzzle_02a "02a" 3101878
  computeCheckAndPrint puzzle_02b "02b" 8444
  computeCheckAndPrint puzzle_03a "03a" 258
  computeCheckAndPrint puzzle_03b "03b" 12304
  computeCheckAndPrint puzzle_04a "04a" 475
  computeCheckAndPrint puzzle_04b "04b" 297
  computeCheckAndPrint puzzle_05a "05a" 5821753
  computeCheckAndPrint puzzle_05b "05b" 11956381
  computeCheckAndPrint puzzle_06a "06a" 271151
  computeCheckAndPrint puzzle_06b "06b" 388
  computeCheckAndPrint puzzle_07a "07a" 21760
  computeCheckAndPrint puzzle_07b "07b" 69816958
  computeCheckAndPrint puzzle_08a "08a" 2480
  computeCheckAndPrint puzzle_08b "08b" 59
  computeCheckAndPrint puzzle_09a "09a" 3345854957
  computeCheckAndPrint puzzle_09b "09b" 68938
  computeCheckAndPrint puzzle_10a "10a" 230
  computeCheckAndPrint puzzle_10b "10b" 1205
  computeCheckAndPrint puzzle_11a "11a" 2238
  computeCheckAndPrint puzzle_11b "11b" 99
  computeCheckAndPrint puzzle_12a "12a" 13500
  computeCheckAndPrint puzzle_12b "12b" 278013787106916
  computeCheckAndPrint puzzle_13a "13a" 286
  computeCheckAndPrint puzzle_13b "13b" 14538
  computeCheckAndPrint puzzle_14a "14a" 483766
  computeCheckAndPrint puzzle_14b "14b" 3061522
