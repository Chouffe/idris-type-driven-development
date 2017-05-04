module ArithState


------------
-- GameState
------------

-- Automatically defines projection functions
-- correct, attempted
record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

-- Automatically defines projection functions
-- score, difficulty
record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
                show (attempted (score st)) ++ "\n" ++
                "Difficulty: " ++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

-- Record update syntax
setDifficulty : Int -> GameState -> GameState
setDifficulty k state = record { difficulty = k } state

-- Nested record update syntax
addWrong : GameState -> GameState
addWrong state = record { score->attempted = attempted (score state) + 1 } state

addCorrect : GameState -> GameState
addCorrect state = record { score->attempted = attempted (score state) + 1
                          , score->correct = correct (score state) + 1
                        } state

-- There is a Lens notation
addWrong' : GameState -> GameState
addWrong' = record { score->attempted $= (+1) }

addCorrect' : GameState -> GameState
addCorrect' = record { score->attempted $= (+1)
                     , score->correct $= (+1)
                     }

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand GetRandom = ?runCommand_rhs_3
runCommand GetGameState = ?runCommand_rhs_4
runCommand (PutGameState x) = ?runCommand_rhs_5
runCommand (Pure x) = pure x
runCommand (Bind x f) = do
  result <- runCommand x
  runCommand $ f result

