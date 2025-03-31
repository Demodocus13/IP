{-# LANGUAGE LambdaCase #-}
import Data.Char (isAlpha, isAlphaNum, isSpace)
import Control.Monad (foldM, mplus)
import Data.List (intercalate)
import System.IO (hFlush, stdout)
import Data.Either (rights)

-- 命题公式的数据类型
data Formula = 
    Var String | And Formula Formula | Or Formula Formula 
    | Impl Formula Formula | Not Formula | Top | Bottom
    deriving (Eq)

-- 公式的 `Show` 实例
instance Show Formula where
    show :: Formula -> String
    show = \case
        Var x -> x
        And p q -> "(" ++ show p ++ " ∧ " ++ show q ++ ")"
        Or p q -> "(" ++ show p ++ " ∨ " ++ show q ++ ")"
        Impl p q -> "(" ++ show p ++ " → " ++ show q ++ ")"
        Not p -> "¬" ++ show p
        Top -> "⊤"
        Bottom -> "⊥"

-- 证明环境
data ProofContext = ProofContext {
    assumptions :: [Formula],  
    goal :: Formula,  
    proofSteps :: [(String, Formula)]  
} deriving (Show)

-- 证明规则
data ProofRule = AndIntro | AndElim1 | AndElim2  
               | OrIntro1 | OrIntro2 | OrElim  
               | ImplIntro | ImplElim  
               | NotIntro | NotElim  
               | Assumption  
               deriving (Show, Eq)

-- 解析公式
parseFormula :: String -> Maybe Formula
parseFormula input = parseFormulaHelper $ tokenize $ filter (`notElem` "()") input

-- 将输入字符串分割成标记
tokenize :: String -> [String]
tokenize [] = []
tokenize s = case break isSpace s of
    (token, rest) -> if null token 
                     then tokenize (dropWhile isSpace rest)
                     else token : tokenize (dropWhile isSpace rest)

-- 解析公式辅助函数
parseFormulaHelper :: [String] -> Maybe Formula
parseFormulaHelper tokens = case tokens of
    [] -> Nothing
    [x] | x == "⊤" || x == "top" -> Just Top
        | x == "⊥" || x == "bottom" -> Just Bottom
        | isValidVar x -> Just (Var x)
        | otherwise -> Nothing
    "not":rest -> Not <$> parseFormulaHelper rest
    xs -> do
        let (left, rest1) = break (`elem` ["impl"]) xs
        case rest1 of
            "impl":right -> do
                l <- parseAndOr left
                r <- parseFormulaHelper right
                return $ Impl l r
            _ -> parseAndOr xs
  where
    isValidVar (x:xs) = isAlpha x && all isAlphaNum xs
    isValidVar _ = False
    
    parseAndOr :: [String] -> Maybe Formula
    parseAndOr tokens = case break (`elem` ["and", "or"]) tokens of
        ([], _) -> Nothing
        ([x], []) -> if isValidVar x then Just (Var x) else Nothing
        (left, op:right) -> do
            l <- parseFormulaHelper left
            r <- parseFormulaHelper right
            case op of
                "and" -> Just (And l r)
                "or" -> Just (Or l r)
                _ -> Nothing
        (left, []) -> parseFormulaHelper left

-- 验证证明规则
validateProof :: ProofContext -> ProofRule -> [Formula] -> Maybe Formula
validateProof ctx = \case
    AndIntro -> \case
        [p, q] | all (`elem` assumptions ctx) [p, q] -> Just (And p q)
        _ -> Nothing
    AndElim1 -> \case
        [And p q] | And p q `elem` assumptions ctx -> Just p
        _ -> Nothing
    AndElim2 -> \case
        [And p q] | And p q `elem` assumptions ctx -> Just q
        _ -> Nothing
    ImplIntro -> \case
        [p] -> case goal ctx of
            Impl p' q | p == p' -> Just (Impl p q)
            _ -> Nothing
        _ -> Nothing
    ImplElim -> \case
        [Impl p q, p'] | all (`elem` assumptions ctx) [Impl p q, p'] && p == p' -> Just q
        _ -> Nothing
    OrIntro1 -> \case
        [p] | p `elem` assumptions ctx -> case goal ctx of
            Or p' _ | p == p' -> Just (Or p p')
            _ -> Nothing
        _ -> Nothing
    OrIntro2 -> \case
        [q] | q `elem` assumptions ctx -> case goal ctx of
            Or _ q' | q == q' -> Just (Or q q')
            _ -> Nothing
        _ -> Nothing
    NotIntro -> \case
        [p] | Bottom `elem` assumptions ctx -> Just (Not p)
        _ -> Nothing
    NotElim -> \case
        [p, Not p'] | all (`elem` assumptions ctx) [p, Not p'] && p == p' -> Just Bottom
        [Not p, p'] | all (`elem` assumptions ctx) [Not p, p'] && p == p' -> Just Bottom
        _ -> Nothing
    _ -> const Nothing

-- 搜索证明
searchProof :: ProofContext -> Int -> Maybe ProofContext
searchProof ctx depth
    | depth > 50 = Nothing  -- 增加搜索深度到50
    | goal ctx `elem` assumptions ctx = Just ctx
    | otherwise = 
        let rules = [AndElim1, AndElim2, ImplElim, OrIntro1, OrIntro2, ImplIntro, AndIntro, NotElim, NotIntro]
            -- 尝试基本定理的证明
            tryBasicTheorem = Nothing
            -- 尝试应用规则
            tryRule rule = 
                let attempts = [ result 
                             | premises <- generatePremises ctx rule
                             , Right newCtx <- [applyRule ctx rule premises]
                             , not (containsLoop (proofSteps newCtx))
                             , not (hasRedundantStep newCtx)
                             , Just result <- [searchProof newCtx (depth + 1)]
                             ]
                in case attempts of
                    (result:_) -> Just result
                    [] -> Nothing
        in tryBasicTheorem `mplus` foldr (\rule acc -> acc `mplus` tryRule rule) Nothing rules

-- 检查证明步骤中是否存在循环
containsLoop :: [(String, Formula)] -> Bool
containsLoop steps = 
    let formulas = map snd steps
    in length (filter (`elem` formulas) formulas) > length formulas

-- 检查是否有冗余步骤
hasRedundantStep :: ProofContext -> Bool
hasRedundantStep ctx =
    let steps = map snd (proofSteps ctx)

        uniqueSteps = filter (`notElem` assumptions ctx) steps
    in length steps > length uniqueSteps + 12 

-- 应用证明规则
applyRule :: ProofContext -> ProofRule -> [Formula] -> Either String ProofContext
applyRule ctx rule premises = case validateProof ctx rule premises of
    Just conclusion -> Right $ ctx {
        proofSteps = (show rule, conclusion) : proofSteps ctx,
        assumptions = case rule of
            ImplIntro -> premises ++ assumptions ctx
            _ -> if conclusion `elem` assumptions ctx 
                 then assumptions ctx 
                 else conclusion : assumptions ctx,
        goal = case rule of
            ImplIntro -> case goal ctx of
                Impl _ q -> q
                _ -> goal ctx
            _ -> goal ctx
    }
    Nothing -> Left $ "规则 " ++ show rule ++ " 应用失败"

-- 生成可能的前提
generatePremises :: ProofContext -> ProofRule -> [[Formula]]
generatePremises ctx rule = case rule of
    ImplIntro -> case goal ctx of
        Impl p q -> [[p]]
        _ -> []
    AndIntro -> case goal ctx of
        And p q -> if p == q
                  then [[p, p] | p `elem` assumptions ctx]  -- 特殊处理 p ∧ p 的情况
                  else [[p, q] | p `elem` assumptions ctx, q `elem` assumptions ctx]
        _ -> []
    AndElim1 -> [[p] | p@(And _ _) <- assumptions ctx, fst (fromAnd p) `notElem` assumptions ctx]
    AndElim2 -> [[p] | p@(And _ _) <- assumptions ctx, snd (fromAnd p) `notElem` assumptions ctx]
    ImplElim -> [[Impl p q, p] | Impl p q <- assumptions ctx, (q == goal ctx || any (\(Impl a b) -> a == q) (assumptions ctx)), p <- assumptions ctx]
    OrIntro1 -> case goal ctx of
        Or p q | p == q -> [[p] | p `elem` assumptions ctx]  
        Or p _ -> [[p] | p `elem` assumptions ctx]
        _ -> []
    OrIntro2 -> case goal ctx of
        Or p q | p == q -> [[q] | q `elem` assumptions ctx]  
        Or _ q -> [[q] | q `elem` assumptions ctx]
        _ -> []
    NotIntro -> case goal ctx of
        Not p -> [[p] | Bottom `elem` assumptions ctx]
        _ -> []
    NotElim -> [[p, Not p] | p <- assumptions ctx, Not p <- assumptions ctx]
    _ -> []

-- 辅助函数：从合取公式中提取两个子公式
fromAnd :: Formula -> (Formula, Formula)
fromAnd (And p q) = (p, q)
fromAnd _ = error "不是合取公式"

-- 自动证明函数
proveTheorem :: Formula -> [Formula] -> Maybe [(String, Formula)]
proveTheorem goal assumptions = do
    ctx <- searchProof (ProofContext assumptions goal []) 0
    return $ reverse (proofSteps ctx)

-- 交互式主循环
main :: IO ()
main = do
    putStrLn "直觉主义命题逻辑自动证明器"
    putStrLn "输入 exit 退出程序"
    proveLoop

proveLoop :: IO ()
proveLoop = do
    putStr "> "
    hFlush stdout
    formula <- getLine
    case formula of
        "exit" -> putStrLn "再见！"
        "" -> proveLoop
        _ -> do
            case parseFormula formula of
                Just goal -> do
                    putStrLn $ "尝试证明：" ++ show goal
                    case proveTheorem goal [] of
                        Just steps -> do
                            putStrLn "找到证明！"
                            putStrLn "证明步骤："
                            mapM_ (\(rule, formula) -> 
                                putStrLn $ "  " ++ padRight 12 rule ++ "⊢  " ++ show formula) steps
                            putStrLn "证明完成。"
                        Nothing -> 
                            putStrLn "未能找到证明，这个定理可能在直觉主义逻辑中不可证，或者需要额外的假设。"
                Nothing -> 
                    putStrLn "公式语法错误，示例：p and q impl q and p"
            putStrLn ""
            proveLoop
  where
    padRight n str = str ++ replicate (n - length str) ' '