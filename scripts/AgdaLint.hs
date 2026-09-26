#!/usr/bin/env cabal
{- cabal:
build-depends:
  , base                  >=4.20
  , containers            >=0.7
  , directory             >=1.3.8
  , filepath              >=1.5
  , generic-data          >=1.1
  , Glob                  >=0.10
  , megaparsec            >=9.7
  , optparse-generic      >=1.5
  , text                  >=2.1.2
  , toml-parser           >=2.0
default-language: GHC2024
default-extensions: DuplicateRecordFields, OverloadedStrings
ghc-options: -O1 -Wall -Wextra -Wcompat
-}
{- project:
index-state: 2026-09-26T00:00:00Z
-}

-- agda style linter

module Main (main) where

import           Control.Monad              (forM, forM_, guard, unless, void,
                                             when)
import           Data.Char                  (chr, digitToInt, isAlphaNum,
                                             isDigit, isLetter, isLower,
                                             isSpace, isUpper, ord, toLower)
import           Data.Foldable              (toList)
import           Data.Containers.ListUtils  (nubOrd)
import qualified Data.Graph                 as Graph
import           Data.Ix                    (inRange)
import           Data.List                  (find, isPrefixOf, mapAccumL,
                                             sortOn, unsnoc)
import qualified Data.List                  as List
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Bifunctor             (first)
import           Data.Maybe                 (catMaybes, fromMaybe, isJust,
                                             listToMaybe, mapMaybe)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.Text                  (Text)
import qualified Data.Text                  as T
import qualified Data.Text.IO               as TIO
import qualified Data.Text.Read             as TR
import           Options.Generic            (ParseRecord, Wrapped,
                                             unwrapRecord, type (:::),
                                             type (<?>))
import           Data.Void                  (Void)
import           System.Directory           (doesFileExist, getCurrentDirectory)
import           Generic.Data                (Constructors, gconName)
import           System.Environment         (withProgName)
import           System.Exit                (ExitCode (..), exitSuccess,
                                             exitWith)
import           System.FilePath            (makeRelative, takeFileName, (</>))
import qualified System.FilePath.Glob       as Glob
import           System.IO                  (hPutStrLn, stderr)
import           Text.Megaparsec            hiding (Pos, State, Token, match)
import qualified Text.Megaparsec            as MP
import           Text.Megaparsec.Char       (char, newline, string)
import qualified Text.Megaparsec.Char.Lexer as L
import           GHC.Generics               (Generic)
import qualified Toml
import           Toml.Schema                (FromValue (..), Matcher,
                                             Value' (..), failAt,
                                             genericFromTable)

------------------------------------------------------------------------
-- rules

data Level = Error | Warning | Off
  deriving (Eq, Ord, Show, Enum, Bounded, Generic)

data RuleId
  = AsciiArrow
  | AsciiLambda
  | PatternLambda
  | AsciiSubscript
  | Prime
  | PrefixType
  | BannedName
  | SortLetter
  | ReservedLetter
  | UnneededSubscript
  | PairSubscript
  | UnusedVariable
  | LineLength
  | TrailingWhitespace
  | Tab
  | LeadingArrow
  | ModuleBlankLine
  | ImportOrder
  | ImportPublic
  | ImportModifierOrder
  | MutualBlock
  | LetBinding
  | TrailingComment
  | SectionHeader
  | WithAlignment
  | UnicodeInstance
  | AsciiPrime
  | MissingFixity
  | BeginSameLine
  | WhereLayout
  | StackedPrivate
  | BotElim
  deriving (Eq, Ord, Enum, Bounded, Show, Generic)

data Rule = Rule
  { ruleId      :: RuleId
  , ruleDefault :: Level
  , ruleSummary :: Text
  , ruleCheck   :: Context -> SourceFile -> [Finding]
  }

-- camelCase constructor name
camelName :: Constructors a => a -> Text
camelName x = case gconName x of
  c : cs -> T.pack (toLower c : cs)
  []     -> ""

ruleName :: RuleId -> Text
ruleName = camelName

rule :: RuleId -> Rule
rule r = case r of
  AsciiArrow -> Rule r Error "use → instead of ->" checkAsciiArrow
  AsciiLambda -> Rule r Error "use λ instead of \\" checkAsciiLambda
  PatternLambda -> Rule r Error "lambdas that match on patterns use λ { (…) → … }" checkPatternLambda
  AsciiSubscript -> Rule r Error "use unicode subscripts (V₁) instead of ascii digits (V1)" checkAsciiSubscript
  Prime -> Rule r Error "no primes on single-letter variables (Γ', σ'')" checkPrime
  PrefixType -> Rule r Error "write types that have a syntax declaration in their notation" checkPrefixType
  BannedName -> Rule r Error "names listed in [bannedNames]" checkBannedName
  SortLetter -> Rule r Warning "typed binders and variables use the letters configured in [[sorts]]" checkSortLetter
  ReservedLetter -> Rule r Error "letters of a reserved sort are not used for binders of other types" checkReservedLetter
  UnneededSubscript -> Rule r Warning "a lone M₁ in a clause should be M" checkUnneededSubscript
  PairSubscript -> Rule r Warning "two of a kind use the letter pair (M N), not M M₁" checkPairSubscript
  UnusedVariable -> Rule r Warning "generalizable variables that are never used" checkUnusedVariable
  LineLength -> Rule r Warning "lines longer than [style] lineLength" checkLineLength
  TrailingWhitespace -> Rule r Warning "trailing whitespace" checkTrailingWhitespace
  Tab -> Rule r Warning "tab characters" checkTab
  LeadingArrow -> Rule r Warning "arrows at line breaks go at the end of the line" checkLeadingArrow
  ModuleBlankLine -> Rule r Warning "a single blank line after the module header" checkModuleBlankLine
  ImportOrder -> Rule r Warning "a block of imports is in alphabetical order" checkImportOrder
  ImportPublic -> Rule r Warning "no public re-exports in the import list" checkImportPublic
  ImportModifierOrder -> Rule r Warning "import modifiers in the order public, using, renaming" checkImportModifierOrder
  MutualBlock -> Rule r Warning "mutual blocks are obsolete; put signatures before definitions" checkMutualBlock
  LetBinding -> Rule r Warning "prefer where blocks to let" checkLetBinding
  TrailingComment -> Rule r Warning "comments go above a term, not at the end of a line" checkTrailingComment
  SectionHeader -> Rule r Warning "dividers are [style] sectionWidth dashes with a title in [style] sectionTitle case" checkSectionHeader
  WithAlignment -> Rule r Warning "the | of a with-clause is not aligned (... | p)" checkWithAlignment
  UnicodeInstance -> Rule r Warning "use {{ }} instead of ⦃ ⦄" checkUnicodeInstance
  AsciiPrime -> Rule r Warning "names use ′ instead of the ascii '" checkAsciiPrime
  MissingFixity -> Rule r Warning "operators (names starting or ending in _) have a fixity declaration" checkMissingFixity
  BeginSameLine -> Rule r Warning "begin goes on the line with the proof it starts" checkBeginSameLine
  WhereLayout -> Rule r Warning "where goes on its own line below the clause" checkWhereLayout
  StackedPrivate -> Rule r Warning "private and variable go on separate lines" checkStackedPrivate
  BotElim -> Rule r Warning "prefer contradiction to ⊥-elim" checkBotElim

allRules :: [Rule]
allRules = map rule [minBound .. maxBound]

------------------------------------------------------------------------
-- findings and fixes

data Pos = Pos {posLine :: Int, posCol :: Int}
  deriving (Eq, Ord, Show)

data Fix
  = ReplaceSpan Pos Int Text
  | ReplaceLine Int Text
  | InsertLineAfter Int Text
  | DeleteLine Int
  deriving (Eq, Ord, Show)

data Finding = Finding
  { findingPos     :: Pos
  , findingMessage :: Text
  , findingFix     :: Maybe Fix
  }
  deriving (Eq, Ord)

data Diagnostic = Diagnostic
  { diagFile    :: FilePath
  , diagFinding :: Finding
  , diagRule    :: RuleId
  , diagLevel   :: Level
  }
  deriving (Eq, Ord)

finding :: Pos -> Text -> Finding
finding p m = Finding p m Nothing

fixed :: Pos -> Text -> Fix -> Finding
fixed p m f = Finding p m (Just f)

------------------------------------------------------------------------
-- config

data SectionTitle = Sentence | Lower | Any
  deriving (Eq, Show, Enum, Bounded, Generic)

data Banned = Banned {bannedReplacement :: Maybe Text, bannedAutoFix :: Bool}

data SortMatch = HeadsAnyOf [Text] | ExactlyOneOf [Text]

data SortSpec = SortSpec {sortMatch :: SortMatch, sortLetters :: [Text], sortReserved :: Bool}

data PairSkip = PairSkip {skipPath :: FilePath, skipPairs :: [(Text, Text)]}

data StyleSpec = StyleSpec
  { styleLineLength   :: Int
  , styleSectionWidth :: Int
  , styleSectionTitle :: SectionTitle
  }

data Config = Config
  { cfgSources         :: [String]
  , cfgExclude         :: [String]
  , cfgAllowlist       :: FilePath
  , cfgRules           :: Map RuleId Level
  , cfgBannedNames     :: Map Text Banned
  , cfgSubscriptIgnore :: [Text]
  , cfgSubscriptExempt :: [Text]
  , cfgSorts           :: [SortSpec]
  , cfgPairs           :: [(Text, Text)]
  , cfgPairSkips       :: [PairSkip]
  , cfgStyle           :: StyleSpec
  }

-- toml config, keys as fields
data RawConfig = RawConfig
  { sources              :: Maybe [Text]
  , exclude              :: Maybe [Text]
  , allowlist            :: Maybe Text
  , rules                :: Maybe (Map Text Level)
  , bannedNames          :: Maybe (Map Text Text)
  , fixBannedNames       :: Maybe [Text]
  , asciiSubscriptIgnore :: Maybe [Text]
  , subscriptExempt      :: Maybe [Text]
  , sorts                :: Maybe [RawSort]
  , pairs                :: Maybe [Text]
  , pairSkip             :: Maybe [RawPairSkip]
  , style                :: Maybe RawStyle
  }
  deriving (Generic)

data RawSort = RawSort {heads :: Maybe [Text], exact :: Maybe [Text], letters :: Text, reserved :: Maybe Bool}
  deriving (Generic)

data RawPairSkip = RawPairSkip {path :: Text, pairs :: [Text]}
  deriving (Generic)

data RawStyle = RawStyle {lineLength :: Maybe Int, sectionWidth :: Maybe Int, sectionTitle :: Maybe SectionTitle}
  deriving (Generic)

instance FromValue RawConfig where fromValue = genericFromTable
instance FromValue RawSort where fromValue = genericFromTable
instance FromValue RawPairSkip where fromValue = genericFromTable
instance FromValue RawStyle where fromValue = genericFromTable
instance FromValue Level where fromValue = enumFromValue
instance FromValue SectionTitle where fromValue = enumFromValue

-- enum by camelCase constructor name
enumFromValue :: forall a l. (Bounded a, Enum a, Constructors a) => Value' l -> Matcher l a
enumFromValue v = do
  t <- fromValue v
  maybe (failAt (Toml.valueAnn v) (unknown t)) pure (find ((== t) . camelName) values)
  where
    values = [minBound .. maxBound] :: [a]
    unknown t = "unknown value " <> show (t :: Text) <> ", expected one of " <> T.unpack (T.intercalate ", " (map camelName values))

pairOf :: Text -> (Text, Text)
pairOf t = case T.unpack t of
  [a, b] -> (T.singleton a, T.singleton b)
  _      -> (t, t)

resolveConfig :: RawConfig -> Either String Config
resolveConfig RawConfig {sources, exclude, allowlist, rules, bannedNames, fixBannedNames, asciiSubscriptIgnore, subscriptExempt, sorts, pairs, pairSkip, style} = do
  let settings = fromMaybe Map.empty rules
      unknown = [n | n <- Map.keys settings, n `notElem` map ruleName [minBound .. maxBound]]
      letterPairs = fromMaybe [] pairs
      badPairs = [p | p <- letterPairs, T.length p /= 2]
  unless (null unknown) $ Left ("unknown rules in config: " <> T.unpack (T.intercalate ", " unknown))
  unless (null badPairs) $ Left ("pairs must be two letters: " <> T.unpack (T.unwords badPairs))
  sortSpecs <- traverse resolveSort (fromMaybe [] sorts)
  pure
    Config
      { cfgSources = maybe ["**/*.agda", "**/*.lagda", "**/*.lagda.md"] (map T.unpack) sources
      , cfgExclude = maybe ["_build/**"] (map T.unpack) exclude
      , cfgAllowlist = maybe "AgdaLint.allow" T.unpack allowlist
      , cfgRules = Map.fromList [(r, Map.findWithDefault (ruleDefault (rule r)) (ruleName r) settings) | r <- [minBound .. maxBound]]
      , cfgBannedNames = Map.mapWithKey (banned (fromMaybe [] fixBannedNames)) (fromMaybe Map.empty bannedNames)
      , cfgSubscriptIgnore = fromMaybe [] asciiSubscriptIgnore
      , cfgSubscriptExempt = fromMaybe [] subscriptExempt
      , cfgSorts = sortSpecs
      , cfgPairs = map pairOf letterPairs
      , cfgPairSkips = maybe [] (map resolvePairSkip) pairSkip
      , cfgStyle = maybe defaultStyle resolveStyle style
      }
  where
    banned fixable k v = Banned (if T.null v then Nothing else Just v) (k `elem` fixable)
    resolveSort RawSort {heads, exact, letters, reserved} = case (heads, exact) of
      (Just hs, Nothing) -> Right (SortSpec (HeadsAnyOf hs) (map T.singleton (T.unpack letters)) (fromMaybe False reserved))
      (Nothing, Just es) -> Right (SortSpec (ExactlyOneOf es) (map T.singleton (T.unpack letters)) (fromMaybe False reserved))
      _                  -> Left "a sort needs exactly one of heads or exact"
    resolvePairSkip RawPairSkip {path, pairs = ps} = PairSkip (T.unpack path) (map pairOf ps)
    defaultStyle = StyleSpec 72 72 Sentence
    resolveStyle RawStyle {lineLength, sectionWidth, sectionTitle} =
      StyleSpec
        (fromMaybe (styleLineLength defaultStyle) lineLength)
        (fromMaybe (styleSectionWidth defaultStyle) sectionWidth)
        (fromMaybe (styleSectionTitle defaultStyle) sectionTitle)

-- config in current directory
configFile :: FilePath
configFile = "AgdaLint.toml"

loadConfig :: Maybe FilePath -> IO Config
loadConfig explicit = do
  let p = fromMaybe configFile explicit
  exists <- doesFileExist p
  when (not exists && isJust explicit) $ failWith (p <> ": no such config file")
  src <- if exists then TIO.readFile p else pure ""
  case Toml.decode src of
    Toml.Failure es -> failWith (p <> ": " <> unlines es)
    Toml.Success ws raw -> do
      unless (null ws) $ failWith (p <> ": " <> unlines ws)
      either (failWith . ((p <> ": ") <>)) pure (resolveConfig raw)

failWith :: String -> IO a
failWith msg = hPutStrLn stderr ("AgdaLint: " <> msg) >> exitWith (ExitFailure 2)

------------------------------------------------------------------------
-- lexer

data TokenKind = Word | Delim | Keyword | Literal | Comment | Pragma
  deriving (Eq, Ord, Show)

data Token = Token
  { tokKind    :: TokenKind
  , tokText    :: Text
  , tokPos     :: Pos
  , tokEndLine :: Int
  }
  deriving (Eq, Ord, Show)

data LineRole = Code | CommentOnly | Blank | Prose
  deriving (Eq, Show)

data Line = Line
  { lineNo     :: Int
  , lineText   :: Text
  , lineTokens :: [Token]
  , lineRole   :: LineRole
  }

keywords :: Set Text
keywords =
  Set.fromList
    [ "module", "where", "let", "in", "data", "record", "field", "constructor", "open", "import"
    , "using", "hiding", "renaming", "to", "public", "private", "variable", "mutual", "infix"
    , "infixl", "infixr", "syntax", "pattern", "postulate", "instance", "abstract", "with"
    , "rewrite", "do", "λ", "∀", "forall"
    ]

delims :: [Char]
delims = "(){};@"

type Lexer = Parsec Void Text

-- whole file
tokensP :: Lexer [Token]
tokensP = skipSpace *> (concat <$> many (tokenP <* skipSpace)) <* eof
  where
    skipSpace = skipMany (satisfy isSpace)

tokenP :: Lexer [Token]
tokenP =
  choice
    [ one Pragma (string "{-#" *> skipUntil "#-}")
    , one Comment (string "{-" *> blockBody)
    , one Comment lineComment
    , one Literal stringLiteral
    , one Delim (void (oneOf delims))
    , wordTokens
    ]
  where
    one kind p = do
      start <- getSourcePos
      (txt, _) <- MP.match p
      end <- getSourcePos
      pure [Token kind txt (toPos start) (unPos (sourceLine end))]
    skipUntil close = skipManyTill anySingle (void (string close) <|> eof)
    blockBody = skipManyTill (string "{-" *> blockBody <|> void anySingle) (void (string "-}") <|> eof)
    lineComment = try $ do
      _ <- string "--" *> takeWhileP Nothing (== '-')
      notFollowedBy (satisfy (\c -> not (isSpace c || isAlphaNum c)))
      void (takeWhileP Nothing (/= '\n'))
    stringLiteral = char '"' *> void (manyTill L.charLiteral (void (char '"') <|> lookAhead (void newline) <|> eof))

-- words
wordTokens :: Lexer [Token]
wordTokens = do
  start <- getSourcePos
  w <- takeWhile1P (Just "word") (\c -> not (isSpace c || c `elem` delims || c == '"'))
  let pos = toPos start
      line = posLine pos
      kindOf x
        | "'" `T.isPrefixOf` x = Literal
        | Set.member x keywords = Keyword
        | otherwise = Word
  pure $ case T.uncons w of
    Just ('.', rest)
      | not (T.null rest), not ("." `T.isPrefixOf` rest) ->
          [Token Delim "." pos line, Token (kindOf rest) rest pos {posCol = posCol pos + 1} line]
    _ -> [Token (kindOf w) w pos line]

toPos :: SourcePos -> Pos
toPos sp = Pos (unPos (sourceLine sp)) (unPos (sourceColumn sp) - 1)

-- literate formats
data Format = PlainAgda | LaTeXAgda | MarkdownAgda

formatOf :: FilePath -> Format
formatOf p
  | ".lagda.md" `T.isSuffixOf` T.pack p = MarkdownAgda
  | ".lagda" `T.isInfixOf` T.pack p = LaTeXAgda
  | otherwise = PlainAgda

-- agda code lines
codeMask :: Format -> [Text] -> [Bool]
codeMask fmt = case fmt of
  PlainAgda    -> map (const True)
  LaTeXAgda    -> fenced ("\\begin{code}" `T.isPrefixOf`) ("\\end{code}" `T.isPrefixOf`)
  MarkdownAgda -> fenced ((== "```agda") . T.strip) ((== "```") . T.strip)
  where
    fenced open close = snd . mapAccumL step False
      where
        step inside t
          | inside = let stay = not (close t) in (stay, stay)
          | otherwise = (open t, False)

lexFile :: FilePath -> Text -> Either String [Line]
lexFile path src = do
  lexed <- first errorBundlePretty (runParser (oneColumnTabs *> tokensP) path masked)
  let byLine = Map.fromListWith (flip (++)) [(posLine (tokPos t), [t]) | t <- lexed]
      insideComment = Set.fromList [n | t <- lexed, tokKind t `elem` [Comment, Pragma], n <- [posLine (tokPos t) + 1 .. tokEndLine t]]
      mkLine n t isCode
        | not isCode = Line n t [] Prose
        | otherwise = Line n t toks role
        where
          toks = Map.findWithDefault [] n byLine
          role
            | any ((`notElem` [Comment, Pragma]) . tokKind) toks = Code
            | not (null toks) || Set.member n insideComment = CommentOnly
            | otherwise = Blank
  pure (zipWith3 mkLine [1 ..] rawLines mask)
  where
    rawLines = T.splitOn "\n" src
    mask = codeMask (formatOf path) rawLines
    masked = T.intercalate "\n" [if m then t else "" | (t, m) <- zip rawLines mask]
    -- tab is one column
    oneColumnTabs = updateParserState (\st -> st {statePosState = (statePosState st) {pstateTabWidth = pos1}})

------------------------------------------------------------------------
-- structure

data Clause = Clause {clauseHead :: Line, clauseBody :: [Line]}

clauseLines :: Clause -> [Line]
clauseLines c = clauseHead c : clauseBody c

data Binder = Binder {binderNames :: [Token], binderType :: [Token]}

data VariableDecl = VariableDecl {varNames :: [Token], varType :: [Text]}

data Notation = Notation {notationParams :: [Text], notationRhs :: [Text]}
  deriving (Eq)

data ImportModifier = ModPublic | ModUsing | ModHiding | ModRenaming
  deriving (Eq, Ord, Show)

data OpenDecl = OpenDecl
  { openModule    :: Text
  , openIsImport  :: Bool
  , openIsOpen    :: Bool
  , openModifiers :: [ImportModifier]
  , openLine      :: Line
  }

data SourceFile = SourceFile
  { srcPath         :: FilePath
  , srcLines        :: [Line]
  , srcModule       :: Maybe Text
  , srcOpens        :: [OpenDecl]
  , srcClauses      :: [Clause]
  , srcVariables    :: [VariableDecl]
  , srcSyntax       :: Map Text Notation
  , srcFixities     :: Set Text
  , srcNamedKeys    :: Set Text
  , srcModuleParams :: Set Text
  , srcTokenCounts  :: Map Text Int
  }

codeLines :: SourceFile -> [Line]
codeLines = filter ((== Code) . lineRole) . srcLines

blockLines :: SourceFile -> [Line]
blockLines = filter ((/= Prose) . lineRole) . srcLines

texts :: [Token] -> [Text]
texts = map tokText

codeTokens :: Line -> [Token]
codeTokens = filter ((`notElem` [Comment, Pragma]) . tokKind) . lineTokens

indentOf :: Line -> Int
indentOf = T.length . T.takeWhile (== ' ') . lineText

firstText :: Line -> Maybe Text
firstText l = tokText <$> listToMaybe (codeTokens l)


analyse :: FilePath -> Text -> Either String SourceFile
analyse path src = do
  ls <- lexFile path src
  let code = filter ((`elem` [Code, Blank]) . lineRole) ls
  pure SourceFile
    { srcPath = path
    , srcLines = ls
    , srcModule = listToMaybe (mapMaybe (fmap tokText . runTokens (word "module" *> name) . codeTokens) code)
    , srcOpens = mapMaybe openDecl code
    , srcClauses = clauses code
    , srcVariables = variables code
    , srcSyntax = Map.fromList (mapMaybe notation code)
    , srcFixities = Set.fromList (concatMap fixity code)
    , srcNamedKeys = Set.fromList (concatMap (namedKeys . codeTokens) code)
    , srcModuleParams =
        Set.fromList [tokText n | l <- code, firstText l == Just "module", b <- binders (codeTokens l), n <- binderNames b]
    , srcTokenCounts = Map.fromListWith (+) [(tokText t, 1) | l <- code, t <- wordsOf l]
    }

-- line token parsers
type TokParser = Parsec Void [Token]

runTokens :: TokParser a -> [Token] -> Maybe a
runTokens p = parseMaybe (p <* takeRest)

-- all matches of p
scan :: TokParser a -> TokParser [a]
scan p = catMaybes <$> many (Just <$> try p <|> Nothing <$ anySingle)

word :: Text -> TokParser Token
word t = satisfy (\x -> tokText x == t && tokKind x `elem` [Word, Keyword])

name :: TokParser Token
name = satisfy ((== Word) . tokKind)

delim :: Text -> TokParser Token
delim t = satisfy (\x -> tokKind x == Delim && tokText x == t)

openDecl :: Line -> Maybe OpenDecl
openDecl l = runTokens p (codeTokens l)
  where
    p = do
      isOpen <- isJust <$> optional (word "open")
      isImport <- isJust <$> optional (word "import")
      guard (isOpen || isImport)
      m <- name
      mods <- mapMaybe (modifier . tokText) <$> many anySingle
      pure (OpenDecl (tokText m) isImport isOpen mods l)
    modifier = \case
      "public"   -> Just ModPublic
      "using"    -> Just ModUsing
      "hiding"   -> Just ModHiding
      "renaming" -> Just ModRenaming
      _          -> Nothing

notation :: Line -> Maybe (Text, Notation)
notation l = runTokens p (codeTokens l)
  where
    p = do
      _ <- word "syntax"
      n <- name
      params <- many (satisfy ((/= "=") . tokText))
      _ <- word "="
      rhs <- many anySingle
      pure (tokText n, Notation {notationParams = texts params, notationRhs = texts rhs})

fixity :: Line -> [Text]
fixity l = fromMaybe [] (runTokens p (codeTokens l))
  where
    p = choice (map word ["infix", "infixl", "infixr"]) *> anySingle *> (texts <$> many anySingle)

-- named argument keys
namedKeys :: [Token] -> [Text]
namedKeys = maybe [] (map tokText) . runTokens (scan (delim "{" *> name <* word "="))

-- line plus indented continuations
clauses :: [Line] -> [Clause]
clauses = finish . foldl' step (Nothing, [], False)
  where
    finish (cur, done, _) = reverse (maybe done (: done) cur)
    extend (Clause h b) l = Clause h (b ++ [l])
    step (cur, done, inVar) l
      | inVar && indentOf l >= 2 && ":" `elem` toks = (cur, done, True)
      | lineRole l == Blank = (cur, done, False)
      | isVariableHeader = (Nothing, flush, True)
      | Just c <- cur, firstText l == Just "..." = (Just (extend c l), done, False)
      | Just c <- cur, isSeparator, indentOf l > indentOf (clauseHead c) = (Just (extend c l), done, False)
      | resets = (Nothing, flush, False)
      | Just c <- cur, indentOf l > indentOf (clauseHead c) = (Just (extend c l), done, False)
      | otherwise = (Just (Clause l []), flush, False)
      where
        flush = maybe done (: done) cur
        toks = texts (codeTokens l)
        isVariableHeader = toks `elem` [["variable"], ["private", "variable"]]
        stripped = T.strip (lineText l)
        isSeparator = not (T.null stripped) && T.all (== '-') stripped
        resets =
          toks == ["mutual"]
            || (take 1 toks `elem` [["module"], ["private"], ["data"], ["record"]] && fmap snd (unsnoc toks) == Just "where")

variables :: [Line] -> [VariableDecl]
variables = go False
  where
    go _ [] = []
    go inVar (l : rest)
      | toks `elem` [["variable"], ["private", "variable"]] = go True rest
      | "private" : "variable" : entry@(_ : _) <- toks, ":" `elem` entry = decl (drop 2 (codeTokens l)) : go False rest
      | inVar && indentOf l >= 2 && ":" `elem` toks = decl (codeTokens l) : go True rest
      | lineRole l == Blank = go inVar rest
      | otherwise = go False rest
      where
        toks = texts (codeTokens l)
    decl ts = let (ns, ty) = break ((== ":") . tokText) ts in VariableDecl ns (drop 1 (texts ty))

-- binders on one line
binders :: [Token] -> [Binder]
binders = fromMaybe [] . runTokens (scan binder)
  where
    binder = do
      close <- (")" <$ delim "(") <|> ("}" <$ delim "{")
      names <- some (satisfy (\t -> tokKind t == Word && tokText t /= ":"))
      _ <- word ":"
      ty <- concat <$> many (bracketed <|> (: []) <$> satisfy (not . isBracket))
      _ <- delim close
      pure (Binder names ty)
    bracketed = do
      o <- delim "(" <|> delim "{"
      inner <- concat <$> many (bracketed <|> (: []) <$> satisfy (not . isBracket))
      c <- delim ")" <|> delim "}"
      pure (o : inner ++ [c])
    isBracket t = tokKind t == Delim && tokText t `elem` ["(", ")", "{", "}"]

codomain :: [Token] -> [Text]
codomain = codomainOf . texts

codomainOf :: [Text] -> [Text]
codomainOf = reverse . takeWhile (/= "→") . reverse

------------------------------------------------------------------------
-- context

data Context = Context
  { ctxConfig      :: Config
  , ctxNotations   :: Map FilePath (Map Text Notation)
  , ctxOperators   :: Set Text
  , ctxImporters   :: Map FilePath [SourceFile]
  }

-- each file with the files it imports, transitively, itself included
importClosures :: [SourceFile] -> Map FilePath [SourceFile]
importClosures files = Map.fromList [(srcPath f, closure f) | f <- files]
  where
    byModule = Map.fromList [(m, srcPath f) | f <- files, Just m <- [srcModule f]]
    imports f = mapMaybe ((`Map.lookup` byModule) . openModule) (filter openIsImport (srcOpens f))
    (graph, fromVertex, toVertex) = Graph.graphFromEdges [(f, srcPath f, imports f) | f <- files]
    closure f = [g | Just v <- [toVertex (srcPath f)], w <- Graph.reachable graph v, let (g, _, _) = fromVertex w]

visibleNotations :: Map FilePath [SourceFile] -> Map FilePath (Map Text Notation)
visibleNotations = Map.map visible
  where
    visible closure =
      let merged = Map.unionsWith pick (map (Map.map Just . srcSyntax) closure)
          pick a b = if a == b then a else Nothing
       in Map.mapMaybe id merged

-- each file with the files that import it, transitively, itself included
importers :: Map FilePath [SourceFile] -> Map FilePath [SourceFile]
importers closures = Map.fromListWith (++) [(srcPath d, [g]) | gs <- Map.elems closures, g <- take 1 gs, d <- gs]

------------------------------------------------------------------------
-- naming rules

subscriptDigit :: Char -> Char
subscriptDigit c = chr (ord '₀' + digitToInt c)

isSubscript :: Char -> Bool
isSubscript = inRange ('₀', '₉')

wordsOf :: Line -> [Token]
wordsOf = filter ((== Word) . tokKind) . codeTokens

replaceTok :: Token -> Text -> Fix
replaceTok t = ReplaceSpan (tokPos t) (T.length (tokText t))

checkAsciiArrow :: Context -> SourceFile -> [Finding]
checkAsciiArrow _ f =
  [fixed (tokPos t) "use → instead of ->" (replaceTok t "→") | l <- codeLines f, t <- wordsOf l, tokText t == "->"]

checkAsciiLambda :: Context -> SourceFile -> [Finding]
checkAsciiLambda _ f =
  [ fixed (tokPos t) "use λ instead of \\" (ReplaceSpan (tokPos t) 1 (if spaced then "λ" else "λ "))
  | l <- codeLines f
  , t <- wordsOf l
  , "\\" `T.isPrefixOf` tokText t
  , let spaced = maybe True (isSpace . fst) (T.uncons (T.drop (posCol (tokPos t) + 1) (lineText l)))
  ]

checkPatternLambda :: Context -> SourceFile -> [Finding]
checkPatternLambda _ f =
  [ finding (tokPos p) "use a pattern-matching lambda: λ { (…) → … }"
  | l <- codeLines f
  , lam : rest <- List.tails (codeTokens l)
  , tokText lam == "λ"
  , take 1 (map tokText rest) /= ["{"]
  , p <- patterns (takeWhile ((/= "→") . tokText) rest)
  ]
  where
    -- parenthesised binders without a type are patterns; () is the absurd lambda
    patterns (t : ts)
      | tokKind t == Delim, tokText t == "(" =
          let (inside, after) = group (1 :: Int) [] ts
           in [t | not (null inside), ":" `notElem` map tokText inside] ++ patterns after
      -- an unmatched closer ends the lambda
      | tokText t `elem` [")", "}", ";"] = []
      | otherwise = patterns ts
    patterns [] = []
    group _ acc [] = (reverse acc, [])
    group d acc (t : ts)
      | tokText t == ")" && d == 1 = (reverse acc, ts)
      | tokText t == ")" = group (d - 1) (t : acc) ts
      | tokText t == "(" = group (d + 1) (t : acc) ts
      | otherwise = group d (t : acc) ts

checkAsciiSubscript :: Context -> SourceFile -> [Finding]
checkAsciiSubscript ctx f =
  [ fixed (tokPos t) ("use " <> u <> " instead of " <> tokText t) (replaceTok t u)
  | l <- codeLines f
  , t <- wordsOf l
  , let (letters, rest) = T.span isLetter (tokText t)
        (digits, primes) = T.span isDigit rest
  , T.length letters `elem` [1, 2]
  , not (T.null digits)
  , T.all (== '\'') primes
  , not (any (`T.isPrefixOf` tokText t) (cfgSubscriptIgnore (ctxConfig ctx)))
  , let u = letters <> T.map subscriptDigit digits <> primes
  ]

isSingleLetterVar :: Text -> Bool
isSingleLetterVar t = case T.unpack t of
  c : rest -> isLetter c && all isSubscript rest
  []       -> False

checkPrime :: Context -> SourceFile -> [Finding]
checkPrime _ f =
  [ finding (tokPos t) ("no primes on variables: " <> tokText t)
  | l <- codeLines f
  , t <- wordsOf l
  , let (base, primes) = T.break (== '\'') (tokText t)
  , not (T.null primes)
  , T.all (== '\'') primes
  , isSingleLetterVar base
  ]

-- application arguments
isAtom :: Set Text -> Token -> Bool
isAtom operators t =
  tokKind t == Word
    && Set.notMember (tokText t) operators
    && not ("]" `T.isSuffixOf` tokText t)

-- notation operators
notationOperators :: [SourceFile] -> Set Text
notationOperators files =
  Set.fromList ["→", "->", ":", "=", "|"]
    <> Set.fromList [x | f <- files, n <- Map.elems (srcSyntax f), x <- notationRhs n, x `notElem` notationParams n]

-- argument span
data Arg = Arg {argFirst :: Token, argLast :: Token}

argument :: Set Text -> TokParser Arg
argument operators = parenthesised <|> (\t -> Arg t t) <$> satisfy (isAtom operators)
  where
    parenthesised = do
      o <- delim "("
      Arg o <$> inside
    inside = skipMany (void (delim "(" *> inside) <|> void (satisfy (not . isParen))) *> delim ")"
    isParen t = tokKind t == Delim && tokText t `elem` ["(", ")"]

-- notation application
application :: Set Text -> Map Text Notation -> TokParser (Token, Notation, [Arg])
application operators table = do
  t <- name
  n <- maybe empty pure (Map.lookup (tokText t) table)
  args <- count (length (notationParams n)) (argument operators)
  notFollowedBy (argument operators)
  pure (t, n, args)

spanText :: Line -> Token -> Token -> Text
spanText l a b = T.take (posCol (tokPos b) + T.length (tokText b) - posCol (tokPos a)) (T.drop (posCol (tokPos a)) (lineText l))

-- prefix uses
prefixUses :: Set Text -> Map Text Notation -> Line -> [(Token, Int, Text)]
prefixUses operators table l
  | firstText l `elem` [Just "syntax", Just "data"] = []
  | otherwise = mapMaybe render (fromMaybe [] (runTokens (scan (lookAhead (application operators table) <* anySingle)) (codeTokens l)))
  where
    render (t, n, args) = do
      (_, end) <- fmap argLast <$> unsnoc args
      let width = posCol (tokPos end) + T.length (tokText end) - posCol (tokPos t)
          sub = Map.fromList (zip (notationParams n) [spanText l (argFirst a) (argLast a) | a <- args])
      pure (t, width, T.unwords [Map.findWithDefault x x sub | x <- notationRhs n])

checkPrefixType :: Context -> SourceFile -> [Finding]
checkPrefixType ctx f =
  [ fixed (tokPos t) ("use the syntax form: " <> out) (ReplaceSpan (tokPos t) w out)
  | let table = Map.findWithDefault Map.empty (srcPath f) (ctxNotations ctx)
  , not (Map.null table)
  , l <- codeLines f
  , (t, w, out) <- prefixUses (ctxOperators ctx) table l
  ]

checkBannedName :: Context -> SourceFile -> [Finding]
checkBannedName ctx f =
  [ Finding (tokPos t) msg (if bannedAutoFix b then replaceTok t <$> bannedReplacement b else Nothing)
  | l <- codeLines f
  , t <- wordsOf l
  , Just b <- [Map.lookup (tokText t) (cfgBannedNames (ctxConfig ctx))]
  , let msg = maybe (tokText t <> " is not allowed") (\r -> "use " <> r <> " instead of " <> tokText t) (bannedReplacement b)
  ]

hasLetterFrom :: [Text] -> Text -> Bool
hasLetterFrom letters v = any (maybe False (T.all isSubscript) . (`T.stripPrefix` v)) letters

checkSortLetter :: Context -> SourceFile -> [Finding]
checkSortLetter ctx f =
  [ finding (tokPos n) (tokText n <> " : " <> T.unwords cod <> " should be one of " <> T.unwords (sortLetters s))
  | (ns, cod) <- [(binderNames b, codomain (binderType b)) | l <- codeLines f, b <- binders (codeTokens l)]
      ++ [(varNames v, codomainOf (varType v)) | v <- srcVariables f]
  , Just s <- [find (sortMatches cod) (cfgSorts (ctxConfig ctx))]
  , n <- ns
  , tokText n /= "_"
  , not (hasLetterFrom (sortLetters s) (tokText n))
  ]

checkReservedLetter :: Context -> SourceFile -> [Finding]
checkReservedLetter ctx f =
  [ finding (tokPos n) (tokText n <> " is reserved for " <> T.unwords (sortNames s) <> ", but has type " <> T.unwords (texts (binderType b)))
  | l <- codeLines f
  , b <- binders (codeTokens l)
  , let cod = codomain (binderType b)
  , not (null cod), cod /= ["_"]
  -- universes are types too
  , take 1 cod /= ["Set"]
  , n <- binderNames b
  , Just s <- [find (\o -> sortReserved o && hasLetterFrom (sortLetters o) (tokText n)) sorts]
  , not (sortMatches cod s)
  ]
  where
    sorts = cfgSorts (ctxConfig ctx)
    sortNames s = case sortMatch s of
      HeadsAnyOf hs   -> hs
      ExactlyOneOf es -> es

sortMatches :: [Text] -> SortSpec -> Bool
sortMatches cod s = case sortMatch s of
  HeadsAnyOf hs   -> any (`elem` hs) cod
  ExactlyOneOf es -> case cod of [c] -> c `elem` es; _ -> False

-- clause names without named-argument keys
clauseNames :: Clause -> [Text]
clauseNames = concatMap (dropKeys . codeTokens) . clauseLines
  where
    dropKeys (Token {tokKind = Delim, tokText = "{"} : _ : e@(Token {tokText = "="} : _)) = dropKeys e
    dropKeys (t : ts) = [tokText t | tokKind t == Word] ++ dropKeys ts
    dropKeys [] = []

-- clauses for subscript rules
relevantClauses :: Context -> SourceFile -> [Clause]
relevantClauses ctx f =
  [ c
  | c <- srcClauses f
  , firstText (clauseHead c) /= Just "syntax"
  , not (any (`elem` clauseNames c) (cfgSubscriptExempt (ctxConfig ctx)))
  ]

clausePos :: Clause -> Pos
clausePos c = Pos (lineNo (clauseHead c)) 0

subscripted :: Text -> Maybe (Text, Text)
subscripted t = case T.unpack t of
  c : rest@(_ : _) | isLetter c, all isSubscript rest -> Just (T.singleton c, T.pack rest)
  _ -> Nothing

checkUnneededSubscript :: Context -> SourceFile -> [Finding]
checkUnneededSubscript ctx f =
  [ finding (clausePos c) (v <> " is the only " <> letter <> " here; use " <> letter)
  | c <- relevantClauses ctx f
  , let names = Set.fromList (clauseNames c)
        families = Map.fromListWith Set.union [(letter, Set.singleton t) | t <- toList names, Just (letter, _) <- [subscripted t]]
  , (letter, vs) <- Map.toList families
  , Set.notMember letter names
  , [v] <- [Set.toList vs]
  , Set.notMember v (srcNamedKeys f)
  , Set.notMember v (srcModuleParams f)
  ]

checkPairSubscript :: Context -> SourceFile -> [Finding]
checkPairSubscript ctx f =
  [ finding (clausePos c) (T.unwords (Set.toList used) <> ": use " <> a <> " and " <> b)
  | c <- relevantClauses ctx f
  , let names = Set.fromList (clauseNames c)
  , (a, b) <- pairs
  , let used = Set.filter (hasLetterFrom [a, b]) names
  , Set.size used == 2
  , used /= Set.fromList [a, b]
  , Set.null (Set.intersection used (srcNamedKeys f))
  , Set.size (Set.map (T.take 1) used) == 1
  , Set.notMember b names
  ]
  where
    skipped = concat [skipPairs s | s <- cfgPairSkips (ctxConfig ctx), skipPath s `isPrefixOf` srcPath f]
    pairs = filter (`notElem` skipped) (cfgPairs (ctxConfig ctx))

checkUnusedVariable :: Context -> SourceFile -> [Finding]
checkUnusedVariable ctx f =
  [ finding (tokPos n) (tokText n <> " is declared but never used")
  | v <- srcVariables f
  , n <- varNames v
  , sum [Map.findWithDefault 0 (tokText n) (srcTokenCounts g) | g <- Map.findWithDefault [f] (srcPath f) (ctxImporters ctx)] <= 1
  ]

------------------------------------------------------------------------
-- stdlib style guide rules

lineStart :: Line -> Pos
lineStart l = Pos (lineNo l) (indentOf l)

checkLineLength :: Context -> SourceFile -> [Finding]
checkLineLength ctx f =
  [ finding (Pos (lineNo l) limit) ("line is " <> T.show (T.length (lineText l)) <> " characters (limit " <> T.show limit <> ")")
  | let limit = styleLineLength (cfgStyle (ctxConfig ctx))
  , l <- blockLines f
  , T.length (lineText l) > limit
  ]

checkTrailingWhitespace :: Context -> SourceFile -> [Finding]
checkTrailingWhitespace _ f =
  [ fixed (Pos (lineNo l) (T.length s)) "trailing whitespace" (ReplaceLine (lineNo l) s)
  | l <- blockLines f
  , let s = T.stripEnd (lineText l)
  , s /= lineText l
  ]

checkTab :: Context -> SourceFile -> [Finding]
checkTab _ f = [finding (Pos (lineNo l) c) "tab character" | l <- blockLines f, Just c <- [T.findIndex (== '\t') (lineText l)]]

checkLeadingArrow :: Context -> SourceFile -> [Finding]
checkLeadingArrow _ f = [finding (lineStart l) "put → at the end of the previous line" | l <- codeLines f, indentOf l > 0, firstText l == Just "→"]

checkModuleBlankLine :: Context -> SourceFile -> [Finding]
checkModuleBlankLine _ f = case dropWhile (not . isHeader) (codeLines f) of
  [] -> []
  (h : _) ->
    let headerEnd = fromMaybe h (find ((== Just "where") . fmap snd . unsnoc . texts . codeTokens) (dropWhile ((< lineNo h) . lineNo) (codeLines f)))
        after = [l | l <- srcLines f, lineNo l > lineNo headerEnd, not (isFence l)]
        pos = Pos (lineNo headerEnd) 0
        msg = "put a single blank line after the module header"
     in case after of
          (a : b : _) | lineRole a == Blank, lineRole b /= Blank -> []
          (a : _) | lineRole a /= Blank -> [fixed pos msg (InsertLineAfter (lineNo headerEnd) "")]
          (_ : rest) ->
            let extra = takeWhile ((== Blank) . lineRole) rest
             in [Finding pos msg (Just (DeleteLine (lineNo e))) | e <- extra]
          [] -> [finding pos msg]
  where
    isHeader l = indentOf l == 0 && firstText l == Just "module"
    isFence l = lineRole l == Prose

checkImportOrder :: Context -> SourceFile -> [Finding]
checkImportOrder _ f = concatMap check (blocks (srcLines f))
  where
    -- a block is a run of imports, broken by blank lines, comments and other code
    blocks ls = case dropWhile (not . isImport) ls of
      [] -> []
      xs@(x : _) ->
        let continues l = isImport l || (lineRole l == Code && indentOf l > indentOf x)
            (b, rest) = span continues xs
         in filter isImport b : blocks rest
    isImport l = maybe False openIsImport (openDecl l)
    check b =
      [ finding (lineStart l) (m <> " should come before " <> p)
      | (prev, l) <- zip b (drop 1 b)
      , Just p <- [openModule <$> openDecl prev]
      , Just m <- [openModule <$> openDecl l]
      , m < p
      ]

checkImportPublic :: Context -> SourceFile -> [Finding]
checkImportPublic _ f =
  [ finding (lineStart (openLine o)) "import without public and open it publicly later"
  | o <- srcOpens f
  , openIsImport o && openIsOpen o
  , ModPublic `elem` openModifiers o
  ]

checkImportModifierOrder :: Context -> SourceFile -> [Finding]
checkImportModifierOrder _ f =
  [ finding (lineStart (openLine o)) "modifiers go in the order public, using, renaming"
  | o <- srcOpens f
  , let ranks = map rank (openModifiers o)
  , ranks /= List.sort ranks
  ]
  where
    rank = \case ModPublic -> 0 :: Int; ModUsing -> 1; ModHiding -> 1; ModRenaming -> 2

checkMutualBlock :: Context -> SourceFile -> [Finding]
checkMutualBlock _ f = [finding (lineStart l) "mutual blocks are obsolete; put signatures before definitions" | l <- codeLines f, texts (codeTokens l) == ["mutual"]]

checkLetBinding :: Context -> SourceFile -> [Finding]
checkLetBinding _ f = [finding (tokPos t) "prefer a where block to let" | l <- codeLines f, t <- codeTokens l, tokKind t == Keyword, tokText t == "let"]

checkTrailingComment :: Context -> SourceFile -> [Finding]
checkTrailingComment _ f =
  [ finding (tokPos c) "put the comment above the term"
  | l <- codeLines f
  , c@Token {tokKind = Comment, tokText = body} <- lineTokens l
  , any ((< posCol (tokPos c)) . posCol . tokPos) (codeTokens l)
  , not (T.all (== '-') body)
  ]

checkSectionHeader :: Context -> SourceFile -> [Finding]
checkSectionHeader ctx f = concat [check l next | (l, next) <- zip ls (map Just (drop 1 ls) ++ [Nothing]), isDivider l]
  where
    style = cfgStyle (ctxConfig ctx)
    ls = blockLines f
    isDivider l = T.length (lineText l) >= 4 && T.all (== '-') (lineText l)
    check l next =
      [ finding (Pos (lineNo l) 0) ("divider is " <> T.show (T.length (lineText l)) <> " dashes (expected " <> T.show (styleSectionWidth style) <> ")")
      | T.length (lineText l) /= styleSectionWidth style
      ]
        ++ case next of
          Just n
            | Just title <- T.stripStart <$> T.stripPrefix "--" (lineText n)
            , not (T.null title)
            , not (T.all (== '-') title)
            , Just problem <- titleProblem title ->
                [finding (Pos (lineNo n) 0) problem]
          _ -> []
    titleProblem t = case styleSectionTitle style of
      Sentence | not (maybe False (isUpper . fst) (T.uncons t)) || not (T.any isLower t) -> Just ("title should be in sentence case: " <> t)
      Lower | not (all allowedWord (T.words t)) -> Just ("title should be lowercase: " <> t)
      _ -> Nothing
      where
        -- acronyms are fine in an otherwise lowercase title
        allowedWord w = T.toLower w == w || (T.any isLower t && T.all (\c -> not (isLetter c) || isUpper c) w)

checkWithAlignment :: Context -> SourceFile -> [Finding]
checkWithAlignment _ f =
  [ finding (lineStart l) "write ... | without aligning the |"
  | l <- codeLines f
  , Just (d, b) <- [runTokens ((,) <$> word "..." <*> word "|") (codeTokens l)]
  , posCol (tokPos b) - posCol (tokPos d) > 4
  ]

checkUnicodeInstance :: Context -> SourceFile -> [Finding]
checkUnicodeInstance _ f =
  [ fixed (tokPos t) "use {{ }} instead of ⦃ ⦄" (replaceTok t (T.replace "⦃" "{{" (T.replace "⦄" "}}" (tokText t))))
  | l <- codeLines f
  , t <- wordsOf l
  , T.any (`elem` ("⦃⦄" :: String)) (tokText t)
  ]

checkAsciiPrime :: Context -> SourceFile -> [Finding]
checkAsciiPrime _ f =
  [ fixed (tokPos t) ("use ′ instead of ' in " <> tokText t) (replaceTok t (T.replace "'" "′" (tokText t)))
  | l <- codeLines f
  , t <- wordsOf l
  , "'" `T.isInfixOf` tokText t
  , not (isSingleLetterVar (T.takeWhile (/= '\'') (tokText t)))
  ]

checkMissingFixity :: Context -> SourceFile -> [Finding]
checkMissingFixity _ f =
  [ finding (lineStart l) (n <> " has no fixity declaration")
  | c <- srcClauses f
  , let l = clauseHead c
  , Just n <- [tokText <$> runTokens (name <* word ":") (codeTokens l)]
  , n /= "_"
  , "_" `T.isPrefixOf` n || "_" `T.isSuffixOf` n
  , Set.notMember n (srcFixities f)
  ]

checkBeginSameLine :: Context -> SourceFile -> [Finding]
checkBeginSameLine _ f = [finding (lineStart l) "put begin on the line with the proof it starts" | l <- codeLines f, firstText l == Just "begin"]

checkWhereLayout :: Context -> SourceFile -> [Finding]
checkWhereLayout _ f =
  [ finding (tokPos w) "put where on its own line below the clause"
  | l <- codeLines f
  , let ts = codeTokens l
  , length ts > 1
  , Just (_, w) <- [unsnoc ts]
  , tokText w == "where"
  , "=" `elem` texts ts
  , firstText l `notElem` map Just ["module", "data", "record", "instance"]
  ]

checkStackedPrivate :: Context -> SourceFile -> [Finding]
checkStackedPrivate _ f = [finding (lineStart l) "put private and variable on separate lines" | l <- codeLines f, take 2 (texts (codeTokens l)) == ["private", "variable"]]

checkBotElim :: Context -> SourceFile -> [Finding]
checkBotElim _ f = [finding (tokPos t) "prefer contradiction to ⊥-elim" | l <- codeLines f, t <- wordsOf l, tokText t == "⊥-elim"]

------------------------------------------------------------------------
-- running

-- command line, flags named after the fields
data Options w = Options
  { fix       :: w ::: Bool <?> "rewrite fixable findings in place"
  , noWarn    :: w ::: Bool <?> "only report errors"
  , listRules :: w ::: Bool <?> "list rules with their configured level"
  , config    :: w ::: Maybe FilePath <?> "config file (default: AgdaLint.toml)"
  }
  deriving (Generic)

instance ParseRecord (Options Wrapped)

loadSources :: FilePath -> Config -> IO [SourceFile]
loadSources root cfg = do
  found <- concat <$> Glob.globDir (map Glob.compile (cfgSources cfg)) root
  let excludes = map Glob.compile (cfgExclude cfg)
      rel = makeRelative root
      keep p = not (any (`Glob.match` rel p) excludes) && not (".#" `isPrefixOf` takeFileName p)
      paths = nubOrd (filter keep found)
  forM (List.sort paths) $ \p -> either failWith pure . analyse (rel p) =<< TIO.readFile p

-- path glob, line (all if Nothing), rule
data Allow = Allow {allowPath :: Glob.Pattern, allowLine :: Maybe Int, allowRule :: RuleId}

parseAllow :: Text -> Either String Allow
parseAllow l = case T.splitOn ":" l of
  [p, n, r] -> Allow (Glob.compile (T.unpack p)) <$> line n <*> ruleOf r
  _ -> Left ("expected path:line:rule, got " <> T.unpack l)
  where
    line n
      | n == "*" = Right Nothing
      | Right (k, "") <- TR.decimal n = Right (Just k)
      | otherwise = Left ("bad line " <> T.unpack n <> " in " <> T.unpack l)
    ruleOf r = maybe (Left ("unknown rule " <> T.unpack r <> " in " <> T.unpack l)) Right (find ((== r) . ruleName) [minBound .. maxBound])

loadAllowlist :: FilePath -> IO [Allow]
loadAllowlist p = do
  ok <- doesFileExist p
  src <- if ok then TIO.readFile p else pure ""
  either (failWith . ((p <> ": ") <>)) pure $
    traverse parseAllow [l | l <- map T.strip (T.lines src), not (T.null l), not ("#" `T.isPrefixOf` l)]

enabled :: Config -> RuleId -> Maybe Level
enabled cfg r = case cfgRules cfg Map.! r of
  Off -> Nothing
  l   -> Just l

lintAll :: Config -> [Allow] -> [SourceFile] -> [Diagnostic]
lintAll cfg allow files =
  [ Diagnostic (srcPath f) fd (ruleId r) lvl
  | f <- files
  , r <- allRules
  , Just lvl <- [enabled cfg (ruleId r)]
  , fd <- ruleCheck r ctx f
  , not (allowed (srcPath f) (ruleId r) fd)
  ]
  where
    closures = importClosures files
    ctx =
      Context
        { ctxConfig = cfg
        , ctxNotations = visibleNotations closures
        , ctxOperators = notationOperators files
        , ctxImporters = importers closures
        }
    allowed p r fd =
      any (\a -> allowRule a == r && Glob.match (allowPath a) p && all (== posLine (findingPos fd)) (allowLine a)) allow

applyFixes :: [Fix] -> [Text] -> [Text]
applyFixes fixes ls = structural (zipWith perLine [1 ..] ls)
  where
    byLine = Map.fromListWith (++) [(n, [fx]) | fx <- fixes, Just n <- [lineOf fx]]
    lineOf = \case ReplaceSpan p _ _ -> Just (posLine p); ReplaceLine n _ -> Just n; _ -> Nothing
    perLine n t = case Map.findWithDefault [] n byLine of
      fs | Just (ReplaceLine _ t') <- find isWhole fs -> t'
      fs -> spans t (sortOn (negate . spanCol) [s | s@ReplaceSpan {} <- fs])
    spanCol = \case ReplaceSpan p _ _ -> posCol p; _ -> 0
    isWhole = \case ReplaceLine {} -> True; _ -> False
    spans t = snd . foldl' apply (maxBound, t)
    apply (limit, t) (ReplaceSpan p w new)
      | posCol p + w <= limit = (posCol p, T.take (posCol p) t <> new <> T.drop (posCol p + w) t)
      | otherwise = (limit, t)
    apply acc _ = acc
    structural xs = concat (zipWith edit [1 ..] xs)
    deletes = Set.fromList [n | DeleteLine n <- fixes]
    inserts = Map.fromListWith (++) [(n, [t]) | InsertLineAfter n t <- fixes]
    edit n t
      | Set.member n deletes = []
      | otherwise = t : Map.findWithDefault [] n inserts

fixRound :: FilePath -> Config -> [Allow] -> IO Bool
fixRound root cfg allow = do
  files <- loadSources root cfg
  let diags = lintAll cfg allow files
      byFile = Map.fromListWith (++) [(diagFile d, [fx]) | d <- diags, Just fx <- [findingFix (diagFinding d)]]
  forM_ (Map.toList byFile) $ \(p, fixes) -> do
    src <- TIO.readFile (root </> p)
    TIO.writeFile (root </> p) (T.intercalate "\n" (applyFixes fixes (T.splitOn "\n" src)))
  pure (not (Map.null byFile))

report :: Diagnostic -> Text
report d =
  T.pack (diagFile d) <> ":" <> T.show (posLine pos) <> ":" <> T.show (posCol pos + 1) <> ": "
    <> camelName (diagLevel d) <> " [" <> ruleName (diagRule d) <> "] " <> findingMessage (diagFinding d)
  where
    pos = findingPos (diagFinding d)

main :: IO ()
main = do
  Options {fix, noWarn, listRules, config} <- withProgName "AgdaLint.hs" (unwrapRecord "Lint agda sources, configured by AgdaLint.toml in the current directory")
  cfg <- loadConfig config
  root <- getCurrentDirectory
  when listRules $ do
    forM_ allRules $ \r -> do
      let lvl = cfgRules cfg Map.! ruleId r
      TIO.putStrLn (T.justifyLeft 24 ' ' (ruleName (ruleId r)) <> T.justifyLeft 9 ' ' (camelName lvl) <> ruleSummary r)
    exitSuccess
  allow <- loadAllowlist (root </> cfgAllowlist cfg)
  when fix $ fixLoop root cfg allow (5 :: Int)
  files <- loadSources root cfg
  let diags = List.sort (lintAll cfg allow files)
      shown = if noWarn then filter ((== Error) . diagLevel) diags else diags
      errors = length (filter ((== Error) . diagLevel) diags)
  mapM_ (TIO.putStrLn . report) shown
  hPutStrLn stderr (show errors <> " error(s), " <> show (length shown - errors) <> " warning(s)")
  exitWith (if errors > 0 then ExitFailure 1 else ExitSuccess)
  where
    fixLoop _ _ _ 0 = pure ()
    fixLoop root cfg allow n = do
      changed <- fixRound root cfg allow
      when changed (fixLoop root cfg allow (n - 1))
