module Language.JavaScript.String
       where

import Control.Applicative ((<*), (<$>))
import Control.Monad (void)

import Text.Parsec
import Text.ParserCombinators.Parsec.Char

import Language.JavaScript.Lexer

stringNumericLiteral :: CharParser st Double
stringNumericLiteral = do
  mb <- optional strWhiteSpace
  do { n <- strNumericLiteral; optional strWhiteSpace; return n } <|>
    do { return 0 }

strWhiteSpace :: CharParser st ()
strWhiteSpace =
  do { strWhiteSpaceChar; void $ optionMaybe strWhiteSpace }

strWhiteSpaceChar :: CharParser st ()
strWhiteSpaceChar = void $
  whiteSpace <|>
  lineTerminator

strNumericLiteral :: CharParser st Double
strNumericLiteral =
  (fromIntegral <$> hexIntegerLiteral) <|>
  strDecimalLiteral

strDecimalLiteral :: CharParser st Double
strDecimalLiteral =
  strUnsignedDecimalLiteral <|>
  do { void $ char '+'; strUnsignedDecimalLiteral } <|>
  do { void $ char '-'; mv <- strUnsignedDecimalLiteral;
       if mv == 0
       then return 0
       else return (-mv) }

strUnsignedDecimalLiteral :: CharParser st Double
strUnsignedDecimalLiteral =
  do { void $ string "Infinity"; return 0 } <|>
  do { (mv, _) <- try $ do { decimalDigits <* char '.' };
       mdv <- optionMaybe decimalDigits;
       mev <- optionMaybe exponentPart;
       case (mdv, mev) of
        (Nothing, Nothing) -> return (fromIntegral mv)
        (Just (dv, n), Nothing) ->
          return $ (fromIntegral mv) + (fromIntegral dv) * 10 ^^ (-n)
        (Nothing, Just ev) -> return $ (fromIntegral mv) * 10 ^^ ev
        (Just (dv, n), Just ev) ->
          return $ ((fromIntegral mv) + (fromIntegral dv) * 10 ^^ (-n)) * 10 ^^ ev} <|>
  do { void $ char '.'; (dv, n) <- decimalDigits; mev <- optionMaybe exponentPart;
       case mev of
        Nothing -> return $ (fromIntegral dv) * 10 ^^ (-n)
        Just ev -> return $ (fromIntegral dv) * 10 ^^ (ev - n) } <|>
  do { (dv, _) <- decimalDigits; mev <- optionMaybe exponentPart;
       case mev of
        Nothing -> return (fromIntegral dv)
        Just ev -> return $ (fromIntegral dv) * 10 ^^ ev }

parseString :: String -> Maybe Double
parseString s =
  case runParser stringNumericLiteral () "" s of
   Right l -> Just l
   Left _  -> Nothing
