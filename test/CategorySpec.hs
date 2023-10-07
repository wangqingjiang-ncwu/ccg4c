-- Copyright China University of Water Resources and Electric Power (c) 2023
-- All rights reserved.

module CategorySpec where

import Category
import Test.Hspec

spec :: Spec
spec = do
  describe "Category" $ do
    it "returns the result of s == np is False" $ do
      sCate == npCate `shouldBe` (False :: Bool)
    it "returns the first element of seps" $ do
      head seps `shouldBe` ("|" :: String)
    it "returns the first element of primitives" $ do
      head primitives `shouldBe` ("s" :: String)
    it "nilCate is the category Nil" $ do
      nilCate `shouldBe` nilCate
    it "sCate is the category s" $ do
      sCate `shouldBe` sCate
    it "npCate is the category np" $ do
      npCate `shouldBe` npCate
    it "Result of veriStrForCate \"s|np\" is True" $ do
      veriStrForCate "s|np" `shouldBe` (True :: Bool)
    it "Result of getCateFromString  \"s|np\" is category s|np" $ do
      show (getCateFromString "s|np") `shouldBe` "s|np"
    it "Result of getCateFromString  \"(s|np)|np\" is category (s|np)|np" $ do
      show (getCateFromString "(s|np)|np") `shouldBe` "(s|np)|np"
    it "Result of indexOfSlash 0 0 \"(s|np)|(s|np)\" is 6" $ do
      indexOfSep 0 0 "(s|np)|(s|np)" `shouldBe` 6
    it "Result of leftStr (s|np)|(s|np) is s|np" $ do
      leftStr "(s|np)|(s|np)" `shouldBe` "s|np"
    it "Result of rightStr (s|np)|np is np" $ do
      rightStr "(s|np)|np" `shouldBe` "np"
    it "Result of midSepStr (s|np)|(s|np) is |" $ do
      midSepStr "(s|np)|(s|np)" `shouldBe` "|"
    it "Result isNil Nil is True" $ do
      isNil (getCateFromString "Nil") `shouldBe` (True :: Bool)
    it "Result isPrimitive (Primitive \"s\") is True" $ do
      isPrimitive (getCateFromString "s") `shouldBe` (True :: Bool)
    it "Result isDerivative (getCateFromString \"(s|np)|(s|np)\") is True" $ do
      isDerivative (getCateFromString "(s|np)|(s|np)") `shouldBe` (True :: Bool)
