-- Copyright China University of Water Resources and Electric Power (c) 2023
-- All rights reserved.

module CLSpec where

import CL
import Test.Hspec

spec :: Spec
spec = do
  describe "CL" $ do
    it "returns the result of sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") (VarTerm "X")) (ConstTerm "Y")) (ConstTerm "Z")) is ((X Z) (Y Z))" $ do
      sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") (VarTerm "X")) (ConstTerm "Y")) (ConstTerm "Z")) `shouldBe` "((X Z) (Y Z))"

    it "Result of subTermOfTerm (getTermFromStr \"(S x) y\") is [S, x, y]" $ do
      subTermOfTerm (getTermFromStr "((S x) y)") `shouldBe` [ConstTerm "S", ConstTerm "x", ConstTerm "y"]
