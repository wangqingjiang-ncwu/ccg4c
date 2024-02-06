-- Copyright China University of Water Resources and Electric Power (c) 2023
-- All rights reserved.

module CLSpec (
     spec
     ) where

import CL
import Test.Hspec

spec :: Spec
spec = do
  describe "CL" $ do
    it "returns the result of sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm \"S\") (VarTerm \"x\")) (ConstTerm \"y\")) (ConstTerm \"z\")) is ((x z) (y z))" $ do
      sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") (VarTerm "x")) (ConstTerm "y")) (ConstTerm "z")) `shouldBe` (JuxTerm (JuxTerm (VarTerm "x") (ConstTerm "z")) (JuxTerm (ConstTerm "y") (ConstTerm "z")))

    it "Result of getTermFromStr \"(S x) y\") is ((S x) y" $ do
      getTermFromStr "((S x) y)" `shouldBe` (JuxTerm (JuxTerm (ConstTerm "S") (ConstTerm "x")) (ConstTerm "y"))

    it "Result of subTermOfTerm (getTermFromStr \"(S x) y\") is [((S x) y), (S x), S, x, y]" $ do
      subTermOfTerm (getTermFromStr "((S x) y)") `shouldBe` [JuxTerm (JuxTerm (ConstTerm "S") (ConstTerm "x")) (ConstTerm "y"), JuxTerm (ConstTerm "S") (ConstTerm "x"), ConstTerm "S", ConstTerm "x", ConstTerm "y"]

    it "Result of subTermReduct ((S x) (Y y2) z) is ((x z) ((y2 (Y y2)) z))" $ do
      subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") (ConstTerm "x")) (JuxTerm (ConstTerm "Y") (ConstTerm "y2"))) (ConstTerm "z")) `shouldBe` (JuxTerm (JuxTerm (ConstTerm "x") (ConstTerm "z")) (JuxTerm (JuxTerm (ConstTerm "y2") (JuxTerm (ConstTerm "Y") (ConstTerm "y2"))) (ConstTerm "z")))

    it "Result of reduct 3 (((S x) (Y y2)) z) is ((x z) ((y2 (y2 (y2 (Y y2)))) z))" $ do
      reduct 3 (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") (ConstTerm "x")) (JuxTerm (ConstTerm "Y") (ConstTerm "y2"))) (ConstTerm "z")) `shouldBe` (JuxTerm (JuxTerm (ConstTerm "x") (ConstTerm "z")) (JuxTerm (JuxTerm (ConstTerm "y2") (JuxTerm (ConstTerm "y2") (JuxTerm (ConstTerm "y2") (JuxTerm (ConstTerm "Y") (ConstTerm "y2"))))) (ConstTerm "z")))
