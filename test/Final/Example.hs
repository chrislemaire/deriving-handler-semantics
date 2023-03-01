{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Final.Example where

import Final.ScopedToSmall
import Final.ScopedToSmallTest

p476 :: Result6
p476 =
  convertVOP4ToVOP6
    ( eval4
        ( Handle4
            ( Handler4
                "T476Eff0"
                ret0
                ( \___op -> case ___op of
                    "T476Eff0Op1" -> \v0 resumeF ->
                      let resume = LambdaV4 resumeF
                       in Let4
                            (Lit4 UnitV4)
                            ( \v1 ->
                                Let4
                                  ( Let4
                                      (App4 (Lit4 resume) (Lit4 (PairV4 (SumRightV4 (ConsV4 UnitV4 (ConsV4 UnitV4 (ConsV4 UnitV4 (ConsV4 UnitV4 NilV4))))) (SumLeftV4 (PairV4 (IntV4 (-95)) (IntV4 (-64)))))))
                                      ( \v2 ->
                                          Let4
                                            (Let4 (Lit4 UnitV4) (\v3 -> Let4 (App4 (Lit4 resume) (UnList4 (Let4 (Lit4 (PairV4 (ConsV4 (PairV4 UnitV4 (IntV4 (-101))) NilV4) UnitV4)) (\v1 -> Lit4 (ConsV4 (PairV4 (SumLeftV4 (SumLeftV4 UnitV4)) NilV4) NilV4))) (Let4 (Lit4 (PairV4 (LambdaV4 (\v1 -> Lit4 (PairV4 (IntV4 (-124)) (IntV4 (-139))))) UnitV4)) (\v1 -> Lit4 (PairV4 (SumLeftV4 (LambdaV4 (\v2 -> Lit4 (IntV4 (-89))))) (SumRightV4 (SumLeftV4 (IntV4 172)))))) (\v1 v2 -> If4 (Lit4 (BoolV4 True)) (Lit4 (PairV4 (SumLeftV4 (LambdaV4 (\v3 -> Lit4 v3))) (SumLeftV4 (PairV4 (IntV4 83) (IntV4 31))))) (Lit4 (PairV4 (SumLeftV4 (LambdaV4 (\v3 -> Lit4 v3))) (SumLeftV4 (PairV4 (IntV4 (-121)) (IntV4 (-170))))))))) (\v2 -> Let4 (Lit4 UnitV4) (\v1 -> Let4 (App4 (Lit4 resume) (UnList4 (BinOp4 (Lit4 (ConsV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 v1))) NilV4)) Concat4 (Lit4 (ConsV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 v1))) (ConsV4 (SumRightV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 UnitV4)))) (ConsV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 v1))) (ConsV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 v1))) NilV4)))))) (UnSum4 (Lit4 (SumRightV4 (ConsV4 (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) NilV4)) (ConsV4 (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) NilV4) (ConsV4 (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) (ConsV4 (LambdaV4 (\v1 -> Lit4 (IntV4 142))) (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) NilV4)))) (ConsV4 (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) NilV4) NilV4)))))) (\v1 -> Lit4 (PairV4 (SumRightV4 (ConsV4 UnitV4 (ConsV4 UnitV4 (ConsV4 UnitV4 NilV4)))) (SumRightV4 (SumRightV4 (IntV4 44))))) (\v1 -> Lit4 (PairV4 (SumLeftV4 (LambdaV4 (\v2 -> Lit4 v2))) (SumRightV4 (SumRightV4 (IntV4 139)))))) (\v1 v2 -> UnSum4 (Lit4 (SumLeftV4 (PairV4 (SumLeftV4 (SumLeftV4 (IntV4 119))) (LambdaV4 (\v3 -> Lit4 (PairV4 (IntV4 42) (IntV4 3))))))) (\v3 -> Lit4 (PairV4 (SumRightV4 (ConsV4 UnitV4 NilV4)) (SumLeftV4 (PairV4 (IntV4 15) (IntV4 20))))) (\v3 -> Lit4 (PairV4 (SumRightV4 (ConsV4 UnitV4 (ConsV4 UnitV4 (ConsV4 UnitV4 NilV4)))) (SumRightV4 (SumRightV4 (IntV4 (-136))))))))) (\v0 -> Lit4 v2)))))
                                            ( \v1 ->
                                                Let4
                                                  (App4 (Lit4 resume) (Lit4 (PairV4 (SumLeftV4 (LambdaV4 (\v1 -> Lit4 v1))) (SumLeftV4 (PairV4 (IntV4 (-171)) (IntV4 90))))))
                                                  ( \v0 ->
                                                      Handle4
                                                        ( Handler4
                                                            "T476Eff1"
                                                            (ret1 v0 v1)
                                                            ( \___op -> case ___op of
                                                                "T476Eff1Op1" -> \v2 resumeF ->
                                                                  let resume = LambdaV4 resumeF
                                                                   in Let4 (Lit4 UnitV4) (\v5 -> Let4 (Lit4 v0) (\v4 -> Let4 (Lit4 UnitV4) (\v3 -> Let4 (App4 (Lit4 resume) (Lit4 (PairV4 (LambdaV4 (\v3 -> Lit4 (LambdaV4 (\v4 -> Lit4 v3)))) UnitV4))) (\v2 -> Lit4 v4))))
                                                                "T476Eff1Op2" -> \v2 resumeF ->
                                                                  let resume = LambdaV4 resumeF
                                                                   in Let4 (Lit4 UnitV4) (\v4 -> Let4 (Lit4 v0) (\v3 -> Let4 (Lit4 UnitV4) (\v2 -> Lit4 v3)))
                                                                "T476Eff1Op3" -> \v2 resumeF ->
                                                                  let resume = LambdaV4 resumeF
                                                                   in App4 (Lit4 resume) (BinOp4 (Lit4 (ConsV4 (SumRightV4 NilV4) (ConsV4 (SumRightV4 (ConsV4 UnitV4 (ConsV4 UnitV4 NilV4))) (ConsV4 (SumRightV4 (ConsV4 UnitV4 (ConsV4 UnitV4 NilV4))) (ConsV4 (SumLeftV4 (IntV4 29)) NilV4))))) Concat4 (Lit4 (ConsV4 (SumLeftV4 (IntV4 83)) (ConsV4 (SumLeftV4 (IntV4 (-160))) (ConsV4 (SumLeftV4 (IntV4 83)) NilV4)))))
                                                            )
                                                            (\___scp -> case ___scp of {})
                                                            (\v2 v3 -> Lit4 v2)
                                                        )
                                                        (Lit4 (SumRightV4 (LambdaV4 (\v2 -> Lit4 (IntV4 (-47))))))
                                                  )
                                            )
                                      )
                                  )
                                  (\v0 -> Let4 (UnSum4 (Lit4 (SumRightV4 (ConsV4 (ConsV4 (ConsV4 (IntV4 102) (ConsV4 (IntV4 126) (ConsV4 (IntV4 (-147)) NilV4))) (ConsV4 (ConsV4 (IntV4 (-91)) (ConsV4 (IntV4 184) (ConsV4 (IntV4 (-76)) (ConsV4 (IntV4 (-139)) NilV4)))) (ConsV4 (ConsV4 (IntV4 85) NilV4) NilV4))) (ConsV4 (ConsV4 (ConsV4 (IntV4 108) (ConsV4 (IntV4 (-36)) (ConsV4 (IntV4 (-55)) NilV4))) (ConsV4 NilV4 (ConsV4 (ConsV4 (IntV4 125) (ConsV4 (IntV4 32) (ConsV4 (IntV4 (-5)) NilV4))) (ConsV4 (ConsV4 (IntV4 (-22)) (ConsV4 (IntV4 169) (ConsV4 (IntV4 (-107)) (ConsV4 (IntV4 (-19)) NilV4)))) NilV4)))) (ConsV4 (ConsV4 (ConsV4 (IntV4 22) (ConsV4 (IntV4 (-57)) (ConsV4 (IntV4 109) NilV4))) (ConsV4 (ConsV4 (IntV4 (-27)) (ConsV4 (IntV4 (-112)) (ConsV4 (IntV4 (-78)) (ConsV4 (IntV4 (-62)) NilV4)))) (ConsV4 (ConsV4 (IntV4 8) NilV4) NilV4))) NilV4))))) (\v1 -> Lit4 (ConsV4 (SumRightV4 (SumRightV4 UnitV4)) (ConsV4 (SumLeftV4 (PairV4 (IntV4 8) (IntV4 170))) NilV4))) (\v1 -> Lit4 (ConsV4 (SumRightV4 (SumRightV4 UnitV4)) NilV4))) (\v1 -> UnList4 (Lit4 (ConsV4 (PairV4 UnitV4 (SumRightV4 UnitV4)) (ConsV4 (PairV4 UnitV4 (SumLeftV4 (ConsV4 (IntV4 (-133)) (ConsV4 (IntV4 131) (ConsV4 (IntV4 (-75)) (ConsV4 (IntV4 17) NilV4)))))) (ConsV4 (PairV4 UnitV4 (SumLeftV4 (ConsV4 (IntV4 175) (ConsV4 (IntV4 72) (ConsV4 (IntV4 (-129)) (ConsV4 (IntV4 189) NilV4)))))) (ConsV4 (PairV4 UnitV4 (SumRightV4 UnitV4)) NilV4))))) (Lit4 v0) (\v2 v3 -> Lit4 v0)))
                            )
                )
                (\___scp -> case ___scp of {})
                ( \v0 v1 -> undefined
                )
            )
            (UnList4 (Lit4 NilV4) (Lit4 (SumRightV4 (SumRightV4 (ConsV4 (IntV4 4) (ConsV4 (IntV4 (-110)) (ConsV4 (IntV4 (-156)) NilV4)))))) (\v0 v1 -> Lit4 (SumRightV4 (SumRightV4 (ConsV4 (IntV4 (-35)) (ConsV4 (IntV4 78) (ConsV4 (IntV4 67) NilV4)))))))
        )
    )
  where
    ret1 :: Value4 -> Value4 -> Value4 -> Expr4
    ret1 v0 v1 v2 = Lit4 v0
    ret0 :: Value4 -> Expr4
    ret0 v0 = UnSum4 (Lit4 (SumRightV4 (PairV4 (LambdaV4 (\v1 -> Lit4 v1)) (ConsV4 (LambdaV4 (\v1 -> Lit4 v1)) NilV4)))) (\v1 -> Lit4 UnitV4) (\v1 -> Lit4 UnitV4)
    ret2 :: Value4 -> Value4 -> Value4 -> Expr4
    ret2 v0 v1 v2 = Lit4 v0
