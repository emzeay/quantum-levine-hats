import LevineHats.Model
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 100000
namespace LevineHats
open scoped BigOperators

abbrev TwoBlocks := Word × Word

def monochrome (x : Word) : Bool := x == 0 || x == 15

def observedBlock (x : TwoBlocks) : Word := if monochrome x.1 then x.2 else x.1

def twoAliceSetting (y : TwoBlocks) : Fin 3 := aliceSetting (observedBlock y)
def twoBobSetting (x : TwoBlocks) : Fin 2 := bobSetting (observedBlock x)

def twoAliceLabel (y : TwoBlocks) (a : Outcome) : Fin 2 × Position :=
  (if monochrome y.1 then 1 else 0, aliceLabel (observedBlock y) a)
def twoBobLabel (x : TwoBlocks) (b : Outcome) : Fin 2 × Position :=
  (if monochrome x.1 then 1 else 0, bobLabel (observedBlock x) b)
def twoHat (x : TwoBlocks) (p : Fin 2 × Position) : Bool :=
  hat (if p.1 = 0 then x.1 else x.2) p.2

def twoWin (x y : TwoBlocks) (a b : Outcome) : Bool :=
  twoHat x (twoAliceLabel y a) && twoHat y (twoBobLabel x b)

def twoSlice (x y : Word) : Nat := ∑ u : Word, ∑ v : Word, ∑ a : Outcome, ∑ b : Outcome,
  if twoWin (x,u) (y,v) a b then
    weight (twoAliceSetting (y,v)) (twoBobSetting (x,u)) a b else 0

theorem twoSlice_0_0 : twoSlice 0 0 = 6068 := by decide +kernel
theorem twoSlice_0_1 : twoSlice 0 1 = 0 := by decide +kernel
theorem twoSlice_0_2 : twoSlice 0 2 = 0 := by decide +kernel
theorem twoSlice_0_3 : twoSlice 0 3 = 0 := by decide +kernel
theorem twoSlice_0_4 : twoSlice 0 4 = 0 := by decide +kernel
theorem twoSlice_0_5 : twoSlice 0 5 = 0 := by decide +kernel
theorem twoSlice_0_6 : twoSlice 0 6 = 0 := by decide +kernel
theorem twoSlice_0_7 : twoSlice 0 7 = 0 := by decide +kernel
theorem twoSlice_0_8 : twoSlice 0 8 = 0 := by decide +kernel
theorem twoSlice_0_9 : twoSlice 0 9 = 0 := by decide +kernel
theorem twoSlice_0_10 : twoSlice 0 10 = 0 := by decide +kernel
theorem twoSlice_0_11 : twoSlice 0 11 = 0 := by decide +kernel
theorem twoSlice_0_12 : twoSlice 0 12 = 0 := by decide +kernel
theorem twoSlice_0_13 : twoSlice 0 13 = 0 := by decide +kernel
theorem twoSlice_0_14 : twoSlice 0 14 = 0 := by decide +kernel
theorem twoSlice_0_15 : twoSlice 0 15 = 6068 := by decide +kernel
theorem twoSlice_1_0 : twoSlice 1 0 = 0 := by decide +kernel
theorem twoSlice_1_1 : twoSlice 1 1 = 17408 := by decide +kernel
theorem twoSlice_1_2 : twoSlice 1 2 = 0 := by decide +kernel
theorem twoSlice_1_3 : twoSlice 1 3 = 0 := by decide +kernel
theorem twoSlice_1_4 : twoSlice 1 4 = 0 := by decide +kernel
theorem twoSlice_1_5 : twoSlice 1 5 = 8704 := by decide +kernel
theorem twoSlice_1_6 : twoSlice 1 6 = 0 := by decide +kernel
theorem twoSlice_1_7 : twoSlice 1 7 = 8704 := by decide +kernel
theorem twoSlice_1_8 : twoSlice 1 8 = 0 := by decide +kernel
theorem twoSlice_1_9 : twoSlice 1 9 = 8704 := by decide +kernel
theorem twoSlice_1_10 : twoSlice 1 10 = 0 := by decide +kernel
theorem twoSlice_1_11 : twoSlice 1 11 = 8704 := by decide +kernel
theorem twoSlice_1_12 : twoSlice 1 12 = 0 := by decide +kernel
theorem twoSlice_1_13 : twoSlice 1 13 = 0 := by decide +kernel
theorem twoSlice_1_14 : twoSlice 1 14 = 0 := by decide +kernel
theorem twoSlice_1_15 : twoSlice 1 15 = 8704 := by decide +kernel
theorem twoSlice_2_0 : twoSlice 2 0 = 0 := by decide +kernel
theorem twoSlice_2_1 : twoSlice 2 1 = 0 := by decide +kernel
theorem twoSlice_2_2 : twoSlice 2 2 = 17408 := by decide +kernel
theorem twoSlice_2_3 : twoSlice 2 3 = 17408 := by decide +kernel
theorem twoSlice_2_4 : twoSlice 2 4 = 0 := by decide +kernel
theorem twoSlice_2_5 : twoSlice 2 5 = 0 := by decide +kernel
theorem twoSlice_2_6 : twoSlice 2 6 = 8704 := by decide +kernel
theorem twoSlice_2_7 : twoSlice 2 7 = 8704 := by decide +kernel
theorem twoSlice_2_8 : twoSlice 2 8 = 0 := by decide +kernel
theorem twoSlice_2_9 : twoSlice 2 9 = 0 := by decide +kernel
theorem twoSlice_2_10 : twoSlice 2 10 = 8704 := by decide +kernel
theorem twoSlice_2_11 : twoSlice 2 11 = 8704 := by decide +kernel
theorem twoSlice_2_12 : twoSlice 2 12 = 0 := by decide +kernel
theorem twoSlice_2_13 : twoSlice 2 13 = 0 := by decide +kernel
theorem twoSlice_2_14 : twoSlice 2 14 = 0 := by decide +kernel
theorem twoSlice_2_15 : twoSlice 2 15 = 8704 := by decide +kernel
theorem twoSlice_3_0 : twoSlice 3 0 = 0 := by decide +kernel
theorem twoSlice_3_1 : twoSlice 3 1 = 8704 := by decide +kernel
theorem twoSlice_3_2 : twoSlice 3 2 = 8704 := by decide +kernel
theorem twoSlice_3_3 : twoSlice 3 3 = 17408 := by decide +kernel
theorem twoSlice_3_4 : twoSlice 3 4 = 0 := by decide +kernel
theorem twoSlice_3_5 : twoSlice 3 5 = 6400 := by decide +kernel
theorem twoSlice_3_6 : twoSlice 3 6 = 4352 := by decide +kernel
theorem twoSlice_3_7 : twoSlice 3 7 = 17408 := by decide +kernel
theorem twoSlice_3_8 : twoSlice 3 8 = 0 := by decide +kernel
theorem twoSlice_3_9 : twoSlice 3 9 = 4352 := by decide +kernel
theorem twoSlice_3_10 : twoSlice 3 10 = 6400 := by decide +kernel
theorem twoSlice_3_11 : twoSlice 3 11 = 17408 := by decide +kernel
theorem twoSlice_3_12 : twoSlice 3 12 = 0 := by decide +kernel
theorem twoSlice_3_13 : twoSlice 3 13 = 0 := by decide +kernel
theorem twoSlice_3_14 : twoSlice 3 14 = 0 := by decide +kernel
theorem twoSlice_3_15 : twoSlice 3 15 = 8704 := by decide +kernel
theorem twoSlice_4_0 : twoSlice 4 0 = 0 := by decide +kernel
theorem twoSlice_4_1 : twoSlice 4 1 = 0 := by decide +kernel
theorem twoSlice_4_2 : twoSlice 4 2 = 0 := by decide +kernel
theorem twoSlice_4_3 : twoSlice 4 3 = 0 := by decide +kernel
theorem twoSlice_4_4 : twoSlice 4 4 = 8704 := by decide +kernel
theorem twoSlice_4_5 : twoSlice 4 5 = 8192 := by decide +kernel
theorem twoSlice_4_6 : twoSlice 4 6 = 0 := by decide +kernel
theorem twoSlice_4_7 : twoSlice 4 7 = 0 := by decide +kernel
theorem twoSlice_4_8 : twoSlice 4 8 = 8704 := by decide +kernel
theorem twoSlice_4_9 : twoSlice 4 9 = 8704 := by decide +kernel
theorem twoSlice_4_10 : twoSlice 4 10 = 0 := by decide +kernel
theorem twoSlice_4_11 : twoSlice 4 11 = 0 := by decide +kernel
theorem twoSlice_4_12 : twoSlice 4 12 = 0 := by decide +kernel
theorem twoSlice_4_13 : twoSlice 4 13 = 17408 := by decide +kernel
theorem twoSlice_4_14 : twoSlice 4 14 = 0 := by decide +kernel
theorem twoSlice_4_15 : twoSlice 4 15 = 8704 := by decide +kernel
theorem twoSlice_5_0 : twoSlice 5 0 = 0 := by decide +kernel
theorem twoSlice_5_1 : twoSlice 5 1 = 17408 := by decide +kernel
theorem twoSlice_5_2 : twoSlice 5 2 = 0 := by decide +kernel
theorem twoSlice_5_3 : twoSlice 5 3 = 0 := by decide +kernel
theorem twoSlice_5_4 : twoSlice 5 4 = 0 := by decide +kernel
theorem twoSlice_5_5 : twoSlice 5 5 = 17408 := by decide +kernel
theorem twoSlice_5_6 : twoSlice 5 6 = 0 := by decide +kernel
theorem twoSlice_5_7 : twoSlice 5 7 = 8704 := by decide +kernel
theorem twoSlice_5_8 : twoSlice 5 8 = 0 := by decide +kernel
theorem twoSlice_5_9 : twoSlice 5 9 = 17408 := by decide +kernel
theorem twoSlice_5_10 : twoSlice 5 10 = 0 := by decide +kernel
theorem twoSlice_5_11 : twoSlice 5 11 = 8704 := by decide +kernel
theorem twoSlice_5_12 : twoSlice 5 12 = 0 := by decide +kernel
theorem twoSlice_5_13 : twoSlice 5 13 = 17408 := by decide +kernel
theorem twoSlice_5_14 : twoSlice 5 14 = 0 := by decide +kernel
theorem twoSlice_5_15 : twoSlice 5 15 = 8704 := by decide +kernel
theorem twoSlice_6_0 : twoSlice 6 0 = 0 := by decide +kernel
theorem twoSlice_6_1 : twoSlice 6 1 = 0 := by decide +kernel
theorem twoSlice_6_2 : twoSlice 6 2 = 0 := by decide +kernel
theorem twoSlice_6_3 : twoSlice 6 3 = 0 := by decide +kernel
theorem twoSlice_6_4 : twoSlice 6 4 = 8704 := by decide +kernel
theorem twoSlice_6_5 : twoSlice 6 5 = 8192 := by decide +kernel
theorem twoSlice_6_6 : twoSlice 6 6 = 8704 := by decide +kernel
theorem twoSlice_6_7 : twoSlice 6 7 = 8704 := by decide +kernel
theorem twoSlice_6_8 : twoSlice 6 8 = 8704 := by decide +kernel
theorem twoSlice_6_9 : twoSlice 6 9 = 8704 := by decide +kernel
theorem twoSlice_6_10 : twoSlice 6 10 = 8192 := by decide +kernel
theorem twoSlice_6_11 : twoSlice 6 11 = 8704 := by decide +kernel
theorem twoSlice_6_12 : twoSlice 6 12 = 0 := by decide +kernel
theorem twoSlice_6_13 : twoSlice 6 13 = 17408 := by decide +kernel
theorem twoSlice_6_14 : twoSlice 6 14 = 0 := by decide +kernel
theorem twoSlice_6_15 : twoSlice 6 15 = 8704 := by decide +kernel
theorem twoSlice_7_0 : twoSlice 7 0 = 0 := by decide +kernel
theorem twoSlice_7_1 : twoSlice 7 1 = 17408 := by decide +kernel
theorem twoSlice_7_2 : twoSlice 7 2 = 0 := by decide +kernel
theorem twoSlice_7_3 : twoSlice 7 3 = 17408 := by decide +kernel
theorem twoSlice_7_4 : twoSlice 7 4 = 0 := by decide +kernel
theorem twoSlice_7_5 : twoSlice 7 5 = 17408 := by decide +kernel
theorem twoSlice_7_6 : twoSlice 7 6 = 0 := by decide +kernel
theorem twoSlice_7_7 : twoSlice 7 7 = 17408 := by decide +kernel
theorem twoSlice_7_8 : twoSlice 7 8 = 0 := by decide +kernel
theorem twoSlice_7_9 : twoSlice 7 9 = 17408 := by decide +kernel
theorem twoSlice_7_10 : twoSlice 7 10 = 0 := by decide +kernel
theorem twoSlice_7_11 : twoSlice 7 11 = 17408 := by decide +kernel
theorem twoSlice_7_12 : twoSlice 7 12 = 0 := by decide +kernel
theorem twoSlice_7_13 : twoSlice 7 13 = 17408 := by decide +kernel
theorem twoSlice_7_14 : twoSlice 7 14 = 0 := by decide +kernel
theorem twoSlice_7_15 : twoSlice 7 15 = 8704 := by decide +kernel
theorem twoSlice_8_0 : twoSlice 8 0 = 0 := by decide +kernel
theorem twoSlice_8_1 : twoSlice 8 1 = 0 := by decide +kernel
theorem twoSlice_8_2 : twoSlice 8 2 = 0 := by decide +kernel
theorem twoSlice_8_3 : twoSlice 8 3 = 0 := by decide +kernel
theorem twoSlice_8_4 : twoSlice 8 4 = 8704 := by decide +kernel
theorem twoSlice_8_5 : twoSlice 8 5 = 0 := by decide +kernel
theorem twoSlice_8_6 : twoSlice 8 6 = 8704 := by decide +kernel
theorem twoSlice_8_7 : twoSlice 8 7 = 0 := by decide +kernel
theorem twoSlice_8_8 : twoSlice 8 8 = 8704 := by decide +kernel
theorem twoSlice_8_9 : twoSlice 8 9 = 0 := by decide +kernel
theorem twoSlice_8_10 : twoSlice 8 10 = 8192 := by decide +kernel
theorem twoSlice_8_11 : twoSlice 8 11 = 0 := by decide +kernel
theorem twoSlice_8_12 : twoSlice 8 12 = 17408 := by decide +kernel
theorem twoSlice_8_13 : twoSlice 8 13 = 0 := by decide +kernel
theorem twoSlice_8_14 : twoSlice 8 14 = 17408 := by decide +kernel
theorem twoSlice_8_15 : twoSlice 8 15 = 8704 := by decide +kernel
theorem twoSlice_9_0 : twoSlice 9 0 = 0 := by decide +kernel
theorem twoSlice_9_1 : twoSlice 9 1 = 0 := by decide +kernel
theorem twoSlice_9_2 : twoSlice 9 2 = 0 := by decide +kernel
theorem twoSlice_9_3 : twoSlice 9 3 = 0 := by decide +kernel
theorem twoSlice_9_4 : twoSlice 9 4 = 8704 := by decide +kernel
theorem twoSlice_9_5 : twoSlice 9 5 = 8192 := by decide +kernel
theorem twoSlice_9_6 : twoSlice 9 6 = 8704 := by decide +kernel
theorem twoSlice_9_7 : twoSlice 9 7 = 8704 := by decide +kernel
theorem twoSlice_9_8 : twoSlice 9 8 = 8704 := by decide +kernel
theorem twoSlice_9_9 : twoSlice 9 9 = 8704 := by decide +kernel
theorem twoSlice_9_10 : twoSlice 9 10 = 8192 := by decide +kernel
theorem twoSlice_9_11 : twoSlice 9 11 = 8704 := by decide +kernel
theorem twoSlice_9_12 : twoSlice 9 12 = 17408 := by decide +kernel
theorem twoSlice_9_13 : twoSlice 9 13 = 0 := by decide +kernel
theorem twoSlice_9_14 : twoSlice 9 14 = 17408 := by decide +kernel
theorem twoSlice_9_15 : twoSlice 9 15 = 8704 := by decide +kernel
theorem twoSlice_10_0 : twoSlice 10 0 = 0 := by decide +kernel
theorem twoSlice_10_1 : twoSlice 10 1 = 0 := by decide +kernel
theorem twoSlice_10_2 : twoSlice 10 2 = 17408 := by decide +kernel
theorem twoSlice_10_3 : twoSlice 10 3 = 17408 := by decide +kernel
theorem twoSlice_10_4 : twoSlice 10 4 = 0 := by decide +kernel
theorem twoSlice_10_5 : twoSlice 10 5 = 0 := by decide +kernel
theorem twoSlice_10_6 : twoSlice 10 6 = 17408 := by decide +kernel
theorem twoSlice_10_7 : twoSlice 10 7 = 8704 := by decide +kernel
theorem twoSlice_10_8 : twoSlice 10 8 = 0 := by decide +kernel
theorem twoSlice_10_9 : twoSlice 10 9 = 0 := by decide +kernel
theorem twoSlice_10_10 : twoSlice 10 10 = 17408 := by decide +kernel
theorem twoSlice_10_11 : twoSlice 10 11 = 8704 := by decide +kernel
theorem twoSlice_10_12 : twoSlice 10 12 = 0 := by decide +kernel
theorem twoSlice_10_13 : twoSlice 10 13 = 0 := by decide +kernel
theorem twoSlice_10_14 : twoSlice 10 14 = 17408 := by decide +kernel
theorem twoSlice_10_15 : twoSlice 10 15 = 8704 := by decide +kernel
theorem twoSlice_11_0 : twoSlice 11 0 = 0 := by decide +kernel
theorem twoSlice_11_1 : twoSlice 11 1 = 0 := by decide +kernel
theorem twoSlice_11_2 : twoSlice 11 2 = 17408 := by decide +kernel
theorem twoSlice_11_3 : twoSlice 11 3 = 17408 := by decide +kernel
theorem twoSlice_11_4 : twoSlice 11 4 = 0 := by decide +kernel
theorem twoSlice_11_5 : twoSlice 11 5 = 0 := by decide +kernel
theorem twoSlice_11_6 : twoSlice 11 6 = 17408 := by decide +kernel
theorem twoSlice_11_7 : twoSlice 11 7 = 17408 := by decide +kernel
theorem twoSlice_11_8 : twoSlice 11 8 = 0 := by decide +kernel
theorem twoSlice_11_9 : twoSlice 11 9 = 0 := by decide +kernel
theorem twoSlice_11_10 : twoSlice 11 10 = 17408 := by decide +kernel
theorem twoSlice_11_11 : twoSlice 11 11 = 17408 := by decide +kernel
theorem twoSlice_11_12 : twoSlice 11 12 = 0 := by decide +kernel
theorem twoSlice_11_13 : twoSlice 11 13 = 0 := by decide +kernel
theorem twoSlice_11_14 : twoSlice 11 14 = 17408 := by decide +kernel
theorem twoSlice_11_15 : twoSlice 11 15 = 8704 := by decide +kernel
theorem twoSlice_12_0 : twoSlice 12 0 = 0 := by decide +kernel
theorem twoSlice_12_1 : twoSlice 12 1 = 0 := by decide +kernel
theorem twoSlice_12_2 : twoSlice 12 2 = 0 := by decide +kernel
theorem twoSlice_12_3 : twoSlice 12 3 = 0 := by decide +kernel
theorem twoSlice_12_4 : twoSlice 12 4 = 8704 := by decide +kernel
theorem twoSlice_12_5 : twoSlice 12 5 = 6400 := by decide +kernel
theorem twoSlice_12_6 : twoSlice 12 6 = 4352 := by decide +kernel
theorem twoSlice_12_7 : twoSlice 12 7 = 0 := by decide +kernel
theorem twoSlice_12_8 : twoSlice 12 8 = 8704 := by decide +kernel
theorem twoSlice_12_9 : twoSlice 12 9 = 4352 := by decide +kernel
theorem twoSlice_12_10 : twoSlice 12 10 = 6400 := by decide +kernel
theorem twoSlice_12_11 : twoSlice 12 11 = 0 := by decide +kernel
theorem twoSlice_12_12 : twoSlice 12 12 = 17408 := by decide +kernel
theorem twoSlice_12_13 : twoSlice 12 13 = 17408 := by decide +kernel
theorem twoSlice_12_14 : twoSlice 12 14 = 17408 := by decide +kernel
theorem twoSlice_12_15 : twoSlice 12 15 = 8704 := by decide +kernel
theorem twoSlice_13_0 : twoSlice 13 0 = 0 := by decide +kernel
theorem twoSlice_13_1 : twoSlice 13 1 = 0 := by decide +kernel
theorem twoSlice_13_2 : twoSlice 13 2 = 0 := by decide +kernel
theorem twoSlice_13_3 : twoSlice 13 3 = 0 := by decide +kernel
theorem twoSlice_13_4 : twoSlice 13 4 = 8704 := by decide +kernel
theorem twoSlice_13_5 : twoSlice 13 5 = 8704 := by decide +kernel
theorem twoSlice_13_6 : twoSlice 13 6 = 8704 := by decide +kernel
theorem twoSlice_13_7 : twoSlice 13 7 = 8704 := by decide +kernel
theorem twoSlice_13_8 : twoSlice 13 8 = 8704 := by decide +kernel
theorem twoSlice_13_9 : twoSlice 13 9 = 8704 := by decide +kernel
theorem twoSlice_13_10 : twoSlice 13 10 = 8192 := by decide +kernel
theorem twoSlice_13_11 : twoSlice 13 11 = 8704 := by decide +kernel
theorem twoSlice_13_12 : twoSlice 13 12 = 17408 := by decide +kernel
theorem twoSlice_13_13 : twoSlice 13 13 = 17408 := by decide +kernel
theorem twoSlice_13_14 : twoSlice 13 14 = 17408 := by decide +kernel
theorem twoSlice_13_15 : twoSlice 13 15 = 8704 := by decide +kernel
theorem twoSlice_14_0 : twoSlice 14 0 = 0 := by decide +kernel
theorem twoSlice_14_1 : twoSlice 14 1 = 0 := by decide +kernel
theorem twoSlice_14_2 : twoSlice 14 2 = 0 := by decide +kernel
theorem twoSlice_14_3 : twoSlice 14 3 = 0 := by decide +kernel
theorem twoSlice_14_4 : twoSlice 14 4 = 8704 := by decide +kernel
theorem twoSlice_14_5 : twoSlice 14 5 = 8192 := by decide +kernel
theorem twoSlice_14_6 : twoSlice 14 6 = 8704 := by decide +kernel
theorem twoSlice_14_7 : twoSlice 14 7 = 8704 := by decide +kernel
theorem twoSlice_14_8 : twoSlice 14 8 = 8704 := by decide +kernel
theorem twoSlice_14_9 : twoSlice 14 9 = 8704 := by decide +kernel
theorem twoSlice_14_10 : twoSlice 14 10 = 8704 := by decide +kernel
theorem twoSlice_14_11 : twoSlice 14 11 = 8704 := by decide +kernel
theorem twoSlice_14_12 : twoSlice 14 12 = 17408 := by decide +kernel
theorem twoSlice_14_13 : twoSlice 14 13 = 17408 := by decide +kernel
theorem twoSlice_14_14 : twoSlice 14 14 = 17408 := by decide +kernel
theorem twoSlice_14_15 : twoSlice 14 15 = 8704 := by decide +kernel
theorem twoSlice_15_0 : twoSlice 15 0 = 6068 := by decide +kernel
theorem twoSlice_15_1 : twoSlice 15 1 = 8704 := by decide +kernel
theorem twoSlice_15_2 : twoSlice 15 2 = 8704 := by decide +kernel
theorem twoSlice_15_3 : twoSlice 15 3 = 8704 := by decide +kernel
theorem twoSlice_15_4 : twoSlice 15 4 = 8704 := by decide +kernel
theorem twoSlice_15_5 : twoSlice 15 5 = 8704 := by decide +kernel
theorem twoSlice_15_6 : twoSlice 15 6 = 8704 := by decide +kernel
theorem twoSlice_15_7 : twoSlice 15 7 = 8704 := by decide +kernel
theorem twoSlice_15_8 : twoSlice 15 8 = 8704 := by decide +kernel
theorem twoSlice_15_9 : twoSlice 15 9 = 8704 := by decide +kernel
theorem twoSlice_15_10 : twoSlice 15 10 = 8704 := by decide +kernel
theorem twoSlice_15_11 : twoSlice 15 11 = 8704 := by decide +kernel
theorem twoSlice_15_12 : twoSlice 15 12 = 8704 := by decide +kernel
theorem twoSlice_15_13 : twoSlice 15 13 = 8704 := by decide +kernel
theorem twoSlice_15_14 : twoSlice 15 14 = 8704 := by decide +kernel
theorem twoSlice_15_15 : twoSlice 15 15 = 6068 := by decide +kernel

def sliceTable : Word → Word → Nat := ![![6068,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6068],![0,17408,0,0,0,8704,0,8704,0,8704,0,8704,0,0,0,8704],![0,0,17408,17408,0,0,8704,8704,0,0,8704,8704,0,0,0,8704],![0,8704,8704,17408,0,6400,4352,17408,0,4352,6400,17408,0,0,0,8704],![0,0,0,0,8704,8192,0,0,8704,8704,0,0,0,17408,0,8704],![0,17408,0,0,0,17408,0,8704,0,17408,0,8704,0,17408,0,8704],![0,0,0,0,8704,8192,8704,8704,8704,8704,8192,8704,0,17408,0,8704],![0,17408,0,17408,0,17408,0,17408,0,17408,0,17408,0,17408,0,8704],![0,0,0,0,8704,0,8704,0,8704,0,8192,0,17408,0,17408,8704],![0,0,0,0,8704,8192,8704,8704,8704,8704,8192,8704,17408,0,17408,8704],![0,0,17408,17408,0,0,17408,8704,0,0,17408,8704,0,0,17408,8704],![0,0,17408,17408,0,0,17408,17408,0,0,17408,17408,0,0,17408,8704],![0,0,0,0,8704,6400,4352,0,8704,4352,6400,0,17408,17408,17408,8704],![0,0,0,0,8704,8704,8704,8704,8704,8704,8192,8704,17408,17408,17408,8704],![0,0,0,0,8704,8192,8704,8704,8704,8704,8704,8704,17408,17408,17408,8704],![6068,8704,8704,8704,8704,8704,8704,8704,8704,8704,8704,8704,8704,8704,8704,6068]]
theorem twoSlice_eq_table (x y : Word) : twoSlice x y = sliceTable x y := by
  fin_cases x <;> fin_cases y
  · exact twoSlice_0_0
  · exact twoSlice_0_1
  · exact twoSlice_0_2
  · exact twoSlice_0_3
  · exact twoSlice_0_4
  · exact twoSlice_0_5
  · exact twoSlice_0_6
  · exact twoSlice_0_7
  · exact twoSlice_0_8
  · exact twoSlice_0_9
  · exact twoSlice_0_10
  · exact twoSlice_0_11
  · exact twoSlice_0_12
  · exact twoSlice_0_13
  · exact twoSlice_0_14
  · exact twoSlice_0_15
  · exact twoSlice_1_0
  · exact twoSlice_1_1
  · exact twoSlice_1_2
  · exact twoSlice_1_3
  · exact twoSlice_1_4
  · exact twoSlice_1_5
  · exact twoSlice_1_6
  · exact twoSlice_1_7
  · exact twoSlice_1_8
  · exact twoSlice_1_9
  · exact twoSlice_1_10
  · exact twoSlice_1_11
  · exact twoSlice_1_12
  · exact twoSlice_1_13
  · exact twoSlice_1_14
  · exact twoSlice_1_15
  · exact twoSlice_2_0
  · exact twoSlice_2_1
  · exact twoSlice_2_2
  · exact twoSlice_2_3
  · exact twoSlice_2_4
  · exact twoSlice_2_5
  · exact twoSlice_2_6
  · exact twoSlice_2_7
  · exact twoSlice_2_8
  · exact twoSlice_2_9
  · exact twoSlice_2_10
  · exact twoSlice_2_11
  · exact twoSlice_2_12
  · exact twoSlice_2_13
  · exact twoSlice_2_14
  · exact twoSlice_2_15
  · exact twoSlice_3_0
  · exact twoSlice_3_1
  · exact twoSlice_3_2
  · exact twoSlice_3_3
  · exact twoSlice_3_4
  · exact twoSlice_3_5
  · exact twoSlice_3_6
  · exact twoSlice_3_7
  · exact twoSlice_3_8
  · exact twoSlice_3_9
  · exact twoSlice_3_10
  · exact twoSlice_3_11
  · exact twoSlice_3_12
  · exact twoSlice_3_13
  · exact twoSlice_3_14
  · exact twoSlice_3_15
  · exact twoSlice_4_0
  · exact twoSlice_4_1
  · exact twoSlice_4_2
  · exact twoSlice_4_3
  · exact twoSlice_4_4
  · exact twoSlice_4_5
  · exact twoSlice_4_6
  · exact twoSlice_4_7
  · exact twoSlice_4_8
  · exact twoSlice_4_9
  · exact twoSlice_4_10
  · exact twoSlice_4_11
  · exact twoSlice_4_12
  · exact twoSlice_4_13
  · exact twoSlice_4_14
  · exact twoSlice_4_15
  · exact twoSlice_5_0
  · exact twoSlice_5_1
  · exact twoSlice_5_2
  · exact twoSlice_5_3
  · exact twoSlice_5_4
  · exact twoSlice_5_5
  · exact twoSlice_5_6
  · exact twoSlice_5_7
  · exact twoSlice_5_8
  · exact twoSlice_5_9
  · exact twoSlice_5_10
  · exact twoSlice_5_11
  · exact twoSlice_5_12
  · exact twoSlice_5_13
  · exact twoSlice_5_14
  · exact twoSlice_5_15
  · exact twoSlice_6_0
  · exact twoSlice_6_1
  · exact twoSlice_6_2
  · exact twoSlice_6_3
  · exact twoSlice_6_4
  · exact twoSlice_6_5
  · exact twoSlice_6_6
  · exact twoSlice_6_7
  · exact twoSlice_6_8
  · exact twoSlice_6_9
  · exact twoSlice_6_10
  · exact twoSlice_6_11
  · exact twoSlice_6_12
  · exact twoSlice_6_13
  · exact twoSlice_6_14
  · exact twoSlice_6_15
  · exact twoSlice_7_0
  · exact twoSlice_7_1
  · exact twoSlice_7_2
  · exact twoSlice_7_3
  · exact twoSlice_7_4
  · exact twoSlice_7_5
  · exact twoSlice_7_6
  · exact twoSlice_7_7
  · exact twoSlice_7_8
  · exact twoSlice_7_9
  · exact twoSlice_7_10
  · exact twoSlice_7_11
  · exact twoSlice_7_12
  · exact twoSlice_7_13
  · exact twoSlice_7_14
  · exact twoSlice_7_15
  · exact twoSlice_8_0
  · exact twoSlice_8_1
  · exact twoSlice_8_2
  · exact twoSlice_8_3
  · exact twoSlice_8_4
  · exact twoSlice_8_5
  · exact twoSlice_8_6
  · exact twoSlice_8_7
  · exact twoSlice_8_8
  · exact twoSlice_8_9
  · exact twoSlice_8_10
  · exact twoSlice_8_11
  · exact twoSlice_8_12
  · exact twoSlice_8_13
  · exact twoSlice_8_14
  · exact twoSlice_8_15
  · exact twoSlice_9_0
  · exact twoSlice_9_1
  · exact twoSlice_9_2
  · exact twoSlice_9_3
  · exact twoSlice_9_4
  · exact twoSlice_9_5
  · exact twoSlice_9_6
  · exact twoSlice_9_7
  · exact twoSlice_9_8
  · exact twoSlice_9_9
  · exact twoSlice_9_10
  · exact twoSlice_9_11
  · exact twoSlice_9_12
  · exact twoSlice_9_13
  · exact twoSlice_9_14
  · exact twoSlice_9_15
  · exact twoSlice_10_0
  · exact twoSlice_10_1
  · exact twoSlice_10_2
  · exact twoSlice_10_3
  · exact twoSlice_10_4
  · exact twoSlice_10_5
  · exact twoSlice_10_6
  · exact twoSlice_10_7
  · exact twoSlice_10_8
  · exact twoSlice_10_9
  · exact twoSlice_10_10
  · exact twoSlice_10_11
  · exact twoSlice_10_12
  · exact twoSlice_10_13
  · exact twoSlice_10_14
  · exact twoSlice_10_15
  · exact twoSlice_11_0
  · exact twoSlice_11_1
  · exact twoSlice_11_2
  · exact twoSlice_11_3
  · exact twoSlice_11_4
  · exact twoSlice_11_5
  · exact twoSlice_11_6
  · exact twoSlice_11_7
  · exact twoSlice_11_8
  · exact twoSlice_11_9
  · exact twoSlice_11_10
  · exact twoSlice_11_11
  · exact twoSlice_11_12
  · exact twoSlice_11_13
  · exact twoSlice_11_14
  · exact twoSlice_11_15
  · exact twoSlice_12_0
  · exact twoSlice_12_1
  · exact twoSlice_12_2
  · exact twoSlice_12_3
  · exact twoSlice_12_4
  · exact twoSlice_12_5
  · exact twoSlice_12_6
  · exact twoSlice_12_7
  · exact twoSlice_12_8
  · exact twoSlice_12_9
  · exact twoSlice_12_10
  · exact twoSlice_12_11
  · exact twoSlice_12_12
  · exact twoSlice_12_13
  · exact twoSlice_12_14
  · exact twoSlice_12_15
  · exact twoSlice_13_0
  · exact twoSlice_13_1
  · exact twoSlice_13_2
  · exact twoSlice_13_3
  · exact twoSlice_13_4
  · exact twoSlice_13_5
  · exact twoSlice_13_6
  · exact twoSlice_13_7
  · exact twoSlice_13_8
  · exact twoSlice_13_9
  · exact twoSlice_13_10
  · exact twoSlice_13_11
  · exact twoSlice_13_12
  · exact twoSlice_13_13
  · exact twoSlice_13_14
  · exact twoSlice_13_15
  · exact twoSlice_14_0
  · exact twoSlice_14_1
  · exact twoSlice_14_2
  · exact twoSlice_14_3
  · exact twoSlice_14_4
  · exact twoSlice_14_5
  · exact twoSlice_14_6
  · exact twoSlice_14_7
  · exact twoSlice_14_8
  · exact twoSlice_14_9
  · exact twoSlice_14_10
  · exact twoSlice_14_11
  · exact twoSlice_14_12
  · exact twoSlice_14_13
  · exact twoSlice_14_14
  · exact twoSlice_14_15
  · exact twoSlice_15_0
  · exact twoSlice_15_1
  · exact twoSlice_15_2
  · exact twoSlice_15_3
  · exact twoSlice_15_4
  · exact twoSlice_15_5
  · exact twoSlice_15_6
  · exact twoSlice_15_7
  · exact twoSlice_15_8
  · exact twoSlice_15_9
  · exact twoSlice_15_10
  · exact twoSlice_15_11
  · exact twoSlice_15_12
  · exact twoSlice_15_13
  · exact twoSlice_15_14
  · exact twoSlice_15_15

theorem two_total_weight : (∑ x : Word, ∑ y : Word, twoSlice x y) = 1560272 := by
  simp only [twoSlice_eq_table]
  decide +kernel

def twoScore : ℚ := (∑ x : Word, ∑ y : Word, ∑ u : Word, ∑ v : Word,
  ∑ a : Outcome, ∑ b : Outcome, if twoWin (x,u) (y,v) a b then
    probability (twoAliceSetting (y,v)) (twoBobSetting (x,u)) a b else 0) / 65536

theorem twoScore_exact : twoScore = 97517/278528 := by
  have h : twoScore = ((∑ x : Word, ∑ y : Word, twoSlice x y : Nat) : ℚ) / 68 / 65536 := by
    simp only [twoScore, twoSlice, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
      Finset.sum_div, ite_div, zero_div, probability_eq_weight]
  rw [h, two_total_weight]
  norm_num

theorem twoScore_above_conjectured_benchmark : twoScore - 7/20 = 161/1392640 := by
  rw [twoScore_exact]
  norm_num

end LevineHats
