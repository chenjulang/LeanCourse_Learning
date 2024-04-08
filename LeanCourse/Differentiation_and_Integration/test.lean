-- 研究方法：
-- 1.从研究生角度看文档--较难
-- 2.从本科生角度从零构建概念，路很长。
-- 3.从mathlib里面熟悉的定理开始反向学习，追究原理深度2-3层最好，
  -- 这样掌握起来会比较快，而且有实际应用，有成就感。

-- 出发点1：数学分析内容整理：lake-packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals.lean
-- sin计算值证明： /Users/chenjulang/Desktop/数学/LeanCourse_Learning/lake-packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Angle.lean
-- 积分计算例子：
-- integral_cos_mul_cos_pow_aux
--  integral_gaussian_complex_Ioi
-- 出发点2:***Lecture13节课，或者MIL的Structure开始重看。
-- 出发点3:
  -- 群里发过的小问题项目
  -- ***或者Kevin的课程：https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Introduction/introduction.html
  -- ***硕士生Lean4教程：https://github.com/adomani/MA4N1_2023
-- 出发点4：有没有低观点的定义出发的证明？LADR4
-- 出发点5:陶哲轩从零学习Lean4过程记录23年10月10日开始：链接：https://mathstodon.xyz/@tao

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

noncomputable section s1

#check sin 0 = 0

end s1
